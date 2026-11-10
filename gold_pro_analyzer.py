# ============================================================
# ⚠️ هذا الملف (الجزء 1 من 2) غير قابل للتشغيل وحده.
# الجزء التاني: gold_pro_analyzer_part2.py — يكمل مباشرة من هنا
# ادمج الاتنين بالأمر: cat gold_pro_analyzer_part1.py gold_pro_analyzer_part2.py > gold_pro_analyzer.py
# ============================================================
#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
============================================================
Gold Pro Analyzer — محلل الذهب الاحترافي الموحّد (نسخة بدون مكتبات خارجية)
============================================================
هذه نسخة معاد كتابتها بالكامل باستخدام مكتبات بايثون القياسية فقط
(urllib, json, math, statistics, bisect, csv, collections) — بدون
numpy أو pandas أو yfinance أو requests أو matplotlib. الهدف: تشتغل
على أي جهاز بايثون عادي (بما فيه Termux على أندرويد) من غير أي
pip install لأي مكتبة خارجية، وبنفس دقة الحسابات والمنطق تمامًا.

طريقة الاستخدام:
    python gold_pro_analyzer.py swing --symbol GC=F --period 6mo --interval 1d --csv gold.csv
    python gold_pro_analyzer.py council --symbol GC=F --full
    python gold_pro_analyzer.py council --symbol GC=F --live
    python gold_pro_analyzer.py cascade --symbol GC=F --live

⚠️ هذا تحليل فني آلي وصفي فقط، وليس توصية استثمارية.
============================================================
"""

import argparse
import bisect
import csv
import json
import logging
import math
import os
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import warnings
from dataclasses import dataclass
from datetime import datetime, timezone
from typing import Dict, List, Optional, Tuple

warnings.filterwarnings("ignore")

logging.basicConfig(level=logging.INFO, format="%(levelname)s: %(message)s")
logger = logging.getLogger("gold_pro_analyzer")

NAN = float("nan")


def isnan(x) -> bool:
    return x is None or (isinstance(x, float) and math.isnan(x))


TIMEFRAMES = ["5m", "15m", "30m"]
TF_MIN = {"1m": 1, "5m": 5, "15m": 15, "30m": 30, "60m": 60,
          "1h": 60, "4h": 240, "1d": 1440}
SCAN_CYCLE_S = 60


def bars_for_minutes(minutes: float, tf_label: str, min_bars: int = 5) -> int:
    tf_min = TF_MIN.get(tf_label, 30)
    return max(min_bars, round(minutes / tf_min))


@dataclass(frozen=True)
class IndicatorConfig:
    sma_period: int = 20
    rsi_period: int = 14
    macd_fast: int = 12
    macd_slow: int = 26
    macd_signal: int = 9
    sr_lookback_minutes: float = 1200.0
    sr_pivot_wing: int = 2
    rsi_overbought: float = 70.0
    rsi_oversold: float = 30.0
    adx_period: int = 14
    adx_trend_min: float = 20.0
    volume_avg_minutes: float = 600.0
    volume_confirm_mult: float = 1.0
    sr_round_step: float = 5.0
    vp_lookback_bars: int = 120
    vp_bins: int = 24
    vp_value_area_pct: float = 0.70
    vp_acceptance_bars: int = 3
    vp_hvn_lvn_std_mult: float = 0.5
    vp_lvn_breakout_lookback: int = 5


@dataclass(frozen=True)
class TradeConfig:
    target_min_points: float = 8.0
    target_max_points: float = 25.0
    atr_target_mult: float = 2.0
    atr_stop_mult: float = 1.5
    max_stop_to_target_ratio: float = 1.0
    min_rr: float = 1.0
    swing_lookback_minutes: float = 300.0
    tp_stage_mults: tuple = (1.0, 1.6, 2.2)


I = IndicatorConfig()
TC = TradeConfig()

_TREND_AR = {
    'up': 'صاعد', 'down': 'هابط', 'flat': 'عرضي',
    'up_weak': 'صاعد لكن يضعف', 'down_weak': 'هابط لكن يضعف',
}
_RSIZONE_AR = {
    'overbought': 'تشبع شرائي', 'oversold': 'تشبع بيعي',
    'weak': 'ضعيف', 'strong': 'قوي', 'neutral': 'محايد',
}


# ============================================================
# 1) هيكل بيانات الشموع (Bars) — قوائم بايثون عادية بدل numpy
# ============================================================
class Bars:
    def __init__(self, times, data, volume_is_proxy: bool = False,
                 live_price: Optional[float] = None, live_time: Optional[datetime] = None):
        n = len(times)
        for k, v in data.items():
            if len(v) != n:
                raise ValueError(f"{k}:{len(v)}!={n}")
        self.times = list(times)
        self.data = {k: [float(x) for x in v] for k, v in data.items()}
        self.volume_is_proxy = volume_is_proxy
        # السعر اللحظي الفعلي وقت الطلب (من meta.regularMarketPrice) — قد يكون أحدث
        # من إغلاق آخر شمعة مقفلة في data['close'], لأن الشمعة الحالية لسه بتتكوّن.
        self.live_price = live_price
        self.live_time = live_time

    def __len__(self):
        return len(self.times)

    def __getitem__(self, c):
        return self.data[c]

    def __contains__(self, c):
        return c in self.data

    def copy(self):
        return Bars(list(self.times), {k: list(v) for k, v in self.data.items()},
                    volume_is_proxy=self.volume_is_proxy,
                    live_price=self.live_price, live_time=self.live_time)

    def slice(self, start=None, end=None):
        return Bars(self.times[start:end], {k: v[start:end] for k, v in self.data.items()},
                    volume_is_proxy=self.volume_is_proxy,
                    live_price=self.live_price, live_time=self.live_time)


class FetchErr(RuntimeError):
    pass


# ============================================================
# 2) جلب البيانات — عبر urllib القياسية مباشرة من Yahoo Finance
#    (بدون yfinance وبدون requests، فقط مكتبات بايثون الجاهزة)
#    مصدرين متاحين: Yahoo Finance (افتراضي، بدون مفتاح API) أو Twelve Data
#    (أدق للرمز XAU/USD السبوت، محتاج مفتاح API مجاني من twelvedata.com)
# ============================================================
_YF_MAX_PERIOD = {
    "1m": "7d", "2m": "60d", "5m": "60d", "15m": "60d", "30m": "60d",
    "60m": "60d", "1h": "730d", "4h": "730d", "1d": "5y",
}

_YAHOO_HOSTS = ["query1.finance.yahoo.com", "query2.finance.yahoo.com"]
_UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"

# --- إعدادات مصدر البيانات النشط (يُضبط مرة واحدة من main() حسب --provider) ---
_PROVIDER = {"name": "yahoo", "api_key": None}


def configure_provider(name: str, api_key: Optional[str] = None) -> None:
    _PROVIDER["name"] = name
    _PROVIDER["api_key"] = api_key


def default_symbol_for_provider() -> str:
    return "XAU/USD" if _PROVIDER["name"] == "twelvedata" else "GC=F"


def _data_source_disclaimer() -> str:
    if _PROVIDER["name"] == "twelvedata":
        return ("⚠️ السعر اللحظي هنا مصدره Twelve Data (سبوت) — قارن دائمًا مع سعر منصة "
                "تداولك الفعلي قبل تنفيذ أي صفقة.")
    return ("⚠️ السعر اللحظي هنا مصدره Yahoo Finance وقد يحمل تأخيرًا بسيطًا (خصوصًا لعقود الذهب "
            "الآجلة GC=F) — قارن دائمًا مع سعر منصة تداولك الفعلي قبل تنفيذ أي صفقة.")


def _yahoo_chart_request(symbol: str, rng: str, interval: str) -> dict:
    q = urllib.parse.urlencode({
        "range": rng, "interval": interval,
        "includePrePost": "false", "events": "div,splits",
    })
    last_err = None
    for host in _YAHOO_HOSTS:
        url = f"https://{host}/v8/finance/chart/{urllib.parse.quote(symbol)}?{q}"
        req = urllib.request.Request(url, headers={"User-Agent": _UA})
        try:
            with urllib.request.urlopen(req, timeout=15) as resp:
                raw = resp.read()
            return json.loads(raw.decode("utf-8"))
        except Exception as e:
            last_err = e
            continue
    raise FetchErr(f"تعذر الاتصال بـ Yahoo Finance: {last_err}")


def _resample_4h_from_1h(bars_1h: Bars) -> Bars:
    """يجمّع شموع الساعة (1h) في شموع 4 ساعات — Yahoo مالوش فريم 4h جاهز، فبنبنيه
    يدويًا (تجميع محاذي لبداية اليوم UTC: 00-04, 04-08, ...، وهي نفس الطريقة
    القياسية المستخدمة في أغلب أدوات التحليل الفني عند تجميع فريمات أكبر)."""
    times = bars_1h.times
    o, h, l, c, vol = bars_1h['open'], bars_1h['high'], bars_1h['low'], bars_1h['close'], bars_1h['volume']
    n = len(times)
    out_times, out_o, out_h, out_l, out_c, out_v = [], [], [], [], [], []
    i = 0
    while i < n:
        day0 = times[i].date()
        grp0 = times[i].hour // 4
        j = i
        while j < n and times[j].date() == day0 and times[j].hour // 4 == grp0:
            j += 1
        out_times.append(times[i].replace(hour=grp0 * 4, minute=0, second=0, microsecond=0))
        out_o.append(o[i]); out_h.append(max(h[i:j])); out_l.append(min(l[i:j])); out_c.append(c[j - 1])
        out_v.append(sum(vol[i:j]))
        i = j
    return Bars(out_times, {"open": out_o, "high": out_h, "low": out_l, "close": out_c, "volume": out_v},
                volume_is_proxy=bars_1h.volume_is_proxy)


def _fetch_klines_yahoo(symbol: str, tf_label: str, limit: int = 300) -> Bars:
    """يجلب شموع OHLCV مباشرة من Yahoo Finance عبر urllib ويحوّلها إلى Bars موحّدة.
    فريم 4h مش متاح مباشرة من Yahoo، فبيتم بناؤه بتجميع شموع الساعة (1h)."""
    need_4h_resample = (tf_label == "4h")
    fetch_tf = "1h" if need_4h_resample else tf_label
    interval = "60m" if fetch_tf == "1h" else fetch_tf
    rng = _YF_MAX_PERIOD.get(fetch_tf, "60d")
    fetch_limit = max(limit * 4, 1200) if need_4h_resample else limit

    try:
        payload = _yahoo_chart_request(symbol, rng, interval)
    except FetchErr:
        raise
    except Exception as e:
        raise FetchErr(f"خطأ أثناء جلب البيانات ({tf_label}): {e}")

    chart = payload.get("chart", {}) if isinstance(payload, dict) else {}
    err = chart.get("error")
    if err:
        raise FetchErr(f"خطأ من Yahoo Finance ({tf_label}): {err}")
    results = chart.get("result") or []
    if not results:
        raise FetchErr(f"لا توجد بيانات للرمز '{symbol}' على فريم {tf_label}")

    result = results[0]
    timestamps = result.get("timestamp") or []
    quote_list = (result.get("indicators", {}) or {}).get("quote") or []
    if not timestamps or not quote_list:
        raise FetchErr(f"لا توجد بيانات للرمز '{symbol}' على فريم {tf_label}")
    quote = quote_list[0]
    o_raw = quote.get("open") or []
    h_raw = quote.get("high") or []
    l_raw = quote.get("low") or []
    c_raw = quote.get("close") or []
    v_raw = quote.get("volume") or []

    n = len(timestamps)
    times, o, h, l, c, vol = [], [], [], [], [], []
    for i in range(n):
        ci = c_raw[i] if i < len(c_raw) else None
        oi = o_raw[i] if i < len(o_raw) else None
        hi = h_raw[i] if i < len(h_raw) else None
        li = l_raw[i] if i < len(l_raw) else None
        vi = v_raw[i] if i < len(v_raw) else None
        if ci is None or oi is None or hi is None or li is None:
            continue
        times.append(datetime.fromtimestamp(timestamps[i], tz=timezone.utc))
        o.append(float(oi)); h.append(float(hi)); l.append(float(li)); c.append(float(ci))
        vol.append(float(vi) if vi is not None else 0.0)

    if len(times) == 0:
        raise FetchErr(f"لا توجد بيانات صالحة للرمز '{symbol}' على فريم {tf_label}")

    if fetch_limit and len(times) > fetch_limit:
        times, o, h, l, c, vol = (times[-fetch_limit:], o[-fetch_limit:], h[-fetch_limit:], l[-fetch_limit:],
                                   c[-fetch_limit:], vol[-fetch_limit:])

    is_proxy = not any(v > 0 for v in vol)
    if is_proxy:
        vol = [abs(h[i] - l[i]) for i in range(len(h))]

    meta = result.get("meta", {}) or {}
    live_price = meta.get("regularMarketPrice")
    live_price = float(live_price) if live_price is not None else None
    live_ts = meta.get("regularMarketTime")
    live_time = datetime.fromtimestamp(live_ts, tz=timezone.utc) if live_ts else None

    bars_1h = Bars(times, {"open": o, "high": h, "low": l, "close": c, "volume": vol},
                    volume_is_proxy=is_proxy, live_price=live_price, live_time=live_time)

    if need_4h_resample:
        bars_4h = _resample_4h_from_1h(bars_1h)
        if limit and len(bars_4h) > limit:
            bars_4h = bars_4h.slice(-limit, None)
        return bars_4h
    return bars_1h


# ---- Twelve Data (https://twelvedata.com) — أدق للرمز السبوت XAU/USD ----
_TD_BASE_URL = "https://api.twelvedata.com"
_TD_INTERVAL = {
    "1m": "1min", "5m": "5min", "15m": "15min", "30m": "30min",
    "1h": "1h", "4h": "4h", "1d": "1day",
}


def _twelvedata_request(path: str, params: dict, timeout: int = 20, retries: int = 3) -> dict:
    q = urllib.parse.urlencode(params)
    url = f"{_TD_BASE_URL}{path}?{q}"
    last_err = None
    for attempt in range(1, retries + 1):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "gold-pro-analyzer/1.0"})
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                raw = resp.read()
            data = json.loads(raw.decode("utf-8"))
            if isinstance(data, dict) and data.get("status") == "error":
                raise FetchErr(f"خطأ من Twelve Data: {data.get('message')}")
            return data
        except FetchErr:
            raise
        except Exception as e:
            last_err = e
            if attempt < retries:
                time.sleep(1.5 * attempt)
    raise FetchErr(f"تعذر الاتصال بـ Twelve Data: {last_err}")


def _fetch_klines_twelvedata(symbol: str, tf_label: str, api_key: str, limit: int = 300) -> Bars:
    """يجلب شموع OHLC من Twelve Data (/time_series) — الحجم غالبًا غير متوفر
    لرموز السبوت زي XAU/USD، فبيتعامل معاه نفس تعامل الحجم البديل التقريبي."""
    interval = _TD_INTERVAL.get(tf_label)
    if interval is None:
        raise FetchErr(f"فريم غير مدعوم من Twelve Data: {tf_label}")

    payload = _twelvedata_request("/time_series", {
        "symbol": symbol, "interval": interval,
        "outputsize": min(limit, 5000), "apikey": api_key, "order": "ASC",
    })
    values = payload.get("values") or []
    if not values:
        raise FetchErr(f"لا توجد بيانات للرمز '{symbol}' على فريم {tf_label} (Twelve Data)")

    times, o, h, l, c, vol = [], [], [], [], [], []
    for v in values:
        try:
            dts = v["datetime"]
            t = (datetime.strptime(dts, "%Y-%m-%d %H:%M:%S") if len(dts) > 10
                 else datetime.strptime(dts, "%Y-%m-%d"))
            oi, hi, li, ci = float(v["open"]), float(v["high"]), float(v["low"]), float(v["close"])
        except (KeyError, ValueError, TypeError):
            continue
        times.append(t); o.append(oi); h.append(hi); l.append(li); c.append(ci)
        vi = v.get("volume")
        vol.append(float(vi) if vi not in (None, "") else 0.0)

    if not times:
        raise FetchErr(f"كل صفوف الشموع غير صالحة للرمز '{symbol}' (Twelve Data)")

    if limit and len(times) > limit:
        times, o, h, l, c, vol = (times[-limit:], o[-limit:], h[-limit:], l[-limit:],
                                   c[-limit:], vol[-limit:])

    is_proxy = not any(v > 0 for v in vol)
    if is_proxy:
        vol = [abs(h[i] - l[i]) for i in range(len(h))]

    return Bars(times, {"open": o, "high": h, "low": l, "close": c, "volume": vol},
                volume_is_proxy=is_proxy)


def _fetch_live_quote_twelvedata(symbol: str, api_key: str):
    """يجلب السعر اللحظي الحقيقي (/quote) — طلب واحد بس لكل دورة تحديث
    (مش لكل فريم) عشان نوفّر رصيد الـ API المحدود بالخطة المجانية."""
    payload = _twelvedata_request("/quote", {"symbol": symbol, "apikey": api_key})
    price = payload.get("close")
    ts = payload.get("timestamp")
    if price is None:
        return None, None
    live_price = float(price)
    live_time = datetime.fromtimestamp(ts, tz=timezone.utc) if ts else None
    return live_price, live_time


def fetch_klines(symbol: str, tf_label: str, limit: int = 300) -> Bars:
    """موزّع المصدر: Yahoo (افتراضي) أو Twelve Data حسب configure_provider()."""
    if _PROVIDER["name"] == "twelvedata":
        api_key = _PROVIDER.get("api_key")
        if not api_key:
            raise FetchErr("مفتاح Twelve Data مفقود — مرره عبر --api-key أو متغير البيئة "
                            "TWELVEDATA_API_KEY / VIPER_API_KEY")
        return _fetch_klines_twelvedata(symbol, tf_label, api_key, limit)
    return _fetch_klines_yahoo(symbol, tf_label, limit)


def fetch_multi_tf(symbol: str, timeframes: List[str], min_bars: int = 60) -> Dict[str, Bars]:
    out: Dict[str, Bars] = {}
    for tf in timeframes:
        try:
            bars = fetch_klines(symbol, tf)
        except FetchErr as e:
            logger.warning("%s", e)
            continue
        bars = bars.slice(0, -1)
        if len(bars) < min_bars:
            logger.warning("%s: بيانات غير كافية (%d شمعة)", tf, len(bars))
            continue
        out[tf] = bars

    # لـ Twelve Data: السعر اللحظي مش جزء من رد /time_series (عكس Yahoo)، فبنجيبه
    # بطلب واحد إضافي بس لكل الدورة (مش لكل فريم) عشان نوفّر رصيد الـ API.
    if out and _PROVIDER["name"] == "twelvedata" and _PROVIDER.get("api_key"):
        try:
            live_price, live_time = _fetch_live_quote_twelvedata(symbol, _PROVIDER["api_key"])
            for b in out.values():
                b.live_price = live_price
                b.live_time = live_time
        except FetchErr as e:
            logger.warning("تعذر جلب السعر اللحظي من Twelve Data: %s", e)

    return out


# ============================================================
# 3) أدوات رياضية عامة (بديل numpy) — تعمل على قوائم بايثون عادية
# ============================================================
def vmean(x) -> float:
    x = list(x)
    return sum(x) / len(x) if x else NAN


def vstd(x) -> float:
    x = list(x)
    n = len(x)
    if n == 0:
        return NAN
    m = sum(x) / n
    return math.sqrt(sum((v - m) ** 2 for v in x) / n)


def vsum(x) -> float:
    return sum(x)


def clip(v: float, lo: float, hi: float) -> float:
    return max(lo, min(hi, v))


def full_nan(n: int) -> List[float]:
    return [NAN] * n


def cumsum(x: List[float]) -> List[float]:
    out = []
    s = 0.0
    for v in x:
        s += v
        out.append(s)
    return out


def diff(x: List[float]) -> List[float]:
    return [x[i] - x[i - 1] for i in range(1, len(x))]


def roll(x: List[float], shift: int) -> List[float]:
    n = len(x)
    if n == 0:
        return []
    shift = shift % n
    return x[-shift:] + x[:-shift] if shift else list(x)


def _linreg_slope(y: List[float]) -> float:
    n = len(y)
    if n < 2 or all(v == y[0] for v in y):
        return 0.0
    xs = list(range(n))
    mx = sum(xs) / n
    my = sum(y) / n
    num = sum((xs[i] - mx) * (y[i] - my) for i in range(n))
    den = sum((xs[i] - mx) ** 2 for i in range(n))
    return num / den if den != 0 else 0.0


def _clip01_100(x: float) -> float:
    return clip(x, 0.0, 100.0)


# ============================================================
# 4) المحرك الرقمي المشترك (بديل numpy لكل المؤشرات الأساسية)
# ============================================================
def sma(x: List[float], period: int) -> List[float]:
    n = len(x)
    out = full_nan(n)
    if n < period:
        return out
    window_sum = sum(x[:period])
    out[period - 1] = window_sum / period
    for i in range(period, n):
        window_sum += x[i] - x[i - period]
        out[i] = window_sum / period
    return out


def ema(x: List[float], period: int) -> List[float]:
    n = len(x)
    out = full_nan(n)
    if n < period:
        return out
    alpha = 2.0 / (period + 1.0)
    seed = sum(x[:period]) / period
    out[period - 1] = seed
    cur = seed
    for i in range(period, n):
        cur = alpha * x[i] + (1 - alpha) * cur
        out[i] = cur
    return out


def rsi_wilder(close: List[float], period: int = 14) -> List[float]:
    n = len(close)
    out = full_nan(n)
    if n < period + 1:
        return out
    delta = diff(close)
    gain = [d if d > 0 else 0.0 for d in delta]
    loss = [-d if d < 0 else 0.0 for d in delta]

    avg_gain = sum(gain[:period]) / period
    avg_loss = sum(loss[:period]) / period
    rs = avg_gain / avg_loss if avg_loss > 0 else math.inf
    out[period] = 100.0 if avg_loss == 0 else 100.0 - 100.0 / (1.0 + rs)

    for i in range(period + 1, n):
        g = gain[i - 1]; l = loss[i - 1]
        avg_gain = (avg_gain * (period - 1) + g) / period
        avg_loss = (avg_loss * (period - 1) + l) / period
        rs = avg_gain / avg_loss if avg_loss > 0 else math.inf
        out[i] = 100.0 if avg_loss == 0 else 100.0 - 100.0 / (1.0 + rs)
    return out


def macd(close: List[float], fast=12, slow=26, signal=9):
    ema_fast = ema(close, fast)
    ema_slow = ema(close, slow)
    macd_line = [ema_fast[i] - ema_slow[i] if not (isnan(ema_fast[i]) or isnan(ema_slow[i])) else NAN
                 for i in range(len(close))]
    n = len(close)
    signal_line = full_nan(n)
    start = next((i for i, v in enumerate(macd_line) if not isnan(v)), None)
    if start is not None:
        sig_part = ema(macd_line[start:], signal)
        for i, v in enumerate(sig_part):
            signal_line[start + i] = v
    hist = [macd_line[i] - signal_line[i] if not (isnan(macd_line[i]) or isnan(signal_line[i])) else NAN
            for i in range(n)]
    return macd_line, signal_line, hist


def atr_wilder(h, l, c, period=14) -> List[float]:
    n = len(c)
    pc = [c[0]] + c[:-1]
    tr = [max(h[i] - l[i], abs(h[i] - pc[i]), abs(l[i] - pc[i])) for i in range(n)]
    if n > 0:
        tr[0] = h[0] - l[0]
    out = full_nan(n)
    if n < period:
        return out
    out[period - 1] = sum(tr[:period]) / period
    for i in range(period, n):
        out[i] = (out[i - 1] * (period - 1) + tr[i]) / period
    return out


def _wilder_smooth(x: List[float], p: int) -> List[float]:
    n = len(x)
    s = full_nan(n)
    if n < p:
        return s
    s[p - 1] = sum(x[:p])
    for i in range(p, n):
        s[i] = s[i - 1] - (s[i - 1] / p) + x[i]
    return s


def dmi_adx_wilder(h, l, c, period=14):
    n = len(c)
    adx_out = full_nan(n)
    plus_di_out = full_nan(n)
    minus_di_out = full_nan(n)
    if n < period * 2:
        return adx_out, plus_di_out, minus_di_out

    up_move = [h[i] - h[i - 1] for i in range(1, n)]
    down_move = [l[i - 1] - l[i] for i in range(1, n)]
    plus_dm = [up_move[i] if (up_move[i] > down_move[i] and up_move[i] > 0) else 0.0 for i in range(n - 1)]
    minus_dm = [down_move[i] if (down_move[i] > up_move[i] and down_move[i] > 0) else 0.0 for i in range(n - 1)]

    pc = [c[0]] + c[:-1]
    tr_full = [max(h[i] - l[i], abs(h[i] - pc[i]), abs(l[i] - pc[i])) for i in range(n)]
    tr = tr_full[1:]

    tr_s = _wilder_smooth(tr, period)
    pdm_s = _wilder_smooth(plus_dm, period)
    mdm_s = _wilder_smooth(minus_dm, period)

    m = len(tr)
    plus_di = full_nan(m)
    minus_di = full_nan(m)
    dx = full_nan(m)
    for i in range(m):
        if isnan(tr_s[i]) or tr_s[i] == 0:
            continue
        plus_di[i] = 100.0 * pdm_s[i] / tr_s[i]
        minus_di[i] = 100.0 * mdm_s[i] / tr_s[i]
        denom = plus_di[i] + minus_di[i]
        dx[i] = 100.0 * abs(plus_di[i] - minus_di[i]) / denom if denom != 0 else 0.0

    for i in range(m):
        plus_di_out[i + 1] = plus_di[i]
        minus_di_out[i + 1] = minus_di[i]

    start = next((i for i, v in enumerate(dx) if not isnan(v)), None)
    if start is None or (m - start) < period:
        return adx_out, plus_di_out, minus_di_out

    valid_dx = [dx[i] for i in range(start, start + period) if not isnan(dx[i])]
    adx_seg = full_nan(m)
    adx_seg[start + period - 1] = vmean(valid_dx) if valid_dx else NAN
    for i in range(start + period, m):
        prev = adx_seg[i - 1]
        adx_seg[i] = prev + (dx[i] - prev) / period if not isnan(prev) else NAN
    for i in range(m):
        adx_out[i + 1] = adx_seg[i]
    return adx_out, plus_di_out, minus_di_out


def bollinger_bands(c: List[float], period=20, mult=2.0):
    mid = sma(c, period)
    n = len(c)
    std = full_nan(n)
    for i in range(period - 1, n):
        std[i] = vstd(c[i - period + 1:i + 1])
    upper = [mid[i] + mult * std[i] if not (isnan(mid[i]) or isnan(std[i])) else NAN for i in range(n)]
    lower = [mid[i] - mult * std[i] if not (isnan(mid[i]) or isnan(std[i])) else NAN for i in range(n)]
    return upper, mid, lower


def stochastic_kd(h, l, c, k_period=14, d_period=3):
    n = len(c)
    k = full_nan(n)
    for i in range(k_period - 1, n):
        hh = max(h[i - k_period + 1:i + 1])
        ll = min(l[i - k_period + 1:i + 1])
        k[i] = 50.0 if hh == ll else 100.0 * (c[i] - ll) / (hh - ll)
    d = full_nan(n)
    for i in range(n):
        if i + 1 >= d_period:
            window = [k[j] for j in range(i - d_period + 1, i + 1)]
            if not any(isnan(v) for v in window):
                d[i] = vmean(window)
    return k, d


def cci_series(h, l, c, period=20):
    tp = [(h[i] + l[i] + c[i]) / 3.0 for i in range(len(c))]
    n = len(c)
    out = full_nan(n)
    for i in range(period - 1, n):
        seg = tp[i - period + 1:i + 1]
        m = vmean(seg)
        mad = vmean([abs(v - m) for v in seg])
        out[i] = 0.0 if mad == 0 else (tp[i] - m) / (0.015 * mad)
    return out


def williams_r_series(h, l, c, period=14):
    n = len(c)
    out = full_nan(n)
    for i in range(period - 1, n):
        hh = max(h[i - period + 1:i + 1])
        ll = min(l[i - period + 1:i + 1])
        out[i] = -50.0 if hh == ll else -100.0 * (hh - c[i]) / (hh - ll)
    return out


def obv_series(c, vol):
    n = len(c)
    direction = [0.0] * n
    for i in range(n):
        prev = c[i - 1] if i > 0 else c[0]
        direction[i] = 1.0 if c[i] > prev else (-1.0 if c[i] < prev else 0.0)
    return cumsum([direction[i] * vol[i] for i in range(n)])


def mfi_series(h, l, c, vol, period=14):
    tp = [(h[i] + l[i] + c[i]) / 3.0 for i in range(len(c))]
    rmf = [tp[i] * vol[i] for i in range(len(c))]
    n = len(c)
    out = full_nan(n)
    for i in range(period, n):
        seg_tp = tp[i - period:i + 1]
        seg_rmf = rmf[i - period + 1:i + 1]
        pos = sum(seg_rmf[j] for j in range(len(seg_rmf)) if seg_tp[j + 1] > seg_tp[j])
        neg = sum(seg_rmf[j] for j in range(len(seg_rmf)) if seg_tp[j + 1] < seg_tp[j])
        out[i] = 100.0 if neg == 0 else 100.0 - 100.0 / (1.0 + pos / neg)
    return out


def roc_series(c, period=12):
    n = len(c)
    out = full_nan(n)
    for i in range(period, n):
        out[i] = (c[i] - c[i - period]) / c[i - period] * 100.0 if c[i - period] != 0 else NAN
    return out


def vwap_cum(h, l, c, vol):
    tp = [(h[i] + l[i] + c[i]) / 3.0 for i in range(len(c))]
    num = cumsum([tp[i] * vol[i] for i in range(len(c))])
    den = cumsum(vol)
    return [num[i] / den[i] if den[i] != 0 else NAN for i in range(len(c))]


def parabolic_sar_series(h, l, af_start=0.02, af_step=0.02, af_max=0.2):
    n = len(h)
    sar = [0.0] * n
    if n == 0:
        return sar
    trend_up = True
    sar[0] = l[0]
    ep = h[0]
    af = af_start
    for i in range(1, n):
        sar[i] = sar[i - 1] + af * (ep - sar[i - 1])
        if trend_up:
            sar[i] = min(sar[i], l[i - 1], l[i - 2] if i >= 2 else l[i - 1])
            if l[i] < sar[i]:
                trend_up = False; sar[i] = ep; ep = l[i]; af = af_start
            elif h[i] > ep:
                ep = h[i]; af = min(af + af_step, af_max)
        else:
            sar[i] = max(sar[i], h[i - 1], h[i - 2] if i >= 2 else h[i - 1])
            if h[i] > sar[i]:
                trend_up = True; sar[i] = ep; ep = h[i]; af = af_start
            elif l[i] < ep:
                ep = l[i]; af = min(af + af_step, af_max)
    return sar


def ichimoku_lines(h, l, c, tenkan_p=9, kijun_p=26, senkou_p=52):
    n = len(c)

    def _mid(period):
        out = full_nan(n)
        for i in range(period - 1, n):
            out[i] = (max(h[i - period + 1:i + 1]) + min(l[i - period + 1:i + 1])) / 2.0
        return out

    tenkan = _mid(tenkan_p)
    kijun = _mid(kijun_p)
    ks = _mid(senkou_p)
    ta_kj = [(tenkan[i] + kijun[i]) / 2.0 if not (isnan(tenkan[i]) or isnan(kijun[i])) else NAN
             for i in range(n)]
    senkou_a = roll(ta_kj, kijun_p)
    for i in range(min(kijun_p, n)):
        senkou_a[i] = NAN
    senkou_b = roll(ks, kijun_p)
    for i in range(min(kijun_p, n)):
        senkou_b[i] = NAN
    return tenkan, kijun, senkou_a, senkou_b


# ============================================================
# 3.5) بروفايل الحجم (Volume Profile) — POC / VAH / VAL / HVN / LVN / BIAS
# ============================================================
def _vp_build_histogram(bars: Bars, lookback: int, n_bins: int):
    h = bars['high'][-lookback:]
    l = bars['low'][-lookback:]
    vol = bars['volume'][-lookback:]
    price_min = min(l)
    price_max = max(h)
    if price_max <= price_min:
        price_max = price_min + max(price_min * 1e-4, 1e-6)
    step = (price_max - price_min) / n_bins
    edges = [price_min + i * step for i in range(n_bins + 1)]
    vol_hist = [0.0] * n_bins
    for i in range(len(h)):
        bl, bh, bv = float(l[i]), float(h[i]), float(vol[i])
        if bv <= 0:
            continue
        if bh <= bl:
            idx = int(clip((bh - price_min) / (price_max - price_min) * n_bins, 0, n_bins - 1))
            vol_hist[idx] += bv
            continue
        lo_idx = bisect.bisect_right(edges, bl) - 1
        hi_idx = bisect.bisect_right(edges, bh) - 1
        lo_idx = int(clip(lo_idx, 0, n_bins - 1))
        hi_idx = int(clip(hi_idx, 0, n_bins - 1))
        total_range = bh - bl
        if lo_idx == hi_idx:
            vol_hist[lo_idx] += bv
        else:
            for b in range(lo_idx, hi_idx + 1):
                bin_lo = max(edges[b], bl)
                bin_hi = min(edges[b + 1], bh)
                overlap = max(0.0, bin_hi - bin_lo)
                if overlap > 0:
                    vol_hist[b] += bv * (overlap / total_range)
    centers = [(edges[i] + edges[i + 1]) / 2.0 for i in range(n_bins)]
    return edges, centers, vol_hist


def _vp_value_area(centers: List[float], vol_hist: List[float], target_pct: float = 0.70) -> Optional[dict]:
    total = sum(vol_hist)
    if total <= 0:
        return None
    n = len(vol_hist)
    poc_idx = max(range(n), key=lambda i: vol_hist[i])
    lo = hi = poc_idx
    cum = vol_hist[poc_idx]
    while cum < target_pct * total and (lo > 0 or hi < n - 1):
        vol_next_lo = vol_hist[lo - 1] if lo > 0 else -1.0
        vol_next_hi = vol_hist[hi + 1] if hi < n - 1 else -1.0
        if vol_next_hi >= vol_next_lo:
            hi += 1; cum += vol_hist[hi]
        else:
            lo -= 1; cum += vol_hist[lo]
    return {
        'poc': centers[poc_idx], 'poc_idx': poc_idx,
        'vah': centers[hi], 'val': centers[lo],
        'value_area_pct': cum / total,
    }


def _vp_hvn_lvn_zones(centers: List[float], vol_hist: List[float], edges: List[float],
                       std_mult: float = 0.5) -> Tuple[list, list]:
    nz = [v for v in vol_hist if v > 0]
    if not nz:
        return [], []
    mean_v = vmean(nz)
    std_v = vstd(nz)
    hvn_thr = mean_v + std_mult * std_v
    lvn_thr = max(mean_v - std_mult * std_v, 0.0)
    n = len(vol_hist)
    hvn_zones, lvn_zones = [], []
    i = 0
    while i < n:
        if vol_hist[i] >= hvn_thr and vol_hist[i] > 0:
            j = i
            while j < n and vol_hist[j] >= hvn_thr:
                j += 1
            hvn_zones.append((edges[i], edges[j], sum(vol_hist[i:j])))
            i = j
        elif vol_hist[i] <= lvn_thr:
            j = i
            while j < n and vol_hist[j] <= lvn_thr:
                j += 1
            lvn_zones.append((edges[i], edges[j], sum(vol_hist[i:j])))
            i = j
        else:
            i += 1
    return hvn_zones, lvn_zones


def _vp_profile_shape(vol_hist: List[float]) -> str:
    n = len(vol_hist)
    if n < 6 or sum(vol_hist) <= 0:
        return "غير محدد"
    third = max(n // 3, 1)
    bottom = sum(vol_hist[:third])
    middle = sum(vol_hist[third:n - third])
    top = sum(vol_hist[n - third:])
    if middle >= bottom and middle >= top:
        return "D (متوازن — منطقة قيمة واضحة حول POC)"
    if top > bottom:
        return "P (ثقل الحجم أعلى — غالبًا بعد صعود وبناء قيمة أعلى)"
    return "b (ثقل الحجم أسفل — غالبًا بعد هبوط/تصفية وبناء قيمة أدنى)"


def _vp_nearest_zone(zones: list, price: float):
    below = [z for z in zones if z[1] <= price]
    above = [z for z in zones if z[0] >= price]
    inside = [z for z in zones if z[0] <= price <= z[1]]
    nearest_below = max(below, key=lambda z: z[1]) if below else None
    nearest_above = min(above, key=lambda z: z[0]) if above else None
    return nearest_below, nearest_above, bool(inside)


_VP_NOT_COMPUTED = object()


def compute_volume_profile(bars: Bars) -> Optional[dict]:
    # تخزين مؤقت على مستوى نفس كائن Bars: بروفايل الحجم بيتحسب مرة واحدة بس
    # لكل شمعات، مش في كل مرة يُستدعى فيها (كان بيتحسب 4 مرات منفصلة لكل فريم —
    # مرة لكل مؤشر من مؤشرات Volume Profile الأربعة — رغم إنه نفس الحساب بالظبط).
    # الكاش مربوط بكائن Bars نفسه (مش عام/مشترك)، فمفيش أي خطر تسريب بيانات بين
    # فحوصات مختلفة أو فريمات مختلفة — كل Bars جديد بيتعمل له من الصفر.
    cached = getattr(bars, '_vp_cache', _VP_NOT_COMPUTED)
    if cached is not _VP_NOT_COMPUTED:
        return cached

    lookback = min(I.vp_lookback_bars, len(bars))
    if lookback < 30:
        bars._vp_cache = None
        return None
    edges, centers, vol_hist = _vp_build_histogram(bars, lookback, I.vp_bins)
    va = _vp_value_area(centers, vol_hist, I.vp_value_area_pct)
    if va is None:
        bars._vp_cache = None
        return None
    hvn_zones, lvn_zones = _vp_hvn_lvn_zones(centers, vol_hist, edges, I.vp_hvn_lvn_std_mult)
    shape = _vp_profile_shape(vol_hist)

    price = bars['close'][-1]
    close = bars['close']; high = bars['high']; low = bars['low']; vol = bars['volume']

    half = lookback // 2
    older = bars.slice(-lookback, -half)
    newer = bars.slice(-half, None)
    poc_prev = poc_curr = va['poc']
    if len(older) >= 10:
        _, c_o, v_o = _vp_build_histogram(older, len(older), I.vp_bins)
        va_o = _vp_value_area(c_o, v_o, I.vp_value_area_pct)
        if va_o: poc_prev = va_o['poc']
    if len(newer) >= 10:
        _, c_n, v_n = _vp_build_histogram(newer, len(newer), I.vp_bins)
        va_n = _vp_value_area(c_n, v_n, I.vp_value_area_pct)
        if va_n: poc_curr = va_n['poc']
    poc_rising = poc_curr > poc_prev
    poc_falling = poc_curr < poc_prev

    k = min(I.vp_acceptance_bars, len(bars))
    recent_close = close[-k:]; recent_high = high[-k:]; recent_low = low[-k:]
    acceptance_above_vah = bool(sum(1 for v in recent_close if v > va['vah']) >= max(k - 1, 1) and price > va['vah'])
    rejection_from_vah = bool(any(v > va['vah'] for v in recent_high) and price < va['vah'])
    acceptance_below_val = bool(sum(1 for v in recent_close if v < va['val']) >= max(k - 1, 1) and price < va['val'])
    rejection_from_val = bool(any(v < va['val'] for v in recent_low) and price > va['val'])

    vol_avg = vmean(vol[-lookback:-1]) if lookback > 1 else vol[-1]
    volume_rising = bool(vol_avg > 0 and vol[-1] >= vol_avg)

    hvn_below, hvn_above, inside_hvn = _vp_nearest_zone(hvn_zones, price)
    lvn_below, lvn_above, inside_lvn = _vp_nearest_zone(lvn_zones, price)

    lvn_breakout_dir = None
    lb = min(I.vp_lvn_breakout_lookback, len(bars) - 1)
    if lb > 0:
        past_price = close[-1 - lb]
        for (zlo, zhi, _zv) in lvn_zones:
            if past_price < zlo and price > zhi:
                lvn_breakout_dir = 'up'; break
            if past_price > zhi and price < zlo:
                lvn_breakout_dir = 'down'; break

    score = 0.0
    components = []

    if price > va['poc']:
        score += 15; components.append("السعر فوق POC (+15)")
    elif price < va['poc']:
        score -= 15; components.append("السعر تحت POC (-15)")

    if poc_rising:
        score += 20; components.append("POC صاعد (+20)")
    elif poc_falling:
        score -= 20; components.append("POC هابط (-20)")

    if rejection_from_vah:
        score -= 20; components.append("رفض من VAH بعد اختراقه (-20)")
    elif acceptance_above_vah:
        score += 35; components.append("قبول فوق VAH (Acceptance) (+35)")
    elif price > va['vah']:
        score += 15; components.append("السعر فوق VAH بدون تأكيد قبول كامل بعد (+15)")

    if rejection_from_val:
        score += 20; components.append("رفض من VAL بعد كسره (+20)")
    elif acceptance_below_val:
        score -= 35; components.append("قبول تحت VAL (Acceptance) (-35)")
    elif price < va['val']:
        score -= 15; components.append("السعر تحت VAL بدون تأكيد قبول كامل بعد (-15)")

    if volume_rising:
        if score > 0:
            score += 10; components.append("حجم أعلى من المتوسط يؤكد الميل الصاعد الحالي (+10)")
        elif score < 0:
            score -= 10; components.append("حجم أعلى من المتوسط يؤكد الميل الهابط الحالي (-10)")

    if inside_hvn:
        components.append("السعر داخل منطقة HVN حاليًا — تماسك بلا وزن اتجاهي")
    elif hvn_below is not None and (hvn_above is None or (price - hvn_below[1]) <= (hvn_above[0] - price)):
        score += 10; components.append(f"أقرب HVN تحت السعر [{hvn_below[0]:.2f}-{hvn_below[1]:.2f}] يعمل كدعم (+10)")
    elif hvn_above is not None:
        score -= 10; components.append(f"أقرب HVN فوق السعر [{hvn_above[0]:.2f}-{hvn_above[1]:.2f}] يعمل كمقاومة (-10)")

    if lvn_breakout_dir == 'up':
        score += 5; components.append("اختراق منطقة LVN صعودًا مؤخرًا — حركة سريعة (+5)")
    elif lvn_breakout_dir == 'down':
        score -= 5; components.append("اختراق منطقة LVN هبوطًا مؤخرًا — حركة سريعة (-5)")

    score = clip(score, -100.0, 100.0)

    result = {
        'price': price, 'poc': va['poc'], 'vah': va['vah'], 'val': va['val'],
        'value_area_pct': va['value_area_pct'],
        'poc_prev': poc_prev, 'poc_curr': poc_curr, 'poc_rising': poc_rising, 'poc_falling': poc_falling,
        'hvn_zones': hvn_zones, 'lvn_zones': lvn_zones, 'shape': shape,
        'acceptance_above_vah': acceptance_above_vah, 'rejection_from_vah': rejection_from_vah,
        'acceptance_below_val': acceptance_below_val, 'rejection_from_val': rejection_from_val,
        'volume_rising': volume_rising,
        'hvn_below': hvn_below, 'hvn_above': hvn_above, 'inside_hvn': inside_hvn,
        'lvn_below': lvn_below, 'lvn_above': lvn_above, 'inside_lvn': inside_lvn,
        'lvn_breakout_dir': lvn_breakout_dir,
        'bias_score_signed': score, 'components': components,
    }
    bars._vp_cache = result
    return result


# ============================================================
# 4) الدعم/المقاومة + تحليل الفريم العام
# ============================================================
def _round_levels(price: float, step: float):
    if not step or step <= 0:
        return None, None
    above = math.ceil(price / step) * step
    below = math.floor(price / step) * step
    if above <= price:
        above += step
    if below >= price:
        below -= step
    return float(above), float(below)


def _dedupe_levels(levels: List[float], tol_abs: float) -> List[float]:
    if not levels:
        return []
    levels = sorted(levels)
    merged = [levels[0]]
    for lv in levels[1:]:
        if abs(lv - merged[-1]) > tol_abs:
            merged.append(lv)
    return merged


def support_resistance(bars: Bars, lookback: int, wing: int, round_step: float = None) -> dict:
    if round_step is None:
        round_step = I.sr_round_step
    h = bars['high'][-lookback:]; l = bars['low'][-lookback:]
    price = bars['close'][-1]
    res_levels, sup_levels = [], []
    for i in range(wing, len(h) - wing):
        if h[i] == max(h[i - wing:i + wing + 1]):
            res_levels.append(h[i])
        if l[i] == min(l[i - wing:i + wing + 1]):
            sup_levels.append(l[i])

    round_res, round_sup = _round_levels(price, round_step)
    if round_res is not None:
        res_levels.append(round_res)
    if round_sup is not None:
        sup_levels.append(round_sup)

    res_levels = sorted(set(r for r in res_levels if r > price))
    sup_levels = sorted(set(s for s in sup_levels if s < price), reverse=True)

    tol = max(price * 0.0002, 0.05)
    res_levels = _dedupe_levels(res_levels, tol)
    sup_levels = sorted(_dedupe_levels(sorted(sup_levels), tol), reverse=True)

    nearest_res = res_levels[0] if res_levels else None
    nearest_sup = sup_levels[0] if sup_levels else None
    next_res = res_levels[1] if len(res_levels) > 1 else None
    next_sup = sup_levels[1] if len(sup_levels) > 1 else None

    return {
        'price': price,
        'nearest_res': nearest_res, 'next_res': next_res,
        'nearest_sup': nearest_sup, 'next_sup': next_sup,
        'round_res': round_res, 'round_sup': round_sup,
    }


def _trend_at(close: List[float], ma_v: List[float], i: int, lag: int = 5) -> Optional[str]:
    if i < lag or isnan(ma_v[i]) or isnan(ma_v[i - lag]):
        return None
    above_ma = close[i] > ma_v[i]
    ma_slope_up = ma_v[i] > ma_v[i - lag]
    if above_ma and ma_slope_up:
        return "up"
    if (not above_ma) and (not ma_slope_up):
        return "down"
    if above_ma and not ma_slope_up:
        return "up_weak"
    return "down_weak"


_PULLBACK_AR = {
    'none': 'بلا تصحيح واضح (السعر لسه بيعمل قمم/قيعان جديدة مع الاتجاه)',
    'shallow': 'ضحل', 'medium': 'متوسط',
    'deep': 'عميق', 'break': 'كسر بنية (تجاوز كامل الحركة السابقة)',
    'unknown': 'غير محدد (بيانات غير كافية)',
}


def _pivot_idx_hl(h: List[float], l: List[float], wing: int):
    """إرجاع indices القمم المحلية (من مصفوفة القمم h) وindices القيعان
    المحلية (من مصفوفة القيعان l) — نفس منطق الفراكتال البسيط (wing bars
    على كل جانب) المستخدم أصلاً في support_resistance/ind_fractals."""
    n = len(h)
    highs_idx, lows_idx = [], []
    for i in range(wing, n - wing):
        if h[i] == max(h[i - wing:i + wing + 1]):
            highs_idx.append(i)
        if l[i] == min(l[i - wing:i + wing + 1]):
            lows_idx.append(i)
    return highs_idx, lows_idx


def classify_pullback_depth(htf_bars: Bars, direction: str, wing: int = 3, lookback: int = 200) -> dict:
    """
    يقيس عمق آخر ارتداد/تصحيح يحصل عكس الاتجاه العام — على نفس فريم الاتجاه
    العام نفسه (مثلاً 4 ساعات)، مش على الفريمات القصيرة — باستخدام نسب
    فيبوناتشي القياسية لتصنيف عمق التصحيح الحالي مقارنة بآخر اندفاعة (impulse)
    كاملة في اتجاه الترند العام:

        retracement < 38.2%   → ضحل   (shallow) : غالبًا مجرد ضجيج طبيعي داخل
                                                    الاتجاه، مش تصحيح حقيقي يستاهل تداول عكسي
        38.2% - 61.8%          → متوسط (medium)
        61.8% - 100%           → عميق  (deep)
        > 100%                 → كسر بنية (break): السعر تجاوز بداية الاندفاعة
                                   نفسها، يعني الاتجاه العام بقى مشكوك فيه أصلاً

    الهدف من الدالة: التفرقة بين "ضجيج قصير المدى" و"تصحيح حقيقي" يمكن قبول
    صفقة عكس الاتجاه العام فيه لكن بحذر شديد (هدفين بس، بدون هدف ثالث بعيد)
    بدل رفض أي صفقة عكس الاتجاه العام رفضًا تامًا كما كان يحدث سابقًا.
    """
    h = htf_bars['high'][-lookback:]
    l = htf_bars['low'][-lookback:]
    c = htf_bars['close'][-lookback:]
    n = len(c)
    empty = {'available': False, 'category': 'unknown', 'retracement_pct': None,
             'swing_high': None, 'swing_low': None}
    if n < wing * 2 + 10:
        return empty

    highs_idx, lows_idx = _pivot_idx_hl(h, l, wing)
    price = c[-1]

    # ملاحظة قسوة الاختبار: على بيانات ناعمة جدًا شبه خط مستقيم (نادر في بيانات
    # سوق حقيقية لكن ممكن يحصل)، مفيش قمة/قاع محلي "مؤكد" (بـwing شمعة من كل
    # جانب) عند بداية الاندفاعة نفسها. بدل ما نرجّع 'unknown' في الحالة دي،
    # نستخدم أبسط وأقوى بديل: أعلى قمة فعلية بالكامل + أدنى قاع فعلي قبلها
    # (أو العكس للهابط) — نفس فكرة قياس فيبوناتشي القياسية بدون اشتراط تأكيد فراكتالي.
    if direction == 'up':
        last_high_i = highs_idx[-1] if highs_idx else None
        lows_before = [i for i in lows_idx if last_high_i is None or i < last_high_i] if lows_idx else []
        if last_high_i is not None and lows_before:
            last_low_i = lows_before[-1]
            swing_low, swing_high = l[last_low_i], h[last_high_i]
        else:
            hi_idx = max(range(n), key=lambda i: h[i])
            if hi_idx == 0:
                return empty
            lo_idx = min(range(hi_idx), key=lambda i: l[i])
            swing_low, swing_high = l[lo_idx], h[hi_idx]
        rng = swing_high - swing_low
        if rng <= 0:
            return empty
        retr = (swing_high - price) / rng * 100.0
    elif direction == 'down':
        last_low_i = lows_idx[-1] if lows_idx else None
        highs_before = [i for i in highs_idx if last_low_i is None or i < last_low_i] if highs_idx else []
        if last_low_i is not None and highs_before:
            last_high_i = highs_before[-1]
            swing_low, swing_high = l[last_low_i], h[last_high_i]
        else:
            lo_idx = min(range(n), key=lambda i: l[i])
            if lo_idx == 0:
                return empty
            hi_idx = max(range(lo_idx), key=lambda i: h[i])
            swing_low, swing_high = l[lo_idx], h[hi_idx]
        rng = swing_high - swing_low
        if rng <= 0:
            return empty
        retr = (price - swing_low) / rng * 100.0
    else:
        return empty

    if retr < 0:
        # السعر لسه بيعمل قمم/قيعان جديدة في اتجاه الترند العام — مفيش تصحيح فعليًا
        retr = 0.0
        category = 'none'
    elif retr < 38.2:
        category = 'shallow'
    elif retr <= 61.8:
        category = 'medium'
    elif retr <= 100.0:
        category = 'deep'
    else:
        category = 'break'

    return {'available': True, 'category': category, 'retracement_pct': retr,
            'swing_high': swing_high, 'swing_low': swing_low}


def analyze_timeframe(bars: Bars, tf_label: str) -> dict:
    if len(bars) == 0:
        raise ValueError(f"analyze_timeframe: بيانات فريم {tf_label} فاضية تمامًا (0 شمعة) — لا يمكن التحليل")
    close = bars['close']; high = bars['high']; low = bars['low']
    vol = bars['volume'] if 'volume' in bars.data else None
    vol_is_proxy = getattr(bars, 'volume_is_proxy', False)
    n = len(close)

    ma = sma(close, I.sma_period)
    ma50 = sma(close, 50)
    ma200 = sma(close, 200)
    rsi_v = rsi_wilder(close, I.rsi_period)
    macd_line, macd_sig, macd_hist = macd(close, I.macd_fast, I.macd_slow, I.macd_signal)
    atr_v = atr_wilder(high, low, close, 14)
    adx_v, plus_di_v, minus_di_v = dmi_adx_wilder(high, low, close, I.adx_period)

    price = close[-1]
    rsi_last = rsi_v[-1] if not isnan(rsi_v[-1]) else None
    macd_last = macd_line[-1] if not isnan(macd_line[-1]) else None
    macd_sig_last = macd_sig[-1] if not isnan(macd_sig[-1]) else None
    macd_hist_last = macd_hist[-1] if not isnan(macd_hist[-1]) else None
    atr_last = atr_v[-1] if not isnan(atr_v[-1]) else vstd(close[-20:])
    adx_last = adx_v[-1] if not isnan(adx_v[-1]) else None
    plus_di_last = plus_di_v[-1] if not isnan(plus_di_v[-1]) else None
    minus_di_last = minus_di_v[-1] if not isnan(minus_di_v[-1]) else None
    trending_market = (adx_last is None) or (adx_last >= I.adx_trend_min)

    vol_avg_bars = bars_for_minutes(I.volume_avg_minutes, tf_label)
    volume_confirmed = True
    vol_avg = None
    if vol is not None and not vol_is_proxy and n >= vol_avg_bars + 1:
        vol_avg = vmean(vol[-vol_avg_bars - 1:-1])
        vol_last = vol[-1]
        volume_confirmed = vol_avg <= 0 or vol_last >= vol_avg * I.volume_confirm_mult

    trend = _trend_at(close, ma, n - 1) or "flat"

    macd_mom = "flat"
    if macd_last is not None and macd_sig_last is not None:
        if macd_last < 0 and macd_hist_last is not None and macd_hist_last > 0:
            macd_mom = "bear_slowing"
        elif macd_last > 0 and macd_hist_last is not None and macd_hist_last < 0:
            macd_mom = "bull_slowing"
        elif macd_last < 0:
            macd_mom = "bear"
        elif macd_last > 0:
            macd_mom = "bull"

    rsi_zone = "neutral"
    if rsi_last is not None:
        if rsi_last >= I.rsi_overbought: rsi_zone = "overbought"
        elif rsi_last <= I.rsi_oversold: rsi_zone = "oversold"
        elif rsi_last < 45: rsi_zone = "weak"
        elif rsi_last > 55: rsi_zone = "strong"

    sr_lookback_bars = bars_for_minutes(I.sr_lookback_minutes, tf_label,
                                         min_bars=I.sr_pivot_wing * 2 + 5)
    sr = support_resistance(bars, sr_lookback_bars, I.sr_pivot_wing)

    k = min(bars_for_minutes(TC.swing_lookback_minutes, tf_label), n)
    recent_low = min(low[-k:])
    recent_high = max(high[-k:])

    return {
        'tf': tf_label, 'price': price,
        'sma': ma[-1] if not isnan(ma[-1]) else None, 'trend': trend,
        'sma50': ma50[-1] if not isnan(ma50[-1]) else None,
        'sma200': ma200[-1] if not isnan(ma200[-1]) else None,
        'rsi': rsi_last, 'rsi_zone': rsi_zone,
        'macd': macd_last, 'macd_signal': macd_sig_last,
        'macd_hist': macd_hist_last, 'macd_mom': macd_mom,
        'atr': atr_last, 'sr': sr,
        'adx': adx_last, 'plus_di': plus_di_last, 'minus_di': minus_di_last,
        'trending_market': trending_market,
        'volume_last': vol[-1] if vol is not None else None,
        'volume_avg': vol_avg, 'volume_confirmed': volume_confirmed,
        'volume_is_proxy': vol_is_proxy,
        'recent_low': recent_low, 'recent_high': recent_high,
    }


# ============================================================
# 5) مجلس المؤشرات (تصويت)
# ============================================================
@dataclass
class IndicatorVote:
    name: str
    category: str
    score: Optional[float]
    kind: str
    note: str = ""
    voted: bool = True


def ind_adx_dmi(bars: Bars) -> IndicatorVote:
    h, l, c = bars['high'], bars['low'], bars['close']
    if len(c) < I.adx_period * 2 + 5:
        return IndicatorVote("ADX / DMI", "اتجاه", None, "حقيقي")
    _, plus_di_v, minus_di_v = dmi_adx_wilder(h, l, c, I.adx_period)
    plus_di, minus_di = plus_di_v[-1], minus_di_v[-1]
    if isnan(plus_di) or isnan(minus_di) or (plus_di + minus_di) == 0:
        return IndicatorVote("ADX / DMI", "اتجاه", 50.0, "حقيقي", "بيانات غير كافية لحساب DI")
    score = 50.0 + 50.0 * (plus_di - minus_di) / (plus_di + minus_di)
    return IndicatorVote("ADX / DMI", "اتجاه", _clip01_100(score), "حقيقي",
                          f"+DI={plus_di:.1f} -DI={minus_di:.1f}")


def ind_bollinger(bars: Bars) -> IndicatorVote:
    c = bars['close']
    if len(c) < 21:
        return IndicatorVote("Bollinger Bands", "اتجاه", None, "حقيقي")
    upper, mid, lower = bollinger_bands(c, 20, 2.0)
    u, lo = upper[-1], lower[-1]
    if isnan(u) or isnan(lo) or u == lo:
        return IndicatorVote("Bollinger Bands", "اتجاه", 50.0, "حقيقي")
    pctb = (c[-1] - lo) / (u - lo) * 100.0
    return IndicatorVote("Bollinger Bands", "اتجاه", _clip01_100(pctb), "حقيقي", f"%B={pctb:.0f}%")


def ind_envelopes(bars: Bars) -> IndicatorVote:
    c = bars['close']; period = 20; dev = 0.001
    if len(c) < period:
        return IndicatorVote("Envelopes", "اتجاه", None, "حقيقي")
    ma = vmean(c[-period:])
    upper, lower = ma * (1 + dev), ma * (1 - dev)
    pct = (c[-1] - lower) / (upper - lower) * 100.0 if upper != lower else 50.0
    return IndicatorVote("Envelopes", "اتجاه", _clip01_100(pct), "حقيقي")


def ind_ichimoku(bars: Bars) -> IndicatorVote:
    h, l, c = bars['high'], bars['low'], bars['close']
    n = len(c)
    if n < 52 + 26:
        return IndicatorVote("Ichimoku Kinko Hyo", "اتجاه", None, "حقيقي")

    def mid(period, end_idx):
        seg_h = h[end_idx - period + 1: end_idx + 1]
        seg_l = l[end_idx - period + 1: end_idx + 1]
        return (max(seg_h) + min(seg_l)) / 2.0

    tenkan = mid(9, n - 1)
    kijun = mid(26, n - 1)
    shift_idx = n - 1 - 26
    tenkan_26ago = mid(9, shift_idx)
    kijun_26ago = mid(26, shift_idx)
    senkou_a = (tenkan_26ago + kijun_26ago) / 2.0
    senkou_b = mid(52, shift_idx)

    price = c[-1]
    cloud_top, cloud_bot = max(senkou_a, senkou_b), min(senkou_a, senkou_b)
    score = 50.0
    if price > cloud_top: score += 25
    elif price < cloud_bot: score -= 25
    if tenkan > kijun: score += 15
    elif tenkan < kijun: score -= 15
    if senkou_a > senkou_b: score += 10
    elif senkou_a < senkou_b: score -= 10
    return IndicatorVote("Ichimoku Kinko Hyo", "اتجاه", _clip01_100(score), "حقيقي")


def ind_moving_average(bars: Bars) -> IndicatorVote:
    c, h, l = bars['close'], bars['high'], bars['low']
    period = 20
    if len(c) < period + 14:
        return IndicatorVote("Moving Average", "اتجاه", None, "حقيقي")
    ma = vmean(c[-period:])
    atr_v = atr_wilder(h, l, c, 14)
    atr_last = atr_v[-1] if not isnan(atr_v[-1]) else vstd(c[-20:])
    if atr_last <= 0:
        return IndicatorVote("Moving Average", "اتجاه", 50.0, "حقيقي")
    z = (c[-1] - ma) / atr_last
    score = 50.0 + 25.0 * math.tanh(z)
    return IndicatorVote("Moving Average", "اتجاه", _clip01_100(score), "حقيقي")


def ind_parabolic_sar(bars: Bars) -> IndicatorVote:
    h, l, c = bars['high'], bars['low'], bars['close']
    if len(c) < 10:
        return IndicatorVote("Parabolic SAR", "اتجاه", None, "حقيقي")
    sar = parabolic_sar_series(h, l)
    uptrend = c[-1] >= sar[-1]
    atr_v = atr_wilder(h, l, c, 14)
    atr_last = atr_v[-1] if not isnan(atr_v[-1]) else vstd(c[-20:])
    dist = (c[-1] - sar[-1]) / atr_last if atr_last > 0 else (1 if uptrend else -1)
    score = 50.0 + 25.0 * math.tanh(dist)
    return IndicatorVote("Parabolic SAR", "اتجاه", _clip01_100(score), "حقيقي",
                          f"{'فوق' if uptrend else 'تحت'} SAR")


def ind_standard_deviation(bars: Bars) -> IndicatorVote:
    c = bars['close']
    if len(c) < 20:
        return IndicatorVote("Standard Deviation", "اتجاه", None, "بروكسي", voted=False)
    slope = _linreg_slope(c[-20:])
    sd = vstd(c[-20:])
    z = slope / (sd + 1e-9)
    score = 50.0 + 30.0 * math.tanh(z * 5)
    return IndicatorVote("Standard Deviation", "اتجاه", _clip01_100(score), "بروكسي",
                          "المؤشر أصلاً بلا اتجاه — بروكسي عبر ميل الانحدار الخطي", voted=False)


def ind_zigzag(bars: Bars) -> IndicatorVote:
    h, l = bars['high'], bars['low']
    n = len(h)
    wing = 3
    if n < wing * 2 + 5:
        return IndicatorVote("ZigZag", "اتجاه", None, "بروكسي", voted=False)
    pivots = []
    for i in range(wing, n - wing):
        if h[i] == max(h[i - wing:i + wing + 1]):
            pivots.append((i, h[i], 'H'))
        elif l[i] == min(l[i - wing:i + wing + 1]):
            pivots.append((i, l[i], 'L'))
    if len(pivots) < 2:
        return IndicatorVote("ZigZag", "اتجاه", 50.0, "بروكسي", "لا سيقان كافية", voted=False)
    last_two = pivots[-2:]
    up_leg = last_two[1][1] > last_two[0][1]
    score = 62.0 if up_leg else 38.0
    return IndicatorVote("ZigZag", "اتجاه", score, "بروكسي",
                          "أداة لاحقة/repainting — ثقة منخفضة مقصودة", voted=False)


def ind_atr(bars: Bars) -> IndicatorVote:
    h, l, c = bars['high'], bars['low'], bars['close']
    if len(c) < 35:
        return IndicatorVote("Average True Range", "مذبذبات", None, "بروكسي", voted=False)
    atr_v = atr_wilder(h, l, c, 14)
    if isnan(atr_v[-1]) or isnan(atr_v[-6]):
        return IndicatorVote("Average True Range", "مذبذبات", 50.0, "بروكسي", voted=False)
    expanding = atr_v[-1] > atr_v[-6]
    above_ma = c[-1] > vmean(c[-20:])
    score = 50.0 if not expanding else (62.0 if above_ma else 38.0)
    return IndicatorVote("Average True Range", "مذبذبات", score, "بروكسي",
                          "المؤشر أصلاً بلا اتجاه — بروكسي عبر تمدد ATR مع موقع السعر", voted=False)


def ind_bears_power(bars: Bars) -> IndicatorVote:
    c, l = bars['close'], bars['low']
    if len(c) < 13:
        return IndicatorVote("Bears Power", "مذبذبات", None, "حقيقي")
    ema13 = ema(c, 13)
    if isnan(ema13[-1]):
        return IndicatorVote("Bears Power", "مذبذبات", None, "حقيقي")
    bp = l[-1] - ema13[-1]
    atr_v = atr_wilder(bars['high'], l, c, 14)
    norm = bp / ((atr_v[-1] if not isnan(atr_v[-1]) else vstd(c[-20:])) + 1e-9)
    score = 50.0 + 25.0 * math.tanh(norm)
    return IndicatorVote("Bears Power", "مذبذبات", _clip01_100(score), "حقيقي")


def ind_bulls_power(bars: Bars) -> IndicatorVote:
    c, h = bars['close'], bars['high']
    if len(c) < 13:
        return IndicatorVote("Bulls Power", "مذبذبات", None, "حقيقي")
    ema13 = ema(c, 13)
    if isnan(ema13[-1]):
        return IndicatorVote("Bulls Power", "مذبذبات", None, "حقيقي")
    bup = h[-1] - ema13[-1]
    atr_v = atr_wilder(h, bars['low'], c, 14)
    norm = bup / ((atr_v[-1] if not isnan(atr_v[-1]) else vstd(c[-20:])) + 1e-9)
    score = 50.0 + 25.0 * math.tanh(norm)
    return IndicatorVote("Bulls Power", "مذبذبات", _clip01_100(score), "حقيقي")


def ind_cci(bars: Bars) -> IndicatorVote:
    h, l, c = bars['high'], bars['low'], bars['close']
    if len(c) < 20:
        return IndicatorVote("Commodity Channel Index", "مذبذبات", None, "حقيقي")
    cci_v = cci_series(h, l, c, 20)
    if isnan(cci_v[-1]):
        return IndicatorVote("Commodity Channel Index", "مذبذبات", 50.0, "حقيقي")
    score = 50.0 + 50.0 * math.tanh(cci_v[-1] / 200.0)
    return IndicatorVote("Commodity Channel Index", "مذبذبات", _clip01_100(score), "حقيقي",
                          f"CCI={cci_v[-1]:.0f}")


def ind_demarker(bars: Bars) -> IndicatorVote:
    h, l = bars['high'], bars['low']
    period = 14
    if len(h) < period + 1:
        return IndicatorVote("DeMarker", "مذبذبات", None, "حقيقي")
    demax = [h[i] - h[i - 1] if h[i] > h[i - 1] else 0.0 for i in range(1, len(h))][-period:]
    demin = [l[i - 1] - l[i] if l[i] < l[i - 1] else 0.0 for i in range(1, len(l))][-period:]
    s1, s2 = sum(demax), sum(demin)
    if s1 + s2 == 0:
        return IndicatorVote("DeMarker", "مذبذبات", 50.0, "حقيقي")
    dm = s1 / (s1 + s2) * 100.0
    return IndicatorVote("DeMarker", "مذبذبات", _clip01_100(dm), "حقيقي")


def ind_force_index(bars: Bars) -> IndicatorVote:
    c = bars['close']; vol = bars['volume']
    if len(c) < 14:
        return IndicatorVote("Force Index", "مذبذبات", None, "حقيقي")
    fi = [(c[i] - c[i - 1]) * vol[i] for i in range(1, len(c))]
    fi_ema = ema(fi, 13)
    if len(fi) < 14 or isnan(fi_ema[-1]):
        return IndicatorVote("Force Index", "مذبذبات", 50.0, "حقيقي")
    sd = vstd(fi[-30:]) if len(fi) >= 30 else vstd(fi) + 1e-9
    z = fi_ema[-1] / (sd + 1e-9)
    score = 50.0 + 30.0 * math.tanh(z)
    is_proxy_vol = getattr(bars, 'volume_is_proxy', False)
    note = "(الحجم بديل تقريبي — تم استبعاده من التصويت)" if is_proxy_vol else ""
    return IndicatorVote("Force Index", "مذبذبات", _clip01_100(score), "حقيقي", note, voted=not is_proxy_vol)


def ind_macd(bars: Bars) -> IndicatorVote:
    c = bars['close']
    if len(c) < 35:
        return IndicatorVote("MACD", "مذبذبات", None, "حقيقي")
    _, _, hist = macd(c, 12, 26, 9)
    valid = [v for v in hist if not isnan(v)]
    if len(valid) < 10 or isnan(hist[-1]):
        return IndicatorVote("MACD", "مذبذبات", 50.0, "حقيقي")
    sd = vstd(valid[-30:]) + 1e-9
    z = hist[-1] / sd
    score = 50.0 + 30.0 * math.tanh(z)
    return IndicatorVote("MACD", "مذبذبات", _clip01_100(score), "حقيقي")


def ind_momentum(bars: Bars) -> IndicatorVote:
    c = bars['close']; period = 10
    if len(c) < period + 1:
        return IndicatorVote("Momentum", "مذبذبات", None, "حقيقي")
    mom = c[-1] / c[-1 - period] * 100.0
    score = 50.0 + 25.0 * math.tanh((mom - 100.0) * 20)
    return IndicatorVote("Momentum", "مذبذبات", _clip01_100(score), "حقيقي", f"Momentum={mom:.2f}")


def ind_osma(bars: Bars) -> IndicatorVote:
    v = ind_macd(bars)
    return IndicatorVote("Moving Average of Oscillator", "مذبذبات", v.score, "حقيقي",
                          "ملاحظة: نفس قيمة هستوجرام MACD تمامًا حسب تعريف MT5")


def ind_rsi(bars: Bars) -> IndicatorVote:
    c = bars['close']
    if len(c) < 15:
        return IndicatorVote("Relative Strength Index", "مذبذبات", None, "حقيقي")
    r = rsi_wilder(c, 14)
    if isnan(r[-1]):
        return IndicatorVote("Relative Strength Index", "مذبذبات", None, "حقيقي")
    return IndicatorVote("Relative Strength Index", "مذبذبات", _clip01_100(r[-1]), "حقيقي")


def ind_rvi(bars: Bars) -> IndicatorVote:
    o, h, l, c = bars['open'], bars['high'], bars['low'], bars['close']
    period = 10
    if len(c) < period + 4:
        return IndicatorVote("Relative Vigor Index", "مذبذبات", None, "حقيقي")
    n = len(c)
    num = [0.0] * n
    den = [0.0] * n
    for i in range(n):
        i1 = max(i - 1, 0); i2 = max(i - 2, 0); i3 = max(i - 3, 0)
        num[i] = (c[i] - o[i]) + 2 * (c[i1] - o[i1]) + 2 * (c[i2] - o[i2]) + (c[i3] - o[i3])
        den[i] = (h[i] - l[i]) + 2 * (h[i1] - l[i1]) + 2 * (h[i2] - l[i2]) + (h[i3] - l[i3])
    num_sma = vmean(num[-period:]); den_sma = vmean(den[-period:])
    if den_sma == 0:
        return IndicatorVote("Relative Vigor Index", "مذبذبات", 50.0, "حقيقي")
    rvi = num_sma / den_sma
    score = 50.0 + 50.0 * math.tanh(rvi * 3)
    return IndicatorVote("Relative Vigor Index", "مذبذبات", _clip01_100(score), "حقيقي")


def ind_stochastic(bars: Bars) -> IndicatorVote:
    h, l, c = bars['high'], bars['low'], bars['close']
    period = 5
    if len(c) < period + 3:
        return IndicatorVote("Stochastic Oscillator", "مذبذبات", None, "حقيقي")
    hh, ll = max(h[-period:]), min(l[-period:])
    if hh == ll:
        return IndicatorVote("Stochastic Oscillator", "مذبذبات", 50.0, "حقيقي")
    k = (c[-1] - ll) / (hh - ll) * 100.0
    return IndicatorVote("Stochastic Oscillator", "مذبذبات", _clip01_100(k), "حقيقي", f"%K={k:.0f}")


def ind_williams_r(bars: Bars) -> IndicatorVote:
    h, l, c = bars['high'], bars['low'], bars['close']
    period = 14
    if len(c) < period:
        return IndicatorVote("Williams' Percent Range", "مذبذبات", None, "حقيقي")
    wpr_v = williams_r_series(h, l, c, period)
    if isnan(wpr_v[-1]):
        return IndicatorVote("Williams' Percent Range", "مذبذبات", 50.0, "حقيقي")
    return IndicatorVote("Williams' Percent Range", "مذبذبات", _clip01_100(100.0 + wpr_v[-1]), "حقيقي")


def ind_accum_dist(bars: Bars) -> IndicatorVote:
    h, l, c, vol = bars['high'], bars['low'], bars['close'], bars['volume']
    if len(c) < 22:
        return IndicatorVote("Accumulation/Distribution", "احجام", None, "حقيقي")
    n = len(c)
    ad = [0.0] * n
    acc = 0.0
    for i in range(n):
        rng = h[i] - l[i] if (h[i] - l[i]) != 0 else 1e-9
        mfm = ((c[i] - l[i]) - (h[i] - c[i])) / rng
        acc += mfm * vol[i]
        ad[i] = acc
    slope = _linreg_slope(ad[-20:])
    sd = vstd(ad[-20:]) + 1e-9
    score = 50.0 + 30.0 * math.tanh(slope / sd * 5)
    is_proxy_vol = getattr(bars, 'volume_is_proxy', False)
    note = "(الحجم بديل تقريبي — تم استبعاده من التصويت)" if is_proxy_vol else ""
    return IndicatorVote("Accumulation/Distribution", "احجام", _clip01_100(score), "حقيقي", note, voted=not is_proxy_vol)


def ind_market_profile(bars: Bars) -> IndicatorVote:
    c = bars['close']
    if len(c) < 30:
        return IndicatorVote("Market Profile", "احجام", None, "بروكسي", voted=False)
    window = c[-30:]
    rounded = [round(v * 2) / 2.0 for v in window]
    counts = {}
    for v in rounded:
        counts[v] = counts.get(v, 0) + 1
    poc = max(counts, key=lambda k: counts[k])
    spread = vstd(window) + 1e-9
    score = 50.0 + 30.0 * math.tanh((c[-1] - poc) / spread)
    return IndicatorVote("Market Profile", "احجام", _clip01_100(score), "بروكسي",
                          "بروكسي تقريبي (POC من توزيع الإغلاقات، مش بيانات tick حقيقية)", voted=False)


def ind_mfi(bars: Bars) -> IndicatorVote:
    h, l, c, vol = bars['high'], bars['low'], bars['close'], bars['volume']
    period = 14
    if len(c) < period + 1:
        return IndicatorVote("Money Flow Index", "احجام", None, "حقيقي")
    mfi_v = mfi_series(h, l, c, vol, period)
    is_proxy_vol = getattr(bars, 'volume_is_proxy', False)
    if isnan(mfi_v[-1]):
        return IndicatorVote("Money Flow Index", "احجام", 50.0, "حقيقي", voted=not is_proxy_vol)
    note = "(الحجم بديل تقريبي — تم استبعاده من التصويت)" if is_proxy_vol else ""
    return IndicatorVote("Money Flow Index", "احجام", _clip01_100(mfi_v[-1]), "حقيقي", note, voted=not is_proxy_vol)

# ============================================================
# ⚠️ هذا الملف (الجزء 2 من 2) استكمال مباشر لـ gold_pro_analyzer_part1.py
# يتضمن مؤشري الخوف والطمع وتدفق السيولة الجداد
# ادمج الاتنين بالأمر: cat gold_pro_analyzer_part1.py gold_pro_analyzer_part2.py > gold_pro_analyzer.py
# ثم: python3 gold_pro_analyzer.py cascade --symbol XAU/USD --provider twelvedata --live --poll 180
# ============================================================
def ind_obv(bars: Bars) -> IndicatorVote:
    c, vol = bars['close'], bars['volume']
    if len(c) < 22:
        return IndicatorVote("On Balance Volume", "احجام", None, "حقيقي")
    obv = obv_series(c, vol)
    slope = _linreg_slope(obv[-20:])
    sd = vstd(obv[-20:]) + 1e-9
    score = 50.0 + 30.0 * math.tanh(slope / sd * 5)
    is_proxy_vol = getattr(bars, 'volume_is_proxy', False)
    note = "(الحجم بديل تقريبي — تم استبعاده من التصويت)" if is_proxy_vol else ""
    return IndicatorVote("On Balance Volume", "احجام", _clip01_100(score), "حقيقي", note, voted=not is_proxy_vol)


def ind_volumes(bars: Bars) -> IndicatorVote:
    o, c, vol = bars['open'], bars['close'], bars['volume']
    if len(c) < 20:
        return IndicatorVote("Volumes", "احجام", None, "بروكسي")
    up_vol = sum(vol[i] for i in range(-20, 0) if c[i] >= o[i])
    total_vol = sum(vol[-20:]) + 1e-9
    score = up_vol / total_vol * 100.0
    note = "المؤشر أصلاً بلا اتجاه — بروكسي عبر نسبة حجم الشموع الصاعدة"
    if getattr(bars, 'volume_is_proxy', False):
        note += " (والحجم نفسه بديل تقريبي هون)"
    return IndicatorVote("Volumes", "احجام", _clip01_100(score), "بروكسي", note, voted=False)


def _alligator_lines(bars: Bars):
    h, l = bars['high'], bars['low']
    median = [(h[i] + l[i]) / 2.0 for i in range(len(h))]

    def smma(x, period):
        n = len(x); out = full_nan(n)
        if n < period: return out
        out[period - 1] = vmean(x[:period])
        for i in range(period, n):
            out[i] = (out[i - 1] * (period - 1) + x[i]) / period
        return out
    jaw, teeth, lips = smma(median, 13), smma(median, 8), smma(median, 5)
    return jaw, teeth, lips, median


def ind_accelerator_oscillator(bars: Bars) -> IndicatorVote:
    h, l = bars['high'], bars['low']
    median = [(h[i] + l[i]) / 2.0 for i in range(len(h))]
    if len(median) < 40:
        return IndicatorVote("Accelerator Oscillator", "بيل_وليامز", None, "حقيقي")
    ao = sma(median, 5)
    ao34 = sma(median, 34)
    ao_diff = [ao[i] - ao34[i] if not (isnan(ao[i]) or isnan(ao34[i])) else NAN for i in range(len(median))]
    ao_sma5 = sma(ao_diff, 5)
    ac = [ao_diff[i] - ao_sma5[i] if not (isnan(ao_diff[i]) or isnan(ao_sma5[i])) else NAN for i in range(len(median))]
    valid = [v for v in ac if not isnan(v)]
    if len(valid) < 5 or isnan(ac[-1]):
        return IndicatorVote("Accelerator Oscillator", "بيل_وليامز", 50.0, "حقيقي")
    sd = vstd(valid[-30:]) + 1e-9
    score = 50.0 + 35.0 * math.tanh(ac[-1] / sd)
    return IndicatorVote("Accelerator Oscillator", "بيل_وليامز", _clip01_100(score), "حقيقي")


def ind_alligator(bars: Bars) -> IndicatorVote:
    jaw, teeth, lips, median = _alligator_lines(bars)
    if isnan(jaw[-1]) or isnan(teeth[-1]) or isnan(lips[-1]):
        return IndicatorVote("Alligator", "بيل_وليامز", None, "حقيقي")
    price = median[-1]
    score = 50.0
    if lips[-1] > teeth[-1] > jaw[-1] and price > lips[-1]: score = 80.0
    elif lips[-1] < teeth[-1] < jaw[-1] and price < lips[-1]: score = 20.0
    elif lips[-1] > jaw[-1]: score = 62.0
    elif lips[-1] < jaw[-1]: score = 38.0
    return IndicatorVote("Alligator", "بيل_وليامز", score, "حقيقي")


def ind_awesome_oscillator(bars: Bars) -> IndicatorVote:
    h, l = bars['high'], bars['low']
    median = [(h[i] + l[i]) / 2.0 for i in range(len(h))]
    if len(median) < 40:
        return IndicatorVote("Awesome Oscillator", "بيل_وليامز", None, "حقيقي")
    ao5 = sma(median, 5); ao34 = sma(median, 34)
    ao = [ao5[i] - ao34[i] if not (isnan(ao5[i]) or isnan(ao34[i])) else NAN for i in range(len(median))]
    valid = [v for v in ao if not isnan(v)]
    if len(valid) < 5 or isnan(ao[-1]):
        return IndicatorVote("Awesome Oscillator", "بيل_وليامز", 50.0, "حقيقي")
    sd = vstd(valid[-30:]) + 1e-9
    score = 50.0 + 35.0 * math.tanh(ao[-1] / sd)
    return IndicatorVote("Awesome Oscillator", "بيل_وليامز", _clip01_100(score), "حقيقي")


def ind_fractals(bars: Bars) -> IndicatorVote:
    h, l = bars['high'], bars['low']
    n = len(h); wing = 2
    if n < wing * 2 + 5:
        return IndicatorVote("Fractals", "بيل_وليامز", None, "بروكسي")
    last_up_fr = last_dn_fr = None
    for i in range(n - wing - 1, wing - 1, -1):
        if last_up_fr is None and h[i] == max(h[i - wing:i + wing + 1]):
            last_up_fr = h[i]
        if last_dn_fr is None and l[i] == min(l[i - wing:i + wing + 1]):
            last_dn_fr = l[i]
        if last_up_fr is not None and last_dn_fr is not None:
            break
    price = h[-1]
    if last_up_fr is not None and price > last_up_fr:
        return IndicatorVote("Fractals", "بيل_وليامز", 68.0, "بروكسي", "كسر آخر فراكتال علوي")
    if last_dn_fr is not None and l[-1] < last_dn_fr:
        return IndicatorVote("Fractals", "بيل_وليامز", 32.0, "بروكسي", "كسر آخر فراكتال سفلي")
    return IndicatorVote("Fractals", "بيل_وليامز", 50.0, "بروكسي", "لا كسر فراكتال حديث")


def ind_gator_oscillator(bars: Bars) -> IndicatorVote:
    jaw, teeth, lips, median = _alligator_lines(bars)
    if isnan(jaw[-1]) or isnan(teeth[-1]) or isnan(lips[-1]):
        return IndicatorVote("Gator Oscillator", "بيل_وليامز", None, "بروكسي", voted=False)
    spread = abs(lips[-1] - teeth[-1]) + abs(teeth[-1] - jaw[-1])
    atr_v = atr_wilder(bars['high'], bars['low'], bars['close'], 14)
    atr_last = atr_v[-1] if not isnan(atr_v[-1]) else vstd(bars['close'][-20:]) + 1e-9
    confidence = min(spread / (atr_last + 1e-9), 1.0)
    bullish = lips[-1] > jaw[-1]
    score = 50.0 + (30.0 * confidence if bullish else -30.0 * confidence)
    return IndicatorVote("Gator Oscillator", "بيل_وليامز", _clip01_100(score), "بروكسي",
                          "لا اتجاه مستقل أصلاً — بروكسي عبر اتجاه Alligator موزون بمقدار التباعد", voted=False)


def ind_market_facilitation_index(bars: Bars) -> IndicatorVote:
    h, l, c, o, vol = bars['high'], bars['low'], bars['close'], bars['open'], bars['volume']
    if len(c) < 3:
        return IndicatorVote("Market Facilitation Index", "بيل_وليامز", None, "بروكسي", voted=False)
    mfi_bw = [(h[i] - l[i]) / (vol[i] if vol[i] != 0 else 1e-9) for i in range(len(c))]
    mfi_up = mfi_bw[-1] > mfi_bw[-2]
    vol_up = vol[-1] > vol[-2]
    green_zone = mfi_up and vol_up
    bull_candle = c[-1] >= o[-1]
    confidence = 30.0 if green_zone else 12.0
    score = 50.0 + (confidence if bull_candle else -confidence)
    note = "لا اتجاه مستقل أصلاً — بروكسي عبر اتجاه الشمعة موزون بمنطقة BW-MFI"
    if getattr(bars, 'volume_is_proxy', False):
        note += " (والحجم بديل تقريبي)"
    return IndicatorVote("Market Facilitation Index", "بيل_وليامز", _clip01_100(score), "بروكسي", note, voted=False)


def _vp_zone_txt(z) -> str:
    return f"{z[0]:.2f}-{z[1]:.2f}" if z else "—"


def ind_volume_profile_poc(bars: Bars) -> IndicatorVote:
    vp = compute_volume_profile(bars)
    if vp is None:
        return IndicatorVote("Volume Profile — POC", "بروفايل الحجم", None, "بروكسي", voted=False)
    price_vs_poc = "فوق" if vp['price'] > vp['poc'] else ("تحت" if vp['price'] < vp['poc'] else "عند")
    migration = "صاعد" if vp['poc_rising'] else ("هابط" if vp['poc_falling'] else "شبه ثابت")
    score = 50.0
    if vp['price'] > vp['poc']: score += 15
    elif vp['price'] < vp['poc']: score -= 15
    if vp['poc_rising']: score += 20
    elif vp['poc_falling']: score -= 20
    note = (f"POC={vp['poc']:.2f} | السعر {price_vs_poc} الـPOC | انتقال POC: {migration} "
            f"({vp['poc_prev']:.2f} → {vp['poc_curr']:.2f})")
    if getattr(bars, 'volume_is_proxy', False):
        note += " | ⚠️ الحجم بديل تقريبي"
    return IndicatorVote("Volume Profile — POC", "بروفايل الحجم", _clip01_100(score), "حقيقي", note, voted=False)


def ind_volume_profile_value_area(bars: Bars) -> IndicatorVote:
    vp = compute_volume_profile(bars)
    if vp is None:
        return IndicatorVote("Volume Profile — Value Area (VAH/VAL)", "بروفايل الحجم", None, "بروكسي", voted=False)
    if vp['rejection_from_vah']:
        status, score = "رفض من VAH بعد اختراقه (احتمال ارتداد هبوطي)", 30.0
    elif vp['acceptance_above_vah']:
        status, score = "قبول فوق VAH (Acceptance — استمرار صعودي محتمل)", 85.0
    elif vp['price'] > vp['vah']:
        status, score = "فوق VAH لكن بدون تأكيد قبول كامل بعد", 62.0
    elif vp['rejection_from_val']:
        status, score = "رفض من VAL بعد كسره (احتمال ارتداد صعودي)", 70.0
    elif vp['acceptance_below_val']:
        status, score = "قبول تحت VAL (Acceptance — استمرار هبوطي محتمل)", 15.0
    elif vp['price'] < vp['val']:
        status, score = "تحت VAL لكن بدون تأكيد قبول كامل بعد", 38.0
    else:
        status, score = "داخل منطقة القيمة (توازن)", 50.0
    note = (f"VAH={vp['vah']:.2f} | VAL={vp['val']:.2f} | تغطية منطقة القيمة {vp['value_area_pct']:.0%} "
            f"| الحالة: {status}")
    if getattr(bars, 'volume_is_proxy', False):
        note += " | ⚠️ الحجم بديل تقريبي"
    return IndicatorVote("Volume Profile — Value Area (VAH/VAL)", "بروفايل الحجم",
                          _clip01_100(score), "حقيقي", note, voted=False)


def ind_volume_profile_hvn_lvn(bars: Bars) -> IndicatorVote:
    vp = compute_volume_profile(bars)
    if vp is None:
        return IndicatorVote("Volume Profile — HVN/LVN", "بروفايل الحجم", None, "بروكسي", voted=False)
    score = 50.0
    notes = []
    if vp['inside_hvn']:
        notes.append("السعر داخل منطقة HVN حاليًا (تماسك)")
    elif vp['hvn_below'] is not None and (vp['hvn_above'] is None or
                                           (vp['price'] - vp['hvn_below'][1]) <= (vp['hvn_above'][0] - vp['price'])):
        score += 10; notes.append(f"أقرب HVN تحت السعر [{_vp_zone_txt(vp['hvn_below'])}] يعمل كدعم")
    elif vp['hvn_above'] is not None:
        score -= 10; notes.append(f"أقرب HVN فوق السعر [{_vp_zone_txt(vp['hvn_above'])}] يعمل كمقاومة")
    if vp['lvn_breakout_dir'] == 'up':
        score += 5; notes.append("اختراق LVN صعودًا مؤخرًا (حركة سريعة)")
    elif vp['lvn_breakout_dir'] == 'down':
        score -= 5; notes.append("اختراق LVN هبوطًا مؤخرًا (حركة سريعة)")
    hvn_txt = ", ".join(_vp_zone_txt(z) for z in vp['hvn_zones'][:3]) or "—"
    lvn_txt = ", ".join(_vp_zone_txt(z) for z in vp['lvn_zones'][:3]) or "—"
    note = f"مناطق HVN: {hvn_txt} | مناطق LVN: {lvn_txt}"
    if notes:
        note += " | " + " ؛ ".join(notes)
    if getattr(bars, 'volume_is_proxy', False):
        note += " | ⚠️ الحجم بديل تقريبي"
    return IndicatorVote("Volume Profile — HVN/LVN", "بروفايل الحجم", _clip01_100(score), "حقيقي", note, voted=False)


def ind_volume_profile_bias(bars: Bars) -> IndicatorVote:
    vp = compute_volume_profile(bars)
    if vp is None:
        return IndicatorVote("Volume Profile — BIAS الشامل", "بروفايل الحجم", None, "بروكسي")
    score = _clip01_100((vp['bias_score_signed'] + 100.0) / 2.0)
    is_proxy_vol = getattr(bars, 'volume_is_proxy', False)
    note = (f"POC={vp['poc']:.2f} VAH={vp['vah']:.2f} VAL={vp['val']:.2f} | الشكل: {vp['shape']} | "
            f"BIAS خام={vp['bias_score_signed']:+.0f}/100 | " + " ؛ ".join(vp['components']))
    if is_proxy_vol:
        note += " | ⚠️ (الحجم بديل تقريبي — تم استبعاد البروفايل بالكامل من التصويت)"
    return IndicatorVote("Volume Profile — BIAS الشامل", "بروفايل الحجم", score, "حقيقي", note,
                          voted=not is_proxy_vol)


COUNCIL_GROUPS = [
    ("نطاق التقلب (Bollinger+Envelopes)", "اتجاه", ["Bollinger Bands", "Envelopes"]),
    ("MACD / OsMA (نفس القيمة فعليًا)", "مذبذبات", ["MACD", "Moving Average of Oscillator"]),
    ("زخم بيل وليامز (AO+AC)", "بيل_وليامز", ["Awesome Oscillator", "Accelerator Oscillator"]),
    ("ضغط المشترين/البائعين (Bulls+Bears Power)", "مذبذبات", ["Bulls Power", "Bears Power"]),
    ("تدفق الحجم التراكمي (OBV+A/D+Force Index)", "احجام",
     ["On Balance Volume", "Accumulation/Distribution", "Force Index"]),
]


def merge_council_groups(votes: List[IndicatorVote]) -> List[IndicatorVote]:
    by_name = {v.name: v for v in votes}
    grouped_names = {n for _, _, members in COUNCIL_GROUPS for n in members}
    merged: List[IndicatorVote] = []

    for group_name, category, members in COUNCIL_GROUPS:
        sub = [by_name[m] for m in members if m in by_name and by_name[m].score is not None]
        if not sub:
            continue
        avg = vmean([v.score for v in sub])
        detail = " + ".join(f"{v.name}={v.score:.0f}%" for v in sub)
        group_voted = all(v.voted for v in sub)
        note = f"دمج: {detail}"
        if not group_voted:
            note += " — أحد الأعضاء مستبعد من التصويت، فالمجموعة معلوماتية فقط"
        merged.append(IndicatorVote(group_name, category, avg, "مدمج", note, voted=group_voted))

    for v in votes:
        if v.name not in grouped_names:
            merged.append(v)
    return merged


# ---- كشف الانحراف (Divergence) بين حركة السعر ومؤشرات الزخم (RSI / MACD) ----
def _find_pivots(vals: List[float], wing: int = 2):
    """يرجّع (indices القمم المحلية, indices القيعان المحلية) — نفس أسلوب الفراكتال
    البسيط المستخدم أصلاً في الدعم/المقاومة، بس مطبّق هنا على أي سلسلة أرقام."""
    n = len(vals)
    highs, lows = [], []
    for i in range(wing, n - wing):
        window = vals[i - wing:i + wing + 1]
        if vals[i] == max(window):
            highs.append(i)
        if vals[i] == min(window):
            lows.append(i)
    return highs, lows


def _detect_divergence(bars: Bars, osc: List[float], osc_name: str,
                        lookback: int = 60, wing: int = 2) -> IndicatorVote:
    name = f"كشف الانحراف ({osc_name})"
    c = bars['close']
    n = len(c)
    if n < lookback + wing * 2 + 5:
        return IndicatorVote(name, "انحراف", None, "حقيقي")

    start = n - lookback
    seg_c = c[start:]
    seg_osc = osc[start:]
    if any(isnan(v) for v in seg_osc[-10:]):
        return IndicatorVote(name, "انحراف", 50.0, "حقيقي", "بيانات المؤشر غير مكتملة", voted=False)

    price_highs, price_lows = _find_pivots(seg_c, wing)

    def osc_ok(i):
        return not isnan(seg_osc[i])

    bearish = bullish = False
    note = "لا يوجد انحراف واضح حاليًا"

    valid_highs = [i for i in price_highs if osc_ok(i)]
    if len(valid_highs) >= 2:
        i1, i2 = valid_highs[-2], valid_highs[-1]
        if seg_c[i2] > seg_c[i1] and seg_osc[i2] < seg_osc[i1]:
            bearish = True
            note = f"انحراف هبوطي: السعر سجّل قمة أعلى لكن {osc_name} سجّل قمة أوطى — ضعف في زخم الصعود"

    valid_lows = [i for i in price_lows if osc_ok(i)]
    if not bearish and len(valid_lows) >= 2:
        i1, i2 = valid_lows[-2], valid_lows[-1]
        if seg_c[i2] < seg_c[i1] and seg_osc[i2] > seg_osc[i1]:
            bullish = True
            note = f"انحراف صعودي: السعر سجّل قاع أدنى لكن {osc_name} سجّل قاع أعلى — ضعف في زخم الهبوط"

    if bearish:
        return IndicatorVote(name, "انحراف", 25.0, "حقيقي", note)
    if bullish:
        return IndicatorVote(name, "انحراف", 75.0, "حقيقي", note)
    return IndicatorVote(name, "انحراف", 50.0, "حقيقي", note, voted=False)


def ind_divergence_rsi(bars: Bars) -> IndicatorVote:
    rsi_v = rsi_wilder(bars['close'], 14)
    return _detect_divergence(bars, rsi_v, "RSI", lookback=60, wing=2)


def ind_divergence_macd(bars: Bars) -> IndicatorVote:
    _, _, hist = macd(bars['close'])
    return _detect_divergence(bars, hist, "MACD", lookback=60, wing=2)


# ============================================================
# مجموعة "Aurora" — مؤشرات مبنية على مفاهيم تحليل فني موثّقة (زخم تدفق
# تكيّفي، Order Blocks من مفاهيم Smart Money Concepts، خرائط مناطق سيولة)،
# مبنية بمنطقنا الخاص هنا — مش نسخة من أي كود أو معادلة تجارية بعينها،
# لأن الأسماء دي بيستخدمها عشرات المنتجات المختلفة وغير المرتبطة ببعض بدون
# صيغة موحّدة موثّقة نقدر نطابقها. الوزن هنا عادي زي باقي المؤشرات (مفيش
# ترجيح إضافي) لحد ما يثبتوا كفاءة فعلية بعد استخدام حقيقي.
# ============================================================
def ind_aurora_flow(bars: Bars, length: int = 40) -> IndicatorVote:
    """Aurora Flow — مؤشر زخم تدفق: يقيس التغير اللوغاريتمي بالسعر (مقياس
    معدل ونسبة حركة السعر) ثم يمرّره على فلتر EMA تكيّفي، ويطبّع القيمة
    الناتجة نسبةً لتقلبها الأخير — نفس أسلوب التطبيع المستخدم في باقي
    مذبذبات الزخم بالكود (Momentum/CCI)."""
    c = bars['close']
    n = len(c)
    if n < length + 20:
        return IndicatorVote("Aurora Flow", "مذبذبات", None, "حقيقي")
    log_ret = [math.log(c[i] / c[i - 1]) if c[i - 1] > 0 else 0.0 for i in range(1, n)]
    flow = ema(log_ret, length)
    valid = [v for v in flow if not isnan(v)]
    if len(valid) < 10 or isnan(flow[-1]):
        return IndicatorVote("Aurora Flow", "مذبذبات", 50.0, "حقيقي")
    sd = vstd(valid[-30:]) + 1e-9
    z = flow[-1] / sd
    score = 50.0 + 35.0 * math.tanh(z)
    return IndicatorVote("Aurora Flow", "مذبذبات", _clip01_100(score), "حقيقي",
                          f"زخم تدفق مطبّع (EMA{length} على العائد اللوغاريتمي) = {z:+.2f}σ")


def _find_last_order_block(bars: Bars, lookback: int = 40, impulse_atr_mult: float = 1.8):
    """يلاقي آخر 'Order Block' (مفهوم من Smart Money Concepts): آخر شمعة
    بلون معاكس قبل حركة اندفاعية قوية (جسمها >= مضاعف من ATR) في الاتجاه
    التاني. يرجّع (اتجاه الاندفاعة, أعلى/أدنى نطاق الشمعة) أو None."""
    o, h, l, c = bars['open'], bars['high'], bars['low'], bars['close']
    n = len(c)
    atr_v = atr_wilder(h, l, c, 14)
    atr_last = atr_v[-1] if not isnan(atr_v[-1]) else vstd(c[-20:])
    if atr_last <= 0 or n < lookback + 5:
        return None
    start = max(1, n - lookback)
    for i in range(n - 2, start - 1, -1):
        body = c[i] - o[i]
        if abs(body) >= impulse_atr_mult * atr_last:
            j = i - 1
            if j < 0:
                continue
            impulse_up = body > 0
            block_is_bear = c[j] < o[j]
            block_is_bull = c[j] > o[j]
            if impulse_up and block_is_bear:
                return 'up', l[j], h[j]
            if (not impulse_up) and block_is_bull:
                return 'down', l[j], h[j]
    return None


def ind_aurora_block(bars: Bars) -> IndicatorVote:
    """Aurora Block — يحدد آخر منطقة 'Order Block' (شمعة معاكسة قبل اندفاعة
    قوية) ويشوف موقع السعر الحالي منها: الدخول جوه بلوك صاعد = دعم محتمل،
    جوه بلوك هابط = مقاومة محتملة."""
    ob = _find_last_order_block(bars)
    price = bars['close'][-1]
    if ob is None:
        return IndicatorVote("Aurora Block", "اتجاه", 50.0, "حقيقي",
                              "لا توجد منطقة Order Block واضحة حاليًا", voted=False)
    direction, lo, hi = ob
    inside = lo <= price <= hi
    if direction == 'up':
        score = 72.0 if inside else (60.0 if price > hi else 40.0)
        note = f"آخر Order Block صاعد عند [{lo:.2f}-{hi:.2f}]"
    else:
        score = 28.0 if inside else (40.0 if price < lo else 60.0)
        note = f"آخر Order Block هابط عند [{lo:.2f}-{hi:.2f}]"
    return IndicatorVote("Aurora Block", "اتجاه", score, "حقيقي", note)


def ind_aurora_map(bars: Bars) -> IndicatorVote:
    """Aurora Map — خريطة أقرب مناطق تجمّع سيولة، معتمدة على نفس بيانات
    بروفايل الحجم المحسوبة أصلاً (HVN) بس بعرض مختلف يركّز على القرب منها.
    معلوماتي فقط (ما يدخلش التصويت) عشان مش بيضيف إشارة جديدة فعليًا —
    بس بيعرض تفاصيل تكميلية عن بروفايل الحجم بصياغة تانية."""
    vp = compute_volume_profile(bars)
    if vp is None:
        return IndicatorVote("Aurora Map", "بروفايل الحجم", None, "بروكسي", voted=False)
    price = vp['price']
    zones = sorted(vp['hvn_zones'], key=lambda z: abs(((z[0] + z[1]) / 2.0) - price))[:3]
    if not zones:
        return IndicatorVote("Aurora Map", "بروفايل الحجم", 50.0, "بروكسي",
                              "لا توجد مناطق سيولة كثيفة واضحة حاليًا", voted=False)
    txt = ", ".join(f"[{z[0]:.2f}-{z[1]:.2f}]" for z in zones)
    nearest = zones[0]
    nearest_mid = (nearest[0] + nearest[1]) / 2.0
    score = 60.0 if price >= nearest_mid else 40.0
    return IndicatorVote("Aurora Map", "بروفايل الحجم", score, "بروكسي",
                          f"أقرب مناطق سيولة كثيفة: {txt}", voted=False)


def ind_flowmap(bars: Bars) -> IndicatorVote:
    """FlowMap — مؤشر مركّب: متوسط Aurora Flow (الزخم) و Aurora Block
    (موقع السعر من آخر منطقة Order Block) في قراءة واحدة. ده الوحيد من
    مجموعة Aurora اللي بيدخل التصويت الفعلي بوزن عادي، عشان منفتحش
    نفس الإشارة أكتر من مرة (زي ما بنعمل مع بروفايل الحجم)."""
    flow = ind_aurora_flow(bars)
    block = ind_aurora_block(bars)
    scores = [v.score for v in (flow, block) if v.score is not None]
    if not scores:
        return IndicatorVote("FlowMap", "Aurora", None, "مدمج")
    score = vmean(scores)
    note = f"دمج: Aurora Flow={flow.score if flow.score is not None else '—'} + Aurora Block={block.score if block.score is not None else '—'}"
    return IndicatorVote("FlowMap", "Aurora", _clip01_100(score), "مدمج", note)


# ============================================================
# مؤشرات معنويات السوق والسيولة — بروكسي مبني بالكامل من بيانات OHLCV
# المتاحة هنا (بدون بيانات خارجية زي VIX أو Put/Call أو تريندات البحث،
# لأن السكريبت بدون مكتبات خارجية وبدون مصادر بيانات إضافية أصلاً).
# ============================================================
def ind_fear_greed(bars: Bars) -> IndicatorVote:
    """مؤشر الخوف والطمع (Fear & Greed) — بروكسي يجمع 4 مكوّنات من نفس
    بيانات السعر المتاحة:
      1) الزخم: موقع السعر من SMA(50) مطبّع بـATR (زخم صاعد قوي = طمع).
      2) التقلب: تمدد/انكماش ATR الحالي عن متوسطه (تقلب متمدد مع هبوط =
         خوف حاد، تقلب منكمش = طمع/رضا هادئ شبيه بانخفاض VIX).
      3) RSI(14): تشبع شرائي = طمع، تشبع بيعي = خوف.
      4) اتساع الحركة: نسبة شموع الصعود لشموع الهبوط في آخر 20 شمعة.
    القيمة 0 = خوف شديد، 100 = طمع شديد، 50 = محايد. التصويت هنا قراءة
    مباشرة (زخم عالي = نتيجة عالية) اتساقًا مع باقي مذبذبات الكود
    (RSI/CCI/Stochastic)؛ ملحوظة: بعض المتداولين بيستخدموا الخوف والطمع
    عكسيًا (طمع شديد = حذر، خوف شديد = فرصة) — تفسير بديل ممكن الاعتماد
    عليه يدويًا، لكن التصويت الآلي هنا بياخد القراءة المباشرة للاتساق.
    ⚠️ ده تقريب من سلوك السعر نفسه، مش نفس منهجية مؤشر CNN أو
    Alternative.me الرسمية اللي بتعتمد مصادر بيانات خارجية غير متاحة هنا."""
    c, h, l, o = bars['close'], bars['high'], bars['low'], bars['open']
    n = len(c)
    if n < 55:
        return IndicatorVote("مؤشر الخوف والطمع", "معنويات السوق", None, "بروكسي", voted=False)

    sub_scores = []

    # 1) الزخم: موقع السعر من SMA(50)
    ma50 = vmean(c[-50:])
    atr_v = atr_wilder(h, l, c, 14)
    atr_last = atr_v[-1] if not isnan(atr_v[-1]) else vstd(c[-20:])
    if atr_last > 0:
        z_mom = (c[-1] - ma50) / atr_last
        sub_scores.append(50.0 + 40.0 * math.tanh(z_mom / 2.0))

    # 2) التقلب: تمدد/انكماش ATR الحالي عن متوسطه
    valid_atr = [v for v in atr_v[-50:] if not isnan(v)]
    if not isnan(atr_v[-1]) and len(valid_atr) >= 10:
        atr_avg = vmean(valid_atr)
        if atr_avg > 0:
            vol_ratio = atr_v[-1] / atr_avg
            price_falling = c[-1] < c[-6] if n >= 6 else False
            if vol_ratio > 1.0:
                fear_intensity = min((vol_ratio - 1.0) * 60.0, 45.0)
                sub_scores.append(50.0 - fear_intensity if price_falling else 50.0 + fear_intensity * 0.4)
            else:
                calm_bonus = min((1.0 - vol_ratio) * 40.0, 20.0)
                sub_scores.append(50.0 + calm_bonus)

    # 3) RSI(14) مباشرة
    rsi_v = rsi_wilder(c, 14)
    if not isnan(rsi_v[-1]):
        sub_scores.append(_clip01_100(rsi_v[-1]))

    # 4) اتساع الحركة: نسبة شموع الصعود في آخر 20 شمعة
    k = min(20, n)
    up_bars = sum(1 for i in range(-k, 0) if c[i] >= o[i])
    sub_scores.append(up_bars / k * 100.0)

    if not sub_scores:
        return IndicatorVote("مؤشر الخوف والطمع", "معنويات السوق", 50.0, "بروكسي",
                              "بيانات غير كافية لحساب كل المكوّنات", voted=False)

    score = _clip01_100(vmean(sub_scores))
    if score >= 75: zone = "طمع شديد 🟢🔥"
    elif score >= 60: zone = "طمع"
    elif score <= 25: zone = "خوف شديد 🔴🥶"
    elif score <= 40: zone = "خوف"
    else: zone = "محايد"
    note = f"المنطقة: {zone} (بروكسي من الزخم/التقلب/RSI/اتساع الحركة — مش نفس مؤشر CNN/Alternative.me الرسمي)"
    return IndicatorVote("مؤشر الخوف والطمع", "معنويات السوق", score, "بروكسي", note)


def ind_liquidity_flow(bars: Bars) -> IndicatorVote:
    """مؤشر تدفق السيولة (Liquidity Flow) — بروكسي يقيس هل السيولة بتتزايد
    في السوق (إضافة/تجميع) ولا بتنسحب منه (سحب/تصريف)، بدمج 3 قراءات:
      1) اتجاه الحجم نفسه: متوسط حجم الفترة الأخيرة مقابل اللي قبلها
         (سيولة داخلة بتتزايد / سيولة بتجف).
      2) تدفق الحجم الموزون بالسعر (شبيه بـChaikin Money Flow): الحجم
         المصاحب لشموع صاعدة مقابل الحجم المصاحب لشموع هابطة.
      3) انتقال POC (من بروفايل الحجم المحسوب أصلاً بالكود): هل مركز ثقل
         التداول بينتقل لأسعار أعلى (سيولة بتتجمع فوق) ولا أدنى.
    القيمة 0 = سحب سيولة قوي (تصريف/بيع)، 100 = إضافة سيولة قوية
    (تجميع/شراء)، 50 = سيولة متوازنة. لو الحجم بديل تقريبي (proxy)، بيتحسب
    للعرض بس ومستبعد من التصويت الفعلي (زي باقي مؤشرات الحجم بالكود)."""
    c, o, vol = bars['close'], bars['open'], bars['volume']
    n = len(c)
    if n < 25:
        return IndicatorVote("تدفق السيولة (Liquidity Flow)", "احجام", None, "بروكسي", voted=False)

    is_proxy_vol = getattr(bars, 'volume_is_proxy', False)
    k = min(20, n)

    half = max(k // 2, 3)
    recent_vol_avg = vmean(vol[-half:])
    prior_vol_avg = vmean(vol[-2 * half:-half]) if n >= 2 * half else recent_vol_avg
    vol_trend_ratio = recent_vol_avg / prior_vol_avg if prior_vol_avg > 0 else 1.0

    up_vol = sum(vol[i] for i in range(-k, 0) if c[i] >= o[i])
    down_vol = sum(vol[i] for i in range(-k, 0) if c[i] < o[i])
    total_vol = up_vol + down_vol
    flow_pct = (up_vol / total_vol * 100.0) if total_vol > 0 else 50.0

    score = flow_pct
    if vol_trend_ratio > 1.05:
        score = 50.0 + (score - 50.0) * min(vol_trend_ratio, 1.6)
    elif vol_trend_ratio < 0.85:
        score = 50.0 + (score - 50.0) * max(vol_trend_ratio, 0.4)

    vp = compute_volume_profile(bars)
    poc_note = ""
    if vp is not None:
        if vp['poc_rising']:
            score += 8; poc_note = " | POC بيتحرك لأعلى (تجمّع سيولة عند أسعار أعلى)"
        elif vp['poc_falling']:
            score -= 8; poc_note = " | POC بيتحرك لأسفل (تجمّع سيولة عند أسعار أدنى)"

    score = _clip01_100(score)
    if score >= 65: state = "إضافة سيولة/تجميع (شراء صافي)"
    elif score <= 35: state = "سحب سيولة/تصريف (بيع صافي)"
    else: state = "سيولة متوازنة نسبيًا"
    vol_state = "متزايد" if vol_trend_ratio > 1.05 else ("متراجع" if vol_trend_ratio < 0.85 else "شبه ثابت")
    note = f"الحالة: {state} | حجم التداول: {vol_state} (نسبة {vol_trend_ratio:.2f}×){poc_note}"
    if is_proxy_vol:
        note += " | ⚠️ الحجم بديل تقريبي — تم استبعاده من التصويت"
    return IndicatorVote("تدفق السيولة (Liquidity Flow)", "احجام", score, "بروكسي", note,
                          voted=not is_proxy_vol)


COUNCIL_INDICATORS = [
    ind_adx_dmi, ind_bollinger, ind_envelopes, ind_ichimoku,
    ind_moving_average, ind_parabolic_sar, ind_standard_deviation, ind_zigzag,
    ind_atr, ind_bears_power, ind_bulls_power, ind_cci, ind_demarker,
    ind_force_index, ind_macd, ind_momentum, ind_osma, ind_rsi, ind_rvi,
    ind_stochastic, ind_williams_r,
    ind_accum_dist, ind_market_profile, ind_mfi, ind_obv, ind_volumes,
    ind_accelerator_oscillator, ind_alligator, ind_awesome_oscillator,
    ind_fractals, ind_gator_oscillator, ind_market_facilitation_index,
    ind_volume_profile_poc, ind_volume_profile_value_area,
    ind_volume_profile_hvn_lvn, ind_volume_profile_bias,
    ind_divergence_rsi, ind_divergence_macd,
    ind_aurora_flow, ind_aurora_block, ind_aurora_map, ind_flowmap,
    ind_fear_greed, ind_liquidity_flow,
]


def run_council(bars: Bars) -> dict:
    raw_votes: List[IndicatorVote] = []
    for fn in COUNCIL_INDICATORS:
        try:
            v = fn(bars)
        except Exception as e:
            v = IndicatorVote(fn.__name__, "?", None, "خطأ", str(e))
        raw_votes.append(v)

    unified_votes = merge_council_groups(raw_votes)
    all_valid = [v for v in unified_votes if v.score is not None]
    votable = [v for v in all_valid if v.voted]
    informational = [v for v in all_valid if not v.voted]

    bull_team = [v for v in votable if v.score > 50.0]
    bear_team = [v for v in votable if v.score < 50.0]
    neutral = [v for v in votable if v.score == 50.0]

    bull_count, bear_count = len(bull_team), len(bear_team)
    overall = 'up' if bull_count > bear_count else ('down' if bear_count > bull_count else 'mixed')
    avg_score = vmean([v.score for v in votable]) if votable else 50.0

    return {
        'raw_votes': raw_votes, 'votes': unified_votes,
        'raw_count': len([v for v in raw_votes if v.score is not None]),
        'valid_count': len(votable), 'informational_count': len(informational),
        'bull_count': bull_count, 'bear_count': bear_count, 'neutral_count': len(neutral),
        'overall': overall, 'avg_score': avg_score,
    }


def format_council(res: dict, tf_label: str) -> str:
    lines = [f"── مجلس المؤشرات ({res['raw_count']} مؤشر خام → {res['valid_count']} صوت محتسب "
             f"+ {res['informational_count']} معلوماتي فقط) — فريم {tf_label} ──"]
    overall_ar = {'up': '🟢 صعود', 'down': '🔴 هبوط', 'mixed': '⚪ تعادل/متضارب'}[res['overall']]
    lines.append(f"  النتيجة (من الأصوات المحتسبة فقط): {overall_ar}  |  فريق الصعود: {res['bull_count']}  مقابل  "
                 f"فريق الهبوط: {res['bear_count']}  (محايد: {res['neutral_count']})")
    lines.append(f"  متوسط النسبة (محتسب فقط): {res['avg_score']:.1f}%")

    lines.append("  ▸ الأصوات المحتسبة بالقرار:")
    for v in res['votes']:
        if v.score is None or not v.voted:
            continue
        tag = "🟢" if v.score > 50 else ("🔴" if v.score < 50 else "⚪")
        lines.append(f"     {tag} {v.name}: {v.score:.0f}%")
        if v.kind == "مدمج" and v.note:
            lines.append(f"        ↳ {v.note}")

    info_votes = [v for v in res['votes'] if v.score is not None and not v.voted]
    if info_votes:
        lines.append("  ▸ معلوماتي فقط (ما يدخل التصويت — بلا اتجاه رسمي أو حجم غير حقيقي):")
        for v in info_votes:
            tag = "🟢" if v.score > 50 else ("🔴" if v.score < 50 else "⚪")
            lines.append(f"     {tag} {v.name} [{v.kind}]: {v.score:.0f}%  ({v.note})")

    skipped = [v.name for v in res['votes'] if v.score is None]
    if skipped:
        lines.append(f"  (بيانات غير كافية لـ: {', '.join(skipped)})")
    return "\n".join(lines)


# ============================================================
# 6) أنماط الشموع اليابانية
# ============================================================
def _avg_body(bars: Bars, lookback: int = 20) -> float:
    o, c = bars['open'][-lookback:], bars['close'][-lookback:]
    return vmean([abs(c[i] - o[i]) for i in range(len(c))]) + 1e-9


def _prior_trend(bars: Bars, lookback: int = 10) -> str:
    c = bars['close']
    if len(c) < lookback + 1:
        return 'flat'
    if c[-1] > c[-1 - lookback]:
        return 'up'
    if c[-1] < c[-1 - lookback]:
        return 'down'
    return 'flat'


def _hammer_shape(bars: Bars) -> Optional[str]:
    o, h, l, c = bars['open'][-1], bars['high'][-1], bars['low'][-1], bars['close'][-1]
    rng = h - l
    if rng <= 0:
        return None
    body = abs(c - o)
    if body / rng > 0.35:
        return None
    upper_wick = h - max(o, c)
    lower_wick = min(o, c) - l
    if lower_wick >= 2 * body and upper_wick <= body * 0.5:
        return 'hammer_shape'
    if upper_wick >= 2 * body and lower_wick <= body * 0.5:
        return 'star_shape'
    return None


def cs_doji(bars: Bars) -> IndicatorVote:
    o, h, l, c = bars['open'][-1], bars['high'][-1], bars['low'][-1], bars['close'][-1]
    rng = h - l
    if rng <= 0:
        return IndicatorVote("دوجي (Doji)", "شموع يابانية", 50.0, "بروكسي", "", voted=False)
    is_doji = abs(c - o) / rng < 0.1
    note = ("جسم صغير جدًا نسبة للمدى — تردد/تعادل بين المشترين والبائعين"
            if is_doji else "لا يوجد نمط دوجي في آخر شمعة")
    return IndicatorVote("دوجي (Doji)", "شموع يابانية", 50.0, "بروكسي", note, voted=False)


def cs_hammer_hanging(bars: Bars) -> IndicatorVote:
    if len(bars) < 11:
        return IndicatorVote("Hammer / Hanging Man", "شموع يابانية", None, "حقيقي")
    if _hammer_shape(bars) != 'hammer_shape':
        return IndicatorVote("Hammer / Hanging Man", "شموع يابانية", 50.0, "حقيقي", "لا يوجد نمط", voted=False)
    trend = _prior_trend(bars, 10)
    if trend == 'down':
        return IndicatorVote("Hammer / Hanging Man", "شموع يابانية", 68.0, "حقيقي",
                              "ظل سفلي طويل بعد اتجاه هابط — إشارة ارتداد صعودية محتملة (Hammer)")
    if trend == 'up':
        return IndicatorVote("Hammer / Hanging Man", "شموع يابانية", 32.0, "حقيقي",
                              "ظل سفلي طويل بعد اتجاه صاعد — إشارة تحذير هبوطية محتملة (Hanging Man)")
    return IndicatorVote("Hammer / Hanging Man", "شموع يابانية", 50.0, "حقيقي",
                          "الشكل موجود لكن الاتجاه السابق غير واضح لتحديد النوع", voted=False)


def cs_shooting_star(bars: Bars) -> IndicatorVote:
    if len(bars) < 11:
        return IndicatorVote("Shooting Star / Inverted Hammer", "شموع يابانية", None, "حقيقي")
    if _hammer_shape(bars) != 'star_shape':
        return IndicatorVote("Shooting Star / Inverted Hammer", "شموع يابانية", 50.0, "حقيقي", "لا يوجد نمط", voted=False)
    trend = _prior_trend(bars, 10)
    if trend == 'up':
        return IndicatorVote("Shooting Star / Inverted Hammer", "شموع يابانية", 32.0, "حقيقي",
                              "ظل علوي طويل بعد اتجاه صاعد — إشارة انعكاس هبوطية محتملة (Shooting Star)")
    if trend == 'down':
        return IndicatorVote("Shooting Star / Inverted Hammer", "شموع يابانية", 68.0, "حقيقي",
                              "ظل علوي طويل بعد اتجاه هابط — إشارة ارتداد صعودية محتملة (Inverted Hammer)")
    return IndicatorVote("Shooting Star / Inverted Hammer", "شموع يابانية", 50.0, "حقيقي",
                          "الشكل موجود لكن الاتجاه غير واضح", voted=False)


def cs_engulfing(bars: Bars) -> IndicatorVote:
    if len(bars) < 2:
        return IndicatorVote("Engulfing (ابتلاع)", "شموع يابانية", None, "حقيقي")
    o1, c1 = bars['open'][-2], bars['close'][-2]
    o2, c2 = bars['open'][-1], bars['close'][-1]
    bull = c1 < o1 and c2 > o2 and c2 >= o1 and o2 <= c1
    bear = c1 > o1 and c2 < o2 and o2 >= c1 and c2 <= o1
    if bull:
        return IndicatorVote("Engulfing (ابتلاع)", "شموع يابانية", 72.0, "حقيقي",
                              "ابتلاع صعودي — شمعة خضراء ابتلعت جسم الشمعة الحمراء السابقة بالكامل")
    if bear:
        return IndicatorVote("Engulfing (ابتلاع)", "شموع يابانية", 28.0, "حقيقي",
                              "ابتلاع هبوطي — شمعة حمراء ابتلعت جسم الشمعة الخضراء السابقة بالكامل")
    return IndicatorVote("Engulfing (ابتلاع)", "شموع يابانية", 50.0, "حقيقي",
                          "لا يوجد نمط ابتلاع في آخر شمعتين", voted=False)


def cs_piercing_darkcloud(bars: Bars) -> IndicatorVote:
    if len(bars) < 2:
        return IndicatorVote("Piercing Line / Dark Cloud Cover", "شموع يابانية", None, "حقيقي")
    o1, c1 = bars['open'][-2], bars['close'][-2]
    o2, c2 = bars['open'][-1], bars['close'][-1]
    mid1 = (o1 + c1) / 2.0
    piercing = c1 < o1 and c2 > o2 and o2 < c1 and mid1 < c2 < o1
    darkcloud = c1 > o1 and c2 < o2 and o2 > c1 and o1 < c2 < mid1
    if piercing:
        return IndicatorVote("Piercing Line / Dark Cloud Cover", "شموع يابانية", 66.0, "حقيقي",
                              "اختراق صعودي — الشمعة الثانية أغلقت فوق منتصف جسم الشمعة الهابطة السابقة")
    if darkcloud:
        return IndicatorVote("Piercing Line / Dark Cloud Cover", "شموع يابانية", 34.0, "حقيقي",
                              "غطاء سحابي هابط — الشمعة الثانية أغلقت تحت منتصف جسم الشمعة الصاعدة السابقة")
    return IndicatorVote("Piercing Line / Dark Cloud Cover", "شموع يابانية", 50.0, "حقيقي", "لا يوجد نمط", voted=False)


def cs_star(bars: Bars) -> IndicatorVote:
    if len(bars) < 3:
        return IndicatorVote("Morning Star / Evening Star", "شموع يابانية", None, "حقيقي")
    o1, c1 = bars['open'][-3], bars['close'][-3]
    o2, c2 = bars['open'][-2], bars['close'][-2]
    o3, c3 = bars['open'][-1], bars['close'][-1]
    body1, body2, body3 = abs(c1 - o1), abs(c2 - o2), abs(c3 - o3)
    avg_body = _avg_body(bars, 20)
    small_middle = body2 < avg_body * 0.5
    mid1 = (o1 + c1) / 2.0
    morning = (c1 < o1 and body1 > avg_body * 0.7 and small_middle and
               c3 > o3 and body3 > avg_body * 0.7 and c3 > mid1)
    evening = (c1 > o1 and body1 > avg_body * 0.7 and small_middle and
               c3 < o3 and body3 > avg_body * 0.7 and c3 < mid1)
    if morning:
        return IndicatorVote("Morning Star / Evening Star", "شموع يابانية", 75.0, "حقيقي", "نجمة الصباح — انعكاس صعودي بثلاث شموع")
    if evening:
        return IndicatorVote("Morning Star / Evening Star", "شموع يابانية", 25.0, "حقيقي", "نجمة المساء — انعكاس هبوطي بثلاث شموع")
    return IndicatorVote("Morning Star / Evening Star", "شموع يابانية", 50.0, "حقيقي", "لا يوجد نمط", voted=False)


def cs_soldiers_crows(bars: Bars) -> IndicatorVote:
    if len(bars) < 3:
        return IndicatorVote("Three White Soldiers / Three Black Crows", "شموع يابانية", None, "حقيقي")
    o = bars['open'][-3:]; c = bars['close'][-3:]
    bullish_run = (all(c[i] > o[i] for i in range(3)) and c[2] > c[1] > c[0] and o[1] > o[0] and o[2] > o[1])
    bearish_run = (all(c[i] < o[i] for i in range(3)) and c[2] < c[1] < c[0] and o[1] < o[0] and o[2] < o[1])
    if bullish_run:
        return IndicatorVote("Three White Soldiers / Three Black Crows", "شموع يابانية", 78.0, "حقيقي", "ثلاث جنود بيض — استمرار صعودي قوي")
    if bearish_run:
        return IndicatorVote("Three White Soldiers / Three Black Crows", "شموع يابانية", 22.0, "حقيقي", "ثلاث غربان سود — استمرار هبوطي قوي")
    return IndicatorVote("Three White Soldiers / Three Black Crows", "شموع يابانية", 50.0, "حقيقي", "لا يوجد نمط", voted=False)


def cs_marubozu(bars: Bars) -> IndicatorVote:
    o, h, l, c = bars['open'][-1], bars['high'][-1], bars['low'][-1], bars['close'][-1]
    rng = h - l
    if rng <= 0:
        return IndicatorVote("Marubozu", "شموع يابانية", 50.0, "حقيقي", "", voted=False)
    body = abs(c - o)
    if body / rng > 0.9:
        if c > o:
            return IndicatorVote("Marubozu", "شموع يابانية", 70.0, "حقيقي", "ماروبوزو صاعد — شمعة زخم قوي بدون أظلال تقريبًا")
        return IndicatorVote("Marubozu", "شموع يابانية", 30.0, "حقيقي", "ماروبوزو هابط — شمعة زخم قوي بدون أظلال تقريبًا")
    return IndicatorVote("Marubozu", "شموع يابانية", 50.0, "حقيقي", "لا يوجد نمط", voted=False)


def cs_spinning_top(bars: Bars) -> IndicatorVote:
    o, h, l, c = bars['open'][-1], bars['high'][-1], bars['low'][-1], bars['close'][-1]
    rng = h - l
    if rng <= 0:
        return IndicatorVote("Spinning Top", "شموع يابانية", 50.0, "بروكسي", "", voted=False)
    body = abs(c - o)
    upper = h - max(o, c); lower = min(o, c) - l
    is_spin = 0.1 <= body / rng <= 0.35 and upper > body * 0.5 and lower > body * 0.5
    note = ("جسم صغير وأظلال متوازنة من الجهتين — تردد السوق" if is_spin else "لا يوجد نمط")
    return IndicatorVote("Spinning Top", "شموع يابانية", 50.0, "بروكسي", note, voted=False)


CANDLESTICK_INDICATORS = [
    cs_doji, cs_hammer_hanging, cs_shooting_star, cs_engulfing,
    cs_piercing_darkcloud, cs_star, cs_soldiers_crows, cs_marubozu, cs_spinning_top,
]


def candlestick_votes(bars: Bars) -> List[IndicatorVote]:
    votes = []
    for fn in CANDLESTICK_INDICATORS:
        try:
            v = fn(bars)
        except Exception as e:
            v = IndicatorVote(fn.__name__, "شموع يابانية", None, "خطأ", str(e))
        votes.append(v)
    return votes


# ============================================================
# 7) التحليل الأساسي (بأسماء ونسب)
# ============================================================
def basic_analysis_votes(analysis: dict) -> List[IndicatorVote]:
    votes: List[IndicatorVote] = []

    if analysis.get('sma') is not None:
        gap = (analysis['price'] - analysis['sma']) / analysis['sma'] * 100
        trend_score_map = {'up': 75.0, 'up_weak': 60.0, 'down': 25.0, 'down_weak': 40.0, 'flat': 50.0}
        score = trend_score_map.get(analysis['trend'], 50.0)
        votes.append(IndicatorVote(f"اتجاه SMA({I.sma_period}) الأساسي", "تحليل أساسي", score, "حقيقي",
                     f"السعر {'فوق' if gap >= 0 else 'تحت'} المتوسط بفارق {gap:+.2f}% "
                     f"({_TREND_AR.get(analysis['trend'], analysis['trend'])})"))

    if analysis.get('sma50') is not None and analysis.get('sma200') is not None:
        price = analysis['price']; s20 = analysis['sma']; s50 = analysis['sma50']; s200 = analysis['sma200']
        up_ok = [price > s20, s20 > s50, s50 > s200]
        down_ok = [price < s20, s20 < s50, s50 < s200]
        up_n, down_n = sum(up_ok), sum(down_ok)
        if up_n == 3:
            score, note = 85.0, "ترتيب صاعد كامل: السعر > SMA20 > SMA50 > SMA200 — هيكل اتجاه قوي"
        elif down_n == 3:
            score, note = 15.0, "ترتيب هابط كامل: السعر < SMA20 < SMA50 < SMA200 — هيكل اتجاه قوي"
        elif up_n >= down_n:
            score, note = 50.0 + up_n * 8.0, f"ترتيب صاعد جزئي ({up_n}/3 شروط متحققة)"
        else:
            score, note = 50.0 - down_n * 8.0, f"ترتيب هابط جزئي ({down_n}/3 شروط متحققة)"
        votes.append(IndicatorVote("ترتيب المتوسطات (SMA 20/50/200)", "تحليل أساسي",
                     _clip01_100(score), "حقيقي", note))

    if analysis.get('rsi') is not None:
        votes.append(IndicatorVote(f"RSI({I.rsi_period}) الأساسي", "تحليل أساسي",
                     _clip01_100(analysis['rsi']), "حقيقي",
                     f"المنطقة: {_RSIZONE_AR.get(analysis['rsi_zone'], analysis['rsi_zone'])}"))

    if analysis.get('macd') is not None:
        mom_score_map = {'bull': 70.0, 'bull_slowing': 58.0, 'bear': 30.0, 'bear_slowing': 42.0, 'flat': 50.0}
        score = mom_score_map.get(analysis.get('macd_mom'), 50.0)
        votes.append(IndicatorVote(f"MACD({I.macd_fast},{I.macd_slow},{I.macd_signal}) الأساسي",
                     "تحليل أساسي", score, "حقيقي", f"الحالة: {analysis.get('macd_mom')}"))

    if analysis.get('adx') is not None:
        strength = min(analysis['adx'] / 50.0, 1.0) * 50.0
        if analysis['trend'] in ('up', 'up_weak'):
            score = 50.0 + strength
        elif analysis['trend'] in ('down', 'down_weak'):
            score = 50.0 - strength
        else:
            score = 50.0
        votes.append(IndicatorVote(f"ADX({I.adx_period}) الأساسي (قوة الاتجاه)", "تحليل أساسي",
                     _clip01_100(score), "حقيقي",
                     f"ADX={analysis['adx']:.1f} ({'اتجاه مؤكد' if analysis.get('trending_market') else 'سوق عرضي'})"))

    if analysis.get('volume_avg') and analysis.get('volume_last') is not None:
        vratio = analysis['volume_last'] / analysis['volume_avg'] if analysis['volume_avg'] else 1.0
        score = 50.0 + max(min((vratio - 1.0) * 50.0, 40.0), -40.0)
        is_proxy = analysis.get('volume_is_proxy', False)
        note = "(الحجم بديل تقريبي — تم استبعاده من التصويت)" if is_proxy else f"الحجم عند {vratio:.0%} من متوسطه"
        votes.append(IndicatorVote("تأكيد الحجم الأساسي", "تحليل أساسي", _clip01_100(score),
                     "بروكسي" if is_proxy else "حقيقي", note, voted=not is_proxy))

    sr = analysis.get('sr') or {}
    if sr.get('nearest_res') and sr.get('nearest_sup'):
        rng = sr['nearest_res'] - sr['nearest_sup']
        if rng > 0:
            pos = (analysis['price'] - sr['nearest_sup']) / rng * 100.0
            votes.append(IndicatorVote("موقع السعر بين الدعم والمقاومة", "تحليل أساسي",
                         _clip01_100(pos), "حقيقي",
                         f"دعم {sr['nearest_sup']:.2f} / مقاومة {sr['nearest_res']:.2f}"))

    return votes


# ============================================================
# 8) التحليل الكامل لكل فريم (أساسي + مجلس + شموع) + بناء الصفقة
# ============================================================
# ---- بوابة ADX كنظام (ترند/تذبذب) — ترجيح الأصوات حسب حالة السوق بدل معاملتها
#      كلها بنفس الوزن. لما السوق في اتجاه واضح (ADX عالي) بنثق أكتر بمؤشرات
#      الاتجاه (فئة "اتجاه" و"بيل_وليامز")، ولما السوق عرضي/متذبذب (ADX واطي)
#      بنثق أكتر بمؤشرات الارتداد عند التطرف (فئة "مذبذبات"). باقي الفئات
#      (احجام، بروفايل الحجم، شموع يابانية، تحليل أساسي، انحراف) بتفضل بوزن
#      محايد ثابت لأنها مش حساسة لحالة الترند/التذبذب بنفس الطريقة.
_TREND_CATEGORIES = {"اتجاه", "بيل_وليامز"}
_OSCILLATOR_CATEGORIES = {"مذبذبات"}


def regime_weighted_score(votes: List[IndicatorVote], trending: bool) -> Optional[float]:
    weighted_sum = 0.0
    weight_total = 0.0
    for v in votes:
        if v.score is None or not v.voted:
            continue
        if v.category in _TREND_CATEGORIES:
            w = 1.5 if trending else 0.6
        elif v.category in _OSCILLATOR_CATEGORIES:
            w = 0.8 if trending else 1.5
        else:
            w = 1.0
        weighted_sum += v.score * w
        weight_total += w
    return weighted_sum / weight_total if weight_total > 0 else None


def full_tf_analysis(bars: Bars, tf_label: str) -> dict:
    analysis = analyze_timeframe(bars, tf_label)
    council = run_council(bars)
    basic_votes = basic_analysis_votes(analysis)
    candle_votes = candlestick_votes(bars)

    votable = [v for v in (council['votes'] + basic_votes + candle_votes)
               if v.score is not None and v.voted]
    bull = [v for v in votable if v.score > 50.0]
    bear = [v for v in votable if v.score < 50.0]
    overall = 'up' if len(bull) > len(bear) else ('down' if len(bear) > len(bull) else 'mixed')
    avg_score = vmean([v.score for v in votable]) if votable else 50.0

    regime_trending = bool(analysis.get('trending_market', True))
    weighted_score = regime_weighted_score(votable, regime_trending)

    return {
        'tf': tf_label, 'analysis': analysis,
        'council_votes': council['votes'], 'basic_votes': basic_votes, 'candle_votes': candle_votes,
        'bull_count': len(bull), 'bear_count': len(bear),
        'neutral_count': len(votable) - len(bull) - len(bear),
        'overall': overall, 'avg_score': avg_score,
        'regime': 'trending' if regime_trending else 'ranging',
        'weighted_score': weighted_score,
    }


def _avg_bar_move(bars: Bars, lookback: int = 30) -> float:
    c = bars['close'][-lookback:]
    if len(c) < 2:
        return 0.0
    return vmean([abs(c[i] - c[i - 1]) for i in range(1, len(c))])


def _format_duration(minutes: float) -> str:
    if minutes <= 0 or not math.isfinite(minutes):
        return "غير محدد"
    if minutes < 60:
        return f"~{minutes:.0f} دقيقة"
    hours = minutes / 60.0
    if hours < 24:
        return f"~{hours:.1f} ساعة"
    return f"~{hours / 24:.1f} يوم"


def _build_trade(analysis: dict, direction: str, min_d: float = None, max_d: float = None) -> Optional[dict]:
    price = analysis['price']; atr_v = analysis['atr'] or 0.0
    sr = analysis['sr']
    min_d = TC.target_min_points if min_d is None else min_d
    max_d = TC.target_max_points if max_d is None else max_d

    if direction == 'up':
        dist_res = (sr['nearest_res'] - price) if sr['nearest_res'] else 0.0
        raw_tp1 = max(dist_res, TC.atr_target_mult * atr_v)
        raw_stop = max(price - analysis['recent_low'], TC.atr_stop_mult * atr_v)
        sign = 1
    else:
        dist_sup = (price - sr['nearest_sup']) if sr['nearest_sup'] else 0.0
        raw_tp1 = max(dist_sup, TC.atr_target_mult * atr_v)
        raw_stop = max(analysis['recent_high'] - price, TC.atr_stop_mult * atr_v)
        sign = -1

    tp1_dist = min(max(raw_tp1, min_d), max_d)
    stop_dist = min(raw_stop, TC.max_stop_to_target_ratio * tp1_dist)
    if stop_dist <= 0:
        return None
    stop = price - stop_dist if direction == 'up' else price + stop_dist
    m1, m2, m3 = TC.tp_stage_mults
    tp1 = price + sign * tp1_dist * m1
    tp2 = price + sign * tp1_dist * m2
    tp3 = price + sign * tp1_dist * m3
    rr = tp1_dist / stop_dist
    if rr < TC.min_rr:
        return None
    return {
        'direction': 'long' if direction == 'up' else 'short',
        'entry': price, 'stop': stop, 'stop_dist': stop_dist,
        'tp1': tp1, 'tp2': tp2, 'tp3': tp3, 'tp1_dist': tp1_dist, 'rr': rr,
    }


def _freshest_live_price(bars_by_tf: Dict[str, Bars]):
    """يرجّع أحدث سعر لحظي (live_price) متاح بين الفريمات المجلوبة، مع وقته.
    السعر ده بييجي من meta.regularMarketPrice في نفس رد Yahoo، وهو غالبًا
    أحدث من إغلاق آخر شمعة مقفلة لأن الشمعة الحالية لسه بتتكوّن."""
    candidates = [(b.live_time, b.live_price) for b in bars_by_tf.values()
                  if b.live_price is not None]
    if not candidates:
        return None, None
    with_time = [c for c in candidates if c[0] is not None]
    if with_time:
        with_time.sort(key=lambda t: t[0], reverse=True)
        return with_time[0][1], with_time[0][0]
    return candidates[0][1], candidates[0][0]


def _reanchor_trade_to_live_price(trade: Optional[dict], live_price: Optional[float],
                                   ref_price: float, atr_hint: Optional[float] = None) -> Optional[dict]:
    """يزيح الدخول/الوقف/الأهداف كلها بنفس المقدار عشان الدخول يبقى مطابق
    للسعر اللحظي الآن بدل سعر إغلاق آخر شمعة مقفلة (اللي ممكن يبقى له كذا دقيقة).
    نفس مسافة الوقف/الأهداف (ونفس نسبة R:R) بتتحفظ زي ما هي، بس بتتنقل كلها
    مع السعر الحالي. لو الفرق كبير جدًا وغير منطقي (احتمال خطأ بيانات)، بيتجاهل
    إعادة الضبط ويسيب القيم الأصلية بدل ما يدّي رقم غلط."""
    if trade is None or live_price is None:
        return trade
    delta = live_price - ref_price
    if atr_hint and atr_hint > 0 and abs(delta) > atr_hint * 15:
        return trade
    new_trade = dict(trade)
    new_trade['entry'] = trade['entry'] + delta
    new_trade['stop'] = trade['stop'] + delta
    new_trade['tp1'] = trade['tp1'] + delta
    new_trade['tp2'] = trade['tp2'] + delta
    # tp3 ممكن يبقى None عمدًا في صفقات التصحيح عكس الاتجاه العام (هدفين بس) —
    # نتجنب هنا كسر الكود بمحاولة جمع None مع رقم.
    new_trade['tp3'] = (trade['tp3'] + delta) if trade.get('tp3') is not None else None
    new_trade['reanchored'] = abs(delta) > 1e-9
    new_trade['closed_bar_price'] = ref_price
    return new_trade


def council_decide_cascade(bars_by_tf: Dict[str, Bars], htf_bars: Optional[Bars] = None) -> dict:
    result = {'per_tf': {}, 'confirmed': False, 'trade': None, 'steps': [], 'htf': None}

    # نجيب السعر اللحظي فورًا من أول ما نستلم البيانات — بغض النظر هل الفحص هيوصل
    # لصفقة مؤكدة ولا لأ، عشان يظهر للمستخدم دايمًا للمقارنة مع منصة تداوله.
    result['live_price'], result['live_time'] = _freshest_live_price(bars_by_tf)

    # 🧭 فلتر الاتجاه العام من فريم 4 ساعات — بوابة أولى قبل أي حاجة تانية. الهدف
    # منها منع تناقض الفريمات القصيرة مع الاتجاه الأكبر (وهو أكتر سبب لاحظناه
    # لرفض الصفقات وتضاربها). لو الفريم الأكبر متعادل (mixed)، ما بيمنعش الفحص.
    htf_direction = None
    if htf_bars is not None:
        r4h = full_tf_analysis(htf_bars, '4h')
        result['htf'] = r4h
        result['steps'].append(f"🧭 فريم 4 ساعات (الاتجاه العام): {r4h['overall']} — متوسط {r4h['avg_score']:.0f}%")
        if r4h['overall'] != 'mixed':
            htf_direction = r4h['overall']

    if '15m' not in bars_by_tf:
        result['per_tf'] = {'15m': None, '30m': None, '5m': None}
        result['why'] = "بيانات فريم 15 دقيقة غير متوفرة — لا يمكن بدء الفحص"
        return result
    r15 = full_tf_analysis(bars_by_tf['15m'], '15m')
    result['per_tf']['15m'] = r15
    ws15_txt = f"{r15['weighted_score']:.0f}%" if r15['weighted_score'] is not None else "—"
    result['steps'].append(f"① فريم 15m (نقطة الانطلاق / الأساس): {r15['overall']} — متوسط {r15['avg_score']:.0f}% "
                            f"| مرجّح حسب النظام: {ws15_txt} ({r15['regime']})")
    if r15['overall'] == 'mixed':
        result['per_tf']['30m'] = None; result['per_tf']['5m'] = None
        result['why'] = f"فريم 15 دقيقة (فريم الأساس) نتيجته متعادلة/متضاربة ({r15['avg_score']:.0f}%) — لا صفقة"
        return result
    direction = r15['overall']

    # ↩️ صفقة تصحيح عكس الاتجاه العام: بدل رفض أي إشارة قصيرة المدى تعاكس اتجاه
    # 4 ساعات رفضًا تامًا، نتأكد الأول هل الاختلاف ده ناتج عن ارتداد/تصحيح متوسط
    # أو عميق حصل بالفعل على الاتجاه العام (مش مجرد ضجيج قصير). لو كان تصحيح
    # حقيقي بالفعل، نسمح بالصفقة لكن بهدفين بس (TP1/TP2) بدون TP3 البعيد،
    # احترازًا من انتهاء التصحيح وارتداد السعر مع الاتجاه العام قبل ما يوصل لهدف
    # بعيد. لو التصحيح ضحل جدًا أو تجاوز بنية الحركة بالكامل (break)، بنفضل
    # نرفض الصفقة زي السابق تمامًا لعدم وضوح كفاية الفرصة.
    counter_trend_pullback = None
    if htf_direction is not None and htf_direction != direction:
        pullback = classify_pullback_depth(htf_bars, htf_direction)
        if pullback['category'] in ('medium', 'deep'):
            counter_trend_pullback = pullback
            result['steps'].append(
                f"↩️ إشارة {direction} الحالية تعاكس الاتجاه العام على 4 ساعات ({htf_direction})، لكنها "
                f"تتزامن مع تصحيح/ارتداد {_PULLBACK_AR[pullback['category']]} بعمق "
                f"{pullback['retracement_pct']:.0f}% من آخر حركة على الاتجاه العام — سيُسمح بصفقة تصحيح "
                f"محدودة (TP1 و TP2 فقط، بدون TP3) بدل رفضها بالكامل"
            )
        else:
            result['per_tf']['30m'] = None; result['per_tf']['5m'] = None
            cat_txt = _PULLBACK_AR.get(pullback['category'], pullback['category'])
            depth_txt = f" بعمق {pullback['retracement_pct']:.0f}%" if pullback['retracement_pct'] is not None else ""
            result['why'] = (f"الاتجاه العام على فريم 4 ساعات ({htf_direction}) بيعاكس اتجاه فريم 15 دقيقة "
                              f"({direction}) — تم رفض الصفقة لعدم التوافق مع الاتجاه الأكبر "
                              f"(تصنيف الوضع الحالي: {cat_txt}{depth_txt} — مش تصحيح كافي ليُعتبر فرصة قابلة للتداول)")
            return result

    w15_ok = (r15['weighted_score'] is None or
              (r15['weighted_score'] > 50.0 if direction == 'up' else r15['weighted_score'] < 50.0))
    if not w15_ok:
        result['per_tf']['30m'] = None; result['per_tf']['5m'] = None
        result['why'] = (f"فريم 15 دقيقة أعطى {direction} بعدد الأصوات، لكن الأصوات المرجّحة حسب حالة "
                          f"السوق ({r15['regime']}) خالفته ({r15['weighted_score']:.0f}%) — لا صفقة")
        return result

    if '30m' not in bars_by_tf:
        result['per_tf']['30m'] = None; result['per_tf']['5m'] = None
        result['why'] = "بيانات فريم 30 دقيقة غير متوفرة"
        return result
    r30 = full_tf_analysis(bars_by_tf['30m'], '30m')
    result['per_tf']['30m'] = r30
    result['steps'].append(f"② فريم 30m (تأكيد السياق الأعلى): {r30['overall']} — متوسط {r30['avg_score']:.0f}%")
    if r30['overall'] != direction:
        result['per_tf']['5m'] = None
        result['why'] = (f"فريم 15 دقيقة أعطى اتجاه {direction} لكن فريم 30 دقيقة خالفه "
                          f"({r30['overall']}, {r30['avg_score']:.0f}%) — توقف الفحص، لا صفقة")
        return result

    if '5m' not in bars_by_tf:
        result['per_tf']['5m'] = None
        result['why'] = "بيانات فريم 5 دقايق غير متوفرة"
        return result
    r5 = full_tf_analysis(bars_by_tf['5m'], '5m')
    result['per_tf']['5m'] = r5
    result['steps'].append(f"③ فريم 5m (تأكيد أخير): {r5['overall']} — متوسط {r5['avg_score']:.0f}%")
    score_ok = (r5['avg_score'] > 50.0) if direction == 'up' else (r5['avg_score'] < 50.0)
    w5_ok = (r5['weighted_score'] is None or
             (r5['weighted_score'] > 50.0 if direction == 'up' else r5['weighted_score'] < 50.0))
    if r5['overall'] != direction or not score_ok or not w5_ok:
        result['why'] = (f"فريم 15m و30m متفقين على {direction} لكن فريم 5 دقايق (التأكيد الأخير) "
                          f"لم يؤكد بشكل كافٍ (عادي: {r5['avg_score']:.0f}%، مرجّح: "
                          f"{r5['weighted_score']:.0f}% إن وُجد) — لا صفقة")
        return result

    trade = _build_trade(r15['analysis'], direction)
    if trade is None:
        result['why'] = "كل الفريمات متفقة لكن نسبة المخاطرة/العائد المحسوبة أقل من الحد الأدنى — تم رفض الصفقة"
        return result

    if counter_trend_pullback is not None:
        # صفقة تصحيح عكس الاتجاه العام: نكتفي بهدفين (TP1/TP2) ونلغي TP3 البعيد
        trade['tp3'] = None
        trade['limited_targets'] = True
        trade['pullback_info'] = counter_trend_pullback

    trade = _reanchor_trade_to_live_price(trade, result['live_price'], r15['analysis']['price'],
                                           atr_hint=r15['analysis'].get('atr'))
    result['confirmed'] = True
    result['direction'] = direction
    result['trade'] = trade
    return result


def council_decide_mtf(bars_by_tf: Dict[str, Bars], htf_bars: Optional[Bars] = None) -> dict:
    order = TIMEFRAMES
    per_tf = {}
    for tf in order:
        if tf not in bars_by_tf:
            continue
        council = run_council(bars_by_tf[tf])
        analysis = analyze_timeframe(bars_by_tf[tf], tf)
        weighted = regime_weighted_score(council['votes'], bool(analysis.get('trending_market', True)))
        direction_ok = council['overall'] != 'mixed'
        if direction_ok and weighted is not None:
            w_ok = (weighted > 50.0) if council['overall'] == 'up' else (weighted < 50.0)
            direction_ok = direction_ok and w_ok
        trade = None
        if direction_ok:
            trade = _build_trade(analysis, council['overall'])
            if trade is not None:
                avg_move = _avg_bar_move(bars_by_tf[tf], 30)
                tf_minutes = TF_MIN.get(tf, 30)
                eta = {}
                m1, m2, m3 = TC.tp_stage_mults
                if avg_move > 0:
                    for label, dist in (('TP1', trade['tp1_dist'] * m1),
                                         ('TP2', trade['tp1_dist'] * m2),
                                         ('TP3', trade['tp1_dist'] * m3)):
                        eta[label] = _format_duration(dist / avg_move * tf_minutes)
                else:
                    eta = {'TP1': 'غير محدد', 'TP2': 'غير محدد', 'TP3': 'غير محدد'}
                trade['eta'] = eta
                trade['bull_count'] = council['bull_count']
                trade['bear_count'] = council['bear_count']
                trade['avg_score'] = council['avg_score']
        per_tf[tf] = {'tf': tf, 'council': council, 'analysis': analysis, 'trade': trade,
                       'weighted_score': weighted}

    directions = [r['trade']['direction'] for r in per_tf.values() if r.get('trade')]
    have_all = all(tf in per_tf and per_tf[tf].get('trade') for tf in order)

    result = {'per_tf': per_tf, 'confirmed': False, 'final_trade': None, 'htf': None}

    htf_direction = None
    if htf_bars is not None:
        r4h = full_tf_analysis(htf_bars, '4h')
        result['htf'] = r4h
        if r4h['overall'] != 'mixed':
            htf_direction = r4h['overall']

    if not directions or len(set(directions)) != 1 or not have_all:
        result['why'] = "الفريمات ما اتفقتش كلها على نفس الاتجاه (أو فيها فريم بدون صفقة واضحة) — لا صفقة نهائية"
        return result

    trades = [per_tf[tf]['trade'] for tf in order if tf in per_tf]
    direction = trades[0]['direction']
    direction_updown = 'up' if direction == 'long' else 'down'

    # ↩️ نفس منطق صفقة التصحيح المستخدم في cascade: لو الفريمات القصيرة كلها
    # متفقة على اتجاه يعاكس الاتجاه العام على 4 ساعات، منرفضش فورًا — نتأكد
    # الأول هل ده تصحيح متوسط/عميق حقيقي على الاتجاه العام (وقتها نسمح بالصفقة
    # بهدفين بس)، أو مجرد ضجيج/تصحيح ضحل (وقتها نرفض زي السابق).
    counter_trend_pullback = None
    if htf_direction is not None and htf_direction != direction_updown:
        pullback = classify_pullback_depth(htf_bars, htf_direction)
        if pullback['category'] in ('medium', 'deep'):
            counter_trend_pullback = pullback
        else:
            cat_txt = _PULLBACK_AR.get(pullback['category'], pullback['category'])
            depth_txt = f" بعمق {pullback['retracement_pct']:.0f}%" if pullback['retracement_pct'] is not None else ""
            result['why'] = (f"الاتجاه العام على فريم 4 ساعات ({htf_direction}) بيعاكس اتجاه الفريمات القصيرة "
                              f"({direction_updown}) — تم رفض الصفقة لعدم التوافق مع الاتجاه الأكبر "
                              f"(تصنيف الوضع الحالي: {cat_txt}{depth_txt} — مش تصحيح كافي ليُعتبر فرصة قابلة للتداول)")
            return result

    avg = lambda k: vmean([t[k] for t in trades])
    entry = avg('entry'); stop = avg('stop')
    tp1, tp2, tp3 = avg('tp1'), avg('tp2'), avg('tp3')
    stop_dist = abs(entry - stop)
    tp1_dist = abs(tp1 - entry)
    rr = tp1_dist / max(stop_dist, 1e-9)
    total_bull = sum(t['bull_count'] for t in trades)
    total_bear = sum(t['bear_count'] for t in trades)

    final_trade = {
        'direction': direction, 'entry': entry, 'stop': stop,
        'tp1': tp1, 'tp2': tp2, 'tp3': tp3, 'rr': rr, 'stop_dist': stop_dist,
        'total_bull_votes': total_bull, 'total_bear_votes': total_bear,
        'eta_30m': trades[-1]['eta'],
    }
    if counter_trend_pullback is not None:
        # صفقة تصحيح عكس الاتجاه العام: نكتفي بهدفين (TP1/TP2) بدون TP3 البعيد
        final_trade['tp3'] = None
        final_trade['limited_targets'] = True
        final_trade['pullback_info'] = counter_trend_pullback
    live_price, live_time = _freshest_live_price(bars_by_tf)
    atr_hint = per_tf[order[0]]['analysis'].get('atr') if order[0] in per_tf else None
    final_trade = _reanchor_trade_to_live_price(final_trade, live_price, entry, atr_hint=atr_hint)

    result['confirmed'] = True
    result['live_price'] = live_price
    result['live_time'] = live_time
    result['final_trade'] = final_trade
    return result


# ============================================================
# 9) تنسيق التقارير (نصية)
# ============================================================
def format_full_tf_analysis(r: dict) -> str:
    a = r['analysis']
    lines = [f"═══ فريم {r['tf']} ═══",
             f"  السعر: {a['price']:.2f} | الاتجاه العام (SMA): {_TREND_AR.get(a['trend'], a['trend'])}",
             ""]

    lines.append("  ▸ التحليل الأساسي:")
    for v in r['basic_votes']:
        if v.score is None:
            continue
        tag = "🟢" if v.score > 50 else ("🔴" if v.score < 50 else "⚪")
        lines.append(f"     {tag} {v.name}: {v.score:.0f}%" + (f"  — {v.note}" if v.note else ""))

    lines.append("")
    lines.append("  ▸ مجلس المؤشرات:")
    for v in r['council_votes']:
        if v.score is None:
            continue
        tag = "🟢" if v.score > 50 else ("🔴" if v.score < 50 else "⚪")
        vtag = "محتسب" if v.voted else "معلوماتي"
        lines.append(f"     {tag} {v.name} [{vtag}]: {v.score:.0f}%")

    lines.append("")
    lines.append("  ▸ الشموع اليابانية:")
    for v in r['candle_votes']:
        if v.score is None:
            continue
        tag = "🟢" if v.score > 50 else ("🔴" if v.score < 50 else "⚪")
        vtag = "محتسب" if v.voted else "معلوماتي"
        lines.append(f"     {tag} {v.name} [{vtag}]: {v.score:.0f}%" + (f"  — {v.note}" if v.note else ""))

    lines.append("")
    regime_ar = "🔥 ترند واضح" if r.get('regime') == 'trending' else "〰️ سوق عرضي/متذبذب"
    ws = r.get('weighted_score')
    ws_txt = f"{ws:.0f}%" if ws is not None else "—"
    lines.append(f"  ── خلاصة فريم {r['tf']}: {r['bull_count']} صعود مقابل {r['bear_count']} هبوط "
                  f"(محايد {r['neutral_count']}) — النتيجة الإجمالية: {r['overall']} "
                  f"(متوسط {r['avg_score']:.0f}%) ──")
    lines.append(f"     نظام السوق (ADX): {regime_ar} | الأصوات المرجّحة حسب النظام: {ws_txt}")
    return "\n".join(lines)


def format_cascade_report(res: dict, symbol: str) -> str:
    lines = [f"📊 تحليل تسلسلي (15m الأساس ← 30m ← 5m) لـ {symbol}", ""]

    htf = res.get('htf')
    if htf is not None:
        htf_emoji = {'up': '🟢 صعود', 'down': '🔴 هبوط', 'mixed': '⚪ متعادل'}[htf['overall']]
        lines.append(f"🧭 الاتجاه العام (فريم 4 ساعات): {htf_emoji} — متوسط {htf['avg_score']:.0f}%")
        lines.append("")

    for tf in ["15m", "30m", "5m"]:
        r = res['per_tf'].get(tf)
        if r is None:
            lines.append(f"⚠️ فريم {tf}: بيانات غير متوفرة (أو الفحص توقف قبل الوصول له)")
            lines.append("")
            continue
        lines.append(format_full_tf_analysis(r))
        lines.append("")

    lines.append("═" * 55)
    lines.append("🔗 خطوات الفحص التسلسلي:")
    for s in res.get('steps', []):
        lines.append(f"  {s}")
    lines.append("")

    if res['confirmed']:
        t = res['trade']
        emoji = "🟢 BUY (شراء)" if t['direction'] == 'long' else "🔴 SELL (بيع)"
        lines.append(f"✅ تأكيد تسلسلي كامل عبر 15m ← 30m ← 5m — {emoji}")
        live_price = res.get('live_price')
        if live_price is not None:
            live_time = res.get('live_time')
            time_txt = live_time.strftime('%H:%M:%S UTC') if live_time else "—"
            lines.append(f"  💲 السعر اللحظي وقت التحليل: {live_price:.2f}  ({time_txt})")
            if t.get('reanchored'):
                lines.append(f"     (تمت إعادة ضبط الدخول/الوقف/الأهداف على هذا السعر بدل سعر آخر شمعة "
                              f"مقفلة {t.get('closed_bar_price', 0):.2f})")
        if t.get('limited_targets'):
            pb = t.get('pullback_info') or {}
            depth_txt = f"{pb.get('retracement_pct', 0):.0f}%" if pb.get('retracement_pct') is not None else "—"
            lines.append(f"  ⚠️ صفقة تصحيح عكس الاتجاه العام (4 ساعات) — تصحيح {_PULLBACK_AR.get(pb.get('category'), '')} "
                          f"بعمق {depth_txt} — الأهداف محدودة بـ TP1/TP2 فقط بدون TP3 احترازًا من انتهاء "
                          f"التصحيح وعودة الاتجاه العام قبل الوصول لهدف بعيد")
        lines.append(f"  الدخول (Entry) : {t['entry']:.2f}")
        lines.append(f"  الوقف (Stop)   : {t['stop']:.2f}  (مسافة {t['stop_dist']:.2f})")
        lines.append(f"  🎯 TP1: {t['tp1']:.2f}")
        lines.append(f"  🎯 TP2: {t['tp2']:.2f}")
        if t.get('tp3') is not None:
            lines.append(f"  🎯 TP3: {t['tp3']:.2f}")
        lines.append(f"  نسبة المخاطرة/العائد (TP1): 1:{t['rr']:.2f}")
        lines.append("  (مسافة الوقف والأهداف محسوبة من تحليل فريم 15 دقيقة — فريم الأساس)")
    else:
        lines.append(f"⛔ لا يوجد — {res.get('why', '')}")

    lines.append("")
    lines.append(_data_source_disclaimer())
    lines.append("⚠️ أنماط الشموع اليابانية والمؤشرات المعلّمة [بروكسي] تقريبات وصفية، مش تعريف رسمي حصري للنمط.")
    lines.append("⚠️ هذا تحليل آلي وصفي فقط، وليس توصية استثمارية.")
    return "\n".join(lines)


def format_council_report(mtf_res: dict, symbol: str) -> str:
    lines = [f"📊 تحليل مجلس المؤشرات {symbol}", ""]
    htf = mtf_res.get('htf')
    if htf is not None:
        htf_emoji = {'up': '🟢 صعود', 'down': '🔴 هبوط', 'mixed': '⚪ متعادل'}[htf['overall']]
        lines.append(f"🧭 الاتجاه العام (فريم 4 ساعات): {htf_emoji} — متوسط {htf['avg_score']:.0f}%")
        lines.append("")
    for tf in TIMEFRAMES:
        r = mtf_res['per_tf'].get(tf)
        if not r:
            lines.append(f"⚠️ فريم {tf}: بيانات غير متوفرة"); continue
        lines.append(format_council(r['council'], tf))
        if r.get('trade'):
            t = r['trade']
            emoji = "🟢 LONG" if t['direction'] == 'long' else "🔴 SHORT"
            lines.append(f"  → قرار الفريم: {emoji} | دخول {t['entry']:.2f} | وقف {t['stop']:.2f} | "
                         f"TP1 {t['tp1']:.2f} (وصول تقريبي {t['eta']['TP1']}) | R:R 1:{t['rr']:.2f}")
        else:
            lines.append("  → قرار الفريم: ⚪ لا اتجاه واضح (تعادل بالتصويت)")
        lines.append("")

    lines.append("═" * 50)
    if mtf_res['confirmed']:
        t = mtf_res['final_trade']
        emoji = "🟢 BUY (شراء)" if t['direction'] == 'long' else "🔴 SELL (بيع)"
        lines.append(f"✅ تأكيد كامل عبر {' + '.join(TIMEFRAMES)} — {emoji}")
        live_price = mtf_res.get('live_price')
        if live_price is not None:
            live_time = mtf_res.get('live_time')
            time_txt = live_time.strftime('%H:%M:%S UTC') if live_time else "—"
            lines.append(f"  💲 السعر اللحظي وقت التحليل: {live_price:.2f}  ({time_txt})")
            if t.get('reanchored'):
                lines.append(f"     (تمت إعادة ضبط الدخول/الوقف/الأهداف على هذا السعر بدل متوسط "
                              f"إغلاقات الفريمات {t.get('closed_bar_price', 0):.2f})")
        lines.append(f"  (إجمالي أصوات الصعود: {t['total_bull_votes']} | إجمالي أصوات الهبوط: {t['total_bear_votes']})")
        if t.get('limited_targets'):
            pb = t.get('pullback_info') or {}
            depth_txt = f"{pb.get('retracement_pct', 0):.0f}%" if pb.get('retracement_pct') is not None else "—"
            lines.append(f"  ⚠️ صفقة تصحيح عكس الاتجاه العام — تصحيح {_PULLBACK_AR.get(pb.get('category'), '')} "
                          f"بعمق {depth_txt} — تم الاكتفاء بـ TP1/TP2 فقط بدون TP3")
        lines.append(f"  الدخول (متوسط الفريمات): {t['entry']:.2f}")
        lines.append(f"  الوقف: {t['stop']:.2f}  (مسافة {t['stop_dist']:.2f})")
        lines.append(f"  🎯 TP1: {t['tp1']:.2f}  |  وصول تقريبي: {t['eta_30m'].get('TP1', '—')}")
        lines.append(f"  🎯 TP2: {t['tp2']:.2f}  |  وصول تقريبي: {t['eta_30m'].get('TP2', '—')}")
        if t.get('tp3') is not None:
            lines.append(f"  🎯 TP3: {t['tp3']:.2f}  |  وصول تقريبي: {t['eta_30m'].get('TP3', '—')}")
        lines.append(f"  نسبة المخاطرة/العائد (TP1): 1:{t['rr']:.2f}")
    else:
        lines.append(f"⛔ لا صفقة نهائية — {mtf_res.get('why', '')}")

    lines.append("")
    lines.append(_data_source_disclaimer())
    lines.append("⚠️ التوقيت المقدّر إحصائي فقط (بناءً على متوسط حركة السعر تاريخيًا)، مش ضمان.")
    lines.append("⚠️ هذا تحليل آلي وصفي فقط، وليس توصية استثمارية.")
    return "\n".join(lines)


def format_council_simple(mtf_res: dict, symbol: str) -> str:
    r = mtf_res['per_tf'].get("30m")
    lines = []
    if r:
        for v in r['council']['votes']:
            if v.score is None:
                continue
            tag = "محتسب" if v.voted else "معلوماتي"
            lines.append(f"{v.name} [{tag}]: {v.score:.0f}%")
    else:
        lines.append("⚠️ بيانات فريم 30 دقيقة غير متوفرة — مفيش مؤشرات تتعرض")

    missing = [tf for tf in TIMEFRAMES if tf not in mtf_res['per_tf']]
    if missing:
        lines.append(f"⚠️ فريمات ناقصة من هذه الدورة: {', '.join(missing)} — "
                      f"القرار النهائي بيتطلب كل الفريمات مع بعض")

    lines.append("")
    if mtf_res['confirmed']:
        t = mtf_res['final_trade']
        emoji = "🟢 BUY" if t['direction'] == 'long' else "🔴 SELL"
        if t.get('tp3') is not None:
            tp_txt = f"TP1 {t['tp1']:.2f} TP2 {t['tp2']:.2f} TP3 {t['tp3']:.2f}"
        else:
            tp_txt = f"TP1 {t['tp1']:.2f} TP2 {t['tp2']:.2f} (صفقة تصحيح — بدون TP3)"
        lines.append(f"{emoji} {symbol} @ {t['entry']:.2f} | SL {t['stop']:.2f} | "
                      f"{tp_txt} | R:R 1:{t['rr']:.2f}")
    else:
        lines.append("لا يوجد")
    return "\n".join(lines)


# ============================================================
# 10) وضع السوينغ (تحليل يومي/متوسط المدى) + CSV (بدون matplotlib/pandas)
# ============================================================
def _trim_by_period(bars: Bars, period: str) -> Bars:
    """يقصّ Bars حسب مدة period بسيطة زي 6mo/1y/60d (تقريبي، بعدد الشموع)."""
    unit_days = {'d': 1, 'mo': 30, 'y': 365}
    n_days = None
    p = period.strip().lower()
    for suf, mult in (('mo', 30), ('y', 365), ('d', 1)):
        if p.endswith(suf):
            try:
                n_days = int(p[:-len(suf)]) * mult
            except ValueError:
                n_days = None
            break
    if n_days is None or len(bars) < 2:
        return bars
    # تقدير عدد الشموع المطلوب من فرق الوقت بين آخر شمعتين
    try:
        delta = (bars.times[-1] - bars.times[-2]).total_seconds() / 86400.0
    except Exception:
        delta = 1.0
    if delta <= 0:
        return bars
    n_bars = max(30, int(n_days / delta))
    return bars.slice(-n_bars, None)


def print_swing_report(symbol: str, bars: Bars):
    r = full_tf_analysis(bars, "1d")
    a = r['analysis']
    last_close = bars['close'][-1]
    prev_close = bars['close'][-2] if len(bars) > 1 else last_close
    change = last_close - prev_close
    change_pct = (change / prev_close) * 100 if prev_close else 0.0

    print("=" * 62)
    print(f"  📊 تحليل سوينغ (يومي) — {symbol}")
    print(f"  🕒 {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("=" * 62)
    print(f"السعر الحالي     : {last_close:.2f}")
    arrow = "🔺" if change >= 0 else "🔻"
    print(f"التغير           : {change:+.2f} ({change_pct:+.2f}%) {arrow}")
    print(f"أعلى/أدنى آخر شمعة: {bars['high'][-1]:.2f} / {bars['low'][-1]:.2f}")
    print(f"ATR (تقلب)       : {a['atr']:.2f}")
    if a.get('sr'):
        sr = a['sr']
        res_txt = f"{sr['nearest_res']:.2f}" if sr['nearest_res'] else "—"
        sup_txt = f"{sr['nearest_sup']:.2f}" if sr['nearest_sup'] else "—"
        print(f"أقرب دعم/مقاومة  : {sup_txt} / {res_txt}")
    print("-" * 62)

    print(format_full_tf_analysis(r))
    print("-" * 62)

    if r['overall'] != 'mixed':
        trade = _build_trade(a, r['overall'], min_d=0.0, max_d=max(a['atr'] * 10, 1.0))
        if trade:
            emoji = "🟢 BUY (شراء)" if trade['direction'] == 'long' else "🔴 SELL (بيع)"
            print(f"الميل العام: {emoji}  (متوسط تصويت {r['avg_score']:.0f}%)")
            print(f"  دخول تقريبي: {trade['entry']:.2f} | وقف: {trade['stop']:.2f} "
                  f"(مسافة {trade['stop_dist']:.2f})")
            print(f"  🎯 TP1: {trade['tp1']:.2f} | TP2: {trade['tp2']:.2f} | TP3: {trade['tp3']:.2f} "
                  f"| R:R 1:{trade['rr']:.2f}")
        else:
            print(f"الميل العام: {'🟢 صاعد' if r['overall']=='up' else '🔴 هابط'} لكن نسبة المخاطرة/العائد غير كافية لصفقة واضحة")
    else:
        print("الميل العام: ⚪ متذبذب / غير حاسم")

    print("=" * 62)
    print("⚠️  تنويه: هذا تحليل فني آلي وليس توصية استثمارية.")
    print()


def export_csv(bars: Bars, out_path: str):
    o, h, l, c, vol = bars['open'], bars['high'], bars['low'], bars['close'], bars['volume']
    n = len(c)

    sma20 = sma(c, 20); sma50 = sma(c, 50); sma200 = sma(c, 200)
    rsi14 = rsi_wilder(c, 14)
    macd_line, macd_sig, macd_hist = macd(c)
    bb_u, bb_m, bb_l = bollinger_bands(c)
    atr14 = atr_wilder(h, l, c, 14)
    adx_v, plus_di_v, minus_di_v = dmi_adx_wilder(h, l, c, 14)
    k_v, d_v = stochastic_kd(h, l, c)
    cci20 = cci_series(h, l, c)
    wpr = williams_r_series(h, l, c)
    obv = obv_series(c, vol)
    mfi14 = mfi_series(h, l, c, vol)
    roc12 = roc_series(c)
    vwap = vwap_cum(h, l, c, vol)
    psar = parabolic_sar_series(h, l)

    vp = compute_volume_profile(bars)

    fieldnames = ["Date", "Open", "High", "Low", "Close", "Volume",
                  "SMA_20", "SMA_50", "SMA_200", "RSI_14",
                  "MACD", "MACD_Signal", "MACD_Hist",
                  "BB_Upper", "BB_Mid", "BB_Lower", "ATR_14",
                  "ADX", "+DI", "-DI", "Stoch_%K", "Stoch_%D",
                  "CCI_20", "Williams_%R", "OBV", "MFI_14", "ROC_12", "VWAP", "PSAR"]
    if vp:
        fieldnames += ["VP_POC", "VP_VAH", "VP_VAL", "VP_BIAS_SIGNED"]

    def fmt(v):
        return "" if isnan(v) else v

    with open(out_path, "w", newline="", encoding="utf-8-sig") as f:
        writer = csv.writer(f)
        writer.writerow(fieldnames)
        for i in range(n):
            row = [bars.times[i].strftime("%Y-%m-%d %H:%M:%S"), o[i], h[i], l[i], c[i], vol[i],
                   fmt(sma20[i]), fmt(sma50[i]), fmt(sma200[i]), fmt(rsi14[i]),
                   fmt(macd_line[i]), fmt(macd_sig[i]), fmt(macd_hist[i]),
                   fmt(bb_u[i]), fmt(bb_m[i]), fmt(bb_l[i]), fmt(atr14[i]),
                   fmt(adx_v[i]), fmt(plus_di_v[i]), fmt(minus_di_v[i]), fmt(k_v[i]), fmt(d_v[i]),
                   fmt(cci20[i]), fmt(wpr[i]), fmt(obv[i]), fmt(mfi14[i]), fmt(roc12[i]),
                   fmt(vwap[i]), fmt(psar[i])]
            if vp:
                row += [vp['poc'], vp['vah'], vp['val'], vp['bias_score_signed']]
            writer.writerow(row)

    if vp:
        print(f"ℹ️  أعمدة VP_* تمثل بروفايل الحجم اللحظي لآخر {min(I.vp_lookback_bars, len(bars))} "
              f"شمعة وقت التحليل (POC={vp['poc']:.2f}, VAH={vp['vah']:.2f}, VAL={vp['val']:.2f}) — "
              f"مش قيمة متغيّرة لكل صف.")
    print(f"💾 تم حفظ البيانات مع كل المؤشرات في: {out_path}")


# ============================================================
# 11) دوال التشغيل (Swing / Council / Cascade) + CLI
# ============================================================
def run_swing_once(symbol: str, period: str, interval: str, csv_out: Optional[str]):
    tf = interval if interval in TF_MIN else "1d"
    bars = fetch_klines(symbol, tf, limit=5000)
    bars = _trim_by_period(bars, period)
    if len(bars) < 60:
        print(f"❌ بيانات غير كافية ({len(bars)} شمعة) لتحليل موثوق.")
        return
    print_swing_report(symbol, bars)
    if csv_out:
        export_csv(bars, csv_out)


def _fetch_htf_bars(symbol: str, tf_label: str = "4h", min_bars: int = 60) -> Optional[Bars]:
    """يجلب بيانات الفريم الأعلى (4 ساعات) لاستخدامه كفلتر اتجاه عام. فشل جلبه
    مش خطأ قاتل — الفحص بيكمل من غيره (بس من غير فلتر الاتجاه الأكبر)."""
    try:
        bars = fetch_klines(symbol, tf_label, limit=300)
    except FetchErr as e:
        logger.warning("فريم %s (فلتر الاتجاه العام): %s", tf_label, e)
        return None
    bars = bars.slice(0, -1)
    if len(bars) < min_bars:
        logger.warning("فريم %s: بيانات غير كافية (%d شمعة) لفلتر الاتجاه العام", tf_label, len(bars))
        return None
    return bars


def run_council_once(symbol: str, print_out: bool = True, full: bool = False) -> str:
    bars_by_tf = fetch_multi_tf(symbol, TIMEFRAMES, min_bars=60)
    if not bars_by_tf:
        msg = "❌ تعذر جلب بيانات كافية لأي فريم."
        if print_out:
            print(msg)
        return msg
    htf_bars = _fetch_htf_bars(symbol)
    mtf_res = council_decide_mtf(bars_by_tf, htf_bars)
    text = format_council_report(mtf_res, symbol) if full else format_council_simple(mtf_res, symbol)
    if print_out:
        print(text)
    return text


def run_cascade_once(symbol: str, print_out: bool = True) -> str:
    bars_by_tf = fetch_multi_tf(symbol, TIMEFRAMES, min_bars=60)
    if not bars_by_tf:
        msg = "❌ تعذر جلب بيانات كافية لأي فريم."
        if print_out:
            print(msg)
        return msg
    htf_bars = _fetch_htf_bars(symbol)
    res = council_decide_cascade(bars_by_tf, htf_bars)
    text = format_cascade_report(res, symbol)
    if print_out:
        print(text)
    return text


def _run_live(fn, label: str, interval_s: int = SCAN_CYCLE_S):
    interval_s = max(int(interval_s), 5)  # حماية من قيمة صغيرة جدًا تضغط على حد الـ API
    print(f"🔄 وضع {label} المستمر — تحديث كل {interval_s} ثانية (Ctrl+C للإيقاف)")
    try:
        while True:
            try:
                fn()
            except FetchErr as e:
                logger.error("%s", e)
            except Exception as e:
                logger.error("خطأ غير متوقع: %s", e)
            print(f"⏱ {datetime.now().strftime('%H:%M:%S')}")
            time.sleep(interval_s)
    except KeyboardInterrupt:
        print("\n⏹ تم الإيقاف.")


def main():
    parser = argparse.ArgumentParser(description="Gold Pro Analyzer — محلل الذهب الاحترافي الموحّد")
    sub = parser.add_subparsers(dest="mode", required=True)

    # مشتركة بين كل الأوضاع: اختيار مصدر البيانات
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--provider", choices=["yahoo", "twelvedata"], default="yahoo",
                         help="مصدر البيانات: yahoo (افتراضي، بدون مفتاح) أو twelvedata (أدق للسبوت، محتاج مفتاح)")
    common.add_argument("--api-key", default=None,
                         help="مفتاح Twelve Data (أو خلّيه فاضي واستخدم متغير البيئة "
                              "TWELVEDATA_API_KEY أو VIPER_API_KEY)")
    common.add_argument("--symbol", default=None,
                         help="افتراضيًا: GC=F مع yahoo أو XAU/USD مع twelvedata")

    sw = sub.add_parser("swing", parents=[common], help="تحليل سوينغ يومي/متوسط المدى")
    sw.add_argument("--period", default="6mo")
    sw.add_argument("--interval", default="1d", help="1d أو 1h ...")
    sw.add_argument("--csv", default=None)

    co = sub.add_parser("council", parents=[common], help="مجلس المؤشرات على 3 فريمات (5m/15m/30m)")
    co.add_argument("--full", action="store_true")
    co.add_argument("--live", action="store_true")
    co.add_argument("--poll", type=int, default=SCAN_CYCLE_S,
                     help=f"المدة بالثواني بين كل تحديث في وضع --live (افتراضي {SCAN_CYCLE_S}) — "
                          f"زوّدها لو النت بطيء أو بيحصل Timeout كتير")

    ca = sub.add_parser("cascade", parents=[common], help="فحص تسلسلي متشدد 15m←30m←5m لسكالبينغ")
    ca.add_argument("--live", action="store_true")
    ca.add_argument("--poll", type=int, default=SCAN_CYCLE_S,
                     help=f"المدة بالثواني بين كل تحديث في وضع --live (افتراضي {SCAN_CYCLE_S}) — "
                          f"زوّدها لو النت بطيء أو بيحصل Timeout كتير")

    args = parser.parse_args()

    api_key = args.api_key or os.environ.get("TWELVEDATA_API_KEY") or os.environ.get("VIPER_API_KEY")
    configure_provider(args.provider, api_key)
    if args.provider == "twelvedata" and not api_key:
        print("❌ اخترت --provider twelvedata لكن مفيش مفتاح API.\n"
              "   مرره عبر --api-key YOUR_KEY أو: export TWELVEDATA_API_KEY=YOUR_KEY")
        return
    symbol = args.symbol or default_symbol_for_provider()

    if args.mode == "swing":
        run_swing_once(symbol, args.period, args.interval, args.csv)
    elif args.mode == "council":
        if args.live:
            _run_live(lambda: run_council_once(symbol, print_out=True, full=args.full), "council",
                       interval_s=args.poll)
        else:
            run_council_once(symbol, print_out=True, full=args.full)
    elif args.mode == "cascade":
        if args.live:
            _run_live(lambda: run_cascade_once(symbol, print_out=True), "cascade", interval_s=args.poll)
        else:
            run_cascade_once(symbol, print_out=True)


if __name__ == "__main__":
    main()


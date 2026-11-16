# -*- coding: utf-8 -*-
"""
GOLD PRO ANALYZER V2
Educational market-analysis dashboard for XAU/USD.
Dependencies: kivy, requests
No broker connection and no automatic order execution.
"""

import csv
import json
import math
import os
import threading
from datetime import datetime

import requests

from kivy.app import App
from kivy.clock import Clock
from kivy.graphics import Color, Line, Rectangle
from kivy.metrics import dp
from kivy.properties import ListProperty, StringProperty
from kivy.uix.boxlayout import BoxLayout
from kivy.uix.button import Button
from kivy.uix.gridlayout import GridLayout
from kivy.uix.label import Label
from kivy.uix.textinput import TextInput
from kivy.uix.widget import Widget
from kivy.uix.scrollview import ScrollView
from kivy.utils import get_color_from_hex
from kivy.core.text import LabelBase

# Use the bundled Arabic font first, so the app does not depend on
# which fonts happen to be installed on the Android device.
_APP_DIR = os.path.dirname(os.path.abspath(__file__))
ARABIC_FONT = None
for _font_path in (
    os.path.join(_APP_DIR, "NotoKufiArabic-Regular.ttf"),
    "/system/fonts/NotoNaskhArabic-Regular.ttf",
    "/system/fonts/NotoNaskhArabicUI-Regular.ttf",
    "/system/fonts/NotoSansArabic-Regular.ttf",
    "/system/fonts/DroidSansArabic.ttf",
):
    if os.path.isfile(_font_path):
        ARABIC_FONT = _font_path
        break

try:
    import arabic_reshaper
    from bidi.algorithm import get_display
    ARABIC_SHAPING_AVAILABLE = True
except Exception:
    arabic_reshaper = None
    get_display = None
    ARABIC_SHAPING_AVAILABLE = False


# -------------------- SETTINGS --------------------

API_URL = "https://api.twelvedata.com/time_series"
SYMBOL = "XAU/USD"
INTERVAL = "5min"
OUTPUT_SIZE = 200
AUTO_REFRESH_SECONDS = 60
RISK_PERCENT = 1.0
APP_TITLE = "GOLD PRO ANALYZER V2.3"

GOLD = get_color_from_hex("#D4AF37")
DARK = get_color_from_hex("#101114")
PANEL = get_color_from_hex("#1B1D22")
WHITE = get_color_from_hex("#F2F2F2")
MUTED = get_color_from_hex("#A7A9AE")
GREEN = get_color_from_hex("#42C98A")
RED = get_color_from_hex("#EF6464")


def ema(values, period):
    if not values:
        return []
    alpha = 2.0 / (period + 1.0)
    result = [float(values[0])]
    for value in values[1:]:
        result.append(alpha * float(value) + (1.0 - alpha) * result[-1])
    return result


def rsi(values, period=14):
    out = [None] * len(values)
    if len(values) <= period:
        return out
    gains, losses = [], []
    for i in range(1, len(values)):
        change = values[i] - values[i - 1]
        gains.append(max(change, 0.0))
        losses.append(max(-change, 0.0))
    avg_gain = sum(gains[:period]) / period
    avg_loss = sum(losses[:period]) / period
    out[period] = 100.0 if avg_loss == 0 and avg_gain > 0 else (
        50.0 if avg_loss == 0 else 100.0 - 100.0 / (1.0 + avg_gain / avg_loss)
    )
    for i in range(period + 1, len(values)):
        avg_gain = ((period - 1) * avg_gain + gains[i - 1]) / period
        avg_loss = ((period - 1) * avg_loss + losses[i - 1]) / period
        out[i] = 100.0 if avg_loss == 0 and avg_gain > 0 else (
            50.0 if avg_loss == 0 else 100.0 - 100.0 / (1.0 + avg_gain / avg_loss)
        )
    return out


def calculate_indicators(candles):
    closes = [c["close"] for c in candles]
    highs = [c["high"] for c in candles]
    lows = [c["low"] for c in candles]
    e20 = ema(closes, 20)
    e50 = ema(closes, 50)
    e12 = ema(closes, 12)
    e26 = ema(closes, 26)
    macd = [a - b for a, b in zip(e12, e26)]
    signal = ema(macd, 9)
    rsi_values = rsi(closes, 14)

    atr_values = [None] * len(candles)
    trs = []
    for i in range(len(candles)):
        if i == 0:
            tr = highs[i] - lows[i]
        else:
            prev = closes[i - 1]
            tr = max(highs[i] - lows[i],
                     abs(highs[i] - prev),
                     abs(lows[i] - prev))
        trs.append(tr)
    if len(trs) >= 14:
        current = sum(trs[:14]) / 14.0
        atr_values[13] = current
        for i in range(14, len(trs)):
            current = ((13.0 * current) + trs[i]) / 14.0
            atr_values[i] = current

    return {
        "ema20": e20[-1], "ema50": e50[-1],
        "rsi": rsi_values[-1], "macd": macd[-1],
        "macd_signal": signal[-1], "atr": atr_values[-1],
        "ema20_series": e20, "ema50_series": e50,
        "rsi_series": rsi_values
    }


class CandleChart(Widget):
    candles = ListProperty([])

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.bind(pos=self.redraw, size=self.redraw, candles=self.redraw)

    def redraw(self, *_):
        self.canvas.clear()
        with self.canvas:
            Color(*PANEL)
            Rectangle(pos=self.pos, size=self.size)
            if len(self.candles) < 2:
                return
            left = self.x + dp(12)
            right = self.right - dp(12)
            bottom = self.y + dp(12)
            top = self.top - dp(12)
            values = [v for c in self.candles[-45:] for v in (c["high"], c["low"])]
            lo, hi = min(values), max(values)
            span = max(hi - lo, 0.01)
            chart = self.candles[-45:]
            step = (right - left) / max(len(chart), 1)
            body_w = max(dp(2), step * 0.52)

            Color(0.45, 0.45, 0.45, 0.35)
            for k in range(1, 4):
                y = bottom + (top - bottom) * k / 4
                Line(points=[left, y, right, y], width=0.6)

            for i, c in enumerate(chart):
                x = left + (i + 0.5) * step
                y_high = bottom + (c["high"] - lo) / span * (top - bottom)
                y_low = bottom + (c["low"] - lo) / span * (top - bottom)
                y_open = bottom + (c["open"] - lo) / span * (top - bottom)
                y_close = bottom + (c["close"] - lo) / span * (top - bottom)
                rising = c["close"] >= c["open"]
                Color(*(GREEN if rising else RED))
                Line(points=[x, y_low, x, y_high], width=1)
                body_y = min(y_open, y_close)
                body_h = max(dp(1.5), abs(y_close - y_open))
                Rectangle(pos=(x - body_w / 2, body_y), size=(body_w, body_h))


class GoldAnalyzerApp(App):
    def build(self):
        self.title = APP_TITLE
        self.lang = "ar"  # Arabic interface
        self.candles = []
        self.last_analysis = None
        self.busy = False
        self.balance = 1000.0
        self.history_path = None

        root = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(6))
        root.canvas.before.clear()
        with root.canvas.before:
            Color(*DARK)
            self.bg = Rectangle(pos=root.pos, size=root.size)
        root.bind(pos=self._update_bg, size=self._update_bg)

        header = BoxLayout(size_hint_y=None, height=dp(48), spacing=dp(6))
        self.title_label = Label(text="[b]محلل الذهب الاحترافي[/b] [color=#D4AF37]V2.3[/color]",
                                 markup=True, color=WHITE, halign="left")
        header.add_widget(self.title_label)
        root.add_widget(header)

        self.status = Label(text=self.tr("جاهز للتحليل", "جاهز"),
                            size_hint_y=None, height=dp(28), color=GOLD,
                            font_name=ARABIC_FONT or "Roboto")
        root.add_widget(self.status)

        self.price_label = Label(text="XAU/USD   --", font_size="25sp",
                                 bold=True, color=GOLD, size_hint_y=None, height=dp(42),
                                 font_name="Roboto")
        root.add_widget(self.price_label)

        self.chart = CandleChart(size_hint_y=0.27)
        root.add_widget(self.chart)

        controls = GridLayout(cols=2, spacing=dp(7), size_hint_y=None, height=dp(44))
        self.api_input = TextInput(hint_text="مفتاح Twelve Data API",
                                   password=True, multiline=False,
                                   background_color=PANEL, foreground_color=WHITE,
                                   cursor_color=GOLD, font_name="Roboto")
        controls.add_widget(self.api_input)
        self.refresh_btn = self.make_button(self.tr("تحليل الآن", "حلّل الآن"),
                                            callback=self.refresh_data)
        controls.add_widget(self.refresh_btn)
        root.add_widget(controls)

        balance_row = BoxLayout(size_hint_y=None, height=dp(42), spacing=dp(7))
        self.balance_input = TextInput(text="1000", hint_text="الرصيد بالدولار",
                                       multiline=False, input_filter="float",
                                       background_color=PANEL, foreground_color=WHITE,
                                       font_name="Roboto")
        balance_row.add_widget(self.balance_input)
        self.risk_input = TextInput(text="1", hint_text="نسبة المخاطرة %",
                                    multiline=False, input_filter="float",
                                    background_color=PANEL, foreground_color=WHITE,
                                    font_name="Roboto")
        balance_row.add_widget(self.risk_input)
        root.add_widget(balance_row)

        self.result_grid = GridLayout(cols=1, spacing=dp(7), size_hint_y=None, padding=(dp(4), dp(6)))
        self.result_grid.bind(minimum_height=self.result_grid.setter("height"))
        self.result_labels = {}
        fields = [
            ("trend", "الاتجاه", "الاتجاه"),
            ("signal", "الحالة", "الإشارة"),
            ("strength", "قوة الشروط", "قوة الشروط"),
            ("rsi", "RSI 14", "RSI 14"),
            ("ema", "EMA 20 / 50", "EMA 20 / 50"),
            ("macd", "MACD", "MACD"),
            ("atr", "ATR 14", "ATR 14"),
            ("candle", "آخر شمعة مكتملة", "آخر شمعة مكتملة"),
            ("risk", "مبلغ المخاطرة النظري", "مبلغ المخاطرة النظري"),
            ("levels", "مستويات تعليمية تقديرية", "مستويات تقديرية تعليمية"),
        ]
        for key, ar, en in fields:
            label = Label(text=f"{self.shape_arabic(ar)}: --", color=WHITE,
                          halign="right", valign="middle", size_hint_y=None,
                          height=dp(58), font_size="16sp",
                          font_name="Roboto",
                          shorten=False, max_lines=3)
            label.bind(width=lambda obj, width: setattr(obj, "text_size", (width - dp(12), None)))
            label.bind(texture_size=lambda obj, size: setattr(obj, "height", max(dp(52), size[1] + dp(14))))
            self.result_labels[key] = (label, ar, en)
            self.result_grid.add_widget(label)
        results_scroll = ScrollView(size_hint=(1, 0.36), do_scroll_x=False, bar_width=dp(4))
        results_scroll.add_widget(self.result_grid)
        root.add_widget(results_scroll)

        footer = BoxLayout(size_hint_y=None, height=dp(42), spacing=dp(7))
        self.history_btn = self.make_button(self.tr("سجل التحليلات", "سجل التحليلات"),
                                            callback=self.show_history)
        footer.add_widget(self.history_btn)
        self.clear_btn = self.make_button(self.tr("مسح السجل", "مسح السجل"),
                                          callback=self.clear_history)
        footer.add_widget(self.clear_btn)
        root.add_widget(footer)

        self.disclaimer = Label(
            text=self.tr("للتعليم والمحاكاة فقط؛ ليست توصية مالية ولا تنفّذ صفقات.",
                         "للتعليم والمحاكاة فقط؛ ليست نصيحة مالية ولا تنفّذ صفقات."),
            color=MUTED, font_size="11sp", size_hint_y=None, height=dp(30),
            font_name=ARABIC_FONT or "Roboto")
        root.add_widget(self.disclaimer)

        self.history_path = os.path.join(self.user_data_dir, "analysis_history.csv")
        Clock.schedule_interval(self.auto_refresh, AUTO_REFRESH_SECONDS)
        return root

    def _update_bg(self, widget, *_):
        self.bg.pos = widget.pos
        self.bg.size = widget.size

    def shape_arabic(self, text):
        """Shape Arabic letters and apply right-to-left display when libraries exist."""
        if not isinstance(text, str):
            return text
        if ARABIC_SHAPING_AVAILABLE:
            try:
                return get_display(arabic_reshaper.reshape(text))
            except Exception:
                return text
        return text

    def tr(self, ar, en):
        return ar

    def make_button(self, text, callback, width=None):
        btn = Button(text=text, size_hint_x=None if width else 1,
                     width=width or 0, background_normal="",
                     background_color=(0.24, 0.20, 0.09, 1),
                     color=GOLD, bold=True, font_name="Roboto")
        btn.bind(on_release=lambda *_: callback())
        return btn

    def toggle_language(self):
        # This build intentionally uses English only.
        self.lang = "ar"

    def auto_refresh(self, _dt):
        if self.api_input.text.strip() and not self.busy:
            self.refresh_data()

    def refresh_data(self):
        if self.busy:
            return
        key = self.api_input.text.strip()
        if not key:
            self.status.text = self.tr("أدخل مفتاح Twelve Data أولاً",
                                       "أدخل مفتاح Twelve Data API أولاً")
            return
        try:
            balance = float(self.balance_input.text)
            risk_pct = float(self.risk_input.text)
            if balance <= 0 or not 0 < risk_pct <= 5:
                raise ValueError
        except ValueError:
            self.status.text = self.tr("تحقق من الرصيد والمخاطرة (0-5%)",
                                       "تحقق من الرصيد ونسبة المخاطرة (0-5%)")
            return

        self.busy = True
        self.refresh_btn.disabled = True
        self.status.text = self.tr("جارٍ جلب البيانات...", "جارٍ جلب بيانات السوق...")
        threading.Thread(target=self.fetch_worker,
                         args=(key, balance, risk_pct), daemon=True).start()

    def fetch_worker(self, key, balance, risk_pct):
        try:
            params = {"symbol": SYMBOL, "interval": INTERVAL,
                      "outputsize": OUTPUT_SIZE, "apikey": key,
                      "format": "JSON"}
            response = requests.get(API_URL, params=params, timeout=25)
            response.raise_for_status()
            payload = response.json()
            if "values" not in payload:
                raise RuntimeError(payload.get("message", "API returned no candle data"))
            candles = []
            for item in reversed(payload["values"]):
                candles.append({
                    "datetime": item["datetime"],
                    "open": float(item["open"]),
                    "high": float(item["high"]),
                    "low": float(item["low"]),
                    "close": float(item["close"])
                })
            if len(candles) < 60:
                raise RuntimeError("Not enough candles; need at least 60")
            indicators = calculate_indicators(candles[:-1])
            # Use the last fully completed candle; latest API row may still be forming.
            candle = candles[-2]
            price = candle["close"]
            if any(v is None or not math.isfinite(v) for v in
                   (indicators["ema20"], indicators["ema50"],
                    indicators["rsi"], indicators["macd"],
                    indicators["macd_signal"], indicators["atr"])):
                raise RuntimeError("Indicator values are incomplete; try again later")

            checks_up = [
                indicators["ema20"] > indicators["ema50"],
                indicators["macd"] > indicators["macd_signal"],
                indicators["rsi"] > 50,
                price > indicators["ema20"]
            ]
            checks_down = [
                indicators["ema20"] < indicators["ema50"],
                indicators["macd"] < indicators["macd_signal"],
                indicators["rsi"] < 50,
                price < indicators["ema20"]
            ]
            up = sum(checks_up)
            down = sum(checks_down)
            if up >= 3:
                signal, trend = "BULLISH", "UP"
                strength = up / 4 * 100
            elif down >= 3:
                signal, trend = "BEARISH", "DOWN"
                strength = down / 4 * 100
            else:
                signal, trend = "NEUTRAL", "SIDEWAYS / MIXED"
                strength = max(up, down) / 4 * 100

            atr = indicators["atr"]
            # Illustrative ATR distances, not a trade instruction.
            if signal == "BULLISH":
                levels = (price - 1.5 * atr, price + 1.5 * atr, price + 3 * atr)
            elif signal == "BEARISH":
                levels = (price + 1.5 * atr, price - 1.5 * atr, price - 3 * atr)
            else:
                levels = None

            result = {
                "price": price, "candle": candle["datetime"],
                "ind": indicators, "signal": signal, "trend": trend,
                "strength": strength, "balance": balance,
                "risk_amount": balance * risk_pct / 100.0,
                "risk_pct": risk_pct, "levels": levels,
                "candles": candles[-60:]
            }
            Clock.schedule_once(lambda _dt: self.fetch_success(result), 0)
        except Exception as exc:
            message = str(exc)
            Clock.schedule_once(lambda _dt: self.fetch_error(message), 0)

    def fetch_success(self, result):
        self.busy = False
        self.refresh_btn.disabled = False
        self.last_analysis = result
        self.candles = result["candles"]
        self.chart.candles = self.candles
        self.price_label.text = f"XAU/USD   {result['price']:.3f} USD"
        self.display_analysis(result)
        self.status.text = self.tr("تم تحديث البيانات: ", "تم التحديث: ") + datetime.now().strftime("%H:%M:%S")
        self.save_history(result)

    def fetch_error(self, message):
        self.busy = False
        self.refresh_btn.disabled = False
        self.status.text = self.tr("تعذر جلب البيانات: ", "خطأ في البيانات: ") + message[:100]

    def display_analysis(self, r):
        i = r["ind"]
        labels = self.result_labels
        values = {
            "trend": r["trend"],
            "signal": r["signal"],
            "strength": f"{r['strength']:.0f}%",
            "rsi": f"{i['rsi']:.2f}",
            "ema": f"{i['ema20']:.3f} / {i['ema50']:.3f}",
            "macd": f"{i['macd']:.5f} / {i['macd_signal']:.5f}",
            "atr": f"{i['atr']:.3f}",
            "candle": r["candle"],
            "risk": f"{r['risk_amount']:.2f} USD ({r['risk_pct']:.2f}%)",
            "levels": "—" if not r["levels"] else
                f"SL* {r['levels'][0]:.3f} | T1* {r['levels'][1]:.3f} | T2* {r['levels'][2]:.3f}"
        }
        for key, (label, ar, en) in labels.items():
            heading = self.shape_arabic(ar) if self.lang == "ar" else en
            label.text = f"{heading}: {values[key]}"
            label.halign = "right" if self.lang == "ar" else "left"
            label.color = (GREEN if r["signal"] == "BULLISH" else
                           RED if r["signal"] == "BEARISH" else WHITE)
        self.result_grid.do_layout()

    def save_history(self, result):
        try:
            exists = os.path.exists(self.history_path)
            with open(self.history_path, "a", newline="", encoding="utf-8") as f:
                writer = csv.writer(f)
                if not exists:
                    writer.writerow(["saved_at", "candle_time", "price", "signal",
                                     "rsi", "ema20", "ema50", "strength"])
                writer.writerow([datetime.now().isoformat(timespec="seconds"),
                                 result["candle"], result["price"],
                                 result["signal"], result["ind"]["rsi"],
                                 result["ind"]["ema20"], result["ind"]["ema50"],
                                 result["strength"]])
        except Exception:
            pass

    def show_history(self):
        if not os.path.exists(self.history_path):
            self.status.text = self.tr("لا يوجد سجل بعد", "لا يوجد سجل بعد")
            return
        try:
            with open(self.history_path, "r", encoding="utf-8") as f:
                rows = list(csv.reader(f))
            recent = rows[-8:]
            lines = [" | ".join(row[:4]) for row in recent]
            self.status.text = "  •  ".join(lines)[-220:]
        except Exception as exc:
            self.status.text = str(exc)[:100]

    def clear_history(self):
        try:
            if os.path.exists(self.history_path):
                os.remove(self.history_path)
            self.status.text = self.tr("تم مسح سجل التحليلات",
                                       "تم مسح سجل التحليلات")
        except Exception as exc:
            self.status.text = str(exc)[:100]


if __name__ == "__main__":
    GoldAnalyzerApp().run()

# -*- coding: utf-8 -*-
import threading, time, requests, traceback, csv, os, json
from datetime import datetime, timezone

from kivy.app import App
from kivy.clock import Clock
from kivy.graphics import Color, RoundedRectangle
from kivy.metrics import dp
from kivy.properties import StringProperty
from kivy.uix.boxlayout import BoxLayout
from kivy.uix.button import Button
from kivy.uix.gridlayout import GridLayout
from kivy.uix.label import Label
from kivy.uix.scrollview import ScrollView
from kivy.uix.textinput import TextInput
from kivy.uix.widget import Widget
from kivy.utils import get_color_from_hex
from kivy.core.window import Window

# منع الشاشة من الإطفاء أثناء عمل البوت
Window.allow_screensaver = False

# -------------------- COLORS --------------------
BG      = get_color_from_hex("#0B0D10")
CARD    = get_color_from_hex("#161A1F")
CARD2   = get_color_from_hex("#1F242B")
GOLD    = get_color_from_hex("#E8B923")
WHITE   = get_color_from_hex("#F5F6F7")
MUTED   = get_color_from_hex("#8B929E")
GREEN   = get_color_from_hex("#3FCC88")
RED     = get_color_from_hex("#EF5B5B")
ORANGE  = get_color_from_hex("#F5A623")
BLUE    = get_color_from_hex("#4A9EFF")

# -------------------- CONFIG --------------------
API_URL = "https://api.twelvedata.com/time_series"
SYMBOL  = "XAU/USD"
DXY_SYMBOL = "DXY"
US10Y_SYMBOL = "US10Y"

AUTO_PILOT_INTERVAL = 60 
ENFORCE_SESSION = False 
SESSION_START_HOUR = 12
SESSION_END_HOUR   = 18

ATR_PERIOD          = 14
ADX_THRESHOLD       = 20
MOMENTUM_CUSHION    = 1.2
SL_ATR_MULT         = 1.8
TP1_ATR_MULT        = 1.5
TP2_ATR_MULT        = 3.0
MIN_RR              = 1.2
MAX_RISK_PCT        = 2.0
MAX_DRAWDOWN_PCT    = 8.0
KELLY_FRACTION      = 0.5

NEWS_API_URL        = "https://fcsapi.com/api-v4/forex/economy_cal"
NEWS_API_KEY        = "" 
NEWS_BLACKOUT_BEFORE = 30
NEWS_BLACKOUT_AFTER  = 45
LOG_FILE = "signals_log.csv"
CONFIG_FILE = "bot_settings.json" # ملف حفظ الإعدادات

# -------------------- INDICATORS --------------------
def ema(v, p):
    if not v or len(v) < p: return [None]*len(v)
    a = 2.0/(p+1.0); o = [None]*len(v); o[p-1] = sum(v[:p])/p
    for i in range(p, len(v)): o[i] = a*v[i] + (1-a)*o[i-1]
    return o

def true_range(h, l, c):
    t = [None]*len(c)
    for i in range(1, len(c)):
        t[i] = max(h[i]-l[i], abs(h[i]-c[i-1]), abs(l[i]-c[i-1]))
    return t

def atr(h, l, c, p=14):
    t = true_range(h, l, c)
    if len(t) < p+1: return [None]*len(c)
    o = [None]*len(c); o[p] = sum(t[1:p+1])/p
    for i in range(p+1, len(t)): o[i] = ((p-1)*o[i-1] + t[i])/p
    return o

def rsi(v, p=14):
    o = [None]*len(v)
    if len(v) <= p: return o
    g, l = [], []
    for i in range(1, len(v)):
        ch = v[i]-v[i-1]; g.append(max(ch, 0.0)); l.append(max(-ch, 0.0))
    ag = sum(g[:p])/p; al = sum(l[:p])/p
    def vv(g, l): return 100.0 if l == 0 and g > 0 else (50.0 if l == 0 else 100-100/(1+g/l))
    o[p] = vv(ag, al)
    for i in range(p+1, len(v)):
        ag = ((p-1)*ag + g[i-1])/p; al = ((p-1)*al + l[i-1])/p; o[i] = vv(ag, al)
    return o

def adx(h, l, c, p=14):
    n = len(c)
    if n < p*2: return [None]*n
    t = true_range(h, l, c); pdm, mdm = [0.0]*n, [0.0]*n
    for i in range(1, n):
        up = h[i]-h[i-1]; dn = l[i-1]-l[i]
        pdm[i] = up if (up > dn and up > 0) else 0.0
        mdm[i] = dn if (dn > up and dn > 0) else 0.0
    def sm(a, pp):
        o = [None]*n; s = sum(a[1:pp+1]); o[pp] = s
        for i in range(pp+1, n): s = s - s/pp + a[i]; o[i] = s
        return o
    ts, ps, ms = sm(t, p), sm(pdm, p), sm(mdm, p)
    pdi, mdi, dx = [None]*n, [None]*n, [None]*n
    for i in range(p, n):
        if ts[i] and ts[i] > 0:
            pdi[i] = 100*ps[i]/ts[i]; mdi[i] = 100*ms[i]/ts[i]
            if pdi[i]+mdi[i] > 0: dx[i] = 100*abs(pdi[i]-mdi[i])/(pdi[i]+mdi[i])
    o = [None]*n; vd = [x for x in dx[p:] if x is not None]
    if len(vd) >= p:
        f = sum(vd[:p])/p; s2 = p*2
        if s2 < n:
            o[s2] = f
            for i in range(s2+1, n):
                if dx[i] is not None and o[i-1] is not None:
                    o[i] = (o[i-1]*(p-1) + dx[i])/p
    return o

def cci(h, l, c, p=20):
    n = len(c); tp = [(h[i]+l[i]+c[i])/3.0 for i in range(n)]; o = [None]*n
    for i in range(p-1, n):
        w = tp[i-p+1:i+1]; s = sum(w)/p
        md = sum(abs(x-s) for x in w)/p
        o[i] = 0.0 if md == 0 else (tp[i]-s)/(0.015*md)
    return o

def vwap_calc(h, l, c, v):
    n = len(c); o = [None]*n; tpv = 0.0; vol = 0.0
    for i in range(n):
        tp = (h[i]+l[i]+c[i])/3.0
        tpv += tp*v[i]; vol += v[i]
        o[i] = tpv/vol if vol > 0 else None
    return o

def ema_slope(e, lookback=5):
    if len(e) < lookback + 1 or e[-1] is None or e[-lookback-1] is None: return 0
    if e[-1] > e[-lookback-1]: return 1
    if e[-1] < e[-lookback-1]: return -1
    return 0

def rsi_divergence(c, r, lookback=20):
    if len(c) < lookback or r[-1] is None: return 0
    window_c = c[-lookback:]; window_r = [x for x in r[-lookback:] if x is not None]
    if len(window_r) < lookback // 2: return 0
    high_idx = window_c.index(max(window_c)); low_idx = window_c.index(min(window_c))
    if high_idx > lookback//2 and window_c[-1] > window_c[high_idx-5]:
        if window_r[-1] < max(window_r) * 0.95: return -1
    if low_idx > lookback//2 and window_c[-1] < window_c[low_idx-5]:
        if window_r[-1] > min(window_r) * 1.05: return 1
    return 0

# -------------------- SMC --------------------
def fvg(h, l):
    b, br = [], []
    for i in range(2, len(h)):
        if l[i] > h[i-2]: b.append(i)
        if h[i] < l[i-2]: br.append(i)
    return b, br

def ob(o, h, l, c, lb=5):
    b, br = [], []
    for i in range(lb, len(c)):
        mv = c[i]-c[i-lb]; ap = sum(h[j]-l[j] for j in range(i-lb, i))/lb
        if ap <= 0: continue
        if mv > 1.5*ap:
            for j in range(i-1, max(i-lb*2, 0), -1):
                if c[j] < o[j]: b.append(j); break
        if mv < -1.5*ap:
            for j in range(i-1, max(i-lb*2, 0), -1):
                if c[j] > o[j]: br.append(j); break
    return b, br

def sweeps(h, l, c):
    s = []
    for i in range(10, len(c)):
        sh = max(h[i-10:i-2]); sl = min(l[i-10:i-2])
        if h[i] > sh and c[i] < sh: s.append(("bearish", i))
        if l[i] < sl and c[i] > sl: s.append(("bullish", i))
    return s

def smc_score(o, h, l, c, direction):
    bob, beob = ob(o, h, l, c); bf, bef = fvg(h, l); sw = sweeps(h, l, c)
    score = 0
    if direction == "BUY":
        if len(bob) > 0: score += 8
        if len(bf) > 0: score += 6
        if any(t == "bullish" for t, _ in sw[-3:]): score += 6
    else:
        if len(beob) > 0: score += 8
        if len(bef) > 0: score += 6
        if any(t == "bearish" for t, _ in sw[-3:]): score += 6
    return min(score, 20)

# -------------------- HELPERS --------------------
def is_news_blackout():
    if not NEWS_API_KEY: return False
    try:
        r = requests.get(NEWS_API_URL, params={"symbol": "XAUUSD", "importance": "2", "access_key": NEWS_API_KEY}, timeout=5).json()
        if not r.get("status"): return False
        now = datetime.now(timezone.utc)
        for ev in r.get("response", []):
            try: et = datetime.fromisoformat(ev["date"].replace("Z", "+00:00"))
            except Exception: continue
            db = (et-now).total_seconds()/60.0
            if -NEWS_BLACKOUT_AFTER <= db <= NEWS_BLACKOUT_BEFORE: return True
        return False
    except Exception: return True

def is_session_active():
    hour = datetime.now(timezone.utc).hour
    return SESSION_START_HOUR <= hour < SESSION_END_HOUR

def log_signal(sig, price, sl, tp1, tp2, conf, intermarket):
    file_exists = os.path.isfile(LOG_FILE)
    with open(LOG_FILE, mode='a', newline='', encoding='utf-8') as f:
        writer = csv.writer(f)
        if not file_exists:
            writer.writerow(["Time_UTC", "Signal", "Price", "SL", "TP1", "TP2", "Confidence", "DXY_Trend", "US10Y_Trend"])
        writer.writerow([datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M"), sig, f"{price:.2f}", f"{sl:.2f}", f"{tp1:.2f}", f"{tp2:.2f}", conf, intermarket['dxy'], intermarket['us10y']])

# -------------------- CONFIDENCE SCORING --------------------
def compute_signal(price, e9, e20, e50, e200, htf_bull, rsi_v, adx_v, cci_v, vwap_v, atr_v, o, h, l, c, vol, e50_slope, intermarket):
    result = {"signal": "WAIT", "confidence": 0, "direction": None, "sl": None, "tp1": None, "tp2": None, "score_parts": {}, "reasons": []}
    if adx_v is None or atr_v is None or atr_v <= 0: return result
    if htf_bull and price > e200 and e9 > e20: direction = "BUY"
    elif (not htf_bull) and price < e200 and e9 < e20: direction = "SELL"
    else: return result

    result["direction"] = direction
    scores = {}
    trend_score = 25 if adx_v >= 30 else (20 if adx_v >= 25 else (15 if adx_v >= ADX_THRESHOLD else 0))
    if trend_score == 0: result["reasons"].append("ADX weak")
    scores["Trend"] = trend_score

    ema_score = 0
    if direction == "BUY":
        if e9 > e20 > e50: ema_score += 10
        if e50 > e200: ema_score += 5
        if e50_slope == 1: ema_score += 5
    else:
        if e9 < e20 < e50: ema_score += 10
        if e50 < e200: ema_score += 5
        if e50_slope == -1: ema_score += 5
    scores["EMA"] = ema_score

    mom_score = 0
    if direction == "BUY":
        if 40 < rsi_v < 70: mom_score += 8
        if cci_v > 0: mom_score += 6
        if rsi_v > 50: mom_score += 6
    else:
        if 30 < rsi_v < 60: mom_score += 8
        if cci_v < 0: mom_score += 6
        if rsi_v < 50: mom_score += 6
    div = rsi_divergence(c, rsi(c, 14), 20)
    if (direction == "BUY" and div == 1) or (direction == "SELL" and div == -1): mom_score += 5 
    elif (direction == "BUY" and div == -1) or (direction == "SELL" and div == 1): mom_score = max(0, mom_score - 8)
    scores["Momentum"] = min(mom_score, 20)

    scores["SMC"] = smc_score(o, h, l, c, direction)

    vwap_score = 0
    if vwap_v is not None:
        dist = abs(price - vwap_v)
        if dist < 0.5 * atr_v: vwap_score = 15
        elif dist < 1.0 * atr_v: vwap_score = 10
        elif dist < 2.0 * atr_v: vwap_score = 5
        else: return result
        if direction == "BUY" and price < vwap_v: vwap_score = max(0, vwap_score - 8)
        if direction == "SELL" and price > vwap_v: vwap_score = max(0, vwap_score - 8)
    scores["VWAP"] = vwap_score

    inter_score = 0
    if direction == "BUY":
        if intermarket["dxy"] == -1: inter_score += 10
        if intermarket["us10y"] == -1: inter_score += 10
        if intermarket["dxy"] == 1: return result
    else:
        if intermarket["dxy"] == 1: inter_score += 10
        if intermarket["us10y"] == 1: inter_score += 10
        if intermarket["dxy"] == -1: return result
    scores["Macro"] = inter_score

    total = sum(scores.values())
    result["confidence"] = total
    result["score_parts"] = scores

    if total < 55: return result

    if direction == "BUY":
        sl = price - SL_ATR_MULT * atr_v
        tp1 = price + TP1_ATR_MULT * atr_v
        tp2 = price + TP2_ATR_MULT * atr_v
    else:
        sl = price + SL_ATR_MULT * atr_v
        tp1 = price - TP1_ATR_MULT * atr_v
        tp2 = price - TP2_ATR_MULT * atr_v

    if abs(price - sl) == 0 or abs(tp2 - price)/abs(price - sl) < MIN_RR: return result

    result["signal"] = direction
    result["sl"] = sl; result["tp1"] = tp1; result["tp2"] = tp2
    return result

# -------------------- CUSTOM WIDGETS --------------------
class Card(BoxLayout):
    def __init__(self, bg=CARD, radius=10, **kw):
        super().__init__(**kw)
        self._radius = radius
        with self.canvas.before:
            Color(*bg); self._rect = RoundedRectangle(pos=self.pos, size=self.size, radius=[dp(radius)])
        self.bind(pos=self._u, size=self._u)
    def _u(self, *a):
        self._rect.pos = self.pos; self._rect.size = self.size

class ConfidenceBar(Widget):
    def __init__(self, **kw):
        super().__init__(**kw)
        self._value = 0
        with self.canvas:
            Color(*CARD2); self._bg = RoundedRectangle(pos=self.pos, size=self.size, radius=[dp(5)])
            Color(*MUTED); self._fill = RoundedRectangle(pos=self.pos, size=(0, self.size[1]), radius=[dp(5)])
        self.bind(pos=self._u, size=self._u)
    def _u(self, *a):
        self._bg.pos = self.pos; self._bg.size = self.size
        w = self.size[0] * (self._value / 100.0)
        self._fill.pos = self.pos; self._fill.size = (w, self.size[1])
    def set_value(self, v, color):
        self._value = max(0, min(100, v))
        self.canvas.clear()
        with self.canvas:
            Color(*CARD2); self._bg = RoundedRectangle(pos=self.pos, size=self.size, radius=[dp(5)])
            Color(*color); self._fill = RoundedRectangle(pos=self.pos, size=(0, self.size[1]), radius=[dp(5)])
        self._u()

class Dot(Widget):
    def __init__(self, color=GREEN, size_=10, **kw):
        super().__init__(size_hint=(None, None), size=(dp(size_), dp(size_)), **kw)
        with self.canvas:
            Color(*color); self._dot = RoundedRectangle(pos=self.pos, size=self.size, radius=[self.size[0]/2])
        self.bind(pos=self._u, size=self._u)
    def _u(self, *a):
        self._dot.pos = self.pos; self._dot.size = self.size; self._dot.radius = [self.size[0]/2]

# -------------------- APP --------------------
class GoldApp(App):
    current_interval = StringProperty("15min")

    def build(self):
        self.active_trade = None
        self.auto_event = None
        try: return self._build_ui()
        except Exception as e: return self._error(f"build() crash:\n{e}")

    def _error(self, msg):
        sv = ScrollView(); box = BoxLayout(orientation="vertical", padding=dp(15), size_hint_y=None)
        box.bind(minimum_height=box.setter("height"))
        lbl = Label(text=msg, color=RED, size_hint_y=None)
        lbl.bind(width=lambda *a: setattr(lbl, "text_size", (lbl.width, None)))
        lbl.bind(texture_size=lambda *a: setattr(lbl, "height", lbl.texture_size[1]))
        box.add_widget(lbl); sv.add_widget(box); return sv

    # حفظ واسترجاع الإعدادات
    def load_settings(self):
        if os.path.exists(CONFIG_FILE):
            try:
                with open(CONFIG_FILE, "r") as f:
                    return json.load(f)
            except: pass
        return {}

    def save_settings(self):
        data = {
            "api_key": self.api_input.text.strip(),
            "tg_token": self.tg_token_input.text.strip(),
            "tg_chat": self.tg_chat_input.text.strip(),
            "balance": self.bal_input.text.strip(),
            "risk": self.risk_input.text.strip(),
            "lot": self.lot_input.text.strip()
        }
        with open(CONFIG_FILE, "w") as f:
            json.dump(data, f)

    def _build_ui(self):
        self.title = "Gold Pro V17"
        self.busy = False; self.peak = None; self.current_bal = None
        
        settings = self.load_settings()
        
        main_scroll = ScrollView()
        root = BoxLayout(orientation="vertical", padding=dp(8), spacing=dp(8), size_hint_y=None)
        root.bind(minimum_height=root.setter("height"))
        main_scroll.add_widget(root)

        # ============ HEADER ============
        header = Card(bg=CARD, size_hint_y=None, height=dp(52), padding=[dp(12), dp(8)], spacing=dp(8))
        header.add_widget(Label(text="GOLD PRO", bold=True, color=GOLD, font_size="18sp", size_hint_x=0.4))
        header.add_widget(Label(text="V17", color=MUTED, font_size="11sp", size_hint_x=0.1))
        self.tf_btn = Button(text="15M", size_hint_x=0.2, background_normal="", background_color=CARD2, color=GOLD, font_size="13sp", bold=True)
        self.tf_btn.bind(on_release=self._toggle_tf)
        header.add_widget(self.tf_btn)
        status_box = BoxLayout(orientation="horizontal", spacing=dp(6), size_hint_x=0.3)
        self.dot_api = Dot(GREEN); status_box.add_widget(self.dot_api)
        status_box.add_widget(Label(text="API", color=MUTED, font_size="10sp"))
        self.dot_session = Dot(GREEN); status_box.add_widget(self.dot_session)
        status_box.add_widget(Label(text="SES", color=MUTED, font_size="10sp"))
        header.add_widget(status_box)
        root.add_widget(header)

        # ============ INPUT CARD ============
        inp_card = Card(bg=CARD, size_hint_y=None, height=dp(180), padding=dp(10), spacing=dp(8), orientation="vertical")
        
        self.api_input = TextInput(text=settings.get("api_key", ""), hint_text="TwelveData API Key", password=True, multiline=False, size_hint_y=None, height=dp(38), background_color=CARD2, foreground_color=WHITE, hint_text_color=MUTED, padding=[dp(10), dp(10)])
        inp_card.add_widget(self.api_input)
        
        tg_row = GridLayout(cols=2, spacing=dp(6), size_hint_y=None, height=dp(38))
        self.tg_token_input = TextInput(text=settings.get("tg_token", ""), hint_text="Telegram Token", password=True, multiline=False, background_color=CARD2, foreground_color=WHITE, hint_text_color=MUTED, padding=[dp(10), dp(10)])
        self.tg_chat_input = TextInput(text=settings.get("tg_chat", ""), hint_text="Chat ID", multiline=False, background_color=CARD2, foreground_color=WHITE, hint_text_color=MUTED, padding=[dp(10), dp(10)])
        tg_row.add_widget(self.tg_token_input); tg_row.add_widget(self.tg_chat_input)
        inp_card.add_widget(tg_row)

        row = GridLayout(cols=3, spacing=dp(6), size_hint_y=None, height=dp(38))
        def mk_input(text_val, hint):
            return TextInput(text=text_val, hint_text=hint, multiline=False, input_filter="float", background_color=CARD2, foreground_color=WHITE, hint_text_color=MUTED, padding=[dp(10), dp(10)])
        
        self.bal_input = mk_input(settings.get("balance", "1000"), "Balance")
        self.risk_input = mk_input(settings.get("risk", "1.0"), "Risk %")
        self.lot_input = mk_input(settings.get("lot", "0.01"), "Min Lot")
        row.add_widget(self.bal_input); row.add_widget(self.risk_input); row.add_widget(self.lot_input)
        inp_card.add_widget(row)
        root.add_widget(inp_card)

        # ============ ACTIVE TRADE CARD ============
        self.trade_card = Card(bg=CARD, size_hint_y=None, height=dp(70), padding=dp(10), spacing=dp(4), orientation="vertical")
        self.lbl_trade_status = Label(text="No Active Trade", font_size="14sp", bold=True, color=MUTED, halign="left", valign="top")
        self.lbl_trade_status.bind(size=lambda *a: setattr(self.lbl_trade_status, "text_size", self.lbl_trade_status.size))
        self.trade_card.add_widget(self.lbl_trade_status)
        root.add_widget(self.trade_card)

        # ============ SIGNAL CARD ============
        sig_card = Card(bg=CARD, size_hint_y=None, height=dp(120), padding=dp(12), spacing=dp(6), orientation="vertical")
        top = BoxLayout(size_hint_y=None, height=dp(46))
        self.lbl_signal = Label(text="WAITING", font_size="32sp", bold=True, color=ORANGE, size_hint_x=0.7)
        self.lbl_conf = Label(text="--%", font_size="22sp", bold=True, color=MUTED, size_hint_x=0.3, halign="right")
        self.lbl_conf.bind(size=lambda *a: setattr(self.lbl_conf, "text_size", self.lbl_conf.size))
        top.add_widget(self.lbl_signal); top.add_widget(self.lbl_conf)
        sig_card.add_widget(top)
        self.conf_bar = ConfidenceBar(size_hint_y=None, height=dp(10))
        sig_card.add_widget(self.conf_bar)
        self.lbl_breakdown = Label(text="Press ANALYZE to start", font_size="11sp", color=MUTED, size_hint_y=None, height=dp(20), halign="left", valign="middle")
        self.lbl_breakdown.bind(size=lambda *a: setattr(self.lbl_breakdown, "text_size", self.lbl_breakdown.size))
        sig_card.add_widget(self.lbl_breakdown)
        root.add_widget(sig_card)

        # ============ DETAILS CARD ============
        details_card = Card(bg=CARD, size_hint_y=None, height=dp(220), padding=dp(12), spacing=dp(4), orientation="vertical")
        self.lbl_details = Label(text="", font_size="13sp", color=WHITE, halign="left", valign="top")
        self.lbl_details.bind(size=lambda *a: setattr(self.lbl_details, "text_size", self.lbl_details.size))
        details_card.add_widget(self.lbl_details)
        root.add_widget(details_card)

        # ============ BUTTONS ============
        btn_row = GridLayout(cols=3, spacing=dp(6), size_hint_y=None, height=dp(52))
        self.btn = Button(text="ANALYZE", background_normal="", background_color=GOLD, color=BG, bold=True, font_size="14sp")
        self.btn.bind(on_release=self._analyze)
        self.auto_btn = Button(text="AUTO: OFF", background_normal="", background_color=CARD2, color=WHITE, bold=True, font_size="14sp")
        self.auto_btn.bind(on_release=self._toggle_auto)
        self.reset_btn = Button(text="RESET", background_normal="", background_color=CARD2, color=RED, bold=True, font_size="14sp")
        self.reset_btn.bind(on_release=self._reset)
        btn_row.add_widget(self.btn); btn_row.add_widget(self.auto_btn); btn_row.add_widget(self.reset_btn)
        root.add_widget(btn_row)

        return main_scroll

    def _toggle_auto(self, *a):
        self.save_settings() # حفظ الإعدادات عند تشغيل البوت التلقائي
        if self.auto_event:
            self.auto_event.cancel()
            self.auto_event = None
            self.auto_btn.text = "AUTO: OFF"
            self.auto_btn.background_color = CARD2
            self.lbl_breakdown.text = "Auto-Pilot Stopped"
        else:
            self.auto_btn.text = "AUTO: ON"
            self.auto_btn.background_color = GREEN
            self.auto_event = Clock.schedule_interval(self._analyze, AUTO_PILOT_INTERVAL)
            self._analyze() 

    def _send_telegram(self, text):
        token = self.tg_token_input.text.strip()
        chat_id = self.tg_chat_input.text.strip()
        if not token or not chat_id: return
        url = f"https://api.telegram.org/bot{token}/sendMessage"
        payload = {"chat_id": chat_id, "text": text, "parse_mode": "HTML"}
        try: requests.post(url, json=payload, timeout=5)
        except: pass

    def _reset(self, *a):
        self.peak = None; self.current_bal = None; self.active_trade = None
        self.lbl_signal.text = "WAITING"; self.lbl_signal.color = ORANGE
        self.lbl_conf.text = "--%"; self.lbl_conf.color = MUTED
        self.conf_bar.set_value(0, MUTED)
        self.lbl_breakdown.text = "Press ANALYZE to start"
        self.lbl_details.text = ""
        self.lbl_trade_status.text = "No Active Trade"; self.lbl_trade_status.color = MUTED
        self._update_dots(api_ok=True, session_ok=is_session_active())

    def _update_dots(self, api_ok=None, session_ok=None):
        def do_update(dt):
            if api_ok is not None:
                self.dot_api.canvas.clear()
                with self.dot_api.canvas:
                    Color(*(GREEN if api_ok else RED))
                    RoundedRectangle(pos=self.dot_api.pos, size=self.dot_api.size, radius=[self.dot_api.size[0]/2])
            if session_ok is not None:
                self.dot_session.canvas.clear()
                with self.dot_session.canvas:
                    Color(*(GREEN if session_ok else ORANGE))
                    RoundedRectangle(pos=self.dot_session.pos, size=self.dot_session.size, radius=[self.dot_session.size[0]/2])
        Clock.schedule_once(do_update, 0)

    def _toggle_tf(self, *a):
        m = {"15min": "1h", "1h": "4h", "4h": "15min"}
        self.current_interval = m.get(self.current_interval, "15min")
        self.tf_btn.text = self.current_interval.upper().replace("MIN", "M")

    def _analyze(self, *args):
        if self.busy: return
        key = self.api_input.text.strip()
        if not key:
            self._set_signal("NO KEY", RED, 0, "Add API Key")
            return
        self.save_settings() # حفظ الإعدادات عند الضغط على تحليل
        self.busy = True; self.btn.disabled = True
        self._set_signal("LOADING", GOLD, 0, "Fetching...")
        threading.Thread(target=self._fetch, args=(key,), daemon=True).start()

    def _set_signal(self, text, color, conf, breakdown):
        self.lbl_signal.text = text
        self.lbl_signal.color = color
        self.lbl_conf.text = f"{conf}%" if conf > 0 else "--%"
        self.lbl_conf.color = color if conf > 0 else MUTED
        self.conf_bar.set_value(conf, color)
        self.lbl_breakdown.text = breakdown

    def _fetch(self, key):
        try:
            session_ok = is_session_active()
            self._update_dots(session_ok=session_ok)
            
            if ENFORCE_SESSION and not session_ok:
                Clock.schedule_once(lambda dt: self._set_signal("WAIT", ORANGE, 0, "Outside Session"), 0)
                return

            def get(sym, interval="15min"):
                params = {"symbol": sym, "interval": interval, "outputsize": 250, "apikey": key}
                for _ in range(3):
                    try:
                        r = requests.get(API_URL, params=params, timeout=15)
                        r.raise_for_status(); d = r.json()
                        if "values" in d: return d
                    except Exception: pass
                    time.sleep(1)
                return None

            r1 = get(SYMBOL, self.current_interval)
            if not r1: raise Exception("Failed XAUUSD")
            r2 = get(SYMBOL, "1h"); r_dxy = get(DXY_SYMBOL, "1h"); r_us10y = get(US10Y_SYMBOL, "1h")

            v1 = list(reversed(r1["values"]))
            o1 = [float(x["open"]) for x in v1]; h1 = [float(x["high"]) for x in v1]
            l1 = [float(x["low"]) for x in v1]; c1 = [float(x["close"]) for x in v1]
            vol = [float(x.get("volume", 1)) for x in v1]

            c2 = [float(x["close"]) for x in list(reversed(r2["values"]))] if r2 else c1
            intermarket = {"dxy": 0, "us10y": 0}
            if r_dxy:
                dxy_c = [float(x["close"]) for x in list(reversed(r_dxy["values"]))]
                dxy_ema = ema(dxy_c, 20)
                if len(dxy_ema) > 1: intermarket["dxy"] = -1 if dxy_c[-1] < dxy_ema[-1] else 1
            if r_us10y:
                us10y_c = [float(x["close"]) for x in list(reversed(r_us10y["values"]))]
                us10y_ema = ema(us10y_c, 20)
                if len(us10y_ema) > 1: intermarket["us10y"] = -1 if us10y_c[-1] < us10y_ema[-1] else 1

            e9, e20, e50, e200 = ema(c1, 9), ema(c1, 20), ema(c1, 50), ema(c1, 200)
            rv = rsi(c1, 14); av = atr(h1, l1, c1, 14); dv = adx(h1, l1, c1, 14); cv = cci(h1, l1, c1, 20)
            vw = vwap_calc(h1, l1, c1, vol)
            htfe = ema(c2, 200); htf_bull = c2[-1] > htfe[-1] if htfe[-1] else False
            e50_slope_val = ema_slope(e50, 5)

            if self.active_trade: self._manage_active_trade(c1[-1], av[-1])

            if not self.active_trade:
                res = compute_signal(c1[-1], e9[-1], e20[-1], e50[-1], e200[-1], htf_bull, rv[-1], dv[-1], cv[-1], vw[-1], av[-1], o1, h1, l1, c1, vol, e50_slope_val, intermarket)
                if not session_ok: res["reasons"].insert(0, "Warning: Outside Session")

                if res["signal"] in ("BUY", "SELL"):
                    self.active_trade = {"dir": res["signal"], "entry": c1[-1], "sl": res["sl"], "tp1": res["tp1"], "tp2": res["tp2"], "tp1_hit": False, "be_moved": False}
                    log_signal(res["signal"], c1[-1], res["sl"], res["tp1"], res["tp2"], res["confidence"], intermarket)
                    
                    msg = (f"🚨 <b>{res['signal']} Signal!</b>\n\n"
                           f"💵 <b>Price:</b> {c1[-1]:.2f}\n"
                           f"🛑 <b>SL:</b> {res['sl']:.2f}\n"
                           f"🎯 <b>TP1:</b> {res['tp1']:.2f} (50%)\n"
                           f"🏁 <b>TP2:</b> {res['tp2']:.2f}\n"
                           f"📊 <b>Confidence:</b> {res['confidence']}%")
                    self._send_telegram(msg)
                    
                    Clock.schedule_once(lambda dt: self._update_trade_ui(), 0)
            else:
                res = {"signal": "ACTIVE", "confidence": 0, "score_parts": {}, "reasons": ["Trade in progress"]}

            extras = {"price": c1[-1], "atr": av[-1], "adx": dv[-1], "rsi": rv[-1], "cci": cv[-1], "vwap": vw[-1]}
            Clock.schedule_once(lambda dt: self._show(res, extras), 0)
            Clock.schedule_once(lambda dt: self._update_trade_ui(), 0)

        except Exception as e:
            msg = str(e)
            Clock.schedule_once(lambda dt: self._set_signal("ERROR", RED, 0, msg[:120]), 0)
        finally:
            Clock.schedule_once(lambda dt: setattr(self.btn, "disabled", False), 0)
            Clock.schedule_once(lambda dt: setattr(self, "busy", False), 0)

    def _manage_active_trade(self, price, current_atr):
        t = self.active_trade
        if not t: return
        if t["dir"] == "BUY":
            if price <= t["sl"]: self.active_trade = None; return
            if not t["tp1_hit"] and price >= t["tp1"]:
                t["tp1_hit"] = True; t["sl"] = t["entry"]; t["be_moved"] = True
            if t["tp1_hit"]:
                new_sl = price - (2.0 * current_atr)
                if new_sl > t["sl"]: t["sl"] = new_sl
            if price >= t["tp2"]: self.active_trade = None
        else: 
            if price >= t["sl"]: self.active_trade = None; return
            if not t["tp1_hit"] and price <= t["tp1"]:
                t["tp1_hit"] = True; t["sl"] = t["entry"]; t["be_moved"] = True
            if t["tp1_hit"]:
                new_sl = price + (2.0 * current_atr)
                if new_sl < t["sl"]: t["sl"] = new_sl
            if price <= t["tp2"]: self.active_trade = None

    def _update_trade_ui(self):
        if not self.active_trade:
            self.lbl_trade_status.text = "No Active Trade"
            self.lbl_trade_status.color = MUTED
            return
        t = self.active_trade
        status = "TP1 Hit (Breakeven)" if t["be_moved"] else "Running"
        color = GREEN if t["dir"] == "BUY" else RED
        self.lbl_trade_status.text = f"ACTIVE: {t['dir']} | Entry: {t['entry']:.2f} | SL: {t['sl']:.2f} | {status}"
        self.lbl_trade_status.color = color

    def _show(self, res, ex):
        sig = res["signal"]; conf = res["confidence"]
        parts = res.get("score_parts", {}); reasons = res.get("reasons", [])
        
        color = GREEN if sig == "BUY" else (RED if sig == "SELL" else ORANGE)
        if sig == "ACTIVE": color = BLUE

        self.lbl_signal.text = sig; self.lbl_signal.color = color
        if conf > 0:
            self.lbl_conf.text = f"{conf}%"; self.lbl_conf.color = color
            self.conf_bar.set_value(conf, color)
        
        if parts: self.lbl_breakdown.text = " | ".join(f"{k}:{v}" for k, v in parts.items())
        else: self.lbl_breakdown.text = "Auto-Pilot Running..." if sig == "ACTIVE" else "Waiting..."

        lines = [f"Price    {ex['price']:.2f}", f"ATR      {ex['atr']:.2f}", f"ADX      {ex['adx']:.1f}", f"RSI      {ex['rsi']:.1f}", f"CCI      {ex['cci']:.1f}"]
        if ex["vwap"]: lines.append(f"VWAP     {ex['vwap']:.2f}")

        if res["signal"] in ("BUY", "SELL") and "sl" in res:
            lines.extend(["", f"SL       {res['sl']:.2f}", f"TP1      {res['tp1']:.2f} (50%)", f"TP2      {res['tp2']:.2f}", f"R:R      1 : {abs(res['tp2']-ex['price'])/abs(ex['price']-res['sl']):.2f}"])
        elif reasons:
            lines.extend(["", "Why:"])
            for r in reasons[:3]: lines.append(f"• {r}")

        self.lbl_details.text = "\n".join(lines)

if __name__ == "__main__":
    GoldApp().run()
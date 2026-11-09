#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ExSDR - sound-card I/Q transceiver front end for a homebrew SDR (HDSDR style).
         (formerly MYSDR)

ExSDR by Grant Taylor VE3XTV.  Edited with Claude AI (Anthropic).

  * RX : I/Q from a sound card (e.g. 192 kHz) -> spectrum + waterfall -> USB/LSB/AM/ECSS/FM/CW
         with noise blanker, spectral noise reduction, notch, AGC, squelch.
         ECSS = exalted carrier selectable sideband: a PLL locks onto the AM carrier,
         a phase meter shows the PLL / carrier phase error and the carrier offset.
  * TX : microphone -> USB/LSB/AM/FM/CW -> I/Q to the sound card.
  * Band buttons 160 m ... 6 m jump to the centre of each band.
  * Control: serial port (9600 8N1) with the command set
         Fnnnnn (kHz)  ?F  P1/P0 ?P  A1/A0 ?A  TX  RX

Needs only:  python3, python3-numpy, python3-tk, alsa-utils   (all from apt)
Run:         python3 exsdr.py            (add --demo to try it without hardware)
Serial test: python3 exsdr.py --serialtest /dev/ttyUSB0     (hardware link only)
Self test:   python3 exsdr.py --selftest
"""
import argparse
import collections
import glob
import json
import math
import os
import queue
import re
import select
import shutil
import subprocess
import sys
import threading
import time

import numpy as np

try:                                      # optional: more picture formats and text on SSTV pictures
    from PIL import Image, ImageDraw, ImageFont
except Exception:
    Image = ImageDraw = ImageFont = None

try:
    import termios
    import fcntl
except ImportError:          # not Linux
    termios = None
    fcntl = None

try:
    import tkinter as tk
    from tkinter import ttk, messagebox, filedialog
except ImportError:
    tk = None
    ttk = None
    messagebox = None
    filedialog = None

APP = "ExSDR"
VERSION = "3.10"
AUTHOR = "Grant Taylor VE3XTV"
CREDIT = "Edited with Claude AI (Anthropic)"
PLACEHOLDER = "******"                    # Settings > Station: not filled in yet
CONFIG_PATH = os.path.expanduser("~/.exsdr.json")
OLD_CONFIG_PATH = os.path.expanduser("~/.mysdr.json")    # read once if ~/.exsdr.json does not exist yet
FMIN_KHZ, FMAX_KHZ = 300, 65535           # 16 bit kHz value of the ExSDR hardware
HARDWARE = ["ExSDR", "HackRF", "RTL-SDR", "SDRplay", "Airspy HF+", "ADALM-Pluto", "SoapySDR (other)", "None"]
HW_LIMITS_KHZ = {"ExSDR": (FMIN_KHZ, FMAX_KHZ),      # homemade SDR, serial control
                 "HackRF": (1000, 6000000),          # HackRF One: 1 MHz ... 6 GHz
                 "RTL-SDR": (500, 1766000),          # RTL-SDR Blog V3 / V4: HF via direct sampling / V4
                 "SDRplay": (1, 2000000),            # RSP1A / RSP1B / RSPdx / RSPduo: 1 kHz ... 2 GHz
                 "Airspy HF+": (9, 260000),          # HF+ Discovery: 9 kHz - 31 MHz and 60 - 260 MHz
                 "ADALM-Pluto": (70000, 6000000),    # 70 MHz - 6 GHz (stock firmware: 325 MHz - 3.8 GHz)
                 "SoapySDR (other)": (1, 6000000),   # anything with a SoapySDR driver
                 "None": (0, 99999)}                 # no radio control
RX_ONLY = ("RTL-SDR", "SDRplay", "Airspy HF+")


def hw_name(cfg):
    h = cfg.get("hardware", "ExSDR")
    return h if h in HARDWARE else "ExSDR"

MODES = ["USB", "LSB", "AM", "ECSS", "FM", "CW", "CQUAM", "KAHN"]
MODE_LABEL = {"CQUAM": "C-QuAM", "KAHN": "Kahn"}
CARRIER_MODES = ("AM", "ECSS", "CQUAM", "KAHN")      # double sideband with a carrier (TX as AM)
PLL_MODES = ("ECSS", "CQUAM", "KAHN")                # carrier PLL in use
STEREO_MODES = ("CQUAM", "KAHN")
# width slider per mode: (min, max, step) Hz.  AM / ECSS width is the total RF bandwidth (+-width/2)
WIDTH_RANGE = {"USB": (500, 6000, 50), "LSB": (500, 6000, 50),
               "AM": (1000, 12000, 100), "ECSS": (1000, 12000, 100),
               "CQUAM": (2000, 12000, 100), "KAHN": (2000, 12000, 100),
               "FM": (5000, 25000, 500), "CW": (50, 1000, 10)}
DEF_WIDTH = {"USB": 2400, "LSB": 2400, "AM": 6000, "ECSS": 6000, "FM": 12000, "CW": 500,
             "CQUAM": 10000, "KAHN": 10000}
STEPS = [1, 10, 100, 500, 1000, 5000, 10000, 100000]
ECSS_SB = ["LSB", "DSB", "USB"]           # sideband used by ECSS
ECSS_SB_LOW = 200.0                       # Hz: single sideband ECSS starts here (keeps the carrier out)

# Amateur bands in kHz (low edge, high edge).  The band buttons jump to the centre.
# 60 m differs a lot from country to country - edit to suit your licence.
BAND_PLANS = {
    "Region 1": [("160", 1810, 2000), ("80", 3500, 3800), ("60", 5351.5, 5366.5), ("40", 7000, 7200),
                 ("30", 10100, 10150), ("20", 14000, 14350), ("17", 18068, 18168), ("15", 21000, 21450),
                 ("12", 24890, 24990), ("10", 28000, 29700), ("6", 50000, 52000)],
    "Region 2": [("160", 1800, 2000), ("80", 3500, 4000), ("60", 5330.5, 5406.4), ("40", 7000, 7300),
                 ("30", 10100, 10150), ("20", 14000, 14350), ("17", 18068, 18168), ("15", 21000, 21450),
                 ("12", 24890, 24990), ("10", 28000, 29700), ("6", 50000, 54000)],
    "Region 3": [("160", 1800, 2000), ("80", 3500, 3900), ("60", 5351.5, 5366.5), ("40", 7000, 7300),
                 ("30", 10100, 10150), ("20", 14000, 14350), ("17", 18068, 18168), ("15", 21000, 21450),
                 ("12", 24890, 24990), ("10", 28000, 29700), ("6", 50000, 54000)],
}


# Broadcast bands in kHz.  MW depends on the region; the short-wave bands are world-wide.
MW_BAND = {"Region 1": (531, 1602), "Region 2": (530, 1700), "Region 3": (531, 1602)}
SW_BROADCAST = [("120", 2300, 2495), ("90", 3200, 3400), ("75", 3900, 4000), ("60", 4750, 5060),
                ("49", 5900, 6200), ("41", 7200, 7450), ("31", 9400, 9900), ("25", 11600, 12100),
                ("22", 13570, 13870), ("19", 15100, 15800), ("16", 17480, 17900), ("15", 18900, 19020),
                ("13", 21450, 21850), ("11", 25670, 26100)]


def band_plan(cfg):
    return BAND_PLANS.get(cfg.get("band_region"), BAND_PLANS["Region 2"])


def broadcast_plan(cfg):
    lo, hi = MW_BAND.get(cfg.get("band_region"), MW_BAND["Region 2"])
    return [("MW", lo, hi)] + SW_BROADCAST


def band_centre_hz(lo_khz, hi_khz):
    """Centre of a band in Hz, rounded to 100 Hz."""
    return int(round((lo_khz + hi_khz) * 500.0 / 100.0)) * 100

DEFAULTS = {
    # serial control
    "serial_port": "/dev/ttyUSB0",
    "baud": 9600,
    "terminator": "",             # appended to every command ("" = none, "\r", "\n", "\r\n")
    "reply_timeout": 1.50,        # seconds to wait for the hardware's reply to a command
                                  # (HF_SDR.BAS 1.1 replies when it has finished: ~0.5 s for F)
    "idle_gap": 0.06,             # seconds of silence that end a reply
    "cmd_gap": 0.10,              # minimum time between two commands (hardware needs ~100 ms)
    "freq_gap": 0.60,             # minimum time before and after a frequency (Fnnnnn) command
    "txrx_gap": 0.40,             # minimum time after TX / RX (the PIC updates relays + LEDs)
    "cfg_version": 4,
    "banner_wait": 0.40,          # listen this long after opening the port for "HF SDR v1"
    "open_delay": 0.0,            # wait after opening the port (boards that reset on open)
    # sound devices (ALSA names used by arecord / aplay)
    "iq_in_dev": "hw:1,0",        # "demo" = built-in test signals
    "iq_out_dev": "hw:1,0",       # "none" = no transmit I/Q
    "audio_out_dev": "default",   # speaker / headphones, "none" = mute
    "mic_in_dev": "default",      # microphone, "none" = silence
    "sample_rate": 192000,
    "audio_rate": 48000,
    # I/Q corrections
    "rx_swap_iq": False, "rx_invert_q": False,
    "rx_gain_bal_db": 0.0, "rx_phase_deg": 0.0,
    "tx_swap_iq": False, "tx_invert_q": False,
    "tx_gain_bal_db": 0.0, "tx_phase_deg": 0.0,
    "tx_dc_i": 0.0, "tx_dc_q": 0.0,
    # modes
    "fm_dev_hz": 5000.0, "am_depth": 0.9, "cw_pitch_hz": 700.0,
    "ssb_tx_lo": 300.0, "ssb_tx_hi": 2700.0,       # used only when tx_follow_rx is off
    "tx_follow_rx": True,                          # TX bandwidth = RX width slider and low cut
    "theme": "Auto",                               # Auto = follow the desktop, or Light / Dark
    "font_size": 0,                                # 0 = desktop font size
    "s9_dbfs": -60.0,                              # S-meter: signal level (dBFS) that reads S9
    "digit_colour": "Amber",                       # frequency display: preset name or #rrggbb
    "hardware": "ExSDR",                           # ExSDR (homemade, serial), HackRF, or None
    "hackrf_lna": 16,                              # HackRF RX LNA gain dB, 0-40 in 8 dB steps
    "hackrf_vga": 20,                              # HackRF RX VGA gain dB, 0-62 in 2 dB steps
    "hackrf_txvga": 0,                             # HackRF TX gain dB, 0-47 (start low!)
    "hackrf_serial": "",                           # blank = first HackRF found
    "rtl_index": 0,                                # RTL-SDR: which dongle (0 = first)
    "rtl_gain": 30.0,                              # RTL-SDR tuner gain dB (0 = automatic)
    "rtl_ppm": 0,                                  # RTL-SDR frequency correction, ppm
    "rtl_hf": "V4 / none",                         # HF: V4 built in, V3 direct sampling, or upconverter
    "airspy_agc": True,                            # Airspy HF+ HF AGC
    "airspy_serial": "",
    "sdr_args": "",                                # SoapySDR device arguments (SDRplay / Pluto / other)
    "sdr_rx_gain": 30.0,                           # SoapySDR RX gain dB
    "sdr_tx_gain": 0.0,                            # SoapySDR TX gain dB (Pluto: start low)
    "sdr_antenna": "",                             # SoapySDR antenna port (blank = default)
    # remembered state
    # Tune this far above the hardware LO. Keeps carriers and the sound card's DC offset
    # out of the passband (a carrier exactly on the LO is removed by the DC filter).
    "lo_offset_hz": 10000,
    "tune_hz": 3650000, "lo_khz": 3640, "mode": "USB",
    "widths": dict(DEF_WIDTH),
    "lowcuts": {"USB": 300, "LSB": 300, "AM": 0, "ECSS": 0, "FM": 0, "CW": 0, "CQUAM": 0, "KAHN": 0},
    "rx_mute_ms": 250,                             # receiver stays muted this long after going back to RX
    "band_region": "Region 2",
    "ui": {},
    # station (Settings > Station)
    "op_name": "",
    "callsign": PLACEHOLDER,
    "qth": PLACEHOLDER,                            # location, e.g. town / province
    "grid": "",                                    # Maidenhead grid locator, e.g. FN03
    # broadcast schedule (Settings > Language)
    "bc_lang": "English",                          # language filter for the broadcast schedule
    "bc_info": True,                               # open the schedule when a SW broadcast band is chosen
    "bc_now_only": True,
    "bc_url": "http://www.eibispace.de/dx/sked-{season}.csv",
}

UI_DEFAULTS = dict(rpt="S", vol=60.0, gain_db=60.0, squelch=-130.0, agc="Med", nb=0, nb_thr=6.0,
                   nr=0, nr_amt=0.5, notch=0, notch_hz=1000.0, auto_iq=1, lowcut=300.0,
                   mic_db=20.0, drive=0.4, src="Mic", ref=-20.0, rng=100.0, zoom="1",
                   step="1000", pre=0, att=0, ecss_sb="DSB", rolloff="Hard", anf=0,
                   comp=0, comp_db=10.0, lim=1, mod_pct=80.0, stereo_w=100.0,
                   emph="Off", af_ref=-10.0, af_rng=80.0, mode_tab=0)


def clamp(v, lo, hi):
    return lo if v < lo else hi if v > hi else v


def load_cfg():
    cfg = json.loads(json.dumps(DEFAULTS))
    path = CONFIG_PATH if os.path.exists(CONFIG_PATH) else OLD_CONFIG_PATH
    try:
        with open(path) as f:
            saved = json.load(f)
        for k, v in saved.items():
            cfg[k] = v
    except (IOError, OSError, ValueError):
        pass
    if not isinstance(cfg.get("widths"), dict):
        cfg["widths"] = {}
    for m in MODES:
        lo, hi, _ = WIDTH_RANGE[m]
        cfg["widths"][m] = clamp(float(cfg["widths"].get(m, DEF_WIDTH[m])), lo, hi)
    if cfg.get("mode") not in MODES:
        cfg["mode"] = "USB"
    if cfg.get("band_region") not in BAND_PLANS:
        cfg["band_region"] = "Region 2"
    if int(cfg.get("cfg_version", 0)) < 3:
        # older versions sent commands while the PIC was still busy (it then stopped receiving)
        cfg["reply_timeout"] = max(float(cfg.get("reply_timeout", 0)), DEFAULTS["reply_timeout"])
        cfg["freq_gap"] = max(float(cfg.get("freq_gap", 0)), DEFAULTS["freq_gap"])
        cfg["txrx_gap"] = max(float(cfg.get("txrx_gap", 0)), DEFAULTS["txrx_gap"])
        cfg["cfg_version"] = 3
    if int(cfg.get("cfg_version", 0)) < 4:
        # 3.2 filled the station in with the author's details: start from blanks instead
        if cfg.get("callsign") == "VE3XTV" and cfg.get("op_name") == "Grant Taylor":
            cfg["callsign"], cfg["op_name"], cfg["qth"] = PLACEHOLDER, "", cfg.get("qth") or PLACEHOLDER
        cfg["cfg_version"] = 4
    return cfg


def station(cfg, key):
    """A Station setting, or "" while it still shows the ****** placeholder."""
    v = str(cfg.get(key, "") or "").strip()
    return "" if not v or set(v) == {"*"} else v


def save_cfg(cfg):
    try:
        with open(CONFIG_PATH, "w") as f:
            json.dump(cfg, f, indent=2, sort_keys=True)
    except (IOError, OSError):
        pass


# ===================================================================== DSP
def bp_taps(f1, f2, fs, L):
    """Complex band-pass FIR passing f1..f2 Hz (negative = below the carrier)."""
    m = np.arange(L) - (L - 1) / 2.0
    bw = max((f2 - f1) / 2.0, 1.0)
    fc = (f1 + f2) / 2.0
    h = (2.0 * bw / fs) * np.sinc(2.0 * bw / fs * m) * np.exp(2j * np.pi * fc / fs * m)
    return h * np.blackman(L)


def shaped_taps(f1, f2, fs, L, t1=0.0, t2=0.0):
    """Complex band-pass f1..f2 Hz with soft (raised cosine) edges: t1 Hz wide at f1, t2 at f2,
    -6 dB at the edge frequency.  t = 0 gives the usual sharp edge."""
    if t1 <= 0 and t2 <= 0:
        return bp_taps(f1, f2, fs, L)
    nfft = 1 << int(math.ceil(math.log2(L * 4)))
    f = np.fft.fftfreq(nfft, 1.0 / fs)

    def edge(x, t):                      # x > 0 inside the pass band
        if t <= 0:
            return (x >= 0).astype(float)
        return np.clip(0.5 + 0.5 * np.sin(np.pi * np.clip(x / t, -0.5, 0.5)), 0.0, 1.0)
    H = edge(f - f1, t1) * edge(f2 - f, t2)
    h = np.fft.fftshift(np.fft.ifft(H))
    c = nfft // 2
    h = h[c - (L - 1) // 2: c + (L - 1) // 2 + 1] * np.kaiser(L, 6.0)
    return h


EMPHASIS = {"Off": 0.0, "50": 50e-6, "75": 75e-6}   # time constants (s)


def emphasis_taps(tau, fs, pre, L=257):
    """FIR (linear phase) with the magnitude of a 1st order emphasis network, time constant tau.
    De-emphasis: 1 / sqrt(1 + (w tau)^2), -3 dB at 1 / (2 pi tau) (50 us 3183 Hz, 75 us 2122 Hz).
    Pre-emphasis: the inverse, with the rise stopped at 15 kHz (a real network needs that too).
    Both are 0 dB at low frequencies."""
    nfft = 4096
    f = np.fft.rfftfreq(nfft, 1.0 / fs)
    w = 2 * np.pi * f
    if pre:
        t2 = 1.0 / (2 * np.pi * 15000.0)
        H = np.sqrt(1 + (w * tau) ** 2) / np.sqrt(1 + (w * t2) ** 2)
    else:
        H = 1.0 / np.sqrt(1 + (w * tau) ** 2)
    h = np.fft.fftshift(np.fft.irfft(H, nfft))
    c = nfft // 2
    return h[c - (L - 1) // 2: c + (L - 1) // 2 + 1] * np.kaiser(L, 5.0)


def lp_taps(fc, fs, L):
    return bp_taps(-fc, fc, fs, L).real


class FIR:
    """Streaming FFT (overlap-save) FIR filter for fixed size blocks."""

    def __init__(self, h, blk):
        self.hist = None
        self.set(h, blk)

    def set(self, h, blk):
        self.h = np.asarray(h, dtype=complex)
        self.L = len(self.h)
        self.blk = blk
        self.nfft = 1 << int(math.ceil(math.log2(blk + self.L - 1)))
        self.H = np.fft.fft(self.h, self.nfft)
        if self.hist is None or len(self.hist) != self.L - 1:
            self.hist = np.zeros(self.L - 1, dtype=complex)

    def process(self, x):
        n = len(x)
        buf = np.concatenate((self.hist, np.asarray(x, dtype=complex)))
        y = np.fft.ifft(np.fft.fft(buf, self.nfft) * self.H)
        self.hist = buf[len(buf) - (self.L - 1):].copy()
        return y[self.L - 1:self.L - 1 + n]


class Notch:
    """Audio notch (2 pole biquad), state is kept between blocks."""

    def __init__(self, fs):
        self.fs = fs
        self.f = None
        self.s = [0.0, 0.0, 0.0, 0.0]
        self.c = None

    def process(self, x, f):
        if f != self.f:
            self.f = f
            w = 2 * math.pi * clamp(f, 50.0, self.fs / 2 - 100.0) / self.fs
            r = 0.997
            a1, a2 = -2 * r * math.cos(w), r * r
            b0, b1, b2 = 1.0, -2 * math.cos(w), 1.0
            g = (1 + a1 + a2) / (2 + b1)          # unity gain at DC
            self.c = (b0 * g, b1 * g, b2 * g, a1, a2)
        b0, b1, b2, a1, a2 = self.c
        x1, x2, y1, y2 = self.s
        out = []
        ap = out.append
        for xi in x.tolist():
            yi = b0 * xi + b1 * x1 + b2 * x2 - a1 * y1 - a2 * y2
            x2 = x1
            x1 = xi
            y2 = y1
            y1 = yi
            ap(yi)
        self.s = [x1, x2, y1, y2]
        return np.array(out)


class NoiseReducer:
    """Spectral subtraction (minimum tracking noise estimate), 50% WOLA."""

    def __init__(self, n=512):
        self.n = n
        self.hop = n // 2
        self.win = np.sqrt(np.hanning(n + 1)[:-1])
        self.inbuf = np.zeros(n - self.hop)
        self.tail = np.zeros(n - self.hop)
        self.ps = None
        self.nz = None
        self.gprev = None
        self.nfr = 0
        self.warm = 16          # frames to ignore at start (filter start-up ramp is not noise)

    def process(self, x, amt):
        n, hop = self.n, self.hop
        buf = np.concatenate((self.inbuf, x))
        nfr = (len(buf) - n) // hop + 1
        if nfr <= 0:
            self.inbuf = buf
            return np.zeros(len(x))
        out = np.zeros(hop * (nfr - 1) + n)
        alpha = 1.0 + 2.5 * amt
        gmin = 10 ** (-(8 + 22 * amt) / 20.0)
        for i in range(nfr):
            seg = buf[i * hop:i * hop + n] * self.win
            X = np.fft.rfft(seg)
            P = (X.real ** 2 + X.imag ** 2) + 1e-18
            if self.ps is None:
                if self.warm > 0:
                    self.warm -= 1
                if self.warm > 0 or float(P.sum()) < 1e-12:   # start-up / silence: pass through
                    out[i * hop:i * hop + n] += np.fft.irfft(X, n) * self.win
                    continue
                self.ps = P.copy()
                self.nz = P.copy()
                self.gprev = np.ones(len(P))
            self.nfr += 1
            self.ps = 0.7 * self.ps + 0.3 * P
            rise = 1.03 if self.nfr < 150 else 1.005     # converge quickly at start, then track slowly
            self.nz = np.minimum(self.ps, self.nz * rise)
            noise = self.nz * 1.8
            g = np.clip(1.0 - alpha * noise / self.ps, gmin, 1.0)
            g = 0.5 * self.gprev + 0.5 * g
            self.gprev = g
            y = np.fft.irfft(X * g, n) * self.win
            out[i * hop:i * hop + n] += y
        out[:n - hop] += self.tail
        res = out[:nfr * hop]
        self.tail = out[nfr * hop:].copy()
        self.inbuf = buf[nfr * hop:].copy()
        return res


class RxDsp:
    """I/Q (complex, N samples at `rate`) -> audio (M samples at `arate`) + spectrum."""
    BLK = 2048
    L = 2049

    def __init__(self, rate=192000, arate=48000):
        self.rate = int(rate)
        self.D = max(1, int(round(rate / float(arate))))
        self.arate = self.rate // self.D
        self.M = self.BLK
        self.N = self.M * self.D
        self.lock = threading.Lock()
        self.p = dict(mode="USB", offset=0.0, width=2400.0, lowcut=300.0, pitch=700.0,
                      nb=False, nb_thr=6.0, nr=False, nr_amt=0.5, notch=False, notch_hz=1000.0,
                      agc="Med", vol=60.0, gain_db=60.0, squelch=-130.0, auto_iq=True,
                      swap=False, invert=False, gain_bal_db=0.0, phase_deg=0.0, fm_dev=5000.0,
                      ecss_sb="DSB", soft=False, anf=False, stereo_w=1.0, deemph="Off")
        self.dc = 0j
        self.have_dc = False
        self.iq_c = 0.0
        self.iq_g = 1.0
        self.iq_n = 0
        self.ph = 0.0
        self.win = np.blackman(self.N)
        self.wsum = float(np.sum(self.win))
        self.spec_pow = None
        self.dec = FIR(lp_taps(self.arate / 2.0, self.rate, 64 * self.D + 1), self.N) if self.D > 1 else None
        self.chan = FIR(bp_taps(300, 2700, self.arate, self.L), self.M)
        self.chan_key = None
        self.nr = NoiseReducer()
        self.notch = Notch(self.arate)
        self.am_c = None
        self.fm_prev = 0j
        self.fm_dc = 0.0
        self.agc_env = 1e-6
        self.agc_gain = 1.0
        self.audio_level = 0.0
        self.hpf = FIR(np.array([1.0]), self.M)               # audio low cut for AM / ECSS / FM
        self.hpf_key = None
        # second audio channel (right) for the stereo modes: its own filters and noise reduction
        self.hpf2 = FIR(np.array([1.0]), self.M)
        self.anf2 = Notch(self.arate)
        self.notch2 = Notch(self.arate)
        self.nr2 = NoiseReducer()
        # stereo decoders
        hp60 = -lp_taps(60.0, self.arate, 1025)
        hp60[512] += 1.0                                       # high-pass 60 Hz: removes the C-QuAM pilot
        self.cq_hs = FIR(hp60, self.M)
        self.cq_hd = FIR(hp60, self.M)
        self.cq_pil = np.zeros(3, dtype=complex)               # 19 / 25 / 31 Hz correlators
        self.cq_n = 0
        self.stereo = False                                    # stereo pilot seen (C-QuAM)
        self.sbfL = FIR(bp_taps(-3000.0, -100.0, self.arate, self.L), self.M)
        self.sbfU = FIR(bp_taps(100.0, 3000.0, self.arate, self.L), self.M)
        self.kahn_key = None
        self.last_stereo = None                                # int16 (M, 2) for stereo modes
        self.audio_lr = None                                   # (left, right) peak levels, stereo modes
        self.digi_audio = np.zeros(self.M)                     # for the digital mode decoders
        self.de1 = FIR(np.array([1.0]), self.M)               # de-emphasis, left / mono
        self.de2 = FIR(np.array([1.0]), self.M)               # de-emphasis, right
        self.de_key = None
        self.hold = False                                      # True: muted, AGC frozen (around TX)
        self.fade = 1.0
        # automatic notch: follows the strongest steady tone in the pass band
        self.anf = Notch(self.arate)
        self.anf_freq = None
        self.anf_cand = None
        self.anf_n = 0
        self.anf_miss = 0
        self.af_win = np.hanning(self.M)
        self.af_wsum = float(np.sum(self.af_win))
        self.af_spec = None
        # ECSS: carrier PLL.  The carrier is picked out with a +-400 Hz filter, the loop runs
        # at arate / PLL_DEC; the audio path is delayed by the same amount as the carrier filter.
        self.PLL_DEC = 16
        self.pll_fs = self.arate / float(self.PLL_DEC)
        self.car = FIR(lp_taps(400.0, self.arate, 481), self.M)
        self.car_dly = np.zeros(240, dtype=complex)           # (481 - 1) / 2 samples
        self.sbf = FIR(bp_taps(ECSS_SB_LOW, 3000.0, self.arate, self.L), self.M)
        self.sbf_key = None
        self.ecss_dc = None
        self.pll_reset()

    def pll_reset(self):
        self.pll_th = 0.0          # NCO phase (rad)
        self.pll_w = 0.0           # NCO frequency (rad per loop sample)
        self.pll_lk = 0.0          # lock detector, ~1 when locked
        self.pll_locked = False
        self.pll = {"phase": 0.0, "offset": 0.0, "locked": False, "level": -150.0, "active": False}

    def _loop(self, bn, zeta=0.707):
        wn = 2 * math.pi * bn / self.pll_fs
        return 2 * zeta * wn, wn * wn

    def set_params(self, **kw):
        with self.lock:
            if kw.get("mode", self.p["mode"]) != self.p["mode"] or \
                    abs(kw.get("offset", self.p["offset"]) - self.p["offset"]) > 300:
                self.pll_reset()                       # retuned: acquire again
            self.p.update(kw)

    def band(self, p=None):
        """Pass band in baseband Hz (f1, f2).  SSB: low cut .. width (the width slider is the
        upper edge, the low cut slider only moves the lower edge)."""
        p = p or self.p
        mode, w = p["mode"], max(float(p["width"]), 50.0)
        lc = clamp(float(p["lowcut"]), 0.0, 1000.0)
        if mode == "USB":
            return lc, max(w, lc + 100.0)
        if mode == "LSB":
            return -max(w, lc + 100.0), -lc
        if mode == "CW":
            return p["pitch"] - w / 2, p["pitch"] + w / 2
        lo = max(ECSS_SB_LOW, lc)
        if mode in ("CQUAM", "KAHN"):
            return -w / 2, w / 2
        if mode == "ECSS" and p.get("ecss_sb") == "USB":
            return lo, max(w / 2, lo + 100)
        if mode == "ECSS" and p.get("ecss_sb") == "LSB":
            return -max(w / 2, lo + 100), -lo
        return -w / 2, w / 2

    def edges(self, p, f1, f2):
        """Roll-off widths (t1, t2) for the filter edges: hard = 0, soft = about 1 kHz at the
        high edges; the low cut edge gets a gentler slope that still passes the low cut point."""
        if not p.get("soft"):
            return 0.0, 0.0
        mode, w = p["mode"], max(float(p["width"]), 50.0)
        if mode == "CW":
            return 0.4 * w, 0.4 * w
        hi = min(1000.0, 0.8 * (f2 - f1))
        if mode in ("USB", "ECSS") and f1 >= 0:
            return min(400.0, 1.5 * f1), hi                   # f1 = low cut, f2 = high edge
        if mode in ("LSB", "ECSS") and f2 <= 0:
            return hi, min(400.0, 1.5 * -f2)
        return hi, hi                                         # AM / FM: both edges are high edges

    def auto_notch(self, a, p):
        self.anf_detect(a, p)
        if self.anf_freq is not None:
            a = self.anf.process(a, round(self.anf_freq, 1))
        return a

    def anf_detect(self, a, p):
        """Find the strongest steady tone in the pass band and notch it out.
        A tone must stay within 25 Hz for 6 blocks (~0.25 s) and stand 18 dB above the
        rest of the pass band; it is released when it has gone for ~0.5 s.  Speech moves
        too much to be caught."""
        X = np.abs(np.fft.rfft(a * self.af_win)) + 1e-12
        db = 20 * np.log10(X)
        binw = self.arate / float(len(a))
        f1, f2 = self.band(p)
        sh = self.shift(p)
        lo, hi = sorted((abs(f1 + sh), abs(f2 + sh)))
        if p["mode"] in CARRIER_MODES + ("FM",) and f1 < 0 < f2:
            lo, hi = 0.0, max(abs(f1), abs(f2))
        k0, k1 = max(3, int(max(lo, 120.0) / binw) + 1), min(len(db) - 2, int(hi / binw) - 1)
        if k1 - k0 > 8:
            seg = db[k0:k1]
            k = int(np.argmax(seg)) + k0
            prom = db[k] - float(np.median(seg))
            if prom > 18.0:
                y0, y1, y2 = db[k - 1], db[k], db[k + 1]       # parabolic peak: sub-bin frequency
                den = y0 - 2 * y1 + y2
                f = (k + (0.5 * (y0 - y2) / den if den else 0.0)) * binw
                if self.anf_cand is not None and abs(f - self.anf_cand) < 25.0:
                    self.anf_n += 1
                    self.anf_cand = 0.7 * self.anf_cand + 0.3 * f
                else:
                    self.anf_cand, self.anf_n = f, 1
                if self.anf_freq is not None and abs(f - self.anf_freq) < 40.0:
                    self.anf_freq = 0.35 * self.anf_freq + 0.65 * f   # follow a drifting tone
                    self.anf_miss = 0
                elif self.anf_n >= 6:
                    self.anf_freq, self.anf_miss = self.anf_cand, 0   # lock (or jump to a new tone)
                elif self.anf_freq is not None:
                    self.anf_miss += 1
            else:
                self.anf_n = max(0, self.anf_n - 1)
                if self.anf_freq is not None:
                    self.anf_miss += 1
            if self.anf_freq is not None and self.anf_miss > 12:
                self.anf_freq = None

    def ecss(self, y, p):
        """Synchronous AM: lock a PLL to the carrier, derotate, take L / U / both sidebands."""
        yr = self.pll_derotate(y, 12.0)
        sb = p.get("ecss_sb", "DSB")
        if sb == "DSB":
            a = yr.real
        else:
            key = (sb, int(round(p["width"])), int(round(p["lowcut"])), bool(p.get("soft")))
            if key != self.sbf_key:
                f1, f2 = self.band(p)
                t1, t2 = self.edges(p, f1, f2)
                self.sbf.set(shaped_taps(f1, f2, self.arate, self.L, t1, t2), self.M)
                self.sbf_key = key
            a = 2.0 * self.sbf.process(yr).real
        m = float(a.mean())                                  # remove the carrier (DC)
        self.ecss_dc = m if self.ecss_dc is None else 0.85 * self.ecss_dc + 0.15 * m
        return a - self.ecss_dc

    def stereo_mix(self, left, right, p):
        """Stereo width: 0 = mono (both channels L+R), 1 = full stereo."""
        w = clamp(float(p.get("stereo_w", 1.0)), 0.0, 1.0)
        mid, side = 0.5 * (left + right), 0.5 * (left - right) * w
        return mid + side, mid - side

    def cquam(self, y, p):
        """Motorola C-QuAM AM stereo.  The envelope is 1 + L + R (what a mono AM set hears),
        the phase angle phi carries L - R:  L - R = E * tan(phi) (C-QuAM -> QuAM correction).
        A 25 Hz pilot in L - R says the station is in stereo."""
        yr = self.pll_derotate(y, 4.0)          # narrow loop: must not follow the L-R phase
        E = np.abs(yr)
        re = np.maximum(yr.real, 0.25 * E + 1e-9)            # tan(phi) limited to about 76 degrees
        diff = E * yr.imag / re
        ssum = E
        # pilot: correlate L - R with 19, 25 and 31 Hz (25 Hz must stand well above its neighbours)
        n0 = self.cq_n
        tt = (n0 + np.arange(len(diff))) / float(self.arate)
        self.cq_n += len(diff)
        for i, fp in enumerate((19.0, 25.0, 31.0)):
            c = complex(np.mean(diff * np.exp(-2j * np.pi * fp * tt)))
            self.cq_pil[i] = 0.9 * self.cq_pil[i] + 0.1 * c
        pv = np.abs(self.cq_pil)
        lvl = float(np.mean(E)) + 1e-9
        if self.stereo:
            self.stereo = pv[1] > 1.5 * max(pv[0], pv[2]) and pv[1] / lvl > 0.003
        else:
            self.stereo = pv[1] > 3.0 * max(pv[0], pv[2]) and pv[1] / lvl > 0.006
        ssum = self.cq_hs.process(ssum).real                 # remove carrier (DC) and pilot,
        diff = self.cq_hd.process(diff).real                 # same filter so they stay aligned
        left, right = 0.5 * (ssum + diff), 0.5 * (ssum - diff)
        return self.stereo_mix(left, right, p)

    def kahn(self, y, p):
        """Kahn / ISB AM stereo: lower sideband = left, upper sideband = right (carrier locked)."""
        yr = self.pll_derotate(y, 12.0)
        w = max(float(p["width"]), 400.0) / 2
        lo = max(100.0, clamp(float(p["lowcut"]), 0.0, 1000.0))
        key = (int(round(w)), int(round(lo)), bool(p.get("soft")))
        if key != self.kahn_key:
            t = min(1000.0, 0.8 * (w - lo)) if p.get("soft") else 0.0
            tl = min(400.0, 1.5 * lo) if p.get("soft") else 0.0
            self.sbfL.set(shaped_taps(-w, -lo, self.arate, self.L, t, tl), self.M)
            self.sbfU.set(shaped_taps(lo, w, self.arate, self.L, tl, t), self.M)
            self.kahn_key = key
        left = 2.0 * self.sbfL.process(yr).real
        right = 2.0 * self.sbfU.process(yr).real
        self.stereo = self.pll_locked
        return self.stereo_mix(left, right, p)

    def pll_derotate(self, y, track_bn):
        """Lock the carrier PLL; returns y delayed and turned so the carrier sits at 0 Hz, 0 deg."""
        D = self.PLL_DEC
        c = self.car.process(y)[::D]
        buf = np.concatenate((self.car_dly, y))
        ym = buf[:len(y)]
        self.car_dly = buf[len(y):]
        K = len(c)
        th0 = np.empty(K)
        th1 = np.empty(K)
        errs = np.empty(K)
        th, w, lk, locked = self.pll_th, self.pll_w, self.pll_lk, self.pll_locked
        acq, trk = self._loop(60.0), self._loop(track_bn)   # wide to acquire, narrow when locked
        wmax = 2 * math.pi * 450.0 / self.pll_fs
        cos, sin, atan2 = math.cos, math.sin, math.atan2
        for k, v in enumerate(c.tolist()):
            cr, sr = cos(th), sin(th)
            e = atan2(v.imag * cr - v.real * sr, v.real * cr + v.imag * sr)
            a, b = trk if locked else acq
            th0[k] = th
            w = clamp(w + b * e, -wmax, wmax)
            th += w + a * e
            th1[k] = th
            errs[k] = e
            lk += 0.004 * (cos(e) - lk)
            if locked and lk < 0.5:
                locked = False
            elif not locked and lk > 0.8:
                locked = True
        frac = np.arange(D) / float(D)
        phase = (th0[:, None] + (th1 - th0)[:, None] * frac[None, :]).ravel()
        self.pll_th = th % (2 * math.pi)
        self.pll_w, self.pll_lk, self.pll_locked = w, lk, locked
        self.pll = {"phase": math.degrees(float(np.angle(np.mean(np.exp(1j * errs))))),
                    "offset": w * self.pll_fs / (2 * math.pi), "locked": locked,
                    "level": 20 * math.log10(float(np.mean(np.abs(c))) + 1e-12), "active": True}
        return ym * np.exp(-1j * phase)                     # carrier now at 0 Hz and 0 degrees

    def shift(self, p=None):
        p = p or self.p
        return p["pitch"] if p["mode"] == "CW" else 0.0

    def process(self, iq):
        with self.lock:
            p = dict(self.p)
        N, M = self.N, self.M
        if p["swap"]:
            iq = iq.imag + 1j * iq.real
        if p["invert"]:
            iq = iq.real - 1j * iq.imag
        m = complex(iq.mean())
        self.dc = m if not self.have_dc else 0.9 * self.dc + 0.1 * m
        self.have_dc = True
        iq = iq - self.dc
        I, Q = iq.real, iq.imag
        if p["gain_bal_db"] or p["phase_deg"]:
            ph = math.radians(p["phase_deg"])
            Q = 10 ** (p["gain_bal_db"] / 20.0) * (Q * math.cos(ph) + I * math.sin(ph))
        if p["auto_iq"]:
            pi_ = float(np.mean(I * I)) + 1e-18
            self.iq_n += 1
            a = max(0.1, 1.0 / self.iq_n)            # fast start, then slow tracking
            c = float(np.mean(I * Q)) / pi_
            self.iq_c = (1 - a) * self.iq_c + a * c
            Q2 = Q - self.iq_c * I
            g = math.sqrt(pi_ / (float(np.mean(Q2 * Q2)) + 1e-18))
            self.iq_g = (1 - a) * self.iq_g + a * g
            Q = Q2 * self.iq_g
        iq = I + 1j * Q

        if p["nb"]:                                    # impulse blanker
            mag = np.abs(iq)
            ref = 1.2 * float(np.median(mag)) + 1e-12
            mask = mag > p["nb_thr"] * ref
            if mask.any():
                mask = np.convolve(mask.astype(np.float64), np.ones(9), "same") > 0
                iq = np.where(mask, 0.0, iq)

        S = np.fft.fftshift(np.fft.fft(iq * self.win))
        pw = (np.abs(S) / self.wsum) ** 2
        self.spec_pow = pw if self.spec_pow is None else 0.6 * self.spec_pow + 0.4 * pw
        spec = 10 * np.log10(self.spec_pow + 1e-14)

        eff = p["offset"] - self.shift(p)
        w = -2 * math.pi * eff / self.rate
        x = iq * np.exp(1j * (self.ph + w * np.arange(N)))
        self.ph = (self.ph + w * N) % (2 * math.pi)
        if self.D > 1:
            x = self.dec.process(x)[::self.D]

        key = (p["mode"], int(round(p["width"])), int(round(p["lowcut"])), int(round(p["pitch"])),
               bool(p.get("soft")))
        if key != self.chan_key:
            if p["mode"] in PLL_MODES:               # carrier and both sidebands; picked apart later
                w2 = max(float(p["width"]), 50.0) / 2
                f1, f2 = -w2, w2
            else:
                f1, f2 = self.band(p)
            f1 = clamp(f1, -self.arate / 2 + 50, self.arate / 2 - 50)
            f2 = clamp(f2, -self.arate / 2 + 50, self.arate / 2 - 50)
            t1, t2 = self.edges(p, f1, f2)
            if p["mode"] in PLL_MODES and p.get("soft"):
                t1 = t2 = min(1000.0, 0.8 * (f2 - f1))
            self.chan.set(shaped_taps(f1, f2, self.arate, self.L, t1, t2), M)
            self.chan_key = key
        y = self.chan.process(x)
        lvl = 10 * math.log10(float(np.mean(y.real ** 2 + y.imag ** 2)) + 1e-20)

        mode = p["mode"]
        if mode not in PLL_MODES and self.pll["active"]:
            self.pll_reset()
        right = None                                           # second channel in the stereo modes
        if mode == "AM":
            env = np.abs(y)
            c = float(env.mean())
            self.am_c = c if self.am_c is None else 0.85 * self.am_c + 0.15 * c
            a = env - self.am_c
        elif mode == "ECSS":
            a = self.ecss(y, p)
        elif mode in STEREO_MODES:
            a, right = self.cquam(y, p) if mode == "CQUAM" else self.kahn(y, p)
        elif mode == "FM":
            z = np.concatenate(([self.fm_prev], y))
            d = np.angle(z[1:] * np.conj(z[:-1]))
            self.fm_prev = y[-1]
            a = d * (self.arate / (2 * math.pi * p["fm_dev"]))
            self.fm_dc = 0.95 * self.fm_dc + 0.05 * float(a.mean())
            a = a - self.fm_dc
        else:
            a = y.real

        if mode not in STEREO_MODES:
            self.stereo = False
        # low cut for AM / ECSS / FM / stereo: audio high-pass (SSB has it in the channel filter)
        lc = clamp(float(p["lowcut"]), 0.0, 1000.0)
        if mode in CARRIER_MODES + ("FM",) and lc >= 20:
            hk = (int(round(lc)), bool(p.get("soft")))
            if hk != self.hpf_key:
                t = min(400.0, 1.5 * lc) if p.get("soft") else 0.0
                lp = shaped_taps(-lc, lc, self.arate, 1025, t, t).real
                hp = -lp
                hp[512] += 1.0
                self.hpf.set(hp, M)
                self.hpf2.set(hp, M)
                self.hpf_key = hk
            a = self.hpf.process(a).real
            if right is not None:
                right = self.hpf2.process(right).real
        self.digi_audio = a if right is None else 0.5 * (a + right)
        if p.get("anf") and mode != "CW":
            self.anf_detect(a if right is None else 0.5 * (a + right), p)
            if self.anf_freq is not None:
                a = self.anf.process(a, round(self.anf_freq, 1))
                if right is not None:
                    right = self.anf2.process(right, round(self.anf_freq, 1))
        else:
            self.anf_freq = None
        if p["notch"]:
            a = self.notch.process(a, p["notch_hz"])
            if right is not None:
                right = self.notch2.process(right, p["notch_hz"])
        if p["nr"]:
            a = self.nr.process(a, p["nr_amt"])
            if right is not None:
                right = self.nr2.process(right, p["nr_amt"])
        tau = EMPHASIS.get(str(p.get("deemph", "Off")), 0.0)
        if tau:
            if self.de_key != tau:
                h = emphasis_taps(tau, self.arate, pre=False)
                self.de1.set(h, M)
                self.de2.set(h, M)
                self.de_key = tau
            a = self.de1.process(a).real
            if right is not None:
                right = self.de2.process(right).real

        maxg = 10 ** (p["gain_db"] / 20.0)
        if self.hold:
            g0 = g1 = self.agc_gain                            # AGC frozen while muted around TX
        elif p["agc"] == "Off":
            g0 = g1 = maxg
        else:
            tau = {"Fast": 0.15, "Med": 0.6, "Slow": 2.5}.get(p["agc"], 0.6)
            peak = float(np.max(np.abs(a))) + 1e-12
            if right is not None:
                peak = max(peak, float(np.max(np.abs(right))))
            self.agc_env = max(peak, self.agc_env * math.exp(-(M / float(self.arate)) / tau))
            g0, g1 = self.agc_gain, min(0.5 / self.agc_env, maxg)
        self.agc_gain = g1
        ramp = np.linspace(g0, g1, M, endpoint=False)
        # mute around TX, then fade back in over 60 ms (no click or noise burst)
        if self.hold:
            ramp = ramp * 0.0
            self.fade = 0.0
        elif self.fade < 1.0:
            f1 = min(1.0, self.fade + M / (0.06 * self.arate))
            ramp = ramp * np.linspace(self.fade, f1, M, endpoint=False)
            self.fade = f1
        vol = p["vol"] / 100.0
        out = np.tanh(a * ramp * vol)
        if right is not None:
            outr = np.tanh(right * ramp * vol)
        if lvl < p["squelch"]:
            out = out * 0.0
            if right is not None:
                outr = outr * 0.0
        if right is not None:
            st = np.empty((M, 2), dtype="<i2")
            st[:, 0] = out * 32000
            st[:, 1] = outr * 32000
            self.last_stereo = st
            self.audio_lr = (float(np.max(np.abs(out))), float(np.max(np.abs(outr))))
            out = 0.5 * (out + outr)                           # mono mix for meters / displays
        else:
            self.last_stereo = None
            self.audio_lr = None
        self.audio_level = float(np.max(np.abs(out)))       # demodulated audio, 0..1 (RX meter)
        A = np.abs(np.fft.rfft(out * self.af_win)) / self.af_wsum * 2.0
        self.af_spec = 20 * np.log10(A + 1e-7)               # audio spectrum, dB (AF display)
        return (out * 32000).astype("<i2"), spec, lvl


class TxDsp:
    """Microphone audio (M samples at `arate`) -> interleaved int16 I/Q (N samples at `rate`)."""
    BLK = 2048
    L = 2049

    def __init__(self, rate=192000, arate=48000):
        self.rate = int(rate)
        self.D = max(1, int(round(rate / float(arate))))
        self.arate = self.rate // self.D
        self.M = self.BLK
        self.N = self.M * self.D
        self.lock = threading.Lock()
        self.p = dict(mode="USB", lowcut=300.0, width=2400.0, mic_gain_db=20.0, drive=0.4,
                      source="mic", offset=0.0, carrier=False, key=False, fm_dev=5000.0,
                      am_depth=0.9, swap=False, invert=False, gain_bal_db=0.0, phase_deg=0.0,
                      dc_i=0.0, dc_q=0.0, audio_bw=3000.0, soft=False,
                      comp=False, comp_db=10.0, limiter=True, mod=0.8, preemph="Off")
        self.fa = FIR(bp_taps(300, 2700, self.arate, self.L), self.M)
        self.fa_key = None
        self.fu = FIR(lp_taps(self.arate / 2.0, self.rate, 64 * self.D + 1), self.N) if self.D > 1 else None
        self.ph = 0.0
        self.t1 = 0.0
        self.t2 = 0.0
        self.fm_ph = 0.0
        self.fm_last = 0.0
        self.dcm = 0.0
        self.env = 0.0
        self.comp_env = 0.0
        self.comp_g = 1.0
        self.lim_g = 1.0
        self.pre = FIR(np.array([1.0]), self.M)               # pre-emphasis
        self.pre_key = None
        self.comp_gr = 0.0          # dB of compression on the last block (for the display)
        self.lim_gr = 0.0           # dB the limiter took off
        self.mod_peak = 0.0         # AM / FM: peak modulation 0..1 (1 = 100 %)

    def set_params(self, **kw):
        with self.lock:
            self.p.update(kw)

    def idle(self):
        self.env = 0.0
        self.comp_gr = self.lim_gr = self.mod_peak = 0.0

    CH = 64                          # control chunk: 64 samples = 1.3 ms at 48 kHz

    def compress(self, a, amount_db):
        """Speech compressor, 4:1 above a threshold set by 'amount' (0..20 dB), with make-up gain
        so full-scale stays full-scale and quiet speech is lifted.  Attack 3 ms, release 150 ms,
        no boost below a noise gate (-40 dBFS) so background noise is not pumped up."""
        C = self.CH
        n = len(a) // C
        pk = np.abs(a[:n * C]).reshape(n, C).max(axis=1)
        th = 10 ** (-clamp(amount_db, 0.0, 30.0) / 20.0)
        r = 4.0
        makeup = th ** (1.0 / r - 1.0)
        att = 1 - math.exp(-C / (self.arate * 0.003))
        rel = 1 - math.exp(-C / (self.arate * 0.150))
        e = self.comp_env
        g = np.empty(n)
        for k in range(n):
            e += (att if pk[k] > e else rel) * (pk[k] - e)
            if e > th:
                gk = makeup * (e / th) ** (1.0 / r - 1.0)
            else:
                gk = makeup
            if e < 0.01:                                   # noise gate: no make-up gain on silence
                gk = 1.0 + (gk - 1.0) * (e / 0.01)
            g[k] = gk
        self.comp_env = e
        # smooth the gain from chunk to chunk (no zipper noise)
        xs = (np.arange(n) + 0.5) * C
        gs = np.interp(np.arange(len(a)), np.concatenate(([0.0], xs)), np.concatenate(([self.comp_g], g)))
        self.comp_g = float(g[-1])
        self.comp_gr = float(20 * math.log10(makeup / max(1e-6, float(g.min()))))
        return a * gs

    def limit(self, x, ceil):
        """Peak limiter: no sample above 'ceil'.  Works on 1.3 ms chunks, looks one chunk ahead
        so the gain is already down when a peak arrives, recovers over ~60 ms."""
        C = self.CH
        n = len(x) // C
        mag = np.abs(x[:n * C]).reshape(n, C).max(axis=1)
        target = np.minimum(1.0, ceil / (mag + 1e-12))
        ahead = np.minimum(target, np.concatenate((target[1:], target[-1:])))
        up = math.exp(-C / (self.arate * 0.060))
        g = np.empty(n)
        gk = self.lim_g
        for k in range(n):
            gk = min(ahead[k], 1.0 - (1.0 - gk) * up)
            g[k] = min(gk, target[k])                     # never let this chunk exceed the ceiling
        self.lim_g = float(gk)
        self.lim_gr = float(-20 * math.log10(max(1e-6, float(g.min()))))
        y = x[:n * C] * np.repeat(g, C)
        if len(x) > n * C:
            y = np.concatenate((y, x[n * C:] * g[-1]))
        return y

    def process(self, mic):
        with self.lock:
            p = dict(self.p)
        M, N, D = self.M, self.N, self.D
        src = p["source"]
        if not hasattr(self, "dpos"):
            self.dpos = self.dmade = 0
        if src == "mic":
            a = (mic - self.dcm) * 10 ** (p["mic_gain_db"] / 20.0)
            self.dcm = 0.98 * self.dcm + 0.02 * float(mic.mean())
        elif src in ("digi", "sstv", "nbtv"):          # Digital modes / SSTV / NBTV tabs
            dg = getattr(self, src, None)
            if dg is None:
                a = np.zeros(M)
            elif self.arate == DIGI_AUDIO:
                a = np.asarray(dg.tx_audio(M), dtype=np.float64)
            else:                                      # these are made at 48 kHz: resample to the audio rate
                n48 = int(round((self.dpos + M) * DIGI_AUDIO / float(self.arate))) - self.dmade
                self.dmade += n48
                self.dpos += M
                g = np.asarray(dg.tx_audio(n48), dtype=np.float64)
                a = np.interp(np.linspace(0, len(g) - 1, M), np.arange(len(g)), g) if len(g) > 1 else np.zeros(M)
            if p["mode"] in CARRIER_MODES + ("FM",):
                a = 2.0 * a
        else:
            t = np.arange(M) / float(self.arate)
            w1 = 2 * math.pi * (1000.0 if src == "tone" else 700.0)
            a = np.sin(self.t1 + w1 * t)
            self.t1 = (self.t1 + w1 * M / self.arate) % (2 * math.pi)
            # AM / FM: test tones at full scale, so 'Mod %' is exactly the modulation they give
            full = p["mode"] in CARRIER_MODES + ("FM",)
            if src == "tone":
                a = (1.0 if full else 0.5) * a
            else:
                w2 = 2 * math.pi * 1900.0
                a = (0.5 if full else 0.25) * (a + np.sin(self.t2 + w2 * t))
                self.t2 = (self.t2 + w2 * M / self.arate) % (2 * math.pi)
        mode = p["mode"]
        if mode in CARRIER_MODES:                      # ECSS / C-QuAM / Kahn are receive methods: TX AM
            mode = "AM"
        if src == "mic" and p.get("comp"):
            a = self.compress(a, float(p.get("comp_db", 10.0)))
        else:
            self.comp_gr = 0.0
        tau = EMPHASIS.get(str(p.get("preemph", "Off")), 0.0)
        if tau and src not in ("digi", "sstv", "nbtv"):                      # before the limiter: boosted highs stay in range
            if self.pre_key != tau:
                self.pre.set(emphasis_taps(tau, self.arate, pre=True), M)
                self.pre_key = tau
            a = self.pre.process(a).real
        if src == "mic" and p.get("limiter", True) and mode in ("USB", "LSB"):
            a = self.limit(a, 0.98)                    # keep the speech peaks out of the hard limiter below
        a = a.astype(complex)
        if mode in ("USB", "LSB"):
            key = (mode, int(round(p["lowcut"])), int(round(p["width"])), bool(p.get("soft")))
            if key != self.fa_key:
                lc, w = p["lowcut"], p["width"]
                f1, f2 = (lc, lc + w) if mode == "USB" else (-(lc + w), -lc)
                if p.get("soft"):
                    tl, th = min(400.0, 1.5 * lc), min(1000.0, 0.8 * w)
                    t1, t2 = (tl, th) if mode == "USB" else (th, tl)
                else:
                    t1 = t2 = 0.0
                self.fa.set(shaped_taps(f1, f2, self.arate, self.L, t1, t2), M)
                self.fa_key = key
            y = 2.0 * self.fa.process(a)               # one sideband of a real signal is half its level
            if p.get("limiter", True):
                y = self.limit(y, 0.95)                # smooth envelope limiter (the filter adds overshoot)
            else:
                self.lim_gr = 0.0
            y = y / np.maximum(1.0, np.abs(y))        # hard ceiling, last resort
            base = y
            self.mod_peak = 0.0
        elif mode in ("AM", "FM"):
            bw = clamp(float(p["audio_bw"]), 500.0, self.arate / 2 - 1000.0)
            key = ("LP", int(round(bw)), bool(p.get("soft")))
            if key != self.fa_key:
                t = min(1000.0, 0.8 * bw) if p.get("soft") else 0.0
                self.fa.set(shaped_taps(-bw, bw, self.arate, self.L, t, t), M)
                self.fa_key = key
            af = self.fa.process(a).real
            if p.get("limiter", True):
                af = self.limit(af, 1.0)               # smooth: peaks over 100 % are turned down
            else:
                self.lim_gr = 0.0
            af = np.clip(af, -1.0, 1.0)                # hard ceiling: never over 100 % modulation
            m = clamp(float(p.get("mod", p.get("am_depth", 0.8))), 0.0, 1.0)
            if mode == "AM":
                m = min(m, 0.99)                       # 100 % would pinch the carrier right off
            af = af * m
            self.mod_peak = float(np.max(np.abs(af)))
            if mode == "AM":
                base = (0.5 + 0.5 * af).astype(complex)
            else:
                arr = np.concatenate(([self.fm_last], af))
                self.fm_last = af[-1]
                xu = np.interp(np.arange(N) / float(D) + 1.0, np.arange(M + 1), arr)
                ph = self.fm_ph + np.cumsum(2 * math.pi * p["fm_dev"] * xu / self.rate)
                self.fm_ph = float(ph[-1]) % (2 * math.pi)
                base = np.exp(1j * ph)
        else:                                          # CW: carrier only
            base = np.zeros(M, dtype=complex)
        if mode == "FM":
            full = base
        elif D > 1:
            u = np.zeros(N, dtype=complex)
            u[::D] = base * D
            full = self.fu.process(u)
        else:
            full = base
        carrier = p["carrier"] or (mode == "CW" and p["key"])
        tgt = 1.0 if carrier else 0.0
        if carrier or self.env > 0.0:
            ramp = np.clip(np.arange(1, N + 1) / max(1.0, 0.005 * self.rate), 0.0, 1.0)
            env = self.env + (tgt - self.env) * ramp
            self.env = tgt
            full = full * (1.0 - env) + 0.5 * env
        if p["offset"] != 0.0 or self.ph != 0.0:
            w = 2 * math.pi * p["offset"] / self.rate
            full = full * np.exp(1j * (self.ph + w * np.arange(N)))
            self.ph = (self.ph + w * N) % (2 * math.pi)
        full = full * p["drive"]
        I, Q = full.real, full.imag
        if p["swap"]:
            I, Q = Q, I
        if p["invert"]:
            Q = -Q
        ph = math.radians(p["phase_deg"])
        Q = 10 ** (p["gain_bal_db"] / 20.0) * (Q * math.cos(ph) + I * math.sin(ph))
        I = I + p["dc_i"]
        Q = Q + p["dc_q"]
        out = np.empty(2 * N, dtype="<i2")
        out[0::2] = (np.clip(I, -1.0, 1.0) * 32700).astype("<i2")
        out[1::2] = (np.clip(Q, -1.0, 1.0) * 32700).astype("<i2")
        return out


class DemoSource:
    """Synthetic I/Q for trying the program without hardware."""

    def __init__(self, rate):
        self.rate = rate
        self.n0 = 0
        self.rng = np.random.RandomState(1)

    def block(self, N):
        t = (self.n0 + np.arange(N)) / float(self.rate)
        self.n0 += N
        x = (self.rng.randn(N) + 1j * self.rng.randn(N)) * 2e-4
        x += 0.02 * (1 + 0.6 * np.sin(2 * np.pi * 440 * t)) * np.exp(2j * np.pi * -39963 * t)   # AM, 37 Hz off
        x += 0.01 * np.exp(2j * np.pi * (25000 + 1200) * t) * (1 + 0.5 * np.sin(2 * np.pi * 3 * t))  # USB tone
        x += 0.02 * np.exp(1j * (2 * np.pi * 60000 * t + 5.0 * np.sin(2 * np.pi * 700 * t)))       # FM
        x += 0.01 * np.exp(2j * np.pi * -70000 * t) * (np.sin(2 * np.pi * 4 * t) > 0)               # CW
        # C-QuAM AM stereo station 45 kHz above the LO: left 500 Hz, right 1200 Hz (taking turns), 25 Hz pilot
        gate = (np.sin(2 * np.pi * 0.5 * t) > 0)
        sl, sr = 0.35 * gate * np.sin(2 * np.pi * 500 * t), 0.35 * ~gate * np.sin(2 * np.pi * 1200 * t)
        ci = 1 + sl + sr
        x += 0.015 * ci * np.exp(1j * np.arctan2(sl - sr + 0.05 * np.sin(2 * np.pi * 25 * t), ci)) \
            * np.exp(2j * np.pi * 45021 * t)
        return x


# ============================================================== digital modes
# PSK31 Varicode (G3PLX), index = ASCII code 0..127 (Wikipedia / ITU-R M.2034 table)
PSK_VARICODE = (
    "1010101011 1011011011 1011101101 1101110111 1011101011 1101011111 1011101111 1011111101 "
    "1011111111 11101111 11101 1101101111 1011011101 11111 1101110101 1110101011 "
    "1011110111 1011110101 1110101101 1110101111 1101011011 1101101011 1101101101 1101010111 "
    "1101111011 1101111101 1110110111 1101010101 1101011101 1110111011 1011111011 1101111111 "
    "1 111111111 101011111 111110101 111011011 1011010101 1010111011 101111111 "
    "11111011 11110111 101101111 111011111 1110101 110101 1010111 110101111 "
    "10110111 10111101 11101101 11111111 101110111 101011011 101101011 110101101 "
    "110101011 110110111 11110101 110111101 111101101 1010101 111010111 1010101111 "
    "1010111101 1111101 11101011 10101101 10110101 1110111 11011011 11111101 "
    "101010101 1111111 111111101 101111101 11010111 10111011 11011101 10101011 "
    "11010101 111011101 10101111 1101111 1101101 101010111 110110101 101011101 "
    "101110101 101111011 1010101101 111110111 111101111 111111011 1010111111 101101101 "
    "1011011111 1011 1011111 101111 101101 11 111101 1011011 "
    "101011 1101 111101011 10111111 11011 111011 1111 111 "
    "111111 110111111 10101 10111 101 110111 1111011 1101011 "
    "11011111 1011101 111010101 1010110111 110111011 1010110101 1011010111 1110110101").split()
PSK_ENC = {chr(i): c for i, c in enumerate(PSK_VARICODE)}
PSK_DEC = {c: chr(i) for i, c in enumerate(PSK_VARICODE)}

# DominoEX primary Varicode (ZL1BPU table), nibbles per ASCII code 0..255.
# The published table gives ':' and '<' the same code (0,8,10); '<' uses the one free code 0,10,8.
DOMINO_VARICODE = (
    "1,15,9 1,15,10 1,15,11 1,15,12 1,15,13 1,15,14 1,15,15 2,8,8 2,12 2,8,9 2,8,10 2,8,11 2,8,12 2,13 "
    "2,8,13 2,8,14 2,8,15 2,9,8 2,9,9 2,9,10 2,9,11 2,9,12 2,9,13 2,9,14 2,9,15 2,10,8 2,10,9 2,10,10 "
    "2,10,11 2,10,12 2,10,13 2,10,14 0 7,11 0,8,14 0,10,11 0,9,10 0,9,9 0,8,15 7,10 0,8,12 0,8,11 "
    "0,9,13 0,8,8 2,11 7,14 7,13 0,8,9 3,15 4,10 4,15 5,9 6,8 5,12 5,14 6,12 6,11 6,14 0,8,10 0,8,13 "
    "0,10,8 7,15 0,9,15 7,12 0,9,8 3,9 4,14 3,12 3,14 3,8 4,12 5,8 5,10 3,10 7,8 6,10 4,11 4,8 4,13 "
    "3,11 4,9 6,15 3,13 2,15 2,14 5,11 6,13 5,13 5,15 6,9 7,9 0,10,14 0,10,9 0,10,15 0,10,10 0,9,12 "
    "0,9,11 4 1,11 0,12 0,11 1 0,15 1,9 0,10 5 2,10 1,14 0,9 0,14 6 3 1,8 2,8 7 0,8 2 0,13 1,13 1,12 "
    "1,15 1,10 2,9 0,10,12 0,9,14 0,10,13 0,11,8 2,10,15 "
    "2,11,8 2,11,9 2,11,10 2,11,11 2,11,12 2,11,13 2,11,14 2,11,15 2,12,8 2,12,9 2,12,10 2,12,11 "
    "2,12,12 2,12,13 2,12,14 2,12,15 2,13,8 2,13,9 2,13,10 2,13,11 2,13,12 2,13,13 2,13,14 2,13,15 "
    "2,14,8 2,14,9 2,14,10 2,14,11 2,14,12 2,14,13 2,14,14 2,14,15 0,11,9 0,11,10 0,11,11 0,11,12 "
    "0,11,13 0,11,14 0,11,15 0,12,8 0,12,9 0,12,10 0,12,11 0,12,12 0,12,13 0,12,14 0,12,15 0,13,8 "
    "0,13,9 0,13,10 0,13,11 0,13,12 0,13,13 0,13,14 0,13,15 0,14,8 0,14,9 0,14,10 0,14,11 0,14,12 "
    "0,14,13 0,14,14 0,14,15 0,15,8 0,15,9 0,15,10 0,15,11 0,15,12 0,15,13 0,15,14 0,15,15 1,8,8 "
    "1,8,9 1,8,10 1,8,11 1,8,12 1,8,13 1,8,14 1,8,15 1,9,8 1,9,9 1,9,10 1,9,11 1,9,12 1,9,13 1,9,14 "
    "1,9,15 1,10,8 1,10,9 1,10,10 1,10,11 1,10,12 1,10,13 1,10,14 1,10,15 1,11,8 1,11,9 1,11,10 "
    "1,11,11 1,11,12 1,11,13 1,11,14 1,11,15 1,12,8 1,12,9 1,12,10 1,12,11 1,12,12 1,12,13 1,12,14 "
    "1,12,15 1,13,8 1,13,9 1,13,10 1,13,11 1,13,12 1,13,13 1,13,14 1,13,15 1,14,8 1,14,9 1,14,10 "
    "1,14,11 1,14,12 1,14,13 1,14,14 1,14,15 1,15,8").split()
DOMINO_ENC = {chr(i): tuple(int(n) for n in c.split(",")) for i, c in enumerate(DOMINO_VARICODE)}
DOMINO_DEC = {v: k for k, v in DOMINO_ENC.items()}
# DominoEX speeds: (original sample rate, symbol length, tone spacing in baud units)
DOMINO_MODES = {"4": (8000, 2048, 2), "5": (11025, 2048, 2), "8": (8000, 1024, 2),
                "11": (11025, 1024, 1), "16": (8000, 512, 1), "22": (11025, 512, 1)}

MORSE = {"A": ".-", "B": "-...", "C": "-.-.", "D": "-..", "E": ".", "F": "..-.", "G": "--.", "H": "....",
         "I": "..", "J": ".---", "K": "-.-", "L": ".-..", "M": "--", "N": "-.", "O": "---", "P": ".--.",
         "Q": "--.-", "R": ".-.", "S": "...", "T": "-", "U": "..-", "V": "...-", "W": ".--", "X": "-..-",
         "Y": "-.--", "Z": "--..", "0": "-----", "1": ".----", "2": "..---", "3": "...--", "4": "....-",
         "5": ".....", "6": "-....", "7": "--...", "8": "---..", "9": "----.", ".": ".-.-.-", ",": "--..--",
         "?": "..--..", "/": "-..-.", "=": "-...-", "+": ".-.-.", "-": "-....-", "(": "-.--.", ")": "-.--.-",
         "'": ".----.", '"': ".-..-.", ":": "---...", ";": "-.-.-.", "@": ".--.-.", "!": "-.-.--",
         "<SK>": "...-.-", "<AS>": ".-...", "<KN>": "-.--."}
MORSE_DEC = {v: k for k, v in MORSE.items() if k != "<KN>"}     # -.--. decodes as '('

DIGI_AUDIO = 48000


class Baseband:
    """Audio (48 kHz) -> complex baseband around f0, filtered to +-bw and resampled to fs_out.
    Two stages: 48 kHz -> 6 kHz (wide filter), then a sharp filter at 6 kHz, then resampling
    to any rate; sharp enough that nothing above fs_out / 2 folds back in."""
    D1 = 8
    FS1 = DIGI_AUDIO // 8

    def __init__(self, fs_out, bw, blk=2048):
        self.fs_out = float(fs_out)
        self.lp1 = FIR(lp_taps(1200.0, DIGI_AUDIO, 255), blk)
        trans = clamp(min(0.5 * bw, fs_out / 2.0 - bw - 5.0), 10.0, 200.0)
        L2 = int(min(1023, max(63, 5.5 * self.FS1 / trans))) | 1
        self.lp2 = FIR(lp_taps(bw + trans / 2.0, self.FS1, L2), blk // self.D1)
        self.ph = 0.0
        self.t = 0.0
        self.prev = 0j

    def process(self, x, f0):
        w = -2 * math.pi * f0 / DIGI_AUDIO
        z = x * np.exp(1j * (self.ph + w * np.arange(len(x))))
        self.ph = (self.ph + w * len(x)) % (2 * math.pi)
        y = self.lp2.process(self.lp1.process(z)[::self.D1])
        step = self.FS1 / self.fs_out
        pos = np.arange(self.t, len(y), step)
        if len(pos) == 0:
            self.t -= len(y)
            self.prev = y[-1]
            return np.zeros(0, dtype=complex)
        ext = np.concatenate(([self.prev], y))
        xi = np.arange(len(ext)) - 1.0
        out = np.interp(pos, xi, ext.real) + 1j * np.interp(pos, xi, ext.imag)
        self.t = pos[-1] + step - len(y)
        self.prev = y[-1]
        return out


class Psk31:
    """BPSK31: 31.25 baud, phase reversal = 0, steady = 1, Varicode with '00' between characters."""
    BAUD = 31.25
    SPS = 16                                  # receiver: 16 samples per symbol (500 Hz)
    TX_SPS = int(DIGI_AUDIO / 31.25)          # 1536 audio samples per symbol

    def __init__(self):
        self.bb = Baseband(self.BAUD * self.SPS, 40.0)
        self.sync = np.zeros(self.SPS)
        self.cnt = 0
        self.since = 8
        self.prev = 0j
        self.code = ""
        self.quality = 0.0
        self.ferr = 0.0
        # transmitter
        self.txbits = collections.deque()
        self.tx_sign = 1.0
        self.tx_pos = 0
        self.tx_bit = None
        self.tx_ph = 0.0

    def rx(self, audio, f0, afc=False):
        out = []
        ferr = 0.0
        for v in self.bb.process(audio, f0):
            i = self.cnt % self.SPS
            self.cnt += 1
            self.sync[i] = 0.95 * self.sync[i] + 0.05 * abs(v)
            self.since -= 1                                      # countdown to the next decision
            if self.since <= 0:
                # clock: next symbol 16 samples on, +-1 towards the amplitude peak (mid symbol)
                pk = int(np.argmax(self.sync))
                adj = 0
                if self.sync[pk] > 1.05 * np.mean(self.sync):
                    dlt = (pk - i + self.SPS // 2) % self.SPS - self.SPS // 2
                    adj = (dlt > 0) - (dlt < 0)
                self.since = self.SPS + adj
                d = v * np.conj(self.prev)
                self.prev = v
                if abs(d) < 1e-15:
                    continue
                e2 = np.angle(d * d)                        # BPSK: square to remove the data
                self.quality = 0.93 * self.quality + 0.07 * math.cos(e2)
                ferr += e2 / 2 / (2 * math.pi) * self.BAUD
                bit = "1" if d.real > 0 else "0"
                self.code += bit
                if self.code.endswith("00"):
                    c = self.code[:-2].lstrip("0")
                    self.code = ""
                    if c and self.quality > 0.6:
                        ch = PSK_DEC.get(c)
                        if ch is not None:
                            out.append(ch)
                elif len(self.code) > 14:
                    self.code = self.code[-2:]
        return "".join(out), ferr

    # --- transmit
    def queue(self, text):
        bits = "0" * 32                                       # preamble: reversals
        for ch in text:
            c = PSK_ENC.get(ch, PSK_ENC.get("?"))
            if ch == "\n":
                c = PSK_ENC["\r"] + "00" + PSK_ENC["\n"]
            bits += c + "00"
        bits += "1" * 24                                       # postamble: steady carrier
        self.txbits.extend(bits)
        self.txbits.append("E")                                # end: fade out

    def tx_busy(self):
        return bool(self.txbits) or self.tx_bit is not None

    def tx_audio(self, n, f0):
        out = np.zeros(n)
        k = 0
        T = self.TX_SPS
        while k < n:
            if self.tx_bit is None:
                if not self.txbits:
                    break
                self.tx_bit = self.txbits.popleft()
                self.tx_pos = 0
            m = min(n - k, T - self.tx_pos)
            p = (self.tx_pos + np.arange(m)) / float(T)
            if self.tx_bit == "0":
                env = self.tx_sign * np.cos(np.pi * p)            # smooth phase reversal
            elif self.tx_bit == "E":
                env = self.tx_sign * np.cos(0.5 * np.pi * p)      # fade out
            else:
                env = np.full(m, self.tx_sign)
            w = 2 * math.pi * f0 / DIGI_AUDIO
            out[k:k + m] = 0.5 * env * np.cos(self.tx_ph + w * np.arange(m))
            self.tx_ph = (self.tx_ph + w * m) % (2 * math.pi)
            self.tx_pos += m
            k += m
            if self.tx_pos >= T:
                if self.tx_bit == "0":
                    self.tx_sign = -self.tx_sign
                self.tx_bit = None
        return out

    def abort(self):
        self.txbits.clear()
        self.tx_bit = None


class DominoEX:
    """DominoEX: 18 tones, IFK+ (tone = previous + nibble + 2, mod 18), nibble Varicode."""
    NT = 18

    def __init__(self, speed="11"):
        sr, symlen, dbl = DOMINO_MODES.get(speed, DOMINO_MODES["11"])
        self.speed = speed
        self.baud = sr / float(symlen)
        self.dbl = dbl
        self.spacing = self.baud * dbl
        self.N = 32 * dbl                     # receiver: samples per symbol, bins are baud wide
        self.bb = Baseband(self.baud * self.N, (self.NT / 2 + 3) * self.spacing)
        self.win = collections.deque(maxlen=self.N)
        self.sync = np.zeros(self.N)
        self.cnt = 0
        self.since = 0
        self.prev_tone = None
        self.nibs = []
        self.quality = 0.0
        self.toff = 0.0                       # tuning error being tracked, in tones
        # transmitter
        self.txnibs = collections.deque()
        self.tx_tone = 0
        self.tx_left = 0.0
        self.tx_cur = None
        self.tx_ph = 0.0

    def bandwidth(self):
        return self.NT * self.spacing

    def rx(self, audio, f0, afc=False):
        out = []
        ferr = 0.0
        maxbin = (self.NT // 2 + 4) * self.dbl                 # search +-(9+4) tones
        for v in self.bb.process(audio, f0):
            self.win.append(v)
            if len(self.win) < self.N:
                continue
            i = self.cnt % self.N
            self.cnt += 1
            S = np.abs(np.fft.fft(np.array(self.win))) ** 2
            S = np.concatenate((S[-maxbin:], S[:maxbin + 1]))  # bins -maxbin .. +maxbin
            b = int(np.argmax(S))
            tot = float(S.sum()) + 1e-20
            self.sync[i] = 0.9 * self.sync[i] + 0.1 * S[b] / tot  # one clean tone per window = 1
            self.since -= 1                                      # countdown to the next symbol
            if self.since <= 0:
                pk = int(np.argmax(self.sync))
                adj = 0
                if self.sync[pk] > 1.05 * np.mean(self.sync):
                    dlt = (pk - i + self.N // 2) % self.N - self.N // 2
                    adj = (dlt > 0) - (dlt < 0)
                self.since = self.N + adj
                # tone position with sub-bin interpolation, less the tracked tuning offset
                frac = 0.0
                if 0 < b < len(S) - 1:
                    y0, y1, y2 = S[b - 1], S[b], S[b + 1]
                    den = y0 - 2 * y1 + y2
                    frac = clamp(0.5 * (y0 - y2) / den, -0.5, 0.5) if den else 0.0
                pos = (b - maxbin + frac) / float(self.dbl) - self.toff
                tone = int(round(pos))
                ratio = S[b] / tot
                self.quality = 0.9 * self.quality + 0.1 * ratio
                if ratio > 0.3:                                   # follow the tuning error (in tones)
                    self.toff += 0.15 * (pos - tone)
                if self.prev_tone is not None:
                    nib = (tone - self.prev_tone - 2) % self.NT
                    if nib < 16:
                        if nib < 8 and self.nibs:
                            ch = DOMINO_DEC.get(tuple(self.nibs))
                            if ch is not None and self.quality > 0.45 and (ch.isprintable() or ch in "\r\n"):
                                out.append("\n" if ch == "\r" else ch)
                            self.nibs = []
                        if nib < 8 or self.nibs:
                            self.nibs.append(nib)
                        if len(self.nibs) > 3:
                            self.nibs = []
                self.prev_tone = tone
        # AFC: hand the tracked offset over to the receiver frequency, a little at a time
        if afc and abs(self.toff) > 0.02:
            ferr = 0.1 * self.toff * self.spacing
            self.toff -= 0.1 * self.toff
        return "".join(out), ferr

    def queue(self, text):
        if not self.tx_busy():
            self.txnibs.extend([0] * 16)                       # preamble (idle): lets the receiver lock
        for ch in text:
            if ch == "\n":
                ch = "\r"
            self.txnibs.extend(DOMINO_ENC.get(ch, DOMINO_ENC["?"]))
        self.txnibs.extend(DOMINO_ENC[" "] * 3)              # flush the receiver's last character
        self.txnibs.append(None)                              # end

    def tx_busy(self):
        return bool(self.txnibs) or self.tx_cur is not None

    def tx_audio(self, n, f0):
        out = np.zeros(n)
        k = 0
        sym = DIGI_AUDIO / self.baud
        while k < n:
            if self.tx_cur is None:
                if not self.txnibs:
                    break
                nib = self.txnibs.popleft()
                if nib is None:
                    self.tx_cur = "end"
                    self.tx_left += sym * 0.5
                else:
                    self.tx_tone = (self.tx_tone + 2 + nib) % self.NT
                    self.tx_cur = self.tx_tone
                    self.tx_left += sym
            m = min(n - k, int(math.ceil(self.tx_left)))
            if m <= 0:
                self.tx_cur = None
                continue
            if self.tx_cur == "end":
                f = f0 + (self.tx_tone - self.NT // 2) * self.spacing
                env = np.linspace(1.0, 0.0, m)
            else:
                f = f0 + (self.tx_cur - self.NT // 2) * self.spacing
                env = 1.0
            w = 2 * math.pi * f / DIGI_AUDIO
            out[k:k + m] = 0.5 * env * np.sin(self.tx_ph + w * np.arange(m))
            self.tx_ph = (self.tx_ph + w * m) % (2 * math.pi)        # continuous phase
            k += m
            self.tx_left -= m
            if self.tx_left <= 0.5:
                self.tx_cur = None
        return out

    def abort(self):
        self.txnibs.clear()
        self.tx_cur = None


class CwModem:
    """CW (Morse): decoder that adapts to the speed, and a keyer for sending."""
    FS = 1000.0

    def __init__(self, wpm=20):
        self.wpm = wpm
        self.bb = Baseband(self.FS, 60.0)
        self.env = 0.0
        self.hi = 1e-6
        self.lo = 1e-7
        self.down = False
        self.run = 0
        self.dot = 1200.0 / wpm                               # ms
        self.elem = ""
        self.spaced = True
        self.quality = 0.0
        self.txq = collections.deque()
        self.tx_cur = None
        self.tx_left = 0
        self.tx_ph = 0.0
        self.tx_lvl = 0.0

    def rx(self, audio, f0, afc=False):
        out = []
        z = self.bb.process(audio, f0)
        for v in np.abs(z):
            self.env += 0.3 * (v - self.env)                  # ~3 ms smoothing
            e = self.env
            self.hi = e if e > self.hi else self.hi * 0.9995 + e * 0.0005
            self.lo = e if e < self.lo else self.lo * 0.995 + e * 0.005
            snr = self.hi / (self.lo + 1e-12)
            self.quality = 0.99 * self.quality + 0.01 * min(1.0, max(0.0, (snr - 2.0) / 8.0))
            thr_on = self.lo + 0.55 * (self.hi - self.lo)
            thr_off = self.lo + 0.40 * (self.hi - self.lo)
            self.run += 1
            ms = self.run * 1000.0 / self.FS
            if not self.down and e > thr_on and snr > 3.0:
                self.down, self.run = True, 0
            elif self.down and e < thr_off:
                self.down = False
                if ms > 0.3 * self.dot:                       # ignore glitches
                    if ms < 2.0 * self.dot:
                        self.elem += "."
                        self.dot = 0.85 * self.dot + 0.15 * ms
                    else:
                        self.elem += "-"
                        self.dot = 0.85 * self.dot + 0.15 * ms / 3.0
                    self.dot = clamp(self.dot, 20.0, 400.0)     # 3 .. 60 wpm
                    self.spaced = False
                self.run = 0
            elif not self.down:
                if self.elem and ms > 2.2 * self.dot:          # gap between characters
                    out.append(MORSE_DEC.get(self.elem, "*") if len(self.elem) < 8 else "")
                    self.elem = ""
                elif not self.elem and not self.spaced and ms > 5.0 * self.dot:   # gap between words
                    out.append(" ")
                    self.spaced = True
        return "".join(out), 0.0

    def queue(self, text):
        unit = int(DIGI_AUDIO * 1.2 / self.wpm)
        i = 0
        text = text.upper()
        while i < len(text):
            ch = text[i]
            if ch == "<" and ">" in text[i:]:
                j = text.index(">", i)
                code = MORSE.get(text[i:j + 1])
                i = j + 1
            else:
                code = MORSE.get(ch)
                i += 1
            if ch in " \n\r":
                self.txq.append((0, 4 * unit))                # +3 from the last letter = 7 units
                continue
            if not code:
                continue
            for n, e in enumerate(code):
                self.txq.append((1, unit if e == "." else 3 * unit))
                self.txq.append((0, unit))
            self.txq.append((0, 2 * unit))                    # letter gap 3 units
        self.txq.append((0, unit))
        self.txq.append(None)

    def tx_busy(self):
        return bool(self.txq) or self.tx_cur is not None

    def tx_audio(self, n, f0):
        out = np.zeros(n)
        k = 0
        edge = int(0.005 * DIGI_AUDIO)                        # 5 ms soft edges: no key clicks
        while k < n:
            if self.tx_cur is None:
                if not self.txq:
                    break
                item = self.txq.popleft()
                if item is None:
                    break
                self.tx_cur, self.tx_left = item
            m = min(n - k, self.tx_left)
            sgn = 1.0 if self.tx_cur else -1.0                # ramp the key level up or down
            lvl = np.clip(self.tx_lvl + sgn * np.arange(1, m + 1) / float(edge), 0.0, 1.0)
            shaped = 0.5 - 0.5 * np.cos(np.pi * lvl)          # raised cosine edges
            w = 2 * math.pi * f0 / DIGI_AUDIO
            out[k:k + m] = 0.5 * shaped * np.sin(self.tx_ph + w * np.arange(m))
            self.tx_ph = (self.tx_ph + w * m) % (2 * math.pi)
            self.tx_lvl = float(lvl[-1]) if m else self.tx_lvl
            k += m
            self.tx_left -= m
            if self.tx_left <= 0:
                self.tx_cur = None
        return out

    def abort(self):
        self.txq.clear()
        self.tx_cur = None


class DigiModem:
    """The digital modes: one decoder at a time on the demodulated audio, the RX text queue,
    the transmitter, AFC and the alignment spectrum."""
    MODES = ("PSK31", "DominoEX", "CW")

    def __init__(self):
        self.mode = "PSK31"
        self.f0 = 1000.0                      # audio frequency of the signal
        self.afc = True
        self.dom_speed = "11"
        self.cw_wpm = 20
        self.rx_text = queue.Queue()
        self.sent = queue.Queue()             # characters as they are sent (echo)
        self.tx_active = False
        self.lock = threading.Lock()
        self.ring = np.zeros(8192)
        self.spec = None                      # alignment spectrum: dB, 0 .. 3 kHz, 5.9 Hz bins
        self.spec_n = 0
        self.make()

    def make(self):
        with self.lock:
            if self.mode == "PSK31":
                self.dem = Psk31()
            elif self.mode == "DominoEX":
                self.dem = DominoEX(self.dom_speed)
            else:
                self.dem = CwModem(self.cw_wpm)

    def set_mode(self, mode, dom_speed=None, cw_wpm=None):
        changed = mode != self.mode or (dom_speed and dom_speed != self.dom_speed) or \
            (cw_wpm and cw_wpm != self.cw_wpm)
        self.mode = mode
        if dom_speed:
            self.dom_speed = dom_speed
        if cw_wpm:
            self.cw_wpm = int(cw_wpm)
        if changed:
            self.make()

    def bandwidth(self):
        if self.mode == "PSK31":
            return 62.5
        if self.mode == "DominoEX":
            return self.dem.bandwidth() if isinstance(self.dem, DominoEX) else 200.0
        return 100.0

    def quality(self):
        return float(getattr(self.dem, "quality", 0.0))

    def rx(self, audio):
        audio = np.asarray(audio, dtype=np.float64)
        n = len(audio)
        self.ring = np.concatenate((self.ring[n:], audio)) if n < len(self.ring) else audio[-len(self.ring):]
        self.spec_n += 1
        if self.spec_n % 2 == 0:
            S = np.abs(np.fft.rfft(self.ring * np.hanning(len(self.ring))))
            k = int(3000.0 * len(self.ring) / DIGI_AUDIO)
            self.spec = 20 * np.log10(S[:k] + 1e-9)
            p = S[:k] ** 2                                    # averaged power, for the carrier checks
            self.spec_avg = p if getattr(self, "spec_avg", None) is None else 0.8 * self.spec_avg + 0.2 * p
        with self.lock:
            dem = self.dem
        if self.tx_active:
            return
        if self.afc and self.mode == "PSK31" and self.spec is not None:
            # Once a second check the carrier against the spectrum: a BPSK loop can also sit
            # 15.6 Hz (half the baud rate) off, where every bit comes out inverted.
            q = dem.quality
            if q > 0.5 and getattr(self, "q_was_low", True):  # a signal has just appeared
                self.fresh = 1
            self.q_was_low = q < 0.3 if (q < 0.3 or q > 0.5) else getattr(self, "q_was_low", True)
            self.chk = getattr(self, "chk", 0) + 1
            fresh = getattr(self, "fresh", 0)
            if fresh:
                self.fresh += 1
                if self.fresh in (12, 24):                    # quick checks ~0.5 s and ~1 s after it started
                    c = self.centroid(self.f0, 40.0)
                    if c is not None and abs(c - self.f0) > 10.0:
                        self.f0 = c
                    if self.fresh == 24:
                        self.fresh = 0
                        self.chk = 0
            elif self.chk >= 48:                              # then every 2 s, two checks must agree
                self.chk = 0
                c = self.centroid(self.f0, 40.0)
                prev, self.c_prev = getattr(self, "c_prev", None), c
                if c is not None and prev is not None and abs(c - self.f0) > 10.0 and abs(c - prev) < 4.0:
                    self.f0 = 0.5 * (c + prev)
        txt, ferr = dem.rx(audio, self.f0, self.afc)
        if self.afc and ferr and self.mode != "CW":
            g = 0.05 if self.mode == "PSK31" else 1.0         # PSK31: ferr is raw; DominoEX: already scaled
            self.f0 += clamp(ferr * g, -2.0, 2.0)             # follow a drifting signal, gently
        if txt:
            self.rx_text.put(txt)

    def centroid(self, near, span):
        """Centre of a clear signal within +-span of 'near' (None if there is none)."""
        binw = DIGI_AUDIO / float(len(self.ring))
        f = np.arange(len(self.spec)) * binw
        m = (f > near - span) & (f < near + span)
        if m.sum() < 5:
            return None
        sp = 10 * np.log10(self.spec_avg + 1e-30) if getattr(self, "spec_avg", None) is not None else self.spec
        s = sp[m]
        if s.max() < np.median(sp[(f > 200) & (f < 2800)]) + 10.0:
            return None                                       # nothing standing out of the noise
        pk = int(np.argmax(s))
        k = max(1, int(25.0 / binw))
        fs, ss = f[m], 10 ** (s / 10.0)
        sl = slice(max(0, pk - k), pk + k + 1)
        return float(np.sum(fs[sl] * ss[sl]) / (np.sum(ss[sl]) + 1e-30))

    def find(self, near=None, span=150.0):
        """Put f0 on the strongest signal (near a frequency, or anywhere 200 - 2800 Hz)."""
        if self.spec is None:
            return self.f0
        binw = DIGI_AUDIO / float(len(self.ring))
        f = np.arange(len(self.spec)) * binw
        if near is None:
            m = (f > 200) & (f < 2800)
        else:
            m = (f > near - span) & (f < near + span)
        if not m.any():
            return self.f0
        s = np.where(m, self.spec, -1e9)
        if self.mode == "PSK31":                              # centre of the energy around the peak
            pk = int(np.argmax(s))
            k = max(1, int(25.0 / binw))
            sl = slice(max(0, pk - k), pk + k + 1)
            pw = 10 ** (self.spec[sl] / 10.0) * m[sl]
            self.f0 = float(np.sum(f[sl] * pw) / (np.sum(pw) + 1e-30))
        elif self.mode == "DominoEX":                           # centre of the energy across the tones
            bw = self.bandwidth()
            k = max(1, int(bw / binw))
            p = np.convolve(10 ** (s / 10.0), np.ones(k), "same")
            self.f0 = float(f[int(np.argmax(p))])
        else:
            self.f0 = float(f[int(np.argmax(s))])
        return self.f0

    # --- transmit
    def send(self, text):
        with self.lock:
            self.dem.queue(text)
        self.sent.put(text)                                   # shown in the RX window as sent text
        self.tx_active = True

    def tx_audio(self, n):
        with self.lock:
            return self.dem.tx_audio(n, self.f0)

    def tx_done(self):
        return self.tx_active and not self.dem.tx_busy()

    def abort(self):
        with self.lock:
            self.dem.abort()
        self.tx_active = False


# ============================================================== SSTV
# Frequencies: sync 1200 Hz, black 1500 Hz, white 2300 Hz; VIS bits 1100 Hz = 1, 1300 Hz = 0.
# Each mode is one transmitted line as a list of pieces:
#   ("sync", ms)        1200 Hz line sync         ("tone", ms, Hz)   a fixed tone (porch, separator)
#   ("ch", ms, name)    pixels of channel R G B Y U V Y0 Y1        ("sep36", ms)  Robot 36 U/V marker
SSTV_SYNC, SSTV_BLACK, SSTV_WHITE = 1200.0, 1500.0, 2300.0


def _martin(c):
    return [("sync", 4.862), ("tone", 0.572, 1500), ("ch", c, "G"), ("tone", 0.572, 1500), ("ch", c, "B"),
            ("tone", 0.572, 1500), ("ch", c, "R"), ("tone", 0.572, 1500)]


def _scottie(c):
    return [("tone", 1.5, 1500), ("ch", c, "G"), ("tone", 1.5, 1500), ("ch", c, "B"), ("sync", 9.0),
            ("tone", 1.5, 1500), ("ch", c, "R")]


def _pd(c):
    return [("sync", 20.0), ("tone", 2.08, 1500), ("ch", c, "Y0"), ("ch", c, "V"), ("ch", c, "U"),
            ("ch", c, "Y1")]


# name: (VIS code, width, height, colour kind, line pieces, sync sent once before the first line ms)
SSTV_MODES = collections.OrderedDict([
    ("Martin M1", (44, 320, 256, "rgb", _martin(146.432), 0.0)),
    ("Martin M2", (40, 320, 256, "rgb", _martin(73.216), 0.0)),
    ("Scottie S1", (60, 320, 256, "rgb", _scottie(138.240), 9.0)),
    ("Scottie S2", (56, 320, 256, "rgb", _scottie(88.064), 9.0)),
    ("Scottie DX", (76, 320, 256, "rgb", _scottie(345.600), 9.0)),
    ("Robot 36", (8, 320, 240, "r36", [("sync", 9.0), ("tone", 3.0, 1500), ("ch", 88.0, "Y"),
                                       ("sep36", 4.5), ("tone", 1.5, 1900), ("ch", 44.0, "C")], 0.0)),
    ("Robot 72", (12, 320, 240, "yuv", [("sync", 9.0), ("tone", 3.0, 1500), ("ch", 138.0, "Y"),
                                        ("tone", 4.5, 1500), ("tone", 1.5, 1900), ("ch", 69.0, "V"),
                                        ("tone", 4.5, 2300), ("tone", 1.5, 1900), ("ch", 69.0, "U")], 0.0)),
    ("PD50", (93, 320, 256, "pd", _pd(91.520), 0.0)),
    ("PD90", (99, 320, 256, "pd", _pd(170.240), 0.0)),
    ("PD120", (95, 640, 496, "pd", _pd(121.600), 0.0)),
    ("PD160", (98, 512, 400, "pd", _pd(195.584), 0.0)),
    ("PD180", (96, 640, 496, "pd", _pd(183.040), 0.0)),
    ("PD240", (97, 640, 496, "pd", _pd(244.480), 0.0)),
    ("PD290", (94, 800, 616, "pd", _pd(228.800), 0.0)),
    ("Wraase SC2-180", (55, 320, 256, "rgb", [("sync", 5.5225), ("tone", 0.5, 1500), ("ch", 235.0, "R"),
                                              ("ch", 235.0, "G"), ("ch", 235.0, "B")], 0.0)),
])
SSTV_BY_VIS = {v[0]: k for k, v in SSTV_MODES.items()}


class SstvLayout:
    """Timing of one mode: where the sync and every channel sit in a transmitted line."""

    def __init__(self, name):
        self.name = name
        self.vis, self.w, self.h, self.kind, self.pieces, self.pre = SSTV_MODES[name]
        self.rows_per_line = 2 if self.kind == "pd" else 1
        self.lines = self.h // self.rows_per_line
        t = 0.0
        self.sync_ms = self.sync_at = None
        self.chans = []                                   # (name, start ms, length ms)
        self.sep_at = None
        for p in self.pieces:
            if p[0] == "sync" and self.sync_at is None:
                self.sync_at, self.sync_ms = t, p[1]
            elif p[0] == "ch":
                self.chans.append((p[2], t, p[1]))
            elif p[0] == "sep36":
                self.sep_at = (t, p[1])
            t += p[1]
        self.line_ms = t
        self.total_s = (self.pre + self.lines * t) / 1000.0


def rgb_to_yuv(img):
    f = img.astype(np.float64)
    y = 0.299 * f[..., 0] + 0.587 * f[..., 1] + 0.114 * f[..., 2]
    u = 128.0 + 0.564 * (f[..., 2] - y)                   # B - Y
    v = 128.0 + 0.713 * (f[..., 0] - y)                   # R - Y
    return np.clip(y, 0, 255), np.clip(u, 0, 255), np.clip(v, 0, 255)


def yuv_to_rgb(y, u, v):
    r = y + 1.402 * (v - 128.0)
    b = y + 1.772 * (u - 128.0)
    g = (y - 0.299 * r - 0.114 * b) / 0.587
    return np.clip(np.stack([r, g, b], axis=-1), 0, 255).astype(np.uint8)


def fit_image(img, w, h):
    """Scale an RGB array to w x h, filling the frame (centre crop), area-averaged."""
    H, W = img.shape[:2]
    s = max(w / float(W), h / float(H))
    cw, ch = min(W, int(round(w / s))), min(H, int(round(h / s)))
    x0, y0 = (W - cw) // 2, (H - ch) // 2
    crop = img[y0:y0 + ch, x0:x0 + cw].astype(np.float64)
    # area average with cumulative sums (works for up- and down-scaling)
    def axis_resample(a, n, ax):
        m = a.shape[ax]
        edges = np.linspace(0, m, n + 1)
        cs = np.concatenate([np.zeros_like(np.take(a, [0], axis=ax)), np.cumsum(a, axis=ax)], axis=ax)
        idx = np.arange(m + 1)
        lo = edges[:-1]
        hi = np.maximum(edges[1:], lo + 1e-6)
        def at(x):
            i = np.clip(np.floor(x).astype(int), 0, m - 1)
            fr = (x - i).reshape([-1 if k == ax else 1 for k in range(a.ndim)])
            return np.take(cs, i, axis=ax) + fr * (np.take(cs, i + 1, axis=ax) - np.take(cs, i, axis=ax))
        shape = [-1 if k == ax else 1 for k in range(a.ndim)]
        return (at(hi) - at(lo)) / (hi - lo).reshape(shape)
    out = axis_resample(axis_resample(crop, h, 0), w, 1)
    return np.clip(out, 0, 255).astype(np.uint8)


def sstv_encode(img, name, fs=DIGI_AUDIO, preamble=True):
    """RGB image (h x w x 3, uint8, already the mode's size) -> phase continuous audio."""
    L = SstvLayout(name)
    if img.shape[:2] != (L.h, L.w):
        img = fit_image(img, L.w, L.h)
    y, u, v = rgb_to_yuv(img)
    rgb = img.astype(np.float64)
    pieces = []                                           # (seconds, Hz or array of pixel Hz)
    if preamble:                                          # MMSSTV style tuning header
        for f in (1900, 1500, 1900, 1500, 2300, 1500, 2300, 1500):
            pieces.append((0.1, f))
    pieces += [(0.3, 1900), (0.01, 1200), (0.3, 1900), (0.03, 1200)]
    bits = [(L.vis >> i) & 1 for i in range(7)]
    bits.append(sum(bits) & 1)                            # even parity
    pieces += [(0.03, 1100 if b else 1300) for b in bits]
    pieces.append((0.03, 1200))
    if L.pre:
        pieces.append((L.pre / 1000.0, 1200))

    def hz(a):
        return SSTV_BLACK + np.asarray(a, dtype=np.float64) / 255.0 * (SSTV_WHITE - SSTV_BLACK)

    for k in range(L.lines):
        if L.kind == "pd":
            r0, r1 = 2 * k, 2 * k + 1
            ch = {"Y0": y[r0], "Y1": y[r1], "U": 0.5 * (u[r0] + u[r1]), "V": 0.5 * (v[r0] + v[r1])}
        elif L.kind == "r36":
            pr = k ^ 1 if k ^ 1 < L.h else k
            ch = {"Y": y[k], "C": 0.5 * (v[k] + v[pr]) if k % 2 == 0 else 0.5 * (u[k] + u[pr])}
        elif L.kind == "yuv":
            ch = {"Y": y[k], "U": u[k], "V": v[k]}
        else:
            ch = {"R": rgb[k, :, 0], "G": rgb[k, :, 1], "B": rgb[k, :, 2]}
        for p in L.pieces:
            if p[0] == "sync":
                pieces.append((p[1] / 1000.0, SSTV_SYNC))
            elif p[0] == "tone":
                pieces.append((p[1] / 1000.0, p[2]))
            elif p[0] == "sep36":
                pieces.append((p[1] / 1000.0, 1500 if k % 2 == 0 else 2300))
            else:
                pieces.append((p[1] / 1000.0, hz(ch[p[2]])))
    total = sum(d for d, _ in pieces)
    n = int(math.ceil(total * fs))
    f = np.empty(n)
    t = 0.0
    for d, val in pieces:
        a, b = int(round(t * fs)), min(n, int(round((t + d) * fs)))
        if np.isscalar(val):
            f[a:b] = val
        else:
            i = ((np.arange(a, b) / fs - t) / d * len(val)).astype(int)
            f[a:b] = val[np.clip(i, 0, len(val) - 1)]
        t += d
    f[int(round(t * fs)):] = 1500.0
    k = np.ones(5) / 5.0                                  # soften the steps a little (less splatter)
    f = np.convolve(f, k, mode="same")
    ph = 2 * math.pi * np.cumsum(f) / fs
    out = 0.5 * np.sin(ph)
    ramp = int(0.005 * fs)                                # soft start and end
    out[:ramp] *= np.linspace(0, 1, ramp)
    out[-ramp:] *= np.linspace(1, 0, ramp)
    return out.astype(np.float32)


def parse_ppm(data):
    """Binary PPM (P6) / PGM (P5) bytes -> RGB array."""
    toks, i = [], 0
    while len(toks) < 4:
        while data[i:i + 1].isspace():
            i += 1
        if data[i:i + 1] == b"#":
            while data[i:i + 1] not in (b"\n", b""):
                i += 1
            continue
        j = i
        while not data[j:j + 1].isspace():
            j += 1
        toks.append(data[i:j])
        i = j
    i += 1
    kind, w, h, mx = toks[0], int(toks[1]), int(toks[2]), int(toks[3])
    ch = 3 if kind == b"P6" else 1
    dt = np.uint8 if mx < 256 else ">u2"
    a = np.frombuffer(data, dtype=dt, count=w * h * ch, offset=i).reshape(h, w, ch).astype(np.float64)
    a = np.clip(a * 255.0 / mx, 0, 255).astype(np.uint8)
    return np.repeat(a, 3, axis=2) if ch == 1 else a


def read_image(path):
    """Any picture file -> RGB array (Pillow if installed, else Tk: PNG, GIF, PPM, PGM)."""
    if Image is not None:
        with Image.open(path) as im:
            return np.asarray(im.convert("RGB")).copy()
    if path.lower().endswith((".ppm", ".pgm", ".pnm")):
        with open(path, "rb") as f:
            return parse_ppm(f.read())
    ph = tk.PhotoImage(file=path)
    import tempfile
    fd, tmp = tempfile.mkstemp(suffix=".ppm")
    os.close(fd)
    try:
        ph.write(tmp, format="ppm")
        with open(tmp, "rb") as f:
            return parse_ppm(f.read())
    finally:
        os.unlink(tmp)


def save_image(img, path):
    if Image is not None:
        Image.fromarray(np.ascontiguousarray(img)).save(path)
        return
    ppm = b"P6 %d %d 255\n" % (img.shape[1], img.shape[0]) + np.ascontiguousarray(img).tobytes()
    if path.lower().endswith(".ppm"):
        with open(path, "wb") as f:
            f.write(ppm)
        return
    tk.PhotoImage(data=ppm, format="PPM").write(path, format="png")


def capture_screen(box=None):
    """Picture of the screen (or the box x, y, w, h) as an RGB array.  Tries Pillow (X11), then the
    usual screenshot programs: grim (Wayland), gnome-screenshot, spectacle (KDE), import, scrot."""
    import tempfile
    err = []
    if Image is not None:
        try:
            from PIL import ImageGrab
            im = ImageGrab.grab(bbox=None if box is None else (box[0], box[1], box[0] + box[2], box[1] + box[3]))
            a = np.asarray(im.convert("RGB")).copy()
            if a.size and a.max() > 0:                    # Wayland can give an all-black picture
                return a
        except Exception as e:
            err.append("Pillow: %s" % e)
    fd, tmp = tempfile.mkstemp(suffix=".png")
    os.close(fd)
    cmds = []
    if shutil.which("grim"):
        cmds.append(["grim"] + (["-g", "%d,%d %dx%d" % box] if box else []) + [tmp])
    if shutil.which("gnome-screenshot"):
        cmds.append(["gnome-screenshot", "-f", tmp])
    if shutil.which("spectacle"):
        cmds.append(["spectacle", "-b", "-n", "-f", "-o", tmp])
    if shutil.which("import"):
        cmds.append(["import", "-silent", "-window", "root"] + (["-crop", "%dx%d+%d+%d" % (box[2], box[3],
                                                                   box[0], box[1])] if box else []) + [tmp])
    if shutil.which("scrot"):
        cmds.append(["scrot", "-o"] + (["-a", "%d,%d,%d,%d" % box] if box else []) + [tmp])
    try:
        for c in cmds:
            try:
                if os.path.exists(tmp):
                    os.unlink(tmp)
                subprocess.run(c, timeout=10, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                if os.path.exists(tmp) and os.path.getsize(tmp) > 0:
                    if Image is None:
                        raise RuntimeError("reading the screenshot needs python3-pil")
                    a = read_image(tmp)
                    full = c[0] in ("gnome-screenshot", "spectacle") or (c[0] == "import" and box is None)
                    if box is not None and (full or a.shape[0] > box[3] + 4):
                        x, y, w, h = box
                        a = a[max(0, y):y + h, max(0, x):x + w]
                    return a
            except (OSError, subprocess.SubprocessError) as e:
                err.append("%s: %s" % (c[0], e))
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)
    raise RuntimeError("no screen capture tool worked (install python3-pil, or grim / gnome-screenshot / "
                       "scrot)" + ("; " + "; ".join(err) if err else ""))


def overlay_text(img, text):
    """Callsign / message across the top of the picture, white with a black outline (Pillow)."""
    if Image is None or not text:
        return img
    im = Image.fromarray(np.ascontiguousarray(img))
    h = im.size[1]
    size = max(12, h // 9)
    font = None
    for name in ("DejaVuSans-Bold.ttf", "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
                 "LiberationSans-Bold.ttf", "/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf"):
        try:
            font = ImageFont.truetype(name, size)
            break
        except Exception:
            pass
    if font is None:
        try:
            font = ImageFont.load_default(size=size)
        except Exception:
            font = ImageFont.load_default()
    d = ImageDraw.Draw(im)
    d.text((max(4, im.size[0] // 40), max(2, h // 50)), text, font=font, fill=(255, 255, 255),
           stroke_width=max(1, size // 12), stroke_fill=(0, 0, 0))
    return np.asarray(im).copy()


def sstv_test_card(w=320, h=256):
    """Colour bars and a grey scale: the picture to send until one is loaded."""
    img = np.zeros((h, w, 3), dtype=np.uint8)
    bars = [(255, 255, 255), (255, 255, 0), (0, 255, 255), (0, 255, 0), (255, 0, 255), (255, 0, 0),
            (0, 0, 255), (0, 0, 0)]
    for i, c in enumerate(bars):
        img[:int(h * 0.62), i * w // 8:(i + 1) * w // 8] = c
    g = (np.arange(w) * 255 // (w - 1)).astype(np.uint8)
    img[int(h * 0.62):int(h * 0.8)] = np.stack([g, g, g], -1)
    for i in range(8):
        img[int(h * 0.8):, i * w // 8:(i + 1) * w // 8] = i * 255 // 7
    return overlay_text(img, "ExSDR") if Image is not None else img


class SstvTx:
    """Plays a prepared SSTV transmission into the transmitter."""

    def __init__(self):
        self.audio = None
        self.pos = 0
        self.tx_active = False
        self.lock = threading.Lock()

    def load(self, audio):
        with self.lock:
            self.audio, self.pos = audio, 0
        self.tx_active = True

    def tx_audio(self, n):
        with self.lock:
            out = np.zeros(n)
            if self.audio is not None and self.pos < len(self.audio):
                seg = self.audio[self.pos:self.pos + n]
                out[:len(seg)] = seg
                self.pos += n
            return out

    def progress(self):
        a = self.audio
        return 0.0 if a is None or not len(a) else min(1.0, self.pos / float(len(a)))

    def tx_done(self):
        return self.tx_active and (self.audio is None or self.pos >= len(self.audio))

    def abort(self):
        with self.lock:
            self.audio, self.pos = None, 0
        self.tx_active = False


class SstvRx:
    """SSTV receiver: FM discriminator on the demodulated audio, VIS detection, line sync tracking
    (corrects slant from sound card clock differences) and image decoding."""
    FS = 12000.0                      # discriminator rate
    FC = 1750.0                       # centre of the SSTV band 1100 .. 2300 Hz

    def __init__(self):
        self.lp = FIR(lp_taps(1000.0, DIGI_AUDIO, 191), 2048)
        self.ph = 0.0
        self.prev = 0j
        self.lock = threading.Lock()
        self.ring = np.zeros(2048, dtype=complex)        # recent baseband for the tuning display
        self.fms = np.zeros(0)                            # 1 ms averages of the frequency, for VIS
        self.ms0 = 0                                      # global index of fms[0]
        self.n = 0                                        # samples of frequency seen (12 kHz)
        self.part = np.zeros(0)                           # samples not yet averaged into fms
        self.vis_cand = None
        self.events = queue.Queue()                       # ("start", mode) ("done", mode, image, ok)
        self.offset = 0.0                                 # mistuning measured on the VIS / syncs
        self.force = None                                 # mode name: start without VIS
        self.auto = True                                  # start on VIS
        self.state = "idle"
        self.mode = None
        self.L = None
        self.img = None
        self.line = 0
        self.version = 0                                  # changes when the image changes
        self.last_vis = ""
        self.recent = np.zeros(0)

    # ---------------------------------------------------------------- front end
    def rx(self, audio):
        w = -2 * math.pi * self.FC / DIGI_AUDIO
        z = audio * np.exp(1j * (self.ph + w * np.arange(len(audio))))
        self.ph = (self.ph + w * len(audio)) % (2 * math.pi)
        y = self.lp.process(z)[::4]
        self.ring = np.concatenate((self.ring, y))[-2048:]
        d = np.empty(len(y))
        d[0] = np.angle(y[0] * np.conj(self.prev))
        d[1:] = np.angle(y[1:] * np.conj(y[:-1]))
        self.prev = y[-1]
        f = np.clip(self.FC + d * self.FS / (2 * math.pi), 900.0, 2600.0)
        with self.lock:
            self.feed(f)

    def feed(self, f):
        self.n += len(f)
        self.recent = np.concatenate((self.recent, f))[-24000:]
        if self.state == "rx":
            self.buf_add(f)
        # 1 ms averages
        p = np.concatenate((self.part, f))
        k = len(p) // 12
        self.part = p[k * 12:]
        if k:
            new = p[:k * 12].reshape(k, 12).mean(axis=1)
            self.fms = np.concatenate((self.fms, new))
            if len(self.fms) > 1500:
                cut = len(self.fms) - 1500
                self.fms = self.fms[cut:]
                self.ms0 += cut
            if self.auto:
                self.find_vis(k)
        if self.state == "rx":
            self.decode_ready()

    # ---------------------------------------------------------------- VIS
    def find_vis(self, k):
        a = self.fms
        if len(a) < 640:
            if self.vis_cand is not None:
                self.vis_cand = None
            return
        cs = np.concatenate(([0.0], np.cumsum(a)))

        def mean(lo, hi):                                  # windows relative to the end e (arrays)
            return (cs[e + hi] - cs[e + lo]) / float(hi - lo)

        e = np.arange(max(610, len(a) - k), len(a) + 1)
        stop = mean(-25, -5)
        start = mean(-295, -275)
        lead = mean(-580, -320)
        off = lead - 1900.0
        ok = (np.abs(off) < 150) & (np.abs(stop - 1200 - off) < 60) & (np.abs(start - 1200 - off) < 60)
        for i in np.nonzero(ok)[0]:
            ei = int(e[i])
            seg = a[ei - 580:ei - 320]
            o = float(np.median(seg))
            if np.mean(np.abs(seg - o) < 60) < 0.7:
                continue
            o -= 1900.0
            bits, err = [], abs(stop[i] - 1200 - o) + abs(start[i] - 1200 - o)
            for b in range(8):
                lo = ei - 270 + 30 * b + 8
                val = float(np.mean(a[lo:lo + 14])) - o
                if abs(val - 1100) < 70:
                    bits.append(1)
                    err += abs(val - 1100)
                elif abs(val - 1300) < 70:
                    bits.append(0)
                    err += abs(val - 1300)
                else:
                    break
            if len(bits) < 8 or sum(bits[:7]) % 2 != bits[7]:
                continue
            code = sum(bit << j for j, bit in enumerate(bits[:7]))
            if code not in SSTV_BY_VIS:
                continue
            g = self.ms0 + ei
            if self.vis_cand is None or err < self.vis_cand[1]:
                self.vis_cand = (g, err, code, o)
        c = self.vis_cand
        if c is not None and self.ms0 + len(a) - c[0] > 12:   # best alignment found: start the image
            self.vis_cand = None
            self.last_vis = "%s (VIS %d)" % (SSTV_BY_VIS[c[2]], c[2])
            self.offset = c[3]
            self.begin(SSTV_BY_VIS[c[2]], start=c[0] * 12, offset=c[3])
            self.fms = self.fms[-1:]                       # no second detection of the same header
            self.ms0 += len(a) - 1

    # ---------------------------------------------------------------- image
    def begin(self, name, start=None, offset=None):
        """Start an image at global sample 'start' (end of VIS), or now without a VIS."""
        if self.state == "rx" and self.line > 8:
            self.finish(False)
        L = self.L = SstvLayout(name)
        self.mode = name
        self.fs_line = L.line_ms * self.FS / 1000.0
        self.manual = start is None
        self.t_start = (self.n if start is None else start) + L.pre * self.FS / 1000.0
        self.buf = np.zeros(int(self.fs_line * (L.lines + 2) + self.FS * 2))
        self.buf0 = int(self.t_start - self.FS * 0.05)     # global sample index of buf[0]
        # samples already received after buf0 (the end of the VIS is just behind us)
        self.buf_n = 0
        self.state = "rx"
        back = self.n - self.buf0
        if back > 0 and len(self.recent) >= back:
            self.buf_add(self.recent[-back:])
        if offset is not None:
            self.offset = offset
        self.syncs = []                                     # (line, sample position)
        self.a, self.b = self.t_start + L.sync_at * self.FS / 1000.0, self.fs_line
        self.locked = not self.manual
        self.misses = 0
        self.planes = {c: np.zeros((L.lines, L.w)) for c in ("R", "G", "B", "Y", "U", "V", "Y0", "Y1", "C")}
        self.sepv = np.zeros(L.lines)
        self.img = np.zeros((L.h, L.w, 3), dtype=np.uint8)
        self.line = 0
        self.state = "rx"
        self.version += 1
        self.events.put(("start", name))

    def buf_add(self, f):
        if self.state != "rx":
            return
        room = len(self.buf) - self.buf_n
        m = min(room, len(f))
        if m > 0:
            self.buf[self.buf_n:self.buf_n + m] = f[:m]
            self.buf_n += m

    def stop(self):
        with self.lock:
            if self.state == "rx":
                self.finish(self.line > 8)

    def start_now(self, name):
        with self.lock:
            self.begin(name)

    def sync_search(self, centre, half):
        """Best 1200 Hz pulse near 'centre' (global sample), +- half samples."""
        L = self.L
        sl = int(round(L.sync_ms * self.FS / 1000.0))
        lo = int(centre - half) - self.buf0
        hi = int(centre + half) - self.buf0 + sl
        if lo < 0 or hi > self.buf_n:
            return None, 0.0
        x = (self.buf[lo:hi] < 1350.0 + self.offset).astype(np.float64)
        cs = np.concatenate(([0.0], np.cumsum(x)))
        s = cs[sl:] - cs[:-sl]
        j = int(np.argmax(s))
        # centre of the plateau (several equally good positions)
        jj = np.nonzero(s >= s[j] - 0.5)[0]
        jj = jj[(jj >= j - sl // 2) & (jj <= j + sl // 2)]
        j = int(round(np.mean(jj)))
        return self.buf0 + lo + j, s[j] / float(sl)

    def refit(self):
        if len(self.syncs) < 4:
            return
        k = np.array([s[0] for s in self.syncs], dtype=np.float64)
        p = np.array([s[1] for s in self.syncs], dtype=np.float64)
        use = np.ones(len(k), dtype=bool)
        for _ in range(3):
            if use.sum() < 4:
                return
            b, a = np.polyfit(k[use], p[use], 1)
            res = np.abs(p - (a + b * k))
            use = res < 0.0015 * self.FS
        if abs(b / self.fs_line - 1.0) < 0.01:
            self.a, self.b = a, b

    def decode_ready(self):
        L = self.L
        if self.manual and not self.locked:
            # no VIS: find the first sync anywhere in the first line period
            if self.buf_n < self.fs_line * 1.2 + 200:
                return
            pos, q = self.sync_search(self.buf0 + self.fs_line * 0.6, self.fs_line * 0.6)
            if pos is None or q < 0.6:
                self.buf_n = 0                             # keep looking from here
                self.buf0 = self.n
                return
            self.a = pos
            self.locked = True
        while self.line < L.lines:
            k = self.line
            need = self.a + self.b * (k + 1) - L.sync_at * self.FS / 1000.0 + 0.01 * self.FS
            if need - self.buf0 > self.buf_n:
                return
            pos, q = self.sync_search(self.a + self.b * k, 0.004 * self.FS)
            if pos is not None and q > 0.55:
                self.syncs.append((k, pos))
                self.misses = 0
                if len(self.syncs) % 4 == 0:
                    self.refit()
                # sync tone frequency: fine offset tracking
                s0 = int(pos - self.buf0)
                sv = self.buf[s0 + 2:s0 + int(L.sync_ms * self.FS / 1000.0) - 2]
                if len(sv) > 4:
                    self.offset += 0.1 * (float(np.median(sv)) - 1200.0 - self.offset)
            else:
                self.misses += 1
            self.decode_line(k)
            self.line += 1
            if self.line % 32 == 0:
                self.redraw()
            self.version += 1
            if self.misses > 30 and self.line > 20:     # the signal has gone
                self.finish(self.line > 30)
                return
        self.finish(True)

    def decode_line(self, k):
        L = self.L
        r = self.b / self.fs_line                          # clock ratio
        ls = self.a + self.b * k - L.sync_at * self.FS / 1000.0 * r - self.buf0
        cs = None
        lo = int(max(0, ls - 2))
        hi = int(min(self.buf_n, ls + self.fs_line * r + 4))
        seg = self.buf[lo:hi] - self.offset
        if len(seg) < 4:
            return
        cs = np.concatenate(([0.0], np.cumsum(seg)))
        xi = np.arange(len(cs), dtype=np.float64)

        def avg(t0, dur, n):
            e = ls - lo + (t0 + dur * np.arange(n + 1) / float(n)) * self.FS / 1000.0 * r
            e = np.clip(e, 0, len(seg))
            c = np.interp(e, xi, cs)
            wdt = np.maximum(np.diff(e), 1e-6)
            return np.diff(c) / wdt

        for name, t0, dur in L.chans:
            f = avg(t0, dur, L.w)
            self.planes[name][k] = np.clip((f - SSTV_BLACK) / (SSTV_WHITE - SSTV_BLACK) * 255.0, 0, 255)
        if L.sep_at is not None:
            self.sepv[k] = float(avg(L.sep_at[0] + 1.0, L.sep_at[1] - 2.0, 1)[0])
        self.render(k)

    def render(self, k):
        L, P = self.L, self.planes
        if L.kind == "rgb":
            self.img[k] = np.stack([P["R"][k], P["G"][k], P["B"][k]], axis=-1).astype(np.uint8)
        elif L.kind == "yuv":
            self.img[k] = yuv_to_rgb(P["Y"][k], P["U"][k], P["V"][k])
        elif L.kind == "pd":
            self.img[2 * k] = yuv_to_rgb(P["Y0"][k], P["U"][k], P["V"][k])
            self.img[2 * k + 1] = yuv_to_rgb(P["Y1"][k], P["U"][k], P["V"][k])
        else:                                              # Robot 36: R-Y and B-Y on alternate lines
            for j in (k - 1, k):
                if j < 0:
                    continue
                cands = [q for q in (j ^ 1, j - 1, j + 1) if 0 <= q <= k and q != j]
                pair = cands[0] if cands else j
                cj, cp = P["C"][j], P["C"][pair]
                v, u = (cj, cp) if self.sepv[j] < 1900.0 else (cp, cj)
                self.img[j] = yuv_to_rgb(P["Y"][j], u, v)

    def redraw(self):
        """Decode every line again with the latest timing fit (straightens the slant)."""
        self.refit()
        n = self.line
        for k in range(n):
            self.decode_line(k)
        if self.L.kind == "r36":
            for k in range(n):
                self.render(k)

    def finish(self, ok):
        if self.state != "rx":
            return
        self.redraw()
        self.state = "idle"
        self.version += 1
        self.events.put(("done", self.mode, self.img.copy(), ok and self.line >= self.L.lines * 0.5))
        self.buf = np.zeros(0)
        self.buf_n = 0

    # ---------------------------------------------------------------- tuning display
    def spectrum(self):
        """dB spectrum of the last 2048 baseband samples: (frequencies Hz, dB)."""
        z = self.ring
        s = np.fft.fftshift(np.fft.fft(z * np.hanning(len(z))))
        f = self.FC + np.fft.fftshift(np.fft.fftfreq(len(z), 1.0 / self.FS))
        return f, 20 * np.log10(np.abs(s) + 1e-9)

    def status(self):
        if self.state == "rx":
            sl = 0.0 if self.b == 0 else (self.b / self.fs_line - 1.0) * 1e6
            return "Receiving %s  line %d / %d   clock %+.0f ppm" % (self.mode, self.line, self.L.lines, sl)
        return "Waiting for VIS" + ("" if not self.last_vis else "   (last: %s)" % self.last_vis) \
            if self.auto else "Idle"


# ============================================================== NBTV (narrow band TV)
# After Con Wassilieff ZL2AFP's analog OFDM NBTV: one audio carrier per picture line (lowest carrier =
# bottom line), a pilot carrier in the centre for exact tuning, picture sent as vertical stripes,
# colour as three frame-sequential fields (R, G, B) and a vertical dotted line marking the frame start.
# Here every stripe is one OFDM symbol (with a short guard interval against multipath): each carrier's
# brightness is the phase step from the last stripe, measured against the pilot, so mistuning and
# sound card clock differences cancel out.  "Baird 30-line" uses the same carriers for the 30 vertical
# lines of John Logie Baird's 1930s television (3:7 tall picture, lines scanned bottom to top).
NBTV_FS = 12000.0                 # receiver rate (complex)
NBTV_CENTRE = 1500.0              # pilot carrier, Hz
NBTV_BETA = 0.9 * math.pi         # phase step for black .. white (+-81 degrees)
# name: (carriers = picture lines, stripes per field, FFT size at 12 kHz, guard samples, colour, Baird)
NBTV_MODES = collections.OrderedDict([
    ("48x48 B&W", (48, 48, 280, 35, False, False)),
    ("48x48 Colour", (48, 48, 280, 35, True, False)),
    ("96x72 B&W", (72, 96, 440, 36, False, False)),
    ("96x72 Colour", (72, 96, 440, 36, True, False)),
    ("Baird 30-line", (30, 70, 184, 24, False, True)),
])


class NbtvLayout:
    def __init__(self, name):
        self.name = name
        self.car, self.cols, self.N, self.cp, self.colour, self.baird = NBTV_MODES[name]
        self.L = self.N + self.cp
        self.df = NBTV_FS / self.N                        # carrier spacing
        self.S = self.car + 3                             # + pilot and an empty slot each side
        self.sp = self.S // 2
        self.data = np.array([s for s in range(self.S) if abs(s - self.sp) > 1])
        self.fields = 3 if self.colour else 1
        self.stripes = 1 + self.cols * self.fields        # marker + fields
        self.t_sym = self.L / NBTV_FS
        self.frame_s = self.stripes * self.t_sym
        self.lo = NBTV_CENTRE - self.sp * self.df
        self.hi = NBTV_CENTRE + (self.S - 1 - self.sp) * self.df
        # picture size (width, height)
        self.w, self.h = (self.car, self.cols) if self.baird else (self.cols, self.car)

    def stripe_values(self, img, field, j):
        """Brightness 0..1 of every carrier for stripe j of a field (img already w x h)."""
        if self.colour:
            ch = img[..., field].astype(np.float64)
        else:
            f = img.astype(np.float64)
            ch = 0.299 * f[..., 0] + 0.587 * f[..., 1] + 0.114 * f[..., 2]
        if self.baird:
            return ch[self.h - 1 - j, :] / 255.0          # line j from the bottom, carriers = columns
        return ch[::-1, j] / 255.0                        # carrier 0 = bottom line

    def marker(self):
        v = np.zeros(self.car)
        v[0::2] = 1.0                                     # dotted line: white / black alternately
        return v


class NbtvTx:
    """Endless NBTV transmission: frames of the latest picture until stopped."""
    UP = 4                                                # 12 kHz design, 48 kHz out

    def __init__(self):
        self.lock = threading.Lock()
        self.tx_active = False
        self.L = None
        self.img = None
        self.need_frame = False
        self.frames = 0

    def start(self, name, img):
        with self.lock:
            self.L = NbtvLayout(name)
            self.img = fit_image(img, self.L.w, self.L.h)
            self.next_img = None
            rng = self.rng = np.random.RandomState(5)
            self.theta = rng.uniform(0, 2 * math.pi, self.L.S)   # random start phases: lower peaks
            self.amp = np.zeros(self.L.S)
            self.amp[self.L.data] = 1.0
            self.amp[self.L.sp] = 2.0
            self.scale = 0.15 / math.sqrt(float(np.sum(self.amp ** 2)) / 2.0)
            self.n = 0
            self.queue = []                               # stripe values to send
            self.pend = np.zeros(0)
            self.header = 40                              # ~1 s of plain carriers to lock on to
            self.frames = 0
            self.tx_active = True

    def set_image(self, img):
        with self.lock:
            if self.L is not None:
                self.next_img = fit_image(img, self.L.w, self.L.h)
                self.need_frame = False

    def _frame(self):
        L = self.L
        if self.next_img is not None:
            self.img, self.next_img = self.next_img, None
        self.queue.append(L.marker())
        for f in range(L.fields):
            for j in range(L.cols):
                self.queue.append(L.stripe_values(self.img, f, j))
        self.frames += 1
        self.need_frame = True                            # ask for a fresh picture for the next one

    def _symbol(self, v):
        L, U = self.L, self.UP
        self.theta[L.data] += NBTV_BETA * (np.clip(v, 0, 1) - 0.5)
        M = L.N * U
        X = np.zeros(M, dtype=complex)
        idx = (np.arange(L.S) - L.sp) % M
        X[idx] = self.amp * np.exp(1j * self.theta)
        u = np.fft.ifft(X) * M
        s = np.concatenate((u[-L.cp * U:], u))
        n = self.n + np.arange(len(s))
        self.n += len(s)
        out = (s * np.exp(2j * math.pi * NBTV_CENTRE * n / (NBTV_FS * U))).real * self.scale
        return np.clip(out, -0.95, 0.95)

    def tx_audio(self, n):
        with self.lock:
            if not self.tx_active or self.L is None:
                return np.zeros(n)
            while len(self.pend) < n:
                if self.header > 0:
                    self.header -= 1                      # random stripes: the receiver locks to these
                    v = self.rng.uniform(0.0, 1.0, self.L.car)
                else:
                    if not self.queue:
                        self._frame()
                    v = self.queue.pop(0)
                self.pend = np.concatenate((self.pend, self._symbol(v)))
            out, self.pend = self.pend[:n], self.pend[n:]
            return out

    def tx_done(self):
        return False                                      # runs until Stop

    def abort(self):
        with self.lock:
            self.tx_active = False
            self.L = None


class NbtvRx:
    """NBTV receiver: guard-interval timing, pilot AFC (coarse search + fine phase), stripes to picture."""

    def __init__(self, name="96x72 Colour"):
        self.lock = threading.Lock()
        # keep only positive audio frequencies (50 - 3200 Hz) before mixing down, so the mirror image
        # of the real audio cannot leak into the carriers.  The carriers sit in the flat, linear-phase
        # part of this filter: to them it is a pure delay, so stripes do not smear into each other.
        self.lp = FIR(bp_taps(50.0, 3200.0, DIGI_AUDIO, 511), 2048)
        self.events = queue.Queue()
        self.set_mode(name)

    def set_mode(self, name):
        with getattr(self, "lock", threading.Lock()):
            self.mode = name
            L = self.L = NbtvLayout(name)
            self.ph = 0.0
            self.afc = 0.0                                # Hz: received pilot - 1500
            self.buf = np.zeros(0, dtype=complex)
            self.base = 0                                 # absolute index of buf[0]
            self.n_in = 0
            self.p = None                                 # next symbol start (absolute, float)
            self.metric = np.zeros(L.L)
            self.msyms = 0
            self.prev = None
            self.ring = np.zeros(4096, dtype=complex)
            self.coarse_n = 0
            self.planes = np.zeros((L.fields, L.h, L.w))
            self.img = np.zeros((L.h, L.w, 3), dtype=np.uint8)
            self.avg = None
            self.count = 0                                # stripe in frame (0 = marker)
            self.synced = False
            self.frames = 0
            self.version = 0
            self.lock_q = 0.0
            self.pilot_db = -99.0

    # ------------------------------------------------------------ input
    def rx(self, audio):
        L = self.L
        w = -2 * math.pi * (NBTV_CENTRE + self.afc) / DIGI_AUDIO
        a = self.lp.process(audio.astype(complex))
        z = a * np.exp(1j * (self.ph + w * np.arange(len(a))))
        self.ph = (self.ph + w * len(a)) % (2 * math.pi)
        y = z[::4]
        with self.lock:
            self.ring = np.concatenate((self.ring, y))[-4096:]
            self.buf = np.concatenate((self.buf, y))
            self.n_in += len(y)
            self.coarse_n += len(y)
            if self.coarse_n >= 1.5 * NBTV_FS:
                self.coarse_n = 0
                self.coarse()
            self.symbols()
            keep = 3 * L.L
            if self.p is not None:
                cut = int(self.p) - self.base - keep
            else:
                cut = len(self.buf) - 4 * L.L
            if cut > 0:
                self.buf = self.buf[cut:]
                self.base += cut

    def coarse(self):
        """Find the pilot (strong tone with empty slots each side) within +-2 carrier spacings."""
        L = self.L
        x = self.ring
        S = np.abs(np.fft.fft(x * np.hanning(len(x)))) ** 2
        f = np.fft.fftfreq(len(x), 1.0 / NBTV_FS)
        o = np.argsort(f)
        f, S = f[o], np.convolve(S[o], np.ones(3) / 3, mode="same")
        grid = np.arange(-2 * L.df, 2 * L.df, 0.5)
        P = lambda g: np.interp(g, f, S)
        m = P(grid) - 0.5 * (P(grid - L.df) + P(grid + L.df))
        k = int(np.argmax(m))
        noise = float(np.median(S)) + 1e-12
        self.pilot_db = 10 * math.log10(max(P(grid[k]), 1e-12) / noise)
        if self.pilot_db > 10 and abs(grid[k]) > L.df * 0.3:
            self.afc += float(grid[k])                    # outside the fine range: jump to it
            self.prev = None

    def symbols(self):
        L = self.L
        N, cp, LL = L.N, L.cp, L.L
        while True:
            if self.p is None:
                if len(self.buf) < 2 * LL + N:
                    return
                self.p = float(self.base)
            p0 = int(round(self.p)) - self.base
            if p0 + 2 * LL + N > len(self.buf):
                return
            # guard interval correlation over one symbol period of start positions
            seg = self.buf[p0:p0 + LL + N + cp]
            c = seg[:LL + cp] * np.conj(seg[N:N + LL + cp])
            cs = np.concatenate(([0], np.cumsum(c)))
            corr = np.abs(cs[cp:cp + LL] - cs[:LL])
            e = np.sum(np.abs(seg[:LL + cp]) ** 2) / (LL + cp) * cp + 1e-12
            idx = (np.arange(LL) + int(round(self.p))) % LL
            self.metric[idx] = 0.95 * self.metric[idx] + 0.05 * corr / e
            self.msyms += 1
            if self.msyms < 20:
                self.p += LL                              # learning the timing
                continue
            here = int(round(self.p))
            tau = int(np.argmax(self.metric))
            err = (tau - here) % LL
            if err > LL / 2:
                err -= LL
            # near the current timing: follow the local peak (sound card clock drift)
            w = max(2, cp // 2)
            loc = (here + np.arange(-w, w + 1)) % LL
            lerr = int(np.argmax(self.metric[loc])) - w
            self.lock_q = float(self.metric[loc].max())
            if self.msyms == 20:
                self.p += err                             # first lock: onto the best peak
                self.prev = None
                self.far = 0
            else:
                self.p += 0.05 * lerr
                # somewhere else clearly better for a while: the timing was wrong, jump there
                if abs(err) > w and self.metric[tau] > 1.3 * self.lock_q:
                    self.far += 1
                else:
                    self.far = 0
                if self.far > 40:
                    self.p += err
                    self.prev = None
                    self.far = 0
            s0 = int(round(self.p)) - self.base + cp - cp // 4
            if s0 + N > len(self.buf) or s0 < 0:
                return
            Z = np.fft.fft(self.buf[s0:s0 + N])
            Zs = Z[(np.arange(L.S) - L.sp) % N]
            self.p += LL
            a0 = s0 + self.base
            if self.prev is not None:
                shift = a0 - (self.prev_at + LL)          # window moved: turn the reference with it
                if shift:
                    self.prev = self.prev * np.exp(2j * math.pi * (np.arange(L.S) - L.sp) * shift / N)
            self.prev_at = a0
            if self.prev is not None:
                d = np.angle(Zs * np.conj(self.prev))
                dp = d[L.sp]
                if abs(Zs[L.sp]) > 1e-9:
                    self.afc += 0.08 * dp / (2 * math.pi * L.t_sym)
                data = np.angle(np.exp(1j * (d[L.data] - dp)))
                self.stripe(np.clip(data / NBTV_BETA + 0.5, 0.0, 1.0))
            self.prev = Zs

    # ------------------------------------------------------------ picture
    def stripe(self, v):
        L = self.L
        alt = np.where(np.arange(L.car) % 2 == 0, 1.0, -1.0)
        mk = float(np.mean((v - 0.5) * 2 * alt))
        if mk > 0.75 and (not self.synced or self.count == 0 or self.count > L.cols * L.fields * 0.5):
            if self.synced and self.count > 1:
                self.complete()
            self.count = 1
            self.synced = True
            return
        if self.count == 0:                               # flywheel: the marker should have been here
            self.count = 1
            return
        k = self.count - 1
        f, j = k // L.cols, k % L.cols
        if f < L.fields:
            if L.baird:
                self.planes[f, L.h - 1 - j, :] = v
            else:
                self.planes[f, :, j] = v[::-1]
        self.count += 1
        if self.count > L.cols * L.fields:
            self.complete()
            self.count = 0
        self.render()

    def render(self):
        L = self.L
        if L.colour:
            a = np.transpose(self.planes, (1, 2, 0))
        else:
            a = np.repeat(self.planes[0][..., None], 3, axis=2)
        self.img = (np.clip(a, 0, 1) * 255).astype(np.uint8)
        self.version += 1

    def complete(self):
        self.render()
        self.frames += 1
        f = self.img.astype(np.float64)
        self.avg = f if self.avg is None or self.avg.shape != f.shape else 0.6 * self.avg + 0.4 * f
        self.events.put(("frame", self.img.copy()))

    def averaged(self):
        return None if self.avg is None else self.avg.astype(np.uint8)

    def spectrum(self):
        z = self.ring[-2048:]
        s = np.fft.fftshift(np.fft.fft(z * np.hanning(len(z))))
        f = NBTV_CENTRE + self.afc + np.fft.fftshift(np.fft.fftfreq(len(z), 1.0 / NBTV_FS))
        return f, 20 * np.log10(np.abs(s) + 1e-9)

    def status(self):
        L = self.L
        if self.lock_q < 0.35 or self.pilot_db < 6:
            return "%s: no signal" % self.mode
        where = "frame %d" % self.frames if self.synced else "waiting for frame marker"
        return "%s   %s   stripe %d/%d" % (self.mode, where, max(0, self.count - 1), L.cols * L.fields)


# ============================================================== broadcast schedule (EiBi)
# Short-wave broadcast schedules by Eike Bierwirth, http://www.eibispace.de  (free to copy)
# CSV: kHz;Time(UTC);Days;ITU;Station;Lng;Target;Remarks;P;Start;Stop
EIBI_URL = "http://www.eibispace.de/dx/sked-{season}.csv"
CACHE_DIR = os.path.join(os.path.expanduser("~"), ".cache", "exsdr")
# language name -> EiBi language codes (the Language box also takes codes typed in, e.g. "Hi, U")
BC_LANGUAGES = collections.OrderedDict([
    ("All languages", None), ("English", ("E",)), ("French", ("F",)), ("Spanish", ("S",)),
    ("Portuguese", ("P",)), ("German", ("G",)), ("Italian", ("I",)), ("Russian", ("R",)),
    ("Arabic", ("A",)), ("Chinese", ("M", "C")), ("Japanese", ("J",)), ("Korean", ("K",)),
    ("Hindi", ("Hi",))])
DAY_NAMES = {"Mo": 1, "Tu": 2, "We": 3, "Th": 4, "Fr": 5, "Sa": 6, "Su": 7}


def _last_sunday(year, month):
    import datetime
    d = datetime.date(year, month + 1, 1) - datetime.timedelta(days=1)
    return d - datetime.timedelta(days=(d.weekday() + 1) % 7)


def eibi_season(now=None):
    """EiBi season name: A = last Sunday of March .. last Sunday of October, B = the winter after."""
    import datetime
    d = (now or datetime.datetime.utcnow()).date()
    y = d.year
    if d < _last_sunday(y, 3):
        return "b%02d" % ((y - 1) % 100)
    if d < _last_sunday(y, 10):
        return "a%02d" % (y % 100)
    return "b%02d" % (y % 100)


def previous_season(s):
    k, y = s[0], int(s[1:])
    return "b%02d" % ((y - 1) % 100) if k == "a" else "a%02d" % y


def bc_lang_codes(name):
    """Language box value -> set of EiBi codes, or None for all languages."""
    name = (name or "").strip()
    if name in BC_LANGUAGES:
        c = BC_LANGUAGES[name]
        return None if c is None else set(c)
    codes = {c.strip() for c in re.split(r"[,;/ ]+", name) if c.strip()}
    return codes or None


def parse_days(s):
    """EiBi days field -> set of weekdays 1 = Monday .. 7 = Sunday, or None (every day / irregular)."""
    s = (s or "").strip()
    if not s:
        return None
    if s.isdigit():
        return {int(c) for c in s if c in "1234567"}
    days = set()
    for part in re.split(r"[,/]", s):
        m = re.match(r"^(Mo|Tu|We|Th|Fr|Sa|Su)(?:-(Mo|Tu|We|Th|Fr|Sa|Su))?$", part.strip())
        if not m:
            return None                                   # "irr", "alt", dates: show it
        a = DAY_NAMES[m.group(1)]
        b = DAY_NAMES[m.group(2)] if m.group(2) else a
        d = a
        while True:
            days.add(d)
            if d == b:
                break
            d = d % 7 + 1
    return days


def parse_eibi(text):
    rows = []
    for line in text.splitlines()[1:]:
        f = line.split(";")
        if len(f) < 7:
            continue
        try:
            khz = float(f[0])
            t = f[1].strip()
            start, stop = int(t[:4]), int(t[5:9])
        except ValueError:
            continue
        rows.append((khz, start, stop, f[2].strip(), f[3].strip(), f[4].strip(), f[5].strip(), f[6].strip(),
                     f[7].strip() if len(f) > 7 else ""))
    rows.sort(key=lambda r: (r[0], r[1]))
    return rows


def on_air(row, now):
    hhmm = now.hour * 100 + now.minute
    start, stop = row[1], row[2]
    if start == stop or (start == 0 and stop >= 2400):
        ok = True
    elif start < stop:
        ok = start <= hhmm < stop
    else:                                                 # runs past midnight
        ok = hhmm >= start or hhmm < stop
    days = parse_days(row[3])
    return ok and (days is None or now.isoweekday() in days)


def lang_match(row, codes):
    if codes is None:
        return True
    low = {c.lower() for c in codes}
    return any(c.strip().lower() in low for c in row[6].split(","))


class BcSchedule:
    """Downloads the EiBi schedule once (kept in ~/.cache/exsdr for 3 days) and answers band queries."""

    def __init__(self, cfg, log):
        self.cfg = cfg
        self.log = log
        self.rows = None
        self.season = ""
        self.source = ""
        self.busy = False
        self.error = ""
        self.lock = threading.Lock()

    def load(self, done=None, force=False):
        """Fetch in the background; done() is called (from that thread) when finished."""
        with self.lock:
            if self.busy:
                return
            self.busy = True

        def run():
            try:
                self._load(force)
            finally:
                self.busy = False
                if done:
                    done()
        threading.Thread(target=run, daemon=True).start()

    def _load(self, force):
        import datetime
        import urllib.request
        os.makedirs(CACHE_DIR, exist_ok=True)
        url_t = self.cfg.get("bc_url") or EIBI_URL
        s0 = eibi_season()
        tried = []
        for season in (s0, previous_season(s0)):
            path = os.path.join(CACHE_DIR, "sked-%s.csv" % season)
            fresh = os.path.exists(path) and time.time() - os.path.getmtime(path) < 3 * 86400
            if not fresh or force:
                url = url_t.format(season=season)
                try:
                    req = urllib.request.Request(url, headers={"User-Agent": "ExSDR/%s" % VERSION})
                    with urllib.request.urlopen(req, timeout=20) as r:
                        data = r.read()
                    if len(data) < 1000 or b";" not in data[:200]:
                        raise ValueError("not a schedule file")
                    with open(path, "wb") as f:
                        f.write(data)
                    self.log("broadcast schedule: downloaded %s (%d kB)" % (url, len(data) // 1024))
                except Exception as e:
                    tried.append("%s: %s" % (url, e))
            if os.path.exists(path):
                with open(path, "rb") as f:
                    raw = f.read()
                try:
                    text = raw.decode("utf-8")
                except UnicodeDecodeError:
                    text = raw.decode("latin-1")
                self.rows = parse_eibi(text)
                self.season = season.upper()
                age = datetime.datetime.fromtimestamp(os.path.getmtime(path)).strftime("%Y-%m-%d")
                self.source = "EiBi %s, eibispace.de (%s)" % (self.season, age)
                self.error = "" if not tried or season != s0 else "using the saved copy (no internet?)"
                return
        self.error = "could not download the schedule (no internet?)"
        if tried:
            self.log("broadcast schedule: " + "; ".join(tried))

    def band(self, lo_khz, hi_khz, codes=None, now_only=True, now=None):
        import datetime
        now = now or datetime.datetime.utcnow()
        out = []
        for r in self.rows or []:
            if lo_khz <= r[0] <= hi_khz and lang_match(r, codes):
                live = on_air(r, now)
                if live or not now_only:
                    out.append((r, live))
        return out


class BcPanel:
    """Broadcast schedule shown in place of the mode tabs (bottom right) while on a SW broadcast band."""

    def __init__(self, app, parent):
        self.app = app
        a = app
        self.band = None
        self.shown = False
        self.last_min = None
        bg = a.CARD
        f = self.frame = tk.Frame(parent, bg=bg, padx=6, pady=4)
        top = tk.Frame(f, bg=bg)
        top.pack(side=tk.TOP, fill=tk.X)
        self.title = tk.Label(top, text="", bg=bg, fg=a.FG, font=a.F_BOLD, anchor="w")
        self.title.pack(side=tk.LEFT)
        a.btn(top, "Tabs", self.back).pack(side=tk.RIGHT)
        self.clock = tk.Label(top, text="", bg=bg, fg=a.ACC, font=a.F_BOLD)
        self.clock.pack(side=tk.RIGHT, padx=8)
        row = tk.Frame(f, bg=bg)
        row.pack(side=tk.TOP, fill=tk.X, pady=(3, 2))
        self.v_lang = tk.StringVar(value=a.cfg.get("bc_lang", "English"))
        cb = ttk.Combobox(row, textvariable=self.v_lang, values=list(BC_LANGUAGES), width=12)
        cb.pack(side=tk.LEFT)
        cb.bind("<<ComboboxSelected>>", lambda e: self.lang_changed())
        cb.bind("<Return>", lambda e: self.lang_changed())
        self.v_now = tk.IntVar(value=int(a.cfg.get("bc_now_only", True)))
        a.toggle(row, "On air now", self.v_now, cmd=self.now_changed).pack(side=tk.LEFT, padx=4)
        a.btn(row, "Refresh", lambda: self.refresh(force=True)).pack(side=tk.LEFT)
        self.count = tk.Label(row, text="", bg=bg, fg=a.MUTED, font=a.F_SMALL)
        self.count.pack(side=tk.RIGHT)
        self.status = tk.Label(f, text="", bg=bg, fg=a.MUTED, font=a.F_SMALL, anchor="w", justify=tk.LEFT,
                               wraplength=360)
        self.status.pack(side=tk.BOTTOM, fill=tk.X, pady=(3, 0))
        mid = tk.Frame(f, bg=bg)
        mid.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
        cols = (("khz", "kHz", 52), ("utc", "UTC", 74), ("station", "Station", 140), ("lng", "Lang", 40),
                ("tgt", "Target", 46))
        self.tree = ttk.Treeview(mid, columns=[c[0] for c in cols], show="headings", height=8,
                                 selectmode="browse")
        for key, text, width in cols:
            self.tree.heading(key, text=text)
            self.tree.column(key, width=width, minwidth=30, stretch=key == "station",
                             anchor="e" if key == "khz" else "w")
        sb = ttk.Scrollbar(mid, orient=tk.VERTICAL, command=self.tree.yview)
        self.tree.config(yscrollcommand=sb.set)
        sb.pack(side=tk.RIGHT, fill=tk.Y)
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.tree.tag_configure("live", foreground=a.ACC)
        self.tree.bind("<Double-1>", self.tune_row)
        self.tree.bind("<Return>", self.tune_row)
        self.items = {}

    def show(self, name, lo, hi):
        """Put the schedule where the tabs are."""
        a = self.app
        if not self.shown:
            a.mode_nb.pack_forget()
            self.frame.pack(fill=tk.BOTH, expand=True)
            self.shown = True
        if self.band != (name, lo, hi):
            self.band = (name, lo, hi)
            self.title.config(text="%s m broadcast band   %d - %d kHz" % (name, lo, hi))
            self.refresh()

    def back(self):
        """Tabs back in the bottom right block."""
        if self.shown:
            self.frame.pack_forget()
            self.app.mode_nb.pack(fill=tk.BOTH, expand=True)
            self.shown = False
            self.band = None

    def refresh(self, force=False):
        sch = self.app.bc_sched
        if sch.rows is None or force:
            self.status.config(text="Downloading the broadcast schedule ...")
            sch.load(done=lambda: self.app.root.after(0, self.fill), force=force)
        else:
            self.fill()

    def fill(self):
        import datetime
        if self.band is None:
            return
        sch = self.app.bc_sched
        for i in self.tree.get_children() or []:
            self.tree.delete(i)
        self.items = {}
        now = datetime.datetime.utcnow()
        self.last_min = now.minute
        self.clock.config(text=now.strftime("%H:%M UTC"))
        if sch.rows is None:
            self.status.config(text=sch.error or "no schedule")
            self.count.config(text="")
            return
        name, lo, hi = self.band
        lst = sch.band(lo, hi, bc_lang_codes(self.v_lang.get()), bool(self.v_now.get()), now)
        for (r, live) in lst:
            iid = self.tree.insert("", tk.END, values=(
                "%g" % r[0], "%04d-%04d" % (r[1], r[2]), r[5], r[6], r[7]), tags=("live",) if live else ())
            self.items[iid] = r
        self.count.config(text="%d %s" % (len(lst), "on air" if self.v_now.get() else "listed"))
        self.status.config(text="Double-click a station to tune it.   %s%s" % (
            sch.source, ("  - " + sch.error) if sch.error else ""))
        self.mark_tuned()

    def mark_tuned(self):
        """Select the station on the frequency you are tuned to."""
        khz = self.app.tune_hz / 1000.0
        for iid, r in self.items.items():
            if abs(r[0] - khz) < 2.5:
                try:
                    self.tree.selection_set(iid)
                    self.tree.see(iid)
                except Exception:
                    pass
                return

    def tick(self):
        """Once a minute: new clock, and the 'on air now' list follows the time."""
        import datetime
        if self.shown and datetime.datetime.utcnow().minute != self.last_min:
            self.fill()

    def lang_changed(self):
        self.app.cfg["bc_lang"] = self.v_lang.get().strip() or "English"
        self.fill()

    def now_changed(self):
        self.app.cfg["bc_now_only"] = bool(self.v_now.get())
        self.fill()

    def tune_row(self, ev=None):
        sel = self.tree.selection()
        if not sel or sel[0] not in self.items:
            return
        khz = self.items[sel[0]][0]
        a = self.app
        if a.v_mode.get() not in CARRIER_MODES:
            a.v_mode.set("AM")
            a.on_mode()
        a.set_tune(int(round(khz * 1000)), recenter=True)
        a.log("tuned to %s on %g kHz" % (self.items[sel[0]][5], khz))


# ============================================================== help text
HELP = [
    ("Getting started", """\
ExSDR is a receiver and transmitter for a sound-card I/Q radio: your homemade ExSDR board, a HackRF One, or no radio at all.

First time:
  1. Press Settings.
  2. Station tab: replace the ****** with your call sign and location, and add your name and grid locator. They are used in the digital mode macros and on SSTV pictures.
     Language tab: the language of the broadcast stations you want listed (English to start with).
  3. Radio tab: choose the hardware - your ExSDR board, HackRF, RTL-SDR, SDRplay, Airspy HF+, ADALM-Pluto, another SoapySDR radio, or None - and, for ExSDR, the serial port (usually /dev/ttyUSB0). The SDR devices tab has the gains and options for each SDR (see the Hardware topic).
  4. Sound devices tab: choose the I/Q input and output (the SDR sound card) and the headset (audio output and microphone). Press Detect sound cards to list them, and Test to try each one.
  5. Press Save + close, then Start.

To try the program without any radio, set Hardware to None and the I/Q input to 'demo': it then makes its own test signals.

The window
  Top row:     Control, Mode, Audio, Frequency, Meters
  Second row:  Bands, Receive, Transmit
  Right:       Digital modes, Digital Voice, SSTV and NBTV tabs
  Below:       spectrum and waterfall of the whole I/Q band
  Bottom:      status line, Help and Show log

Press F1 at any time for this help."""),

    ("Tuning", """\
There are two frequencies:
  LO     where the hardware is tuned (the centre of the spectrum display)
  TUNE   the frequency you are listening to, inside the band the sound card can see

Ways to tune:
  - Mouse wheel over a digit of TUNE: steps that digit up or down.
  - Click the top half of a digit to go up, the bottom half to go down.
  - Click or drag in the spectrum or waterfall: tunes to that spot.
  - Mouse wheel over the spectrum or waterfall: steps by the Step size.
  - Type a frequency in kHz in 'Tune kHz' and press Enter (the LO follows).
  - LO = Tune moves the hardware so the signal sits near the centre again.
  - Band buttons jump to the centre of each ham band (160 - 6 m) or broadcast band (MW - 11 m).
    The ham band plan (Region 1, 2 or 3) is set under Settings > Modes / TX.

Right-click the frequency display to change its colour.

With the ExSDR board, frequency commands are spaced out (Settings > Radio, gaps) so the PIC never misses one. Fast tuning inside the visible band needs no command at all."""),

    ("Broadcast schedule", """\
Pressing a short-wave broadcast band button (120 m - 11 m) shows the stations on that band in the bottom right block, in place of the Digital modes / SSTV tabs, with the time in UTC.
The tabs come back when you go to a ham band, MW, or tune outside the broadcast bands, or press Tabs.
Tuning into another broadcast band switches the list to it, and the station you are tuned to is highlighted.

  Language     shows only stations in this language (Settings > Language sets the default, English).
               'All languages' lists everything; EiBi language codes can be typed too, e.g. E, F.
  On air now   only broadcasts scheduled for this time and day (UTC); turn it off to see the whole day.
               Stations on air now are shown in the accent colour.
  Refresh      downloads the schedule again.
  Double-click a station to tune to it (in AM).

The schedule is the free EiBi list (eibispace.de) for the current season. It is downloaded the first time it is needed and kept for 3 days in ~/.cache/exsdr, so it still works without internet.
Schedules change: a station listed may be off the air, and propagation decides what you can hear."""),

    ("Modes and filters", """\
USB / LSB   single sideband voice and digital modes
AM          envelope detector
ECSS        AM received as one sideband locked to the carrier (less fading distortion).
            Choose the sideband with the ECSS L / DSB / U buttons.
FM          narrow band FM
            FM rpt (right of the FM button): Simplex, - or + repeater shift on 10 m (100 kHz) and 6 m
            (1 MHz). You listen on the dial frequency and transmit shifted; the line below shows the TX
            frequency. The radio returns to the receive frequency when you stop transmitting.
            ExSDR will not transmit if the shifted signal would fall outside the band (band plan of
            your region, Settings > Modes / TX): the line turns red and the log says why.
            Usual shifts: 10 m repeaters 29.620 - 29.680 MHz, input 100 kHz lower (-);
            6 m repeaters mostly 1 MHz lower (-), some areas use +.
CW          Morse, heard at the CW pitch (Settings > Modes / TX)
C-QuAM      AM stereo (Motorola C-QuAM)
Kahn        AM stereo with LSB = left, USB = right (Kahn ISB)

Bandwidth slider: up to 6 kHz on SSB, 12 kHz on AM / ECSS. The mouse wheel adjusts it too.
Low cut: removes audio below 0 - 1000 Hz.
Roll-off Soft / Hard: gentle or sharp filter edges.
Emph Off / 50 / 75 us: de-emphasis on receive and the matching pre-emphasis on transmit.
Stereo width: 0 % = mono, 100 % = full stereo (C-QuAM and Kahn).

The transmit bandwidth follows the receive filter unless you turn that off in Settings > Modes / TX."""),

    ("Receive tools", """\
AGC          Off, Fast, Med, Slow
NB           noise blanker for clicks and pulses (NB threshold sets how hard it works)
NR           noise reduction (NR amount)
Notch        manual notch at 'Notch Hz'
Auto notch   finds the strongest steady tone in the passband and removes it; the tone frequency is shown beside it
Auto IQ      corrects the sound card's I/Q balance (removes the mirror image)
Volume, RF gain / AGC limit, Squelch: as the names say.

The Audio card shows a waterfall of the demodulated audio. Ref dB and Range dB set its brightness and contrast."""),

    ("Transmit", """\
TX           switches to transmit and stays there until pressed again
Hold TX      transmits only while the button is held down
Tune carrier sends a steady carrier for tuning an antenna tuner (use low drive!)
CW key       keys CW; the space bar does the same in CW mode

Source: Mic, 1 kHz tone or Two-tone (for testing the transmitter).
Mic gain dB, Drive (output level), AM / FM mod % (100 % is the most allowed).
Compressor and Compression dB make speech louder; Limiter stops peaks clipping.
The readout under the meters shows compression, limiting and modulation while transmitting.

After transmitting, the receiver stays muted for a moment (Settings > Radio) so there is no burst of noise.

With the ExSDR board, TX / RX and the frequency are sent to the PIC over the serial port."""),

    ("Meters", """\
S-meter (Frequency card): signal strength. Settings > Look sets the level that reads S9.

Meters card:
  Carrier PLL   the phase meter for ECSS and AM stereo: the needle shows the phase error between the PLL and the station's carrier, with the carrier offset in Hz. A still, centred needle means it is locked.
  Level         MIC = microphone level, then the receive audio (split into L and R in stereo modes), or the transmit level while transmitting. 0 - 100 %.
  Readout       compression, limiting and modulation while transmitting."""),

    ("Digital modes", """\
PSK31, DominoEX and CW (Morse) decoders and transmitters, on SSB (USB normally).

  ON / OFF     turns the decoders on; when off the tab is greyed out and uses no processor time
  Mode         PSK31, DominoEX (speed 4 - 22) or CW (speed in words per minute)
  AFC          follows a signal that drifts
  Find         looks for the nearest signal
  Centre RF    retunes the radio so the signal sits at 1000 Hz audio
  Alignment    small waterfall around the decoder; click a trace to tune onto it.
               The red box shows the width of the mode, Q the signal quality.

RX box: decoded text. What you send is shown there in red.
TX box: type the message, then Send (or Ctrl+Enter). The radio is switched to USB if it is not on SSB, transmits, and goes back to receive by itself. Stop aborts.
Macro buttons CQ, Info and 73 put ready-made text with your call sign, name and location in the TX box.

Tips: set the SSB bandwidth to at least 2.4 kHz. If the first word is lost, the decoder was still pulling in: click the signal first, or use Find."""),

    ("SSTV", """\
Slow scan TV pictures: Martin M1 / M2, Scottie S1 / S2 / DX, Robot 36 / 72, PD50 / 90 / 120 / 160 / 180 / 240 / 290 and Wraase SC2-180.

Receive
  ON / OFF     turns the SSTV decoder on
  Auto (VIS)   starts a picture by itself when the mode code at the start of a picture is heard
  Start        starts the chosen mode now (when you tuned in part way through a picture)
  Stop         ends the picture
  The picture is straightened as it comes in (sound card clock differences), and mistuning up to about 150 Hz is corrected.

Tuning meter
  Waterfall and spectrum from 1000 to 2500 Hz. S = sync 1200 Hz, B = black 1500 Hz, V = start tone 1900 Hz, W = white 2300 Hz.
  The offset readout is green within 20 Hz. Correct retunes the radio by the measured offset.

Transmit
  Choose the mode, Load image... (cropped to fill the mode's picture size), then Send. Stop TX aborts.
  Text puts your call sign (or anything you type) across the top of the picture.
  Until a picture is loaded, a colour bar test card is sent.

Saving
  Save image... saves the picture in view (PNG, JPEG, BMP or PPM).
  Auto save keeps every complete picture in ~/ExSDR/SSTV, named by date, time and mode.

SSTV uses LSB on 80 / 40 m and USB on 20 m and up (14.230 MHz is the usual calling frequency). Keep the bandwidth at 2.4 kHz or more and Low cut under 1 kHz."""),

    ("NBTV", """\
Narrow band TV after Con Wassilieff ZL2AFP's analog OFDM NBTV: moving pictures in about 2 kHz of SSB.
One audio carrier per picture line (lowest carrier = bottom line), a pilot carrier at 1500 Hz in the middle for tuning, the picture sent as vertical stripes, colour as red, green and blue fields one after the other, and a dotted line at the start of every frame.

Modes
  48x48 B&W      48 lines, square picture      about 1.3 s a frame
  48x48 Colour                                 about 3.8 s
  96x72 B&W      72 lines, 4:3 picture         about 3.9 s
  96x72 Colour                                 about 11.5 s
  Baird 30-line  John Logie Baird's 1930s format: 30 vertical lines, a tall 3:7 picture scanned
                 bottom to top, about 1.2 s a frame. 'Neon' shows it in the orange glow of a Baird televisor.

Receive
  Choose the mode the other station is sending (there is no mode code). The picture builds up stripe by stripe and keeps running like television. Average blends frames together to clean up a noisy picture.
  Save frame... saves the picture in view; Record saves every received frame to ~/ExSDR/NBTV/<date_time_mode>/ to make into a movie.

Tuning meter
  Waterfall and spectrum 300 - 2800 Hz. The green box is where the carriers should be, the yellow dashed line the 1500 Hz pilot position, the red line where the pilot is received.
  The receiver finds the pilot by itself within about +-2 carrier spacings (+-50 to +-130 Hz) and then holds it to a fraction of a hertz, so the tuning does not have to be exact. Correct retunes the radio so the pilot sits on 1500 Hz.

Transmit
  Source: Test card, Picture file (Load...) or Screen. For Screen, press Area... and move the see-through window over what you want to send (or choose Whole screen); a new screen picture is taken for every frame, so you can send live video of a program, a web camera window, a clock...
  Send transmits continuously (in USB) until Stop TX. Keep the power down: many carriers at once need a clean, linear transmitter (about 20 % of PEP average).
  Screen capture uses python3-pil on X11; on Wayland install grim (wlroots) or gnome-screenshot.

Note: Con's own modulation details are not fully published, so these modes are built from his published numbers and work between ExSDR stations; they are not guaranteed to decode his Windows programs."""),

    ("Hardware", """\
Choose the radio in Settings > Radio > Hardware; its options are in Settings > SDR devices.
Every SDR is brought down to the same 192 kHz I/Q slice, so all of ExSDR works the same with each of them. Tuning inside the slice is instant; the radio itself is only retuned when you go further.

ExSDR          your homemade HF radio: I/Q through the sound card, control over the serial port.
HackRF One     1 MHz - 6 GHz, receive and transmit (half duplex).  sudo apt install hackrf
               RF amp button = the HackRF's amplifier.
RTL-SDR        RTL-SDR Blog V3 / V4, NooElec and other RTL2832U dongles. Receive only.  sudo apt install rtl-sdr
               HF reception: 'V4 / none' (the V4 receives HF by itself), 'V3 direct sampling'
               (needs the RTL-SDR Blog drivers), or 'Upconverter +125 MHz' for a Ham-it-up style converter.
               Auto gain button = the tuner's automatic gain; otherwise the gain set in SDR devices.
SDRplay        RSP1A / RSP1B / RSPdx / RSPduo, 1 kHz - 2 GHz. Receive only.
               Needs the SDRplay API (sdrplay.com), the SoapySDRPlay3 module and python3-soapysdr.
               Antenna port (RSPdx: Antenna A / B / C, RSP2: Hi-Z) in SDR devices.
Airspy HF+     HF+ and HF+ Discovery, 9 kHz - 31 MHz and 60 - 260 MHz. Receive only.  sudo apt install airspyhf
               LNA button = +6 dB preamp, Atten = 12 dB attenuator.
ADALM-Pluto    70 MHz - 6 GHz, receive and transmit (stock firmware 325 MHz - 3.8 GHz; no HF without a
               transverter).  Needs python3-soapysdr and the SoapySDR PlutoSDR module.
               Network Pluto: device arguments uri=ip:192.168.2.1
SoapySDR other LimeSDR, bladeRF, USRP, Airspy R2 ... anything SoapySDR can open: enter its device
               arguments (e.g. driver=lime). 'SoapySDRUtil --find' lists what is connected.
None           no radio control; everything else works (use the 'demo' I/Q input to try it out).

For the SoapySDR radios the AGC button turns on the radio's own automatic gain, and Atten lowers the RX gain by 20 dB.
Receive-only radios: the TX button and the Send buttons of the mode tabs tell you there is no transmitter."""),

    ("Settings", """\
Station        operator name, call sign, location (QTH) and grid locator (****** = not set yet)
Language       language filter for the broadcast schedule, whether it opens with the SW band buttons, and where it is downloaded from
Radio          hardware, serial port and timing for the ExSDR board, receiver mute after TX
SDR devices    gains and options for HackRF, RTL-SDR, Airspy HF+, and SDRplay / ADALM-Pluto / other SoapySDR radios
Sound devices  I/Q input / output and headset; Test plays or records a short sample, Release card frees a card held by PipeWire
Modes / TX     band plan, TX bandwidth, FM deviation, CW pitch
Look           colours (Auto follows the desktop), font size, frequency display colour, S9 level
I/Q correction swap I/Q, invert Q, gain and phase balance, TX carrier null

Save + close keeps the settings in ~/.exsdr.json (sound and radio changes restart the receiver)."""),

    ("Troubleshooting", """\
Device or resource busy
  Another program has the sound card. Use 'default' for the headset and pick the card in the PulseAudio mixer, or press Release card in Settings > Sound devices.

No transmit output
  Check the I/Q output device in Settings and press Start; TX is not available while stopped.

The ExSDR board stops answering
  Use the fixed PIC firmware (HF_SDR.BAS 1.1) and keep the gaps in Settings > Radio. Show log lists every command and reply.

Mirror images in the spectrum
  Turn on Auto IQ, or set the balance under I/Q correction.

Tests from the command line
  python3 exsdr.py --install-desktop           adds ExSDR with its icon to the application menu
  python3 exsdr.py --selftest                  checks the DSP, digital modes and SSTV
  python3 exsdr.py --serialtest /dev/ttyUSB0   checks the link to the ExSDR board
  python3 exsdr.py --demo                      runs without any radio"""),

    ("About", """\
{app} {version}
by {author}

Sound-card SDR transceiver software for the ExSDR homemade HF radio (PIC18F252), the HackRF One, or no radio.

{credit}

Needs python3, python3-numpy, python3-tk and alsa-utils (python3-pil optional, for more picture formats and SSTV text)."""),
]


# ============================================================== hardware link
class SerialLink:
    """Serial control of the homebrew hardware (termios only, no pyserial).

    The hardware does NOT echo. It answers every command with a text message:
        F03650 -> "Frequency Set to 3650 kHz"      ?F -> "Frequency = 7100 kHz"
        TX     -> "Tx Set"                         RX -> "Rx Set"
        ?P     -> "Pre Amp = off" / "Pre Amp = on"
        ?A     -> "Attenuator = off" / "Attenuator = on"
        power-on banner: "HF SDR v1"
    Two commands must be at least cmd_gap (100 ms) apart.  Everything the hardware
    reports (also unsolicited text such as the banner) is parsed and pushed to
    `self.events`, so the GUI always shows what the hardware says, not what was asked.
    """
    FREQ_RE = re.compile(r"Frequency\D*(\d+)\s*kHz", re.I)
    PRE_RE = re.compile(r"Pre\s*-?\s*Amp\b.*?\b(on|off)\b", re.I)
    ATT_RE = re.compile(r"Attenuator\b.*?\b(on|off)\b", re.I)
    TX_RE = re.compile(r"\bTx\s+Set\b", re.I)
    RX_RE = re.compile(r"\bRx\s+Set\b", re.I)
    HELLO_RE = re.compile(r"HF\s*SDR\b.*", re.I)

    def __init__(self, cfg, log):
        self.cfg = cfg
        self.log = log
        self.fd = None
        self.q = queue.Queue()
        self.events = queue.Queue()
        self.stop_evt = threading.Event()
        self.thread = None
        self.lock = threading.Lock()
        self.pend_freq = None
        self.t_last = 0.0
        self.last_kind = ""
        self.hw ={"freq": None, "pre": None, "att": None, "tx": None, "version": None}
        self.connected = False

    # ------------------------------------------------------------ open / close
    def open(self):
        if termios is None:
            raise RuntimeError("serial control needs Linux")
        port = self.cfg["serial_port"]
        try:
            fd = os.open(port, os.O_RDWR | os.O_NOCTTY | os.O_NONBLOCK)
        except OSError as e:
            hint = ""
            if e.errno == 13:
                hint = "  (permission: sudo usermod -aG dialout $USER, then log out and in)"
            raise RuntimeError("cannot open %s: %s%s" % (port, e.strerror, hint))
        attrs = termios.tcgetattr(fd)
        speed = getattr(termios, "B%d" % int(self.cfg["baud"]), None)
        if speed is None:
            os.close(fd)
            raise RuntimeError("unsupported baud rate %s" % self.cfg["baud"])
        attrs[0] = 0
        attrs[1] = 0
        attrs[2] = termios.CS8 | termios.CREAD | termios.CLOCAL       # 8 data, no parity, 1 stop
        attrs[3] = 0
        attrs[4] = speed
        attrs[5] = speed
        attrs[6][termios.VMIN] = 0
        attrs[6][termios.VTIME] = 0
        termios.tcsetattr(fd, termios.TCSANOW, attrs)
        self.fd = fd
        if self.cfg["open_delay"]:
            time.sleep(self.cfg["open_delay"])
        self.t_last = time.time()
        self.stop_evt.clear()
        self.thread = threading.Thread(target=self._run, daemon=True)
        self.thread.start()
        self.connected = True
        self.log("serial: %s open at %s baud 8N1" % (port, self.cfg["baud"]))

    def close(self):
        self.stop_evt.set()
        if self.thread is not None:
            self.thread.join(2.0)
            self.thread = None
        if self.fd is not None:
            try:
                os.close(self.fd)
            except OSError:
                pass
        self.fd = None
        self.connected = False

    # ------------------------------------------- public (thread safe, non blocking)
    def set_freq_khz(self, khz):
        with self.lock:
            self.pend_freq = int(clamp(khz, FMIN_KHZ, FMAX_KHZ))
        self.q.put(("freq",))

    def set_flag(self, letter, on):
        key = {"P": "pre", "A": "att"}[letter]
        self.q.put(("cmd", "%s%d" % (letter, 1 if on else 0), "?" + letter, key))

    def submit_txrx(self, cmd, delay=0.0, done=None):
        self.q.put(("txrx", cmd, delay, done))

    def send_raw(self, text):
        self.q.put(("raw", text))

    def query_all(self):
        for letter, key in (("F", "freq"), ("P", "pre"), ("A", "att")):
            self.q.put(("query", "?" + letter))

    # ------------------------------------------------------------------ parsing
    def parse(self, text):
        """Turn hardware text into events, update self.hw, return [(kind, value)]."""
        evs = []
        for line in re.split(r"[\r\n]+", text):
            line = line.strip()
            if not line:
                continue
            m = self.FREQ_RE.search(line)
            if m:
                evs.append(("freq", int(m.group(1))))
                continue
            m = self.PRE_RE.search(line)
            if m:
                evs.append(("pre", m.group(1).lower() == "on"))
                continue
            m = self.ATT_RE.search(line)
            if m:
                evs.append(("att", m.group(1).lower() == "on"))
                continue
            if self.TX_RE.search(line):
                evs.append(("tx", True))
                continue
            if self.RX_RE.search(line):
                evs.append(("tx", False))
                continue
            m = self.HELLO_RE.search(line)
            if m:
                evs.append(("hello", m.group(0).strip()))
                continue
            evs.append(("text", line))
        for kind, val in evs:
            if kind == "hello":
                self.hw["version"] = val
            elif kind in self.hw:
                self.hw[kind] = val
            if kind == "freq":
                with self.lock:
                    latest = self.pend_freq is None      # False: a newer request is already waiting
                self.events.put(("freq", val, latest))
            else:
                self.events.put((kind, val))
        return evs

    # ------------------------------------------------------------------- worker
    def _run(self):
        try:
            self._listen(self.cfg["banner_wait"])        # power-on banner "HF SDR v1"
        except Exception as e:
            self.log("serial error: %s" % e)
        while not self.stop_evt.is_set():
            try:
                try:
                    item = self.q.get(timeout=0.1)
                except queue.Empty:
                    self._drain()                         # unsolicited text, e.g. hardware power-cycled
                    continue
                self._handle(item)
            except OSError as e:
                self.log("serial link lost: %s" % e)
                self.connected = False
                return
            except Exception as e:
                self.log("serial error: %s" % e)

    def _read_idle(self, first_wait):
        data = b""
        while True:
            to = self.cfg["idle_gap"] if data else first_wait
            r, _, _ = select.select([self.fd], [], [], to)
            if not r:
                break
            chunk = os.read(self.fd, 256)
            if not chunk:
                break
            data += chunk
        return data

    def _listen(self, secs):
        text = self._read_idle(secs).decode("ascii", "ignore")
        if text.strip():
            self.log("hw< " + " | ".join(l.strip() for l in re.split(r"[\r\n]+", text) if l.strip()))
            self.parse(text)

    def _drain(self):
        r, _, _ = select.select([self.fd], [], [], 0)
        if r:
            self._listen(0.0)

    def xfer(self, cmd):
        """Send one command, wait for the reply. Returns (reply_text, events)."""
        self._drain()
        is_freq = re.match(r"F\d+$", cmd) is not None
        gap = self.cfg["cmd_gap"]
        # The PIC is busy after some commands (PLL, band relays, LED update: PAUSE 200,
        # PAUSE 100, 16 x PAUSE 10).  A byte that arrives while it is busy overruns its
        # USART, and the old firmware then stops receiving altogether - the "lock up".
        if is_freq or self.last_kind == "F":
            gap = max(gap, float(self.cfg.get("freq_gap", 0.6)))
        if self.last_kind == "TXRX":
            gap = max(gap, float(self.cfg.get("txrx_gap", 0.4)))
        wait = gap - (time.time() - self.t_last)
        if wait > 0:
            time.sleep(wait)
        self.last_kind = "F" if is_freq else "TXRX" if cmd in ("TX", "RX") else ""
        try:
            termios.tcflush(self.fd, termios.TCIFLUSH)
        except Exception:
            pass
        os.write(self.fd, (cmd + self.cfg["terminator"]).encode("ascii"))
        text = self._read_idle(self.cfg["reply_timeout"]).decode("ascii", "ignore")
        self.t_last = time.time()
        shown = " | ".join(l.strip() for l in re.split(r"[\r\n]+", text) if l.strip())
        self.log("hw> %-7s < %s" % (cmd, shown or "(no reply)"))
        return text, self.parse(text)

    def _handle(self, item):
        kind = item[0]
        if kind == "freq":
            with self.lock:
                k, self.pend_freq = self.pend_freq, None
            if k is None:
                return                                    # already sent (requests were merged)
            text, evs = self.xfer("F%05d" % k)
            if not any(e[0] == "freq" for e in evs):
                self.log("warning: no 'Frequency Set' reply for F%05d" % k)
        elif kind == "cmd":
            text, evs = self.xfer(item[1])
            if not any(e[0] == item[3] for e in evs):     # reply did not say on/off: ask
                self.xfer(item[2])
        elif kind == "query":
            self.xfer(item[1])
        elif kind == "txrx":
            if item[2]:
                time.sleep(item[2])
            text, evs = self.xfer(item[1])
            ok = ("tx", item[1] == "TX") in evs
            if not ok:
                self.log("warning: no '%s Set' reply from hardware" % item[1].capitalize())
            if item[3]:
                item[3](ok)
        elif kind == "raw":
            self.xfer(item[1])


class NullRadio:
    """Hardware 'None': no radio control.  Tuning, spectrum, demodulation and TX audio all work,
    nothing is sent to a radio."""

    def __init__(self, cfg, log):
        self.cfg = cfg
        self.log = log
        self.events = queue.Queue()
        self.q = queue.Queue()
        self.connected = False
        self.hw = {"freq": None, "pre": None, "att": None, "tx": None, "version": None}

    def open(self):
        self.log("hardware: none - no radio control (receive, spectrum and TX audio still work)")

    def close(self):
        pass

    def set_freq_khz(self, khz):
        pass

    def set_flag(self, letter, on):
        pass

    def submit_txrx(self, cmd, delay=0.0, done=None):
        if done:
            done(True)

    def send_raw(self, text):
        self.log("no radio control (hardware: none)")

    def query_all(self):
        pass


class HackRF:
    """HackRF One through hackrf_transfer  (sudo apt install hackrf).

    Receive: hackrf_transfer -r -  gives 8-bit I/Q at 2.304 MHz, filtered and divided by 12
    down to 192 kHz - the same I/Q rate as the sound card, so all of ExSDR's DSP is unchanged.
    Transmit: 192 kHz I/Q from the modulator is raised to 2.304 MHz and fed to hackrf_transfer -t -.
    The HackRF is half duplex: going to TX stops the receive stream and the other way round.

    No-gap tuning: the HackRF sees 2.304 MHz, ExSDR uses a 192 kHz slice of it.  The slice is
    moved digitally (a mixer before the decimation filter), so a new LO only needs the HackRF
    itself retuned - which restarts hackrf_transfer, about 0.5 s - when it moves more than
    SHIFT_MAX away.  The HackRF's DC spike is kept SHIFT_NEW away, outside the slice."""
    NAME = "HackRF"
    CAN_TX = True
    SAMPLE_BYTES = 2                # bytes per complex sample on the tool's stdout
    RATE = 2304000
    DEC = 12
    OUT_RATE = RATE // DEC          # 192 kHz
    BLK_OUT = RxDsp.BLK * 4         # 8192 samples at 192 kHz per block
    BLK = BLK_OUT * DEC             # 98304 samples at 2.304 MHz
    SHIFT_MIN = 110                 # kHz: slice edge stays clear of the DC spike
    SHIFT_MAX = 800                 # kHz: inside the HackRF's baseband filter
    SHIFT_NEW = 450                 # kHz: where the slice goes after a hardware retune

    def __init__(self, cfg, log):
        self.cfg = cfg
        self.log = log
        self.events = queue.Queue()
        self.q = queue.Queue()
        self.connected = False
        self.active = False         # True while the engine runs (Start pressed)
        self.mode = "rx"
        self.amp = False
        self.freq_khz = None        # the LO ExSDR asked for (centre of the 192 kHz slice)
        self.hw_khz = None          # where the HackRF itself is tuned
        self.shift_hz = 0.0         # slice centre relative to the HackRF centre
        self.rx_ph = 0.0
        self.tx_ph = 0.0
        self.retunes = 0
        self.proc = None
        self.proc_mode = None
        self.gen = 0
        self.lock = threading.RLock()
        self.rxq = queue.Queue(maxsize=8)
        self.errs = 0
        self.hw = {"freq": None, "pre": False, "att": False, "tx": False, "version": None}
        self.make_filters()

    def make_filters(self):
        self.BLK = self.BLK_OUT * self.DEC
        self.dec_fir = FIR(lp_taps(88000.0, self.RATE, 511), self.BLK)
        self.int_fir = FIR(lp_taps(88000.0, self.RATE, 511) * self.DEC, self.BLK)

    # ---------------------------------------------------------------- radio interface
    def open(self):
        if not shutil.which("hackrf_transfer"):
            raise RuntimeError("hackrf_transfer not found - install it with: sudo apt install hackrf")
        try:
            r = subprocess.run(["hackrf_info"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=8)
            info = r.stdout.decode("utf8", "ignore")
        except Exception as e:
            raise RuntimeError("hackrf_info failed: %s" % e)
        if "Serial number" not in info:
            raise RuntimeError("no HackRF found - is it plugged in?  (hackrf_info: %s)"
                               % (info.strip().splitlines() or ["no output"])[-1])
        fw = re.search(r"Firmware Version:\s*(\S+)", info)
        self.hw["version"] = "HackRF One" + (" fw %s" % fw.group(1) if fw else "")
        self.connected = True
        self.log("hardware: %s" % self.hw["version"])
        self.events.put(("hello", self.hw["version"]))

    def close(self):
        self.activate(False)
        self.connected = False

    def set_freq_khz(self, khz):
        lo, hi = HW_LIMITS_KHZ[self.NAME]
        khz = int(clamp(khz, lo, hi))
        if khz == self.freq_khz:
            return
        self.freq_khz = khz
        self.hw["freq"] = khz
        self.events.put(("freq", khz, True))
        d = None if self.hw_khz is None else khz - self.hw_khz
        if d is None or not self.SHIFT_MIN <= abs(d) <= self.SHIFT_MAX:
            hw = khz - self.SHIFT_NEW                          # HackRF centre below the slice ...
            if hw < lo:
                hw = khz + self.SHIFT_NEW                      # ... or above it near 1 MHz
            self.hw_khz = int(hw)
            self.retunes += 1
        self.shift_hz = (khz - self.hw_khz) * 1000.0           # digital shift, no restart
        self._restart()

    def set_flag(self, letter, on):
        if letter == "P":                  # Pre-amp button = HackRF RF amplifier (about 11-14 dB)
            self.amp = bool(on)
            self.hw["pre"] = self.amp
            self.events.put(("pre", self.amp))
            self._restart()
        else:
            self.hw["att"] = False
            self.events.put(("att", False))
            self.log("HackRF has no attenuator - lower the LNA gain in Settings instead")

    def submit_txrx(self, cmd, delay=0.0, done=None):
        def run():
            if delay:
                time.sleep(delay)
            self.mode = "tx" if cmd == "TX" else "rx"
            self.hw["tx"] = self.mode == "tx"
            self._restart()
            self.events.put(("tx", self.mode == "tx"))
            if done:
                done(True)
        threading.Thread(target=run, daemon=True).start()

    def send_raw(self, text):
        self.log("HackRF: no raw commands - use Settings for the gains")

    def query_all(self):
        if self.freq_khz is not None:
            self.events.put(("freq", self.freq_khz, True))
        self.events.put(("pre", self.amp))
        self.events.put(("att", False))

    # ---------------------------------------------------------------- streaming
    def activate(self, on):
        self.active = on
        if on:
            self._restart()
        else:
            with self.lock:
                self._kill()

    def _kill(self):
        p, self.proc, self.proc_mode = self.proc, None, None
        self.gen += 1
        if p is not None:
            try:
                if p.stdin:
                    p.stdin.close()
            except Exception:
                pass
            try:
                p.send_signal(2)                               # SIGINT: hackrf_transfer stops cleanly
                p.wait(timeout=1.5)
            except Exception:
                try:
                    p.kill()
                    p.wait(timeout=1.0)
                except Exception:
                    pass

    def _cmd(self, mode):
        c = self.cfg
        cmd = ["hackrf_transfer", "-f", str(int(self.hw_khz) * 1000), "-s", str(self.RATE),
               "-a", "1" if self.amp else "0"]
        if str(c.get("hackrf_serial", "")).strip():
            cmd += ["-d", str(c["hackrf_serial"]).strip()]
        if mode == "rx":
            lna = int(clamp(round(float(c.get("hackrf_lna", 16)) / 8.0) * 8, 0, 40))
            vga = int(clamp(round(float(c.get("hackrf_vga", 20)) / 2.0) * 2, 0, 62))
            cmd += ["-r", "-", "-l", str(lna), "-g", str(vga)]
        else:
            cmd += ["-t", "-", "-x", str(int(clamp(float(c.get("hackrf_txvga", 0)), 0, 47)))]
        return cmd

    def _restart(self):
        with self.lock:
            if not self.active or self.freq_khz is None:
                return
            if self.proc is not None and self.proc.poll() is None and self.proc_mode == self.mode and \
                    getattr(self, "_running_cmd", None) == self._cmd(self.mode):
                return                                         # already streaming like this
            self._kill()
            cmd = self._cmd(self.mode)
            try:
                p = subprocess.Popen(cmd, stdin=subprocess.PIPE if self.mode == "tx" else subprocess.DEVNULL,
                                     stdout=subprocess.PIPE if self.mode == "rx" else subprocess.DEVNULL,
                                     stderr=subprocess.PIPE)
            except OSError as e:
                self.log("%s: cannot start %s: %s" % (self.NAME, cmd[0], e))
                return
            self.proc, self.proc_mode, self._running_cmd = p, self.mode, cmd
            self.gen += 1
            g = self.gen
            threading.Thread(target=self._stderr, args=(p,), daemon=True).start()
            if self.mode == "rx":
                threading.Thread(target=self._reader, args=(p, g), daemon=True).start()

    def _stderr(self, p):
        try:
            for line in p.stderr:
                if p is not self.proc:
                    continue                                   # stopped on purpose: ignore its goodbye
                t = line.decode("utf8", "ignore").strip()
                low = t.lower()
                # skip the once-a-second throughput lines and normal start-up chatter
                if not t or "mib" in low or "call hackrf_" in low or low.startswith(("sample", "frequency",
                                                                                     "using", "stop with")):
                    continue
                if self.errs < 10:
                    self.errs += 1
                    self.log("%s: %s" % (self.NAME, t))
        except Exception:
            pass

    def _samples(self, raw):
        x = np.frombuffer(raw, dtype=np.int8).astype(np.float64) / 128.0
        return x[0::2] + 1j * x[1::2]

    def _reader(self, p, g):
        nbytes = self.BLK * self.SAMPLE_BYTES
        while g == self.gen:
            try:
                raw = p.stdout.read(nbytes)
            except Exception:
                break
            if len(raw) < nbytes:
                if g == self.gen and self.active:
                    self.log("%s receive stream stopped - is it still connected?" % self.NAME)
                break
            iq = self._samples(raw)
            self.rx_iq(iq)

    def rx_iq(self, iq):
        """Wide I/Q at RATE -> the 192 kHz slice -> receiver queue."""
        w = -2 * np.pi * self.shift_hz / self.RATE                 # bring the slice to 0 Hz
        iq = iq * np.exp(1j * (self.rx_ph + w * np.arange(len(iq))))
        self.rx_ph = (self.rx_ph + w * len(iq)) % (2 * np.pi)
        y = self.dec_fir.process(iq)[::self.DEC]
        try:
            self.rxq.put_nowait(y)
        except queue.Full:
            pass

    def block(self, n):
        """n complex samples at 192 kHz for the receiver (zeros while transmitting or restarting)."""
        try:
            y = self.rxq.get(timeout=n / float(self.OUT_RATE) * 1.5)
            if len(y) == n:
                return y
        except queue.Empty:
            pass
        return np.zeros(n, dtype=complex)

    def write(self, data):
        """TX: interleaved int16 I/Q at 192 kHz (as made by TxDsp) -> HackRF."""
        p = self.proc
        if p is None or self.proc_mode != "tx":
            return
        a = np.frombuffer(data, dtype="<i2").astype(np.float64) / 32768.0
        iq = a[0::2] + 1j * a[1::2]
        up = np.zeros(len(iq) * self.DEC, dtype=complex)
        up[::self.DEC] = iq
        up = self.int_fir.process(up)
        w = 2 * np.pi * self.shift_hz / self.RATE                  # back up to the slice
        up = up * np.exp(1j * (self.tx_ph + w * np.arange(len(up))))
        self.tx_ph = (self.tx_ph + w * len(up)) % (2 * np.pi)
        out = np.empty(2 * len(up), dtype=np.int8)
        out[0::2] = np.clip(np.round(up.real * 127.0), -127, 127)
        out[1::2] = np.clip(np.round(up.imag * 127.0), -127, 127)
        try:
            p.stdin.write(out.tobytes())
            p.stdin.flush()
        except (OSError, ValueError):
            pass                                               # restarted to RX meanwhile


class RtlSdr(HackRF):
    """RTL-SDR dongles (RTL-SDR Blog V3 / V4, NooElec ...) through rtl_sdr  (sudo apt install rtl-sdr).
    Receive only.  8-bit unsigned I/Q at 1.92 MHz, divided by 10 to 192 kHz.  HF: the V4 has it built
    in, the V3 uses direct sampling (-D 2, RTL-SDR Blog drivers), or an upconverter in front."""
    NAME = "RTL-SDR"
    CAN_TX = False
    SAMPLE_BYTES = 2
    RATE = 1920000
    DEC = 10
    SHIFT_MIN = 110
    SHIFT_MAX = 650
    SHIFT_NEW = 400

    def open(self):
        if not shutil.which("rtl_sdr"):
            raise RuntimeError("rtl_sdr not found - install it with: sudo apt install rtl-sdr")
        info = ""
        if shutil.which("rtl_test"):
            try:
                r = subprocess.run(["rtl_test", "-t"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   timeout=6)
                info = r.stdout.decode("utf8", "ignore")
            except Exception:
                info = ""
            if info and "No supported devices" in info:
                raise RuntimeError("no RTL-SDR found - is it plugged in?")
        m = re.search(r"\d+:\s+(.+?),\s+(.+?),\s+SN:\s*(\S+)", info)
        self.hw["version"] = "RTL-SDR" + (" (%s)" % m.group(2) if m else "")
        self.connected = True
        self.log("hardware: %s - receive only" % self.hw["version"])
        self.events.put(("hello", self.hw["version"]))

    def set_flag(self, letter, on):
        if letter == "P":                   # Pre-amp button = tuner automatic gain
            self.amp = bool(on)
            self.hw["pre"] = self.amp
            self.events.put(("pre", self.amp))
            self._restart()
        else:
            self.events.put(("att", False))
            self.log("RTL-SDR has no attenuator - lower the gain in Settings > SDR devices")

    def _samples(self, raw):
        x = (np.frombuffer(raw, dtype=np.uint8).astype(np.float64) - 127.5) / 128.0
        return x[0::2] + 1j * x[1::2]

    def _cmd(self, mode):
        c = self.cfg
        hz = int(self.hw_khz) * 1000
        hf = str(c.get("rtl_hf", "V4 / none"))
        cmd = ["rtl_sdr"]
        if hf.startswith("Upconverter"):
            hz += 125000000                                    # 125 MHz upconverter (Ham-it-up etc.)
        elif hf.startswith("V3") and hz < 28800000:
            cmd += ["-D", "2"]                                 # direct sampling, Q branch
        cmd += ["-f", str(hz), "-s", str(self.RATE), "-d", str(int(c.get("rtl_index", 0)))]
        g = float(c.get("rtl_gain", 30))
        if not self.amp and g > 0:
            cmd += ["-g", "%.1f" % g]
        if int(c.get("rtl_ppm", 0)):
            cmd += ["-p", str(int(c.get("rtl_ppm", 0)))]
        return cmd + ["-"]


class AirspyHF(HackRF):
    """Airspy HF+ / HF+ Discovery through airspyhf_rx  (sudo apt install airspyhf).  Receive only.
    Float32 I/Q at 768 kHz, divided by 4 to 192 kHz."""
    NAME = "Airspy HF+"
    CAN_TX = False
    SAMPLE_BYTES = 8
    RATE = 768000
    DEC = 4
    SHIFT_MIN = 0
    SHIFT_MAX = 250
    SHIFT_NEW = 0

    def open(self):
        if not shutil.which("airspyhf_rx"):
            raise RuntimeError("airspyhf_rx not found - install it with: sudo apt install airspyhf")
        if shutil.which("airspyhf_info"):
            try:
                r = subprocess.run(["airspyhf_info"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=6)
                info = r.stdout.decode("utf8", "ignore")
                if "not found" in info.lower() or "no device" in info.lower():
                    raise RuntimeError("no Airspy HF+ found - is it plugged in?")
            except subprocess.SubprocessError:
                pass
        self.hw["version"] = "Airspy HF+"
        self.connected = True
        self.log("hardware: Airspy HF+ - receive only")
        self.events.put(("hello", self.hw["version"]))

    def set_flag(self, letter, on):
        key = "pre" if letter == "P" else "att"
        if letter == "P":
            self.amp = bool(on)                                # Pre-amp = HF+ LNA (+6 dB)
        else:
            self.att = bool(on)                                # Atten = 12 dB HF attenuator
        self.hw[key] = bool(on)
        self.events.put((key, bool(on)))
        self._restart()

    def _samples(self, raw):
        x = np.frombuffer(raw, dtype=np.float32).astype(np.float64)
        return x[0::2] + 1j * x[1::2]

    def _cmd(self, mode):
        c = self.cfg
        cmd = ["airspyhf_rx", "-f", "%.6f" % (self.hw_khz / 1000.0), "-a", str(self.RATE), "-r", "stdout",
               "-m", "on" if self.amp else "off", "-g", "on" if c.get("airspy_agc", True) else "off"]
        if getattr(self, "att", False):
            cmd += ["-t", "2"]
        if str(c.get("airspy_serial", "")).strip():
            cmd += ["-s", str(c["airspy_serial"]).strip()]
        return cmd


class SoapyRadio(HackRF):
    """SDRplay, ADALM-Pluto and any other radio with a SoapySDR driver, through SoapySDR's Python
    module (sudo apt install python3-soapysdr, plus the module for the radio).  Tuning, gain and
    TX / RX are done in place - no restarts.  The wide I/Q is cut down to 192 kHz like the HackRF."""
    NAME = "SoapySDR (other)"
    DRIVER = ""
    CAN_TX = True
    SHIFT_MIN = 110
    SHIFT_MAX = 700
    SHIFT_NEW = 250
    RATES = (2304000, 1920000, 1536000, 3072000, 2688000, 768000, 384000, 192000)

    def args(self):
        a = str(self.cfg.get("sdr_args", "")).strip()
        if self.DRIVER and "driver=" not in a:
            a = "driver=%s" % self.DRIVER + ("," + a if a else "")
        return a

    def open(self):
        try:
            import SoapySDR
        except ImportError:
            raise RuntimeError("needs SoapySDR for Python: sudo apt install python3-soapysdr, and the "
                               "SoapySDR module for the %s" % self.NAME)
        self.S = SoapySDR
        args = self.args()
        found = SoapySDR.Device.enumerate(args)
        if not found:
            raise RuntimeError("no %s found (SoapySDR args '%s') - is it plugged in, and is its SoapySDR "
                               "module installed?  SoapySDRUtil --find lists what SoapySDR can see"
                               % (self.NAME, args))
        self.dev = SoapySDR.Device(args)
        RX = SoapySDR.SOAPY_SDR_RX
        ok = []
        try:
            for r in self.dev.getSampleRateRange(RX, 0):
                ok.append((r.minimum(), r.maximum()))
        except Exception:
            pass
        rate = None
        for r in self.RATES:
            if not ok or any(lo - 1 <= r <= hi + 1 for lo, hi in ok):
                rate = r
                break
        if rate is None:
            raise RuntimeError("%s: none of the usable sample rates (192 kHz x n) is supported" % self.NAME)
        self.RATE, self.DEC = rate, rate // 192000
        self.SHIFT_MAX = max(0, int(rate / 2000) - 100 - 96)
        self.SHIFT_NEW = min(250, self.SHIFT_MAX)
        self.SHIFT_MIN = min(110, self.SHIFT_NEW)
        self.make_filters()
        self.dev.setSampleRate(RX, 0, rate)
        ant = str(self.cfg.get("sdr_antenna", "")).strip()
        if ant:
            self.dev.setAntenna(RX, 0, ant)
        self.rx_st = self.tx_st = None
        try:
            key = self.dev.getHardwareKey()
        except Exception:
            key = self.NAME
        self.hw["version"] = "%s (%s)" % (self.NAME, key) if key and key != self.NAME else self.NAME
        self.connected = True
        self.log("hardware: %s, I/Q %d kHz -> 192 kHz%s" % (self.hw["version"], rate // 1000,
                                                            "" if self.CAN_TX else ", receive only"))
        self.events.put(("hello", self.hw["version"]))

    def close(self):
        self.activate(False)
        self.connected = False
        self.dev = None

    def set_flag(self, letter, on):
        key = "pre" if letter == "P" else "att"
        if letter == "P":
            self.amp = bool(on)                                # Pre-amp = the radio's automatic gain
        else:
            self.att = bool(on)                                # Atten = 20 dB less gain
        self.hw[key] = bool(on)
        self.events.put((key, bool(on)))
        self._restart()

    def _kill(self):
        self.gen += 1
        S, d = getattr(self, "S", None), getattr(self, "dev", None)
        for name in ("rx_st", "tx_st"):
            st = getattr(self, name, None)
            if st is not None and d is not None:
                try:
                    d.deactivateStream(st)
                    d.closeStream(st)
                except Exception:
                    pass
            setattr(self, name, None)
        self.proc_mode = None

    def _gains(self):
        S, d, c = self.S, self.dev, self.cfg
        RX, TX = S.SOAPY_SDR_RX, S.SOAPY_SDR_TX
        try:
            if d.hasGainMode(RX, 0):
                d.setGainMode(RX, 0, bool(self.amp))
            if not self.amp:
                d.setGain(RX, 0, float(c.get("sdr_rx_gain", 30)) - (20.0 if getattr(self, "att", False) else 0.0))
        except Exception as e:
            self.log("%s RX gain: %s" % (self.NAME, e))
        if self.CAN_TX:
            try:
                d.setGain(TX, 0, float(c.get("sdr_tx_gain", 0)))
            except Exception:
                pass

    def _restart(self):
        with self.lock:
            if not self.active or self.freq_khz is None or getattr(self, "dev", None) is None:
                return
            S, d = self.S, self.dev
            hz = float(self.hw_khz) * 1000.0
            want = self.mode if self.CAN_TX else "rx"
            if self.proc_mode != want:
                self._kill()
                if want == "rx":
                    self.rx_st = d.setupStream(S.SOAPY_SDR_RX, S.SOAPY_SDR_CF32)
                else:
                    d.setSampleRate(S.SOAPY_SDR_TX, 0, self.RATE)
                    self.tx_st = d.setupStream(S.SOAPY_SDR_TX, S.SOAPY_SDR_CF32)
            try:
                d.setFrequency(S.SOAPY_SDR_RX if want == "rx" else S.SOAPY_SDR_TX, 0, hz)
            except Exception as e:
                self.log("%s: cannot tune %.3f MHz: %s" % (self.NAME, hz / 1e6, e))
            self._gains()
            if self.proc_mode != want:
                st = self.rx_st if want == "rx" else self.tx_st
                d.activateStream(st)
                self.proc_mode = want
                self.gen += 1
                if want == "rx":
                    threading.Thread(target=self._soapy_reader, args=(self.gen,), daemon=True).start()

    def _soapy_reader(self, g):
        n = self.BLK
        buf = np.zeros(n, dtype=np.complex64)
        while g == self.gen:
            got = 0
            while got < n and g == self.gen:
                st = self.rx_st
                if st is None:
                    return
                try:
                    sr = self.dev.readStream(st, [buf[got:]], n - got, timeoutUs=500000)
                except Exception as e:
                    self.log("%s receive stream: %s" % (self.NAME, e))
                    return
                if sr.ret > 0:
                    got += sr.ret
                elif sr.ret not in (-1, -4):                   # timeout / overflow: keep going
                    if self.errs < 10:
                        self.errs += 1
                        self.log("%s receive error %d" % (self.NAME, sr.ret))
            if g == self.gen:
                self.rx_iq(buf.astype(np.complex128))

    def write(self, data):
        st = self.tx_st
        if st is None or self.proc_mode != "tx":
            return
        a = np.frombuffer(data, dtype="<i2").astype(np.float64) / 32768.0
        iq = a[0::2] + 1j * a[1::2]
        up = np.zeros(len(iq) * self.DEC, dtype=complex)
        up[::self.DEC] = iq
        up = self.int_fir.process(up)
        w = 2 * np.pi * self.shift_hz / self.RATE
        up = up * np.exp(1j * (self.tx_ph + w * np.arange(len(up))))
        self.tx_ph = (self.tx_ph + w * len(up)) % (2 * np.pi)
        out = (0.7 * up).astype(np.complex64)
        k = 0
        while k < len(out) and self.tx_st is st:
            try:
                sr = self.dev.writeStream(st, [out[k:]], len(out) - k, timeoutUs=500000)
            except Exception:
                return
            if sr.ret <= 0:
                return
            k += sr.ret


class SdrPlay(SoapyRadio):
    NAME = "SDRplay"
    DRIVER = "sdrplay"
    CAN_TX = False


class Pluto(SoapyRadio):
    NAME = "ADALM-Pluto"
    DRIVER = "plutosdr"
    CAN_TX = True


RADIO_CLASSES = {"HackRF": HackRF, "RTL-SDR": RtlSdr, "Airspy HF+": AirspyHF, "SDRplay": SdrPlay,
                 "ADALM-Pluto": Pluto, "SoapySDR (other)": SoapyRadio}


def make_radio(cfg, log):
    h = hw_name(cfg)
    if h in RADIO_CLASSES:
        return RADIO_CLASSES[h](cfg, log)
    if h == "None":
        return NullRadio(cfg, log)
    return SerialLink(cfg, log)


# ================================================================ audio / engine
class Stream:
    def __init__(self, name, cmd, log, stdin=False, stdout=False):
        self.name = name
        self.log = log
        self.errs = 0
        self.dev = cmd[cmd.index("-D") + 1] if "-D" in cmd else ""
        self.direction = "capture" if cmd[0] == "arecord" else "playback"
        try:
            self.p = subprocess.Popen(cmd, stdin=subprocess.PIPE if stdin else subprocess.DEVNULL,
                                      stdout=subprocess.PIPE if stdout else subprocess.DEVNULL,
                                      stderr=subprocess.PIPE)
        except OSError:
            raise RuntimeError("cannot run %s - install it with: sudo apt install alsa-utils" % cmd[0])
        if stdin and fcntl is not None:
            try:
                fcntl.fcntl(self.p.stdin.fileno(), 1031, 4096)     # F_SETPIPE_SZ: keep latency low
            except Exception:
                pass
        threading.Thread(target=self._err, daemon=True).start()

    def _err(self):
        try:
            for line in self.p.stderr:
                s = line.decode("utf8", "ignore").strip()
                low = s.lower()
                if not s or "underrun" in low or "overrun" in low:
                    continue
                if self.errs < 6:
                    self.errs += 1
                    self.log("%s: %s" % (self.name, s))
                    if "busy" in low:
                        self.log("%s: %s" % (self.name, busy_hint(self.dev, self.direction)))
        except Exception:
            pass

    def read(self, n):
        return self.p.stdout.read(n)

    def write(self, b):
        self.p.stdin.write(b)
        self.p.stdin.flush()

    def close(self):
        try:
            self.p.terminate()
            self.p.wait(timeout=1.0)
        except Exception:
            try:
                self.p.kill()
            except Exception:
                pass


class Engine:
    def __init__(self, cfg, log):
        self.cfg = cfg
        self.log = log
        self.serial = None
        self.modem = DigiModem()
        self.modem_on = True
        self.sstv = SstvRx()
        self.sstv_tx = SstvTx()
        self.sstv_on = True
        self.nbtv = NbtvRx()
        self.nbtv_tx = NbtvTx()
        self.nbtv_on = False
        self.running = False
        self.tx_on = False
        self.tx_want = False
        self.tx_ok = False
        self.rx_mute_until = 0.0
        self.latest = None
        self.mic_level = 0.0
        self.tx_level = 0.0
        self.streams = []
        self.threads = []
        self.build()

    @property
    def hackrf(self):
        return isinstance(self.serial, HackRF)

    def build(self):
        """(Re)create the radio for the chosen hardware and the DSP for its I/Q rate."""
        want = dict(RADIO_CLASSES, **{"None": NullRadio}).get(hw_name(self.cfg), SerialLink)
        if not isinstance(self.serial, want) or type(self.serial) is not want:
            if self.serial is not None:
                self.serial.close()
            self.serial = make_radio(self.cfg, self.log)
        rate = HackRF.OUT_RATE if self.hackrf else self.cfg["sample_rate"]   # every SDR gives 192 kHz
        self.rx = RxDsp(rate, self.cfg["audio_rate"])
        self.tx = TxDsp(rate, self.cfg["audio_rate"])
        self.tx.digi = self.modem
        self.tx.sstv = self.sstv_tx
        self.tx.nbtv = self.nbtv_tx

    def start(self):
        if self.running:
            return
        self.running = True
        self.tx_on = False
        self.tx_want = False
        self.tx_ok = False
        self.latest = None
        self.threads = [threading.Thread(target=self._rx_loop, daemon=True),
                        threading.Thread(target=self._tx_loop, daemon=True)]
        for t in self.threads:
            t.start()
        if self.hackrf:
            self.serial.activate(True)

    def stop(self):
        self.running = False
        if self.tx_on or self.tx_want:
            self.tx_end()
        if self.hackrf:
            self.serial.activate(False)
        for s in list(self.streams):
            s.close()
        self.streams = []
        for t in self.threads:
            t.join(2.0)
        self.threads = []

    def shutdown(self):
        self.stop()
        self.serial.close()

    # --- T/R switching
    def tx_begin(self):
        self.tx_want = True
        self.rx_mute_until = float("inf")               # receiver muted (AGC held) until back in RX
        if self.serial.connected:
            def done(ok):
                # transmit only once the hardware has confirmed with "Tx Set"
                if ok:
                    self.tx_on = self.tx_want
                else:
                    self.log("no 'Tx Set' reply - not transmitting; returning to receive")
                    self.tx_want = False
                    self.tx_on = False
                    self.rx_mute_until = time.time() + 0.3
                    self.serial.submit_txrx("RX", 0.0)
            self.serial.submit_txrx("TX", 0.0, done)
        else:
            self.log("serial not connected - transmitting I/Q without T/R switching")
            self.tx_on = True

    def tx_end(self):
        self.tx_want = False
        self.tx_on = False
        settle = max(0.0, float(self.cfg.get("rx_mute_ms", 250))) / 1000.0
        if self.serial.connected:
            # stay muted until the radio has really switched back ("Rx Set" / HackRF restarted),
            # then a little longer for the relays and the receiver to settle; 2 s at the most
            self.rx_mute_until = time.time() + 2.0 + settle

            def done(ok):
                self.rx_mute_until = time.time() + settle
            self.serial.submit_txrx("RX", 0.12, done)
        else:
            self.rx_mute_until = time.time() + settle

    # --- worker threads
    def _arec(self, name, dev, ch, rate):
        s = Stream(name, ["arecord", "-q", "-D", dev, "-t", "raw", "-f", "S16_LE", "-c", str(ch),
                          "-r", str(rate), "--buffer-time=100000"], self.log, stdout=True)
        self.streams.append(s)
        return s

    def _aplay(self, name, dev, ch, rate):
        s = Stream(name, ["aplay", "-q", "-D", dev, "-t", "raw", "-f", "S16_LE", "-c", str(ch),
                          "-r", str(rate), "--buffer-time=100000"], self.log, stdin=True)
        self.streams.append(s)
        return s

    def _rx_loop(self):
        cfg, rx = self.cfg, self.rx
        N = rx.N
        try:
            hackrf = self.hackrf
            demo = cfg["iq_in_dev"] == "demo" and not hackrf
            if hackrf:
                src = self.serial                            # I/Q from the HackRF, already at 192 kHz
            elif demo:
                src = DemoSource(rx.rate)
            else:
                src = self._arec("iq-in", cfg["iq_in_dev"], 2, rx.rate)
            spk = None
            if cfg["audio_out_dev"] != "none":
                # stereo: many USB headsets do not accept mono on hw:
                spk = self._aplay("audio-out", cfg["audio_out_dev"], 2, rx.arate)
            t0 = time.time()
            nblk = 0
            silence = bytes(rx.M * 4)
            while self.running:
                if hackrf:
                    iq = src.block(N)
                elif demo:
                    iq = src.block(N)
                    nblk += 1
                    dt = t0 + nblk * N / float(rx.rate) - time.time()
                    if dt > 0:
                        time.sleep(dt)
                else:
                    raw = src.read(N * 4)
                    if len(raw) < N * 4:
                        raise RuntimeError("I/Q input stopped - check the device name and sample rate")
                    s = np.frombuffer(raw, dtype="<i2").astype(np.float64) / 32768.0
                    iq = s[0::2] + 1j * s[1::2]
                rx.hold = self.tx_on or self.tx_want or time.time() < self.rx_mute_until
                pcm, spec, lvl = rx.process(iq)
                dau = rx.digi_audio
                if rx.arate != DIGI_AUDIO and (self.modem_on or self.sstv_on or self.nbtv_on):
                    n48 = int(round(len(dau) * DIGI_AUDIO / float(rx.arate)))
                    dau = np.interp(np.linspace(0, len(dau) - 1, n48), np.arange(len(dau)), dau)
                if self.modem_on and not rx.hold:
                    try:
                        self.modem.rx(dau)
                    except Exception as e:                   # a decoder problem must not stop RX
                        self.log("digital decoder: %s" % e)
                if self.sstv_on and not rx.hold:
                    try:
                        self.sstv.rx(dau)
                    except Exception as e:
                        self.log("SSTV decoder: %s" % e)
                if self.nbtv_on and not rx.hold:
                    try:
                        self.nbtv.rx(dau)
                    except Exception as e:
                        self.log("NBTV decoder: %s" % e)
                if spk is not None:
                    try:
                        st = rx.last_stereo                  # C-QuAM / Kahn: real stereo
                        spk.write(silence if rx.hold else (st.tobytes() if st is not None
                                                           else np.repeat(pcm, 2).tobytes()))
                    except (OSError, ValueError) as e:
                        # no speaker, but keep receiving: spectrum, waterfall and TX still work
                        self.log("audio output %s stopped (%s) - receiving continues without sound"
                                 % (cfg["audio_out_dev"], e))
                        spk = None
                self.latest = (spec, lvl, time.time())
        except Exception as e:
            if self.running:
                self.log("RX stopped: %s" % e)
            self.running = False

    def _tx_loop(self):
        cfg, tx = self.cfg, self.tx
        out = mic = None
        self.mic_level = 0.0
        self.tx_level = 0.0
        hackrf = self.hackrf
        if hackrf and not self.serial.CAN_TX:
            out = None                                       # receive-only SDR
        elif hackrf:
            out = self.serial                                # TX I/Q goes to the SDR
        elif cfg["iq_out_dev"] != "none":
            try:
                out = self._aplay("iq-out", cfg["iq_out_dev"], 2, tx.rate)
            except Exception as e:
                self.log("TX I/Q output %s: %s" % (cfg["iq_out_dev"], e))
        if cfg["mic_in_dev"] != "none":
            try:
                mic = self._arec("mic", cfg["mic_in_dev"], 1, tx.arate)
            except Exception as e:
                self.log("microphone %s: %s - test tones still work" % (cfg["mic_in_dev"], e))
        self.tx_ok = out is not None
        if hackrf and not self.serial.CAN_TX:
            pass
        elif out is None and cfg["iq_out_dev"] == "none" and not hackrf:
            self.log("no TX I/Q output device set (Settings) - transmit is off")
        silence = bytes(tx.N * 4)
        zeros = np.zeros(tx.M)
        dcm = 0.0
        t0 = time.time()
        nblk = 0
        while self.running:
            m = zeros
            if mic is not None:
                raw = mic.read(tx.M * 2)
                if len(raw) < tx.M * 2:
                    # do not stop the TX path: the test tones and Tune carrier need no microphone
                    self.log("microphone %s stopped - check the device in Settings (test tones still work)"
                             % cfg["mic_in_dev"])
                    mic = None
                    t0, nblk = time.time(), 0
                else:
                    m = np.frombuffer(raw, dtype="<i2").astype(np.float64) / 32768.0
            # mic level after the mic gain, 0..1 (shown on the MIC meter, RX and TX)
            dcm = 0.98 * dcm + 0.02 * float(m.mean())
            g = 10 ** (tx.p["mic_gain_db"] / 20.0)
            self.mic_level = min(1.5, float(np.max(np.abs(m - dcm))) * g)
            if self.tx_on:
                try:
                    pcm = tx.process(m)
                except Exception as e:                       # never let one bad block stop transmit
                    if time.time() - getattr(self, "tx_err_t", 0) > 5:
                        self.tx_err_t = time.time()
                        import traceback
                        tb = traceback.extract_tb(e.__traceback__)[-1]
                        self.log("TX processing error: %r (line %d, %s)" % (e, tb.lineno, tb.name))
                    pcm = np.zeros(tx.N * 2, dtype="<i2")
                self.tx_level = float(np.max(np.abs(pcm))) / 32767.0
                data = pcm.tobytes()
            else:
                tx.idle()
                self.tx_level = 0.0
                data = silence
            if out is not None:
                try:
                    out.write(data)
                except (OSError, ValueError) as e:
                    self.log("TX I/Q output %s stopped (%s). If the log shows a format or rate error, "
                             "use plughw:... instead of hw:... in Settings" % (cfg["iq_out_dev"], e))
                    out = None
                    self.tx_ok = False
                    self.tx_on = False
                    t0, nblk = time.time(), 0
            # keep real time when nothing else does: no mic, and no sound card output to block on
            if mic is None and (out is None or hackrf):
                nblk += 1
                dt = t0 + nblk * tx.M / float(tx.arate) - time.time()
                if dt > 0:
                    time.sleep(dt)


# ======================================================================== GUI
def list_alsa():
    devs = []
    for tool in ("arecord", "aplay"):
        try:
            txt = subprocess.check_output([tool, "-l"], stderr=subprocess.DEVNULL).decode("utf8", "ignore")
        except Exception:
            continue
        for m in re.finditer(r"card (\d+): (\S+) \[(.*?)\], device (\d+): (.*?) \[", txt):
            devs.append(("%s hw:%s,%s  (%s - %s)" % (tool, m.group(1), m.group(4), m.group(3), m.group(5)),
                         "hw:%s,%s" % (m.group(1), m.group(4))))
    return devs


def alsa_devices():
    """Sound devices with their names: {"capture": [(value, name)], "playback": [...]}.
    Each card is offered as plughw:CARD=..,DEV=.. (ALSA converts the sample format if needed,
    recommended) and as hw:CARD=..,DEV=.. (direct).  Card names stay the same after a reboot,
    card numbers may not."""
    res = {"capture": [], "playback": []}
    for tool, kind in (("arecord", "capture"), ("aplay", "playback")):
        try:
            txt = subprocess.check_output([tool, "-l"], stderr=subprocess.DEVNULL).decode("utf8", "ignore")
        except Exception:
            continue
        for m in re.finditer(r"card (\d+): (\S+) \[(.*?)\], device (\d+): (.*?) \[(.*?)\]", txt):
            num, cid, cname, dev, dname = m.group(1), m.group(2), m.group(3), m.group(4), m.group(5)
            name = "%s - %s (card %s)" % (cname, dname.strip(), num)
            for pre in ("plughw", "hw"):
                res[kind].append(("%s:CARD=%s,DEV=%s" % (pre, cid, dev), name, num, dev))
        try:
            big = subprocess.check_output([tool, "-L"], stderr=subprocess.DEVNULL).decode("utf8", "ignore")
        except Exception:
            big = ""
        names = set(l.strip() for l in big.splitlines() if l and not l[0].isspace())
        for v, desc in (("pipewire", "PipeWire sound server"), ("pulse", "PulseAudio sound server")):
            if v in names:
                res[kind].insert(0, (v, desc, None, None))
    return res


ASOUND = "/proc/asound"
SHARED_DEVICES = ("default", "pipewire", "pulse")       # go through the desktop sound server


def alsa_card_dev(dev):
    """(card number, device number) for hw:1,0 / plughw:CARD=H340,DEV=0 ..., or None."""
    v = (dev or "").strip()
    m = re.match(r"(?:plug)?hw:(?:CARD=)?([^,]+)(?:,(?:DEV=)?(\d+))?$", v)
    if not m:
        return None
    card, d = m.group(1), int(m.group(2) or 0)
    if card.isdigit():
        return int(card), d
    try:
        link = os.readlink(os.path.join(ASOUND, card))         # /proc/asound/H340 -> card2
        return int(re.sub(r"\D", "", link)), d
    except (OSError, ValueError):
        return None


def alsa_owner(dev, direction):
    """Name and pid of the program that has this device open, e.g. 'pipewire (pid 1234)'."""
    cd = alsa_card_dev(dev)
    if cd is None:
        return ""
    base = os.path.join(ASOUND, "card%d" % cd[0], "pcm%d%s" % (cd[1], "c" if direction == "capture" else "p"))
    owners = []
    for st in sorted(glob.glob(os.path.join(base, "sub*", "status"))):
        try:
            txt = open(st).read()
        except OSError:
            continue
        m = re.search(r"owner_pid\s*:\s*(\d+)", txt)
        if m:
            pid = m.group(1)
            try:
                comm = open("/proc/%s/comm" % pid).read().strip()
            except OSError:
                comm = "?"
            owners.append("%s (pid %s)" % (comm, pid))
    return ", ".join(owners)


def busy_hint(dev, direction):
    """Explain a 'Device or resource busy' error."""
    who = alsa_owner(dev, direction)
    txt = "%s is in use%s." % (dev, " by " + who if who else " by another program")
    if who and re.match(r"(pipewire|pulseaudio|wireplumber)", who):
        txt += (" That is the desktop sound server. For the headset choose 'default' (or 'pipewire' /"
                " 'pulse') in Settings so it is shared. For the SDR card press 'Release card' in"
                " Settings (or set the card's profile to Off in the sound settings).")
    elif who and "exsdr" in who.lower() or (who and re.match(r"(aplay|arecord|python)", who)):
        txt += " Is another copy of ExSDR still running?"
    return txt


def sound_server_cards():
    """{alsa card number: sound-server card name} from 'pactl list cards'."""
    try:
        txt = subprocess.check_output(["pactl", "list", "cards"], stderr=subprocess.DEVNULL,
                                      timeout=5).decode("utf8", "ignore")
    except Exception:
        return {}
    res = {}
    for block in re.split(r"\n(?=Card #)", txt):
        n = re.search(r"Name:\s*(\S+)", block)
        c = re.search(r'alsa\.card\s*=\s*"(\d+)"', block)
        if n and c:
            res[int(c.group(1))] = n.group(1)
    return res


def release_card(dev):
    """Tell PipeWire / PulseAudio to let go of the card (profile off).  Returns a line of text."""
    cd = alsa_card_dev(dev)
    if cd is None:
        return "choose a hw: or plughw: device first"
    name = sound_server_cards().get(cd[0])
    if not name:
        return "card %d is not used by the desktop sound server (or pactl is missing)" % cd[0]
    try:
        r = subprocess.run(["pactl", "set-card-profile", name, "off"], stdout=subprocess.DEVNULL,
                           stderr=subprocess.PIPE, timeout=5)
    except Exception as e:
        return "pactl failed: %s" % e
    if r.returncode:
        return "pactl failed: %s" % r.stderr.decode("utf8", "ignore").strip()
    return ("released card %d (%s) from the desktop sound server. To give it back, choose a profile "
            "for it again in the sound settings." % (cd[0], name))


def describe_device(value, devs):
    """Name of a device given as default, hw:1,0, plughw:CARD=CODEC,DEV=0 ..."""
    v = (value or "").strip()
    if v in ("demo", "none", "default"):
        return {"demo": "built-in test signals", "none": "not used",
                "default": "system default - shared through the desktop sound server"}[v]
    if v in ("pipewire", "pulse"):
        return "desktop sound server (shared)"
    m = re.match(r"(?:plug)?hw:(\d+)(?:,(\d+))?$", v)
    for kind in ("capture", "playback"):
        for val, name, num, dev in devs.get(kind, []):
            if val == v or (m and num == m.group(1) and dev == (m.group(2) or "0")):
                return name
    return ""


def dev_value(text):
    """The device part of a 'value   [name]' combobox entry."""
    t = (text or "").strip()
    return t.split()[0] if t else ""


def sound_test(kind, dev, rate, ch, iq=False, secs=2):
    """Play a short tone on, or record from, one device.  Returns a line of text."""
    if not dev or dev == "none":
        return "no device selected"
    if dev == "demo":
        return "demo = built-in test signals, nothing to test"
    fmt = ["-q", "-D", dev, "-t", "raw", "-f", "S16_LE", "-c", str(ch), "-r", str(rate)]
    try:
        if kind == "playback":
            t = np.arange(int(rate * secs)) / float(rate)
            if iq:      # complex tone 5 kHz above the LO: I = cos, Q = sin
                x = np.empty((len(t), 2))
                x[:, 0], x[:, 1] = np.cos(2 * np.pi * 5000 * t), np.sin(2 * np.pi * 5000 * t)
            else:
                x = np.sin(2 * np.pi * 1000 * t)[:, None].repeat(ch, axis=1)
            data = (0.3 * x * 32767).astype("<i2").tobytes()
            r = subprocess.run(["aplay"] + fmt, input=data, stdout=subprocess.DEVNULL,
                               stderr=subprocess.PIPE, timeout=secs + 8)
            err = r.stderr.decode("utf8", "ignore").strip()
            if r.returncode != 0:
                if "busy" in err.lower():
                    return "FAILED: " + busy_hint(dev, "playback")
                return "FAILED: " + (err.splitlines()[-1] if err else "aplay error %d" % r.returncode)
            return "OK - played %d s of %s at 30 %% level, %d Hz, %d ch" % (
                secs, "a 5 kHz I/Q tone" if iq else "1 kHz", rate, ch)
        r = subprocess.run(["arecord"] + fmt + ["-d", "1"], stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE, timeout=10)
        err = r.stderr.decode("utf8", "ignore").strip()
        if r.returncode != 0 or not r.stdout:
            if "busy" in err.lower():
                return "FAILED: " + busy_hint(dev, "capture")
            return "FAILED: " + (err.splitlines()[-1] if err else "arecord error %d" % r.returncode)
        a = np.frombuffer(r.stdout[:len(r.stdout) // (2 * ch) * 2 * ch], "<i2").astype(float) / 32768.0
        a = a.reshape(-1, ch)
        parts = []
        for c in range(ch):
            x = a[:, c] - a[:, c].mean()
            rms = 20 * math.log10(math.sqrt(float(np.mean(x * x))) + 1e-9)
            parts.append("%s peak %3d %%, %5.1f dBFS" % (("I", "Q")[c] if iq else "level",
                                                         round(100 * float(np.max(np.abs(x)))), rms))
        return "OK - recorded 1 s at %d Hz: " % rate + ";  ".join(parts)
    except FileNotFoundError:
        return "FAILED: aplay / arecord not found (sudo apt install alsa-utils)"
    except subprocess.TimeoutExpired:
        return "FAILED: no data - device busy or wrong sample rate?"


# ------------------------------------------------------------------ look / theme
GNOME_ACCENTS = {"blue": "#3584e4", "teal": "#2190a4", "green": "#3a944a", "yellow": "#c88800",
                 "orange": "#ed5b00", "red": "#e62d42", "pink": "#d56199", "purple": "#9141ac",
                 "slate": "#6f8396"}
YARU_ACCENTS = {"blue": "#0073e5", "red": "#da3450", "purple": "#7764d8", "magenta": "#b34cb3",
                "olive": "#4b8501", "sage": "#657b69", "bark": "#787859", "viridian": "#03875b",
                "prussiangreen": "#308280", "orange": "#e95420"}


def desktop_look():
    """Light / dark, accent colour and font of the desktop (GNOME, Ubuntu, KDE)."""
    look = {"dark": False, "accent": None, "family": None, "size": None, "source": "built-in"}

    def gs(key):
        try:
            return subprocess.check_output(["gsettings", "get", "org.gnome.desktop.interface", key],
                                           stderr=subprocess.DEVNULL, timeout=2).decode().strip().strip("'")
        except Exception:
            return ""
    scheme, theme, accent, font = gs("color-scheme"), gs("gtk-theme"), gs("accent-color"), gs("font-name")
    if scheme or theme:
        look["source"] = "GNOME"
        look["dark"] = "dark" in scheme or "dark" in theme.lower()
        m = re.match(r"Yaru-([a-z]+)", theme)
        if accent in GNOME_ACCENTS:
            look["accent"] = GNOME_ACCENTS[accent]
        elif m and m.group(1) in YARU_ACCENTS:
            look["accent"] = YARU_ACCENTS[m.group(1)]
        elif theme.startswith("Yaru"):
            look["accent"] = YARU_ACCENTS["orange"]
        m = re.match(r"(.+?)\s+(\d+(?:\.\d+)?)$", font)
        if m:
            look["family"], look["size"] = m.group(1), int(round(float(m.group(2))))
    kde = os.path.expanduser("~/.config/kdeglobals")
    if look["source"] == "built-in" and os.path.exists(kde):
        try:
            txt = open(kde).read()
            look["source"] = "KDE"
            m = re.search(r"^ColorScheme=(.*)$", txt, re.M)
            look["dark"] = bool(m and "dark" in m.group(1).lower())
            m = re.search(r"^AccentColor=(\d+),(\d+),(\d+)", txt, re.M)
            if m:
                look["accent"] = "#%02x%02x%02x" % tuple(int(x) for x in m.groups())
            m = re.search(r"^font=([^,]+),(\d+)", txt, re.M)
            if m:
                look["family"], look["size"] = m.group(1), int(m.group(2))
        except Exception:
            pass
    return look


def _mix(c1, c2, t):
    """Blend two #rrggbb colours: t = 0 -> c1, t = 1 -> c2."""
    a = [int(c1[i:i + 2], 16) for i in (1, 3, 5)]
    b = [int(c2[i:i + 2], 16) for i in (1, 3, 5)]
    return "#%02x%02x%02x" % tuple(int(round(x + (y - x) * t)) for x, y in zip(a, b))


# frequency display colours (right-click the display, or Settings -> Look)
DIGIT_COLOURS = {"Amber": "#f4c96b", "Green": "#72e08a", "Cyan": "#6fd6ff", "Blue": "#7aa7ff",
                 "White": "#e8edf2", "Orange": "#ff9f43", "Red": "#ff5f56", "Accent": None}


def digit_colour(name, accent):
    """#rrggbb for a preset name, 'Accent' (desktop accent colour) or a #rrggbb value."""
    n = (name or "Amber").strip()
    if re.match(r"^#[0-9a-fA-F]{6}$", n):
        return n.lower()
    for k, v in DIGIT_COLOURS.items():
        if k.lower() == n.lower():
            return v or accent or DIGIT_COLOURS["Amber"]
    return DIGIT_COLOURS["Amber"]


def make_palette(look, choice="Auto"):
    dark = look["dark"] if choice not in ("Light", "Dark") else choice == "Dark"
    acc = look.get("accent") or "#3d8fd6"
    if dark:
        p = dict(BG="#232629", CARD="#2b2f33", FIELD="#1c1f22", FG="#e2e4e7", MUTED="#9ba2aa",
                 BORDER="#3a3f45", HOVER="#363b40")
    else:
        p = dict(BG="#e9ecef", CARD="#f8f9fa", FIELD="#ffffff", FG="#1f2328", MUTED="#5f6670",
                 BORDER="#cdd2d8", HOVER="#e1e5ea")
    p.update(dark=dark, ACC=acc, SEL=_mix(acc, p["CARD"], 0.55 if not dark else 0.35),
             TXSEL=_mix("#e05252", p["CARD"], 0.35), RED="#d9534f", GREEN="#4caf50",
             DISPLAY="#11161b", DIGIT="#f4c96b", DIGIT_DIM="#c8a35a", GRID="#26303a", SCALE_TXT="#8a96a3")
    return p


def fit_to_screen(win, margin_w=20, margin_h=90):
    """Make a window no bigger than the display, and centre it."""
    try:
        win.update_idletasks()
        rw, rh = win.winfo_reqwidth(), win.winfo_reqheight()
        sw, sh = win.winfo_screenwidth(), win.winfo_screenheight()
        w, h = min(rw, sw - margin_w), min(rh, sh - margin_h)
        win.minsize(min(640, w), min(400, h))
        x, y = max(0, (sw - w) // 2), max(0, (sh - h - 40) // 2)
        win.geometry("%dx%d+%d+%d" % (w, h, x, y))
    except Exception:
        pass


def list_ports():
    ports = []
    for pat in ("/dev/ttyUSB*", "/dev/ttyACM*", "/dev/ttyS[0-9]*", "/dev/serial/by-id/*"):
        ports += sorted(glob.glob(pat))
    return ports


class App:
    def __init__(self, root, cfg):
        self.root = root
        self.cfg = cfg
        self.logq = queue.Queue()
        self.eng = Engine(cfg, self.logq.put)
        self.ser = self.eng.serial
        self.rate = self.eng.rx.rate
        self.fmin_khz, self.fmax_khz = HW_LIMITS_KHZ[hw_name(cfg)]
        self.lo_khz = int(clamp(cfg["lo_khz"], self.fmin_khz, self.fmax_khz))
        self.tune_hz = int(cfg["tune_hz"])
        self.sw, self.sh = 1000, 200
        self.ww, self.wh = 1000, 200
        self.last_ts = None
        self.grid_key = None
        self.wf_arr = None
        self.wf_img = None
        self.settings_win = None
        self.lvl_s = -120.0
        self.af_s = None
        self.log_shown = False
        ui = dict(UI_DEFAULTS)
        ui.update(cfg.get("ui", {}))
        self.ui = ui
        for k in [k for k, v in ui.items() if v is None]:     # unset values: use the defaults
            del ui[k]
        self.vars = {}
        self.setup_look()
        self.v_dcol = tk.StringVar(value=self.cfg.get("digit_colour", "Amber"))
        self.set_title()
        root.configure(bg=self.BG)
        root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.lut = self.make_lut()
        self.bc_sched = BcSchedule(self.cfg, self.log)
        self.bc_win = None
        self.build_gui()
        self.station_changed()
        self.on_mode(initial=True)
        self.apply_hardware()
        self.update_freq_display()
        self.connect_serial()
        self.root.after(50, self.tick)

    # ------------------------------------------------------------------ look
    def setup_look(self):
        """Colours and fonts that follow the desktop (light / dark, accent colour, font)."""
        self.look = desktop_look()
        pal = make_palette(self.look, self.cfg.get("theme", "Auto"))
        for k, v in pal.items():
            setattr(self, k, v)
        self.set_digit_colours(self.cfg.get("digit_colour", "Amber"))
        try:
            import tkinter.font as tkfont
            fam = self.look["family"]
            size = int(self.cfg.get("font_size", 0) or self.look["size"] or 10)
            for name in ("TkDefaultFont", "TkTextFont", "TkMenuFont", "TkHeadingFont", "TkTooltipFont"):
                f = tkfont.nametofont(name)
                if fam:
                    f.configure(family=fam)
                f.configure(size=size)
            base = tkfont.nametofont("TkDefaultFont").actual()
            fam = base["family"]
        except Exception:
            fam, size = "Helvetica", 10
        self.F = (fam, size)
        self.F_SMALL = (fam, max(7, size - 2))
        self.F_CAP = (fam, max(7, size - 2), "bold")
        self.F_BOLD = (fam, size, "bold")
        self.F_BIG = (fam, size + 1, "bold")
        self.F_MONO = ("DejaVu Sans Mono", max(7, size - 1))
        self.F_TUNE = ("DejaVu Sans Mono", size + 20, "bold")
        self.F_LO = ("DejaVu Sans Mono", size + 7, "bold")
        st = ttk.Style(self.root)
        try:
            st.theme_use("clam")
        except Exception:
            pass
        c = dict(background=self.CARD, foreground=self.FG, fieldbackground=self.FIELD,
                 bordercolor=self.BORDER, lightcolor=self.CARD, darkcolor=self.CARD,
                 arrowcolor=self.MUTED, selectbackground=self.SEL, selectforeground=self.FG,
                 insertcolor=self.FG, troughcolor=self.FIELD)
        for w in ("TCombobox", "TEntry", "TSpinbox"):
            st.configure(w, **c)
            st.map(w, fieldbackground=[("readonly", self.FIELD)], foreground=[("readonly", self.FG)],
                   bordercolor=[("focus", self.ACC)], lightcolor=[("focus", self.ACC)])
        st.configure("TScale", background=self.SEL, troughcolor=self.FIELD, bordercolor=self.BORDER,
                     lightcolor=self.SEL, darkcolor=self.SEL, sliderlength=14)
        st.map("TScale", background=[("active", self.ACC)])
        st.configure("TNotebook", background=self.BG, bordercolor=self.BORDER, lightcolor=self.BG,
                     darkcolor=self.BG, tabmargins=(4, 4, 4, 0))
        st.configure("TNotebook.Tab", background=self.BG, foreground=self.MUTED, bordercolor=self.BORDER,
                     lightcolor=self.BG, darkcolor=self.BG, padding=(12, 4))
        st.map("TNotebook.Tab", background=[("selected", self.CARD)], foreground=[("selected", self.FG)])
        st.configure("Treeview", background=self.FIELD, fieldbackground=self.FIELD, foreground=self.FG,
                     bordercolor=self.BORDER, lightcolor=self.FIELD, darkcolor=self.FIELD, rowheight=18)
        st.map("Treeview", background=[("selected", self.SEL)], foreground=[("selected", self.FG)])
        st.configure("Treeview.Heading", background=self.CARD, foreground=self.MUTED, bordercolor=self.BORDER,
                     lightcolor=self.CARD, darkcolor=self.CARD, relief="flat")
        st.configure("Vertical.TScrollbar", background=self.CARD, troughcolor=self.BG,
                     bordercolor=self.BG, arrowcolor=self.MUTED)
        r = self.root
        r.option_add("*TCombobox*Listbox.background", self.FIELD)
        r.option_add("*TCombobox*Listbox.foreground", self.FG)
        r.option_add("*TCombobox*Listbox.selectBackground", self.SEL)
        r.option_add("*TCombobox*Listbox.selectForeground", self.FG)
        r.option_add("*TCombobox*Listbox.borderWidth", 0)

    # ---------------------------------------------------------------- helpers
    def var(self, name):
        d = self.ui[name]
        if isinstance(d, str):
            v = tk.StringVar(value=d)
        elif isinstance(d, int):
            v = tk.IntVar(value=d)
        else:
            v = tk.DoubleVar(value=d)
        self.vars[name] = v
        return v

    def fget(self, name, default=0.0):
        try:
            return float(self.vars[name].get())
        except (ValueError, tk.TclError):
            return default

    def log(self, s):
        self.logq.put(s)

    def make_lut(self):
        # soft waterfall: dark blue -> blue -> cyan -> yellow -> orange -> white
        pos = [0.0, 0.25, 0.45, 0.65, 0.85, 1.0]
        R = [12, 20, 30, 240, 250, 255]
        G = [16, 50, 170, 220, 120, 255]
        B = [28, 120, 220, 90, 40, 255]
        x = np.linspace(0, 1, 256)
        return np.stack([np.interp(x, pos, c) for c in (R, G, B)], axis=1).astype(np.uint8)

    @staticmethod
    def _bg(parent):
        try:
            return parent.cget("bg")
        except Exception:
            return None

    def frame(self, parent, **kw):
        return tk.Frame(parent, bg=self._bg(parent), **kw)

    def btn(self, parent, text, cmd=None, w=None):
        return tk.Button(parent, text=text, command=cmd, width=w, bg=self.FIELD if self.dark else self.CARD,
                         fg=self.FG, activebackground=self.HOVER, activeforeground=self.FG, relief=tk.FLAT,
                         bd=0, highlightthickness=1, highlightbackground=self.BORDER, highlightcolor=self.ACC,
                         padx=8, pady=3, cursor="hand2")

    def lbl(self, parent, text, muted=False, font=None):
        return tk.Label(parent, text=text, bg=self._bg(parent), fg=self.MUTED if muted else self.FG,
                        font=font or self.F)

    def toggle(self, parent, text, variable, value=None, cmd=None, width=None, color=None):
        """Flat push button that stays pressed (radio button when value is given)."""
        common = dict(text=text, variable=variable, command=cmd, indicatoron=False, width=width,
                      bg=self.FIELD if self.dark else self.CARD, fg=self.FG, selectcolor=color or self.SEL,
                      activebackground=self.HOVER, activeforeground=self.FG, relief=tk.FLAT, bd=0,
                      offrelief=tk.FLAT, highlightthickness=1, highlightbackground=self.BORDER,
                      padx=6, pady=3, cursor="hand2")
        if value is None:
            return tk.Checkbutton(parent, **common)
        return tk.Radiobutton(parent, value=value, **common)

    def chk(self, parent, text, name, cmd):
        return self.toggle(parent, text, self.var(name), cmd=cmd)

    def scale(self, parent, text, name, lo, hi, res, cmd, length=110, extra=None):
        """Title + value on one line, a flat slider below.  extra(top) may add to the title line."""
        f = self.frame(parent)
        top = self.frame(f)
        top.pack(fill=tk.X)
        tk.Label(top, text=text, bg=self._bg(f), fg=self.MUTED, font=self.F_SMALL).pack(side=tk.LEFT)
        val = tk.Label(top, text="", bg=self._bg(f), fg=self.FG, font=self.F_SMALL)
        val.pack(side=tk.RIGHT)
        if extra:
            extra(top)
        v = self.var(name)
        dec = 0 if res >= 1 else (1 if res >= 0.1 else 2)

        def changed(*_):
            try:
                x = round(float(v.get()) / res) * res
            except (ValueError, tk.TclError):
                return
            val.config(text=("%." + str(dec) + "f") % x)
            cmd()
        self._last_scale = ttk.Scale(f, from_=lo, to=hi, orient=tk.HORIZONTAL, length=length, variable=v,
                                     command=changed)
        self._last_scale.pack(fill=tk.X)
        try:
            val.config(text=("%." + str(dec) + "f") % float(v.get()))
        except (ValueError, tk.TclError):
            pass
        return f

    def group(self, parent, title):
        """A soft card with a small title."""
        f = tk.Frame(parent, bg=self.CARD, highlightthickness=1, highlightbackground=self.BORDER,
                     highlightcolor=self.BORDER, padx=8, pady=4)
        if title:
            tk.Label(f, text=title.upper(), bg=self.CARD, fg=self.MUTED, font=self.F_CAP).pack(
                side=tk.TOP, anchor="w", pady=(0, 3))
        return f

    def display(self, parent):
        """Dark panel for an HDSDR style digit display."""
        return tk.Frame(parent, bg=self.DISPLAY, padx=8, pady=2, highlightthickness=1,
                        highlightbackground=self.BORDER)

    def set_digit_colours(self, name):
        c = digit_colour(name, self.ACC)
        self.DIGIT = c
        self.DIGIT_DIM = _mix(c, self.DISPLAY, 0.35)       # LO digits, dots, dimmed leading zeros
        self.DIGIT_OFF = _mix(c, self.DISPLAY, 0.78)

    def change_digit_colour(self, name):
        """Recolour the LO and Tune displays now, and remember the choice."""
        self.cfg["digit_colour"] = name
        self.v_dcol.set(name)
        self.set_digit_colours(name)
        if hasattr(self, "lo_box"):
            self.fill_displays()
            self.update_freq_display()
            try:
                self.meter.itemconfig(self.sm_txt, fill=self.DIGIT)
            except Exception:
                pass
        save_cfg(self.cfg)

    def digit_menu(self, event):
        """Right-click on a frequency display: choose its colour."""
        m = tk.Menu(self.root, tearoff=0, bg=self.CARD, fg=self.FG, activebackground=self.SEL,
                    activeforeground=self.FG, bd=0)
        m.add_command(label="Display colour", state=tk.DISABLED)
        for name in DIGIT_COLOURS:
            sw = digit_colour(name, self.ACC)
            m.add_radiobutton(label="  %s" % name, variable=self.v_dcol, value=name,
                              command=lambda n=name: self.change_digit_colour(n), foreground=sw,
                              activeforeground=sw)
        try:
            m.tk_popup(event.x_root, event.y_root)
        finally:
            m.grab_release()

    def ndigits(self):
        """8 digits up to 99.999.999 Hz, 10 digits (up to 9.999 GHz) when the hardware goes higher."""
        return 10 if self.fmax_khz * 1000 > 99999999 else 8

    def _digits(self, box, n, font):
        for w in box.winfo_children():
            w.destroy()
        digits = []
        for i in range(n):
            d = tk.Label(box, text="0", font=font, fg=self.DIGIT, bg=self.DISPLAY, padx=0, bd=0,
                         cursor="sb_v_double_arrow")
            d.pack(side=tk.LEFT)
            digits.append(d)
            if i < n - 1 and (n - 1 - i) % 3 == 0:            # G.MMM.kkk.hhh
                dot = tk.Label(box, text=".", font=font, fg=self.DIGIT_DIM, bg=self.DISPLAY, padx=0)
                dot.pack(side=tk.LEFT)
                dot.bind("<Button-3>", self.digit_menu)
        for d in digits:
            d.bind("<Button-3>", self.digit_menu)
        box.bind("<Button-3>", self.digit_menu)
        return digits

    def fill_displays(self):
        n = self.ndigits()
        self.lo_digits = self._digits(self.lo_box, n, self.F_LO)
        for i, d in enumerate(self.lo_digits):
            d.bind("<Button-4>", lambda e, i=i: self.lo_digit_step(i, 1))
            d.bind("<Button-5>", lambda e, i=i: self.lo_digit_step(i, -1))
            d.bind("<MouseWheel>", lambda e, i=i: self.lo_digit_step(i, 1 if e.delta > 0 else -1))
            d.bind("<Button-1>", lambda e, i=i: self.lo_digit_step(
                i, 1 if e.y < e.widget.winfo_height() / 2 else -1))
        self.digits = self._digits(self.tune_box, n, self.F_TUNE)
        hz = tk.Label(self.tune_box, text=" Hz", font=self.F_SMALL, fg=self.DIGIT_DIM, bg=self.DISPLAY)
        hz.pack(side=tk.LEFT, anchor="s")
        hz.bind("<Button-3>", self.digit_menu)
        for i, d in enumerate(self.digits):
            d.bind("<Button-1>", lambda e, i=i: self.digit_click(e, i))
            d.bind("<Button-4>", lambda e, i=i: self.digit_step(i, 1))
            d.bind("<Button-5>", lambda e, i=i: self.digit_step(i, -1))
            d.bind("<MouseWheel>", lambda e, i=i: self.digit_step(i, 1 if e.delta > 0 else -1))

    # -------------------------------------------------------------------- GUI
    def build_gui(self):
        r = self.root
        gap = dict(padx=3, pady=3)

        # ---------- status bar (very bottom) ----------
        sbar = tk.Frame(r, bg=self.BG)
        sbar.pack(side=tk.BOTTOM, fill=tk.X, padx=6, pady=(0, 3))
        self.hw_label = tk.Label(sbar, text="", bg=self.BG, fg=self.MUTED, font=self.F_SMALL, anchor="w")
        self.hw_label.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.btn_log = self.btn(sbar, "Show log", self.toggle_log)
        self.btn_log.config(font=self.F_SMALL, pady=0)
        self.btn_log.pack(side=tk.RIGHT)
        hb = self.btn(sbar, "Help  (F1)", self.open_help)
        hb.config(font=self.F_SMALL, pady=0)
        hb.pack(side=tk.RIGHT, padx=4)
        self.station_lbl = tk.Label(sbar, text="", bg=self.BG, fg=self.ACC, font=self.F_SMALL)
        self.station_lbl.pack(side=tk.RIGHT, padx=8)
        r.bind("<F1>", lambda e: self.open_help())

        # ---------- log (hidden until asked for, or when something goes wrong) ----------
        self.log_card = self.group(r, "Log")
        self.logbox = tk.Text(self.log_card, height=5, bg=self.FIELD, fg=self.FG, font=self.F_MONO, bd=0,
                              highlightthickness=0, insertbackground=self.FG, wrap=tk.WORD)
        self.logbox.pack(side=tk.TOP, fill=tk.X)
        row = self.frame(self.log_card)
        row.pack(fill=tk.X, pady=(3, 0))
        self.lbl(row, "Send to hardware", muted=True, font=self.F_SMALL).pack(side=tk.LEFT)
        self.e_raw = ttk.Entry(row, width=20)
        self.e_raw.pack(side=tk.LEFT, padx=4)
        self.e_raw.bind("<Return>", self.send_raw)
        self.btn(row, "Read back ?F ?P ?A", self.ser.query_all).pack(side=tk.LEFT)

        # ---------- bottom control panel (HDSDR style) ----------
        panel = tk.Frame(r, bg=self.BG)
        panel.pack(side=tk.BOTTOM, fill=tk.X, padx=4)
        self.panel = panel
        # left: the two rows of controls, both ending at the same right edge
        # right: the mode tabs, a square in the bottom right corner below the waterfall
        left = tk.Frame(panel, bg=self.BG)
        left.pack(side=tk.LEFT, fill=tk.Y)
        rowA = tk.Frame(left, bg=self.BG)
        rowA.pack(side=tk.TOP, fill=tk.X)
        rowB = tk.Frame(left, bg=self.BG)
        rowB.pack(side=tk.TOP, fill=tk.X)
        xg = self.group(panel, None)
        xg.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=3, pady=3)
        self.build_mode_tabs(xg)
        self.tabs_card = xg
        self.bc_win = BcPanel(self, xg)

        # A1: Start / Settings
        cg = self.group(rowA, "Control")
        cg.pack(side=tk.LEFT, fill=tk.Y, **gap)
        self.btn_run = self.btn(cg, "Start", self.toggle_run, 8)
        self.btn_run.config(font=self.F_BOLD, bg=self.SEL)
        self.btn_run.pack(fill=tk.X, pady=(0, 3))
        self.btn(cg, "Settings", self.open_settings, 8).pack(fill=tk.X, pady=(0, 3))
        self.b_pre = self.chk(cg, "Pre-amp", "pre", self.on_pre)
        self.b_pre.pack(fill=tk.X, pady=(0, 3))
        self.b_att = self.chk(cg, "Atten", "att", self.on_att)
        self.b_att.pack(fill=tk.X)

        # A2: Mode and filter
        mg = self.group(rowA, "Mode")
        mg.pack(side=tk.LEFT, fill=tk.Y, **gap)
        row = self.frame(mg)
        row.pack(anchor="w")
        self.v_mode = tk.StringVar(value=self.cfg["mode"])
        for i, m in enumerate(["LSB", "USB", "CW", "AM", "ECSS", "FM"]):
            self.toggle(row, MODE_LABEL.get(m, m), self.v_mode, value=m, cmd=self.on_mode, width=6).grid(
                row=i // 3, column=i % 3, padx=1, pady=1, sticky="ew")
        # FM repeater shift, right of the FM button: 10 m 100 kHz, 6 m 1 MHz
        rp = self.frame(row)
        rp.grid(row=0, column=3, rowspan=2, sticky="w", padx=(6, 0))
        rr = self.frame(rp)
        rr.pack(anchor="w")
        self.lbl(rr, "FM rpt", muted=True, font=self.F_SMALL).pack(side=tk.LEFT, padx=(0, 3))
        self.rpt_btns = []
        v_rpt = self.var("rpt")                    # one variable shared by the three buttons
        for text, val in (("Simplex", "S"), ("-", "-"), ("+", "+")):
            b = self.toggle(rr, text, v_rpt, value=val, cmd=self.on_rpt, width=6 if val == "S" else 2)
            b.pack(side=tk.LEFT, padx=1)
            self.rpt_btns.append(b)
        self.rpt_lbl = tk.Label(rp, text="", bg=self._bg(rp), fg=self.MUTED, font=self.F_SMALL, anchor="w")
        self.rpt_lbl.pack(anchor="w", pady=(2, 0))
        row = self.frame(mg)
        row.pack(anchor="w")
        for m in ("CQUAM", "KAHN"):
            self.toggle(row, MODE_LABEL.get(m, m), self.v_mode, value=m, cmd=self.on_mode, width=6).pack(
                side=tk.LEFT, padx=1, pady=1)
        # emphasis: one setting for both directions (RX de-emphasis matches TX pre-emphasis)
        self.lbl(row, "  Emph", muted=True, font=self.F_SMALL).pack(side=tk.LEFT)
        v_em = self.var("emph")
        for t_ in ("Off", "50", "75"):
            self.toggle(row, t_, v_em, value=t_, cmd=self.on_emphasis, width=3).pack(side=tk.LEFT, padx=1)
        self.lbl(row, "us", muted=True, font=self.F_SMALL).pack(side=tk.LEFT, padx=(2, 0))
        side = self.frame(mg)
        side.pack(anchor="w", pady=(4, 0))
        self.lbl(side, "ECSS", muted=True, font=self.F_SMALL).pack(side=tk.LEFT)
        v_sb = self.var("ecss_sb")
        self.sb_buttons = []
        for text, val in (("L", "LSB"), ("DSB", "DSB"), ("U", "USB")):
            b = self.toggle(side, text, v_sb, value=val, cmd=self.push_rx, width=3)
            b.pack(side=tk.LEFT, padx=1)
            self.sb_buttons.append(b)
        self.lbl(side, "   Roll-off", muted=True, font=self.F_SMALL).pack(side=tk.LEFT)
        v_ro = self.var("rolloff")
        for text in ("Soft", "Hard"):
            self.toggle(side, text, v_ro, value=text, cmd=self.on_filter_shape, width=4).pack(side=tk.LEFT, padx=1)
        row = self.frame(mg)
        row.pack(fill=tk.X, pady=(4, 0))
        self.lbl(row, "Bandwidth", muted=True, font=self.F_SMALL).pack(side=tk.LEFT)
        self.width_lbl = tk.Label(row, text="", bg=self._bg(row), fg=self.FG, font=self.F_BOLD)
        self.width_lbl.pack(side=tk.RIGHT)
        lo, hi, st = WIDTH_RANGE[self.cfg["mode"]]
        self.v_width = tk.IntVar(value=int(self.cfg["widths"].get(self.cfg["mode"], DEF_WIDTH[self.cfg["mode"]])))
        self.sc_width = ttk.Scale(mg, from_=lo, to=hi, orient=tk.HORIZONTAL, length=220,
                                  variable=self.v_width, command=self.on_width)
        self.sc_width.pack(fill=tk.X)
        self.sc_width.bind("<Button-4>", lambda e: self.width_nudge(1))
        self.sc_width.bind("<Button-5>", lambda e: self.width_nudge(-1))
        self.sc_width.bind("<MouseWheel>", lambda e: self.width_nudge(1 if e.delta > 0 else -1))
        self.lowcut_box = self.scale(mg, "Low cut Hz", "lowcut", 0, 1000, 10, self.on_lowcut, 220)
        self.lowcut_box.pack(fill=tk.X, pady=(3, 0))
        self.sc_lowcut = self._last_scale
        self.scale(mg, "Stereo width %  (0 mono - 100 stereo)", "stereo_w", 0, 100, 1,
                   self.push_rx, 220, extra=self._stereo_indicator).pack(fill=tk.X, pady=(3, 0))
        self.sc_stereo = self._last_scale


        # A3: audio spectrum (like HDSDR's AF display)
        ag = self.group(rowA, "Audio")
        ag.pack(side=tk.LEFT, fill=tk.Y, **gap)
        self.af = tk.Canvas(ag, width=230, height=66, bg=self.DISPLAY, highlightthickness=0)
        self.af.pack()
        self.afw = tk.Canvas(ag, width=230, height=58, bg=self.DISPLAY, highlightthickness=0)
        self.afw.pack(pady=(2, 0))
        self.afw_item = self.afw.create_image(0, 0, anchor="nw")
        self.afw_arr = np.zeros((58, 230, 3), dtype=np.uint8)
        row = self.frame(ag)
        row.pack(fill=tk.X, pady=(2, 0))
        self.scale(row, "Ref dB", "af_ref", -60, 10, 1, lambda: None, 105).pack(side=tk.LEFT, padx=(0, 6))
        self.scale(row, "Range dB", "af_rng", 20, 120, 1, lambda: None, 105).pack(side=tk.LEFT)
        self.afw_img = None
        self.af_band = self.af.create_rectangle(0, 0, 0, 0, fill="#1e3a52", outline="")
        self.af_line = self.af.create_line(0, 0, 1, 1, fill="#7fd1ff")
        self.af_anf = self.af.create_line(-5, 0, -5, 0, fill="#ff6b6b", dash=(3, 2))
        self.af_axis = []

        # A4: frequency displays and S-meter
        fg_ = self.group(rowA, "Frequency")
        fg_.pack(side=tk.LEFT, fill=tk.Y, **gap)
        row = self.frame(fg_)
        row.pack(anchor="w", fill=tk.X)
        self.lbl(row, "LO", muted=True, font=self.F_CAP).pack(side=tk.LEFT, padx=(0, 6))
        self.lo_box = self.display(row)
        self.lo_box.pack(side=tk.LEFT)
        self.lo_label = tk.Label(row, text="", bg=self._bg(row), fg=self.MUTED, font=self.F_SMALL)
        self.lo_label.pack(side=tk.LEFT, padx=8)
        row = self.frame(fg_)
        row.pack(anchor="w", pady=(3, 0))
        self.lbl(row, "TUNE", muted=True, font=self.F_CAP).pack(side=tk.LEFT, padx=(0, 6))
        self.tune_box = self.display(row)
        self.tune_box.pack(side=tk.LEFT)
        self.fill_displays()
        row = self.frame(fg_)
        row.pack(anchor="w", fill=tk.X, pady=(4, 0))
        self.lbl(row, "Tune kHz", muted=True, font=self.F_SMALL).pack(side=tk.LEFT)
        self.e_freq = ttk.Entry(row, width=11)
        self.e_freq.pack(side=tk.LEFT, padx=4)
        self.e_freq.bind("<Return>", self.freq_entered)
        self.btn(row, "LO = Tune", self.recenter).pack(side=tk.LEFT, padx=2)
        self.lbl(row, "  Step", muted=True, font=self.F_SMALL).pack(side=tk.LEFT)
        ttk.Combobox(row, textvariable=self.var("step"), values=[str(s) for s in STEPS], width=7).pack(
            side=tk.LEFT, padx=4)
        self.meter = tk.Canvas(fg_, width=330, height=34, bg=self.DISPLAY, highlightthickness=0)
        self.meter.pack(anchor="w", pady=(5, 0), fill=tk.X)
        self.build_smeter()

        # A5: carrier PLL phase meter - stretched so its right edge lines up with Transmit below
        pg = self.group(rowA, "Meters")
        pg.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, **gap)
        self.pm = tk.Canvas(pg, width=240, height=76, bg=self.DISPLAY, highlightthickness=0)
        self.lbl(pg, "Carrier PLL  (ECSS / stereo)", muted=True, font=self.F_SMALL).pack(anchor="w")
        self.pm.pack(anchor="w")
        self.build_phase_meter()
        self.lbl(pg, "Level 0 - 100 %   MIC  /  RX audio  /  TX", muted=True, font=self.F_SMALL).pack(
            anchor="w", pady=(4, 0))
        self.vu = tk.Canvas(pg, width=240, height=36, bg=self.DISPLAY, highlightthickness=0)
        self.vu.pack(anchor="w")
        self.build_vu()
        self.tx_stat = tk.Label(pg, text="", bg=self._bg(pg), fg=self.MUTED, font=self.F_SMALL, anchor="w",
                                justify=tk.LEFT)
        self.tx_stat.pack(anchor="w", fill=tk.X)

        # B1: bands
        bg_ = self.group(rowB, "Bands")
        bg_.pack(side=tk.LEFT, fill=tk.Y, **gap)
        self.band_box = self.frame(bg_)
        self.band_box.pack(anchor="n")
        self.build_band_buttons()

        # B2: receive DSP
        rcg = self.group(rowB, "Receive")
        rcg.pack(side=tk.LEFT, fill=tk.Y, **gap)
        row = self.frame(rcg)
        row.pack(anchor="w")
        self.lbl(row, "AGC", muted=True, font=self.F_SMALL).pack(side=tk.LEFT)
        cb = ttk.Combobox(row, textvariable=self.var("agc"), values=["Off", "Fast", "Med", "Slow"], width=5,
                          state="readonly")
        cb.pack(side=tk.LEFT, padx=(3, 8))
        cb.bind("<<ComboboxSelected>>", lambda ev: self.push_rx())
        for text, name in (("NB", "nb"), ("NR", "nr"), ("Notch", "notch"), ("Auto notch", "anf"),
                           ("Auto IQ", "auto_iq")):
            self.chk(row, text, name, self.push_rx).pack(side=tk.LEFT, padx=1)
        self.anf_lbl = tk.Label(row, text="", width=11, anchor="w", bg=self._bg(row), fg=self.MUTED,
                                font=self.F_SMALL)
        self.anf_lbl.pack(side=tk.LEFT, padx=(4, 0))
        grid = self.frame(rcg)
        grid.pack(anchor="w", pady=(4, 0))
        sl = (("Volume", "vol", 0, 100, 1), ("RF gain / AGC limit dB", "gain_db", 0, 100, 1),
              ("Squelch dBFS", "squelch", -130, -20, 1), ("NB threshold", "nb_thr", 2, 20, 0.5),
              ("NR amount", "nr_amt", 0, 1, 0.05), ("Notch Hz", "notch_hz", 100, 5000, 10))
        for i, (t, n, a, b, res) in enumerate(sl):
            self.scale(grid, t, n, a, b, res, self.push_rx, 120).grid(row=i // 3, column=i % 3, padx=4, pady=1,
                                                                      sticky="ew")

        # B3: transmit
        tg = self.group(rowB, "Transmit")
        tg.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, **gap)
        row = self.frame(tg)
        row.pack(anchor="w")
        self.v_ptt = tk.IntVar(value=0)
        self.b_ptt = self.toggle(row, "  TX  ", self.v_ptt, cmd=self.on_ptt, color=self.TXSEL)
        self.b_ptt.config(font=self.F_BIG, padx=12)
        self.b_ptt.pack(side=tk.LEFT, padx=(0, 3))
        hold = self.btn(row, "Hold TX")
        hold.pack(side=tk.LEFT, padx=2)
        hold.bind("<ButtonPress-1>", lambda e: self.ptt(True))
        hold.bind("<ButtonRelease-1>", lambda e: self.ptt(False))
        self.v_tune = tk.IntVar(value=0)
        self.toggle(row, "Tune carrier", self.v_tune, cmd=self.push_tx, color=self.TXSEL).pack(side=tk.LEFT, padx=2)
        key = self.btn(row, "CW key (space)")
        key.pack(side=tk.LEFT, padx=2)
        key.bind("<ButtonPress-1>", lambda e: self.cw_key(True))
        key.bind("<ButtonRelease-1>", lambda e: self.cw_key(False))
        r.bind("<KeyPress-space>", self.space_down)
        r.bind("<KeyRelease-space>", self.space_up)
        row = self.frame(tg)
        row.pack(anchor="w", pady=(4, 0))
        col = self.frame(row)
        col.pack(side=tk.LEFT, anchor="n")
        self.lbl(col, "Source", muted=True, font=self.F_SMALL).pack(anchor="w")
        cb = ttk.Combobox(col, textvariable=self.var("src"), values=["Mic", "1 kHz tone", "Two-tone"], width=10,
                          state="readonly")
        cb.pack(anchor="w")
        cb.bind("<<ComboboxSelected>>", lambda ev: self.push_tx())
        self.scale(row, "Mic gain dB", "mic_db", 0, 60, 1, self.push_tx, 95).pack(side=tk.LEFT, padx=5, anchor="n")
        self.scale(row, "Drive", "drive", 0, 1, 0.01, self.push_tx, 95).pack(side=tk.LEFT, padx=5, anchor="n")
        self.mod_box = self.scale(row, "AM / FM mod %", "mod_pct", 0, 100, 1, self.push_tx, 95)
        self.mod_box.pack(side=tk.LEFT, padx=5, anchor="n")
        self.sc_mod = self._last_scale
        # speech processing: compressor + limiter
        row = self.frame(tg)
        row.pack(anchor="w", pady=(4, 0))
        self.chk(row, "Compressor", "comp", self.push_tx).pack(side=tk.LEFT, padx=(0, 2), anchor="s")
        self.scale(row, "Compression dB", "comp_db", 0, 20, 1, self.push_tx, 95).pack(side=tk.LEFT, padx=5, anchor="n")
        self.chk(row, "Limiter", "lim", self.push_tx).pack(side=tk.LEFT, padx=2, anchor="s")

        # ---------- spectrum and waterfall: top, full width, takes the remaining space ----------
        sg = self.group(r, None)
        sg.pack(side=tk.TOP, fill=tk.BOTH, expand=True, padx=7, pady=(6, 3))
        hdr = self.frame(sg)
        hdr.pack(side=tk.TOP, fill=tk.X, pady=(0, 3))
        tk.Label(hdr, text="SPECTRUM / WATERFALL", bg=self.CARD, fg=self.MUTED, font=self.F_CAP).pack(
            side=tk.LEFT, anchor="s")
        db = self.frame(hdr)
        db.pack(side=tk.RIGHT)
        self.lbl(db, "Zoom", muted=True, font=self.F_SMALL).pack(side=tk.LEFT)
        cb = ttk.Combobox(db, textvariable=self.var("zoom"), values=["1", "2", "4", "8", "16"], width=3,
                          state="readonly")
        cb.pack(side=tk.LEFT, padx=(3, 10))
        self.scale(db, "Ref dB", "ref", -100, 0, 1, lambda: None, 110).pack(side=tk.LEFT, padx=6)
        self.scale(db, "Range dB", "rng", 30, 130, 1, lambda: None, 110).pack(side=tk.LEFT, padx=6)
        self.sp = tk.Canvas(sg, width=1000, height=160, bg=self.DISPLAY, highlightthickness=0)
        self.sp.pack(fill=tk.BOTH, expand=True)
        self.sp_line = self.sp.create_line(0, 0, 1, 1, fill="#7fd1ff")
        self.sp_band = self.sp.create_rectangle(0, 0, 0, 0, fill="#3d6b8c", stipple="gray50", outline="")
        self.sp_tune = self.sp.create_line(0, 0, 0, 0, fill="#ff6b6b")
        self.sp.bind("<Configure>", self.on_sp_resize)
        for w in (self.sp,):
            w.bind("<Button-1>", self.spec_click)
            w.bind("<B1-Motion>", self.spec_click)
            w.bind("<Button-4>", lambda e: self.step_tune(1))
            w.bind("<Button-5>", lambda e: self.step_tune(-1))
            w.bind("<MouseWheel>", lambda e: self.step_tune(1 if e.delta > 0 else -1))
        tk.Frame(sg, bg=self.BORDER, height=1).pack(fill=tk.X)
        self.wf = tk.Canvas(sg, width=1000, height=180, bg=self.DISPLAY, highlightthickness=0)
        self.wf.pack(fill=tk.BOTH, expand=True)
        self.wf_item = self.wf.create_image(0, 0, anchor="nw")
        self.wf.bind("<Configure>", self.on_wf_resize)
        self.wf.bind("<Button-1>", self.spec_click)
        self.wf.bind("<B1-Motion>", self.spec_click)
        self.wf.bind("<Button-4>", lambda e: self.step_tune(1))
        self.wf.bind("<Button-5>", lambda e: self.step_tune(-1))
        self.root.after(5, self.square_tabs)
        self.root.after(10, lambda: fit_to_screen(self.root))

    def square_tabs(self):
        """Make the tabs container about as wide as the two control rows are high."""
        try:
            self.root.update_idletasks()
            h = self.panel.winfo_reqheight()
            if h > 50:
                self.tabs_card.config(width=h)
                self.tabs_card.pack_propagate(False)
        except Exception:
            pass

    def update_tx_stat(self):
        tx = self.eng.tx
        parts = []
        if self.eng.tx_on:
            if self.vars["comp"].get():
                parts.append("comp %d dB" % round(tx.comp_gr))
            if self.vars["lim"].get():
                parts.append("lim %d dB" % round(tx.lim_gr))
            if self.v_mode.get() in CARRIER_MODES + ("FM",):
                parts.append("mod %d %%" % round(100 * tx.mod_peak))
        self.tx_stat.config(text="   ".join(parts), fg=self.ACC if parts else self.MUTED)

    # tabs for the digital / image modes - place holders until they are filled in
    MODE_TABS = [
        ("Digital modes", "Digital modes - coming later"),
        ("Digital Voice", "Digital Voice - coming later"),
        ("SSTV", ""),
        ("NBTV", ""),
    ]

    def build_mode_tabs(self, parent):
        """Notebook with one empty page per future mode family.  self.mode_tabs[name] is the page
        frame, ready for its controls to be added."""
        self.mode_nb = ttk.Notebook(parent)
        self.mode_nb.pack(fill=tk.BOTH, expand=True)
        self.mode_tabs = {}
        for name, note in self.MODE_TABS:
            page = tk.Frame(self.mode_nb, bg=self.CARD, padx=6, pady=4)
            self.mode_nb.add(page, text=" %s " % name)
            if name == "Digital modes":
                self.build_digital_tab(page)
            elif name == "SSTV":
                self.build_sstv_tab(page)
            elif name == "NBTV":
                self.build_nbtv_tab(page)
            else:
                tk.Label(page, text=note, bg=self.CARD, fg=self.MUTED, font=self.F_SMALL,
                         anchor="nw", justify=tk.LEFT).pack(anchor="nw")
            self.mode_tabs[name] = page
        try:
            self.mode_nb.select(int(self.ui.get("mode_tab", 0)))
        except Exception:
            pass

    # ------------------------------------------------------------ digital modes
    def build_digital_tab(self, page):
        m = self.eng.modem
        top = self.frame(page)
        top.pack(fill=tk.X)
        self.v_digi_on = tk.IntVar(value=int(self.ui.get("digi_on", 1)))
        self.digi_onoff_btn = self.toggle(top, "ON", self.v_digi_on, cmd=self.on_digi_onoff, width=4,
                                          color="#4caf50")
        self.digi_onoff_btn.pack(side=tk.LEFT, padx=(0, 4))
        self.v_dmode = tk.StringVar(value=self.ui.get("dmode", "PSK31"))
        for t_ in DigiModem.MODES:
            self.toggle(top, t_, self.v_dmode, value=t_, cmd=self.on_digi_mode, width=8).pack(side=tk.LEFT, padx=1)
        self.dsub_box = self.frame(top)
        self.dsub_box.pack(side=tk.LEFT, padx=(6, 0))
        self.v_dspeed = tk.StringVar(value=str(self.ui.get("dspeed", "11")))
        self.v_dwpm = tk.StringVar(value=str(self.ui.get("dwpm", 20)))
        self.cb_dspeed = ttk.Combobox(self.dsub_box, textvariable=self.v_dspeed, values=list(DOMINO_MODES),
                                      width=4, state="readonly")
        self.cb_dspeed.bind("<<ComboboxSelected>>", lambda e: self.on_digi_mode())
        self.sp_wpm = ttk.Spinbox(self.dsub_box, from_=5, to=60, textvariable=self.v_dwpm, width=4,
                                  command=self.on_digi_mode)
        self.sp_wpm.bind("<Return>", lambda e: self.on_digi_mode())
        self.dsub_lbl = tk.Label(self.dsub_box, text="", bg=self.CARD, fg=self.MUTED, font=self.F_SMALL)
        # alignment: audio spectrum + waterfall around the signal, click to tune the decoder
        row = self.frame(page)
        row.pack(fill=tk.X, pady=(4, 0))
        self.v_afc = tk.IntVar(value=int(self.ui.get("dafc", 1)))
        self.toggle(row, "AFC", self.v_afc, cmd=self.on_digi_mode, width=4).pack(side=tk.LEFT, padx=1)
        self.btn(row, "Find", self.digi_find).pack(side=tk.LEFT, padx=2)
        self.btn(row, "Centre RF", self.digi_centre_rf).pack(side=tk.LEFT, padx=2)
        self.dfreq_lbl = tk.Label(row, text="", bg=self.CARD, fg=self.FG, font=self.F_BOLD)
        self.dfreq_lbl.pack(side=tk.LEFT, padx=6)
        self.dq = tk.Canvas(row, width=60, height=12, bg=self.DISPLAY, highlightthickness=0)
        self.dq.pack(side=tk.RIGHT, padx=2)
        self.dq_bar = self.dq.create_rectangle(0, 0, 0, 12, fill="#4caf50", outline="")
        tk.Label(row, text="Q", bg=self.CARD, fg=self.MUTED, font=self.F_SMALL).pack(side=tk.RIGHT)
        self.dal = tk.Canvas(page, width=360, height=64, bg=self.DISPLAY, highlightthickness=0, cursor="crosshair")
        self.dal.pack(fill=tk.X, pady=(3, 0))
        self.dal_img = None
        self.dal_item = self.dal.create_image(0, 0, anchor="nw")
        self.dal_arr = None
        self.dal.bind("<Button-1>", self.digi_click)
        self.dal.bind("<Configure>", lambda e: setattr(self, "dal_arr", None))
        self.dal_span = 600.0                                 # Hz shown around the decoder frequency
        # RX text
        rx = self.frame(page)
        rx.pack(fill=tk.BOTH, expand=True, pady=(3, 0))
        self.drx = tk.Text(rx, height=6, width=40, bg=self.FIELD, fg=self.FG, font=self.F_MONO, bd=0,
                           highlightthickness=1, highlightbackground=self.BORDER, wrap=tk.WORD)
        self.drx.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.drx.tag_configure("tx", foreground="#e05252")
        sb = ttk.Scrollbar(rx, orient=tk.VERTICAL, command=self.drx.yview)
        sb.pack(side=tk.RIGHT, fill=tk.Y)
        self.drx.config(yscrollcommand=sb.set)
        # TX text + buttons
        self.dtx = tk.Text(page, height=3, width=40, bg=self.FIELD, fg=self.FG, font=self.F_MONO, bd=0,
                           insertbackground=self.FG, highlightthickness=1, highlightbackground=self.BORDER,
                           wrap=tk.WORD)
        self.dtx.pack(fill=tk.X, pady=(3, 0))
        self.dtx.bind("<Control-Return>", lambda e: (self.digi_send(), "break")[1])
        bar = self.frame(page)
        bar.pack(fill=tk.X, pady=(3, 0))
        self.btn(bar, "Send  (Ctrl+Enter)", self.digi_send).pack(side=tk.LEFT)
        self.btn(bar, "Stop", self.digi_stop).pack(side=tk.LEFT, padx=3)
        self.btn(bar, "Clear RX", lambda: self.drx.delete("1.0", tk.END)).pack(side=tk.RIGHT)
        for t_ in ("73", "Info", "CQ"):
            b = self.btn(bar, t_, lambda t_=t_: self.digi_macro(t_))
            b.config(padx=4)
            b.pack(side=tk.RIGHT, padx=1)
        self.dstate = tk.Label(bar, text="", bg=self.CARD, fg=self.MUTED, font=self.F_SMALL)
        self.dstate.pack(side=tk.LEFT, padx=6)
        self.digi_tx = False
        m.f0 = float(self.ui.get("df0", 1000.0))
        self.on_digi_mode()
        kids = [w for w in (page.winfo_children() or []) if w is not top]
        self.digi_body = kids + [w for w in (top.winfo_children() or []) if w is not self.digi_onoff_btn]
        if not kids:                                          # (no widget tree: test stubs)
            self.digi_body = []
        self.on_digi_onoff()

    # ------------------------------------------------------------ on / off for a tab
    def set_enabled(self, widgets, on):
        """Grey out (or enable) every control inside these widgets."""
        def walk(w):
            try:
                if isinstance(w, ttk.Combobox):
                    w.config(state="readonly" if on else "disabled")
                elif isinstance(w, (ttk.Spinbox,)):
                    w.config(state="normal" if on else "disabled")
                elif isinstance(w, (tk.Button, tk.Checkbutton, tk.Radiobutton, tk.Entry, tk.Text, tk.Label)):
                    w.config(state="normal" if on else "disabled")
            except Exception:
                pass
            try:
                kids = w.winfo_children()
            except Exception:
                kids = []
            for c in kids or []:
                walk(c)
        for w in widgets:
            walk(w)

    def on_digi_onoff(self):
        on = bool(self.v_digi_on.get())
        self.eng.modem_on = on
        if not on:
            self.digi_stop()
            self.dal.delete("ov")
            self.dal_arr = None
            self.dal.itemconfig(self.dal_item, image="")
        self.set_enabled(self.digi_body, on)
        self.digi_onoff_btn.config(text="ON" if on else "OFF")
        self.ui["digi_on"] = int(on)

    # ------------------------------------------------------------ SSTV
    SSTV_DIR = os.path.join(os.path.expanduser("~"), "ExSDR", "SSTV")
    IMG_TYPES = [("Images", "*.png *.jpg *.jpeg *.bmp *.gif *.ppm *.pgm *.webp *.tif *.tiff"), ("All files", "*")]

    def build_sstv_tab(self, page):
        modes = list(SSTV_MODES)
        top = self.frame(page)
        top.pack(fill=tk.X)
        self.v_sstv_on = tk.IntVar(value=int(self.ui.get("sstv_on", 1)))
        self.sstv_onoff_btn = self.toggle(top, "ON", self.v_sstv_on, cmd=self.on_sstv_onoff, width=4,
                                          color="#4caf50")
        self.sstv_onoff_btn.pack(side=tk.LEFT, padx=(0, 4))
        body = []
        b1 = self.frame(top)
        b1.pack(side=tk.LEFT, fill=tk.X, expand=True)
        body.append(b1)
        self.v_sstv_vis = tk.IntVar(value=int(self.ui.get("sstv_vis", 1)))
        self.toggle(b1, "Auto (VIS)", self.v_sstv_vis, cmd=self.on_sstv_vis).pack(side=tk.LEFT, padx=1)
        self.v_sstv_rxmode = tk.StringVar(value=self.ui.get("sstv_rxmode", "Martin M1"))
        ttk.Combobox(b1, textvariable=self.v_sstv_rxmode, values=modes, width=13,
                     state="readonly").pack(side=tk.LEFT, padx=3)
        self.btn(b1, "Start", self.sstv_start_rx).pack(side=tk.LEFT, padx=1)
        self.btn(b1, "Stop", self.sstv_stop_rx).pack(side=tk.LEFT, padx=1)
        # viewer
        vr = self.frame(page)
        vr.pack(fill=tk.X, pady=(3, 0))
        body.append(vr)
        self.v_sstv_view = tk.StringVar(value="RX")
        self.toggle(vr, "RX image", self.v_sstv_view, value="RX", cmd=self.sstv_redraw).pack(side=tk.LEFT, padx=1)
        self.toggle(vr, "TX image", self.v_sstv_view, value="TX", cmd=self.sstv_redraw).pack(side=tk.LEFT, padx=1)
        self.sstv_stat = tk.Label(vr, text="", bg=self.CARD, fg=self.MUTED, font=self.F_SMALL, anchor="w")
        self.sstv_stat.pack(side=tk.LEFT, padx=6, fill=tk.X, expand=True)
        self.sv = tk.Canvas(page, width=320, height=200, bg=self.DISPLAY, highlightthickness=0)
        self.sv.pack(fill=tk.BOTH, expand=True, pady=(2, 0))
        self.sv_item = self.sv.create_image(0, 0, anchor="nw")
        self.sv_img = None
        self.sv_key = None
        self.sv.bind("<Configure>", lambda e: self.sstv_redraw())
        # tuning meter: waterfall + spectrum 1000 .. 2500 Hz, sync / black / white marks, offset
        tr = self.frame(page)
        tr.pack(fill=tk.X, pady=(3, 0))
        body.append(tr)
        self.st = tk.Canvas(tr, width=240, height=40, bg=self.DISPLAY, highlightthickness=0)
        self.st.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.st_item = self.st.create_image(0, 0, anchor="nw")
        self.st_img = None
        self.st_arr = None
        self.st_avg = None
        self.st.bind("<Configure>", lambda e: setattr(self, "st_arr", None))
        tb = self.frame(tr)
        tb.pack(side=tk.LEFT, padx=(4, 0))
        self.st_off = tk.Label(tb, text="--", bg=self.CARD, fg=self.FG, font=self.F_BOLD, width=9)
        self.st_off.pack()
        self.btn(tb, "Correct", self.sstv_correct).pack(fill=tk.X)
        # transmit
        tx = self.frame(page)
        tx.pack(fill=tk.X, pady=(3, 0))
        body.append(tx)
        self.v_sstv_txmode = tk.StringVar(value=self.ui.get("sstv_txmode", "Martin M1"))
        cb = ttk.Combobox(tx, textvariable=self.v_sstv_txmode, values=modes, width=13, state="readonly")
        cb.pack(side=tk.LEFT)
        cb.bind("<<ComboboxSelected>>", lambda e: self.sstv_prepare_tx())
        self.btn(tx, "Load image...", self.sstv_load).pack(side=tk.LEFT, padx=2)
        self.btn(tx, "Send", self.sstv_send).pack(side=tk.LEFT, padx=1)
        self.btn(tx, "Stop TX", self.sstv_stop_tx).pack(side=tk.LEFT, padx=1)
        sr = self.frame(page)
        sr.pack(fill=tk.X, pady=(3, 0))
        body.append(sr)
        self.lbl(sr, "Text", muted=True, font=self.F_SMALL).pack(side=tk.LEFT)
        self.v_sstv_text = tk.StringVar(value=self.ui.get("sstv_text", station(self.cfg, "callsign")))
        en = tk.Entry(sr, textvariable=self.v_sstv_text, width=12, bg=self.FIELD, fg=self.FG, bd=0,
                      insertbackground=self.FG, highlightthickness=1, highlightbackground=self.BORDER)
        en.pack(side=tk.LEFT, padx=3)
        en.bind("<Return>", lambda e: self.sstv_prepare_tx())
        en.bind("<FocusOut>", lambda e: self.sstv_prepare_tx())
        if Image is None:
            en.config(state="disabled")
            self.v_sstv_text.set("(needs python3-pil)")
        self.btn(sr, "Save image...", self.sstv_save).pack(side=tk.LEFT, padx=2)
        self.v_sstv_auto = tk.IntVar(value=int(self.ui.get("sstv_autosave", 1)))
        self.toggle(sr, "Auto save", self.v_sstv_auto, cmd=lambda: self.ui.update(
            sstv_autosave=int(self.v_sstv_auto.get()))).pack(side=tk.LEFT, padx=1)
        self.sstv_body = body
        self.sstv_src = None                                  # loaded picture (full size)
        self.sstv_tx_img = None                               # picture fitted to the TX mode
        self.sstv_last = None                                 # last received picture
        self.sstv_last_mode = ""
        self.sstv_txing = False
        self.eng.sstv.auto = bool(self.v_sstv_vis.get())
        src = self.ui.get("sstv_image")
        if src and os.path.isfile(src):
            try:
                self.sstv_src = read_image(src)
                self.sstv_src_path = src
            except Exception:
                self.sstv_src = None
        if self.sstv_src is None:
            self.sstv_src = sstv_test_card()
            self.sstv_src_path = ""
        self.sstv_prepare_tx()
        self.on_sstv_onoff()

    def on_sstv_onoff(self):
        on = bool(self.v_sstv_on.get())
        self.eng.sstv_on = on
        if not on:
            self.eng.sstv.stop()
            self.sstv_stop_tx()
            self.st_arr = None
            self.st.delete("ov")
            self.st.itemconfig(self.st_item, image="")
        self.set_enabled(self.sstv_body, on)
        self.sstv_onoff_btn.config(text="ON" if on else "OFF")
        self.ui["sstv_on"] = int(on)

    def on_sstv_vis(self):
        self.eng.sstv.auto = bool(self.v_sstv_vis.get())
        self.ui["sstv_vis"] = int(self.v_sstv_vis.get())

    def sstv_start_rx(self):
        name = self.v_sstv_rxmode.get()
        self.ui["sstv_rxmode"] = name
        if name in SSTV_MODES:
            self.eng.sstv.start_now(name)
            self.v_sstv_view.set("RX")
            self.log("SSTV: receiving %s (started by hand)" % name)

    def sstv_stop_rx(self):
        self.eng.sstv.stop()

    def sstv_prepare_tx(self):
        name = self.v_sstv_txmode.get()
        if name not in SSTV_MODES or self.sstv_src is None:
            return
        L = SstvLayout(name)
        img = fit_image(self.sstv_src, L.w, L.h)
        text = self.v_sstv_text.get().strip()
        if Image is not None and text:
            img = overlay_text(img, text)
        self.sstv_tx_img = img
        self.ui.update(sstv_txmode=name, sstv_text=self.v_sstv_text.get() if Image is not None else "")
        self.sv_key = None
        self.sstv_redraw()

    def sstv_load(self):
        if filedialog is None:
            return
        path = filedialog.askopenfilename(parent=self.root, title="Load image for SSTV", filetypes=self.IMG_TYPES)
        if not path:
            return
        try:
            self.sstv_src = read_image(path)
        except Exception as e:
            self.log("SSTV: cannot read %s: %s" % (path, e))
            return
        self.sstv_src_path = path
        self.ui["sstv_image"] = path
        self.v_sstv_view.set("TX")
        self.sstv_prepare_tx()
        self.log("SSTV: loaded %s (%d x %d)" % (os.path.basename(path), self.sstv_src.shape[1], self.sstv_src.shape[0]))

    def sstv_save(self, path=None):
        img = self.sstv_last if self.v_sstv_view.get() == "RX" or self.sstv_tx_img is None else self.sstv_tx_img
        if self.v_sstv_view.get() == "RX" and self.eng.sstv.img is not None:
            img = self.eng.sstv.img.copy()
        if img is None:
            self.log("SSTV: no picture to save yet")
            return
        if path is None:
            if filedialog is None:
                return
            os.makedirs(self.SSTV_DIR, exist_ok=True)
            mode = (self.sstv_last_mode or self.eng.sstv.mode or "sstv").replace(" ", "")
            path = filedialog.asksaveasfilename(
                parent=self.root, title="Save SSTV picture", initialdir=self.SSTV_DIR, defaultextension=".png",
                initialfile=time.strftime("%Y%m%d_%H%M%S_") + mode + ".png",
                filetypes=[("PNG", "*.png"), ("JPEG", "*.jpg"), ("Bitmap", "*.bmp"), ("PPM", "*.ppm")])
            if not path:
                return
        try:
            save_image(img, path)
            self.log("SSTV: saved %s" % path)
        except Exception as e:
            self.log("SSTV: cannot save %s: %s" % (path, e))

    def sstv_send(self):
        if self.sstv_tx_img is None:
            self.log("SSTV: load a picture first")
            return
        if getattr(self, "digi_tx", False) or self.sstv_txing or getattr(self, "nbtv_txing", False):
            self.log("SSTV: already transmitting")
            return
        if self.v_mode.get() not in ("USB", "LSB"):
            self.v_mode.set("USB")
            self.on_mode()
            self.log("SSTV: switched to USB")
        name = self.v_sstv_txmode.get()
        self.eng.sstv_tx.load(sstv_encode(self.sstv_tx_img, name))
        self.sstv_txing = True
        self.v_sstv_view.set("TX")
        self.push_tx()
        self.ptt(True)
        if not self.eng.tx_want and not self.eng.tx_on:      # TX refused
            self.eng.sstv_tx.abort()
            self.sstv_txing = False
            self.push_tx()
            return
        self.log("SSTV: sending %s, %.0f s" % (name, SstvLayout(name).total_s + 1.7))

    def sstv_stop_tx(self):
        self.eng.sstv_tx.abort()
        if getattr(self, "sstv_txing", False):
            self.sstv_txing = False
            self.ptt(False)
            self.push_tx()

    def sstv_correct(self):
        """Retune the receiver by the measured offset so the sync sits on 1200 Hz."""
        off = self.eng.sstv.offset
        if self.v_mode.get() not in ("USB", "LSB"):
            self.log("SSTV: Correct works in USB or LSB")
            return
        d = off if self.v_mode.get() == "USB" else -off
        self.set_tune(int(round(self.tune_hz + d)))
        with self.eng.sstv.lock:
            self.eng.sstv.offset = 0.0

    # ------------------------------------------------------------ NBTV
    NBTV_DIR = os.path.join(os.path.expanduser("~"), "ExSDR", "NBTV")
    NBTV_SOURCES = ("Test card", "Picture file", "Screen")

    def build_nbtv_tab(self, page):
        top = self.frame(page)
        top.pack(fill=tk.X)
        self.v_nbtv_on = tk.IntVar(value=int(self.ui.get("nbtv_on", 1)))
        self.nbtv_onoff_btn = self.toggle(top, "ON", self.v_nbtv_on, cmd=self.on_nbtv_onoff, width=4,
                                          color="#4caf50")
        self.nbtv_onoff_btn.pack(side=tk.LEFT, padx=(0, 4))
        body = []
        b1 = self.frame(top)
        b1.pack(side=tk.LEFT, fill=tk.X, expand=True)
        body.append(b1)
        self.v_nbtv_mode = tk.StringVar(value=self.ui.get("nbtv_mode", "96x72 Colour"))
        cb = ttk.Combobox(b1, textvariable=self.v_nbtv_mode, values=list(NBTV_MODES), width=13, state="readonly")
        cb.pack(side=tk.LEFT)
        cb.bind("<<ComboboxSelected>>", lambda e: self.on_nbtv_mode())
        self.v_nbtv_avg = tk.IntVar(value=int(self.ui.get("nbtv_avg", 0)))
        self.toggle(b1, "Average", self.v_nbtv_avg, cmd=self.nbtv_settings).pack(side=tk.LEFT, padx=(4, 1))
        self.v_nbtv_neon = tk.IntVar(value=int(self.ui.get("nbtv_neon", 1)))
        self.toggle(b1, "Neon", self.v_nbtv_neon, cmd=self.nbtv_settings).pack(side=tk.LEFT, padx=1)
        vr = self.frame(page)
        vr.pack(fill=tk.X, pady=(3, 0))
        body.append(vr)
        self.v_nbtv_view = tk.StringVar(value="RX")
        self.toggle(vr, "RX picture", self.v_nbtv_view, value="RX", cmd=self.nbtv_force).pack(side=tk.LEFT, padx=1)
        self.toggle(vr, "TX picture", self.v_nbtv_view, value="TX", cmd=self.nbtv_force).pack(side=tk.LEFT, padx=1)
        self.nbtv_stat = tk.Label(vr, text="", bg=self.CARD, fg=self.MUTED, font=self.F_SMALL, anchor="w")
        self.nbtv_stat.pack(side=tk.LEFT, padx=6, fill=tk.X, expand=True)
        self.nv = tk.Canvas(page, width=320, height=200, bg="#000000", highlightthickness=0)
        self.nv.pack(fill=tk.BOTH, expand=True, pady=(2, 0))
        self.nv_item = self.nv.create_image(0, 0, anchor="nw")
        self.nv_img = None
        self.nv_key = None
        self.nv.bind("<Configure>", lambda e: self.nbtv_force())
        # tuning meter
        tr = self.frame(page)
        tr.pack(fill=tk.X, pady=(3, 0))
        body.append(tr)
        self.nt = tk.Canvas(tr, width=240, height=40, bg=self.DISPLAY, highlightthickness=0)
        self.nt.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.nt_item = self.nt.create_image(0, 0, anchor="nw")
        self.nt_img = None
        self.nt_arr = None
        self.nt_avg = None
        self.nt.bind("<Configure>", lambda e: setattr(self, "nt_arr", None))
        tb = self.frame(tr)
        tb.pack(side=tk.LEFT, padx=(4, 0))
        self.nt_off = tk.Label(tb, text="--", bg=self.CARD, fg=self.FG, font=self.F_BOLD, width=9)
        self.nt_off.pack()
        self.btn(tb, "Correct", self.nbtv_correct).pack(fill=tk.X)
        # transmit
        tx = self.frame(page)
        tx.pack(fill=tk.X, pady=(3, 0))
        body.append(tx)
        self.v_nbtv_src = tk.StringVar(value=self.ui.get("nbtv_src", "Test card"))
        cs = ttk.Combobox(tx, textvariable=self.v_nbtv_src, values=list(self.NBTV_SOURCES), width=11,
                          state="readonly")
        cs.pack(side=tk.LEFT)
        cs.bind("<<ComboboxSelected>>", lambda e: self.nbtv_source_changed())
        self.btn(tx, "Load...", self.nbtv_load).pack(side=tk.LEFT, padx=2)
        self.btn(tx, "Area...", self.nbtv_area).pack(side=tk.LEFT, padx=1)
        self.btn(tx, "Send", self.nbtv_send).pack(side=tk.LEFT, padx=(4, 1))
        self.btn(tx, "Stop TX", self.nbtv_stop_tx).pack(side=tk.LEFT, padx=1)
        sr = self.frame(page)
        sr.pack(fill=tk.X, pady=(3, 0))
        body.append(sr)
        self.btn(sr, "Save frame...", self.nbtv_save).pack(side=tk.LEFT)
        self.v_nbtv_rec = tk.IntVar(value=0)
        self.toggle(sr, "Record", self.v_nbtv_rec, cmd=self.nbtv_record, color="#e05252").pack(side=tk.LEFT, padx=3)
        self.nbtv_area_lbl = tk.Label(sr, text="", bg=self.CARD, fg=self.MUTED, font=self.F_SMALL)
        self.nbtv_area_lbl.pack(side=tk.LEFT, padx=4)
        self.nbtv_body = body
        self.nbtv_txing = False
        self.nbtv_capturing = False
        self.nbtv_rec_dir = None
        self.nbtv_rec_n = 0
        self.nbtv_last = None
        a = self.ui.get("nbtv_area")
        self.nbtv_area_box = tuple(a) if isinstance(a, (list, tuple)) and len(a) == 4 else None
        self.nbtv_pic = None
        p = self.ui.get("nbtv_image")
        if p and os.path.isfile(p):
            try:
                self.nbtv_pic = read_image(p)
            except Exception:
                self.nbtv_pic = None
        self.nbtv_tx_img = None
        self.on_nbtv_mode()
        self.nbtv_source_changed()
        self.on_nbtv_onoff()

    def on_nbtv_onoff(self):
        on = bool(self.v_nbtv_on.get())
        self.eng.nbtv_on = on
        if not on:
            self.nbtv_stop_tx()
            self.nt_arr = None
            self.nt.delete("ov")
            self.nt.itemconfig(self.nt_item, image="")
        self.set_enabled(self.nbtv_body, on)
        self.nbtv_onoff_btn.config(text="ON" if on else "OFF")
        self.ui["nbtv_on"] = int(on)

    def nbtv_settings(self):
        self.ui.update(nbtv_avg=int(self.v_nbtv_avg.get()), nbtv_neon=int(self.v_nbtv_neon.get()))
        self.nbtv_force()

    def nbtv_force(self):
        self.nv_key = None
        self.nbtv_redraw()

    def on_nbtv_mode(self):
        name = self.v_nbtv_mode.get()
        if name not in NBTV_MODES:
            return
        if self.nbtv_txing:
            self.nbtv_stop_tx()
        self.eng.nbtv.set_mode(name)
        self.ui["nbtv_mode"] = name
        self.nbtv_tx_img = None
        self.nbtv_prepare()

    def nbtv_source_changed(self):
        self.ui["nbtv_src"] = self.v_nbtv_src.get()
        if self.v_nbtv_src.get() == "Screen":
            self.nbtv_area_lbl.config(text="area %dx%d" % self.nbtv_area_box[2:] if self.nbtv_area_box
                                      else "whole screen")
        else:
            self.nbtv_area_lbl.config(text="")
        self.nbtv_prepare()

    def nbtv_prepare(self, img=None):
        """Picture for the TX view (and the transmitter) from the chosen source."""
        L = NbtvLayout(self.v_nbtv_mode.get())
        src = self.v_nbtv_src.get()
        if img is None:
            if src == "Picture file" and self.nbtv_pic is not None:
                img = self.nbtv_pic
            elif src == "Screen" and self.nbtv_tx_img is not None:
                return
            else:
                img = sstv_test_card()
        self.nbtv_tx_img = fit_image(img, L.w, L.h)
        self.nv_key = None
        self.nbtv_redraw()

    def nbtv_load(self):
        if filedialog is None:
            return
        path = filedialog.askopenfilename(parent=self.root, title="Picture for NBTV", filetypes=self.IMG_TYPES)
        if not path:
            return
        try:
            self.nbtv_pic = read_image(path)
        except Exception as e:
            self.log("NBTV: cannot read %s: %s" % (path, e))
            return
        self.ui["nbtv_image"] = path
        self.v_nbtv_src.set("Picture file")
        self.v_nbtv_view.set("TX")
        self.nbtv_source_changed()
        if self.nbtv_txing:
            self.eng.nbtv_tx.set_image(self.nbtv_pic)

    def nbtv_area(self):
        """A see-through window: move and size it over what you want to send, then press Use."""
        if getattr(self, "nbtv_area_win", None) is not None:
            self.nbtv_area_win.lift()
            return
        w = tk.Toplevel(self.root)
        self.nbtv_area_win = w
        w.title("NBTV capture area")
        w.configure(bg="#e05252")
        try:
            w.attributes("-alpha", 0.45)
        except Exception:
            pass
        if self.nbtv_area_box:
            x, y, ww, hh = self.nbtv_area_box
            w.geometry("%dx%d+%d+%d" % (ww, hh, x, y))
        else:
            w.geometry("384x288+200+200")
        tk.Label(w, text="Move and resize this window over\nwhat you want to send, then press Use",
                 bg="#e05252", fg="white").pack(expand=True)
        bar = tk.Frame(w, bg="#e05252")
        bar.pack(side=tk.BOTTOM, pady=6)

        def done(use):
            if use:
                try:
                    w.update_idletasks()
                    self.nbtv_area_box = (w.winfo_rootx(), w.winfo_rooty(), w.winfo_width(), w.winfo_height())
                    self.ui["nbtv_area"] = list(self.nbtv_area_box)
                except Exception:
                    pass
            self.nbtv_area_win = None
            w.destroy()
            if use:
                self.v_nbtv_src.set("Screen")
                self.nbtv_source_changed()
                self.nbtv_grab()
        tk.Button(bar, text="Use this area", command=lambda: done(True)).pack(side=tk.LEFT, padx=4)
        tk.Button(bar, text="Whole screen", command=lambda: (setattr(self, "nbtv_area_box", None),
                                                             self.ui.pop("nbtv_area", None), done(False),
                                                             self.v_nbtv_src.set("Screen"),
                                                             self.nbtv_source_changed(),
                                                             self.nbtv_grab())).pack(side=tk.LEFT, padx=4)
        tk.Button(bar, text="Cancel", command=lambda: done(False)).pack(side=tk.LEFT, padx=4)
        w.protocol("WM_DELETE_WINDOW", lambda: done(False))

    def nbtv_grab(self):
        """Take a screen picture in the background (it can take a moment) and use it."""
        if self.nbtv_capturing:
            return
        self.nbtv_capturing = True
        box = self.nbtv_area_box

        def run():
            try:
                img = capture_screen(box)
            except Exception as e:
                img = None
                self.log("NBTV screen capture: %s" % e)
            self.nbtv_capturing = False
            if img is not None:
                self.root.after(0, lambda: self.nbtv_screen_ready(img))
        threading.Thread(target=run, daemon=True).start()

    def nbtv_screen_ready(self, img):
        if self.v_nbtv_src.get() != "Screen":
            return
        self.nbtv_prepare(img)
        if self.nbtv_txing:
            self.eng.nbtv_tx.set_image(img)

    def nbtv_send(self):
        if getattr(self, "digi_tx", False) or getattr(self, "sstv_txing", False) or self.nbtv_txing:
            self.log("NBTV: already transmitting")
            return
        if self.v_mode.get() not in ("USB", "LSB"):
            self.v_mode.set("USB")
            self.on_mode()
            self.log("NBTV: switched to USB")
        if self.nbtv_tx_img is None:
            self.nbtv_prepare()
        self.eng.nbtv_tx.start(self.v_nbtv_mode.get(), self.nbtv_tx_img)
        self.nbtv_txing = True
        self.v_nbtv_view.set("TX")
        self.push_tx()
        self.ptt(True)
        if not self.eng.tx_want and not self.eng.tx_on:
            self.eng.nbtv_tx.abort()
            self.nbtv_txing = False
            self.push_tx()
            return
        L = NbtvLayout(self.v_nbtv_mode.get())
        self.log("NBTV: sending %s, %.1f s per frame, until Stop TX" % (L.name, L.frame_s))

    def nbtv_stop_tx(self):
        self.eng.nbtv_tx.abort()
        if getattr(self, "nbtv_txing", False):
            self.nbtv_txing = False
            self.ptt(False)
            self.push_tx()

    def nbtv_correct(self):
        off = self.eng.nbtv.afc
        if self.v_mode.get() not in ("USB", "LSB"):
            self.log("NBTV: Correct works in USB or LSB")
            return
        self.set_tune(int(round(self.tune_hz + (off if self.v_mode.get() == "USB" else -off))))
        with self.eng.nbtv.lock:
            self.eng.nbtv.afc -= round(off)

    def nbtv_save(self, path=None, img=None):
        if img is None:
            img = self.nbtv_display_image()
        if img is None:
            self.log("NBTV: no picture yet")
            return
        if path is None:
            if filedialog is None:
                return
            os.makedirs(self.NBTV_DIR, exist_ok=True)
            path = filedialog.asksaveasfilename(
                parent=self.root, title="Save NBTV frame", initialdir=self.NBTV_DIR, defaultextension=".png",
                initialfile=time.strftime("%Y%m%d_%H%M%S_") + self.v_nbtv_mode.get().replace(" ", "") + ".png",
                filetypes=[("PNG", "*.png"), ("JPEG", "*.jpg"), ("Bitmap", "*.bmp"), ("PPM", "*.ppm")])
            if not path:
                return
        L = NbtvLayout(self.v_nbtv_mode.get())
        k = max(1, 384 // max(L.w, L.h))                     # save it big enough to see
        try:
            save_image(np.repeat(np.repeat(img, k, axis=0), k, axis=1), path)
            if self.nbtv_rec_dir is None:
                self.log("NBTV: saved %s" % path)
        except Exception as e:
            self.log("NBTV: cannot save %s: %s" % (path, e))

    def nbtv_record(self):
        if self.v_nbtv_rec.get():
            self.nbtv_rec_dir = os.path.join(self.NBTV_DIR, time.strftime("%Y%m%d_%H%M%S_")
                                             + self.v_nbtv_mode.get().replace(" ", ""))
            try:
                os.makedirs(self.nbtv_rec_dir, exist_ok=True)
            except OSError as e:
                self.log("NBTV: cannot record: %s" % e)
                self.v_nbtv_rec.set(0)
                self.nbtv_rec_dir = None
                return
            self.nbtv_rec_n = 0
            self.log("NBTV: recording every received frame to %s" % self.nbtv_rec_dir)
        else:
            if self.nbtv_rec_dir:
                self.log("NBTV: %d frames recorded in %s" % (self.nbtv_rec_n, self.nbtv_rec_dir))
            self.nbtv_rec_dir = None

    def nbtv_display_image(self):
        rx = self.eng.nbtv
        if self.v_nbtv_view.get() == "TX":
            return self.nbtv_tx_img
        if self.v_nbtv_avg.get() and rx.averaged() is not None:
            return rx.averaged()
        return rx.img

    def nbtv_tick(self):
        rx = self.eng.nbtv
        if not self.eng.nbtv_on:
            return
        while not rx.events.empty():
            ev = rx.events.get()
            if ev[0] == "frame":
                self.nbtv_last = ev[1]
                if self.nbtv_rec_dir:
                    self.nbtv_rec_n += 1
                    self.nbtv_save(os.path.join(self.nbtv_rec_dir, "frame_%04d.png" % self.nbtv_rec_n),
                                   rx.averaged() if self.v_nbtv_avg.get() else ev[1])
        tx = self.eng.nbtv_tx
        if self.nbtv_txing and not (self.eng.tx_want or self.eng.tx_on):
            tx.abort()
            self.nbtv_txing = False
            self.push_tx()
            self.log("NBTV: transmit stopped")
        if self.nbtv_txing:
            if self.v_nbtv_src.get() == "Screen" and tx.need_frame:
                tx.need_frame = False
                self.nbtv_grab()                          # fresh screen picture for the next frame
            self.nbtv_stat.config(text=("Sending %s   frame %d" % (self.v_nbtv_mode.get(), tx.frames))
                                  if self.eng.tx_on else "Waiting for the radio to switch to TX ...")
        else:
            self.nbtv_stat.config(text=rx.status() if self.eng.running else "Press Start to receive")
        self.nbtv_redraw()
        self.draw_nbtv_tuning()

    def nbtv_redraw(self):
        c = self.nv
        W, H = max(20, c.winfo_width() or 0), max(20, c.winfo_height() or 0)
        rx = self.eng.nbtv
        view = self.v_nbtv_view.get()
        img = self.nbtv_display_image()
        key = (view, rx.version if view == "RX" else id(img), W, H, self.v_nbtv_avg.get(), self.v_nbtv_neon.get())
        if key == self.nv_key:
            return
        self.nv_key = key
        if img is None:
            return
        L = rx.L if view == "RX" else NbtvLayout(self.v_nbtv_mode.get())
        if L.baird and self.v_nbtv_neon.get():
            # the orange-pink glow of the neon lamp in a Baird televisor
            y = img.astype(np.float64).mean(axis=2) / 255.0
            img = (np.stack([y * 255, y * 150, y * 90], axis=-1)).astype(np.uint8)
        h, w = img.shape[:2]
        s = min(W / float(w), H / float(h))
        dw, dh = max(1, int(w * s)), max(1, int(h * s))
        # smooth enlargement (these pictures are tiny): bilinear
        yy = np.clip((np.arange(dh) + 0.5) / s - 0.5, 0, h - 1)
        xx = np.clip((np.arange(dw) + 0.5) / s - 0.5, 0, w - 1)
        y0, x0 = np.floor(yy).astype(int), np.floor(xx).astype(int)
        y1, x1 = np.minimum(y0 + 1, h - 1), np.minimum(x0 + 1, w - 1)
        fy, fx = (yy - y0)[:, None, None], (xx - x0)[None, :, None]
        f = img.astype(np.float64)
        a = (f[y0][:, x0] * (1 - fx) + f[y0][:, x1] * fx) * (1 - fy) + \
            (f[y1][:, x0] * (1 - fx) + f[y1][:, x1] * fx) * fy
        a = np.ascontiguousarray(a.astype(np.uint8))
        self.nv_img = tk.PhotoImage(data=b"P6 %d %d 255\n" % (dw, dh) + a.tobytes(), format="PPM")
        c.itemconfig(self.nv_item, image=self.nv_img)
        c.coords(self.nv_item, (W - dw) // 2, (H - dh) // 2)

    def draw_nbtv_tuning(self):
        c = self.nt
        rx = self.eng.nbtv
        if not self.eng.running:
            return
        W, H = max(50, c.winfo_width() or 0), int(c.cget("height"))
        f, db = rx.spectrum()
        self.nt_avg = db if self.nt_avg is None or len(self.nt_avg) != len(db) else 0.6 * self.nt_avg + 0.4 * db
        lo, hi = 300.0, 2800.0
        fx = lo + (np.arange(W) + 0.5) / W * (hi - lo)
        row = np.interp(fx, f, self.nt_avg)
        top = float(np.max(row))
        lvl = np.clip((row - (top - 50.0)) / 50.0, 0.0, 1.0)
        wh = H - 14
        if self.nt_arr is None or self.nt_arr.shape[:2] != (wh, W):
            self.nt_arr = np.zeros((wh, W, 3), dtype=np.uint8)
        self.nt_arr[1:] = self.nt_arr[:-1]
        self.nt_arr[0] = self.lut[(lvl * 255).astype(np.uint8)]
        self.nt_img = tk.PhotoImage(data=b"P6 %d %d 255\n" % (W, wh) + self.nt_arr.tobytes(), format="PPM")
        c.itemconfig(self.nt_item, image=self.nt_img)
        c.coords(self.nt_item, 0, 14)
        c.delete("ov")
        pts = np.empty(2 * W)
        pts[0::2] = np.arange(W)
        pts[1::2] = 13 - lvl * 12
        c.create_line(*pts.tolist(), fill="#7fd1ff", tags="ov")
        L = rx.L
        X = lambda fr: (fr - lo) / (hi - lo) * W
        c.create_rectangle(X(L.lo + rx.afc), 0, X(L.hi + rx.afc), H, outline="#4caf50", tags="ov")
        c.create_line(X(NBTV_CENTRE), 0, X(NBTV_CENTRE), H, fill="#e5c07b", dash=(2, 3), tags="ov")
        c.create_line(X(NBTV_CENTRE + rx.afc), 0, X(NBTV_CENTRE + rx.afc), H, fill="#e05252", tags="ov")
        c.create_text(X(NBTV_CENTRE) + 2, 1, text="pilot", anchor="nw", fill="#e5c07b", font=self.F_SMALL,
                      tags="ov")
        off = rx.afc
        ok = rx.pilot_db > 6 and rx.lock_q > 0.35
        self.nt_off.config(text="%+.1f Hz" % off if ok else "no pilot",
                           fg=("#4caf50" if abs(off) < 5 else "#e5c07b" if abs(off) < 20 else "#e05252")
                           if ok else self.MUTED)

    def sstv_tick(self):
        rx = self.eng.sstv
        while not rx.events.empty():
            ev = rx.events.get()
            if ev[0] == "start":
                self.log("SSTV: receiving %s" % ev[1])
                self.v_sstv_view.set("RX")
            elif ev[0] == "done":
                self.sstv_last, self.sstv_last_mode = ev[2], ev[1]
                self.log("SSTV: %s picture %s" % (ev[1], "received" if ev[3] else "ended early"))
                if ev[3] and self.v_sstv_auto.get():
                    try:
                        os.makedirs(self.SSTV_DIR, exist_ok=True)
                        self.sstv_save(os.path.join(self.SSTV_DIR, time.strftime("%Y%m%d_%H%M%S_")
                                                    + ev[1].replace(" ", "") + ".png"))
                    except OSError as e:
                        self.log("SSTV: auto save failed: %s" % e)
        if self.sstv_txing and not (self.eng.tx_want or self.eng.tx_on):
            self.eng.sstv_tx.abort()                      # TX ended (TX button, hardware refused ...)
            self.sstv_txing = False
            self.push_tx()
            self.log("SSTV: transmit stopped")
        if self.sstv_txing and self.eng.sstv_tx.tx_done():
            self.eng.sstv_tx.tx_active = False
            self.sstv_txing = False
            self.ptt(False)
            self.push_tx()
            self.log("SSTV: picture sent")
        if self.sstv_txing:
            self.sstv_stat.config(text=("Sending %s  %d %%" % (self.v_sstv_txmode.get(),
                                                               100 * self.eng.sstv_tx.progress()))
                                  if self.eng.tx_on else "Waiting for the radio to switch to TX ...")
        elif self.eng.sstv_on:
            self.sstv_stat.config(text=rx.status() if self.eng.running else "Press Start to receive")
        else:
            self.sstv_stat.config(text="SSTV off")
        self.sstv_redraw()
        if self.eng.sstv_on:
            self.draw_sstv_tuning()

    def sstv_redraw(self):
        c = self.sv
        W, H = max(20, c.winfo_width() or 0), max(20, c.winfo_height() or 0)
        rx = self.eng.sstv
        view = self.v_sstv_view.get()
        if view == "RX":
            img = rx.img if rx.img is not None else self.sstv_last
            mark = rx.line * (2 if rx.L is not None and rx.L.kind == "pd" else 1) if rx.state == "rx" else None
            key = ("RX", rx.version, id(img), W, H)
        else:
            img = self.sstv_tx_img
            mark = None
            if self.sstv_txing and img is not None:
                L = SstvLayout(self.v_sstv_txmode.get())
                mark = int(img.shape[0] * clamp((self.eng.sstv_tx.progress() * (L.total_s + 1.7) - 1.7)
                                                / L.total_s, 0.0, 1.0))
            key = ("TX", id(img), mark, W, H)
        if key == self.sv_key:
            return
        self.sv_key = key
        c.delete("ov")
        if img is None:
            c.itemconfig(self.sv_item, image="")
            c.create_text(W / 2, H / 2, text="no picture yet", fill=self.MUTED, tags="ov")
            return
        h, w = img.shape[:2]
        s = min(W / float(w), H / float(h))
        dw, dh = max(1, int(w * s)), max(1, int(h * s))
        ys = np.minimum((np.arange(dh) / s).astype(int), h - 1)
        xs = np.minimum((np.arange(dw) / s).astype(int), w - 1)
        a = np.ascontiguousarray(img[ys][:, xs])
        self.sv_img = tk.PhotoImage(data=b"P6 %d %d 255\n" % (dw, dh) + a.tobytes(), format="PPM")
        x0, y0 = (W - dw) // 2, (H - dh) // 2
        c.itemconfig(self.sv_item, image=self.sv_img)
        c.coords(self.sv_item, x0, y0)
        if mark is not None and 0 < mark < h:
            y = y0 + mark * s
            c.create_line(x0, y, x0 + dw, y, fill="#e05252", tags="ov")

    def draw_sstv_tuning(self):
        c = self.st
        rx = self.eng.sstv
        if not self.eng.running:
            return
        W, H = max(50, c.winfo_width() or 0), int(c.cget("height"))
        f, db = rx.spectrum()
        self.st_avg = db if self.st_avg is None or len(self.st_avg) != len(db) else 0.5 * self.st_avg + 0.5 * db
        lo, hi = 1000.0, 2500.0
        fx = lo + (np.arange(W) + 0.5) / W * (hi - lo)
        row = np.interp(fx, f, self.st_avg)
        top = float(np.max(row))
        lvl = np.clip((row - (top - 50.0)) / 50.0, 0.0, 1.0)
        wh = H - 14
        if self.st_arr is None or self.st_arr.shape[:2] != (wh, W):
            self.st_arr = np.zeros((wh, W, 3), dtype=np.uint8)
        self.st_arr[1:] = self.st_arr[:-1]
        self.st_arr[0] = self.lut[(lvl * 255).astype(np.uint8)]
        self.st_img = tk.PhotoImage(data=b"P6 %d %d 255\n" % (W, wh) + self.st_arr.tobytes(), format="PPM")
        c.itemconfig(self.st_item, image=self.st_img)
        c.coords(self.st_item, 0, 14)
        c.delete("ov")
        pts = np.empty(2 * W)
        pts[0::2] = np.arange(W)
        pts[1::2] = 13 - lvl * 12
        c.create_line(*pts.tolist(), fill="#7fd1ff", tags="ov")
        for fr, col, t in ((1200, "#e05252", "S"), (1500, "#9aa4ae", "B"), (1900, "#e5c07b", "V"),
                           (2300, "#ffffff", "W")):
            x = (fr + rx.offset - lo) / (hi - lo) * W
            c.create_line(x, 0, x, H, fill=col, dash=(2, 3), tags="ov")
            c.create_text(x + 2, 1, text=t, anchor="nw", fill=col, font=self.F_SMALL, tags="ov")
        off = rx.offset
        self.st_off.config(text="%+.0f Hz" % off,
                           fg="#4caf50" if abs(off) < 20 else "#e5c07b" if abs(off) < 60 else "#e05252")

    def on_digi_mode(self):
        m = self.eng.modem
        mode = self.v_dmode.get()
        for w in self.dsub_box.winfo_children():
            w.pack_forget()
        if mode == "DominoEX":
            self.dsub_lbl.config(text="speed")
            self.dsub_lbl.pack(side=tk.LEFT)
            self.cb_dspeed.pack(side=tk.LEFT, padx=2)
        elif mode == "CW":
            self.dsub_lbl.config(text="wpm")
            self.dsub_lbl.pack(side=tk.LEFT)
            self.sp_wpm.pack(side=tk.LEFT, padx=2)
        try:
            wpm = int(float(self.v_dwpm.get()))
        except ValueError:
            wpm = 20
        m.set_mode(mode, dom_speed=self.v_dspeed.get(), cw_wpm=clamp(wpm, 5, 60))
        m.afc = bool(self.v_afc.get())
        self.ui.update(dmode=mode, dspeed=self.v_dspeed.get(), dwpm=wpm, dafc=int(self.v_afc.get()))

    def digi_click(self, e):
        W = max(50, self.dal.winfo_width())
        m = self.eng.modem
        f = m.f0 + (e.x / float(W) - 0.5) * self.dal_span
        m.f0 = clamp(f, 100.0, 3000.0)
        m.find(near=m.f0, span=40.0 if m.mode == "PSK31" else 60.0)   # snap onto the signal

    def digi_find(self):
        self.eng.modem.find()

    def digi_centre_rf(self):
        """Retune the receiver so the digital signal sits at 1000 Hz audio."""
        m = self.eng.modem
        d = m.f0 - 1000.0
        if self.v_mode.get() == "LSB":
            d = -d
        elif self.v_mode.get() not in ("USB", "LSB"):
            self.log("Centre RF works in USB or LSB")
            return
        self.set_tune(int(round(self.tune_hz + d)))
        m.f0 = 1000.0

    def digi_send(self):
        text = self.dtx.get("1.0", tk.END).rstrip("\n")
        if not text.strip():
            return
        if getattr(self, "sstv_txing", False) or getattr(self, "nbtv_txing", False):
            self.log("already transmitting SSTV / NBTV")
            return
        if self.v_mode.get() not in ("USB", "LSB"):
            self.v_mode.set("USB")                            # digital modes go out as audio on SSB
            self.on_mode()
            self.log("digital modes: switched to USB")
        self.dtx.delete("1.0", tk.END)
        self.digi_tx = True
        self.push_tx()
        self.eng.modem.send(text + (" " if not text.endswith(" ") else ""))
        self.ptt(True)
        if not self.eng.tx_want and not self.eng.tx_on:      # TX was refused (not started, no output)
            self.eng.modem.abort()
            self.digi_tx = False
            self.push_tx()

    def digi_stop(self):
        self.eng.modem.abort()
        if self.digi_tx:
            self.digi_tx = False
            self.ptt(False)
            self.push_tx()

    def digi_tick(self):
        m = self.eng.modem
        # decoded and sent text
        while not m.rx_text.empty():
            self.drx.insert(tk.END, m.rx_text.get())
            self.drx.see(tk.END)
        while not m.sent.empty():
            self.drx.insert(tk.END, m.sent.get() + "\n", "tx")
            self.drx.see(tk.END)
        if not self.eng.modem_on:
            return
        if self.digi_tx and not (self.eng.tx_want or self.eng.tx_on):
            m.abort()
            self.digi_tx = False
            self.push_tx()
        if self.digi_tx and m.tx_done():
            m.tx_active = False
            self.digi_tx = False
            self.ptt(False)                                   # message finished: back to receive
            self.push_tx()
        q = m.quality()
        self.dq.coords(self.dq_bar, 0, 0, 60 * clamp(q, 0.0, 1.0), 12)
        self.dq.itemconfig(self.dq_bar, fill="#4caf50" if q > 0.6 else "#e5c07b" if q > 0.3 else "#e05252")
        self.dfreq_lbl.config(text="%.0f Hz" % m.f0)
        self.dstate.config(text="sending ..." if self.digi_tx else "")
        self.draw_alignment()

    def draw_alignment(self):
        """Waterfall + spectrum of the audio around the decoder frequency, with the mode's width."""
        m = self.eng.modem
        spec = m.spec
        if spec is None or not self.eng.running:
            return
        c = self.dal
        W, H = max(50, c.winfo_width() or 0), int(c.cget("height"))
        binw = DIGI_AUDIO / float(len(m.ring))
        f = np.arange(len(spec)) * binw
        fx = m.f0 + (np.arange(W) / float(W) - 0.5) * self.dal_span
        row = np.interp(fx, f, spec, left=-150, right=-150)
        top = float(np.max(spec)) if len(spec) else -20.0
        lvl = (np.clip((row - (top - 60.0)) / 60.0, 0.0, 1.0) * 255).astype(np.uint8)
        wh = H - 16
        if self.dal_arr is None or self.dal_arr.shape[:2] != (wh, W):
            self.dal_arr = np.zeros((wh, W, 3), dtype=np.uint8)
        self.dal_arr[1:] = self.dal_arr[:-1]
        self.dal_arr[0] = self.lut[lvl]
        ppm = b"P6 %d %d 255\n" % (W, wh) + self.dal_arr.tobytes()
        self.dal_img = tk.PhotoImage(data=ppm, format="PPM")
        c.itemconfig(self.dal_item, image=self.dal_img)
        c.coords(self.dal_item, 0, 16)
        # spectrum line on top, mode width and centre
        c.delete("ov")
        ys = 15 - np.clip((row - (top - 60.0)) / 60.0, 0.0, 1.0) * 14
        pts = np.empty(2 * W)
        pts[0::2] = np.arange(W)
        pts[1::2] = ys
        c.create_line(*pts.tolist(), fill="#7fd1ff", tags="ov")
        bw = m.bandwidth()
        x0 = W / 2.0 - bw / self.dal_span * W / 2.0
        x1 = W / 2.0 + bw / self.dal_span * W / 2.0
        c.create_rectangle(x0, 0, x1, H, outline="#e05252", tags="ov")
        c.create_line(W / 2.0, 0, W / 2.0, H, fill="#e05252", dash=(2, 2), tags="ov")

    # ------------------------------------------------------------ station, title, help
    def set_title(self):
        self.root.title("%s %s" % (APP, VERSION))

    def show_bc_info(self, name, lo, hi):
        self.bc_win.show(name, lo, hi)

    def bc_follow_tune(self):
        """Leaving the broadcast bands brings the tabs back; tuning into another SW band follows it."""
        p = self.bc_win
        if p is None or not p.shown:
            return
        khz = self.tune_hz / 1000.0
        for name, lo, hi in SW_BROADCAST:
            if lo <= khz <= hi:
                if p.band is None or p.band[0] != name:
                    p.show(name, lo, hi)
                else:
                    p.mark_tuned()
                return
        p.back()

    def station_text(self):
        c = self.cfg
        parts = [station(c, k) for k in ("callsign", "op_name", "qth", "grid")]
        return "   ".join(p for p in parts if p)

    def station_changed(self):
        self.set_title()
        self.station_lbl.config(text=self.station_text())

    def digi_macro(self, which):
        c = self.cfg
        call = station(c, "callsign")
        if not call:
            call = "NOCALL"
            self.log("enter your call sign in Settings > Station")
        first = station(c, "op_name").split(" ")[0]
        if which == "CQ":
            t = "CQ CQ CQ de %s %s %s pse k " % (call, call, call)
        elif which == "Info":
            bits = []
            if first:
                bits.append("Name %s" % first)
            if station(c, "qth"):
                bits.append("QTH %s" % station(c, "qth"))
            if station(c, "grid"):
                bits.append("Loc %s" % station(c, "grid"))
            bits.append("Rig ExSDR")
            t = " - ".join(bits) + " "
        else:
            t = "Thanks for the QSO, 73 de %s sk " % call
        if self.v_dmode.get() == "CW":
            t = t.upper().replace(" - ", " = ")
        self.dtx.insert(tk.END, t)
        self.dtx.focus_set()

    def open_help(self, topic=None):
        if getattr(self, "help_win", None) is not None:
            try:
                self.help_win.lift()
                return
            except Exception:
                self.help_win = None
        w = tk.Toplevel(self.root)
        self.help_win = w
        w.title("%s help" % APP)
        w.configure(bg=self.BG)

        def close():
            self.help_win = None
            w.destroy()
        w.protocol("WM_DELETE_WINDOW", close)
        w.bind("<Escape>", lambda e: close())
        head = tk.Frame(w, bg=self.BG)
        head.pack(side=tk.TOP, fill=tk.X, padx=10, pady=(8, 2))
        try:
            self.help_logo = tk.PhotoImage(data=LOGO_PNG).subsample(2, 2)
            tk.Label(head, image=self.help_logo, bg=self.BG, bd=0).pack(side=tk.LEFT, padx=(0, 10))
        except Exception:
            self.help_logo = None
        tk.Label(head, text="%s %s" % (APP, VERSION), bg=self.BG, fg=self.FG, font=self.F_BOLD).pack(side=tk.LEFT)
        tk.Label(head, text="   by %s" % AUTHOR, bg=self.BG, fg=self.ACC, font=self.F_BOLD).pack(side=tk.LEFT)
        tk.Label(head, text=CREDIT, bg=self.BG, fg=self.MUTED, font=self.F_SMALL).pack(side=tk.RIGHT)
        bar = tk.Frame(w, bg=self.BG)
        bar.pack(side=tk.BOTTOM, fill=tk.X, padx=10, pady=6)
        self.btn(bar, "Close", close).pack(side=tk.RIGHT)
        body = tk.Frame(w, bg=self.BG)
        body.pack(side=tk.TOP, fill=tk.BOTH, expand=True, padx=10)
        lb = tk.Listbox(body, width=18, bg=self.FIELD, fg=self.FG, selectbackground=self.SEL,
                        selectforeground=self.FG, bd=0, highlightthickness=1, highlightbackground=self.BORDER,
                        activestyle="none", exportselection=False)
        lb.pack(side=tk.LEFT, fill=tk.Y)
        for name, _ in HELP:
            lb.insert(tk.END, "  " + name)
        txt = tk.Text(body, width=86, height=30, bg=self.FIELD, fg=self.FG, bd=0, wrap=tk.WORD, padx=12,
                      pady=8, highlightthickness=1, highlightbackground=self.BORDER, font=self.F)
        sb = ttk.Scrollbar(body, orient=tk.VERTICAL, command=txt.yview)
        sb.pack(side=tk.RIGHT, fill=tk.Y)
        txt.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(6, 0))
        txt.config(yscrollcommand=sb.set)
        txt.tag_configure("title", font=self.F_BOLD, foreground=self.ACC, spacing3=6)

        def show(i):
            name, body_ = HELP[i]
            body_ = body_.format(app=APP, version=VERSION, author=AUTHOR, credit=CREDIT)
            txt.config(state="normal")
            txt.delete("1.0", tk.END)
            txt.insert(tk.END, name + "\n", "title")
            if name == "About":
                try:
                    self.help_big_logo = tk.PhotoImage(data=LOGO_PNG)
                    txt.image_create(tk.END, image=self.help_big_logo)
                    txt.insert(tk.END, "\n\n")
                except Exception:
                    pass
            txt.insert(tk.END, body_)
            txt.config(state="disabled")
            lb.selection_clear(0, tk.END)
            lb.selection_set(i)
        lb.bind("<<ListboxSelect>>", lambda e: show(lb.curselection()[0]) if lb.curselection() else None)
        names = [n for n, _ in HELP]
        show(names.index(topic) if topic in names else 0)
        fit_to_screen(w, margin_h=120)

    def toggle_log(self, show=None):
        show = (not self.log_shown) if show is None else show
        if show and not self.log_shown:
            self.log_card.pack(side=tk.BOTTOM, fill=tk.X, padx=7, pady=(0, 3), before=self.panel)
        elif not show and self.log_shown:
            self.log_card.pack_forget()
        self.log_shown = show
        if show:
            self.log_unseen = 0
        self.btn_log.config(text="Hide log" if show else "Show log",
                            fg=self.FG, highlightbackground=self.BORDER)

    # ---------------------------------------------------------------- S-meter
    SM_X0, SM_X1 = 8, 250            # S0 ... S9+60

    def sm_x(self, db_s9):
        """x for a level in dB relative to S9 (S9 at 60 % of the scale)."""
        x0, x1 = self.SM_X0, self.SM_X1
        if db_s9 <= 0:
            t = 0.6 * clamp((db_s9 + 54.0) / 54.0, 0.0, 1.0)
        else:
            t = 0.6 + 0.4 * clamp(db_s9 / 60.0, 0.0, 1.0)
        return x0 + (x1 - x0) * t

    def build_smeter(self):
        c = self.meter
        for s_ in (1, 3, 5, 7, 9):
            x = self.sm_x((s_ - 9) * 6.0)
            c.create_line(x, 22, x, 27, fill=self.SCALE_TXT)
            c.create_text(x, 31, text=str(s_), fill=self.SCALE_TXT, font=self.F_SMALL)
        for d in (20, 40, 60):
            x = self.sm_x(d)
            c.create_line(x, 22, x, 27, fill="#c06060")
            c.create_text(x, 31, text="+%d" % d, fill="#c06060", font=self.F_SMALL)
        c.create_rectangle(self.SM_X0, 6, self.SM_X1, 18, outline="#2c3640", fill="#0b0f13")
        self.sm_bar = c.create_rectangle(self.SM_X0, 7, self.SM_X0, 17, outline="", fill=self.ACC)
        self.sm_bar2 = c.create_rectangle(self.sm_x(0), 7, self.sm_x(0), 17, outline="", fill="#e05252")
        self.sm_txt = c.create_text(self.SM_X1 + 8, 12, text="", anchor="w", fill=self.DIGIT, font=self.F_BOLD)
        self.sm_dbfs = c.create_text(self.SM_X1 + 8, 28, text="", anchor="w", fill=self.SCALE_TXT,
                                     font=self.F_SMALL)

    def draw_smeter(self, lvl):
        self.lvl_s = 0.7 * self.lvl_s + 0.3 * lvl
        d = self.lvl_s - float(self.cfg.get("s9_dbfs", -60.0))
        c = self.meter
        x = self.sm_x(d)
        x9 = self.sm_x(0)
        c.coords(self.sm_bar, self.SM_X0, 7, min(x, x9), 17)
        c.coords(self.sm_bar2, x9, 7, max(x, x9), 17)
        if d <= 0:
            txt = "S%d" % int(clamp(round(9 + d / 6.0), 0, 9))
        else:
            txt = "S9+%d" % int(round(d))
        c.itemconfig(self.sm_txt, text=txt)
        c.itemconfig(self.sm_dbfs, text="%.0f dBFS" % self.lvl_s)

    # ----------------------------------------------------------- AF spectrum
    def draw_af(self):
        spec = self.eng.rx.af_spec
        if spec is None:
            return
        c = self.af
        W, H = int(c.cget("width")), int(c.cget("height"))
        rx = self.eng.rx
        f1, f2 = rx.band(rx.p)
        sh = rx.shift(rx.p)
        lo_a, hi_a = sorted((abs(f1 + sh), abs(f2 + sh)))
        if rx.p["mode"] in CARRIER_MODES + ("FM",):
            lo_a, hi_a = 0.0, max(abs(f1), abs(f2))
        fmax = clamp(math.ceil((hi_a * 1.25 + 500) / 1000.0) * 1000.0, 3000.0, rx.arate / 2.0)
        n = len(spec)
        k = max(2, int(n * fmax / (rx.arate / 2.0)))
        seg = spec[:k]
        self.af_s = seg if self.af_s is None or len(self.af_s) != len(seg) else 0.6 * self.af_s + 0.4 * seg
        xs = np.linspace(0, W, len(seg))
        ref, rng = self.fget("af_ref", -10.0), max(10.0, self.fget("af_rng", 80.0))
        ys = np.clip((ref - self.af_s) / rng, 0.0, 1.0) * (H - 14)
        pts = np.empty(2 * len(seg))
        pts[0::2] = xs
        pts[1::2] = ys
        c.coords(self.af_line, *pts.tolist())
        # audio waterfall: newest line on top, same frequency scale as the audio spectrum above
        ww, wh = int(self.afw.cget("width")), int(self.afw.cget("height"))
        row = np.interp(np.linspace(0, len(seg) - 1, ww), np.arange(len(seg)), seg)
        lvl = (np.clip((row - (ref - rng)) / rng, 0.0, 1.0) * 255).astype(np.uint8)   # same scale as above
        self.afw_arr[1:] = self.afw_arr[:-1]
        self.afw_arr[0] = self.lut[lvl]
        lo_x, hi_x = int(lo_a / fmax * (ww - 1)), int(min(hi_a / fmax, 1.0) * (ww - 1))
        self.afw_arr[0, [lo_x, hi_x]] = (90, 140, 190)      # filter edges as thin lines
        ppm = b"P6 %d %d 255\n" % (ww, wh) + self.afw_arr.tobytes()
        self.afw_img = tk.PhotoImage(data=ppm, format="PPM")
        self.afw.itemconfig(self.afw_item, image=self.afw_img)
        c.coords(self.af_band, lo_a / fmax * W, 0, max(hi_a / fmax * W, lo_a / fmax * W + 1), H - 14)
        fa = rx.anf_freq
        if fa:
            xa = fa / fmax * W
            c.coords(self.af_anf, xa, 0, xa, H - 14)
        else:
            c.coords(self.af_anf, -5, 0, -5, 0)
        if getattr(self, "_af_fmax", None) != fmax:
            self._af_fmax = fmax
            c.delete("axis")
            step = 1000 if fmax <= 6000 else 2000
            f = 0
            while f <= fmax:
                x = f / fmax * W
                c.create_line(x, H - 14, x, H - 10, fill=self.SCALE_TXT, tags="axis")
                c.create_text(min(max(x, 6), W - 8), H - 5, text="%g" % (f / 1000.0), fill=self.SCALE_TXT,
                              font=self.F_SMALL, tags="axis")
                f += step
            c.create_text(W - 2, 2, text="kHz", anchor="ne", fill=self.SCALE_TXT, font=self.F_SMALL, tags="axis")

    # --------------------------------------------------------------- frequency
    # ------------------------------------------------------------ FM repeater shift
    RPT_SHIFT = {"10": 100000, "6": 1000000}      # Hz: 10 m 100 kHz, 6 m 1 MHz

    def rpt_band(self, hz=None):
        """(band name, low Hz, high Hz, shift Hz) of the 10 m / 6 m band at hz (band plan of the
        region in Settings), or None."""
        hz = self.tune_hz if hz is None else hz
        for name, lo, hi in band_plan(self.cfg):
            if name in self.RPT_SHIFT and lo * 1000 <= hz <= hi * 1000:
                return name, int(lo * 1000), int(hi * 1000), self.RPT_SHIFT[name]
        return None

    def rpt_offset(self, hz=None):
        """Repeater shift for this frequency (Hz), or 0 outside 10 m / 6 m."""
        b = self.rpt_band(hz)
        return b[3] if b else 0

    def tx_half_bw(self):
        """Half the transmitted bandwidth (Hz) - how close to a band edge the carrier may go."""
        try:
            w = float(self.v_width.get())
        except (ValueError, tk.TclError, AttributeError):
            w = 12000.0
        return w / 2.0 if self.v_mode.get() in ("FM",) + CARRIER_MODES else 0.0

    def rpt_problem(self):
        """Why the shifted transmit frequency may not be used ('' when it is fine)."""
        sh = self.tx_shift_hz()
        if not sh:
            return ""
        b = self.rpt_band()
        tx = self.tune_hz + sh
        h = self.tx_half_bw()
        if b is None or tx - h < b[1] or tx + h > b[2]:
            name, lo, hi = (b[0], b[1], b[2]) if b else ("?", 0, 0)
            return "TX %.3f MHz is outside the %s m band (%.3f - %.3f MHz)" % (tx / 1e6, name, lo / 1e6, hi / 1e6)
        return ""

    def tx_shift_hz(self):
        """How far the transmitter is from the receiver: FM repeater shift, otherwise 0."""
        d = self.vars["rpt"].get() if "rpt" in self.vars else "S"
        if self.v_mode.get() != "FM" or d == "S":
            return 0
        off = self.rpt_offset()
        return -off if d == "-" else off

    def on_rpt(self):
        self.update_rpt()

    def update_rpt(self):
        if not hasattr(self, "rpt_lbl"):
            return
        off = self.rpt_offset()
        usable = self.v_mode.get() == "FM" and off > 0
        for b in self.rpt_btns:
            b.config(state=tk.NORMAL if usable else tk.DISABLED)
        if not usable:
            self.rpt_lbl.config(text="10 m / 6 m FM only" if self.v_mode.get() == "FM" else "", fg=self.MUTED)
            return
        sh = self.tx_shift_hz()
        if sh == 0:
            self.rpt_lbl.config(text="simplex   (shift %s)" % ("100 kHz" if off == 100000 else "1 MHz"),
                                fg=self.MUTED)
        elif self.rpt_problem():
            self.rpt_lbl.config(text="TX %.3f MHz - outside band, no TX" % ((self.tune_hz + sh) / 1e6),
                                fg="#e05252")
        else:
            self.rpt_lbl.config(text="TX %.3f MHz  (%s)" % ((self.tune_hz + sh) / 1e6,
                                                         ("%+d MHz" % (sh // 1000000)) if abs(sh) >= 1000000
                                                         else ("%+d kHz" % (sh // 1000))),
                                fg=self.ACC)

    def update_freq_display(self):
        n = len(self.digits)
        s = "%0*d" % (n, int(self.tune_hz))
        lead = True
        for d, ch in zip(self.digits, s):                 # dim the leading zeros, like HDSDR
            lead = lead and ch == "0"
            d.config(text=ch, fg=self.DIGIT_DIM if lead else self.DIGIT)
        s = "%0*d" % (n, int(self.lo_khz * 1000))
        lead = True
        for d, ch in zip(self.lo_digits, s):
            lead = lead and ch == "0"
            d.config(text=ch, fg=self.DIGIT_OFF if lead else self.DIGIT_DIM)
        self.lo_label.config(text="offset %+.3f kHz" % ((self.tune_hz - self.lo_khz * 1000) / 1000.0))
        self.e_freq.delete(0, tk.END)
        self.e_freq.insert(0, "%.3f" % (self.tune_hz / 1000.0))
        self.highlight_band()
        self.update_rpt()

    # ------------------------------------------------------------------ bands
    BAND_COLS = 8

    def build_band_buttons(self):
        for w in self.band_box.winfo_children():
            w.destroy()
        self.band_btns = []
        row = 0
        for group, title, plan in (("ham", "Amateur bands (m)", band_plan(self.cfg)),
                                   ("bc", "Broadcast bands (m)", broadcast_plan(self.cfg))):
            tk.Label(self.band_box, text=title, bg=self.CARD, fg=self.MUTED, font=self.F_SMALL,
                     anchor="w").grid(row=row, column=0, columnspan=self.BAND_COLS, sticky="w",
                                      pady=(3 if row else 0, 0))
            row += 1
            for i, (name, lo, hi) in enumerate(plan):
                b = self.btn(self.band_box, name, lambda g=group, n=name: self.goto_band(n, g), 3)
                b.config(padx=2, pady=1)
                b.grid(row=row + i // self.BAND_COLS, column=i % self.BAND_COLS, padx=1, pady=1, sticky="ew")
                self.band_btns.append((b, lo, hi))
            row += (len(plan) + self.BAND_COLS - 1) // self.BAND_COLS
        if hasattr(self, "digits"):
            self.highlight_band()

    def goto_band(self, name, group="ham"):
        plan = band_plan(self.cfg) if group == "ham" else broadcast_plan(self.cfg)
        for n, lo, hi in plan:
            if n == name:
                break
        else:
            return
        hz = band_centre_hz(lo, hi)
        if not self.fmin_khz * 1000 <= hz <= self.fmax_khz * 1000:
            self.log("%s m band is outside what the %s hardware can tune (%.1f - %.1f MHz)"
                     % (name, hw_name(self.cfg), self.fmin_khz / 1000.0, self.fmax_khz / 1000.0))
            return
        m = self.v_mode.get()
        if group == "bc":
            if m not in CARRIER_MODES:                    # broadcast stations are AM
                self.v_mode.set("AM")
                self.on_mode()
        elif m in ("USB", "LSB"):                         # usual sideband for the ham band
            self.v_mode.set("LSB" if hz < 10000000 and name != "60" else "USB")
            self.on_mode()
        self.set_tune(hz, recenter=True)
        if group == "bc" and name != "MW" and self.cfg.get("bc_info", True):
            self.show_bc_info(name, lo, hi)
        what = "MW broadcast band" if name == "MW" else \
            ("%s m %s band" % (name, "amateur" if group == "ham" else "broadcast"))
        self.log("%s (%s - %s kHz): centre %.1f kHz" % (what, lo, hi, hz / 1000.0))

    def highlight_band(self):
        self.bc_follow_tune()
        f = self.tune_hz / 1000.0
        for b, lo, hi in getattr(self, "band_btns", []):
            inside = lo <= f <= hi
            b.config(bg=self.SEL if inside else (self.FIELD if self.dark else self.CARD))

    def lo_for(self, hz):
        """Hardware LO (kHz) that puts `hz` about lo_offset_hz above the LO."""
        want = (hz - self.cfg["lo_offset_hz"]) / 1000.0
        return int(clamp(int(round(want)), self.fmin_khz, self.fmax_khz))

    def set_tune(self, hz, recenter=False):
        hz = int(clamp(hz, self.fmin_khz * 1000, self.fmax_khz * 1000 + 999))
        off = hz - self.lo_khz * 1000
        if recenter or abs(off) > 0.35 * self.rate:
            lo = self.lo_for(hz)
            if lo != self.lo_khz:
                self.lo_khz = lo
                self.ser.set_freq_khz(lo)
        self.tune_hz = hz
        self.update_freq_display()
        self.push_rx()

    def lo_digit_step(self, i, direction):
        """Wheel / click on the LO display: move the hardware LO in kHz steps."""
        weight = 10 ** (len(self.lo_digits) - 1 - i)
        if weight < 1000:
            return                                        # the hardware tunes in 1 kHz steps
        lo = int(clamp(self.lo_khz + direction * weight // 1000, self.fmin_khz, self.fmax_khz))
        if lo == self.lo_khz:
            return
        self.lo_khz = lo
        self.ser.set_freq_khz(lo)
        if abs(self.tune_hz - lo * 1000) > 0.45 * self.rate:     # keep the tune frequency in view
            self.tune_hz = lo * 1000 + int(self.cfg["lo_offset_hz"])
        self.update_freq_display()
        self.push_rx()

    def digit_step(self, i, direction):
        self.set_tune(self.tune_hz + direction * 10 ** (len(self.digits) - 1 - i))

    def digit_click(self, e, i):
        self.digit_step(i, 1 if e.y < e.widget.winfo_height() / 2 else -1)

    def step_tune(self, direction):
        self.set_tune(self.tune_hz + direction * int(self.fget("step", 1000)))

    def freq_entered(self, ev=None):
        try:
            self.set_tune(int(round(float(self.e_freq.get()) * 1000.0)), recenter=True)
        except ValueError:
            self.update_freq_display()

    def recenter(self):
        self.set_tune(self.tune_hz, recenter=True)

    # ------------------------------------------------------------ control push
    def on_mode(self, initial=False):
        m = self.v_mode.get()
        if hasattr(self, "rpt_btns"):
            self.root.after_idle(self.update_rpt)
        lo, hi, st = WIDTH_RANGE[m]
        w = int(clamp(self.cfg["widths"].get(m, DEF_WIDTH[m]), lo, hi))
        self.sc_width.config(from_=lo, to=hi)
        self.v_width.set(w)
        lcs = self.cfg.setdefault("lowcuts", {})
        if not initial or m not in lcs:
            self.vars["lowcut"].set(float(lcs.get(m, 300 if m in ("USB", "LSB") else 0)))
        try:
            self.sc_lowcut.state(["disabled"] if m == "CW" else ["!disabled"])
            self.sc_mod.state(["!disabled"] if m in CARRIER_MODES + ("FM",) else ["disabled"])
            self.sc_stereo.state(["!disabled"] if m in STEREO_MODES else ["disabled"])
        except Exception:
            pass
        state = tk.NORMAL if m == "ECSS" else tk.DISABLED
        for b in self.sb_buttons:
            b.config(state=state)
        self.show_width()
        self.push_rx()
        self.push_tx()

    def on_width(self, ev=None):
        m = self.v_mode.get()
        lo, hi, st = WIDTH_RANGE[m]
        try:
            w = int(clamp(round(float(self.v_width.get()) / st) * st, lo, hi))   # snap to the step
        except (ValueError, tk.TclError):
            return
        if w != self.v_width.get():
            self.v_width.set(w)
        if self.cfg["widths"].get(m) == w and ev is not None and self.eng.rx.p.get("width") == w:
            return                                        # slider moved within the same step
        self.cfg["widths"][m] = float(w)
        self.show_width()
        self.push_rx()
        self.push_tx()                                    # TX filter follows the RX width

    def _stereo_indicator(self, top):
        self.stereo_lbl = tk.Label(top, text="STEREO", bg=self._bg(top), fg=self.BORDER, font=self.F_CAP)
        self.stereo_lbl.pack(side=tk.RIGHT, padx=6)

    def on_emphasis(self):
        self.push_rx()
        self.push_tx()

    def on_lowcut(self):
        lc = int(round(self.fget("lowcut", 0.0) / 10.0) * 10)
        self.cfg.setdefault("lowcuts", {})[self.v_mode.get()] = lc
        self.push_rx()
        self.push_tx()

    def on_filter_shape(self):
        self.push_rx()
        self.push_tx()

    def width_nudge(self, direction):
        lo, hi, st = WIDTH_RANGE[self.v_mode.get()]
        self.v_width.set(int(clamp(self.v_width.get() + direction * st, lo, hi)))
        self.on_width()

    def show_width(self):
        w = int(self.v_width.get())
        self.width_lbl.config(text="%.1f kHz" % (w / 1000.0) if w >= 1000 else "%d Hz" % w)

    def push_rx(self, *_):
        try:
            width = float(self.v_width.get())
        except ValueError:
            width = DEF_WIDTH[self.v_mode.get()]
        c = self.cfg
        self.eng.rx.set_params(
            mode=self.v_mode.get(), offset=float(self.tune_hz - self.lo_khz * 1000), width=width,
            lowcut=round(self.fget("lowcut", 300.0) / 10.0) * 10, pitch=c["cw_pitch_hz"], nb=bool(self.vars["nb"].get()),
            nb_thr=self.fget("nb_thr", 6.0), nr=bool(self.vars["nr"].get()), nr_amt=self.fget("nr_amt", 0.5),
            notch=bool(self.vars["notch"].get()), notch_hz=self.fget("notch_hz", 1000.0),
            agc=self.vars["agc"].get(), vol=self.fget("vol", 60.0), gain_db=self.fget("gain_db", 60.0),
            squelch=self.fget("squelch", -130.0), auto_iq=bool(self.vars["auto_iq"].get()),
            swap=c["rx_swap_iq"], invert=c["rx_invert_q"], gain_bal_db=c["rx_gain_bal_db"],
            phase_deg=c["rx_phase_deg"], fm_dev=c["fm_dev_hz"], ecss_sb=self.vars["ecss_sb"].get(),
            soft=self.vars["rolloff"].get() == "Soft", anf=bool(self.vars["anf"].get()),
            stereo_w=self.fget("stereo_w", 100.0) / 100.0, deemph=self.vars["emph"].get())

    def push_tx(self, *_):
        c = self.cfg
        src = {"Mic": "mic", "1 kHz tone": "tone", "Two-tone": "two"}.get(self.vars["src"].get(), "mic")
        if getattr(self, "digi_tx", False):
            src = "digi"
        elif getattr(self, "sstv_txing", False):
            src = "sstv"
        elif getattr(self, "nbtv_txing", False):
            src = "nbtv"
        mode = self.v_mode.get()
        lowcut, width, audio_bw = self.tx_band(mode)
        soft = self.cfg.get("tx_follow_rx", True) and self.vars["rolloff"].get() == "Soft"
        self.eng.tx.set_params(
            mode=mode, lowcut=lowcut, width=width, audio_bw=audio_bw, soft=soft,
            mic_gain_db=self.fget("mic_db", 20.0), drive=self.fget("drive", 0.4), source=src,
            carrier=bool(self.v_tune.get()), fm_dev=c["fm_dev_hz"], mod=self.fget("mod_pct", 80.0) / 100.0,
            comp=bool(self.vars["comp"].get()), comp_db=self.fget("comp_db", 10.0),
            limiter=bool(self.vars["lim"].get()), preemph=self.vars["emph"].get(),
            swap=c["tx_swap_iq"], invert=c["tx_invert_q"], gain_bal_db=c["tx_gain_bal_db"],
            phase_deg=c["tx_phase_deg"], dc_i=c["tx_dc_i"], dc_q=c["tx_dc_q"])

    def tx_band(self, mode):
        """TX audio band: (SSB low cut, SSB width, AM / FM audio bandwidth) in Hz.
        With 'TX bandwidth follows RX filter' the TX uses the RX width slider and low cut:
        SSB from low cut to low cut + width, AM / ECSS audio up to width / 2 (same RF bandwidth)."""
        c = self.cfg
        if not c.get("tx_follow_rx", True):
            return c["ssb_tx_lo"], max(100.0, c["ssb_tx_hi"] - c["ssb_tx_lo"]), 3000.0
        try:
            width = float(self.v_width.get())
        except (ValueError, tk.TclError):
            width = DEF_WIDTH.get(mode, 2400)
        lowcut = max(50.0, round(self.fget("lowcut", 300.0) / 10.0) * 10)
        if mode in CARRIER_MODES:
            return lowcut, width, width / 2.0
        if mode == "FM":
            return lowcut, width, 3000.0           # FM: deviation sets the RF width, audio stays 3 kHz
        return lowcut, max(100.0, width - lowcut), 3000.0   # SSB: low cut .. width, like the receiver

    def push_all(self):
        self.rate = self.eng.rx.rate
        self.push_rx()
        self.push_tx()

    # ---------------------------------------------------------------- hardware
    def apply_hardware(self):
        """Frequency range, display size and buttons for the chosen hardware."""
        h = hw_name(self.cfg)
        self.fmin_khz, self.fmax_khz = HW_LIMITS_KHZ[h]
        if len(getattr(self, "digits", [])) != self.ndigits():
            self.fill_displays()
        self.lo_khz = int(clamp(self.lo_khz, self.fmin_khz, self.fmax_khz))
        self.tune_hz = int(clamp(self.tune_hz, self.fmin_khz * 1000, self.fmax_khz * 1000 + 999))
        self.b_pre.config(state=tk.DISABLED if h == "None" else tk.NORMAL,
                          text={"HackRF": "RF amp", "RTL-SDR": "Auto gain", "Airspy HF+": "LNA",
                                "SDRplay": "AGC", "ADALM-Pluto": "AGC", "SoapySDR (other)": "AGC"}.get(h, "Pre-amp"))
        self.b_att.config(state=tk.NORMAL if h in ("ExSDR", "Airspy HF+", "SDRplay", "ADALM-Pluto",
                                                   "SoapySDR (other)") else tk.DISABLED)
        self.update_freq_display()

    def connect_serial(self):
        try:
            self.ser.open()
        except Exception as e:
            self.log("%s: %s" % ("serial" if hw_name(self.cfg) == "ExSDR" else hw_name(self.cfg), e))
            return
        self.hw_init()

    def hw_init(self):
        """Put the hardware in receive and read its settings; the screen follows the hardware."""
        if not self.ser.connected:
            return
        if isinstance(self.ser, HackRF):
            self.ser.set_freq_khz(self.lo_khz)       # the HackRF takes ExSDR's LO (it has no memory)
        self.ser.submit_txrx("RX")
        self.ser.query_all()

    def poll_hw(self):
        """Apply what the hardware reported (replies and unsolicited text) to the screen."""
        while True:
            try:
                ev = self.ser.events.get_nowait()
            except queue.Empty:
                break
            kind = ev[0]
            if kind == "freq":
                khz, latest = int(ev[1]), ev[2]
                if latest and khz != self.lo_khz and self.fmin_khz <= khz <= self.fmax_khz:
                    off = self.tune_hz - self.lo_khz * 1000     # keep the offset inside the window
                    self.lo_khz = khz
                    self.tune_hz = khz * 1000 + off
                    self.update_freq_display()
                    self.push_rx()
            elif kind == "pre":
                self.vars["pre"].set(1 if ev[1] else 0)
            elif kind == "att":
                self.vars["att"].set(1 if ev[1] else 0)
            elif kind == "hello":
                self.log("hardware started: %s - reading its settings" % ev[1])
                self.ser.submit_txrx("RX", 1.0)          # old firmware is still busy after the banner
                self.ser.query_all()
        if self.v_ptt.get() and not self.eng.tx_want and not self.eng.tx_on:
            self.v_ptt.set(0)                                    # TX was refused or cancelled

    def on_pre(self):
        self.ser.set_flag("P", bool(self.vars["pre"].get()))

    def on_att(self):
        self.ser.set_flag("A", bool(self.vars["att"].get()))

    def send_raw(self, ev=None):
        t = self.e_raw.get().strip()
        if t and self.ser.connected:
            self.ser.send_raw(t)
        elif t:
            self.log("serial not connected")

    # ------------------------------------------------------------------- T/R
    def on_ptt(self):
        self.ptt(bool(self.v_ptt.get()))

    def ptt(self, on):
        if on:
            if self.eng.tx_want:
                return
            if not getattr(self.ser, "CAN_TX", True):
                self.log("%s is a receiver only - no transmit" % hw_name(self.cfg))
                self.v_ptt.set(0)
                return
            if not (self.eng.running and self.eng.tx_ok):
                self.log("TX not available: press Start and check the I/Q output device")
                self.v_ptt.set(0)
                return
            shift = self.tx_shift_hz()
            why = self.rpt_problem()
            if why:
                self.log("not transmitting: %s - choose the other shift or Simplex" % why)
                self.v_ptt.set(0)
                return
            tx_hz = self.tune_hz + shift
            self.rx_lo_khz = self.lo_khz if shift else None   # where to go back to after TX
            lo = self.lo_for(tx_hz)
            if lo != self.lo_khz:
                self.lo_khz = lo
                self.ser.set_freq_khz(lo)
            self.eng.tx.set_params(offset=float(tx_hz - self.lo_khz * 1000))
            if shift:
                self.log("FM repeater: TX %.4f MHz, RX %.4f MHz" % (tx_hz / 1e6, self.tune_hz / 1e6))
            self.update_freq_display()
            self.push_rx()
            self.push_tx()
            self.eng.tx_begin()
            self.v_ptt.set(1)                            # the TX button shows it, whoever started it
        else:
            if self.eng.tx_want or self.eng.tx_on:
                self.eng.tx_end()
            self.eng.tx.set_params(key=False)
            self.v_ptt.set(0)
            back = getattr(self, "rx_lo_khz", None)
            if back is not None:                         # repeater shift: back to the receive frequency
                self.rx_lo_khz = None
                if back != self.lo_khz:
                    self.lo_khz = back
                    self.ser.set_freq_khz(back)
                self.update_freq_display()
                self.push_rx()

    def cw_key(self, down):
        self.eng.tx.set_params(key=bool(down))

    def space_down(self, ev):
        if self.v_mode.get() == "CW" and ev.widget.winfo_class() not in ("Entry", "TEntry", "TCombobox"):
            self.cw_key(True)

    def space_up(self, ev):
        self.cw_key(False)

    # ------------------------------------------------------------- run / stop
    def toggle_run(self):
        if self.eng.running:
            self.eng.stop()
            self.v_ptt.set(0)
        else:
            self.push_all()
            self.eng.start()
        self.btn_run.config(text="Stop" if self.eng.running else "Start")

    # ---------------------------------------------------------------- display
    def on_sp_resize(self, e):
        self.sw, self.sh = max(100, e.width), max(60, e.height)
        self.grid_key = None

    def on_wf_resize(self, e):
        self.ww, self.wh = max(100, e.width), max(40, e.height)
        self.wf_arr = None

    def view(self):
        zoom = max(1.0, self.fget("zoom", 1.0))
        span = self.rate / zoom
        off = self.tune_hz - self.lo_khz * 1000
        cen = off if zoom > 1 else 0.0
        cen = clamp(cen, -self.rate / 2.0 + span / 2.0, self.rate / 2.0 - span / 2.0)
        return cen, span

    def spec_click(self, e):
        cen, span = self.view()
        w = self.sw if e.widget is self.sp else self.ww
        frel = cen + (e.x / float(w) - 0.5) * span
        self.set_tune(int(round((self.lo_khz * 1000 + frel) / 10.0)) * 10)

    def segment(self, spec, W):
        N = len(spec)
        cen, span = self.view()
        i0 = max(0, int(round(N / 2.0 + (cen - span / 2.0) / self.rate * N)))
        i1 = min(N, int(round(N / 2.0 + (cen + span / 2.0) / self.rate * N)))
        seg = spec[i0:max(i1, i0 + 2)]
        if len(seg) >= 2 * W:
            k = len(seg) // W
            return seg[:k * W].reshape(W, k).max(axis=1)
        return np.interp(np.linspace(0, len(seg) - 1, W), np.arange(len(seg)), seg)

    def draw_grid(self):
        cen, span = self.view()
        ref, rng = self.fget("ref", -20.0), self.fget("rng", 100.0)
        key = (self.lo_khz, round(cen), round(span), ref, rng, self.sw, self.sh)
        if key == self.grid_key:
            return
        self.grid_key = key
        self.sp.delete("grid")
        W, H = self.sw, self.sh
        step = 1000.0
        for s in (1000, 2000, 5000, 10000, 20000, 50000, 100000, 200000):
            step = s
            if span / s <= 9:
                break
        f0 = self.lo_khz * 1000 + cen - span / 2.0
        f = math.ceil(f0 / step) * step
        while f < f0 + span:
            x = (f - f0) / span * W
            self.sp.create_line(x, 0, x, H, fill=self.GRID, tags="grid")
            self.sp.create_text(x + 3, H - 10, text="%.1f" % (f / 1000.0), fill=self.SCALE_TXT, anchor="w", tags="grid")
            f += step
        d = ref
        while d > ref - rng:
            y = (ref - d) / rng * H
            self.sp.create_line(0, y, W, y, fill=self.GRID, tags="grid")
            self.sp.create_text(3, y + 8, text="%d" % d, fill=self.SCALE_TXT, anchor="w", tags="grid")
            d -= 10
        self.sp.tag_lower("grid")

    def draw(self, spec, lvl):
        ref, rng = self.fget("ref", -20.0), self.fget("rng", 100.0)
        W, H = self.sw, self.sh
        self.draw_grid()
        seg = self.segment(spec, W)
        y = np.clip((ref - seg) / rng, 0.0, 1.0) * (H - 1)
        co = np.empty(2 * W)
        co[0::2] = np.arange(W)
        co[1::2] = y
        self.sp.coords(self.sp_line, *co.tolist())
        # pass band and tune marker
        rx = self.eng.rx
        cen, span = self.view()
        off = self.tune_hz - self.lo_khz * 1000
        f1, f2 = rx.band(rx.p)
        sh = rx.shift(rx.p)
        a = (off - sh + f1 - cen) / span + 0.5
        b = (off - sh + f2 - cen) / span + 0.5
        t = (off - cen) / span + 0.5
        self.sp.coords(self.sp_band, a * W, 0, max(b * W, a * W + 1), H)
        self.sp.coords(self.sp_tune, t * W, 0, t * W, H)
        # waterfall
        ww, wh = self.ww, self.wh
        if self.wf_arr is None or self.wf_arr.shape[1] != ww or self.wf_arr.shape[0] != wh:
            self.wf_arr = np.zeros((wh, ww, 3), dtype=np.uint8)
        wseg = self.segment(spec, ww)
        idx = (np.clip((wseg - (ref - rng)) / rng, 0.0, 1.0) * 255).astype(np.uint8)
        self.wf_arr[1:] = self.wf_arr[:-1]
        self.wf_arr[0] = self.lut[idx]
        ppm = b"P6 %d %d 255\n" % (ww, wh) + self.wf_arr.tobytes()
        self.wf_img = tk.PhotoImage(data=ppm, format="PPM")
        self.wf.itemconfig(self.wf_item, image=self.wf_img)
        self.draw_smeter(lvl)
        self.draw_af()

    # ---------------------------------------------------------------- VU meter
    VU_X0, VU_X1 = 34, 196

    def build_vu(self):
        c, x0, x1 = self.vu, self.VU_X0, self.VU_X1
        self.vu_bars = {}
        for row, name in enumerate(("MIC", "TX")):
            y0 = 3 + row * 17
            lab = c.create_text(4, y0 + 6, text=name, anchor="w", fill="#8a93a0", font=("Courier", 8, "bold"))
            c.create_rectangle(x0, y0, x1, y0 + 12, outline="#333", fill="#101010")
            for pct, col in ((70, "#5a5a20"), (90, "#5a2020")):          # yellow / red zones
                xp = x0 + (x1 - x0) * pct / 100.0
                c.create_line(xp, y0, xp, y0 + 12, fill=col)
            bar = c.create_rectangle(x0, y0 + 1, x0, y0 + 11, outline="", fill="#4caf50")
            peak = c.create_line(x0, y0, x0, y0 + 12, fill="#ffffff")
            txt = c.create_text(x1 + 4, y0 + 6, text="", anchor="w", fill="#d0d6dc", font=("Courier", 8))
            self.vu_bars[name] = [bar, peak, txt, y0, 0.0, 0.0, lab]     # ..., shown level, peak hold, label
        # stereo: the RX row splits into a left (top half) and a right (bottom half) bar
        y0 = self.vu_bars["TX"][3]
        self.vu_lr = {}
        for k, (ya, yb) in (("L", (y0 + 1, y0 + 6)), ("R", (y0 + 7, y0 + 12))):
            b = c.create_rectangle(x0, ya, x0, yb, outline="", fill="#4caf50", state="hidden")
            pk = c.create_line(x0, ya, x0, yb, fill="#ffffff", state="hidden")
            self.vu_lr[k] = [b, pk, ya, yb, 0.0, 0.0]

    def draw_vu(self):
        c, x0, x1 = self.vu, self.VU_X0, self.VU_X1
        run = self.eng.running
        tx = self.eng.tx_on
        # second row: TX I/Q level while transmitting, demodulated RX audio while receiving
        out = (self.eng.tx_level if tx else self.eng.rx.audio_level) if run else 0.0
        self.vu.itemconfig(self.vu_bars["TX"][6], text="TX" if tx else "RX",
                           fill="#ff6b6b" if tx else "#8a93a0")
        lr = self.eng.rx.audio_lr if (run and not tx) else None
        split = lr is not None
        self.vu.itemconfig(self.vu_bars["TX"][6], text="L/R" if split else ("TX" if tx else "RX"))
        for k in ("L", "R"):
            b, pk = self.vu_lr[k][:2]
            c.itemconfig(b, state="normal" if split else "hidden")
            c.itemconfig(pk, state="normal" if split else "hidden")
        if split:
            pcts = []
            for k, lvl in (("L", lr[0]), ("R", lr[1])):
                b, pk, ya, yb, shown, hold = self.vu_lr[k]
                shown = lvl if lvl > shown else shown * 0.8 + lvl * 0.2
                hold = lvl if lvl > hold else max(0.0, hold - 0.01)
                self.vu_lr[k][4:6] = [shown, hold]
                pct = min(shown, 1.0)
                c.coords(b, x0, ya, x0 + (x1 - x0) * pct, yb)
                c.itemconfig(b, fill="#4caf50" if pct < 0.7 else "#e5c07b" if pct < 0.9 else "#e53935")
                xp = x0 + (x1 - x0) * min(hold, 1.0)
                c.coords(pk, xp, ya, xp, yb)
                pcts.append(round(pct * 100))
            bar, peak, txt = self.vu_bars["TX"][:3]
            c.coords(bar, x0, 0, x0, 0)                           # the mono bar steps aside
            c.coords(peak, x0, 0, x0, 0)
            c.itemconfig(txt, text="%d/%d" % tuple(pcts), fill="#d0d6dc")
        for name, lvl in (("MIC", self.eng.mic_level if run else 0.0), ("TX", out)):
            if split and name == "TX":
                continue
            bar, peak, txt, y0, shown, hold = self.vu_bars[name][:6]
            shown = lvl if lvl > shown else shown * 0.8 + lvl * 0.2      # fast up, slow down
            hold = lvl if lvl > hold else max(0.0, hold - 0.01)
            self.vu_bars[name][4:6] = [shown, hold]
            pct = min(shown, 1.0)
            col = "#4caf50" if pct < 0.7 else "#e5c07b" if pct < 0.9 else "#e53935"
            c.coords(bar, x0, y0 + 1, x0 + (x1 - x0) * pct, y0 + 11)
            c.itemconfig(bar, fill=col)
            xp = x0 + (x1 - x0) * min(hold, 1.0)
            c.coords(peak, xp, y0, xp, y0 + 12)
            c.itemconfig(txt, text="CLIP" if hold >= 1.0 else "%3d%%" % round(pct * 100),
                         fill="#ff6b6b" if hold >= 1.0 else "#d0d6dc")

    # ------------------------------------------------------------- phase meter
    PM_CX, PM_CY, PM_R = 76, 70, 60

    def build_phase_meter(self):
        c, cx, cy, r = self.pm, self.PM_CX, self.PM_CY, self.PM_R
        box = (cx - r, cy - r, cx + r, cy + r)
        c.create_arc(*box, start=0, extent=180, style=tk.ARC, outline="#555", width=2)
        c.create_arc(*box, start=67.5, extent=45, style=tk.ARC, outline="#2e7d32", width=4)   # +-45 deg
        for deg in (-180, -135, -90, -45, 0, 45, 90, 135, 180):
            a = math.radians(90 - deg / 2.0)
            ln = 9 if deg % 90 == 0 else 5
            c.create_line(cx + (r - ln) * math.cos(a), cy - (r - ln) * math.sin(a),
                          cx + r * math.cos(a), cy - r * math.sin(a), fill="#888")
        for deg, x, y in ((-180, cx - r, cy + 1), (-90, cx - r * 0.72 - 6, cy - r * 0.72 - 2),
                          (0, cx, cy - r - 1), (90, cx + r * 0.72 + 6, cy - r * 0.72 - 2), (180, cx + r, cy + 1)):
            c.create_text(x, y, text=str(deg), fill="#8a93a0", font=("Courier", 7),
                          anchor="s" if deg == 0 else "center")
        self.pm_needle = c.create_line(cx, cy, cx, cy - r + 8, fill="#444", width=3)
        c.create_oval(cx - 3, cy - 3, cx + 3, cy + 3, fill="#888", outline="")
        self.pm_lamp = c.create_oval(150, 6, 162, 18, fill="#333", outline="#666")
        self.pm_lock = c.create_text(167, 12, text="LOCK", anchor="w", fill="#666", font=("Courier", 9, "bold"))
        self.pm_off = c.create_text(150, 38, text="ECSS off", anchor="w", fill="#8a93a0", font=("Courier", 9))
        self.pm_ph = c.create_text(150, 56, text="", anchor="w", fill="#8a93a0", font=("Courier", 9))

    def draw_phase_meter(self):
        c, cx, cy, r = self.pm, self.PM_CX, self.PM_CY, self.PM_R
        st = self.eng.rx.pll
        if self.v_mode.get() not in PLL_MODES or not self.eng.running or not st.get("active"):
            c.coords(self.pm_needle, cx, cy, cx, cy - r + 8)
            c.itemconfig(self.pm_needle, fill="#444")
            c.itemconfig(self.pm_lamp, fill="#333")
            c.itemconfig(self.pm_lock, fill="#666")
            c.itemconfig(self.pm_off, text="PLL off" if self.v_mode.get() not in PLL_MODES else "press Start")
            c.itemconfig(self.pm_ph, text="")
            return
        ph = clamp(st["phase"], -180.0, 180.0)
        a = math.radians(90 - ph / 2.0)
        c.coords(self.pm_needle, cx, cy, cx + (r - 8) * math.cos(a), cy - (r - 8) * math.sin(a))
        lk = st["locked"]
        c.itemconfig(self.pm_needle, fill=self.ACC if lk else "#888")
        c.itemconfig(self.pm_lamp, fill="#00e676" if lk else self.RED)
        c.itemconfig(self.pm_lock, fill="#00e676" if lk else "#ff6b6b")
        c.itemconfig(self.pm_off, text="%+7.1f Hz" % st["offset"], fill="#d0d6dc")
        c.itemconfig(self.pm_ph, text="%+6.1f deg" % st["phase"], fill="#d0d6dc")

    def tick(self):
        try:
            self.poll_hw()
            self.drain_log()
            self.draw_phase_meter()
            self.draw_vu()
            self.update_tx_stat()
            self.digi_tick()
            self.sstv_tick()
            self.nbtv_tick()
            self.bc_win.tick()
            on = self.eng.running and self.v_mode.get() in STEREO_MODES and self.eng.rx.stereo
            self.stereo_lbl.config(fg=self.ACC if on else (self.MUTED if self.v_mode.get() in STEREO_MODES
                                                            else self.BORDER))
            f = self.eng.rx.anf_freq if self.eng.running else None
            on = bool(self.vars["anf"].get())
            self.anf_lbl.config(text=("ANF %d Hz" % round(f)) if f else ("ANF: no tone" if on else ""),
                                fg=self.ACC if f else self.MUTED)
            if self.eng.running:
                lat = self.eng.latest
                if lat is not None and lat[2] != self.last_ts:
                    self.last_ts = lat[2]
                    self.draw(lat[0], lat[1])
            elif self.btn_run.cget("text") == "Stop":
                self.eng.stop()
                self.btn_run.config(text="Start")
            self.update_status()
        except Exception as ex:
            self.log("GUI error: %r" % (ex,))
        self.root.after(40, self.tick)

    def update_status(self):
        hw = self.ser.hw

        def f(v, on="on", off="off"):
            return "?" if v is None else (on if v else off)
        h = hw_name(self.cfg)
        if h == "None":
            who = "none - no radio control"
        elif self.ser.connected:
            who = hw["version"] or h
        else:
            who = "%s not connected" % h
        txt = "Radio: %s     F = %s kHz     pre-amp %s     atten %s     %s" % (
            who,
            "?" if hw["freq"] is None else hw["freq"], f(hw["pre"]), f(hw["att"]),
            "TRANSMIT" if self.eng.tx_on else "receive")
        txt += "     |     %s look (%s)" % ("dark" if self.dark else "light", self.look["source"])
        self.hw_label.config(text=txt, fg="#e05252" if self.eng.tx_on else self.MUTED)
        self.btn_run.config(bg=self.TXSEL if self.eng.running else self.SEL)
        self.b_ptt.config(text="  TX  " if not self.eng.tx_on else " ON AIR ")

    def drain_log(self):
        n = 0
        while n < 50:
            try:
                s = self.logq.get_nowait()
            except queue.Empty:
                break
            self.logbox.insert(tk.END, time.strftime("%H:%M:%S ") + s + "\n")
            if not self.log_shown and re.search(r"error|stopped|failed|warning|busy|cannot|not available", s, re.I):
                # the log stays as the user left it; the button shows that something needs a look
                self.log_unseen = getattr(self, "log_unseen", 0) + 1
                self.btn_log.config(text="Show log (%d new)" % self.log_unseen, fg="#e05252",
                                    highlightbackground="#e05252")
            n += 1
        if n:
            self.logbox.see(tk.END)
            lines = int(float(self.logbox.index("end-1c").split(".")[0]))
            if lines > 300:
                self.logbox.delete("1.0", "%d.0" % (lines - 300))

    # --------------------------------------------------------------- settings
    def open_settings(self):
        if self.settings_win is not None:
            try:
                self.settings_win.lift()
                return
            except Exception:
                self.settings_win = None
        SettingsDialog(self)

    def apply_settings(self, restart):
        if restart:
            was = self.eng.running
            self.eng.stop()
            self.ser.close()
            self.eng.build()
            self.ser = self.eng.serial
            self.rate = self.eng.rx.rate
            self.apply_hardware()
            self.connect_serial()
            self.push_all()
            if was:
                self.eng.start()
            self.btn_run.config(text="Stop" if self.eng.running else "Start")
        else:
            self.push_all()
        self.build_band_buttons()
        save_cfg(self.cfg)

    def on_close(self):
        try:
            try:
                self.ui["mode_tab"] = int(self.mode_nb.index(self.mode_nb.select()))
                self.vars.setdefault("mode_tab", tk.IntVar(value=self.ui["mode_tab"])).set(self.ui["mode_tab"])
            except Exception:
                pass
            self.cfg["tune_hz"] = int(self.tune_hz)
            self.cfg["lo_khz"] = int(self.lo_khz)
            self.cfg["mode"] = self.v_mode.get()
            ui = {}
            for k, v in self.vars.items():
                try:
                    ui[k] = v.get()
                except Exception:
                    pass
            for k in ("dmode", "dspeed", "dwpm", "dafc", "digi_on", "sstv_on", "sstv_vis", "sstv_txmode",
                      "sstv_text", "sstv_autosave", "sstv_image", "sstv_rxmode", "nbtv_on", "nbtv_mode", "nbtv_avg",
                      "nbtv_neon", "nbtv_src", "nbtv_image", "nbtv_area"):
                if self.ui.get(k) is not None:
                    ui[k] = self.ui.get(k)
            ui["df0"] = float(self.eng.modem.f0)
            self.cfg["ui"] = ui
            save_cfg(self.cfg)
            self.eng.shutdown()
        finally:
            self.root.destroy()


class SettingsDialog:
    TERMS = {"none": "", "CR": "\r", "LF": "\n", "CR+LF": "\r\n"}
    TABS = [
        ("Sound devices", [
            ("I/Q input device (SDR card, or demo)", "iq_in_dev", "devin"),
            ("I/Q output device (SDR card, or none)", "iq_out_dev", "devout"),
            ("Audio output (headset / speaker)", "audio_out_dev", "devout"),
            ("Microphone (headset, or none)", "mic_in_dev", "devin"),
            ("I/Q sample rate", "sample_rate", "rate"), ("Audio rate", "audio_rate", "int")]),
        ("Station", [
            ("Operator name", "op_name", "str"),
            ("Call sign", "callsign", "call"),
            ("Location (QTH)", "qth", "str"),
            ("Grid locator (e.g. FN03 or FN03ab)", "grid", "grid")]),
        ("Language", [
            ("Broadcast station language", "bc_lang", "lang"),
            ("Show the broadcast schedule for SW bands", "bc_info", "bool"),
            ("Schedule download address", "bc_url", "url")]),
        ("Radio", [
            ("Hardware", "hardware", "hardware"),
            ("Mute receiver after TX, ms (no noise burst)", "rx_mute_ms", "int"),
            ("-- ExSDR (homemade, serial control) --", None, "head"),
            ("Serial port", "serial_port", "port"), ("Baud rate", "baud", "int"),
            ("Command terminator", "terminator", "term"),
            ("Hardware reply wait s", "reply_timeout", "float"), ("Reply idle gap s", "idle_gap", "float"),
            ("Gap between commands s", "cmd_gap", "float"),
            ("Gap around frequency commands s", "freq_gap", "float"),
            ("Gap after TX / RX s", "txrx_gap", "float"), ("Listen for banner s", "banner_wait", "float"),
            ("Wait after opening port s", "open_delay", "float")]),
        ("SDR devices", [
            ("-- HackRF One  (sudo apt install hackrf) --", None, "head"),
            ("HackRF RX LNA gain dB (0-40, 8 dB steps)", "hackrf_lna", "int"),
            ("HackRF RX VGA gain dB (0-62, 2 dB steps)", "hackrf_vga", "int"),
            ("HackRF TX gain dB (0-47, start low)", "hackrf_txvga", "int"),
            ("HackRF serial number (blank = first)", "hackrf_serial", "str"),
            ("-- RTL-SDR, receive only  (sudo apt install rtl-sdr) --", None, "head"),
            ("RTL-SDR dongle number (0 = first)", "rtl_index", "int"),
            ("RTL-SDR gain dB (0 = automatic)", "rtl_gain", "float"),
            ("RTL-SDR frequency correction ppm", "rtl_ppm", "int"),
            ("RTL-SDR HF reception", "rtl_hf", "rtlhf"),
            ("-- Airspy HF+ / Discovery, receive only  (sudo apt install airspyhf) --", None, "head"),
            ("Airspy HF+ HF AGC", "airspy_agc", "bool"),
            ("Airspy HF+ serial number (blank = first)", "airspy_serial", "str"),
            ("-- SDRplay / ADALM-Pluto / other SoapySDR radios  (python3-soapysdr) --", None, "head"),
            ("SoapySDR device arguments (e.g. serial=..., uri=ip:192.168.2.1)", "sdr_args", "url"),
            ("RX gain dB", "sdr_rx_gain", "float"),
            ("TX gain dB (Pluto: start low)", "sdr_tx_gain", "float"),
            ("Antenna port (blank = default, e.g. Antenna B, Hi-Z)", "sdr_antenna", "str")]),
        ("Modes / TX", [
            ("Band plan (band buttons)", "band_region", "region"),
            ("TX bandwidth follows RX filter", "tx_follow_rx", "bool"),
            ("SSB TX low cut Hz (if not following)", "ssb_tx_lo", "float"),
            ("SSB TX high cut Hz (if not following)", "ssb_tx_hi", "float"),
            ("FM deviation at 100 % mod, Hz", "fm_dev_hz", "float"),
            ("CW pitch Hz", "cw_pitch_hz", "float")]),
        ("Look", [
            ("Colours (Auto = follow the desktop)", "theme", "theme"),
            ("Font size (0 = desktop size)", "font_size", "int"),
            ("Frequency display colour (or #rrggbb)", "digit_colour", "digitcol"),
            ("S-meter: level that reads S9 (dBFS)", "s9_dbfs", "float")]),
        ("I/Q correction", [
            ("RX swap I/Q", "rx_swap_iq", "bool"), ("RX invert Q (flip sidebands)", "rx_invert_q", "bool"),
            ("RX manual gain balance dB", "rx_gain_bal_db", "float"), ("RX manual phase deg", "rx_phase_deg", "float"),
            ("TX swap I/Q", "tx_swap_iq", "bool"), ("TX invert Q (flip sidebands)", "tx_invert_q", "bool"),
            ("TX gain balance dB", "tx_gain_bal_db", "float"), ("TX phase deg", "tx_phase_deg", "float"),
            ("TX DC offset I (carrier null)", "tx_dc_i", "float"),
            ("TX DC offset Q (carrier null)", "tx_dc_q", "float")]),
    ]
    FIELDS = [f for _, fields in TABS for f in fields if f[1]]
    RESTART = ("serial_port", "baud", "terminator", "iq_in_dev", "iq_out_dev", "audio_out_dev",
               "mic_in_dev", "sample_rate", "audio_rate", "reply_timeout", "idle_gap", "cmd_gap", "freq_gap",
               "txrx_gap", "banner_wait", "open_delay", "hardware", "hackrf_lna", "hackrf_vga",
               "hackrf_txvga", "hackrf_serial", "rtl_index", "rtl_gain", "rtl_ppm", "rtl_hf", "airspy_agc",
               "airspy_serial", "sdr_args", "sdr_rx_gain", "sdr_tx_gain", "sdr_antenna")
    DEV_KEYS = {"iq_in_dev": ("capture", ["demo", "default"]), "mic_in_dev": ("capture", ["default", "none"]),
                "iq_out_dev": ("playback", ["none", "default"]), "audio_out_dev": ("playback", ["default", "none"])}

    def __init__(self, app):
        self.app = app
        self.win = tk.Toplevel(app.root)
        app.settings_win = self.win
        self.win.title("%s settings" % APP)
        self.win.configure(bg=app.BG)
        self.win.protocol("WM_DELETE_WINDOW", self.close)
        self.vars = {}
        self.devs = {"capture": [], "playback": []}
        self.widgets = {}
        self.dev_names = {}
        # the buttons go in first, at the bottom, so they always stay on the screen
        bar = tk.Frame(self.win, bg=app.BG)
        bar.pack(side=tk.BOTTOM, fill=tk.X, padx=8, pady=6)
        app.btn(bar, "Detect sound cards", self.detect).pack(side=tk.LEFT, padx=4)
        for text, cmd in (("Save + close", self.save_close), ("Apply", self.apply), ("Cancel", self.close)):
            app.btn(bar, text, cmd).pack(side=tk.RIGHT, padx=4)
        self.info = tk.Label(self.win, text="", bg=app.BG, fg=app.FG, justify=tk.LEFT, anchor="w",
                             font=("Courier", 9), wraplength=900)
        self.info.pack(side=tk.BOTTOM, fill=tk.X, padx=10)
        try:
            style = ttk.Style(self.win)
            style.configure("ExSDR.TNotebook.Tab", padding=(10, 3))
        except Exception:
            pass
        nb = ttk.Notebook(self.win, style="ExSDR.TNotebook")
        nb.pack(side=tk.TOP, fill=tk.BOTH, expand=True, padx=8, pady=(8, 0))
        for title, fields in self.TABS:
            tab = tk.Frame(nb, bg=app.BG, padx=8, pady=8)
            nb.add(tab, text="  %s  " % title)
            r0 = 0
            if title == "Sound devices":
                tk.Label(tab, justify=tk.LEFT, bg=app.BG, fg=app.ACC, text=(
                    "I/Q in and I/Q out are on the same card, so pick the same card for both.\n"
                    "  SDR card: plughw:CARD=...  It needs the card to itself: if it shows\n"
                    "            'IN USE by pipewire', press Release card.\n"
                    "  Headset:  'default' for audio output and microphone, then choose the headset in\n"
                    "            the PulseAudio mixer - shared with the desktop, never 'busy'.\n"
                    "  Test needs Stop first.\n"
                    "  With HackRF the I/Q comes from the HackRF over USB: only the headset is used here.")).grid(
                    row=0, column=0, columnspan=4, sticky="w", pady=(0, 6))
                r0 = 1
            for i, (text, key, kind) in enumerate(fields):
                self.add_field(tab, r0 + i, text, key, kind)
        self.detect()
        fit_to_screen(self.win, margin_h=120)
        self.win.lift()

    def add_field(self, body, r, text, key, kind):
        app = self.app
        if kind == "head":                                   # sub heading inside a tab
            tk.Label(body, text=text.strip("- "), bg=app.BG, fg=app.MUTED, font=app.F_CAP).grid(
                row=r, column=0, columnspan=4, sticky="w", padx=4, pady=(8, 1))
            return
        tk.Label(body, text=text, bg=app.BG, fg=app.FG).grid(row=r, column=0, sticky="w", padx=4, pady=2)
        val = app.cfg[key]
        if kind == "bool":
            v = tk.IntVar(value=1 if val else 0)
            w = tk.Checkbutton(body, variable=v, bg=app.BG, activebackground=app.BG, fg=app.FG,
                               selectcolor=app.FIELD, highlightthickness=0, bd=0)
        elif kind == "term":
            inv = {b: a for a, b in self.TERMS.items()}
            v = tk.StringVar(value=inv.get(val, "none"))
            w = ttk.Combobox(body, textvariable=v, values=list(self.TERMS.keys()), width=22)
        elif kind == "port":
            v = tk.StringVar(value=str(val))
            w = ttk.Combobox(body, textvariable=v, values=list_ports(), width=34)
        elif kind in ("devin", "devout"):
            v = tk.StringVar(value=str(val))
            w = ttk.Combobox(body, textvariable=v, values=[], width=44)
            w.bind("<<ComboboxSelected>>", lambda e, k=key: self.show_name(k))
            w.bind("<FocusOut>", lambda e, k=key: self.show_name(k))
            f = tk.Frame(body, bg=app.BG)
            f.grid(row=r, column=2, sticky="w")
            app.btn(f, "Test", lambda k=key: self.test(k)).pack(side=tk.LEFT, padx=2)
            if key in ("iq_in_dev", "iq_out_dev"):
                app.btn(f, "Release card", lambda k=key: self.release(k)).pack(side=tk.LEFT, padx=2)
            nl = tk.Label(body, text="", bg=app.BG, fg="#9ccc65", font=("Courier", 9), anchor="w")
            nl.grid(row=r, column=3, sticky="w", padx=4)
            self.dev_names[key] = nl
        elif kind == "rate":
            v = tk.StringVar(value=str(val))
            w = ttk.Combobox(body, textvariable=v, values=["48000", "96000", "192000", "384000"], width=12)
        elif kind == "region":
            v = tk.StringVar(value=str(val))
            w = ttk.Combobox(body, textvariable=v, values=list(BAND_PLANS), width=12, state="readonly")
        elif kind == "hardware":
            v = tk.StringVar(value=hw_name(app.cfg))
            w = ttk.Combobox(body, textvariable=v, values=HARDWARE, width=16, state="readonly")
            tk.Label(body, text="SDR options: SDR devices tab.  None = no radio control", bg=app.BG, fg=app.MUTED,
                     font=app.F_SMALL).grid(row=r, column=2, columnspan=2, sticky="w", padx=4)
        elif kind == "digitcol":
            v = tk.StringVar(value=str(val))
            w = ttk.Combobox(body, textvariable=v, values=list(DIGIT_COLOURS), width=12)
            tk.Label(body, text="also: right-click the frequency display", bg=app.BG, fg=app.MUTED,
                     font=app.F_SMALL).grid(row=r, column=2, columnspan=2, sticky="w", padx=4)
        elif kind == "rtlhf":
            v = tk.StringVar(value=str(val))
            w = ttk.Combobox(body, textvariable=v, values=["V4 / none", "V3 direct sampling",
                                                           "Upconverter +125 MHz"], width=20, state="readonly")
        elif kind == "lang":
            v = tk.StringVar(value=str(val))
            w = ttk.Combobox(body, textvariable=v, values=list(BC_LANGUAGES), width=16)
            tk.Label(body, text="filters the broadcast schedule; EiBi codes can be typed too, e.g. E, F",
                     bg=app.BG, fg=app.MUTED, font=app.F_SMALL).grid(row=r, column=2, columnspan=2, sticky="w",
                                                                      padx=4)
        elif kind == "url":
            v = tk.StringVar(value=str(val))
            w = ttk.Entry(body, textvariable=v, width=48)
        elif kind == "theme":
            v = tk.StringVar(value=str(val))
            w = ttk.Combobox(body, textvariable=v, values=["Auto", "Light", "Dark"], width=12, state="readonly")
        else:
            v = tk.StringVar(value=str(val))
            w = ttk.Entry(body, textvariable=v, width=16)
        w.grid(row=r, column=1, sticky="w", padx=4, pady=2)
        self.vars[key] = (v, kind)
        self.widgets[key] = w

    def detect(self):
        self.devs = alsa_devices()
        for key, (kind, extra) in self.DEV_KEYS.items():
            vals = ["%-30s [%s]" % (x, describe_device(x, self.devs)) for x in extra]
            vals += ["%-30s [%s]" % (val, name) for val, name, _, _ in self.devs[kind]]
            self.widgets[key].config(values=vals)
            self.show_name(key)
        lines = []
        for kind, title in (("capture", "Inputs  (arecord)"), ("playback", "Outputs (aplay)")):
            names = []
            for val, name, num, dev in self.devs[kind]:
                if num is not None and name not in names:
                    names.append(name)
            lines.append("%s: %s" % (title, ";  ".join(names) or "none found"))
        if not self.devs["capture"] and not self.devs["playback"]:
            lines = ["no ALSA sound devices found (is alsa-utils installed?  sudo apt install alsa-utils)"]
        self.info.config(text="\n".join(lines))

    def show_name(self, key):
        v, _ = self.vars[key]
        val = dev_value(v.get())
        if val != v.get():
            v.set(val)                         # keep only the device part in the box
        name = describe_device(val, self.devs) or "(unknown device)"
        who = alsa_owner(val, self.DEV_KEYS[key][0])
        if who and not self.app.eng.running:
            name += "  - IN USE by " + who
        self.dev_names[key].config(text=name, fg="#ff6b6b" if who and not self.app.eng.running else "#9ccc65")

    def release(self, key):
        dev = dev_value(self.vars[key][0].get())
        res = release_card(dev)
        self.app.log("release %s: %s" % (dev, res))
        self.info.config(text=res)
        self.win.after(800, lambda: [self.show_name(k) for k in self.DEV_KEYS])

    def test(self, key):
        if self.app.eng.running:
            self.info.config(text="Press Stop first - ExSDR is using the sound devices while it runs.")
            return
        dev = dev_value(self.vars[key][0].get())
        try:
            rate = int(float(self.vars["sample_rate"][0].get()))
            arate = int(float(self.vars["audio_rate"][0].get()))
        except ValueError:
            rate, arate = 192000, 48000
        kind = self.DEV_KEYS[key][0]
        iq = key in ("iq_in_dev", "iq_out_dev")
        label = [t for t, k, _ in self.FIELDS if k == key][0]
        self.info.config(text="%s %s: testing ..." % (label, dev))

        def run():
            res = sound_test(kind, dev, rate if iq else arate, 2 if iq else 1, iq=iq)
            self.app.log("sound test %s: %s" % (dev, res))
            try:
                self.win.after(0, lambda: self.info.config(text="%s  %s:\n%s" % (label, dev, res)))
            except Exception:
                pass
        threading.Thread(target=run, daemon=True).start()

    def collect(self):
        new = {}
        for key, (v, kind) in self.vars.items():
            raw = v.get()
            if kind == "bool":
                new[key] = bool(raw)
            elif kind == "term":
                new[key] = self.TERMS.get(raw, "")
            elif kind in ("int", "rate"):
                new[key] = int(float(raw))
            elif kind == "float":
                new[key] = float(raw)
            elif kind in ("devin", "devout"):
                new[key] = dev_value(raw)
            elif kind == "call":
                new[key] = str(raw).strip().upper()
            elif kind == "grid":                         # FN03fq: field + square upper, subsquare lower
                g = str(raw).strip()
                new[key] = g[:4].upper() + g[4:6].lower() + g[6:]
            else:
                new[key] = str(raw).strip()
        return new

    def apply(self):
        try:
            new = self.collect()
        except ValueError as e:
            messagebox.showerror(APP, "Bad value: %s" % e)
            return False
        for k in ("callsign", "qth"):
            if k in new and not new[k]:
                new[k] = PLACEHOLDER
        g = new.get("grid", "")
        if g and not re.match(r"^[A-R]{2}[0-9]{2}([A-X]{2}([0-9]{2})?)?$", g, re.I):
            messagebox.showerror(APP, "The grid locator should look like FN03 or FN03ab.")
            return False
        if new["sample_rate"] % new["audio_rate"]:
            messagebox.showerror(APP, "The I/Q sample rate must be a multiple of the audio rate.")
            return False
        restart = any(new[k] != self.app.cfg[k] for k in self.RESTART)
        if new.get("digit_colour") != self.app.cfg.get("digit_colour"):
            self.app.change_digit_colour(new["digit_colour"])
        if any(new[k] != self.app.cfg[k] for k in ("theme", "font_size")):
            self.info.config(text="Colours and font size change when ExSDR is started again.")
        self.app.cfg.update(new)
        self.app.apply_settings(restart)
        self.app.station_changed()
        if self.app.bc_win is not None:
            self.app.bc_win.v_lang.set(self.app.cfg.get("bc_lang", "English"))
            if self.app.bc_win.shown:
                self.app.bc_win.fill()
        return True

    def save_close(self):
        if self.apply():
            self.close()

    def close(self):
        self.app.settings_win = None
        self.win.destroy()


# ===================================================================== selftest
def _tone(x, fs):
    w = np.blackman(len(x))
    S = np.abs(np.fft.rfft(x * w))
    k = int(np.argmax(S))
    rest = np.concatenate((S[:max(0, k - 12)], S[k + 12:]))
    return k * fs / float(len(x)), 20 * math.log10(S[k] / (math.sqrt(float(np.mean(rest ** 2))) + 1e-12))


def _run_rx(rx, sig, skip=4):
    out = []
    for b in range(len(sig) // rx.N):
        pcm, spec, lvl = rx.process(sig[b * rx.N:(b + 1) * rx.N])
        if b >= skip:
            out.append(pcm.astype(np.float64) / 32000.0)
    return np.concatenate(out)


class PicModel:
    """Simulated HF_SDR.BAS on a pty, with the PIC's timing.

    Like the real PIC: a command is up to 6 bytes read by HSERIN with a 100 ms timeout,
    the PIC is busy after F (PLL, band, LEDs ~0.48 s), TX/RX (~0.3 s) and after power-on
    (~0.5 s).  The USART holds only 2 bytes: a third byte arriving while busy is an
    overrun.  firmware="1.0": reply first, then busy; an overrun makes it deaf for good.
    firmware="1.1": busy first, then reply; overruns are cleared (HSER_CLROERR)."""
    BUSY = {"F": 0.48, "TX": 0.30, "RX": 0.30, "boot": 0.50}

    def __init__(self, firmware):
        import pty
        self.fw = firmware
        self.master, self.slave = pty.openpty()
        self.port = os.ttyname(self.slave)
        self.f, self.p, self.a, self.tx = 7100, 1, 0, 0
        self.deaf = False
        self.overruns = 0
        self.ncmd = 0
        self.busy_until = 0.0
        self.stop = threading.Event()
        threading.Thread(target=self._run, daemon=True).start()

    def close(self):
        self.stop.set()
        time.sleep(0.1)
        for fd in (self.master, self.slave):
            try:
                os.close(fd)
            except OSError:
                pass

    def say(self, txt):
        os.write(self.master, (txt + "\r\n").encode())

    def busy(self, what):
        self.busy_until = time.time() + self.BUSY[what]

    def _get(self, timeout):
        r, _, _ = select.select([self.master], [], [], timeout)
        return os.read(self.master, 1) if r else b""

    def _run(self):
        time.sleep(0.15)
        if self.fw == "1.0":
            self.say("HF SDR v1")
            self.busy("boot")
        else:
            time.sleep(self.BUSY["boot"])
            self.say("HF SDR v1")
        while not self.stop.is_set():
            try:
                b = self._get(0.05)
            except OSError:
                return
            if not b:
                continue
            if time.time() < self.busy_until:
                # bytes keep coming while the PIC sits in a PAUSE: the 2-byte FIFO overflows
                more = b""
                while True:
                    c = self._get(0.004)
                    if not c:
                        break
                    more += c
                if len(b + more) > 2:
                    self.overruns += 1
                    if self.fw == "1.0":
                        self.deaf = True
                time.sleep(max(0.0, self.busy_until - time.time()))
                if self.deaf:
                    continue
                cmd = (b + more)[:2] if len(b + more) > 2 else b + more   # what survived in the FIFO
            else:
                cmd = b
            if self.deaf:
                continue
            while len(cmd) < 6:                      # HSERIN 100, Timeout, [D0..D5]
                c = self._get(0.1)
                if not c:
                    break
                cmd += c
            self.handle(cmd.decode("ascii", "ignore"))

    def handle(self, c):
        self.ncmd += 1
        late = self.fw != "1.0"
        if c.startswith("F"):
            if len(c) < 6 or not c[1:6].isdigit():
                if late:
                    self.say("Error F")
                return
            self.f = int(c[1:6])
            msg = "Frequency Set to %d kHz" % self.f
            if late:
                time.sleep(self.BUSY["F"])
                self.say(msg)
            else:
                self.say(msg)
                self.busy("F")
        elif c[:2] in ("TX", "RX"):
            self.tx = 1 if c[:2] == "TX" else 0
            msg = "Tx Set" if self.tx else "Rx Set"
            if late:
                time.sleep(self.BUSY["TX"])
                self.say(msg)
            else:
                self.say(msg)
                self.busy("TX")
        elif c[:1] in ("P", "A") and c[1:2] in ("0", "1"):
            on = c[1] == "1"
            if c[0] == "P":
                self.p = on
                self.say("Pre Amp = %s" % ("on" if on else "off"))
            else:
                self.a = on
                self.say("Attenuator = %s" % ("on" if on else "off"))
        elif c[:2] == "?F":
            self.say("Frequency = %d kHz" % self.f)
        elif c[:2] == "?P":
            self.say("Pre Amp = %s" % ("on" if self.p else "off"))
        elif c[:2] == "?A":
            self.say("Attenuator = %s" % ("on" if self.a else "off"))


def pic_session(firmware, cfg):
    """Drive a PicModel the way the GUI does: power-up, fast tuning, preamp, TX / RX."""
    pic = PicModel(firmware)
    cfg = dict(cfg)
    cfg["serial_port"] = pic.port
    link = SerialLink(cfg, lambda s: None)
    link.open()
    hello_delay = cfg.get("_hello_delay", 1.0)
    t_end = time.time() + 3.0
    while time.time() < t_end:                     # the GUI answers the banner
        try:
            ev = link.events.get(timeout=0.05)
        except queue.Empty:
            continue
        if ev[0] == "hello":
            link.submit_txrx("RX", hello_delay)
            link.query_all()
            break
    for k in range(40):                            # tuning across the band, a step every 40 ms
        link.set_freq_khz(7000 + 7 * k)
        if k == 20:
            link.set_flag("P", False)
        time.sleep(0.04)
    done = []
    link.submit_txrx("TX", 0.0, done.append)
    link.submit_txrx("RX", 0.0, done.append)
    link.set_freq_khz(14175)
    link.query_all()
    t_end = time.time() + 20.0
    while (not link.q.empty() or len(done) < 2) and time.time() < t_end:
        time.sleep(0.05)
    time.sleep(1.0)
    link.close()
    pic.close()
    return pic, link, done


def selftest():
    fails = []

    def check(name, ok, info=""):
        print("%-46s %s  %s" % (name, "PASS" if ok else "FAIL", info))
        if not ok:
            fails.append(name)

    fs = 192000
    nb = 14
    t = np.arange(nb * 8192) / float(fs)
    rng = np.random.RandomState(7)
    noise = (rng.randn(len(t)) + 1j * rng.randn(len(t))) * 1e-4

    def rx_case(name, sig, mode, offset, want, width=2400.0, **kw):
        rx = RxDsp(fs, 48000)
        rx.set_params(mode=mode, offset=offset, width=width, **kw)
        a = _run_rx(rx, sig + noise)
        f, snr = _tone(a, 48000)
        check(name, abs(f - want) < 15 and snr > 30, "%.0f Hz, peak/rest %.0f dB" % (f, snr))
        return a

    a_usb = rx_case("RX USB tone", 0.05 * np.exp(2j * np.pi * 6000 * t), "USB", 5000.0, 1000)
    a_lsb = rx_case("RX LSB tone", 0.05 * np.exp(2j * np.pi * 4000 * t), "LSB", 5000.0, 1000)
    rx_case("RX AM", 0.05 * (1 + 0.6 * np.cos(2 * np.pi * 1000 * t)) * np.exp(2j * np.pi * 12000 * t),
            "AM", 12000.0, 1000, width=6000.0)
    rx_case("RX FM", 0.05 * np.exp(1j * (2 * np.pi * -15000 * t + 3.0 * np.sin(2 * np.pi * 1000 * t))),
            "FM", -15000.0, 1000, width=16000.0)
    rx_case("RX CW (pitch 700)", 0.05 * np.exp(2j * np.pi * 3000 * t), "CW", 3000.0, 700, width=250.0)
    # ECSS: AM station whose carrier is 37 Hz above where we tuned
    def ecss_case(name, sig, sb, want, offset=12000.0, width=8000.0):
        rx = RxDsp(fs, 48000)
        rx.set_params(mode="ECSS", offset=offset, width=width, lowcut=0.0, ecss_sb=sb)
        f, snr = _tone(_run_rx(rx, sig + noise), 48000)
        check(name, abs(f - want) < 15 and snr > 30 and rx.pll["locked"],
              "%.0f Hz, %.0f dB, PLL %s, offset %+.1f Hz, phase %+.1f deg"
              % (f, snr, "locked" if rx.pll["locked"] else "NOT locked", rx.pll["offset"], rx.pll["phase"]))
        return rx
    am37 = 0.05 * (1 + 0.6 * np.cos(2 * np.pi * 1000 * t)) * np.exp(2j * np.pi * 12037 * t + 0.8j)
    rx = ecss_case("RX ECSS DSB (carrier 37 Hz off)", am37, "DSB", 1000)
    check("ECSS phase meter: offset and phase", abs(rx.pll["offset"] - 37) < 1 and abs(rx.pll["phase"]) < 10,
          "%+.2f Hz (expect +37), %+.1f deg (expect ~0)" % (rx.pll["offset"], rx.pll["phase"]))
    two = 0.05 * np.exp(2j * np.pi * 12037 * t) + 0.02 * np.exp(2j * np.pi * (12037 + 1500) * t) \
        + 0.02 * np.exp(2j * np.pi * (12037 - 700) * t)                 # different audio in each sideband
    ecss_case("RX ECSS U picks the upper sideband", two, "USB", 1500)
    ecss_case("RX ECSS L picks the lower sideband", two, "LSB", 700)
    rx = RxDsp(fs, 48000)
    rx.set_params(mode="ECSS", offset=12000.0, width=8000.0)
    _run_rx(rx, 0.05 * (1 + 0.5 * np.cos(2 * np.pi * 800 * t)) * np.exp(2j * np.pi * 12300 * t) + noise)
    check("ECSS acquires a carrier 300 Hz off", rx.pll["locked"] and abs(rx.pll["offset"] - 300) < 1,
          "%+.1f Hz" % rx.pll["offset"])
    rx = RxDsp(fs, 48000)
    rx.set_params(mode="ECSS", offset=12000.0, width=8000.0)
    _run_rx(rx, noise * 50)
    check("ECSS does not lock on noise", not rx.pll["locked"])
    # AM stereo: C-QuAM and Kahn, left 700 Hz, right 1900 Hz, carrier 37 Hz off
    Ls, Rs = 0.3 * np.sin(2 * np.pi * 700 * t), 0.3 * np.sin(2 * np.pi * 1900 * t)
    I = 1 + Ls + Rs
    cq = 0.05 * I * np.exp(1j * np.arctan2(Ls - Rs + 0.05 * np.sin(2 * np.pi * 25 * t), I)) \
        * np.exp(2j * np.pi * 12037 * t)
    kh = 0.05 * np.exp(2j * np.pi * 12037 * t) * (1 + 0.3 * np.exp(-2j * np.pi * 700 * t)
                                                   + 0.3 * np.exp(2j * np.pi * 1900 * t))

    def stereo_case(name, mode, sig):
        rx = RxDsp(fs, 48000)
        rx.set_params(mode=mode, offset=12000.0, width=10000.0, lowcut=0.0, agc="Off", gain_db=20, vol=100)
        sts = []
        for b in range(len(sig) // rx.N):
            rx.process(sig[b * rx.N:(b + 1) * rx.N] + noise[b * rx.N:(b + 1) * rx.N])
            sts.append(rx.last_stereo.astype(np.float64))
        st = np.concatenate(sts[6:])
        fl, sl = _tone(st[:, 0], 48000)
        fr, sr = _tone(st[:, 1], 48000)
        check(name, abs(fl - 700) < 15 and abs(fr - 1900) < 15 and sl > 30 and sr > 30 and rx.stereo,
              "left %.0f Hz (%.0f dB), right %.0f Hz (%.0f dB), stereo %s" % (fl, sl, fr, sr, rx.stereo))
    stereo_case("RX C-QuAM: left / right apart, pilot seen", "CQUAM", cq)
    stereo_case("RX Kahn: LSB -> left, USB -> right", "KAHN", kh)
    # widest filters: SSB 6 kHz, AM 12 kHz (+-6 kHz)
    rx_case("RX USB width 6 kHz passes 5.8 kHz audio", 0.05 * np.exp(2j * np.pi * 10800 * t), "USB", 5000.0,
            5800, width=6000.0, lowcut=300.0)
    rx_case("RX AM width 12 kHz passes 5.5 kHz audio",
            0.05 * (1 + 0.6 * np.cos(2 * np.pi * 5500 * t)) * np.exp(2j * np.pi * 12000 * t), "AM", 12000.0,
            5500, width=12000.0)
    # low cut moves only the lower edge; soft roll-off; automatic notch
    def lvl_at(fa, **kw):
        rx = RxDsp(fs, 48000)
        rx.set_params(mode="USB", offset=5000.0, width=2400.0, agc="Off", gain_db=0, vol=100, **kw)
        a = _run_rx(rx, 0.01 * np.exp(2j * np.pi * (5000 + fa) * t))
        return 20 * math.log10(math.sqrt(float(np.mean(a * a))) + 1e-9)
    r = [lvl_at(f, lowcut=600.0) for f in (400, 1000, 2300)]
    check("Low cut 600 Hz: cuts 400 Hz, keeps 1-2.3 kHz", r[0] - r[1] < -60 and abs(r[2] - r[1]) < 1,
          "400 Hz %.0f dB, 2300 Hz %.1f dB" % (r[0] - r[1], r[2] - r[1]))
    h, sft = lvl_at(2600, lowcut=300.0), lvl_at(2600, lowcut=300.0, soft=True)
    ref = lvl_at(1000, lowcut=300.0)
    check("Soft roll-off: gentle slope above the edge", h - ref < -60 and -25 < sft - ref < -6,
          "2.6 kHz: hard %.0f dB, soft %.0f dB" % (h - ref, sft - ref))
    rx = RxDsp(fs, 48000)
    rx.set_params(mode="USB", offset=5000.0, width=2700.0, anf=True, agc="Off", gain_db=20, vol=100)
    a = _run_rx(rx, 0.02 * np.exp(2j * np.pi * 6500 * t) + noise * 20, 10)
    S = np.abs(np.fft.rfft(a * np.blackman(len(a))))
    fq = np.fft.rfftfreq(len(a), 1 / 48000.0)
    above = 20 * math.log10(S[np.argmin(abs(fq - 1500))] / np.median(S[(fq > 600) & (fq < 2400)]))
    check("Automatic notch locks on and removes a 1.5 kHz tone", rx.anf_freq is not None and
          abs(rx.anf_freq - 1500) < 5 and above < 10, "notch %s Hz, tone left %+.0f dB above the band"
          % (None if rx.anf_freq is None else round(rx.anf_freq), above))
    d0, d1 = lvl_at(300, lowcut=50.0, deemph="75"), lvl_at(2122, lowcut=50.0, deemph="75")
    check("RX de-emphasis 75 us: -3 dB at 2122 Hz", abs(d1 - d0 + 3.0) < 0.4, "%+.1f dB" % (d1 - d0))
    plan = dict((n, (lo, hi)) for n, lo, hi in BAND_PLANS["Region 2"])
    cen = [band_centre_hz(*plan[n]) for n in ("160", "40", "20", "6")]
    check("Band buttons: centre of 160/40/20/6 m", cen == [1900000, 7150000, 14175000, 52000000], str(cen))
    bc = dict((n, band_centre_hz(lo, hi)) for n, lo, hi in broadcast_plan({"band_region": "Region 2"}))
    check("Broadcast buttons: MW + 14 SW bands, centres", len(bc) == 15 and bc["MW"] == 1115000
          and bc["49"] == 6050000 and bc["31"] == 9650000 and bc["11"] == 25885000,
          "MW %d, 49 m %d, 31 m %d, 11 m %d" % (bc["MW"], bc["49"], bc["31"], bc["11"]))

    rx = RxDsp(fs, 48000)
    rx.set_params(mode="LSB", offset=5000.0, width=2400.0)
    a_rej = _run_rx(rx, 0.05 * np.exp(2j * np.pi * 6000 * t) + noise)
    rej = 20 * math.log10((np.sqrt(np.mean(a_rej ** 2)) + 1e-12) / np.sqrt(np.mean(a_usb ** 2)))
    check("RX opposite sideband rejection", rej < -40, "%.0f dB" % rej)

    # I/Q imbalance corrected by the auto balance
    # tone 1 kHz above the LO, listening at the LO: its mirror image falls inside the LSB passband
    sig = 0.05 * np.exp(2j * np.pi * 1000 * t)
    bad = sig.real + 1j * (0.8 * (sig.imag * math.cos(0.15) + sig.real * math.sin(0.15)))
    res = []
    for auto in (False, True):
        rx = RxDsp(fs, 48000)
        rx.set_params(mode="LSB", offset=0.0, auto_iq=auto, agc="Off", gain_db=20)
        res.append(np.sqrt(np.mean(_run_rx(rx, bad + noise, 8) ** 2)))
    imp = 20 * math.log10(res[0] / (res[1] + 1e-12))
    check("Auto I/Q balance improves image", imp > 12, "%.0f dB better" % imp)

    # AGC
    lv = []
    for amp in (0.003, 0.1):
        rx = RxDsp(fs, 48000)
        rx.set_params(mode="USB", offset=5000.0, agc="Med")
        lv.append(np.sqrt(np.mean(_run_rx(rx, amp * np.exp(2j * np.pi * 6000 * t) + noise, 8) ** 2)))
    d = abs(20 * math.log10(lv[0] / lv[1]))
    check("AGC levels two signals alike", d < 4, "%.1f dB difference for 30 dB input difference" % d)

    # noise blanker
    sig = 0.05 * np.exp(2j * np.pi * 6000 * t) + noise
    sp = sig.copy()
    for k in range(40, len(sp) - 50, 997):
        sp[k] += 3.0
    snr = []
    for nbk in (False, True):
        rx = RxDsp(fs, 48000)
        rx.set_params(mode="USB", offset=5000.0, nb=nbk, nb_thr=6.0)
        snr.append(_tone(_run_rx(rx, sp), 48000)[1])
    check("Noise blanker removes impulses", snr[1] - snr[0] > 6, "%.0f -> %.0f dB" % (snr[0], snr[1]))

    # noise reduction
    # (voice-like gated tone: a steady carrier is treated as noise by any spectral-subtraction NR)
    tn = np.arange(40 * 8192) / float(fs)
    big = (rng.randn(len(tn)) + 1j * rng.randn(len(tn))) * 4e-3
    gate = (np.floor(tn * 4) % 2 == 0).astype(float)             # 4 Hz, 50 % on
    sig = 0.02 * gate * np.exp(2j * np.pi * 6000 * tn) + big
    ratio = []
    for nr in (False, True):
        rx = RxDsp(fs, 48000)
        rx.set_params(mode="USB", offset=5000.0, nr=nr, nr_amt=0.7, agc="Off", gain_db=40)
        a = _run_rx(rx, sig, 8)
        e = np.convolve(a * a, np.ones(480) / 480.0, "same")     # 10 ms energy
        g48 = gate[:len(tn):4][8 * 2048:8 * 2048 + len(a)]
        on = e[(g48 > 0.5)][4000:-4000]
        off = e[(g48 < 0.5)][4000:-4000]
        ratio.append(10 * math.log10(np.median(on) / np.median(off)))
    check("Noise reduction improves on/off ratio", ratio[1] - ratio[0] > 3, "%.0f -> %.0f dB" % (ratio[0], ratio[1]))

    # notch
    sig = 0.05 * np.exp(2j * np.pi * 6000 * t) + 0.05 * np.exp(2j * np.pi * 6800 * t) + noise
    pw = []
    for nt in (False, True):
        rx = RxDsp(fs, 48000)
        rx.set_params(mode="USB", offset=5000.0, notch=nt, notch_hz=1800.0, agc="Off", gain_db=40)
        a = _run_rx(rx, sig)
        S = np.abs(np.fft.rfft(a * np.blackman(len(a))))
        pw.append(S[int(1800 * len(a) / 48000.0)])
    check("Notch removes interferer", 20 * math.log10(pw[0] / pw[1]) > 20, "%.0f dB" % (20 * math.log10(pw[0] / pw[1])))

    # spectrum placement
    rx = RxDsp(fs, 48000)
    rx.set_params(offset=0.0)
    _, spec, _ = rx.process(0.1 * np.exp(2j * np.pi * 20000 * t[:rx.N]) + noise[:rx.N])
    k = int(np.argmax(spec))
    f = (k - len(spec) / 2) * fs / float(len(spec))
    check("Spectrum shows +20 kHz at the right bin", abs(f - 20000) < 50 and abs(spec[k] + 20) < 2,
          "%.0f Hz, %.1f dBFS" % (f, spec[k]))

    # TX -> RX loopback
    def loop(mode, tx_kw=None, rx_kw=None, width=2400.0):
        tx = TxDsp(fs, 48000)
        tx.set_params(mode=mode, mic_gain_db=0.0, drive=0.5, offset=10000.0, **(tx_kw or {}))
        rx = RxDsp(fs, 48000)
        rx.set_params(mode=mode, offset=10000.0, width=width, **(rx_kw or {}))
        tt = np.arange(30 * tx.M) / 48000.0
        mic = 0.3 * np.sin(2 * np.pi * 1000 * tt)
        iqs = []
        for b in range(30):
            o = tx.process(mic[b * tx.M:(b + 1) * tx.M]).astype(np.float64) / 32768.0
            iqs.append(o[0::2] + 1j * o[1::2])
        iq = np.concatenate(iqs)
        return iq, _run_rx(rx, iq, 6)

    iq, a = loop("USB")
    S = np.abs(np.fft.fftshift(np.fft.fft(iq[8192:] * np.blackman(len(iq) - 8192))))
    fr = np.fft.fftshift(np.fft.fftfreq(len(iq) - 8192, 1.0 / fs))
    up = S[np.argmin(abs(fr - 11000))]          # carrier at +10 kHz, audio 1 kHz
    lo_ = S[np.argmin(abs(fr - 9000))]
    check("TX USB sideband suppression", 20 * math.log10(up / (lo_ + 1e-9)) > 45, "%.0f dB" % (20 * math.log10(up / (lo_ + 1e-9))))
    f, snr = _tone(a, 48000)
    check("TX USB -> RX USB loopback", abs(f - 1000) < 15 and snr > 35, "%.0f Hz, %.0f dB" % (f, snr))
    iq, a = loop("LSB")
    f, snr = _tone(a, 48000)
    check("TX LSB -> RX LSB loopback", abs(f - 1000) < 15 and snr > 35, "%.0f Hz, %.0f dB" % (f, snr))
    iq, a = loop("AM", width=8000.0)
    f, snr = _tone(a, 48000)
    check("TX AM -> RX AM loopback", abs(f - 1000) < 15 and snr > 30, "%.0f Hz, %.0f dB" % (f, snr))
    iq, a = loop("ECSS", width=8000.0)
    f, snr = _tone(a, 48000)
    check("TX ECSS (sent as AM) -> RX ECSS loopback", abs(f - 1000) < 15 and snr > 30, "%.0f Hz, %.0f dB" % (f, snr))
    # AM / FM modulation level and the 100 % limit
    def tx_iq(mode, **kw):
        tx = TxDsp(fs, 48000)
        tx.set_params(mode=mode, drive=1.0, offset=0.0, **kw)
        o = np.concatenate([tx.process(np.zeros(tx.M)) for _ in range(12)]).astype(np.float64) / 32700.0
        return (o[0::2] + 1j * o[1::2])[4 * tx.N:]
    e = np.abs(tx_iq("AM", source="tone", mod=0.8))
    dep = (e.max() - e.min()) / (e.max() + e.min())
    check("TX AM tone at Mod 80 % gives 80 % modulation", abs(dep - 0.8) < 0.01, "%.1f %%" % (100 * dep))
    iq = tx_iq("FM", source="tone", mod=0.5)
    dv = np.diff(np.unwrap(np.angle(iq))) * fs / (2 * math.pi)
    dv = (np.percentile(dv, 99.9) - np.percentile(dv, 0.1)) / 2
    check("TX FM tone at Mod 50 % gives 2.5 kHz deviation", abs(dv - 2500) < 50, "%.0f Hz" % dv)
    tl = np.arange(12 * 2048) / 48000.0
    loud = 3.0 * np.sin(2 * np.pi * 400 * tl) * (1 + np.sin(2 * np.pi * 2 * tl))
    tx = TxDsp(fs, 48000)
    tx.set_params(mode="AM", source="mic", mic_gain_db=20.0, mod=1.0, drive=1.0, offset=0.0, limiter=True)
    o = np.concatenate([tx.process(loud[b * tx.M:(b + 1) * tx.M]) for b in range(12)]).astype(np.float64) / 32700.0
    e = np.abs(o[0::2] + 1j * o[1::2])[4 * tx.N:]
    check("TX AM limiter: overdriven mic never over 100 %", e.min() > 0.0 and (e.max() - e.min()) / (e.max() + e.min()) <= 1.0,
          "carrier low point %.3f of full" % (e.min() / e.max()))
    iq, a = loop("FM", width=16000.0)
    f, snr = _tone(a, 48000)
    check("TX FM -> RX FM loopback", abs(f - 1000) < 15 and snr > 30, "%.0f Hz, %.0f dB" % (f, snr))
    tx = TxDsp(fs, 48000)
    tx.set_params(mode="CW", drive=0.5, key=True)
    o = np.concatenate([tx.process(np.zeros(tx.M)) for _ in range(4)]).astype(np.float64)[-2 * tx.N:]
    amp = np.abs(o[0::2] + 1j * o[1::2]).mean() / 32700
    check("TX CW key-down carrier level", abs(amp - 0.25) < 0.02, "%.3f (expect 0.25)" % amp)
    print("TX data length per block: %d bytes" % (len(tx.process(np.zeros(tx.M))) * 2))

    # reply parsing (strings as sent by the hardware)
    sl = SerialLink(dict(DEFAULTS), lambda s: None)
    cases = [("Frequency Set to 3650 kHz", ("freq", 3650)), ("Frequency = 7100 kHz", ("freq", 7100)),
             ("Pre Amp = on", ("pre", True)), ("Pre Amp = off", ("pre", False)),
             ("Pre Amp Set on", ("pre", True)), ("Attenuator = off", ("att", False)),
             ("Attenuator = on\r\n", ("att", True)), ("Tx Set", ("tx", True)), ("Rx Set", ("tx", False)),
             ("HF SDR v1", ("hello", "HF SDR v1"))]
    bad = [(t, sl.parse(t)) for t, want in cases if sl.parse(t) != [want]]
    check("Parse hardware reply texts", not bad, "%d of %d ok" % (len(cases) - len(bad), len(cases)))

    # serial link against a simulated radio on a pty: no echo, text replies, banner at power-on,
    # and the radio complains if two commands arrive less than 100 ms apart
    if termios is not None:
        import pty
        master, slave = pty.openpty()
        port = os.ttyname(slave)
        state = {"f": 100, "p": 0, "a": 0, "tx": 0, "viol": 0, "last": 0.0, "n": 0,
                 "prev": "", "fgap": 9.9}           # fgap: shortest gap seen before / after an F command
        stop = threading.Event()

        def say(s):
            os.write(master, (s + "\r\n").encode())

        def radio():
            time.sleep(0.15)
            say("HF SDR v1")
            while not stop.is_set():
                r, _, _ = select.select([master], [], [], 0.05)
                if not r:
                    continue
                try:
                    data = os.read(master, 256).decode()
                except OSError:                         # port closed at the end of the test
                    break
                now = time.time()
                if now - state["last"] < 0.095:
                    state["viol"] += 1
                gap = now - state["last"]
                state["last"] = now
                for c in re.findall(r"\?[FPA]|F\d{5}|P[01]|A[01]|TX|RX", data):
                    state["n"] += 1
                    if c.startswith("F") or state["prev"].startswith("F"):
                        state["fgap"] = min(state["fgap"], gap)
                    state["prev"] = c
                    if c.startswith("F"):
                        state["f"] = int(c[1:])
                        say("Frequency Set to %d kHz" % state["f"])
                    elif c == "?F":
                        say("Frequency = %d kHz" % state["f"])
                    elif c in ("P0", "P1"):
                        state["p"] = int(c[1])
                        say("ok")                       # reply that does not say on/off: forces ?P
                    elif c in ("A0", "A1"):
                        state["a"] = int(c[1])
                        say("ok")
                    elif c == "?P":
                        say("Pre Amp = %s" % ("on" if state["p"] else "off"))
                    elif c == "?A":
                        say("Attenuator = %s" % ("on" if state["a"] else "off"))
                    elif c == "TX":
                        state["tx"] = 1
                        say("Tx Set")
                    elif c == "RX":
                        state["tx"] = 0
                        say("Rx Set")
        th = threading.Thread(target=radio, daemon=True)
        th.start()
        cfg = json.loads(json.dumps(DEFAULTS))
        cfg["serial_port"] = port
        msgs = []
        link = SerialLink(cfg, msgs.append)
        link.open()
        link.query_all()
        link.set_freq_khz(3650)
        link.set_flag("P", True)
        link.set_flag("A", True)
        got = []
        link.submit_txrx("TX", 0.0, got.append)
        link.set_freq_khz(7100)
        link.set_freq_khz(14250)            # merged with the one before: only one command goes out
        link.submit_txrx("RX", 0.0, got.append)
        t_end = time.time() + 10.0
        while len(got) < 2 and time.time() < t_end:
            time.sleep(0.05)
        time.sleep(0.5)
        # fast tuning: a new frequency every 40 ms for 2 s (mouse wheel / dragging on the spectrum)
        nf0 = sum(1 for m in msgs if re.match(r"hw> F\d{5}", m))
        f_radio0, f_hw0 = state["f"], link.hw["freq"]
        evs = []
        while not link.events.empty():
            evs.append(link.events.get())
        for k in range(50):
            link.set_freq_khz(7000 + k)
            if k % 10 == 0:
                link.query_all()
            time.sleep(0.04)
        t_end = time.time() + 15.0
        while (state["f"] != 7049 or not link.q.empty()) and time.time() < t_end:
            time.sleep(0.05)
        time.sleep(0.5)
        nf_fast = sum(1 for m in msgs if re.match(r"hw> F\d{5}", m)) - nf0
        link.close()
        os.close(master)
        os.close(slave)
        stop.set()
        check("Serial: banner 'HF SDR v1' seen", link.hw["version"] == "HF SDR v1", str(link.hw["version"]))
        check("Serial: frequency set, hardware reply read", f_radio0 == 14250 and f_hw0 == 14250,
              "radio=%s hw reply=%s" % (f_radio0, f_hw0))
        nf = nf0
        fresh = [e[1] for e in evs if e[0] == "freq" and e[2]]
        check("Serial: 3 frequency requests merged into 1 command", nf == 1 and fresh[-1] == 14250,
              "%d F command sent; stale replies ignored: %s" % (nf, [e[1] for e in evs if e[0] == "freq" and not e[2]]))
        check("Serial: preamp / attenuator via read-back", state["p"] == 1 and state["a"] == 1 and
              link.hw["pre"] is True and link.hw["att"] is True)
        check("Serial: TX then RX confirmed by replies", state["tx"] == 0 and got == [True, True] and
              link.hw["tx"] is False, "confirmed flags %s" % got)
        check("Serial: 100 ms spacing kept", state["viol"] == 0, "%d commands, %d too close" % (state["n"], state["viol"]))
        check("Serial: freq_gap kept around every F command", state["fgap"] >= cfg["freq_gap"] - 0.005,
              "shortest gap %.0f ms (freq_gap %.0f ms)" % (state["fgap"] * 1000, cfg["freq_gap"] * 1000))
        check("Serial: fast tuning thinned out, ends on last freq", state["f"] == 7049 and nf_fast < 15,
              "50 requests -> %d F commands, radio ends on %d kHz" % (nf_fast, state["f"]))
    if termios is not None:
        base = json.loads(json.dumps(DEFAULTS))
        for fw in ("1.0", "1.1"):
            pic, link, done = pic_session(fw, base)
            ok = (not pic.deaf and pic.overruns == 0 and pic.f == 14175 and link.hw["freq"] == 14175
                  and done == [True, True] and pic.p is False)
            check("PIC model fw %s: no overrun, never deaf" % fw, ok,
                  "%d commands, %d overruns, deaf=%s, radio %d kHz, TX/RX %s"
                  % (pic.ncmd, pic.overruns, pic.deaf, pic.f, done))
    # SSTV: encode a test card, 40 Hz mistuned + sender clock 200 ppm fast, decode from the VIS
    for name in ("Robot 36", "Martin M2", "PD120"):
        L = SstvLayout(name)
        card = fit_image(sstv_test_card(), L.w, L.h)
        au = sstv_encode(card, name).astype(np.float64)
        au = np.interp(np.arange(int(len(au) / 1.0002)) * 1.0002, np.arange(len(au)), au)
        sp = np.fft.rfft(au)
        k = int(round(40.0 * len(au) / 48000.0))
        au = np.fft.irfft(np.concatenate((np.zeros(k), sp[:-k])), len(au)) + 0.02 * rng.randn(len(au))
        sr = SstvRx()
        for i in range(0, len(au) - 2048, 2048):
            sr.rx(au[i:i + 2048])
        sr.rx(np.zeros(48000))
        done = [e for e in list(sr.events.queue) if e[0] == "done"]
        psnr = 0.0
        if done:
            mse = np.mean((done[-1][2][4:-4, 8:-8].astype(float) - card[4:-4, 8:-8]) ** 2)
            psnr = 10 * np.log10(255.0 ** 2 / max(mse, 1e-9))
        check("SSTV %s (VIS, 40 Hz off, 200 ppm)" % name, bool(done) and psnr > 22,
              "PSNR %.1f dB, offset %+.0f Hz" % (psnr, sr.offset))

    # NBTV: 2 frames, 20 Hz mistuned, sender clock 150 ppm fast, noise
    for name in ("48x48 Colour", "96x72 B&W", "Baird 30-line"):
        L = NbtvLayout(name)
        card = sstv_test_card()
        ntx = NbtvTx()
        ntx.start(name, card)
        au = ntx.tx_audio(int((1.5 + 2.2 * L.frame_s) * 48000))
        au = np.interp(np.arange(int(len(au) / 1.00015)) * 1.00015, np.arange(len(au)), au)
        sp = np.fft.rfft(au)
        k = int(round(20.0 * len(au) / 48000.0))
        au = np.fft.irfft(np.concatenate((np.zeros(k), sp[:-k])), len(au)) + 0.01 * rng.randn(len(au))
        nr = NbtvRx(name)
        for i in range(0, len(au) - 2048, 2048):
            nr.rx(au[i:i + 2048])
        frames = [e[1] for e in list(nr.events.queue) if e[0] == "frame"]
        ref = fit_image(card, L.w, L.h).astype(float)
        if not L.colour:
            ref = np.repeat((ref @ [0.299, 0.587, 0.114])[..., None], 3, 2)
        psnr = 10 * np.log10(255.0 ** 2 / max(np.mean((frames[-1] - ref) ** 2), 1e-9)) if frames else 0.0
        check("NBTV %s (20 Hz off, 150 ppm)" % name, psnr > 25,
              "PSNR %.1f dB, pilot %+.1f Hz, %.2f s/frame" % (psnr, nr.afc, L.frame_s))

    print("\n%s" % ("ALL TESTS PASSED" if not fails else "FAILED: " + ", ".join(fails)))
    return 1 if fails else 0


def serialtest(port):
    """Talk to the hardware alone (no sound, no window) to check the link."""
    cfg = load_cfg()
    if port:
        cfg["serial_port"] = port
    link = SerialLink(cfg, print)
    try:
        link.open()
    except Exception as e:
        print("serial:", e)
        return 1
    print("listening %.1f s for the power-on banner ..." % cfg["banner_wait"])
    time.sleep(cfg["banner_wait"] + 0.3)
    link.query_all()
    time.sleep(1.2)
    print("hardware says:", link.hw)
    print("Type a command (F03650, TX, RX, P1, A0, ?F, ?P, ?A) and press Enter; empty line or Ctrl-D quits.")
    try:
        while True:
            line = input("> ").strip()
            if not line:
                break
            link.send_raw(line)
            time.sleep(0.5)
    except (EOFError, KeyboardInterrupt):
        pass
    link.close()
    return 0


# ================================================================ logo and icons
# The ExSDR logo (Help) and the program icon in several sizes, as PNG in base64, so the
# program stays one file.  python3 exsdr.py --install-desktop puts the icon and a menu
# entry in the desktop's application menu.
LOGO_PNG = (
    "iVBORw0KGgoAAAANSUhEUgAAAXwAAACpCAMAAAAfvXbQAAABIFBMVEV67/tG3vg11/cxzfKSl5qIjI1IsM+BiIoe1vgfzPIb"
    "w+0YuOYZr94bo9Iaj79+g4R0en1obXBhZmkgfK1RYGxJWGZITlQ/Rkw6QEI3PD0gP38cNXAXL3YYL20XK24WK28WKm8WKWwW"
    "KWsXKWgWKGgaKl0XKWMXJ2IWKWMWJ2IWJmEXJlsVLG8VKWoVJ2gTJ2kUKGAUJmAWJWAWJFwWJFsWI1oWJFcVJFcWI1YVI1YS"
    "JGMTI1wTJFgTIlcSIVcWI1MWIlMVIlMVIVIVIk8VIE8WIUsUIlEUIU8UIE0SIlASIE4UH0wUHkoUHkgSH08PHlMSHkkUHkYT"
    "HkYUHUYTHUYTHUQTHUESHUQUHEUTHEMQHEoTHEERHEEOGUkPGDoKETdO8Q/XAABtVklEQVR42qVdCUNaS7M0MTE3i0ajZhFw"
    "Q5F9U0EWIaBsooCIogb1//+LV9U9cziguV9y38QtLih1+tT0dFd3z/z69WuE15ubX3fXV9e3t7fX13jfKw8vufoXWOfnveZ5"
    "rXnetqvZxIusdvMEq1EpN+rVSrX6U1f56OcRV7l8dJTNZSO5LFYmkylmMoeHB1j7B5GDQ7zBChzg3X5kfz+CT/NdhG/S+/w4"
    "HSjgg3Q6vZ+O4G06nE6lw+FUKoS34YAvpZ97YUUCgYP9Qmp/f7+wj1/Gdch1gH+Hmcgu/6CM/FG5owxXNsM/F394JZOpVOp4"
    "DpVKtV6pntTr1ZPGibPqfL6n+HciT7+Gdb7bvjgHRhcXvV7/st/vX14ObgeDy8FgIGBe3wDdkV3AmXDrmrEfjH5dXxF8fvvV"
    "sJkB+PgE8e/1zrGazYv2GP32ubkC8ic1yuVmvYr10+IP1M0VyOSyyawBH9hnBAlAfLAP8PcJ/r4Bn28IPt6k9VPpwD6B19d0"
    "OpUC+EngHg6FBPzw3hTouDbpZCSV3A/gJ/mzshT5jMKPjyN7uQz/HryWy7wIvAA5sRaCXy6XCT6sqVwt14m+azVPTk8bQP5U"
    "ba/WBPinhP6816tdDIjX5RWwv70ag39DxAV5gn/zDPybm7s7gn99i3/Xl8N+eXR1qeuih8eu9ZqnxLuGX3rKX4wL0MBfcHIq"
    "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")
ICON_PNG = {
    16: (
        "iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAYAAAAf8/9hAAACgklEQVR42nWTz2tUVxTHP+fc+94bNTExP6yhSQ0qtElB2lSy"
        "SYlduLBLoS7ctLtushAEN/6ACC1BBMVVdy7cZNHargvtKgj+BZpWZZoMaqJpq5nEGWfeO8fFGwlivHC4F+49534Wn6/AybB/"
        "vGvWNZzGbRe4AML2y0Ec0U2x4vrS3Y3ZMPLp5GyIlYtu7azT+L5mtu49CzGb7h5QZGT8uxaqARUBebvZHcy2AylJ3IuIaoIV"
        "UG+Uj9/McIc0gZ07S3LvFAKqJYmLRlptlx2pyDfHsb4+vChKzkqC3H2A/XkbYgpphCSCAy+bUBR4Gj1qJRW7cJrm9GGSuiOt"
        "Nu6G91SIt35HVtegvxd5uEzx7D80KPLJQbynG33yVKJ9OUl74jDJ/B/E+V9KMgBVbL0OXx8jn/mWeK9KOPcjOjVJfuZ7tFpD"
        "frhKLHr78EcvsKERWjMzgONm0NVFcucO3JwnSKR98gTx/FnywUFkcQkuXyNffkzURpOivgnP15GNTQiKmEGjidQ38Z7dyM+/"
        "EgcGeDXxBfqyQfbTDay6jOzpJfLoMb7RQO4tEhcWICbgjgPeakGeYxOfke/9AP2nimUZ7akp4nINbzQIPfLhrFhBMbQPHxvD"
        "Rz/CDh3Cj0ygWYJrIP/qKLK2RnrrN/j/OcWBA+jgXqRWQ0Y+PmWoig8PQwylC6qQpsirJqYRYkTXnsHKKmQZPjoK3V3oyqpH"
        "ggruSLW6JSuAOaig7qVIGmFHBcyQ+3+DGR4TiW7WFpFAGt9VuRMfpGNmYeU5TRzE3bxQcZ8LmirmghnvlL/ZfUtpcwmSqLjN"
        "hfV/xxa6+11F9HPwpPPlexJZhkhEN8zyK7W/ikuvAcNdJdJtcGQkAAAAAElFTkSuQmCC"),
    32: (
        "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"
        "L3+3WM9f0l8A+VWKiwajAm4AAAAASUVORK5CYII="),
    48: (
        "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"),
    64: (
        "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"
        "SUVORK5CYII="),
    128: (
        "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"),
    256: (
        "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"),
}


def set_window_icon(root):
    """Window / taskbar icon from the embedded PNGs (Tk 8.6 reads PNG)."""
    try:
        imgs = [tk.PhotoImage(data=ICON_PNG[s]) for s in (256, 128, 64, 48, 32, 16)]
        root.iconphoto(True, *imgs)
        root._exsdr_icons = imgs                     # keep them alive
    except Exception:
        pass


def install_desktop():
    """Icon in ~/.local/share/icons and a menu entry in ~/.local/share/applications."""
    import base64
    home = os.path.expanduser("~")
    for s, data in ICON_PNG.items():
        d = os.path.join(home, ".local", "share", "icons", "hicolor", "%dx%d" % (s, s), "apps")
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, "exsdr.png"), "wb") as f:
            f.write(base64.b64decode(data))
    app_dir = os.path.join(home, ".local", "share", "applications")
    os.makedirs(app_dir, exist_ok=True)
    path = os.path.join(app_dir, "exsdr.desktop")
    me = os.path.abspath(__file__)
    with open(path, "w") as f:
        f.write("[Desktop Entry]\nType=Application\nName=ExSDR\nGenericName=SDR transceiver\n"
                "Comment=Sound-card SDR transceiver: SSB, AM, FM, CW, digital modes, SSTV, NBTV\n"
                "Exec=\"%s\" \"%s\"\nIcon=exsdr\nTerminal=false\nCategories=HamRadio;Audio;Network;\n"
                "StartupWMClass=Exsdr\n" % (sys.executable, me))
    os.chmod(path, 0o755)
    try:
        subprocess.run(["gtk-update-icon-cache", "-q", os.path.join(home, ".local", "share", "icons", "hicolor")],
                       timeout=10, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except Exception:
        pass
    print("ExSDR added to the application menu:\n  %s\n  icons in ~/.local/share/icons/hicolor/*/apps/exsdr.png"
          % path)


def main():
    ap = argparse.ArgumentParser(description="ExSDR sound-card SDR transceiver")
    ap.add_argument("--install-desktop", action="store_true",
                    help="add ExSDR with its icon to the desktop's application menu")
    ap.add_argument("--selftest", action="store_true", help="run DSP and serial self tests (no GUI)")
    ap.add_argument("--demo", action="store_true", help="use built-in test signals instead of the sound card")
    ap.add_argument("--list-devices", action="store_true", help="list ALSA devices and serial ports")
    ap.add_argument("--serialtest", nargs="?", const="", metavar="PORT",
                    help="test the hardware link only, e.g. --serialtest /dev/ttyUSB0")
    args = ap.parse_args()
    if args.install_desktop:
        install_desktop()
        return
    if args.serialtest is not None:
        sys.exit(serialtest(args.serialtest))
    if args.selftest:
        sys.exit(selftest())
    if args.list_devices:
        for t, _ in list_alsa():
            print(t)
        print("serial ports:", " ".join(list_ports()) or "none found")
        return
    if tk is None:
        sys.exit("Tkinter is missing.  Install it with:  sudo apt install python3-tk")
    cfg = load_cfg()
    if args.demo:
        cfg["iq_in_dev"] = "demo"
    root = tk.Tk(className="exsdr")
    set_window_icon(root)
    App(root, cfg)
    root.mainloop()


if __name__ == "__main__":
    main()

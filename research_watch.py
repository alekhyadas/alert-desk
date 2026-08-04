#!/usr/bin/env python3
"""
Research watcher: tells you when the story around a holding changes.

Watches every ticker in holdings.csv for three things:
  1. A new analyst rating change (upgrade, downgrade, or fresh initiation)
  2. A meaningful move in the average analyst price target
  3. A new quarter of results appearing

When something changes it sends a plain-language explanation to Telegram and
email, with a chart of the last eight quarters where results are involved.

Timing, honestly: this is same-day, not instant. Yahoo publishes rating
changes and quarterly numbers on its own schedule, often hours behind the
actual announcement and sometimes a day. For true real-time you need a paid
terminal. This is for "don't let a downgrade sit unnoticed for a week".

Coverage, honestly: Yahoo's fundamentals for Indian smallcaps are patchy.
Large caps work well, recent IPOs often have nothing. A silent ticker means
no data, not no news.

Run it once a day. Every run only reports what CHANGED since the last run,
with state kept in research_state.json.
"""

import csv
import io
import json
import os
import smtplib
import time
import urllib.parse
import urllib.request
import uuid
from datetime import datetime
from email.mime.image import MIMEImage
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from pathlib import Path
from zoneinfo import ZoneInfo

BASE_DIR = Path(__file__).resolve().parent
HOLDINGS_CSV = BASE_DIR / "holdings.csv"
STATE_FILE = BASE_DIR / "research_state.json"

SUFFIX = {"NSE": ".NS", "BSE": ".BO", "US": ""}
IST = ZoneInfo("Asia/Kolkata")

# A target move smaller than this is model noise, not news.
TARGET_MOVE_PCT = 2.0
EARNINGS_WARN_DAYS = 3      # heads-up window before a scheduled results date

# When a holding is seen for the first time, its latest quarter is normally
# recorded as a baseline rather than announced, otherwise every stock would
# report old news on day one. But a genuinely recent quarter should still be
# reported: that is the difference between a baseline and a missed result.
CATCHUP_DAYS = 75
# Telegram takes one photo per message, so a large catch-up would arrive as
# dozens of pushes. Beyond this the write-up still goes out, just without a chart.
MAX_CHARTS_PER_RUN = 6
PACE_SECONDS = 1.5          # be polite to Yahoo
# A ceiling only to stop a pathological holdings file from running for hours.
# At roughly 4.5s per symbol a full pass over ~120 names takes about 9 minutes,
# well inside the workflow timeout, and once a day that is a small share of
# the monthly Actions budget. Anything beyond this is reported rather than
# dropped in silence, because a quietly ignored holding is worse than a slow run.
MAX_SYMBOLS = 200

INK, PANEL, LINE = "#160A0C", "#241114", "#47232A"
PAPER, MUTED = "#F4EAE7", "#C29CA1"
CRIMSON, GREEN, AMBER = "#D24A4F", "#63B98A", "#E0A44C"


# ----------------------------------------------------------------------
# Inputs
# ----------------------------------------------------------------------

def load_symbols():
    """Unique (symbol, ticker, exchange) from holdings.csv, preserving order."""
    if not HOLDINGS_CSV.exists():
        return []
    seen, out = set(), []
    with open(HOLDINGS_CSV, newline="", encoding="utf-8-sig") as f:
        for row in csv.DictReader(f):
            row = {k.strip().lower(): (v or "").strip() for k, v in row.items() if k}
            tk, ex = row.get("ticker", "").upper(), row.get("exchange", "").upper()
            if not tk or ex not in SUFFIX:
                continue
            if row.get("enabled", "yes").lower() in ("no", "false", "0", "off"):
                continue
            sym = tk + SUFFIX[ex]
            if sym in seen:
                continue
            seen.add(sym)
            out.append((sym, tk, ex))
    if len(out) > MAX_SYMBOLS:
        print(f"WARNING: {len(out)} symbols found, only the first {MAX_SYMBOLS} "
              f"will be checked. Not watched: "
              + ", ".join(t for _, t, _ in out[MAX_SYMBOLS:]))
    return out[:MAX_SYMBOLS]


def load_state():
    if STATE_FILE.exists():
        try:
            return json.loads(STATE_FILE.read_text())
        except json.JSONDecodeError:
            print("WARNING: research_state.json unreadable, starting fresh")
    return {}


def save_state(state):
    STATE_FILE.write_text(json.dumps(state, indent=2, sort_keys=True) + "\n")


# ----------------------------------------------------------------------
# Fetching
# ----------------------------------------------------------------------

def fetch_research(symbol):
    """Current research picture for one symbol. Never raises."""
    out = {"ratings": [], "target": None, "quarter": None, "quarters": [],
           "balance": [], "news": [], "next_earnings": None,
           "next_earnings_in": None}
    try:
        import yfinance as yf
        import pandas as pd
        t = yf.Ticker(symbol)

        try:
            ud = t.upgrades_downgrades
            if ud is not None and len(ud) > 0:
                s = ud.sort_index(ascending=False)
                idx = s.index
                idx_n = idx.tz_localize(None) if idx.tz is not None else idx
                cutoff = pd.Timestamp.utcnow().tz_localize(None) - pd.Timedelta(days=120)
                for dt, r in s[idx_n >= cutoff].iterrows():
                    out["ratings"].append({
                        "id": f"{dt.strftime('%Y-%m-%d')}|{r.get('Firm', '?')}|"
                              f"{r.get('ToGrade', '')}",
                        "date": dt.strftime("%d %b %Y"),
                        "firm": str(r.get("Firm", "?")),
                        "to": str(r.get("ToGrade", "") or "?"),
                        "frm": str(r.get("FromGrade", "") or ""),
                        "action": str(r.get("Action", "")).lower(),
                    })
        except Exception:
            pass

        try:
            apt = t.analyst_price_targets or {}
            if apt.get("mean"):
                out["target"] = round(float(apt["mean"]), 2)
            for k, dst in (("low", "target_low"), ("high", "target_high")):
                if apt.get(k):
                    out[dst] = round(float(apt[k]), 2)
        except Exception:
            pass
        try:
            info = t.info
            if info.get("numberOfAnalystOpinions"):
                out["n_analysts"] = int(info["numberOfAnalystOpinions"])
            if info.get("currentPrice"):
                out["price"] = float(info["currentPrice"])
        except Exception:
            pass

        try:
            q = t.quarterly_income_stmt
            if q is not None and not q.empty:
                cols = sorted(q.columns, reverse=True)[:8]

                def pick(names, col):
                    for n in names:
                        if n in q.index:
                            v = q.loc[n, col]
                            if v == v and v is not None:
                                return float(v)
                    return None

                for c in cols:
                    rev = pick(["Total Revenue", "Operating Revenue"], c)
                    net = pick(["Net Income", "Net Income Common Stockholders",
                                "Net Income Continuous Operations"], c)
                    if rev is None and net is None:
                        continue
                    gross = pick(["Gross Profit"], c)
                    cogs = pick(["Cost Of Revenue"], c)
                    if gross is None and rev is not None and cogs is not None:
                        gross = rev - cogs
                    op = pick(["Operating Income", "Total Operating Income As Reported"], c)
                    ebitda = pick(["EBITDA", "Normalized EBITDA"], c)
                    interest = pick(["Interest Expense", "Interest Expense Non Operating"], c)
                    tax = pick(["Tax Provision"], c)
                    pretax = pick(["Pretax Income"], c)
                    opex = pick(["Operating Expense", "Total Expenses"], c)
                    # Individual cost lines: this is where "why" actually
                    # lives. A margin fall caused by raw material is a
                    # different problem from one caused by staff or ad spend.
                    parts = {}
                    for label, names in (
                            ("cost of goods", ["Cost Of Revenue"]),
                            ("staff and admin", ["Selling General And Administration",
                                                 "General And Administrative Expense"]),
                            ("selling and marketing", ["Selling And Marketing Expense"]),
                            ("research", ["Research And Development"]),
                            ("depreciation", ["Reconciled Depreciation",
                                              "Depreciation And Amortization"
                                              " In Income Statement"]),
                            ("other operating", ["Other Operating Expenses"]),
                            ("interest", ["Interest Expense",
                                          "Interest Expense Non Operating"]),
                            ("tax", ["Tax Provision"])):
                        v = pick(names, c)
                        if v is not None:
                            parts[label] = v

                    def m(x):
                        return (x / rev * 100) if (rev and x is not None and rev != 0) else None

                    out["quarters"].append({
                        "period": c.strftime("%b %Y") if hasattr(c, "strftime") else str(c)[:10],
                        "sort": c.strftime("%Y-%m") if hasattr(c, "strftime") else str(c)[:7],
                        "revenue": rev, "net": net, "gross": gross, "op": op,
                        "ebitda": ebitda, "interest": interest, "tax": tax,
                        "pretax": pretax, "opex": opex,
                        "parts": parts,
                        "margin": m(net), "gross_margin": m(gross),
                        "op_margin": m(op), "ebitda_margin": m(ebitda),
                    })
                if out["quarters"]:
                    out["quarter"] = out["quarters"][0]["sort"]
        except Exception:
            pass

        # Balance-sheet items for working-capital flags
        try:
            b = t.quarterly_balance_sheet
            if b is not None and not b.empty:
                bc = sorted(b.columns, reverse=True)[:5]

                def bpick(names, col):
                    for n in names:
                        if n in b.index:
                            v = b.loc[n, col]
                            if v == v and v is not None:
                                return float(v)
                    return None
                for c in bc:
                    out["balance"].append({
                        "sort": c.strftime("%Y-%m") if hasattr(c, "strftime") else str(c)[:7],
                        "receivables": bpick(["Accounts Receivable",
                                              "Gross Accounts Receivable"], c),
                        "inventory": bpick(["Inventory"], c),
                        "debt": bpick(["Total Debt", "Long Term Debt"], c),
                    })
        except Exception:
            pass

        # Did the last reported quarter beat or miss what analysts expected?
        # This is the single most direct answer to "how were the results",
        # and it is in the same table as the scheduled dates.
        try:
            import pandas as pd
            ed = t.earnings_dates
            if ed is not None and len(ed) > 0:
                idx = ed.index
                idx_n = idx.tz_localize(None) if idx.tz is not None else idx
                now_n = pd.Timestamp.now("UTC").tz_localize(None)
                past = [(d, r) for d, r in zip(idx_n, ed.to_dict("records"))
                        if d <= now_n]
                past.sort(key=lambda x: x[0], reverse=True)
                for d, r in past[:1]:
                    est, act = r.get("EPS Estimate"), r.get("Reported EPS")
                    if est == est and act == act and est not in (None, 0):
                        out["eps_est"] = float(est)
                        out["eps_act"] = float(act)
                        out["eps_surprise"] = (float(act) / float(est) - 1) * 100
                        out["eps_date"] = d.strftime("%d %b %Y")
                hist = []
                for d, r in past[:5]:
                    sp = r.get("Surprise(%)")
                    if sp == sp and sp is not None:
                        hist.append(float(sp))
                if hist:
                    out["surprise_history"] = hist
        except Exception:
            pass

        # Scheduled results date. Announced in advance and far more timely
        # than waiting for Yahoo to publish the actual numbers, which for
        # Indian companies can lag the filing by weeks.
        try:
            import pandas as pd
            ed = t.earnings_dates
            if ed is not None and len(ed) > 0:
                idx = ed.index
                idx_n = idx.tz_localize(None) if idx.tz is not None else idx
                now_n = pd.Timestamp.now('UTC').tz_localize(None)
                future = sorted([d for d in idx_n if d >= now_n])
                if future:
                    out["next_earnings"] = future[0].strftime("%Y-%m-%d")
                    # Compare calendar dates, not timestamps: subtracting
                    # timestamps truncates the part-day and reports a date two
                    # days out as "tomorrow".
                    out["next_earnings_in"] = (future[0].date() - now_n.date()).days
        except Exception:
            pass

        # Headlines with summaries, ranked by relevance to this company.
        # Yahoo's feed mixes company news with generic market pieces, and a
        # story about interest rates in general explains nothing about why
        # one company's quarter looked the way it did.
        # but financial media routinely report the rationale behind a
        # downgrade, and that reporting is in this feed.
        try:
            import datetime as _dt
            import re as _re0
            for n in (t.news or [])[:20]:
                c = n.get("content", n)
                title = c.get("title") or n.get("title")
                if not title:
                    continue
                link = ((c.get("canonicalUrl") or {}).get("url")
                        or (c.get("clickThroughUrl") or {}).get("url")
                        or n.get("link", ""))
                _raw_summary = (c.get("summary") or c.get("description")
                                or c.get("excerpt") or c.get("snippet")
                                or n.get("summary") or n.get("description") or "")
                if isinstance(_raw_summary, dict):
                    _raw_summary = _raw_summary.get("text", "") or ""
                summary = _re0.sub(r"\s*\((?:BOM|NSE|BSE|NS)[:\s][^)]*\)", "",
                                   str(_raw_summary))
                pub = (c.get("pubDate") or c.get("displayTime")
                       or n.get("providerPublishTime") or "")
                when = None
                if isinstance(pub, (int, float)):
                    when = _dt.datetime.fromtimestamp(pub)
                elif isinstance(pub, str) and pub:
                    try:
                        when = _dt.datetime.fromisoformat(pub.replace("Z", "+00:00"))
                        when = when.replace(tzinfo=None)
                    except ValueError:
                        pass
                prov = ""
                pr = c.get("provider") or n.get("publisher")
                if isinstance(pr, dict):
                    prov = pr.get("displayName", "")
                elif isinstance(pr, str):
                    prov = pr
                # "Birlasoft Ltd (BOM:532400) Q1 2027 Earnings Call
                # Highlights: ..." carries an exchange code and a stock phrase
                # that add nothing and crowd out the actual point.
                title = _re0.sub(r"\s*\((?:BOM|NSE|BSE|NS)[:\s][^)]*\)", "",
                                 str(title))
                title = _re0.sub(r"\s*Earnings Call Highlights:\s*", ": ", title)
                title = _re0.sub(r"\s{2,}", " ", title)
                # Feed headlines often arrive pre-truncated with a trailing
                # ellipsis, which reads as if the message itself was cut off.
                title = _re0.sub(r"\s*(\.{3}|\u2026)\s*$", "", title)
                # Removing a trailing ellipsis can leave the headline hanging
                # on a conjunction, e.g. "Strong Revenue Growth and".
                title = _re0.sub(r"\s+(and|with|amid|amidst|as|despite|on|for|"
                                 r"to|in|of|the|a)\s*$", "", title,
                                 flags=_re0.IGNORECASE).strip(" :-,")
                out["news"].append({"title": title[:160],
                                    "summary": str(summary)[:400],
                                    "link": link, "provider": prov,
                                    "when": when})
            # Company-specific stories first, then ones with any summary at
            # all, then the rest. Recency breaks ties.
            import re as _re
            def _norm(x):
                return _re.sub(r"[^a-z0-9]", "", x.lower())
            base = _norm(symbol.split(".")[0])
            def _score(n):
                blob = (n["title"] + " " + n.get("summary", "")).lower()
                sc = 0
                # Compare like with like: the ticker and the article text are
                # both stripped to letters and digits, so M&MFIN can match
                # "M&M Financial" and "MM Financial" alike.
                if base and base[:5] in _norm(blob):
                    sc += 4
                if any(w in blob for w in ("q1", "q2", "q3", "q4", "quarter",
                                           "results", "earnings", "profit")):
                    sc += 2
                if n.get("summary"):
                    sc += 1
                # Wire agencies and Indian financial press report what was
                # said; aggregators mostly restate the headline.
                prov = (n.get("provider") or "").lower()
                if any(x in prov for x in ("reuters", "moneycontrol", "mint",
                                           "economic times", "business standard",
                                           "bloomberg", "cnbc")):
                    sc += 3
                return sc
            # A results alert should carry coverage of THIS quarter. Older
            # earnings-call pieces are not wrong, they are simply about a
            # different quarter, and mixing them in is how the message became
            # three unrelated stories stacked together.
            fresh_cut = _dt.datetime.now() - _dt.timedelta(days=45)
            fresh = [n for n in out["news"]
                     if not n.get("when") or n["when"] >= fresh_cut]
            if fresh:
                out["news"] = fresh
            out["news"].sort(key=lambda n: (-_score(n),
                                            -(n["when"].timestamp() if n.get("when") else 0)))
        except Exception:
            pass

    except Exception as e:  # noqa: BLE001
        out["error"] = str(e)[:100]
    return out


# ----------------------------------------------------------------------
# Change detection
# ----------------------------------------------------------------------

def detect(prev, now):
    """Return a list of event dicts describing what changed."""
    events = []

    seen = set(prev.get("rating_ids", []))
    for r in now["ratings"]:
        if r["id"] not in seen:
            events.append({"kind": "rating", **r, "news": now.get("news", [])})

    old_t, new_t = prev.get("target"), now.get("target")
    if old_t and new_t and old_t != 0:
        move = (new_t / old_t - 1) * 100
        if abs(move) >= TARGET_MOVE_PCT:
            events.append({"kind": "target", "old": old_t, "new": new_t,
                           "move": move, "n": now.get("n_analysts"),
                           "low": now.get("target_low"),
                           "high": now.get("target_high"),
                           "price": now.get("price"),
                           "ratings": now.get("ratings", []),
                           "news": now.get("news", [])})

    ne, days = now.get("next_earnings"), now.get("next_earnings_in")
    if ne and days is not None and 0 <= days <= EARNINGS_WARN_DAYS:
        if prev.get("earnings_warned") != ne:
            events.append({"kind": "upcoming", "date": ne, "days": days})

    if now.get("quarter") and now["quarter"] != prev.get("quarter"):
        first_sighting = prev.get("quarter") is None
        report = not first_sighting
        if first_sighting:
            # Never seen before. Report only if the quarter is recent enough
            # to still be news, so newly added holdings catch up instead of
            # waiting a full quarter to say anything.
            try:
                import datetime as _dt
                q_end = _dt.datetime.strptime(now["quarter"] + "-01", "%Y-%m-%d")
                # quarter key is the period-end month, so allow to month end
                age = (_dt.datetime.now() - q_end).days - 30
                report = age <= CATCHUP_DAYS
            except (ValueError, TypeError):
                report = False
        if report:
            events.append({"kind": "results", "quarters": now["quarters"],
                           "balance": now.get("balance"), "news": now.get("news"),
                           "catchup": first_sighting,
                           "eps_est": now.get("eps_est"),
                           "eps_act": now.get("eps_act"),
                           "eps_surprise": now.get("eps_surprise"),
                           "surprise_history": now.get("surprise_history")})

    return events


# ----------------------------------------------------------------------
# Plain language
# ----------------------------------------------------------------------

def crore(v):
    """Indian readers think in crore, not billions."""
    if v is None:
        return "n/a"
    return f"{v / 1e7:,.0f} Cr"


def _pct(a, b):
    if a is None or b is None or b == 0:
        return None
    return (a / b - 1) * 100


def locate_margin_move(q, ref, label):
    """Say WHERE margin moved by walking down the P&L.

    Gross margin covers input cost and pricing. Operating margin adds
    overheads, staff and advertising. Net adds interest and tax. Whichever
    step changed most is where the pressure actually sits, which is a very
    different diagnosis in each case.
    """
    if not ref:
        return []
    steps = []
    for key, name, meaning in (
            ("gross_margin", "Gross margin", "input costs or pricing"),
            ("op_margin", "Operating margin", "overheads, staff, ad spend"),
            ("margin", "Net margin", "interest and tax")):
        a, b = q.get(key), ref.get(key)
        if a is not None and b is not None:
            steps.append((key, name, meaning, a, b, a - b))
    if not steps:
        return []

    out = [f"Margin walk vs {label}:"]
    for _, name, _, a, b, d in steps:
        out.append(f"  {name} {b:.1f}% to {a:.1f}% ({d:+.1f} pts)")

    # Read the bottom line FIRST, then locate it. An earlier version tested
    # gross margin alone, so a company whose input costs rose while operating
    # and net margins both widened was told its margins were being squeezed.
    # That is not a wording problem, it is the tool asserting something false.
    gross_d = next((d for k, _, _, _, _, d in steps if k == "gross_margin"), None)
    op_d = next((d for k, _, _, _, _, d in steps if k == "op_margin"), None)
    net_d = next((d for k, _, _, _, _, d in steps if k == "margin"), None)
    bottom = net_d if net_d is not None else op_d
    if bottom is None:
        return out

    if bottom > 0.5:
        if gross_d is not None and gross_d < -0.5:
            out.append("  Input costs rose or prices fell, but that was more "
                       "than made up for further down: the bottom line still "
                       "widened, from overheads, interest or tax.")
        elif gross_d is not None and gross_d > 0.5:
            out.append("  The improvement starts at the top, with better "
                       "pricing or cheaper inputs, and it carried through.")
        else:
            out.append("  Gross margin held steady, so the improvement came "
                       "from below it: overheads, interest or tax.")
    elif bottom < -0.5:
        if (gross_d is not None and op_d is not None
                and gross_d < -0.5 and op_d < gross_d - 0.5):
            # Both levels fell, and operating fell further. Saying only "the
            # squeeze starts at the top" would contradict the cost breakdown
            # below, which names overheads as the larger drag.
            out.append(f"  Costs rose at both levels: {abs(gross_d):.1f} points "
                       f"went at the gross line, from inputs or pricing, and a "
                       f"further {abs(op_d - gross_d):.1f} points below it, from "
                       f"overheads and other operating costs.")
        elif gross_d is not None and gross_d < -0.5:
            out.append("  The squeeze starts at the top: they are paying more "
                       "for inputs or charging less, not overspending below it.")
        elif op_d is not None and op_d < -0.5:
            out.append("  Gross margin held but operating margin fell, so this "
                       "is cost below the production line: overheads, headcount "
                       "or spending to win sales.")
        else:
            out.append("  The business itself held up; the damage is below "
                       "operating profit, so interest cost or tax.")
    else:
        out.append("  Margins broadly steady on all three lines.")

    # A net margin above the operating margin is not a better business, it is
    # income earned outside operations: treasury, one-offs, asset sales. Left
    # unsaid, the walk reads as if profitability improved down the P&L.
    op_m, net_m = q.get("op_margin"), q.get("margin")
    if op_m is not None and net_m is not None and net_m > op_m + 1:
        out.append(f"  Note: net margin ({net_m:.1f}%) sits ABOVE operating "
                   f"margin ({op_m:.1f}%), so part of the profit came from "
                   f"outside the core business, such as treasury income or a "
                   f"one-off. The operating line is the better guide to trading.")
    return out

def build_flags(quarters, balance):
    """Mechanical flags. Each is a factual pattern in the numbers, not a
    forecast and not a view on the shares. They exist to make you look
    somewhere specific, not to conclude anything."""
    flags = []
    if not quarters:
        return flags
    q = quarters[0]

    # Margin falling several quarters running
    ms = [x.get("margin") for x in quarters[:4] if x.get("margin") is not None]
    if len(ms) >= 3 and all(ms[i] < ms[i + 1] for i in range(len(ms) - 1)):
        flags.append(f"Net margin has fallen {len(ms)} quarters in a row "
                     f"({ms[-1]:.1f}% to {ms[0]:.1f}%). A trend, not a quarter.")

    # Profit propped up by something other than the business
    yoy = quarters[4] if len(quarters) > 4 else None
    if yoy:
        op_g, net_g = _pct(q.get("op"), yoy.get("op")), _pct(q.get("net"), yoy.get("net"))
        if op_g is not None and net_g is not None and op_g < -3 and net_g > 3:
            flags.append("Operating profit fell but net profit rose, so "
                         "something below the operating line is holding the "
                         "bottom line up. Worth checking for one-off income.")
        if op_g is not None and net_g is not None and op_g > 3 and net_g < -3:
            flags.append("Operating profit rose but net profit fell, so "
                         "interest, tax or a write-off ate the gain.")

    # Growth losing steam
    revs = [x.get("revenue") for x in quarters[:6] if x.get("revenue")]
    if len(revs) >= 5:
        g_now, g_prev = _pct(revs[0], revs[4]), _pct(revs[1], revs[5] if len(revs) > 5 else None)
        if g_now is not None and g_prev is not None and g_prev > 5 and g_now < g_prev - 5:
            flags.append(f"Revenue growth is decelerating: {g_now:+.0f}% this "
                         f"quarter against {g_prev:+.0f}% last, both year on year.")

    # Interest rising faster than sales
    if yoy and q.get("interest") and yoy.get("interest"):
        i_g, r_g = _pct(q["interest"], yoy["interest"]), _pct(q.get("revenue"), yoy.get("revenue"))
        if i_g is not None and r_g is not None and i_g > 20 and i_g > r_g + 15:
            flags.append(f"Interest cost up {i_g:.0f}% year on year while "
                         f"revenue moved {r_g:+.0f}%. Debt is growing faster "
                         f"than the business it funds.")

    # Receivables outrunning sales: the classic revenue-quality question
    if len(balance) >= 5 and yoy:
        rec_now = balance[0].get("receivables")
        rec_yoy = balance[4].get("receivables") if len(balance) > 4 else None
        if rec_now and rec_yoy:
            rec_g, rev_g = _pct(rec_now, rec_yoy), _pct(q.get("revenue"), yoy.get("revenue"))
            if rec_g is not None and rev_g is not None and rec_g > rev_g + 20:
                flags.append(f"Receivables up {rec_g:.0f}% against revenue "
                             f"{rev_g:+.0f}%. Sales are being booked faster "
                             f"than cash is coming in.")
    return flags




def why_it_moved(q, ref):
    """Name the cost lines responsible, and size them in rupees.

    "Margins fell" is a restatement of the numbers. This asks the next
    question: which costs grew faster than sales, and what did that cost in
    rupees of profit. Every figure is a subtraction between two reported
    lines, so it names causes inside the P&L without claiming to know why
    management let them move.
    """
    if not ref or not q.get("revenue") or not ref.get("revenue"):
        return []
    rev_g = (q["revenue"] / ref["revenue"] - 1) * 100
    out, movers = [], []
    for label, now_v in (q.get("parts") or {}).items():
        was = (ref.get("parts") or {}).get(label)
        if was is None or was == 0 or now_v is None:
            continue
        g = (now_v / was - 1) * 100
        # What the change in this line cost, over and above what revenue
        # growth alone would have justified.
        drag = now_v - was * (q["revenue"] / ref["revenue"])
        movers.append((label, g, drag, now_v, was))
    if not movers:
        return []

    movers.sort(key=lambda x: -abs(x[2]))
    worst = [m for m in movers if m[2] > 0][:3]
    best = [m for m in movers if m[2] < 0][:2]

    out.append(f"Revenue {'grew' if rev_g >= 0 else 'fell'} "
               f"{abs(rev_g):.0f}%. Against that:")
    for label, g, drag, now_v, was in worst:
        out.append(f"  {label} {g:+.0f}% to {crore(now_v)}, which is "
                   f"{crore(abs(drag))} more than revenue growth alone "
                   f"would explain")
    for label, g, drag, now_v, was in best:
        out.append(f"  {label} {g:+.0f}% to {crore(now_v)}, {crore(abs(drag))} "
                   f"less than revenue growth would imply, which helped")

    if worst:
        top = worst[0]
        out.append(f"  So the single biggest drag was {top[0]}, costing about "
                   f"{crore(abs(top[2]))} of profit this quarter.")

    # What profit would have been had the cost shape held
    if q.get("net") is not None and ref.get("net") is not None and ref.get("margin"):
        would = q["revenue"] * ref["margin"] / 100
        gap = q["net"] - would
        if abs(gap) > 0.02 * abs(would):
            out.append(f"  At last year's margin, this revenue would have "
                       f"produced {crore(would)} of net profit instead of "
                       f"{crore(q['net'])}, a difference of {crore(abs(gap))}.")
    return out


def quarter_context(quarters, eps=None):
    """Answer the question the raw numbers do not: was this a good quarter?

    Three angles, because each can contradict the others and the tension is
    the useful part. Against what analysts expected. Against last quarter,
    not just last year, since a year-on-year figure hides a recent turn.
    And against the company's own recent range, so a "record" is visibly a
    record rather than just a big number.
    """
    if not quarters:
        return []
    q = quarters[0]
    prev = quarters[1] if len(quarters) > 1 else None
    out = []

    if eps and eps.get("eps_surprise") is not None:
        sp = eps["eps_surprise"]
        word = "beat" if sp > 1 else ("missed" if sp < -1 else "matched")
        line = (f"Earnings per share {word} what analysts expected: "
                f"{eps['eps_act']:.2f} against {eps['eps_est']:.2f}")
        if abs(sp) >= 1:
            line += f", {abs(sp):.0f}% {'above' if sp > 0 else 'below'}"
        out.append(line + ".")
        hist = eps.get("surprise_history") or []
        if len(hist) >= 3:
            beats = sum(1 for x in hist if x > 0)
            out.append(f"  Beat in {beats} of the last {len(hist)} quarters.")

    if prev:
        for key, name in (("revenue", "Revenue"), ("net", "Net profit")):
            a, b = q.get(key), prev.get(key)
            if a is not None and b is not None and b != 0:
                ch = (a / b - 1) * 100
                if abs(ch) >= 1:
                    out.append(f"{name} {'up' if ch > 0 else 'down'} "
                               f"{abs(ch):.0f}% on last quarter "
                               f"({prev['period']}), not just on last year.")

    revs = [x.get("revenue") for x in quarters if x.get("revenue")]
    nets = [x.get("net") for x in quarters if x.get("net") is not None]
    margins = [x.get("margin") for x in quarters if x.get("margin") is not None]
    if len(revs) >= 4 and q.get("revenue") == max(revs):
        out.append(f"Highest revenue of the last {len(revs)} quarters.")
    if len(nets) >= 4 and q.get("net") is not None:
        if q["net"] == max(nets):
            out.append(f"Highest net profit of the last {len(nets)} quarters.")
        elif q["net"] == min(nets):
            out.append(f"Lowest net profit of the last {len(nets)} quarters.")
    if len(margins) >= 4 and q.get("margin") is not None:
        if q["margin"] == max(margins):
            out.append(f"Best net margin of the last {len(margins)} quarters.")
        elif q["margin"] == min(margins):
            out.append(f"Weakest net margin of the last {len(margins)} quarters.")

    # Is growth speeding up or slowing down?
    if len(quarters) > 5:
        g_now = _pct(q.get("revenue"), quarters[4].get("revenue"))
        g_prev = _pct(quarters[1].get("revenue"), quarters[5].get("revenue"))
        if g_now is not None and g_prev is not None and abs(g_now - g_prev) >= 3:
            out.append(f"Revenue growth {'speeding up' if g_now > g_prev else 'slowing'}: "
                       f"{g_now:+.0f}% this quarter against {g_prev:+.0f}% last, "
                       f"both measured against a year earlier.")
    return out


def explain_results(quarters, balance=None, news=None, ticker="", exchange="NSE",
                    next_earnings=None, eps=None):
    """Full plain-language write-up of a quarter: the headline numbers, where
    the margin actually moved, mechanical flags, and where to read what
    management themselves said."""
    if not quarters:
        return []
    q = quarters[0]
    prev_q = quarters[1] if len(quarters) > 1 else None
    yoy = quarters[4] if len(quarters) > 4 else None

    lines = [f"Quarter ending {q['period']}", ""]
    lines.append("THE NUMBERS")
    if q["revenue"] is not None:
        rg = _pct(q["revenue"], yoy["revenue"]) if yoy else None
        lines.append(f"  Revenue {crore(q['revenue'])}"
                     + (f"  ({rg:+.0f}% YoY)" if rg is not None else ""))
    if q.get("op") is not None:
        og = _pct(q["op"], yoy.get("op")) if yoy else None
        lines.append(f"  Operating profit {crore(q['op'])}"
                     + (f"  ({og:+.0f}% YoY)" if og is not None else ""))
    if q["net"] is not None:
        ng = _pct(q["net"], yoy["net"]) if yoy else None
        lines.append(f"  Net profit {crore(q['net'])}"
                     + (f"  ({ng:+.0f}% YoY)" if ng is not None else ""))
    if q.get("interest"):
        lines.append(f"  Interest cost {crore(q['interest'])}")

    # The one-line human summary
    if yoy:
        rg, ng = _pct(q["revenue"], yoy["revenue"]), _pct(q["net"], yoy["net"])
        if rg is not None and ng is not None:
            lines.append("")
            if rg > 2 and ng < -2:
                lines.append("  In short: they sold more but kept less of it.")
            elif rg < -2 and ng > 2:
                lines.append("  In short: they sold less but kept more of it.")
            elif rg > 2 and ng > rg + 5:
                lines.append("  In short: profit grew faster than sales, which "
                             "is operating leverage working for them.")
            elif rg < -2 and ng < -2:
                lines.append("  In short: both sales and profit shrank.")
            elif abs(rg) <= 2 and abs(ng) <= 2:
                lines.append("  In short: broadly flat on both lines.")
            elif rg > 2 and ng > 2:
                lines.append("  In short: sales and profit grew at a similar "
                             "pace, so the shape of the business is unchanged.")
            else:
                lines.append(f"  In short: revenue {rg:+.0f}% and profit "
                             f"{ng:+.0f}% against a year ago.")

    ctx = quarter_context(quarters, eps)
    if ctx:
        lines.append("")
        lines.append("WAS IT A GOOD QUARTER")
        for c in ctx:
            lines.append(f"  {c}" if not c.startswith("  ") else c)

    walk = locate_margin_move(q, yoy, "a year ago") or \
        locate_margin_move(q, prev_q, "last quarter")
    if walk:
        lines.append("")
        lines.append("WHERE THE MARGIN MOVED")
        lines.extend("  " + w if not w.startswith("  ") else w for w in walk)

    why = why_it_moved(q, yoy) if yoy else []
    if why:
        lines.append("")
        lines.append("WHY IT MOVED")
        for w in why:
            lines.append(w if w.startswith("  ") else f"  {w}")

    flags = build_flags(quarters, balance or [])
    if flags:
        lines.append("")
        lines.append("FLAGS")
        for f in flags:
            lines.append(f"  - {f}")

    if news:
        lines.append("")
        lines.append("IN THE NEWS")
        # Titles alone say nothing about why the quarter looked as it did.
        # The summary usually carries management's own explanation, and the
        # plain-English pass strips the research vocabulary out of it.
        for n in news[:3]:
            lines.append(f"  {n['title']}")
            summary = (n.get("summary") or "").strip()
            if summary:
                txt = summary if len(summary) <= 260 else \
                    summary[:260].rsplit(" ", 1)[0] + " [...]"
                # Yahoo often supplies an already-clipped summary that stops
                # mid-sentence. Say so, rather than leaving a dangling phrase
                # that reads like the alert itself failed.
                if len(summary) <= 260 and not summary.rstrip().endswith((".", "!", "?", "\"")):
                    txt = txt.rstrip() + " [...]"
                lines.append(f"    {txt}")
                lines.extend(format_plain(summary, indent="    "))
            if n.get("provider"):
                lines.append(f"    {n['provider']}")
            if n.get("link"):
                lines.append(f"    {n['link']}")

    lines.append("")
    lines.append("WHAT MANAGEMENT SAID")
    lines.append("  Not available in any free data feed. The filing and the "
                 "earnings call commentary are here:")
    if exchange in ("NSE", "BSE"):
        lines.append(f"  https://www.screener.in/company/{ticker}/")
        lines.append(f"  https://www.nseindia.com/get-quotes/equity?symbol={ticker}")
    if next_earnings:
        lines.append("")
        lines.append(f"NEXT RESULTS DUE  {next_earnings}")
    lines.append("")
    lines.append("Flags are patterns in the numbers, not conclusions.")
    return lines





# Equity research is written for people who already speak it. This maps the
# recurring vocabulary to plain English. Only terms actually present in a
# given article are shown, so the explanation stays short and relevant.
JARGON = {
    "bfsi": "banks, financial services and insurance companies as customers",
    "vertical": "an industry segment the company sells into",
    "deal win": "signing a new customer contract",
    "deal wins": "signing new customer contracts",
    "order intake": "value of new orders signed in the period",
    "order book": "work already won but not yet delivered or billed",
    "tcv": "total contract value, the full worth of a deal over its life",
    "acv": "annual contract value, what a deal is worth per year",
    "ramp": "how quickly a signed contract turns into actual revenue",
    "ramp-up": "how quickly a signed contract turns into actual revenue",
    "renewal": "an existing customer re-signing rather than leaving",
    "discretionary spend": "optional projects clients can delay when cautious",
    "guidance": "the company's own forecast for coming quarters",
    "consensus": "the average of what analysts expect",
    "beat": "came in better than analysts expected",
    "miss": "came in worse than analysts expected",
    "margin compression": "keeping less profit out of each rupee of sales",
    "margin expansion": "keeping more profit out of each rupee of sales",
    "operating leverage": "profit growing faster than sales because fixed costs are spread wider",
    "ebitda": "profit before interest, tax and depreciation, a rough proxy for cash from operations",
    "pat": "profit after tax, the bottom line",
    "topline": "revenue",
    "bottomline": "net profit",
    "qoq": "compared with the previous quarter",
    "yoy": "compared with the same quarter a year earlier",
    "headwind": "something making performance harder",
    "tailwind": "something making performance easier",
    "re-rating": "the market deciding to pay more per rupee of earnings",
    "de-rating": "the market deciding to pay less per rupee of earnings",
    "multiple": "how many rupees investors pay per rupee of annual earnings",
    "valuation": "what the market is paying relative to earnings or assets",
    "nim": "net interest margin, the gap between what a bank earns on loans and pays on deposits",
    "gnpa": "gross bad loans as a share of total lending",
    "npa": "loans the borrower has stopped repaying",
    "slippage": "loans newly turning bad this period",
    "credit cost": "money set aside for loans expected to go bad",
    "aum": "assets under management, the total pool a firm manages for clients",
    "casa": "cheap current and savings deposits, which lower a bank's funding cost",
    "capex": "spending on plant, equipment or capacity",
    "working capital": "cash tied up in stock and unpaid customer bills",
    "attrition": "staff leaving, which raises hiring and training cost",
    "utilisation": "how much of the billable workforce is actually on paid projects",
    "offshore": "work done from India rather than at the client's site, cheaper per hour",
    "onsite": "work done at the client's location, more expensive",
    "realisation": "the actual price achieved per unit sold",
    "volume growth": "selling more units, as opposed to charging more",
    "pricing power": "being able to raise prices without losing customers",
    "destocking": "distributors running down existing stock instead of ordering",
    "channel inventory": "unsold stock sitting with distributors and retailers",
    "sssg": "same-store sales growth, sales from shops open over a year",
    "accretive": "expected to add to earnings per share",
    "dilutive": "expected to reduce earnings per share",
    "one-off": "a gain or cost that will not repeat",
    "provisioning": "money set aside for expected losses",
    "asset quality": "how likely a lender's borrowers are to repay",
    "free cash flow": "cash left after running and reinvesting in the business",
    "receivables": "money billed to customers but not yet collected",
    "gross margin": "what is left after the direct cost of making the product",
    "operating margin": "what is left after production costs and overheads",
    "mid single digits": "roughly 4 to 6 percent",
    "high single digits": "roughly 7 to 9 percent",
    "low double digits": "roughly 10 to 12 percent",
    "softness": "weaker than before, without being a collapse",
    "muted": "flat or barely growing",
    "subdued": "weaker than normal",
}



# Phrase-level swaps chosen to stay grammatical inside a sentence, so the
# result reads as prose rather than as a lookup table. Longest phrases are
# applied first, since "margin compression" must win over "margin".
PHRASES = [
    ("deal-win softness", "weaker new contract wins"),
    ("deal win softness", "weaker new contract wins"),
    ("deal wins", "new contract wins"),
    ("deal win", "new contract win"),
    ("order intake", "new orders signed"),
    ("order book", "pending order pipeline"),
    ("BFSI vertical", "banking and insurance segment"),
    ("BFSI", "banks and insurers"),
    ("vertical", "industry segment"),
    ("discretionary spend", "optional project spending"),
    ("discretionary spending", "optional project spending"),
    ("slower ramp", "a slower start-up"),
    ("ramp-up", "start-up to full revenue"),
    ("renewals", "existing customers re-signing"),
    ("renewal", "an existing customer re-signing"),
    ("EBITDA margin expansion", "operating profit margin widening"),
    ("EBITDA margin compression", "operating profit margin shrinking"),
    ("EBITDA margin", "operating profit margin"),
    ("margin expansion of", "profit margins widening by"),
    ("margin compression", "shrinking profit margins"),
    ("margin expansion", "widening profit margins"),
    ("operating leverage", "profits rising faster than sales"),
    ("mid single digits", "about 4 to 6 percent"),
    ("high single digits", "about 7 to 9 percent"),
    ("low double digits", "about 10 to 12 percent"),
    ("low single digits", "about 1 to 3 percent"),
    ("de-rating", "investors paying less per rupee of profit"),
    ("re-rating", "investors paying more per rupee of profit"),
    ("headwinds", "things making it harder"),
    ("headwind", "something making it harder"),
    ("tailwinds", "things making it easier"),
    ("tailwind", "something making it easier"),
    ("credit costs", "bad-loan charges"),
    ("credit cost", "bad-loan charges"),
    ("asset quality", "how reliably borrowers are repaying"),
    ("slippages", "loans newly turning bad"),
    ("slippage", "loans newly turning bad"),
    ("provisioning", "set-asides for expected losses"),
    ("gross NPA", "bad loans"),
    ("GNPA", "bad loans"),
    ("NPAs", "bad loans"),
    ("NPA", "bad loans"),
    ("NIM", "the gap between lending and deposit rates"),
    ("CASA", "cheap current and savings deposits"),
    ("AUM", "the pool of money it manages for clients"),
    ("attrition", "staff turnover"),
    ("utilisation", "capacity in use"),
    ("utilization", "capacity in use"),
    ("realisation", "achieved selling prices"),
    ("realization", "achieved selling prices"),
    ("pricing power", "pricing strength"),
    ("destocking", "distributors running down stock"),
    ("channel inventory", "unsold stock sitting with distributors"),
    ("SSSG", "sales growth from shops open over a year"),
    ("same-store sales", "sales from shops open over a year"),
    ("free cash flow", "spare cash after costs and reinvestment"),
    ("working capital", "cash tied up in stock and unpaid bills"),
    ("capex", "spending on plant and capacity"),
    ("receivables", "money billed but not yet collected"),
    ("EBITDA margin", "operating profit margin"),
    ("EBITDA", "operating profit"),
    ("PAT", "net profit"),
    ("topline", "revenue"),
    ("bottomline", "net profit"),
    ("YoY", "compared with a year earlier"),
    ("QoQ", "compared with the previous quarter"),
    ("guidance", "the company's forecast"),
    ("consensus estimates", "analyst expectations"),
    ("consensus", "analyst expectations"),
    ("accretive", "adding to per-share earnings"),
    ("dilutive", "reducing per-share earnings"),
    ("one-off", "a one-time item that will not repeat"),
    ("muted", "flat"),
    ("subdued", "weaker than normal"),
    ("softness", "weakness"),
    ("elevated", "higher than normal"),
    ("moderating", "easing off"),
    ("trimming", "cutting"),
    ("citing", "because of"),
]


def rewrite_plain(text):
    """Swap research vocabulary for ordinary words, in place.

    This is substitution, not paraphrase. The sentence keeps the analyst's
    own structure and claims; only the vocabulary changes. That is a
    deliberate limit: a genuine rewrite needs a language model, and a
    paraphrase can quietly assert something the source never said.
    """
    if not text:
        return "", False
    import re as _re
    out, hits = text, 0
    for term, plain in PHRASES:
        pattern = _re.compile(r"\b" + _re.escape(term) + r"\b", _re.IGNORECASE)
        new, n = pattern.subn(plain, out)
        if n:
            hits += n
            out = new
    # tidy the artefacts substitution tends to leave behind
    out = _re.sub(r"\s{2,}", " ", out)
    out = _re.sub(r"\ba (a|an|the)\b", r"a", out)
    out = _re.sub(r"\ban (a|an)\b", "an", out)
    out = out.strip()
    # Case-insensitive substitution loses the capital wherever a swapped term
    # begins a sentence, e.g. "Muted demand ..." becoming "flat demand ...".
    # Restore it at the start and after every sentence break.
    if out:
        out = _re.sub(r"(^|[.!?]\s+)([a-z])",
                      lambda m: m.group(1) + m.group(2).upper(), out)
    return out, hits >= 2


def plain_english(text):
    """Explain the jargon actually used in a piece of coverage.

    Deterministic and offline: it looks up terms that appear, rather than
    rewriting the sentence. That means it never invents a meaning the source
    did not carry, which a paraphrase can quietly do.
    """
    if not text:
        return []
    low = " " + text.lower().replace(",", " ").replace(".", " ") + " "
    found = []
    for term, meaning in JARGON.items():
        if f" {term} " in low or f" {term}s " in low:
            if any(term in t for t, _ in found):
                continue
            found.append((term, meaning))
    found.sort(key=lambda x: -len(x[0]))
    return found[:5]


def format_plain(text, indent="    "):
    """Plain-English version of a piece of coverage, with the glossary as a
    fallback when too little could be swapped to make prose worth showing."""
    if not text:
        return []
    rewritten, worthwhile = rewrite_plain(text)
    if worthwhile:
        out, line = [f"{indent}In plain English:"], ""
        for word in rewritten.split():
            if len(line) + len(word) + 1 > 74:
                out.append(f"{indent}  {line}")
                line = word
            else:
                line = f"{line} {word}".strip()
        if line:
            out.append(f"{indent}  {line}")
        return out
    terms = plain_english(text)
    if not terms:
        return []
    out = [f"{indent}In plain terms:"]
    for term, meaning in terms:
        out.append(f"{indent}  {term} = {meaning}")
    return out


def rationale_for(rating, news, window_days=4):
    """Find coverage that plausibly explains one rating change.

    A broker's own note is a paid product with no public URL. What is public
    is the financial press reporting on it, which usually carries the stated
    reason. Matching is by the firm being named, or failing that by an
    article landing within a few days of the action. The second kind is
    weaker evidence and is labelled as such, because a same-week article is
    not proof of causation.
    """
    import datetime as _dt
    try:
        rdate = _dt.datetime.strptime(rating["date"], "%d %b %Y")
    except (ValueError, KeyError):
        return []
    firm = (rating.get("firm") or "").lower().split()[0] if rating.get("firm") else ""

    named, nearby = [], []
    for n in news:
        blob = (n.get("title", "") + " " + n.get("summary", "")).lower()
        close = False
        if n.get("when"):
            close = abs((n["when"] - rdate).days) <= window_days
        if firm and firm in blob:
            named.append(n)
        elif close and any(w in blob for w in
                           ("downgrade", "upgrade", "target", "rating",
                            "brokerage", "analyst", "cut", "raise")):
            nearby.append(n)
        elif close:
            nearby.append(n)

    out = []
    for n in named[:2]:
        out.append({"why": "names the firm", "item": n})
    if not named:
        for n in nearby[:2]:
            out.append({"why": "same week, not confirmed as related", "item": n})
    return out


def format_rationale(matches):
    lines = []
    for m in matches:
        n = m["item"]
        src = n.get("provider") or "source"
        lines.append(f"  {n['title']}")
        if n.get("summary"):
            txt = n["summary"].strip()
            if len(txt) > 240:
                txt = txt[:240].rsplit(" ", 1)[0] + "..."
            lines.append(f"    {txt}")
        lines.extend(format_plain(n.get("summary") or n.get("title", "")))
        lines.append(f"    {src} ({m['why']})")
        if n.get("link"):
            lines.append(f"    {n['link']}")
    return lines


def explain_target_move(e):
    """Say what a move in the CONSENSUS target can and cannot tell you.

    Yahoo publishes the average of all covering analysts, not each firm's
    individual number, so a change in the mean cannot be pinned on a named
    house unless that house also filed a rating change. What the arithmetic
    does give you is the size of the underlying revision, which separates
    "one analyst made a big cut" from "several trimmed slightly".
    """
    import datetime as _dt
    lines = []
    direction = "cut" if e["move"] < 0 else "raised"
    lines.append(f"Consensus target {direction} {abs(e['move']):.1f}%, "
                 f"from {e['old']:,.2f} to {e['new']:,.2f}.")

    n = e.get("n")
    if n and n > 0:
        delta_mean = e["new"] - e["old"]
        aggregate = delta_mean * n
        lines.append(f"Averaged across {n} analysts, so the total revision is "
                     f"about {abs(aggregate):,.0f} rupees of target. That is one "
                     f"analyst moving {abs(aggregate):,.0f}, or several moving "
                     f"{abs(aggregate) / max(2, n // 2):,.0f} each.")
    if e.get("low") and e.get("high"):
        lines.append(f"Current spread {e['low']:,.2f} to {e['high']:,.2f}"
                     + (f", price {e['price']:,.2f}." if e.get("price") else "."))

    # A rating change in the same window is the most likely cause
    recent = []
    for r in (e.get("ratings") or []):
        try:
            d = _dt.datetime.strptime(r["date"], "%d %b %Y")
            if (_dt.datetime.now() - d).days <= 14:
                recent.append(r)
        except (ValueError, KeyError):
            continue
    if recent:
        lines.append("Rating action filed in the same fortnight, which is the "
                     "most likely source:")
        for r in recent[:2]:
            grade = (f"{r['frm']} to {r['to']}" if r.get("frm")
                     and r["frm"] != r["to"] else r.get("to", "?"))
            lines.append(f"  {r['date']}  {r['firm']}: {grade}")
            for ln in format_rationale(rationale_for(r, e.get("news") or [])):
                lines.append("  " + ln)
    else:
        lines.append("No rating change filed in the last fortnight, so this is "
                     "a quiet revision to numbers rather than a published "
                     "upgrade or downgrade. Yahoo does not name which firm "
                     "moved.")

    if e.get("news"):
        lines.append("Recent coverage:")
        for nx in e["news"][:3]:
            lines.append(f"  {nx['title']}")
    return lines


def explain_rating(e):
    verb = {"up": "upgraded", "down": "downgraded", "init": "started covering",
            "main": "reiterated", "reit": "reiterated"}.get(e["action"], "rerated")
    if e["frm"] and e["frm"] != e["to"]:
        what = f"from {e['frm']} to {e['to']}"
    else:
        what = f"at {e['to']}"
    return f"{e['firm']} {verb} it {what} on {e['date']}."


# ----------------------------------------------------------------------
# Chart
# ----------------------------------------------------------------------

def quarter_chart(ticker, quarters):
    """Eight quarters of revenue and profit as bars, margin as a line.
    Returns PNG bytes, or None if there is not enough to plot."""
    usable = [q for q in quarters if q["revenue"] is not None][:8]
    if len(usable) < 2:
        return None
    usable = list(reversed(usable))
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        from matplotlib.ticker import FuncFormatter

        labels = [q["period"] for q in usable]
        rev = [q["revenue"] / 1e7 for q in usable]
        net = [(q["net"] / 1e7) if q["net"] is not None else 0 for q in usable]
        marg = [q["margin"] for q in usable]

        fig, ax = plt.subplots(figsize=(8.4, 4.2), dpi=140)
        fig.patch.set_facecolor(INK)
        ax.set_facecolor(PANEL)
        x = range(len(usable))
        ax.bar([i - 0.2 for i in x], rev, width=0.4, color=CRIMSON,
               label="Revenue (Cr)")
        ax.bar([i + 0.2 for i in x], net, width=0.4, color=GREEN,
               label="Net profit (Cr)")
        ax.set_xticks(list(x))
        ax.set_xticklabels(labels, rotation=45, ha="right", color=MUTED, fontsize=8)
        ax.tick_params(colors=MUTED, labelsize=8)
        ax.yaxis.set_major_formatter(FuncFormatter(lambda v, p: f"{v:,.0f}"))
        for s in ax.spines.values():
            s.set_color(LINE)
        ax.grid(axis="y", color=LINE, linewidth=0.6, alpha=0.6)
        ax.set_axisbelow(True)

        if any(m is not None for m in marg):
            ax2 = ax.twinx()
            ax2.plot(list(x), [m if m is not None else float("nan") for m in marg],
                     color=AMBER, marker="o", markersize=4, linewidth=1.8,
                     label="Net margin %")
            ax2.tick_params(colors=AMBER, labelsize=8)
            ax2.set_ylabel("Net margin %", color=AMBER, fontsize=9)
            for s in ax2.spines.values():
                s.set_color(LINE)

        ax.set_title(f"{ticker} — last {len(usable)} quarters",
                     color=PAPER, fontsize=12, fontweight="bold", loc="left")
        ax.set_ylabel("Rs crore", color=MUTED, fontsize=9)
        h1, l1 = ax.get_legend_handles_labels()
        leg = ax.legend(h1, l1, loc="upper left", fontsize=8, framealpha=0)
        for t in leg.get_texts():
            t.set_color(MUTED)
        fig.tight_layout()
        buf = io.BytesIO()
        fig.savefig(buf, format="png", facecolor=INK)
        plt.close(fig)
        return buf.getvalue()
    except Exception as e:  # noqa: BLE001
        print(f"  chart failed for {ticker}: {e}")
        return None


# ----------------------------------------------------------------------
# Delivery
# ----------------------------------------------------------------------


SITE_LABELS = {"screener.in": "Screener", "nseindia.com": "NSE filing",
               "bseindia.com": "BSE filing", "reuters.com": "Reuters",
               "moneycontrol.com": "Moneycontrol", "livemint.com": "Mint",
               "economictimes": "Economic Times",
               "business-standard": "Business Standard",
               "gurufocus": "GuruFocus", "yahoo.com": "full article"}


def link_label(url):
    import re as _re
    host = _re.sub(r"^https?://(www\.)?", "", url).split("/")[0].lower()
    return next((v for k, v in SITE_LABELS.items() if k in url.lower()), host)


def linkify_html(text, colour):
    """Escape text and turn bare URLs into named links.

    Shared by the email and the Telegram renderer. They used to each do this
    separately, which is how the email ended up still showing raw URLs after
    the Telegram side was fixed.
    """
    import re as _re
    out = text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    return _re.sub(r"https?://[^\s<>\"]+",
                   lambda m: f'<a href="{m.group(0)}" style="color:{colour}">'
                             f'{link_label(m.group(0))}</a>', out)


def to_telegram_html(text):
    """Convert a plain write-up into Telegram-safe HTML.

    Two things go wrong if this is skipped. An unescaped ampersand breaks
    the whole message for any ticker like M&MFIN, and a bare URL on its own
    line gets auto-linked together with whatever text follows it, which is
    why section headings were being absorbed into the previous story's link.
    Escaping first and emitting explicit anchors avoids both.
    """
    import re as _re
    out = (text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;"))

    SITE = {"screener.in": "Screener", "nseindia.com": "NSE filing",
            "bseindia.com": "BSE filing", "reuters.com": "Reuters",
            "moneycontrol.com": "Moneycontrol", "livemint.com": "Mint",
            "economictimes": "Economic Times",
            "business-standard": "Business Standard",
            "gurufocus": "GuruFocus", "yahoo.com": "full article"}

    def anchor(m):
        # A column of identical "open" links tells you nothing about where
        # each one goes. Name the destination instead.
        url = m.group(0)
        host = _re.sub(r"^https?://(www\.)?", "", url).split("/")[0].lower()
        label = next((v for k, v in SITE.items() if k in url.lower()), host)
        return f'<a href="{url}">{label}</a>'
    out = _re.sub(r"https?://[^\s<>\"]+", anchor, out)

    # Bold the section headings so the message has visible structure.
    for head in ("THE NUMBERS", "WAS IT A GOOD QUARTER",
                 "WHERE THE MARGIN MOVED", "WHY IT MOVED", "FLAGS",
                 "IN THE NEWS", "WHAT MANAGEMENT SAID", "NEXT RESULTS DUE"):
        out = out.replace(head, f"<b>{head}</b>")
    out = _re.sub(r"(?m)^(\s*)(In plain English:|In plain terms:|Margin walk[^\n]*)$",
                  r"\1<i>\2</i>", out)
    return out


def tg_send_photo(caption, png):
    """sendPhoto needs multipart/form-data, which urllib will not build."""
    token = os.environ.get("TELEGRAM_BOT_TOKEN")
    chat = os.environ.get("TELEGRAM_CHAT_ID")
    if not token or not chat:
        return False
    boundary = uuid.uuid4().hex
    parts = []
    for k, v in (("chat_id", chat), ("caption", caption[:1024]),
                 ("parse_mode", "HTML")):
        parts.append(f"--{boundary}\r\nContent-Disposition: form-data; "
                     f'name="{k}"\r\n\r\n{v}\r\n'.encode())
    parts.append(f"--{boundary}\r\nContent-Disposition: form-data; "
                 f'name="photo"; filename="chart.png"\r\n'
                 f"Content-Type: image/png\r\n\r\n".encode())
    parts.append(png)
    parts.append(f"\r\n--{boundary}--\r\n".encode())
    body = b"".join(parts)
    req = urllib.request.Request(
        f"https://api.telegram.org/bot{token}/sendPhoto", data=body,
        headers={"Content-Type": f"multipart/form-data; boundary={boundary}"})
    try:
        with urllib.request.urlopen(req, timeout=45) as r:
            r.read()
        return True
    except Exception as e:  # noqa: BLE001
        print(f"  telegram photo failed: {e}")
        return False


def tg_send_text(text):
    token = os.environ.get("TELEGRAM_BOT_TOKEN")
    chat = os.environ.get("TELEGRAM_CHAT_ID")
    if not token or not chat:
        return
    for i in range(0, len(text), 3900):
        data = urllib.parse.urlencode({
            "chat_id": chat, "text": text[i:i + 3900], "parse_mode": "HTML",
            "disable_web_page_preview": "true"}).encode()
        try:
            with urllib.request.urlopen(urllib.request.Request(
                    f"https://api.telegram.org/bot{token}/sendMessage",
                    data=data), timeout=30) as r:
                r.read()
        except Exception as e:  # noqa: BLE001
            print(f"  telegram text failed: {e}")
            return


def send_email(subject, html, images):
    """images: list of (cid, png_bytes) embedded inline, so the charts show
    in the mail body rather than as downloads."""
    user = os.environ.get("SMTP_USER")
    pw = os.environ.get("SMTP_APP_PASSWORD")
    to = os.environ.get("ALERT_EMAIL_TO", user)
    if not user or not pw:
        print("SMTP not configured, skipping email")
        return
    root = MIMEMultipart("related")
    root["Subject"] = subject
    root["From"] = user
    root["To"] = to
    alt = MIMEMultipart("alternative")
    root.attach(alt)
    alt.attach(MIMEText("Your mail client needs HTML to show this digest.",
                        "plain", "utf-8"))
    alt.attach(MIMEText(html, "html", "utf-8"))
    for cid, png in images:
        img = MIMEImage(png, "png")
        img.add_header("Content-ID", f"<{cid}>")
        img.add_header("Content-Disposition", "inline", filename=f"{cid}.png")
        root.attach(img)
    with smtplib.SMTP_SSL("smtp.gmail.com", 465, timeout=45) as s:
        s.login(user, pw)
        s.sendmail(user, [to], root.as_string())
    print(f"  emailed to {to}")


def build_html(blocks):
    FONT = "'Segoe UI',Arial,sans-serif"
    body = ""
    for b in blocks:
        chart = (f'<div style="margin-top:10px"><img src="cid:{b["cid"]}" '
                 f'style="width:100%;max-width:560px;border-radius:8px"></div>'
                 if b.get("cid") else "")
        lines = "".join(
            f'<div style="font-family:{FONT};font-size:13px;color:{PAPER};'
            f'margin-top:5px">{linkify_html(ln, CRIMSON)}</div>'
            for ln in b["lines"])
        body += f'''<tr><td style="padding:16px 18px;border-bottom:1px solid {LINE}">
  <div style="font-family:{FONT};font-weight:700;font-size:17px;color:{PAPER}">
    {b["icon"]} {b["ticker"]}
    <span style="font-size:11px;font-weight:400;color:{MUTED};border:1px solid {LINE};
      border-radius:4px;padding:1px 6px">{b["kind"]}</span></div>
  {lines}{chart}
</td></tr>'''
    return f'''<!DOCTYPE html><html><body style="margin:0;padding:24px 12px;background:#0d0607">
<table role="presentation" width="100%" cellpadding="0" cellspacing="0"><tr><td align="center">
<table role="presentation" width="620" cellpadding="0" cellspacing="0"
  style="max-width:620px;background:{PANEL};border:1px solid {LINE};border-radius:12px;overflow:hidden">
  <tr><td style="background:{INK};padding:20px 18px">
    <div style="font-family:{FONT};font-size:22px;font-weight:700;color:{PAPER}">
      Research <span style="color:{CRIMSON}">Watch</span></div>
    <div style="font-family:{FONT};font-size:13px;color:{MUTED};margin-top:2px">
      {datetime.now(IST).strftime('%d %b %Y')} &middot; what changed since yesterday</div>
  </td></tr>
  {body}
  <tr><td style="padding:14px 18px;background:{INK};font-family:{FONT};
    font-size:11px;color:{MUTED}">
    Data from Yahoo Finance, which lags the original announcement and covers
    Indian smallcaps thinly. Descriptions of results state what the numbers
    did; they are not a view on the shares.
  </td></tr>
</table></td></tr></table></body></html>'''


# ----------------------------------------------------------------------

def main():
    symbols = load_symbols()
    if not symbols:
        print("No symbols in holdings.csv")
        return
    state = load_state()
    print(f"Checking {len(symbols)} symbol(s)")

    blocks, tg_msgs, charts = [], [], []
    warned = {}
    for sym, tk, ex in symbols:
        now = fetch_research(sym)
        time.sleep(PACE_SECONDS)
        prev = state.get(sym, {})
        events = detect(prev, now)

        for e in events:
            if e["kind"] == "rating":
                icon = {"up": "\u2b06\ufe0f", "down": "\u2b07\ufe0f"}.get(e["action"], "\U0001F4DD")
                rlines = [explain_rating(e)]
                matches = rationale_for(e, e.get("news") or [])
                if matches:
                    rlines.append("Why, according to the coverage:")
                    rlines.extend(format_rationale(matches))
                else:
                    rlines.append("No coverage found explaining it. The note "
                                  "itself is paid research with no public link.")
                blocks.append({"ticker": tk, "kind": "rating change", "icon": icon,
                               "lines": rlines, "cid": None})
                tg_msgs.append(f"{icon} <b>{tk}</b> \u2014 rating change\n"
                               + "\n".join(rlines))
            elif e["kind"] == "target":
                icon = "\U0001F4C8" if e["move"] > 0 else "\U0001F4C9"
                tlines = explain_target_move(e)
                blocks.append({"ticker": tk, "kind": "target change", "icon": icon,
                               "lines": tlines, "cid": None})
                tg_msgs.append(f"{icon} <b>{tk}</b> \u2014 target change\n"
                               + "\n".join(tlines))
            elif e["kind"] == "upcoming":
                when = ("today" if e["days"] == 0 else
                        "tomorrow" if e["days"] == 1 else f"in {e['days']} days")
                line = (f"Results scheduled for {e['date']} ({when}). "
                        f"Yahoo often publishes the actual numbers days to "
                        f"weeks after the filing, so watch the exchange site "
                        f"on the day if it matters.")
                blocks.append({"ticker": tk, "kind": "results due",
                               "icon": "\U0001F4C5", "lines": [line], "cid": None})
                tg_msgs.append(f"\U0001F4C5 <b>{tk}</b> \u2014 results due\n{line}")
                warned[sym] = e["date"]
            elif e["kind"] == "results":
                lines = explain_results(e["quarters"], e.get("balance"),
                                        e.get("news"), tk, ex,
                                        now.get("next_earnings"), eps=e)
                png = (quarter_chart(tk, e["quarters"])
                       if len(charts) < MAX_CHARTS_PER_RUN else None)
                cid = None
                if png:
                    cid = f"chart{len(charts)}"
                    charts.append((cid, png))
                blocks.append({"ticker": tk, "kind": "results", "icon": "\U0001F4CA",
                               "lines": lines, "cid": cid})
                head = (f"\U0001F4CA <b>{tk}</b> \u2014 results out"
                        + (" <i>(catching up, newly watched)</i>"
                           if e.get("catchup") else ""))
                full = head + "\n" + "\n".join(lines)
                # Telegram caps photo captions at 1024 characters, so the
                # chart carries only a stub. The full write-up is sent
                # immediately afterwards as its own message, per stock: an
                # earlier version pooled every write-up into one combined
                # message at the end, so what actually appeared under each
                # chart was an eight-line stub and the analysis was lost in
                # a wall of text far below.
                body = to_telegram_html("\n".join(lines))
                head_html = (f"\U0001F4CA <b>{tk}</b> \u2014 results out"
                             + (" <i>(catching up)</i>" if e.get("catchup") else ""))
                if png:
                    caption = head_html + "\n" + to_telegram_html(
                        "\n".join(lines[:4]))
                    tg_send_photo(caption[:900], png)
                tg_send_text(head_html + "\n" + body)

        state[sym] = {"rating_ids": [r["id"] for r in now["ratings"]],
                      "target": now.get("target"),
                      "quarter": now.get("quarter"),
                      "next_earnings": now.get("next_earnings"),
                      "earnings_warned": warned.get(sym, prev.get("earnings_warned")),
                      "checked": datetime.now(ZoneInfo("UTC")).isoformat(timespec="seconds")}

    save_state(state)

    if not blocks:
        print("Nothing changed today.")
        return
    print(f"{len(blocks)} change(s) found")

    if tg_msgs:
        tg_send_text("\U0001F50D <b>Research Watch</b>\n\n" +
                     "\n\n\u2500\u2500\u2500\n\n".join(tg_msgs))
    send_email(f"Research watch: {len(blocks)} change(s)",
               build_html(blocks), charts)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Daily portfolio digest. Runs once after NSE close (scheduled by digest.yml).

For every enabled alert in holdings.csv it reports: last price, day move,
distance to each armed alert band, position in the 52-week range, analyst
mean target where Yahoo has one, and the next earnings date if known.

Output goes three places:
  1. Email (same SMTP secrets as the alert system)
  2. Telegram (same bot)
  3. digest.json committed to the repo, which the Alert Desk dashboard renders

This file is deliberately standalone: it shares no imports with
stock_alerts.py so either can be updated without touching the other.
"""

import csv
import json
import re
import os
import smtplib
import time
import urllib.parse
import urllib.request
from datetime import datetime, timedelta
from email.mime.text import MIMEText
from pathlib import Path
from zoneinfo import ZoneInfo

BASE_DIR = Path(__file__).resolve().parent
HOLDINGS_CSV = BASE_DIR / "holdings.csv"
STATE_FILE = BASE_DIR / "alerts_state.json"
DIGEST_FILE = BASE_DIR / "digest.json"

SUFFIX = {"NSE": ".NS", "BSE": ".BO", "US": ""}
IST = ZoneInfo("Asia/Kolkata")


def load_rows():
    rows = []
    if not HOLDINGS_CSV.exists():
        return rows
    with open(HOLDINGS_CSV, newline="", encoding="utf-8-sig") as f:
        for row in csv.DictReader(f):
            row = {k.strip().lower(): (v or "").strip() for k, v in row.items() if k}
            if not row.get("ticker"):
                continue
            if row.get("enabled", "yes").lower() in ("no", "false", "0", "off"):
                continue
            rows.append(row)
    return rows


def load_fired():
    if STATE_FILE.exists():
        try:
            return json.loads(STATE_FILE.read_text())
        except json.JSONDecodeError:
            pass
    return {}


# A single share held for the annual report, the AGM, or a shareholder
# quota in a subsidiary IPO is not a position. It has no thesis and no exit,
# so dead-money and position-event logic produce pure noise about something
# never intended to be sold. The marker lives in the note field so the CSV
# schema is unchanged and the dashboard reads the same string.
PERK_TAG = re.compile(r"#(perk|report|agm)\b", re.I)


def is_perk(entry):
    """True when any row behind this holding is tagged as a perk."""
    note = entry.get("note") or ""
    if PERK_TAG.search(note):
        return True
    for lot in entry.get("lots") or []:
        if PERK_TAG.search(lot.get("note") or ""):
            return True
    for row in entry.get("rows") or []:
        if PERK_TAG.search(row.get("note") or ""):
            return True
    return False


DEAD_MONEY_RETURN = 8.0     # a return this weak, on money held over a year
DEAD_MONEY_MIN_VALUE = 5000  # and a position at least this size


def holding_age(entry):
    """(days_held, basis). Falls back to lt_qty when buy_date is missing.

    lt_qty is the quantity a broker has marked long term, which by
    definition means held over a year. It is a floor, not a date, so it
    proves "over a year" and nothing more precise. Only Zerodha reports it.
    """
    raw = (entry.get("buy_date") or "").strip()
    for fmt in ("%Y-%m-%d", "%d-%m-%Y", "%d/%m/%Y", "%d %b %Y"):
        try:
            d = datetime.strptime(raw, fmt).date()
            return (datetime.now(IST).date() - d).days, "buy_date"
        except ValueError:
            continue
    try:
        if float(entry.get("lt_qty") or 0) > 0:
            return 366, "lt_qty"
    except (ValueError, TypeError):
        pass
    return None, None


def dead_money(entries):
    """Capital held over a year that has gone nowhere.

    Ranked by rupees tied up, not by percentage, because the question is how
    much money is idle rather than which line looks worst.

    This does not recommend selling anything. It reports how long capital
    has been committed, what it earned, and how far the price sits below its
    own split-adjusted peak. Whether that is dead money or a thesis still
    playing out is not something a price series can tell you.
    """
    out = []
    for e in entries:
        if not e.get("price") or not e.get("qty"):
            continue
        if is_perk(e):
            continue
        value = e["price"] * e["qty"]
        if value < DEAD_MONEY_MIN_VALUE:
            continue
        days, basis = holding_age(e)
        if not days or days < 365:
            continue
        pl = e.get("pl_pct")
        if pl is None or pl > DEAD_MONEY_RETURN:
            continue
        years = days / 365.25
        annual = ((1 + pl / 100) ** (1 / years) - 1) * 100 if years > 0 else None
        ath, off_ath = e.get("ath"), None
        if ath and ath > 0:
            off_ath = (e["price"] / ath - 1) * 100
        out.append({"ticker": e["ticker"], "value": value, "pl_pct": pl,
                    "pl_abs": e.get("pl_abs"), "days": days, "basis": basis,
                    "annual": annual, "off_ath": off_ath,
                    "splits": e.get("ath_splits_applied") or 0,
                    "location": e.get("location", "")})
    out.sort(key=lambda x: -x["value"])
    return out


def band_target(row):
    if row.get("alert_type", "").lower() == "watch":
        return None
    # A trailing stop's target lives in alerts_state.json and moves daily.
    # The digest has no business guessing it, and the GIVING BACK GAINS
    # section already covers the same ground from the position side.
    if row.get("alert_type", "").lower() == "trail":
        return None
    v = float(row["alert_value"])
    if row["alert_type"] == "price":
        return v
    # Blank reference_price means the target is measured from your own cost
    # basis, matching the fallback in stock_alerts.py. These two must agree,
    # or the digest would show a different target than the one that fires.
    ref = row.get("reference_price", "").strip()
    r = float(ref) if ref else float(row["avg_cost"])
    return r * (1 + v / 100) if row["direction"] == "above" else r * (1 - v / 100)


def alert_key(row, symbol):
    ref = ""
    if row["alert_type"] == "watch":
        return f"{symbol}|watch"
    if row["alert_type"] == "percent":
        rp = row.get("reference_price", "").strip()
        ref = float(rp) if rp else float(row["avg_cost"])
    return f"{symbol}|{row['alert_type']}|{float(row['alert_value'])}|{row['direction']}|{ref}"


def fetch_snapshot(symbol):
    """Best-effort market snapshot for one symbol. Never raises."""
    out = {"price": None, "prev_close": None, "year_high": None,
           "year_low": None, "mean_target": None, "earnings": None,
           "ath": None, "ath_date": None}
    try:
        import yfinance as yf
        t = yf.Ticker(symbol)
        fi = t.fast_info
        out["price"] = float(fi.last_price)
        for attr, key in (("previous_close", "prev_close"),
                          ("year_high", "year_high"), ("year_low", "year_low")):
            try:
                val = getattr(fi, attr)
                if val:
                    out[key] = float(val)
            except Exception:
                pass
        try:
            # auto_adjust=False returns RAW prices. After a 1-for-5 split the
            # pre-split high is five times the post-split price, so the raw
            # peak is compared against a price that can never reach it and the
            # holding looks permanently 80% below its high.
            #
            # Splits are divided out by hand rather than using auto_adjust=True,
            # because that also adjusts for dividends, which lowers historical
            # prices and manufactures false "at its peak" signals.
            #
            # This adjusts YAHOO'S PRICE HISTORY only. avg_cost and qty come
            # from broker statements that are already restated after a split
            # and must never be touched. See bug 2.
            hist = t.history(period="max", auto_adjust=False)
            if hist is not None and len(hist) > 0 and "High" in hist:
                highs = hist["High"].dropna()
                splits = None
                try:
                    s = t.splits
                    if s is not None and len(s) > 0:
                        splits = s[s > 0]
                except Exception:
                    splits = None
                if splits is not None and len(splits) > 0:
                    # Every high gets divided by the product of the splits that
                    # happened after it, putting the whole series on today's
                    # share count.
                    factors = []
                    for when in highs.index:
                        later = splits[splits.index > when]
                        f = 1.0
                        for ratio in later.values:
                            f *= float(ratio)
                        factors.append(f)
                    adjusted = highs / factors
                    out["ath_splits_applied"] = int(len(splits))
                else:
                    adjusted = highs
                if len(adjusted) > 0:
                    out["ath"] = float(adjusted.max())
                    out["ath_days"] = len(adjusted)
                    out["ath_raw"] = float(highs.max())
                    try:
                        out["ath_date"] = adjusted.idxmax().strftime("%d %b %Y")
                    except Exception:
                        pass
        except Exception:
            pass
        # Dividends. Across 120-odd Indian holdings this is real income that
        # never appears anywhere else in the system.
        try:
            import pandas as pd
            dv = t.dividends
            if dv is not None and len(dv) > 0:
                idx = dv.index
                idx_n = idx.tz_localize(None) if idx.tz is not None else idx
                now_n = pd.Timestamp.now("UTC").tz_localize(None)
                yr = now_n - pd.Timedelta(days=365)
                paid = [(d, float(v)) for d, v in zip(idx_n, dv.values) if d >= yr]
                if paid:
                    out["div_ttm"] = sum(v for _, v in paid)
                    out["div_last"] = paid[-1][1]
                    out["div_last_date"] = paid[-1][0].strftime("%d %b %Y")
        except Exception:
            pass
        try:
            info = t.info
            out["mean_target"] = info.get("targetMeanPrice")
            # Same t.info call as the target above, so the company name
            # costs nothing extra: no new request, no added quota.
            out["name"] = info.get("longName") or info.get("shortName")
        except Exception:
            pass
        try:
            cal = t.calendar
            ed = None
            if isinstance(cal, dict):
                ed = cal.get("Earnings Date")
                if isinstance(ed, (list, tuple)) and ed:
                    ed = ed[0]
            if ed:
                out["earnings"] = str(ed)[:10]
        except Exception:
            pass
    except Exception as e:  # noqa: BLE001
        out["error"] = str(e)[:120]
    return out


def pct(a, b):
    return (a / b - 1) * 100



# Indian equity capital gains, as the rules stood at the time of writing:
# listed shares held 12 months or less are short term, taxed at 20%; beyond
# 12 months they are long term, taxed at 12.5% on gains above a Rs 1.25 lakh
# annual exemption. Rates change with each Budget. Everything below is
# arithmetic on your own numbers, not tax advice, and is worth checking with
# your CA before acting on it.
LTCG_DAYS = 365
STCG_RATE = 0.20
LTCG_RATE = 0.125
LTCG_EXEMPTION = 125000
APPROACHING_DAYS = 45      # how early to flag a position nearing long term


def holding_days(buy_date):
    if not buy_date:
        return None
    for fmt in ("%Y-%m-%d", "%d-%m-%Y", "%d/%m/%Y", "%d %b %Y"):
        try:
            d = datetime.strptime(buy_date.strip(), fmt)
            return (datetime.now() - d).days
        except ValueError:
            continue
    return None


def tax_lines(entry):
    """Holding-period position for one holding. Only meaningful when a
    buy_date was recorded."""
    days = holding_days(entry.get("buy_date"))
    if days is None:
        return []
    gain = entry.get("pl_abs")
    cur = entry["currency"]
    if days > LTCG_DAYS:
        return [f"Held {days} days, long term"]
    left = LTCG_DAYS + 1 - days
    line = f"Held {days} days, short term, long term in {left}"
    if gain and gain > 0 and left <= APPROACHING_DAYS:
        saving = gain * (STCG_RATE - LTCG_RATE)
        line += (f". Selling now taxes {cur}{gain:,.0f} at 20% instead of "
                 f"12.5%, a difference of about {cur}{saving:,.0f}")
    return [line]


def build_tax_summary(entries):
    """Realisable gains and losses, split by holding period.

    Losses can be set against gains, and unused losses carry forward eight
    years if the return is filed on time. This just lays out what is sitting
    there; which of it to actually realise is a decision with your CA.
    """
    st_g = st_l = lt_g = lt_l = 0.0
    approaching = []
    no_date = 0
    for e in entries:
        pl = e.get("pl_abs")
        if pl is None:
            continue
        days = holding_days(e.get("buy_date"))
        if days is None:
            no_date += 1
            continue
        if days > LTCG_DAYS:
            if pl >= 0:
                lt_g += pl
            else:
                lt_l += pl
        else:
            if pl >= 0:
                st_g += pl
            else:
                st_l += pl
            left = LTCG_DAYS + 1 - days
            if pl > 0 and left <= APPROACHING_DAYS:
                approaching.append((e["ticker"], left, pl,
                                    pl * (STCG_RATE - LTCG_RATE)))
    if not (st_g or st_l or lt_g or lt_l):
        return None
    net_st = st_g + st_l
    net_lt = lt_g + lt_l
    est = max(0.0, net_st) * STCG_RATE + \
        max(0.0, net_lt - LTCG_EXEMPTION) * LTCG_RATE
    return {"st_gain": st_g, "st_loss": st_l, "lt_gain": lt_g, "lt_loss": lt_l,
            "net_st": net_st, "net_lt": net_lt, "est_tax": est,
            "approaching": sorted(approaching, key=lambda x: x[1]),
            "no_date": no_date}



POSITION_STATE_FILE = BASE_DIR / "position_state.json"

# How far off its tracked low a losing position must climb before it counts
# as "recovering", and how close to cost before "approaching breakeven".
RECOVERY_PCT = 15.0
NEAR_BREAKEVEN_PCT = 5.0
# Within this much of the all-time high counts as "approaching"; at or above
# it counts as a breakout. 0.5% of slack absorbs the fact that Yahoo's ATH
# comes from daily highs while the price here is a last-traded value.
NEAR_ATH_PCT = 4.0
ATH_TOLERANCE = 0.995


def load_position_state():
    if POSITION_STATE_FILE.exists():
        try:
            return json.loads(POSITION_STATE_FILE.read_text())
        except json.JSONDecodeError:
            print("WARNING: position_state.json unreadable, starting fresh")
    return {}


def save_position_state(st):
    POSITION_STATE_FILE.write_text(json.dumps(st, indent=2, sort_keys=True) + "\n")


def detect_position_events(entries, pstate):
    """Notice when a holding changes state relative to YOUR cost.

    Every event here is a fact about your own position, computed from your
    own purchase price: you are back above what you paid, you are near it,
    you have climbed off the bottom, you have made a new low. What to do
    about any of them is not something this file has an opinion on, and the
    wording is deliberately flat for that reason.

    Each event fires once per transition, so a stock oscillating around
    breakeven does not send a message every day.
    """
    events = []
    for e in entries:
        if is_perk(e):
            continue
        price, cost = e.get("price"), e.get("avg_cost")
        if not price or not cost:
            continue
        key = f"{e['ticker']}|{e['exchange']}"
        prev = pstate.get(key, {})
        cur = e["currency"]
        pl_pct = (price / cost - 1) * 100

        low = min(price, prev.get("low", price))
        high = max(price, prev.get("high", price))
        was_profit = prev.get("in_profit")
        first_seen = prev.get("first_seen")

        # 1. Crossed from loss into profit
        if was_profit is False and pl_pct >= 0:
            held = ""
            if first_seen:
                try:
                    d = (datetime.now(IST) - datetime.fromisoformat(first_seen)).days
                    if d >= 25:
                        held = f" after {d} days underwater"
                except ValueError:
                    pass
            events.append({
                "ticker": e["ticker"], "kind": "breakeven",
                "text": (f"Back above your cost of {cur}{cost:,.2f}{held}. "
                         f"Now {cur}{price:,.2f}, {pl_pct:+.1f}%."),
                "gap": 0.0, "ref": cost, "now": price, "cur": cur,
                "detail": e})

        # 2. Approaching breakeven from below
        elif (pl_pct < 0 and abs(pl_pct) <= NEAR_BREAKEVEN_PCT
                and not prev.get("near_flagged")):
            events.append({
                "ticker": e["ticker"], "kind": "near",
                "text": (f"Within {abs(pl_pct):.1f}% of your cost of "
                         f"{cur}{cost:,.2f}. Now {cur}{price:,.2f}."),
                "gap": abs(pl_pct), "ref": cost, "now": price, "cur": cur,
                "detail": e})
            prev["near_flagged"] = True

        # 3. Climbed meaningfully off its low while still underwater
        elif pl_pct < -NEAR_BREAKEVEN_PCT and low > 0:
            off_low = (price / low - 1) * 100
            if off_low >= RECOVERY_PCT and not prev.get("recovery_flagged"):
                events.append({
                    "ticker": e["ticker"], "kind": "recovering",
                    "text": (f"Up {off_low:.0f}% from its {cur}{low:,.2f} low, "
                             f"still {pl_pct:.0f}% below your cost of "
                             f"{cur}{cost:,.2f}."),
                    "gap": off_low, "ref": cost, "now": price, "cur": cur,
                    "detail": e})
                prev["recovery_flagged"] = True

        # 4. At or above the highest price on record
        ath = e.get("ath")
        if ath and ath > 0:
            off_ath = (price / ath - 1) * 100
            short_hist = (e.get("history_days") or 999) < 500
            tag = " since listing" if short_hist else " on record"
            if price >= ath * ATH_TOLERANCE:
                if not prev.get("ath_flagged"):
                    events.append({
                        "ticker": e["ticker"], "kind": "ath",
                        "text": (f"At its highest price{tag}: {cur}{price:,.2f}. "
                                 f"Previous peak {cur}{ath:,.2f}"
                                 + (f" set {e['ath_date']}" if e.get("ath_date") else "")
                                 + ("." if not short_hist else
                                    ". Short listing history, so this is a high "
                                    "since listing rather than a true all-time high.")),
                        "gap": 0.0, "ref": ath, "now": price, "cur": cur,
                        "detail": e})
                    prev["ath_flagged"] = True
            elif off_ath >= -NEAR_ATH_PCT:
                if not prev.get("near_ath_flagged") and not prev.get("ath_flagged"):
                    events.append({
                        "ticker": e["ticker"], "kind": "nearath",
                        "text": (f"Within {abs(off_ath):.1f}% of its highest price"
                                 f"{tag} of {cur}{ath:,.2f}. Now {cur}{price:,.2f}."),
                        "gap": abs(off_ath), "ref": ath, "now": price, "cur": cur,
                        "detail": e})
                    prev["near_ath_flagged"] = True
            else:
                # Clearly off the peak again, so both can fire next time.
                prev["ath_flagged"] = False
                prev["near_ath_flagged"] = False

        # 5. New low. Stated, not interpreted.
        if prev.get("low") and price < prev["low"] * 0.97 and pl_pct < 0:
            events.append({
                "ticker": e["ticker"], "kind": "newlow",
                "text": (f"New low since tracking began: {cur}{price:,.2f}, "
                         f"{pl_pct:.0f}% below your cost of {cur}{cost:,.2f}."),
                "gap": abs(pl_pct), "ref": cost, "now": price, "cur": cur,
                "detail": e})
            prev["recovery_flagged"] = False   # can recover again from here

        if pl_pct >= 0:
            prev["near_flagged"] = False
            prev["recovery_flagged"] = False
            # Returning to profit ends the drawdown. Re-base the low so any
            # future "off its low" is measured from the NEXT dip, not from a
            # trough the position has already fully climbed out of.
            low = price

        pstate[key] = {"low": low, "high": high, "in_profit": pl_pct >= 0,
                       "ath_flagged": prev.get("ath_flagged", False),
                       "near_ath_flagged": prev.get("near_ath_flagged", False),
                       "last_price": round(price, 2),
                       "first_seen": first_seen or datetime.now(IST).isoformat(
                           timespec="seconds"),
                       "near_flagged": prev.get("near_flagged", False),
                       "recovery_flagged": prev.get("recovery_flagged", False)}
    return events



# ----------------------------------------------------------------------
# Event triage
#
# Rendering every event identically buries the two that matter under six
# proximity notices. A stock touching a new low and a stock sitting 3.4%
# away from cost are not the same news and should not look the same.
#
# The score orders them. It is a measure of how far something moved, not a
# view on what to do about it.
# ----------------------------------------------------------------------

CROSSED = ("newlow", "breakeven", "ath", "recovering")
APPROACHING = ("near", "nearath")

EVENT_WEIGHT = {"newlow": 90, "breakeven": 80, "ath": 78, "recovering": 60,
                "near": 40, "nearath": 35}
EVENT_TONE = {"breakeven": "good", "ath": "good", "recovering": "good",
              "newlow": "bad", "near": "flat", "nearath": "flat"}
NEAR_BAND = 5.0     # the window inside which "close" is scored


def event_score(x):
    """Higher means more worth reading. Crossings outrank approaches, and
    within the approaches, tighter outranks looser."""
    kind = x.get("kind")
    base = EVENT_WEIGHT.get(kind, 30)
    gap = x.get("gap")
    if kind in APPROACHING and gap is not None:
        return base + (NEAR_BAND - min(gap, NEAR_BAND)) * 3.0
    if kind == "recovering" and gap is not None:
        return base + min(15.0, gap / 2.0)
    if kind == "newlow" and gap is not None:
        return base + min(10.0, gap / 5.0)
    return float(base)


def rank_events(events):
    return sorted(events, key=lambda x: (-event_score(x), x.get("ticker", "")))


def events_summary(events):
    """One line naming what actually happened, for the top of the section."""
    n = {}
    for x in events:
        n[x["kind"]] = n.get(x["kind"], 0) + 1

    def s(c, one, many):
        return f"{c} {one if c == 1 else many}"

    parts = []
    if n.get("newlow"):
        parts.append(s(n["newlow"], "new low", "new lows"))
    if n.get("ath"):
        parts.append(s(n["ath"], "at its peak", "at their peaks"))
    if n.get("breakeven"):
        parts.append(s(n["breakeven"], "back above cost", "back above cost"))
    if n.get("recovering"):
        parts.append(s(n["recovering"], "off its low", "off their lows"))
    close = n.get("near", 0) + n.get("nearath", 0)
    if close:
        parts.append(f"{close} getting close")
    return ", ".join(parts) or f"{len(events)} change(s)"



# ----------------------------------------------------------------------
# Reminders
#
# Everything else in this system is triggered by a price. Nothing was
# triggered by a date, so lock-in expiries, record dates, advance tax
# instalments and "check this again in a month" had nowhere to live and
# were simply forgotten.
#
# Deliberately stateless. Repeating reminders compute their next occurrence
# from the anchor date arithmetically, and one-off reminders stop showing a
# fixed number of days after they pass. There is no reminders_state.json to
# fall out of sync, no acknowledgement to chase, and nothing that breaks if
# a run is missed or the file is edited by hand.
# ----------------------------------------------------------------------

REMINDERS_FILE = BASE_DIR / "reminders.csv"
REMINDER_GRACE_DAYS = 7        # how long a passed one-off keeps nagging
REMINDER_DEFAULT_LEAD = 7      # days of warning when lead_days is blank
REPEATS = {"none": 0, "weekly": 0, "monthly": 1, "quarterly": 3, "yearly": 12}


def _add_months(d, months):
    """Month arithmetic that survives month ends.

    31 January plus one month is 28 February, not an exception. Naive
    day-count arithmetic drifts a reminder anchored to the 31st backwards
    through the calendar over a year.
    """
    m = d.month - 1 + months
    year = d.year + m // 12
    month = m % 12 + 1
    last = [31, 29 if (year % 4 == 0 and (year % 100 != 0 or year % 400 == 0))
            else 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31][month - 1]
    return d.replace(year=year, month=month, day=min(d.day, last))


def next_occurrence(anchor, repeat, today, grace=REMINDER_GRACE_DAYS):
    """The next date this reminder is due, or None once it is finished.

    A one-off keeps showing for `grace` days after it passes, then stops.
    A repeater rolls forward past every occurrence already out of grace.
    """
    repeat = (repeat or "none").strip().lower()
    if repeat not in REPEATS:
        repeat = "none"
    if repeat == "none":
        return anchor if (today - anchor).days <= grace else None

    # Every occurrence is computed from the original anchor, never from the
    # previous occurrence. Stepping month by month clamps a 31st anchor to
    # the 28th in February and then keeps it there, so a monthly reminder
    # anchored to the 31st silently drifts backwards through the calendar.
    n, d = 0, anchor
    while (today - d).days > grace and n < 600:
        n += 1
        d = (anchor + timedelta(days=7 * n) if repeat == "weekly"
             else _add_months(anchor, REPEATS[repeat] * n))
    return d


def load_reminders():
    """Read reminders.csv. Returns (due, errors).

    Malformed rows are reported, never silently dropped. A reminder that
    vanishes because a date was typed wrong is worse than no reminder at
    all, because you believe it is still watching.
    """
    if not REMINDERS_FILE.exists():
        return [], []
    today = datetime.now(IST).date()
    due, errors = [], []
    try:
        with open(REMINDERS_FILE, newline="", encoding="utf-8-sig") as f:
            rows = list(csv.DictReader(f))
    except (OSError, csv.Error) as exc:
        return [], [f"reminders.csv could not be read: {exc}"]

    for i, row in enumerate(rows, start=2):
        label = (row.get("label") or "").strip()
        if not label or label.startswith("#"):
            continue
        if (row.get("enabled", "yes") or "yes").strip().lower() in (
                "no", "false", "0", "off"):
            continue
        raw = (row.get("date") or "").strip()
        anchor = None
        for fmt in ("%Y-%m-%d", "%d-%m-%Y", "%d/%m/%Y", "%d %b %Y"):
            try:
                anchor = datetime.strptime(raw, fmt).date()
                break
            except ValueError:
                continue
        if not anchor:
            errors.append(f"row {i} ({label}): date '{raw}' not understood")
            continue
        try:
            lead = int(float((row.get("lead_days") or "").strip()
                             or REMINDER_DEFAULT_LEAD))
        except ValueError:
            errors.append(f"row {i} ({label}): lead_days "
                          f"'{row.get('lead_days')}' is not a number")
            lead = REMINDER_DEFAULT_LEAD

        when = next_occurrence(anchor, row.get("repeat"), today)
        if when is None:
            continue
        left = (when - today).days
        if left > lead:
            continue
        due.append({"label": label, "date": when, "days": left,
                    "ticker": (row.get("ticker") or "").strip().upper(),
                    "note": (row.get("note") or "").strip(),
                    "repeat": (row.get("repeat") or "none").strip().lower()})
    due.sort(key=lambda r: r["days"])
    return due, errors


def reminder_phrase(r):
    d = r["days"]
    if d < 0:
        return f"overdue by {abs(d)} day" + ("s" if abs(d) != 1 else "")
    if d == 0:
        return "today"
    if d == 1:
        return "tomorrow"
    return f"in {d} days"


HISTORY_FILE = BASE_DIR / "portfolio_history.csv"
HISTORY_FIELDS = ["date", "invested", "current", "pl", "pl_pct",
                  "holdings", "winners", "losers",
                  # Index closes, appended so past rows keep working: a row
                  # written before this existed simply has them blank.
                  "nifty50", "nifty500", "midcap", "smallcap"]


# ----------------------------------------------------------------------
# Benchmarks
#
# "Up 48%" means nothing on its own. Up 48% while the index did 60% is a
# bad outcome wearing a green number. Four index levels are stored daily
# alongside the portfolio so any period can be compared honestly later.
#
# Four extra quotes once a day. Negligible against the Actions budget.
# ----------------------------------------------------------------------

BENCHMARKS = {
    "nifty50": "^NSEI",
    "nifty500": "^CRSLDX",
    "midcap": "NIFTY_MIDCAP_100.NS",
    "smallcap": "^CNXSC",
}


def fetch_benchmarks():
    """Index closes for today. Missing values are left blank, never guessed."""
    try:
        import yfinance as yf
    except ImportError:
        return {}
    out = {}
    for name, sym in BENCHMARKS.items():
        try:
            t = yf.Ticker(sym)
            px = None
            fi = getattr(t, "fast_info", None)
            if fi is not None:
                px = getattr(fi, "last_price", None)
            if not px:
                h = t.history(period="5d")
                if h is not None and len(h) and "Close" in h:
                    px = float(h["Close"].dropna().iloc[-1])
            if px:
                out[name] = round(float(px), 2)
        except Exception:  # noqa: BLE001
            continue
    return out


# ----------------------------------------------------------------------
# XIRR
#
# "Up 48.5%" is the wrong number and always has been. It compares today's
# value against money that went in across five years, treating a rupee
# invested last month the same as one invested in 2021. XIRR is the
# annualised rate that actually reconciles every cashflow with its date.
#
# The limitation, stated rather than hidden: only the OLDEST purchase date
# per holding is known, so a position built up over several buys is treated
# as a single outflow on that first date. That overstates the holding period
# and therefore understates the annual rate. It is wrong in a known
# direction, which is far more useful than a number that is wrong in an
# unknown one.
# ----------------------------------------------------------------------


def xirr(flows, guess=0.15):
    """Annualised return that reconciles dated cashflows. None if unsolvable.

    Bisection rather than Newton: Newton diverges on the irregular, heavily
    front-loaded flow patterns a real portfolio produces, and a wrong return
    figure is worse than no figure.
    """
    flows = [(d, a) for d, a in flows if a]
    if len(flows) < 2:
        return None
    if not (any(a < 0 for _, a in flows) and any(a > 0 for _, a in flows)):
        return None
    t0 = min(d for d, _ in flows)

    def npv(rate):
        total = 0.0
        for d, a in flows:
            years = (d - t0).days / 365.0
            try:
                total += a / ((1 + rate) ** years)
            except (OverflowError, ZeroDivisionError):
                return None
        return total

    lo, hi = -0.9999, 10.0
    f_lo, f_hi = npv(lo), npv(hi)
    if f_lo is None or f_hi is None or f_lo * f_hi > 0:
        return None
    for _ in range(200):
        mid = (lo + hi) / 2
        f_mid = npv(mid)
        if f_mid is None:
            return None
        if abs(f_mid) < 1e-6:
            break
        if f_lo * f_mid < 0:
            hi, f_hi = mid, f_mid
        else:
            lo, f_lo = mid, f_mid
    return round(mid * 100, 2)


def portfolio_xirr(entries):
    """XIRR across every holding with a known purchase date.

    Holdings without a date are excluded entirely rather than being dated
    from a guess, and the count is reported so the figure can be read with
    the right amount of trust.
    """
    today = datetime.now(IST).date()
    flows, covered, skipped, value = [], 0, 0, 0.0
    for e in entries:
        if not e.get("price") or not e.get("qty") or not e.get("avg_cost"):
            continue
        days, basis = holding_age(e)
        if not days or basis != "buy_date":
            skipped += 1
            continue
        bought = today - timedelta(days=days)
        flows.append((bought, -e["avg_cost"] * e["qty"]))
        value += e["price"] * e["qty"]
        covered += 1
    if covered < 2:
        return None
    flows.append((today, value))
    rate = xirr(flows)
    if rate is None:
        return None
    invested = -sum(a for _, a in flows if a < 0)
    return {"xirr": rate, "holdings": covered, "skipped": skipped,
            "invested": round(invested, 2), "value": round(value, 2),
            "absolute_pct": round((value / invested - 1) * 100, 2)
            if invested else None}


def month_review(rows, entries):
    """A calendar-month summary of the portfolio against the indices.

    Returns None until there is a row from far enough back, rather than
    comparing against the oldest row available and calling a nine-day
    stretch "the month".
    """
    if len(rows) < 2:
        return None
    latest = rows[-1]
    target = (datetime.now(IST) - timedelta(days=30)).strftime("%Y-%m-%d")
    older = [r for r in rows if r.get("date", "") <= target]
    if not older:
        return None
    base = older[-1]

    def num(r, k):
        try:
            return float(r.get(k) or 0)
        except (TypeError, ValueError):
            return 0.0

    # Money added during the month is not performance, so the comparison is
    # made on value net of new investment rather than on the raw total.
    inv_then, inv_now = num(base, "invested"), num(latest, "invested")
    cur_then, cur_now = num(base, "current"), num(latest, "current")
    added = inv_now - inv_then
    if not cur_then:
        return None
    ret = ((cur_now - added) / cur_then - 1) * 100

    idx = {}
    for name in BENCHMARKS:
        a, b = num(base, name), num(latest, name)
        if a and b:
            idx[name] = round((b / a - 1) * 100, 2)

    priced = [e for e in entries if e.get("day_pct") is not None]
    movers = sorted(priced, key=lambda e: -(e.get("pl_abs") or 0))
    return {
        "from": base.get("date"), "to": latest.get("date"),
        "return_pct": round(ret, 2),
        "value_then": round(cur_then, 2), "value_now": round(cur_now, 2),
        "added": round(added, 2),
        "indices": idx,
        "winners": int(num(latest, "winners")), "losers": int(num(latest, "losers")),
        "best": [{"ticker": e["ticker"], "pl_abs": round(e.get("pl_abs") or 0),
                  "pl_pct": e.get("pl_pct")} for e in movers[:5]],
        "worst": [{"ticker": e["ticker"], "pl_abs": round(e.get("pl_abs") or 0),
                   "pl_pct": e.get("pl_pct")} for e in movers[-5:][::-1]],
    }


def append_history(digest):
    """Keep one row per day so performance can be seen over time.

    digest.json is overwritten on every run, so without this the portfolio's
    own history is discarded daily and questions like "how did this month go"
    have no data behind them. One row a day is a few kilobytes a year.
    """
    t = (digest.get("totals") or {}).get("inr")
    if not t:
        return
    today = datetime.now(IST).strftime("%Y-%m-%d")
    rows = []
    if HISTORY_FILE.exists():
        try:
            with open(HISTORY_FILE, newline="", encoding="utf-8-sig") as f:
                rows = [r for r in csv.DictReader(f)
                        if r.get("date") and r["date"] != today]
        except (OSError, csv.Error):
            rows = []
    winners = sum(1 for e in digest["entries"]
                  if (e.get("pl_pct") or 0) > 0)
    losers = sum(1 for e in digest["entries"]
                 if (e.get("pl_pct") or 0) < 0)
    bench = fetch_benchmarks()
    rows.append({"date": today,
                 **{k: f"{v:.2f}" for k, v in bench.items()},
                 "invested": f"{t['invested']:.2f}",
                 "current": f"{t['current']:.2f}",
                 "pl": f"{t['pl_abs']:.2f}",
                 "pl_pct": f"{t['pl_pct']:.2f}",
                 "holdings": str(t["count"]),
                 "winners": str(winners), "losers": str(losers)})
    rows.sort(key=lambda r: r["date"])
    with open(HISTORY_FILE, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=HISTORY_FIELDS)
        w.writeheader()
        for r in rows:
            w.writerow({k: r.get(k, "") for k in HISTORY_FIELDS})
    return rows


def history_lines(rows, cur="\u20B9"):
    """Compare today against a week and a month ago, from the saved history."""
    if not rows or len(rows) < 2:
        return []
    latest = rows[-1]
    out = []
    for back, label in ((7, "a week"), (30, "a month"), (90, "three months")):
        target = (datetime.now(IST) - timedelta(days=back)).strftime("%Y-%m-%d")
        older = [r for r in rows if r["date"] <= target]
        if not older:
            continue
        was = older[-1]
        try:
            now_v, was_v = float(latest["current"]), float(was["current"])
        except (ValueError, KeyError):
            continue
        if was_v == 0:
            continue
        ch = now_v - was_v
        out.append(f"  vs {label} ago ({was['date']}): "
                   f"{cur}{ch:+,.0f} ({(now_v / was_v - 1) * 100:+.2f}%)")
    return (["PORTFOLIO OVER TIME"] + out) if out else []



CONCENTRATION_LIMIT = 12.0     # percent of portfolio in one stock
THEME_LIMIT = 20.0             # percent in one account, as a rough proxy


def concentration_lines(entries, total):
    """Flag single names that have grown into an outsized share.

    A winner that keeps winning quietly becomes a concentration decision
    nobody made. Aggregated across accounts, because the same stock held in
    four places is one exposure.
    """
    if not total:
        return []
    agg = {}
    for e in entries:
        if not e.get("current"):
            continue
        agg[e["ticker"]] = agg.get(e["ticker"], 0) + e["current"]
    big = [(tk, v, v / total * 100) for tk, v in agg.items()
           if v / total * 100 >= CONCENTRATION_LIMIT]
    if not big:
        return []
    big.sort(key=lambda x: -x[2])
    out = ["CONCENTRATION"]
    for tk, v, pctv in big:
        out.append(f"  {tk} is {pctv:.1f}% of the portfolio "
                   f"(Rs {v:,.0f}). Stated, not judged.")
    return out



LTCG_EXEMPTION_PER_PAN = 125000


def per_account_tax(entries):
    """Capital gains position for each person, and how much of their annual
    long-term exemption is still unused.

    This is the calculation no broker can do for you, because each broker
    only sees its own account and the exemption belongs to the PAN. With
    several family accounts there is a meaningful amount of tax-free gain
    available each year that simply expires unused if nobody counts it.

    Long-term quantity comes from the lt_qty column. Where a broker does not
    report it the holding is treated as short term, which understates the
    exemption available rather than overstating it.
    """
    acc = {}
    for e in entries:
        price = e.get("price")
        if not price:
            continue
        for lot in e.get("lots") or []:
            cost, qty = lot.get("cost"), lot.get("qty")
            if not cost or not qty:
                continue
            who = lot["account"]
            a = acc.setdefault(who, {"lt_gain": 0.0, "lt_loss": 0.0,
                                     "st_gain": 0.0, "st_loss": 0.0,
                                     "value": 0.0, "unknown_lt": 0,
                                     "harvest_lt": [], "harvest_st": []})
            gain_ps = price - cost
            lt_q = min(lot.get("lt_qty") or 0, qty)
            st_q = qty - lt_q
            if not lot.get("lt_qty"):
                a["unknown_lt"] += 1
            a["value"] += price * qty
            if lt_q:
                amt = gain_ps * lt_q
                if amt >= 0:
                    a["lt_gain"] += amt
                    a["harvest_lt"].append((e["ticker"], amt, lt_q))
                else:
                    a["lt_loss"] += amt
                    a["harvest_lt"].append((e["ticker"], amt, lt_q))
            if st_q:
                amt = gain_ps * st_q
                if amt >= 0:
                    a["st_gain"] += amt
                else:
                    a["st_loss"] += amt
                    a["harvest_st"].append((e["ticker"], amt, st_q))
    for who, a in acc.items():
        a["lt_net"] = a["lt_gain"] + a["lt_loss"]
        a["st_net"] = a["st_gain"] + a["st_loss"]
        a["exempt_used"] = max(0.0, min(LTCG_EXEMPTION_PER_PAN, a["lt_net"]))
        a["exempt_left"] = LTCG_EXEMPTION_PER_PAN - a["exempt_used"]
        a["harvest_lt"].sort(key=lambda x: -x[1])
        a["harvest_st"].sort(key=lambda x: x[1])
    return acc


def exemption_lines(acc):
    if not acc:
        return []
    out = ["THE TAX-FREE ALLOWANCE NOBODY TRACKS",
           f"  Each PAN gets Rs {LTCG_EXEMPTION_PER_PAN:,.0f} of long-term gains "
           f"tax free every financial year. Across {len(acc)} accounts that is "
           f"Rs {LTCG_EXEMPTION_PER_PAN * len(acc):,.0f} a year, and any part "
           f"not used by 31 March is gone."]
    total_left = 0.0
    for who, a in sorted(acc.items(), key=lambda x: -x[1]["value"]):
        out.append("")
        out.append(f"  {who}  (holdings worth Rs {a['value']:,.0f})")
        out.append(f"    Long-term position if sold today: "
                   f"Rs {a['lt_net']:+,.0f}")
        if a["lt_net"] > 0:
            out.append(f"    Rs {a['exempt_used']:,.0f} of the allowance would "
                       f"be used, Rs {a['exempt_left']:,.0f} still free")
        else:
            out.append(f"    Nothing to shelter yet, the full "
                       f"Rs {LTCG_EXEMPTION_PER_PAN:,.0f} is unused")
        total_left += a["exempt_left"]
        if a["st_net"]:
            out.append(f"    Short-term position: Rs {a['st_net']:+,.0f} "
                       f"(taxed at 20% if realised)")
        if a["harvest_lt"] and a["harvest_lt"][0][1] > 5000:
            tk, amt, q = a["harvest_lt"][0]
            out.append(f"    Largest long-term gain sitting there: {tk}, "
                       f"Rs {amt:,.0f} on {q:,.0f} shares")
        losses = [h for h in a["harvest_st"] if h[1] < -2000][:3]
        if losses and a["st_gain"] > 0:
            tot = sum(abs(h[1]) for h in losses)
            out.append("    Short-term losses available to offset short-term "
                       "gains: " + ", ".join(f"{t} Rs {abs(v):,.0f}"
                                              for t, v, _ in losses)
                       + f" (about Rs {min(tot, a['st_gain']) * 0.20:,.0f} of tax)")
        if a["unknown_lt"]:
            out.append(f"    {a['unknown_lt']} holding(s) here have no long-term "
                       f"quantity recorded, so they count as short term and the "
                       f"figure above is conservative")
    out.append("")
    out.append(f"  Unused across the family: Rs {total_left:,.0f}. Rates and "
               f"rules change each Budget; confirm with your CA before acting.")
    return out


def build():
    rows = load_rows()
    fired = load_fired()
    by_symbol = {}
    for row in rows:
        ex = row["exchange"].upper()
        symbol = row["ticker"].upper() + SUFFIX.get(ex, "")
        loc_bits = [b for b in (row.get("account", "").strip(),
                                row.get("broker", "").strip()) if b]
        def _n(f):
            try:
                return float(row.get(f, ""))
            except ValueError:
                return None
        by_symbol.setdefault(symbol, {"ticker": row["ticker"].upper(),
                                       "exchange": ex, "rows": [],
                                       "location": " / ".join(loc_bits),
                                       "avg_cost": _n("avg_cost"),
                                       "qty": _n("qty"),
                                       "buy_date": row.get("buy_date", "").strip()})
        try:
            _lt = float(row.get("lt_qty", "") or 0)
        except ValueError:
            _lt = 0
        by_symbol[symbol].setdefault("lots", []).append({
            "account": row.get("account", "").strip() or "Unassigned",
            "broker": row.get("broker", "").strip(),
            "cost": _n("avg_cost"), "qty": _n("qty"), "lt_qty": _lt,
            "buy_date": row.get("buy_date", "").strip()})
        by_symbol[symbol]["rows"].append(row)
        if not by_symbol[symbol]["location"] and loc_bits:
            by_symbol[symbol]["location"] = " / ".join(loc_bits)

    # avg_cost and qty were taken from the FIRST row for a symbol, so any
    # holding split across accounts counted only one lot. SBIFUNDS showed 32
    # shares instead of 58. Every figure downstream, portfolio value, P&L,
    # concentration, was wrong for every multi-account name. Aggregate across
    # lots instead, weighting the cost by quantity. Rows carrying only an
    # alert have no cost or qty and drop out on their own.
    for grp in by_symbol.values():
        priced = [l for l in grp.get("lots", []) if l.get("cost") and l.get("qty")]
        total_qty = sum(l["qty"] for l in priced)
        if total_qty:
            grp["qty"] = total_qty
            grp["avg_cost"] = round(
                sum(l["cost"] * l["qty"] for l in priced) / total_qty, 4)

    entries = []
    for symbol, grp in by_symbol.items():
        snap = fetch_snapshot(symbol)
        time.sleep(1)  # gentle pacing for Yahoo
        cur = "$" if grp["exchange"] == "US" else "\u20B9"
        e = {"ticker": grp["ticker"], "exchange": grp["exchange"],
             "currency": cur, "location": grp.get("location", ""),
             "avg_cost": grp.get("avg_cost"), "qty": grp.get("qty"),
             "buy_date": grp.get("buy_date", ""),
             "lots": grp.get("lots", []),
             "sector": (grp.get("rows") or [{}])[0].get("sector", "").strip(),
             **snap, "bands": []}
        price = snap.get("price")
        if price:
            if snap.get("prev_close"):
                e["day_pct"] = round(pct(price, snap["prev_close"]), 2)
            if snap.get("year_high"):
                e["off_high_pct"] = round(pct(price, snap["year_high"]), 1)
            if snap.get("year_low"):
                e["off_low_pct"] = round(pct(price, snap["year_low"]), 1)
            e["history_days"] = snap.get("ath_days")
            if grp.get("avg_cost"):
                e["pl_pct"] = round(pct(price, grp["avg_cost"]), 1)
                if grp.get("qty"):
                    e["invested"] = round(grp["avg_cost"] * grp["qty"], 2)
                    e["current"] = round(price * grp["qty"], 2)
                    e["pl_abs"] = round(e["current"] - e["invested"], 2)
            if snap.get("div_ttm") and grp.get("qty"):
                e["div_income"] = round(snap["div_ttm"] * grp["qty"], 2)
                e["div_yield"] = round(snap["div_ttm"] / price * 100, 2)
                if grp.get("avg_cost"):
                    # Yield on what you paid, not on today's price. For a
                    # holding up 130% these are very different numbers.
                    e["div_yoc"] = round(snap["div_ttm"] / grp["avg_cost"] * 100, 2)
            if snap.get("ath"):
                e["off_ath_pct"] = round(pct(price, snap["ath"]), 1)
            held_days, held_basis = holding_age(e)
            if held_days:
                e["held_days"] = held_days
                e["held_basis"] = held_basis
            if snap.get("mean_target"):
                e["target_upside_pct"] = round(pct(snap["mean_target"], price), 1)
            for row in grp["rows"]:
                try:
                    tgt = band_target(row)
                except (ValueError, KeyError):
                    continue
                if tgt is None:
                    continue   # watch-only row, no band to report
                k = alert_key(row, symbol)
                status = "fired" if k in fired else "armed"
                away = pct(tgt, price)
                e["bands"].append({"direction": row["direction"],
                                    "target": round(tgt, 2),
                                    "away_pct": round(away, 1),
                                    "status": status})
        entries.append(e)

    div_total = sum(e.get("div_income") or 0 for e in entries)
    div_payers = [e for e in entries if e.get("div_income")]

    # Portfolio totals across every account, which no single broker app can
    # show you. Only counts holdings where you recorded avg_cost and qty.
    priced = [e for e in entries if e.get("invested")]
    totals = {}
    if priced:
        inr = [e for e in priced if e["currency"] != "$"]
        if inr:
            ti = sum(e["invested"] for e in inr)
            tc = sum(e["current"] for e in inr)
            totals["inr"] = {"invested": round(ti, 2), "current": round(tc, 2),
                             "pl_abs": round(tc - ti, 2),
                             "pl_pct": round((tc / ti - 1) * 100, 2) if ti else 0,
                             "count": len(inr)}

    pstate = load_position_state()
    pos_events = rank_events(detect_position_events(entries, pstate))
    # The peak each position has reached while tracked is already maintained
    # in position_state. Carrying it onto the entry is what lets the brief
    # say how much of a gain has been handed back.
    for e in entries:
        st = pstate.get(f"{e['ticker']}|{e['exchange']}") or {}
        if st.get("high"):
            e["peak"] = st["high"]
    save_position_state(pstate)

    acct_tax = per_account_tax(entries)
    digest = {"date": datetime.now(IST).strftime("%d %b %Y"),
              "events": pos_events,
              "concentration": [
                  {"ticker": tk, "value": round(v, 2),
                   "pct": round(v / (totals.get("inr", {}).get("current") or 1) * 100, 2)}
                  for tk, v in sorted(
                      {e["ticker"]: sum(x.get("current") or 0 for x in entries
                                        if x["ticker"] == e["ticker"])
                       for e in entries if e.get("current")}.items(),
                      key=lambda x: -x[1])[:10]],
              "per_account_tax": {k: {kk: vv for kk, vv in v.items()
                                      if kk not in ("harvest_lt", "harvest_st")}
                                  for k, v in acct_tax.items()},
              "dividends": {"ttm_total": round(div_total, 2),
                            "payers": len(div_payers),
                            "top": sorted(
                                [{"ticker": e["ticker"],
                                  "income": e["div_income"],
                                  "yield": e.get("div_yield"),
                                  "yoc": e.get("div_yoc")}
                                 for e in div_payers],
                                key=lambda x: -x["income"])[:8]},
              "totals": totals,
              # Surfaced so the dashboard can render peaks and holding periods
              # without reimplementing the split adjustment or the age fallback.
              # A third copy of that logic would drift like the first two did.
              "dead_money": [{k: v for k, v in d.items() if k != "detail"}
                             for d in dead_money(entries)],
              "tax": build_tax_summary(entries),
              "generated_utc": datetime.now(ZoneInfo("UTC")).isoformat(timespec="seconds"),
              "entries": entries}
    DIGEST_FILE.write_text(json.dumps(digest, indent=2) + "\n")
    digest["history"] = append_history(digest) or []
    digest["month"] = month_review(digest["history"], digest["entries"])
    digest["xirr"] = portfolio_xirr(digest["entries"])
    rem_due, rem_errors = load_reminders()
    digest["reminders"] = [{**r, "date": r["date"].strftime("%Y-%m-%d")}
                           for r in rem_due]
    digest["reminder_errors"] = rem_errors
    return digest


def format_text(digest):
    lines = [f"Portfolio digest  {digest['date']}", ""]
    ev = digest.get("events") or []
    if ev:
        icon = {"breakeven": "[BREAKEVEN]", "near": "[NEAR COST]",
                "recovering": "[RECOVERING]", "newlow": "[NEW LOW]",
                "ath": "[ALL-TIME HIGH]", "nearath": "[NEAR ATH]"}
        lines.append("POSITION CHANGES SINCE YESTERDAY")
        for x in ev:
            lines.append(f"  {icon.get(x['kind'], '')} {x['ticker']}: {x['text']}")
        lines.append("  These are statements about your own position, not "
                     "recommendations.")
        lines.append("")

    tt = (digest.get("totals") or {}).get("inr") or {}
    cl = concentration_lines(digest.get("entries") or [], tt.get("current"))
    if cl:
        lines.extend(cl)
        lines.append("")

    hl = history_lines(digest.get("history") or [])
    if hl:
        lines.extend(hl)
        lines.append("")

    el = exemption_lines(per_account_tax(digest.get("entries") or []))
    if el:
        lines.extend(el)
        lines.append("")

    dv = digest.get("dividends") or {}
    if dv.get("ttm_total"):
        lines.append("DIVIDENDS, LAST 12 MONTHS")
        lines.append(f"  About Rs {dv['ttm_total']:,.0f} from {dv['payers']} "
                     f"holdings")
        for d in dv["top"][:5]:
            extra = ""
            if d.get("yoc"):
                extra = f", {d['yoc']:.1f}% on what you paid"
            lines.append(f"  {d['ticker']}: Rs {d['income']:,.0f}"
                         + (f" ({d['yield']:.1f}% yield{extra})" if d.get("yield") else ""))
        lines.append("  Based on dividends declared per share over the last "
                     "year applied to your current quantity, so it is an "
                     "indication rather than what actually reached your account.")
        lines.append("")

    t = (digest.get("totals") or {}).get("inr")
    if t:
        lines.append(f"Across {t['count']} holdings with cost recorded: "
                     f"invested Rs {t['invested']:,.0f}, "
                     f"now Rs {t['current']:,.0f}, "
                     f"{t['pl_abs']:+,.0f} ({t['pl_pct']:+.2f}%)")
        lines.append("")
    for e in digest["entries"]:
        c = e["currency"]
        if not e.get("price"):
            lines.append(f"{e['ticker']}: price unavailable"
                         f" ({e.get('error', 'no data')})")
            lines.append("")
            continue
        day = f"  {e['day_pct']:+.2f}% today" if e.get("day_pct") is not None else ""
        lines.append(f"{e['ticker']}  {c}{e['price']:,.2f}{day}")
        for b in e["bands"]:
            flag = " [FIRED]" if b["status"] == "fired" else ""
            lines.append(f"  band {b['direction']} {c}{b['target']:,.2f}"
                         f" ({b['away_pct']:+.1f}% away){flag}")
        for tl in tax_lines(e):
            lines.append(f"  {tl}")
        if e.get("pl_pct") is not None:
            pl = f"  your cost {c}{e['avg_cost']:,.2f}, {e['pl_pct']:+.1f}%"
            if e.get("pl_abs") is not None:
                pl += f" ({c}{e['pl_abs']:+,.2f} on {e['qty']:,.0f} shares)"
            lines.append(pl)
        ctx = []
        if e.get("ath"):
            lines.append(f"  all-time high {c}{e['ath']:,.2f}"
                         f" ({e.get('off_ath_pct', 0):+.1f}% from here)"
                         + (f", set {e['ath_date']}" if e.get('ath_date') else ""))
        if e.get("off_high_pct") is not None:
            ctx.append(f"{e['off_high_pct']:+.1f}% vs 52w high")
        if e.get("off_low_pct") is not None:
            ctx.append(f"{e['off_low_pct']:+.1f}% vs 52w low")
        if ctx:
            lines.append("  " + ", ".join(ctx))
        if e.get("mean_target"):
            lines.append(f"  analyst mean target {c}{e['mean_target']:,.2f}"
                         f" ({e.get('target_upside_pct', 0):+.1f}%)")
        if e.get("earnings"):
            lines.append(f"  next earnings: {e['earnings']}")
        lines.append("")
    t = digest.get("tax")
    if t:
        lines.append("TAX POSITION ON UNREALISED P&L")
        lines.append(f"  Short term: gains Rs {t['st_gain']:,.0f}, "
                     f"losses Rs {t['st_loss']:,.0f}, net Rs {t['net_st']:+,.0f}")
        lines.append(f"  Long term:  gains Rs {t['lt_gain']:,.0f}, "
                     f"losses Rs {t['lt_loss']:,.0f}, net Rs {t['net_lt']:+,.0f}")
        lines.append(f"  If all of it were realised today, tax would be "
                     f"roughly Rs {t['est_tax']:,.0f}")
        if t["st_loss"] < 0 and t["st_gain"] > 0:
            off = min(abs(t["st_loss"]), t["st_gain"])
            lines.append(f"  Rs {off:,.0f} of short-term gains could be offset "
                         f"by realising short-term losses, saving about "
                         f"Rs {off * STCG_RATE:,.0f}")
        for tk, left, gain, saving in t["approaching"][:5]:
            lines.append(f"  {tk} turns long term in {left} days "
                         f"(worth about Rs {saving:,.0f} on the current gain)")
        if t["no_date"]:
            lines.append(f"  {t['no_date']} holding(s) have no buy_date, so they "
                         f"are excluded from these figures")
        lines.append("  Rates change each Budget and this ignores your other "
                     "income. Confirm with your CA before acting.")
        lines.append("")
    ents = digest.get("entries") or []
    priced = sum(1 for e in ents if e.get("price"))
    if ents and priced < len(ents) * 0.8:
        lines.append(f"WARNING: only {priced} of {len(ents)} holdings returned "
                     f"a price this run. The totals above are therefore "
                     f"incomplete, not a real fall in value.")
        lines.append("")

    lines.append("Data: Yahoo Finance, best effort. Analyst coverage on "
                 "smallcaps is thin; treat targets as context, not signals.")
    return "\n".join(lines)


def format_html(digest):
    """Table-based, inline-styled HTML for broad email client compatibility
    (Outlook's engine ignores flex/grid, so plain tables + inline styles only).
    """
    INK, PANEL, LINE, PAPER, MUTED = "#160A0C", "#241114", "#47232A", "#F4EAE7", "#C29CA1"
    CRIMSON, ARMED, FIRED = "#D24A4F", "#63B98A", "#E0A44C"
    FONT = "'Segoe UI',Arial,sans-serif"
    MONO = "Consolas,'Courier New',monospace"
    cur_sym = "\u20B9"

    def row(e):
        cur = e["currency"]
        if not e.get("price"):
            return (f'<tr><td style="padding:14px 18px;border-bottom:1px solid {LINE};'
                    f'font-family:{FONT};color:{MUTED};font-size:13px">'
                    f'<b style="color:{PAPER}">{e["ticker"]}</b> &mdash; price unavailable '
                    f'({e.get("error","no data")})</td></tr>')
        day = e.get("day_pct")
        day_html = ""
        if day is not None:
            color = ARMED if day >= 0 else CRIMSON
            day_html = (f'<span style="color:{color};font-family:{MONO};font-size:13px">'
                        f'{"+" if day>=0 else ""}{day}% today</span>')
        bands_html = ""
        for b in e["bands"]:
            badge = (f'<span style="background:#3A2A12;color:{FIRED};font-size:10px;'
                     f'font-weight:600;letter-spacing:.04em;border-radius:10px;'
                     f'padding:1px 8px;margin-left:6px">FIRED</span>'
                     if b["status"] == "fired" else "")
            bands_html += (f'<div style="font-family:{MONO};font-size:13px;color:{PAPER};'
                           f'margin-top:4px">{b["direction"]} {cur}{fmt_num(b["target"])} '
                           f'<span style="color:{MUTED}">'
                           f'({"+" if b["away_pct"]>=0 else ""}{b["away_pct"]}% away)</span>'
                           f'{badge}</div>')
        ctx = []
        if e.get("off_high_pct") is not None:
            ctx.append(f'{e["off_high_pct"]:+.1f}% vs 52w high')
        if e.get("off_low_pct") is not None:
            ctx.append(f'{e["off_low_pct"]:+.1f}% vs 52w low')
        if e.get("ath"):
            ctx.append(f'ATH {cur}{fmt_num(e["ath"])} '
                       f'({e.get("off_ath_pct",0):+.1f}%)')
        if e.get("mean_target"):
            ctx.append(f'target {cur}{fmt_num(e["mean_target"])} '
                       f'({e.get("target_upside_pct",0):+.1f}%)')
        if e.get("earnings"):
            ctx.append(f'earnings {e["earnings"]}')
        if e.get("location"):
            ctx.append(f'held in {e["location"]}')
        for tl in tax_lines(e):
            ctx.append(tl)
        pl_html = ""
        if e.get("pl_pct") is not None:
            pcol = ARMED if e["pl_pct"] >= 0 else CRIMSON
            pl_txt = f'cost {cur}{fmt_num(e["avg_cost"])} &middot; {e["pl_pct"]:+.1f}%'
            if e.get("pl_abs") is not None:
                pl_txt += f' ({cur}{e["pl_abs"]:+,.0f})'
            pl_html = (f'<div style="font-family:{FONT};font-size:12.5px;'
                       f'color:{pcol};margin-top:4px">{pl_txt}</div>')
        ctx_html = (f'<div style="font-family:{FONT};font-size:12px;color:{MUTED};'
                    f'margin-top:6px">{" &middot; ".join(ctx)}</div>') if ctx else ""
        return (f'<tr><td style="padding:14px 18px;border-bottom:1px solid {LINE}">'
                f'<div style="font-family:{FONT};font-weight:700;font-size:16px;'
                f'color:{PAPER}">{e["ticker"]} '
                f'<span style="font-size:11px;font-weight:400;color:{MUTED};'
                f'border:1px solid {LINE};border-radius:4px;padding:1px 6px">'
                f'{e["exchange"]}</span></div>'
                f'<div style="margin-top:4px;font-family:{MONO};font-size:15px;'
                f'color:{PAPER}">{cur}{fmt_num(e["price"])} &nbsp; {day_html}</div>'
                f'{pl_html}{bands_html}{ctx_html}</td></tr>')

    def fmt_num(n):
        return f"{n:,.2f}"

    rows = "".join(row(e) for e in digest["entries"])
    ev = rank_events(digest.get("events") or [])
    events_html = ""
    if ev:
        col = {"good": ARMED, "bad": CRIMSON, "flat": FIRED}
        label = {"breakeven": "BACK TO BREAKEVEN", "near": "NEAR YOUR COST",
                 "recovering": "OFF ITS LOW", "newlow": "NEW LOW",
                 "ath": "ALL-TIME HIGH", "nearath": "NEAR ALL-TIME HIGH"}
        crossed = [x for x in ev if x["kind"] in CROSSED]
        approaching = [x for x in ev if x["kind"] in APPROACHING]

        def sub(title):
            return (f'<div style="font-family:{FONT};font-size:10px;'
                    f'font-weight:700;letter-spacing:.06em;color:{MUTED};'
                    f'margin:16px 0 2px">{title}</div>')

        items = ""
        # Crossings get the full treatment: badge, name, the sentence.
        if crossed:
            items += sub("CROSSED A LINE")
        for x in crossed:
            c = col.get(EVENT_TONE.get(x["kind"]), PAPER)
            items += (f'<table role="presentation" width="100%" cellpadding="0" '
                      f'cellspacing="0" style="margin-top:8px"><tr>'
                      f'<td style="width:3px;background:{c}"></td>'
                      f'<td style="padding:2px 0 2px 10px">'
                      f'<span style="font-family:{FONT};font-size:10px;'
                      f'font-weight:700;letter-spacing:.05em;color:{c};'
                      f'border:1px solid {c};border-radius:10px;padding:1px 7px">'
                      f'{label.get(x["kind"], "")}</span> '
                      f'<b style="font-family:{FONT};font-size:14px;color:{PAPER}">'
                      f'{x["ticker"]}</b>'
                      f'<div style="font-family:{FONT};font-size:12.5px;'
                      f'color:{MUTED};margin-top:2px">{x["text"]}</div>'
                      f'</td></tr></table>')

        # Approaches are proximity notices, not events. One tight line each,
        # ordered by how close they actually are, so the 0.0% sits above the
        # 4.0% instead of wherever the alphabet put it.
        if approaching:
            items += sub(f"GETTING CLOSE ({len(approaching)})")
            rows_ap = ""
            for x in approaching:
                c = col.get(EVENT_TONE.get(x["kind"]), PAPER)
                what = "cost" if x["kind"] == "near" else "peak"
                gap = x.get("gap")
                gap_txt = f'{gap:.1f}%' if gap is not None else "close"
                ref = x.get("ref")
                now_p = x.get("now")
                cur = x.get("cur", cur_sym)
                right = ""
                if ref is not None and now_p is not None:
                    right = (f'{cur}{fmt_num(now_p)} '
                             f'<span style="color:{MUTED}">vs {cur}{fmt_num(ref)}</span>')
                rows_ap += (
                    f'<tr>'
                    f'<td style="padding:5px 0;font-family:{FONT};font-size:13px;'
                    f'color:{PAPER};white-space:nowrap">'
                    f'<span style="color:{c}">&#9679;</span> '
                    f'<b>{x["ticker"]}</b></td>'
                    f'<td style="padding:5px 8px;font-family:{FONT};font-size:12.5px;'
                    f'color:{c};white-space:nowrap">{gap_txt} from {what}</td>'
                    f'<td align="right" style="padding:5px 0;font-family:{MONO};'
                    f'font-size:12.5px;color:{PAPER};white-space:nowrap">{right}</td>'
                    f'</tr>')
            items += (f'<table role="presentation" width="100%" cellpadding="0" '
                      f'cellspacing="0">{rows_ap}</table>')

        events_html = (
            f'<tr><td style="padding:14px 18px;border-bottom:1px solid {LINE};'
            f'background:{INK}">'
            f'<div style="font-family:{FONT};font-size:11px;color:{MUTED};'
            f'letter-spacing:.06em">POSITION CHANGES SINCE YESTERDAY</div>'
            f'<div style="font-family:{FONT};font-size:15px;font-weight:700;'
            f'color:{PAPER};margin-top:4px">{events_summary(ev)}</div>'
            f'{items}'
            f'<div style="font-family:{FONT};font-size:11px;color:{MUTED};'
            f'margin-top:14px">Ordering reflects how far something moved. '
            f'These are statements about your own position measured against '
            f'what you paid, not recommendations.</div></td></tr>')

    # Reminders sit above everything the market decided, because they are the
    # only items on the page that you put there yourself.
    rem = digest.get("reminders") or []
    rem_err = digest.get("reminder_errors") or []
    rem_html = ""
    if rem or rem_err:
        rows = ""
        for r in rem:
            c = CRIMSON if r["days"] < 0 else (FIRED if r["days"] <= 1 else ARMED)
            tick = (f' <span style="color:{MUTED}">[{r["ticker"]}]</span>'
                    if r.get("ticker") else "")
            note = (f'<div style="font-family:{FONT};font-size:12px;'
                    f'color:{MUTED};margin-top:2px">{r["note"]}</div>'
                    if r.get("note") else "")
            rows += (f'<tr><td style="padding:6px 0;border-bottom:1px solid {LINE}">'
                     f'<span style="color:{c};font-size:13px">&#9679;</span> '
                     f'<b style="font-family:{FONT};font-size:13.5px;'
                     f'color:{PAPER}">{r["label"]}</b>{tick}'
                     f'<span style="font-family:{FONT};font-size:12.5px;'
                     f'color:{c}"> &middot; {reminder_phrase(r)}</span>'
                     f'<span style="font-family:{FONT};font-size:11.5px;'
                     f'color:{MUTED}"> ({r["date"]}'
                     + (f', repeats {r["repeat"]}'
                        if r.get("repeat") not in ("", "none") else "")
                     + f')</span>{note}</td></tr>')
        for e in rem_err:
            rows += (f'<tr><td style="padding:6px 0;font-family:{FONT};'
                     f'font-size:12px;color:{CRIMSON}">reminders.csv {e}</td></tr>')
        rem_html = (
            f'<tr><td style="padding:14px 18px;border-bottom:1px solid {LINE};'
            f'background:{INK}">'
            f'<div style="font-family:{FONT};font-size:11px;color:{MUTED};'
            f'letter-spacing:.06em">REMINDERS</div>'
            f'<table role="presentation" width="100%" cellpadding="0" '
            f'cellspacing="0" style="margin-top:4px">{rows}</table></td></tr>')

    tx = digest.get("tax")
    tax_html = ""
    if tx:
        rows_tx = (
            f'<tr><td style="font-family:{FONT};font-size:12.5px;color:{MUTED};'
            f'padding:2px 0">Short term net</td>'
            f'<td align="right" style="font-family:{MONO};font-size:13px;'
            f'color:{ARMED if tx["net_st"] >= 0 else CRIMSON};padding:2px 0">'
            f'{cur_sym}{tx["net_st"]:+,.0f}</td></tr>'
            f'<tr><td style="font-family:{FONT};font-size:12.5px;color:{MUTED};'
            f'padding:2px 0">Long term net</td>'
            f'<td align="right" style="font-family:{MONO};font-size:13px;'
            f'color:{ARMED if tx["net_lt"] >= 0 else CRIMSON};padding:2px 0">'
            f'{cur_sym}{tx["net_lt"]:+,.0f}</td></tr>'
            f'<tr><td style="font-family:{FONT};font-size:12.5px;color:{MUTED};'
            f'padding:2px 0">Tax if all realised today</td>'
            f'<td align="right" style="font-family:{MONO};font-size:13px;'
            f'color:{PAPER};padding:2px 0">{cur_sym}{tx["est_tax"]:,.0f}</td></tr>')
        extra = ""
        if tx["st_loss"] < 0 and tx["st_gain"] > 0:
            off = min(abs(tx["st_loss"]), tx["st_gain"])
            extra += (f'<div style="font-family:{FONT};font-size:12px;'
                      f'color:{PAPER};margin-top:8px">{cur_sym}{off:,.0f} of '
                      f'short-term gains could be offset by realising '
                      f'short-term losses, saving about '
                      f'{cur_sym}{off * STCG_RATE:,.0f}.</div>')
        for tk, left, gain, saving in tx["approaching"][:4]:
            extra += (f'<div style="font-family:{FONT};font-size:12px;'
                      f'color:{FIRED};margin-top:4px">{tk} turns long term in '
                      f'{left} days, worth about {cur_sym}{saving:,.0f}.</div>')
        if tx["no_date"]:
            extra += (f'<div style="font-family:{FONT};font-size:11px;'
                      f'color:{MUTED};margin-top:6px">{tx["no_date"]} holding(s) '
                      f'have no buy date and are excluded.</div>')
        tax_html = (
            f'<tr><td style="padding:14px 18px;border-bottom:1px solid {LINE}">'
            f'<div style="font-family:{FONT};font-size:11px;color:{MUTED};'
            f'letter-spacing:.06em">TAX POSITION ON UNREALISED P&amp;L</div>'
            f'<table width="100%" cellpadding="0" cellspacing="0" '
            f'style="margin-top:6px">{rows_tx}</table>{extra}'
            f'<div style="font-family:{FONT};font-size:11px;color:{MUTED};'
            f'margin-top:8px">Rates change each Budget and this ignores your '
            f'other income. Confirm with your CA.</div></td></tr>')

    t = (digest.get("totals") or {}).get("inr")
    totals_html = ""
    if t:
        tcol = ARMED if t["pl_abs"] >= 0 else CRIMSON
        totals_html = (
            f'<tr><td style="padding:14px 18px;background:{INK};'
            f'border-bottom:1px solid {LINE}">'
            f'<div style="font-family:{FONT};font-size:11px;color:{MUTED};'
            f'letter-spacing:.06em">ACROSS {t["count"]} HOLDINGS WITH COST RECORDED</div>'
            f'<div style="font-family:{MONO};font-size:18px;color:{PAPER};margin-top:4px">'
            f'{cur_sym}{t["current"]:,.0f} '
            f'<span style="color:{tcol};font-size:14px">'
            f'{t["pl_abs"]:+,.0f} ({t["pl_pct"]:+.2f}%)</span></div>'
            f'<div style="font-family:{FONT};font-size:11.5px;color:{MUTED};margin-top:2px">'
            f'invested {cur_sym}{t["invested"]:,.0f}</div></td></tr>')
    return f'''<!DOCTYPE html><html><body style="margin:0;padding:24px 12px;background:#0d0607">
<table role="presentation" width="100%" cellpadding="0" cellspacing="0"><tr><td align="center">
<table role="presentation" width="600" cellpadding="0" cellspacing="0"
  style="max-width:600px;background:{PANEL};border:1px solid {LINE};border-radius:12px;overflow:hidden">
  <tr><td style="background:{INK};padding:20px 18px">
    <div style="font-family:{FONT};font-size:22px;font-weight:700;color:{PAPER}">
      Portfolio <span style="color:{CRIMSON}">Digest</span></div>
    <div style="font-family:{FONT};font-size:13px;color:{MUTED};margin-top:2px">{digest["date"]}</div>
  </td></tr>
  {rem_html}
  {events_html}
  {totals_html}
  {tax_html}
  {rows}
  <tr><td style="padding:14px 18px;font-family:{FONT};font-size:11px;color:{MUTED}">
    Data: Yahoo Finance, best effort. Analyst coverage on smallcaps is thin;
    treat targets as context, not signals.
  </td></tr>
</table></td></tr></table>
</body></html>'''


BULLET = "\u2022"
# Telegram is a glance on a phone, not a report. Every section below is
# filtered, and a section that has nothing to say prints nothing at all. On a
# quiet day the whole message is four lines, which is the point: something
# arriving means something happened.
TELEGRAM_FULL_LIST = False    # True brings back the full holdings table
PRE_BLOCK_CHARS = 3000        # a <pre> block must fit inside one message

BIG_MOVE_PCT = 3.0            # a day move worth naming on percent alone
BIG_MOVE_RUPEES = 2000        # or on rupees alone, whatever the percent
GIVEBACK_PCT = 10.0           # how far below its own peak before a winner shows
GIVEBACK_MIN_GAIN = 20.0      # and only for positions still up this much
DEEP_LOSS_PCT = -25.0         # losses at least this deep
SIZE_WARN_PCT = 10.0          # one holding as a share of the whole portfolio
EARNINGS_SOON_DAYS = 7
WINNER_MIN_RUPEES = 5000      # below this a gain is not worth a line


def day_rupees(e):
    """What today's move was worth in money for this holding."""
    if not e.get("prev_close") or not e.get("qty") or not e.get("price"):
        return None
    return (e["price"] - e["prev_close"]) * e["qty"]


def days_until(date_str):
    if not date_str:
        return None
    for fmt in ("%Y-%m-%d", "%d-%m-%Y", "%d/%m/%Y", "%d %b %Y"):
        try:
            d = datetime.strptime(str(date_str).strip()[:10], fmt)
            return (d.date() - datetime.now(IST).date()).days
        except ValueError:
            continue
    return None


def inr_short(n):
    """Indian short form. 6,51,240 reads as 6.51 L on a phone screen."""
    if n is None:
        return "-"
    a = abs(n)
    if a >= 1e7:
        return f"\u20B9{n / 1e7:,.2f} Cr"
    if a >= 1e5:
        return f"\u20B9{n / 1e5:,.2f} L"
    return f"\u20B9{n:,.0f}"


def px(n):
    """Prices below 100 need paise, above 100 they are noise on a phone."""
    if n is None:
        return "-"
    return f"{n:,.2f}" if abs(n) < 100 else f"{n:,.0f}"


def tg_esc(s):
    return (str(s).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;"))


def _table(rows):
    return "<pre>" + "\n".join(tg_esc(r) for r in rows) + "</pre>"


def _head(title, sub=None):
    s = f"\u2501\u2501 <b>{title}</b> \u2501\u2501"
    return s + (f"\n<i>{sub}</i>" if sub else "")


def telegram_messages(digest):
    """Three messages instead of one.

    One message forces everything to compete for the same attention, and the
    old single message lost that fight so badly it had to be cut down to
    almost nothing. Splitting by decision type means each one can be dense
    without being noise, because you already know what you are reading
    before you open it: what happened today, what your positions look like,
    and what is coming.

    Every section is still filtered, and a section with nothing to say
    prints nothing. On a quiet day this is one short message, not three.
    """
    ents = [e for e in (digest.get("entries") or []) if e.get("price")]
    t = (digest.get("totals") or {}).get("inr") or {}
    out = []

    # ==================================================================
    # 1. TODAY
    # ==================================================================
    L = [f"\U0001F4CA <b>Portfolio</b>  {tg_esc(digest.get('date', ''))}", ""]
    if t:
        arrow = "\u25B2" if (t.get("pl_abs") or 0) >= 0 else "\u25BC"
        L.append(f"<b>{inr_short(t.get('current'))}</b>   {arrow} "
                 f"{inr_short(t.get('pl_abs'))} ({t.get('pl_pct', 0):+.2f}%)")
        L.append(f"<i>invested {inr_short(t.get('invested'))} across "
                 f"{t.get('count', 0)} holdings</i>")

    day_moves = [(e, day_rupees(e)) for e in ents]
    day_moves = [(e, r) for e, r in day_moves if r is not None]
    day_abs = sum(r for _, r in day_moves)
    up_n = sum(1 for e in ents if (e.get("day_pct") or 0) > 0)
    down_n = sum(1 for e in ents if (e.get("day_pct") or 0) < 0)
    if day_moves:
        L.append(f"Today: <b>{inr_short(day_abs)}</b>  "
                 f"<i>({up_n} up, {down_n} down)</i>")

    # How the portfolio has travelled, straight off the saved history.
    for line in _trend_lines(digest.get("history") or []):
        L.append(line)
    L.append("")
    quiet_from = len(L)

    ev = rank_events(digest.get("events") or [])
    crossed = [x for x in ev if x["kind"] in CROSSED]
    close = [x for x in ev if x["kind"] in APPROACHING]
    if crossed:
        L.append(_head("CHANGES"))
        mark = {"newlow": "\U0001F53B", "breakeven": "\u2705",
                "ath": "\U0001F680", "recovering": "\u2197"}
        for x in crossed:
            L.append(f"{mark.get(x['kind'], BULLET)} <b>{tg_esc(x['ticker'])}</b>  "
                     f"{tg_esc(x['text'])}")
        L.append("")
    if close:
        names = ", ".join(f"{tg_esc(x['ticker'])} {x.get('gap', 0):.1f}%"
                          for x in close[:8])
        L.append(f"\U0001F440 <i>close to a line: {names}"
                 + (f" and {len(close) - 8} more" if len(close) > 8 else "")
                 + "</i>")
        L.append("")

    fired = [(e, b) for e in ents for b in e.get("bands", [])
             if b.get("status") == "fired"]
    if fired:
        L.append(_head("ALERTS FIRED"))
        for e, b in fired[:10]:
            L.append(f"\U0001F514 <b>{tg_esc(e['ticker'])}</b> {b['direction']} "
                     f"{px(b['target'])}, now {px(e['price'])}")
        L.append("")

    # Armed bands sitting just short of their trigger. Knowing something is
    # about to fire is worth more than being told after it has.
    nearly = []
    for e in ents:
        for b in e.get("bands", []):
            if b.get("status") == "armed" and abs(b.get("away_pct", 99)) <= 2.0:
                nearly.append((e, b))
    nearly.sort(key=lambda x: abs(x[1]["away_pct"]))
    if nearly:
        names = ", ".join(f"{tg_esc(e['ticker'])} {abs(b['away_pct']):.1f}%"
                          for e, b in nearly[:6])
        L.append(f"\u23F3 <i>bands about to trigger: {names}</i>")
        L.append("")

    # Percent alone is the wrong filter. A 5% move on a 1,500 rupee holding
    # is 75 rupees. A 2% move on an 80,000 rupee holding is 1,600. A stock
    # qualifies on either measure and the table sorts by money.
    moved = [(e, e["day_pct"], r) for e, r in day_moves
             if e.get("day_pct") is not None
             and (abs(e["day_pct"]) >= BIG_MOVE_PCT or abs(r) >= BIG_MOVE_RUPEES)]
    moved.sort(key=lambda x: -abs(x[2]))
    if moved:
        L.append(_head("MOVED TODAY",
                       f"{BIG_MOVE_PCT:.0f}% or {inr_short(BIG_MOVE_RUPEES)}, "
                       f"whichever comes first"))
        L.append(_table(
            f"{'\U0001F7E2' if d > 0 else '\U0001F534'} {e['ticker']:<11.11}"
            f"{d:>+6.1f}%{r:>+9,.0f}" for e, d, r in moved[:14]))
        if len(moved) > 14:
            L.append(f"<i>and {len(moved) - 14} more</i>")
        L.append("")
    elif day_moves:
        # Nothing cleared the bar, so name what nudged the total anyway.
        ranked = sorted(day_moves, key=lambda x: -x[1])
        picks = [x for x in (ranked[:2] + ranked[-2:]) if abs(x[1]) > 1]
        if picks:
            L.append("<i>quiet day. Biggest contributors: "
                     + ", ".join(f"{tg_esc(e['ticker'])} {r:+,.0f}"
                                 for e, r in picks) + "</i>")
            L.append("")

    if len(L) <= quiet_from:
        L.append("\u2705 <i>Nothing crossed a threshold today. No big moves, "
                 "no position changes, no alerts fired.</i>")
    out.append("\n".join(L).strip())

    # ==================================================================
    # 2. POSITIONS
    # ==================================================================
    L = ["\U0001F4C8 <b>Positions</b>", ""]
    body_from = len(L)

    # The closest this system will come to a sell prompt, and it is still
    # only a fact: a position that was up more is now up less, and this is
    # how much has gone. Peak means the highest price seen since tracking
    # began, not an all-time high.
    giveback = []
    for e in ents:
        peak, price, pl = e.get("peak"), e.get("price"), e.get("pl_pct")
        if not peak or not price or pl is None or pl < GIVEBACK_MIN_GAIN:
            continue
        off = (price / peak - 1) * 100
        if off <= -GIVEBACK_PCT:
            giveback.append((e, off, (peak - price) * (e.get("qty") or 0)))
    giveback.sort(key=lambda x: -x[2])
    if giveback:
        L.append(_head("GIVING BACK GAINS",
                       f"{GIVEBACK_PCT:.0f}%+ below their own peak, "
                       f"still in profit"))
        L.append(_table(
            f"{e['ticker']:<11.11}{off:>+6.1f}% off{-lost:>+10,.0f}"
            for e, off, lost in giveback[:8]))
        L.append("")

    # A gain only earns a line once it is worth real money. Otherwise this
    # section fires every single day on trivial amounts and stops being read.
    winners = sorted((e for e in ents
                      if (e.get("pl_abs") or 0) >= WINNER_MIN_RUPEES),
                     key=lambda e: -e["pl_abs"])
    if winners:
        L.append(_head("CARRYING THE PORTFOLIO", "largest gains in rupees"))
        L.append(_table(
            f"{e['ticker']:<11.11}{e['pl_pct']:>+6.1f}%{e['pl_abs']:>+11,.0f}"
            for e in winners[:6]))
        L.append("")

    # Capital that has been committed over a year and gone nowhere. Not a
    # sell list. It answers "where is my money sitting idle", which is a
    # question about the portfolio, not a view on any of the shares.
    dead = dead_money(ents)
    if dead:
        idle = sum(d["value"] for d in dead)
        L.append(_head("HELD OVER A YEAR, GONE NOWHERE",
                       f"{inr_short(idle)} across {len(dead)}, "
                       f"under {DEAD_MONEY_RETURN:.0f}% total return"))
        rows = []
        for d in dead[:8]:
            ann = f"{d['annual']:>+6.1f}/yr" if d["annual"] is not None else "      -"
            rows.append(f"{d['ticker']:<11.11}{inr_short(d['value']):>10}"
                        f"{d['pl_pct']:>+7.1f}%{ann}")
        L.append(_table(rows))
        approx = [d for d in dead if d["basis"] == "lt_qty"]
        if approx:
            L.append(f"<i>{len(approx)} dated from lt_qty only, so over a "
                     f"year is all that is known. Fill buy_date for real "
                     f"holding periods.</i>")
        L.append("")

    losers = [e for e in ents if (e.get("pl_pct") is not None
                                  and e["pl_pct"] <= DEEP_LOSS_PCT)]
    losers.sort(key=lambda e: e.get("pl_abs") or 0)
    if losers:
        L.append(_head("DEEPEST LOSSES", "ranked by rupees, not by percent"))
        L.append(_table(
            f"{e['ticker']:<11.11}{e['pl_pct']:>+6.1f}%{(e.get('pl_abs') or 0):>+11,.0f}"
            for e in losers[:8]))
        L.append("")

    # The whole reason this system exists: no broker shows a family its
    # combined position, so nobody can see which account is doing the work.
    acc = per_account_tax(digest.get("entries") or [])
    if len(acc) > 1:
        rows = []
        for who, a in sorted(acc.items(), key=lambda x: -x[1]["value"]):
            net = a.get("lt_net", 0) + a.get("st_net", 0)
            base = a["value"] - net
            pct_s = f"{net / base * 100:>+6.1f}%" if base else "      -"
            rows.append(f"{who:<10.10}{inr_short(a['value']):>11}{pct_s}")
        L.append(_head("BY ACCOUNT", "value and unrealised P&L"))
        L.append(_table(rows))
        L.append("")

    sect = {}
    for e in ents:
        if e.get("sector") and e.get("current"):
            s = sect.setdefault(e["sector"][:14], {"v": 0.0, "p": 0.0})
            s["v"] += e["current"]
            s["p"] += e.get("pl_abs") or 0
    if len(sect) > 2 and t.get("current"):
        top = sorted(sect.items(), key=lambda x: -x[1]["v"])[:6]
        L.append(_head("BY SECTOR", "share of portfolio and P&L"))
        L.append(_table(
            f"{k:<15.15}{v['v'] / t['current'] * 100:>5.1f}%{v['p']:>+11,.0f}"
            for k, v in top))
        L.append("")

    if t.get("current"):
        big = [(e, e["price"] * e["qty"] / t["current"] * 100)
               for e in ents if e.get("qty")]
        big = [x for x in big if x[1] >= SIZE_WARN_PCT]
        big.sort(key=lambda x: -x[1])
        if big:
            L.append("\u2696 <b>Position size:</b> "
                     + ", ".join(f"{tg_esc(e['ticker'])} {s:.1f}%"
                                 for e, s in big[:5])
                     + " of the portfolio")
            L.append("")

    if len(L) > body_from:
        out.append("\n".join(L).strip())

    # ==================================================================
    # 3. AHEAD
    # ==================================================================
    L = ["\U0001F5D3 <b>Ahead</b>", ""]
    body_from = len(L)

    rem = digest.get("reminders") or []
    if rem:
        L.append(_head("REMINDERS", "set by you"))
        for r in rem[:10]:
            face = "\U0001F534" if r["days"] < 0 else (
                "\U0001F7E1" if r["days"] <= 1 else "\U0001F535")
            tick = f" [{tg_esc(r['ticker'])}]" if r.get("ticker") else ""
            note = f"\n     <i>{tg_esc(r['note'])}</i>" if r.get("note") else ""
            L.append(f"{face} <b>{tg_esc(r['label'])}</b>{tick} "
                     f"{reminder_phrase(r)} ({r['date']}){note}")
        if len(rem) > 10:
            L.append(f"<i>and {len(rem) - 10} more</i>")
        L.append("")
    for err in (digest.get("reminder_errors") or [])[:4]:
        L.append(f"\u26A0 <i>reminders.csv {tg_esc(err)}</i>")
    if digest.get("reminder_errors"):
        L.append("")

    soon = [(e, days_until(e.get("earnings"))) for e in ents]
    soon = [(e, d) for e, d in soon if d is not None and 0 <= d <= EARNINGS_SOON_DAYS]
    soon.sort(key=lambda x: x[1])
    if soon:
        L.append(_head("RESULTS DUE", f"next {EARNINGS_SOON_DAYS} days"))
        L.append(_table(f"{e['ticker']:<11.11}{e['earnings']:>12}"
                        f"{d:>4}d" for e, d in soon[:10]))
        L.append("")

    # Tax only earns a line when there is something to do about it.
    tx = digest.get("tax") or {}
    approaching = (tx.get("approaching") or [])[:4]
    offset = 0
    if tx.get("st_loss", 0) < 0 and tx.get("st_gain", 0) > 0:
        offset = min(abs(tx["st_loss"]), tx["st_gain"])
    if approaching or offset:
        L.append(_head("TAX", "only what is actionable"))
        for tk, left, gain, saving in approaching:
            L.append(f"\U0001F4B0 <b>{tg_esc(tk)}</b> turns long term in "
                     f"<b>{left} days</b>, worth about {inr_short(saving)}")
        if offset:
            L.append(f"\U0001F4B0 {inr_short(offset)} of short term gains could "
                     f"be offset by realising short term losses, saving about "
                     f"{inr_short(offset * STCG_RATE)}")
        L.append("")

    # The allowance nobody counts, because it belongs to the PAN and no
    # broker can see across accounts. Unused on 31 March means gone.
    # The allowance is only actionable if there is a long-term gain to shelter,
    # or if the financial year is running out. Printing "nothing used" every
    # day for twelve months trains you to skip the section.
    year_end_soon = datetime.now(IST).month in (1, 2, 3)
    have_lt_gain = any(a.get("lt_net", 0) > 0 for a in acc.values())
    if acc and (have_lt_gain or year_end_soon):
        rows = []
        for who, a in sorted(acc.items(), key=lambda x: -x[1].get("exempt_left", 0)):
            left = a.get("exempt_left")
            if left:
                rows.append(f"{who:<10.10}{inr_short(left):>12} free")
        if rows:
            L.append(_head("LTCG ALLOWANCE LEFT",
                           "per PAN this financial year, expires 31 March"))
            L.append(_table(rows[:6]))
            L.append("")

    stretched = [e for e in ents
                 if e.get("target_upside_pct") is not None
                 and e["target_upside_pct"] < 0]
    stretched.sort(key=lambda e: e["target_upside_pct"])
    if stretched:
        L.append(_head("TRADING ABOVE THE ANALYST MEAN",
                       "context only, targets follow price as often as lead it"))
        L.append(_table(
            f"{e['ticker']:<11.11}{px(e['price']):>9}{e['target_upside_pct']:>+7.1f}%"
            for e in stretched[:8]))
        L.append("")

    dead = [e for e in (digest.get("entries") or []) if not e.get("price")]
    no_date = sum(1 for e in ents if not e.get("buy_date"))
    warn = []
    if dead:
        warn.append(f"{len(dead)} returned no price: "
                    f"{tg_esc(', '.join(e['ticker'] for e in dead[:6]))}")
    if no_date:
        warn.append(f"{no_date} have no buy_date, so they are missing from "
                    f"every tax figure above")
    if warn:
        L.append("\u26A0 <i>" + ". ".join(warn) + "</i>")
        L.append("")

    L.append("<i>Yahoo Finance, best effort. Analyst coverage on smallcaps is "
             "thin, so treat targets as context. Nothing here is a "
             "recommendation to buy, sell or hold.</i>")
    if len(L) > body_from + 1:
        out.append("\n".join(L).strip())
    else:
        out[-1] += ("\n\n<i>Yahoo Finance, best effort. Nothing here is a "
                    "recommendation to buy, sell or hold.</i>")

    return [m for m in out if m.strip()]


def _trend_lines(rows):
    """Week and month change, read off portfolio_history.csv."""
    if len(rows) < 2:
        return []
    try:
        now_v = float(rows[-1]["current"])
    except (ValueError, KeyError, TypeError):
        return []
    bits = []
    for back, label in ((7, "1w"), (30, "1m")):
        target = (datetime.now(IST) - timedelta(days=back)).strftime("%Y-%m-%d")
        older = [r for r in rows if r.get("date", "") <= target]
        if not older:
            continue
        try:
            was = float(older[-1]["current"])
        except (ValueError, KeyError, TypeError):
            continue
        if was:
            bits.append(f"{label} {(now_v / was - 1) * 100:+.1f}%")
    return [f"<i>{' \u00B7 '.join(bits)}</i>"] if bits else []


def send_email(subject, text_body, html_body=None):
    from email.mime.multipart import MIMEMultipart
    user = os.environ.get("SMTP_USER")
    password = os.environ.get("SMTP_APP_PASSWORD")
    to_addr = os.environ.get("ALERT_EMAIL_TO", user)
    if not user or not password:
        print("SMTP not configured, skipping email")
        return
    msg = MIMEMultipart("alternative")
    msg["Subject"] = subject
    msg["From"] = user
    msg["To"] = to_addr
    msg.attach(MIMEText(text_body, "plain", "utf-8"))
    if html_body:
        msg.attach(MIMEText(html_body, "html", "utf-8"))
    with smtplib.SMTP_SSL("smtp.gmail.com", 465, timeout=30) as server:
        server.login(user, password)
        server.sendmail(user, [to_addr], msg.as_string())
    print(f"digest emailed to {to_addr}")


def send_telegram(text, parse_mode=None):
    token = os.environ.get("TELEGRAM_BOT_TOKEN")
    chat_id = os.environ.get("TELEGRAM_CHAT_ID")
    if not token or not chat_id:
        return
    # Telegram caps messages at 4096 chars; split on stock boundaries if needed
    chunks, cur_chunk = [], ""
    paras = text.split("\n\n")
    for para in paras:
        if len(cur_chunk) + len(para) + 2 > 3900:
            chunks.append(cur_chunk)
            cur_chunk = para
        else:
            cur_chunk = (cur_chunk + "\n\n" + para) if cur_chunk else para
    if cur_chunk:
        chunks.append(cur_chunk)
    url = f"https://api.telegram.org/bot{token}/sendMessage"
    for chunk in chunks:
        payload = {"chat_id": chat_id, "text": chunk}
        if parse_mode:
            payload["parse_mode"] = parse_mode
        data = urllib.parse.urlencode(payload).encode()
        try:
            with urllib.request.urlopen(urllib.request.Request(url, data=data),
                                        timeout=30) as r:
                r.read()
        except Exception as e:  # noqa: BLE001
            print(f"WARNING: telegram digest send failed: {e}")
            return
    print("digest sent to telegram")


if __name__ == "__main__":
    digest = build()
    text = format_text(digest)
    html = format_html(digest)
    print(text)
    send_email(f"Portfolio digest {digest['date']}", text, html)
    for msg in telegram_messages(digest):
        send_telegram(msg, parse_mode="HTML")

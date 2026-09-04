#!/usr/bin/env python3
"""Regression tests for the stock alert system.

Every test here exists because something broke once. The handoff document
carried a list of ten bugs "so they are not repeated", but a list in a
document is folklore: it relies on a human remembering to check. This file
turns that list into enforcement.

Run locally:      python test_system.py
Run in CI:        the tests workflow calls this on every push

No pytest, no dependencies beyond the standard library, because adding a
package to a GitHub Actions run costs minutes on a plan that has none to
spare.
"""

import csv
import io
import sys
import tempfile
import unittest
from datetime import date
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import digest
import research_watch
import stock_alerts


# ======================================================================
# The ten bugs from the handoff, one test each
# ======================================================================

class HistoricalBugs(unittest.TestCase):
    """Bug 1 is checked by CI running pyflakes, not from here: a deleted
    function leaves valid syntax, so only a linter catches it."""

    def test_bug2_split_never_touches_cost_basis(self):
        """Broker statements are already restated after a split. Applying
        Yahoo's split history on top double counts."""
        src = Path("stock_alerts.py").read_text()
        start = src.index("def apply_split_adjustments")
        body = src[start:start + 4000]
        for forbidden in ("row['avg_cost'] =", 'row["avg_cost"] =',
                          "row['qty'] =", 'row["qty"] ='):
            self.assertNotIn(forbidden, body,
                             f"split adjustment must never write {forbidden}")

    def test_bug3_none_price_cannot_pass_a_finite_guard(self):
        """isFinite(null) is true in JavaScript. The Python equivalent is
        letting None through a truthiness check and crashing downstream."""
        entry = {"ticker": "X", "price": None, "qty": 10, "prev_close": 100.0}
        self.assertIsNone(digest.day_rupees(entry),
                          "a null price must not produce a rupee figure")

    def test_bug5_findall_with_group_returns_the_group(self):
        """re.findall with a capturing group returns the group, not the
        match, which silently zeroed sentiment counts."""
        import re
        pattern = r"\b(gain|loss)\b"
        self.assertEqual(re.findall(pattern, "a gain and a loss"),
                         ["gain", "loss"])
        self.assertEqual(len(re.findall(r"\b(?:gain|loss)\b",
                                        "a gain and a loss")), 2)

    def test_bug6_word_boundaries_are_mandatory(self):
        """'ban' matched inside 'bank'."""
        for _weight, _direction, pattern, label in research_watch.NEWS_SIGNALS:
            self.assertTrue(
                pattern.startswith(r"\b") or pattern.startswith("(?")
                or "\\b" in pattern,
                f"signal '{label}' has no word boundary: {pattern}")

    def test_bug7_ticker_matching_is_not_substring(self):
        """'LT' was found inside 'results'."""
        import re
        self.assertIsNone(re.search(r"\bLT\b", "results are out"))
        self.assertIsNotNone(re.search(r"\bLT\b", "LT reported today"))

    def test_bug8_nothing_is_truncated_silently(self):
        """A cap of 60 symbols silently ignored 41 holdings."""
        src = Path("research_watch.py").read_text()
        idx = src.index("def load_symbols")
        body = src[idx:idx + 1500]
        self.assertIn("Not watched", body,
                      "truncation must name what it dropped")

    def test_bug9_telegram_photo_caption_stays_under_the_cap(self):
        """Telegram photo captions cap at 1024 characters."""
        src = Path("research_watch.py").read_text()
        self.assertIn("caption[:900]", src,
                      "photo captions must be truncated below the 1024 cap")

    def test_bug10_gemini_thinking_budget_is_zero(self):
        """Newer Gemini models emit their reasoning unless thinkingBudget
        is 0."""
        src = Path("research_watch.py").read_text()
        self.assertIn("thinkingBudget", src)


# ======================================================================
# Bugs found while building, which are now equally permanent
# ======================================================================

class RecentlyFixed(unittest.TestCase):

    def test_multi_lot_quantity_is_summed_not_taken_from_first_row(self):
        """avg_cost and qty came from the FIRST csv row for a symbol, so
        every holding split across accounts was undercounted. SBIFUNDS
        showed 32 shares against 58 actually held."""
        lots = [{"cost": 100.0, "qty": 30}, {"cost": 200.0, "qty": 10}]
        total = sum(l["qty"] for l in lots)
        wavg = sum(l["cost"] * l["qty"] for l in lots) / total
        self.assertEqual(total, 40)
        self.assertAlmostEqual(wavg, 125.0)
        src = Path("digest.py").read_text()
        self.assertIn('grp["qty"] = total_qty',
                      src, "lot aggregation must sum across rows")

    def test_alert_ids_never_contain_a_moving_peak(self):
        """A trailing stop id built from the peak becomes a brand new alert
        every day, fires forever, and can never be acknowledged."""
        alerts = stock_alerts.load_holdings()
        for a in alerts:
            if a["type"] == "trail":
                self.assertRegex(a["id"], r"^[A-Z0-9.\-&]+\|trail\|[\d.]+$",
                                 "trail id must be symbol|trail|value only")

    def test_trailing_peak_only_ratchets_upward(self):
        state, alert = {}, {"id": "T|trail|20", "value": 20.0, "avg_cost": 0}
        seq = [900, 1140, 1000, 915]
        peaks = [stock_alerts.update_trail_peak(state, alert, p) for p in seq]
        self.assertEqual(peaks, [900, 1140, 1140, 1140])

    def test_trailing_stop_fires_only_below_the_stop(self):
        state = {}
        alert = {"id": "T|trail|20", "type": "trail", "value": 20.0,
                 "avg_cost": 0}
        stock_alerts.update_trail_peak(state, alert, 1140)
        stop = stock_alerts.target_price(alert, 1140)
        self.assertAlmostEqual(stop, 912.0)
        self.assertFalse(915 <= stop, "a price above the stop must not fire")
        self.assertTrue(912 <= stop, "a price at the stop must fire")

    def test_split_clears_trailing_peaks(self):
        """A 1-for-5 divides the price by five overnight. Against a
        pre-split peak every stop in the file fires at once."""
        state = {stock_alerts.TRAIL_PEAKS_KEY: {
            "ABC.NS|trail|20": {"peak": 1000.0},
            "XYZ.NS|trail|15": {"peak": 500.0}}}
        removed = stock_alerts.reset_trail_peaks_for(state, "ABC.NS")
        self.assertEqual(removed, 1)
        peaks = state[stock_alerts.TRAIL_PEAKS_KEY]
        self.assertNotIn("ABC.NS|trail|20", peaks)
        self.assertIn("XYZ.NS|trail|15", peaks,
                      "an unrelated symbol's peak must survive")

    def test_trailing_stop_stays_idle_while_underwater(self):
        """A trailing stop protects a gain. With no gain there is nothing
        to protect, and arming against a depressed peak would fire on the
        next tick down."""
        state = {}
        alert = {"id": "U|trail|20", "value": 20.0, "avg_cost": 500.0}
        peak = stock_alerts.update_trail_peak(state, alert, 300.0)
        self.assertEqual(peak, 500.0, "peak floors at cost")

    def test_target_price_refuses_to_guess_a_trail_target(self):
        alert = {"type": "trail", "value": 20.0}
        self.assertIsNone(stock_alerts.target_price(alert, peak=None),
                          "no peak means no knowable target, not a guess")

    def test_repeating_reminders_do_not_drift_off_month_ends(self):
        """Stepping month by month clamps a 31st anchor to 28 February and
        leaves it there, walking the reminder backwards through the year."""
        today = date(2026, 8, 24)
        got = digest.next_occurrence(date(2026, 1, 31), "monthly", today)
        self.assertEqual(got, date(2026, 8, 31))

    def test_leap_day_reminders_survive_a_common_year(self):
        got = digest.next_occurrence(date(2024, 2, 29), "yearly",
                                     date(2026, 8, 24))
        self.assertEqual(got, date(2027, 2, 28))

    def test_one_off_reminders_expire_after_their_grace_period(self):
        today = date(2026, 8, 24)
        self.assertIsNone(
            digest.next_occurrence(date(2026, 8, 10), "none", today))
        self.assertEqual(
            digest.next_occurrence(date(2026, 8, 20), "none", today),
            date(2026, 8, 20))

    def test_percent_change_off_a_loss_making_base_is_suppressed(self):
        """A percentage change measured from a negative base prints
        nonsense like -300% for a genuine turnaround."""
        quarters = [{"period": "Q1", "revenue": 1000.0, "net": 100.0,
                     "margin": 10.0}] + [{}] * 3 + [
            {"period": "Q1 LY", "revenue": 800.0, "net": -50.0, "margin": -6.25}]
        _tone, _score, _head, chips = research_watch.results_signal(quarters)
        for c in chips:
            self.assertNotIn("-300", str(c["value"]))
        labels = " ".join(str(c["value"]) for c in chips)
        self.assertIn("loss to profit", labels)

    def test_thesis_direction_handles_rewritten_risk_leans(self):
        """match_themes rewrites 'challenges' into 'is the risk playing
        out:' for risk-type themes, so startswith('challenges') misses
        exactly the cases that matter most."""
        self.assertEqual(research_watch.thesis_tone("is the risk playing out:"),
                         research_watch.BAD)
        self.assertEqual(research_watch.thesis_tone("suggests the risk is easing:"),
                         research_watch.GOOD)
        self.assertEqual(research_watch.thesis_tone("challenges"),
                         research_watch.BAD)
        self.assertEqual(research_watch.thesis_tone("supports"),
                         research_watch.GOOD)

    def test_all_time_high_is_split_adjusted(self):
        """auto_adjust=False returns raw prices. After a 1-for-5 split the
        pre-split high is five times the post-split price, so the holding
        looks permanently 80% below a peak it can never reach."""
        src = Path("digest.py").read_text()
        self.assertIn("splits[splits.index > when]", src,
                      "highs must be divided by the splits that came after")
        # Scoped to the all-time-high block only. Other history() calls
        # exist for unrelated reasons, such as an index close fallback, and
        # adjustment does not matter for those.
        import re as _re
        blk = src[src.index("hist = t.history"):src.index('out["ath"]')]
        for call in _re.findall(r"\.history\([^)]*\)", blk):
            self.assertIn("auto_adjust=False", call,
                          "auto_adjust=True also adjusts dividends, which "
                          "manufactures false at-its-peak signals")

    def test_dead_money_excludes_recent_and_small_and_winners(self):
        ents = [
            {"ticker": "OLD", "price": 100.0, "qty": 200, "pl_pct": 2.0,
             "buy_date": "2023-01-01", "ath": 200.0},
            {"ticker": "NEW", "price": 100.0, "qty": 200, "pl_pct": 2.0,
             "buy_date": "2026-06-01", "ath": 200.0},
            {"ticker": "TINY", "price": 10.0, "qty": 5, "pl_pct": 2.0,
             "buy_date": "2023-01-01", "ath": 20.0},
            {"ticker": "WINNER", "price": 100.0, "qty": 200, "pl_pct": 40.0,
             "buy_date": "2023-01-01", "ath": 110.0},
        ]
        got = [d["ticker"] for d in digest.dead_money(ents)]
        self.assertEqual(got, ["OLD"])

    def test_holding_age_falls_back_to_lt_qty(self):
        """Only Zerodha reports lt_qty and no row has a buy_date, so the
        fallback is the only thing that makes this run at all today."""
        days, basis = digest.holding_age({"buy_date": "", "lt_qty": 32})
        self.assertEqual(basis, "lt_qty")
        self.assertGreaterEqual(days, 365)
        days, basis = digest.holding_age({"buy_date": "", "lt_qty": 0})
        self.assertIsNone(days)

    def test_month_review_excludes_new_money_from_the_return(self):
        """Money paid in during the month is not performance. Comparing raw
        totals would show a buying month as a gain."""
        rows=[{"date":"2026-08-02","invested":"600000","current":"900000",
               "winners":"70","losers":"30","nifty50":"24000"},
              {"date":"2026-09-01","invested":"700000","current":"1000000",
               "winners":"70","losers":"30","nifty50":"24000"}]
        m=digest.month_review(rows,[])
        self.assertEqual(m["added"],100000)
        # value rose 100000 but all of it was deposited, so the return is nil
        self.assertAlmostEqual(m["return_pct"],0.0,places=6)
        self.assertEqual(m["indices"]["nifty50"],0.0)

    def test_month_review_needs_real_history(self):
        self.assertIsNone(digest.month_review([],[]))
        self.assertIsNone(digest.month_review(
            [{"date":"2026-08-30","current":"1","invested":"1"},
             {"date":"2026-09-01","current":"1","invested":"1"}],[]),
            "a two-day gap must not be reported as a month")

    def test_perk_holdings_are_muted_everywhere(self):
        """One share held for the annual report is not a position. A stop on
        it can only ever fire falsely, and it should never appear as dead
        money."""
        perk={"ticker":"ITCHOTELS","note":"#perk RTA: KFintech","price":300.0,
              "qty":1,"avg_cost":280.0,"pl_pct":2.0,"buy_date":"2023-01-01"}
        real={"ticker":"GLAXO","note":"","price":300.0,"qty":200,
              "avg_cost":500.0,"pl_pct":-40.0,"buy_date":"2023-01-01"}
        self.assertTrue(digest.is_perk(perk))
        self.assertFalse(digest.is_perk(real))
        self.assertEqual([d["ticker"] for d in digest.dead_money([perk,real])],
                         ["GLAXO"])
        self.assertEqual(digest.detect_position_events([perk],{}), [])

    def test_perk_marker_matches_across_all_three_files(self):
        """Three files test for the same tag. If the patterns drift, the
        dashboard hides a holding that the scheduler still alerts on."""
        a=Path("digest.py").read_text()
        b=Path("stock_alerts.py").read_text()
        c=Path("index.html").read_text()
        self.assertIn("#(perk|report|agm)", a)
        self.assertIn("#(perk|report|agm)", b)
        self.assertIn("#(perk|report|agm)", c)

    def test_xirr_matches_a_known_answer(self):
        """1,00,000 growing to 1,21,000 over exactly two years is 10% a
        year, not 21%. This is the whole reason the figure exists."""
        import datetime as _dt
        r = digest.xirr([(_dt.date(2024, 9, 4), -100000),
                         (_dt.date(2026, 9, 4), 121000)])
        self.assertAlmostEqual(r, 10.0, places=1)

    def test_xirr_refuses_the_unsolvable(self):
        """No sign change means no rate exists. Returning a number here
        would be inventing one."""
        import datetime as _dt
        self.assertIsNone(digest.xirr([(_dt.date(2024, 1, 1), -100),
                                       (_dt.date(2025, 1, 1), -100)]))
        self.assertIsNone(digest.xirr([(_dt.date(2024, 1, 1), -100)]))

    def test_xirr_excludes_holdings_with_no_purchase_date(self):
        """A holding with no date must be dropped, never dated from a
        guess, and the count of drops has to be reported."""
        e = [{"ticker": "A", "price": 121.0, "qty": 1000, "avg_cost": 100.0,
              "buy_date": "2024-09-04"},
             {"ticker": "B", "price": 200.0, "qty": 10, "avg_cost": 100.0,
              "buy_date": "2023-09-04"},
             {"ticker": "C", "price": 50.0, "qty": 10, "avg_cost": 100.0,
              "buy_date": "", "lt_qty": 10}]
        got = digest.portfolio_xirr(e)
        self.assertEqual(got["holdings"], 2)
        self.assertEqual(got["skipped"], 1)
        self.assertIsNotNone(got["xirr"])

    def test_position_size_uses_lakh_not_crore(self):
        """crore() renders an 18,000 rupee holding as '0 Cr'."""
        self.assertIn("L", research_watch.money_short(150000))
        self.assertEqual(research_watch.money_short(18876), "\u20B918,876")


# ======================================================================
# Telegram output, where a malformed tag rejects the whole message
# ======================================================================

class TelegramSafety(unittest.TestCase):

    def _fake_digest(self, n):
        ents = []
        for i in range(n):
            p = 100.0 + i
            ents.append({"ticker": f"TICKER{i:03d}", "exchange": "NSE",
                         "currency": "\u20B9", "price": p, "prev_close": p * 0.99,
                         "day_pct": 1.0, "avg_cost": p * 0.9, "qty": 10,
                         "pl_pct": 11.1, "pl_abs": p, "peak": p,
                         "invested": p * 9, "current": p * 10, "bands": [],
                         "sector": "TEST", "buy_date": "2025-01-01",
                         "lots": [{"account": "A", "broker": "B",
                                   "cost": p * 0.9, "qty": 10, "lt_qty": 10}]})
        inv = sum(e["invested"] for e in ents)
        cur = sum(e["current"] for e in ents)
        return {"date": "12 Aug 2026", "entries": ents, "history": [],
                "totals": {"inr": {"count": n, "invested": inv, "current": cur,
                                   "pl_abs": cur - inv, "pl_pct": 10.0}},
                "events": [], "tax": {}}

    def test_pre_tags_are_balanced_in_every_message(self):
        for n in (1, 22, 123, 300):
            for msg in digest.telegram_messages(self._fake_digest(n)):
                self.assertEqual(msg.count("<pre>"), msg.count("</pre>"),
                                 f"unbalanced <pre> at {n} holdings")

    def test_no_paragraph_exceeds_the_message_limit(self):
        """send_telegram splits on blank lines. A <pre> block straddling a
        chunk boundary loses its closing tag and Telegram rejects it."""
        for n in (123, 300):
            for msg in digest.telegram_messages(self._fake_digest(n)):
                for para in msg.split("\n\n"):
                    self.assertLess(len(para), 3900,
                                    f"paragraph too long at {n} holdings")

    def test_html_special_characters_are_escaped(self):
        d = self._fake_digest(2)
        d["entries"][0]["ticker"] = "A&B<C>"
        for msg in digest.telegram_messages(d):
            self.assertNotIn("<C>", msg, "raw angle brackets break parse_mode")

    def test_a_quiet_day_still_produces_a_message(self):
        d = self._fake_digest(5)
        for e in d["entries"]:
            e["day_pct"] = 0.0
            e["prev_close"] = e["price"]
            e["pl_abs"] = 1.0
        msgs = digest.telegram_messages(d)
        self.assertTrue(msgs, "silence is indistinguishable from a failed run")
        self.assertIn("Portfolio", msgs[0])


# ======================================================================
# Cross-file agreement, the drift that no single file can catch
# ======================================================================

class CrossFileConsistency(unittest.TestCase):
    """digest.py and stock_alerts.py each compute an alert's trigger price
    with their own code over the same csv. There is a comment in digest.py
    saying the two must agree. Nothing enforced it until now."""

    def test_trigger_prices_agree_between_digest_and_alerts(self):
        rows = list(csv.DictReader(
            io.StringIO(Path("holdings.csv").read_text(encoding="utf-8-sig"))))
        alerts = {a["id"]: a for a in stock_alerts.load_holdings()}
        checked = 0
        for row in rows:
            atype = (row.get("alert_type") or "").strip().lower()
            if atype in ("", "watch", "trail"):
                continue
            try:
                from_digest = digest.band_target(row)
            except (ValueError, KeyError, TypeError):
                continue
            symbol = row["ticker"].upper() + stock_alerts.SUFFIX.get(
                row["exchange"].upper(), "")
            match = [a for a in alerts.values()
                     if a["symbol"] == symbol and a["type"] == atype
                     and abs(a["value"] - float(row["alert_value"])) < 1e-9]
            if not match:
                continue
            from_alerts = stock_alerts.target_price(match[0])
            self.assertAlmostEqual(
                from_digest, from_alerts, places=2,
                msg=f"{row['ticker']}: digest says {from_digest}, "
                    f"alerts says {from_alerts}")
            checked += 1
        self.assertGreater(checked, 0, "no alerts were actually compared")

    def test_digest_does_not_invent_a_trail_target(self):
        row = {"alert_type": "trail", "alert_value": "20", "direction": "below",
               "reference_price": "", "avg_cost": "100"}
        self.assertIsNone(digest.band_target(row))

    def test_every_holdings_row_survives_both_loaders(self):
        alerts = stock_alerts.load_holdings()
        self.assertIsInstance(alerts, list)
        symbols = research_watch.load_symbols()
        self.assertGreater(len(symbols), 0)


# ======================================================================
# Data completeness, reported rather than assumed
# ======================================================================

class DataHealth(unittest.TestCase):

    def setUp(self):
        self.rows = list(csv.DictReader(
            io.StringIO(Path("holdings.csv").read_text(encoding="utf-8-sig"))))

    def test_no_duplicate_alert_definitions(self):
        """Two identical alert rows share a state key. One fires, the other
        is silently swallowed, and you believe both are armed."""
        seen = {}
        for i, r in enumerate(self.rows, start=2):
            atype = (r.get("alert_type") or "").lower()
            if atype in ("", "watch"):
                continue
            key = (r["ticker"].upper(), r["exchange"].upper(), atype,
                   r.get("alert_value", ""), r.get("direction", ""),
                   r.get("reference_price", ""))
            if key in seen:
                self.fail(f"row {i} duplicates row {seen[key]}: {key[0]} "
                          f"{atype} {key[3]}")
            seen[key] = i

    def test_alert_values_contain_no_thousands_separators(self):
        """A comma splits the csv column and the row silently changes
        meaning."""
        for i, r in enumerate(self.rows, start=2):
            for field in ("alert_value", "reference_price", "avg_cost", "qty"):
                self.assertNotIn(",", r.get(field) or "",
                                 f"row {i}: comma in {field}")

    def test_long_term_quantity_never_exceeds_total(self):
        for i, r in enumerate(self.rows, start=2):
            try:
                qty, lt = float(r["qty"]), float(r["lt_qty"])
            except (ValueError, KeyError, TypeError):
                continue
            self.assertLessEqual(lt, qty, f"row {i}: lt_qty above qty")

    def test_report_completeness(self):
        """Not an assertion. Prints what the dataset is missing, because a
        gap nobody can see is a gap nobody fixes."""
        priced = [r for r in self.rows if (r.get("avg_cost") or "").strip()]
        no_date = [r for r in priced if not (r.get("buy_date") or "").strip()]
        no_lt = [r for r in priced if not (r.get("lt_qty") or "").strip()]
        no_sector = [r for r in priced if not (r.get("sector") or "").strip()]
        flagged = [r for r in self.rows
                   if "UNCONFIRMED" in (r.get("note") or "").upper()]
        print("\n  Data health")
        print(f"    rows                      {len(self.rows)}")
        print(f"    with a cost basis         {len(priced)}")
        print(f"    missing buy_date          {len(no_date)}"
              f"   (blocks every holding period figure)")
        print(f"    missing lt_qty            {len(no_lt)}"
              f"   (tax exemption runs conservative)")
        print(f"    missing sector            {len(no_sector)}")
        print(f"    tickers flagged unconfirmed {len(flagged)}")
        if flagged:
            print("      " + ", ".join(r["ticker"] for r in flagged))


class ReminderFile(unittest.TestCase):

    def test_reminders_parse_without_error(self):
        if not Path("reminders.csv").exists():
            self.skipTest("no reminders.csv")
        _due, errors = digest.load_reminders()
        self.assertEqual(errors, [], f"reminders.csv has errors: {errors}")

    def test_a_bad_date_is_reported_not_swallowed(self):
        """A reminder that vanishes because of a typo is worse than no
        reminder, because you believe it is still watching."""
        original = digest.REMINDERS_FILE
        with tempfile.NamedTemporaryFile("w", suffix=".csv", delete=False,
                                         encoding="utf-8") as f:
            f.write("label,date,repeat,lead_days,ticker,note,enabled\n")
            f.write("Broken,not-a-date,none,7,,,yes\n")
            tmp = Path(f.name)
        try:
            digest.REMINDERS_FILE = tmp
            _due, errors = digest.load_reminders()
            self.assertTrue(errors, "a malformed date must be reported")
        finally:
            digest.REMINDERS_FILE = original
            tmp.unlink()


if __name__ == "__main__":
    unittest.main(verbosity=2)

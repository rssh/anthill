## Attributes

- id: WI-20260903-W9D4Z-one-authored-mistake-in-a-simp
- created: 2026-09-03T09:30:17Z

- status: Open
- status_agent: user
- status_at: 2026-09-03T09:30:17Z

- acceptance: cargo-test, scaland-sbt-test

## Description

ONE AUTHORED MISTAKE IN A `[simp]` RHS IS REPORTED ONCE PER FIRING SITE, BYTE-IDENTICAL IN TEXT AND LOCATION.

MEASURED on the WI-20260903-FCZ3N tree, in `zzd` with `operation sink(r: Int64) -> Int64 = r`:

| program | errors |
|---|---|
| `rule bad(?x) <=> sink("nope") [simp]` + `operation c(n) = bad(n)`          | 1 — `4:20: … sink.r (op-arg): expected Int64, got String` |
| the same rule + `operation c(n) = bad(n) + bad(n)`                          | **2, byte-identical**, both `4:20` |
| CONTROL: `operation c2(n) = sink("nope") + sink("nope")` (written twice)   | 2, at `4:37` and `4:52` — two places, two messages |

The control is what says the duplication is not the ordinary two-mistakes case: the author wrote ONE `sink("nope")`, and it is reported N times with nothing to tell the copies apart.

WHY IT LOOKS LIKE THIS NOW. WI-20260903-FCZ3N made a fired `[simp]` RHS keep the span the AUTHOR wrote, which is the whole point of that ticket — before it, the N copies carried their N REDEXES' distinct spans, so they were distinguishable and every one of them pointed at a line where the mistake is not written. So this is not a regression to undo: the location is now right and the COUNT is the residue. Raised by `/code-review` on FCZ3N, which is also where the wi873 `nth_at_span` fixture had to be re-sited for the same collision (`one_rule_fired_at_two_redexes_collides_on_one_span`).

THE QUESTION IS WHOSE. Collapsing identical `(span, message)` load errors is a change to the whole diagnostic channel, not to `[simp]`: every pass feeds it, several suites assert error COUNTS, and "two errors that happen to render alike" would have to be shown impossible rather than assumed. That is why it is not folded into FCZ3N.

ACCEPTANCE. The two-firing-site program above reports the mistake ONCE, at `4:20`; the two-written-copies control still reports TWICE, at its two spans. Census the corpus for existing identical-`(span, message)` pairs FIRST — if the dedup collapses any of them, each one is either a second instance of this same shape or a suite whose count assertion is now measuring the dedup, and both have to be named before the change lands. Say which rows fail when it is backed out.

NOTE: do NOT pin the current 2 with a fixture in the meantime — a row asserting the duplication would go red on this ticket's own fix.

Split out of WI-20260903-FCZ3N, which measured it and does not own it.


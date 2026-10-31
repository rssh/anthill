## Attributes

- id: WI-20260924-GP8JC-the-bodied-defaulted-spec-op
- created: 2026-09-24T19:10:59Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-31T23:27:01Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

THE BODIED (DEFAULTED) SPEC-OP WEAVE IS CARRIER-BLIND: a clause's require dictionary is threaded into EVERY call to a defaulted spec operation, whatever argument the call carries — a clean load and a definite wrong answer.

MEASURED 2026-09-24, and the same with WI-20260911-5G28A S2's weave change backed out:
  sort Desc   { sort T = ?; operation describe(x: T) -> Int64 = 1 }        -- DEFAULTED
  sort Thing  { entity thing;  provides Desc[T = Thing];  operation describe(x: Thing) -> Int64 = 7 }
  sort Gadget { entity gadget; provides Desc[T = Gadget]; operation describe(x: Gadget) -> Int64 = 9 }
  rule two(?x, ?y, ?r1, ?r2) :- ?d = require[Desc[T]], Desc.describe(?x, ?r1), Desc.describe(?y, ?r2)
  rule twoTyped(a: Thing, b: Gadget, ?r1, ?r2) :- ?d = require[Desc[T = Thing]], Desc.describe(a, ?r1), Desc.describe(b, ?r2)
two(thing(), gadget(), ?r1, ?r2) answers 9, 9 where the carriers' own answers are 7, 9; twoTyped answers the same 9, 9 although its bracket names Thing. CONTROL: with describe BODY-LESS both answer 7, 9 (since S2's carrier direction).

WHY. record_find_dictionary_grounding reaches a defaulted op only through its last witness scan (scan_body_dfs), which walks a LIFO stack — so the witness is the LAST call, describe(?y) / describe(b), and ?d is Gadget's dictionary. That scan does not read the bracket (WI-20260917-HRFR5's bracket choice is on the direct scan only), and collect_covered_calls covers every BODIED call (functional_relation_arity) carrier-blind, as WI-1040 wove it — so Gadget's dictionary also reaches describe(?x).

WHY S2's FIX DOES NOT CARRY OVER. S2 made the BODY-LESS weave carrier-directed — a call is covered only where it shares the argument the dictionary was read from — because an uncovered body-less call dispatches on its VALUE. An uncovered BODIED call folds the SPEC DEFAULT instead (WI-1040 measured `via` answering 1 then 7), so the direction alone turns two's 9, 9 into 1, 9: one wrong answer for another. Either an uncovered defaulted call at another carrier must dispatch on its value as a body-less one does, or the clause must be refused — WI-20260909-96ZTM's plan V: "a covered call matching NO dictionary must not be silently dropped".

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven): two answers 7, 9; twoTyped answers 7, 9, or is refused naming the bracket and the witness it disagrees with. Controls, passing either way by design: the body-less twin (7, 9); WI-1040's two calls at ONE carrier (require[Desc[T]], Desc.describe(?x, ?a), Desc.describe(?x, ?b)) still dispatch both through the dictionary; nar1x_carrier_less_spec_op_test's defaulted-tag rows unchanged.

FOUND BY WI-20260911-5G28A S2 (docs/design/060-implementation.md §7.3, "FOUND DRIVING S2, AND NOT S2's").

## Changes

### 2026-10-31T23:26:53Z — feedback — claude

DELIVERED. Run on the tree first (2026-10-31): two(thing(), gadget()) still answered 9, 9 (reversed 7, 7); twoTyped already answered 7, 9; and the ticket's premise had lapsed — an UNCOVERED defaulted call now dispatches on its value (7, 9; the default 1 only for a carrier with no member of its own). So S2's carrier direction carries over. Two halves, each a defect of its own:
(1) THE WEAVE IS CARRIER-DIRECTED FOR A BODIED CALLEE TOO (collect_covered_calls: the carrier-argument gate no longer exempts a bodied op; install_rule_provider_dictionaries' copy of the same filter deleted). Backed out: two 7, 7 / 9, 9; a nested call 7, 7; a passed dictionary reached dark()'s call (heatOther 30, ownOther 1).
(2) A DEFAULTED OP IS A DIRECT WITNESS (anchor.rs: the direct scan admits defaulted_spec_op_parent beside lookup_spec_op_dispatch, so body order and the bracket read as for a body-less op; defaulted_spec_op_witness_grounds_soundly deleted). Backed out: a citation's dictionary was read at the LAST call (rankBoth's heatAt 1 where the body-less twin answers 30); a defaulted call beside an operation that requires the spec was never covered (Util.twice: 30 -> 1); two bracket-named requires (Desc[T = Leaf] / Desc[T = Other]) were refused where the body-less twin loads — now admitted, each dictionary its own bracket's. The old whole-body scan stays, after the transitive and inherited ones, for a defaulted call NO GOAL RUNS (a negand, a branch), first in body order: /code-review found that deleting it refused `not(Desc.describe(?x, 1))`, which loaded before. Its body-less twin is refused, before and after — not changed here.
Rows and the per-half back-out table: rustland/anthill-core/tests/include/wi_gp8jc_defaulted_weave_test.rs (8 rows, commit 80163072; twoTyped and the body-less twin pass either way by design; WI-1040's one-carrier pair is wi1040::every_covered_call_in_the_clause_is_woven, unmoved). Over the 36 test files that write require[...]: no other row moved under either back-out. kernel-language.md: the "a call to a DEFAULTED operation is still covered whatever it carries — a known gap" parenthetical removed; 060-implementation.md §7.3 records the delivery. /code-review (xhigh): 8 findings, 5 fixed, 1 no change (a projected anchor covers no carrier-bearing call — the body-less rule), 2 skipped (the inherited-witness reordering is undriven; an unalignable bodied call is never covered, as a body-less one is not).


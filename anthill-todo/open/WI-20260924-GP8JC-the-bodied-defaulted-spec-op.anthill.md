## Attributes

- id: WI-20260924-GP8JC-the-bodied-defaulted-spec-op
- created: 2026-09-24T19:10:59Z

- status: Open
- status_agent: user
- status_at: 2026-09-24T19:10:59Z

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


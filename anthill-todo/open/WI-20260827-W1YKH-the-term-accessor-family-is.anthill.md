## Attributes

- id: WI-20260827-W1YKH-the-term-accessor-family-is
- created: 2026-08-27T11:16:54Z

- status: Open
- status_agent: user
- status_at: 2026-08-27T11:16:54Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE TERM-ACCESSOR FAMILY IS CARRIER-BLIND: `term_field` REFUSES A `Value::Entity`, WHICH IS EXACTLY WHAT `as_term` PRODUCES — so the composition the reflection surface exists for cannot run. Split out of WI-20260827-1ZG70's analysis; independent of it, and a wrong answer on GROUND input today.

`as_term[E](e: E) -> Term` is the IDENTITY at the host level (`eval/builtins.rs`: `let [e] = ...; Ok(e)`), and its own declaration says why that is right — "at runtime the engine's carriers already let a `Value::Entity` inhabit `Term`". So `as_term(some(7))` hands on a `Value::Entity`. `term_field` then matches `Value::Term { id }` and `other => return Err(type_mismatch("Term", ...))`. The canonical way to GET a term is rejected by the operation that exists to READ one.

MEASURED 2026-08-27 on the tree at b09aa9f1:

  rule f1(?t) :- term_field(as_term(some(7)), "value") <=> ?t
      SUSPENDS.  Correct answer: some(7).

The suspension is the mild half. `bridge_op_to_eval` residualizes the error, `reduce_op_value` restores the un-reduced CALL, and the ENCLOSING accessor then reads that call as data and COMMITS — the WI-880 wrong-answer class, one operation over. Those rows are WI-20260827-4XXSD's, which owns the enclosing half; this ticket owns the CAUSE. Landing 4XXSD alone turns the wrong answers into suspensions and leaves f1 suspended; landing this alone makes f1 answer. Both are wanted, neither subsumes the other.

THE FAMILY IS NOT UNIFORM, and the census is the ticket rather than the one-line fix:

  term_functor_name   CARRIER-NEUTRAL already — `value_head_symbol`, and its own
                      comment records the migration off a hand-matched Fn/Ref/Ident/
                      Entity nest.
  term_field          `Value::Term` ONLY; anything else is a LOUD type_mismatch that
                      residualizes into the silent wrong answer above.
  term_as_int         `Value::Term` only; everything else falls to `_ => None` and
                      answers `none()` SILENTLY. A refusal spelled as an answer.
  term_as_string      same shape as term_as_int.
  term_as_entity      carrier-AWARE (`Value::Term` and `Value::Entity` both), which is
                      the shape the rest should have.

So three distinct behaviours for one question, and two of the three are wrong in DIFFERENT directions — one loud-then-silently-swallowed, one silent from the start. `term_list_items`, `term_to_string` and `extract` are NOT in the list above because I did not read their carrier handling; census them rather than assume.

WHAT `none()` MAY AND MAY NOT MEAN. `term_as_int`'s declaration says "Returns none() unless the term is exactly `Const(IntLiteral(_))`" — so `none()` for an ENTITY is arguably correct and only the SILENCE is wrong. `term_field`'s says "Returns none() when the term has no matching named arg or is not Fn-shaped" — and an Entity with that named arg HAS one, so `none()` there would be a wrong answer and the current `type_mismatch` is at least honest. Decide per operation against its own declared contract, not family-wide.

THE REPAIR DIRECTION, prototyped and measured for `term_field` alone: read the `Value::Entity`'s named args directly. f1 goes from SUSPEND to `some(7)`; `term_functor_name(term_field(...))` from `some("term_field")` to `some("some")`; `term_to_string(term_field(...))` from the printed CALL text to `"some(value: 7)"`. Full workspace 5863 passed / 0 failed with it, and 5863 / 0 without it — THE CORPUS DOES NOT REACH THIS, so green is not evidence and every row must be driven.

TWO ROWS ARE BLIND, recorded so they are not mistaken for witnesses: `term_as_int(term_field(as_term(some(7)), "value"))` answers `none()` before AND after (before, from reading the un-reduced call; after, because the argument is the `Option` wrapper, not a `Const` int), and the `= some(7)` row is 0/0 both ways. Same value, opposite reasons.

RELATION TO CLAUDE.md's localized invariants: this is the "per-carrier host-op keying" rule, which is stated in docs/kernel-language.md and enforced at a doc-commented site. Check whether that site should have caught this family and did not.

ACCEPTANCE: `term_field(as_term(some(7)), "value")` answers `some(7)`, driven, on a carrier the program can actually produce; the family census above is completed (`term_list_items` / `term_to_string` / `extract` read, not assumed) and each operation's behaviour on a non-`Term` carrier is either made neutral or DOCUMENTED at its declaration as deliberate; no accessor answers `none()` for a carrier it simply did not recognise — that is a refusal spelled as an answer, and the loud-over-silent rule forbids it; the two blind rows are recorded AS blind; full workspace green via rustland/scripts/test.sh.

REFERENCE: `term_field` / `term_as_int` / `term_as_string` / `term_as_entity` / `term_functor_name` (rustland/anthill-core/src/eval/builtins.rs), `as_term`'s declaration in stdlib/anthill/reflect/reflect.anthill, WI-880 (which host-mapped the family), WI-20260827-4XXSD (the enclosing half).

## Changes

### 2026-08-27T11:39:02Z — feedback — user

THIS TICKET IS THE EXPIRY OF `wi_4xxsd_unreduced_host_arg_test`, delivered 2026-08-27. That file borrows THIS defect as its un-reducible inner call, so landing this one changes its rows and it must be updated in the same commit.

WHAT CHANGES THERE, with the values already written at the test site:

  rule f1(?t)      :- term_field(as_term(some(7)), "value") <=> ?t
      asserted TODAY as a suspension, under a comment calling it the PREMISE.
      With this ticket it answers `some(7)` and that assertion is the TRIPWIRE that
      fires — it is written to say exactly this, not to be silently relaxed.
  rule functor(?n) :- term_functor_name(term_field(as_term(some(7)), "value")) <=> ?n
      asserted TODAY as a suspension; becomes 1 DEFINITE `some("some")`.
  rule printed(?s) :- term_to_string(term_field(as_term(some(7)), "value")) <=> ?s
      asserted TODAY as a suspension; becomes 1 DEFINITE `"some(value: 7)"`.

DO NOT SIMPLY UPDATE THE THREE EXPECTATIONS AND MOVE ON. 4XXSD's claim is that a host op never reads an inner call the bridge could not reduce, and those two witnesses are the only rows driving it. Once this ticket makes the inner call reduce, they no longer exercise a FAILED inner call at all and 4XXSD is left with a control and no witness. Either re-point them at an inner call that still fails, or say at the site that no such call remains reachable from source — which would be a real narrowing of the class and worth recording rather than losing.

NOTE ONE SHAPE THAT IS NOT A CANDIDATE, measured while filing: a declared-but-unimplemented operation (`sort_as_term`) does NOT reproduce it. `is_unreduced_op_call` deliberately excludes a body-less unmapped op — that is the symbolic-algebra boundary its own doc argues (the wi616 five) — so such a call passes the refusal AND the ground gate and the host does read it. That is the intended boundary, not a gap this ticket or 4XXSD moves.

AND THE BLIND ROWS STAY BLIND, for a THIRD reason. `term_as_int(term_field(as_term(some(7)), "value"))` answers `none()` before 4XXSD (reading the un-reduced call), after 4XXSD (the argument suspends), and after THIS ticket (the argument is the `Option` WRAPPER `term_field` returns, which is not a `Const` int). Three mechanisms, one value. They are recorded as blind in 4XXSD's file header; do not promote either into a witness here.


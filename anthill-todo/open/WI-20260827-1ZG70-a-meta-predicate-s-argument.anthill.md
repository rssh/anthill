## Attributes

- id: WI-20260827-1ZG70-a-meta-predicate-s-argument
- created: 2026-08-27T09:31:02Z

- status: Open
- status_agent: user
- status_at: 2026-08-27T09:31:02Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260827-4XXSD-an-un-reduced-op-call-is

## Description

A META-PREDICATE'S ARGUMENT NEED NOT BE GROUND — the reflection surface is host-mapped
since WI-880 and still suspends on exactly the terms reflection exists to inspect.

The bridge will not hand a host function a non-ground argument, which is RIGHT for
`Int64.add` (a logic variable is not a number) and WRONG for `term_functor_name` /
`term_field` / `extract`: their domain IS terms, variables included. The functor of
`some(?x)` is `some`, whatever `?x` turns out to be — that is what a meta-predicate is
for, and Prolog's `functor/3` answers for `foo(X,Y)` without hesitation.

MEASURED 2026-08-27 on the tree at WI-880:

  rule g(?n)  :- term_functor_name(as_term(some(7)))  <=> ?n     1 solution
  rule ng(?n) :- term_functor_name(as_term(some(?x))) <=> ?n     1 solution, CONDITIONAL
      residual: unify(term_functor_name(as_term(some(value: ?_))), ?_)

One `?_` one level down inside the argument is enough to suspend the whole call.

WHY IT BITES IN PRACTICE RATHER THAN IN A FIXTURE. Over the guardians KB, most
`SortProvidesInfo.spec` views are NOT ground — they carry open effect-row tails:

  residual: unify(term_functor_name(SortView(Iterable,
              E: EffectsRows(effects_expr: merge(left: open(tail: ?_),
                                                 right: open(tail: ?_))), ...)), ?_)

An open row tail is exactly the thing a reflection reader should be able to LOOK AT and
report. So after WI-880 the surface is visible to the gate and still unusable on the
population it was migrated for. NOTE the relation is not the problem: `SortProvidesInfo`
is an ordinary fact relation and enumerates fine; the suspension is entirely in the host
call downstream of it.

WHAT TO DECIDE, and it is a policy question rather than a bug with one obvious patch.
Either (a) the reflect family is exempt from the ground gate as a class — a host function
over `Term` receives a term and that is its contract; or (b) the gate becomes
per-parameter, keyed on the DECLARED type (`Term` / `Type` / `NodeOccurrence` slots take
non-ground arguments, everything else does not), which is narrower and does not hand a
blanket exemption to a future reflect operation that genuinely needs ground input; or (c)
the operations that can answer structurally are separated from those that cannot, and
only the first group is exempted. (b) looks right and (c) is the fallback if some
operation turns out to straddle.

WATCH THE TRAP WI-880 ALREADY HIT ONCE, from its own commit message: "an un-reduced call
IS a term, so once the accessors were host-mapped a `Term`-typed parameter passed the
bridge's ground check and the host function ran ON THE CALL". Widening the gate on
`Term`-typed slots is the SAME COORDINATE that defect was on, so whatever lands must keep
`term_as_int(as_term(7))` reducing its argument first rather than inspecting the call —
and must drive that row, since `= none()` was the row that caught it and `= some(7)` was
blind to it.

RELATION TO THE NEIGHBOUR: filed alongside the ticket about a rule body being unable to
BIND an operation's result. They are independent — this one is about whether the call
RUNS, that one about what happens to what it returns — and a consumer needs both.

ACCEPTANCE: `term_functor_name(as_term(some(?x)))` answers `some` rather than suspending;
a reflection reader over `SortProvidesInfo` whose spec view carries open effect-row tails
gets an answer; the WI-880 regression row `term_as_int(as_term(7)) = none()` stays 0 and
`= some(7)` stays 1, driven, so the un-reduced-call trap cannot come back; the chosen
policy (a/b/c above) is stated in kernel-language.md §5.2 beside VPEWK's rows; full
workspace green via rustland/scripts/test.sh.

## Changes

### 2026-08-27T11:17:45Z — feedback — user

POLICY (b) IS REFUTED, DRIVEN — and it fails on this ticket's OWN headline row, through the operation the acceptance clause names. Measured 2026-08-27 by prototyping (b) exactly as written ("the gate becomes per-parameter, keyed on the DECLARED type") and running the row:

  rule ng(?n) :- term_functor_name(as_term(some(?x))) <=> ?n
      baseline    0 definite / 1 total   SUSPENDS
      policy (b)  1 DEFINITE, ?n = some("as_term")     <-- WRONG VALUE
  rule nge(1) :- term_functor_name(as_term(some(?x))) = some("some")
      baseline    0 / 1   suspends (sound)
      policy (b)  0 / 0   DECIDED FALSE                <-- a sound suspension turned unsound

WHY. `as_term[E](e: E) -> Term` takes a TYPE VARIABLE, not a `Term`. A `Term`-keyed exemption never reaches it, so `as_term(some(?x))` stays un-reduced; the now-exempt OUTER slot accepts that un-reduced call as legitimate `Term` data; `term_functor_name` reads its head and reports the CALL's functor. This is precisely the trap the ticket's own WATCH THE TRAP paragraph names — it just arrives through the inner operation rather than the outer one, which is the case a declared-type key cannot see.

POLICY (a) ANSWERS THE HEADLINE ROW AND IS STILL UNSOUND. Prototyped as "exempt every `anthill.reflect.*` op": `ng` answers `some("some")` correctly and every WI-880 guard holds — but

  rule varB(1) :- term_as_int(as_term(?x)) = none()
      baseline    0 / 1   suspends (sound)
      policy (a)  1 DEFINITE            <-- asserts `?x` is not an integer, with `?x` FREE
  rule varA(1) :- term_as_int(as_term(?x)) = some(7)
      baseline    0 / 1   suspends
      policy (a)  0 / 0   DECIDED FALSE

THERE IS A FOURTH OPTION, AND IT IS THE ONE THE TRIAD IS MISSING. The separator is neither the operation (a) nor the declared type (b): it is WHETHER THE POSITION THE ACCESSOR READS IS INSTANTIATED. `term_functor_name(some(?x))` is decidable — the head is `some` whatever `?x` turns out to be, which is this ticket's own opening argument. `term_functor_name(?x)` is not. `term_as_int(?x)` is not, because that accessor READS THE WHOLE TERM. This is exactly the discipline of the `functor/3` the ticket cites, which answers for `foo(X,Y)` and RAISES an instantiation error on an unbound first argument — the ticket quoted the first half of that contract and not the second.

  (d) Drop the blanket ground gate for the reflect family, and give each accessor its
      OWN instantiation requirement: it returns `EvalError::Suspended` for the one case
      it cannot answer — a variable at the position it reads. The bridge ALREADY
      residualizes on `Suspended`, so this needs no new mechanism.

DRIVEN, on `term_as_int`: with (d) added on top of (a), `varA` and `varB` return to sound suspensions while `ng` KEEPS the right answer `some("some")` and every WI-880 guard stays put. Full workspace 5863 passed / 0 failed.

(c) — "separate the operations that can answer structurally from those that cannot" — is the closest of the three, and (d) is what it becomes once you notice the split is not between OPERATIONS but between an operation and its ARGUMENT. `term_functor_name` is on both sides of (c) depending on what it is handed.

THE PREREQUISITE, now filed as WI-20260827-4XXSD and added as a dependency. The ground gate is answering TWO questions, and only one of them is groundness: it is also the only thing stopping an outer accessor from reading an UN-REDUCED INNER CALL, and it does that by accident (a call is refused only when it happens to contain a variable). Relaxing it — under (a), (b) or (d) — makes every un-reducible inner call readable data at every exempt slot. Split the questions first: refuse an `is_unreduced_op_call` argument on its own line, before the ground check. That refusal is a wrong-answer fix on its own, needs no exemption, and measured green.

WI-20260827-W1YKH is the third piece and is INDEPENDENT of this one: `term_field` refuses a `Value::Entity`, which is what `as_term` produces, so the composed reader does not work even on GROUND input. This ticket's practical acceptance clause ("a reflection reader over `SortProvidesInfo` ... gets an answer") needs that one too — an open effect-row tail is reached by DRILLING IN, and the drill is `term_field`.

THE CORPUS IS GREEN FOR ALL OF IT — 5863 passed / 0 failed at baseline, with the prerequisite alone, and with all four pieces. Nothing in the suite reaches any of this, so green is not evidence and every row above must be driven at its own test site.

ACCEPTANCE AMENDMENT: replace "the chosen policy (a/b/c above) is stated in kernel-language.md §5.2" with the (d) reading, and add `varA` / `varB` to the control set — a repair that answers the headline row while deciding either of those is not a repair. A driven prototype of (a)+(d)+the prerequisite exists and measured green.


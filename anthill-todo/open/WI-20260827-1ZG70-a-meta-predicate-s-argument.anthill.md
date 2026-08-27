## Attributes

- id: WI-20260827-1ZG70-a-meta-predicate-s-argument
- created: 2026-08-27T09:31:02Z

- status: Open
- status_agent: user
- status_at: 2026-08-27T09:31:02Z

- acceptance: cargo-test, scaland-sbt-test

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


## Attributes

- id: WI-20261015-D2KZ5-an-unwritten-t1-is-bound-to
- created: 2026-10-15T17:31:46Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-27T11:16:20Z

- acceptance: cargo-test, scaland-sbt-test

- tags: effects

## Description

AN UNWRITTEN `T1` IS BOUND TO WHICHEVER `Error` LABEL OF THE BODY'S ROW PAIRS FIRST, so swapping the branches of an `if` flips an `Error.reify` verdict.

MEASURED (2026-10-15; the same on ee3696eb and after the WI-20260908-9WVT7 guarded-raise fix):
  operation twoLabels(a: Int64, b: Int64) -> Result[E = DivisionByZero, T = Int64] effects {Error[String]} =
    Error.reify(lambda () -> if a < 0 then Error.raise("negative") else a / b)
is refused ("expected Result[E = DivisionByZero, T = Int64], got Result[E = String, T = Int64]"), while the same with the branches swapped (`if a >= 0 then a / b else Error.raise("negative")`) loads and catches. Unguarded twins flip the same way, and so does an eta'd callee whose written row lists `{Error[String], Error[DivisionByZero]}` in either order. A `let r: Result[E = DivisionByZero, …]` annotation does not choose either.

MECHANISM. `match_present_labels` (typing/effects.rs) pairs greedily and 1-to-1 in row order, so the first label of the callback's row that unifies with `Error[T1]` binds `T1`. A lambda's row keeps body order (`make_arrow_value`) and a declared row keeps written order; `pair_present_labels`' doc assumes rows sorted by display name, which only `build_canonical_effects_rows` gives. The expected result type is not consulted.

WORKAROUND: `Error.reify[T1 = DivisionByZero](…)`.

TO DECIDE: which label an unwritten `T1` is when the body raises two `Error` labels. 027.4 says `T1` is inferred from the body's row, which is ambiguous there: refuse as ambiguous and ask for `[T1 = …]`, take it from the expected type, or fix an order.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh): both branch orders, and both written orders of an eta'd callee, give one verdict; the rule is stated in kernel-language.md and 027.4; rows for each.

## Changes

### 2026-10-15T20:47:51Z — feedback — claude

IN A RULE BODY THE CHOICE CANNOT BE WRITTEN, and a typed head does not make it (measured 2026-10-15 on cc3d1a7d, from the WI-20260908-9WVT7 review). Over `operation twoWays(n: Int64) -> Int64 effects {Error[Boom], Error[Other]} = if n < 0 then Error.raise(boom("negative")) else Error.raise(other(n))`:
  `rule pickOtherNeg(?r: Result[E = Other, T = Int64]) :- Error.reify(lambda () -> twoWays(0 - 7), ?r)` answers NO SOLUTIONS with nothing said — `T1` is `Boom` (the first label), the boundary catches `boom("negative")`, and the head's domain guard then rejects the `err(boom(…))`;
  `rule pickOther(?r: Result[E = Other, T = Int64]) :- Error.reify(lambda () -> twoWays(7), ?r)` faults on the declined `other(n: 7)` and answers two generated conditional rows instead of `err(other(n: 7))`;
  the workaround `Error.reify[T1 = Other](…)` is refused on a rule-body goal ("call-site type arguments `Error.reify[…](…)` are not supported here");
  the operation-body twin `operation pickOp(n: Int64) -> Result[E = Other, T = Int64] = Error.reify(lambda () -> twoWays(n))` is refused at load ("expected Result[E = Other, T = Int64], got Result[E = Boom, T = Int64]"), so only the rule body is silent.
So whatever rule this ticket decides should reach the rule-body form too: the expected type the head writes (one of the three options above), or the bracket admitted at a rule-body goal.

### 2026-10-27T11:16:17Z — feedback — claude

Delivered with WI-20261016-BDVYW (2026-10-27), decided with the user there: an unwritten T1 is the least pattern that admits every Error label of the thunk's row, and labels no one sort heads are refused in every order (both branch orders of an if, both written orders of an eta'd callee's row), the call naming one by a bracket, [T1 = DivisionByZero]; in a rule body, whose term writes no bracket yet (WI-20261024-TC54R), the boundary goes in an operation the rule calls. Rule stated in kernel-language §8.7 and 027.4's status. Rows: wi_bdvyw_boundary_pattern_test::labels_no_one_sort_heads_are_refused_in_either_order, wi_9wvt7_reify_rule_body_test::a_rule_body_boundary_over_two_sorts_is_refused.


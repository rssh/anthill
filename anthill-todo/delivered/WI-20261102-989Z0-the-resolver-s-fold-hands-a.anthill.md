## Attributes

- id: WI-20261102-989Z0-the-resolver-s-fold-hands-a
- created: 2026-11-02T07:07:19Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-05T17:16:13Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-068

## Description

THE RESOLVER'S FOLD HANDS A NESTED BRIDGE AN OPERATION BODY'S LITERAL UNEVALUATED: a rule calling an operation whose body passes a `[…]` to a default body that reads its dictionary gets the right answer, a `match_failed` warning and an INCOMPLETE search. Found on WI-20260925-SHED7 (the `fromList` default body).

MEASURED on 5476eece, the same on f0d38c95:

  sort Pc
    sort C = ?
    sort Element = ?
    operation emp() -> C
    operation ins(c: C, elem: Element) -> C
    operation len(xs: List[T = Element]) -> Int64 = match xs
      case nil() -> 0
      case cons(x, rest) -> 1
  end
  sort Bx   -- bnil, badd(e: Int64, rest: Bx); provides Pc[C = Bx, Element = Int64] with emp and ins
  operation q() -> Int64 = Pc[C = Bx].len([1, 2, 3])
  rule r(?x) :- ?x <=> q()

`r(?x)`: "warning: `Pc.len` could not be evaluated by the resolver: raised match_failed(occurrence: var_ref(name: xs), scrutinee: ListLiteral(1, 2, 3))", then `?x = 1`, then "the search is INCOMPLETE". The fold (`reduce_op_value`) reduces `q`'s body; one level down `Pc.len` reads requirement slots (its parameter names the spec's `Element`), so the NeedsDict arm bridges it at that depth (WI-1037) with the folded arguments as values. `[1, 2, 3]` there is the operation body's `Constructor{ListLiteral}` (`typing::literal_as_constructor`), which eval builds into a `cons` spine but which presents as `ListLiteral(1, 2, 3)`, so no arm of `match xs` takes it. The fault is recorded; the depth-0 bridge then runs `q` whole and answers 1.

CONTROLS: `len(xs: List[T = Int64])` (no slot read, no nested bridge) answers clean; the rule-body call `?x <=> Pc[C = Bx].len([1, 2, 3])` (a rule's literal is lowered to a spine) answers clean; `q` run as a program prints 1. The same nested bridge declines an argument that is still a call (WI-20261016-5CDN5), which is how WI-20261102-6GAS1's panic is reached. WI-20261013-DEY66 retires this fold.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven, back-out stated at its site): `r(?x)` answers 1, definite, no warning, the search complete; the same with a set literal, a tuple literal and a literal nested in a constructor (`some([1, 2])`); the controls unchanged.

## Changes

### 2026-11-05T17:16:11Z — feedback — claude

DELIVERED with WI-20261013-DEY66 (ab6d7288): the fold is retired, so no nested bridge is handed an operation body's literal — every call runs whole in the interpreter. r(?x) over q() = Pc[C = Bx].len([1, 2, 3]) answers 1, definite, no fault, the search complete; the literal nested in a constructor, olen(some([1, 2])), the same (both faulted match_failed before); the tuple literal (1, 2) answered 2 before as well (control). A set literal gets no row: no operation of Set has a body that reads a set. Rows: wi_dey66_per_consumer_reductions_test (a_call_reached_through_an_operation_body_runs_whole, a_literal_nested_in_a_constructor_runs_whole, control_a_tuple_literal_ran_before_too), failing on HEAD fd640523. scaland testFull 851 passed (scaland has no fold).


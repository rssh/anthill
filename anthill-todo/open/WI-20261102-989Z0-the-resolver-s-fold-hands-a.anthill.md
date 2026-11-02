## Attributes

- id: WI-20261102-989Z0-the-resolver-s-fold-hands-a
- created: 2026-11-02T07:07:19Z

- status: Open
- status_agent: claude
- status_at: 2026-11-02T07:07:19Z

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


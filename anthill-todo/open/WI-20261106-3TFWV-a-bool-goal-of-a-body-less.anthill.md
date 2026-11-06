## Attributes

- id: WI-20261106-3TFWV-a-bool-goal-of-a-body-less
- created: 2026-11-06T11:42:10Z

- status: Open
- status_agent: claude
- status_at: 2026-11-06T11:42:10Z

- acceptance: cargo-test

- tags: proposal-068

## Description

A `Bool` GOAL OF A BODY-LESS SPEC OPERATION THE TYPER DID NOT PIN IS READ AS A RELATION WITH NO CLAUSES, so it fails and its `not` succeeds — under a clause's guard and at an open type alike. kernel-language §5.2's goal-position table reads a `Bool` operation at its declared arity as the condition `eq(f(args), true)`: reduced, `false` failing, an under-determined argument suspending, never decided by negation. Found beside WI-20261105-C6GK8 (its review's sweep).

MEASURED on a88ec85b, the same on 65f8438b, over `sort Pred { sort T = ?  operation ok(x: T) -> Bool }`, `sort Leaf { entity leaf(v: Int64)  provides Pred[T = Leaf]  operation ok(x: Leaf) -> Bool = match x case leaf(v) -> v > 2 }`, `sort Other { provides Pred[T = Leaf]  operation ok(x: Leaf) -> Bool = false }` and `fact src(leaf(v: 3))`. UNDER A GUARD, `rule chkG[A](?x: A) :- Pred[T = A], Pred.ok(?x)`: `rule viaG(?y) :- src(?y), chkG(?y)` answers no solutions and `rule notG(?y) :- src(?y), not(chkG(?y))` answers `?y = leaf(v: 3)`; cited from an operation body, `chkG[A = Leaf](leaf(v: 3))` yields no row. Its result-column twin `rule chkGR[A](?x: A, ?r) :- Pred[T = A], Pred.ok(?x, ?r)` answers `?r = true` through `viaGR(?y, ?r) :- src(?y), chkGR(?y, ?r)`. AT AN OPEN TYPE, `rule chk(?x) :- Pred.ok(?x)` loads, `via(?y) :- src(?y), chk(?y)` answers no solutions and `notVia(?y) :- src(?y), not(chk(?y))` answers `?y = leaf(v: 3)`, where the twin `rule chk(?x, ?r) :- Pred.ok(?x, ?r)` is refused at load, "a rule takes no dictionary it does not declare" (060.1 §1). With `?x: Leaf` written the goal is pinned to `Leaf.ok` and answers `leaf(v: 3)`.

WHY: the resolver reads a goal `f(args)` as `eq(f(args), true)` (`dispatched_bool_relation`, kb/resolve.rs) only for an `f` with a body or a goal the typer pinned to one. The guarded goal is stored woven, `ApplyWithin Pred.ok(?x, <dictionary>)` behind its `find_dictionary` / `domain` reads, as the twin is; the open one is stored as the bare spec operation. Both fall through to a lookup of the relation `Pred.ok`, which has no clause. And the typer's refusal of a call at a type the clause declares no requirement at (`undeclared_requirement`, kb/typing/rule_requirements.rs) is raised for the twin and not for the goal form.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven, back-out stated at its site): `viaG` answers `leaf(v: 3)` and `notG` nothing; `chkG[A = Leaf](leaf(v: 3))` one row and `chkG[A = Leaf, Pred = Other](leaf(v: 3))` none, each `not` the other way; a guarded goal whose argument a later goal binds suspends and answers once it is bound; `rule chk(?x) :- Pred.ok(?x)` is refused at load with its twin's refusal, and both repairs run — the guard, `chk[A](?x: A) :- Pred[T = A], Pred.ok(?x)`, and the typed head, `?x: Leaf`. CONTROLS unchanged: the result-column twins, the pinned goal, a bodied `Bool` operation's goal (WI-580's view), `wi1043_bodyless_rule_body_test::a_pinned_body_less_bool_goal_decides`.


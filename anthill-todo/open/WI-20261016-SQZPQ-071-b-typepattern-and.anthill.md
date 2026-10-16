## Attributes

- id: WI-20261016-SQZPQ-071-b-typepattern-and
- created: 2026-10-16T14:51:18Z

- status: Open
- status_agent: claude
- status_at: 2026-10-16T14:51:18Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261016-Y1EZJ-071-a-the-proposal-and-the

- tags: proposal-071

## Description

071 (b): `TypePattern` AND `TypeValue provides TypePattern[T = T]`, BEHAVIOUR-NEUTRAL. Proposal 071 §1.1, §1.2, §1.5.
THE CHANGE: `sort anthill.reflect.TypePattern { sort T = ?; operation admits(t: Type) -> Bool }` beside `TypeValue`; in `TypeValue`, `provides TypePattern[T = T] :- TypeValue[T = T] where operation admits(t: Type) -> Bool = …` (066's `where` block puts the condition in the member's scope). `admits` is backed by ONE subtype test over two type terms — carrier-neutral (`TermView` on both sides), an open slot admitting every type, variance from the declared `Covariant` facts — the run-time half of the predicate stage (e) gives the typer's discharge. A written `provides TypePattern[…]` is refused at load, as a written `provides TypeValue[…]` is. Nothing reads `TypePattern` yet.
MEASURED (2026-10-16, a program-level stand-in): `sort Mark { sort T = ?; provides Tag[T = T] :- TypeValue[T = T] where operation tag() -> Type = T end }` answers `Boom` through `tagOf[B](x: B) requires Tag[T = B] = Tag.tag()`; outside the `where` block the member is refused (nothing puts `TypeValue[T = T]` in its scope), and with its own `requires` it is refused as strengthening the spec's precondition.
ACCEPTANCE (cargo-test via rustland/scripts/test.sh, scaland sbt testFull): `admits` driven through a slot — a pattern at `Boom[Reason = String]` admits that type and not `Boom[Reason = Int64]`; a pattern at `IoError` admits `FileNotFound` (`sort FileNotFound requires IoError`); a written `provides TypePattern[…]` refused; every other row unchanged.


## Attributes

- id: WI-20261016-SQZPQ-071-b-typepattern-and
- created: 2026-10-16T14:51:18Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-20T07:41:20Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261016-Y1EZJ-071-a-the-proposal-and-the

- tags: proposal-071

## Description

071 (b): `TypePattern` AND `TypeValue provides TypePattern[T = T]`, BEHAVIOUR-NEUTRAL. Proposal 071 §1.1, §1.2, §1.5.
THE CHANGE: `sort anthill.reflect.TypePattern { sort T = ?; operation admits(t: Type) -> Bool }` beside `TypeValue`; in `TypeValue`, `provides TypePattern[T = T] :- TypeValue[T = T] where operation admits(t: Type) -> Bool = …` (066's `where` block puts the condition in the member's scope). `admits` is backed by ONE subtype test over two type terms — carrier-neutral (`TermView` on both sides), an open slot admitting every type, variance from the declared `Covariant` facts — the run-time half of the predicate stage (e) gives the typer's discharge. A written `provides TypePattern[…]` is refused at load, as a written `provides TypeValue[…]` is. Nothing reads `TypePattern` yet.
MEASURED (2026-10-16, a program-level stand-in): `sort Mark { sort T = ?; provides Tag[T = T] :- TypeValue[T = T] where operation tag() -> Type = T end }` answers `Boom` through `tagOf[B](x: B) requires Tag[T = B] = Tag.tag()`; outside the `where` block the member is refused (nothing puts `TypeValue[T = T]` in its scope), and with its own `requires` it is refused as strengthening the spec's precondition.
ACCEPTANCE (cargo-test via rustland/scripts/test.sh, scaland sbt testFull): `admits` driven through a slot — a pattern at `Boom[Reason = String]` admits that type and not `Boom[Reason = Int64]`; a pattern at `IoError` admits `FileNotFound` (`sort FileNotFound requires IoError`); a written `provides TypePattern[…]` refused; every other row unchanged.

## Changes

### 2026-10-20T07:41:19Z — feedback — user

Delivered 2026-10-20. TypePattern (a spec: sort T = ?; operation admits(t: Type) -> Bool) and its one row, written on a sort of its own rather than on TypeValue as the description first had it (user, 2026-10-20): anthill.reflect.TypeValuePattern provides TypePattern[T = T] :- TypeValue[T = T], whose admits asks the one subtype test, the public reflect operation anthill.reflect.type_admits (kb/typing/type_pattern.rs). On TypeValue, which every sort provides, the block member was read as an operation of every sort, and the condition naming its own sort was stored as TypeValue with T left out. A written provides TypePattern[…] is refused at load (HandWrittenTypePattern); a second clause of the row by 066 §7.5 and, behind a seal, as a clause written into a sealed provision.

The test, as decided with the user (2026-10-20): nominal on the head; a sort refining the pattern's through requires is each instance its clauses give it, its own arguments put for the parameters a clause names; per argument by declared variance (Covariant / Contravariant facts; both: either; none: equal); an argument left out on either side, or written ?, admits; Nothing below everything; an arrow is the Function it is (§4.4), the empty row written {} or reported Nothing by a TypeValue; a decided false is not undone by an unjudged argument. Not judged, a run-time error: two named tuples, two effect rows that are not one row, a row beside another type, a type variable, a data value (one whose field is keyed like its sort's parameter included), and types nested deeper than 512 levels. A call at a type with an open slot is refused at load until stage (e).

Repairs the row needed or the two reviews found: a ? type argument in an operation body is left out where the typer types the type value, and a ?_ written again anywhere in the operation (signature and body) is refused; a sort's own operation named type_value no longer answers TypeValue.type_value, and the override and member checks no longer hold it to TypeValue's contract; a slot call naming a type with an open slot is refused with the account the slot gets inferred and left out, and a library spec's element left an unbound parameter with the unconstrained element's account (a program's spec still completes to its one provider); the resolver's advice for a goal that is not ground names both repairs; the lowered read of T carries its bracket, keyed by the bare parameter, so a body typed again (an unsealed later load, a @[simp] rewrite) reads it as written; behind a seal, a clause written at the head of a sealed provision is refused (ChangesSealedCode), found by the typer oracle.

Rows: rustland/anthill-core/tests/include/wi_sqzpq_type_pattern_test.rs; wi_9bkz4's a_clause_written_into_a_sealed_provision_is_refused. Each part's back-out measured with a temporary switch. Controls: full gate, scaland testFull, families, node carrier, typer oracle.


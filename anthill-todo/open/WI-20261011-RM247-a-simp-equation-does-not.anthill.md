## Attributes

- id: WI-20261011-RM247-a-simp-equation-does-not
- created: 2026-10-11T05:28:01Z

- status: Open
- status_agent: claude
- status_at: 2026-10-11T05:28:01Z

- acceptance: cargo-test

- tags: typing

## Description

A `@[simp]` EQUATION DOES NOT DEFINE A BODY-LESS OPERATION OF A PARAMETRIC SORT: THE PROGRAM LOADS CLEAN AND THE CALL DIES `OperationBodyMissing`. Measured 2026-10-10 on 5273d5a2 and on 5ba58df5; found while writing a fixture for WI-20261008-JMMHQ.

THE PROGRAM. `sort Box` with `sort V = ?`, `entity mk(v: V)`, `operation peek(b: Box[V]) -> V = b.v`, `operation open(b: Box[V]) -> V` and `rule open(?b) <=> peek(?b) @[simp]`; in another namespace `operation go() -> Int64 =` / `let b = Box.mk(4)` / `Box.open(b)`. It loads with no diagnostic and `go()` fails `OperationBodyMissing { name: "…Box.open" }`. The same with the sort written `sort Box[V]`. The twin with `entity mk(v: Int64)` and no parameter runs to 4. kernel-language.md §5.3: the `@[simp]` tag is what makes a body-less operation's defining equation run.

MECHANISM, measured by printing the verdict in `simp_fire_guard_holds` (typing/value_type.rs). `lookup_spec_op_dispatch` answers that `Box.open` is a spec operation of `Box` — an operation of a PARAMETRIC sort is one (`spec_op_parent_sort`, WI-210) — the carrier argument's sort is `Box`, and the guard asks whether that sort provides the spec: whether `Box` provides `Box`. It does not, so an equation with a value right-hand side does not fire. For the unparameterized sort the functor is no spec operation and the guard is not asked. WI-714 met the same wall for `Relation` (`sort_provides(Relation, Relation)` is false) and went round it for a macro-headed right-hand side only.

WHAT. Decide what `Box` is here. A sort with constructors that nothing provides is a data sort that takes parameters, not a spec, and its equation is a definition: the guard should not ask for a provision there, or should hold where the carrier IS the sort the rule is written in. WI-20261003-4DYR6 is the other side of the same identification (a spec with no parameter is not dispatched as one); deciding what a spec is there may settle this and may not — its first option widens what counts as a spec and does not narrow it. WI-885 (a `@[simp]` equation is a backing kind no predicate sees) and WI-20260909-M8QWJ (an operation with nothing to run loads clean) are why nothing names the gap before the call.

CONTROL. The program as a row asserting 4: fails on the tree before. The unparameterized twin passes either way. A spec's law over a carrier that does not provide the spec stays unfired — `simp_fire_guard_holds`' own rows.


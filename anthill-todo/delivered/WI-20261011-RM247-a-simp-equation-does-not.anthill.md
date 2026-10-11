## Attributes

- id: WI-20261011-RM247-a-simp-equation-does-not
- created: 2026-10-11T05:28:01Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-11T06:16:45Z

- acceptance: cargo-test

- tags: typing

## Description

A `@[simp]` EQUATION DOES NOT DEFINE A BODY-LESS OPERATION OF A PARAMETRIC SORT: THE PROGRAM LOADS CLEAN AND THE CALL DIES `OperationBodyMissing`. Measured 2026-10-10 on 5273d5a2 and on 5ba58df5; found while writing a fixture for WI-20261008-JMMHQ.

THE PROGRAM. `sort Box` with `sort V = ?`, `entity mk(v: V)`, `operation peek(b: Box[V]) -> V = b.v`, `operation open(b: Box[V]) -> V` and `rule open(?b) <=> peek(?b) @[simp]`; in another namespace `operation go() -> Int64 =` / `let b = Box.mk(4)` / `Box.open(b)`. It loads with no diagnostic and `go()` fails `OperationBodyMissing { name: "…Box.open" }`. The same with the sort written `sort Box[V]`. The twin with `entity mk(v: Int64)` and no parameter runs to 4. kernel-language.md §5.3: the `@[simp]` tag is what makes a body-less operation's defining equation run.

MECHANISM, measured by printing the verdict in `simp_fire_guard_holds` (typing/value_type.rs). `lookup_spec_op_dispatch` answers that `Box.open` is a spec operation of `Box` — an operation of a PARAMETRIC sort is one (`spec_op_parent_sort`, WI-210) — the carrier argument's sort is `Box`, and the guard asks whether that sort provides the spec: whether `Box` provides `Box`. It does not, so an equation with a value right-hand side does not fire. For the unparameterized sort the functor is no spec operation and the guard is not asked. WI-714 met the same wall for `Relation` (`sort_provides(Relation, Relation)` is false) and went round it for a macro-headed right-hand side only.

WHAT. Decide what `Box` is here. A sort with constructors that nothing provides is a data sort that takes parameters, not a spec, and its equation is a definition: the guard should not ask for a provision there, or should hold where the carrier IS the sort the rule is written in. WI-20261003-4DYR6 is the other side of the same identification (a spec with no parameter is not dispatched as one); deciding what a spec is there may settle this and may not — its first option widens what counts as a spec and does not narrow it. WI-885 (a `@[simp]` equation is a backing kind no predicate sees) and WI-20260909-M8QWJ (an operation with nothing to run loads clean) are why nothing names the gap before the call.

CONTROL. The program as a row asserting 4: fails on the tree before. The unparameterized twin passes either way. A spec's law over a carrier that does not provide the spec stays unfired — `simp_fire_guard_holds`' own rows.

## Changes

### 2026-10-11T06:16:44Z — feedback — claude

DELIVERED. A BODY-LESS OPERATION OF A DATA SORT IS NOT A DISPATCHED SPEC OPERATION, with a type parameter or without. `lookup_spec_op_dispatch` (typing/call_class.rs) answers nothing where the declaring sort has constructors (`sort_is_data`): nothing provides a data sort (kernel-language.md §5.1), so there is no provider to dispatch to and the operation is the sort's own. The ticket's program runs to 4 in both spellings of the parameter.

WHERE, AND WHY NOT AT THE GUARD — three placements, each measured over the full workspace. (1) The guard alone (`simp_fire_guard_holds` holding for a data sort): operation bodies run, and a rule body that calls the operation is still refused at load — 'Box provides no Box … Add a provides Box[…]', advice no program can follow — by `check_occ_spec_op_requirements`, another reader of the same answer. (2) The shared leg `sort_is_parametric`, which all three spec-operation gates read: three rows of wi_hzvqa_alias_receiver_test lose a load refusal, because the rule-body walk is triggered by that leg (`spec_op_call_parent`) and stops checking the arguments of a data sort's operations. (3) The body-less half alone — delivered: nothing fails but two tests that state how the gates relate, restated (wi1043 the_walk_gate_is_the_two_halves_and_a_data_sorts_body_less_operations, on a fixture of its own; the oracle of wi1042 the_shared_gate_agrees_with_the_wi444_spelling). In the library the reclassified operations are Pair.fst and Pair.snd.

WHAT ELSE MOVES, measured against e5efe908. A caller generic in the content (`at[X](b: Box[V = X]) = Box.open(b)`) and a lambda binder with no written type were refused for a missing `requires Box[V = …]`; both run. A rule body calling the operation — defined by an equation, or backed by clauses (`rule open(mk(v: ?v), ?v) :- true`) — was refused for a `provides Box[…]`; it loads and answers as the same sort without its parameter does. An operation with no parameter of the sort (`zero()`) and one taking only the content (`same(v: V)`) are defined too. In the resolver such an operation with nothing to run is now 'no implementation' rather than 'a provider's only', as the plain sort's is.

CONTROLS, wi_rm247_data_sort_equation_test, 20 rows. With the leg backed out 16 fail: 11 die OperationBodyMissing, 2 are refused for `requires Box[V = …]`, 3 for `provides Box[…]`. The plain twin, a host-backed operation and two spec rows pass with it backed out; the two spec rows fail with the leg widened to every parametric sort, each loading clean with its law fired.

NOT DONE HERE. The defaulted half, `spec_op_parent_sort`, eval's value-directed dispatch, the loader's `enclosing_is_spec` and the reading in `requires` still call a sort with a parameter and constructors a spec — WI-20261003-4DYR6.

FOUND ON THE WAY, on e5efe908 for a sort with no parameter, NOT FIXED, no ticket filed. (a) A rewrite hides an ill-typed call: with `rule open(?b) <=> 0 @[simp]`, `Box.open("s")` loads and runs to 0 — the typer fires a rewrite before it checks the call it replaces. With this change the parametric sort does the same; while its rule could not fire the call was refused (`open.b (op-arg): expected Box[V = ?_], got String`). (b) A constructor applied on an equation's right-hand side — `rule wrap(?v) <=> mk(?v) @[simp]`, and `<=> some(?v)` on an operation at namespace level — loads and dies `unknown operation: …Box.mk` when the rewritten body runs: the right-hand side is spliced as an application, which the typer accepts and eval does not construct. (c) A body-less operation backed by clauses (`rule full(mk(v: ?v)) :- true`) answers from a rule body and dies OperationBodyMissing from an operation body, with a message that says no rule clause is indexed under it.

GATE on e5efe908 with this change: rustland/scripts/test.sh, full: 36 binaries, 9108 passed, 0 failed, 14 ignored. /code-review run. No spec text changed; scaland has no typer and nothing mirrors this.

### 2026-10-11T06:26:50Z — feedback — claude

FOLLOW-ON, 2026-10-11, after a4f007ad: (b) above is FIXED for a constructor applied on a right-hand side. Eval reads a constructor-headed application as the construction it is (eval/eval.rs, beside its sort-headed and rule-headed arms — the typer's `is_entity_constructor` arm already did): `rule wrap(?v) <=> mk(?v) @[simp]` runs, by position or by field name, for the plain sort, a library constructor, a constructor under another, and a free-standing entity. Six rows in wi_rm247_data_sort_equation_test; five fail with the arm backed out, each loading clean and dying UnknownOperation on the constructor, and the row for a constructor with no field passes either way. STILL OPEN under (b), measured with the arm in place, no ticket filed: a constructor that shares its sort's name (`sort E { entity E(n: Int64) }`, `<=> E(n: ?v)`) is refused at load, read as E applied to type arguments; a tuple on the right-hand side (`<=> (?a, ?a)`) loads clean and dies in eval, 'unhandled Expr variant' — the tuple node of a rule's text; and the C++ and Rust generators read the rewritten bodies with no reading for a constructor-headed application. (a) and (c) are as written above. GATE on a4f007ad with the arm: rustland/scripts/test.sh, full: 36 binaries, 9114 passed, 0 failed, 14 ignored. /code-review run.

### 2026-10-11T06:33:56Z — feedback — claude

DECIDED AND FILED, 2026-10-11, after fb862725. (a) STANDS: asked 'should a rewrite be allowed to fire on a call that would not type-check?', the user answered yes — the rewrite replaces the call and what is checked is the text it leaves, so `Box.open("s")` under `rule open(?b) <=> 0 @[simp]` running to 0 is not a defect, for the plain sort or the parametric one. SPEC: §5.3 has one paragraph saying an operation of a sort with constructors is the sort's own whether or not the sort takes parameters (agreed). FILED, the two that die in eval: the tuple on a right-hand side as WI-20261011-3HN0N, the clause-backed operation called from an operation body as WI-20261011-CR6GD. NOT FILED: a constructor that shares its sort's name refused at load on a right-hand side, and the generators' reading of a rewritten body.


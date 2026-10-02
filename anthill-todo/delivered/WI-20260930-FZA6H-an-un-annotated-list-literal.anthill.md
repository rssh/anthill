## Attributes

- id: WI-20260930-FZA6H-an-un-annotated-list-literal
- created: 2026-09-30T09:10:23Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-30T20:43:25Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

AN UN-ANNOTATED LIST LITERAL OVER A GENERIC CALL WHOSE ANSWER HOLDS A VALUE PANICS THE LOADER. `sort Foo { sort T = ?; sort N = ?; entity foo(v: T) }`, `operation mk(x: Int64) -> Foo[T = Int64, N = 3] = foo(v: x)`, `operation wrap[A](x: A) -> Option[T = A] = some(x)`, `operation go() -> Int64 = let xs = [wrap(mk(1))]` then `1`: `anthill load` panics "expect_term: expected a hash-consed Value::Term, got Value::Entity" (eval/value.rs:491) — a panic in release too. MEASURED on the build after WI-20260929-0RP29 and on the release build before it, identically. The `N = Bool` twin loads, and so does the annotated `let xs: List[T = Option[T = Foo[T = Int64, N = 3]]] = [wrap(mk(1))]`. MECHANISM (traced by WI-20260929-0RP29's /code-review): the call's return is σ-resolved by `resolve_type_deep_value` (typing/apply.rs ~1909), whose `splice_non_term_bindings` rebuilds `Option[T = A]` around `A` bound to the occurrence-carried `Foo[…, N = 3]` through the goal-world `fn_value` — as a `Value::Entity` spine, which no type builder takes; `TypeResult.ty` carries it un-normalized (apply.rs ~3995); the list literal's element type (typing/constructor.rs ~360) reaches `seq_literal_type` → `parameterized_value` (constructor.rs ~432), whose `type_children` term branch calls `expect_term` on it. The same builders are reached from type_ctor.rs ~654/668, visit.rs ~1455 and relation.rs ~1277. FIX: rebuild the σ splice through the carrier-choosing type builders (a type application is `parameterized_value`, not `fn_value`), or accept an entity at the builders' intake (`type_children` / `value_to_type_child_at`) by rebuilding it — then retire the local lowerings that paper over it (`spliced_type_child`, projection.rs `child_type_value`'s entity arm). ACCEPTANCE: the program loads and `go` runs, as its `N = Bool` twin does; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-09-30T20:43:18Z — feedback — user

DELIVERED with WI-20260929-0RP29's fourth fix pass, by the FIX's second route: the type builders ACCEPT an entity-carried type at their intake — type_children and value_to_type_child (typing/result.rs) convert one through entity_type_on_builders, moved from projection.rs to result.rs as the builders' one owner (its spec view lowered by lower_spec_view, shared with eliminate_spec_view). The local lowerings that papered over it are retired: projection.rs child_type_value's entity arm delegates to that owner (type_child_value), and spliced_type_child no longer lowers an entity to a term. The same conversion fixed the branch join and meet (combine_parameterized_same_base / meet_parameterized_same_base), which had started panicking on this very carrier in the third fix pass. The ticket's program runs: go answers 1, as its N = Bool twin does (wi_0rp29_nested_projection_value_in_type_test::a_list_literal_over_a_type_holding_a_value_loads — with the intake conversion backed out it and the join/meet rows fail, panicking). The σ splice itself (splice_non_term_bindings -> fn_value) still builds the entity; the FIX's first route — building it through the type builders — was not taken. Full workspace green via rustland/scripts/test.sh.


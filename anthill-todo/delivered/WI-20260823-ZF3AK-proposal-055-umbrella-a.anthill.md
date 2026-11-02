## Attributes

- id: WI-20260823-ZF3AK-proposal-055-umbrella-a
- created: 2026-08-23T09:39:39Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-02T10:34:03Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260824-WAHB6-classify-a-nominal-type-once, WI-20260824-Q0093-every-operation-expression, WI-20260824-PAPX0-decide-and-encode-the-dot, WI-20260824-JM6ZW-retire-the-expectation

- tags: proposal-055

## Description

Proposal 055 umbrella A — RESOLVED NOMINAL TYPE VALUES THROUGH THE OPERATION-EXPRESSION PIPELINE. Implement docs/proposals/055-types-in-value-position.md §2 and docs/design/055-implementation.md §§1–4, 8–10 for typed expressions: classify a bare sort, in-scope type parameter, or sort-headed bracket application exactly once after name resolution as an explicit TypeValue; expected Type validates or infers but never classifies; carry the resolved distinction through every genuine operation ValueExpression occurrence (positional/named arguments, operation result, let value/continuation, if condition/branches, match scrutinee/guard/body, lambda body, collection/set/tuple elements, parenthesized/infix/prefix operands, bounded-quantifier collection, proof/metadata values). Preserve outer heads, typed callees op[T](...), Sort(...) constructors, binders, patterns, labels, member names and TypeExpr positions. Decide and encode the sort-companion versus Type-value dot receiver split; ambiguity is loud, never lookup-order fallback. ACCEPTANCE: operation t() -> Type = Cell[Int64] evaluates to the canonical type term; unannotated let and generic id infer Type; a collection of nominal types is driven and evaluated; a String/Bool destination rejects with expected ..., got Type naming the denoted sort; bare and applied variants work; constructor/callee/head/binder controls retain their old meaning; WI-206/WI-707/WI-708/WI-709 controls remain green; tests state which fail on back-out and which controls pass either way; full Rust workspace passes via rustland/scripts/test.sh. This is an umbrella: split reviewable subtickets under it if implementation measurement proves necessary, but preserve this end-to-end acceptance boundary.

## Changes

### 2026-11-02T10:34:02Z — feedback — claude

DELIVERED — umbrella A's end-to-end acceptance checked on the tree. Every part is delivered (WI-20260824-WAHB6, WI-20260824-Q0093, WI-20260824-PAPX0, WI-20260824-JM6ZW), and the one clause no part drove for a nominal type is driven now.

THE CLAUSE: "a generic `id` infers `Type`" (proposal 055 §2: `idT[T](x: T)` infers `T = Type` as `idT(5)` infers `T = Int64`). Only a sort named by a dotted path had a row (`wi_rxt6s_dotted_sort_type_value_test`). New file `rustland/anthill-core/tests/include/wi_zf3ak_umbrella_a_acceptance_test.rs`, 5 rows: `idT(Cell)`, `idT(Cell[V = Int64])`, `idT(Cell[Int64])`, an unannotated `let u = idT(Cell[Int64])` and a list of two `idT` results evaluate to the type terms (the positional one keyed by `V`); `sz(idT(Cell))`, `sz(idT(Cell[V = Int64]))` and `if idT(…) then …` are refused `expected String, got Type` / `expected Bool, got Type`; an unannotated `let u = Cell[Int64]`, `let u = Cell` and `let u = idT(…)` meet `sz(u)` as `Type`; `idT[T = Type](Cell[V = Int64])` runs and `idT[T = String](Cell)` / `(Cell[V = Int64])` are refused naming the sort. Control: `sz(idT(5))` is `expected String, got Int64`, `sz(idT("s"))` loads. The file's header says where every other acceptance clause is pinned.

BACK-OUT, measured in a one-file binary: both loader predicates forced `false` (WAHB6's back-out) for the fixture's programs fail 4 rows, as `UnclassifiedTypeValue`; the control row passes. A switch over every load no longer measures these rows: the stdlib's own bodies hold type values (`anthill.reflect.TypeValuePattern`), so it refuses the stdlib first.

QUESTION FOR THE USER, measured, not changed: the wrong-destination message names the sort for a written type and not for a let-bound name — `sz(Cell[Int64])` is `got Type (Cell[Int64])`, `let u = Cell[Int64]` then `sz(u)` is `got Type`. `denoted_type_value`'s doc (Q0093, 2026-09-07) decided a variable denotes nothing at its position; kernel-language §5.4 (PAPX0, later) says a name a `let` bound to a written type denotes that sort, and the dot reads it so. Through a call (`sz(idT(Cell))`) both agree: no sort. The rows assert the call case only.

/code-review (xhigh): 4 findings; 3 fixed (the two assertion helpers moved to `tests/common`, shared with the Q0093 matrix; the let destination row; the applied face of the Bool and typed-callee rows), the let-bound message is the question above. No language, spec or production code changed. Full workspace via `rustland/scripts/test.sh`: 11,478 passed, 0 failed, 17 ignored. scaland `sbt testFull`: 51 + 797 passed, 0 failed (no Scala file changed). Umbrellas B (WI-20260823-53W12) and C (WI-20260823-Z9HJ2) no longer wait on this one.


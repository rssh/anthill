## Attributes

- id: WI-20260823-ZF3AK-proposal-055-umbrella-a
- created: 2026-08-23T09:39:39Z

- status: Open
- status_agent: user
- status_at: 2026-08-23T09:39:39Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-055

## Description

Proposal 055 umbrella A — RESOLVED NOMINAL TYPE VALUES THROUGH THE OPERATION-EXPRESSION PIPELINE. Implement docs/proposals/055-types-in-value-position.md §2 and docs/design/055-implementation.md §§1–4, 8–10 for typed expressions: classify a bare sort, in-scope type parameter, or sort-headed bracket application exactly once after name resolution as an explicit TypeValue; expected Type validates or infers but never classifies; carry the resolved distinction through every genuine operation ValueExpression occurrence (positional/named arguments, operation result, let value/continuation, if condition/branches, match scrutinee/guard/body, lambda body, collection/set/tuple elements, parenthesized/infix/prefix operands, bounded-quantifier collection, proof/metadata values). Preserve outer heads, typed callees op[T](...), Sort(...) constructors, binders, patterns, labels, member names and TypeExpr positions. Decide and encode the sort-companion versus Type-value dot receiver split; ambiguity is loud, never lookup-order fallback. ACCEPTANCE: operation t() -> Type = Cell[Int64] evaluates to the canonical type term; unannotated let and generic id infer Type; a collection of nominal types is driven and evaluated; a String/Bool destination rejects with expected ..., got Type naming the denoted sort; bare and applied variants work; constructor/callee/head/binder controls retain their old meaning; WI-206/WI-707/WI-708/WI-709 controls remain green; tests state which fail on back-out and which controls pass either way; full Rust workspace passes via rustland/scripts/test.sh. This is an umbrella: split reviewable subtickets under it if implementation measurement proves necessary, but preserve this end-to-end acceptance boundary.

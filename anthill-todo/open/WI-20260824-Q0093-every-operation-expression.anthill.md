## Attributes

- id: WI-20260824-Q0093-every-operation-expression
- created: 2026-08-24T05:04:43Z

- status: Open
- status_agent: user
- status_at: 2026-08-24T05:04:43Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260824-WAHB6-classify-a-nominal-type-once

- tags: proposal-055

## Description

EVERY OPERATION-EXPRESSION OCCURRENCE ADMITS A NOMINAL TYPE VALUE (proposal 055 umbrella A, step 2 -- the §3 matrix).

After WI-20260824-WAHB6 records the classification, make every child whose grammar/IR role is `ValueExpression` in an OPERATION EXPRESSION consume it, and pin the adjacent non-value role at each family. docs/design/055-implementation.md §3 owns the list; the fact / rule-body / metadata-of-declaration halves belong to umbrella B (WI-20260823-53W12), the dot receiver to its own ticket.

FAMILIES (each needs its own row): positional and named call/constructor arguments; operation result; `let` value and continuation; `if` condition, then, else; `match` scrutinee, branch guard, branch body; lambda body; collection, set and tuple element values including named-tuple values; parenthesized expression and infix/prefix operands; bounded-quantifier collection; `proof` conclude goal and continuation body; metadata values.

PER FAMILY, per design §9: (1) a DRIVING test that resolves or evaluates the expression and asserts the resulting `Type` value -- not that the file loads; (2) a negative destination (`String` / `Bool` where the family admits one) rejecting with `expected ..., got Type` naming the denoted sort; (3) a CONTROL pinning the adjacent non-value role -- head, callee, pattern, binder, label, member name, metadata key, `TypeExpr` child -- unchanged or loudly refused; (4) bare AND applied nominal variants; (5) at least one logical-variable argument where the type stays non-ground.

MEASURED, and it shapes the estimate: the typer walk is uniform. Bare names funnel through `check_bare_ref` at `typing.rs:10461` / `10473` / `10488` and a sort-headed application through the single Apply arm at `typing.rs:10512`, so the expectation is that this is mostly a TEST increment over WAHB6's record. ANY family that turns out to need a code arm of its own is the finding of this ticket and must be stated at that arm's site -- do not absorb it silently into "the matrix".

ACCEPTANCE (from the umbrella): `operation t() -> Type = Cell[Int64]` evaluates to the canonical type term; an unannotated `let` and a generic `id` infer `Type`; a collection of nominal types is driven and evaluated; a `String` / `Bool` destination rejects with `expected ..., got Type` naming the denoted sort; constructor, callee, head and binder controls retain their old meaning. Tests state which rows fail on back-out and which pass either way by design. Full Rust workspace via rustland/scripts/test.sh.

The matrix may ship in two commits if it runs long, but the ticket closes only with every family covered -- a partial matrix reads as "covered everything" to the next reader, so any family deliberately left out must be named in the delivery note with its reason.

## Changes

### 2026-08-24T05:55:30Z — feedback — user

SCOPE NOTE FROM WI-20260824-WAHB6's DELIVERY -- read its feedback before starting.

The widening does NOT arrive family by family. WAHB6 classifies at the loader, unconditionally, so every ValueExpression position stopped depending on the expected sort at once. This ticket therefore PINS the widening per family rather than delivering it: the driving test, the negative destination and the adjacent-role control are the deliverable, and a family that needs a CODE arm of its own is the finding to report at that arm's site.

ALREADY COVERED by `wi_wahb6_type_value_classification_test`, so do not re-file these as new rows: operation result (bare and applied), `let` value and continuation (unannotated -- the position with no expected sort at all), a type ARGUMENT inside a type application, the eponymous-constructor control, and the local-shadows-a-sort control. Everything else in design §3's operation-expression list is open.

ONE MEASURED ASYMMETRY TO CARRY: a bare STANDALONE ENTITY is deliberately still on its old arms (`check_bare_ref`'s `is_free_standing_entity` arm and its eval twin) -- see `bare_name_denotes_type`'s doc for why the predicate cannot be asked at load time. Its rows belong here, and if the matrix needs it classified, moving it needs a point that can answer `is_free_standing_entity` reliably.


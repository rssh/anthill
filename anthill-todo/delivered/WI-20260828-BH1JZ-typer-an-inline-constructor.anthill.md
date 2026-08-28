## Attributes

- id: WI-20260828-BH1JZ-typer-an-inline-constructor
- created: 2026-08-28T15:35:04Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-28T16:15:20Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

typer: an INLINE constructor application whose only consumer is a SPEC-OP CALL does not ground its own sort params. MEASURED MATRIX, stdlib carriers, four rows that bracket it exactly: (1) `operation probe(xs: List[T = Int64]) -> MappedStream[Source = List[T = Int64], Src = Int64, T = Int64, ES = {}, EF = {}] = mapped(xs, inc)` — CLEAN, the declared return pins every param; (2) the same construction consumed by `Stream.splitFirst(mapped(xs, inc))` — REFUSED with `Stream.splitFirst.dispatch: expected matching impl for per-call bindings, got no impl matches`; (3) consumed by `FiniteCollection.collect(mapped(xs, inc))` — REFUSED with `undeclared effect ??_`; (4) the SAME witness consumer fed an ALREADY-TYPED carrier (`operation probe(m: MappedStream[Source = List[T = Int64], …]) = FiniteCollection.collect(m)`) — CLEAN. So neither the construction nor the witness is broken on its own; what is missing is grounding the construction's params when the only thing downstream is a spec-op call, which cannot pin them the way a declared type does. NOT the shapes already ruled out, each by its own measurement: not the arrow/transform row (WI-20260828-8Q0Q5 fixed that, and row 3 still fails with an inline `lambda` in place of `inc`); not transitive provision (a hand-written carrier providing the spec through an intermediate is CLEAN in the same shape); not a missing provision reader for a concrete carrier into a spec-typed field (the hand-written analogue of exactly that shape is CLEAN). LOW IMPACT, stated so it is not over-prioritised: the stdlib never writes the failing spelling — `xs.map(f)` resolves `FiniteCollection.map`, whose declared return pins every param, which is row 1. It bites a USER writing the combinator by hand. Surfaced by WI-590, whose test file documents the bracket at wi590_conditional_finiteness_test's header and works around it by naming the carrier in the probe's signature.

## Changes

### 2026-08-28T16:15:26Z — feedback — user

DELIVERED — the headline program type-checks, and the diagnosis in the ticket's own description was WRONG about the mechanism.

WHAT IT ACTUALLY WAS. Not 'an inline construction's params are grounded by nothing when the consumer is a spec-op call' — the consumer was never the axis. `bare_spec_arg_provision_projection`, the reader that rebuilds a carrier argument as the spec its field declares, answered for exactly ONE shape: a receiver spelled BARE whose sort provides the spec DIRECTLY. Two independent departures were declined, and the miss was SILENT — the caller falls back to the raw type, `unify_types` of `List[T = Int64]` against `Iterable[C = ?_, Element = ?_, E = ?_]` answers TRUE while binding nothing, and the constructed carrier's params (INCLUDING the sibling arrow field's row) stay free, surfacing far away as `undeclared effect ??_`.

THE 2x2, measured on unmodified code, because the first fixture CONFOUNDED the axes (the carrier that worked was both direct AND unparameterized):
                | direct provision | transitive provision
  bare receiver | clean            | LEAKED
  written args  | LEAKED           | LEAKED
Only the conjunction worked, so both axes had to move.

THREE EDITS, one reader. (1) the direct view falls back to `transitive_provision_view`, which already composes exactly this and whose own doc names List-through-Stream as its case. (2) the receiver test accepts a written application (`xs: List[T = Int64]`), RESTRICTED to concrete carriers — the first cut accepted any parameterized view and broke MappedStream.splitFirst's own body, binding `Source` to the spec `Stream` instead of the tail's carrier. (3) a written type argument overrides the receiver projection in σ; threading `xs.T` left the sibling arrow field demanding `xs.T -> ?_` against `Int64 -> Int64`, a mismatch between two spellings of one type.

AND A FOURTH, which is the one the witness needed: the spec's CARRIER param binds to the RECEIVER's own type, not to what the provision writes there. A self-referential provision spells it with the sort's own name (`Stream provides Iterable[C = Stream, …]` — `C = Self`), and composing through a hop substitutes the intermediate's PARAMS, not that self-reference, so it survived literally: the construction inferred `MappedStream[Source = Stream, …]` and the finiteness witness asked whether the SPEC Stream is a FiniteCollection. Joined by VarId and not by Symbol — the first attempt compared symbols and changed nothing, because the two scopes mint different symbols for one param.

SOUNDNESS RE-MEASURED, not inherited: this change grounds the very parameter the witness gate reads, so it could have made an infinite source collectable. It does not, and that row is in the test for exactly that reason.

NOT CLOSED, spun out as WI-20260828-EKWDC: the description's row (2), `Stream.splitFirst(mapped(xs, inc))`, is still refused — but by a DIFFERENT mechanism this fix revealed rather than caused. The receiver's type is now fully ground; what fails is MappedStream's own `requires Iterable[…]` reaching the call site in its DECLARED params, uninstantiated. That is requirement forwarding, not carrier-argument projection.

Tests: wi_bh1jz_carrier_arg_projection_test — 6 rows, per-row back-outs stated at each site. rustland/scripts/test.sh green — 36 binaries, 5975 passed, 0 failures. scaland sbt test green — 544 passed, 0 failures.


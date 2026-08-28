## Attributes

- id: WI-20260828-RJX44-typer-dot-dispatch-and
- created: 2026-08-28T08:49:28Z

- status: Open
- status_agent: user
- status_at: 2026-08-28T08:49:28Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

Typer: DOT DISPATCH and QUALIFIED dispatch disagree about the effect row of a TRANSITIVELY-provided spec op. Same op, same receiver, same context — the qualified spelling grounds the row and the dot spelling leaks `?_`.

MEASURED against the stdlib (with WI-590's consolidation applied so the receiver's static type is the concrete carrier):
  * `length(takeN(Iterable.iterator(FiniteCollection.map(xs, inc)), 1000))`  -> OK
  * `length(takeN(xs.map(inc).iterator(), 1000))`                            -> `type mismatch in <op>.effects (op-effects): expected declared: [], got undeclared effect: ?_`
Both call `Iterable.iterator` on the same `MappedStream` value. Ascription is NOT the variable: `xs.map(inc).iterator()` ascribed to `Stream[T = Int64, E = {}]` by a declared return ALSO fails, and the qualified form succeeds unascribed. The separator is dot-vs-qualified, nothing else.

WHY IT IS REACHABLE ONLY NOW: the receiver must be a carrier that provides the spec TRANSITIVELY (`MappedStream provides Stream`, `Stream provides Iterable`) AND whose provision writes a VARIABLE row (`{ES, EF}`). On main, `FiniteCollection.map` returns a `FiniteCollection` VIEW, so `.iterator()` resolves through the requires graph instead and never takes this path. WI-590 makes `map` return the concrete carrier, which exposes it. `List` does not expose it either: its `provides Stream[T, {}]` writes a GROUND row.

NOT the same defect as 4812c4c7 (row-tail spelling in `substitute_carrier_params`), which is fixed and green — this reproduces WITH that fix in place. Also not fixable by giving `MappedStream` an explicit `provides Iterable`: WI-495/WI-496 DELIBERATELY deleted exactly those clauses from `List` so Iterable-ness derives transitively, so re-adding them contradicts a delivered decision.

WHERE TO START: `bind_spec_params_from_carrier_param` is NOT reached for (spec = Iterable, carrier = MappedStream) — a trace on that pair printed nothing, so dot dispatch resolves the op somewhere else entirely (`find_spec_op_for_provided_sort`'s transitive spec walk is the likely owner; note `transitive_carrier_for_param` may report the INTERMEDIATE as the effective carrier, so a trace filtered on the concrete carrier will miss it — filter on the SPEC). Compare what the qualified path does with the row at that point; the qualified one demonstrably has the information.

ACCEPTANCE: a dot-dispatched, transitively-provided spec op grounds its effect row identically to its qualified spelling. A test that DRIVES it (both spellings side by side, asserting the same declared row is accepted) plus a stated control naming what fails with the fix backed out. Blocks WI-590's wi614_requires_dot_dispatch_test group (4 tests, one shared fixture op `map_then_iterator_count`).


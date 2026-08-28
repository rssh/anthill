## Attributes

- id: WI-20260828-RJX44-typer-dot-dispatch-and
- created: 2026-08-28T08:49:28Z

- status: Open
- status_agent: user
- status_at: 2026-08-28T08:56:33Z

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

## Changes

### 2026-08-28T08:56:28Z — feedback — user

TITLE FRAMING IS WRONG — corrected by measurement, before anyone acts on it. This is NOT a dot-vs-qualified divergence. The QUALIFIED spelling `Stream.iterator(m)` fails identically. Three spellings on the SAME receiver (a parameter typed `MappedStream[Source = List[T = Int64], Src = Int64, T = Int64, ES = {}, EF = {}]`, WI-590's consolidation applied):

  length(takeN(Iterable.iterator(m), 1000))   -> OK
  length(takeN(Stream.iterator(m), 1000))     -> undeclared effect: ?_
  length(takeN(m.iterator(), 1000))           -> undeclared effect: ?_

So the dot form is not the defect; it merely RESOLVES to `Stream.iterator` — the INTERMEDIATE spec's own member — where the qualified `Iterable.iterator` reaches the outer spec op and grounds. Confirmed by tracing `find_spec_op_for_provided_sort`, which is called with `recv_sort = anthill.prelude.MappedStream` for `iterator`.

THE REAL SUBJECT: `Stream.iterator(s: Stream) -> Stream[T = s.T, E = s.E]` is a SELF-RECEIVER spec op with a RECEIVER-PROJECTED return. On a receiver whose carrier provides Stream with a COMPUTED row (`MappedStream provides Stream[T = T, E = {ES, EF}]`), the projection `s.E` does not ground. It grounds fine where the provision wrote a GROUND row — `List provides Stream[T, {}]` — which is why nothing on main exercises it.

WHAT I RULED OUT, so it is not re-tried:
  * NOT the two-spellings row-tail defect fixed in 4812c4c7 — this reproduces WITH that fix in place.
  * NOT `project_via_provided_spec`'s "effect member projects only from a GROUND provision" guard: a trace on that function never fires for this receiver, so the projection is not even reaching it.
  * NOT the sort-level `requires Iterable[C = Source, …]` on the carrier — added it to a synthetic carrier, both spellings still passed.
  * NOT the witness route (carrier provides a spec that itself `requires` the outer one) — modelled it synthetically, both spellings still passed.
  * A synthetic two-hop model (`Wrap provides Str`, `Str provides Iter`, variable row) does NOT reproduce, in either spelling, even with the above added. Something about the real `Stream`/`Iterable` pair is load-bearing and I did not isolate it — likely that `Stream` is self-receiver with a receiver-PROJECTED return, which my model's `iter(s: Str) -> T` is not. START THERE: give the synthetic intermediate a return of `Str[T = s.T, E = s.E]` shape rather than a bare element.

ACCEPTANCE unchanged in substance but restate it on the real subject: a self-receiver spec op whose return projects the receiver (`s.E`) grounds that projection when the receiver's carrier provides the spec with a computed row. Test must DRIVE it with the QUALIFIED spelling (the dot is a consequence, not the subject) plus a control on a ground-row provision (`List`), which must stay green.


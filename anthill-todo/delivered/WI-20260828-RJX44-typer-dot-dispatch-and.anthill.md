## Attributes

- id: WI-20260828-RJX44-typer-dot-dispatch-and
- created: 2026-08-28T08:49:28Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-28T09:52:25Z

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

### 2026-08-28T09:11:05Z — feedback — user

SCOPE CORRECTED AGAIN, and this time it shrinks to a three-line program on a CLEAN MAIN TREE. Nothing about WI-590, MappedStream, witnesses, transitive provision, or computed rows is required. Reproduced with the stdlib UNPATCHED:

  operation a(xs: List[T = Int64]) -> Int64 =
    length(takeN(Stream.iterator(xs), 1000))       -- FAILS: undeclared effect: ?_
  operation b(xs: List[T = Int64]) -> Int64 =
    length(takeN(Iterable.iterator(xs), 1000))     -- OK
  operation c(xs: List[T = Int64]) -> Int64 =
    length(takeN(xs.iterator(), 1000))             -- FAILS (dot resolves to Stream.iterator)
  operation d(xs: List[T = Int64]) -> Stream[T = Int64, E = {}] =
    Stream.iterator(xs)                            -- OK: an ascription pins it

ROOT CAUSE, traced to the line. `Stream.iterator(s: Stream) -> Stream[T = s.T, E = s.E]` has a RECEIVER-PROJECTED return. Resolving `s.E` reaches the projection chain with the receiver's sort read as `anthill.prelude.Stream` — the PARAMETER's declared type, not the ARGUMENT's — and `Stream` DOES declare `E`, so the first arm returns `ProjResult::Neutral` (typing.rs, the `type_params_of_sort(s).contains(member)` gate just before `project_via_provided_spec`). The neutral is then incurred as the call's effect and can never be discharged, hence `?_`. Instrumented: for this program the projection entry fires only with sort = Stream / LogicalStream / FilteredStream and NEVER with sort = List, so `project_via_provided_spec` — which would map `E` through `List provides Stream[T, {}]` to the ground `{}` — is never reached.

`Iterable.iterator(c: C) -> Stream[Element, E]` works because its return names the SPEC's own params, grounded by ordinary carrier-param binding: no projection is involved. That is the whole difference between (a) and (b).

NARROWER STILL, worth keeping: the RETURN's `s.T` is fine — (d) type-checks, so the element projection grounds. It is specifically the EFFECT-row projection `s.E` that becomes a neutral and then cannot be discharged.

PREVIOUS FRAMINGS ON THIS TICKET WERE BOTH WRONG; the sequence is recorded so nobody re-walks it. (1) "dot vs qualified" — false, the qualified `Stream.iterator(m)` fails too; the dot merely resolves to that op. (2) "needs a carrier providing the spec with a COMPUTED row (MappedStream)" — false, a plain `List` with its GROUND `provides Stream[T, {}]` fails identically. Both were narrowed away by measurement, not argument.

ALSO RULED OUT by measurement, unchanged: not the row-tail defect fixed in 4812c4c7 (reproduces with it in place); not the sort-level `requires` on the carrier; not the witness route; and `project_via_provided_spec`'s ground-row guard is irrelevant because that function is never reached.

FIX DIRECTION: at a CALL SITE the op's receiver-projected effects must be re-keyed to the ARGUMENT (`s.E` -> `xs.E`) and resolved against the argument's type before being incurred. `check_apply_iter` already builds `param_to_arg_sym` / `param_to_arg_head` for exactly this re-key (WI-459/WI-506), so the question is whether the effect projection is resolved to a neutral BEFORE that re-key runs, or the re-key does not cover this position. Start by tracing the order of the two.

ACCEPTANCE: the (a)/(c) programs above load clean and thread `{}`; (b)/(d) stay green as controls; a test that DRIVES it on a CONCRETE receiver with a ground provision (`List`) — no WI-590 machinery needed — plus a stated control. Note this makes the ticket independently valuable: `Stream.iterator`, `Stream.tail` and any other receiver-projected spec op are affected on main today.

### 2026-08-28T09:52:20Z — feedback — user

RESOLVED — and it was a ONE-LINE STDLIB SIGNATURE, not a typer change.

  operation iterator(s: Stream) -> Stream = s                     -- was: element and row UNWRITTEN
  operation iterator(s: Stream) -> Stream[T = s.T, E = s.E] = s   -- now

A bare `-> Stream` hands back a stream carrying no element and no effect row, so a consumer that PAYS the row (`takeN`, declared `effects s.E`) has nothing to read and leaks `?_`. Every sibling on the sort already wrote the projections (`tail(s) -> Stream[T = s.T, E = s.E]`, `splitFirst`'s `B` likewise), so this was the single signature on `Stream` that dropped them. The identity body `= s` makes the projected form exactly as true as the bare one; it just says more.

WHY NOTHING CAUGHT IT: the OTHER route to an iterator, `Iterable.iterator(c: C) -> Stream[Element, E]`, names the SPEC's own params and grounds by ordinary carrier-param binding, so it never needed the projections; and an ASCRIBING call site (`-> Stream[T = Int64, E = {}]`) pins the row itself. Both are now controls in the test, green either way.

CENSUS, because one dropped signature suggests others: grepped every `operation` in stream / finite_stream / logical_stream / iterable whose return is not parameterized. The only remaining ones return `s.T` or `Bool`, which need nothing. `iterator` was the sole offender.

TESTS: rjx44_stream_iterator_row_test.rs — 2 driving cases (qualified and dot, each feeding `takeN` so nothing at the use site pins the row) and 2 controls (the `Iterable.iterator` spelling, and an ascribing return). Reverting the signature turns both driving cases red with `undeclared effect: ?_` and leaves both controls green. Full workspace green, 36 binaries, 3700 tests in anthill-core.

THREE FRAMINGS OF THIS TICKET WERE WRONG BEFORE THIS ONE, and the sequence is the lesson: (1) "dot dispatch and qualified dispatch disagree" — false, the qualified `Stream.iterator(m)` fails too; (2) "needs a carrier providing the spec with a COMPUTED row (MappedStream / WI-590)" — false, a plain `List` with a GROUND `provides Stream[T, {}]` fails identically on an UNPATCHED tree; (3) "a receiver-projected return does not ground against the provision" — false, `Stream.iterator` has no projections in its return at all, which IS the defect. Each was narrowed by measurement, and each narrowing made the repro smaller: from a five-sort WI-590 consolidation to three lines against the shipped stdlib. The typer was never at fault.


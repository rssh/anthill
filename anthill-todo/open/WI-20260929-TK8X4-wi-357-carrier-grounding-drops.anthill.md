## Attributes

- id: WI-20260929-TK8X4-wi-357-carrier-grounding-drops
- created: 2026-09-29T20:16:09Z

- status: Open
- status_agent: user
- status_at: 2026-09-29T20:16:09Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

WI-357 CARRIER GROUNDING DROPS A RECEIVER TYPE ARGUMENT THAT HOLDS A VALUE, SO A WRONGLY TYPED PROGRAM IS ACCEPTED AND FAILS AT RUN TIME. `sort Peek { sort T = ?; operation peek(p: Peek) -> T }`, `sort Holder { sort T = ?; entity holder(x: T); provides Peek[T]; operation peek(h: Holder) -> T = match h case holder(x) -> x }`, and `f(h: Holder[T = Buf[T = Int64, N = 3]]) -> Int64 = Peek.peek(h)` — wrongly typed, `Peek.peek(h)` is a `Buf` — LOADS, and `anthill run` fails "main returned non-Int64 value"; `Peek.peek(h).v` is refused "<unresolved receiver>.v … no such member". The `N = Bool` twin is refused "expected Int64, got Buf[T = Int64, N = Bool]" and its `.v` runs. MEASURED before and after WI-20260929-WBHTM (which closed the direct `Holder.peek(h)` spelling — the unifier now binds the argument's occurrence-carried type — but not this one). MECHANISM: `parameterized_vid_bindings` (typing/carrier.rs) returns `None` for a non-`Term` binding, so `bind_spec_params_from_carrier` never binds `Peek.T` and the unbound return type is filled from the expected type; its doc's claim that the drop "surfaces a LOUD unconstrained" is false here. FIX: lower the binding (`dispatch_type_term`, as `receiver_type_args` does since WBHTM) — but NOT an effect row, which the WI-612 comment (carrier.rs ~1956) relies on this arm dropping; `bind_spec_params_from_carrier` and the unit test `wi470_parameterized_vid_bindings_reads_both_carriers` then take `&mut`. FOUND by WI-20260929-WBHTM's /code-review (V7). ACCEPTANCE: the wrongly typed `f` is refused and `Peek.peek(h).v` runs, both as their `N = Bool` twins; an effect-row control unchanged; full workspace green via rustland/scripts/test.sh.


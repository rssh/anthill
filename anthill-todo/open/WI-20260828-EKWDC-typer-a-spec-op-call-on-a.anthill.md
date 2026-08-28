## Attributes

- id: WI-20260828-EKWDC-typer-a-spec-op-call-on-a
- created: 2026-08-28T16:14:52Z

- status: Open
- status_agent: user
- status_at: 2026-08-28T16:14:52Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

typer: a SPEC-OP call on a value whose carrier declares its own `requires` cannot discharge that requirement when the receiver is an INLINE construction. MEASURED: `Stream.splitFirst(mapped(xs, inc))` with `xs: List[T = Int64]` is refused with `Stream.splitFirst.dispatch: no impl matches — unresolved: Iterable[C = MappedStream.Source, Element = MappedStream.Src, E = MappedStream.ES]`. Read the unresolved requirement: it is spelled in `MappedStream`'s OWN DECLARED PARAMETERS (`MappedStream.Source` etc.), not instantiated at the receiver — even though the receiver's type is now fully ground (`MappedStream[Source = List[T = Int64], Src = Int64, T = Int64, ES = {}, EF = {}]`, verified by wi_bh1jz_carrier_arg_projection_test::the_carrier_param_binds_to_the_receiver_not_to_the_provisions_self_reference). So the defect is that the carrier's `requires` clause is checked in its declaration scope rather than under the receiver's own type arguments; instantiating it would ask whether `List[T = Int64]` provides Iterable, which it does. DISTINCT FROM WI-20260828-BH1JZ, which is DELIVERED and fixed the projection that grounds the construction: this failure is what BH1JZ's fix REVEALED underneath, and it is a different mechanism (requirement forwarding / instantiation at a spec-op call, cf. the WI-821 family) rather than a further gap in carrier-argument projection. NOT the same as the working path: `FiniteCollection.collect(mapped(xs, inc))` is CLEAN, because the witness supplies that op and its own `requires` is discharged against the ground carrier application; `Stream.splitFirst` instead reaches MappedStream's own declared `requires`. ACCEPTANCE: the program above loads clean; the six rows of wi_bh1jz_carrier_arg_projection_test stay green, INCLUDING an_infinite_source_is_still_refused.


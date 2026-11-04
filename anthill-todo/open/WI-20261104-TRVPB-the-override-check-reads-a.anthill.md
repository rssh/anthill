## Attributes

- id: WI-20261104-TRVPB-the-override-check-reads-a
- created: 2026-11-04T06:52:27Z

- status: Open
- status_agent: user
- status_at: 2026-11-04T06:52:27Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

THE OVERRIDE CHECK DOES NOT READ A SPEC OPERATION'S `effects {P.E}` OFF THE PROVISION'S CARRIER. `sort Sp { sort P = ?  requires Strm[C = P]  operation h(s: Self) -> Int64 effects {P.E} }` beside `sort Car { entity car  provides Sp[P = Mem]  operation h(s: Car) -> Int64 effects {Error} = 1 }`, with `Mem provides Strm[C = Mem, E = {Error}]`, is refused "'Car' overrides 'Sp.h' but does not refine it: the override declares effect `Error`, which is not covered by any effect the spec operation declares (effects must not widen)" — at `P = Mem` the spec's row is `{Error}`, which the override's is. A call is charged the override's row as expected: `Sp.h(car)` loads under `effects {Error}` and is refused naming `Error` under `effects {}`. MEASURED on 0eaa2e86 (found while measuring WI-20261103-JGW88's review). MECHANISM, not traced further: `check_override_refinement` (`typing/signature.rs`, effects-⊆) substitutes the provision's bindings into the spec operation's declared atoms (`sigma_subst_type`) and compares each override atom with them by `types_compatible`; no step reads the projection off the bound carrier's provision of `Strm`, as a call's row now is (`resolve_type_deep_value`, JGW88). EXPECTED: loads and runs; an override raising more than `Mem`'s row is refused. OPEN QUESTION for the user: at a provision whose carrier's `Strm` leaves `E` unwritten, is any override row admitted, or is the override refused as the call refuses an unread projection? ACCEPTANCE: rows; back-outs measured; full gate green.


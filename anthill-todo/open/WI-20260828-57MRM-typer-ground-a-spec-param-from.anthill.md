## Attributes

- id: WI-20260828-57MRM-typer-ground-a-spec-param-from
- created: 2026-08-28T06:39:24Z

- status: Open
- status_agent: user
- status_at: 2026-08-28T06:39:24Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

Typer: ground a spec param from a WITNESS provision whose CARRIER KEY IS PARAMETERIZED. A witness keys its carrier as an APPLICATION (`fact FiniteCollection[C = MappedStream[Source = S, Src = Src, T = T, ES = ES, EF = EF], Element = T, E = {ES, EF}]`) and writes its OTHER bindings in its OWN variables (`Element = T`, `E = {ES, EF}` are the WITNESS's T/ES/EF, not MappedStream's). `bind_spec_params_from_carrier_param` grounds a view value via `typaram_ref_vid(value, carrier_sym)` plus `substitute_carrier_params(..., carrier_sym, recv_bindings)`, both keyed on the CARRIER sort's params — neither finds anything inside the witness's variables, the value never becomes ground, and the spec param silently leaks `?_`. An ordinary `provides` never hits this because it keys the BARE carrier, whose bindings are already in the carrier's own params.

SYMPTOM (measured, on a WI-590 consolidation tree): a DERIVED (default-bodied) spec op dispatched through such a witness leaks its effect row. `FiniteCollection.collect` works — the witness SUPPLIES it, so its row comes from that op's own declaration; `size` does NOT: both `xs.map(inc).size()` and the qualified `FiniteCollection.size(FiniteCollection.map(xs, inc))` fail with `type mismatch in <op>.effects (op-effects): expected declared: [], got undeclared effect: ?_`. `foldLeft`/`foldRight` would be the same. `xs.map(f).size()` is wi492's `map_then_size` and an eval_test assertion, so this blocks WI-590.

TRACED, so the search does not restart: `carrier_param_receiver` DOES return a view for `FiniteCollection.size` on a `MappedStream` receiver, and `transitive` is FALSE (no eval deferral) — the view is simply expressed in the wrong variables. Decoded, it is `C = APP MappedStream [(T, T), (Source, S), (Src, Src), (ES, ES), (EF, EF)]`, `Element = T`, `E = <effects row>`. The carrier binding IS the dictionary relating the two namespaces, so inverting it (witness var -> the receiver's type-arg for the carrier slot it fills) and substituting before grounding is the fix direction.

ATTEMPT MADE AND BACKED OUT — read this before repeating it. Adding that inversion+substitution at the top of `bind_spec_params_from_carrier_param`'s binding loop did NOT move `size`, and it BROKE a previously-green case (`length(FiniteCollection.collect(xs.map(inc)))`, which had been fine). Two conclusions: (a) the site that grounds a DERIVED op's declared effect row is somewhere other than that loop — find it first, by instrumenting which arm each binding takes for the failing `size` call; (b) whatever fix lands must apply ONLY where no OVERRIDE supplies the op. `collect` is supplied by the witness sort itself and takes its params from that op's declaration, so substituting corrupted them; only ops with no witness-supplied override need the view re-expressed.

SCOPE: typer only, no stdlib change needed to reproduce — a minimal fixture is a parameterized carrier plus a witness sort with `requires`+`fact` (see rustland/anthill-core/tests/include/wi590_witness_param_carrier_test.rs for the shape; extend it to dispatch a DERIVED spec op, not just the witness-supplied `collect`). ACCEPTANCE: a derived carrier-param spec op dispatched through a parameterized-carrier witness grounds its effect row and its element; a test that DRIVES it (resolve/typecheck the call, not merely load a declaration) plus a stated control naming which rows fail with the change backed out. Full workspace green.

CONTEXT: split out of WI-590 (finiteness Phase D), whose feedback carries the full measurement log. WI-590 also needs the CONSTRUCTION-side twin of the enclosing-`requires` lookup delivered in e9b46fb4 — that half was implemented, verified working, and removed before commit because the only fixture that would drive it also type-checks with the change backed out; it should land with the stdlib work that needs it, and its note about NOT row-wrapping the effect value is in WI-590's feedback.


## Attributes

- id: WI-20260828-57MRM-typer-ground-a-spec-param-from
- created: 2026-08-28T06:39:24Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-28T08:07:15Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

Typer: ground a spec param from a WITNESS provision whose CARRIER KEY IS PARAMETERIZED. A witness keys its carrier as an APPLICATION (`fact FiniteCollection[C = MappedStream[Source = S, Src = Src, T = T, ES = ES, EF = EF], Element = T, E = {ES, EF}]`) and writes its OTHER bindings in its OWN variables (`Element = T`, `E = {ES, EF}` are the WITNESS's T/ES/EF, not MappedStream's). `bind_spec_params_from_carrier_param` grounds a view value via `typaram_ref_vid(value, carrier_sym)` plus `substitute_carrier_params(..., carrier_sym, recv_bindings)`, both keyed on the CARRIER sort's params — neither finds anything inside the witness's variables, the value never becomes ground, and the spec param silently leaks `?_`. An ordinary `provides` never hits this because it keys the BARE carrier, whose bindings are already in the carrier's own params.

SYMPTOM (measured, on a WI-590 consolidation tree): a DERIVED (default-bodied) spec op dispatched through such a witness leaks its effect row. `FiniteCollection.collect` works — the witness SUPPLIES it, so its row comes from that op's own declaration; `size` does NOT: both `xs.map(inc).size()` and the qualified `FiniteCollection.size(FiniteCollection.map(xs, inc))` fail with `type mismatch in <op>.effects (op-effects): expected declared: [], got undeclared effect: ?_`. `foldLeft`/`foldRight` would be the same. `xs.map(f).size()` is wi492's `map_then_size` and an eval_test assertion, so this blocks WI-590.

TRACED, so the search does not restart: `carrier_param_receiver` DOES return a view for `FiniteCollection.size` on a `MappedStream` receiver, and `transitive` is FALSE (no eval deferral) — the view is simply expressed in the wrong variables. Decoded, it is `C = APP MappedStream [(T, T), (Source, S), (Src, Src), (ES, ES), (EF, EF)]`, `Element = T`, `E = <effects row>`. The carrier binding IS the dictionary relating the two namespaces, so inverting it (witness var -> the receiver's type-arg for the carrier slot it fills) and substituting before grounding is the fix direction.

ATTEMPT MADE AND BACKED OUT — read this before repeating it. Adding that inversion+substitution at the top of `bind_spec_params_from_carrier_param`'s binding loop did NOT move `size`, and it BROKE a previously-green case (`length(FiniteCollection.collect(xs.map(inc)))`, which had been fine). Two conclusions: (a) the site that grounds a DERIVED op's declared effect row is somewhere other than that loop — find it first, by instrumenting which arm each binding takes for the failing `size` call; (b) whatever fix lands must apply ONLY where no OVERRIDE supplies the op. `collect` is supplied by the witness sort itself and takes its params from that op's declaration, so substituting corrupted them; only ops with no witness-supplied override need the view re-expressed.

SCOPE: typer only, no stdlib change needed to reproduce — a minimal fixture is a parameterized carrier plus a witness sort with `requires`+`fact` (see rustland/anthill-core/tests/include/wi590_witness_param_carrier_test.rs for the shape; extend it to dispatch a DERIVED spec op, not just the witness-supplied `collect`). ACCEPTANCE: a derived carrier-param spec op dispatched through a parameterized-carrier witness grounds its effect row and its element; a test that DRIVES it (resolve/typecheck the call, not merely load a declaration) plus a stated control naming which rows fail with the change backed out. Full workspace green.

CONTEXT: split out of WI-590 (finiteness Phase D), whose feedback carries the full measurement log. WI-590 also needs the CONSTRUCTION-side twin of the enclosing-`requires` lookup delivered in e9b46fb4 — that half was implemented, verified working, and removed before commit because the only fixture that would drive it also type-checks with the change backed out; it should land with the stdlib work that needs it, and its note about NOT row-wrapping the effect value is in WI-590's feedback.

## Changes

### 2026-08-28T08:06:39Z — feedback — user

DELIVERED as commit 2c44a257. The root cause was NOT "compound rows are unhandled" — it was that a witness's head is read in the WRONG NAMESPACE, and a name coincidence was hiding it.

REPRODUCED self-contained first (no stdlib consolidation needed), with controls that separate the axes: a carrier-param spec with one PRIMITIVE op the witness supplies and one DERIVED (default-bodied) op; a parameterized carrier; a witness. Four measurements: bare row + primitive OK; bare row + derived OK; compound row + primitive OK; compound row + derived FAILS. Then the decisive one — RENAME the witness's row parameter so it no longer shares the carrier's short name, and the BARE row + derived case fails too. So the bare case had only ever worked because witness and carrier happened to spell the parameter `ES` identically.

TRACED to the exact terms. A witness `fact` is a TEMPLATE over the witness sort's own binder, and one parameter has TWO SPELLINGS depending on position: in a type-argument slot it is `Ref(parameter symbol)` (`Wrap[ES = ES]`), inside an effect ROW it is the bare `Var(Global(vid))` a row tail carries (`{ES, EF}` lowers to `merge[open[tail = Var], open[tail = Var]]`, both tails anonymous, name `_`). Dumped: the witness sort's parameters are `S -> Var(Global 118), T -> Var(Global 119), ES -> Var(Global 120), EF -> Var(Global 121)` and the two row tails were exactly `Var(Global 121)` / `Var(Global 120)`. The identity was present all along; `bind_spec_params_from_carrier_param` was looking it up via `typaram_ref_vid(value, CARRIER)` — by short name, against the wrong sort. Named leaves resolved only on a name collision; row leaves never resolved, so `substitute_carrier_params` returned a non-ground value and the param was skipped.

FIX: match the fact's CARRIER BINDING against the receiver's type to obtain σ over the WITNESS's parameters, then apply σ to the rest of the head. σ is keyed on the witness's VarId so both spellings resolve. Gated on the carrier binding being an APPLICATION of the carrier (the witness signature) so an ordinary `provides` never reaches the provider scan; the witness is selected by the same iterator/filter/find-predicate `provision_binds_param_to_carrier`'s witness arm uses, so σ cannot come from a different binder than the view did.

SOUNDNESS, raised by the user mid-implementation and it changed the code: NEVER join by short name. A head may write another sort's parameters into the slots and may PERMUTE them (`Alg[T = X.S, S = X.T]`); comparing last segments pairs `X.S` with the witness's `S` and silently INVERTS the permutation. Both resolvers now go through `type_param_vid_in_sort` (symbol identity). The same correction was applied to WI-590's `enclosing_requires_licensing_clause`, where one false match would grant a licence AND bind a wrong rigid together.

REVIEW caught a real regression the effect-row tests could not: an instantiated binding IS the receiver's type-arg, so running it through the carrier-keyed classification DROPPED it, and a `String` was accepted where the witness pins `Element = Int64` (the un-instantiated read had refused it). Every effect-row fixture pins `Element` through its declared return, so only the row was ever driven. A rewritten GROUND value is now bound directly, and `refuses_a_wrong_element_type_through_an_instantiated_witness` pins it — measured red on its own back-out. Review also found WI-590's licence branch ordered BEFORE `op_requires_covers_call` (skipping WI-1091's dictionary-slot classification when both licences apply) and, in the `NoMatch` arm, falling through to `DispatchNoMatch` instead of returning. Both fixed.

TESTS: wi57mrm_witness_instantiation_test.rs — 2 driving cases, 3 controls, 1 negative. Back out `witness_instantiation` and both driving cases go red with `undeclared effect: ?_` while every control stays green. Full workspace green, 36 binaries.


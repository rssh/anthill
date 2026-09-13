## Attributes

- id: WI-20260913-KXNEX-a-provides-that-leaves-its
- created: 2026-09-13T18:34:43Z

- status: Open
- status_agent: user
- status_at: 2026-09-13T18:34:43Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A `provides` THAT LEAVES ITS SPEC'S CARRIER PARAMETER UNBOUND LOADS CLEAN AND NAMES NO CARRIER — value-directed dispatch then dies `OperationBodyMissing` at the first call, against a provider that DOES implement the operation. Make it a LOAD ERROR.

MEASURED (WI-20260830-7MK73, commit ad00948e). `sort guardians.LiveLlm` declared `operation complete(self: LiveLlm, p: Prompt)` and `provides Llm[E = {External}]`; it loaded. `guardians.summarize(llm, …)`, whose body is `llm.complete(p)`, driven with a `live_llm(…)` value, died `OperationBodyMissing { name: "guardians.Llm.complete" }`. Writing `provides Llm[C = LiveLlm, E = {External}]` fixed it with no other change. The same held for `FakeLlm`, and for the BARE `FileHarness provides Harness` / `LoadChecker provides Checker`, where binding `C` moved `guardians.attempt` off `OperationBodyMissing { name: "guardians.Harness.render_task" }`. Nothing reported any of the four at load — every caller in the example had only ever been LOADED.

WHY IT IS SILENT: READERS DISAGREE ABOUT THE SAME PROVISION. The typer's provider-keyed reading accepted it: `LiveLlm`'s `E = {External}` reached callers' rows, and `a_carriers_effect_row_reaches_the_caller_that_was_handed_it` was green throughout. Dispatch's carrier-keyed reading (`provision_binds_param_to_carrier`, from `carrier_param_receiver_for_values`) needs the carrier parameter bound to the carrier and found nothing. `provision_carrier_binding` (kb/typing.rs) answers `None` for both shapes — no binding at the carrier parameter, and a bare spec reference — and its own doc audits what each caller makes of `None`: the `dispatch_carrier` builtin mints the PROVIDER, the witness reader and the dot-call match DECLINE. One `None`, two meanings, no diagnostic.

THE SPEC ALREADY SIDES WITH DISPATCH (§5.1): "A `provides` clause names its PROVIDER by WHERE it is written, and its CARRIER by its bindings", and WI-1076 fixes WHICH parameter is the carrier (the first declared type parameter some operation takes). So a provision of a spec that HAS a carrier parameter and does not bind it is a provision about no carrier.

THE DECISION (discussed with the user): a LOAD ERROR, not a default of `C` to the enclosing sort. Decidable at the declaration, needs no call site, and the repair it prescribes (`C = <provider>`) is one binding.

WHAT MUST STAY LEGAL: (1) a spec with NO carrier parameter — §5.1: its provisions record the provider (`sort List provides Stream[T, {}]`); (2) a witness, which binds the carrier explicitly; (3) DERIVED / composed rows from the chain walk, which are not written provisions; (4) whatever the census below finds legitimate.

RELATION TO WI-20260909-M8QWJ — ADJACENT, NOT THE SAME, and that ticket's check would not catch this. M8QWJ asks whether anything could run a body-less operation, and its question 3 explicitly DEFERS a spec operation called on a still-abstract carrier. This defect lives exactly in that deferred case: `summarize`'s `llm: Llm` is abstract, the value that arrives implements `complete`, and only the provision fails to connect them. In the other direction this ticket makes M8QWJ's static enumeration sounder: once every written provision names its carrier, "a provider's implementation" (its question 2) is readable off provisions with no silent `None` arm. Cross-reference only — neither is a technical prerequisite of the other.

CENSUS SO FAR: a bare `provides X` with no bindings occurs nowhere in stdlib/, examples/ or rustland/anthill-todo/anthill after ad00948e (the two in lib/harness.anthill were the only ones). 83 written provisions carry bindings; which of those omit their spec's carrier parameter needs each spec's carrier parameter, i.e. the census is a code question, not a grep.

QUESTIONS:
 1. CENSUS FIRST, over stdlib, examples, anthill-stl, anthill-todo and the test fixtures: each unbound-carrier provision is either a latent dispatch bug or a shape the rule must admit.
 2. WHERE: at the provision recorder (the `None` arm is where the silence is) or a post-load pass over provisions. The carrier parameter is read off the spec's operations, so a provision loaded before its spec's operations needs the whole KB — cross-file order (WI-321) decides which.
 3. MESSAGE: name the spec, its carrier parameter, the provider, and the repair.

ACCEPTANCE: `provides Llm[E = {External}]` against a spec whose carrier parameter is `C`, and a bare `provides Harness`, are refused AT LOAD naming the carrier parameter; controls that load: the same with `C = <provider>`, a provision of a carrier-parameter-less spec, a witness; reverting the four guardians `C =` bindings in a scratch copy is refused at load where it used to fault at run time; stdlib, examples and the full workspace green via rustland/scripts/test.sh.


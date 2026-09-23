## Attributes

- id: WI-20260913-KXNEX-a-provides-that-leaves-its
- created: 2026-09-13T18:34:43Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-22T18:37:35Z

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

## Changes

### 2026-09-22T18:37:25Z — feedback — claude

DELIVERED. A written `provides` clause over a spec that HAS a carrier parameter and binds nothing at it is now a LOAD ERROR naming the spec, the carrier parameter, the provider and the repair. `check_provision_names_carrier` (kb/typing.rs), raised through `LoadError::ProvisionNamesNoCarrier`. kernel-language.md 5.1 carries the rule.

Q1 CENSUS -- DONE FIRST, and it found the defect in four more places than the ticket knew about.
 * SHIPPED CORPUS: ZERO unbound. stdlib (83 written clauses, matching the ticket's count), examples/github-todo and rustland/anthill-todo/anthill were measured with an env-gated probe printing every clause and its verdict. 48 clauses name a carrier; 51-54 are of specs with NO carrier parameter and are legal by rule. The three non-stdlib ones are `anthill.stage0.GithubForge`/`FakeForge provides Forge` (BARE, in secondary entries -- `Forge` is SELF-REPRESENTING, so there is no parameter to bind) and `FileBasedWorkitemStore provides WorkItemStore[State = WIS]`.
 * TEST FIXTURES: FOUR fixtures carried it, 6 tests, found by running the whole workspace with the check on. Each is a latent dispatch bug that survived because the fixture only ever LOADED -- the ticket's own diagnosis, reproduced four times:
   - `wi_pyns2_written_row_type_argument_test`: `Carrier3 provides Spec3[E = {External}]`. The guardians shape exactly.
   - `wi_rsrp5_effect_label_routes_test`: `CPlace provides Spec[E = {Modify[clock2]}]`. Same.
   - `wi_cbrsw_permission_effect_test`: a BARE `provides Gate` over `sort C = ?`. Its own comment says it copies the shape `examples/guardians` uses -- it copied the version from BEFORE WI-20260830-7MK73 repaired it.
   - `wi859_self_provider_candidate_test`: a deliberate BARE `provides Desc` beside `provides Desc[T = Leaf]`, as the vehicle for a GROUPING claim (two provisions, one candidate).
  The first three are repaired with one binding each, subject untouched. The fourth is the only one that needed a decision -- see below.

Q2 WHERE -- A POST-LOAD PASS, and the ticket's own reasoning decides it: `spec_carrier_param` reads the carrier parameter off the spec's OPERATIONS, and cross-file mutual recursion (WI-321) lets a provision load before the file declaring them. Deciding at the recorder would answer "no carrier parameter" for a spec that has one and pass the very shape the check exists to refuse. So `load_provides_clause` RECORDS (new `WrittenProvidesClause` registry, drained once per load by `load_phase_inner`, captured/truncated in `LoadCheckMarks` exactly as its WI-835 neighbour is) and the check decides once the KB is whole, beside the two other provider-side checks and after them.
  THE REGISTRY IS WRITTEN CLAUSES, not a filter over the provision relation. The relation holds DERIVED rows (`eq_derive::run`, `derive_forwarded_provisions`); excluding them by a growing list of "not this producer either" is the WI-838 shape. And it is EVERY written provision, because WI-20260917-S8JYF made `provides` the only spelling -- there is no `fact Spec[...]` route left. A secondary entry's clause reaches the same recorder (measured: the two `Forge` ones are in the census).

Q3 MESSAGE -- names the spec, its carrier parameter, the provider, and the repair, and says what the silence COST (loads clean, then `OperationBodyMissing` at the first call), since otherwise a refusal reads as the loader being newly fussy about a program that "worked". One owner (`provision_names_no_carrier_message`), both rendering paths. Worded to fit BOTH refused shapes with no branch: an earlier draft ended "keeping the bindings already there" and quoted `provides Spec[...]`, which tells the author of a BARE clause to keep bindings it has not got and misquotes brackets they did not write.

THE ONE DESIGN CONSEQUENCE WORTH FLAGGING -- A BARE `provides Spec` OVER A CARRIER-PARAMETER SPEC IS NOW REFUSED, and `wi859`'s fixture wrote one on purpose. Its doc claimed the self-provider kind "must take it", because `witness_dispatch_carrier` answers `None` for a bare provision exactly as for an explicit self-provision. That was true of the GROUPING and false of DISPATCH -- which is this ticket in one sentence, and the guardians measurement is what settles it: bare `FileHarness provides Harness` did NOT dispatch. So the reading was a fiction of the grouping, not a shape being taken away. The fixture now writes two provisions that both name the carrier (`Desc[T = Leaf]` and `Desc[T = Leaf, U = Int64]`, `U` inert), which drives the same grouping claim. MEASURED non-vacuous, because a pair collapsing at the fact layer would leave it asserting "one candidate" about one provision: 4226 facts with the second clause against 4225 without.

WHAT STAYS LEGAL, each driven by its own control: a spec with NO carrier parameter (self-representing -- the `Forge` shape); a WITNESS; a carrier bound through the PROVIDER'S OWN type parameter (`provides Ord[T = List[T = E]]` -- which is why the check asks "bound at all" rather than reusing `provision_binding_at_param`, whose sort-like base filter answers `None` for a type-param binding and would refuse the stdlib); derived rows, which are not in the registry.

IT ASKS `spec_carrier_param` AND NOT `spec_carrier_param_or_sole`, deliberately: the defect is "dispatch reads `None` where the author meant a carrier", and dispatch reads through the former. The two-rung ladder would refuse clauses over specs whose sole parameter dispatch never treats as the carrier -- a diagnostic about a reading nothing performs.

POSITIONAL BINDINGS ARE READ, and the pair is MEASURED both ways rather than assumed: with `C` declared first `provides Spec[Impl]` loads; with the spec's OTHER parameter declared first the same clause is refused naming `C`. Only the spec's parameter ORDER differs between the two, so the pair measures the mapping and not the clause. Without it `provides VectorSpace[Vec3, Float]` would read as binding nothing.

ACCEPTANCE, all green:
 * `provides Spec[<non-carrier> = ...]` and a BARE `provides Spec` refused at load, each naming `C` -- `a_provision_binding_a_non_carrier_parameter_is_refused`, `a_bare_provision_of_a_carrier_parameter_spec_is_refused`.
 * THE TICKET'S OWN MEASUREMENT RE-RUN: `reverting_the_guardians_carrier_bindings_is_refused_at_load` reads the SHIPPED `examples/guardians/lib` files, asserts they load, strips the four `C =` bindings (asserting it struck exactly four, so a renamed binding cannot silently leave the sources untouched) and asserts all four are refused BY NAME. Refused at LOAD where it used to fault at run time.
 * THE CONTROL THAT DRIVES THE CAPABILITY: `a_bound_carrier_loads_and_the_abstract_call_dispatches` CALLS through an abstract receiver (`drive(s: Spec, p) = s.run(p)`) and asserts the provider's value, 42. Backed out -- check disabled AND `C = Impl` struck -- it LOADS CLEAN and panics `OperationBodyMissing { name: "test.kxnex.Spec.run" }`: the guardians failure reproduced in nine lines. That is the pairing that makes it evidence; every other control passes either way BY DESIGN and says so.
 * Full workspace green via rustland/scripts/test.sh; scaland green (578 passed) via `sbt testFull`.

Rows: `wi_kxnex_provision_names_carrier_test` (4 refusals + 5 controls). /code-review run: two findings, both mine, both handled -- the new struct had been inserted between `ParameterizedSite`'s doc comment and its struct (reassigning the WI-835 doc and leaving that type bare), and the `wi859` fixture's non-vacuousness was assumed rather than measured.

RELATION TO WI-20260909-M8QWJ unchanged: adjacent, neither a prerequisite. This makes M8QWJ's static enumeration sounder -- every written provision now names its carrier, so "a provider's implementation" is readable off provisions with no silent `None` arm.


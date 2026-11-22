## Attributes

- id: WI-20261122-CXR5B-the-readers-of-the-single
- created: 2026-11-22T10:23:52Z

- status: Open
- status_agent: user
- status_at: 2026-11-22T10:23:52Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261121-JE2MT-two-readings-of-which-sort-a

- tags: typing

## Description

THE READERS OF THE SINGLE CARRIER PARAMETER MOVE TO THE SORT CARRIER AND THE OPERATION CARRIER (stage 2 of docs/design/spec-carrier-set.md; filed with the user 2026-11-22. Stage 1 is WI-20261121-JE2MT, which delivers the owner `sort_carrier` and the derivations built on it).

The implementation computes ONE carrier parameter per spec, by five ladders (design §2, L1-L5), and about 120 sites read it (docs/design/spec-carrier-set/readers.md): dispatch, the coherence grouping, the witness classification, the default rows, the member checks, projections and refusals.

DECIDED with the user (design §6):
- 1: a call fixes its OPERATION CARRIER, the type-vars its signature mentions (`Self` mentions them all). Parameters are fixed by the arguments, the result by the type expected at the call, any type-var by a bracket or a `requires`, and a provider's provisions by a bracket naming it. What the call leaves unfixed is read off the provisions at what it fixes. It is refused when it fixes nothing and names no provider, or when those provisions disagree. One provider and several are held alike, so §8.7's refusal of one provider writing two provisions goes. The kernel-language.md §5.4 wording is approved, with its amendment.
- 3: a provision binds each type-var an operation takes a value of.
- 4: the SORT CARRIER is all the type-vars, for every spec; `Self` is the spec at all of them.
- 5: anthill.reflect.typing.provision_carrier's ?c is the SUBSTITUTED SORT. self_provides, default_provider, the loader's default index and one_default move with it.
- 6: a binding whose type-var appears only in operations' results does not make a provision the provider's own.

MEASURED today (design §3; docs/design/spec-carrier-set/run.sh reruns each):
- b3/b4: the carrier and the default row move with the order two type-vars are declared.
- b5-b8: two witnesses that differ in a type-var no argument fixes are a first match by declaration order.
- d5 and e3/e5: one provider writing two provisions is refused at load.
- d7: naming the witness in a bracket is refused.
- d11: a call naming its provider is refused, although it should answer 1.
- d12: a call naming its provider on a spec with no type-vars loads clean and fails at run ("operation has no body").
- e4: a provider whose values `joinTwo` receives is filed as a witness.
- e5: a `joinTwo` bound by name has its receiver refused where the same member passes.
- c1: a Monad witness at another sort is refused; its cause is to be named.

TO DO:
- the readers, by question (W, O, S, V, P, M, K, X: design §4);
- the two indexes keyed by the single parameter: ProvidesIndex's witness carriers, and the eq-dispatch index's witness filing (WI-20261121-DBR8V's (b) follows from it);
- the default index's key under a compound ?c, on the per-call path;
- kernel-language.md §5.1, §5.2 (the `Self` passage's wording is still to be drafted for the user), §5.4 (approved), §8.3, §8.7;
- a note in 058 §3.6.

ACCEPTANCE: design §7's stage 2 rows, each driven with its back-out; families green; full workspace green via rustland/scripts/test.sh; scaland testFull.

## Changes

### 2026-11-22T11:03:31Z — feedback — claude

Two decisions this ticket restates changed with the user on 2026-11-22, after a fourth review of docs/design/spec-carrier-set.md. They supersede the description where it differs. DECISION 5, corrected: provision_carrier's ?c is the type of the values the provision is for. For a spec with a dictionary that is the spec at all its type-vars (`Set provides Eq[T = Self]` is at `Eq[T = Set]`). For a self-representing spec it is the PROVIDER at its own type-vars (`List provides Stream[T = T, E = {}]` is at `List[T = T]`), and the spec's type-vars are read off it. With the spec's substituted sort there instead, rule (2) of default_provider would write six overlapping 'default Stream' rows, and one_default (check_one_default, kb/defaults.rs:798) would refuse the standard library (probes g1-g4). DECISION 6, decided again (it was option (b)): every binding counts. A provider provides a spec for itself when its sort is the head of the carrier or the head of one of the carrier's bindings. One verdict moves: f4, two sorts each owning a provision of Coll[C = Foo, Elem = Num], is refused at load until one is marked `default provides`; it runs today. f1's Num gains a harmless inferred default row. f2's Foo for Dflt and the nine stdlib NonEq self-provisions keep their own provisions. Stage 2's rows for both are in the design's §7.

### 2026-11-22T11:23:16Z — feedback — claude

After a fifth review of docs/design/spec-carrier-set.md (2026-11-22), the design's §1 table was reworked with the user from Self's definition (kernel-language.md §5.2). A provision's CARRIER is what Self denotes for the values the provision is for. For a spec with a dictionary it is the spec at the provision's bindings (Eq[T = Set]). For a self-representing spec, which is one where some operation takes a value of type Self, it is the provider at its own type-vars (List[T = T]), and the spec's type-vars are Self's projections read off it. DECISION 5 is confirmed against it: provision_carrier's ?c is that carrier. DECISION 7, from the table: one provider writing two provisions of a self-representing spec that differ in a type-var is refused at load (one carrier, two readings of Self.C), as today and per §8.7. DECISION 8, from the table: a spec with both shapes (wi1076's Holder: peek(c: C) beside joinTwo(a: Self, …)) is self-representing. Its provisions are at the provider, and BoxHolder is no longer a witness at Box. Several providers at one C are refused at the call until the provider is written; a default row cannot settle that tie, and where the providers have constructors the unfiled c3 defect blocks naming one too. These supersede the description where it differs. Stage 2's rows are in the design's §7.

### 2026-11-22T11:43:56Z — feedback — claude

Two additions, decided with the user on 2026-11-22 after a sixth review of docs/design/spec-carrier-set.md. (1) A SECOND AMENDMENT to the approved kernel-language.md §5.4 wording, merged into the design's quoted text: 'For a self-representing spec, a value at a parameter typed Self fixes the provision's carrier, the provider whose value it is, and so does the type expected at a result typed Self.' Rows: g2 (Src.next(ones)) keeps answering 12; g6 (let o: Ones = Src.make[T = Int64]()) is refused as ambiguous today and must answer 1. (2) The c3 defect is now a row of THIS ticket. Today a provider with constructors may never be named in a bracket ('expected no explicit selection of a concrete provider', the concrete-provider rule, dispatch.rs is_value_directed_provider, TieRepair::ValueDirected), because 'the value decides'. Under decision 8 that premise fails: for a self-representing spec with two such providers, a call with no Self value has no bracket repair. The only call that works today is the provider's own member (g5: Src.next(Ones.make()) answers 1). TO DO: such a provider may be named where no value at the call decides; c3 and g4 then answer. The spec's concrete-provider paragraph (§5.4, around line 3783) is reworded for the user's approval.

### 2026-11-22T15:19:06Z — feedback — claude

Steps 1 and 2 delivered (stage 2 of docs/design/spec-carrier-set.md, in progress). STEP 1, 7425f192a: a provision is at its carrier and is its provider's own where the provider heads the carrier or one of its bindings (decisions 5, 6, 8). typing::provision_carrier is the one owner; the reflect relations read it (provision_carrier_of, was dispatch_carrier; own_provision_carrier_of; typing.anthill gains own_provision), and so do 058 §3.6's default rows, filed per spec and compared over the whole substituted sort. f4 is refused at load until one provision is marked default provides (one_default's new TwoOwnProviders case; a mark on a provider's own provision is admitted beside another own provider's inferred row and answers the lookup). kernel-language.md §5.1 reworded with the user. STEP 2, 2c95a5da8: what a call fixes selects its provision on the typed call path (decision 1, §5.4's two amendments): typing::select_provision_at_carrier chooses among the provisions at the receiver's carrier by the bracket's provider, what sigma holds and the type expected at the call, and refuses where they still disagree on what the call leaves free; a bracket naming a provider fixes every type-var its provisions write; a pinned call on a spec with no type-var reads the pin; the expected type at a Self result fixes the provider where it supplies the operation. Moved: b1, b3/b4, e1, e2, e4, f1, f2, g2's ?c; f4; b6, b7, b8, d7, d11, d12, g6. Rows: wi_cxr5b_provision_carrier_test, kb::defaults::lookup_tests, wi_cxr5b_call_fixes_test. REMAINING: d5 (one provider writing two provisions, refused by three load checks) with §5.4's approved wording; c3/g4 (a provider with constructors named in a bracket; §5.4's concrete-provider paragraph to reword for the user); the untyped eval path (carrier_param_receiver_for_values); the witness classification and the V readers (c1: Monad's M[A] is not read as taking M; e4/e5; the bound-joinTwo receiver defect); decision 3 (ProvisionNamesNoCarrier restated) and decision 7; the P/M/K/X readers; kernel-language.md §5.2 (the Self passage, wording for the user), §5.4, §8.3, §8.7. Seen, not fixed: reflect queries lower each matched spec view to the term store per query (store growth for rows with variables).

### 2026-11-22T17:04:07Z — feedback — user

Step 3 (c4163e059): one provider and several are held alike (decision 1's d5; decision 7). A provider's provisions of a spec were grouped by their binding of the single carrier parameter in three places, which were d5's three refusals: the suppliers a dictionary of the provider answers (spec_op_suppliers_of_provider, with the application a resolved instance is for, tree_application), the instance-fact leg of the coherence grouping, and check_provision_binding_agreement, which bucketed by the FIRST type-var declared. Each now reads typing::SpecApplication, a provision's binding of every type-var; a self-representing spec is one application per provider, so e3/e5 stay refused and now name C bound two ways (decision 7). A bracket naming a provider whose own standing provisions disagree on what the call leaves free is refused, where it ran the first written. Moved: d5 -> 1 (String expected -> two, Coll[Elem = String] -> two, nothing fixing Elem refused naming WB with a repair that runs), d14 (one witness binding tag at Tag[T = Foo] and Tag[T = Bar]) -> 21, Box's own Show at Box[E = Int64] and Box[E = String] with operation bindings -> 21. Kept refused by name: a provider's OWN provisions of a dictionary spec that agree where it heads a binding and bind another type-var apart (d15; the wi842 and wi_n3w68 pins), since the ~20 readers of provider_spec_view_bindings take the first; they go with the P readers. kernel-language.md: §5.4's approved wording landed, §8.7's 'One carrier declaring one spec twice' restated, §5.1's paragraph on readers still on one parameter updated. Rows: wi_cxr5b_one_provider_test (6), 5 failing with src/ at 757d23229 and the own control passing; each of the three groupings backed out alone fails d5's row. /code-review (high): 6 findings; 1 fixed (own provisions put in one bucket refused Box's two own Show provisions, which loaded before), 1 not reproduced (tree_application over every type-var: r2 answers 21), 4 skipped (the conservative comparator of SpecApplication::same for sigma-built bindings; e3's call-site tie still rendered as witness routes by provision_supplier; MixedProviderKinds not per application, pre-existing; a §5.4 cross-reference to §8.7's own-provision refusal, for the user). Gate 12562 / 0; families green; scaland testFull 811 + 51 (2 skipped) + 1. REMAINING: c3/g4 (§5.4's concrete-provider paragraph to reword for the user), the untyped eval path, the witness classification and V readers (c1; the bound-joinTwo receiver defect, reproduced with ONE provision, independent of this step), decision 3, the P readers (provider_spec_view_bindings, whose own-provision refusal this step keeps), M/K/X readers, §5.2 and §8.3.


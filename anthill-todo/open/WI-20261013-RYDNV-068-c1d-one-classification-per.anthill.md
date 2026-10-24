## Attributes

- id: WI-20261013-RYDNV-068-c1d-one-classification-per
- created: 2026-10-13T08:03:31Z

- status: Open
- status_agent: claude
- status_at: 2026-10-13T08:03:31Z

- acceptance: cargo-test

- depends_on: WI-20261013-R1W5A-068-c1c-a-call-or-a-binder, WI-20261013-GFS6A-068-d1a-a-woven-call-is

- tags: proposal-068, typing

## Description

068 C1d — ONE CLASSIFICATION PER CALL, READ BY THE TYPER AND BY THE REQUIREMENT INFERENCE (decision 3 of WI-20260926-7D48J; its part 4). DESIGN FIRST, in docs/design/requirement-channel.md: the typer's per-call classification — pinned at a concrete carrier / needs a dictionary / value-directed where a variable's type is undetermined (the WI-282 exemption) — becomes the ONE input of WI-20260925-P7VP4's inference, replacing its own `spec_op_call_carrier_outcome` reading, so the two cannot disagree. ROWS: the position rows of 7D48J's 2026-10-08 note — over `sign[A](x: A, y: A) requires WeakOrd[T = A]`, `?c = Util.sign(?a, ?b)` and `PartialEq.eq(Util.sign(?a, ?b), ?c)` are decided as `Util.sign(?a, ?b, ?c)` is; `Holder.hsign(?a, ?b, …)`; `Mk.mk(?c)` against its operation-body twin; row (2) of the 2026-09-26 note (a call with no argument at its carrier parameter is refused at typing unless a `require` supplies it).

FROM WI-20261003-4DYR6: THE RULE BODY'S GATE GOES. `spec_op_call_parent` (typing/call_class.rs) is the one gate that still reads the declaring sort — a type parameter or a provider — because the walk decides at load, with no carrier, whether a goal is typed as a call and whether a woven call carries one dispatch dictionary or requirement slots. MEASURED 2026-10-13 with that gate answering for every sort that may be provided: 35 rows fail (wi_p7vp4 16, wi_nekr0 10, wi_9r5hn 3, wi_mhrn1 3, wi_prva2 3) — a module-style `sort Util`'s operation woven as dispatched (`Util.isLess[A](a: A, b: A) requires WeakOrd[A]` in a rule body refused 'requirement … cannot be supplied'), a goal that is a relation over terms typed as a call ('fields.entity (op-arg): expected Type, got Pt'). With the classification made per call those rows pass with no test on the sort; `spec_operation_short_names` (kb/load.rs) and wi1043's the_walk_gate_is_the_two_halves_and_a_data_sorts_operations are restated.

ALSO HERE, from WI-20260926-DSEXA's 2026-09-30 note: the load-time refusal to weave an unpinned body-less operation in a value slot (`inferred_demand`) is retired, on D1a's answer that a dictionary with no provider at a ground carrier is UNREDUCED.

ACCEPTANCE (cargo-test, driven): a call the clause typing places at a concrete carrier is pinned at load and not woven, a row per class, each back-out reddening its own row; P7VP4's, SHED7's and 0RRQP's rows unchanged or flipped as C1a records. WI-20260926-Y6ZCD waits on this part.

## Changes

### 2026-10-14T15:07:44Z — feedback — claude

D1a's ANSWER IS IN PLACE (WI-20261013-GFS6A, 4d22dbc2): an INFERRED find_dictionary read at a ground carrier no provider supplies answers Unknown { Unreduced } (read_dictionary_into), not a failure; a written read and one whose dictionary a citation supplied still fail. Retiring inferred_demand's refusal can rely on it.

### 2026-10-14T16:11:48Z — feedback — claude

CORRECTION (38c9e23b, decided with the user 2026-10-14): D1a's answer is the reverse of the note above — an inferred find_dictionary read at a ground carrier no provider supplies FAILS, as a written one does: a missing provider is no undecided answer. Retiring inferred_demand's refusal therefore gives such a call a failing condition, which is now the intended verdict, not the 'definite failure' DSEXA's 2026-09-30 note warned of.

### 2026-10-21T13:58:31Z — feedback — claude

SHED7 DEPENDS ON THIS PART (user, 2026-10-21). Proposal 067 §4's solver over any collection builds its collection with `vs <=> PersistentCollection[C = C].fromList([?p, ?q, ?r])`, in `sort Sat[C] requires PersistentCollection[C = C, Element = Bit]` with `rule model(vs: C)`: a call with no argument at its carrier parameter (`C` is only its result), the case of row (2) — the typed head `vs: C` (WF14Z) and the sort's requirement (0RRQP) supply it. MEASURED 2026-10-21 on c0883a2e, with a stand-in spec `Builder` carrying `fromList` (PersistentCollection has none yet) and `Bag` providing it: `Builder.fromList[C = C]([…])` is refused (call-site type arguments on a rule-body goal); the repair that refusal advises — an operation of `Sat` carrying the bracket — is refused ("element `C = fl.Sat.C` is unconstrained at this call site; this is a RULE-body goal"); adding `?d = require[Builder[C = C, Element = Bit]]` is refused ("no head bound of this clause names a sort, so none can provide `Builder`"); `Builder[C = C].fromList(…)` and `Builder.fromList(…)` load and then flounder at run time (`relation_floundered`). Wanted once this part lands: `Sat[C = Bag[T = Bit]].model` 2 models, a given model 1, a refuted one none. Program and measurements: docs/brainstorms/fillable-collection-landscape.md §4.

### 2026-10-22T14:38:27Z — feedback — user

FROM WI-20261013-WF14Z (2026-10-22, user: the value-slot part stays here). WF14Z's seventh part dispatches a dot through another clause variable's requirement slot: in sort Box (requires O: WeakOrd[T]), ?p <=> box(a: ?x, b: ?y), ?c <=> ?x.compare(?y) is WeakOrd.compare(?x, ?y) (find_spec_op_for_clause_slot), where it was the term 1.compare(5). In a value slot it answers by the values, Int64's own -1, as the written ?c <=> WeakOrd.compare(?x, ?y) there does, while the goal WeakOrd.compare(?x, ?y, ?c) answers 4 / -4 through the citation's slot (carried_slot_reading): inferred_demand declines an unpinned body-less op in a value slot, the refusal this ticket's description retires. ROWS THAT FLIP when it is retired: wi_0rrqp_clause_typed_through_constructor_test::a_dot_through_another_variables_slot_is_the_call (dotOutside and valOutside -1 -> -4, beside goalOutside -4); and the two-box dot form (rule two over ?p, ?q with ?c <=> ?x.compare(?y), cited as CBox.two(asc(), desc())) becomes refused as its written goal form is in two_slots_that_may_name_two_providers_are_refused — add that spelling to the row. 068-implementation §6.9 states the limit.

### 2026-10-24T05:10:52Z — feedback — user

FROM WI-20261023-GBH5F (proposal 069 stage 2, 2026-10-24): an operation type parameter's DEFAULT is installed by the typer at a rule-body call (user's decision: context-free, 069 §2), and is evidence this ticket's one classification must hand the weave. MEASURED: `rule viaRule(?n) :- d(?n)` over `d[T = Int64]() -> Int64 requires Desc[T = T]` (`IntDesc provides Desc[T = Int64]`, `StrDesc provides Desc[T = String]`) loads clean and aborts a debug build at the query, `DeferToRequirement: requirement param __req_desc not bound in caller frame` — the weave reads the argument values (none), not the σ that holds T = Int64. The same today for a typed head (`rule r(?o: Option[T = Int64], ?t) :- whichN(?o, ?t)` over `whichN[T](o: Option[T]) -> Type requires TypeValue[T = T]`, `r(none(), ?t)`), so the default adds a source, not a class. A row for the acceptance here: `viaRule(?n)` answers 7 (IntDesc's).


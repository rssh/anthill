## Attributes

- id: WI-20260921-R10KC-decide-whether-a-requirement
- created: 2026-09-21T15:25:33Z

- status: Open
- status_agent: user
- status_at: 2026-09-21T15:25:33Z

- acceptance: cargo-test

## Description

A SPEC DEFAULT BODY MUST RECEIVE ITS PROVISION'S DICTIONARY, and must resolve a body-less sibling member by PROJECTION out of it rather than by value-directed dispatch. Today it receives nothing, falls back to the value, and then tries to RECONSTRUCT the requirement from the argument data - which cannot work for a slot that leaves no trace in the data.

THE MEASURED PROGRAM (~70 lines, scratchpad `valuedict.anthill`, reconstructible from this paragraph; re-measured on the merged tree at ccf530b5). `MySet` is a carrier with `requires O: WeakOrd[T]` whose `contains` reads the slot through `WeakOrd.compare`. `Searchable` is a spec with a body-less member `contains(c: C, x: Element)` and ONE shared default body `containsAny(c, xs)` that calls it. Two rival `WeakOrd[String]` are in scope, so nothing below is explained by there being one thing to pick. `anthill load` is CLEAN (4293 facts, 432 rules); `anthill run` dies:

  error: cannot dispatch `anthill.prelude.WeakOrd.compare`: ... reached by dispatching on a
  VALUE, which carries its sort but none of its type parameters - so the provider the value's
  construction chose for the slot cannot be recovered here, and more than one could have been.

THE FOUR STEPS, and the information is present at three of them. (1) `MySet.empty[T = String, O = ByLength]()` - the typer builds MySet's dictionary from the bracket, puts it in `empty`'s frame; the frame pops and the returned `nothing()` keeps none of it. (2) `MySet.insert(…, "zz")` - built AGAIN from the type; runs. (3) `Searchable.containsAny(s, …)` - the typer knows `s : MySet[T = String, O = ByLength]` and resolves the provision, but the frame it enters is the SPEC's, and eval.rs says what that channel holds: "They used to enter the impl's frame with the SPEC call's own channel, EMPTY for the ordinary abstract call." There is no slot to hand it to. (4) `contains(c, h)` in the body - `c : C`, and the same doc states the consequence: "Both arms resolve the impl from a runtime RECEIVER VALUE, precisely because the typer could not pin it - so no call site built the impl a dictionary and no caller slot names it." The runtime then rebuilds from `node(elem: "zz", rest: nothing())`, which mentions no ordering.

WHY PROJECTION IS THE RIGHT ROUTE AND NOT A NEW MECHANISM: a body-less spec operation IS a dictionary entry, and the projection already exists. `stdlib/anthill/realization/runtime.anthill`: `operation resolveOp(d: Dictionary, specOp: Symbol) -> OpRef` - "the impl op plus THIS DICT AS ITS DISPATCH ENVIRONMENT. Keyed by the SPEC OP SYMBOL - the same key the interpreter dispatches on. The reflect face of `dispatch_via_sort_ops_table`." An `OpRef`'s `dict` is installed into the callee frame at apply (WI-420) rather than forwarding the caller's.

AND ONE DICTIONARY IS SUFFICIENT, because `dict_layout` already reserves the space. For spec = Searchable, provider = MySet the layout is the spec half (EMPTY - Searchable declares no `requires`) then the provider half (MySet's own sort-level `requires O`). So the dictionary is

  Dictionary( sub0 = Dictionary(impl: ByLength),  impl: MySet )

which carries BOTH halves of what the body needs: `impl` says which implementation `contains` resolves to, and `sub0` is the evidence that implementation reads. THE ONE-SENTENCE STATEMENT OF THE DEFECT: both routes find the same implementation, and only one of them brings the evidence.

WHAT THIS TICKET IS NO LONGER ABOUT. It was filed as "may a requirement dictionary be stored in a VALUE", with five obstacles about where a field would live in the tree. That framing is RETIRED and the correction is recorded in this ticket's Changes. `s` never needed to carry anything; the dictionary is built three times in the program above and simply never reaches the frame that reads it. A value-carried dictionary survives only for the routes where there is genuinely NO static type to build one from - a host `interp.call` whose value was built in Rust (`seed_entry_requirements` has nothing to read), the SLD bridge calling from a rule body, and a true existential (`List[T = MySet[T = String, O = ?]]`), which Anthill does not have. If this ticket lands, whoever takes it states which of those three still refuse and whether `NamedSlotNotCarried` survives for them.

NEGATIVE RESULT, MEASURED, so it is not retried: the slot cannot be declared on the SPEC. `Searchable requires OE: WeakOrd[Element]` with `OE = O` written in the provision head is refused - "'MySet' provides 'Searchable', which requires 'WeakOrd', but 'MySet' does not provide 'WeakOrd'". A `requires` on a spec is an obligation on the PROVIDER, so that spelling demands MySet itself be an ordering. The evidence must travel as the provider's own condition, which is exactly the half `dict_layout` reserves.

PRIOR ATTEMPT AND THE LIKELY PREREQUISITE. Frame inheritance was tried during WI-456 (2026-09-20) and backed out because "a dictionary does not record which spec it witnesses"; it broke `wi435_iterable_op_on_map_handle_value_dispatches`. CONFIRMED at the representation: `eval/dictionary.rs` is `Dictionary(sub0 … subn-1, impl: S)` - the PROVIDER is recorded, the spec is not, and `alloc_dictionary(spec, provider, subs)` takes the spec only to validate against `dict_layout` and then drops it. So making a dictionary self-describing may be this ticket's first step rather than a separate one; whoever takes it decides and says which.

BLAST RADIUS, and it is the reason this is not a SortedSet patch. EVERY spec default body calling a body-less sibling is on the value-directed route today. Most of them work, and it is worth being exact about why: the rebuild SUCCEEDS wherever the reconstructed goal has a unique answer - one provider for `Eq[T = String]`, say - not because evidence travelled. It fails exactly where the construction site made a SELECTION that the data does not record, which is what a named slot is. `wi456_sorted_set_collection_test::single_ordering_control_*` passes either way by design and pins that boundary.

ACCEPTANCE:
 - the probe program RUNS through the DEFAULT BODY and answers yes;
 - and the ordering decides it there: one polymorphic body, `O = ByLength` and `O = Alphabetical` giving DIFFERENT answers for the same query, so one answer twice fails the test;
 - `wi456_sorted_set_collection_test::a_default_body_reading_the_slot_by_value_is_refused_naming_it` INVERTS rather than being deleted, and its `direct` row is FIRST strengthened to that split - today it answers 1 under either ordering, so it proves the typed call RUNS and not that the comparator DECIDED;
 - the programs that work today by unique-answer rebuild still work, named rather than assumed: `single_ordering_control_*`, `wi435_iterable_op_on_map_handle_value_dispatches`, and `op_scoped_relay_chain_correct_via_value_direction` still computes 551;
 - the three no-static-type routes are each stated - refusing or running - and `NamedSlotNotCarried`'s remaining population is named at its site;
 - full workspace green via rustland/scripts/test.sh.

RELATED: WI-456, where this was measured (its §33 in docs/design/058-implementation.md is the layout this reads); WI-20260921-159S9, the other residue of that measurement and a neighbour here, since it is also about which channel reaches a body; WI-857, whose "chain-free-provider accident" is why the blast radius is wide. NOT WI-402, which is Delivered and covers `ensures Spec[C]`, the RETURN position.

NOTE ON THE ID: the slug reads "decide-whether-a-requirement" from the original framing. Ids are never renumbered, so it stays.
## Changes

### 2026-09-21T18:08:09Z — feedback — user

DESCRIPTION REWRITTEN 2026-09-21, SAME DAY IT WAS FILED, because the first framing asked the question at the wrong altitude and would have sent a claimer at the wrong target. Recorded rather than silently replaced.

WHAT IT SAID. "DECIDE WHETHER A REQUIREMENT DICTIONARY MAY BE STORED IN A VALUE", followed by five obstacles - `tip` is nullary so an empty set has nowhere to put one; `bin` IS the set with no root wrapper, so a per-node field duplicates it n times; `eq` is extensional and would have to exclude the field; the discrimination tree indexes structure; SMT terms are data. Every one of those is a cost of ONE MECHANISM - a field on the carrier's own constructors - and I let the mechanism into the problem statement. The five were answers to a question nobody had established was the right one.

HOW IT CAME APART, in the user's questions and in this order. (1) "What can be the reason it CAN'T be stored in a Value?" - there is none. A `Value` is a tree, a `Dictionary` is already a `Value::Entity`, and trees nest; the five were consequences dressed as impossibilities. (2) "Why do you think we have erasure?" - I had imported the word from Java and it fits badly. `Value::Entity` has exactly `{functor, pos, named}` and `Term::Fn` matches it, which is all the refusal message means; but `T = String` IS recoverable from the elements, so the gap is not that type arguments are erased, it is that a WITNESS slot is the one type argument with no footprint in the data. And `Value::OpRef` already carries a `dict`, with WI-420's reason - "an eta'd OpRef escapes to a foreign apply frame, so it cannot inherit" - so the precedent for a value carrying evidence was already in the tree. (3) "But at compile time `s` always has a type" - correct, and decisive: the type is known at EVERY concrete site, and what is shared is the BODY. So the failure is a missing parameter pass, not a missing fact. (4) "`contains` is without body, it means contains is in dictionary" - the one that lands it. A body-less spec operation IS a dictionary entry, `Dictionary.resolveOp` already projects it and hands back an `OpRef` carrying that dict as its dispatch environment, and `dict_layout`'s provider half already holds the comparator. Both routes find the same implementation; only one brings the evidence.

WHAT SURVIVED THE REWRITE: the measured program, the refusal text, the ByLength / Alphabetical split as the acceptance shape, the negative result about declaring the slot on the spec, and the observation that the committed test's `direct` row proves the typed call RUNS and not that the comparator DECIDED.

WHAT DID NOT: the five obstacles, the word "erasure", and the premise that a datum must hold a dictionary. That premise is demoted to the three routes where there is genuinely no static type to build one from - host entry, the SLD bridge, and a true existential - and the new acceptance asks whoever takes this to state which of them still refuse.


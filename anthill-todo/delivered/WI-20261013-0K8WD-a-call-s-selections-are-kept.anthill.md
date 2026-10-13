## Attributes

- id: WI-20261013-0K8WD-a-call-s-selections-are-kept
- created: 2026-10-13T10:21:45Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-13T11:52:41Z

- acceptance: cargo-test

- tags: typing

## Description

A CALL'S SELECTIONS ARE KEPT BY THE REQUIRED SORT, NOT BY THE REQUIREMENT — so a sort with two requirements on one sort cannot be called with a provider for each (user, 2026-10-13: 'ok, file ticket for per-requirement key'; found on WI-20260925-0RRQP, whose second acceptance row waits on it).

MEASURED 2026-10-13 on 83eff5ca:

  sort ByLength
    provides Ord[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(a.length(), b.length())
  end
  sort Descending
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)
  end
  sort Entry
    sort K = ?
    sort V = ?
    requires OK: WeakOrd[T = K]
    requires OV: WeakOrd[T = V]
    entity entry(k: K, v: V)
    operation cmp(a: Self, b: Self) -> Int64 =
      let c = a.k.compare(b.k)
      if eq(c, 0) then a.v.compare(b.v) else c
  end
  Entry.cmp[K = String, V = Int64, OK = ByLength, OV = Descending](entry(k: "bob", v: 3), entry(k: "amy", v: 7))

Nothing in it is ambiguous: `a.k.compare(b.k)` is at `String`, so it is `OK`; `a.v.compare(b.v)` is at `Int64`, so it is `OV`. The answer owed is 4 — the keys are equal by length, and 7 - 3 under `Descending`. It is a load error: 'two providers are selected for anthill.prelude.WeakOrd at the call to Entry.cmp: ByLength and Descending — one spec, one witness per call'. THE SAME REFUSAL where both are written in the value's type (`operation mk() -> Pair2[K = Int64, V = Int64, OK = Descending, OV = Ascending]`, refused at the call that takes `mk()`). AND WITH ONE SELECTED the other is refused as unsupplied — `Pair2.keyDirect[K = Int64, V = String, OK = Descending](…)`: 'leaves its named requirement slot `OV` universally quantified, and NOTHING HERE CAN SUPPLY IT … a construction here would answer for Descending' — where `String` has an order of its own; the provider selected for `OK` is the one that would be handed to `OV`. So a sort with two NAMED requirements on one sort cannot be called at all. WHAT WORKS: the two requirements unnamed and nothing selected, each type's own provision answering (1 for the program above, by `String`'s own order); two requirements on two DIFFERENT sorts, both selected (`OK: WeakOrd[T = K]`, `SV: Show[T = V]` answer 4 / 7 and -4 / 9); and in every program that loads, a call in the body — written `WeakOrd.compare(k1, k2)` or as the dot `k1.compare(k2)` — reads the requirement at its receiver's type.

WHERE: a selection is `InstanceSelection { spec_sort, witness, slots }` (rustland/anthill-core/src/kb/typing/slots.rs). `push_selection` adds one and refuses a second, different witness for a `spec_sort` already selected (`TypeError::ConflictingSelection`), whoever wrote it — the call's bracket (`seed_op_type_args`) or the argument's type (`selections_from_slot_bindings`). `resolve`'s step 0 reads it back by the sort alone, `pinned_selection_for(kb, scope.selected, goal.spec_sort)` (typing/synth.rs); `selected` rides `ResolutionScope` through dict.rs, carrier.rs, apply.rs, bridge.rs, build.rs and dep_projection.rs, and is part of `resolve_cache`'s key. `InstanceSelection`'s doc says the key is the sort because that is the coordinate the goal carries, that two slots of one sort are therefore indistinguishable to a pin, and that a slot-precise key is 058 phase 3b's business; docs/design/058-implementation.md marks 3b delivered (WI-843), and the key is still the sort's. These sites were found by reading and are a lower bound: grep `selected` before scoping.

TO DECIDE BEFORE BUILDING, with its program — TWO REQUIREMENTS AT ONE TYPE, proposal 058's own opening example:

  sort Semi
    sort T = ?
    requires Plus: Mon[T]
    requires Times: Mon[T]
    operation mulAdd(a: T, b: T, c: T) -> T = Plus.combine(Times.combine(a, b), c)
  end
  Semi.mulAdd[T = Int64, Plus = Sum, Times = Product](2, 3, 4)

A key per requirement lets the CALL say which provider is whose. The BODY still cannot say which requirement a call reads, since both are at `T`: `Times.combine(a, b)` is refused, 'no rule, fact, operation, entity, const or builtin is declared under that name'. `wi844_sorted_set_driver_test::two_witnesses_for_one_spec_are_refused_whoever_wrote_them` pins the refusal for this shape on purpose (`requires A: WeakOrd[T]`, `requires B: WeakOrd[T]`): one stored witness had answered both requirements. Whether this ticket ends at requirements their types tell apart, that row standing, or also takes a call through a requirement's name.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh, driven by value): `Entry.cmp` above answers 4, and -4 with `OV = Ascending`; the two written in the value's type answer the same; one selected and the other left out is answered by the other type's own provision where it has one, and refused as today where it has none; WI-20260925-0RRQP's second row — a sort with `requires OK: WeakOrd[T = K]`, `requires OV: WeakOrd[T = V]`, `rule keyOrder(?p, ?c) :- ?p <=> entry(k1: ?a, k2: ?b, v1: ?, v2: ?), WeakOrd.compare(?a, ?b, ?c)` and its `valOrder` twin, cited from member operations — routes each clause's condition to its own requirement and not to either by scan order; `wi_0rrqp_clause_typed_through_constructor_test::two_requirements_on_one_sort_cannot_each_be_given_a_provider` and the NOT DRIVABLE note in `wi_wn9p8_forward_soundness_test` are replaced by rows that drive it. CONTROLS, each said at its site: one requirement selected, as today (the rows of wi840_named_requires_slot_test, wi844_sorted_set_driver_test, wi870_bracket_value_slot_test, wi_tx0g6_selection_validation_test); two different witnesses for ONE requirement still refused; the same-type pair as decided above; a selection by the sort's name for an unnamed requirement (`[WeakOrd = Descending]`) unchanged, and still refused where the name picks out two ('names more than one requirement slot'); full workspace green.

## Changes

### 2026-10-13T11:52:48Z — feedback — claude

DELIVERED 2026-10-13 in dc0ef2db. A selection is kept by the requirement it is for — its name, or unnamed — beside the sort (SelectedSlot), and each reader asks for its own requirement's: the walk that fills the callee's frame entry by entry, the dispatch, the binding check, and the inference of an unwritten name. DRIVEN (wi_0k8wd_selection_per_requirement_test): Entry.cmp 4 and -4; the two written in the value's type — result, let, receiver bracket, constructor bracket — the same; K and V both Int64 with OK = Descending, OV = Ascending, keys 4 and values -4, swapped -4 and 4; an operation's own two names; a named requirement beside an unnamed one; an unwritten parameter slot, a one-parameter function value and a forward under an operation's and a sort's own names; 0RRQP's second row in its own file (4 / -4, swapped, and 4 / 7 at two types); the wn9p8 note replaced by a row on all four channels. WHERE IT DIFFERS FROM THE ACCEPTANCE AS WRITTEN: one selected and the other left out is answered by the other type's own provision where the call BUILDS the value (String's: 1; Bool: refused), and where the call TAKES a value whose type does not say the slot it is refused as the call with one requirement is (Box.directOf[T = Int64](box(a: 1, b: 5)), measured) — the refusal now names String where it named the provider selected for the other requirement. THE SAME-TYPE PAIR, decided by measurement: requires Plus: Mon[T] beside requires Times: Mon[T] is ONE SortRequiresInfo fact, one chain entry and one dictionary slot, and the body reads it by the goal, so the two are one requirement under two names; two providers for it stay refused (the wi844 and wi841 rows stand, reworded: 'for one requirement'), one under either name is its selection, and the same for an operation restating its sort's requirement or its own, compared by what no goal tells apart. TWO THINGS THE CHANGE NEEDED: a restated line is recorded at the first one's entry (it was recorded past the end of the chain: [Plus = Sum] alone and no selection at all were refused, 'position … could not be established'), and a named requirement's position is settled to the chain's once the facts are final (it was the source line's; resolve_requires_bindings moves a requirement with bindings behind a parameterless one — the wi840 row that pinned the old coupling is rewritten). BACK-OUT: nine mechanisms, each under a temporary switch over 387 rows, table in the test file's header. GATES: full workspace 9616 passed, 0 failed; the same under ANTHILL_TEST_NODE_CARRIER=1; no Scala file changed and the scaland suite was not run. /code-review: 13 findings — 7 fixed, 1 not reachable (a secondary entry may not state requires), 5 left: the spec text and the row below, the positional slot table (the binder on the requirement fact would replace the ordinal and the settling), a re-settle at every load (measured within noise), and a name-keyed selection across a dispatch that no row can drive. LEFT WITH THE USER, none filed: (1) kernel-language §5.4 is not edited — it still lists 'two keys selecting different witnesses for one spec' as a refusal and says biFold[plus = AddM, times = MulM](xs) distinguishes two slots of one spec; (2) whether two requirements of one sort at one type are to be two — the dictionary would hold two entries and the body need a way to say which it reads (Plus.combine(a, b) is refused today); (3) found while probing, present before this change: Desc.pair[other = Loud](coin(n: 5), "s") over operation pair[U](x: T, y: U) requires other: Tagger[T = U] loads and the selection is not handed to the member the call is dispatched to by its receiver's value — AmbiguousRequirement where it runs (the row a_selection_for_a_requirement_on_the_dispatched_spec_is_not_the_dispatchs records the outcome); and an operation taking two values of its sort is refused as a function value, with one named requirement as with two.

### 2026-10-13T11:58:09Z — feedback — claude

AFTER DELIVERY, on the user's word (2026-10-13, 'Do 1 and issue ticket for 2'): kernel-language §5.2 and §5.4 are written (2d6209c7) — what a requirement is, that one stated twice is one under two names, and that a selection is for one requirement; and the same-type pair as two requirements is filed, WI-20261013-50ZMN. STILL NOT FILED, the two defects found while probing: a selection for a spec operation's own requirement is not handed to the member the call is dispatched to, and an operation taking two values of its sort is refused as a function value.

### 2026-10-13T14:14:11Z — feedback — claude

THE TWO DEFECTS FOUND WHILE PROBING, delivered 2026-10-13 in cd231c81 on the user's word ('let check for the next report', then 'yes, change §5.2 and implement it', then 'commit and push'). (1) A SELECTION FOR A SPEC OPERATION'S OWN REQUIREMENT IS HANDED TO THE MEMBER THAT ANSWERS. It was worse than the tie this ticket recorded: where the argument's type has a provision of its own the selection was dropped with nothing said — Desc.cmp2[WeakOrd = ByLength](coin(n: 5), "bob", "amyy") answered 1, String's own order, where -1 is owed. The call's types and selections are the spec operation's; the member's requirement is written over a type parameter of its own. Where the member is known as the call is typed, its type parameters are bound to the spec operation's by position (the override check's pairing) and each requirement it states takes the selection for the spec operation's that reads the same, under its own name (call_at_member). Where the member is chosen when the call runs — deferred to a requirement the caller holds on its operation or its sort, a receiver typed as the spec or as an abstract sort providing it, a spec default body calling its sibling — the call is stamped for the spec operation and the evaluator hands the slots over under the member's slot names (stamp_spec_op_supply, member_slots_at_spec_op); no dictionary was built at such a call. kernel-language §5.2 says both. BEHAVIOUR THAT CHANGED WITH IT: a dispatched call with two providers and none selected, or at a type parameter of the caller it requires nothing of, is a load error, as the member's own spelling was (the wi_bqhgd fixture relied on the difference and states the clause); a rule-body goal whose member is known at load answers where it was refused for pinning no element; a rule-body goal whose member is found when it runs stays the bridge's (proposal 068 §3). (2) AN OPERATION OF SEVERAL PARAMETERS IS A FUNCTION VALUE AT A LABELLED ARROW. Not about two values of its sort: any operation of two or more parameters on a sort with a requirement was refused at (p: A, q: B) -> R and loaded at (A, B) -> R; the pin unified the two parameter tuples as data, which share no label, and relates them by position now. ROWS: spec_op_requirement_at_member_test (20 rows) and op_fn_value_labelled_arrow_test (5), each with its back-out table; this ticket's own row a_selection_for_a_requirement_on_the_dispatched_spec_is_not_the_dispatchs asserts 13. GATES: full workspace 9641 passed, 0 failed; the same under ANTHILL_TEST_NODE_CARRIER=1; anthill-core under ANTHILL_TYPER_ORACLE=1 8648 passed; no Scala file changed and scaland was not run. /code-review twice, 26 findings: 13 fixed, 7 needed no change, 6 left. NOT REACHED: the two instance-fact returns and the no-match licence are not stamped, no program having been built that reaches them; the Rust, C++ and Scala generators were not examined for the run-time route. FOUND WHILE PROBING, with the user and not filed: the override check refuses a member that restates the spec operation's requires in another order, in part, or unnamed where the spec names it; let f: (Plain[T = Int64]) -> Int64 = uno is refused for any operation of a parametric sort; an operation's own named requirement left unwritten at a call is refused as unconstrained with one provider; a rule named as the last segment of its namespace did not resolve by its qualified name.


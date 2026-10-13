## Attributes

- id: WI-20261013-0K8WD-a-call-s-selections-are-kept
- created: 2026-10-13T10:21:45Z

- status: Open
- status_agent: claude
- status_at: 2026-10-13T10:21:45Z

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


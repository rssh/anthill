## Attributes

- id: WI-20261013-50ZMN-two-requirements-of-one-sort
- created: 2026-10-13T11:57:50Z

- status: Open
- status_agent: claude
- status_at: 2026-10-13T11:57:50Z

- acceptance: cargo-test

- tags: typing

## Description

TWO REQUIREMENTS OF ONE SORT AT ONE TYPE ARE HELD AS ONE — so `requires Plus: Mon[T]`, `requires Times: Mon[T]` cannot be given a provider each, and a body has no way to say which of the two it reads (user, 2026-10-13: 'issue ticket for 2'; found on WI-20261013-0K8WD, which ends at requirements their bindings tell apart). It is proposal 058's opening case — `(Int64, +, 0)` beside `(Int64, ×, 1)` in one body — and its §3.3 / §4 example, `biFold[plus = AddM, times = MulM](xs)` over `requires plus: Monoid[T], times: Monoid[T]`.

MEASURED 2026-10-13 on 2d6209c7:

  sort Mon
    sort T = ?
    operation combine(a: T, b: T) -> T
  end
  sort Sum
    provides Mon[T = Int64]
    operation combine(a: Int64, b: Int64) -> Int64 = add(a, b)
  end
  sort Product
    provides Mon[T = Int64]
    operation combine(a: Int64, b: Int64) -> Int64 = mul(a, b)
  end
  sort Semi
    sort T = ?
    requires Plus: Mon[T]
    requires Times: Mon[T]
    operation mulAdd(a: T, b: T, c: T) -> T = Plus.combine(Times.combine(a, b), c)
  end
  Semi.mulAdd[T = Int64, Plus = Sum, Times = Product](2, 3, 4)

The answer owed is 10 — 2 × 3, then + 4. Two load errors. THE BODY: `Times.combine(a, b)` is 'unknown functor — no rule, fact, operation, entity, const or builtin is declared under that name'; a requirement's name is a type parameter, and no call is written through it. THE CALL: 'two providers are selected for Mon at the call to Semi.mulAdd: Sum and Product — for one requirement: a sort required twice at the same bindings is held once, under either name, and takes one provider'. With the body written `Mon.combine(Mon.combine(a, b), c)` the sort loads, and `[Plus = Sum]` answers 9, `[Times = Product]` 24, `[Plus = Sum, Times = Sum]` 9 — every call of the body through the one provider, whichever name wrote it — and a call that selects nothing is refused for the two providers there are. THE OPERATION-LEVEL TWIN, `operation biFold[T](a: T, b: T, c: T) -> T requires plus: Mon[T], times: Mon[T]`, is refused the same at `biFold[T = Int64, plus = Sum, times = Product](2, 3, 4)`. ROWS THAT HOLD THIS: wi_0k8wd_selection_per_requirement_test::a_requirement_stated_twice_is_one_requirement, ::an_operation_that_restates_a_requirement_holds_one and ::a_requirement_restated_with_a_parameter_left_open_is_the_same_one; wi844_sorted_set_driver_test::two_witnesses_for_one_spec_are_refused_whoever_wrote_them; wi841_call_site_selection_test::two_witnesses_for_one_spec_in_one_bracket_are_refused.

WHAT HOLDS IT AS ONE, in three places. (1) THE FACT: the two lines assert one `SortRequiresInfo(sort_ref: Semi, spec: Mon[T = Semi.T])` — the head is a hash-consed term, and the second assert is the first — so `direct_requires` reads one entry, the chain has one, and both names are recorded at it (`typing::place_of_requirement`, `NamedRequirementSlot`). (2) THE SLOT'S NAME: a dictionary slot is named from the sort it requires (`synth_req_names`, told apart by the spec term's identity), which two equal requirements share; an operation's own two entries are kept apart in its chain and bound under one frame name — measured on an intermediate build of 0K8WD, before its refusal of the pair was put back: `biFold[plus = Sum, times = Product](2, 3, 4)` answered 24 and the two swapped 9, both calls through `times`. (3) THE READ: a body's call asks for a requirement by its goal — `Mon.combine(a, b)` at `T` is `Mon[T = T]` — and takes the first entry of the frame that covers it; the goal names neither `Plus` nor `Times`. kernel-language §5.2 states the present rule: a requirement is the sort it names at its bindings, and one stated twice is one requirement under two names.

TO DECIDE BEFORE BUILDING, each over the program above:
  (a) HOW A BODY SAYS WHICH REQUIREMENT A CALL READS. `Plus.combine(a, b)` — a call through the requirement's name — is how the program is naturally written and is not in the language. What is: a forward into a callee's named slot, `Via.via[T = T, M = Plus](a, b)` over `sort Via` with `requires M: Mon[T]` and `operation via(a: T, b: T) -> T = Mon.combine(a, b)`, which loads today and reads the one dictionary under either name (0K8WD's `byNames` drives it), and would read `Plus`'s own once there are two.
  (b) WHAT A CALL THAT DOES NOT SAY MEANS. `Mon.combine(a, b)` in a body whose frame holds two requirements that cover it: refused naming both, as two constraining specs that declare one member are (§8.7), or the first, which is an answer by the order they are written in.
  (c) WHICH PAIRS ARE TWO. Two names (`Plus`, `Times`); a name beside an unnamed line (`requires Mon[T]`, `requires Times: Mon[T]`); a sort's requirement restated by an operation of the sort; two that differ only in a parameter one of them leaves unbound. 0K8WD keeps all four as one (`state_one_requirement`).
  (d) THE TYPE. `Semi[T = Int64, Plus = Sum, Times = Product]` has the two parameters already, and a value of it would carry two providers; whether one of the pair left out is inferred on its own (§5.2) follows from (c).

WHERE, found by reading and a lower bound — grep before scoping: the entry — `Loader::load_requires_decl` and the `SortRequiresInfo` fact (a third field carrying the binder is the form `KnowledgeBase::named_requirement_slots`' doc names; it would also replace `of_base` and `settle_named_requirement_slots`), and every reader of that relation outside the typer; the slot's name — `synth_req_names`, `op_dict_entries`, the frame's `__req_*` binding; the read — `resolve_inner`'s scope step, `find_requires_slot`, `find_requires_location`, `build_dep_projection`'s Strategy 1; the key — `slot_key_at` and `state_one_requirement` (typing/slots.rs), where 'one requirement' is decided for a selection.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh, driven by value): `Semi.mulAdd[T = Int64, Plus = Sum, Times = Product](2, 3, 4)` answers 10, and 20 with the two swapped, its body written as (a) decides; the operation-level `biFold` the same; the two carried by a value's type the same; the call that does not say is as (b) decides; the rows named above are replaced by rows that drive two, where (c) makes the pair two; kernel-language §5.2 and §5.4 and proposal 058 §3.3 / §4 say what holds. CONTROLS, each said at its site: two requirements at two types as 0K8WD left them (its rows); one requirement under one name; a requirement stated twice where (c) keeps it one; full workspace green.


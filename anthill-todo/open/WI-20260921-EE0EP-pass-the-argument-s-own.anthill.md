## Attributes

- id: WI-20260921-EE0EP-pass-the-argument-s-own
- created: 2026-09-21T19:01:33Z

- status: Open
- status_agent: user
- status_at: 2026-09-21T19:01:33Z

- acceptance: cargo-test

- tags: modinst

## Description

PASS THE ARGUMENT'S OWN DICTIONARY, SO `s.O` IS A CHANNEL AND NOT ONLY A NAME. A parameter whose type leaves a NAMED requirement slot unwritten is refused today; it should instead receive the ARGUMENT'S carrier dictionary and read the slot as a projection out of it. Then writing `O` and projecting `s.O` mean the same thing, which is what §5.4's quantifier rules already say they are.

THE ASYMMETRY, MEASURED (2026-09-21, on the merged tree, with `enum MySet requires O: WeakOrd[T]` and two rival `WeakOrd[String]` in scope):

  operation has(s: MySet[T = String], x: String) -> Bool = MySet.contains(s, x)
    -> LOAD ERROR: "leaves its named requirement slot `O: anthill.prelude.WeakOrd`
       universally quantified - the argument's type omits it, which means ANY provider,
       and no slot of this signature supplies its dictionary ... Write `O` in the
       parameter's type, or declare a NAMED slot for it and write that name there, so
       the caller supplies the value's own"

while the DECLARED-AND-FORWARDED spelling RUNS and the slot decides (`requires S: Searchable[C = C, Element = E]` over `List[T = C]`, two orderings, two answers - `wi_r10kc_spec_default_body_dictionary_test::a_generic_consumer_over_a_list_keeps_each_elements_ordering`).

DEPTH IS NOT THE AXIS, which is the measurement that says this is a missing channel rather than a rule about nesting. §"How the slot is named" (WI-1059) says a TOP-LEVEL unwritten slot IS the projection off the value that carries it - `s: Stream[T = Int64]` is checked as `s: Stream[T = Int64, E = s.E]` - so the slot HAS a name there, where a NESTED one (WI-1061) has only a fresh unnameable rigid. Both get the SAME refusal, word for word (`an_unwritten_named_slot_has_no_channel_at_any_depth` drives the pair). So the name exists and buys nothing, because a signature that omits the slot has nowhere for the caller to put a dictionary.

THE EVIDENCE IS ALREADY WHERE IT WOULD HAVE TO BE, which is what makes this cheap rather than a new representation. `dict_layout`'s PROVIDER half is the carrier's own `requires` chain, so a carrier's dictionary already NESTS its named slots' dictionaries. MEASURED, the frame of `MySet.insert` under `O = ByLength`:

  __req_self    => Dictionary( sub0 = Dictionary(...; impl: ByLength) ; impl: MySet )
  __req_weakord => Dictionary(...; impl: ByLength)          -- the same sub0

So `s.O`'s dictionary IS sub-dictionary k of `s`'s carrier dictionary, where k is `O`'s index in `MySet`'s chain. Nothing has to be added to the VALUE and nothing to the dictionary's shape; what is missing is that a callee whose parameter type omits the slot is handed no dictionary for `s` at all.

WHAT THIS IS NOT. Not WI-20260921-R10KC, which is Delivered and adjacent: there the dictionary EXISTS at the call site and never reached the frame that reads it, and the fix threads it. Here there is no slot in the signature to thread one THROUGH. Not WI-1094 either, though it is that ticket's other branch: WI-1094's own sub-question (a) put the two outcomes side by side - "the parameter case must either forward the value's own dictionary (058 §3.9's 'run time copies it along') or be REFUSED, and today it is neither" - and it shipped the refusal, correctly, because the defect it was closing was a SILENT WRONG ANSWER (a `SortedSet[O = Descending]` read back ascending). Taking the other branch now does not reopen that: forwarding the VALUE'S OWN dictionary is the opposite of constructing one from the signature, which is what read `3` instead of `7`.

WHAT TO DECIDE AT PICKUP.
 (a) WHICH PARAMETERS carry a dictionary - every parameter whose type has an unwritten named slot, or only those whose slot the body READS? The second is cheaper and the first is uniform; the body-reads question is answerable (the same walk `op_reads_requirement_slots` makes).
 (b) THE NESTED CASE. `List[T = MySet[T = String]]` has no `s` to project off - the element is reached by a pattern match, not by a parameter. Does the LIST's parameter dictionary reach it, or is the nested case still refused? A list has ONE element type and therefore one witness (`a_list_holds_one_witness_for_every_element`), so there is a single right answer to carry; whether the channel reaches it is the question.
 (c) WHETHER THE REFUSAL SURVIVES for anything. An EXISTENTIAL RETURN opened to a rigid skolem (`operation mk() -> MySet[T = String]`, WI-1063) names no provider at all, so there is nothing for a caller to forward - that one must stay refused, and the diagnostic should then say WHY it differs from the parameter case rather than printing today's shared sentence.
 (d) WHETHER `s.O` BECOMES WRITABLE in a signature, or stays implicit. The projection is already a legal type (`RigidTypeProjection`, path-dependent-types.md §5.3); making it the spelling of the channel would let an author name the slot without declaring a `requires`.

ACCEPTANCE: `operation has(s: MySet[T = String], x: String) = MySet.contains(s, x)` LOADS and ANSWERS BY THE VALUE'S OWN COMPARATOR - driven at BOTH rival orderings over ONE body, so one answer twice fails; WI-1094's `erase3` shape (`SortedSet[T = Int64, O = Descending]` through a signature that omits `O`) reads back `7` and not `3`, which is the same test WI-1094 pinned as REFUSED, inverted rather than deleted; `an_unwritten_named_slot_has_no_channel_at_any_depth` inverts or is re-justified per (b); the existential-return row of `wi_r10kc_spec_default_body_dictionary_test` still refuses, per (c), and its message is re-read to say why; each test says which case fails when the change is backed out; full workspace green via rustland/scripts/test.sh.

REFERENCE: docs/design/path-dependent-types.md §5.5 (written by R10KC; its last paragraph IS this question), §5.3 `RigidTypeProjection`; docs/kernel-language.md §"How the slot is named" (WI-1059), §"Which skolem, by depth" (WI-1061), §"In a RETURN the quantifier flips to exists" (WI-1063), and the named-slot paragraph this ticket would amend; 058 §3.4, §3.9. Driver fixtures: `wi_r10kc_spec_default_body_dictionary_test`, `wi858_pair_orderings_test`.


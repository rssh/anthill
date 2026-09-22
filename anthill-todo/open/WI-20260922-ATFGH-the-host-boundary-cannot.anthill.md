## Attributes

- id: WI-20260922-ATFGH-the-host-boundary-cannot
- created: 2026-09-22T14:51:56Z

- status: Open
- status_agent: user
- status_at: 2026-09-22T14:51:56Z

- acceptance: cargo-test

- tags: typing

## Description

THE HOST BOUNDARY CANNOT SUPPLY AN OP-SCOPED REQUIREMENT, SO AN UNFILLED ONE ANSWERS FROM THE DATA INSTEAD OF SAYING SO. Found by /code-review during WI-20260921-EE0EP; pinned there as `wi_ee0ep_param_dictionary_test::the_host_entry_does_not_receive_the_parameters_dictionary`.

THE MEASUREMENT. One operation, one pair of values, two routes:

  operation has(s: MySet[T = String], x: String) -> Bool = MySet.contains(s, x)

  TYPED (an anthill call site)  byLength = true    alphabetical = false
  HOST  (`interp.call`)         byLength = false   alphabetical = false

One answer twice, silently. `interp.call` passes VALUES and no types; a `Value::Entity` is `{ functor, pos, named }` and carries its sort and none of its type arguments (058 §4.7), so the slot EE0EP synthesizes is unfilled and value-direction answers — recovering the element type and never the witness.

IT FALSIFIES A RECORDED PREDICTION, which is what makes this a ticket rather than a known cost. `Interpreter::call_with_requirements` is the entry that DOES take host-supplied dictionaries, and it counts the PARENT SORT's chain only. Its doc says of the op half: "an op-scoped `requires` has no host-boundary spelling ... Nothing in tree declares an entry op with its own `requires`; if one ever does, its slots stay unfilled here and the body's own read is what says so." EE0EP synthesizes exactly such a slot, so the case now exists — and the consolation is untrue: the read does not say so, value-direction rescues it with a wrong answer.

WHAT TO DECIDE AT PICKUP.
 (a) LOUD FIRST, and it may be the whole ticket. An unfilled slot that value-direction then answers is the silent class; making that raise restores what the `call_with_requirements` doc already promises. Narrow it to the slots a host cannot spell rather than to `SupplySource::FromParam`, or the same hole reopens for the next synthesized kind.
 (b) THE SPELLING. Then let a host supply the op half: either widen `call_with_requirements` past the parent-sort chain, or take a witness per slot (`O = ByLength`) and build the dictionary from it. The second is the smaller surface and the one a host can actually produce — WI-822 records that a host "has no way to build" handles for an op-scoped element, and naming the witness sidesteps that.
 (c) NOT BY PASSING TYPES. Runtime needs the DICTIONARY; the type is only where a typed call site reads the witness from, at compile time. A type-taking host API would import a compile-time artifact into a runtime boundary. Recorded because it was the first idea and it is the wrong one.
 (d) WHETHER WI-868'S STAND-IN SURVIVES. `seed_entry_requirements` fabricates self-rooted stand-ins so `interp.call` works at all on a sort with a `requires`, with three measurements behind it at `Interpreter::stand_in_requirement`. (a) must not break that; the stand-in is for the SORT half.

ACCEPTANCE: the two routes above AGREE, driven at both rival orderings, or the host route REFUSES naming the slot — never one answer twice; EE0EP's pinned row flips from asserting `false` to asserting the agreement, and says what it asserted before; WI-868's three stand-in measurements still hold, each named; full workspace green via rustland/scripts/test.sh.

REFERENCE: `Interpreter::call_with_requirements` and `seed_entry_requirements` (eval/mod.rs), `wi_r10kc_spec_default_body_dictionary_test::the_host_entry_route_answers_by_value_direction`, docs/design/path-dependent-types.md §5.5, docs/design/operation-call-model.md §"Host-to-entry-op boundary", 058 §4.7.


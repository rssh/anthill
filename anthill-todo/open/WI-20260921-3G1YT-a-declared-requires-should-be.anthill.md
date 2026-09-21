## Attributes

- id: WI-20260921-3G1YT-a-declared-requires-should-be
- created: 2026-09-21T14:16:49Z

- status: Open
- status_agent: user
- status_at: 2026-09-21T14:16:49Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A DECLARED `requires` SHOULD BE OWED BY THE CALLER BECAUSE IT IS DECLARED, not because the callee currently reads it. Decided by the user, 2026-09-21, during WI-20260921-28TAT.

THE RULE TODAY (kernel-language.md §8.7, last sentence of "Where the ambiguity error is raised"). An unpinnable requirement at a call site is PARKED and reported only where the callee will actually miss the dictionary — `report_unsuppliable_requirements`' `if !reads { continue; }` (typing.rs), asking `op_body_reads_sort_requirement_slot` / `op_body_reads_op_requirement_slot`. It rests on a measurement recorded at the site: 29 stdlib bodies declare a chain and NEVER READ IT.

WHY IT IS WRONG. That measurement establishes those clauses are UNREAD, not that they are UNOWED — and the repair for such a body is to delete the clause it does not use. Three defects follow: (1) a caller admitted on the strength of the callee's PRESENT body breaks when that body changes, with nothing at the call site having moved; (2) the "does the body read it" test is a walk of the callee's body, so it answers "reads nothing" for a callee that HAS no body — WI-20260921-28TAT hit exactly that with `Error.reify`, which is body-less and implemented by the interpreter, and 23 unevidenced reify call sites passed in silence; (3) the rule already needed one per-spec exemption carved out of it (N31XX's "an unfilled `TypeValue` slot is NEVER benign"), which is usually the sign of a wrong rule rather than a special case.

THE CHANGE. Delete the `if !reads { continue; }` gate, so every parked refusal is reported. That also kills the machinery behind it — `op_body_reads_sort_requirement_slot`, `op_body_reads_op_requirement_slot`, `SlotToRead`, and 28TAT's `native_backing_reads_slots` — roughly 250 lines.

MEASURED, and this is the ticket's starting point: with the gate removed the core suite is 4808 passed / 21 FAILED. FOUR are control rows asserting the old rule by name and would be rewritten, not fixed (`wi1102::control_a_body_that_never_reads_the_slot_still_runs`, `wi945::control_a_callee_that_never_reads_the_slot`, `wi_xsvcs::a_slot_the_callee_never_reads_still_loads_and_answers`, `wi855::other_unresolvable_causes_still_enter_unsupplied`).

THE OTHER SEVENTEEN ARE THE BLOCKER, and they are the stdlib's own generic combinators — `x13yv_map_map_chain_test` (5), `n01py_witness_provision_subtype_test` (5), `wi508_nullary_carrier_dispatch_test` (2), `wi599`, `typer_capability_matrix`, `wi1119`, `wi201`, `wi999`. The diagnostic is one shape:
  `anthill.prelude.MappedStream.map.requires`: requirement `Iterable[C = MappedStream.Source, Element = MappedStream.Src, E = MappedStream.ES]` cannot be supplied: element `C = MappedStream.Source` is unconstrained at this call site.
`MappedStream` declares `requires Iterable[C = Source, ...]` at SORT level and a call on a mapped-stream receiver pins no `Source`, so no dictionary can be built. The clause is not noise — a mapped stream's source genuinely must be iterable — so it cannot be deleted.

SO THIS DEPENDS ON INFERENCE THAT PINS A RECEIVER'S SORT PARAMETERS FROM THE RECEIVER'S TYPE. That is the real prerequisite and it is not scoped here.

ACCEPTANCE:
 - the gate is gone and the three read-predicates with it, each deletion explained;
 - a caller that cannot supply a declared `requires` is refused, DRIVEN, with the message naming the clause;
 - its control: the same call with the clause suppliable loads and answers;
 - the four control rows are rewritten to assert the NEW rule, each saying what it asserted before;
 - the seventeen stdlib-combinator rows answer what they answer today — i.e. the receiver-parameter inference exists;
 - kernel-language.md §8.7's paragraph is rewritten to the new rule (WI-20260921-28TAT already corrected it to describe the CONDITIONAL refusal accurately; this replaces that);
 - full workspace green via rustland/scripts/test.sh; scaland `sbt testFull`.


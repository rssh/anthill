## Attributes

- id: WI-20260911-6B67S-receiver-bound-requirement
- created: 2026-09-11T16:27:08Z

- status: Open
- status_agent: claude
- status_at: 2026-09-11T16:27:08Z

- acceptance: cargo-test, scaland-sbt-test

## Description

RECEIVER-BOUND REQUIREMENT SLOT: the diagnostic says the witness PROVIDES the spec when it
provides nothing. The receiver channel skips `validate_instance_selection`, so
`check_selection_bindings` fires on an invariant only the CALLEE channel establishes.

FOUND BY `/code-review` during WI-20260911-7TN1Q; REPRODUCED independently 2026-09-11 at
189f7603 plus that delivery. PRE-EXISTING in WI-20260911-RS2G4, which is what made the
receiver bracket bind at all.

THE PROGRAM. A witness that provides nothing, selected through each of 035's two spellings:

    sort NotOrd
      entity notOrd
    end
    operation viaRecv()   -> SortedSet[T = Int64] = SortedSet[T = Int64, O = NotOrd].empty()
    operation viaCallee() -> SortedSet[T = Int64] = SortedSet.empty[T = Int64, O = NotOrd]()

MEASURED. Both refuse; only one tells the truth.

  RECEIVER: "expected a provider of anthill.prelude.WeakOrd, got probe.NotOrd PROVIDES
    anthill.prelude.WeakOrd, BUT NOT AT THE BINDINGS this call to
    anthill.prelude.SortedSet.empty needs — the selected witness must provide the spec AS
    INSTANTIATED here, not merely somewhere"

  CALLEE: "... got probe.NotOrd DOES NOT PROVIDE anthill.prelude.WeakOrd — a call-site
    `[WeakOrd = NotOrd]` on anthill.prelude.SortedSet.empty must name a sort that declares
    `fact anthill.prelude.WeakOrd[...]` or `provides anthill.prelude.WeakOrd[...]`"

`NotOrd` declares no `fact` and no `provides`, so the receiver message is FALSE and it
sends the author looking for a binding mismatch that does not exist. The same split
appears for `O = List[T = Int64]` ("anthill.prelude.List provides WeakOrd, but not at the
bindings ..."). This is the one place RS2G4's "one rule, two spellings, same bytes" claim
is untrue.

THE CAUSE, located rather than guessed. `check_selection_bindings` sets `at_bindings: true`
under the comment "Reached only past `validate_instance_selection`, which already
established that the witness provides the spec SOMEWHERE". `seed_receiver_type_args` never
calls `validate_instance_selection`; its own doc says so ("WHAT THIS LEG DOES NOT DO ...
this leg runs neither") but states the consequence as "accepted with the slot quietly
unselected". MEASURED, that is not what happens: the slot IS selected — through the
type-carried producer `selections_from_slot_bindings`, which reads the parameter back out
of sigma — and is then refused with the wrong branch. So the existing comment names the
gap and mis-states its effect; both halves want fixing.

THE FIX, two candidate directions; choosing between them is this ticket's work.
  * Route the receiver's slot bindings through `validate_instance_selection` /
    `check_witness_provides_spec`. That is "one rule, two spellings", and it also picks up
    the `SelectionValueNotASort` check this leg skips. But it changes what a
    receiver-bound slot is ALLOWED to be, and an ARGUMENT carrying the same type has always
    reached the unvalidated producer too (RS2G4's own note), so it needs its own census.
  * Or have `check_selection_bindings` fall back to the `at_bindings: false` wording when
    it cannot establish "provides somewhere". Smaller, changes no verdict, repairs only the
    message.

ACCEPTANCE.
  * The two programs above produce the SAME diagnostic, and it is the true one.
  * CONTROL: a witness that DOES provide the spec but not at these bindings keeps the
    `at_bindings: true` message in BOTH spellings. That is what separates "the wrong
    branch" from "no branch", and a fix that makes both spellings say "does not provide"
    unconditionally fails it.
  * RS2G4's stale comment is corrected wherever it survives.
  * cargo-test green via rustland/scripts/test.sh.

REFERENCE: `check_selection_bindings` / `validate_instance_selection` /
`selections_from_slot_bindings` / `seed_receiver_type_args` (typing.rs); WI-20260911-RS2G4
(the receiver bracket); WI-20260911-7TN1Q (the review pass that found it).


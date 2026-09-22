## Attributes

- id: WI-20260911-6B67S-receiver-bound-requirement
- created: 2026-09-11T16:27:08Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-22T20:20:51Z

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

## Changes

### 2026-09-22T20:20:45Z — feedback — user

DELIVERED, and NOT where the ticket expected. Neither candidate direction landed: the fix
is at the PRODUCER, `selections_from_slot_bindings`, which now runs §4.4 check 1 itself.
`check_selection_bindings`' `at_bindings: true` is a literal again — the invariant is now
TRUE rather than asked about.

WHAT LOCATED IT. The producer was inconsistent BY EXACTLY ONE LEVEL: it already ran check
1 on every NESTED slot witness (`witness_value_slot_selections` -> `check_slot_witnesses_
provide`) and on none of its TOP-LEVEL ones. A nested `ListOrd[OE = NotOrd]` was refused
by name while the `O = NotOrd` carrying it was passed downstream to be guessed about.

WHY NOT DIRECTION 1 (route the receiver leg through `validate_instance_selection`). A
THIRD program, which the ticket did not know about, reaches the same false message with NO
BRACKET WRITTEN ANYWHERE:

    operation viaArg(s: SortedSet[T = Int64, O = NotOrd]) -> List[T = Int64] =
      SortedSet.toList(s)

The slot rides in the ARGUMENT'S TYPE and the σ-read producer reads it back out of sigma.
A receiver-leg repair has no bracket to hook onto.

WHY NOT DIRECTION 2 (fall back to the `at_bindings: false` wording at the consumer). Built
and measured first; rejected on two counts. (a) `check_selection_bindings` `continue`s
when the goal has no candidates, so with an ABSTRACT element the refusal falls through to
`resolve`'s step 0 and renders the SAME false claim one rung down -- `gArg[E](s: SortedSet
[T = E, O = NotOrd])` got "the call selected NotOrd ..., which provides no instance at
these bindings". Check 1 at the producer runs before any goal is formed and closes it.
(b) the producer's OTHER caller, the eta path, runs no `check_selection_bindings` at all,
so a consumer repair leaves that channel unchecked either way.

A SECOND, SILENT DEFECT WAS FOUND AND CLOSED IN THE SAME PLACE. A slot value with no sort
head was `continue`d. RS2G4's comment called that "accepted with the slot quietly
unselected"; MEASURED, it is worse -- `SortedSet[T = Int64, O = (Int64, Int64)].empty()`
LOADED CLEAN with the written `O` DROPPED and the requirement answered by an ordinary
search, so the call silently got a different provider's answer. It only looks reported
when two providers happen to tie, and then as an AMBIGUITY. Now `SelectionValueNotASort`,
the same refusal the callee bracket has always made.

THIS IS A VERDICT CHANGE, not a message change, and the ticket's census does not cover it.
RS2G4's "no form-(3) call in stdlib/examples/anthill-todo" was scoped to the RECEIVER
BRACKET; the new check also fires on the ARGUMENT-TYPE channel, which is far more widely
used. The suite is the census, and it did its job: a first cut refused on every
`sort_functor_of == None` and broke §7.1 forwarding outright -- 11 rows across wi1094,
wi844, wi_ee0ep and wi_r10kc, every one an UNWRITTEN slot taking its argument's own
comparator. `is_type_param_value` reads a flex var and a sort PARAMETER as abstract and
says NOTHING about a skolem or the `s.O` `UnwrittenFill::Projection` that fills an
unwritten slot, so the ordering argument that looked like safety was not one. The refusal
is now narrowed to `SlotBinderState::NoWitnessReading` -- arrow, tuple, effect row,
denoted -- asked of `slot_binder_state` rather than inferred from the `None`. That makes
that enum variant's separate existence load-bearing rather than documentary.

TWO DIAGNOSTIC CORRECTIONS, both found by `/code-review`, both in this ticket's own family:
  * the `at_bindings: false` arm said "a call-site `[WeakOrd = NotOrd]` on ...", naming
    syntax the argument channel's author never wrote. Now channel-neutral ("a selection of
    `WeakOrd = NotOrd` at ..."); the actionable repair clause is unchanged.
  * `WitnessDoesNotProvide` and `SelectionValueNotASort` mapped to `field_name: "type_arg"`
    and rendered `...toList.type_arg` for programs with no type arg. Now "selection", which
    is the rule WI-844 already states three arms down for `ConflictingSelection`.

ACCEPTANCE.
  * The ticket's two programs produce the SAME diagnostic, byte for byte, and it is the
    true one. So does the third (argument) channel, and so does the abstract-element case.
  * CONTROL HELD: `ByLength`, which really does provide `WeakOrd[T = String]`, asked at
    `T = Int64` keeps the `at_bindings` wording in ALL THREE channels. Green before and
    after -- that is what makes it a control.
  * RS2G4's stale comment corrected at `seed_receiver_type_args`, and the same
    mis-statement corrected where it had been quoted as a justification at
    `selections_from_slot_bindings` and `SlotBinderState::NoWitnessReading`.
  * cargo-test green via rustland/scripts/test.sh (full workspace, 36 binaries, exit 0);
    scaland `sbt testFull` 578/578 (it carries no instance-selection machinery).

BACK-OUT, MEASURED one mechanism at a time over the file's 8 rows: (M1) check 1 at the
producer -> 4 red; (M2) the headless refusal -> 1 red; (M3) the channel-neutral wording ->
1 red. The control and the driven accept path pass either way by design and are named as
such at their sites.

NO FORWARDING FIXTURE IS COPIED INTO THE NEW FILE, deliberately. wi1094 / wi_ee0ep / wi844
/ wi_r10kc own that shape with 11 rows and are what CAUGHT the over-refusal; the header
cites them. A local copy was written and deleted -- and the copy it replaced (a slot bound
to a DECLARED parameter) had passed straight through the broken version, which is the
sharper lesson: a forwarding fixture is a control here only in the UNWRITTEN spelling, and
the wrong one buys a green light and no safety.

STILL OPEN, PINNED BY A ROW THAT FAILS THE DAY IT CLOSES: §4.4 CHECK 3
(`ValueDirectedSelection`) on the receiver bracket -- `SortedSet[T = String, O = ConcOrd]
.empty()` loads where the callee spelling refuses. Check 3 refuses a SPELLING, so unlike
check 1 it cannot move to the producer: that channel has no spelling, and a TYPE may
legitimately carry a concrete witness. It needs its own copy at `seed_receiver_type_args`,
and is left as a verdict change with no measured victim.

NOTED, NOT FIXED (pre-existing, unchanged by this delivery): `impl_sorts_providing_spec`,
which check 1 reads, applies neither the conversion-edge filter nor the derived-through-
conversion skip that `collect_provides_candidates` applies. `O = Ord` therefore reports
"Ord provides WeakOrd, but not at the bindings ..." though `sort Ord provides WeakOrd[T =
T]` is a conversion edge whose own comment says "nothing has type Ord". Same false-message
class, one relation over; both spellings agree today, so it is not an asymmetry.


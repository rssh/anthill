## Attributes

- id: WI-20260921-159S9-make-the-op-scoped-requirement
- created: 2026-09-21T14:58:46Z

- status: Open
- status_agent: user
- status_at: 2026-09-21T14:58:46Z

- acceptance: cargo-test

## Description

Make the OP-SCOPED requirement channel reliable enough to supply a CROSS-SORT call, so that a slot declared on an operation is as good as one declared on its sort. MEASURED, two programs differing only in where the slot is written (scratchpad probes opslot.anthill / opslot2.anthill, reconstructible in ten lines): `sort OnSort { sort E = ?  requires OE: WeakOrd[E]  operation ins(s: SortedSet[T = E, O = OE], x: E) = SortedSet.insert(s, x) }` RUNS and prints zz; moving the identical clause onto the operation — `operation ins[E, OE](s: SortedSet[T = E, O = OE], x: E) requires OE: WeakOrd[E] = SortedSet.insert(s, x)` — is REFUSED AT LOAD by WI-456's no_scope_route arm ("a slot declared on the OPERATION does not reach this call"). Two spellings of one program, one of which does not work, which is the same shape WI-822 LEG 1 closed for receiverless dispatch and did not close here.

WHY IT IS NOT "read the op half at the call site", and this is the whole content of the ticket: the instance-dictionary builders read TypingEnv::enclosing_chain — the SORT half — ON PURPOSE, because that channel is read STRICTLY at eval while several routes into an operation fill NO op slot (a host interp.call: seed_entry_requirements cannot seed one, since a stand-in is rooted at the PARENT SORT and would mis-dispatch; an eta'd OpRef; a dictionary-directed dispatch). Composing the chain was MEASURED and rejected: the blame moves onto the CALLER for a slot no route ever gives it, where the sort-only chain names the callee whose own requires genuinely went unsupplied. That measurement is pinned as wi822_op_scoped_supply_test::the_instance_dictionary_channel_never_forwards_an_op_slot, which FLIPS if anyone composes the chain. Deferring on every op-scoped call was also tried and broke 30 tests (wi842/wi843/wi855/wi876/wi886/wi869 + the eta route), which is why a body reads an op slot on exactly ONE route today: a dispatch that TIES (op_scoped_defer_location, called only from the Ambiguous arm).

SO THE WORK IS THE ENTRY SIDE, not the call site: make every route that enters an operation fill its op-scoped slots, and only then let the instance-dictionary builder read the composed chain. Blast radius is the requirement ABI — WI-822's own words, "synth_req_names, expand_dispatching_dict, start_apply_deferred, call_with_requirements, seed_entry_requirements, classify_pin_or_apply_within and record_apply_within_concrete are all sort-keyed", plus the whole stdlib and anthill-todo.

CONTEXT THAT RAISED THE PRIORITY: WI-28TAT removes the frame type-argument channel and WI-N31XX is shrinking it. When the requirement channel is the ONLY channel, op-level `requires` stops being a corner and becomes load-bearing, and these three unfilled entry routes become holes in the only mechanism.

NOT A REOPEN OF WI-822, which delivered both its legs and recorded this residue deliberately ("RESIDUE, recorded not ticketed (101 open unblocked)"); this is the successor with a fix direction neither leg attempted. Related: WI-456 (the refusal that now names this at load), WI-841's an_op_scoped_selection_that_could_differ_is_refused_not_ignored (the same placement question one coordinate over).

ACCEPTANCE: the (B) spelling above RUNS and prints zz, and answers aaa when its caller's set is built with O = Alphabetical (one polymorphic body, two orderings — so one answer twice means the slot decided nothing); wi456_no_scope_route_test::an_op_scoped_slot_is_refused_for_now INVERTS to a value assertion rather than being deleted; the_instance_dictionary_channel_never_forwards_an_op_slot is re-derived rather than merely re-pointed — if the chain is composed, its attribution assertion must be replaced by a measurement saying who SHOULD be blamed once the op half is reliably filled; op_scoped_relay_chain_correct_via_value_direction still computes 551; full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-09-21T15:38:33Z — feedback — claude

ONE ROUTE'S SHORTCUT REFUTED, from WI-20260921-28TAT — recorded here so it is not retried. `start_apply_deferred` is named in this ticket's blast radius; this is what happens if you try to fill it from the CALL SITE instead of the entry side.

THE ATTEMPT. The two `CallClass::DeferToRequirement` arms call `classify()` directly rather than through `classify_pin_or_apply_within`, so they stamp no op-scoped dictionaries, and `start_apply_deferred` installs the SORT half alone. The obvious repair is to stamp there for the SPEC op (`fn_sym`), on the reading that §8.7 forbids an override from STRENGTHENING a clause — so the spec's chain looks like the one both ends share.

IT IS WRONG, and eval's own count guard says so. The impl is chosen at run time and lays out its OWN op-scoped chain; "not strengthened" does not mean "same layout". MEASURED: `wi456_sorted_set_collection_test::generic_consumer_keeps_the_carriers_ordering` failed with `EvalError::Internal("op-scoped frame push: the call site supplied 1 slot(s) for `anthill.prelude.PersistentCollection.insert`, but dispatch landed on `anthill.prelude.SortedSet.insert`")`. The stamp holds `TermId`s built from the CALLER's substitution against the SPEC's chain, and nothing at eval can re-key them onto a different declaration — which is this ticket's own conclusion ("the work is the ENTRY side, not the call site") arriving from the other direction. Reverted; the site in `check_apply_iter`'s spec-op exit carries the note.

WHAT 28TAT LEFT IN PLACE that bears on the acceptance here. Op-level evidence is no longer a field of `CallClass::ConcreteApplyWithin`: it is a `NodeOccurrence` stamp (`op_dicts`) written by ONE function (`stamp_op_scoped_dicts`) and read on every apply route, so "what a call carries" is now independent of "where it dispatches". Three writers stamp it today — `classify_pin_or_apply_within` (which also covers the `PinNow` arm, where the build used to be discarded), the Direct arm, and a new site at the spec-op exit for a call NO arm classified. The defer arms are the remaining hole, and the gate there (`occ.classification_is_none()`) documents that it does not cover them.

ALSO FROM 28TAT, and it is the reason the priority note in the description is now literal rather than anticipated: the frame type-argument channel IS GONE (commit on `main`), so the requirement channel is the only channel. `Error.reify` is the first operation whose op-level `requires` is load-bearing at run time — the reify boundary reads its payload sort out of that dictionary — and an unsupplied slot there is a LOAD ERROR rather than a silent widening (`native_backing_reads_slots`: body-less is not "reads nothing" when the backing is the interpreter).

SUPERSEDES WI-20260921-6JP6N, filed by me before I saw this ticket and rejected as a duplicate: it scoped the same defect at the call site, which is the framing this ticket already argues against.


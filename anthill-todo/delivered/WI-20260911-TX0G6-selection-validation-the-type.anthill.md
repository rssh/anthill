## Attributes

- id: WI-20260911-TX0G6-selection-validation-the-type
- created: 2026-09-11T14:39:56Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-23T08:20:12Z

- acceptance: cargo-test, scaland-sbt-test

## Description

SELECTION VALIDATION: the TYPE-CARRIED producer runs neither of the BRACKET producer's
two checks, so one provider choice is refused at one spelling and silently unselected at
the other — 058 §3.5/§4.4 enforced on one of its two channels.

FOUND by `/code-review` (high) on WI-20260911-RS2G4, 2026-09-11. PRE-EXISTING: the
asymmetry is between the two producers of one selection channel, and RS2G4 is named only
because it adds a third way to reach the unvalidated one.

THE TWO PRODUCERS, both WI-844's "three producers of one channel" (058-implementation §2):
  * THE BRACKET — `seed_op_type_args`. For a binding whose target is a requirement slot it
    runs `selection_witness_sym(...).ok_or(SelectionValueNotASort)?` and then
    `validate_instance_selection` (§4.4 check 1 — the witness provides the spec at the
    call's own bindings; §3.5 check 3 — it may not be a CONCRETE provider).
  * THE TYPE — `selections_from_slot_bindings`, which reads the slot's parameter back out
    of sigma once argument unification is done. It runs NEITHER: a value with no sort head
    takes a `continue` (`let Some(witness) = sort_functor_of(kb, bound) else { continue }`)
    and no witness is ever handed to `validate_instance_selection`.

  So the slot is quietly left unselected where the bracket spelling is loud. That is the
  silent skip the house rule forbids, and it reaches the type producer's THREE inputs: an
  ARGUMENT whose type carries the slot (WI-844's own case, the oldest), an eta'd op
  reference's expected arrow (`attach_eta_dispatch_dict`), and — since
  WI-20260911-RS2G4 — a companion RECEIVER's bracket, which binds the sort's parameters
  and is therefore read back through this producer rather than through the bracket one.

TO BE MEASURED FIRST, because the shape below is constructed and not observed:

    SortedSet.empty[T = Int64, O = <not a sort>]()     refused (bracket producer)
    SortedSet[T = Int64, O = <not a sort>].empty()     accepted? (type producer)

  and the same pair with a CONCRETE provider in the `O` position (§3.5 check 3). The
  delivery must DRIVE both spellings and report the verdicts before proposing anything —
  RS2G4's census found NO form-(3) call anywhere in `stdlib/`, `examples/` or the loaded
  `anthill-todo` code, so this is latent and nothing forces the shape today.

WHY IT IS NOT A ONE-LINE MOVE. Giving the type producer the bracket producer's checks
changes what an ARGUMENT-CARRIED selection is allowed to be, which is a much older and
much wider population than the receiver bracket RS2G4 added. `validate_instance_selection`
check 3 refuses naming a CONCRETE provider on the reasoning that at a call site "the
argument's own value already directs the dispatch" — and a selection read OUT OF an
argument's type is exactly that case, so the check may be WRONG there rather than merely
missing. Decide which of the two checks belongs on which producer before moving either.

ACCEPTANCE.
  * The two spellings above give the SAME verdict, driven, with the message compared
    byte-for-byte the way RS2G4's `the_receiver_spelling_reads_as_the_callee_spelling`
    does.
  * Each check is decided SEPARATELY and the decision is recorded: check 1 (provides the
    spec at these bindings) and check 3 (not a concrete provider) are different rules with
    different reasons, and §3.5's own argument bears on check 3 only.
  * A CENSUS of what the change newly refuses over the three corpora and the full suite,
    reported separately for the argument-carried and the bracket-carried populations —
    the argument one is the large one.
  * Whatever is deliberately left unchecked says so at the site, with the reason, so the
    next reader finds the boundary measured rather than assumed.
  * cargo-test green via rustland/scripts/test.sh.

REFERENCE: `seed_op_type_args` and `selections_from_slot_bindings` (typing.rs);
`validate_instance_selection`, `witness_value_slot_selections`, `push_selection`;
WI-844 (the type-carried producer), WI-841 (§4.4's binding-precise validation),
WI-870 (§3.3 nested slot bindings), proposal 058 §3.4/§3.5/§4.4/§4.7;
WI-20260911-RS2G4 (the receiver leg, and the comment at `seed_receiver_type_args` that
records this).

## Changes

### 2026-09-11T14:40:37Z — feedback — claude

RUST-ONLY: scaland loads no operations, so it has no call-site bracket and no twin to keep in step.

### 2026-09-23T08:20:12Z — feedback — claude

DELIVERED. The two bracket spellings of a slot selection now validate through ONE owner,
`validate_written_selection`, so they agree by construction. The type channel keeps
check 1 only, as a measured decision.

MEASURED FIRST, before any change (scratch probes, deleted). callee = `SortedSet.empty[…, O = W]()`,
receiver = `SortedSet[…, O = W].empty()`, type = a parameter/result/let typed `O = W`:

  O = (Int64, Int64)  no sort head   callee refused / receiver refused, same bytes / type refused   (6B67S)
  O = NotOrd          provides none  refused / refused, same bytes / refused                        (6B67S)
  O = ConcOrd         concrete       REFUSED (check 3) / LOADED / loads
  O = Pair            concrete self  REFUSED (check 3) / LOADED / loads
  O = OE (R's slot)   a forward      REFUSED "R.OE does not provide WeakOrd" / LOADED, ran the
                                     caller's order / loads
  O = P (plain param) not a slot     refused / LOADED, and a set typed O = ByLength ordered by
                                     OE's RevLen (silent wrong answer) / loads, same wrong order

So 6B67S had already closed the ticket's `<not a sort>` pair. Found open: check 3 on the
receiver, a false check-1 refusal of a forward on the callee, and the receiver's silent
wrong order for a plain parameter.

THE DECISION, ONE CHECK AT A TIME (recorded at each site):
  * CHECK 1: every channel, at the σ-read producer (6B67S). Unchanged.
  * CHECK 3: the two WRITTEN channels only, the callee's (already) and now the receiver's,
    through one owner. NOT the type channel. A type legitimately carries a concrete
    witness: WI-1094's inference WRITES one (`SortedSet.empty[T = Pair[…]]()` types as
    `O = Pair`), and every later call reads it back. Result, parameter and eta typings of
    `O = ConcOrd` load and RUN in ConcOrd's order (driven). The census below measures
    what check 3 on the type channel would break.
  * FORWARD: a value naming one of the enclosing declaration's OWN NAMED SLOTS forwards in
    both spellings (`names_a_declared_slot`). A plain parameter does not. A forward is
    answered by the slot's GOAL, keyed by spec, so `[O = P]` got OE's dictionary. It is
    refused in both spellings now. A rung-2 (spec short name) key binds no parameter, so it
    keeps check 1's refusal even for a slot-naming value.

CENSUS, by counters at the three sites (callee leg, receiver leg, σ-read producer),
attributed per test, over `anthill load` of stdlib (embedded), examples/github-todo,
rustland/anthill-todo/anthill and anthill-stl, and over the WHOLE workspace suite. Removed
afterwards.
  CORPORA: 0 hits at every site in all four. Statically too: no form-(3) call; SortedSet's O is
    the only named slot and is bound only to O itself inside sortedset.anthill. No corpus
    verdict flips in either direction.
  SUITE, pre-existing tests only (every hit is in wi_tests):
    BRACKET-CARRIED
      receiver slot bindings    4 calls / 4 tests, all 6B67S rows: 2 ok, 1 check-1,
                                1 no-sort-head (same verdicts, now raised at the receiver's leg).
                                NEWLY REFUSED: 0. No abstract receiver binding exists, so the
                                plain-parameter refusal also flips nothing.
      callee named-slot         254 calls: 250 ok, 3 check-1, 1 no-sort-head, 0 check-3.
                                NEWLY FORWARDED: 0.
      callee rung-2 (unchanged) 78 calls: 65 ok, 8 check-1, 3 no-sort-head, 2 check-3.
      The one pre-existing flip is 6B67S's pinned row
      `a_concrete_provider_is_still_accepted_by_the_receiver_bracket`, written to fail on
      closure. It is replaced by a pointer to the new file.
    ARGUMENT/TYPE-CARRIED (unchanged by construction)
      864 producer reads of a decided witness (599 type-carried, 265 echoing a callee bracket),
      24 of them CONCRETE, in 3 tests: wi858 a_bracketless_pair_set_takes_the_prelude_ordering and
      wi869 a_bracketless_sorted_set_of_pairs_sorts (WI-1094's inferred O = Pair), wi_r10kc
      a_generic_consumer_over_a_list_keeps_each_elements_ordering (a typed MySet).
      P3, check 3 MOVED onto the producer over the whole wi_tests binary: exactly 4 fail. They
      are those 3, plus this ticket's boundary row. Census and back-out agree.

BACK-OUT, one mechanism at a time, measured on the final code (rows of the new file):
  (R) receiver leg's validation call  -> every_refusal_reads_the_same_in_both_spellings,
      the_concrete_refusal_names_no_bracket_the_author_did_not_write,
      a_plain_parameter_is_refused_in_both_spellings
  (F) callee forward off              -> an_abstract_slot_binding_forwards_in_both_spellings
  (N) forward widened to any abstract -> a_plain_parameter_is_refused_in_both_spellings
  (W) old check-3 wording             -> the_concrete_refusal_names_no_bracket_the_author_did_not_write
  (F) widened to rung-2 keys          -> an_abstract_value_at_a_spec_key_is_still_refused
  (P3) check 3 on the producer        -> a_type_may_carry_a_concrete_witness_and_it_is_honoured
                                         (+ the 3 pre-existing tests above)

6B67S's TABLE, re-measured after this change: backing out M1 (check 1 at the producer) no
longer reddens `a_witness_that_provides_nothing_says_so_in_every_spelling`, because both of
its spellings are brackets and now validate at their own leg. It still reddens the three rows
with an ARGUMENT spelling. M2 unchanged. Recorded in that file's header.

TWO FINDINGS, NOT ACTED ON — raised with the user:
  (1) CHECK 3's CRITERION ("the witness has constructors") vs its REASON ("the value directs
      the dispatch, so an explicit witness cannot change it"). MEASURED with check 3 switched
      off: `WeakOrd.compare[WeakOrd = ConcOrd]("a","bb")` answers 1 against the bare call's -1,
      and a named slot bound to ConcOrd orders by it ("bbb,cc,a,"). The reason holds only for a
      witness that IS its provision's carrier: `[WeakOrd = Pair]` on pairs answers -1, as bare.
      The kernel spec (§5.4) states the rule for every call-site selection, so this delivery
      implements it on the receiver too and records the limit at `validate_instance_selection`.
  (2) THE TYPE CHANNEL'S FORWARD OF A PLAIN PARAMETER. `s: SortedSet[T = E, O = P]` in a sort
      that also `requires OE: WeakOrd[E]` still forwards through WI-1094's `Quantified` arm and
      takes OE's dictionary. Measured: a ByLength-typed set inserted into in RevLen's order. The
      written channels now refuse the same binding. Recorded at the arm.

CODE: `validate_written_selection` (new, the one owner) and `names_a_declared_slot` (new);
`seed_op_type_args` and `seed_receiver_type_args` call it; the channel-neutral check-3 wording
("an explicit selection of `WeakOrd = ConcOrd`", which names no bracket the author didn't
write). Docs: kernel-language §5.4's validation paragraph; 058-implementation §2.
TESTS: wi_tx0g6_selection_validation_test (7 rows); 6B67S's pinned row replaced, its header
re-measured.
REVIEW. `/code-review` (high), 7 findings: fixed the receiver's sticky-contradiction path, which
`continue`d past the new validation (it now falls through, as the callee does; that state is
reasoned-unreachable per 7TN1Q), and `ValueDirectedSelection`'s field name (`type_arg` ->
`selection`, pinned). Measured one away: a foreign slot binder `[O = R.OE]` is a non-manifest
projection, refused at load, and never reaches the forward gate. Left as raised: the two
findings above, the plain-parameter refusal's repair advice (check 1's wording), and the
receiver's duplicate check 1 (negligible).
cargo-test: full workspace green via rustland/scripts/test.sh (every binary, 0 failures).
scaland `sbt testFull`: 578/578 (it carries no instance-selection machinery).

### 2026-09-23T09:02:00Z — feedback — user

FOLLOW-UP (commit d18a3652). Finding 2 (the type channel forwards a PLAIN parameter and answers it with another same-spec slot's dictionary) was attempted inline with the brackets' own gate, "is the binder a slot", and REVERTED. On the type channel that gate breaks a correct shape: a plain parameter a REQUIREMENT mentions (PolyD, Strategy 2b), which runs at both orderings. It failed 4 rows of wi456_no_scope_route_test. The same gate on the brackets therefore refuses that shape too. Measured: the receiver spelling RAN it before this ticket; the callee always refused it; the bare call runs. Zero such brackets exist in the suite or the corpora. It is recorded as conservative at each site, pinned by a_plain_parameter_tied_to_a_requirement_is_refused_in_brackets_too, and the separating criterion is filed as WI-20260923-WN9P8. Full workspace green.


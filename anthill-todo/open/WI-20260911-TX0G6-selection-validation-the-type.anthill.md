## Attributes

- id: WI-20260911-TX0G6-selection-validation-the-type
- created: 2026-09-11T14:39:56Z

- status: Open
- status_agent: claude
- status_at: 2026-09-11T14:39:56Z

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


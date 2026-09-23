//! WI-20260911-6B67S — THE σ-READ PRODUCER VALIDATES ITS OWN TOP-LEVEL SELECTION.
//!
//! `check_selection_bindings` renders `TypeError::WitnessDoesNotProvide` in two wordings
//! and picked between them from an invariant it did not check:
//!
//! > Reached only past `validate_instance_selection`, which already established that
//! > the witness provides the spec SOMEWHERE.
//!
//! True of the BRACKET producer (`seed_op_type_args`, which runs §4.4 check 1 first) and
//! FALSE of the σ-READ one (`selections_from_slot_bindings`). So a witness that provides
//! NOTHING was told it *"provides WeakOrd, but not at the bindings this call needs"*.
//! `NotOrd` declares no `fact` and no `provides`: the message asserts a provision that
//! does not exist and sends the author after a binding mismatch that is not there.
//!
//! THE PRODUCER WAS INCONSISTENT BY EXACTLY ONE LEVEL, which is what located the fix.
//! `selections_from_slot_bindings` already ran check 1 on every NESTED slot witness
//! (`witness_value_slot_selections` → `check_slot_witnesses_provide`) and on none of its
//! TOP-LEVEL ones — a nested `ListOrd[OE = NotOrd]` was refused by name while the
//! `O = NotOrd` carrying it was passed downstream to be guessed about. It now runs check
//! 1 on both. Making the CONSUMER ask was tried first and is the worse shape: it leaves
//! the invariant false, and this producer's OTHER caller (the eta path, which runs no
//! `check_selection_bindings` at all) keeps an unchecked selection either way.
//!
//! TWO CHANNELS REACH THIS PRODUCER, which is why the repair cannot live at either one.
//! A RECEIVER bracket (`SortedSet[T = Int64, O = NotOrd].empty()`) and an ARGUMENT whose
//! TYPE carries the slot (`s: SortedSet[T = Int64, O = NotOrd]`, no bracket anywhere)
//! both land here. [`the_same_refusal_reaches_a_call_with_no_bracket_at_all`] is the row
//! that rules out a receiver-leg repair.
//!
//! **THREE MECHANISMS, MEASURED ONE AT A TIME** — a single "all off" run credits one
//! site for another's rows. Counts are of this file's 8 rows.
//!
//! | backed out | fails |
//! |---|---|
//! | (M1) check 1 at the producer (`check_witness_provides_spec`) | [`a_witness_that_provides_nothing_says_so_in_every_spelling`], [`the_same_refusal_reaches_a_call_with_no_bracket_at_all`], [`the_repair_advice_names_no_syntax_the_author_did_not_write`], [`an_abstract_element_no_longer_hides_a_witness_that_provides_nothing`] |
//! | (M2) the headless refusal (`SelectionValueNotASort`, was a `continue`) | [`a_slot_value_with_no_sort_head_is_refused_in_every_spelling`] |
//! | (M3) the channel-neutral `at_bindings: false` wording | [`the_repair_advice_names_no_syntax_the_author_did_not_write`] |
//! | (M2) WIDENED to every `sort_functor_of` `None` — the shape that shipped broken | 11 rows in `wi1094_named_slot_inference_test`, `wi_ee0ep_param_dictionary_test`, `wi844_sorted_set_driver_test`, `wi_r10kc_spec_default_body_dictionary_test` |
//!
//! (M3) is named by one row that (M1) also reddens — it has to be, since (M1) is what
//! routes a bracket-less channel into that arm at all. Backing out (M3) ALONE is what
//! isolates it, and that is the run recorded above.
//!
//! **(M1)'s FIRST ROW NO LONGER ISOLATES IT, since WI-20260911-TX0G6.** The receiver
//! spelling now runs check 1 at its OWN leg, through the callee's owner
//! (`validate_written_selection`). So
//! [`a_witness_that_provides_nothing_says_so_in_every_spelling`], which writes a bracket
//! in both of its spellings, is refused at a bracket leg whether or not the producer
//! checks. MEASURED after TX0G6: backing out (M1) alone reddens the other three rows in
//! its list and leaves that one green. Each of those three has an ARGUMENT spelling,
//! which reaches the producer with no bracket at all, so they are what (M1) still owns.
//!
//! THE LAST TABLE ROW IS NOT HYPOTHETICAL, AND ITS ROWS ARE NOT HERE ON PURPOSE. (M2)
//! keyed on "no sort head" was written, measured against this file — which stayed
//! GREEN — and broke §7.1 forwarding in four other files: an UNWRITTEN slot is filled
//! with an `s.O` [`UnwrittenFill::Projection`], a skolem with no sort head, so the
//! widened refusal ate every "takes the argument's own dictionary" row.
//!
//! Those four files OWN that shape; this one cites them. A local copy was written and
//! then deleted, because it would be an eleventh witness to a fact ten already establish
//! — and because the copy it replaced (`an_abstract_slot_still_forwards`, a slot bound
//! to a DECLARED parameter) passed straight through the broken version, which is the
//! sharper lesson: a forwarding fixture is only a control for this delivery if it uses
//! the UNWRITTEN spelling, and picking the wrong one bought a green light and no
//! safety. The mechanism this file owns is the narrowing to
//! [`SlotBinderState::NoWitnessReading`]; the census that the narrowing is *necessary*
//! is those 11 rows, and `scripts/test.sh` is what reads it.
//!
//! **PASS EITHER WAY, BY DESIGN** — each load-bearing, none decoration:
//!  * [`a_provider_at_other_bindings_keeps_the_at_bindings_message`] is THE control the
//!    ticket names, and it is what separates "the wrong branch" from "no branch": a fix
//!    that made every witness report `does not provide` would pass the rows above and
//!    fail this one. Green before and after.
//!  * [`a_correct_selection_still_loads_and_runs`] drives the ACCEPT path to a value.
//!    (M1) and (M2) are new REFUSALS, so the thing most worth proving is what they do
//!    not refuse.
//!
//! LEFT OPEN HERE, CLOSED BY WI-20260911-TX0G6: §4.4 check 3 on the receiver bracket.
//! Check 3 is the one check that cannot move to the producer. The receiver leg now
//! validates a written selection through the callee's own owner, so
//! `wi_tx0g6_selection_validation_test` owns that row, and also the back-out effect
//! TX0G6 had on the table above (recorded at this file's M1 row).
//!
//! REFERENCE: `selections_from_slot_bindings`, `check_witness_provides_spec`,
//! `check_selection_bindings`, `seed_receiver_type_args` (typing.rs);
//! WI-20260911-RS2G4 (the receiver bracket), WI-20260911-7TN1Q (the review that found it).

use anthill_core::eval::Value;

/// `NotOrd` provides NOTHING — the whole point, since the false message claimed it
/// provided `WeakOrd`. `ByLength` provides `WeakOrd[T = String]`, so asked at
/// `T = Int64` it is a genuine provider AT OTHER BINDINGS: the control's witness.
/// `ConcOrd` provides the same and HAS a constructor, which is check 3's shape.
const DECLS: &str = r#"
  import anthill.prelude.{Int64, String, Bool, Ord, WeakOrd, List, SortedSet}
  import anthill.prelude.String.{length}
  import anthill.prelude.Numeric.{sub}

  sort NotOrd
    entity notOrd
  end

  sort ByLength
    provides WeakOrd[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))
  end

  sort ConcOrd
    entity conc
    provides WeakOrd[T = String]
    operation compare(a: String, b: String) -> Int64 = 0
  end
"#;

fn program(body: &str) -> String {
    format!("\nnamespace probe.b6\n{DECLS}\n{body}\nend\n")
}

fn load_errors(body: &str) -> Vec<String> {
    match crate::common::try_load_kb_with(&program(body)) {
        Ok(_) => Vec::new(),
        Err(es) => es.to_vec(),
    }
}

/// The ONE error this body must produce, with the leading `<line>:<col>: ` stripped so
/// two spellings written at different columns compare for the MESSAGE — which is the
/// whole claim of "one rule, two spellings".
///
/// THE PREFIX IS CHECKED BY SHAPE, NOT TAKEN ON THE FIRST `": "`, and its absence
/// PANICS (found by `/code-review`). `LoadError::TypeMismatch` has a SPANLESS branch
/// that renders no `line:col: ` at all, and a bare `split_once(": ")` would then
/// amputate the message HEAD — `type mismatch in <op>.type_arg` — and report success,
/// because every substring asserted below lives in the `got …` tail. Both spellings
/// would amputate identically, so the comparison would stay green while comparing the
/// wrong bytes.
fn sole_message(body: &str) -> String {
    let errs = load_errors(body);
    assert_eq!(
        errs.len(),
        1,
        "expected exactly one error for:\n{body}\ngot {errs:#?}"
    );
    let (prefix, msg) = errs[0]
        .split_once(": ")
        .unwrap_or_else(|| panic!("no `line:col: ` prefix to strip in: {}", errs[0]));
    let digits_pair = prefix.split_once(':').is_some_and(|(l, c)| {
        !l.is_empty()
            && l.bytes().all(|b| b.is_ascii_digit())
            && !c.is_empty()
            && c.bytes().all(|b| b.is_ascii_digit())
    });
    assert!(
        digits_pair,
        "expected a `line:col` prefix, got {prefix:?} in: {}",
        errs[0]
    );
    msg.to_string()
}

/// The two 035 spellings of one selection, as the ticket writes them.
const RECV_NOT_ORD: &str =
    "  operation viaRecv() -> SortedSet[T = Int64] = SortedSet[T = Int64, O = NotOrd].empty()";
const CALLEE_NOT_ORD: &str =
    "  operation viaCallee() -> SortedSet[T = Int64] = SortedSet.empty[T = Int64, O = NotOrd]()";
/// The THIRD channel: the slot rides in the argument's declared type, and the call that
/// is judged (`SortedSet.toList(s)`) writes no bracket either.
const ARG_NOT_ORD: &str =
    "  operation viaArg(s: SortedSet[T = Int64, O = NotOrd]) -> List[T = Int64] =\n    \
     SortedSet.toList(s)";

/// THE TICKET'S HEADLINE ROW. Both bracket spellings refuse — they always did — and now
/// both refuse with the TRUE message. Asserted three ways, because "they agree" alone
/// would also be satisfied by both being wrong:
///   1. each says `does not provide`;
///   2. neither says `provides … but not at the bindings`, the false claim;
///   3. the two agree BYTE FOR BYTE.
///
/// Before the fix the receiver arm rendered the `at_bindings` wording while the callee
/// arm rendered this one — (1) and (3) failing together. (M1).
#[test]
fn a_witness_that_provides_nothing_says_so_in_every_spelling() {
    let recv = sole_message(RECV_NOT_ORD);
    let callee = sole_message(CALLEE_NOT_ORD);

    for (what, msg) in [("receiver", &recv), ("callee", &callee)] {
        assert!(
            msg.contains("probe.b6.NotOrd does not provide anthill.prelude.WeakOrd"),
            "the {what} spelling must name the REAL fault — NotOrd declares no \
             `provides` at all; got: {msg}"
        );
        assert!(
            !msg.contains("but not at the bindings"),
            "the {what} spelling must not assert a provision NotOrd does not have; \
             got: {msg}"
        );
    }
    assert_eq!(
        recv, callee,
        "035 lists the receiver and the callee bracket as two ways of writing one thing, \
         so one selection must produce one message"
    );
}

/// THE CHANNEL THAT CHOSE THE FIX'S LOCATION. No bracket is written ANYWHERE: the slot
/// rides in the argument's declared type and `selections_from_slot_bindings` reads it
/// back out of σ. Repairing `seed_receiver_type_args` — the ticket's other candidate
/// direction — could not have reached this, because there is no bracket for a
/// bracket-side check to run on. (M1).
#[test]
fn the_same_refusal_reaches_a_call_with_no_bracket_at_all() {
    let msg = sole_message(ARG_NOT_ORD);
    assert!(
        msg.contains("probe.b6.NotOrd does not provide anthill.prelude.WeakOrd"),
        "an argument-carried witness reaches the same producer and must get the same \
         true message; got: {msg}"
    );
    assert!(!msg.contains("but not at the bindings"), "got: {msg}");
}

/// THE REPAIR ADVICE MUST NAME NO SYNTAX THE AUTHOR DID NOT WRITE (found by
/// `/code-review`). The `at_bindings: false` arm used to read *"a call-site
/// `[WeakOrd = NotOrd]` on anthill.prelude.SortedSet.toList"*. For [`ARG_NOT_ORD`] there
/// is no bracket in the file at all — `NotOrd` sits in the enclosing operation's
/// PARAMETER TYPE — so that told the author to fix syntax they never wrote, on a stdlib
/// operation. The same species of false diagnostic this ticket exists to remove, and
/// (M1) is what widened its reach by routing a bracket-less channel into that arm, so it
/// is repaired in the same delivery.
///
/// The REPAIR half is unchanged and still asserted: `provides WeakOrd[…]` is what the
/// author must add either way, and a rewording that dropped it would be a regression.
/// (M3, and (M1) reddens it too — see the header.)
#[test]
fn the_repair_advice_names_no_syntax_the_author_did_not_write() {
    let msg = sole_message(ARG_NOT_ORD);
    assert!(
        !msg.contains("a call-site"),
        "there is no call-site bracket in this program — the advice must not claim one; \
         got: {msg}"
    );
    assert!(
        msg.contains("must name a sort that declares `provides anthill.prelude.WeakOrd[…]`"),
        "the actionable half must survive the rewording; got: {msg}"
    );
}

/// THE HEADLESS SLOT VALUE — the silent skip this delivery turned loud, in all three
/// spellings. A tuple has no sort head, so `sort_functor_of` answered `None` and the
/// producer `continue`d.
///
/// THE SKIP WAS ARGUED AS "the requirement's own route reports it", AND THAT WAS MEASURED
/// FALSE: `SortedSet[T = Int64, O = (Int64, Int64)].empty()` LOADED CLEAN — the written
/// `O` dropped and the requirement answered by an ordinary search, so the call did not
/// merely lose its selection, it silently got somebody else's. It only looks reported
/// when two providers happen to tie, and then it is reported as an AMBIGUITY, never as
/// the malformed binding it is. (M2).
#[test]
fn a_slot_value_with_no_sort_head_is_refused_in_every_spelling() {
    let recv = sole_message(
        "  operation hlRecv() -> SortedSet[T = Int64] =\n    \
         SortedSet[T = Int64, O = (Int64, Int64)].empty()",
    );
    let callee = sole_message(
        "  operation hlCallee() -> SortedSet[T = Int64] =\n    \
         SortedSet.empty[T = Int64, O = (Int64, Int64)]()",
    );
    let arg = sole_message(
        "  operation hlArg(s: SortedSet[T = Int64, O = (Int64, Int64)]) -> List[T = Int64] =\n    \
         SortedSet.toList(s)",
    );

    for (what, msg) in [("receiver", &recv), ("callee", &callee), ("argument", &arg)] {
        assert!(
            msg.contains("must name a WITNESS SORT"),
            "the {what} spelling must refuse a slot value with no sort head rather than \
             drop it and let a search answer; got: {msg}"
        );
    }
    assert_eq!(recv, callee, "one rule, two spellings");
}

/// AN ABSTRACT ELEMENT MUST NOT HIDE THE FAULT, and this is the row that says the fix is
/// at the right DEPTH. With `T` a type parameter the goal `WeakOrd[T = E]` has NO
/// candidates, and `check_selection_bindings` skips entirely on that
/// (`if candidates.is_empty() { continue; }`) — so before this delivery the refusal fell
/// through to `resolve`'s step 0, which renders *"the call selected `NotOrd` …, which
/// provides no instance at these bindings"*: the SAME false claim, one rung down, for a
/// witness that provides nothing anywhere.
///
/// A consumer-side repair at `check_selection_bindings` could not have reached this —
/// that rung never runs here. Check 1 at the producer runs before any goal is formed, so
/// both spellings now refuse by name. (M1).
#[test]
fn an_abstract_element_no_longer_hides_a_witness_that_provides_nothing() {
    let arg = sole_message(
        "  operation gArg[E](s: SortedSet[T = E, O = NotOrd]) -> List[T = E] =\n    \
         SortedSet.toList(s)",
    );
    let callee = sole_message(
        "  operation gCallee[E](s: SortedSet[T = E, O = NotOrd]) -> List[T = E] =\n    \
         SortedSet.toList[T = E, O = NotOrd](s)",
    );

    for (what, msg) in [("argument", &arg), ("callee", &callee)] {
        assert!(
            msg.contains("probe.b6.NotOrd does not provide anthill.prelude.WeakOrd"),
            "the {what} spelling must name the real fault even where the element is \
             abstract; got: {msg}"
        );
        assert!(
            !msg.contains("provides no instance at these bindings"),
            "step 0's wording asserts a provision NotOrd does not have; got: {msg}"
        );
    }
    assert_eq!(arg, callee, "one rule, two spellings");
}

/// THE CONTROL THE TICKET NAMES, and the reason this is a branch repair rather than a
/// branch deletion. `ByLength` genuinely provides `WeakOrd[T = String]`, so asked for
/// `T = Int64` the `at_bindings` wording is TRUE and must survive — in all three
/// channels.
///
/// GREEN BEFORE AND AFTER. That is what makes it a control: a "fix" that made every
/// witness report `does not provide` would pass every row above and fail this one.
#[test]
fn a_provider_at_other_bindings_keeps_the_at_bindings_message() {
    let recv = sole_message(
        "  operation ctlRecv() -> SortedSet[T = Int64] = SortedSet[T = Int64, O = ByLength].empty()",
    );
    let callee = sole_message(
        "  operation ctlCallee() -> SortedSet[T = Int64] = SortedSet.empty[T = Int64, O = ByLength]()",
    );
    let arg = sole_message(
        "  operation ctlArg(s: SortedSet[T = Int64, O = ByLength]) -> List[T = Int64] =\n    \
         SortedSet.toList(s)",
    );

    for (what, msg) in [("receiver", &recv), ("callee", &callee), ("argument", &arg)] {
        assert!(
            msg.contains("provides anthill.prelude.WeakOrd, but not at the bindings"),
            "the {what} spelling must keep the AT-BINDINGS wording for a witness that \
             really does provide the spec elsewhere; got: {msg}"
        );
        assert!(
            !msg.contains("does not provide"),
            "the {what} spelling must not tell the author to add a `provides` ByLength \
             already declares; got: {msg}"
        );
    }
    assert_eq!(recv, callee, "one selection, one message");
}

/// THE ACCEPT PATH, DRIVEN TO A VALUE. This delivery adds two REFUSALS, so the thing
/// most worth proving is what they do not refuse: a correct receiver-spelled selection
/// must still load, still select `ByLength`, and still order by it.
///
/// THE INSERTS ARE IN ALPHABETICAL ORDER so the assertion excludes INSERTION order as
/// well as alphabetical (found by `/code-review` — inserting `"zz"` first made `"zz"`
/// the answer under a set that did no ordering at all). `"aaa"` then `"zz"`: alphabetical
/// says `"aaa"`, insertion says `"aaa"`, and only `ByLength` — which orders by length —
/// says `"zz"`.
#[test]
fn a_correct_selection_still_loads_and_runs() {
    let src = program(
        "  import anthill.prelude.List.{cons, nil}\n  \
         operation firstOf(l: List[T = String]) -> String =\n    \
           match l\n      \
             case nil() -> \"<empty>\"\n      \
             case cons(h, t) -> h\n  \
         operation drive(n: Int64) -> String =\n    \
           let s = SortedSet[T = String, O = ByLength].empty()\n    \
           firstOf(SortedSet.toList(SortedSet.insert(SortedSet.insert(s, \"aaa\"), \"zz\")))",
    );
    let mut interp = crate::common::interp_for(&src);
    match interp.call("probe.b6.drive", &[Value::Int(0)]) {
        Ok(Value::Str(s)) => assert_eq!(
            &*s, "zz",
            "the receiver bracket must still select ByLength, which orders by length — \
             `aaa` would be both the alphabetical and the insertion-order answer"
        ),
        other => panic!("expected the ByLength ordering to run; got {other:?}"),
    }
}

// CLOSED BY WI-20260911-TX0G6. A row here pinned the one check this delivery left
// open: §4.4 CHECK 3 (`ValueDirectedSelection`), under which
// `SortedSet[T = String, O = ConcOrd].empty()` loaded while the callee spelling refused
// it. It asserted the open behaviour so that closing the gap would fail it and be a
// recorded decision rather than a drift. It failed as designed, and the decision is
// `wi_tx0g6_selection_validation_test`'s: the receiver leg now validates a written
// selection through the callee's own owner (`validate_written_selection`), and check 3
// still does not run at the producer, because a TYPE may legitimately carry a concrete
// witness. The closed behaviour is asserted there, byte for byte against the callee
// spelling.

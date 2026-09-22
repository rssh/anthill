//! WI-20260830-X9PB4 — `require[X]` builds a dictionary for a spec whose elements
//! the WITNESS CALL does not name, where before it built none at all.
//!
//! THE ROW THE TICKET NAMES, one file, one `List`, two spellings of one goal:
//!
//! ```text
//!   rule woven(?ls, ?n) :- require[FiniteCollection[C = List[T = String]]], size(?ls, ?n)
//!   rule plain(?ls, ?n) :- size(?ls, ?n)
//! ```
//!
//! WI-20260830-NX4FD gave the PLAIN spelling the win (`Int(2)`) and left the woven
//! one delaying. Its own row `the_woven_spelling_does_not_yet_receive_the_win`
//! asserted that inequality and said at its site to re-aim it; this ticket does,
//! renaming it `the_woven_spelling_receives_the_win`.
//!
//! ## The mechanism is NOT the one the ticket predicted, and that is the finding
//!
//! The ticket read it as the bridge's defect one route over — "an under-determined
//! sub-slot was never completed" — and proposed giving `find_dictionary` the same
//! [`unique_provider_completion`] treatment [`resolve_bridge_requirements`] has.
//! MEASURED, that is not where it broke and that treatment does not fix it:
//!
//!  * The failure is at the TOP-LEVEL goal, not a sub-slot. `resolve` answered
//!    `NoMatch { hint: "no impl provides anthill.prelude.FiniteCollection" }` for
//!    `FiniteCollection[C = List[T = String]]` — ZERO candidates, on a spec `List`
//!    provides outright.
//!  * `List provides FiniteCollection[C = List[T], Element = T, E = {}]` was rejected
//!    on `Element`, which the goal OMITTED — and an omitted type param is
//!    DISCRIMINATING at `collect_provides_candidates` ("else every concrete `Eq` impl
//!    would match a bare `Eq` goal", wi325 / wi237).
//!  * The completion cannot reach it. `unique_provider_completion` proposes a
//!    provider's own GROUND value for an open element; `Element = T` is `List`'s own
//!    parameter, not ground. Extending it to substitute what the goal's pinned `C`
//!    determines was built and DRIVEN, and it still answered `None`: the iteration
//!    meets `FiniteStream provides FiniteCollection[C = FiniteStream, Element = T,
//!    E = E]` first, `List[T = String]` matches its bare `C` (a `List` IS a
//!    `FiniteStream`), its `Element` stays abstract, and that is the OPEN-ENDED RIVAL
//!    veto — which is correct and must not be relaxed. The completion route was
//!    backed out; nothing here credits it.
//!
//! ## What it is instead: a goal producer that DROPPED the element
//!
//! `require[X]`'s bracket does not survive to the goal. `lower_require` strips the
//! spec's type arguments (a bare `T` in term position has no binding in a free rule),
//! so `witness_sort_goal` rebuilds the goal from the WITNESS CALL's carried types —
//! and `FiniteCollection.size(c: C)` names `C` and nothing else. Writing
//! `require[FiniteCollection[C = List[T = String], Element = String]]` changed
//! nothing, MEASURED: the bracket is gone before the goal exists.
//!
//! The element must therefore be SYNTHESIZED, and WI-507 had already settled what it
//! must be synthesized AS — its own doc names this shape: "a carrier-only `clear(c)`
//! pins only the carrier `C`, so the spec's sibling `Element` arrives as
//! `Ref(Sort.Element)` — matches any impl-param binding WITHOUT constraining it".
//! `witness_sort_goal` now carries every un-named element as that wildcard.
//! `goal_from_requires_entry` has had the shape for free all along, because a written
//! `requires Iterable[C = C, Element = Element, E = E]` spells every element.
//!
//! ## What fails when the change is backed out — MEASURED, not predicted
//!
//! Back out = keep the wildcard loop at the end of `witness_sort_goal` but do not
//! `bindings.push` what it built. Three of this file's five rows fail, plus one in
//! the neighbouring file:
//!
//!  * `the_woven_spelling_answers_both_boxes` (then named `…_what_the_plain_one_does`) — FAILS. The woven rule's
//!    DEFINITE answers go to `[]` against the plain spelling's `[0, 2]`; its only
//!    solution is an INDEFINITE one.
//!  * `the_bound_dictionary_names_the_carrier_that_provides_the_spec` — FAILS: `?d`
//!    binds nothing at all, so no carrier is named.
//!  * `an_element_a_provider_leaves_open_is_answered` (arm 1 of the two-arm row) —
//!    FAILS: `?d` does not bind.
//!  * `a_self_representing_spec_receives_its_dictionary_too` — FAILS: `?d` yields one
//!    INDEFINITE solution and names no carrier.
//!  * `wi_nx4fd_functional_relation_row_param_test::the_woven_spelling_receives_the_win`
//!    — FAILS, the same equality one file over. It is NX4FD's own record that the
//!    weaving population moved, re-aimed by this ticket; the mechanism and the
//!    controls live here.
//!
//! `a_tie_on_a_synthesized_element_delays_rather_than_reporting_a_defect` is the odd
//! one out and belongs to the SECOND half of the change: it passes with the whole
//! ticket backed out and with the whole ticket in, and ABORTS in between — with the
//! wildcard loop present and its tie-routing removed. See its site. (That flag was
//! `synthesized`; WI-20260913-J38VE renamed it `WitnessGoal::from_carried_types` and
//! inverted it, because a WRITTEN element clears it for the same reason a minted wildcard
//! does — the routing and this row are unchanged.)
//!
//! And what does NOT move, each here because the widening could plausibly have
//! reached it:
//!
//!  * `an_element_a_provider_pins_concretely_is_still_discriminating` (arm 2) — a
//!    wildcard is refused against a CONCRETE candidate binding exactly as an omission
//!    was, so wi325 / wi237's coherence rule is untouched. Passes either way; it is
//!    the arm that says the widening is a widening and not a deletion.
//!  * `a_spec_whose_witness_names_every_element_is_unmoved` — the WI-1040 population.
//!    `Desc[T]` with `describe(x: T)` leaves nothing un-named, so no wildcard is
//!    minted and the goal is byte-identical. Passes either way.
//!  * `an_effect_row_element_is_left_to_its_own_owner` — passes either way too, and
//!    it is not idle: it is the control for ONE LINE of the change (the effect-row
//!    guard inside the wildcard loop), which the whole 3934-test binary cannot tell
//!    the presence of. Drop that guard and its `E = Error` arm alone fails. See its
//!    site.

use anthill_core::eval::Value;

use crate::common::{definite_unary, load_kb_with, query_unary};

// ── the acceptance row ─────────────────────────────────────────────────────

/// One file, one `List`, and the two spellings of one goal over two `Box`es whose
/// answers DISAGREE — the empty one is there so a predicate that answered a constant
/// fails as loudly as one that answered nothing.
const SRC: &str = r#"
namespace x9pb4
  import anthill.prelude.{List, String, Bool, Int64, FiniteCollection}
  import anthill.prelude.FiniteCollection.{size}

  sort Box
    entity Box(items: List[T = String])
  end

  fact Box(items: ["a", "b"])
  fact Box(items: [])

  rule woven(?ls, ?n) :- require[FiniteCollection[C = List[T = String]]], size(?ls, ?n)

  rule answer_woven(?n) :- Box(items: ?ls), woven(?ls, ?n)
end
"#;

/// WI-20260922-0DK3H — [`SRC`] WITHOUT the `require`, which is now a LOAD ERROR and so
/// cannot share a file with the rules that must load. See
/// [`the_plain_spelling_is_refused_and_the_require_is_the_repair`].
const PLAIN_SRC: &str = r#"
namespace x9pb4_plain
  import anthill.prelude.{List, String, Bool, Int64, FiniteCollection}
  import anthill.prelude.FiniteCollection.{size}

  sort Box
    entity Box(items: List[T = String])
  end

  fact Box(items: ["a", "b"])

  rule plain(?ls, ?n) :- size(?ls, ?n)
  rule answer_plain(?n) :- Box(items: ?ls), plain(?ls, ?n)
end
"#;

/// The definite `Int64` answers of a unary rule, sorted — the goal enumerates two
/// `Box`es and their order is not this ticket's subject.
fn ints(kb: &mut anthill_core::kb::KnowledgeBase, qn: &str) -> Vec<i64> {
    let mut got: Vec<i64> = definite_unary(kb, qn)
        .iter()
        .map(|v| match v {
            Value::Int(i) => *i,
            other => panic!("{qn}: expected an Int column, got {other:?}"),
        })
        .collect();
    got.sort_unstable();
    got
}

/// THE ACCEPTANCE ROW — the woven spelling answers two numbers, BY VALUE.
///
/// WI-20260922-0DK3H CHANGED WHAT THIS IS MEASURED AGAINST. It used to assert that the
/// woven spelling answers what the PLAIN one does, with the plain answer read first as
/// the control. The plain spelling is now a load error
/// ([`the_plain_spelling_is_refused_and_the_require_is_the_repair`]), so the comparison
/// has no second side; the guarantee it bought — "an equality both sides satisfy by
/// answering nothing proves nothing" — is bought instead by asserting `[0, 2]` outright,
/// over two `Box`es whose lengths DISAGREE.
///
/// THE TWO ROWS ARE STILL A PAIR, and a sharper one than before: they are the same goal
/// differing by exactly the `require`, and now one loads and the other does not.
#[test]
fn the_woven_spelling_answers_both_boxes() {
    let mut kb = load_kb_with(SRC);
    let woven = ints(&mut kb, "x9pb4.answer_woven");
    assert_eq!(
        woven,
        vec![0, 2],
        "`require[FiniteCollection[C = List[T = String]]], size(?ls, ?n)` must bind each \
         Box's length. Before X9PB4 the woven rule yielded ONE INDEFINITE solution — the \
         `find_dictionary` goal came back `Undecided` and the arity+1 site routed to \
         `unify` and delayed"
    );
}

/// WI-20260922-0DK3H — **THE OTHER HALF, AND THE TICKET'S THESIS IN ONE PAIR.** The same
/// `size(?ls, ?n)` over the same `List` WITHOUT the bracket: nothing types `?ls`, so the
/// dep `Iterable[C, Element, E]` has every element open and no provider fact can decide
/// it. The only thing that could ever have supplied the dictionary is the runtime value
/// of `?ls`, and that is the dispatch this ticket removes.
///
/// IT USED TO ANSWER `[0, 2]`, and this row's own former doc says why that was not a
/// static win: "`size` also reaches `2` by value-directed dispatch (WI-1044)". That is
/// precisely the route deleted here.
#[test]
fn the_plain_spelling_is_refused_and_the_require_is_the_repair() {
    let errs = match crate::common::try_load_kb_with(PLAIN_SRC) {
        Err(errs) => errs,
        Ok(_) => panic!("the plain spelling has no evidence and must be refused at load"),
    };
    assert!(
        errs.iter()
            .any(|e| e.contains("Iterable") || e.contains("FiniteCollection")),
        "the refusal must name the spec whose evidence is missing, so the author is sent \
         to the `require[…]` spelling the row above drives; got {errs:#?}"
    );
}

/// AND IT IS THE RIGHT DICTIONARY, not merely the right number.
///
/// `size` also reaches `2` by value-directed dispatch (WI-1044), so an equal pair of
/// numbers above is consistent with a `require` that resolved nothing and got
/// rescued. This row reads the dictionary itself through the named spelling
/// (`?d = require[…]`, WI-1040) and asserts the carrier it names.
///
/// `List` and NOT `FiniteStream`, and the rival is REAL rather than hypothetical.
/// `dispatch_candidate_impl_sorts` (WI-1110's diagnostic reader) over this exact goal,
/// MEASURED both ways:
///
/// ```text
///   FiniteCollection[C = List[T = String]]                        ⇒ []
///   FiniteCollection[C = List[T = String], Element = <wildcard>]  ⇒ [FiniteStream, List]
/// ```
///
/// So the wildcard turns zero candidates into TWO — `FiniteStream provides
/// FiniteCollection[C = FiniteStream, …]` matches a `List` carrier through
/// `types_lesseq`, because `List provides FiniteStream` — and this row is what says
/// the right one of them wins. Specificity decides: `C = List[T]` is a parametric head
/// matched structurally and scores, `C = FiniteStream` is a bare ref.
///
/// FAILS WHEN BACKED OUT: `?d` binds nothing, so there is no carrier to name.
#[test]
fn the_bound_dictionary_names_the_carrier_that_provides_the_spec() {
    let src = r#"
namespace x9pb4_d
  import anthill.prelude.{List, String, Bool, Int64, FiniteCollection}
  import anthill.prelude.FiniteCollection.{size}
  import anthill.prelude.Option.{none}

  sort Box
    entity Box(items: List[T = String])
  end

  fact Box(items: ["a", "b"])

  rule dict(?ls, ?d) :- ?d = require[FiniteCollection[C = List[T = String]]], size(?ls, ?ignored)
  rule answer(?d) :- Box(items: ?ls), dict(?ls, ?d)
end
"#;
    let mut kb = load_kb_with(src);
    let sols = query_unary(&mut kb, "x9pb4_d.answer");
    let [(v, true)] = sols.as_slice() else {
        panic!(
            "`?d = require[FiniteCollection[…]]` must bind exactly one DEFINITE \
             dictionary — before this ticket it bound none, got {sols:?}"
        );
    };
    assert_eq!(
        dictionary_impl(&kb, v),
        "anthill.prelude.List",
        "the dictionary must name the carrier the goal's own `C` selects. \
         `anthill.prelude.FiniteStream` here would be a WRONG dictionary the \
         wildcard element admitted — it provides `FiniteCollection` too, and a \
         `List` matches its bare `C` carrier"
    );
}

/// The `impl` carrier of a dictionary value, as a qualified name. Panics on any other
/// shape — a test whose subject is "which provider did the goal select" may not shrug
/// at an unexpected one. Read carrier-neutrally through the WI-1019 view, the same
/// way `wi1040_require_clause_dictionary_test::dictionary_parts` reads it.
fn dictionary_impl(kb: &anthill_core::kb::KnowledgeBase, v: &Value) -> String {
    use anthill_core::kb::term_view::{TermView, ViewHead};
    let impl_key = kb
        .try_resolve_symbol("anthill.realization.runtime.Dictionary.impl")
        .expect("the `Dictionary.impl` accessor must resolve");
    let impl_child = v
        .named_arg(kb, impl_key)
        .unwrap_or_else(|| panic!("a dictionary must carry `impl`, got {v:?}"))
        .to_value();
    let ViewHead::Functor {
        functor: Some(s),
        pos_arity: 0,
        named_arity: 0,
    } = impl_child.head(kb)
    else {
        panic!("`impl` must name a sort, got {impl_child:?}")
    };
    kb.qualified_name_of(s).to_string()
}

// ── the two-arm row: what a wildcard admits, and what it still refuses ──────

/// The shape both arms share: a spec with a SECOND element (`Note`) that the witness
/// `describe(x: T)` cannot pin, so the goal must synthesize it. `note` is what the
/// provision binds `Note` to, and it is the only thing that differs between the arms
/// — `N`, the carrier's own parameter, or the concrete `Int64`.
///
/// Deliberately the same shape as the stdlib row the ticket is about:
/// `List provides FiniteCollection[C = List[T], Element = T, …]` names its element BY
/// its own parameter, which the goal's pinned carrier then fixes.
fn noted(note: &str) -> String {
    format!(
        r#"
namespace x9pb4_n
  import anthill.prelude.{{Int64}}

  sort Desc
    sort T = ?
    sort Note = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Leaf
    sort N = ?
    entity leaf(n: N)
    provides Desc[T = Leaf[N], Note = {note}]
    operation describe(x: Leaf) -> Int64 = 7
  end

  rule dict(?x, ?d) :- ?d = require[Desc[T]], Desc.describe(?x, ?ignored)
  rule answer(?d) :- dict(leaf(n: 1), ?d)
end
"#
    )
}

/// EVIDENCE ARM — a provider's OWN parameter for the un-named element is
/// universally quantified, so it cannot discriminate anything, and the wildcard is
/// what lets the goal say so. `?d` binds and names `Leaf`.
///
/// FAILS WHEN BACKED OUT: the goal omits `Note`, the omission is discriminating, the
/// candidate is rejected, and `?d` binds nothing.
#[test]
fn an_element_a_provider_leaves_open_is_answered() {
    let src = noted("N");
    let mut kb = load_kb_with(&src);
    let sols = query_unary(&mut kb, "x9pb4_n.answer");
    let [(v, true)] = sols.as_slice() else {
        panic!(
            "a provision whose `Note` is its OWN parameter constrains nothing, so the \
             goal's wildcard must match it and bind a dictionary; got {sols:?}"
        );
    };
    assert_eq!(
        dictionary_impl(&kb, v),
        "x9pb4_n.Leaf",
        "and it must name the carrier that provides `Desc`"
    );
}

/// CONTROL — AND IT PASSES EITHER WAY, BY DESIGN. The same program with the
/// provision naming a CONCRETE `Note`: `Int64` is a claim about the instance, so the
/// goal — which has no opinion about `Note` — must not match it. `?d` binds nothing.
///
/// A wildcard is refused against a concrete candidate binding by
/// `dispatch_values_match` (`types_lesseq` refuses a param ref against a sort, and
/// the two sort symbols differ), which is the same verdict the OMISSION produced. So
/// this arm reads identically before and after — that is the point: it is what says
/// the reject was WIDENED for a universally-quantified candidate value and not
/// DELETED, and wi325 / wi237's rule ("every concrete `Eq` impl would match a bare
/// `Eq` goal") still holds.
///
/// It is a control only because the arm above answers — one row binding nothing is
/// also what an un-drivable fixture gives, and the two fixtures differ by four
/// characters.
#[test]
fn an_element_a_provider_pins_concretely_is_still_discriminating() {
    let src = noted("Int64");
    let mut kb = load_kb_with(&src);
    let sols = query_unary(&mut kb, "x9pb4_n.answer");
    assert!(
        sols.iter().all(|(_, definite)| !definite),
        "a provision that PINS `Note = Int64` says something the goal cannot confirm, \
         so no dictionary may be built for it — a binding here would be the \
         coherence hole the strict reject exists to refuse. Got {sols:?}"
    );
}

// ── controls ───────────────────────────────────────────────────────────────

/// CONTROL — THE WI-1040 POPULATION IS UNMOVED, and passes either way.
///
/// `Desc[T]` with `describe(x: T)`: the witness names every element the spec has, so
/// the wildcard loop mints nothing and the goal is byte-identical to what it was.
/// This is the shape WI-1040's own doc records the last wrong move in this population
/// on — `require[PartialEq[T]], eq(?x, ?y)` taken from ONE solution to ZERO with a
/// green corpus — so it is named here rather than left to the corpus.
#[test]
fn a_spec_whose_witness_names_every_element_is_unmoved() {
    let src = r#"
namespace x9pb4_u
  import anthill.prelude.{Int64}

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end

  rule via(?x, ?r) :- require[Desc[T]], Desc.describe(?x, ?r)
  rule answer(?r) :- via(leaf(), ?r)
end
"#;
    let mut kb = load_kb_with(src);
    assert!(
        matches!(
            definite_unary(&mut kb, "x9pb4_u.answer").as_slice(),
            [Value::Int(7)]
        ),
        "the covered call must still reach the implementation `Leaf` SUPPLIES (7), \
         not the spec's own default (1)"
    );
}

/// CONTROL FOR ONE LINE OF THE CHANGE — the effect-row exclusion inside the wildcard
/// loop, and it is DRIVEN rather than argued.
///
/// The loop mints a wildcard for every element the witness does not name EXCEPT an
/// effect row, because an omitted row already has an owner one layer down:
/// `collect_provides_candidates` skips a spec param `sort_param_is_effect_row`
/// answers for, on WI-387/WI-714's reasoning that "a row is the observation effect,
/// not carrier identity, so it must not drop the candidate". A wildcard would take
/// the question away from that owner and answer it differently.
///
/// TWO ARMS, differing only in what the provision binds the row to:
///
///  * `E = {}` — binds a dictionary. This arm is the fixture control: it binds with
///    the exclusion, WITHOUT it, and before this ticket, so a `concrete` arm that
///    bound nothing could not be blamed on an un-drivable program.
///  * `E = Error` — binds a dictionary too, and ONLY because of the exclusion.
///
/// WHAT FAILS WHEN THE EXCLUSION IS BACKED OUT (drop the `sort_param_is_effect_row`
/// guard so the row takes a wildcard as well): the `concrete` arm alone. `?d` yields
/// one INDEFINITE solution — `Ref(Walk.E)` reaches `dispatch_values_match` against
/// the provision's written `Error`, the two sort symbols differ, and the only
/// candidate is dropped. The `empty` arm is unmoved, which is why both are here.
///
/// It passes with the WHOLE ticket backed out as well (an omitted row was skipped at
/// the matcher then too) — so it measures this line, not the change.
#[test]
fn an_effect_row_element_is_left_to_its_own_owner() {
    let program = |row: &str, op_effects: &str| {
        format!(
            r#"
namespace x9pb4_e
  import anthill.prelude.{{Int64, Error}}

  sort Walk
    sort C = ?
    effects E = ?
    operation step(c: C) -> Int64 effects E = 1
  end

  sort Src
    entity src
    provides Walk[C = Src, E = {row}]
    operation step(c: Src) -> Int64{op_effects} = 5
  end

  rule dict(?x, ?d) :- ?d = require[Walk[C]], Walk.step(?x, ?ignored)
  rule answer(?d) :- dict(src(), ?d)
end
"#
        )
    };
    for (label, row, op_effects) in [("{}", "{}", ""), ("Error", "Error", " effects Error")] {
        let src = program(row, op_effects);
        let mut kb = load_kb_with(&src);
        let sols = query_unary(&mut kb, "x9pb4_e.answer");
        let [(v, true)] = sols.as_slice() else {
            panic!(
                "`provides Walk[C = Src, E = {label}]` must still answer the \
                 `require[Walk[C]]` goal — an effect row the witness does not name is \
                 not this goal's to have an opinion about. Got {sols:?}"
            );
        };
        assert_eq!(
            dictionary_impl(&kb, v),
            "x9pb4_e.Src",
            "and the dictionary must name the one carrier that provides `Walk`"
        );
    }
}

// ── the two rows /code-review asked for, both DRIVEN ───────────────────────

/// FOUND BY /code-review AND CONFIRMED AS A REGRESSION THIS TICKET INTRODUCED — the
/// widened candidate set can TIE, and a tie used to be unreachable here.
///
/// `fetch_dictionary` maps a resolution tie to `FindDictFetch::Defect`, whose contract
/// is "overlap is refused at typing/load, so reaching this means the coherence
/// machinery let one through" — `debug_assert!(false, …)` in every debug build. That
/// reading needs the goal to be decided ENTIRELY by the witness's carried types. A
/// SYNTHESIZED element is not decided by them at all, so two providers can tie on
/// precisely the element nobody named — which is no overlap and no defect.
///
/// THE FIXTURE IS THE REVIEW'S OWN SHAPE: one carrier reaching two providers through
/// `types_lesseq` (`Carrier provides MidA`, `Carrier provides MidB`), each writing a
/// BARE-REF `C` — so both score +1 on `C` — and each naming `Note` by its OWN
/// parameter, so both score 0 on the wildcard. `pick_most_specific` finds no winner.
///
/// MEASURED, THREE WAYS:
///  * with the whole ticket backed out — ONE INDEFINITE solution (zero candidates,
///    `NoMatch`, delay). This is the behaviour that must be preserved.
///  * with the wildcard loop in and the tie-routing OUT (`WitnessGoal::from_carried_
///    types`, called `synthesized` when this row was written) — `panicked at
///    resolve.rs: find_dictionary: two providers answer
///    `x9pb4_tie.Spec[C = x9pb4_tie.Carrier, Note = x9pb4_tie.Spec.Note]` at run time:
///    x9pb4_tie.MidA, x9pb4_tie.MidB`. An abort on a program with no defect in it.
///  * as shipped — ONE INDEFINITE solution again.
///
/// THE OTHER ARM — a tie on a goal every element of which came off a CARRIED TYPE,
/// reporting `Defect` — stays undriven, as it was through this ticket and
/// WI-20260913-J38VE. It briefly looked reachable (WI-20260916-8WRJC's own measurement),
/// and the three rows at the foot of this file are why it is not: a tie WITH a default is
/// settled by 058 §3.2 rung 2a before the fetch, and one with NO default does not LOAD.
/// What separates those rows from this one is the ELEMENT: here the tie is on an element
/// NOBODY NAMED, so no provider is wrong and a delay is honest; there both providers
/// answer the very carrier the goal names.
#[test]
fn a_tie_on_a_synthesized_element_delays_rather_than_reporting_a_defect() {
    let src = r#"
namespace x9pb4_tie
  import anthill.prelude.{Int64}

  sort Spec
    sort C = ?
    sort Note = ?
    operation probe(c: C) -> Int64 = 1
  end

  sort MidA
    sort N = ?
    provides Spec[C = MidA, Note = N]
    operation probe(c: MidA) -> Int64 = 7
  end

  sort MidB
    sort N = ?
    provides Spec[C = MidB, Note = N]
    operation probe(c: MidB) -> Int64 = 9
  end

  sort Carrier
    entity carrier
    provides MidA[N = Int64]
    provides MidB[N = Int64]
  end

  rule dict(?x, ?d) :- ?d = require[Spec[C]], Spec.probe(?x, ?ignored)
  rule answer(?d) :- dict(carrier(), ?d)
end
"#;
    let mut kb = load_kb_with(src);
    let sols = query_unary(&mut kb, "x9pb4_tie.answer");
    assert!(
        sols.iter().all(|(_, definite)| !definite),
        "two providers tying on the element NOBODY NAMED must leave the dictionary \
         undecided — a bound `?d` here would be one of two answers picked at random. \
         Got {sols:?}"
    );
    assert!(
        !sols.is_empty(),
        "…and it must DELAY rather than answer nothing, which is what the goal did \
         before this ticket. Got {sols:?}"
    );
}

/// A SELF-REPRESENTING SPEC GETS ITS DICTIONARY TOO — the branch /code-review noticed
/// no fixture reached, DRIVEN rather than excluded.
///
/// `Bag.first(b: Bag)` names its carrier BY THE SORT ITSELF (WI-596's other spec
/// shape), so the pinned loop above the wildcard one pushes NO bindings at all — it
/// sets `SortGoal::carrier` and continues — and EVERY element of the spec is
/// synthesized here. That makes this the widest case the loop produces, and it is
/// sound for the same reason the narrow one is: `IntBag provides Bag[E = N]` names the
/// element by its own parameter, WI-350's carrier filter still selects the impl, and a
/// provision pinning `E` concretely would still be refused.
///
/// FAILS WHEN THE WILDCARD LOOP IS BACKED OUT, measured: `?d` yields one INDEFINITE
/// solution and no carrier, and `Bag.first` answers `Int(7)` INDEFINITELY. So this is
/// evidence, not only a control — a self-representing spec's `require[X]` could not
/// build a dictionary at all before.
#[test]
fn a_self_representing_spec_receives_its_dictionary_too() {
    let src = r#"
namespace x9pb4_sr
  import anthill.prelude.{Int64}

  sort Bag
    sort E = ?
    operation first(b: Bag) -> Int64 = 0
  end

  sort IntBag
    sort N = ?
    entity intBag(n: N)
    provides Bag[E = N]
    operation first(b: IntBag) -> Int64 = 7
  end

  rule dict(?x, ?d) :- ?d = require[Bag[E]], Bag.first(?x, ?ignored)
  rule answer(?d) :- dict(intBag(n: 1), ?d)
end
"#;
    let mut kb = load_kb_with(src);
    let sols = query_unary(&mut kb, "x9pb4_sr.answer");
    let [(v, true)] = sols.as_slice() else {
        panic!(
            "a self-representing spec's `require[Bag[E]]` must bind a DEFINITE \
             dictionary — before this ticket the goal had no bindings at all and \
             every provision with head bindings was rejected. Got {sols:?}"
        );
    };
    assert_eq!(
        dictionary_impl(&kb, v),
        "x9pb4_sr.IntBag",
        "and it must name the carrier WI-350's filter selected"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════
// WHAT HAPPENS TO A TIE WHOSE EVERY ELEMENT CAME OFF A CARRIED TYPE — the three rows
// that bound `FindDictFetch::Defect`'s population, and leave it empty.
//
// It briefly had one. Between the two commits of 2026-09-16 a two-provider program
// REACHED that arm, because `goal_carrier_key` asked `spec_carrier_param` alone and a
// spec whose operations are all NULLARY therefore had no carrier parameter to key a
// default row at — the rung was declined outright and a tie with a perfectly good
// default was reported. WI-20260916-8WRJC closed that (rung 2 of
// `spec_carrier_param_or_sole`), and the arm is once again unreachable by any route
// measured here. Its disposition still changed and stays changed: `BuiltinResult::Error`
// rather than `debug_assert!(false, …)`, because an invariant that holds today is
// exactly the kind that stops holding unnoticed, and the cost of being wrong was an
// aborted process rather than a sentence.
//
// WHAT SEPARATES A SETTLED TIE FROM A REFUSED ONE IS A DEFAULT, and nothing else. 058
// §3.2 rung 2a takes the default among tied candidates and §3.6's INFERRED row makes a
// self-providing carrier its own default, so `Red provides Desc[T = Red]` beside a rival
// is not a tie at all. Where NO row names a winner — two rivals, neither of them the
// carrier — the program does not LOAD, and
// [`a_tie_no_default_settles_is_refused_at_load_naming_both`] pins that refusal.
//
// WI-20260916-8WRJC IS WHY THESE ROWS ARE THREE AND NOT ONE. Until it landed
// `goal_carrier_key` asked `spec_carrier_param` alone, so a spec whose operations are all
// NULLARY had no carrier parameter to key a default row at, the rung was declined
// outright, and the FIRST fixture below — which has a perfectly good default — reported
// a tie. The row that measured that is now
// [`a_nullary_op_spec_takes_its_default_like_any_other`], and its sibling
// [`the_carrier_bearing_spelling_answers_the_same`] is what says the spec's operations no
// longer decide: one defaulted, uncalled `touch(x: T)` used to be the difference between
// a default and a tie.
// ════════════════════════════════════════════════════════════════════════════════════

/// Two providers of `Desc[T = Red]` where ONE OF THEM IS THE CARRIER: `Red` itself (7,
/// and 058 §3.6's inferred `default_provider` row therefore names it) beside `Rival` (11).
/// `tag()` is NULLARY and BODY-LESS, so nothing can value-direct it and no default body
/// can stand in for the dictionary — the dispatch is the only thing under measurement.
fn two_providers(ns: &str, carrier_op: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation tag() -> Int64
{carrier_op}  end

  sort Red
    import anthill.prelude.Int64
    entity red
    provides Desc[T = Red]
    operation tag() -> Int64 = 7
  end

  sort Rival
    import anthill.prelude.Int64
    provides Desc[T = Red]
    operation tag() -> Int64 = 11
  end

  rule tied(p: Red, ?r) :- ?d = require[Desc[T = Red]], Desc.tag(?r)
  rule answer(?r) :- tied(red(), ?r)
end
"#
    )
}

/// TWO RIVAL PROVIDERS AND NO DEFAULT — `Red` provides nothing itself, so 058 §3.6
/// writes no inferred row and rung 2a has no winner to take. `RivalA` and `RivalB` have
/// equal claims on `Desc[T = Red]`.
///
/// THE WITNESS PATH, NOT THE ANCHOR, AND THAT IS FORCED. MEASURED: the anchored spelling
/// (`rule tied(p: Red, …) :- ?d = require[Desc[T = Red]], …`) does not LOAD here — "this
/// clause's head bound(s) — Red — provide no `Desc`" — and a bound that DOES provide is
/// its own default. So after WI-20260916-8WRJC the anchor form cannot tie at all, and
/// the witness form is the arm's whole remaining population: the goal's element comes off
/// `tag`'s ARGUMENT TYPE (`from_carried_types`, which is what makes a tie a `Defect`
/// rather than an `Undecided`), and nothing gates the carrier on providing anything.
fn rival_pair(ns: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation tag(x: T) -> Int64
  end

  sort Red
    entity red
  end

  sort RivalA
    import anthill.prelude.Int64
    provides Desc[T = Red]
    operation tag(x: Red) -> Int64 = 7
  end

  sort RivalB
    import anthill.prelude.Int64
    provides Desc[T = Red]
    operation tag(x: Red) -> Int64 = 11
  end

  rule tied(?r) :- ?d = require[Desc[T]], Desc.tag(red(), ?r)
  rule answer(?r) :- tied(?r)
end
"#
    )
}

/// WI-20260916-8WRJC'S ACCEPTANCE — a spec whose operations are ALL NULLARY keys its
/// default like any other spec.
///
/// `Red` provides `Desc` for itself, so 058 §3.6's inferred row names it and rung 2a has
/// a winner to take. Nothing about that involves an operation, and until this ticket
/// `goal_carrier_key` asked only `spec_carrier_param` — "the param some declared
/// OPERATION receives on" — so this program reported `two providers answer …` instead.
///
/// FAILS WHEN THE CHANGE IS BACKED OUT, measured on the whole workspace: restore
/// `spec_carrier_param` here and this is the ONE row of 7067 that moves, from `7` to zero
/// definite rows and a recorded tie. That number is also the ticket's blast-radius
/// census: the fourteen stdlib sorts that reach rung 2 become default-consultable at the
/// fetch and not one of them has two candidates there.
#[test]
fn a_nullary_op_spec_takes_its_default_like_any_other() {
    let src = two_providers("x9pb4_tie2", "");
    let mut kb = load_kb_with(&src);
    let (sols, errors) = unary_with_errors(&mut kb, "x9pb4_tie2.answer");
    assert!(
        errors.is_empty(),
        "a tie the defaults substrate can settle must not be REPORTED as one; got \
         {errors:?}"
    );
    assert!(
        matches!(
            definite_unary(&mut kb, "x9pb4_tie2.answer").as_slice(),
            [Value::Int(7)]
        ),
        "the DEFAULT is the self-providing carrier's own provision, so `Red` answers 7 \
         and `Rival`'s 11 does not. Solutions were {sols:?}"
    );
}

/// THE CONTROL — the same two providers, the same answer, with a carrier-bearing
/// operation added to the spec.
///
/// PASSES EITHER WAY BY DESIGN, and that is its content: this spelling always worked,
/// because `spec_carrier_param` finds the parameter `touch` receives on. Its job is to
/// pin that the ROW ABOVE differs from it in nothing an author would call semantic — one
/// defaulted operation nobody implements and nobody calls — so the two answering
/// differently was a defect and not a rule.
#[test]
fn the_carrier_bearing_spelling_answers_the_same() {
    let src = two_providers("x9pb4_tie3", "    operation touch(x: T) -> Int64 = 0\n");
    let mut kb = load_kb_with(&src);
    let (sols, errors) = unary_with_errors(&mut kb, "x9pb4_tie3.answer");
    assert!(errors.is_empty(), "no tie to report; got {errors:?}");
    assert!(
        matches!(
            definite_unary(&mut kb, "x9pb4_tie3.answer").as_slice(),
            [Value::Int(7)]
        ),
        "the same 7 the nullary spelling now gives. Solutions were {sols:?}"
    );
}

/// THE OTHER HALF OF THE RULE — a tie NO default settles is refused at LOAD, naming both
/// providers and saying what to write.
///
/// `Red` provides nothing itself, so 058 §3.6 writes no inferred row and rung 2a has no
/// winner to take: `RivalA` and `RivalB` have equal claims on `Desc[T = Red]`. The typer
/// says so before anything runs — *"ambiguous dispatch of `Desc.tag`: 2 instances provide
/// `Desc` … they may coexist, so say which: write `[Desc = …]` in the call's bracket
/// list"*. Take the default where there is one; refuse, with the repair, where there is
/// not.
///
/// PASSES EITHER WAY BY DESIGN — this is the typer's selection check, which
/// WI-20260916-8WRJC does not touch. It is here because it is what says the RESOLVER's
/// tie arm (`FindDictFetch::Defect`, resolve.rs) has no reachable population: a
/// no-default tie never gets past load, and a tie WITH a default is settled by rung 2a
/// before the fetch reports anything.
///
/// MEASURED, both routes to that arm, 2026-09-16:
///   * the ANCHOR form — `rule tied(p: Red, …) :- ?d = require[Desc[T = Red]], …` —
///     does not load either, with a DIFFERENT message ("this clause's head bound(s) —
///     Red — provide no `Desc`"), and a bound that DOES provide is its own default;
///   * the WITNESS form is this row.
/// So the `Error` the arm now returns is the disposition for a BROKEN INVARIANT, not a
/// live path — which is the whole reason it must not be a `debug_assert!`: an invariant
/// that holds today is exactly the kind that stops holding without anyone noticing, and
/// the cost of being wrong was an aborted process rather than a sentence.
#[test]
fn a_tie_no_default_settles_is_refused_at_load_naming_both() {
    let errs = crate::common::try_load_kb_with(&rival_pair("x9pb4_tie4"))
        .err()
        .unwrap_or_else(|| panic!("two rival providers and no default must not LOAD"));
    let joined = errs.join("\n");
    assert!(
        joined.contains("ambiguous dispatch")
            && joined.contains("x9pb4_tie4.RivalA")
            && joined.contains("x9pb4_tie4.RivalB"),
        "the refusal must name BOTH providers — an author told only that something is \
         ambiguous cannot write the bracket that fixes it; got:\n{joined}"
    );
}

/// [`query_unary`]'s goal, resolved so [`anthill_core::kb::resolve::ResolveStats`] comes
/// back with it. Returns each solution's definiteness and the recorded fault messages.
fn unary_with_errors(
    kb: &mut anthill_core::kb::KnowledgeBase,
    qn: &str,
) -> (Vec<bool>, Vec<String>) {
    use anthill_core::kb::resolve::ResolveConfig;
    use anthill_core::kb::term::{Term, Var};
    use smallvec::SmallVec;

    let sym = kb
        .try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("unary_with_errors: `{qn}` does not resolve"));
    let r_sym = kb.intern("r");
    let r_vid = kb.fresh_var(r_sym);
    let r_var = kb.alloc(Term::Var(Var::Global(r_vid)));
    let goal = kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::from_elem(r_var, 1),
        named_args: SmallVec::new(),
    });
    let (sols, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    (
        sols.iter().map(|s| s.is_definite()).collect(),
        stats.errors.iter().map(|e| e.message.clone()).collect(),
    )
}

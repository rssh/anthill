//! WI-20260909-96ZTM — TWO REQUIREMENTS OF ONE SPEC IN ONE CLAUSE ARE TWO DICTIONARIES.
//! Design: `docs/design/060-implementation.md` §8.5; the rebuilt plan and why the first
//! attempt was backed out are in the ticket.
//!
//! ## Since proposal 060.1 §5
//!
//! The ticket's two dictionaries were two `?d = require[X]` bound to two columns, attributed
//! by the written bracket to two typed head bindings, and the acceptance asserted the BOUND
//! dictionaries — handed across a rule boundary, where WI-860's check agreed or refused —
//! because, measured then, two dictionaries per CALL were ill-posed: calls that name carriers
//! need none (value dispatch decides), and two NULLARY calls need them and are
//! indistinguishable. Proposal 060.1 §5 removed the form, and with it every column a
//! dictionary rides. What tells two nullary calls apart now is the requirement's NAME:
//! `require d1: Desc[T = A], require d2: Desc[T = B]`, and `d1.tag(?r1)`, `d2.tag(?r2)` —
//! each call reads the dictionary it names (060.1 §8.6), and a nullary call that names
//! neither is refused, as in an operation body. Two requirements of one spec at one
//! parameter are two dictionaries under two names, and two slots unnamed (§8.5). So the rows
//! below assert through nullary calls, which only a dictionary can answer (the spec's own
//! `tag()` is `1`).
//!
//! The ticket's back-outs — the duplicate-`require` lift, the bracket choosing among anchors,
//! the gate on two `require`s, the one-dictionary-per-call refusal — were measured on the
//! removed form, whose machinery they named; none of them reads a named requirement. The
//! rows for the bracket's dedupe (`two_requires_differing_only_inside_a_type_ARGUMENT_…`) and
//! for an anchor the bracket could not choose (`two_anchors_…`) went with it: a name says
//! which requirement a call reads, and an introducer says which parameter a requirement is at.

use anthill_core::eval::Value;

/// `Leaf` answers 7 and `Other` answers 9, through `describe` and through the NULLARY `tag`,
/// whose spec default is `1` — so a `7` or a `9` from `tag()` came through a dictionary.
fn two_carriers(ns: &str, tail: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
    operation tag() -> Int64 = 1
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
    operation tag() -> Int64 = 7
  end

  sort Other
    import anthill.prelude.Int64
    entity other
    provides Desc[T = Other]
    operation describe(x: Other) -> Int64 = 9
    operation tag() -> Int64 = 9
  end

{tail}end
"#
    )
}

/// The single definite Int each of `{ns}.first` and `{ns}.second` answers, `None` for
/// anything else or for a relation the program does not write.
fn two(ns: &str, src: &str) -> (Option<i64>, Option<i64>) {
    let mut kb = crate::common::load_kb_with(src);
    let mut one = |rel: &str| {
        let qn = format!("{ns}.{rel}");
        kb.try_resolve_symbol(&qn)?;
        match crate::common::query_unary(&mut kb, &qn).as_slice() {
            [(Value::Int(i), true)] => Some(*i),
            _ => None,
        }
    };
    (one("first"), one("second"))
}

/// `first` and `second` over `get(args…, ?r1, ?r2)`.
fn firsts(call: &str) -> String {
    format!(
        "  rule first(?r) :- {}\n  rule second(?r) :- {}\n",
        call.replace("?r1", "?r").replace("?r2", "?"),
        call.replace("?r1", "?").replace("?r2", "?r"),
    )
}

fn refusal(src: &str) -> String {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected a refusal; it loaded clean:\n{src}"))
        .join("\n")
}

/// The clause under test: two requirements of one spec at two type parameters, each under a
/// name, and a nullary call through each.
const GET2: &str = "  rule get2[A, B](?x: A, ?y: B, ?r1, ?r2) :- \
     require d1: Desc[T = A], require d2: Desc[T = B], d1.tag(?r1), d2.tag(?r2)\n";

/// THE ACCEPTANCE. `d1` is the dictionary at `?x`'s type and `d2` at `?y`'s, and each nullary
/// call reads its own: `(7, 9)` at `(leaf, other)`, and swapped with the arguments, `(9, 7)`.
/// No value names either call's carrier, and the spec's own `tag()` is `1`, so the numbers
/// came through the two dictionaries and not through anything else.
#[test]
fn the_two_dictionaries_are_attributed_to_their_own_carriers() {
    let ns = "test.w96ztm.attr";
    let src = |args: &str| {
        two_carriers(ns, &format!("{GET2}{}", firsts(&format!("get2({args}, ?r1, ?r2)"))))
    };
    assert_eq!(two(ns, &src("leaf(), other()")), (Some(7), Some(9)), "`d1` is `Leaf`'s, `d2` `Other`'s");
    assert_eq!(two(ns, &src("other(), leaf()")), (Some(9), Some(7)), "and they follow the arguments");
}

/// THE YARDSTICK: one requirement under a name, one nullary call through it — `Leaf`'s 7,
/// `Other`'s 9.
#[test]
fn the_single_require_clause_is_unchanged() {
    let ns = "test.w96ztm.one";
    for (arg, want) in [("leaf()", 7), ("other()", 9)] {
        let src = two_carriers(
            ns,
            &format!(
                "  rule get[A](?x: A, ?r) :- require d: Desc[T = A], d.tag(?r)\n  \
                 rule first(?r) :- get({arg}, ?r)\n"
            ),
        );
        assert_eq!(two(ns, &src).0, Some(want), "{arg}");
    }
}

/// THE CONTROL the numbers above are read against: the same clause with the requirements
/// deleted answers the spec's DEFAULT for both calls, `(1, 1)` — `tag()` is defaulted, and a
/// call with nothing to say which instance it means folds it. Written without names it is
/// REFUSED at load: an unnamed requirement supplies the evidence for an instance a call names
/// and does not say which instance that is (as in an operation body). So every `7` and `9`
/// above arrived through a named dictionary.
#[test]
fn the_control_without_the_requires_the_row_above_would_lie() {
    let ns = "test.w96ztm.ctl";
    let bare = two_carriers(
        ns,
        &format!(
            "  rule get2(?x, ?y, ?r1, ?r2) :- Desc.tag(?r1), Desc.tag(?r2)\n{}",
            firsts("get2(leaf(), other(), ?r1, ?r2)")
        ),
    );
    assert_eq!(two(ns, &bare), (Some(1), Some(1)), "no requirement: the spec's default, twice");
    let errs = refusal(&two_carriers(
        "test.w96ztm.ctlu",
        "  rule get2[A, B](?x: A, ?y: B, ?r1, ?r2) :- Desc[T = A], Desc[T = B], \
         Desc.tag(?r1), Desc.tag(?r2)\n",
    ));
    assert!(errs.contains("`require s: Desc[…]`") && errs.contains("`s.tag(…)`"), "unnamed: {errs}");
}

/// TWO NAMES AT ONE PARAMETER ARE TWO DICTIONARIES (060.1 §8.6), each read where its name is
/// written: at `leaf()`, both `Leaf`'s, `(7, 7)`. The row refused two equal `require`s —
/// "nothing distinguishes them" — which a name now does; unnamed, the two are two slots, as an
/// operation's two equal `requires` lines are (§8.5).
#[test]
fn two_equal_requires_are_refused() {
    let ns = "test.w96ztm.eq";
    let src = two_carriers(
        ns,
        &format!("  rule get2[A](?x: A, ?r1, ?r2) :- require d1: Desc[T = A], require d2: Desc[T = A], \
         d1.tag(?r1), d2.tag(?r2)\n{}",
        firsts("get2(leaf(), ?r1, ?r2)")),
    );
    assert_eq!(two(ns, &src), (Some(7), Some(7)));
}

/// A NULLARY CALL THAT NAMES NEITHER of two requirements is refused at the call — it writes
/// no instance, and both requirements cover it — naming the two calls to write. The row was
/// the one-dictionary-per-call refusal of a call two bound dictionaries both claimed, which
/// PANICKED with that refusal backed out.
#[test]
fn a_call_two_dictionaries_both_claim_is_refused() {
    let ns = "test.w96ztm.amb";
    let errs = refusal(&two_carriers(
        ns,
        "  rule anchored[A, B](?x: A, ?y: B, ?r) :- require d1: Desc[T = A], \
         require d2: Desc[T = B], Desc.tag(?r)\n",
    ));
    assert!(errs.contains("write `d1.tag(…)` or `d2.tag(…)`"), "got:\n{errs}");
}

/// A CARRIER-BEARING CALL READS THE REQUIREMENT AT ITS OWN ARGUMENT'S PARAMETER, unnamed:
/// `Desc.describe(?x, ?r)` at `?x: A` is covered by `d1` alone, and answers `Leaf`'s 7. The
/// row was the gate that refused two `require`s the written bracket had not each chosen — one
/// call at `?x: Leaf` and a second `require` no call had — which bound the second by scan
/// order with the gate backed out. The introducer says which parameter each requirement is at,
/// and the weave covers a call at its own carrier only.
#[test]
fn a_witness_grounded_pair_is_refused_whatever_the_bracket_says() {
    let ns = "test.w96ztm.wit";
    let src = two_carriers(
        ns,
        "  rule anchored[A, B](?x: A, ?y: B, ?r) :- require d1: Desc[T = A], \
         require d2: Desc[T = B], Desc.describe(?x, ?r)\n  \
         rule first(?r) :- anchored(leaf(), other(), ?r)\n",
    );
    assert_eq!(two(ns, &src).0, Some(7));
}

/// THE CONTROL FOR THE REFUSALS ABOVE, through the NULLARY `tag()`: one requirement under a
/// name threads through it (`7`), where the spec default is `1` — and with the requirement
/// deleted the same call folds that default.
#[test]
fn the_control_a_single_require_threads_through_a_nullary_call() {
    let ns = "test.w96ztm.one2";
    let src = two_carriers(
        ns,
        "  rule anchored[A](?x: A, ?r) :- require d: Desc[T = A], d.tag(?r)\n  \
         rule first(?r) :- anchored(leaf(), ?r)\n",
    );
    assert_eq!(two(ns, &src).0, Some(7), "one named requirement threads through `tag()`");
    let bare = two_carriers(
        ns,
        "  rule anchored(?x, ?r) :- Desc.tag(?r)\n  rule first(?r) :- anchored(leaf(), ?r)\n",
    );
    assert_eq!(two(ns, &bare).0, Some(1), "no requirement: the spec DEFAULT");
}

/// THE NAME DECIDES, NOT THE WRITTEN ORDER: `d2` written first, `d1.tag` still reads the
/// dictionary at `?x`'s type.
#[test]
fn the_bracket_decides_and_not_the_written_order() {
    let ns = "test.w96ztm.ord";
    let src = two_carriers(
        ns,
        &format!("  rule get2[A, B](?x: A, ?y: B, ?r1, ?r2) :- require d2: Desc[T = B], \
         require d1: Desc[T = A], d1.tag(?r1), d2.tag(?r2)\n{}",
        firsts("get2(leaf(), other(), ?r1, ?r2)")),
    );
    assert_eq!(two(ns, &src), (Some(7), Some(9)));
}

// ════════════════════════════════════════════════════════════════════════════════════
// TWO DIFFERENT SPECS — `p(x: Ord[A], y: Eq[B])`
//
// Everything above this line is about two `require`s on ONE spec base, which is what S4
// was filed for: the duplicate pre-pass and the anchored gate both exist to tell two
// dictionaries of the SAME spec apart. TWO DIFFERENT SPECS is a case neither gate has to
// decide — `views_structurally_equal` separates the instances and the anchored gate's
// `find(|(s, _)| *s == canon)` finds no prior entry — so the clause passes both without a
// refusal and each `require` grounds on its own anchor.
//
// (Measured while the clauses wrote `require[…]`; since proposal 060.1 §5 each instance is
// written on its call's receiver, `Ord[A = Red].otag(?a)`, or named at an introducer.)
//
// CENSUSED 2026-09-13 and that is why these rows exist: EVERY fixture in this file, in
// `wi_qmfc5_typed_head_anchor_test.rs` and in `wi_s8cbv_projection_requirement_test.rs`
// uses ONE spec base (`Desc`, or `PartialEq`; `Thing` / `Gadget` there are DATA sorts, not
// specs). The umbrella drove two dictionaries of one spec exhaustively and never drove one
// dictionary each of two specs, so this capability had no pin and a regression would have
// shipped green.
//
// THESE ROWS PIN A CAPABILITY THAT ALREADY WORKS — no source change came with them — AND
// THE BACK-OUT SAYS THEY ARE NOT REDUNDANT. MEASURED 2026-09-13, applying only the FIRST
// weave (`for (call, call_fn, out) in weaves.into_iter().take(1)`): across ALL 4612
// `wi_tests`, **exactly these two rows fail and nothing else does**. So the weave loop
// running more than once — the whole point of "two dictionaries" — was UNDRIVEN before
// them. The existing rows above assert the BOUND dictionaries by value across a rule
// boundary (the file's own fixture discipline: "if a row asserts through a call, the spec
// op must be NULLARY"), which needs no second weave at all; these are the first to make
// TWO covered calls each dispatch through its OWN dictionary.
//
// A BACK-OUT THAT MEASURED NOTHING, recorded so it is not tried again: making the anchored
// gate's lookup spec-BLIND (`find(|_s, _| true)`) fails ZERO rows. That gate only fires
// when one side is NOT anchored (`!found.anchored || !*prev_anchored`), and both requires
// here are anchored — so spec-keying is not what admits this shape, and an earlier draft
// of this comment claimed it was, unmeasured.
// ════════════════════════════════════════════════════════════════════════════════════

/// Two specs, each with a NULLARY BODY-LESS operation, so neither number can be reached by
/// value dispatch or by a default. `combo` is a FACT TABLE rather than arithmetic, so the
/// pair that actually arrived is named: only `(7, 9)` answers `16`.
fn two_specs(ns: &str, tail: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Ord
    import anthill.prelude.Int64
    sort A = ?
    operation otag() -> Int64
    operation orecv(x: A) -> Int64 = 0
  end

  sort Eqq
    import anthill.prelude.Int64
    sort B = ?
    operation etag() -> Int64
    operation erecv(x: B) -> Int64 = 0
  end

  sort Red
    import anthill.prelude.Int64
    entity red
    provides Ord[A = Red]
    operation otag() -> Int64 = 7
  end

  sort Blue
    import anthill.prelude.Int64
    entity blue
    provides Eqq[B = Blue]
    operation etag() -> Int64 = 9
  end

  fact combo(7, 9, 16)
  fact combo(7, 7, 101)
  fact combo(9, 9, 202)
  fact combo(9, 7, 303)

{tail}end
"#
    )
}

/// The single definite `Int` of a solution list, read carrier-neutrally. A fact column
/// used to arrive TERM-carried (`Value::Term`) where an operation's return was a
/// `Value::Int`; since WI-20260907-VM9Q7 an answered literal folds to the native carrier
/// either way, and which carrier it rides is not this file's subject.
fn one_definite_term(kb: &anthill_core::kb::KnowledgeBase, got: &[(Value, bool)]) -> Option<i64> {
    match got {
        [(v, true)] => crate::common::scalar_int(kb, v),
        _ => None,
    }
}

fn two_spec_answer(ns: &str, tail: &str) -> Option<i64> {
    let mut kb = crate::common::load_kb_with(&two_specs(ns, tail));
    let got = crate::common::query_unary(&mut kb, &format!("{ns}.answer"));
    one_definite_term(&kb, &got)
}

#[test]
fn two_typed_head_parameters_bounded_by_DIFFERENT_specs_thread_both_dictionaries() {
    // `16` IS THE WHOLE ASSERTION. It is the `(7, 9)` row of `combo`, and `(7,7)`, `(9,9)`
    // and `(9,7)` are all distinct rows — so one dictionary serving both calls, or either
    // call falling back to anything, answers a different number or none at all.
    assert_eq!(
        two_spec_answer(
            "test.twospec.concrete",
            "  rule p(x: Red, y: Blue, ?r) :- Ord[A = Red].otag(?a), Eqq[B = Blue].etag(?b), \
             combo(?a, ?b, ?r)\n  \
             rule answer(?r) :- p(red(), blue(), ?r)\n",
        ),
        Some(16),
        "both dictionaries must reach their own call",
    );
}

#[test]
fn the_control_one_require_of_the_pair_answers_its_own_number() {
    // WHAT SAYS THE `7` ABOVE CAME FROM `Ord`'s DICTIONARY rather than from anywhere else:
    // drop the `Eqq` require, pair `Ord`'s number with itself, and the table answers the
    // `(7, 7)` row. If `otag()` were reaching some default this would not be `7`.
    assert_eq!(
        two_spec_answer(
            "test.twospec.one",
            "  rule p(x: Red, y: Blue, ?r) :- Ord[A = Red].otag(?a), combo(?a, ?a, ?r)\n  \
             rule answer(?r) :- p(red(), blue(), ?r)\n",
        ),
        Some(101),
    );
}

#[test]
fn the_control_without_either_require_neither_call_answers() {
    // THE ROW THE NUMBERS ABOVE ARE READ AGAINST. Both spec ops are BODY-LESS and write
    // nothing of their spec's carrier, so with no `require` in the clause nothing at either
    // call fixes it — which is what says every number above arrived through a dictionary.
    // Each call is refused at load, naming the `require` that would fix it
    // (WI-20261013-RYDNV). Before, the clause loaded and each call was UNREDUCED (proposal 068
    // §2): every row `combo` enumerated around them was undecided, naming that cause; and
    // before WI-20260926-CYNPE there were NO rows — the WI-938 hook sent such a call to
    // candidate selection and the clause answered nothing, silently.
    let errs = crate::common::load_errors_of(&two_specs(
        "test.twospec.none",
        "  rule p(x: Red, y: Blue, ?r) :- Ord.otag(?a), Eqq.etag(?b), combo(?a, ?b, ?r)\n  \
         rule answer(?r) :- p(red(), blue(), ?r)\n",
    ));
    crate::common::assert_refused_naming(
        &errs,
        &["test.twospec.none.Ord.otag", "`Ord[A = …].otag(…)`"],
        "`otag` names no instance",
    );
    crate::common::assert_refused_naming(
        &errs,
        &["test.twospec.none.Eqq.etag", "`Eqq[B = …].etag(…)`"],
        "`etag` names no instance",
    );
}

#[test]
fn the_other_two_bound_spellings_thread_both_as_well() {
    // THE SAME CAPABILITY AT THE OTHER TWO SPELLINGS a bound can take (§8.3), because
    // which one an author writes must not decide whether two specs are served.
    //
    // INTRODUCER — `p[A, B](x: A, y: B) :- require o: Ord[A = A], require e: Eqq[B = B]`,
    // each nullary call through its requirement's name (`o.otag(?a)`).
    assert_eq!(
        two_spec_answer(
            "test.twospec.introducer",
            "  rule p[A, B](x: A, y: B, ?r) :- require o: Ord[A = A], require e: Eqq[B = B], \
             o.otag(?a), e.etag(?b), combo(?a, ?b, ?r)\n  \
             rule answer(?r) :- p(red(), blue(), ?r)\n",
        ),
        Some(16),
        "the introducer spelling must thread both",
    );
    // (The SPEC-MEMBER spelling, `p(x: Ord.A, y: Eqq.B, ?r)`, wrote its two `require[…]`s at
    // the concrete `Red` and `Blue`, removed by proposal 060.1 §5. Its bound is the
    // introducer's unnamed guard, which a nullary call cannot read; the concrete instances
    // are the first row's.)
}

/// The parameter typed at the spec itself: `Ord` is a spec over `A`, a `Red` provides
/// it and is not an `Ord`, so the bound could match nothing. Refused once per parameter.
#[test]
fn a_parameter_typed_at_the_spec_itself_is_refused() {
    let errs = crate::common::load_errors_of(&two_specs(
        "test.twospec.direct",
        "  rule p(x: Ord, y: Eqq, ?r) :- Ord[A = Red].otag(?a), Eqq[B = Blue].etag(?b), \
         combo(?a, ?b, ?r)\n  \
         rule answer(?r) :- p(red(), blue(), ?r)\n",
    ));
    assert_eq!(errs.len(), 2, "one refusal per parameter; got {errs:#?}");
    assert!(
        errs[0].contains("a rule variable is typed `test.twospec.direct.Ord`")
            && errs[0].contains("Write `test.twospec.direct.Ord.A`"),
        "the first names `Ord` and its member spelling; got {}",
        errs[0],
    );
    assert!(
        errs[1].contains("a rule variable is typed `test.twospec.direct.Eqq`")
            && errs[1].contains("Write `test.twospec.direct.Eqq.B`"),
        "the second names `Eqq` and its member spelling; got {}",
        errs[1],
    );
}

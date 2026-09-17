//! WI-20260909-96ZTM — TWO `require`s IN ONE CLAUSE BIND TWO DICTIONARIES, each to its
//! own variable. Design: `docs/design/060-implementation.md` §8.5; the rebuilt plan and
//! why the first attempt was backed out are in the ticket.
//!
//! ## The acceptance asserts the BOUND DICTIONARIES, not a woven call
//!
//! That is not a stylistic choice — it is the only thing measurable. A first attempt
//! asserted through the calls and its headline row answered `7` and `9` **with both
//! `require`s deleted**: the values came from ordinary value dispatch on the concrete
//! carriers. Measured, two-dictionaries-per-CALL is ill-posed both ways:
//!
//!   * two calls that NAME carriers (`describe(?x)`, `describe(?y)`) do not need
//!     dictionaries at all — value dispatch decides, and deleting both `require`s
//!     changes nothing;
//!   * two NULLARY calls do need them and are indistinguishable — neither names a
//!     carrier, so nothing can say which dictionary it wants.
//!
//! A bound dictionary, though, is directly observable: hand it across a rule boundary
//! and WI-860's supplied-vs-derived check either agrees or refuses. That is what
//! [`the_two_dictionaries_are_attributed_to_their_own_carriers`] uses, and it cannot pass
//! on value dispatch because the discriminating answer is `[]`.

//! ## What fails when each half is backed out — MEASURED, tree restored between
//!
//!  * **The duplicate-`require` lift** (the refusal keyed on the spec BASE again, as
//!    before this ticket). **5 rows** — every row that needs two dictionaries to exist.
//!  * **The bracket choosing among anchors**. **4 rows**, including
//!    `wi_qmfc5…::the_written_bracket_chooses_between_two_anchors`.
//!  * **The gate on two `require`s** — admitting them whatever grounded them. **1 row**:
//!    [`a_witness_grounded_pair_is_refused_whatever_the_bracket_says`], standing in front
//!    of five shapes that otherwise load clean with the WRONG dictionary. Since
//!    WI-20260917-HRFR5 the gate asks whether the WRITTEN BRACKET chose each `require`
//!    rather than whether an ANCHOR grounded it — a widening that leaves this row's two
//!    shapes refused, because neither gives the bracket a witness to choose.
//!  * **The one-dictionary-per-call refusal**. **1 row**:
//!    [`a_call_two_dictionaries_both_claim_is_refused`], which PANICS rather than fails.
//!  * **Carrier direction** — implemented, then REMOVED, because backing it out failed
//!    **0 rows**. For it to matter there would have to be a covered call that names a
//!    carrier and is NOT itself a witness; a nullary op names nothing, and anything with
//!    a carrier parameter is a witness. A branch that cannot be driven is not in the diff.
//!
//! Every count above was produced by a patch that ASSERTS it applied. An earlier
//! back-out in this ticket silently no-oped — rustfmt had reflowed the line it matched
//! on — and reported "no failures", which is indistinguishable from a control that
//! measures nothing.
//!
//! [`the_single_require_clause_is_unchanged`] passes under all of them BY DESIGN — it is
//! WI-1040's own cross-boundary pair, restated as the yardstick.
//!
//! ## What this ticket does NOT touch
//!
//! The WEAVE is unchanged. A first attempt rewrote `weave_covered_call` into a single
//! accumulating pass so one call could carry two dictionaries; that broke NESTED covered
//! calls on a SINGLE `require` (a panic in debug, the spec default in release), and the
//! shape it enabled has no reader — `dictionary_dispatch_target` destructures a
//! one-element slice and eval hard-errors on more, because that channel answers "which
//! instance does THIS CALL dispatch on" and one call dispatches on one instance. N
//! dictionaries at a call site already work through the SLOT-indexed `op_dicts` channel
//! (WI-822), which is a different question and needs nothing from here.

use anthill_core::eval::Value;

/// `Leaf` answers 7 and `Other` answers 9. `use` is the WI-1040 consumer shape: it takes
/// a dictionary through its HEAD and re-derives one locally, so `read_dictionary_into`
/// runs in CHECK mode (WI-860) and disagreement is observable as `[]`.
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

  fact seed(leaf())
  fact seedo(other())

{tail}end
"#
    )
}

fn answers(ns: &str, src: &str) -> Vec<(Value, bool)> {
    let mut kb = crate::common::load_kb_with(src);
    crate::common::query_unary(&mut kb, &format!("{ns}.answer"))
}

/// The single DEFINITE Int of a solution list, or `None` for anything else — an empty
/// list, an indefinite residual, more than one. `None` is what a WI-860 disagreement
/// looks like, and it is the discriminating observation in this file.
fn one_definite(got: &[(Value, bool)]) -> Option<i64> {
    match got {
        [(Value::Int(i), true)] => Some(*i),
        _ => None,
    }
}

/// The clause under test: ONE rule with TWO TYPED HEAD BINDINGS — proposal 060 §3's
/// second anchor, twice — binding TWO dictionaries of one spec and handing both out
/// through its head. `?d1` is written for `Leaf` and `?d2` for `Other`, and the written
/// bracket is what says which anchor each names.
///
/// NO WITNESS CALL, deliberately. The anchors ground both requires, so nothing here
/// depends on which body call a scan happens to reach first — the defect that made the
/// first attempt's pairing come out inverted.
const GET2: &str = "  rule get2(?x: Leaf, ?y: Other, ?d1, ?d2) :- \
     ?d1 = require[Desc[T = Leaf]], ?d2 = require[Desc[T = Other]], \
     seed(?x), seedo(?y)\n  \
     rule use(?x, ?d, ?r) :- ?d = require[Desc[T]], Desc.describe(?x, ?r)\n";

#[test]
fn the_two_dictionaries_are_attributed_to_their_own_carriers() {
    // THE ACCEPTANCE. `?d1` must be `Leaf`'s and `?d2` must be `Other`'s, and the proof is
    // that handing each to a consumer with the MATCHING carrier agrees, while handing it
    // to the other one is refused by WI-860's check.
    //
    // WHY THIS CANNOT PASS ON VALUE DISPATCH: the discriminating observation is `[]`, and
    // no amount of value-directed dispatch produces a REFUSAL. The two agreeing rows pin
    // that the `[]`s are "checked and disagreed" rather than "never arrived" — without
    // them a dictionary dropped on the way would look identical.
    let ns = "test.w96ztm.attr";
    let run = |q: &str| {
        answers(
            ns,
            &two_carriers(ns, &format!("{GET2}  rule answer(?r) :- {q}\n")),
        )
    };

    // ?d1 is Leaf's — agrees with a Leaf consumer, disagrees with an Other one.
    assert_eq!(
        one_definite(&run("get2(leaf(), other(), ?d1, ?), use(leaf(), ?d1, ?r)")),
        Some(7),
        "`?d1` is written for `Leaf` and must agree with a `Leaf` consumer",
    );
    assert!(
        run("get2(leaf(), other(), ?d1, ?), use(other(), ?d1, ?r)").is_empty(),
        "`?d1` is `Leaf`'s, so an `Other` consumer must REFUSE it (WI-860)",
    );

    // ?d2 is Other's — the mirror. This is the pair that says the two are ATTRIBUTED and
    // not merely both present: swap the variable and the verdicts swap with it.
    assert_eq!(
        one_definite(&run("get2(leaf(), other(), ?, ?d2), use(other(), ?d2, ?r)")),
        Some(9),
        "`?d2` is written for `Other` and must agree with an `Other` consumer",
    );
    assert!(
        run("get2(leaf(), other(), ?, ?d2), use(leaf(), ?d2, ?r)").is_empty(),
        "`?d2` is `Other`'s, so a `Leaf` consumer must REFUSE it (WI-860)",
    );
}

#[test]
fn the_single_require_clause_is_unchanged() {
    // THE YARDSTICK. WI-1040's own cross-boundary rows, restated here so a back-out of
    // anything in this ticket is read against a clause that must not move: one `require`,
    // handed to a matching consumer (7) and to a mismatched one (`[]`).
    let ns = "test.w96ztm.one";
    let one = "  rule get(?x, ?d) :- ?d = require[Desc[T]], Desc.describe(?x, ?i)\n  \
               rule use(?x, ?d, ?r) :- ?d = require[Desc[T]], Desc.describe(?x, ?r)\n";
    assert_eq!(
        one_definite(&answers(
            ns,
            &two_carriers(
                ns,
                &format!("{one}  rule answer(?r) :- get(leaf(), ?d), use(leaf(), ?d, ?r)\n")
            )
        )),
        Some(7),
    );
    assert!(answers(
        ns,
        &two_carriers(
            ns,
            &format!("{one}  rule answer(?r) :- get(other(), ?d), use(leaf(), ?d, ?r)\n")
        )
    )
    .is_empty(),);
}

#[test]
fn the_control_without_the_requires_the_row_above_would_lie() {
    // THE CHECK THE FIRST ATTEMPT SKIPPED, and it is why that attempt's headline measured
    // nothing: run the acceptance clause with BOTH `require`s deleted and see which
    // assertions survive.
    //
    // The two AGREEING rows survive — an unbound `?d` lets `use` derive its own
    // dictionary at its own carrier and answer. So they are NOT the evidence.
    // The two DISAGREEING rows do not: they answer a value instead of `[]`, because
    // there is no supplied dictionary for WI-860 to check. THOSE are the load-bearing
    // assertions, and this row is what says so.
    let ns = "test.w96ztm.ctl";
    let bare = "  rule get2(?x: Leaf, ?y: Other, ?d1, ?d2) :- seed(?x), seedo(?y)\n  \
                rule use(?x, ?d, ?r) :- ?d = require[Desc[T]], Desc.describe(?x, ?r)\n";
    let run = |q: &str| {
        answers(
            ns,
            &two_carriers(ns, &format!("{bare}  rule answer(?r) :- {q}\n")),
        )
    };
    assert_eq!(
        one_definite(&run("get2(leaf(), other(), ?d1, ?), use(leaf(), ?d1, ?r)")),
        Some(7),
        "the AGREEING row passes with no `require` at all — it measures value dispatch",
    );
    assert_eq!(
        one_definite(&run("get2(leaf(), other(), ?d1, ?), use(other(), ?d1, ?r)")),
        Some(9),
        "the DISAGREEING row answers 9 here and `[]` in the acceptance — that difference \
         IS the attribution, and it is the only part of the acceptance that measures it",
    );
}

fn refusal(src: &str) -> String {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected a refusal; it loaded clean:\n{src}"))
        .join("\n")
}

#[test]
fn two_equal_requires_are_refused() {
    // ONE `require` IS ONE DICTIONARY. Written twice, nothing distinguishes them, so
    // there is no answer to which is which — refused rather than guessed.
    //
    // THE CONTROL IS THE ACCEPTANCE ITSELF: the same clause with `T = Other` in the
    // second require loads and attributes. One word apart, opposite verdicts.
    let ns = "test.w96ztm.eq";
    let errs = refusal(&two_carriers(
        ns,
        "  rule get2(?x: Leaf, ?y: Other, ?d1, ?d2) :- \
           ?d1 = require[Desc[T = Leaf]], ?d2 = require[Desc[T = Leaf]], \
           seed(?x), seedo(?y)\n",
    ));
    assert!(
        errs.contains("name a different instance") && errs.contains("the same one twice"),
        "got:\n{errs}"
    );
}

#[test]
fn two_requires_differing_only_inside_a_type_ARGUMENT_are_not_equal() {
    // THE ROW THAT KEEPS THE EQUALITY TEST HONEST, and the one a hand-rolled key got
    // wrong: an earlier attempt compared each binding VALUE by its head's SHORT name, so
    // `Desc[T = Box[E = Leaf]]` and `Desc[T = Box[E = Other]]` both keyed `("T","Box")`,
    // compared EQUAL, and this valid program was refused. `views_structurally_equal`
    // compares deeply, so the difference inside the type ARGUMENT is seen.
    //
    // It is still refused — by the ANCHOR gate, because both bounds answer `Box` and the
    // bracket cannot separate them — but for the RIGHT reason, with the right message.
    let ns = "test.w96ztm.deep";
    let errs = refusal(&format!(
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
  sort Box
    sort E = ?
    entity box(v: E)
    provides Desc[T = Box] :- Desc[E]
  end
  fact seedbl(box(v: leaf()))
  fact seedbo(box(v: other()))
  rule get2(?x: Box, ?y: Box, ?d1, ?d2) :- ?d1 = require[Desc[T = Box[E = Leaf]]], ?d2 = require[Desc[T = Box[E = Other]]], seedbl(?x), seedbo(?y)
end
"#
    ));
    assert!(
        !errs.contains("the same one twice"),
        "two requires differing INSIDE a type argument are not equal; got:\n{errs}"
    );
    assert!(
        errs.contains("2 of them do") && errs.contains("the written bracket names no one of them"),
        "they are refused by the ANCHOR gate instead — both bounds answer `Box`; got:\n{errs}"
    );
}

#[test]
fn two_anchors_the_bracket_cannot_choose_between_are_refused() {
    // THE CHOICE MUST BE THE AUTHOR'S. A bare `require[Desc]` names no carrier, so with
    // two anchors there is nothing to select on. This is the control that says the
    // acceptance is driven by the BRACKET and not by anchor order.
    let ns = "test.w96ztm.bare";
    let errs = refusal(&two_carriers(
        ns,
        "  rule get2(?x: Leaf, ?y: Other, ?d) :- ?d = require[Desc], seed(?x), seedo(?y)\n",
    ));
    assert!(
        errs.contains("2 of them do — Leaf, Other")
            && errs.contains("the written bracket names no one of them"),
        "got:\n{errs}"
    );
}

#[test]
fn a_call_two_dictionaries_both_claim_is_refused() {
    // A CALL CARRIES AT MOST ONE DICTIONARY — that is `requirements`' MEANING ("which
    // instance does THIS CALL dispatch on"), not a limit to widen. So a clause that binds
    // two dictionaries for a spec AND contains a call neither can be shown to own is
    // refused, loudly, at the call.
    //
    // WITHOUT THIS the second weave could not find its target by `Rc::ptr_eq` — the first
    // had already rebuilt the node — and the load PANICKED on
    // `debug_assert!(wove, …)`. Driven: lifting the duplicate-`require` refusal without
    // this one reproduces that panic.
    //
    // The nullary `tag()` names no carrier at all, so nothing can tell the two apart —
    // and the row below shows a call that DOES name one is refused too, for a different
    // reason.
    let ns = "test.w96ztm.amb";
    let errs = refusal(&two_carriers(
        ns,
        "  rule anchored(?x: Leaf, ?y: Other, ?r) :- ?d1 = require[Desc[T = Leaf]], ?d2 = require[Desc[T = Other]], seed(?x), seedo(?y), Desc.tag(?r)\n",
    ));
    assert!(
        errs.contains("dispatch through ONE dictionary"),
        "got:\n{errs}"
    );
}

#[test]
fn a_witness_grounded_pair_is_refused_whatever_the_bracket_says() {
    // TWO `require`s ARE ADMITTED ONLY WHERE THE WRITTEN BRACKET CHOSE EACH ONE.
    //
    // WI-20260917-HRFR5 WIDENED THAT AND THESE TWO SHAPES STAY REFUSED, which is why the
    // row survives it: what changed is that a bracket can now choose a WITNESS as well as
    // a head binding, and neither shape here gives it one to choose.
    //
    //   * the first clause has ONE covered call, `Desc.describe(?x, ?r)` at `?x: Leaf`.
    //     `require[Desc[T = Leaf]]` names it, but `require[Desc[T = Other]]` names a
    //     carrier no call in this clause has — so the second `require` is chosen by
    //     nothing, and admitting the pair would bind it by scan order;
    //   * the second has UNTYPED carriers (`eq(?a, ?b)`), whose sorts are a run-time
    //     fact. Nothing at LOAD can say which bracket that call belongs to.
    //
    // The shapes HRFR5 does admit are in `wi_hrfr5_witness_attribution_test`, and the
    // pair here is what says the widening did not become "admit two requires whenever
    // a witness grounds them".
    //
    // THIS IS THE GATE THAT KEEPS THE LIFT HONEST. `/code-review` drove what its absence
    // cost: with the duplicate refusal lifted for EVERY grounding path,
    // `?d1 = require[PartialEq[T = Thing]], ?d2 = require[PartialEq[T = Gadget]],
    // eq(?a, ?b)` loaded clean with BOTH bound to `Thing`'s dictionary — a body-less op
    // is never a covered call, so the one-dictionary-per-call refusal never sees it.
    // Five shapes went from a loud refusal to a silent wrong answer.
    let ns = "test.w96ztm.wit";
    let errs = refusal(&two_carriers(
        ns,
        "  rule anchored(?x: Leaf, ?y: Other, ?r) :- ?d1 = require[Desc[T = Leaf]], ?d2 = require[Desc[T = Other]], seed(?x), seedo(?y), Desc.describe(?x, ?r)\n",
    ));
    assert!(
        errs.contains("unless the WRITTEN BRACKET says which carrier each one means"),
        "got:\n{errs}"
    );

    // AND THE SAME GATE ON THE PLAINEST SHAPE: no typed head at all, so nothing can be
    // anchored. A body-less spec op is used deliberately — it is never a covered call, so
    // this is the shape the one-dictionary-per-call refusal structurally cannot catch.
    let errs = refusal(
        r#"namespace test.w96ztm.bl
  import anthill.prelude.{Int64, PartialEq}
  import anthill.prelude.PartialEq.eq
  sort Thing
    entity thing(v: Int64)
  end
  sort Gadget
    entity gadget(v: Int64)
  end
  fact PartialEq[T = Thing]
  fact PartialEq[T = Gadget]
  rule twin(?a, ?b, ?d1, ?d2) :- ?d1 = require[PartialEq[T = Thing]], ?d2 = require[PartialEq[T = Gadget]], eq(?a, ?b)
end
"#,
    );
    assert!(
        errs.contains("unless the WRITTEN BRACKET says which carrier each one means"),
        "got:\n{errs}"
    );
}

#[test]
fn the_control_a_single_require_threads_through_a_nullary_call() {
    // THE CONTROL FOR THE REFUSALS ABOVE, and it uses the NULLARY `tag()` on purpose.
    //
    // An earlier version of this control used `Desc.describe(?x, ?r)` and asserted `7` —
    // which that clause answers with the `require` deleted AND with the type annotation
    // deleted, because `describe` names its carrier and value dispatch decides. It
    // measured nothing. That is the exact defect the first attempt at this ticket was
    // reverted for, re-landed in the file whose own header states the rule; `/code-review`
    // caught it.
    //
    // `tag()` is nullary, so `1` is the spec default and `7` is reachable only through a
    // dictionary — the three-way check is in
    // [`the_control_without_the_requires_the_row_above_would_lie`].
    let ns = "test.w96ztm.one2";
    assert_eq!(
        one_definite(&answers(
            ns,
            &two_carriers(
                ns,
                "  rule anchored(?x: Leaf, ?r) :- ?d1 = require[Desc[T = Leaf]], seed(?x), Desc.tag(?r)\n  \
                 rule answer(?r) :- anchored(?x, ?r)\n"
            )
        )),
        Some(7),
        "one `require` under one anchor threads through the nullary call",
    );
    // AND THE BACK-OUT OF ITS OWN EVIDENCE: with the `require` gone the same clause folds
    // the spec default. THIS is what says the row measures the dictionary.
    assert_eq!(
        one_definite(&answers(
            ns,
            &two_carriers(
                ns,
                "  rule anchored(?x: Leaf, ?r) :- seed(?x), Desc.tag(?r)\n  \
                 rule answer(?r) :- anchored(?x, ?r)\n"
            )
        )),
        Some(1),
        "no `require` ⇒ the spec DEFAULT — the difference is the whole measurement",
    );
}

#[test]
fn the_bracket_decides_and_not_the_written_order() {
    // WITHOUT THIS ROW an implementation that simply paired the Nth `require` with the
    // Nth anchor would satisfy every assertion above: `GET2` writes `T = Leaf` first
    // under `?x: Leaf`, so bracket order and anchor order agree there. `/code-review`
    // named that as the gap. Here they DISAGREE — `T = Other` is written first — and the
    // attribution must follow the BRACKET.
    let ns = "test.w96ztm.ord";
    let swapped = "  rule get2(?x: Leaf, ?y: Other, ?d1, ?d2) :- \
         ?d1 = require[Desc[T = Other]], ?d2 = require[Desc[T = Leaf]], \
         seed(?x), seedo(?y)\n  \
         rule use(?x, ?d, ?r) :- ?d = require[Desc[T]], Desc.describe(?x, ?r)\n";
    let run = |q: &str| {
        answers(
            ns,
            &two_carriers(ns, &format!("{swapped}  rule answer(?r) :- {q}\n")),
        )
    };
    // `?d1` now holds OTHER's, because that is what its bracket says.
    assert_eq!(
        one_definite(&run("get2(leaf(), other(), ?d1, ?), use(other(), ?d1, ?r)")),
        Some(9),
        "`?d1` is written `T = Other` here, so it must be `Other`'s despite being first",
    );
    assert!(
        run("get2(leaf(), other(), ?d1, ?), use(leaf(), ?d1, ?r)").is_empty(),
        "and a `Leaf` consumer must REFUSE it — the mirror of the acceptance, inverted",
    );
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

/// The single definite `Int` of a solution list. A fact column arrives TERM-carried
/// (`Value::Term`) rather than as a `Value::Int`, unlike an operation's return — so this
/// reads through the term store and [`one_definite`] above cannot be reused.
fn one_definite_term(kb: &anthill_core::kb::KnowledgeBase, got: &[(Value, bool)]) -> Option<i64> {
    match got {
        [(Value::Int(i), true)] => Some(*i),
        [(Value::Term { id, .. }, true)] => match kb.get_term(*id) {
            anthill_core::kb::term::Term::Const(anthill_core::kb::term::Literal::Int(i)) => {
                Some(*i)
            }
            _ => None,
        },
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
            "  rule p(x: Red, y: Blue, ?r) :- ?d1 = require[Ord[A = Red]], \
             ?d2 = require[Eqq[B = Blue]], Ord.otag(?a), Eqq.etag(?b), combo(?a, ?b, ?r)\n  \
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
            "  rule p(x: Red, y: Blue, ?r) :- ?d1 = require[Ord[A = Red]], \
             Ord.otag(?a), combo(?a, ?a, ?r)\n  \
             rule answer(?r) :- p(red(), blue(), ?r)\n",
        ),
        Some(101),
    );
}

#[test]
fn the_control_without_either_require_neither_call_answers() {
    // THE ROW THE NUMBERS ABOVE ARE READ AGAINST. Both spec ops are BODY-LESS, so with no
    // `require` in the clause there is no instance and no default and the clause has NO
    // solutions — which is what says every number above arrived through a dictionary.
    //
    // PASSES EITHER WAY BY DESIGN: it describes the fixture.
    let mut kb = crate::common::load_kb_with(&two_specs(
        "test.twospec.none",
        "  rule p(x: Red, y: Blue, ?r) :- Ord.otag(?a), Eqq.etag(?b), combo(?a, ?b, ?r)\n  \
         rule answer(?r) :- p(red(), blue(), ?r)\n",
    ));
    let got = crate::common::query_unary(&mut kb, "test.twospec.none.answer");
    assert!(got.is_empty(), "expected no solutions, got {got:?}");
}

#[test]
fn the_other_two_bound_spellings_thread_both_as_well() {
    // THE SAME CAPABILITY AT THE OTHER TWO SPELLINGS a bound can take (§8.3), because
    // which one an author writes must not decide whether two specs are served.
    //
    // INTRODUCER — `p[A, B](x: A, y: B) :- Ord[A], Eqq[B]`, where `rule_type_bounds`
    // records THE SPEC for each parameter rather than a carrier sort.
    assert_eq!(
        two_spec_answer(
            "test.twospec.introducer",
            "  rule p[A, B](x: A, y: B, ?r) :- Ord[A], Eqq[B], ?d1 = require[Ord[A = A]], \
             ?d2 = require[Eqq[B = B]], Ord.otag(?a), Eqq.etag(?b), combo(?a, ?b, ?r)\n  \
             rule answer(?r) :- p(red(), blue(), ?r)\n",
        ),
        Some(16),
        "the introducer spelling must thread both",
    );
    // SPEC-APPLICATION — the bound is written as the spec itself.
    assert_eq!(
        two_spec_answer(
            "test.twospec.specbound",
            "  rule p(x: Ord, y: Eqq, ?r) :- ?d1 = require[Ord[A = Red]], \
             ?d2 = require[Eqq[B = Blue]], Ord.otag(?a), Eqq.etag(?b), combo(?a, ?b, ?r)\n  \
             rule answer(?r) :- p(red(), blue(), ?r)\n",
        ),
        Some(16),
        "a spec-application bound must thread both",
    );
}

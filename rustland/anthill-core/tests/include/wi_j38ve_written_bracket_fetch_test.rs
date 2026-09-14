//! WI-20260913-J38VE — THE FETCH READS THE WRITTEN BRACKET: the elements a `require`
//! bracket names are what select the provider row, where before they were replaced by
//! WI-20260830-X9PB4's synthesized wildcard and the clause delayed.
//!
//! Design: `docs/design/060-implementation.md` §8.6.
//!
//! ## What was wrong, and why it was silent
//!
//! `fetch_dictionary` took `(spec_sort, op_functor, arg_vals)` and never saw slot 0 — the
//! spec instance WI-20260909-51W18 retains on the emitted goal. So the goal it built
//! pinned only what a CARRIED TYPE decided (the witness call's arguments, or the anchor's
//! head binding) and wildcarded every other element of the spec. A wildcard is REFUSED
//! against a provider's CONCRETE binding, so `Red provides Sp[C = Red, P = Int64]`
//! answered nothing: no candidate, `Undecided`, and the clause delayed on a clean load.
//!
//! Because a spec operation names only its carrier, "every other element" is EVERY
//! element of every multi-parameter spec — not the corner §8.6 first recorded.
//!
//! ## The rows here, and what each one is for
//!
//! The two ACCEPTANCE rows live in `wi_qmfc5_typed_head_anchor_test.rs`, where they were
//! pinned as delays and this ticket flips them. This file holds what those two cannot
//! reach:
//!
//!  * the WITNESS route ([`a_written_element_the_witness_cannot_name_selects_the_row`]) —
//!    the anchor rows measure only the typed-head producer, and the fix threads slot 0
//!    into BOTH;
//!  * the SUM with WI-20260909-S8CBV gate (1)
//!    ([`a_projected_carrier_and_a_written_element_compose`]) — a bracket whose carrier is
//!    a projection AND whose content is written, which needs both tickets and neither
//!    alone;
//!  * the TIE VERDICT ([`a_tie_a_written_element_does_not_cause_stays_a_delay`]) — the
//!    regression a first cut of this ticket had, kept as a row rather than as a comment;
//!  * an APPLIED element
//!    ([`an_applied_written_element_pins_what_the_author_actually_wrote`]) — a second
//!    first-cut regression, found by `/code-review`: the lowering discarded the written
//!    type's ARGUMENTS, which both lost the agreeing row and selected a disagreeing one.
//!
//! Every fixture's spec op is `tag()`: NULLARY, so nothing in it can value-dispatch, and
//! BODY-LESS in the carrier route's fixtures, so a `7` can only have come through a
//! dictionary. The two parameters are at DIFFERENT types (`C = Red`, `P = Int64`) so an
//! answer cannot be produced by a goal that keyed on the wrong one.
//!
//! ## What fails when each half is backed out — MEASURED, one restore between each
//!
//! | backed out | rows | which |
//! |---|---|---|
//! | THE PREFERENCE (`written_element` → `None` at entry) | **4** | the two acceptance rows in `wi_qmfc5…`, plus [`a_written_element_the_witness_cannot_name_selects_the_row`] and [`a_projected_carrier_and_a_written_element_compose`] — each back to the residual it was |
//! | the WITNESS call site (`witness_sort_goal` passes `&[]`) | **1** | [`a_written_element_the_witness_cannot_name_selects_the_row`] alone — the anchor rows are unmoved, which is what makes this a per-producer axis and not one switch |
//! | the ANCHOR's PARAMETER branch (`anchor_sort_goal` passes `&[]` before `spec_carrier_param_or_sole`) | **2** | `wi_qmfc5…::a_multi_parameter_spec…` and [`a_projected_carrier_and_a_written_element_compose`] |
//! | the ANCHOR's SELF-REPRESENTING branch (passes `&[]`) | **1** | `wi_qmfc5…::a_self_representing_spec…` alone — the two branches of one function are two call sites and are backed out separately |
//! | the FLAG CLEARING (`sort_goal_with_wildcards`' one `from_carried_types = false` made conditional on `written_element` having declined, so only a MINT clears it) | **1** | [`a_tie_a_written_element_does_not_cause_stays_a_delay`], and it ABORTS rather than fails — `debug_assert!(false, "find_dictionary: two providers answer …")` |
//! | the FAITHFUL LOWERING (`written_element` back to `type_value_as_term`) | **1** | [`an_applied_written_element_pins_what_the_author_actually_wrote`], and BOTH its assertions — the agreeing spelling stops answering AND the disagreeing one starts |
//!
//! Each row below states which of those it moves under. The in-fixture controls — the
//! spellings that write NOTHING for the element and must keep delaying — pass under ALL
//! of them by design, and are what say the WRITTEN BINDING is doing the work rather than
//! the fixture.

use anthill_core::eval::Value;

/// A two-parameter spec: a CARRIER `C` and a CONTENT `P` at a different type, with
/// `crecv(x: C)` so the carrier is identifiable (`spec_carrier_param_or_sole`'s rung 1)
/// and can serve as a witness. `tag()` is nullary and BODY-LESS in the spec, so only a
/// dictionary can answer it.
fn two_param(ns: &str, tail: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Sp
    import anthill.prelude.Int64
    sort C = ?
    sort P = ?
    operation tag() -> Int64
    operation crecv(x: C) -> Int64 = 0
  end

  sort Red
    import anthill.prelude.Int64
    entity red
    provides Sp[C = Red, P = Int64]
    operation tag() -> Int64 = 7
    operation crecv(x: Red) -> Int64 = 5
  end

  sort Box
    sort E = ?
    entity box(v: E)
  end

{tail}end
"#
    )
}

/// The single DEFINITE `Int64` of a solution list, or `None` for anything else — no
/// solutions, an indefinite residual, or more than one.
fn one_definite(got: &[(Value, bool)]) -> Option<i64> {
    match got {
        [(Value::Int(i), true)] => Some(*i),
        _ => None,
    }
}

fn answer(ns: &str, tail: &str) -> Option<i64> {
    let mut kb = crate::common::load_kb_with(&two_param(ns, tail));
    one_definite(&crate::common::query_unary(
        &mut kb,
        &format!("{ns}.answer"),
    ))
}

// ── the WITNESS route ───────────────────────────────────────────────────────

#[test]
fn a_written_element_the_witness_cannot_name_selects_the_row() {
    // THE WITNESS PRODUCER'S OWN ROW. `wi_qmfc5…`'s two acceptance rows both go through
    // the typed-head ANCHOR; this clause has no typed head at all — `Sp.crecv(red(), ?c)`
    // is the witness, and `witness_sort_goal` builds the goal. It pins `C` from that
    // call's carried type and could never pin `P`, because no parameter of any `Sp`
    // operation names `P`. That is the whole population: a spec op names its carrier, so
    // every other element of every spec reaches the shared wildcard tail.
    //
    // ASSERTED BY VALUE. `7` is `Red`'s `tag()`; the spec's own `tag()` is body-less, so a
    // clause that failed to thread the dictionary answers a residual, not a wrong number.
    let witness = "  rule answer(?r) :- ?d = require[Sp[C = Red, P = Int64]], \
                   Sp.crecv(red(), ?c), Sp.tag(?r)\n";
    assert_eq!(
        answer("test.j38ve.w", witness),
        Some(7),
        "the written `P = Int64` is what matches `Red provides Sp[C = Red, P = Int64]`",
    );

    // THE CONTROLS, IN THE SAME FIXTURE AND THE SAME CLAUSE SHAPE — the two spellings
    // that say NOTHING about `P`. They must still delay: the wildcard is correct where
    // the author named no element, and this ticket does not widen what a wildcard matches.
    // They pass under every back-out in the file header, which is what makes the row above
    // a measurement of the WRITTEN BINDING rather than of the fixture.
    for (ns, bracket) in [("test.j38ve.wc", "Sp[C = Red]"), ("test.j38ve.wb", "Sp")] {
        let tail = format!(
            "  rule answer(?r) :- ?d = require[{bracket}], Sp.crecv(red(), ?c), Sp.tag(?r)\n"
        );
        assert_eq!(
            answer(ns, &tail),
            None,
            "`{bracket}` names nothing for `P`, so the wildcard stands and the goal delays",
        );
    }
}

// ── the sum with WI-20260909-S8CBV gate (1) ────────────────────────────────

#[test]
fn a_projected_carrier_and_a_written_element_compose() {
    // NEITHER TICKET ALONE REACHES THIS. The carrier is a PROJECTION (`C = p.E`, gate
    // (1)'s δ at fire time) and the content is WRITTEN (`P = Int64`, this ticket). Before
    // gate (1) the clause did not load; after it, and before this ticket, it loaded and
    // residualized — δ resolved `p.E` to `Red` and then the synthesized `P` wildcard threw
    // the row away again.
    //
    // AND IT IS THE ROW THAT SAYS THE TWO READS OF SLOT 0 SHARE ONE WALK: the projected
    // member and the written bindings come off one `extract_type`
    // (`requirement_bracket`), and a bracket that needs both is what would expose them
    // disagreeing.
    //
    // FAILS under THE PREFERENCE and under the ANCHOR's PARAMETER branch.
    assert_eq!(
        answer(
            "test.j38ve.p",
            "  rule anchored(p: Box, ?r) :- ?d = require[Sp[C = p.E, P = Int64]], Sp.tag(?r)\n  \
             rule answer(?r) :- anchored(box(v: red()), ?r)\n"
        ),
        Some(7),
        "`p.E` is `Red` here and the written `P = Int64` is what completes the goal",
    );

    // THE CONTROL: the same projected carrier with `P` left to the wildcard. Still a
    // residual, so the `7` above is the written element's doing and not the projection's.
    assert_eq!(
        answer(
            "test.j38ve.pc",
            "  rule anchored(p: Box, ?r) :- ?d = require[Sp[C = p.E]], Sp.tag(?r)\n  \
             rule answer(?r) :- anchored(box(v: red()), ?r)\n"
        ),
        None,
        "a projected carrier does not by itself decide the spec's other element",
    );
}

// ── the tie verdict, which a first cut of this ticket got wrong ────────────

/// The X9PB4 tie fixture — `Carrier` reaching `Spec` through TWO providers that score
/// alike — at a chosen bracket.
fn tie(ns: &str, bracket: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.{{Int64}}

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

  rule dict(?x, ?d) :- ?d = require[{bracket}], Spec.probe(?x, ?ignored)
  rule answer(?d) :- dict(carrier(), ?d)
end
"#
    )
}

#[test]
fn a_tie_a_written_element_does_not_cause_stays_a_delay() {
    // A REGRESSION THIS TICKET INTRODUCED AND CLOSED, measured on X9PB4's own fixture.
    //
    // `fetch_dictionary` maps a resolution TIE to `FindDictFetch::Defect` — a
    // `debug_assert!(false, …)` in every debug build — and X9PB4 made that conditional on
    // the goal having been decided ENTIRELY by carried types, precisely so this program
    // (two providers `Carrier` reaches through `types_lesseq`, neither more specific)
    // delays instead of aborting. A first cut of this ticket let a WRITTEN element leave
    // that condition intact, on the reading that an element the author named makes the
    // goal fully determined. MEASURED, it aborts:
    //
    //   find_dictionary: two providers answer
    //   `Spec[C = Carrier, Note = Int64]` at run time: MidA, MidB
    //
    // AND THE READING WAS WRONG ON ITS OWN TERMS: the tie is on `C`, which both providers
    // match through subtyping, and has nothing to do with `Note`. Pinning an element does
    // not convert an unrelated tie into overlap. So a written element clears the flag
    // exactly as a minted wildcard does — the flag asks the COARSE question "did anything
    // but a carried type decide this goal", not "which element did they tie on".
    //
    // BACKING OUT the `from_carried_types = false` beside the written pin makes THIS ROW
    // ABORT, and nothing else in the workspace moves.
    for (ns, bracket) in [
        ("j38ve_tie_w", "Spec[C = Carrier, Note = Int64]"),
        ("j38ve_tie_b", "Spec[C]"),
    ] {
        let mut kb = crate::common::load_kb_with(&tie(ns, bracket));
        let sols = crate::common::query_unary(&mut kb, &format!("{ns}.answer"));
        assert!(
            !sols.is_empty() && sols.iter().all(|(_, definite)| !definite),
            "`{bracket}`: two providers tying must leave the dictionary undecided and \
             DELAY — never abort, and never pick one of the two. Got {sols:?}",
        );
    }
}

// ── an APPLIED written element, which /code-review found lossy ─────────────

/// A two-parameter spec whose CONTENT element is an APPLIED type (`Box[E = …]`), with the
/// provider's binding and the bracket's spelled independently.
fn applied(ns: &str, provides: &str, bracket: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Leaf
    entity leaf
  end
  sort Other
    entity other
  end
  sort Box
    sort E = ?
    entity box(v: E)
  end

  sort Sp
    import anthill.prelude.Int64
    sort C = ?
    sort P = ?
    operation tag() -> Int64
    operation crecv(x: C) -> Int64 = 0
  end

  sort Red
    import anthill.prelude.Int64
    entity red
    provides Sp[C = Red, P = {provides}]
    operation tag() -> Int64 = 7
    operation crecv(x: Red) -> Int64 = 5
  end

  rule anchored(x: Red, ?r) :- ?d = require[Sp[C = Red, P = {bracket}]], Sp.tag(?r)
  rule answer(?r) :- anchored(red(), ?r)
end
"#
    )
}

fn applied_answer(ns: &str, provides: &str, bracket: &str) -> Option<i64> {
    let mut kb = crate::common::load_kb_with(&applied(ns, provides, bracket));
    one_definite(&crate::common::query_unary(
        &mut kb,
        &format!("{ns}.answer"),
    ))
}

#[test]
fn an_applied_written_element_pins_what_the_author_actually_wrote() {
    // FOUND BY `/code-review` ON THIS TICKET'S OWN DIFF, and it is a defect this ticket
    // introduced rather than one it inherited. A first cut converted the bracket's value
    // with `type_value_as_term`, which returns the term id only for a `Value::Term` and
    // otherwise falls to `sort_functor_of_view(..).map(|s| kb.alloc(Term::Ref(s)))` — the
    // bare SORT HEAD, arguments discarded. MEASURED: a written binding always arrives as a
    // `Value::Node`, never a `Value::Term`, so EVERY applied element took the lossy path.
    //
    // BOTH FACES WERE WRONG, which is why this row is a pair:
    //   * the AGREEING spelling delayed — the goal pinned bare `Box` and the provider's
    //     applied `Box[E = Leaf]` refused it, so the ticket's headline capability simply
    //     did not hold for an applied element;
    //   * and the DISAGREEING one ANSWERED — `require[…P = Box[E = Other]]` selected the
    //     `Box[E = Leaf]` row, because both had been reduced to `Box`. That is the worse
    //     half: a wrong answer where the pre-ticket code delayed.
    //
    // FIXED by lowering through `value_to_term` — WI-390's "faithful, total Value → Term
    // boundary", whose own doc names this exact use ("the one converter to use where a
    // value-in-type may ride, e.g. a `requires`/`provides` spec").
    //
    // BACKING OUT that converter (back to `type_value_as_term`) fails BOTH assertions
    // here and nothing else in the workspace — the file header's table has it.
    assert_eq!(
        applied_answer("test.j38ve.aa", "Box[E = Leaf]", "Box[E = Leaf]"),
        Some(7),
        "the author's applied element AGREES with the provision, so the row must be found",
    );
    assert_eq!(
        applied_answer("test.j38ve.ad", "Box[E = Leaf]", "Box[E = Other]"),
        None,
        "and a DIFFERENT argument must not select it — reducing both to `Box` made the \
         author's `E = Other` mean nothing",
    );
}

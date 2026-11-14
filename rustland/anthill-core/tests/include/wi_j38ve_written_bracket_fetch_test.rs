//! WI-20260913-J38VE — THE FETCH READS THE WRITTEN BRACKET: the elements a requirement
//! names are what select the provider row, where before they were replaced by
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
//! ## Since proposal 060.1 §5
//!
//! The requirement was the clause's `?d = require[Sp[C = Red, P = Int64]]`, which §5
//! removed. A clause declares it at the head's introducer, under a name since `tag()` takes
//! no argument to name the instance by — `rule g[A](?x: A, ?r) :- require s: Sp[C = A, P =
//! Int64], s.tag(?r)` — and its read reads the instance whole (`carrier_type: true`). Two
//! things moved with it: an element left unwritten is open, read off the provision at the
//! carrier as RYDNV reads it, so the wildcard controls that delayed answer `Red`'s 7; and the
//! rows that select by the written element need a second provision at `C = Red`
//! ([`BY_BOOL`]) to have something to select between. Over those two, an UNWRITTEN `P`
//! answers `Red`'s 7: `Red`'s own provision is the default among a carrier's providers
//! (058 §3.6), as `wi_x9pb4…::a_nullary_op_spec_takes_its_default_like_any_other` has it.
//!
//! ## The rows here, and what each one is for
//!
//!  * the written element selecting between two provisions
//!    ([`a_written_element_the_witness_cannot_name_selects_the_row`]);
//!  * a projected carrier and a written element together — the introducer at the column's
//!    element ([`a_projected_carrier_and_a_written_element_compose`]);
//!  * the TIE VERDICT ([`a_tie_a_written_element_does_not_cause_stays_a_delay`]) — two
//!    providers a carrier reaches alike, which delays and neither aborts nor picks;
//!  * an APPLIED element
//!    ([`an_applied_written_element_pins_what_the_author_actually_wrote`]) — the written
//!    type's arguments select, and a different argument selects nothing.
//!
//! Every fixture's spec op is `tag()`: NULLARY, so nothing in it can value-dispatch, and
//! BODY-LESS, so a `7` can only have come through a dictionary. The two parameters are at
//! DIFFERENT types (`C = Red`, `P = Int64`) so an answer cannot be produced by a goal that
//! keyed on the wrong one.
//!
//! ## What failed when each half was backed out — MEASURED on `require[…]`
//!
//! | backed out | rows | which |
//! |---|---|---|
//! | THE PREFERENCE (`written_element` → `None` at entry) | **4** | the two acceptance rows in `wi_qmfc5…`, plus the witness row and the projected-carrier row — each back to the residual it was |
//! | the WITNESS call site (`witness_sort_goal` passes `&[]`) | **1** | the witness row alone |
//! | the ANCHOR's PARAMETER branch (`anchor_sort_goal` passes `&[]` before `spec_carrier_param_or_sole`) | **2** | `wi_qmfc5…::a_multi_parameter_spec…` and the projected-carrier row |
//! | the ANCHOR's SELF-REPRESENTING branch (passes `&[]`) | **1** | `wi_qmfc5…::a_self_representing_spec…` alone |
//! | the FLAG CLEARING (`sort_goal_with_wildcards`' one `from_carried_types = false` made conditional on `written_element` having declined) | **1** | the tie row, which ABORTED rather than failed — `debug_assert!(false, "find_dictionary: two providers answer …")` |
//! | the FAITHFUL LOWERING (`written_element` back to `type_value_as_term`) | **1** | the applied row, and BOTH its assertions |
//!
//! Those are the removed form's readers. The guard's read was not backed out so; the rows
//! below pin its answers, each beside a spelling that selects nothing.

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

/// A second provision at `C = Red`, a witness at `P = Bool` — what a written `P` selects
/// between.
const BY_BOOL: &str = "  sort ByBool\n    import anthill.prelude.{Int64, Bool}\n    \
                       provides Sp[C = Red, P = Bool]\n    operation tag() -> Int64 = 8\n    \
                       operation crecv(x: Red) -> Int64 = 6\n  end\n";

/// The single DEFINITE `Int64` of a solution list, or `None` for anything else — no
/// solutions, an indefinite residual, or more than one.
fn one_definite(got: &[(Value, bool)]) -> Option<i64> {
    match got {
        [(Value::Int(i), true)] => Some(*i),
        _ => None,
    }
}

/// The goal `answer`'s refusal at load: its dictionary, at the concrete types the goal gives,
/// is built from the provisions there (060.1 §1), and none answers.
#[track_caller]
fn refused_at_load(src: &str, instance: &str) {
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(src),
        &["answer.body", &format!("no provider answers `{instance}`")],
        "the goal at an instance nothing provides",
    );
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
    // THE WRITTEN ELEMENT SELECTS THE ROW. Two provisions at `C = Red`, `Red`'s at
    // `P = Int64` (7) and `ByBool`'s at `P = Bool` (8): the requirement's written `P` is the
    // only thing that tells them apart, and no parameter of any `Sp` operation names `P`.
    //
    // ASSERTED BY VALUE. The spec's own `tag()` is body-less, so a clause that failed to
    // thread the dictionary answers a residual, not a wrong number.
    for (ns, element, want) in [
        ("test.j38ve.wi", "Int64", 7),
        ("test.j38ve.wb", "Bool", 8),
        ("test.j38ve.wo", "?", 7),
    ] {
        let tail = format!(
            "{BY_BOOL}  rule g[A](?x: A, ?r) :- require s: Sp[C = A, P = {element}], s.tag(?r)\n  \
             rule answer(?r) :- g(red(), ?r)\n"
        );
        assert_eq!(
            answer(ns, &tail),
            Some(want),
            "`P = {element}` selects its provision (`?`, unwritten: the carrier's own, the default)"
        );
    }

    // THE CONTROLS, beside `Red`'s provision alone: a written `P` that no provision states
    // selects nothing — the goal at `red()` is refused at load, its dictionary built there and
    // none answering, as an operation's call at `Red` is — and an unwritten one is read off
    // the provision at the carrier.
    let alone = |ns: &str, bracket: &str| {
        answer(
            ns,
            &format!(
                "  rule g[A](?x: A, ?r) :- require s: {bracket}, s.tag(?r)\n  \
                 rule answer(?r) :- g(red(), ?r)\n"
            ),
        )
    };
    refused_at_load(
        &two_param(
            "test.j38ve.wn",
            "  rule g[A](?x: A, ?r) :- require s: Sp[C = A, P = Bool], s.tag(?r)\n  \
             rule answer(?r) :- g(red(), ?r)\n",
        ),
        "test.j38ve.wn.Sp[C = test.j38ve.wn.Red, P = anthill.prelude.Bool]",
    );
    assert_eq!(alone("test.j38ve.wc", "Sp[C = A]"), Some(7), "`P` read off `Red`'s provision");
}

// ── the sum with WI-20260909-S8CBV gate (1) ────────────────────────────────

#[test]
fn a_projected_carrier_and_a_written_element_compose() {
    // A CARRIER AT A COLUMN'S ELEMENT AND A WRITTEN CONTENT. The element of `p: Box[E = E]`
    // is the carrier, which the citation fixes at `Red`, and `P = Int64` is written. The row
    // was `require[Sp[C = p.E, P = Int64]]`, the carrier a PROJECTION (S8CBV gate (1)'s δ at
    // fire time); proposal 060.1 §5 removed it, and the introducer names the element.
    assert_eq!(
        answer(
            "test.j38ve.p",
            "  rule anchored[E](p: Box[E = E], ?r) :- require s: Sp[C = E, P = Int64], s.tag(?r)\n  \
             rule answer(?r) :- anchored(box(v: red()), ?r)\n"
        ),
        Some(7),
        "the element is `Red` here and the written `P = Int64` is `Red`'s provision",
    );

    // THE CONTROL: the same element with a `P` no provision states selects nothing — the goal
    // is refused at load — so the `7` above is the written element's doing and not the
    // carrier's alone.
    refused_at_load(
        &two_param(
            "test.j38ve.pc",
            "  rule anchored[E](p: Box[E = E], ?r) :- require s: Sp[C = E, P = Box[E = Red]], s.tag(?r)\n  \
             rule answer(?r) :- anchored(box(v: red()), ?r)\n",
        ),
        "test.j38ve.pc.Sp[C = test.j38ve.pc.Red, P = test.j38ve.pc.Box[E = test.j38ve.pc.Red]]",
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
    provides Spec[C = Self, Note = N]
    operation probe(c: Self) -> Int64 = 7
  end

  sort MidB
    sort N = ?
    provides Spec[C = Self, Note = N]
    operation probe(c: Self) -> Int64 = 9
  end

  sort Carrier
    entity carrier
    provides MidA[N = Int64]
    provides MidB[N = Int64]
  end

  rule dict[A](?x: A, ?r) :- {bracket}, Spec.probe(?x, ?r)
end
"#
    )
}

#[test]
fn a_tie_a_written_element_does_not_cause_is_refused_not_aborted() {
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
    // BACKING OUT the `from_carried_types = false` beside the written pin made THIS ROW
    // ABORT, and nothing else in the workspace moved — measured while the requirement was
    // `?d = require[Spec[C = Carrier, Note = Int64]]` (removed by proposal 060.1 §5). It is
    // the introducer's guard at the call's carrier now, written and bare. It delayed, asked
    // as a query whose read ran, until a query became typed where it is read (proposal 073
    // §6.2): the query at `carrier()` is refused there, naming both providers, as a rule's
    // goal at `carrier()` is at load (060.1 §1) and an operation's call at `Carrier` is —
    // never an abort, and never one of the two picked.
    for (ns, bracket) in [
        ("j38ve_tie_w", "Spec[C = A, Note = Int64]"),
        ("j38ve_tie_b", "Spec[A]"),
    ] {
        let mut kb = crate::common::load_kb_with(&tie(ns, bracket));
        crate::common::assert_refused_naming(
            &crate::common::query_pattern_refusals(&mut kb, &format!("{ns}.dict({ns}.Carrier.carrier(), ?r)")),
            &["two providers answer", &format!("{ns}.MidA"), &format!("{ns}.MidB")],
            bracket,
        );
        crate::common::assert_refused_naming(
            &crate::common::load_errors_of(&tie(ns, bracket).replacen(
                "  rule dict[A]",
                "  rule answer(?r) :- dict(carrier(), ?r)\n  rule dict[A]",
                1,
            )),
            &["answer.body", "two providers answer", &format!("{ns}.MidA"), &format!("{ns}.MidB")],
            "the goal at `carrier()`",
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

  rule anchored[A](x: A, ?r) :- require s: Sp[C = A, P = {bracket}], s.tag(?r)
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
    //   * and the DISAGREEING one ANSWERED — `require[…P = Box[E = Other]]` (removed by
    //     proposal 060.1 §5; the requirement is the introducer's, under a name) selected the
    //     `Box[E = Leaf]` row, because both had been reduced to `Box`. That is the worse
    //     half: a wrong answer where the pre-ticket code delayed.
    //
    // FIXED by lowering through `value_to_term` — WI-390's "faithful, total Value → Term
    // boundary", whose own doc names this exact use ("the one converter to use where a
    // value-in-type may ride, e.g. a `requires`/`provides` spec"). Since WI-20260829-2NMXA
    // the goal takes the written type on the carrier it rides, and nothing is lowered.
    //
    // BACKING OUT that converter (back to `type_value_as_term`) fails BOTH assertions
    // here and nothing else in the workspace — the file header's table has it.
    assert_eq!(
        applied_answer("test.j38ve.aa", "Box[E = Leaf]", "Box[E = Leaf]"),
        Some(7),
        "the author's applied element AGREES with the provision, so the row must be found",
    );
    // And a DIFFERENT argument must not select it — reducing both to `Box` made the author's
    // `E = Other` mean nothing: the goal at `red()` is refused at load, nothing providing
    // `Sp` at `P = Box[E = Other]`.
    refused_at_load(
        &applied("test.j38ve.ad", "Box[E = Leaf]", "Box[E = Other]"),
        "test.j38ve.ad.Sp[C = test.j38ve.ad.Red, P = test.j38ve.ad.Box[E = test.j38ve.ad.Other]]",
    );
}

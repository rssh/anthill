//! WI-20260922-QHDGC — a LOGICAL VARIABLE is admitted in a requirement's binding, because
//! a logical variable is a type everywhere else; and it reads as the UNWRITTEN element, not
//! as a selector.
//!
//! The ticket admitted it in `require[Spec[T = ?t]]`, where it was refused with the message a
//! literal gets. Proposal 060.1 §5 removed `require[X]`, and a clause's requirement is the
//! head introducer's guard, whose carrier is the introduced variable: `Desc[T = ?t]` has no
//! guard spelling, so the rows here put the variable where a guard has one to hold — the
//! element no call can name, `P` of `Sp[C = A, P = ?p]`. MEASURED on the guard before this
//! change (and on d39bd428): `Sp[C = A, P = ?p]` and `Sp[C = A, P = ?]` loaded and answered
//! NOTHING — the read kept the variable as written, and no provision's `P = Int64` met it —
//! where `Sp[C = A]` answers both carriers. Now a variable nothing has bound is read off the
//! provision as an omitted element is (`provider_requirement_goal_with_provider`), which is
//! QHDGC's rule and DK83Q's (`X[T = ?]` is `X`).
//!
//! The four refusals — a literal, an entity constructor, a rule name, a tuple type — were
//! the `require[…]` lowering's (`report_dropped_spec_binding`). A guard lowered its bindings
//! as DATA and loaded each of them, answering nothing; it refuses them now in the same words
//! (`guard_binding_lowers`), except the CONSTRUCTOR, which a head bound reads
//! as a type (WI-742 §2.1) and a guard therefore admits — its row is inverted.
//!
//! What fails when each part is backed out:
//!  * the variable read as omitted — [`a_variable_element_reads_as_the_abstract_case`] and
//!    [`the_three_other_variable_spellings_load_too`] (no answer);
//!  * the guard's refusal — the three refusal rows (each loads).


/// A two-parameter spec: a CARRIER `C` and a CONTENT `P`, which no `Sp` operation names, so
/// only the requirement can say anything about it. `Red` and `Blue` provide `Sp` at `P =
/// Int64`; `tag()` is nullary and body-less, so `7` and `9` came through a dictionary. The
/// clause declares the requirement at `?x`'s type, `bracket` naming `A` for the carrier.
fn two_carrier(ns: &str, bracket: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.{{Int64, Bool}}

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

  sort Blue
    import anthill.prelude.Int64
    entity blue
    provides Sp[C = Blue, P = Int64]
    operation tag() -> Int64 = 9
    operation crecv(x: Blue) -> Int64 = 6
  end

  fact item(red())
  fact item(blue())

  rule g[A](?x: A, ?r) :- require s: {bracket}, s.tag(?r)
end
"#
    )
}

/// What the queries `g(red(), ?r)` and `g(blue(), ?r)` give, in that order: each one's definite
/// integer answers, or `None` where the query is refused when it is read. A query is typed
/// where it is read (proposal 073 §6.2), so each passes `g`'s guard the dictionary its
/// argument's type builds, and one no provision answers is refused, as a rule body's goal at
/// that type is. The conjunction `item(?x), g(?x, ?r)` leaves `A` open and is refused
/// ([`a_logical_variable_binding_loads`]).
fn two_carrier_answers(ns: &str, bracket: &str) -> [Option<Vec<i64>>; 2] {
    use anthill_core::kb::term_view::TermView;
    let src = two_carrier(ns, bracket);
    let mut kb = crate::common::load_kb_with(&src);
    ["Red.red()", "Blue.blue()"].map(|value| {
        let pattern = format!("{ns}.g({ns}.{value}, ?r)");
        if !crate::common::query_pattern_refusals(&mut kb, &pattern).is_empty() {
            return None;
        }
        let goal = crate::common::query_pattern_term(&mut kb, &pattern);
        let written = anthill_core::kb::load::query_goal_as_written(&kb, &goal);
        let r = TermView::pos_arg(&written, &kb, 1).expect("`?r` is `g`'s second argument").to_value();
        let solutions = kb.resolve(&[goal], &anthill_core::kb::resolve::ResolveConfig::default());
        Some(
            solutions
                .iter()
                .filter(|sol| sol.is_definite())
                .map(|sol| {
                    let v = kb.reify_value(&r, &sol.subst);
                    crate::common::scalar_int(&kb, &v).expect("`g` answers an integer")
                })
                .collect(),
        )
    })
}

/// Both carriers answer, `Red`'s 7 and `Blue`'s 9.
fn both() -> [Option<Vec<i64>>; 2] {
    [Some(vec![7]), Some(vec![9])]
}

/// The refusal text for `bracket`, or a panic if it loaded.
fn refusal(ns: &str, bracket: &str) -> String {
    crate::common::try_load_kb_with(&two_carrier(ns, bracket))
        .err()
        .unwrap_or_else(|| panic!("`{bracket}` must be refused; it loaded clean"))
        .join("\n")
}

// ── the variable is admitted ────────────────────────────────────────────────

#[test]
fn a_logical_variable_binding_loads() {
    let ns = "test.qhdgc.load";
    let errs = crate::common::try_load_kb_with(&two_carrier(ns, "Sp[C = A, P = ?p]")).err();
    assert!(
        errs.is_none(),
        "`Sp[C = A, P = ?p]` must load; got {:?}",
        errs.unwrap().join("\n"),
    );
    // A query that leaves `?x`'s type open passes `g` nothing, and is refused naming `A`.
    let mut kb = crate::common::load_kb_with(&two_carrier(ns, "Sp[C = A, P = ?p]"));
    crate::common::assert_refused_naming(
        &crate::common::query_pattern_refusals(&mut kb, &format!("{ns}.g(?x, ?r)")),
        &["`Sp` at `g`'s `A`"],
        "a query leaving the carrier open",
    );
}

/// The other spellings of a variable at `P` — anonymous, positional, both — answer as the
/// unwritten element does, `Red`'s 7 and `Blue`'s 9. (The row asserted the stored goal's
/// binding was a closed variable at `T`, on `require[Desc[…]]`'s own lowering; the guard's
/// read is the instance the loader builds, and the answer is what says it was read.)
#[test]
fn the_three_other_variable_spellings_load_too() {
    for (ns, bracket) in [
        ("test.qhdgc.anon", "Sp[C = A, P = ?]"),
        ("test.qhdgc.pos", "Sp[A, ?p]"),
        ("test.qhdgc.posanon", "Sp[A, ?]"),
    ] {
        assert_eq!(two_carrier_answers(ns, bracket), both(), "`{bracket}`");
    }
}

// ── the acceptance row, and the two that bound what a variable MEANS ─────────

/// THE ACCEPTANCE ROW — the dictionary is selected PER SOLUTION and answers at two carriers,
/// `7` and `9`, both definite, with the written `P = Int64` beside the carrier. Its control is
/// a `P` no provision states, `Bool`, at which each query is refused — so the row measures the
/// written element doing work, not the fixture. (On `require[Sp[C = ?c, P = Int64]]` the control was
/// the unwritten `Sp[C = ?c]`, which delayed then; the guard reads an unwritten element off the
/// provision, WI-20261013-RYDNV, and it answers.)
#[test]
fn a_variable_element_composes_with_a_written_one_at_two_carriers() {
    assert_eq!(
        two_carrier_answers("test.qhdgc.two", "Sp[C = A, P = Int64]"),
        both(),
        "the written `P` selects, per carrier",
    );
    assert_eq!(
        two_carrier_answers("test.qhdgc.twob", "Sp[C = A, P = Bool]"),
        [None, None],
        "a `P` no provision states is refused — otherwise the row above measures nothing",
    );
}

/// A VARIABLE AT `P` IS THE UNWRITTEN ELEMENT: it answers what `Sp[C = A]` answers, and not
/// what a written sort there answers (`Bool`, refused). FAILS with the variable kept as written
/// (`provider_requirement_goal_with_provider`'s filter): it answers nothing, as on d39bd428.
#[test]
fn a_variable_element_reads_as_the_abstract_case() {
    let written = two_carrier_answers("test.qhdgc.abs1", "Sp[C = A, P = Bool]");
    let omitted = two_carrier_answers("test.qhdgc.abs2", "Sp[C = A]");
    let variable = two_carrier_answers("test.qhdgc.abs3", "Sp[C = A, P = ?p]");
    assert_eq!(omitted, both(), "the unwritten element, read off the provision");
    assert_eq!(variable, omitted, "a variable at `P` must match the spelling that omits `P`");
    assert_ne!(
        variable, written,
        "…and must NOT match a spelling that writes a sort there — a variable is no selector",
    );
}

#[test]
fn a_variable_at_a_provider_tie_is_refused_rather_than_aborting() {
    // THE HAZARD ROW. `fetch_dictionary` maps a resolution TIE to `FindDictFetch::Defect`
    // with `debug_assert!(false, "find_dictionary: two providers answer …")` — an ABORT in
    // every debug build — but only while the goal was decided ENTIRELY by carried types.
    // A variable must not land on the carried-type path. `Carrier` reaches `Spec` through
    // TWO providers that score alike, so this program TIES; the two concrete spellings are
    // the controls, and the variable spellings must be refused as they are. (They were
    // `require[…]` spellings, removed by proposal 060.1 §5; the guard is at `?x`'s type.) A
    // query is typed where it is read (073 §6.2), so the tie is refused there, naming both
    // providers, as a rule body's goal at `carrier()` is at load; it delayed while the query's
    // guard read its dictionary when it ran.
    for bracket in [
        "Spec[C = A]",
        "Spec[C = A, Note = Int64]",
        "Spec[C = A, Note = ?n]",
        "Spec[A, ?]",
    ] {
        let src = format!(
            r#"namespace test.qhdgc.tie
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
        );
        let mut kb = crate::common::load_kb_with(&src);
        crate::common::assert_refused_naming(
            &crate::common::query_pattern_refusals(
                &mut kb,
                "test.qhdgc.tie.dict(test.qhdgc.tie.Carrier.carrier(), ?r)",
            ),
            &["two providers answer", "test.qhdgc.tie.MidA", "test.qhdgc.tie.MidB"],
            bracket,
        );
        // A rule's goal at `carrier()` builds the dictionary at load (060.1 §1), and the tie is
        // refused there, naming both providers, as an operation's call at `Carrier` is.
        crate::common::assert_refused_naming(
            &crate::common::load_errors_of(&src.replace(
                "  rule dict[A]",
                "  rule answer(?r) :- dict(carrier(), ?r)\n  rule dict[A]",
            )),
            &["answer.body", "two providers answer", "test.qhdgc.tie.MidA", "test.qhdgc.tie.MidB"],
            bracket,
        );
    }
}

// ── the other carriers stay refused, one row each ───────────────────────────
//
// ONE ROW PER CARRIER so the refusal is ATTRIBUTABLE: each names its own carrier. A guard
// lowered them as data and loaded each, answering nothing; it refuses them as `require[…]`
// did.

#[test]
fn a_literal_stays_refused() {
    let errs = refusal("test.qhdgc.lit", "Sp[C = A, P = 3]");
    assert!(
        errs.contains("`3` in it names neither a sort nor a type parameter in scope"),
        "the diagnostic must name the literal; got:\n{errs}",
    );
}

/// INVERTED: a constructor is a type where a head bound reads one (WI-742 §2.1), so a guard
/// admits it, and it states a `P` no provision has — `Sp[C = A, P = red]` is refused at each
/// carrier.
/// The `require[…]` lowering refused it as naming no sort.
#[test]
fn an_entity_constructor_stays_refused() {
    assert_eq!(two_carrier_answers("test.qhdgc.ent", "Sp[C = A, P = red]"), [None, None]);
}

#[test]
fn a_rule_name_stays_refused() {
    let errs = refusal("test.qhdgc.rule", "Sp[C = A, P = item]");
    assert!(
        errs.contains("`item` in it names neither a sort nor a type parameter in scope"),
        "the diagnostic must name the rule; got:\n{errs}",
    );
}

#[test]
fn a_tuple_type_stays_refused() {
    let errs = refusal("test.qhdgc.tup", "Sp[C = A, P = (Red, Red)]");
    assert!(
        errs.contains("names neither a sort nor a type parameter in scope"),
        "a tuple type must stay refused; got:\n{errs}",
    );
}

// ── the controls that ALREADY passed ─────────────────────────────────────────

#[test]
fn the_head_parameter_spelling_already_passed() {
    // CONTROL: `?x: ?t` is a head parameter whose TYPE is a logical variable — the evidence
    // that a variable is no category error in type position. Loads on either tree.
    let src = two_carrier("test.qhdgc.param", "Sp[C = A]").replace(
        "  rule g[A]",
        "  rule answer(?r) :- item(?x), inner(?x, ?r)\n  rule inner(?x: ?t, ?r) :- ?r <=> 1\n  rule g[A]",
    );
    assert!(
        crate::common::try_load_kb_with(&src).is_ok(),
        "the head-parameter control must load on either tree",
    );
}

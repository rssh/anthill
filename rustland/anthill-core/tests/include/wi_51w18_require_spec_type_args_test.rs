//! WI-20260909-51W18 — a `require[X]` / `requires(X)` kept the spec's TYPE ARGUMENTS.
//!
//! `requirement-channel.md` §10 item 1, whose answer is written at
//! `docs/design/060-implementation.md` §8.6. Both producers used to strip the bracket, so
//! `require[Desc]` and `require[Desc[T = Leaf]]` were byte-identical after convert; this
//! ticket kept it, lowered as a TYPE (`build_require_spec_occurrence`), and refused what
//! named no sort.
//!
//! ## Since proposal 060.1 §5
//!
//! `require[X]` and `requires(X)` are removed, and with them that lowering's population. A
//! clause's requirement is its head introducer's guard, whose bindings the loader reads when
//! it folds the guard (`try_body_tvar_guard`): positional and named against the spec's
//! declared parameters, a bogus name or an over-application refused there already. What this
//! file drove for the bracket is driven for the guard, by the answers the requirement gives
//! rather than the stored goal's shape: a written binding selects, positional is named, a name
//! is resolved where it is written — the spec's own parameter name at namespace level is
//! refused, inside a sort declaring it is that sort's (WI-20261021-Z2P21) — and a binding that
//! names no sort — which a guard lowered as DATA, loading and answering nothing — is refused in
//! the bracket's words (`guard_binding_lowers`). The rows on the stored shape, on the check tier and on the term
//! surfaces of `requires(X)` went with the forms; the term surfaces refuse the removed
//! spelling now.
//!
//! What fails when `guard_binding_lowers` is backed out (every binding lowered as written):
//! [`a_name_that_denotes_nothing_is_reported`] and [`a_binding_that_is_not_a_name_at_all_is_reported`]
//! (each loads).

/// A two-parameter spec: a CARRIER `C`, which `crecv(x: C)` receives on, and a content `P`
/// no operation names. `Red` provides it at `P = Int64` (5), `ByBool` at `P = Bool` (6) — so
/// a written `P` is what selects between them. The clause's requirement is `spec`, at the
/// introducer `A`, cited at `red()`.
fn program(ns: &str, spec: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.{{Int64, Bool}}

  sort Sp
    import anthill.prelude.Int64
    sort C = ?
    sort P = ?
    operation crecv(x: C) -> Int64 = 0
  end

  sort Red
    import anthill.prelude.Int64
    entity red
    provides Sp[C = Red, P = Int64]
    operation crecv(x: Red) -> Int64 = 5
  end

  sort ByBool
    import anthill.prelude.{{Int64, Bool}}
    provides Sp[C = Red, P = Bool]
    operation crecv(x: Red) -> Int64 = 6
  end

  fact item(1)
  rule g[A](?x: A, ?r) :- {spec}, Sp.crecv(?x, ?r)
  rule answer(?r) :- g(red(), ?r)
end
"#
    )
}

/// The definite `Int64` answers of `{ns}.answer`, sorted.
fn answers(ns: &str, spec: &str) -> Vec<i64> {
    answers_of(&program(ns, spec), ns)
}

/// [`answers`] over the program `src`.
fn answers_of(src: &str, ns: &str) -> Vec<i64> {
    let mut kb = crate::common::load_kb_with(src);
    let mut out: Vec<i64> = crate::common::query_unary(&mut kb, &format!("{ns}.answer"))
        .iter()
        .map(|sol| match sol {
            (anthill_core::eval::Value::Int(i), true) => *i,
            other => panic!("`{ns}.answer` must answer definite Ints, got {other:?}"),
        })
        .collect();
    out.sort_unstable();
    out
}

fn refusal(ns: &str, spec: &str) -> String {
    crate::common::try_load_kb_with(&program(ns, spec))
        .err()
        .unwrap_or_else(|| panic!("`{spec}` must be refused; it loaded clean"))
        .join("\n")
}

/// A WRITTEN BINDING SELECTS: `P = Int64` is `Red`'s provision (5), `P = Bool` `ByBool`'s (6).
#[test]
fn a_written_binding_survives_onto_the_stored_goal() {
    assert_eq!(answers("test.w51w18.wi", "Sp[C = A, P = Int64]"), vec![5]);
    assert_eq!(answers("test.w51w18.wb", "Sp[C = A, P = Bool]"), vec![6]);
}

/// THE POSITIONAL SPELLING BINDS AS THE NAMED ONE: `Sp[A, Int64]` is `Sp[C = A, P = Int64]`,
/// and a positional after a named binding takes the next parameter the name left,
/// `Sp[P = Bool, A]` binding `A` at `C`.
#[test]
fn the_positional_spelling_binds_the_same_way() {
    assert_eq!(answers("test.w51w18.pos", "Sp[A, Int64]"), vec![5]);
    assert_eq!(answers("test.w51w18.mixed", "Sp[P = Bool, A]"), vec![6]);
}

/// A BOGUS PARAMETER NAME AND AN OVER-APPLICATION ARE REFUSED, as invalid type arguments.
#[test]
fn a_bogus_parameter_name_and_an_over_application_are_refused() {
    for (spec, expect) in [
        ("Sp[C = A, Bogus = Int64]", "no type parameter named 'Bogus'"),
        ("Sp[A, Int64, Int64]", "over-applied"),
    ] {
        let errs = refusal("test.w51w18.argck", spec);
        assert!(
            errs.contains(expect) && errs.contains("invalid type argument"),
            "`{spec}` must be refused as an invalid type argument naming {expect}; got:\n{errs}",
        );
    }
}

/// A NAME IN THE GUARD IS RESOLVED WHERE IT IS WRITTEN, and the spec's own parameter name is
/// no exception (WI-20261021-Z2P21): at namespace level nothing is named `P`, so `Sp[C = A, P =
/// P]` is refused naming it, as an operation's `requires Sp[C = A, P = P]` is, positionally
/// (`Sp[A, P]`), with the keyword and under a name alike. The element that selects no instance
/// is written `?` or left out, and each spelling of that answers `Red`'s own 5 (058 §3.6: a
/// carrier that provides a spec for itself is its own default among the two at `Red`). FAILS
/// with the spec's own parameter name read as the element left out (the early return in
/// `report_dropped_spec_binding`): each of the four loads and answers 5.
#[test]
fn the_specs_own_parameter_name_is_refused_where_nothing_declares_it() {
    for spec in ["Sp[C = A, P = P]", "Sp[A, P]", "require Sp[C = A, P = P]"] {
        let errs = refusal("test.w51w18.free", spec);
        assert!(
            errs.contains("`P` in it names neither a sort nor a type parameter in scope (`P` is the name of one of `Sp`'s own type parameters")
                && errs.contains("written `?` or left out"),
            "`{spec}` must be refused naming `P` and the repair; got:\n{errs}",
        );
    }
    let named = crate::common::try_load_kb_with(
        &program("test.w51w18.named", "require s: Sp[C = A, P = P]").replace("Sp.crecv(?x, ?r)", "s.crecv(?x, ?r)"),
    )
    .err()
    .expect("the named form must be refused")
    .join("\n");
    assert!(named.contains("`P` in it names neither a sort nor a type parameter in scope"), "got:\n{named}");
    for repair in ["Sp[C = A]", "Sp[C = A, P = ?]", "Sp[A, ?]"] {
        assert_eq!(answers("test.w51w18.repair", repair), vec![5], "`{repair}`");
    }
}

/// Inside a sort that declares `P` the guard's `P` is that sort's, fixed where the rule is
/// cited, as an operation's `requires` there is: `Box[P = Bool].g` is `ByBool`'s 6 and `Box[P =
/// Int64].g` `Red`'s 5. Passes with the early return in `report_dropped_spec_binding` restored,
/// by design (the name resolves before it is asked); fails with the citation's read of `P`
/// backed out (`dictionary_at_goal`, wi_z2p21_guard_at_a_sort_parameter_test): 5 at `Bool`.
#[test]
fn the_name_is_the_enclosing_sorts_parameter_where_one_is_declared() {
    for (bracket, want) in [("Bool", 6), ("Int64", 5)] {
        let ns = format!("test.w51w18.insort{bracket}");
        let src = program(&ns, "Sp[C = A]").replace(
            "  rule g[A](?x: A, ?r) :- Sp[C = A], Sp.crecv(?x, ?r)\n",
            "  sort Box\n    import anthill.prelude.Int64\n    sort P = ?\n    \
             rule g[A](?x: A, ?r) :- Sp[C = A, P = P], Sp.crecv(?x, ?r)\n  end\n",
        );
        assert!(src.contains("sort Box"), "the fixture's rule line moved");
        let src = src.replace("g(red(), ?r)", &format!("Box[P = {bracket}].g(red(), ?r)"));
        assert_eq!(answers_of(&src, &ns), vec![want], "`Box[P = {bracket}]`");
    }
}

/// A NAME THAT DENOTES NOTHING IS REPORTED, naming itself. A guard lowered it as data and the
/// load reported an unresolved name in a scope's words; the bracket's sentence says what the
/// position takes.
#[test]
fn a_name_that_denotes_nothing_is_reported() {
    let errs = refusal("test.w51w18.zork", "Sp[C = A, P = Zork]");
    assert!(
        errs.contains("`Sp` has a type parameter list (it declares C, P), and `Zork` in it names neither a sort nor a type parameter in scope;"),
        "got:\n{errs}",
    );
    assert!(!errs.contains("unresolved name"), "reported once, in the bracket's words: {errs}");
}

/// A BINDING THAT IS NOT A NAME AT ALL — a literal, a rule name — is reported naming itself. A
/// guard lowered either as data and loaded; the rule name answered nothing.
#[test]
fn a_binding_that_is_not_a_name_at_all_is_reported() {
    for written in ["3", "item"] {
        let errs = refusal("test.w51w18.lit", &format!("Sp[C = A, P = {written}]"));
        assert!(
            errs.contains(&format!("`{written}` in it names neither a sort")),
            "`{written}`: got:\n{errs}",
        );
    }
}

/// THE REMOVED SPELLINGS IN EVERY TERM SURFACE — a constraint's body, its named form, an
/// operation's `ensures` — are refused where they stand (they loaded, carrying their bracket).
#[test]
fn a_bracketed_requires_loads_in_every_term_surface() {
    for (name, tail) in [
        ("constraint", "  constraint c: false :- requires(Sp[C]), item(?x)\n"),
        ("constraint-bind", "  constraint c: false :- ?d = require[Sp[C]], item(?x)\n"),
        ("ensures", "  operation we(x: Int64) -> Int64 ensures requires(Sp[C]) = x\n"),
    ] {
        let src = program("test.w51w18.term", "Sp[C = A]").replace("end\n", &format!("{tail}end\n"));
        let errs = crate::common::parse_errs(&src);
        assert!(errs.iter().any(|e| e.contains("is no longer written")), "{name}: {errs:?}");
    }
}

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
//! rather than the stored goal's shape: a written binding selects, positional is named, the
//! spec's own parameter name is the open binding, and a binding that names no sort — which a
//! guard lowered as DATA, loading and answering nothing — is refused in the bracket's words
//! (`guard_binding_lowers`). The rows on the stored shape, on the check tier and on the term
//! surfaces of `requires(X)` went with the forms; the term surfaces refuse the removed
//! spelling now.
//!
//! What fails when `guard_binding_lowers` is backed out (every binding lowered as written):
//! [`a_name_that_denotes_nothing_is_reported`] and [`a_binding_that_is_not_a_name_at_all_is_reported`]
//! (each loads), [`the_free_parameter_spelling_answers_as_the_bare_one_does`] (an unresolved
//! name).

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
    let mut kb = crate::common::load_kb_with(&program(ns, spec));
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

/// THE SPEC'S OWN PARAMETER NAME IS THE OPEN BINDING, as it was in `require[Spec[T]]`: `Sp[C
/// = A, P = P]` answers what `Sp[C = A]` answers. With `P` open, `Red`'s own provision is the
/// default among the two at `Red` (058 §3.6: a carrier that provides a spec for itself is its
/// own default), so both answer its 5. FAILS with the binding lowered as written: an
/// unresolved name `P`.
#[test]
fn the_free_parameter_spelling_answers_as_the_bare_one_does() {
    assert_eq!(answers("test.w51w18.bare", "Sp[C = A]"), vec![5]);
    assert_eq!(answers("test.w51w18.free", "Sp[C = A, P = P]"), vec![5]);
}

/// A NAME THAT DENOTES NOTHING IS REPORTED, naming itself and the spec's own parameters. A
/// guard lowered it as data and the load reported an unresolved name in a scope's words; the
/// bracket's sentence says what the position takes.
#[test]
fn a_name_that_denotes_nothing_is_reported() {
    let errs = refusal("test.w51w18.zork", "Sp[C = A, P = Zork]");
    assert!(
        errs.contains("`Zork` in it names neither a sort nor one of `Sp`'s own type parameters (C, P)"),
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

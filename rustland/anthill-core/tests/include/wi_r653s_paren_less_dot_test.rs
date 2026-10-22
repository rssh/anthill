//! WI-20261008-R653S — a member of a sort written WITHOUT PARENTHESES gives one answer in
//! every spelling (kernel-language.md §5.4, *A receiver that denotes a sort*; §6.7, *A
//! dotted paren-less name in a LOGICAL position*).
//!
//! THE RULE (user, 2026-10-22: "in Box.zero V is inferred — so it should be the same as
//! written V"). Without parentheses a member is the call with no arguments that the written
//! `Sort[…].m()` makes:
//!
//!   Box.zero    Box[V = Int64].zero    (Box).zero    let t = Box; t.zero
//!
//! all call `zero`; the sort's parameters are inferred where the spelling binds none, and
//! the bracket or an alias binds them where it does. A rule member is the relation the
//! written `Box.rows` cites. BEFORE, measured on 31fef79b: `t.zero` and `(Box).zero`
//! called, `Box.zero` was refused as an unresolved name, `Box[V = Int64].zero` as "a RULE
//! citation", and `t.rows` / `(Box).rows` as "declared in `Box` and is neither".
//!
//! EVERY ROW HAS ITS OWN SOURCE: a refused fixture would take every row sharing it down.
//!
//! CONTROLS — each piece backed out on its own, one temporary switch per piece, all in
//! one build, measured over this module and the six it moved
//! (`dotted_nullary_op_call_test`, `wi_5g28a_paren_less_citation_test`,
//! `wi_papx0_dot_receiver_split_test`, `wi_a3fy2_rule_body_type_receiver_test`,
//! `wi_rxt6s_dotted_sort_type_value_test`, `wi1075_absolute_path_test`; 95 rows):
//!
//!   [L] the loader's operation rung (`Loader::try_qualified_op_ref` answering `false`)
//!       — FAIL:
//!         a_nullary_operation_is_its_call_in_every_spelling
//!         the_sorts_parameters_are_inferred_where_nothing_binds_them
//!         a_chain_past_the_operation_reads_its_value
//!         a_const_value_calls_it
//!         an_internal_operation_is_refused_as_its_applied_name_is
//!         dotted_nullary_op_call_test::an_operation_body_calls_it_too
//!         wi_rxt6s_dotted_sort_type_value_test::a_member_past_the_sort_is_its_call
//!   [R] the bracketed spelling refused for an operation again (the refusal not skipping
//!       `SymbolKind::Operation`) — FAIL:
//!         a_nullary_operation_is_its_call_in_every_spelling
//!         a_spec_member_is_called_at_the_bracket
//!         wi_5g28a_paren_less_citation_test::a_paren_less_bracket_on_an_operation_is_its_call
//!   [P] a nullary operation no value prefix (`resolve_qualified_value_readonly` without
//!       its operation arm) — FAIL: a_chain_past_the_operation_reads_its_value
//!   [T] the typer's rule arm (`written_sort_dot` finding no rule) — FAIL:
//!         a_rule_member_is_the_relation_in_every_spelling
//!         a_rule_member_in_a_rule_body_is_the_goal
//!   [I] the `internal` arm of the operation rung — FAIL:
//!         an_internal_operation_is_refused_as_its_applied_name_is
//!   [AR] the resolver's alias reading (`nullary_op_component`) — FAIL:
//!         an_alias_in_a_rule_body_is_read_as_its_sort (`?x <=> CA.zero` binds the term)
//!   [AT] the typer's alias reading (`dotted_citation_nullary_op`) — FAIL:
//!         an_alias_in_a_rule_body_is_read_as_its_sort (`5 = CA.zero` is refused)
//!
//! A MEMBER THAT TAKES ARGUMENTS, AND A ONE-SEGMENT NAME (user, 2026-10-22, "let fix both
//! now"). Written without parentheses such a member is read as its one-segment name:
//! a function value where one is expected, at the receiver's parameters, and refused as
//! the name is elsewhere. And a one-segment name of a parametric sort's member fixes the
//! sort's parameters where it stands, as its call does. Measured the same way, over this
//! module and the four others it touches (69 rows):
//!
//!   [E1] `open_declaring_sort_params` answering its input — FAIL:
//!         a_one_segment_name_is_at_parameters_of_its_own
//!         a_member_that_takes_arguments_is_its_function_value
//!         the_receivers_parameters_are_the_functions
//!   [E2] its pin from the expected type — FAIL: a_one_segment_name_is_at_parameters_of_its_own
//!   [E3] its pin from the receiver — FAIL: the_receivers_parameters_are_the_functions
//!   [E4] `paren_less_member_as_function` answering `None` — FAIL:
//!         a_member_that_takes_arguments_is_its_function_value
//!         the_receivers_parameters_are_the_functions
//!         elsewhere_it_is_refused_as_its_one_segment_name_is
//!   [E5] `is_hof_shaped` without its paren-less arm — FAIL:
//!         a_member_that_takes_arguments_is_its_function_value
//!         the_receivers_parameters_are_the_functions
//!   [E6] the call a dot on a sort makes not carrying the dot's `paren_less` — FAIL:
//!         a_member_that_takes_arguments_is_its_function_value
//!         the_receivers_parameters_are_the_functions
//!         elsewhere_it_is_refused_as_its_one_segment_name_is
//!   [E7] the converter not marking `(e).m` — FAIL:
//!         a_member_that_takes_arguments_is_its_function_value (its `(Box).inc` rows)
//!
//! PASS UNDER EVERY BACK-OUT, by design: the applied controls inside each row
//! (`Box.zero()`, `Box.rows(1)`, `CA.zero()`, …), and the let-bound and parenthesized
//! spellings of a nullary operation, which called before this change.

use anthill_core::eval::Value;

use crate::common::{interp_for, load_errors_of, load_kb_with, query_unary};

/// The sorts every row is about, indented for a namespace body.
const BOX: &str = r#"
  sort P
    entity pt(x: Int64, y: Int64)
    operation sum(p: P) -> Int64 = match p
      case pt(x, y) -> x + y
  end
  sort Box[V]
    entity mk(v: V)
    entity nul
    operation zero() -> Int64 = 5
    operation inc(x: Int64) -> Int64 = x + 1
    operation wrap(x: V) -> V = x
    operation origin() -> P = pt(x: 3, y: 4)
    operation empty() -> Box[V] = nul
    rule rows(?x) :- base(?x)
  end
  sort CA = Box[V = Int64]
  fact base(1)
  fact base(2)
"#;

/// A namespace `test.<ns>` holding [`BOX`] and `body`, preceded by `prefix` (another
/// namespace, for the row that reads a sort from outside it).
fn source(ns: &str, prefix: &str, body: &str) -> String {
    format!(
        "{prefix}\nnamespace test.{ns}\n  import anthill.prelude.{{Type, Bool, Int64, String, Error, Additive}}\n{BOX}\n{body}\nend\n"
    )
}

/// Load, call `test.<ns>.go()`, and hand back its integer.
fn run_int(ns: &str, prefix: &str, body: &str) -> i64 {
    let mut interp = interp_for(&source(ns, prefix, body));
    match interp.call(&format!("test.{ns}.go"), &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{ns}: expected an Int64, got {other:?}"),
    }
}

/// `go` returning `expr`, which may start with `let` lines.
fn go(expr: &str) -> String {
    format!("  operation go() -> Int64 effects {{Error}} =\n    {expr}")
}

/// Load, resolve `test.<ns>.r(?x)`, and hand back the integers `?x` is bound to. Every
/// answer must be definite.
fn ints(ns: &str, body: &str) -> Vec<i64> {
    let mut kb = load_kb_with(&source(ns, "", body));
    let mut got: Vec<i64> = query_unary(&mut kb, &format!("test.{ns}.r"))
        .into_iter()
        .map(|(v, definite)| {
            assert!(definite, "{ns}: a conditional answer, {v:?}");
            match v {
                Value::Int(n) => n,
                other => panic!("{ns}: expected an Int64, got {other:?}"),
            }
        })
        .collect();
    got.sort();
    got
}

/// The refusals of a source that must not load, rendered.
fn refusal(ns: &str, prefix: &str, body: &str) -> String {
    let errs = load_errors_of(&source(ns, prefix, body));
    assert!(!errs.is_empty(), "{ns}: must be refused, and loaded clean");
    format!("{errs:?}")
}

/// The message the written spelling drew before: its segments read as names nothing
/// declares. No refusal below may be that one.
const UNRESOLVED: &str = "expected resolved name";

// ── an operation ────────────────────────────────────────────────────────────

#[test]
fn a_nullary_operation_is_its_call_in_every_spelling() {
    for (ns, body, expected) in [
        ("r653sapplied", go("Box.zero()"), 5),
        ("r653swritten", go("Box.zero"), 5),
        ("r653sbracket", go("Box[V = Int64].zero"), 5),
        ("r653slet", go("let t = Box\n    t.zero"), 5),
        ("r653sletbr", go("let t = Box[V = Int64]\n    t.zero"), 5),
        ("r653sparen", go("(Box).zero"), 5),
        ("r653sparenbr", go("(Box[V = Int64]).zero"), 5),
        ("r653salias", go("CA.zero"), 5),
        ("r653spath", go("test.r653spath.Box.zero"), 5),
        // Inside the sort's own body, where it used to be typed as reflect's
        // `field_access` (`field_access.field: expected String, got Int64`).
        (
            "r653sown",
            "  sort Cnt\n    operation six() -> Int64 = 6\n    operation inner() -> Int64 = Cnt.six\n  end\n  operation go() -> Int64 = Cnt.inner()".to_string(),
            6,
        ),
    ] {
        assert_eq!(run_int(ns, "", &body), expected, "{ns}");
    }
}

/// `Box.empty` takes `V` where it is used, as `Box.empty()` does; a bracket and an alias
/// bind it. Driven both ways: an inferred `V` is accepted at two instances, a bound one is
/// refused at another.
#[test]
fn the_sorts_parameters_are_inferred_where_nothing_binds_them() {
    let read = |ty: &str, expr: &str| {
        go(&format!(
            "let b: Box[V = {ty}] = {expr}\n    match b\n      case nul -> 9\n      case mk(v) -> 8"
        ))
    };
    assert_eq!(run_int("r653sinfint", "", &read("Int64", "Box.empty")), 9);
    assert_eq!(run_int("r653sinfstr", "", &read("String", "Box.empty")), 9);
    for (ns, expr) in [
        ("r653sboundapp", "Box[V = Int64].empty()"),
        ("r653sbound", "Box[V = Int64].empty"),
        ("r653sboundalias", "CA.empty"),
        ("r653sboundlet", "t.empty"),
    ] {
        let body = read("String", expr).replace("let b", "let t = Box[V = Int64]\n    let b");
        let rendered = refusal(ns, "", &body);
        assert!(
            rendered.contains("expected Box[V = String], got Box[V = Int64]"),
            "{ns}: {rendered}"
        );
    }
}

/// A dotted chain that continues past the operation reads the call's value, as it does
/// past `Box.origin()` and past a let-bound `t.origin`.
#[test]
fn a_chain_past_the_operation_reads_its_value() {
    for (ns, expr, expected) in [
        ("r653schainapp", "Box.origin().x", 3),
        ("r653schainfield", "Box.origin.x", 3),
        ("r653schaincall", "Box.origin.sum()", 7),
        ("r653schainalias", "CA.origin.sum()", 7),
    ] {
        assert_eq!(run_int(ns, "", &go(expr)), expected, "{ns}");
    }
}

#[test]
fn a_const_value_calls_it() {
    let body = "  const c: Int64 = Box.zero\n  operation go() -> Int64 = c";
    assert_eq!(run_int("r653sconst", "", body), 5);
}

/// A spec's member is called at the bracket as the applied spelling calls it.
#[test]
fn a_spec_member_is_called_at_the_bracket() {
    for (ns, expr) in [
        ("r653sspecapp", "Additive[T = Int64].zero() + 3"),
        ("r653sspec", "Additive[T = Int64].zero + 3"),
        ("r653sspeclet", "let t = Additive[T = Int64]\n    t.zero + 3"),
    ] {
        assert_eq!(run_int(ns, "", &go(expr)), 3, "{ns}");
    }
}

/// Callers taking a function, and one taking a box at a fixed `V`, for the rows below.
const TAKERS: &str = "  operation ap(f: (x: Int64) -> Int64) -> Int64 = f(4)\n  operation aps(f: (x: String) -> String) -> Int64 = String.length(f(\"abc\"))\n  operation call0(f: () -> Int64) -> Int64 = f()\n  operation ts(b: Box[V = String]) -> Int64 = 1\n";

/// A member that takes arguments, written without parentheses, is its function value
/// where one is expected, in every spelling — as its one-segment name is — and the
/// bracket, or the alias, binds the sort's parameters in the function's type.
#[test]
fn a_member_that_takes_arguments_is_its_function_value() {
    for (ns, expr, expected) in [
        ("r653sfnwritten", "let f: (x: Int64) -> Int64 = Box.inc\n    f(4)", 5),
        ("r653sfnbracket", "let f: (x: Int64) -> Int64 = Box[V = Int64].wrap\n    f(4)", 4),
        ("r653sfnalias", "ap(CA.wrap)", 4),
        ("r653sfnpath", "ap(test.r653sfnpath.Box.inc)", 5),
        ("r653sfnlet", "let t = Box\n    ap(t.inc)", 5),
        ("r653sfnletbr", "let t = Box[V = Int64]\n    ap(t.wrap)", 4),
        ("r653sfnparen", "ap((Box).inc)", 5),
        ("r653sfnparenbr", "ap((Box[V = Int64]).wrap)", 4),
        // `V` taken where each one stands, as a call takes it.
        ("r653sfntwo", "ap(Box.wrap) + aps(Box.wrap) * 10", 34),
        // A nullary operation is the function only where its result is not.
        ("r653sfnnullary", "call0(Box.zero)", 5),
    ] {
        let body = format!("{TAKERS}{}", go(expr));
        assert_eq!(run_int(ns, "", &body), expected, "{ns}");
    }
}

/// The bracket and the alias are what the function's type is at: written at another
/// instance than the slot's, the function is refused there.
#[test]
fn the_receivers_parameters_are_the_functions() {
    for (ns, expr, said) in [
        (
            "r653sfnbadbr",
            "let f: (x: Int64) -> Int64 = Box[V = String].wrap\n    f(4)",
            "expected Int64 -> Int64, got String -> String",
        ),
        ("r653sfnbadalias", "aps(CA.wrap)", "expected String -> String, got Int64 -> Int64"),
        (
            "r653sfnbadlet",
            "let t = Box[V = Int64]\n    aps(t.wrap)",
            "expected String -> String, got Int64 -> Int64",
        ),
    ] {
        let rendered = refusal(ns, "", &format!("{TAKERS}{}", go(expr)));
        assert!(rendered.contains(said), "{ns}: {rendered}");
    }
}

/// Written with parentheses the member is the call with no arguments, an arity error, also
/// where a function is expected; and with no function expected the spelling without them
/// is refused as its one-segment name is, as an operation no slot lifts.
#[test]
fn elsewhere_it_is_refused_as_its_one_segment_name_is() {
    for (ns, expr, said) in [
        ("r653sargsapp", "ap(Box.inc())", "expected 1 argument"),
        ("r653sargsletapp", "let t = Box\n    ap(t.inc())", "expected 1 argument"),
        (
            "r653sargsnoslot",
            "let f = Box.inc\n    3",
            "this position supplies no function type to lift it against",
        ),
        (
            "r653sargsnoslotlet",
            "let t = Box\n    let f = t.inc\n    3",
            "this position supplies no function type to lift it against",
        ),
    ] {
        let rendered = refusal(ns, "", &format!("{TAKERS}{}", go(expr)));
        assert!(rendered.contains(said), "{ns}: {rendered}");
        assert!(!rendered.contains(UNRESOLVED), "{ns}: {rendered}");
    }
}

// ── a one-segment name ──────────────────────────────────────────────────────

/// The one-segment name of a parametric sort's member fixes the sort's parameters where it
/// stands, as its call does. It kept the sort's own `V`: `let b: Box[V = Int64] = empty` was
/// refused, "got Box[V = V]", and `let f: (x: Int64) -> Int64 = wrap`, "got V -> V", where
/// the same names as arguments and `empty()` loaded.
#[test]
fn a_one_segment_name_is_at_parameters_of_its_own() {
    let imports = |ns: &str| format!("  import test.{ns}.Box.{{wrap, empty}}\n{TAKERS}");
    for (ns, expr, expected) in [
        ("r653sseglet", "let b: Box[V = Int64] = empty\n    match b\n      case nul -> 9\n      case mk(v) -> v", 9),
        ("r653sseglets", "let b: Box[V = String] = empty\n    match b\n      case nul -> 9\n      case mk(v) -> 8", 9),
        ("r653ssegfn", "let f: (x: Int64) -> Int64 = wrap\n    f(4)", 4),
        ("r653ssegtwo", "let f: (x: Int64) -> Int64 = wrap\n    let h: (x: String) -> String = wrap\n    f(4) + String.length(h(\"ab\")) * 10", 24),
    ] {
        let body = format!("{}{}", imports(ns), go(expr));
        assert_eq!(run_int(ns, "", &body), expected, "{ns}");
    }
    // The instance a `let` fixes is the value's from then on.
    let rendered = refusal(
        "r653ssegfixed",
        "",
        &format!("{}{}", imports("r653ssegfixed"), go("let b: Box[V = Int64] = empty\n    ts(b)")),
    );
    assert!(rendered.contains("expected Box[V = String], got Box[V = Int64]"), "{rendered}");
    // Inside the sort the name is at a `V` of its own too, which the body's `V` fixes.
    let inside = "  sort Cell[V]\n    operation wrap(x: V) -> V = x\n    operation lifted() -> Int64 =\n      let f: (x: V) -> V = wrap\n      7\n  end\n  operation go() -> Int64 = Cell.lifted()";
    assert_eq!(run_int("r653sseginside", "", inside), 7);
}

/// An `internal` operation named from outside its sort is refused with the words the
/// applied `Vault.secret()` draws.
#[test]
fn an_internal_operation_is_refused_as_its_applied_name_is() {
    let lib = |ns: &str| {
        format!(
            "namespace lib.{ns}\n  sort Vault\n    internal operation secret() -> Int64 = 13\n  end\nend\n"
        )
    };
    for (ns, expr) in [("r653shidapp", "Vault.secret()"), ("r653shid", "Vault.secret")] {
        let rendered = refusal(
            ns,
            &lib(ns),
            &format!("  import lib.{ns}.Vault\n{}", go(expr)),
        );
        assert!(
            rendered.contains(&format!("is internal to 'lib.{ns}.Vault'")),
            "{ns}: {rendered}"
        );
        assert!(!rendered.contains(UNRESOLVED), "{ns}: {rendered}");
    }
}

// ── a rule ──────────────────────────────────────────────────────────────────

#[test]
fn a_rule_member_is_the_relation_in_every_spelling() {
    // The rows of the relation, counted: both with no column bound, one with `1` bound.
    for (ns, lets, expr, expected) in [
        ("r653srelwritten", "", "Box.rows", 2),
        ("r653srellet", "let t = Box\n    ", "t.rows", 2),
        ("r653srelletbr", "let t = Box[V = Int64]\n    ", "t.rows", 2),
        ("r653srelparen", "", "(Box).rows", 2),
        ("r653srelapplied", "", "Box.rows(1)", 1),
        ("r653srelletapplied", "let t = Box\n    ", "t.rows(1)", 1),
        ("r653srelparenapplied", "", "(Box).rows(1)", 1),
    ] {
        let body = go(&format!("{lets}{expr}.takeN(10).length()"));
        assert_eq!(run_int(ns, "", &body), expected, "{ns}");
    }
}

/// In a rule body the dot is the goal the written `Box.rows(?x)` is, and a bracket on its
/// receiver — written, or fixed by an alias — is refused as the written one is: a relation
/// named in a rule body is passed no type argument.
#[test]
fn a_rule_member_in_a_rule_body_is_the_goal() {
    assert_eq!(ints("r653srbwritten", "  rule r(?x) :- Box.rows(?x)"), [1, 2]);
    assert_eq!(ints("r653srbparen", "  rule r(?x) :- (Box).rows(?x)"), [1, 2]);
    for (ns, goal) in [
        ("r653srbbrwritten", "Box[V = Int64].rows(?x)"),
        ("r653srbbr", "(Box[V = Int64]).rows(?x)"),
        ("r653srbalias", "(CA).rows(?x)"),
    ] {
        let rendered = refusal(ns, "", &format!("  rule r(?x) :- {goal}"));
        assert!(
            rendered.contains(&format!("type bracket on `test.{ns}.Box.rows` in a rule body")),
            "{ns}: {rendered}"
        );
    }
}

/// In a rule body a dotted name through an alias is the call it names in the sort the
/// alias stands for, as `CA.zero()` and `(CA).zero` are. It bound the term
/// `field_access(CA, zero)`, and `5 = CA.zero` was refused as a walk's defect.
#[test]
fn an_alias_in_a_rule_body_is_read_as_its_sort() {
    for (ns, body) in [
        ("r653saliasapp", "  rule r(?x) :- ?x <=> CA.zero()"),
        ("r653saliasparen", "  rule r(?x) :- ?x <=> (CA).zero"),
        ("r653saliasbound", "  rule r(?x) :- ?x <=> CA.zero"),
    ] {
        assert_eq!(ints(ns, body), [5], "{ns}");
    }
    assert_eq!(ints("r653saliaseq", "  rule r(1) :- 5 = CA.zero"), [1]);
    assert_eq!(ints("r653saliasne", "  rule r(1) :- 0 = CA.zero"), Vec::<i64>::new());
}

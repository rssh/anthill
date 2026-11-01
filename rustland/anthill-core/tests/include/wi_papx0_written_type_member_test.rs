//! WI-20260824-PAPX0 — a member of a sort written after its bracket, `Box[V = Int64].V`, is
//! read as `(Box[V = Int64]).V` is: one type value, one answer in every spelling
//! (kernel-language.md §5.4).
//!
//! THE RULE. In an operation body and in a rule body the paren-less `Sort[…].m` keeps the
//! citation when `m` is a rule, an operation or a constructor; any other member the sort
//! declares — a type member, a const — is the dot `(Sort[…]).m` the converter builds beside
//! it (`Loader::citation_read_as_dot`), so a type member is read at the parameters the
//! bracket binds and a const is refused as a receiver that denotes a sort refuses it. A type
//! member reached through a pure alias, whose qualified name names nothing (`CB[Int64].V`),
//! is read so too. A clause's own term — a fact, a rule head — keeps the citation. In a
//! type, `Sort[…].Member` is the member at the bracket's parameters
//! (`Loader::bracket_member_child`, `typing::bracket_member`), and so is `Alias.Member`
//! where the alias fixes the parameters the member is defined over.
//!
//! EVERY ROW HAS ITS OWN SOURCE.
//!
//! CONTROLS — measured, each piece backed out on its own by a temporary switch in one
//! build:
//!
//!   the dot reading (`citation_read_as_dot` answering the citation always) — FAIL:
//!     a_type_parameter_after_a_bracket_is_its_binding
//!     a_member_over_the_parameters_after_a_bracket_is_its_definition_there
//!     a_member_through_an_applied_alias_after_a_bracket
//!     a_const_after_a_bracket_is_refused_as_through_the_dot
//!     wi_5g28a_paren_less_citation_test::a_nested_sort_after_the_bracket_is_its_member
//!   its arm for a pure alias (answering no) — FAIL:
//!     a_member_through_an_applied_alias_after_a_bracket
//!   that arm reading only an alias, not the sort the name writes — FAIL:
//!     an_internal_member_after_a_bracket_is_hidden_as_through_the_dot
//!   the operation's equation term keeping the citation — FAIL:
//!     an_internal_member_after_a_bracket_is_hidden_as_through_the_dot (a second error)
//!   the walk it is read in (the clause term walk reading the dot as well) — FAIL:
//!     a_clause_term_keeps_the_citation
//!   the type position's reading (`bracket_member_child` lowering the written
//!   `Sort.Member`) — FAIL:
//!     a_bracketed_member_is_a_type
//!     a_bracketed_member_bounds_a_rule_variable
//!     an_alias_defined_by_a_bracketed_member_in_either_order
//!   a refused member standing as the written `Sort.Member` rather than a fresh variable
//!   — FAIL:
//!     a_bracketed_member_is_a_type (a second error)
//!   an alias's member over the parameters it fixes, in a type (`alias_type_member`'s new
//!   arm skipped) — FAIL:
//!     an_alias_member_over_its_fixed_parameters_is_a_type
//!   the member named for the order aliases are declared in (`collect_type_expr_heads`
//!   leaving the member out) — FAIL:
//!     an_alias_defined_by_a_bracketed_member_in_either_order (the alias written first)
//!   the constructor looked up by its written name (by short name instead) — FAIL:
//!     a_constructor_is_reached_by_its_written_name
//!   the const's advice — FAIL:
//!     a_const_after_a_bracket_is_refused_as_through_the_dot
//!
//!   Without the grammar's `type_member` node every type-position row is a syntax error.
//!
//!   PASS UNDER EVERY BACK-OUT, by design: the parenthesized and let-bound twins each row
//!   compares with, and the constructor control `(Box[]).mk(v: 4)`; and
//!   `wi_1y96b_eponymous_type_receiver_test`, which pins a reading this did not change.

use anthill_core::eval::Value;

use crate::common::{interp_for, load_errors_of, load_kb_with, print_type, query_unary};

/// The sorts every row is about, indented for a namespace body.
const SORTS: &str = r#"
  sort Box[V]
    entity mk(v: V)
    operation tag() -> Int64 = 7
  end
  sort Q[A]
    sort L = List[T = A]
    sort K = Int64
  end
  sort Pr[A, B]
    sort LB = List[T = B]
  end
  sort Ou[T]
    const KK: Int64 = 4
  end
  sort Ep
    entity Ep(name: String)
    operation em() -> Int64 = 8
  end
  sort CB = Box
  sort CQ = Q[A = Int64]
"#;

fn source(ns: &str, body: &str) -> String {
    format!(
        "namespace test.{ns}\n  import anthill.prelude.{{Type, Bool, String, Int64, List, PartialEq}}\n{SORTS}\n{body}\nend\n"
    )
}

/// Load, call `test.<ns>.go()`, and hand back its value.
fn run(ns: &str, body: &str) -> Value {
    let mut interp = interp_for(&source(ns, body));
    interp
        .call(&format!("test.{ns}.go"), &[])
        .unwrap_or_else(|e| panic!("{ns}: {e:?}"))
}

fn is_true(ns: &str, body: &str) -> bool {
    match run(ns, body) {
        Value::Bool(b) => b,
        other => panic!("{ns}: expected a Bool, got {other:?}"),
    }
}

fn int(ns: &str, body: &str) -> i64 {
    match run(ns, body) {
        Value::Int(n) => n,
        other => panic!("{ns}: expected an Int64, got {other:?}"),
    }
}

/// Resolve `test.<ns>.r(?x)` and print each answer as a type.
fn types(ns: &str, body: &str) -> Vec<String> {
    let mut kb = load_kb_with(&source(ns, body));
    query_unary(&mut kb, &format!("test.{ns}.r"))
        .into_iter()
        .map(|(v, definite)| {
            assert!(definite, "{ns}: a conditional answer");
            print_type(&kb, &v)
        })
        .collect()
}

/// The refusals of a source that must not load, rendered.
fn refusal(ns: &str, body: &str) -> String {
    let errs = load_errors_of(&source(ns, body));
    assert!(!errs.is_empty(), "{ns}: must be refused, and loaded clean");
    format!("{errs:?}")
}

fn eq(expr: &str, ty: &str) -> String {
    format!("  operation go() -> Bool = PartialEq.eq({expr}, {ty})")
}

fn bound(expr: &str) -> String {
    format!("  rule r(?x) :- ?x <=> {expr}")
}

// ── values ─────────────────────────────────────────────────────────────────

/// Before this the written spelling was refused in both bodies — "`Box[…].V` names neither
/// a rule nor an operation … drop it (`Box.V`)", and in a rule body "`V(…)` is an
/// application" — where the parenthesized one answered `Int64`.
#[test]
fn a_type_parameter_after_a_bracket_is_its_binding() {
    assert!(is_true("papx0wm1", &eq("Box[V = Int64].V", "Int64")));
    assert!(is_true("papx0wm1p", &eq("(Box[V = Int64]).V", "Int64")));
    assert!(is_true("papx0wm1n", &eq("Box[Int64].V", "Int64")));
    assert!(is_true(
        "papx0wm1i",
        "  operation idt(t: Type) -> Type = t\n  operation go() -> Bool = PartialEq.eq(idt(Box[V = Int64].V), Int64)"
    ));
    assert_eq!(types("papx0wm1r", &bound("Box[V = Int64].V")), ["Int64"]);
    assert_eq!(types("papx0wm1rp", &bound("(Box[V = Int64]).V")), ["Int64"]);
}

#[test]
fn a_member_over_the_parameters_after_a_bracket_is_its_definition_there() {
    assert!(is_true("papx0wm2", &eq("Q[A = Int64].L", "List[T = Int64]")));
    assert!(is_true("papx0wm2p", &eq("(Q[A = Int64]).L", "List[T = Int64]")));
    assert!(is_true("papx0wm2k", &eq("Q[A = Int64].K", "Int64")));
    assert_eq!(types("papx0wm2r", &bound("Q[A = Int64].L")), ["List[T = Int64]"]);
}

/// `CB.V` names nothing — the parameter is `Box`'s — so the written spelling was the
/// typer's unknown functor while the parenthesized one answered.
#[test]
fn a_member_through_an_applied_alias_after_a_bracket() {
    assert!(is_true("papx0wm3", &eq("CB[Int64].V", "Int64")));
    assert!(is_true("papx0wm3p", &eq("(CB[Int64]).V", "Int64")));
}

/// A const reads no bracket. The written spelling drew two errors in an operation body
/// (the refusal and the typer's unknown functor) and in a rule body bound the data term
/// `Ou[T = Int64].KK()`; it is refused now as the parenthesized one is.
#[test]
fn a_const_after_a_bracket_is_refused_as_through_the_dot() {
    for (ns, body) in [
        ("papx0wm4", "  operation go() -> Int64 = Ou[T = Int64].KK".to_string()),
        ("papx0wm4p", "  operation go() -> Int64 = (Ou[T = Int64]).KK".to_string()),
        ("papx0wm4r", bound("Ou[T = Int64].KK")),
        ("papx0wm4rp", bound("(Ou[T = Int64]).KK")),
    ] {
        let said = refusal(ns, &body);
        for token in [
            "`KK` is declared in `Ou` and is none of them",
            &format!("a const is read by its name, `test.{ns}.Ou.KK`"),
        ] {
            assert!(said.contains(token), "{ns}: `{token}` not in {said}");
        }
        assert!(!said.contains("unknown functor"), "{ns}: {said}");
    }
    assert_eq!(int("papx0wm4b", "  operation go() -> Int64 = Ou.KK"), 4);
}

/// A fact's and a rule head's own term keep the citation, refused as before; the dot is
/// read in the two bodies only.
#[test]
fn a_clause_term_keeps_the_citation() {
    for (ns, body) in [
        ("papx0wm5", "  fact holds(Box[V = Int64].V)"),
        ("papx0wm5h", "  rule hd(Box[V = Int64].V) :- true"),
    ] {
        let said = refusal(ns, body);
        assert!(said.contains("`V(…)` is an application"), "{ns}: {said}");
    }
}

/// An `internal` member is hidden from another namespace through either spelling, by the
/// one refusal: the written one was the typer's unknown functor, since its qualified name
/// resolves to nothing from there.
#[test]
fn an_internal_member_after_a_bracket_is_hidden_as_through_the_dot() {
    let said = |ns: &str, expr: &str| {
        let errs = load_errors_of(&format!(
            "namespace lib.{ns}\n  import anthill.prelude.Int64\n  sort Hid[V]\n    entity hid(v: V)\n    internal sort Secret = Int64\n  end\nend\nnamespace test.{ns}\n  import anthill.prelude.{{Type, Int64, Bool, PartialEq}}\n  operation go() -> Bool = PartialEq.eq({}, Int64)\nend\n",
            expr.replace("NS", ns)
        ));
        assert_eq!(errs.len(), 1, "{ns}: {errs:?}");
        errs[0].clone()
    };
    for (ns, expr) in [("papx0wm6", "lib.NS.Hid[V = Int64].Secret"), ("papx0wm6p", "(lib.NS.Hid[V = Int64]).Secret")] {
        let e = said(ns, expr);
        assert!(e.contains(&format!("'Secret' is internal to 'lib.{ns}.Hid'")), "{ns}: {e}");
    }
}

// ── types ──────────────────────────────────────────────────────────────────

#[test]
fn a_bracketed_member_is_a_type() {
    assert_eq!(
        int("papx0wt1", "  operation go() -> Int64 =\n    let y: Box[V = Int64].V = 5\n    y"),
        5
    );
    assert_eq!(
        int("papx0wt1n", "  operation go() -> Int64 =\n    let y: Box[Int64].V = 6\n    y"),
        6
    );
    assert_eq!(
        int(
            "papx0wt1p",
            "  operation f(x: Q[A = Int64].L) -> Box[V = Int64].V = 2\n  operation go() -> Int64 = f([1])"
        ),
        2
    );
    let said = refusal(
        "papx0wt1s",
        "  operation go() -> Int64 =\n    let y: Box[V = Int64].V = \"s\"\n    1",
    );
    assert!(said.contains("expected Int64, got String"), "{said}");
    let said = refusal(
        "papx0wt1l",
        "  operation go() -> Int64 =\n    let y: Q[A = Int64].L = [\"s\"]\n    1",
    );
    assert!(said.contains("expected Int64, got String"), "{said}");
    // A member defined over a parameter the bracket leaves open is no type, and that is
    // the one error the type draws.
    for (ns, ty, name) in [("papx0wt1o", "Pr[A = Int64].LB", "Pr[…].LB"), ("papx0wt1oa", "CPr.LB", "CPr.LB")] {
        let errs = load_errors_of(&source(
            ns,
            &format!("  sort CPr = Pr[A = Int64]\n  operation go() -> Int64 =\n    let y: {ty} = [1]\n    1"),
        ));
        assert_eq!(errs.len(), 1, "{ns}: {errs:?}");
        assert!(
            errs[0].contains(&format!("`{name}` names no type here"))
                && errs[0].contains("defined over a parameter of `Pr` the receiver leaves open"),
            "{ns}: {errs:?}"
        );
    }
}

/// A rule head's bound written so is the member's type: the variable is bound by it.
#[test]
fn a_bracketed_member_bounds_a_rule_variable() {
    let mut kb = load_kb_with(&source("papx0wt4", "  rule r(?x: Box[V = Int64].V) :- ?x <=> 3"));
    let answers: Vec<Value> =
        query_unary(&mut kb, "test.papx0wt4.r").into_iter().map(|(v, _)| v).collect();
    assert!(matches!(answers.as_slice(), [Value::Int(3)]), "{answers:?}");
    let said = refusal("papx0wt4s", "  rule r(?x: Box[V = Int64].V) :- ?x <=> \"s\"");
    assert!(said.contains("expected Int64, got String"), "{said}");
}

/// `CQ.L` was the rigid `L` in a type — "expected L, got List[T = Int64]" for `[1]` —
/// where `let t = Q[A = Int64]` then `t.L` was `List[T = Int64]`.
#[test]
fn an_alias_member_over_its_fixed_parameters_is_a_type() {
    assert_eq!(
        int("papx0wt2", "  operation go() -> Int64 =\n    let y: CQ.L = [1]\n    1"),
        1
    );
    let said = refusal(
        "papx0wt2s",
        "  operation go() -> Int64 =\n    let y: CQ.L = [\"s\"]\n    1",
    );
    assert!(said.contains("expected Int64, got String"), "{said}");
}

#[test]
fn an_alias_defined_by_a_bracketed_member_in_either_order() {
    let use_it = "  operation go() -> Int64 =\n    let y: CQL = [3]\n    1";
    assert_eq!(int("papx0wt3", &format!("  sort CQL = Q[A = Int64].L\n{use_it}")), 1);
    // Written before `Q`: the alias waits for the member it names.
    let first = format!(
        "namespace test.papx0wt3f\n  import anthill.prelude.{{Int64, List}}\n  sort CQL = Q[A = Int64].L\n{use_it}\n  sort Q[A]\n    sort L = List[T = A]\n  end\nend\n"
    );
    let mut interp = interp_for(&first);
    match interp.call("test.papx0wt3f.go", &[]) {
        Ok(Value::Int(1)) => {}
        other => panic!("the alias written first: {other:?}"),
    }
    let said = refusal(
        "papx0wt3s",
        "  sort CQL = Q[A = Int64].L\n  operation go() -> Int64 =\n    let y: CQL = [\"s\"]\n    1",
    );
    assert!(said.contains("expected Int64, got String"), "{said}");
}

// ── constructors ───────────────────────────────────────────────────────────

/// `Ep`'s constructor is the sort's own name, which `Ep.Ep` does not name: the written
/// `Ep[].Ep(name: "x")` names nothing, and `(Ep[]).Ep(name: "x")` constructed. Both are
/// refused now.
#[test]
fn a_constructor_is_reached_by_its_written_name() {
    let said = refusal("papx0wc1", "  operation go() -> Ep = (Ep[]).Ep(name: \"x\")");
    assert!(said.contains("no such member"), "{said}");
    let said = refusal("papx0wc1w", "  operation go() -> Ep = Ep[].Ep(name: \"x\")");
    assert!(said.contains("unknown functor"), "{said}");
    let built = run(
        "papx0wc1c",
        "  operation go() -> Int64 =\n    match (Box[]).mk(v: 4)\n      case mk(v) -> v",
    );
    assert!(matches!(built, Value::Int(4)), "{built:?}");
}

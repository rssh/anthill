//! WI-20261124-YFD7F, stage S0 — a `<=>` or `===` whose two sides the clause types
//! differently is refused at load, as `=` and `!=` already are.
//!
//! WHY S0 COMES FIRST. YFD7F's approach (a) lets a call pass `__trusted` for an argument the
//! typer has established, and the callee then skips its check. That is sound only if a
//! variable the typer has at `T` never holds anything else, and one shape broke it:
//! `rule p(?l: List[T = Int64]) :- ?l <=> cons(head: ?, tail: ?t), ?t <=> "x"` LOADED CLEAN.
//! The typer knew `?t: List[T = Int64]` (passing `?t` to a `String` column is refused), but
//! `<=>` and `===` are resolver builtins, and the call check that types `=` and `!=` (a
//! spec operation) skipped them (`rule_dispatch::call_dispatch_shape`). Their sides were put
//! at one fresh `T` by their kernel signatures (`operation unify[T](a: T, b: T)`), so the
//! disagreement was "the call's fault" (`rule_constraints::constrain_vid`) — and no call
//! check ran to report it.
//!
//! MEASURED before the change (release CLI, 2026-11-27): `=` and `!=` at a mistyped side —
//! refused; `?t <=> ?s` against a `String` column — refused, through the bound; `?t <=> "x"`
//! in either order, and `?t === "x"` — loaded clean. A monomorphic list sort loaded clean
//! too, and so did `?h <=> "x"` on an `Int64` field: the gap is not about type parameters.
//!
//! THE CHECK (`rule_constraints::settle_equality_sides`): a committed `<=>` / `===` / `!==`
//! goal of a relational clause is set aside by the walk and its two sides compared once every
//! other position is read. Written FIRST (`?t <=> "x", ?l <=> cons(head: ?, tail: ?t)`), the
//! literal's sort reaches `?t` as a placeholder before the list field does, and the field — a
//! placeholder too — is dropped; the drop is recorded (`ClauseConstraints::placeholder_clashes`)
//! and read by the check, so the order of the text does not decide. A side whose variable a `|`
//! branch, a negation or a quantifier's body also types is not compared
//! (`ClauseConstraints::uncommitted_vars`): the walk records a branch's positions in the clause's
//! one map.
//!
//! BACK-OUTS, each RUN (2026-11-27):
//!  * [C] no mismatch ever reported: the six `*_is_refused` rows fail, each loading clean.
//!  * [P] the dropped clash not recorded: the two `*_written_first_is_refused` rows fail.
//!  * [U] a side typed by a branch compared anyway: `a_branch_clash_does_not_refuse_a_committed_unify`
//!    fails — refused, `expected List[T = Int64], got Int64`, a clause that answers.
//! Passing under all three BY DESIGN: the `=` / `!=` refusals (already there), the well-typed
//! controls (load and answer the same), and the `|` branch row.

use crate::common::{assert_refused_naming, load_errors_of, load_kb_with, shown_rows};

const NS: &str = "wiyfd7f.unify";

fn program(decls: &str) -> String {
    format!(
        r#"
namespace {NS}
  import anthill.prelude.{{Int64, List, String}}
  import anthill.prelude.List.{{cons, nil}}

  sort IL
    entity inil
    entity icons(h: Int64, t: IL)
  end

{decls}
end
"#
    )
}

/// The ticket's shape: the tail of a `List[T = Int64]` unified with a `String`.
#[test]
fn a_tail_unified_with_a_string_is_refused() {
    let errs = load_errors_of(&program(
        "  rule p(?l: List[T = Int64]) :- ?l <=> cons(head: ?, tail: ?t), ?t <=> \"x\"",
    ));
    assert_refused_naming(
        &errs,
        &["unify", "expected List[T = Int64]", "got String"],
        "`?t <=> \"x\"` at the tail of a `List[T = Int64]`",
    );
}

/// The same with the `<=>` written first: what decides is the clause's typing, not the order.
#[test]
fn a_mistyped_unify_written_first_is_refused() {
    let errs = load_errors_of(&program(
        "  rule p(?l: List[T = Int64]) :- ?t <=> \"x\", ?l <=> cons(head: ?, tail: ?t)",
    ));
    assert_refused_naming(
        &errs,
        &["unify", "expected List[T = Int64]", "got String"],
        "`?t <=> \"x\"` written before the destructuring",
    );
}

/// `===` tests where `<=>` binds; a mistyped side is the same mistake.
#[test]
fn a_mistyped_struct_eq_is_refused() {
    let errs = load_errors_of(&program(
        "  rule p(?l: List[T = Int64]) :- ?l <=> cons(head: ?, tail: ?t), ?t === \"x\"",
    ));
    assert_refused_naming(
        &errs,
        &["struct_eq", "expected List[T = Int64]", "got String"],
        "`?t === \"x\"` at the tail of a `List[T = Int64]`",
    );
}

/// `!==` is `===`'s negation, and its sides are held to one type the same way.
#[test]
fn a_mistyped_struct_neq_is_refused() {
    let errs = load_errors_of(&program(
        "  rule p(?l: List[T = Int64]) :- ?l <=> cons(head: ?, tail: ?t), ?t !== \"x\"",
    ));
    assert_refused_naming(
        &errs,
        &["struct_neq", "expected List[T = Int64]", "got String"],
        "`?t !== \"x\"` at the tail of a `List[T = Int64]`",
    );
}

/// No type parameter involved: an `Int64` field unified with a `String`.
#[test]
fn a_monomorphic_field_unified_with_a_string_is_refused() {
    let errs = load_errors_of(&program(
        "  rule p(?l: IL) :- ?l <=> icons(h: ?h, t: ?), ?h <=> \"x\"",
    ));
    assert_refused_naming(
        &errs,
        &["unify", "expected Int64", "got String"],
        "`?h <=> \"x\"` at an `Int64` field",
    );
}

/// CONTROL, refused before and after: `=` and `!=` were always checked, as a spec operation's
/// call is.
#[test]
fn eq_and_neq_at_a_mistyped_side_stay_refused() {
    for (connective, name) in [("=", "eq"), ("!=", "neq")] {
        let errs = load_errors_of(&program(&format!(
            "  rule p(?l: List[T = Int64]) :- ?l <=> cons(head: ?, tail: ?t), ?t {connective} \"x\""
        )));
        assert_refused_naming(
            &errs,
            &[name, "expected List[T = Int64]", "got String"],
            &format!("`?t {connective} \"x\"`"),
        );
    }
}

/// CONTROL, answering before and after: well-typed `<=>` and `===` of every shape a body
/// writes — a destructuring, a binding to a literal of the right type, a variable nothing
/// types, a construction at a type parameter, an anonymous field.
#[test]
fn well_typed_unifies_load_and_answer() {
    let mut kb = load_kb_with(&program(
        r#"  rule tailOf(?l: List[T = Int64], ?t) :- ?l <=> cons(head: ?, tail: ?t)
  rule tail12(?t) :- tailOf([1, 2], ?t)
  rule headOf(?r) :- ?x <=> [7, 8], ?x <=> cons(head: ?h, tail: ?), ?r <=> ?h
  rule anyv(?v) :- ?v <=> "x"
  rule same(?r) :- ?a <=> 3, ?a === 3, ?r <=> ?a
  rule isNil(?r) :- ?l <=> nil(), ?l <=> [], ?r <=> 1

  sort Wrap[T]
    entity wrap(v: T)
    rule unwrap(?w: Wrap[T = T], ?v) :- ?w <=> wrap(v: ?v)
  end
  rule unwrapped(?v) :- Wrap.unwrap(wrap(v: 3), ?v)"#,
    ));
    for (relation, want) in [
        ("tail12", "[2]"),
        ("headOf", "7"),
        ("anyv", "\"x\""),
        ("same", "3"),
        ("isNil", "1"),
        ("unwrapped", "3"),
    ] {
        assert_eq!(
            shown_rows(&mut kb, &format!("{NS}.{relation}")),
            vec![(want.to_string(), true)],
            "`{relation}`"
        );
    }
}

/// CONTROL, the same before and after: a `|` types a variable for each branch alone (WI-C6VN0),
/// so a branch that binds `?m` to a `String` beside one that binds it to a tail is not a
/// mistyped `<=>`, and is not refused. Its answer is right either way: the callee's typed
/// column checks the `String` and refuses it. YFD7F's evidence rule passes no `__trusted` for
/// `?m` after the `|`, since one branch did not establish a list.
#[test]
fn a_branch_typing_a_variable_differently_is_not_refused() {
    let mut kb = load_kb_with(&program(
        r#"  rule memL(?x, ?l: List[T = Int64]) :- (?l <=> cons(head: ?x, tail: ?)) | (?l <=> cons(head: ?, tail: ?t), memL(?x, ?t))
  rule p(?l: List[T = Int64]) :- ((?l <=> cons(head: ?, tail: ?m)) | (?m <=> "x")), memL(2, ?m)
  rule q(?r) :- p([1, 2]), ?r <=> 1"#,
    ));
    assert_eq!(shown_rows(&mut kb, &format!("{NS}.q")), vec![("1".to_string(), true)]);
}

/// `/code-review` finding 1 — a clash inside a `|` branch must not refuse a committed `<=>`.
#[test]
fn a_branch_clash_does_not_refuse_a_committed_unify() {
    let mut kb = load_kb_with(&program(
        r#"  rule p(?l: List[T = Int64], ?r) :- ((?l <=> cons(head: ?, tail: ?m)) | (?m <=> 3)), ?m <=> 3, ?r <=> 1
  rule q(?r) :- p(nil(), ?r)"#,
    ));
    assert_eq!(shown_rows(&mut kb, &format!("{NS}.q")), vec![("1".to_string(), true)]);
}

/// `/code-review` finding 2 — a variable against a variable, written before the destructuring.
#[test]
fn a_mistyped_var_unify_written_first_is_refused() {
    let errs = load_errors_of(&program(
        "  rule p(?l: List[T = Int64]) :- ?t <=> ?s, ?s <=> \"x\", ?l <=> cons(head: ?, tail: ?t)",
    ));
    assert_refused_naming(&errs, &["unify", "List[T = Int64]", "String"], "`?t <=> ?s` first");
}

//! WI-20260825-P9Y67 — A MINTED BOOLEAN CONNECTIVE NAMES ITS TARGET OUTRIGHT.
//!
//! `|` / `&` / `!` minted the SHORT functors `or` / `and` / `not`, resolved down the
//! ordinary name ladder whose lowest rung is the implicit tier — so a same-spelled
//! declaration in the enclosing namespace CAPTURED the operator. This is
//! WI-20260825-KD9SW's move for the three operators that ticket deliberately left out,
//! and the reason it could leave them out was wrong: it read position-direction as a
//! reason the operator could not carry an address, when the position routing runs on the
//! RESOLVED SYMBOL and an address at the goal spelling preserves both readings.
//!
//! ## Why the address is `anthill.kernel.*` and no library move had to land first
//!
//! `+` needed WI-20260825-1WBZT to split `Numeric` into syntax categories before KD9SW
//! could address it, because the address names where the operation is DECLARED and
//! `Numeric.add` was a bundle a `Money` carrier could not claim honestly. These three
//! need no such split: `|` IS disjunction and disjunction is `push_choice`. The value
//! reading survives because `Loader::redirect_op_body_boolean` maps `kernel.X` to
//! `Bool.X` whenever `in_op_body_value`, downstream of resolution — see
//! `parse::pratt::CONNECTIVE_FUNCTORS` for the full argument, including why this is not
//! the attempt withdrawn from WI-20260824-BFB9A.
//!
//! ## WHAT FAILS WHEN THIS IS BACKED OUT
//!
//! Put the short functors back in `parse::pratt`'s tables (`functor: "or"`, …):
//!   * [`a_shadow_no_longer_captures_a_goal_position_or`] fails, and it is THE row — the
//!     shadowed arm answers `?x = ?_` as a CONDITIONAL with the residual
//!     `eq(or(p(?_), p(99)), true)` instead of `?x = 1` definite. A disjunction stops
//!     being a disjunction: the goal is re-read as a boolean VALUE expression and `?x`
//!     never binds.
//!   * [`a_shadow_no_longer_captures_a_value_position_connective`] fails on all three
//!     arms — each inverts against its control.
//!   * [`a_written_bare_connective_still_resolves_by_scope`] fails on its `viaOperator`
//!     half and passes either way on its `viaBareCall` half — SPLIT DELIBERATELY, and
//!     the doc here said "passes either way" until the back-out was actually run. Only
//!     the second half is the design-invariant one (a written name is an ordinary name);
//!     the first is one more capture row, because with the short spelling the same local
//!     `or` captures the operator too. The row's value is that it holds both against ONE
//!     declaration, which is what makes the two spellings' disagreement attributable.
//!   * [`the_kernel_conjunction_is_reachable_by_qualified_name`] passes either way for
//!     the pratt half and fails when `register_stdlib_scopes`' `and` pre-declaration is
//!     removed — a separate defect this ticket found, see its own doc.

use crate::common::{interp_for, query_unary, try_load_kb_with};
use anthill_core::eval::Value;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::{Literal, Term};

/// The sole DEFINITE integer `qn` answers, or a panic naming what came back instead.
///
/// Reads the answer as a TERM: a rule answers by unification, so the binding is the
/// literal term the goal carried and the eval-side `Int` carrier never appears here.
/// The `true` in the pattern is load-bearing — the defect this file pins answered ONE
/// solution that was CONDITIONAL, so a count alone would have called it success.
fn sole_definite_int(kb: &mut KnowledgeBase, qn: &str) -> i64 {
    let answers = query_unary(kb, qn);
    // BOTH CARRIERS, deliberately: a rule answers by unification and the binding comes
    // back as the literal TERM the goal carried, while a `<=>` over a hash-consed
    // literal can hand back the occurrence carrier instead. Same integer, two
    // representations, and a helper that knows only one silently turns a passing row
    // into a panic about the wrong thing (measured — it did).
    match answers.as_slice() {
        [(Value::Term { id, .. }, true)] => match kb.get_term(*id) {
            Term::Const(Literal::Int(i)) => *i,
            other => panic!("`{qn}` must answer an Int literal, got {other:?}"),
        },
        [(Value::Node(occ), true)] => match occ.as_expr() {
            Some(anthill_core::kb::node_occurrence::Expr::Const(Literal::Int(i))) => *i,
            other => panic!("`{qn}` must answer an Int literal, got {other:?}"),
        },
        other => panic!("`{qn}` must answer exactly one DEFINITE term, got {other:?}"),
    }
}

/// `fact p(1)` and a rule whose body is a minted disjunction, with `SHADOW` spliced in.
fn goal_src(shadow: &str) -> String {
    format!(
        r#"
namespace p9y67.goal
  import anthill.prelude.{{Int64, Bool}}
{shadow}
  fact p(1)
  rule q(?x) :- p(?x) | p(99)
end
"#
    )
}

/// An operation body computing `EXPR` and reporting it as 1 / 0, with `SHADOW` spliced
/// in. Driven through a VALUE — "it loads" would keep passing through every capture this
/// ticket is about.
fn value_src(shadow: &str, expr: &str) -> String {
    format!(
        r#"
namespace p9y67.val
  import anthill.prelude.{{Int64, Bool}}
{shadow}
  operation probe() -> Int64 =
    let b = {expr}
    if b then 1 else 0
end
"#
    )
}

fn drive(src: &str, qn: &str) -> String {
    let mut interp = interp_for(src);
    let got = interp
        .call(qn, &[])
        .unwrap_or_else(|e| panic!("{qn} must evaluate: {e:?}"));
    format!("{got:?}")
}

/// THE HEADLINE, and the row that separates this defect from an ordinary wrong answer.
///
/// A free-standing `operation or` used to change what every rule in reach MEANS, not
/// just what a call returns. Both halves are asserted because only the pair distinguishes
/// the defect from a missing answer: the binding (`?x = 1`, so the disjunction still
/// bound through its branches) AND definiteness (the shadowed arm used to answer one
/// FLOUNDERED solution, which `.len()` alone would have counted as success — see the
/// residual named in this file's back-out note).
#[test]
fn a_shadow_no_longer_captures_a_goal_position_or() {
    for (label, shadow) in [
        ("control", ""),
        (
            "shadowed",
            "  operation or(a: Bool, b: Bool) -> Bool = false",
        ),
    ] {
        let src = goal_src(shadow);
        let mut kb = try_load_kb_with(&src)
            .unwrap_or_else(|e| panic!("{label}: fixture must load: {e:?}"));
        assert_eq!(
            sole_definite_int(&mut kb, "p9y67.goal.q"),
            1,
            "{label}: `p(?x) | p(99)` must bind `?x` through its first branch, \
             DEFINITELY — the shadowed arm used to answer `?x = ?_` as a conditional \
             with the residual `eq(or(p(?_), p(99)), true)`"
        );
    }
}

/// The three VALUE rows, each against its own control. Every one used to INVERT: the
/// shadow answered 1 where the connective answers 0, and vice versa.
///
/// The shadow bodies are chosen to be the OPPOSITE of the connective's answer at the
/// operands used, which is what makes each arm a separating row rather than a
/// coincidence — a shadow returning the same value as the real connective would pass
/// with or without the fix.
#[test]
fn a_shadow_no_longer_captures_a_value_position_connective() {
    for (expr, shadow, expect) in [
        (
            "false & false",
            "  operation and(a: Bool, b: Bool) -> Bool = true",
            "Int(0)",
        ),
        (
            "true | true",
            "  operation or(a: Bool, b: Bool) -> Bool = false",
            "Int(1)",
        ),
        ("!true", "  operation not(a: Bool) -> Bool = true", "Int(0)"),
    ] {
        assert_eq!(
            drive(&value_src("", expr), "p9y67.val.probe"),
            expect,
            "control: `{expr}` with no shadow"
        );
        assert_eq!(
            drive(&value_src(shadow, expr), "p9y67.val.probe"),
            expect,
            "`{expr}` must mean the connective even beside `{}`",
            shadow.trim()
        );
    }
}

/// THE MIGRATION BOUNDARY: one declaration, two spellings, two answers.
///
/// An operator names its operation absolutely; a WRITTEN bare name is an ordinary name
/// and still resolves by scope. So the two spellings disagree, and that is the language
/// rule (§5.5) rather than a defect — this row is what says the change did not quietly
/// reach written code.
///
/// WHICH HALF MEASURES WHAT, since the two are not the same kind of claim and an earlier
/// draft of this doc called the whole row invariant: `viaBareCall` passes with or without
/// the address and is the design-invariant half; `viaOperator` FAILS on back-out (it
/// answers 0, captured) and is a capture row like the two above it. Holding both against
/// a single `operation or` is the point — it is what makes the disagreement attributable
/// to the SPELLING rather than to two different fixtures.
///
/// It also states the one place these three part company with KD9SW's twelve: they KEEP
/// their `PRELUDE_QUALIFIED` entries, so a bare `not(...)` with no local declaration and
/// no import still reaches the kernel primitive. Retiring that tier is a migration, not
/// this repair.
#[test]
fn a_written_bare_connective_still_resolves_by_scope() {
    let src = r#"
namespace p9y67.written
  import anthill.prelude.{Int64, Bool}
  operation or(a: Bool, b: Bool) -> Bool = false
  operation viaOperator() -> Int64 =
    let b = true | true
    if b then 1 else 0
  operation viaBareCall() -> Int64 =
    let b = or(true, true)
    if b then 1 else 0
end
"#;
    assert_eq!(
        drive(src, "p9y67.written.viaOperator"),
        "Int(1)",
        "`true | true` names `..anthill.kernel.or` outright"
    );
    assert_eq!(
        drive(src, "p9y67.written.viaBareCall"),
        "Int(0)",
        "…while the WRITTEN name means the local declaration, which is why the two \
         spellings are not interchangeable"
    );
}

/// A DATA SLOT KEEPS ITS SPELLING, SO A RULE BODY STILL MATCHES A FACT — the row that
/// pins a regression this ticket SHIPPED AND BACKED OUT, and it is here because the
/// mistake is an inviting one.
///
/// §6.6 says a goal's ARGUMENT is a value expression, so applying the op-body redirect
/// (`kernel.X` → `Bool.X`) to a rule body's non-goal slots looks like the missing mirror
/// of `route_body_goal_boolean`. It is not. A fact HEAD, a rule head and a query pattern
/// all build through `convert_term` and are NOT redirected, so the rewrite made a rule
/// body spell the same source text differently from the fact it is meant to match — and
/// a term's spelling is its identity. Exit 0, no diagnostic: the same silent
/// unqueryability the withdrawn `reclaim_minted_operator` produced
/// (WI-20260824-BFB9A), reached from the other side. Found by `/code-review`.
///
/// THE ENTITY ROW IS THE CONTROL and passes either way BY DESIGN: `boxed(v: 1)` is not a
/// connective, so no redirect could ever reach it. It is what says the two boolean rows
/// measure the REDIRECT rather than a broken fixture — with the regression in place it
/// stayed green while both boolean rows went to zero.
///
/// WHERE THE POSITION KNOWLEDGE GOES INSTEAD: a consumer that knows it is reading a
/// condition. `anthill-smt-gen`'s `translate_condition` is only ever called on one, so it
/// lowers BOTH spellings (`wi680_ite_lowering_test`); the loader cannot, because it
/// cannot tell a condition from a reified goal being STORED.
#[test]
fn a_data_slot_keeps_its_spelling_so_a_body_matches_a_fact() {
    let mut kb = try_load_kb_with(
        r#"
namespace p9y67.asym
  import anthill.prelude.{Int64}
  import anthill.kernel.{not, or}
  sort Box
    entity boxed(v: Int64)
  end
  fact wrap(boxed(v: 1))
  fact holdsN(not(true))
  fact holdsO(or(true, false))
  rule viaEntity(?x) :- wrap(boxed(v: 1)), ?x <=> 1
  rule viaNot(?x)    :- holdsN(not(true)), ?x <=> 1
  rule viaOr(?x)     :- holdsO(or(true, false)), ?x <=> 1
end
"#,
    )
    .unwrap_or_else(|e| panic!("fixture must load: {e:?}"));

    assert_eq!(
        sole_definite_int(&mut kb, "p9y67.asym.viaEntity"),
        1,
        "the CONTROL: an entity argument matches, and passes either way by design"
    );
    assert_eq!(
        sole_definite_int(&mut kb, "p9y67.asym.viaNot"),
        1,
        "a body goal's DATA slot holding `not(true)` must still match the fact holding \
         the identical term — this answered NOTHING while the redirect was in place"
    );
    assert_eq!(
        sole_definite_int(&mut kb, "p9y67.asym.viaOr"),
        1,
        "…and the same for `or(true, false)`, which is the exact shape BFB9A's \
         withdrawn attempt made unqueryable from the other direction"
    );
}

/// A DEFECT THIS TICKET FOUND RATHER THAN INTRODUCED, pinned where it was found.
///
/// WI-20260822-J38JE added `anthill.kernel.and` and a `POSITION_DIRECTED_BOOLEANS` row
/// crediting it with the goal reading of `&`. But `kernel.anthill` declares `and` only as
/// a RULE HEAD, and a rule head does not register a qualified name — so
/// `goal_position_boolean`'s lookup answered `None` and that row NEVER FIRED. The
/// conjunction reading worked by a different mechanism entirely (`goal_arg_slots` and
/// `is_goal_conjunction` match the resolved symbol's LOCAL NAME, which
/// `anthill.prelude.Bool.and` also answers), so the capability was real and its stated
/// guard was not the one supplying it.
///
/// It surfaced the moment `&` began carrying an address: `..anthill.kernel.and` resolved
/// to nothing and reached the typer verbatim as "unknown functor". The peer `or` has
/// always had its pre-declaration; `push_choice` / `push_and` get theirs from
/// `register_builtin_tag`, which defines a missing name rather than skipping it.
///
/// `wi040_reserved_vocab_test::every_desugar_target_is_declared_by_the_standard_load` is
/// the row that NAMES it (it walks `CONNECTIVE_FUNCTORS` now); this one states what the
/// name has to reach and drives the reading that depends on it.
#[test]
fn the_kernel_conjunction_is_reachable_by_qualified_name() {
    let mut kb = try_load_kb_with(
        r#"
namespace p9y67.conj
  import anthill.prelude.{Int64}
  fact p(1)
  fact p(2)
  fact r(1)
  rule both(?x) :- p(?x) & r(?x)
end
"#,
    )
    .unwrap_or_else(|e| panic!("fixture must load: {e:?}"));
    for qn in ["anthill.kernel.and", "anthill.kernel.or", "anthill.kernel.not"] {
        assert!(
            kb.try_resolve_symbol(qn).is_some(),
            "`{qn}` must resolve: it is what a minted connective's address names"
        );
    }
    assert_eq!(
        sole_definite_int(&mut kb, "p9y67.conj.both"),
        1,
        "`p(?x) & r(?x)` must be the conjunction — one definite answer, not two"
    );
}

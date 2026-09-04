//! WI-20260903-FC2X4 — A COMPOUND EXPRESSION WRITTEN IN A RULE IS THE ONE THE AUTHOR
//! WROTE.
//!
//! `lambda` / `if` / `let` / `match` / `proof` are lowered by the converter into
//! POSITIONAL marker terms (`convert.rs`'s `alloc_marker_term`:
//! `lambda_expr(param, body)`), and exactly one walk reads that layout —
//! `Loader::visit_load`, whose marker arms index `pos_args` by position, push the binder's
//! names onto `local_names_stack`, and build the reflect NAMED form beside a
//! `NodeKind::Pattern` occurrence for the binder. A RULE has always used a different walk
//! (`build_body_atom_occurrence`, WI-246), and that walk had no such arm: `lambda_expr` is
//! an `is_reflect_form_functor` name, so a marker went to
//! `materialize_from_handle_spanned`, whose `visit_fn` reads the NAMED keys, found none,
//! and built the form with `⊥` in every slot.
//!
//! ── THE POPULATION, MEASURED ON THE WI-20260903-FCZ3N TREE ──────────────────
//!
//! One program per row. Four of the five are SILENT because `?y <=> …` binds without
//! typing; the lambda is the loud tail, not the whole of it:
//!
//! ```text
//!   :- apply1(lambda (x: Int64) -> x + 1, 2) = 3     REFUSED  "<bottom>.expr" at 1:1
//!   :- ?y <=> (if 1 = 1 then 10 else 20)             ANSWERS  If{⊥, ⊥, ⊥}
//!   :- ?y <=> (let a = 5  a + 1)                     ANSWERS  Let{<marker>, ⊥, ⊥}
//!   :- ?y <=> (match 1 case 1 -> 100 case _ -> 200)  ANSWERS  Match{⊥, branches: []}
//!   :- ?y <=> (proof q by derivation end 7)          ANSWERS  Proof{⊥}
//! ```
//!
//! ── WHAT THE TERM CARRIER DOES *NOT* DO, AND WHOSE QUESTION THAT IS ─────────
//!
//! `convert_term` still builds the positional marker for a fact head, a rule head and a
//! query pattern, so `fact p(lambda x -> 1)` and a goal `p(lambda x -> 1)` still do not
//! unify. That is **WI-20260829-8VGRW**, an open question with three answers (make it
//! match, refuse it, make the reflect spelling the only one) whose own feedback says the
//! family must move together. Lowering the term here would move ONE member: `if` has no
//! binder, so its two sides would agree and start matching, while `lambda` and `let`
//! alpha-rename their binder per SITE (`Loader::binder_sym` is `intern_unique`) and would
//! not — the exact asymmetry that ticket exists to avoid.
//! `wi_ybbc3_compound_expression_positions_test::a_compound_form_in_a_rule_data_position_loads_and_matches_nothing`
//! is the row that pins it, and it is UNMOVED by this ticket (verified: it passes both
//! ways).
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ──────────────────────────
//!
//! FOUR axes reach this file, in four places, and the matrix is MEASURED one back-out at
//! a time — not predicted. It is not a diagonal: two rows fall to one axis each, and
//! those asymmetries are what say the axes are separate decisions rather than one change
//! with four names.
//!
//! ```text
//!                                                    axis 1  axis 2  axis 3  axis 5
//!   a_lambda_in_a_rule_body_is_applied_and_answers…    RED     RED     RED    green
//!   a_dot_and_an_unknown_name_inside_a_rule_body_…     RED     RED     RED    green
//!   a_lambda_in_a_fired_simp_rhs_is_applied_and_…      RED    green   green   green
//!   the_other_compound_surfaces_carry_what_was_…       RED     RED    green   green
//!   a_let_binder_in_a_rule_body_is_the_symbol_…        RED     RED    green   green
//!   a_function_slot_argument_that_is_returned_…        RED     RED    green   green
//!   an_arrow_inside_a_rule_body_lambda_is_not_…        RED     RED    green    RED
//!   the_same_call_in_an_operation_body_is_the_…       green   green   green   green
//!   a_written_reflect_expression_form_is_not_re_…     green   green   green   green
//! ```
//!
//! **AXIS 1 — THE LOADER DELEGATION.** `Loader::compound_expression_occurrence` made to
//! answer `None`, so a marker goes back to the term round-trip. Fells 7 of the 9.
//!
//! **AXIS 2 — THE TYPER'S BINDER SHAPE.** The `CallDispatch::BinderForm` arm removed from
//! `typing::call_dispatch_shape`, so `dispatch_calls_in_occ` descends into a lambda / let
//! body with no Γ to put the binder in. Fells every rule-body row with
//! `x.name` / `a.name`: `expected resolved name, got unresolved`, AT THE BODY'S OWN SPAN.
//! The `if` / `match` / `proof` arms of the surfaces row stay green — they bind no name
//! their children read — which is what says this axis is the SCOPE and not the shape.
//!
//! **AXIS 3 — THE APPLY-SITE CLOSURE.** The `Value::Node` arm of
//! `eval::dispatch_call_with_requirements_inner`'s local-callable lookup removed, so a
//! lambda the resolver proved is not callable. Fells the two rows that APPLY what they
//! built, with ZERO answers (the callee reports `unknown operation: apply1.f` inside the
//! bridge and `bridge_op_to_eval` residualizes).
//!
//! **AXIS 5 — THE ARROW READER'S POSITION.** The `!self.lowering_rule_compound_expr`
//! clause dropped from `visit_load`'s arrow arm, so an operation body's "a bare `->` is a
//! keyword-less lambda" refusal fires inside a RULE's lambda. Fells ONE row here, and
//! `wi618_bare_arrow_logic_test::lambda_binder_under_inner_arrow_still_loads` with it.
//!
//! **AXIS 4 — THE SPLICED PATTERN'S OWNER** is NOT measured by any row in this file, and
//! could not be: `from.owner` is `None` at every splice in the corpus (542 fires,
//! instrumented). It is driven directly by
//! `kb::simp_rewrite::tests::a_spliced_pattern_takes_the_redexs_owner`, which carries the
//! measurement.
//!
//! **WHY THE `[simp]` ROW IS GREEN ON AXES 2 AND 3, measured and not assumed.** A
//! `[simp]` equation has an EMPTY body by construction (`KnowledgeBase::is_equation`), so
//! its RHS is not among `rule_body_nodes` and `type_rule_bodies` never walks it; and the
//! fired RHS is spliced into an OPERATION body, where the typer and eval both handle the
//! lambda at its own site. That position needed the loader fix and nothing else — which
//! is exactly why row A and row B are both here rather than one standing in for the
//! other, as the ticket asks.
//!
//! ── TWO PROGRAMS THIS REFUSES THAT USED TO "LOAD" ──────────────────────────
//!
//! Both loaded before only because the body was `⊥`, i.e. meant nothing, and both are now
//! refused because a binder form is TYPED — with `expected: None`, since the enclosing
//! call sits in a rule DATA slot and WI-1058 deliberately does not type-check one:
//!
//! ```text
//!   :- ?r <=> apply1(lambda x -> x + 1, 2)      "ambiguous dispatch of Additive.add"
//!                                               (the ANNOTATED twin answers 3, and so
//!                                                does the op-body twin, whose arrow slot
//!                                                supplies the binder's type)
//!   :- ?y <=> (lambda t -> (t -> t))            "`arrow` … unknown functor"
//! ```
//!
//! An unannotated binder whose body PINS it from its own call is unaffected — measured on
//! `wi620_paren_lambda_param_test`'s `all_match(?xs, lambda (x) -> is_pos(x))`, which
//! loads clean. Supplying the argument slot's declared arrow as the binder form's expected
//! type is **WI-20260904-50B2K**; this ticket does not settle it.

use anthill_core::eval::Value;
use anthill_core::kb::node_occurrence::{
    for_each_child, for_each_pattern_child, Expr, NodeKind, NodeOccurrence, Pattern,
};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;
use std::rc::Rc;

/// The shared preamble: a higher-order operation to APPLY a lambda with, so every row
/// that claims a lambda "works" has something to hand it to.
const PREAMBLE: &str = "  import anthill.prelude.{Int64, Bool, Function}\n  \
   operation apply1(f: Function[A = Int64, B = Int64], n: Int64) -> Int64 = f(n)\n";

fn program(ns: &str, body: &str) -> String {
    format!("namespace {ns}\n{PREAMBLE}{body}end\n")
}

/// Load, failing loudly with the loader's own messages — every row here asserts about a
/// program that must LOAD, so a refusal is the finding and must not read as "no answer".
fn load(ns: &str, body: &str) -> KnowledgeBase {
    let src = program(ns, body);
    crate::common::try_load_kb_with(&src).unwrap_or_else(|errs| {
        panic!(
            "must load; got {} error(s):\n{}",
            errs.len(),
            errs.join("\n")
        )
    })
}

/// DEFINITE solutions of an arbitrary goal pattern — `.len()` would count a FLOUNDERED
/// one as an answer (WI-20260822-WZX6B), and every "does not answer" row here is exactly
/// the shape that residualizes when the bridge declines.
fn definite(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .filter(|s| s.is_definite())
        .count()
}

/// The single definite value a unary goal produces — so a row asserts the VALUE and not
/// merely that something answered.
fn only_value(kb: &mut KnowledgeBase, qn: &str) -> Option<Value> {
    let mut vs = crate::common::definite_unary(kb, qn);
    assert!(
        vs.len() <= 1,
        "{qn}: expected at most one answer, got {vs:?}"
    );
    vs.pop()
}

/// That value as an `i64`. `Value` has no `PartialEq` (a handle-carrying variant has no
/// structural equality), so a row asserts on the SCALAR it means rather than on the enum.
///
/// CARRIER-NEUTRAL, and measured rather than assumed: the same arithmetic comes back as a
/// native `Value::Int` down one path and as a `Value::Node(Const(Int))` down another (the
/// dot-dispatch row), because a reduction that ends inside an occurrence keeps the carrier
/// it was proved on. `Value::as_int` reads the variant alone, so a row using it would have
/// failed on a right answer.
fn only_int(kb: &mut KnowledgeBase, qn: &str) -> i64 {
    let v = only_value(kb, qn).unwrap_or_else(|| panic!("{qn}: no definite answer"));
    if let Some(i) = v.as_int() {
        return i;
    }
    if let Value::Node(occ) = &v {
        if let Some(Expr::Const(anthill_core::kb::term::Literal::Int(i))) = occ.as_expr() {
            return *i;
        }
    }
    panic!("{qn}: expected an Int64 answer, got {v:?}")
}

/// Every node of an occurrence tree, `Expr` and `Pattern` alike, as a short tag —
/// `BOTTOM` for `Expr::Bottom`, the variant name otherwise. The `⊥`-filled shapes this
/// ticket removes are invisible to a value comparison (they ARE the value `?y` binds to),
/// so the rows below read the tree.
fn tags(occ: &Rc<NodeOccurrence>, out: &mut Vec<String>) {
    match &occ.kind {
        NodeKind::Expr { expr, .. } => {
            out.push(match expr {
                Expr::Bottom => "BOTTOM".to_string(),
                other => format!("{other:?}")
                    .split(['{', '('])
                    .next()
                    .unwrap()
                    .trim()
                    .to_string(),
            });
            for_each_child(expr, |c| tags(c, out));
        }
        NodeKind::Pattern { pattern, .. } => {
            out.push(match pattern {
                Pattern::Var { .. } => "Pattern::Var".to_string(),
                Pattern::Wildcard => "Pattern::Wildcard".to_string(),
                Pattern::Literal { .. } => "Pattern::Literal".to_string(),
                Pattern::Constructor { .. } => "Pattern::Constructor".to_string(),
                Pattern::Tuple { .. } => "Pattern::Tuple".to_string(),
            });
            for_each_pattern_child(occ, |c| tags(c, out));
        }
        other => out.push(format!("{other:?}")),
    }
}

/// The node a `?y <=> <compound>` rule binds, as its tag list.
fn bound_node_tags(ns: &str, body: &str, qn: &str) -> Vec<String> {
    let mut kb = load(ns, body);
    let v = only_value(&mut kb, qn).unwrap_or_else(|| panic!("{qn}: no definite answer"));
    let Value::Node(occ) = v else {
        panic!("{qn}: expected an occurrence-carried value, got {v:?}");
    };
    let mut out = Vec::new();
    tags(&occ, &mut out);
    out
}

/// **A — THE TICKET'S OWN PROGRAM.** A lambda in a RULE BODY is applied, and the answer
/// is 3.
///
/// The `= 4` arm is what makes the `= 3` arm mean something: a goal that merely LOADS and
/// answers would satisfy the first assertion with any value at all, and this pair pins
/// which one. RED on axes 1 and 2 as a LOAD REFUSAL, and on axis 3 as `0` where `1` is
/// expected.
#[test]
fn a_lambda_in_a_rule_body_is_applied_and_answers_three() {
    let mut kb = load(
        "zzfc2x4.body",
        "  rule right(1) :- apply1(lambda (x: Int64) -> x + 1, 2) = 3\n  \
           rule wrong(1) :- apply1(lambda (x: Int64) -> x + 1, 2) = 4\n  \
           rule value(?r) :- ?r <=> apply1(lambda (x: Int64) -> x + 1, 2)\n",
    );
    assert_eq!(
        definite(&mut kb, "zzfc2x4.body.right(?x)"),
        1,
        "`apply1(lambda (x: Int64) -> x + 1, 2) = 3` must hold in a rule body",
    );
    assert_eq!(
        definite(&mut kb, "zzfc2x4.body.wrong(?x)"),
        0,
        "…and `= 4` must not — else the row above measures only that something answered",
    );
    assert_eq!(
        only_int(&mut kb, "zzfc2x4.body.value"),
        3,
        "the applied lambda's VALUE, read out rather than compared against inside the rule",
    );
}

/// **B — THE SECOND POSITION THE TICKET NAMES:** a lambda in a `[simp]` RHS, DRIVEN
/// through a consumer operation, with the value asserted.
///
/// Two different arguments, so the answer tracks the input rather than matching a
/// constant the RHS could have folded to on its own.
///
/// RED ON AXIS 1 ONLY, and that asymmetry with row A is the reason both rows exist. The
/// RHS occurrence is built by the same walk row A needs (WI-20260903-FCZ3N put it there),
/// so the loader fix is shared; but a `[simp]` equation has an empty BODY, so
/// `type_rule_bodies` never walks this lambda (axis 2), and the fired RHS lands in an
/// OPERATION body where eval reduces it at its own site rather than across the bridge
/// (axis 3). Measured, not predicted — see the matrix above.
#[test]
fn a_lambda_in_a_fired_simp_rhs_is_applied_and_answers() {
    let mut kb = load(
        "zzfc2x4.simp",
        "  rule lam(?n) <=> apply1(lambda (x: Int64) -> x * 10, ?n) [simp]\n  \
           operation four() -> Int64 = lam(4)\n  \
           operation seven() -> Int64 = lam(7)\n  \
           rule from_four(?r) :- ?r <=> four()\n  \
           rule from_seven(?r) :- ?r <=> seven()\n",
    );
    assert_eq!(
        only_int(&mut kb, "zzfc2x4.simp.from_four"),
        40,
        "a lambda spliced from a fired `[simp]` RHS must be APPLIED, not merely present",
    );
    assert_eq!(
        only_int(&mut kb, "zzfc2x4.simp.from_seven"),
        70,
        "…and the answer must track the argument, so 40 above is not a constant",
    );
}

/// **THE YARDSTICK.** The same call written in an OPERATION body answers 3 — before this
/// ticket and after, and under every back-out above.
///
/// It is what says the defect was POSITIONAL: the closure machinery, the higher-order
/// apply and the arithmetic all worked, and only a lambda written in a RULE could not
/// reach them. A row that fails here is not a regression in this ticket, it is the
/// fixture breaking.
#[test]
fn the_same_call_in_an_operation_body_is_the_yardstick() {
    let mut kb = load(
        "zzfc2x4.opbody",
        "  operation viaop() -> Int64 = apply1(lambda (x: Int64) -> x + 1, 2)\n  \
           rule value(?r) :- ?r <=> viaop()\n",
    );
    assert_eq!(
        only_int(&mut kb, "zzfc2x4.opbody.value"),
        3,
        "the operation-body twin is the control and must be unmoved",
    );
}

/// **C — THE SILENT HALF.** The four compound surfaces that are not a lambda bound a
/// `⊥`-filled node and said nothing; each now carries what was written.
///
/// The assertion is `BOTTOM` NOWHERE plus one shape fact per surface, because these rows
/// answer either way — what changed is WHAT they answer, and a solution count cannot see
/// it. RED on axis 1 for all four (the `if` arm loses its condition, `match` its
/// branches, `proof` its body, `let` all three of pattern / value / body); RED on axis 2
/// for the `let` arm only, as a load refusal naming its binder.
#[test]
fn the_other_compound_surfaces_carry_what_was_written() {
    // `if` — the condition and both branches are the written ones.
    let t = bound_node_tags(
        "zzfc2x4.iff",
        "  rule value(?y) :- ?y <=> (if 1 = 1 then 10 else 20)\n",
        "zzfc2x4.iff.value",
    );
    assert!(
        !t.contains(&"BOTTOM".to_string()),
        "`if` still carries ⊥: {t:?}"
    );
    assert_eq!(
        t,
        vec!["If", "Apply", "Const", "Const", "Const", "Const"],
        "the written condition (`1 = 1`, an Apply over two literals) and both branches",
    );

    // `let` — a real binder, its value, and a body that reads it.
    let t = bound_node_tags(
        "zzfc2x4.lett",
        "  rule value(?y) :- ?y <=> (let a = 5  a + 1)\n",
        "zzfc2x4.lett.value",
    );
    assert!(
        !t.contains(&"BOTTOM".to_string()),
        "`let` still carries ⊥: {t:?}"
    );
    assert_eq!(
        t,
        vec!["Let", "Pattern::Var", "Const", "Apply", "VarRef", "Const"],
        "the pattern is a PATTERN (it was a reflect `Expr::Apply` on `pattern_var`), and \
         the body is the written `a + 1`",
    );

    // `match` — the scrutinee and BOTH branches, each with its own pattern.
    let t = bound_node_tags(
        "zzfc2x4.matt",
        "  rule value(?y) :- ?y <=> (match 1 case 1 -> 100 case _ -> 200)\n",
        "zzfc2x4.matt.value",
    );
    assert!(
        !t.contains(&"BOTTOM".to_string()),
        "`match` still carries ⊥: {t:?}"
    );
    assert_eq!(
        t,
        vec![
            "Match",
            "Const",
            "Pattern::Literal",
            "Const",
            "Pattern::Wildcard",
            "Const"
        ],
        "two branches with their own patterns — the branch LIST was empty",
    );

    // `proof` — its continuation body.
    let t = bound_node_tags(
        "zzfc2x4.prf",
        "  rule q(1) :- 1 = 1\n  rule value(?y) :- ?y <=> (proof q by derivation end 7)\n",
        "zzfc2x4.prf.value",
    );
    assert!(
        !t.contains(&"BOTTOM".to_string()),
        "`proof` still carries ⊥: {t:?}"
    );
    assert_eq!(t, vec!["Proof", "Const"], "the proof's continuation body");
}

/// **THE BINDER IS ONE IDENTITY.** A `let` in a rule body binds a name its body REFERS
/// to, and the two are the same `Symbol`.
///
/// Row C asserts the SHAPES (`Pattern::Var` … `VarRef`); this asserts they are the same
/// binder. Both are needed: the alpha-renamed binder symbol
/// (`Loader::binder_sym`, `intern_unique`) is what the old walk could not produce at all —
/// its `pattern_var` marker kept the SOURCE name as a bare `Ident` — so a shape-only
/// assertion would pass on a tree whose body names a symbol nothing binds.
///
/// RED on axes 1 and 2 (a load refusal, before any tree exists to compare).
#[test]
fn a_let_binder_in_a_rule_body_is_the_symbol_its_body_reads() {
    let mut kb = load(
        "zzfc2x4.binder",
        "  rule value(?y) :- ?y <=> (let a = 5  a + 1)\n",
    );
    let Some(Value::Node(occ)) = only_value(&mut kb, "zzfc2x4.binder.value") else {
        panic!("no occurrence-carried answer");
    };
    let Some(Expr::Let { pattern, body, .. }) = occ.as_expr() else {
        panic!("expected an Expr::Let, got {:?}", occ.kind);
    };
    let NodeKind::Pattern {
        pattern: Pattern::Var { name: bound },
        ..
    } = &pattern.kind
    else {
        panic!(
            "the let's pattern must be a Pattern-kind binder, got {:?}",
            pattern.kind
        );
    };
    // The body is `a + 1`: an Apply whose first argument is the reference.
    let Some(Expr::Apply { pos_args, .. }) = body.as_expr() else {
        panic!("expected the written `a + 1`, got {:?}", body.kind);
    };
    let Some(Expr::VarRef { name: read }) = pos_args[0].as_expr() else {
        panic!(
            "expected a VarRef to the binder, got {:?}",
            pos_args[0].kind
        );
    };
    assert_eq!(
        bound, read,
        "the binder the pattern introduces and the name the body reads must be ONE symbol",
    );
}

/// **THE PROVENANCE BOUNDARY.** A reflect expression form the author WROTE is not a
/// converter marker and is not re-lowered: it keeps the term round-trip's reading, where
/// `param` is an ordinary `Expr` child.
///
/// PASSES EITHER WAY BY DESIGN, and is here as the boundary statement rather than as a
/// control for any axis: the delegation is gated on `SimpleTermStore::is_minted`, AND the
/// marker's functor carries `ABSOLUTE_PATH_MARKER` (`..anthill.reflect.Expr.lambda_expr`),
/// which `_identifier_token` cannot spell — so no written call can reach the arm through
/// either gate. What this row does guard is that the round-trip still SERVES a written
/// reflect form, which is the path a reflection rule matching expression syntax as data
/// depends on.
#[test]
fn a_written_reflect_expression_form_is_not_re_lowered() {
    let t = bound_node_tags(
        "zzfc2x4.written",
        "  rule value(?y) :- ?y <=> anthill.reflect.Expr.lambda_expr(param: 1, body: 2)\n",
        "zzfc2x4.written.value",
    );
    assert_eq!(
        t,
        vec!["Lambda", "Const", "Const"],
        "a WRITTEN `lambda_expr(param:, body:)` keeps `visit_fn`'s reading — its `param` \
         is the Expr child the author put there, not a binder this ticket would have \
         built",
    );
}

/// **THE POSITION KEEPS ITS OWN ARROW READER.** A rule lends `visit_load` its compound
/// expressions; it does not adopt that walk's reading of a bare `->`.
///
/// In an OPERATION body `->` in expression position is always the WI-605 keyword-less
/// lambda typo (`LoadError::ArrowTermInExprPosition`). In a RULE the rule side reads it
/// with `Loader::check_bare_arrow_typo`, whose `binder_form_layout` SCOPES the lambda's
/// binder — so `lambda t -> (t -> t)` is not a typo, the keyword is right there. The
/// delegation put the op-body arm underneath that reader, and the first cut of this ticket
/// told an author writing exactly that lambda "a lambda needs the `lambda` keyword",
/// contradicted by the keyword three characters to the left. Measured as
/// `wi618_bare_arrow_logic_test::lambda_binder_under_inner_arrow_still_loads`, which fails
/// with the gate removed, as does this row.
///
/// **THE PROGRAM IS STILL REFUSED, and for an accurate reason.** A lambda body is a VALUE
/// expression and `(t -> t)` is an arrow TERM, so the typer — which now types a binder
/// form as a unit (`CallDispatch::BinderForm`) — reports that `arrow` names no operation.
/// What this row pins is WHICH sentence: not the self-contradictory advice. (Before this
/// ticket the program "loaded" with a `⊥` body, i.e. meaning nothing. Reading an arrow
/// term inside a rule-body lambda AS A TYPE is a design question this ticket does not
/// settle — WI-20260904-50B2K.)
///
/// **AND THE GATE DELETES NO DIAGNOSTIC.** A genuine keyword-less typo written inside a
/// rule-body lambda is still refused, by the reader that owns the question — so the
/// op-body arm was redundant here, not load-bearing. Without this arm the gate would read
/// as a silent widening of what loads.
#[test]
fn an_arrow_inside_a_rule_body_lambda_is_not_read_as_a_keyword_typo() {
    let hinted = |ns: &str, body: &str| -> Vec<String> {
        crate::common::try_load_kb_with(&program(ns, body))
            .err()
            .unwrap_or_default()
    };

    // The legitimate keyword lambda whose BODY is an arrow type.
    let e = hinted(
        "zzfc2x4.arrow",
        "  rule value(?y) :- ?y <=> (lambda t -> (t -> t))\n",
    );
    assert!(
        !e.iter().any(|m| m.contains(crate::common::LAMBDA_HINT)),
        "the `lambda` keyword IS present — the op-body arrow advice must not fire: {e:?}",
    );
    assert!(
        e.iter()
            .any(|m| m.contains("arrow") && m.contains("unknown functor")),
        "…and what IS said names the arrow term, which a value position cannot read: {e:?}",
    );

    // The genuine typo, one level in. Still refused, with the rule-side sentence.
    let e = hinted(
        "zzfc2x4.typo",
        "  rule value(?y) :- ?y <=> (lambda t -> (q -> q))\n",
    );
    assert!(
        e.iter().any(|m| m.contains(crate::common::LAMBDA_HINT)),
        "a keyword-less `q -> q` inside a rule-body lambda must still be refused: {e:?}",
    );
    assert!(
        e.iter().any(|m| m.contains("in a rule body")),
        "…by the RULE-side reader, which is the one that scopes the lambda's binder: {e:?}",
    );
}

/// **THE BINDER'S SUBTREE IS TYPED, NOT SKIPPED** — a dot inside a rule-body lambda is
/// dispatched, and a name that resolves to nothing is refused with the sentence its
/// operation-body twin gets.
///
/// THREE ROWS FROM ONE `/code-review` FINDING, and the first was a PANIC. The first cut of
/// axis 2 made `dispatch_calls_in_occ` return a binder form UNWALKED — which also left it
/// UNTYPED, since a node with no `CallDispatch` never reaches `type_check_node_at`. The
/// loader change makes that subtree real code for the first time, so an undispatched
/// `Expr::DotApply` inside it reached eval as a pre-dispatch form and died
/// `unhandled Expr variant in eval` — a `debug_assert` in debug, and in release a rule that
/// silently answers 0. The repair is `CallDispatch::BinderForm`: the node does not recurse
/// and IS handed to `type_check_node`, whose `Expr::Lambda` / `Let` / `Match` arms bind the
/// pattern into Γ (`bind_and_label_pattern`) — the one place in the typer that knows how.
///
/// RED on axis 2 (the arm removed): row 1 PANICS, rows 2 and 3 lose their diagnostic and
/// the program loads clean. Green on every other axis.
#[test]
fn a_dot_and_an_unknown_name_inside_a_rule_body_binder_are_decided() {
    // 1 — A DOT. It must dispatch AND run; before the repair it reached eval un-lowered
    // as a pre-dispatch `Expr::DotApply` and died there.
    const BOXED: &str = "  sort Box\n    entity box(value: Int64)\n    \
       operation peek(b: Box) -> Int64 = b.value\n  end\n  \
       operation useb(f: anthill.prelude.Function[A = Box, B = Int64], b: Box) -> Int64 = f(b)\n";
    let mut kb = load(
        "zzfc2x4.dot",
        &format!(
            "{BOXED}  rule value(?r) :- ?r <=> useb(lambda (x: Box) -> x.peek(), box(value: 7))\n"
        ),
    );
    assert_eq!(
        only_int(&mut kb, "zzfc2x4.dot.value"),
        7,
        "a dotted call inside a rule-body lambda must dispatch and RUN",
    );

    // …and a BOGUS member inside one is refused rather than reaching eval. The pair is
    // what says the subtree is decided, not merely walked past.
    let bogus = crate::common::try_load_kb_with(&program(
        "zzfc2x4.dotbogus",
        &format!("{BOXED}  rule value(?r) :- ?r <=> useb(lambda (x: Box) -> x.nosuchmember(), box(value: 7))\n"),
    ))
    .err()
    .unwrap_or_default();
    assert!(
        bogus.iter().any(|m| m.contains("nosuchmember")),
        "a bogus member inside a rule-body lambda must be named, not silently dropped: \
         {bogus:?}",
    );

    // 2 and 3 — AN UNKNOWN NAME, in the rule and in its operation-body twin. The two
    // spellings must get ONE verdict; the defect was that the rule accepted it silently.
    let rule_errs = crate::common::try_load_kb_with(&program(
        "zzfc2x4.unknown",
        "  rule value(?r) :- ?r <=> apply1(lambda (x: Int64) -> nosuchname + x, 2)\n",
    ))
    .err()
    .unwrap_or_default();
    let op_errs = crate::common::try_load_kb_with(&program(
        "zzfc2x4.unknownop",
        "  operation viaop() -> Int64 = apply1(lambda (x: Int64) -> nosuchname + x, 2)\n",
    ))
    .err()
    .unwrap_or_default();
    assert!(
        op_errs
            .iter()
            .any(|m| m.contains("nosuchname") && m.contains("expected resolved name")),
        "the operation-body twin is the yardstick and must refuse: {op_errs:?}",
    );
    assert!(
        rule_errs
            .iter()
            .any(|m| m.contains("nosuchname") && m.contains("expected resolved name")),
        "…and the RULE must say the same thing, not load clean: {rule_errs:?}",
    );
}

/// **A FUNCTION-SLOT ARGUMENT THAT IS RETURNED IS NOT A CLOSURE.** The lambda→closure
/// conversion happens where the value is APPLIED, so a callee that merely passes it
/// through hands the resolver back the occurrence it can carry.
///
/// The first cut converted at the bridge BOUNDARY, gated on the callee's declared
/// parameter type. Two things went wrong, both closed by moving the conversion to the
/// apply site (`Interpreter::closure_of_applied_lambda_node`): a `[simp]` MACRO reaches
/// that same entry and reads its lambda argument as SYNTAX (converting on the way in
/// felled 85 rows across the relation algebra), and this row — a `Function`-typed slot the
/// callee RETURNS rather than applies handed back an opaque `Value::Closure`, which is not
/// unifiable, not deep-ground and not printable, where a `Value::Node` had been.
///
/// RED under a conversion moved back to the boundary; green on every axis in the matrix
/// above, because nothing here applies what it built.
#[test]
fn a_function_slot_argument_that_is_returned_stays_an_occurrence() {
    let mut kb = load(
        "zzfc2x4.passthru",
        "  operation idf(f: Function[A = Int64, B = Int64]) -> Function[A = Int64, B = Int64] = f\n  \
           rule value(?r) :- ?r <=> idf(lambda (x: Int64) -> x + 1)\n",
    );
    let v = only_value(&mut kb, "zzfc2x4.passthru.value").expect("one answer");
    let Value::Node(occ) = &v else {
        panic!(
            "a pass-through function slot must hand the resolver an OCCURRENCE it can \
             carry, not an opaque handle: {v:?}"
        );
    };
    assert!(
        matches!(occ.as_expr(), Some(Expr::Lambda { .. })),
        "…and that occurrence is the lambda that was written: {:?}",
        occ.kind
    );
}

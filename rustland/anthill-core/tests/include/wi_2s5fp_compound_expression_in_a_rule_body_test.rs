//! WI-20261011-2S5FP — a compound expression written in a rule body's value slot denotes
//! its value (kernel-language.md §5.9; proposal 068 §1).
//!
//! THE RULE. An `if`, a `let` or a `match` a rule body writes in a value slot — an operand
//! of `<=>` or `=`, a call's argument, a goal's argument, a field of a construction — is
//! evaluated as the same text is in an operation body, once every variable it names is
//! bound; until then it waits. It is typed as that operation body, whole. A lambda stays a
//! value, run where it is applied. An in-body proof is refused in a rule body (§5.10): a
//! rule body is a derivation, and a rule is proved by a proof declaration.
//!
//! BEFORE (measured 2026-10-11 on b3f238c0 and again on 030aec34): the form was bound as
//! it was written (`?r = if eq(1, 1) then 10 else 20`), compared as data (a true `=`
//! answered nothing, and `not` over it held), left a residual under a call, and killed the
//! process when the callee read into it (`fstof((if … then (4, 5) else …))`, a panic in
//! the bridge).
//!
//! EVERY ROW HAS ITS OWN SOURCE: a row that shares a fixture with another measures the
//! fixture.
//!
//! CONTROLS — see the ledger at the end of the file.

use anthill_core::eval::Value;

use crate::common::{load_errors_of, load_kb_with, query_unary, resolve_with_messages, run_int64};

/// `test.<name>`, holding `body`, with the operations the rows call.
fn ns(name: &str, body: &str) -> String {
    format!(
        "namespace test.{name}\n  import anthill.prelude.{{Type, Int64, String, Bool, List, Cell}}\n  \
         import anthill.prelude.Time.{{now, Clock}}\n  \
         operation inc(p: Int64) -> Int64 = p + 1\n  \
         operation fstof(p: (Int64, Int64)) -> Int64 = p._1\n  \
         operation idI(x: Int64) -> Int64 = x\n{body}\nend\n"
    )
}

/// The answers of `test.<name>.value(?r)` over `body`.
fn answers(name: &str, body: &str) -> Vec<(Value, bool)> {
    let mut kb = load_kb_with(&ns(name, body));
    query_unary(&mut kb, &format!("test.{name}.value"))
}

/// `value(?r)` answers `n`, definitely, and nothing else.
#[track_caller]
fn assert_answers(name: &str, body: &str, n: i64) {
    let got = answers(name, body);
    assert!(
        matches!(got.as_slice(), [(Value::Int(v), true)] if *v == n),
        "{name}: expected {n}, definite; got {got:?}"
    );
}

/// The load of `body` is refused, one of its errors containing `needle`.
#[track_caller]
fn assert_refused(name: &str, body: &str, needle: &str) {
    let errs = load_errors_of(&ns(name, body));
    assert!(
        errs.iter().any(|e| e.contains(needle)),
        "{name}: expected a refusal containing {needle:?}; got {errs:?}"
    );
}

// ── the ticket's programs: (1) an operand of `<=>` ──────────────────────────────

#[test]
fn an_if_bound_by_unify_is_its_value() {
    assert_answers("p1if", "  rule value(?r) :- ?r <=> (if 1 = 1 then 10 else 20)", 10);
}

#[test]
fn a_let_bound_by_unify_is_its_value() {
    assert_answers("p1let", "  rule value(?r) :- ?r <=> (let a = 5  a + 1)", 6);
}

#[test]
fn a_match_bound_by_unify_is_its_value() {
    assert_answers(
        "p1match",
        "  rule value(?r) :- ?r <=> (match 1 case 1 -> 100 case _ -> 200)",
        100,
    );
}

// ── (2) an operand of `=`, and `not` over it ────────────────────────────────────

#[test]
fn an_if_compared_by_eq_holds() {
    assert_answers(
        "p2if",
        "  rule value(?r) :- (if 1 = 1 then 10 else 20) = 10, ?r <=> 1",
        1,
    );
}

#[test]
fn a_let_compared_by_eq_holds() {
    assert_answers("p2let", "  rule value(?r) :- (let a = 5  a + 1) = 6, ?r <=> 1", 1);
}

#[test]
fn a_match_compared_by_eq_holds() {
    assert_answers(
        "p2match",
        "  rule value(?r) :- (match 1 case 1 -> 100 case _ -> 200) = 100, ?r <=> 1",
        1,
    );
}

/// Before: `not` over the true comparison held, definitely — a falsehood proved.
#[test]
fn not_over_a_true_comparison_answers_nothing() {
    let got = answers(
        "p2not",
        "  rule value(?r) :- not((if 1 = 1 then 10 else 20) = 10), ?r <=> 1",
    );
    assert!(got.is_empty(), "{got:?}");
}

// ── (3) a call's argument ───────────────────────────────────────────────────────

#[test]
fn an_if_as_a_calls_argument_runs() {
    assert_answers("p3if", "  rule value(?r) :- ?r <=> inc((if 1 = 1 then 10 else 20))", 11);
}

#[test]
fn a_let_as_a_calls_argument_runs() {
    assert_answers("p3let", "  rule value(?r) :- ?r <=> inc((let a = 5  a + 1))", 7);
}

#[test]
fn a_match_as_a_calls_argument_runs() {
    assert_answers(
        "p3match",
        "  rule value(?r) :- ?r <=> inc((match 1 case 1 -> 100 case _ -> 200))",
        101,
    );
}

#[test]
fn a_call_over_an_if_compared_by_eq_holds() {
    assert_answers(
        "p3eq",
        "  rule value(?r) :- inc((if 1 = 1 then 10 else 20)) = 11, ?r <=> 1",
        1,
    );
}

// ── (4) an argument the callee reads into ───────────────────────────────────────

/// Before: the process died, the operation handed the `if` as a node ("field_access:
/// entity has no field _1").
#[test]
fn an_argument_the_callee_reads_into_runs() {
    assert_answers(
        "p4",
        "  rule value(?r) :- ?r <=> fstof((if 1 = 1 then (4, 5) else (6, 7)))",
        4,
    );
}

// ── carried from WI-20261023-Y2HFK ──────────────────────────────────────────────

#[test]
fn a_let_bound_by_unify_runs_its_arithmetic() {
    assert_answers("y2pure", "  rule value(?r) :- ?r <=> (let x = 3  x + 1)", 4);
}

#[test]
fn a_let_as_an_unparenthesized_argument_runs() {
    assert_answers("y2arg", "  rule value(?r) :- ?r <=> idI(let x = 3  x + 1)", 4);
}

/// A `let`'s own cell: the typing masks it (WI-20261013-R1W5A), and the value is computed.
#[test]
fn a_let_over_its_own_cell_runs() {
    assert_answers(
        "y2cell",
        "  rule value(?r) :- ?r <=> (let c = Cell.new(3)  Cell.get(c))",
        3,
    );
}

// ── the clause's variables in a form ────────────────────────────────────────────

#[test]
fn an_if_over_a_bound_head_variable_runs() {
    assert_answers(
        "varhead",
        "  rule pick(?c, ?r) :- ?r <=> (if ?c then 1 else 2)\n  \
           rule value(?r) :- pick(false, ?r)",
        2,
    );
}

/// The form waits for the variable it names, and runs once a later goal binds it.
#[test]
fn an_if_over_a_variable_bound_later_runs() {
    assert_answers(
        "varlater",
        "  rule value(?r) :- ?r <=> (if ?c then 1 else 2), ?c <=> true",
        1,
    );
}

/// Nothing binds the variable: the answer is conditional on the form, never the form.
#[test]
fn an_if_over_a_variable_nothing_binds_is_conditional() {
    let got = answers("varnever", "  rule value(?r) :- ?r <=> (if ?c then 1 else 2)");
    assert!(
        matches!(got.as_slice(), [(Value::Var(_), false)]),
        "{got:?}"
    );
}

/// `?x` is the clause's variable under a binder `x`: a binder is spelled without the sigil.
/// Before, it was a variable of its own, never bound.
#[test]
fn a_clause_variable_under_a_let_binder_of_its_name_is_the_clauses() {
    assert_answers(
        "xlet",
        "  rule value(?r) :- ?x <=> 10, ?r <=> (let x = 3  x + ?x)",
        13,
    );
}

#[test]
fn a_clause_variable_under_a_match_binder_of_its_name_is_the_clauses() {
    assert_answers(
        "xmatch",
        "  rule value(?r) :- ?x <=> 10, ?r <=> (match 1 case x -> x + ?x)",
        11,
    );
}

#[test]
fn a_clause_variable_under_a_lambda_binder_of_its_name_is_the_clauses() {
    assert_answers(
        "xlam",
        "  rule value(?r) :- ?x <=> 10, ?r <=> (let f = lambda (x: Int64) -> x + ?x  f(1))",
        11,
    );
}

#[test]
fn a_head_variable_under_a_let_binder_of_its_name_is_the_clauses() {
    assert_answers(
        "xhead",
        "  rule plus(?x, ?r) :- ?r <=> (let x = 3  x + ?x)\n  \
           rule value(?r) :- plus(10, ?r)",
        13,
    );
}

/// A sigil-free head parameter is the clause's variable inside the form too, as it is in
/// the rule's own term. Before, it was an unresolved name there.
#[test]
fn a_head_parameter_in_a_form_is_the_clauses() {
    assert_answers(
        "hparam",
        "  rule plus(x: Int64, ?r) :- ?r <=> (let a = 1  a + x)\n  \
           rule value(?r) :- plus(10, ?r)",
        11,
    );
}

#[test]
fn a_head_parameter_in_an_if_condition_is_the_clauses() {
    assert_answers(
        "hparamif",
        "  rule pos(x: Int64, ?r) :- ?r <=> (if x > 5 then x else 0)\n  \
           rule value(?r) :- pos(10, ?r)",
        10,
    );
}

/// The control of the two above: a binder of the form spelled like the parameter shadows it.
#[test]
fn a_binder_shadows_a_head_parameter_of_its_name() {
    assert_answers(
        "hparamshadow",
        "  rule plus(x: Int64, ?r) :- ?r <=> (let x = 1  x + 1)\n  \
           rule value(?r) :- plus(10, ?r)",
        2,
    );
}

/// The control of the four above: a clause variable no binder is spelled like.
#[test]
fn a_clause_variable_under_a_let_binder_of_another_name_is_the_clauses() {
    assert_answers(
        "ylet",
        "  rule value(?r) :- ?y <=> 10, ?r <=> (let x = 3  x + ?y)",
        13,
    );
}

// ── other positions ─────────────────────────────────────────────────────────────

#[test]
fn a_let_in_a_goals_argument_meets_its_fact() {
    assert_answers(
        "goalarg",
        "  fact p(6)\n  rule value(?r) :- p((let a = 5  a + 1)), ?r <=> 1",
        1,
    );
}

/// The control of the row above: the value is compared, so another value meets nothing.
#[test]
fn a_let_in_a_goals_argument_meets_no_other_fact() {
    let got = answers(
        "goalargno",
        "  fact p(6)\n  rule value(?r) :- p((let a = 5  a + 2)), ?r <=> 1",
    );
    assert!(got.is_empty(), "{got:?}");
}

#[test]
fn an_if_in_a_constructions_field_is_its_value() {
    assert_answers(
        "ctor",
        "  entity box(v: Int64)\n  \
           rule value(?r) :- ?b <=> box(v: (if true then 1 else 2)), box(v: ?r) <=> ?b",
        1,
    );
}

#[test]
fn an_if_in_a_list_literal_is_its_value() {
    assert_answers(
        "list",
        "  rule value(?r) :- ?l <=> [(if true then 1 else 2), 3], ?l = [1, 3], ?r <=> 1",
        1,
    );
}

#[test]
fn an_if_compared_by_an_order_holds() {
    assert_answers("order", "  rule value(?r) :- (if true then 3 else 4) > 2, ?r <=> 1", 1);
}

#[test]
fn a_lambda_under_an_if_is_applied() {
    assert_answers(
        "lamif",
        "  operation app(f: (Int64) -> Int64, x: Int64) -> Int64 = f(x)\n  \
           rule value(?r) :- ?r <=> (if true then app(lambda (y: Int64) -> y + 1, 2) else 0)",
        3,
    );
}

#[test]
fn nested_forms_run() {
    assert_answers(
        "nested",
        "  rule value(?r) :- ?r <=> (if true then (let a = 2  (match a case 2 -> 20 case _ -> 0)) else 0)",
        20,
    );
}

#[test]
fn a_dot_on_a_clause_variable_under_an_if_runs() {
    assert_answers(
        "dotif",
        "  rule value(?r) :- ?l <=> [1, 2], ?r <=> (if ?l.length() > 0 then ?l.length() else 0)",
        2,
    );
}

/// A type a substitution rebuilt — the entry `(?a) -> Int64` once `?a` is bound — is the
/// type argument it spells, equal to the one written ground.
#[test]
fn a_type_rebuilt_over_a_clause_variable_under_an_if_is_a_type_argument() {
    assert_answers(
        "rebuilt",
        "  sort Box[V]\n    operation tag() -> Int64 = 7\n  end\n  fact pick(String)\n  \
           operation same(a: Type, b: Type) -> Bool = anthill.prelude.PartialEq.eq(a, b)\n  \
           rule value(?r) :- pick(?a), ?t <=> (if true then Box[V = (?a) -> Int64] else Box[V = Int64]),\n    \
             same(?t, Box[V = (String) -> Int64]), ?r <=> 1",
        1,
    );
}

/// WI-20261011-3HN0N's reading reaches the text under an `if`: a tuple an equation leaves
/// there is the constructor an operation body writes.
#[test]
fn a_tuple_an_equation_leaves_under_an_if_runs() {
    assert_answers(
        "eqtuple",
        "  operation both(a: Int64) -> (Int64, Int64)\n  \
           rule both(?a) <=> (?a, ?a) @[simp]\n  \
           rule value(?r) :- ?r <=> (if true then fstof(both(4)) else 0)",
        4,
    );
}

/// A form that raises has no value: the answer is conditional, and the fault names the
/// form and its repair.
#[test]
fn a_match_that_raises_is_reported_by_its_form() {
    let (sols, messages) = resolve_with_messages(
        &ns("raises", "  rule value(?r) :- ?r <=> (match 3 case 1 -> 1)"),
        "test.raises.value(?r)",
    );
    assert!(
        sols.iter().all(|s| !s.is_definite()),
        "a raise is no definite answer"
    );
    assert!(
        messages.iter().any(|m| m.starts_with("the `match` written in a rule body")
            && m.contains("raised match_failed")
            && m.contains("Handle it inside the expression")),
        "{messages:?}"
    );
}

// ── the reflect constructor written as a call is data ──────────────────────────

/// `anthill.reflect.Expr.if_expr(…)` builds the node the syntax builds, and is an entity
/// construction: it is destructured, not run.
#[test]
fn a_reflect_if_constructor_bound_by_unify_is_data() {
    assert_answers(
        "reflif",
        "  rule value(?r) :- ?y <=> anthill.reflect.Expr.if_expr(cond: true, then_branch: 1, else_branch: 2),\n    \
             anthill.reflect.Expr.if_expr(cond: ?c, then_branch: ?r, else_branch: ?e) <=> ?y",
        1,
    );
}

/// Typed as data: its condition is no `Bool` position.
#[test]
fn a_reflect_if_constructor_is_not_typed_as_code() {
    assert_answers(
        "reflty",
        "  rule value(?r) :- ?y <=> anthill.reflect.Expr.if_expr(cond: 3, then_branch: 1, else_branch: 2),\n    \
             anthill.reflect.Expr.if_expr(cond: ?c, then_branch: ?r, else_branch: ?e) <=> ?y",
        1,
    );
}

// ── typed as the operation body it is evaluated as ──────────────────────────────

#[test]
fn an_if_whose_condition_is_not_bool_is_refused() {
    assert_refused(
        "badcond",
        "  rule value(?r) :- ?r <=> (if 3 then 1 else 2)",
        "expected Bool, got Int64",
    );
}

#[test]
fn an_if_whose_condition_is_a_clause_variable_of_another_type_is_refused() {
    assert_refused(
        "badcondvar",
        "  rule value(?r) :- ?c <=> 3, ?r <=> (if ?c then 1 else 2)",
        "expected Bool, got Int64",
    );
}

#[test]
fn an_if_whose_branches_disagree_is_refused() {
    assert_refused(
        "badbranches",
        "  rule value(?r) :- ?r <=> (if true then 1 else \"a\")",
        "expected Int64, got String",
    );
}

/// Refused either way: the walk that entered an `if` found the call, the typer's own
/// visit finds it now.
#[test]
fn an_effectful_call_under_an_if_is_refused() {
    assert_refused(
        "effect",
        "  operation stamp() -> String effects {Clock} = now()\n  \
           rule value(?r) :- ?r <=> (if true then stamp() else \"x\")",
        "performs `Clock`, and a rule body performs no effect",
    );
}

// ── an in-body proof ────────────────────────────────────────────────────────────

#[test]
fn an_in_body_proof_in_a_rule_body_is_refused() {
    assert_refused(
        "prf",
        "  rule trivial(?x) :- true\n  \
           rule value(?r) :- ?r <=> (proof trivial by derivation end 7)",
        "an in-body proof stands in an operation or const body",
    );
}

#[test]
fn an_in_body_proof_under_an_if_in_a_rule_body_is_refused() {
    assert_refused(
        "prfif",
        "  rule trivial(?x) :- true\n  \
           rule value(?r) :- ?r <=> (if true then (proof trivial by derivation end 7) else 0)",
        "an in-body proof stands in an operation or const body",
    );
}

/// An equation's right-hand side is spliced into the bodies it rewrites, an operation's
/// among them, and is no rule body: it may hold a proof.
#[test]
fn an_in_body_proof_in_an_equations_right_hand_side_is_admitted() {
    assert_answers(
        "prfeq",
        "  rule trivial(?x) :- true\n  \
           operation f(x: Int64) -> Int64\n  \
           rule f(?x) <=> (proof trivial by derivation end ?x) @[simp]\n  \
           operation g() -> Int64 = f(4)\n  \
           rule value(?r) :- ?r <=> g()",
        4,
    );
}

/// The controls: an operation body keeps its proofs, in control flow and nested in an
/// expression alike (the user, 2026-10-26: allowing the nested one or not does not matter).
#[test]
fn an_operation_body_keeps_its_proofs() {
    let src = ns(
        "prfop",
        "  rule trivial(?x) :- true\n  \
           operation inLet() -> Int64 =\n    let a = 1\n    proof trivial by derivation end\n    a + 6\n  \
           operation inArg() -> Int64 = inc(proof trivial by derivation end 7)\n  \
           operation nested() -> Int64 = inc((proof trivial by derivation end 7))",
    );
    assert_eq!(run_int64(&src, "test.prfop.inLet"), Ok(7));
    assert_eq!(run_int64(&src, "test.prfop.inArg"), Ok(8));
    assert_eq!(run_int64(&src, "test.prfop.nested"), Ok(8));
}

// ── the operation-body twin ─────────────────────────────────────────────────────

#[test]
fn an_operations_if_reached_from_a_rule_runs() {
    assert_answers(
        "twin",
        "  operation pick(c: Bool) -> Int64 = if c then 10 else 20\n  \
           rule value(?r) :- ?r <=> inc(pick(true))",
        11,
    );
}

// ── the ledger ──────────────────────────────────────────────────────────────────
//
// Measured 2026-10-26, one back-out at a time, over this file and
// wi_fc2x4_lambda_in_a_rule_test (52 rows; the type-argument row was added after, and its
// back-out measured beside wi_tcsgt_structural_bracket_entry_test).
//
//   THE EVALUATION — `evaluate::evaluated_form` answering `None`, so the form is a
//   computation to no consumer: 32 rows FAIL, every value, comparison, argument and
//   variable row of this file (the form is bound as written, compared as data, handed to
//   the callee as a node), `a_match_that_raises_is_reported_by_its_form` and the
//   equation row with them.
//
//   THE `if` TYPED WHOLE — `if` left out of `call_dispatch_shape`'s compound arm, the walk
//   entering it under `TypingEnv::under` as before: 3 FAIL, the two condition rows and the
//   branch row, which load.
//
//   THE PROOF REFUSAL — no `LoadError::ProofInClause`: 2 FAIL, the two proof rows.
//
//   `?x` UNDER A BINDER — `load_op_body_var` reading `?x` as the binder `x` in a rule's
//   compound expression too: 4 FAIL, the four rows of that name; the row over `?y` is their
//   control and passes.
//
//   THE SYNTAX BIT — `NodeOccurrence::is_compound_syntax` not asked, so a reflect
//   constructor written as a call is read as the syntax: 2 FAIL, the two reflect rows (the
//   one bound by `<=>` is evaluated to `1`, the other refused as an `if` whose condition is
//   no `Bool`).
//
//   THE TYPE ARGUMENT READ THROUGH THE VIEW — `Interpreter::expect_type_arg` taking a
//   `Value::Term` alone, as before: 2 FAIL,
//   a_type_rebuilt_over_a_clause_variable_under_an_if_is_a_type_argument and
//   wi_tcsgt_structural_bracket_entry_test::an_entry_under_a_rules_let_and_if_is_the_type,
//   each conditional (the run refused "expected Type (a type argument), got Entity").
//
//   THE PROOF IN AN EQUATION'S RIGHT-HAND SIDE — the refusal asked there too: 1 FAILS,
//   an_in_body_proof_in_an_equations_right_hand_side_is_admitted (refused, where the
//   parent answered 4).
//
//   A HEAD PARAMETER IN A FORM — `load_var_ref` not reading `rule_param_vars`: 2 FAIL, the
//   two head-parameter rows, refused "unresolved name 'x'" as on the parent;
//   a_binder_shadows_a_head_parameter_of_its_name is their control and passes.
//
//   PASS under every back-out, by design: a_let_in_a_goals_argument_meets_no_other_fact,
//   an_effectful_call_under_an_if_is_refused (the walk that entered an `if` found the call
//   before), an_operation_body_keeps_its_proofs, an_operations_if_reached_from_a_rule_runs;
//   and every row of wi_fc2x4_lambda_in_a_rule_test, which reads the stored forms.

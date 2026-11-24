//! WI-20261124-C6VN0 — A QUERY'S TYPED VARIABLE TYPES ITS VARIABLE, AND A `LogicalQuery` VALUE
//! WRITES ONE (kernel-language §5.3; proposal 010.1 §3.1 and Q2).
//!
//! A caller that builds a query term to term puts value terms where a clause had typed
//! expressions, and a value term carries what its constructor fixes and no more: `nil` says no
//! element type, so `PartialEq.eq(nil, nil)` was refused, `PartialEq[T = List.T]` nothing fixing
//! the element. A query's typed variable `?x: T` added a guard and checked its columns, and the
//! typer never read the variable at `T`: `PartialEq.eq(?xs: List[Int64], ?ys: List[Int64])` was
//! refused the same way, the annotation written at the very call. And a `LogicalQuery` value
//! had no way to write a typed variable at all.
//!
//! Now `?x: T` is read as a rule head's bound is read in its body — the typer reads `?x` at `T`
//! in the goal it is written in — and `typed_query(var: ?x, type: T, query: q)` is `?x: T`
//! written in `q`. A caller keeps a variable where the expression was, gives it the type the
//! declaration has, and binds it to the value: `?xs <=> nil`.
//!
//! Every value row is driven from outside the crate: the goals are built at run time
//! (`run_time_goals`, typed by no load), the declared types are read off the operation's
//! `OperationInfo` parameters as a caller outside the crate reads them, a `LogicalQuery` value is
//! built, and it is handed to `execute_typed_logical_query_with` / `refute_typed_logical_query_with`.
//!
//! BACK-OUTS: measured, listed at the end of this file.

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::execute::{ExecuteOptions, LowerError, Refutation};
use anthill_core::kb::load::QueryPattern;
use anthill_core::kb::node_occurrence::{for_each_child, Expr};
use anthill_core::kb::reflect_reader::read_operations;
use anthill_core::kb::term::Var;
use anthill_core::kb::term_view::TermView;
use anthill_core::kb::KnowledgeBase;
use anthill_core::persistence::print::TermPrinter;

use crate::common::{load_kb_with, query_goals, run_time_goals};

const SRC: &str = r#"
namespace c6vn0
  import anthill.prelude.{Int64, Bool, String, List, PartialEq, Eq}
  import anthill.prelude.List.{cons, nil}

  -- A sort whose own `eq` is not its structure: two points are equal by `x` alone.
  sort Pt
    entity pt(x: Int64, y: Int64)
    operation eq(a: Self, b: Self) -> Bool =
      match a
        case pt(ax, _) ->
          match b
            case pt(bx, _) -> PartialEq.eq(ax, bx)
    provides PartialEq[Self]
    provides Eq[Self]
  end

  -- The declarations a caller reads the types off: `xs = ys`, the clause anthill-traces checks.
  sort Ops
    operation same(xs: List[Int64], ys: List[Int64]) -> Bool
      requires (xs = ys)
    operation samePt(a: Pt, b: Pt) -> Bool
      requires (a = b)
    operation kinds(i: Int64, s: String, ss: List[String]) -> Bool
  end

  -- Binds nothing and fixes no type: each column is the argument's own.
  rule bind(?x, ?x) :- true
end
"#;

const L: &str = "anthill.prelude.List[T = anthill.prelude.Int64]";
const NIL: &str = "anthill.prelude.List.nil";
const ONE: &str = "anthill.prelude.List.cons(head: 1, tail: anthill.prelude.List.nil)";
const EQ: &str = "anthill.prelude.PartialEq.eq";

fn sym(kb: &KnowledgeBase, qn: &str) -> Symbol {
    kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("`{qn}` resolves"))
}

fn entity(kb: &mut KnowledgeBase, qn: &str, fields: Vec<(&str, Value)>) -> Value {
    let functor = sym(kb, qn);
    let named: Vec<(Symbol, Value)> = fields.into_iter().map(|(f, v)| (kb.intern(f), v)).collect();
    Value::Entity {
        functor,
        pos: Vec::new().into(),
        named: named.into(),
    }
}

/// The type `Ops.<op>` declares for its parameter `param`, read off its `OperationInfo` record —
/// the route a caller outside the crate has to a declaration's types.
fn declared(kb: &mut KnowledgeBase, op: &str, param: &str) -> Value {
    let ops = sym(kb, "c6vn0.Ops");
    let records = read_operations(kb, ops).expect("Ops' operations read");
    let name_key = kb.intern("name");
    let type_key = kb.intern("type_name");
    for record in records {
        let name = TermPrinter::new(kb).print_term(record.name);
        if name.trim_matches('"').rsplit('.').next() != Some(op) {
            continue;
        }
        for p in &record.params {
            let Some(written) = TermView::named_arg(p, kb, name_key).map(|c| c.to_value()) else {
                continue;
            };
            if TermPrinter::new(kb).print_value(&written).trim_matches('"') == param {
                return TermView::named_arg(p, kb, type_key)
                    .map(|c| c.to_value())
                    .unwrap_or_else(|| panic!("`{op}.{param}` has a type"));
            }
        }
    }
    panic!("`Ops.{op}` declares `{param}`")
}

/// The goals `patterns`, built at run time and typed by no load, sharing their variables.
fn goals(kb: &mut KnowledgeBase, patterns: &[&str]) -> Vec<QueryPattern> {
    run_time_goals(kb, patterns)
}

/// The variable `?name` of `goals`, as the value a caller puts in `typed_query`'s `var`.
fn var(kb: &KnowledgeBase, goals: &[QueryPattern], name: &str) -> Value {
    let mut stack: Vec<QueryPattern> = goals.to_vec();
    while let Some(n) = stack.pop() {
        let Some(expr) = n.as_expr() else { continue };
        if let Expr::Var(Var::Global(vid)) = expr {
            if kb.local_name_of(vid.name()) == name {
                return Value::Var(Var::Global(*vid));
            }
        }
        for_each_child(expr, |c| stack.push(c.clone()));
    }
    panic!("the goals hold `?{name}`")
}

/// One `pattern_query` per goal, joined by `conjunction`.
fn conj(kb: &mut KnowledgeBase, goals: &[QueryPattern]) -> Value {
    let mut parts: Vec<Value> = goals
        .iter()
        .map(|g| entity(kb, "anthill.reflect.LogicalQuery.pattern_query", vec![("term", Value::Node(g.clone()))]))
        .collect();
    let mut q = parts.pop().expect("a query has a goal");
    while let Some(left) = parts.pop() {
        q = entity(kb, "anthill.reflect.LogicalQuery.conjunction", vec![("left", left), ("right", q)]);
    }
    q
}

fn typed(kb: &mut KnowledgeBase, var: Value, ty: Value, query: Value) -> Value {
    entity(
        kb,
        "anthill.reflect.LogicalQuery.typed_query",
        vec![("var", var), ("type", ty), ("query", query)],
    )
}

fn wrap(kb: &mut KnowledgeBase, ctor: &str, fields: Vec<(&str, Value)>) -> Value {
    entity(kb, &format!("anthill.reflect.LogicalQuery.{ctor}"), fields)
}

/// The definite answers of `q` through the typed execute, or its refusal.
fn answers(kb: &mut KnowledgeBase, q: &Value) -> Result<usize, LowerError> {
    let mut stream = kb.execute_typed_logical_query_with(q, &ExecuteOptions::default())?;
    let mut definite = 0;
    while let Some(answer) = stream.next_solution(kb).expect("the search does not fault") {
        if !answer.is_definite() {
            let r: Vec<String> = answer.residual.iter().map(|v| TermPrinter::new(kb).print_value(v)).collect();
            panic!("every answer is definite; residual {r:?}");
        }
        definite += 1;
    }
    Ok(definite)
}

/// The verdict of `q` through the typed refutation: `"answered"`, `"refuted"`, or the undecided cause.
fn verdict(kb: &mut KnowledgeBase, q: &Value) -> String {
    match kb.refute_typed_logical_query_with(q, &ExecuteOptions::default()) {
        Err(e) => format!("refused: {e}"),
        Ok(outcome) => match outcome.verdict {
            Refutation::Answered(_) => "answered".to_string(),
            Refutation::Refuted(_) => "refuted".to_string(),
            Refutation::Undecided(u) => format!("undecided: {u:?}"),
        },
    }
}

/// `?xs <=> a, ?ys <=> b, PartialEq.eq(?xs, ?ys)`, each variable declared at `same`'s parameter
/// type — `requires (xs = ys)` decided term to term, the variables standing for the parameters.
fn same_query(kb: &mut KnowledgeBase, a: &str, b: &str) -> Value {
    let g = goals(kb, &[&format!("?xs <=> {a}"), &format!("?ys <=> {b}"), &format!("{EQ}(?xs, ?ys)")]);
    let (xs, ys) = (var(kb, &g, "xs"), var(kb, &g, "ys"));
    let (txs, tys) = (declared(kb, "same", "xs"), declared(kb, "same", "ys"));
    let body = conj(kb, &g);
    let inner = typed(kb, ys, tys, body);
    typed(kb, xs, txs, inner)
}

/// Row (1): two empty lists declared `List[Int64]` are equal — the comparison is typed at the
/// declared type, and holds, through the typed execute and the refutation alike.
#[test]
fn two_empty_lists_declared_are_equal() {
    let mut kb = load_kb_with(SRC);
    let q = same_query(&mut kb, NIL, NIL);
    assert_eq!(answers(&mut kb, &q).expect("the query types"), 1);
    assert_eq!(verdict(&mut kb, &q), "answered");
}

/// Row (2): an empty list and `[1]`, declared `List[Int64]`, are not equal: no answer, and the
/// refutation is complete — violated, not undecided.
#[test]
fn an_empty_list_and_a_list_of_one_declared_differ() {
    let mut kb = load_kb_with(SRC);
    let q = same_query(&mut kb, NIL, ONE);
    assert_eq!(answers(&mut kb, &q).expect("the query types"), 0);
    assert_eq!(verdict(&mut kb, &q), "refuted");
}

/// Row (3): operands declared at a sort with an `eq` of its own are compared by it, not by their
/// structure: `pt(1, 2)` and `pt(1, 9)` are equal as `Pt`s (by `x`) and differ structurally —
/// the same two values under `===` are refuted, the control that the eq that decided is `Pt`'s.
/// A value of such a sort names it in its constructor, so here the declaration and the value
/// agree; what the row pins is that the declared type routes the comparison to the sort's own
/// member and no structural reading stands in for it.
#[test]
fn a_sort_declared_with_its_own_eq_is_compared_by_it() {
    let mut kb = load_kb_with(SRC);
    let (p1, p2) = ("c6vn0.Pt.pt(x: 1, y: 2)", "c6vn0.Pt.pt(x: 1, y: 9)");
    for (compare, expected) in [(format!("{EQ}(?a, ?b)"), "answered"), ("?a === ?b".to_string(), "refuted")] {
        let g = goals(&mut kb, &[&format!("?a <=> {p1}"), &format!("?b <=> {p2}"), &compare]);
        let (a, b) = (var(&kb, &g, "a"), var(&kb, &g, "b"));
        let (ta, tb) = (declared(&mut kb, "samePt", "a"), declared(&mut kb, "samePt", "b"));
        let body = conj(&mut kb, &g);
        let inner = typed(&mut kb, b, tb, body);
        let q = typed(&mut kb, a, ta, inner);
        assert_eq!(verdict(&mut kb, &q), expected, "`{compare}` over pt(1, 2) and pt(1, 9) as `Pt`s");
    }
}

/// Row (4): a declared type the value does not fit is refused where the query is read, not
/// ignored: `?xs` declared `List[Int64]` and bound to `["a"]`. So is a `typed_query` whose `var`
/// is a value rather than a variable, and one handed to the face no typer reads, which would
/// drop the type.
#[test]
fn a_declared_type_the_value_does_not_fit_is_refused() {
    let mut kb = load_kb_with(SRC);
    let q = same_query(&mut kb, "[\"a\"]", NIL);
    match answers(&mut kb, &q) {
        Err(LowerError::QueryRefused(detail)) => assert!(
            detail.contains("`?xs` at the type its column holds"),
            "the misfit names the variable; got {detail}"
        ),
        other => panic!("`[\"a\"]` declared `List[Int64]` is refused; got {other:?}"),
    }

    let g = goals(&mut kb, &[&format!("{EQ}({NIL}, {NIL})")]);
    let l = declared(&mut kb, "same", "xs");
    let body = conj(&mut kb, &g);
    let not_a_var = Value::Node(g[0].clone());
    let q = typed(&mut kb, not_a_var, l, body);
    assert!(
        matches!(answers(&mut kb, &q), Err(LowerError::TypedQueryNotAVariable { .. })),
        "a value in `var` is refused"
    );

    let q = same_query(&mut kb, NIL, NIL);
    assert!(
        matches!(kb.execute_logical_query(&q), Err(LowerError::TypedQueryUntyped)),
        "the untyped face refuses a typed variable"
    );
}

/// Row (5), the control: the same queries with no declared type type and answer as before —
/// two empty lists, by variables or written in place, are refused (nothing fixes the element),
/// and two lists of one compare and hold.
#[test]
fn without_a_declared_type_the_queries_answer_as_before() {
    let mut kb = load_kb_with(SRC);
    let g = goals(&mut kb, &[&format!("?xs <=> {NIL}"), &format!("?ys <=> {NIL}"), &format!("{EQ}(?xs, ?ys)")]);
    let q = conj(&mut kb, &g);
    assert!(
        matches!(answers(&mut kb, &q), Err(LowerError::QueryRefused(ref d)) if d.contains("PartialEq")),
        "two empty lists with no type are refused"
    );
    let g = goals(&mut kb, &[&format!("{EQ}({NIL}, {NIL})")]);
    let q = conj(&mut kb, &g);
    assert!(matches!(answers(&mut kb, &q), Err(LowerError::QueryRefused(_))), "`eq(nil, nil)` is refused");
    let g = goals(&mut kb, &[&format!("{EQ}({ONE}, {ONE})")]);
    let q = conj(&mut kb, &g);
    assert_eq!(answers(&mut kb, &q).expect("`eq([1], [1])` types"), 1);
}

/// The written form reads the type as the value form does: `?xs: List[Int64]` at the very call
/// types the comparison, its operands bound to `nil` by goals that fix no type.
#[test]
fn a_written_typed_variable_types_the_call() {
    let mut kb = load_kb_with(SRC);
    for (ys, expected) in [(NIL, 1), (ONE, 0)] {
        let patterns = [
            format!("c6vn0.bind(?xs, {NIL})"),
            format!("c6vn0.bind(?ys, {ys})"),
            format!("{EQ}(?xs: {L}, ?ys: {L})"),
        ];
        let patterns: Vec<&str> = patterns.iter().map(String::as_str).collect();
        let g = query_goals(&mut kb, &patterns);
        let sols = kb.resolve(&g, &anthill_core::kb::resolve::ResolveConfig::default());
        assert_eq!(sols.iter().filter(|s| s.is_definite()).count(), expected, "ys = {ys}");
        assert_eq!(sols.len(), expected, "ys = {ys}: every answer definite");
    }
}

/// A typed variable types the goal it is written in and no other: under `negation` it types the
/// negand, and two branches of `disjunction` may each type one variable, each read at its own —
/// an `Int64` compared in one and a `Pt` by `Pt.eq` in the other. Read at one branch's type in
/// both, the `Pt` comparison would be refused.
#[test]
fn a_typed_variable_types_its_own_branch() {
    let mut kb = load_kb_with(SRC);
    let g = goals(
        &mut kb,
        &[
            "?x <=> 1",
            &format!("{EQ}(?x, 1)"),
            "?x <=> c6vn0.Pt.pt(x: 1, y: 2)",
            &format!("{EQ}(?x, c6vn0.Pt.pt(x: 1, y: 9))"),
        ],
    );
    let x = var(&kb, &g, "x");
    let (int, pt) = (declared(&mut kb, "kinds", "i"), declared(&mut kb, "samePt", "a"));
    let left = conj(&mut kb, &g[..2]);
    let right = conj(&mut kb, &g[2..]);
    let left = typed(&mut kb, x.clone(), int, left);
    let right = typed(&mut kb, x, pt, right);
    let q = wrap(&mut kb, "disjunction", vec![("left", left), ("right", right)]);
    assert_eq!(answers(&mut kb, &q).expect("each branch types at its own type"), 2);

    // Under `negation`: `?l <=> [], ?m <=> [1], not(eq(?l, ?m))`, `?l` and `?m` declared
    // `List[Int64]` inside the negand, which is where the comparison is typed. Bound outside, as
    // a negand's variables must be when `not` runs (a free one flounders).
    let g = goals(&mut kb, &[&format!("?l <=> {NIL}"), &format!("?m <=> {ONE}"), &format!("{EQ}(?l, ?m)")]);
    let (l, m) = (var(&kb, &g, "l"), var(&kb, &g, "m"));
    let (tl, tm) = (declared(&mut kb, "same", "xs"), declared(&mut kb, "same", "ys"));
    let binds = conj(&mut kb, &g[..2]);
    let compare = conj(&mut kb, &g[2..]);
    let inner = typed(&mut kb, m, tm, compare);
    let negand = typed(&mut kb, l, tl, inner);
    let negation = wrap(&mut kb, "negation", vec![("query", negand)]);
    let q = wrap(&mut kb, "conjunction", vec![("left", binds), ("right", negation)]);
    assert_eq!(answers(&mut kb, &q).expect("the negand types"), 1, "`[] = [1]` fails, so its negation holds");
}

/// A variable is read at one type where it is read: two types for it whose goals meet — one
/// `typed_query` inside another, or two written at the top of a query — are refused, naming
/// both types.
#[test]
fn a_variable_given_two_types_where_they_meet_is_refused() {
    let mut kb = load_kb_with(SRC);
    let g = goals(&mut kb, &["c6vn0.bind(?x, 1)"]);
    let x = var(&kb, &g, "x");
    let (int, s) = (declared(&mut kb, "kinds", "i"), declared(&mut kb, "kinds", "s"));
    let body = conj(&mut kb, &g);
    let inner = typed(&mut kb, x.clone(), s, body);
    let q = typed(&mut kb, x, int, inner);
    match answers(&mut kb, &q) {
        Err(LowerError::QueryRefused(detail)) => assert!(
            detail.contains("`?x` at one type where it is read"),
            "the clash names the variable; got {detail}"
        ),
        other => panic!("two types for `?x`, one inside the other, are refused; got {other:?}"),
    }

    let patterns = [
        "c6vn0.bind(?x: anthill.prelude.Int64, 1)",
        "c6vn0.bind(?x: anthill.prelude.String, 1)",
    ];
    let src: String = patterns.iter().map(|p| format!("fact {p}\n")).collect();
    let parsed = anthill_core::parse::parse(&src).expect("the goals parse");
    let errs = anthill_core::kb::load::scan_query_definitions(&mut kb, &[&parsed]);
    assert!(errs.is_empty(), "the goals scan: {errs:?}");
    let ids: Vec<_> = parsed
        .items
        .iter()
        .filter_map(|item| match item {
            anthill_core::parse::ir::Item::Fact(f) => Some(f.term),
            _ => None,
        })
        .collect();
    let scope = kb.global_scope();
    let mut var_map = std::collections::HashMap::new();
    let refused = anthill_core::kb::load::convert_query_terms(&mut kb, &parsed, &ids, scope, &mut var_map)
        .err()
        .map(|errs| errs.iter().map(|e| e.to_string()).collect::<Vec<_>>())
        .unwrap_or_default();
    assert!(
        refused.iter().any(|e| e.contains("`?x` at one type where it is read")),
        "two types for `?x` at the top of a written query are refused; got {refused:?}"
    );
}

// BACK-OUTS, measured 2026-11-24 on a temporary binary holding this file and
// `wi_cbrd2_typed_query_variable_test` (whose 11 rows pass under every switch), each part
// switched off in one build and the switches then removed. The control, no switch: all pass.
//
// * the type not stamped on the variable (`stamp_typed_variable_types`' last loop):
//   [`two_empty_lists_declared_are_equal`], [`a_written_typed_variable_types_the_call`] and
//   [`a_typed_variable_types_its_own_branch`] — each refused, nothing fixing the element;
// * the clash not refused (`stamp_typed_variable_types`' pair check):
//   [`a_variable_given_two_types_where_they_meet_is_refused`];
// * a call read at the query's first type for the name instead of its own occurrences' (the
//   per-call env in `typed_spec_op_calls`): [`a_typed_variable_types_its_own_branch`], the `Pt`
//   branch refused at `Int64`;
// * the untyped face not refusing it (`execute_logical_query`):
//   [`a_declared_type_the_value_does_not_fit_is_refused`];
// * `typed_query` not lowered (`lower_query_with`'s arm; the value is then no `LogicalQuery`
//   constructor): every row that builds one — six.
//
// Passing either way BY DESIGN: [`an_empty_list_and_a_list_of_one_declared_differ`] and
// [`a_sort_declared_with_its_own_eq_is_compared_by_it`] without the stamp — `[1]` bound to `?ys`
// fixes the element for the comparison, and a `Pt` value names its sort — so each rests on the
// lowering alone; [`a_declared_type_the_value_does_not_fit_is_refused`] without the stamp, the
// column check (WI-20261105-CBRD2) refusing the misfit; and
// [`without_a_declared_type_the_queries_answer_as_before`] under every switch, being the control.

//! WI-20261109-5BP39 (proposal 051 Phase 2, 2 of 4) — every scalar carrier supplies its
//! `eq`, and a typed call at one is pinned to it as any member is.
//!
//! Before, `PartialEq.eq` was `@[host_implemented]` at the SPEC (`partial_eq_eq` →
//! `semantic_equal`), and a typed call at `Int64` recorded no pin: the call ran the
//! value-directed host code — IEEE for a `Float` pair, reflexivity, the equality index,
//! raw structure — and the rule-body goal ran the resolver's `SemEq` the same way.
//! Measured on 356ce140 with a trace in `builtin_eq`: `PartialEq.eq(1, 1)` in an operation
//! body reached it; a rule goal `PartialEq.eq(1, 1, ?r)` stayed `Unclassified`.
//!
//! Now (1) `Int64`, `BigInt`, `String`, `Bool` declare `eq`, mapped to `literal_eq`, and
//! `Float` declares it mapped to `float_eq` (IEEE); `Symbol` and `Type`, which have no sort
//! body to declare a member in, bind theirs on the provision (`eq = symbolEq`, `eq =
//! typeEq`, each `a === b`); (2) `PartialEq.eq`'s primitive is `BuiltinTag::ScalarEq`,
//! which `derive_carrier_builtin_tags` gives each scalar member, so a rule goal pinned to
//! `Int64.eq` runs it; (3) the spec declares no implementation: a goal written at arity + 1
//! (`eq(a, b, ?r)`) was read as a relation goal while the spec was host-mapped (its clause
//! set holds every stored equation), and is typed and pinned now; (4) a call that reaches
//! the spec operation with no member — one no type reaches, a host call, one at a composite
//! with no `eq` of its own — is compared by its values in the interpreter
//! (`Interpreter::eq_spec_op`, both entries), as the resolver's `SemEq` compares the goal.
//!
//! ## Back-out
//!
//! Measured 2026-11-09, one part at a time, the rest of the tree kept, over this file and
//! the wi616, wi625, wi645, wi664 and wi_tsys6 rows:
//!
//! - the scalar members out (their declarations and mappings): the calls are left
//!   unclassified, and `an_operation_body_runs_the_scalar_member` and
//!   `a_rule_goal_runs_the_scalar_member` fail;
//! - the spec host-implemented again (`@[host_implemented]`, `eq: "partial_eq_eq"` and its
//!   `HOST_FNS` row): the goals written at arity + 1 are unclassified, and
//!   `a_rule_goal_runs_the_scalar_member` fails;
//! - the interpreter's route out (both arms on `eq_spec_op`): a call reaching the spec
//!   operation dies `OperationBodyMissing` — `a_composite_with_no_eq_of_its_own_compares_by_value`,
//!   seven wi625 rows, five wi664 rows, wi645's `totalfloat_eq_is_lawful_reflexive_on_nan`
//!   and wi_tsys6's `a_non_ground_operand_is_undecided` fail;
//! - the `Symbol` / `Type` bindings out: `symbol_and_type_run_their_bound_eq` fails, the
//!   calls left to the spec operation.
//!
//! PASS EITHER WAY, BY DESIGN: which primitive a pinned scalar goal runs (`ScalarEq` or the
//! spec's `SemEq`) moves no verdict — at a scalar the value-directed cascade answers what
//! the member answers. The rows hold the pin, which is what the typed route changes, and
//! the values, which it must keep.

use anthill_core::eval::{Interpreter, Value};
use anthill_core::kb::node_occurrence::{for_each_child, ApplyDispatch, Expr, NodeOccurrence};
use anthill_core::kb::term::Term;
use anthill_core::kb::KnowledgeBase;
use std::rc::Rc;

use crate::common::{interp_for, query_unary};

const EQ: &str = "anthill.prelude.PartialEq.eq";

/// What the typer decided for each call of `PartialEq.eq` under `roots`: the operation it
/// runs, or `None` for a call left unclassified.
fn decided(kb: &KnowledgeBase, roots: &[Rc<NodeOccurrence>]) -> Vec<Option<String>> {
    let mut out = Vec::new();
    let mut stack: Vec<Rc<NodeOccurrence>> = roots.to_vec();
    while let Some(o) = stack.pop() {
        let Some(expr) = o.as_expr() else { continue };
        if let Expr::Apply { functor, .. } = expr {
            if kb.qualified_name_of(*functor) == EQ {
                out.push(match o.apply_dispatch() {
                    ApplyDispatch::Pin(t) | ApplyDispatch::NeedsDict(t) => {
                        Some(kb.qualified_name_of(t).to_string())
                    }
                    ApplyDispatch::Unclassified => None,
                });
            }
        }
        for_each_child(expr, |c| stack.push(Rc::clone(c)));
    }
    out
}

fn decided_in_op(kb: &KnowledgeBase, op: &str) -> Vec<Option<String>> {
    let sym = kb.try_resolve_symbol(op).unwrap_or_else(|| panic!("`{op}` resolves"));
    let body = kb.op_body_node(sym).unwrap_or_else(|| panic!("`{op}` has a body"));
    decided(kb, &[Rc::clone(body)])
}

fn decided_in_rule(kb: &KnowledgeBase, qn: &str) -> Vec<Option<String>> {
    let roots: Vec<Rc<NodeOccurrence>> = kb
        .rule_ids_by_qn(qn)
        .into_iter()
        .flat_map(|rid| kb.rule_body_nodes(rid).to_vec())
        .collect();
    decided(kb, &roots)
}

fn pinned(member: &str) -> Vec<Option<String>> {
    vec![Some(member.to_string())]
}

fn call_bool(interp: &mut Interpreter, op: &str, args: &[Value]) -> bool {
    match interp.call(op, args) {
        Ok(Value::Bool(b)) => b,
        other => panic!("`{op}`: expected a Bool, got {other:?}"),
    }
}

/// The one definite `Bool` the unary relation `qn` answers.
fn rule_bool(interp: &mut Interpreter, qn: &str) -> bool {
    match query_unary(interp.kb_mut(), qn).as_slice() {
        [(Value::Bool(b), true)] => *b,
        other => panic!("`{qn}`: expected one definite Bool, got {other:?}"),
    }
}

const NS: &str = "test.p5bp39";

fn scalar_program() -> String {
    format!(
        r#"namespace {NS}
  import anthill.prelude.{{Int64, Float, String, Bool, BigInt, PartialEq}}
  import anthill.prelude.Float.{{nan, neg}}
  import anthill.prelude.BigInt.{{to_bigint}}

  operation intApart() -> Bool = PartialEq.eq(1, 2)
  operation intSame(a: Int64) -> Bool = PartialEq.eq(a, a)
  operation floatNan() -> Bool = PartialEq.eq(nan, nan)
  operation floatZeros() -> Bool = PartialEq.eq(neg(0.0), 0.0)
  operation stringApart() -> Bool = PartialEq.eq("a", "b")
  operation boolApart() -> Bool = PartialEq.eq(true, false)
  operation bigSame() -> Bool = PartialEq.eq(to_bigint(7), to_bigint(7))

  rule intGoal(?r) :- PartialEq.eq(1, 2, ?r)
  rule floatNanGoal(?r) :- PartialEq.eq(nan, nan, ?r)
  rule floatZerosGoal(?r) :- PartialEq.eq(neg(0.0), 0.0, ?r)
  rule stringGoal(?r) :- PartialEq.eq("a", "a", ?r)
  rule boolGoal(?r) :- PartialEq.eq(true, false, ?r)
  rule intTest(?r: Int64) :- ?r <=> 1, ?r = 1
  rule floatTest(?r: Float) :- ?r <=> nan, not(?r = nan)
end
"#
    )
}

/// A typed call at each scalar carrier is pinned to the carrier's own `eq`, and answers what
/// the carrier's host function answers: IEEE for `Float` (`nan` apart from itself, the two
/// zeros equal). `intSame` is answered by `Eq`'s law at the member's entry. FAILS with the
/// members out (each pin `PartialEq.eq`); the values pass either way.
#[test]
fn an_operation_body_runs_the_scalar_member() {
    let mut interp = interp_for(&scalar_program());
    let kb = interp.kb();
    for (op, member) in [
        ("intApart", "anthill.prelude.Int64.eq"),
        ("intSame", "anthill.prelude.Int64.eq"),
        ("floatNan", "anthill.prelude.Float.eq"),
        ("floatZeros", "anthill.prelude.Float.eq"),
        ("stringApart", "anthill.prelude.String.eq"),
        ("boolApart", "anthill.prelude.Bool.eq"),
        ("bigSame", "anthill.prelude.BigInt.eq"),
    ] {
        assert_eq!(decided_in_op(kb, &format!("{NS}.{op}")), pinned(member), "{op}");
    }
    let mut at = |op: &str, args: &[Value]| call_bool(&mut interp, &format!("{NS}.{op}"), args);
    assert!(!at("intApart", &[]));
    assert!(at("intSame", &[Value::Int(5)]));
    assert!(!at("floatNan", &[]), "IEEE: nan is apart from itself");
    assert!(at("floatZeros", &[]), "IEEE: -0.0 equals 0.0");
    assert!(!at("stringApart", &[]));
    assert!(!at("boolApart", &[]));
    assert!(at("bigSame", &[]));
}

/// A rule goal at a scalar carrier — the call written with its result column, and `=` at a
/// typed variable — is pinned to the member and decided by its primitive. While the spec was
/// host-mapped a goal written at arity + 1 was read as a goal on the relation `PartialEq.eq`
/// — whose clauses are every stored equation — and left unclassified. FAILS with the members
/// out and with the spec host-implemented again (`intGoal`'s pin `None`); the values pass
/// either way.
#[test]
fn a_rule_goal_runs_the_scalar_member() {
    let mut interp = interp_for(&scalar_program());
    for (rule, member) in [
        ("intGoal", "anthill.prelude.Int64.eq"),
        ("floatNanGoal", "anthill.prelude.Float.eq"),
        ("floatZerosGoal", "anthill.prelude.Float.eq"),
        ("stringGoal", "anthill.prelude.String.eq"),
        ("boolGoal", "anthill.prelude.Bool.eq"),
        ("intTest", "anthill.prelude.Int64.eq"),
        ("floatTest", "anthill.prelude.Float.eq"),
    ] {
        assert_eq!(decided_in_rule(interp.kb(), &format!("{NS}.{rule}")), pinned(member), "{rule}");
    }
    assert!(!rule_bool(&mut interp, &format!("{NS}.intGoal")));
    assert!(!rule_bool(&mut interp, &format!("{NS}.floatNanGoal")), "IEEE: nan");
    assert!(rule_bool(&mut interp, &format!("{NS}.floatZerosGoal")), "IEEE: zeros");
    assert!(rule_bool(&mut interp, &format!("{NS}.stringGoal")));
    assert!(!rule_bool(&mut interp, &format!("{NS}.boolGoal")));
    let int_test = query_unary(interp.kb_mut(), &format!("{NS}.intTest"));
    assert!(matches!(int_test.as_slice(), [(Value::Int(1), true)]), "{int_test:?}");
    // `not(nan = nan)` holds: the goal is decided false, not undecided.
    let float_test = query_unary(interp.kb_mut(), &format!("{NS}.floatTest"));
    assert!(matches!(float_test.as_slice(), [(_, true)]), "{float_test:?}");
}

/// `Symbol` and `Type` are `sort X = ?`, with no body a member could be declared in, so each
/// binds its `eq` on the provision; a typed call is pinned to the binding. FAILS with the
/// bindings out (pinned to `PartialEq.eq`).
#[test]
fn symbol_and_type_run_their_bound_eq() {
    let src = format!(
        r#"namespace {NS}.st
  import anthill.prelude.{{Int64, Bool, PartialEq, Type, List}}
  import anthill.reflect.{{Symbol}}
  operation symbols(a: Symbol, b: Symbol) -> Bool = PartialEq.eq(a, b)
  operation types(a: Type, b: Type) -> Bool = PartialEq.eq(a, b)
  operation sameList() -> Bool = types(List[T = Int64], List[T = Int64])
  operation apart() -> Bool = types(Int64, Bool)
end
"#
    );
    let mut interp = interp_for(&src);
    let kb = interp.kb();
    assert_eq!(
        decided_in_op(kb, &format!("{NS}.st.symbols")),
        pinned("anthill.reflect.symbolEq")
    );
    assert_eq!(
        decided_in_op(kb, &format!("{NS}.st.types")),
        pinned("anthill.prelude.typeEq")
    );
    let sym = |interp: &mut Interpreter, qn: &str| {
        let s = interp.kb().try_resolve_symbol(qn).expect("resolves");
        Value::term(interp.kb_mut().alloc(Term::Ref(s)))
    };
    let int64 = sym(&mut interp, "anthill.prelude.Int64");
    let bool_ = sym(&mut interp, "anthill.prelude.Bool");
    let symbols = format!("{NS}.st.symbols");
    assert!(call_bool(&mut interp, &symbols, &[int64.clone(), int64.clone()]));
    assert!(!call_bool(&mut interp, &symbols, &[int64, bool_]));
    assert!(call_bool(&mut interp, &format!("{NS}.st.sameList"), &[]));
    assert!(!call_bool(&mut interp, &format!("{NS}.st.apart"), &[]));
}

/// A composite that writes no `eq` is given the one its equality derives (3 of 4,
/// WI-20261109-FEM1J), and a typed call is pinned to it. A host call reaches the spec
/// operation, which declares no implementation: its operands are compared by their values,
/// which reach the member through the equality index. FAILS with the interpreter's route
/// out: `OperationBodyMissing` for `PartialEq.eq`, at the host call.
#[test]
fn a_composite_with_no_eq_of_its_own_compares_by_value() {
    let src = format!(
        r#"namespace {NS}.bx
  import anthill.prelude.{{Int64, Bool, PartialEq}}
  sort Cell
    entity cell(n: Int64)
  end
  operation same() -> Bool = PartialEq.eq(cell(1), cell(1))
  operation apart() -> Bool = PartialEq.eq(cell(1), cell(2))
  operation one() -> Cell = cell(1)
end
"#
    );
    let mut interp = interp_for(&src);
    assert_eq!(
        decided_in_op(interp.kb(), &format!("{NS}.bx.same")),
        pinned(&format!("{NS}.bx.Cell.eq")),
        "the derived member"
    );
    assert!(call_bool(&mut interp, &format!("{NS}.bx.same"), &[]));
    assert!(!call_bool(&mut interp, &format!("{NS}.bx.apart"), &[]));
    let one = interp.call(&format!("{NS}.bx.one"), &[]);
    let one = one.unwrap_or_else(|e| panic!("cell(1): {e:?}"));
    assert!(call_bool(&mut interp, EQ, &[one.clone(), one]));
}

//! WI-577 — first-class runtime dictionaries + op-refs.
//!
//! The two runtime VIEW sorts `anthill.realization.runtime.Dictionary` /
//! `OpRef` — the anthill face of the runtime dispatch values
//! `Value::Requirement` / `Value::OpRef` — exposed as native builtins over the
//! `RequirementArena`. These tests build requirement dictionaries by hand (as
//! the interpreter does when reducing `construct_requirement`) and exercise
//! each accessor op through `Interpreter::call`, which dispatches straight to
//! the registered builtin.
//!
//! Reference: docs/design/requirement-dictionaries.md §2 (runtime sorts) / §2.4
//! (OpRef) / §4 (phasing).

use smallvec::SmallVec;

use anthill_core::eval::{Interpreter, Value};
use anthill_core::intern::Symbol;
use anthill_core::kb::term::Term;

mod common;

const DICT: &str = "anthill.realization.runtime.Dictionary";
const OPREF: &str = "anthill.realization.runtime.OpRef";

fn interp() -> Interpreter {
    // Stdlib alone (with the eval builtins registered) — we construct the
    // requirement values by hand.
    common::interp_for("namespace test.wi577.empty\nend\n")
}

fn resolve(interp: &Interpreter, qn: &str) -> Symbol {
    interp
        .kb()
        .try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("symbol {qn} not found in KB"))
}

/// Build a `Symbol` runtime value (a `Ref` term) for a qualified name — the
/// representation `impl` / `op` return and `resolveOp` consumes.
fn sym_val(interp: &mut Interpreter, qn: &str) -> Value {
    let s = resolve(interp, qn);
    Value::term(interp.kb_mut().alloc(Term::Ref(s)))
}

/// The qualified name of a `Symbol` runtime value.
fn sym_qn(interp: &Interpreter, v: &Value) -> String {
    match v {
        Value::Term { id, .. } => match interp.kb().get_term(*id) {
            Term::Ref(s) | Term::Ident(s) => interp.kb().qualified_name_of(*s).to_string(),
            other => panic!("expected a Ref/Ident Symbol term, got {other:?}"),
        },
        other => panic!("expected a Symbol (Term) value, got {}", other.type_name()),
    }
}

fn named_field<'a>(interp: &Interpreter, named: &'a [(Symbol, Value)], short: &str) -> &'a Value {
    named
        .iter()
        .find(|(k, _)| {
            let qn = interp.kb().qualified_name_of(*k);
            qn.rsplit('.').next().unwrap_or(qn) == short
        })
        .map(|(_, v)| v)
        .unwrap_or_else(|| panic!("named field '{short}' not found"))
}

fn expect_int(v: &Value) -> i64 {
    match v {
        Value::Int(n) => *n,
        other => panic!("expected Int, got {}", other.type_name()),
    }
}

// ── Dictionary.impl / arity / sub — the structural view ──────────────────────

#[test]
fn dictionary_impl_arity_sub() {
    let mut interp = interp();
    let int64 = resolve(&interp, "anthill.prelude.Int64");
    let bool_sym = resolve(&interp, "anthill.prelude.Bool");

    // parent{ Int64, subs = [ child{ Bool } ] }
    let child = interp.alloc_requirement(bool_sym, SmallVec::new());
    let mut subs: SmallVec<[_; 1]> = SmallVec::new();
    subs.push(child);
    let dict = Value::Requirement(interp.alloc_requirement(int64, subs));

    // impl(d) — the resolved impl identity.
    let got = interp.call(&format!("{DICT}.impl"), &[dict.clone()]).unwrap();
    assert_eq!(sym_qn(&interp, &got), "anthill.prelude.Int64");

    // arity(d) — one sub-requirement.
    let got = interp.call(&format!("{DICT}.arity"), &[dict.clone()]).unwrap();
    assert_eq!(expect_int(&got), 1);

    // sub(d, 0) — the child dict (a Requirement); impl(child) == Bool, arity 0.
    let child_dict = interp.call(&format!("{DICT}.sub"), &[dict.clone(), Value::Int(0)]).unwrap();
    assert!(matches!(child_dict, Value::Requirement(_)), "sub must return a Dictionary handle");
    let child_impl = interp.call(&format!("{DICT}.impl"), &[child_dict.clone()]).unwrap();
    assert_eq!(sym_qn(&interp, &child_impl), "anthill.prelude.Bool");
    let child_arity = interp.call(&format!("{DICT}.arity"), &[child_dict]).unwrap();
    assert_eq!(expect_int(&child_arity), 0);

    // Out-of-range projection is a loud error, not an arena panic.
    let err = interp.call(&format!("{DICT}.sub"), &[dict, Value::Int(5)]);
    assert!(err.is_err(), "out-of-range sub must error");
}

// ── Dictionary.resolveOp → OpRef.op / OpRef.dict ─────────────────────────────

#[test]
fn resolve_op_real_impl_yields_callable_opref() {
    let mut interp = interp();
    let int64 = resolve(&interp, "anthill.prelude.Int64");

    // Int64 provides Eq — resolve `Eq.eq` against a Dictionary{Int64}.
    let eq_eq = sym_val(&mut interp, "anthill.prelude.Eq.eq");
    let dict = Value::Requirement(interp.alloc_requirement(int64, SmallVec::new()));
    let opref = interp.call(&format!("{DICT}.resolveOp"), &[dict, eq_eq]).unwrap();

    // The result carries the dispatch dict — so it stays callable.
    match &opref {
        Value::OpRef { dict, .. } => {
            assert!(dict.is_some(), "resolveOp must capture this dict as the dispatch env")
        }
        other => panic!("resolveOp must return an OpRef, got {}", other.type_name()),
    }

    // op(r) — a fully-qualified resolved-op identity.
    let op_id = interp.call(&format!("{OPREF}.op"), &[opref.clone()]).unwrap();
    assert!(sym_qn(&interp, &op_id).contains('.'), "op identity must be fully qualified");

    // dict(r) — some(Dictionary).
    let d = interp.call(&format!("{OPREF}.dict"), &[opref]).unwrap();
    match &d {
        Value::Entity { functor, named, .. } => {
            assert!(interp.kb().qualified_name_of(*functor).ends_with(".some"), "dict(r) must be some(...)");
            assert!(matches!(named_field(&interp, named, "value"), Value::Requirement(_)));
        }
        other => panic!("dict(r) must be an Option, got {}", other.type_name()),
    }
}

#[test]
fn resolve_op_no_table_row_falls_back_to_spec_op() {
    let mut interp = interp();
    // Bool does NOT provide Numeric — no `add` row for the Bool impl — so
    // resolveOp falls back to the spec op itself (mirrors
    // `dispatch_via_sort_ops_table`'s `unwrap_or(fn_sym)`).
    let bool_sym = resolve(&interp, "anthill.prelude.Bool");
    let add = sym_val(&mut interp, "anthill.prelude.Numeric.add");
    let dict = Value::Requirement(interp.alloc_requirement(bool_sym, SmallVec::new()));

    let opref = interp.call(&format!("{DICT}.resolveOp"), &[dict, add]).unwrap();
    let op_id = interp.call(&format!("{OPREF}.op"), &[opref]).unwrap();
    assert_eq!(sym_qn(&interp, &op_id), "anthill.prelude.Numeric.add");
}

// ── Dictionary.ops — bulk enumeration ────────────────────────────────────────

#[test]
fn ops_enumerates_dict_operations_as_oprefs() {
    let mut interp = interp();
    let int64 = resolve(&interp, "anthill.prelude.Int64");
    // Sanity: the impl carries table rows to enumerate.
    assert!(
        !interp.kb().sort_ops_for_impl(int64).is_empty(),
        "Int64 should have SortOpsTable rows (own + inherited spec ops)"
    );

    let dict = Value::Requirement(interp.alloc_requirement(int64, SmallVec::new()));
    let list = interp.call(&format!("{DICT}.ops"), &[dict]).unwrap();

    // A non-empty cons list whose head is a dict-bearing OpRef.
    match &list {
        Value::Entity { functor, named, .. } => {
            let qn = interp.kb().qualified_name_of(*functor).to_string();
            assert!(qn.ends_with(".cons"), "ops over an impl with rows must be a non-empty List, got {qn}");
            let head = named_field(&interp, named, "head");
            assert!(
                matches!(head, Value::OpRef { dict: Some(_), .. }),
                "each ops element is a callable, dict-bearing OpRef"
            );
        }
        other => panic!("ops must return a List, got {}", other.type_name()),
    }
}

// ── OpRef invocation — a resolved (builtin-backed) op is callable ────────────

#[test]
fn opref_backed_by_builtin_is_callable() {
    // A higher-order op applies its Function-typed parameter. Passing a
    // `Value::OpRef` whose `op` is a NATIVE builtin (`Int64.abs`, no anthill
    // body) must run the builtin: `spread_eta_args` reads the arity from the
    // signature (`OperationInfo.params`), then the apply path's builtin step
    // dispatches it. Regression guard for the WI-577 review finding that a
    // body-less OpRef errored `UnknownOperation` on apply.
    let src = "namespace test.wi577.apply\n\
               import anthill.prelude.{Int64, Function}\n\
               operation applyUnary(f: Function[Int64, Int64], x: Int64) -> Int64 = f(x)\n\
               end\n";
    let mut interp = common::interp_for(src);
    let abs = resolve(&interp, "anthill.prelude.Int64.abs");
    let opref = Value::OpRef { op: abs, dict: None };
    let got = interp
        .call("test.wi577.apply.applyUnary", &[opref, Value::Int(-5)])
        .unwrap();
    match got {
        Value::Int(n) => assert_eq!(n, 5, "applying the builtin-backed OpRef must run Int64.abs(-5)"),
        other => panic!("expected Int, got {}", other.type_name()),
    }
}

// ── OpRef.dict — none() for a requires-free op ───────────────────────────────

#[test]
fn opref_dict_none_for_dictless_ref() {
    let mut interp = interp();
    let eq_eq = resolve(&interp, "anthill.prelude.Eq.eq");
    // A bare op-ref with no captured dict (a requires-free / namespace-level op).
    let opref = Value::OpRef { op: eq_eq, dict: None };
    let d = interp.call(&format!("{OPREF}.dict"), &[opref]).unwrap();
    match &d {
        Value::Entity { functor, named, .. } => {
            assert!(interp.kb().qualified_name_of(*functor).ends_with(".none"), "must be none()");
            assert!(named.is_empty());
        }
        other => panic!("dict(r) must be an Option, got {}", other.type_name()),
    }
}

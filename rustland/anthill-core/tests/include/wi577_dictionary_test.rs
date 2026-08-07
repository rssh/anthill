//! WI-577 — first-class runtime dictionaries + op-refs.
//!
//! The two runtime VIEW sorts `anthill.realization.runtime.Dictionary` /
//! `OpRef` — the anthill face of the runtime dispatch values
//! a requirement dictionary / `Value::OpRef` — exposed as native builtins over
//! the values themselves (WI-1045; there is no arena behind a dictionary any
//! more). These tests build requirement dictionaries by hand (as
//! the interpreter does when reducing the `Dictionary` IR node) and exercise
//! each accessor op through `Interpreter::call`, which dispatches straight to
//! the registered builtin.
//!
//! Reference: docs/design/requirement-dictionaries.md §2 (runtime sorts) / §2.4
//! (OpRef) / §4 (phasing).

use smallvec::SmallVec;

use anthill_core::eval::value::Dictionary;
use anthill_core::eval::{Interpreter, Value};
use anthill_core::intern::Symbol;
use anthill_core::kb::term::Term;

const DICT: &str = "anthill.realization.runtime.Dictionary";
const OPREF: &str = "anthill.realization.runtime.OpRef";

fn interp() -> Interpreter {
    // Stdlib alone (with the eval builtins registered) — we construct the
    // requirement values by hand.
    crate::common::interp_for("namespace test.wi577.empty\nend\n")
}

fn resolve(interp: &Interpreter, qn: &str) -> Symbol {
    interp
        .kb()
        .try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("symbol {qn} not found in KB"))
}

/// Build a `Symbol` runtime value (a `Ref` term) for a qualified name — the
/// carrier `resolveOp` is HANDED here, and deliberately NOT the one `impl` / `op`
/// return: those mint `Value::SymbolRef` (WI-1016), so keeping this side on the
/// interned spelling makes `resolveOp` take one carrier and answer in the other,
/// which is the cross-carrier round trip worth testing.
fn sym_val(interp: &mut Interpreter, qn: &str) -> Value {
    let s = resolve(interp, qn);
    Value::term(interp.kb_mut().alloc(Term::Ref(s)))
}

/// The qualified name of a `Symbol` runtime value.
///
/// Reads the symbol by CONTENT (`value_symbol`), not by carrier. It used to
/// match `Value::Term { id } → Term::Ref | Ident`, asserting the carrier as well
/// as the symbol.
///
/// That made it the ONLY thing that noticed when `symbol_value` was briefly
/// flipped to mint `Value::SymbolRef` — which is a statement about test
/// COVERAGE, not about blast radius: anthill-stl's `expect_symbol` read by
/// carrier too and stayed green over five broken host ops. The flip landed in
/// WI-1016, whose own tests pin the CARRIER; this reader is by-content either
/// way, which is what it should have been from the start.
fn sym_qn(interp: &Interpreter, v: &Value) -> String {
    match interp.kb().value_symbol(v) {
        Some(s) => interp.kb().qualified_name_of(s).to_string(),
        None => panic!("expected a Symbol value, got {}", v.type_name()),
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
    let child = crate::common::dict(&interp, bool_sym, []);
    let mut subs: SmallVec<[_; 1]> = SmallVec::new();
    subs.push(child);
    let dict = crate::common::dict(&interp, int64, subs).into_value();

    // impl(d) — the resolved impl identity.
    let got = interp.call(&format!("{DICT}.impl"), &[dict.clone()]).unwrap();
    assert_eq!(sym_qn(&interp, &got), "anthill.prelude.Int64");

    // arity(d) — one sub-requirement.
    let got = interp.call(&format!("{DICT}.arity"), &[dict.clone()]).unwrap();
    assert_eq!(expect_int(&got), 1);

    // sub(d, 0) — the child dict; impl(child) == Bool, arity 0.
    let child_dict = interp.call(&format!("{DICT}.sub"), &[dict.clone(), Value::Int(0)]).unwrap();
    assert!(Dictionary::from_value(interp.kb(), &child_dict).is_some(),
        "sub must return a dictionary, got {child_dict:?}");
    let child_impl = interp.call(&format!("{DICT}.impl"), &[child_dict.clone()]).unwrap();
    assert_eq!(sym_qn(&interp, &child_impl), "anthill.prelude.Bool");
    let child_arity = interp.call(&format!("{DICT}.arity"), &[child_dict]).unwrap();
    assert_eq!(expect_int(&child_arity), 0);

    // Out-of-range projection is a loud error, not a panic.
    let err = interp.call(&format!("{DICT}.sub"), &[dict, Value::Int(5)]);
    assert!(err.is_err(), "out-of-range sub must error");
}

// ── Dictionary.resolveOp → OpRef.op / OpRef.dict ─────────────────────────────

#[test]
fn resolve_op_real_impl_yields_callable_opref() {
    let mut interp = interp();
    let int64 = resolve(&interp, "anthill.prelude.Int64");

    // Int64 provides Eq — resolve `Eq.eq` against a Dictionary{Int64}.
    let eq_eq = sym_val(&mut interp, "anthill.prelude.PartialEq.eq");
    let dict = crate::common::dict(&interp, int64, []).into_value();
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
            let inner = named_field(&interp, named, "value");
            assert!(Dictionary::from_value(interp.kb(), &inner).is_some(),
                "the payload must be a dictionary, got {inner:?}");
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
    let dict = crate::common::dict(&interp, bool_sym, []).into_value();

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

    let dict = crate::common::dict(&interp, int64, []).into_value();
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
    let mut interp = crate::common::interp_for(src);
    let abs = resolve(&interp, "anthill.prelude.Int64.abs");
    // `named: None` — a bare ref names its own op (WI-857).
    let opref = Value::OpRef { op: abs, dict: None, named: None };
    let got = interp
        .call("test.wi577.apply.applyUnary", &[opref, Value::Int(-5)])
        .unwrap();
    match got {
        Value::Int(n) => assert_eq!(n, 5, "applying the builtin-backed OpRef must run Int64.abs(-5)"),
        other => panic!("expected Int, got {}", other.type_name()),
    }
}

/// WI-857 REGRESSION — an `OpRef` minted by `resolveOp` must remember the op the
/// call NAMED, not only the one it resolved to.
///
/// `resolveOp` returns `op` = the RESOLVED impl member (`Descending.compare`) while
/// `dict` witnesses the SPEC (`Ordered`), whose layout puts `Ordered`'s own chain —
/// `Eq`, `PartialOrd` — in front of the provider's. Applying that ref reads the
/// layout to slice the callee's frame, and reading it off the resolved op alone
/// measures a spec-instance dictionary against `Descending`'s own chain, which is
/// EMPTY: a valid arity-2 dictionary is then rejected as "wants 0 slot(s)". Found by
/// review; the pre-WI-857 code matched by accident because a dictionary bundled only
/// the provider's chain.
///
/// Asserted on the VALUE rather than by applying it: the mint site is what carries
/// the named op, and `OpRef.op` is the public face of the resolution.
#[test]
fn resolve_op_remembers_the_named_spec_op() {
    let src = "namespace test.wi577.named\n\
               import anthill.prelude.{Int64, Ordered}\n\
               import anthill.prelude.Numeric.{sub}\n\
               sort Descending\n\
               fact Ordered[T = Int64]\n\
               operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)\n\
               end\n\
               end\n";
    let mut interp = crate::common::interp_for(src);
    let desc = resolve(&interp, "test.wi577.named.Descending");
    // A LAYOUT-VALID `Ordered[Int64]` dictionary supplied by `Descending`: the spec
    // half is `Ordered`'s two entries; `Descending` declares no `requires`.
    let mut subs: SmallVec<[_; 1]> = SmallVec::new();
    subs.push(crate::common::dict(&interp, desc, []));
    subs.push(crate::common::dict(&interp, desc, []));
    let dict = crate::common::dict(&interp, desc, subs).into_value();
    let cmp = sym_val(&mut interp, "anthill.prelude.Ordered.compare");
    let opref = interp.call(&format!("{DICT}.resolveOp"), &[dict, cmp]).unwrap();
    match &opref {
        Value::OpRef { op, named, .. } => {
            assert_eq!(
                interp.kb().qualified_name_of(*op),
                "test.wi577.named.Descending.compare",
                "resolveOp resolves to the witness's own member",
            );
            let named = named.expect(
                "the NAMED op must be carried: `op` alone cannot say which spec the \
                 captured dictionary witnesses, so applying this ref would measure it \
                 against `Descending`'s (empty) chain and reject a valid arity-2 dict",
            );
            assert_eq!(
                interp.kb().qualified_name_of(named),
                "anthill.prelude.Ordered.compare",
                "the named op is the SPEC op the call passed in",
            );
        }
        other => panic!("resolveOp must return an OpRef, got {}", other.type_name()),
    }
}

// ── OpRef.dict — none() for a requires-free op ───────────────────────────────

#[test]
fn opref_dict_none_for_dictless_ref() {
    let mut interp = interp();
    let eq_eq = resolve(&interp, "anthill.prelude.PartialEq.eq");
    // A bare op-ref with no captured dict (a requires-free / namespace-level op).
    let opref = Value::OpRef { op: eq_eq, dict: None, named: None };
    let d = interp.call(&format!("{OPREF}.dict"), &[opref]).unwrap();
    match &d {
        Value::Entity { functor, named, .. } => {
            assert!(interp.kb().qualified_name_of(*functor).ends_with(".none"), "must be none()");
            assert!(named.is_empty());
        }
        other => panic!("dict(r) must be an Option, got {}", other.type_name()),
    }
}

// ── OpRef.named — the spec op the call named (WI-1019) ───────────────────────

/// `OpRef.named(r)` — the accessor face of the `named` half.
///
/// WI-1019 declared it because that half is part of the value's IDENTITY (two
/// `OpRef`s agreeing on `op` and `dict` but not on `named` are different values,
/// and the structural view keys on all three), while this sort's declared
/// accessor set claimed to "expose everything the value holds" and omitted it.
///
/// Driven through `Interpreter::call` on a REAL `resolveOp`-minted ref, so this
/// tests the anthill-visible operation. `resolve_op_remembers_the_named_spec_op`
/// asserts the same fact on the `Value` — and it passed for as long as the
/// accessor was missing, which is precisely why it could not have caught the gap.
///
/// CONTROL: drop the `OpRef.named` registration in `builtins.rs` and this test
/// fails to dispatch, while `resolve_op_remembers_the_named_spec_op` stays green.
#[test]
fn opref_named_reads_the_spec_op_through_the_accessor() {
    let src = "namespace test.wi577.namedop\n\
               import anthill.prelude.{Int64, Ordered}\n\
               import anthill.prelude.Numeric.{sub}\n\
               sort Descending\n\
               fact Ordered[T = Int64]\n\
               operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)\n\
               end\n\
               end\n";
    let mut interp = crate::common::interp_for(src);
    let desc = resolve(&interp, "test.wi577.namedop.Descending");
    let mut subs: SmallVec<[_; 1]> = SmallVec::new();
    subs.push(crate::common::dict(&interp, desc, []));
    subs.push(crate::common::dict(&interp, desc, []));
    let dict = crate::common::dict(&interp, desc, subs).into_value();
    let cmp = sym_val(&mut interp, "anthill.prelude.Ordered.compare");
    let opref = interp.call(&format!("{DICT}.resolveOp"), &[dict, cmp]).unwrap();

    let got = interp.call(&format!("{OPREF}.named"), &[opref]).unwrap();
    match &got {
        Value::Entity { functor, named, .. } => {
            assert!(
                interp.kb().qualified_name_of(*functor).ends_with(".some"),
                "a resolveOp-minted ref carries a named spec op",
            );
            assert_eq!(
                sym_qn(&interp, named_field(&interp, named, "value")),
                "anthill.prelude.Ordered.compare",
                "and it is the SPEC op the call passed in, not the resolved member",
            );
        }
        other => panic!("named(r) must be an Option, got {}", other.type_name()),
    }

    // none() for an eta'd ref, where spec and provider coincide — the other half
    // of the contract, so the `some(...)` above is not merely "always some".
    let eq_eq = resolve(&interp, "anthill.prelude.PartialEq.eq");
    let bare = Value::OpRef { op: eq_eq, dict: None, named: None };
    let got = interp.call(&format!("{OPREF}.named"), &[bare]).unwrap();
    match &got {
        Value::Entity { functor, named, .. } => {
            assert!(interp.kb().qualified_name_of(*functor).ends_with(".none"), "must be none()");
            assert!(named.is_empty());
        }
        other => panic!("named(r) must be an Option, got {}", other.type_name()),
    }
}

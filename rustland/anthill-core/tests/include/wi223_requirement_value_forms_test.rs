//! WI-223 — runtime support for the operation-call model: tests that the
//! eval reduces the requirement-typed value forms emitted by the
//! requirement-insertion pass:
//!
//!   - `var_ref(name)` → the frame requirement of that name
//!   - `requirement_at_sort(chain, slot)` → projected sub-requirement
//!   - `Dictionary(subs…, impl: S)` → a freshly-built dictionary value
//!
//! WI-1045 — the reductions produce ORDINARY VALUES, so each assertion reads
//! the result back through `Dictionary::from_value`: the same boundary an
//! anthill caller crosses, and the only shape check in the crate.
//!
//! Tests use `Interpreter::run_with_requirements` to seed the frame's
//! requirements before stepping the body — exercising reductions in
//! isolation from the WI-222 rewrite pass that will eventually emit them.
//!
//! Reference: docs/design/operation-call-model.md §"Two primitives:
//! requirement_at_current and requirement_at_sort", §"Construction site".


use smallvec::SmallVec;

use anthill_core::eval::value::Dictionary;
use anthill_core::eval::{Interpreter, Value};
use anthill_core::kb::term::{Literal, Term};
use anthill_core::kb::KnowledgeBase;

use crate::common::load_kb_with;

fn fresh_interp() -> Interpreter {
    // Stdlib alone — no user source needed; we construct IR terms by hand.
    let kb = load_kb_with("namespace test.wi223.empty\nend\n");
    Interpreter::new(kb)
}

fn alloc_int(kb: &mut KnowledgeBase, n: i64) -> anthill_core::kb::term::TermId {
    kb.alloc(Term::Const(Literal::Int(n)))
}

/// Build `var_ref(name: <sym>)` — a named requirement read (WI-237
/// names model; replaced the positional `requirement_at_current`).
fn build_req_var_ref(
    kb: &mut KnowledgeBase,
    var_ref_sym: anthill_core::intern::Symbol,
    name_sym: anthill_core::intern::Symbol,
) -> anthill_core::kb::term::TermId {
    let name_ref = kb.alloc(Term::Ref(name_sym));
    let name_field = kb.intern("name");
    kb.alloc(Term::Fn {
        functor: var_ref_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(name_field, name_ref)]),
    })
}

#[test]
fn var_ref_yields_frame_requirement_handle() {
    // Pre-seed a single named requirement; an op body that reads
    // `var_ref(name: __req_probe)` must return the dictionary whose impl
    // matches what we passed in.
    let mut interp = fresh_interp();
    let probe_sym = interp.kb_mut().intern("test.wi223.IntFooImpl");
    let handle = crate::common::dict(&interp, probe_sym, []);
    let expected_impl = handle.impl_sort();

    let var_ref_sym = interp.kb()
        .try_resolve_symbol("anthill.reflect.Expr.var_ref")
        .expect("reflect.Expr.var_ref registered");
    let req_name = interp.kb_mut().intern("__req_probe");
    let expr = build_req_var_ref(interp.kb_mut(), var_ref_sym, req_name);

    let mut requirements: SmallVec<[_; 2]> = SmallVec::new();
    requirements.push((req_name, handle));
    let value = interp.run_with_requirements(expr, requirements)
        .expect("var_ref should reduce to the frame requirement");

    let read = expect_dict(&interp, &value);
    assert_eq!(read.impl_sort(), expected_impl,
        "the value delivered should carry the seeded dictionary's impl");
}

/// The dictionary a reduction delivered, read back through the ONE boundary.
fn expect_dict(interp: &Interpreter, v: &Value) -> Dictionary {
    Dictionary::from_value(interp.kb(), v)
        .unwrap_or_else(|| panic!("expected a Dictionary value, got {v:?}"))
}

#[test]
fn var_ref_unbound_requirement_errors() {
    // Frame has 0 requirements; reading `var_ref(name: __req_probe)` as
    // a value must dispatch_call-miss and surface a clear error rather
    // than panicking. Defensive case for the eval loud-failure discipline.
    let mut interp = fresh_interp();
    let var_ref_sym = interp.kb()
        .try_resolve_symbol("anthill.reflect.Expr.var_ref")
        .expect("var_ref registered");
    let req_name = interp.kb_mut().intern("__req_probe");
    let expr = build_req_var_ref(interp.kb_mut(), var_ref_sym, req_name);

    let result = interp.run_with_requirements(expr, SmallVec::new());
    assert!(result.is_err(),
        "unbound requirement name must error, not panic; got {result:?}");
}

#[test]
fn requirement_at_sort_projects_sub_handle() {
    // Build a parent requirement carrying a child; an op body of
    // `requirement_at_sort(chain: requirement_at_current(0), slot: 0)`
    // must yield the child handle.
    let mut interp = fresh_interp();
    let parent_sym = interp.kb_mut().intern("test.wi223.ParentImpl");
    let child_sym = interp.kb_mut().intern("test.wi223.ChildImpl");

    let child_handle = crate::common::dict(&interp, child_sym, []);
    let mut bundle: SmallVec<[_; 1]> = SmallVec::new();
    bundle.push(child_handle);
    let parent_handle = crate::common::dict(&interp, parent_sym, bundle);

    let var_ref_sym = interp.kb()
        .try_resolve_symbol("anthill.reflect.Expr.var_ref")
        .unwrap();
    let raas_sym = interp.kb()
        .try_resolve_symbol("anthill.reflect.Expr.requirement_at_sort")
        .expect("requirement_at_sort registered");

    // chain = var_ref(name: __req_parent) — a names-model requirement
    // read; requirement_at_sort projects its slot 0.
    let req_name = interp.kb_mut().intern("__req_parent");
    let inner = build_req_var_ref(interp.kb_mut(), var_ref_sym, req_name);
    let zero = alloc_int(interp.kb_mut(), 0);
    let chain_field = interp.kb_mut().intern("chain");
    let slot_field = interp.kb_mut().intern("slot");
    let expr = interp.kb_mut().alloc(Term::Fn {
        functor: raas_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(chain_field, inner), (slot_field, zero)]),
    });

    let mut requirements: SmallVec<[_; 2]> = SmallVec::new();
    requirements.push((req_name, parent_handle));
    let value = interp.run_with_requirements(expr, requirements)
        .expect("requirement_at_sort should reduce successfully");

    let read = expect_dict(&interp, &value);
    assert_eq!(read.impl_sort(), child_sym,
        "the projected sub-dictionary should be the child's");
}

#[test]
fn dictionary_node_builds_a_childless_dictionary() {
    // `Dictionary(impl: Foo)` builds a dictionary with no sub-dictionaries.
    //
    // WI-1045 — the arena live-count half of this test is DELETED, not ported:
    // there is no arena, so "the slot releases after the value drops" has no
    // subject. What remains is the reduction itself, which is what the IR node
    // is for.
    let mut interp = fresh_interp();
    let foo_sym = interp.kb_mut().intern("test.wi223.Foo");
    let expr = crate::common::dict_term(interp.kb_mut(), foo_sym, &[]);

    let value = interp.run_with_requirements(expr, SmallVec::new())
        .expect("the Dictionary node should reduce successfully");

    let read = expect_dict(&interp, &value);
    assert_eq!(read.impl_sort(), foo_sym,
        "the built dictionary's impl should match the requested one");
    assert_eq!(read.arity(), 0, "no sub-dictionaries expected");
}

#[test]
fn dictionary_node_bundles_sub_dictionaries() {
    // Construct a parent that bundles a child dictionary (built via a nested
    // `Dictionary` node); pin the IR wiring: the eval produces a parent whose
    // 0-th sub-dictionary is the freshly-built child.
    let mut interp = fresh_interp();
    let parent_sym = interp.kb_mut().intern("test.wi223.Parent");
    let child_sym = interp.kb_mut().intern("test.wi223.Child");

    // Inner: Dictionary(impl: Child) — a POSITIONAL child of the outer node,
    // the same layout the value carries (WI-1045's one spelling).
    let child_construct = crate::common::dict_term(interp.kb_mut(), child_sym, &[]);
    let parent_construct =
        crate::common::dict_term(interp.kb_mut(), parent_sym, &[child_construct]);

    let value = interp.run_with_requirements(parent_construct, SmallVec::new())
        .expect("the nested Dictionary chain should reduce");

    let read = expect_dict(&interp, &value);
    assert_eq!(read.impl_sort(), parent_sym, "parent impl preserved");
    assert_eq!(read.arity(), 1, "parent should bundle one sub-dictionary");
    assert_eq!(read.sub(0).expect("slot 0").impl_sort(), child_sym,
        "parent's 0-th sub-dictionary should be the child");
}

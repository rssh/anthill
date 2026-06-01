//! `anthill.reflect.extract` — the type-reflection builtin that reifies the
//! engine's deep-form `Type` term into the `TypeExtractor` ADT. Drives the
//! builtin through `Interpreter::call` over real stdlib symbols.

use anthill_core::eval::builtins::register_standard_builtins;
use anthill_core::eval::{Interpreter, Value};
use anthill_core::intern::Symbol;
use anthill_core::kb::term::Term;
use smallvec::SmallVec;

use crate::common::load_kb_with;

/// A named field of an entity `Value`.
fn field<'a>(v: &'a Value, key: Symbol) -> Option<&'a Value> {
    match v {
        Value::Entity { named, .. } => named.iter().find(|(k, _)| *k == key).map(|(_, x)| x),
        _ => None,
    }
}

fn entity_functor(v: &Value) -> Option<Symbol> {
    match v {
        Value::Entity { functor, .. } => Some(*functor),
        _ => None,
    }
}

#[test]
fn extract_sort_ref_reifies_sortref() {
    let mut kb = load_kb_with("");
    let int_sym = kb.try_resolve_symbol("anthill.prelude.Int").expect("Int sort");
    let sortref = kb
        .try_resolve_symbol("anthill.prelude.TypeExtractor.SortRef")
        .expect("SortRef ctor");
    let ty = kb.make_sort_ref(int_sym);

    let mut interp = Interpreter::new(kb);
    register_standard_builtins(&mut interp).expect("register builtins");
    let r = interp
        .call("anthill.reflect.extract", &[Value::Term(ty)])
        .expect("extract should evaluate");

    assert_eq!(
        entity_functor(&r),
        Some(sortref),
        "extract(sort_ref(Int)) should reify as SortRef, got {r:?}"
    );
}

#[test]
fn extract_parameterized_reifies_parameterized_with_typebinding() {
    let mut kb = load_kb_with("");
    let int_sym = kb.try_resolve_symbol("anthill.prelude.Int").expect("Int sort");
    let list_sym = kb.try_resolve_symbol("anthill.prelude.List").expect("List sort");
    let param_ctor = kb
        .try_resolve_symbol("anthill.prelude.TypeExtractor.Parameterized")
        .expect("Parameterized ctor");
    let binding_ctor = kb
        .try_resolve_symbol("anthill.prelude.TypeExtractor.TypeBinding")
        .expect("TypeBinding ctor");
    let cons_sym = kb
        .try_resolve_symbol("anthill.prelude.List.cons")
        .expect("List.cons");
    let bindings_key = kb.intern("bindings");
    let head_key = kb.intern("head");
    let t_param = kb.intern("T");

    // List[T = Int]
    let int_ref = kb.make_sort_ref(int_sym);
    let base = kb.make_sort_ref(list_sym);
    let ty = kb.make_parameterized_type(base, &[(t_param, int_ref)]);

    let mut interp = Interpreter::new(kb);
    register_standard_builtins(&mut interp).expect("register builtins");
    let r = interp
        .call("anthill.reflect.extract", &[Value::Term(ty)])
        .expect("extract should evaluate");

    assert_eq!(
        entity_functor(&r),
        Some(param_ctor),
        "extract(parameterized) should reify as Parameterized, got {r:?}"
    );
    // bindings is a non-empty cons list whose head is a TypeBinding.
    let bindings = field(&r, bindings_key).expect("Parameterized.bindings");
    assert_eq!(
        entity_functor(bindings),
        Some(cons_sym),
        "bindings should be a non-empty list, got {bindings:?}"
    );
    let head = field(bindings, head_key).expect("cons head");
    assert_eq!(
        entity_functor(head),
        Some(binding_ctor),
        "each binding should be re-wrapped as TypeExtractor.TypeBinding, got {head:?}"
    );
}

#[test]
fn extract_non_type_reifies_error() {
    let mut kb = load_kb_with("");
    let error_ctor = kb
        .try_resolve_symbol("anthill.prelude.TypeExtractor.Error")
        .expect("Error ctor");
    // A plain term whose functor is not a Type constructor.
    let foo = kb.intern("foo");
    let non_type = kb.alloc(Term::Fn {
        functor: foo,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });

    let mut interp = Interpreter::new(kb);
    register_standard_builtins(&mut interp).expect("register builtins");
    let r = interp
        .call("anthill.reflect.extract", &[Value::Term(non_type)])
        .expect("extract should evaluate (total)");

    assert_eq!(
        entity_functor(&r),
        Some(error_ctor),
        "extract(non-type) should reify as Error, got {r:?}"
    );
}

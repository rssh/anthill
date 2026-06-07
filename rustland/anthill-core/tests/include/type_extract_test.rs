//! `anthill.reflect.extract` — the type-reflection builtin that reifies the
//! engine's deep-form `Type` term into the `TypeExtractor` ADT. Drives the
//! builtin through `Interpreter::call` over real stdlib symbols.

use anthill_core::eval::builtins::register_standard_builtins;
use anthill_core::eval::{Interpreter, Value};
use anthill_core::intern::Symbol;
use anthill_core::kb::term::{Term, TermId};
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
    let int_sym = kb.try_resolve_symbol("anthill.prelude.Int64").expect("Int64 sort");
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
        "extract(sort_ref(Int64)) should reify as SortRef, got {r:?}"
    );
}

#[test]
fn extract_parameterized_reifies_parameterized_with_typebinding() {
    let mut kb = load_kb_with("");
    let int_sym = kb.try_resolve_symbol("anthill.prelude.Int64").expect("Int64 sort");
    let list_sym = kb.try_resolve_symbol("anthill.prelude.List").expect("List sort");
    let param_ctor = kb
        .try_resolve_symbol("anthill.prelude.TypeExtractor.Parameterized")
        .expect("Parameterized ctor");
    let binding_ctor = kb
        .try_resolve_symbol("anthill.prelude.TypeBinding")
        .expect("TypeBinding ctor");
    let cons_sym = kb
        .try_resolve_symbol("anthill.prelude.List.cons")
        .expect("List.cons");
    let bindings_key = kb.intern("bindings");
    let head_key = kb.intern("head");
    let t_param = kb.intern("T");

    // List[T = Int64]
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
fn extract_term_backed_ref_reifies_sortref() {
    // WI-361 stage 2: a bare sort carried as the *term backing* `Ref(S)` (not the
    // deep `sort_ref(name: Ref(S))`) reifies as SortRef — the dual-form reader.
    let mut kb = load_kb_with("");
    let int_sym = kb.try_resolve_symbol("anthill.prelude.Int64").expect("Int64 sort");
    let sortref = kb
        .try_resolve_symbol("anthill.prelude.TypeExtractor.SortRef")
        .expect("SortRef ctor");
    let name_key = kb.intern("name");
    // term backing: bare `Ref(Int64)`.
    let ty = kb.alloc(Term::Ref(int_sym));

    let mut interp = Interpreter::new(kb);
    register_standard_builtins(&mut interp).expect("register builtins");
    let r = interp
        .call("anthill.reflect.extract", &[Value::Term(ty)])
        .expect("extract should evaluate");

    assert_eq!(
        entity_functor(&r),
        Some(sortref),
        "Ref(Int64) should reify as SortRef, got {r:?}"
    );
    let name = field(&r, name_key).expect("SortRef.name");
    assert!(
        matches!(name, Value::Term(t) if matches!(interp.kb().get_term(*t), Term::Ref(s) if *s == int_sym)),
        "SortRef.name should be Ref(Int64), got {name:?}"
    );
}

#[test]
fn extract_term_backed_fn_reifies_parameterized() {
    // WI-361 stage 2: a type application carried as the *term backing*
    // `Fn{S, named}` — the base sort IS the functor, the named args ARE the
    // bindings (no `parameterized` wrapper) — reifies as Parameterized.
    let mut kb = load_kb_with("");
    let int_sym = kb.try_resolve_symbol("anthill.prelude.Int64").expect("Int64 sort");
    let list_sym = kb.try_resolve_symbol("anthill.prelude.List").expect("List sort");
    let param_ctor = kb
        .try_resolve_symbol("anthill.prelude.TypeExtractor.Parameterized")
        .expect("Parameterized ctor");
    let binding_ctor = kb
        .try_resolve_symbol("anthill.prelude.TypeBinding")
        .expect("TypeBinding ctor");
    let cons_sym = kb
        .try_resolve_symbol("anthill.prelude.List.cons")
        .expect("List.cons");
    let bindings_key = kb.intern("bindings");
    let base_key = kb.intern("base");
    let head_key = kb.intern("head");
    let t_param = kb.intern("T");

    // term backing: `List[T = Int64]` == `Fn{List, named:[(T, Ref(Int64))]}`.
    let int_ref = kb.alloc(Term::Ref(int_sym));
    let mut named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
    named.push((t_param, int_ref));
    let ty = kb.alloc(Term::Fn { functor: list_sym, pos_args: SmallVec::new(), named_args: named });

    let mut interp = Interpreter::new(kb);
    register_standard_builtins(&mut interp).expect("register builtins");
    let r = interp
        .call("anthill.reflect.extract", &[Value::Term(ty)])
        .expect("extract should evaluate");

    assert_eq!(
        entity_functor(&r),
        Some(param_ctor),
        "Fn{{List,..}} should reify as Parameterized, got {r:?}"
    );
    // base is `Ref(List)` — the functor lifted to the base-sort field.
    let base = field(&r, base_key).expect("Parameterized.base");
    assert!(
        matches!(base, Value::Term(t) if matches!(interp.kb().get_term(*t), Term::Ref(s) if *s == list_sym)),
        "Parameterized.base should be Ref(List), got {base:?}"
    );
    // bindings is a non-empty cons list whose head is a re-wrapped TypeBinding.
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
        "each binding re-wrapped as TypeExtractor.TypeBinding, got {head:?}"
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

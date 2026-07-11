//! WI-578 — the `value_type_term` reader.
//!
//! `value_type_term` computes a runtime value's type-term CARRIER-AGNOSTICALLY (a
//! `Value::Entity` and the hash-consed `Value::Term` of the same constructor type
//! identically — one `TermView` read path, WI-342/348). These pin the milestone
//! `min_sort_of_value` could NOT reach: a bare constructed value gets its FULL
//! parameterized type (`cons(1, nil)` -> `List[Int64]`), not `None`.

use anthill_core::eval::value::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::node_occurrence::value_to_term;
use anthill_core::kb::subst::Substitution;
use anthill_core::kb::term::{Term, Var, VarId};
use anthill_core::kb::typing::{sort_functor_of_view, value_type_term};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

fn load_kb() -> KnowledgeBase {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    assert!(!files.is_empty(), "no stdlib files found");
    let parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).expect("stdlib load failed");
    kb
}

fn sym(kb: &KnowledgeBase, qn: &str) -> Symbol {
    kb.try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("symbol {qn} not registered"))
}

/// A sort symbol resolves to `name` exactly, or to a qualified path ending in `.name`.
fn assert_sort_named(kb: &KnowledgeBase, s: Symbol, name: &str) {
    let full = kb.resolve_sym(s);
    assert!(
        full == name || full.ends_with(&format!(".{name}")),
        "expected sort {name}, got {full}",
    );
}

/// `cons(head: <hd>, tail: <tl>)` as a transient `Value::Entity` (named sorted into
/// the KB canonical `Symbol::index()` order, the form `value_to_term` lowers to).
fn cons_value(kb: &mut KnowledgeBase, hd: Value, tl: Value) -> Value {
    let cons = sym(kb, "anthill.prelude.List.cons");
    let head = kb.intern("head");
    let tail = kb.intern("tail");
    let mut named = vec![(head, hd), (tail, tl)];
    named.sort_by_key(|(s, _)| s.index());
    Value::Entity { functor: cons, pos: vec![].into(), named: named.into() }
}

fn nil_value(kb: &KnowledgeBase) -> Value {
    let nil = sym(kb, "anthill.prelude.List.nil");
    Value::Entity { functor: nil, pos: vec![].into(), named: vec![].into() }
}

/// Assert a parameterized type `Fn{S, named: [(_, P), ...]}` carries a param `P`
/// whose sort head is `name`.
fn assert_type_param_is(kb: &KnowledgeBase, ty: &Value, name: &str) {
    let tid = ty.expect_term();
    match kb.get_term(tid) {
        Term::Fn { named_args, .. } => {
            assert!(
                !named_args.is_empty(),
                "expected a parameterized type with a binding, got bare {ty:?}",
            );
            let found = named_args.iter().any(|(_, p)| {
                sort_functor_of_view(kb, &Value::term(*p))
                    .map(|s| {
                        let full = kb.resolve_sym(s);
                        full == name || full.ends_with(&format!(".{name}"))
                    })
                    .unwrap_or(false)
            });
            assert!(found, "expected a type param with sort {name} in {ty:?}");
        }
        other => panic!("expected a parameterized Fn type, got {other:?}"),
    }
}

#[test]
fn value_type_term_scalar_is_literal_sort() {
    let mut kb = load_kb();
    let subst = Substitution::new();
    let ty = value_type_term(&mut kb, &subst, &Value::Int(7));
    let head = sort_functor_of_view(&kb, &ty).expect("scalar has a sort head");
    assert_sort_named(&kb, head, "Int64");
}

/// The MILESTONE: a bare constructed list gets its FULL parameterized type
/// `List[Int64]` — the case `min_sort_of_value` returned `None` for.
#[test]
fn value_type_term_of_cons_is_list_of_int() {
    let mut kb = load_kb();
    let subst = Substitution::new();
    let nil = nil_value(&kb);
    let cons = cons_value(&mut kb, Value::Int(1), nil);
    let ty = value_type_term(&mut kb, &subst, &cons);
    let head = sort_functor_of_view(&kb, &ty).expect("cons has a sort head");
    assert_sort_named(&kb, head, "List");
    assert_type_param_is(&kb, &ty, "Int64");
}

/// CARRIER-AGNOSTIC: the SAME constructor typed through a hash-consed `Value::Term`
/// yields the same `List[Int64]` — one read path for both carriers (WI-342/348).
#[test]
fn value_type_term_is_carrier_agnostic() {
    let mut kb = load_kb();
    let subst = Substitution::new();
    let nil = nil_value(&kb);
    let cons = cons_value(&mut kb, Value::Int(1), nil);

    // Entity carrier.
    let ty_entity = value_type_term(&mut kb, &subst, &cons);
    let he = sort_functor_of_view(&kb, &ty_entity).expect("entity sort head");

    // Term carrier: promote the SAME value into a hash-consed TermId.
    let tid = value_to_term(&mut kb, &cons).expect("lower cons to a term");
    let ty_term = value_type_term(&mut kb, &subst, &Value::term(tid));
    let ht = sort_functor_of_view(&kb, &ty_term).expect("term sort head");

    assert_eq!(
        kb.resolve_sym(he),
        kb.resolve_sym(ht),
        "the two carriers must type to the same sort head",
    );
    assert_sort_named(&kb, ht, "List");
    assert_type_param_is(&kb, &ty_term, "Int64");
}

/// A bare nullary constructor `nil` types as its sort `List` (the element param is
/// under-determined — a `?_`, present so the sort's arity is kept).
#[test]
fn value_type_term_of_nil_is_list() {
    let mut kb = load_kb();
    let subst = Substitution::new();
    let nil = nil_value(&kb);
    let ty = value_type_term(&mut kb, &subst, &nil);
    let head = sort_functor_of_view(&kb, &ty).expect("nil has a sort head");
    assert_sort_named(&kb, head, "List");
}

/// A CYCLIC σ (`?x := cons(1, ?x)` — the SLD bind path is not occurs-checked) must
/// FLOUNDER to a bounded type, never loop forever / overflow the stack. The element
/// type is still pinned by each level's head, so the sort head stays `List`.
#[test]
fn value_type_term_flounders_on_cyclic_sigma() {
    let mut kb = load_kb();
    let xname = kb.intern("x");
    let vid = VarId::new(1, xname);
    // ?x := cons(head: 1, tail: ?x) — a structure that contains the var itself.
    let cyc = cons_value(&mut kb, Value::Int(1), Value::Var(Var::Global(vid)));
    let mut subst = Substitution::new();
    subst.bind_value(&kb, vid, cyc);
    // Must RETURN (the depth cap breaks the structural cycle), not hang/overflow.
    let ty = value_type_term(&mut kb, &subst, &Value::Var(Var::Global(vid)));
    let head = sort_functor_of_view(&kb, &ty).expect("cyclic list still has a List head");
    assert_sort_named(&kb, head, "List");
}

/// A DEEP value (longer than the recursion cap) types WITHOUT stack overflow; the
/// element type survives (each `cons` head re-pins it), only the innermost tail's
/// type truncates to `?_`. Built as a flat hash-consed `Value::Term` so the kept
/// value has no recursive `Rc`-drop.
#[test]
fn value_type_term_bounds_deep_recursion() {
    let mut kb = load_kb();
    let subst = Substitution::new();
    let mut lst = nil_value(&kb);
    for i in 0..600i64 {
        lst = cons_value(&mut kb, Value::Int(i), lst);
    }
    let tid = value_to_term(&mut kb, &lst).expect("lower deep list to a term");
    let ty = value_type_term(&mut kb, &subst, &Value::term(tid));
    let head = sort_functor_of_view(&kb, &ty).expect("deep list has a List head");
    assert_sort_named(&kb, head, "List");
    assert_type_param_is(&kb, &ty, "Int64");
}

/// An UNBOUND var carrying a `Type` constraint reads its declared bound's sort from
/// the constraint store (the store-fallback that superseded `store_sort_bound`); only
/// a payload with a sort head is returned, and an unconstrained var is `?_`.
#[test]
fn value_type_term_unbound_var_reads_store_bound() {
    let mut kb = load_kb();
    let numeric = kb.make_sort_ref_by_name("Numeric");
    let xname = kb.intern("x");
    let vid = VarId::new(2, xname);
    let mut subst = Substitution::new();
    subst.add_type_constraint(vid, Value::term(numeric));
    let ty = value_type_term(&mut kb, &subst, &Value::Var(Var::Global(vid)));
    let head = sort_functor_of_view(&kb, &ty).expect("store-bound var has a sort head");
    assert_sort_named(&kb, head, "Numeric");

    // An unbound, unconstrained var is under-determined → a fresh `?_` (no sort head).
    let unconstrained = VarId::new(3, xname);
    let ty2 = value_type_term(&mut kb, &subst, &Value::Var(Var::Global(unconstrained)));
    assert!(
        sort_functor_of_view(&kb, &ty2).is_none(),
        "an unbound, unconstrained var → ?_ (no sort head)",
    );
}

/// A reflect-`*Literal` entity carrying its elements positionally (no declared field).
fn literal_value(kb: &KnowledgeBase, qn: &str, elems: Vec<Value>) -> Value {
    Value::Entity { functor: sym(kb, qn), pos: elems.into(), named: vec![].into() }
}

/// WI-578 (phase-2b review item A) — an un-desugared `[...]` reaches the value-typer as
/// a `ListLiteral` entity whose DECLARED type has no element field. The fixed
/// `constructor_value_type` mirrors `check_seq_literal_constructor`, typing it as
/// `List[Int64]` — NOT the bare `Ref(ListLiteral)` the field-driven path produced.
#[test]
fn value_type_term_of_list_literal_is_list_of_int() {
    let mut kb = load_kb();
    let subst = Substitution::new();
    let lit = literal_value(&kb, "anthill.reflect.ListLiteral", vec![Value::Int(1), Value::Int(2), Value::Int(3)]);
    let ty = value_type_term(&mut kb, &subst, &lit);
    let head = sort_functor_of_view(&kb, &ty).expect("list literal has a sort head");
    assert_sort_named(&kb, head, "List");
    assert_type_param_is(&kb, &ty, "Int64");
}

/// WI-578 (review item A) — an un-desugared `{...}` (`SetLiteral`) types as `Set[Int64]`,
/// not `Ref(SetLiteral)`.
#[test]
fn value_type_term_of_set_literal_is_set_of_int() {
    let mut kb = load_kb();
    let subst = Substitution::new();
    let lit = literal_value(&kb, "anthill.reflect.SetLiteral", vec![Value::Int(1), Value::Int(2)]);
    let ty = value_type_term(&mut kb, &subst, &lit);
    let head = sort_functor_of_view(&kb, &ty).expect("set literal has a sort head");
    assert_sort_named(&kb, head, "Set");
    assert_type_param_is(&kb, &ty, "Int64");
}

/// WI-578 (review item A) — the empty `TupleLiteral` (the `()` unit literal) types as
/// `Unit`, NOT `Ref(TupleLiteral)`: `constructor_value_type` routes it to the aggregate
/// path (`tuple_value_type`) exactly as the occurrence-typer's
/// `check_tuple_literal_constructor` does.
#[test]
fn value_type_term_of_empty_tuple_literal_is_unit() {
    let mut kb = load_kb();
    let subst = Substitution::new();
    let lit = literal_value(&kb, "anthill.reflect.TupleLiteral", vec![]);
    let ty = value_type_term(&mut kb, &subst, &lit);
    let head = sort_functor_of_view(&kb, &ty).expect("() has a sort head");
    assert_sort_named(&kb, head, "Unit");
}

/// WI-595 — an UNDER-DETERMINED bound value's type is REFINED by the carrier
/// var's store bound. `?x := nil` types as `List[?]` (the
/// `value_type_term_of_nil_is_list` baseline); the declared `List[Int64]` store
/// constraint meets in to recover the element type, so reading `?x` yields
/// `List[Int64]`. The sort head stays `List` (the refine never changes the head).
#[test]
fn value_type_term_refines_underdetermined_bound_var_with_constraint() {
    let mut kb = load_kb();
    let xname = kb.intern("x");
    let vid = VarId::new(1, xname);
    let mut subst = Substitution::new();
    // ?x := nil — under-determined element (`List[?]`).
    let nil = nil_value(&kb);
    subst.bind_value(&kb, vid, nil);
    // Declared bound ?x : List[Int64], obtained by typing `cons(1, nil)`.
    let list_int64 = {
        let inner_nil = nil_value(&kb);
        let c = cons_value(&mut kb, Value::Int(1), inner_nil);
        value_type_term(&mut kb, &subst, &c)
    };
    subst.add_type_constraint(vid, list_int64);
    let ty = value_type_term(&mut kb, &subst, &Value::Var(Var::Global(vid)));
    let head = sort_functor_of_view(&kb, &ty).expect("refined type still has a List head");
    assert_sort_named(&kb, head, "List");
    // The discriminating assertion: without the refine the element is a `?_`.
    assert_type_param_is(&kb, &ty, "Int64");
}

/// WI-595 soundness — an INCOMPATIBLE store bound must NOT degrade the bound
/// value's own concrete type. `?x := 5` is `Int64`; a (bogus) `List[Int64]` bound
/// meets to `nothing`, so it is IGNORED and the value's `Int64` stands. The read
/// never collapses to bottom (which would silently suspend every later firing).
#[test]
fn value_type_term_ignores_incompatible_constraint() {
    let mut kb = load_kb();
    let xname = kb.intern("x");
    let vid = VarId::new(1, xname);
    let mut subst = Substitution::new();
    subst.bind_value(&kb, vid, Value::Int(5));
    let list_int64 = {
        let inner_nil = nil_value(&kb);
        let c = cons_value(&mut kb, Value::Int(1), inner_nil);
        value_type_term(&mut kb, &subst, &c)
    };
    subst.add_type_constraint(vid, list_int64);
    let ty = value_type_term(&mut kb, &subst, &Value::Var(Var::Global(vid)));
    let head = sort_functor_of_view(&kb, &ty).expect("an Int64 value keeps its own sort head");
    assert_sort_named(&kb, head, "Int64");
}

//! WI-284 — typed occurrences + `min_sort`.
//!
//! The typer keeps each occurrence's inferred type (`set_inferred_type`,
//! written by the `Stamp` work-frame as each node's `TypeResult` is
//! finalized), and `min_sort` widens that type to the least declared
//! sort. These tests pin the acceptance examples: `3` -> Int,
//! `cons(1, nil())` -> List, an entity value -> its sort, and an
//! unresolved type var -> None. They also check that *child*
//! occurrences carry their own type (uniform stamping), and that
//! `sort_functor_of` unwraps the typer's reflect Type shapes.

use std::rc::Rc;

use anthill_core::intern::Symbol;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
use anthill_core::kb::term::{Literal, Term, Var};
use anthill_core::kb::typing::{min_sort, sort_functor_of, type_check_node, TypingEnv};
use anthill_core::parse;
use anthill_core::span::{SourceId, SourceSpan};

/// stdlib + a small `Color` sort (for the entity-value case).
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

    let color = parse::parse("sort Color {\n  entity red\n  entity green\n}\n")
        .expect("parse Color");
    load::load(&mut kb, &color, &NullResolver).expect("Color load failed");
    kb
}

/// A source-origin expression occurrence with a throwaway span.
fn occ(expr: Expr) -> Rc<NodeOccurrence> {
    NodeOccurrence::new_expr(expr, SourceSpan::new(SourceId::from_raw(0), 0, 0), None)
}

/// Type the occurrence (asserting success), then return its `min_sort`.
fn typed_min_sort(kb: &mut KnowledgeBase, occ: &Rc<NodeOccurrence>) -> Option<Symbol> {
    let env = TypingEnv::empty();
    let r = type_check_node(kb, &env, occ, None);
    assert!(r.is_ok(), "expected the occurrence to type-check; got {:?}", r.err());
    min_sort(kb, occ)
}

/// A sort symbol resolves to `name` exactly, or to a qualified path
/// ending in `.name` (e.g. `anthill.prelude.Int`).
fn assert_sort_named(kb: &KnowledgeBase, sym: Symbol, name: &str) {
    let full = kb.resolve_sym(sym);
    assert!(
        full == name || full.ends_with(&format!(".{name}")),
        "expected min_sort {name}, got {full}",
    );
}

#[test]
fn min_sort_of_int_literal_is_int() {
    let mut kb = load_kb();
    let n3 = occ(Expr::Const(Literal::Int(3)));
    let ms = typed_min_sort(&mut kb, &n3).expect("min_sort(3) should be Some");
    assert_sort_named(&kb, ms, "Int");
    // The occurrence carries its inferred type, not just a derived sort.
    assert!(n3.inferred_type().is_some(), "typer must keep the inferred type");
}

#[test]
fn min_sort_of_list_constructor_is_list() {
    let mut kb = load_kb();
    let cons = kb
        .try_resolve_symbol("anthill.prelude.List.cons")
        .expect("List.cons registered");
    let nil = kb
        .try_resolve_symbol("anthill.prelude.List.nil")
        .expect("List.nil registered");
    let head = kb.intern("head");
    let tail = kb.intern("tail");

    // nil() — a no-arg List constructor.
    let onil = occ(Expr::Constructor { name: nil, pos_args: vec![], named_args: vec![] });
    let nil_sort = typed_min_sort(&mut kb, &onil).expect("min_sort(nil()) Some");
    assert_sort_named(&kb, nil_sort, "List");

    // cons(head: 1, tail: nil()) — the acceptance example.
    let o1 = occ(Expr::Const(Literal::Int(1)));
    let onil2 = occ(Expr::Constructor { name: nil, pos_args: vec![], named_args: vec![] });
    let ocons = occ(Expr::Constructor {
        name: cons,
        pos_args: vec![],
        named_args: vec![(head, Rc::clone(&o1)), (tail, Rc::clone(&onil2))],
    });
    let cons_sort = typed_min_sort(&mut kb, &ocons).expect("min_sort(cons(..)) Some");
    assert_sort_named(&kb, cons_sort, "List");

    // Uniform stamping: the child occurrences carry their own type too —
    // the head arg `1` -> Int, the tail `nil()` -> List.
    assert_sort_named(&kb, min_sort(&kb, &o1).expect("child `1` typed"), "Int");
    assert_sort_named(&kb, min_sort(&kb, &onil2).expect("child `nil()` typed"), "List");
}

#[test]
fn min_sort_of_entity_value_is_its_sort() {
    let mut kb = load_kb();
    let red_term = kb.resolve_qualified_name_term("Color.red");
    let red = match kb.get_term(red_term) {
        Term::Fn { functor, .. } => *functor,
        Term::Ref(s) => *s,
        other => panic!("Color.red resolved to unexpected term: {other:?}"),
    };
    let ored = occ(Expr::Constructor { name: red, pos_args: vec![], named_args: vec![] });
    let ms = typed_min_sort(&mut kb, &ored).expect("min_sort(red) should be Some");
    assert_sort_named(&kb, ms, "Color");
}

#[test]
fn min_sort_of_unresolved_type_var_is_none() {
    let mut kb = load_kb();
    let x = kb.intern("?x");
    let vid = kb.fresh_var(x);
    let ovar = occ(Expr::Var(Var::Global(vid)));
    let env = TypingEnv::empty();
    // A bare logical var types to a fresh type var (Ok), so the
    // occurrence IS typed — but its type has no declared sort head.
    let r = type_check_node(&mut kb, &env, &ovar, None);
    assert!(r.is_ok(), "bare var should type to a fresh type var; got {:?}", r.err());
    assert!(ovar.inferred_type().is_some(), "the type var is still kept");
    assert!(
        min_sort(&kb, &ovar).is_none(),
        "min_sort of an unresolved type var must be None",
    );
}

#[test]
fn sort_functor_of_returns_none_on_type_var() {
    let mut kb = load_kb();
    let t = kb.intern("?t");
    let tv = kb.make_type_var(t);
    assert!(
        sort_functor_of(&kb, tv).is_none(),
        "sort_functor_of of a type variable must be None",
    );
    // And it does extract a concrete sort from a sort_ref.
    let int_ty = kb.make_sort_ref_by_name("Int");
    let s = sort_functor_of(&kb, int_ty).expect("sort_functor_of(sort_ref(Int)) Some");
    assert_sort_named(&kb, s, "Int");
}
// (Removed `wi313_min_sort_of_kb_entity_is_kb`: it asserted `kb` is an entity,
// but WI-313 resolved with `kb` becoming a zero-arg operation in reflect.anthill
// — its property "a nullary-entity construction has min_sort = its sort" is
// covered by `min_sort_of_entity_value_is_its_sort` (Color.red).)

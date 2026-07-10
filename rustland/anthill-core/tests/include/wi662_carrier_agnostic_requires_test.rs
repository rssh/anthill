//! WI-662 — a sort-level `requires` whose spec is DENOTED-BEARING (a value fact,
//! not a hash-consed term) round-trips through the requires chain instead of
//! being silently dropped, and its spec is preserved carrier-faithfully.
//!
//! Bucket 2 of the carrier-agnostic-heads umbrella (WI-661): `RequiresEntry.spec`
//! moved from `TermId` to `Value`. Pre-WI-662, `direct_requires` skipped every
//! value-fact `SortRequiresInfo` (`fact_head_named_args() else continue`), so a
//! denoted-bearing sort-level requirement never reached the requires chain — it
//! could not even be *stored* (a `TermId` can't carry a `Value::Node`). Post-WI-390
//! the loader lowers every term-representable spec to a `Term`, so a value-fact
//! `SortRequiresInfo` is not producible from valid surface syntax (only from
//! opaque residue, which is separately gated). We therefore construct the value
//! fact directly — the exact head shape `assert_fact_carrier` emits when a spec
//! carries a `Value::Node` binding — and assert the round-trip; a ground control
//! pins that the term path is byte-identical (spec stays a `Value::Term`).

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
use anthill_core::kb::term::{Literal, Term};
use anthill_core::kb::typing::{requires_chain_flat, requires_tree};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use anthill_core::span::{SourceId, SourceSpan};

/// Stdlib + a two-sort source (`Foo` the required spec, `Carrier` the requiring
/// sort) → the loaded KB.
fn load_kb() -> KnowledgeBase {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let src = r#"
namespace test.wi662
  import anthill.prelude.{Int64}
  sort Foo
    sort T = ?
  end
  sort Carrier
    entity c(x: Int64)
  end
end
"#;
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let s = std::fs::read_to_string(p).expect("read stdlib");
            parse::parse(&s).expect("parse stdlib")
        })
        .collect();
    parsed.push(parse::parse(src).expect("parse test source"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).expect("load");
    kb
}

/// Assert a `SortRequiresInfo` fact `Carrier requires <spec>` through the SAME
/// carrier funnel the loader uses (`assert_fact_carrier` → a `Value::Entity` head
/// whenever a child value is non-term). With `denoted`, the spec is a
/// `SortView(Foo, k = <Value::Node>)` value; otherwise a bare ground `Foo` term.
/// Returns the `(Carrier, Foo)` symbols.
fn assert_requires_fact(kb: &mut KnowledgeBase, denoted: bool) -> (Symbol, Symbol) {
    let carrier = kb.try_resolve_symbol("test.wi662.Carrier").expect("Carrier");
    let foo = kb.try_resolve_symbol("test.wi662.Foo").expect("Foo");
    let requires_sym = kb.resolve_symbol("anthill.reflect.SortRequiresInfo");
    let sort_ref_field = kb.intern("sort_ref");
    let spec_field = kb.intern("spec");
    kb.register_entity_fields(requires_sym, vec![sort_ref_field, spec_field]);

    // sort_ref: a term whose functor IS the carrier (what `direct_requires`
    // matches against the queried sort via `same_symbol`).
    let sort_ref = Value::term(kb.make_name_term_from_sym(carrier));
    // spec base: a bare `Fn{Foo}` — `spec_base_functor` reads `Foo` off it whether
    // it is the whole spec (ground) or the SortView's positional-0 (denoted).
    let foo_base = Value::term(kb.make_name_term_from_sym(foo));
    let spec = if denoted {
        // A `Value::Node` binding — a `TermId` cannot carry it, the exact reason
        // the pre-WI-662 term-only `RequiresEntry.spec` dropped such a requirement.
        let sp = SourceSpan::new(SourceId::from_raw(0), 0, 0);
        let node = NodeOccurrence::new_expr(Expr::Const(Literal::Int(7)), sp, None);
        let sortview = kb.resolve_symbol("anthill.reflect.SortView");
        let k = kb.intern("k");
        Value::Entity {
            functor: sortview,
            pos: vec![foo_base].into(),
            named: vec![(k, Value::Node(node))].into(),
            ty: None,
        }
    } else {
        foo_base
    };

    let req_sort = kb.make_name_term("Requirement");
    let domain = kb.make_name_term("test.wi662");
    kb.assert_fact_carrier(
        requires_sym,
        Vec::new(),
        vec![(sort_ref_field, sort_ref), (spec_field, spec)],
        req_sort,
        domain,
        None,
    );
    (carrier, foo)
}

/// The chain entry for `Carrier`'s requirement on `Foo`, rebuilt fresh (the load
/// pass may have memoized an empty chain for the bare `Carrier`).
fn carrier_requires_foo_spec(kb: &mut KnowledgeBase) -> Option<Value> {
    let carrier = kb.try_resolve_symbol("test.wi662.Carrier").expect("Carrier");
    let foo = kb.try_resolve_symbol("test.wi662.Foo").expect("Foo");
    kb.invalidate_requires_chain_cache();
    requires_chain_flat(kb, carrier)
        .into_iter()
        .find(|e| e.required_sort == foo)
        .map(|e| e.spec)
}

#[test]
fn denoted_sort_requires_round_trips_through_chain() {
    let mut kb = load_kb();
    assert_requires_fact(&mut kb, /* denoted */ true);

    let spec = carrier_requires_foo_spec(&mut kb).expect(
        "WI-662: the denoted-bearing requires must appear in the chain (not be \
         dropped as a value-fact skip)",
    );
    assert!(
        !matches!(spec, Value::Term { .. }),
        "WI-662: the denoted spec must round-trip carrier-faithfully as a value \
         (not collapse/drop to a term); got {spec:?}",
    );
}

#[test]
fn ground_sort_requires_still_rides_as_term() {
    // Guard: the ground case is byte-identical — a term-representable spec keeps
    // the chain entry's spec a hash-consed `Value::Term`.
    let mut kb = load_kb();
    assert_requires_fact(&mut kb, /* denoted */ false);

    let spec = carrier_requires_foo_spec(&mut kb)
        .expect("the ground requires must appear in the chain");
    assert!(
        matches!(spec, Value::Term { .. }),
        "a fully-ground requires spec must ride as a hash-consed Value::Term \
         (byte-identical to pre-WI-662); got {spec:?}",
    );
}

/// WI-662 (the substitution fix): a denoted spec at a CHILD level whose co-carried
/// type-param binding references an enclosing param must be ROOT-SCOPED by the
/// WI-230 substitution composition — the denoted carrier is walked (its term
/// children substituted), not cloned verbatim. `Parent requires Middle[T = Int64]`
/// and `Middle requires Foo[X = Middle.T, E = <denoted>]`; `requires_tree(Parent)`
/// must compose `Middle.T := Int64` into the denoted Foo spec so `X = Int64`, while
/// preserving the denoted `E` binding (a `Value::Node` a `TermId` can't carry).
#[test]
fn denoted_child_spec_type_binding_is_root_scoped() {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    // `Parent requires Middle[T = Int64]` loads via natural syntax (a ground
    // SortView fact); the denoted `Middle requires Foo[...]` is asserted directly
    // (no surface syntax produces a value-fact requires — see the module note).
    let src = r#"
namespace test.wi662b
  import anthill.prelude.{Int64}
  sort Foo
    sort X = ?
  end
  sort Middle
    sort T = ?
  end
  sort Parent
    requires Middle[T = Int64]
  end
end
"#;
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let s = std::fs::read_to_string(p).expect("read stdlib");
            parse::parse(&s).expect("parse stdlib")
        })
        .collect();
    parsed.push(parse::parse(src).expect("parse test source"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).expect("load");

    let middle = kb.try_resolve_symbol("test.wi662b.Middle").expect("Middle");
    let foo = kb.try_resolve_symbol("test.wi662b.Foo").expect("Foo");
    let parent = kb.try_resolve_symbol("test.wi662b.Parent").expect("Parent");
    let middle_t = kb.try_resolve_symbol("test.wi662b.Middle.T").expect("Middle.T");
    let int64 = kb.resolve_symbol("anthill.prelude.Int64");

    // Assert the denoted `Middle requires Foo[X = Middle.T, E = <Node>]`.
    let requires_sym = kb.resolve_symbol("anthill.reflect.SortRequiresInfo");
    let sort_ref_field = kb.intern("sort_ref");
    let spec_field = kb.intern("spec");
    kb.register_entity_fields(requires_sym, vec![sort_ref_field, spec_field]);
    let sortview = kb.resolve_symbol("anthill.reflect.SortView");
    let x_sym = kb.intern("X");
    let e_sym = kb.intern("E");
    let sort_ref = Value::term(kb.make_name_term_from_sym(middle));
    let foo_base = Value::term(kb.make_name_term_from_sym(foo));
    // `X = Middle.T` — the enclosing param the parent binds to Int64.
    let x_ref = Value::term(kb.alloc(Term::Ref(middle_t)));
    let sp = SourceSpan::new(SourceId::from_raw(0), 0, 0);
    let node = NodeOccurrence::new_expr(Expr::Const(Literal::Int(9)), sp, None);
    let spec = Value::Entity {
        functor: sortview,
        pos: vec![foo_base].into(),
        named: vec![(x_sym, x_ref), (e_sym, Value::Node(node))].into(),
        ty: None,
    };
    let req_sort = kb.make_name_term("Requirement");
    let domain = kb.make_name_term("test.wi662b");
    kb.assert_fact_carrier(
        requires_sym,
        Vec::new(),
        vec![(sort_ref_field, sort_ref), (spec_field, spec)],
        req_sort,
        domain,
        None,
    );

    kb.invalidate_requires_chain_cache();
    let tree = requires_tree(&mut kb, parent);

    // Parent → Middle node → Foo sub-entry (the denoted, now root-scoped spec).
    let middle_node = tree
        .iter()
        .find(|n| n.entry.required_sort == middle)
        .expect("Parent requires Middle");
    let foo_node = middle_node
        .sub_requires
        .iter()
        .find(|n| n.entry.required_sort == foo)
        .expect("Middle requires Foo (denoted — must not be dropped)");

    // Still a denoted value carrier (not collapsed to a Term)...
    assert!(
        !matches!(foo_node.entry.spec, Value::Term { .. }),
        "the denoted Foo spec must stay a value carrier; got {:?}",
        foo_node.entry.spec,
    );
    // ...and its `X` binding must have been root-scoped `Middle.T := Int64`.
    let x_binding = match &foo_node.entry.spec {
        Value::Entity { named, .. } => named.iter().find(|(k, _)| *k == x_sym).map(|(_, v)| v),
        _ => None,
    }
    .expect("Foo spec carries an X binding");
    let x_head = match x_binding {
        Value::Term { id, .. } => match kb.get_term(*id) {
            Term::Ref(s) | Term::Ident(s) => Some(*s),
            Term::Fn { functor, .. } => Some(*functor),
            _ => None,
        },
        _ => None,
    };
    assert_eq!(
        x_head,
        Some(int64),
        "WI-662: `X = Middle.T` must be root-scoped to `X = Int64` (the denoted carrier \
         is walked, not cloned verbatim); got X head {x_head:?}, Middle.T is {middle_t:?}",
    );
}

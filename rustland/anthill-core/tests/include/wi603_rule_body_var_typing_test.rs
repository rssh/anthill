//! WI-603 — complete the untyped→typed transform for rule bodies.
//!
//! Before WI-603 only a rule body's DOT subtrees were stamped with a type (the
//! WI-282 dot-dispatch pass); a plain `f(?x, ?y)` atom was walked for its var
//! types (`collect_rule_var_types`) but STAMPED BY NOBODY, so its arg occurrences
//! carried no `inferred_type`. `type_rule_bodies` now collects each rule's var
//! types ONCE (from op-param / entity-field signatures, unified across the rule's
//! occurrences of a var) and stamps them onto every body `Var` leaf — a single
//! source of truth (the signature), read by the former two `collect_rule_var_types`
//! call sites instead of recomputed.
//!
//! These tests load a rule with a NON-dot body atom and assert its arg occurrences
//! now carry the signature-derived sort.

use anthill_core::intern::Symbol;
use anthill_core::kb::load::{self, LoadError, NullResolver};
use anthill_core::kb::node_occurrence::{for_each_child, Expr, NodeOccurrence};
use anthill_core::kb::typing::sort_functor_of_view;
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use std::rc::Rc;

fn load_capturing_errors(extra: &str) -> (KnowledgeBase, Vec<LoadError>) {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => (kb, vec![]),
        Err(errs) => (kb, errs),
    }
}

fn errors_text(errs: &[LoadError]) -> String {
    errs.iter().map(|e| format!("{e}")).collect::<Vec<_>>().join("\n")
}

/// The sort-head symbol of an occurrence's stamped `inferred_type`, if any.
fn occ_sort(kb: &KnowledgeBase, occ: &Rc<NodeOccurrence>) -> Option<Symbol> {
    occ.inferred_type().and_then(|t| sort_functor_of_view(kb, &t))
}

/// True iff `sym`'s resolved (qualified) name ends with `.short` or equals it.
fn is_named(kb: &KnowledgeBase, sym: Symbol, short: &str) -> bool {
    kb.resolve_sym(sym).rsplit('.').next() == Some(short)
}

/// Locate the first body atom applying `atom_short` in any non-fact rule under
/// `rule_qn`, returning `(pos_args, named_args)` as cloned occurrence handles.
/// Recurses through nested occurrences (so a nested goal is found too).
fn find_atom_args(
    kb: &KnowledgeBase,
    rule_qn: &str,
    atom_short: &str,
) -> Option<(Vec<Rc<NodeOccurrence>>, Vec<(Symbol, Rc<NodeOccurrence>)>)> {
    fn search(
        kb: &KnowledgeBase,
        occ: &Rc<NodeOccurrence>,
        atom_short: &str,
    ) -> Option<(Vec<Rc<NodeOccurrence>>, Vec<(Symbol, Rc<NodeOccurrence>)>)> {
        let expr = occ.as_expr()?;
        match expr {
            Expr::Apply { functor: f, pos_args, named_args, .. }
            | Expr::Constructor { name: f, pos_args, named_args, .. }
            | Expr::Instantiation { name: f, pos_args, named_args }
                if kb.resolve_sym(*f).rsplit('.').next() == Some(atom_short) =>
            {
                return Some((pos_args.clone(), named_args.clone()));
            }
            _ => {}
        }
        let mut result = None;
        for_each_child(expr, |c| {
            if result.is_none() {
                result = search(kb, c, atom_short);
            }
        });
        result
    }
    let sym = kb.try_resolve_symbol(rule_qn)?;
    for rid in kb.rules_by_functor(sym) {
        if kb.is_fact(rid) {
            continue;
        }
        for n in kb.rule_body_nodes(rid).iter() {
            if let Some(found) = search(kb, n, atom_short) {
                return Some(found);
            }
        }
    }
    None
}

// ── Acceptance: a positional `f(?x, ?y)` op-call atom carries arg types ──

#[test]
fn rule_body_op_call_args_typed_from_signature() {
    // `f(x: Int64, y: Int64) -> Bool` used as a rule-body goal `f(?x, ?y)` — a
    // plain (non-dot) atom. After WI-603 each positional arg occurrence carries
    // `inferred_type` Int64, sourced from `f`'s param signature. Pre-WI-603 the
    // dot-only stamp never visited this atom, so the args were untyped.
    let src = r#"
        namespace test.wi603.opcall
          import anthill.prelude.{Bool, Int64}
          operation f(x: Int64, y: Int64) -> Bool
          rule r(?x, ?y)
            :- f(?x, ?y)
        end
    "#;
    let (kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(), "expected clean load; got:\n{}", errors_text(&errs));

    let (pos, _named) = find_atom_args(&kb, "test.wi603.opcall.r", "f")
        .expect("the `f(?x, ?y)` body atom must be present");
    assert_eq!(pos.len(), 2, "f has two positional args");
    for (i, arg) in pos.iter().enumerate() {
        let sort = occ_sort(&kb, arg).unwrap_or_else(|| {
            panic!("arg {i} of f(?x, ?y) must carry an inferred_type (WI-603)")
        });
        assert!(
            is_named(&kb, sort, "Int64"),
            "arg {i} of f(?x, ?y) must be typed Int64 from f's signature; got {}",
            kb.resolve_sym(sort),
        );
    }
}

// ── An entity-constructor body atom types its named args too ────────────

#[test]
fn rule_body_entity_constructor_named_args_typed() {
    // The entity-field source of truth: `point(x: Int64, y: Int64)` as a body goal
    // `point(x: ?x, y: ?y)`. Each named-arg occurrence carries Int64 from the
    // field's declared type.
    let src = r#"
        namespace test.wi603.ctor
          import anthill.prelude.Int64
          sort Point
            entity point(x: Int64, y: Int64)
          end
          rule holds(?x, ?y)
            :- point(x: ?x, y: ?y)
        end
    "#;
    let (kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(), "expected clean load; got:\n{}", errors_text(&errs));

    let (_pos, named) = find_atom_args(&kb, "test.wi603.ctor.holds", "point")
        .expect("the `point(x: ?x, y: ?y)` body atom must be present");
    assert_eq!(named.len(), 2, "point has two named args");
    for (field, arg) in &named {
        let sort = occ_sort(&kb, arg).unwrap_or_else(|| {
            panic!("field `{}` occurrence must carry an inferred_type (WI-603)", kb.resolve_sym(*field))
        });
        assert!(
            is_named(&kb, sort, "Int64"),
            "field `{}` must be typed Int64; got {}",
            kb.resolve_sym(*field),
            kb.resolve_sym(sort),
        );
    }
}

// ── Cross-occurrence unification: a var shared across two atoms ──────────

#[test]
fn rule_body_var_shared_across_atoms_is_typed_at_both() {
    // `?x` appears in two DISTINCT body atoms — `box(v: ?x)` and `point(x: ?x, …)`
    // — both constraining it to Int64. The "one genuinely new fact" of WI-603 is
    // the cross-occurrence unification living on the occurrence: BOTH occurrences
    // of `?x` must carry the (unified) Int64 type.
    let src = r#"
        namespace test.wi603.shared
          import anthill.prelude.Int64
          sort Box
            entity box(v: Int64)
          end
          sort Point
            entity point(x: Int64, y: Int64)
          end
          rule linked(?x, ?y)
            :- box(v: ?x), point(x: ?x, y: ?y)
        end
    "#;
    let (kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(), "expected clean load; got:\n{}", errors_text(&errs));

    // `?x` at the `box` atom's `v:` field.
    let (_bp, box_named) = find_atom_args(&kb, "test.wi603.shared.linked", "box")
        .expect("the `box(v: ?x)` atom must be present");
    let box_x = &box_named.iter().find(|(f, _)| is_named(&kb, *f, "v")).expect("box.v arg").1;
    let box_x_sort = occ_sort(&kb, box_x).expect("box(v: ?x) arg must be typed (WI-603)");
    assert!(is_named(&kb, box_x_sort, "Int64"), "box(v: ?x) arg should be Int64");

    // The same `?x` at the `point` atom's `x:` field.
    let (_pp, point_named) = find_atom_args(&kb, "test.wi603.shared.linked", "point")
        .expect("the `point(x: ?x, y: ?y)` atom must be present");
    let point_x = &point_named.iter().find(|(f, _)| is_named(&kb, *f, "x")).expect("point.x arg").1;
    let point_x_sort = occ_sort(&kb, point_x).expect("point(x: ?x) arg must be typed (WI-603)");
    assert!(is_named(&kb, point_x_sort, "Int64"), "point(x: ?x) arg should be Int64");
}

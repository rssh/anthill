//! WI-282 — rule-body dot dispatch (the rule-body peer of WI-279).
//!
//! A value-receiver dot form `?x.field` / `?x.method(args)` must dispatch in a
//! RULE body, not just an operation body — "dot means the same in all
//! expression positions". The typer's `dispatch_rule_body_dots` sweep rewrites
//! each `Expr::DotApply` in every rule body to its method-`Apply` / reflect
//! `field_access` form BEFORE the body reaches SLD, using the rule's
//! constrained De Bruijn var types so a receiver `?x` resolves to a concrete
//! sort.
//!
//! An UNRESOLVED receiver (a polymorphic body var, or the reflect
//! `Expr.dot_apply` constructor carried as data — which `materialize_from_handle`
//! collapses to `Expr::DotApply`) is left untouched, not errored: only a genuine
//! member-not-found on a KNOWN sort is a loud error.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver, LoadError};
use anthill_core::kb::node_occurrence::{NodeOccurrence, Expr, for_each_child};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, Var};
use anthill_core::parse;
use smallvec::SmallVec;
use std::rc::Rc;

fn load_capturing_errors(extra: &str) -> (KnowledgeBase, Vec<LoadError>) {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
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

/// Does any body atom of any non-fact rule under `functor_qn` still carry an
/// `Expr::DotApply`? (After dispatch, a value dot is gone.)
fn rule_bodies_have_dot(kb: &KnowledgeBase, functor_qn: &str) -> bool {
    fn occ_has_dot(occ: &Rc<NodeOccurrence>) -> bool {
        let Some(expr) = occ.as_expr() else { return false };
        if matches!(expr, Expr::DotApply { .. }) {
            return true;
        }
        let mut found = false;
        for_each_child(expr, |c| found = found || occ_has_dot(c));
        found
    }
    let Some(sym) = kb.try_resolve_symbol(functor_qn) else { return false };
    let mut any = false;
    for rid in kb.rules_by_functor(sym) {
        if kb.is_fact(rid) { continue; }
        for n in kb.rule_body_nodes(rid).iter() {
            if occ_has_dot(n) { any = true; }
        }
    }
    any
}

/// Does any body atom of any non-fact rule under `functor_qn` apply the
/// operation `op_qn`? (After method dispatch, `?b.peek()` becomes `peek(?b)`.)
fn rule_bodies_apply(kb: &KnowledgeBase, functor_qn: &str, op_short: &str) -> bool {
    fn occ_applies(kb: &KnowledgeBase, occ: &Rc<NodeOccurrence>, op_short: &str) -> bool {
        let Some(expr) = occ.as_expr() else { return false };
        if let Expr::Apply { functor, .. } = expr {
            if kb.resolve_sym(*functor).rsplit('.').next() == Some(op_short) {
                return true;
            }
        }
        let mut found = false;
        for_each_child(expr, |c| found = found || occ_applies(kb, c, op_short));
        found
    }
    let Some(sym) = kb.try_resolve_symbol(functor_qn) else { return false };
    for rid in kb.rules_by_functor(sym) {
        if kb.is_fact(rid) { continue; }
        for n in kb.rule_body_nodes(rid).iter() {
            if occ_applies(kb, n, op_short) { return true; }
        }
    }
    false
}

// ── Acceptance: `?x.field` in a rule body dispatches before SLD ─────────

#[test]
fn rule_body_field_access_dispatches() {
    // `?p` is typed `Point` by the `p:` field of the `wrap` constructor goal;
    // `?p.x` must dispatch to a `field_access`, leaving NO DotApply in the body.
    let src = r#"
        namespace wi282.field
          export Point
          export Wrapper
          sort Point
            entity point(x: Int64, y: Int64)
          end
          sort Wrapper
            entity wrap(p: Point, v: Int64)
          end
          rule holds(?p, ?v)
            :- wrap(p: ?p, v: ?v), eq(?v, ?p.x)
        end
    "#;
    let (kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(), "expected clean load; got:\n{}", errors_text(&errs));
    assert!(
        !rule_bodies_have_dot(&kb, "wi282.field.holds"),
        "expected ?p.x to be dispatched (no Expr::DotApply left in the rule body)"
    );
}

// ── Acceptance: `?x.method(args)` in a rule body dispatches ─────────────

#[test]
fn rule_body_method_call_dispatches() {
    // `?b` is typed `Box` by the `b:` field of `holder`; `?b.peek()` must
    // dispatch to `peek(?b)` — an `Apply` of the operation, no DotApply left.
    let src = r#"
        namespace wi282.method
          export Box
          export Holder
          sort Box
            entity box(value: Int64)
            operation peek(b: Box) -> Int64 = ?b.value
          end
          sort Holder
            entity holder(b: Box)
          end
          rule peeks(?b, ?v)
            :- holder(b: ?b), eq(?v, ?b.peek())
        end
    "#;
    let (kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(), "expected clean load; got:\n{}", errors_text(&errs));
    assert!(
        !rule_bodies_have_dot(&kb, "wi282.method.peeks"),
        "expected ?b.peek() to be dispatched (no Expr::DotApply left in the rule body)"
    );
    assert!(
        rule_bodies_apply(&kb, "wi282.method.peeks", "peek"),
        "expected ?b.peek() to dispatch to an Apply of `peek`"
    );
}

// ── A genuine member-not-found on a KNOWN sort is a loud error ──────────

#[test]
fn rule_body_dot_no_such_member_errors() {
    // `?p: Point` has no member `bogus` — a clear no-match error, not a silent
    // pass-through into SLD.
    let src = r#"
        namespace wi282.nomatch
          export Point
          export Wrapper
          sort Point
            entity point(x: Int64, y: Int64)
          end
          sort Wrapper
            entity wrap(p: Point, v: Int64)
          end
          rule bad(?p, ?v)
            :- wrap(p: ?p, v: ?v), eq(?v, ?p.bogus)
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    let text = errors_text(&errs);
    assert!(
        text.contains("bogus") || text.to_lowercase().contains("dot"),
        "expected a no-match error for ?p.bogus; got:\n{text}"
    );
}

// ── A polymorphic / unconstrained receiver is left alone (no error) ─────

#[test]
fn rule_body_dot_unresolved_receiver_left_alone() {
    // `?p` is never constrained to a sort (it only appears as a dot receiver),
    // so its type is unresolved. The dot cannot be decided — leave it untouched,
    // do NOT error (the pre-WI-282 status quo: it flows to SLD structurally).
    let src = r#"
        namespace wi282.poly
          export P
          sort P
            entity p(x: Int64)
          end
          rule loose(?p)
            :- p(x: ?p.x)
        end
    "#;
    let (kb, errs) = load_capturing_errors(src);
    assert!(
        errs.is_empty(),
        "an unresolved-receiver dot must not error (status quo); got:\n{}",
        errors_text(&errs)
    );
    // The dot was undecidable, so it is preserved (still a DotApply).
    assert!(
        rule_bodies_have_dot(&kb, "wi282.poly.loose"),
        "an undecidable dot should be left in place"
    );
}

// ── Resolution does not regress: a dispatched rule body still resolves ──
// (no panic). The dispatched `field_access` / method `Apply` is the right
// STRUCTURAL form; SLD does not yet EVALUATE it (the separate "computational
// rule body" concern), exactly as the undispatched `dot_apply` goal did not.
// These tests pin that dispatch + resolution is panic-free — the rule-body
// peer of op-body dispatch — not that the projection is computed.

fn resolve_query(kb: &mut KnowledgeBase, functor_qn: &str, arity: usize) -> usize {
    let functor = kb.resolve_symbol(functor_qn);
    let args: SmallVec<[anthill_core::kb::term::TermId; 4]> = (0..arity)
        .map(|i| {
            let s = kb.intern(&format!("q{i}"));
            let v = kb.fresh_var(s);
            kb.alloc(Term::Var(Var::Global(v)))
        })
        .collect();
    let goal = kb.alloc(Term::Fn { functor, pos_args: args, named_args: SmallVec::new() });
    let cfg = ResolveConfig { max_solutions: 10, ..ResolveConfig::default() };
    kb.resolve(&[goal], &cfg).len()
}

#[test]
fn dispatched_nested_field_access_resolves_without_panic() {
    let src = r#"
        namespace wi282.res
          export Point
          export Wrapper
          sort Point
            entity point(x: Int64, y: Int64)
          end
          sort Wrapper
            entity wrap(p: Point, v: Int64)
          end
          rule holds(?p, ?v)
            :- wrap(p: ?p, v: ?v), eq(?v, ?p.x)
          fact wrap(p: point(x: 7, y: 8), v: 7)
        end
    "#;
    let (mut kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(), "clean load expected; got:\n{}", errors_text(&errs));
    assert!(
        !rule_bodies_have_dot(&kb, "wi282.res.holds"),
        "the rule-body dot must be dispatched before SLD"
    );
    // Resolving the dispatched rule must not panic the resolver (the
    // `field_access` builtin's term-only narrow is never reached as a goal).
    let _ = resolve_query(&mut kb, "wi282.res.holds", 2);
}

#[test]
fn dispatched_top_level_field_goal_resolves_without_panic() {
    // A bare top-level `?b.flag` body atom dispatches to a top-level
    // `field_access(?b, flag)` goal — the exact shape that would hit the
    // resolver's `Value::Node` term-only narrow if it were classified there.
    // It must resolve without panic.
    let src = r#"
        namespace wi282.toplevel
          export Box
          export Holder
          sort Box
            entity box(flag: Bool, value: Int64)
          end
          sort Holder
            entity holder(b: Box)
          end
          rule active(?b)
            :- holder(b: ?b), ?b.flag
          fact holder(b: box(flag: true, value: 1))
        end
    "#;
    let (mut kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(), "clean load expected; got:\n{}", errors_text(&errs));
    assert!(
        !rule_bodies_have_dot(&kb, "wi282.toplevel.active"),
        "the top-level rule-body dot must be dispatched"
    );
    let _ = resolve_query(&mut kb, "wi282.toplevel.active", 1);
}

// ── Reflect data safety: a sort whose constructor is named `dot_apply` ──

#[test]
fn reflect_dot_apply_constructor_loads_clean() {
    // The stdlib `anthill.reflect.Expr` sort has a `dot_apply` CONSTRUCTOR; its
    // auto-generated induction rule carries `dot_apply(...)` as DATA, which
    // `materialize_from_handle` collapses to `Expr::DotApply`. The dispatch sweep
    // must NOT mistake that for a value dispatch and error. Loading stdlib alone
    // (no extra source) must be clean.
    let (_kb, errs) = load_capturing_errors("namespace wi282.empty\nend");
    assert!(
        errs.is_empty(),
        "stdlib (incl. the reflect Expr.induction rule) must load clean; got:\n{}",
        errors_text(&errs)
    );
}

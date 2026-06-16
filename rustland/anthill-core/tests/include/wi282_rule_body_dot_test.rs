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
// (no panic). A dispatched `field_access` is the right STRUCTURAL form; with
// WI-482 it also EVALUATES at SLD (see `*_evaluates_*` tests below). A method
// `Apply` does NOT yet evaluate as a rule-body goal (WI-483). These no-panic
// tests query with UNBOUND head vars, which residualize via the caller-var
// delay pre-check before the body runs — they pin panic-freedom, not the
// projection (the `*_evaluates_*` tests below use ground queries that run the
// body and assert the computed value).

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

/// Resolve `functor_qn(args...)` with explicit GROUND argument terms and return
/// the solution count. A ground query has no caller logic vars, so the
/// caller-var delay pre-check is skipped and the rule body actually runs — the
/// shape that exercises rule-body field_access EVALUATION (WI-482).
fn resolve_query_ground(kb: &mut KnowledgeBase, functor_qn: &str, args: &[anthill_core::kb::term::TermId]) -> usize {
    let functor = kb.resolve_symbol(functor_qn);
    let goal = kb.alloc(Term::Fn {
        functor,
        pos_args: SmallVec::from_slice(args),
        named_args: SmallVec::new(),
    });
    let cfg = ResolveConfig { max_solutions: 10, ..ResolveConfig::default() };
    kb.resolve(&[goal], &cfg).len()
}

/// Build a ground `point(x: <x>, y: <y>)` entity term in `kb`.
fn make_point(kb: &mut KnowledgeBase, point_qn: &str, x: i64, y: i64) -> anthill_core::kb::term::TermId {
    use anthill_core::kb::term::Literal;
    let point = kb.resolve_symbol(point_qn);
    let xk = kb.intern("x");
    let yk = kb.intern("y");
    let xv = kb.alloc(Term::Const(Literal::Int(x)));
    let yv = kb.alloc(Term::Const(Literal::Int(y)));
    let mut named: SmallVec<[(anthill_core::intern::Symbol, anthill_core::kb::term::TermId); 2]> = SmallVec::new();
    named.push((xk, xv));
    named.push((yk, yv));
    kb.alloc(Term::Fn { functor: point, pos_args: SmallVec::new(), named_args: named })
}

#[test]
fn dispatched_nested_field_access_resolves_without_panic() {
    let src = r#"
        namespace wi282.res
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

// ── WI-482: a dispatched rule-body dot EVALUATES at SLD ─────────────────

// NOTE on these tests' shape: the dot receiver must be typed for dispatch, and
// only an ENTITY CONSTRUCTOR field types a rule var (a free predicate like
// `pt(p: ?p)` leaves `?p` unconstrained, so its dot is left undispatched). So
// each rule constrains the receiver through an entity constructor goal (`wrap`),
// mirroring the working dispatch tests above. Queries are GROUND so the body
// runs (an unbound-var query residualizes via the caller-var delay pre-check).

#[test]
fn rule_body_nested_field_access_evaluates_in_eq() {
    // `eq(?x, ?p.x)` dispatches `?p.x` to a nested `field_access(?p, "x")`; the
    // resolver must reduce that projection to the field value and compare —
    // `xcoord(point(7,8), 7)` succeeds, `xcoord(point(7,8), 99)` fails.
    let src = r#"
        namespace wi282.eval
          sort Point
            entity point(x: Int64, y: Int64)
          end
          sort Wrapper
            entity wrap(p: Point, v: Int64)
          end
          rule xcoord(?p, ?x)
            :- wrap(p: ?p, v: ?v), eq(?x, ?p.x)
          fact wrap(p: point(x: 7, y: 8), v: 0)
        end
    "#;
    let (mut kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(), "clean load expected; got:\n{}", errors_text(&errs));
    assert!(
        !rule_bodies_have_dot(&kb, "wi282.eval.xcoord"),
        "the rule-body dot must be dispatched before SLD"
    );
    let pt = make_point(&mut kb, "wi282.eval.Point.point", 7, 8);
    let seven = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(7)));
    let n_match = resolve_query_ground(&mut kb, "wi282.eval.xcoord", &[pt, seven]);
    assert_eq!(n_match, 1, "field_access(point(7,8), x) must evaluate to 7 ⇒ eq(7,7) succeeds");

    let pt2 = make_point(&mut kb, "wi282.eval.Point.point", 7, 8);
    let ninetynine = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(99)));
    let n_miss = resolve_query_ground(&mut kb, "wi282.eval.xcoord", &[pt2, ninetynine]);
    assert_eq!(n_miss, 0, "field_access yields 7, not 99 ⇒ eq(99,7) fails (no silent success)");
}

#[test]
fn rule_body_nested_field_access_evaluates_in_arith() {
    // `mul(?p.x, 10, ?r)` (an arithmetic builtin) must reduce the dotted operand
    // `?p.x` before multiplying: `scaled(point(3,4), 30)` succeeds, `…(…, 31)`
    // fails.
    let src = r#"
        namespace wi282.arith
          sort Point
            entity point(x: Int64, y: Int64)
          end
          sort Wrapper
            entity wrap(p: Point, v: Int64)
          end
          rule scaled(?p, ?r)
            :- wrap(p: ?p, v: ?v), mul(?p.x, 10, ?r)
          fact wrap(p: point(x: 3, y: 4), v: 0)
        end
    "#;
    let (mut kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(), "clean load expected; got:\n{}", errors_text(&errs));
    assert!(
        !rule_bodies_have_dot(&kb, "wi282.arith.scaled"),
        "the rule-body dot must be dispatched before SLD"
    );
    let pt = make_point(&mut kb, "wi282.arith.Point.point", 3, 4);
    let thirty = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(30)));
    let n_match = resolve_query_ground(&mut kb, "wi282.arith.scaled", &[pt, thirty]);
    assert_eq!(n_match, 1, "mul(field_access(point(3,4),x)=3, 10) must be 30");

    let pt2 = make_point(&mut kb, "wi282.arith.Point.point", 3, 4);
    let thirtyone = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(31)));
    let n_miss = resolve_query_ground(&mut kb, "wi282.arith.scaled", &[pt2, thirtyone]);
    assert_eq!(n_miss, 0, "3*10 = 30, not 31");
}

#[test]
fn rule_body_nested_field_access_chain_evaluates() {
    // A two-hop chain `?w.p.x` dispatches to
    // `field_access(field_access(?w, "p"), "x")`; `reduce_dot_value` must collapse
    // it inside-out. `inner(wrap(point(5,6)), 5)` succeeds, `…(…, 6)` fails.
    let src = r#"
        namespace wi282.chain
          sort Point
            entity point(x: Int64, y: Int64)
          end
          sort Wrapper
            entity wrap(p: Point)
          end
          sort Outer
            entity outer(w: Wrapper)
          end
          rule inner(?w, ?x)
            :- outer(w: ?w), eq(?x, ?w.p.x)
          fact outer(w: wrap(p: point(x: 5, y: 6)))
        end
    "#;
    let (mut kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(), "clean load expected; got:\n{}", errors_text(&errs));
    assert!(
        !rule_bodies_have_dot(&kb, "wi282.chain.inner"),
        "the chained rule-body dot must be dispatched before SLD"
    );
    let make_wrap = |kb: &mut KnowledgeBase| {
        let wrap_sym = kb.resolve_symbol("wi282.chain.Wrapper.wrap");
        let pk = kb.intern("p");
        let pt = make_point(kb, "wi282.chain.Point.point", 5, 6);
        let mut named: SmallVec<[(anthill_core::intern::Symbol, anthill_core::kb::term::TermId); 2]> = SmallVec::new();
        named.push((pk, pt));
        kb.alloc(Term::Fn { functor: wrap_sym, pos_args: SmallVec::new(), named_args: named })
    };
    let wrap = make_wrap(&mut kb);
    let five = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(5)));
    let n_match = resolve_query_ground(&mut kb, "wi282.chain.inner", &[wrap, five]);
    assert_eq!(n_match, 1, "?w.p.x must collapse to 5");

    let wrap2 = make_wrap(&mut kb);
    let six = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(6)));
    let n_miss = resolve_query_ground(&mut kb, "wi282.chain.inner", &[wrap2, six]);
    assert_eq!(n_miss, 0, "?w.p.x is 5, not 6");
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

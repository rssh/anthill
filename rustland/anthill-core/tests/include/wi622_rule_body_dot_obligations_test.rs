//! WI-622 — rule-body dot obligations should be relational-aware, generalizing
//! WI-602 (value-preconditions) to the OTHER op-body-only obligation a rule-body
//! value-method-dot can trip: `UnconstrainedTypeParam` (WI-270).
//!
//! WI-557 premise: a rule body is SLD/relational, so an op-body call-site
//! obligation over a symbolic rule-body var legitimately FLOATS.
//! `dispatch_dots_in_occ` types the dot with `expected: None`, so a return-only
//! type-param cannot be pinned at that isolated call site — yet SLD resolution
//! unifies it against the goal context (or it stays a harmless phantom on a
//! value-less return-only param). Pre-WI-622 that surfaced as a spurious
//! `UnconstrainedTypeParam` hard load error (WI-602 had inverted
//! `dispatch_dots_in_occ` to surface every `type_check_node` error except
//! `DotDispatchNoMatch{None}`, so this obligation now reaches the loader).
//!
//! Unlike the value-precondition case there is NO definite sub-case to still
//! raise on: "unconstrained" means "no binding at all" (a genuine type CONFLICT
//! surfaces as a contradiction / `TypeMismatch`, not here), which is exactly the
//! float condition in a rule body — so the check is skipped there, while op-body
//! checking is unchanged.
//!
//! The sibling spec-op `DispatchNoMatch` obligation needs no gate: dot dispatch
//! resolves a spec op only on a CONCRETE (or abstract-spec) receiver, never an
//! abstract type-param, so a rule-body spec-op dot that reaches that raise always
//! has a concrete carrier — a DEFINITE failure that must stay loud. The last test
//! pins that a concrete-provider spec-op dot dispatches CLEAN in a rule body (the
//! relational-safe path), guarding against a future regression that would make it
//! spurious.

use anthill_core::kb::load::{self, LoadError, NullResolver};
use anthill_core::kb::node_occurrence::{for_each_child, Expr, NodeOccurrence};
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

/// Does any body atom of any non-fact rule under `functor_qn` still carry an
/// `Expr::DotApply`? (After dispatch a value dot is gone — so `true` here means
/// the dot was NOT dispatched.)
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
    for rid in kb.rules_by_functor(sym) {
        if kb.is_fact(rid) {
            continue;
        }
        for n in kb.rule_body_nodes(rid).iter() {
            if occ_has_dot(n) {
                return true;
            }
        }
    }
    false
}

// `make[T]` carries its type-param `T` ONLY in the return type, so a call with no
// caller-side `expected` cannot pin it. `GHolder` gives a `Gadget`-typed var.
const GADGET: &str = r#"
  import anthill.prelude.{Int64, Option}
  sort Gadget
    entity gadget(id: Int64)
    operation make[T](g: Gadget) -> Option[T = T]
  end
  sort GHolder
    entity gholder(g: Gadget)
  end
"#;

// ── Acceptance 1: rule-body return-only type-param dot DISPATCHES clean ───────

#[test]
fn rule_body_return_only_type_param_dot_dispatches() {
    // `?g.make()` in a RULE body: `?g: Gadget` (from `gholder.g`). `make`'s `T`
    // appears only in the return, and the rule-body dot is typed with
    // `expected: None`, so pre-WI-622 the call raised a spurious
    // `UnconstrainedTypeParam` ("expected a type for 'T', got unconstrained").
    // WI-622 skips that op-body-only obligation in rule-body context: the dot
    // dispatches (`make(?g)`) and `T` floats, pinned by resolution-time
    // unification or left a harmless phantom.
    let src = format!(
        r#"
namespace anthill.test.wi622utp
{GADGET}
  rule uses(?g, ?r)
    :- gholder(g: ?g), eq(?r, ?g.make())
end
"#
    );
    let (kb, errs) = load_capturing_errors(&src);
    assert!(
        errs.is_empty(),
        "a return-only type-param op dotted in a rule body must load clean (the \
         type param floats — no op-body call-site pin applies); got:\n{}",
        errors_text(&errs)
    );
    assert!(
        !rule_bodies_have_dot(&kb, "anthill.test.wi622utp.uses"),
        "the rule-body dot `?g.make()` must DISPATCH (no leftover Expr::DotApply)"
    );
}

// ── Acceptance 2: op-body checking is UNCHANGED (gate is rule-body-scoped) ─────

#[test]
fn op_body_return_only_type_param_dot_still_errors() {
    // The SAME op via the dot form `?g.make()` in an OP body, in a `let` with no
    // annotation → `expected: None`, so `T` (return-only) is genuinely
    // unconstrained at this imperative call site: a loud `UnconstrainedTypeParam`
    // (the WI-270 behavior). This proves the WI-622 gate keys on RULE-body
    // context, NOT on dot dispatch generally.
    let src = format!(
        r#"
namespace anthill.test.wi622opdot
{GADGET}
  operation caller(g: Gadget) -> Int64
    = let x = ?g.make()
      0
end
"#
    );
    let (_kb, errs) = load_capturing_errors(&src);
    let text = errors_text(&errs).to_lowercase();
    assert!(
        text.contains("unconstrained") || text.contains("type for 't'"),
        "an op-body dot call to a return-only type-param op must still flag the \
         unconstrained type param (the gate is rule-body-scoped, not dot-scoped); \
         got:\n{}",
        errors_text(&errs)
    );
}

// ── Acceptance 3: a concrete-provider spec-op dot in a rule body is CLEAN ──────

#[test]
fn rule_body_concrete_spec_op_dot_dispatches() {
    // `?a.pick(?b)` where `?a: Widget` and `fact Comparable[T = Widget]`: `pick`
    // resolves to `Comparable.pick` via the provider (the WI-281 spec-satisfaction
    // dot), and the synthesized `pick(?a, ?b)` dispatches on the CONCRETE carrier
    // `Widget`. This is the relational-safe spec-op path: no `DispatchNoMatch`,
    // because the carrier is concrete and genuinely provides the spec. It guards
    // the WI-622 finding that the spec-op obligation needs no rule-body gate (a
    // dot never resolves a spec op on an abstract type-param carrier, so any
    // reachable `DispatchNoMatch` here is a definite concrete failure).
    let src = r#"
namespace anthill.test.wi622specdot
  import anthill.prelude.{Int64}
  sort Comparable
    sort T = ?
    operation pick(a: T, b: T) -> T = a
  end
  sort Widget
    entity widget(id: Int64)
    fact Comparable[T = Widget]
  end
  sort WPair
    entity wpair(a: Widget, b: Widget)
  end
  rule choose(?a, ?b, ?r)
    :- wpair(a: ?a, b: ?b), eq(?r, ?a.pick(?b))
end
"#;
    let (kb, errs) = load_capturing_errors(src);
    assert!(
        errs.is_empty(),
        "a concrete-provider spec-op dotted in a rule body must load clean \
         (Widget provides Comparable — a resolvable dispatch, not a float); got:\n{}",
        errors_text(&errs)
    );
    assert!(
        !rule_bodies_have_dot(&kb, "anthill.test.wi622specdot.choose"),
        "the rule-body dot `?a.pick(?b)` must DISPATCH (no leftover Expr::DotApply)"
    );
}

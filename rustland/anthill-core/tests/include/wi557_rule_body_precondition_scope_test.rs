//! WI-557 — scope the WI-539 call-site value-precondition `requires`-check to
//! OP-BODY context; it must not leak into rule-body dot-dispatch.
//!
//! The WI-539 check (typing.rs `check_apply_iter`) is an op-body Hoare obligation:
//! the callee's value precondition `σ(requires)` must be PROVED from the local-
//! interpretation Γ at the imperative call site. A rule body is SLD/relational —
//! there is no call-site Γ and no imperative semantics — so the obligation does
//! not apply there. `dispatch_rule_body_dots` is ALSO a client of
//! `check_apply_iter` (via `dispatch_dots_in_occ -> type_check_node`), with a
//! structurally empty Γ. Before WI-557 a value precondition over a rule-body
//! variable would float (`definite_only`) and raise a spurious
//! `UnsatisfiedPrecondition`, which `dispatch_dots_in_occ`'s `Err(_)` arm SWALLOWS
//! — leaving the dot UNDISPATCHED (so the bug is observable as a missed dispatch,
//! not as a surfaced error).
//!
//! WI-557 marks the rule-body env (`TypingEnv::mark_rule_body_dispatch`) so the
//! precondition check is skipped there. The two acceptance facts:
//!   * a value-precondition op invoked via a dot in a RULE body now DISPATCHES
//!     cleanly (no leftover `Expr::DotApply`, the op `Apply` is present) — proving
//!     the spurious obligation no longer fires;
//!   * the SAME op invoked in an OP body with a symbolic argument STILL raises
//!     `UnsatisfiedPrecondition` — op-body checking (the flag stays `false`) is
//!     unchanged.

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
/// `Expr::DotApply`? (After dispatch, a value dot is gone — so `true` here means
/// the dot was NOT dispatched, the pre-WI-557 swallowed-error symptom.)
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

/// Does any body atom of any non-fact rule under `functor_qn` apply the operation
/// short-named `op_short`? (After dispatch, `?b.guarded(?k)` becomes
/// `guarded(?b, ?k)`.)
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
        if kb.is_fact(rid) {
            continue;
        }
        for n in kb.rule_body_nodes(rid).iter() {
            if occ_applies(kb, n, op_short) {
                return true;
            }
        }
    }
    false
}

/// `guarded(b, n)` is a `Box` member carrying a VALUE precondition
/// `requires neq(n, 0)` — the rule-body / op-body call sites below dispatch on
/// `?b.guarded(?k)` and `?b.guarded(?n)` respectively.
const PRELUDE: &str = r#"
  import anthill.prelude.{Int64}
  sort Box
    entity box(value: Int64)
    operation guarded(b: Box, n: Int64) -> Int64
      requires neq(n, 0)
      = n
  end
  sort Holder
    entity holder(b: Box, k: Int64)
  end
"#;

// ── Acceptance 1: rule-body dot over a value-precondition op DISPATCHES ──────

#[test]
fn rule_body_value_precondition_dot_dispatches() {
    // `?b.guarded(?k)` in a RULE body: `?b: Box` (from `holder.b`), `?k: Int64`
    // (from `holder.k`). The callee's `requires neq(n, 0)` would float over the
    // rule-body var `?k` and (pre-WI-557) raise an `UnsatisfiedPrecondition` that
    // `dispatch_dots_in_occ` swallows, leaving the dot undispatched. WI-557 skips
    // the precondition check in rule-body context, so the dot dispatches: no
    // `DotApply` left, and `guarded(?b, ?k)` is applied.
    let src = format!(
        r#"
namespace anthill.test.wi557rule
{PRELUDE}
  rule uses(?b, ?k, ?r)
    :- holder(b: ?b, k: ?k), eq(?r, ?b.guarded(?k))
end
"#
    );
    let (kb, errs) = load_capturing_errors(&src);
    assert!(
        errs.is_empty(),
        "a value-precondition op dotted in a rule body must load clean; got:\n{}",
        errors_text(&errs)
    );
    assert!(
        !rule_bodies_have_dot(&kb, "anthill.test.wi557rule.uses"),
        "the rule-body dot `?b.guarded(?k)` must DISPATCH (no leftover Expr::DotApply); \
         a leftover dot is the pre-WI-557 swallowed-precondition symptom"
    );
    assert!(
        rule_bodies_apply(&kb, "anthill.test.wi557rule.uses", "guarded"),
        "the dispatched body must apply `guarded(?b, ?k)`"
    );
}

// ── Acceptance 2: op-body precondition checking is UNCHANGED ──────────────────

#[test]
fn op_body_value_precondition_dot_call_still_errors() {
    // The SAME op via the DOT form `?b.guarded(?n)` in an OP body — symbolic
    // argument `?n`, so `neq(?n, 0)` floats and the obligation is undischarged: a
    // loud `UnsatisfiedPrecondition` (the WI-539 behavior). This proves the
    // WI-557 gate keys on RULE-body context, NOT on dot dispatch generally:
    // op-body dot dispatch runs `check_apply_iter` with the flag `false`, so the
    // precondition still fires and the error surfaces (op bodies do not swallow).
    // (Free-op PLAIN-call precondition checking is covered by WI-539's
    // `precondition_unproved_for_symbolic_argument`, in this same suite.)
    let src = format!(
        r#"
namespace anthill.test.wi557opdot
{PRELUDE}
  operation caller(b: Box, n: Int64) -> Int64 =
    ?b.guarded(?n)
end
"#
    );
    let (_kb, errs) = load_capturing_errors(&src);
    let text = errors_text(&errs);
    assert!(
        text.to_lowercase().contains("precondition"),
        "an op-body dot call must still flag the unsatisfied precondition for a \
         symbolic argument (the gate is rule-body-scoped, not dot-scoped); got:\n{text}"
    );
}

// ── WI-602: a DEFINITE rule-body precondition violation must be rejected ───────

/// WI-602 (FILED, currently failing — hence `#[ignore]`): WI-557 skips the
/// WI-539 call-site precondition check for ALL rule-body context to avoid a
/// spurious `UnsatisfiedPrecondition` over a SYMBOLIC rule-body var (which
/// legitimately FLOATS — see `rule_body_value_precondition_dot_dispatches`, the
/// symbolic case that must stay clean). But the gate is UNCONDITIONAL, so it also
/// swallows a DEFINITE violation: `?b.guarded(0)` with a literal `0` makes
/// `neq(0, 0)` ground-FALSE (refuted, not floating), yet the rule body loads clean
/// while the SAME call in an op body raises `unsatisfied precondition`
/// (`op_body_value_precondition_dot_call_still_errors`). That is a real soundness
/// hole — at simp-firing time the violating term is even injected unchecked, since
/// eval does not re-check value-preconditions.
///
/// This test asserts the CORRECT behavior (the definite violation IS rejected), so
/// it FAILS today and PASSES once the rule-body gate becomes refutation-aware
/// (raise on a ground-REFUTED precondition, skip only a float — the WI-067/WI-292
/// polarity). Un-ignore it when WI-602 lands.
#[test]
#[ignore = "WI-602: rule-body gate unconditionally skips DEFINITE precondition violations; \
            un-ignore once the gate is refutation-aware"]
fn rule_body_definite_precondition_violation_is_rejected() {
    // DEFINITE violation: the precondition arg is the LITERAL `0`, so `neq(0, 0)`
    // is ground-false — a refutation, NOT a symbolic float.
    let rule_src = format!(
        r#"
namespace anthill.test.wi600
{PRELUDE}
  rule uses(?b, ?r)
    :- holder(b: ?b, k: ?), eq(?r, ?b.guarded(0))
end
"#
    );
    let (_kb, errs) = load_capturing_errors(&rule_src);
    let text = errors_text(&errs);
    assert!(
        text.to_lowercase().contains("precondition"),
        "WI-602: a DEFINITE rule-body precondition violation `guarded(_, 0)` \
         (`neq(0,0)` ground-false) must be rejected, exactly as the op-body form is; \
         WI-557's unconditional rule-body skip is too broad. errors were:\n{text}"
    );
}

#[test]
fn op_body_value_precondition_qualified_call_still_errors() {
    // The non-dot analog: the SAME `Box` member called by its QUALIFIED name
    // `Box.guarded(...)` in an OP body, with a symbolic argument `?n`. The
    // precondition `neq(?n, 0)` floats and is undischarged — a loud
    // `UnsatisfiedPrecondition` (WI-539, unchanged by the WI-557 gate). A member
    // op is NOT in bare namespace scope, so it is reached from outside its sort
    // only via qualification or dot — bare `guarded(...)` is `unknown functor`,
    // which is correct member scoping and independent of `requires`.
    let src = format!(
        r#"
namespace anthill.test.wi557opqual
{PRELUDE}
  operation caller(n: Int64) -> Int64 =
    Box.guarded(box(value: 1), n)
end
"#
    );
    let (_kb, errs) = load_capturing_errors(&src);
    let text = errors_text(&errs);
    assert!(
        text.to_lowercase().contains("precondition"),
        "an op-body qualified call must still flag the unsatisfied precondition \
         for a symbolic argument; got:\n{text}"
    );
}

//! WI-221 — defer-to-requirement detection (open-bound trigger).
//!
//! When a spec-op call is reached via the enclosing sort's `requires`
//! chain, the impl is determined at runtime by the requirement value
//! the caller supplies — NOT by the static type-args. The Pin-now
//! rewrite (WI-218) must be skipped for such calls. Otherwise
//! ground-via-requires calls are silently mis-dispatched to a single
//! impl when the impl was meant to vary per requirement.
//!
//! Reference: docs/design/operation-call-model.md
//! §"Defer-to-requirement detection".


use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::typing::{
    lookup_spec_op_dispatch,
    find_unique_impl_op,
    requires_chain_flat,
    DispatchOutcome,
};
use anthill_core::kb::subst::Substitution;
use anthill_core::kb::term::{Term, Var};
use anthill_core::parse;

fn load_with(extra: &str) -> KnowledgeBase {
    let files = crate::common::collect_stdlib_and_rust_bindings();
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
        Ok(_) => kb,
        Err(errs) => {
            for e in &errs { eprintln!("{e}"); }
            // Tests below tolerate non-fatal load issues — the post-load
            // KB still carries the requires/SortProvidesInfo records the
            // dispatch outcome depends on. Mirrors the load_with helper
            // in wi210_dispatch_test.rs.
            kb
        }
    }
}

/// Build a per-call substitution that binds the named type-param of
/// `spec_qn` (e.g. "T") to the named carrier sort. Mirrors the helper
/// in wi210_dispatch_test.rs.
fn subst_with_param(
    kb: &mut KnowledgeBase,
    spec_qn: &str,
    param_short: &str,
    carrier_qn: &str,
) -> Substitution {
    let param_qn = format!("{spec_qn}.{param_short}");
    let param_sym = kb.try_resolve_symbol(&param_qn)
        .unwrap_or_else(|| panic!("{param_qn} not registered"));
    let alias_sym = kb.try_resolve_symbol("SortAlias").expect("SortAlias");
    let mut param_var = None;
    for rid in kb.rules_by_functor(alias_sym) {
        if !kb.is_fact(rid) { continue; }
        let head = kb.rule_head(rid);
        if let Term::Fn { pos_args, .. } = kb.get_term(head).clone() {
            if pos_args.len() < 2 { continue; }
            if let Term::Fn { functor, .. } = kb.get_term(pos_args[0]) {
                if *functor == param_sym {
                    if let Term::Var(Var::Global(v)) = kb.get_term(pos_args[1]) {
                        param_var = Some(*v);
                    }
                }
            }
        }
    }
    let param_var = param_var.unwrap_or_else(||
        panic!("{param_short}'s SortAlias not found for {spec_qn}"));

    let carrier_sym = kb.try_resolve_symbol(carrier_qn)
        .unwrap_or_else(|| panic!("{carrier_qn} not registered"));
    let carrier_term = kb.make_sort_ref(carrier_sym);

    let mut subst = Substitution::new();
    subst.bind_term(param_var, carrier_term);
    subst
}

#[test]
fn dispatch_defers_when_call_reaches_spec_via_requires() {
    // Sort `Wi221Box` declares `requires Eq[T = Int64]`. A spec-op call
    // (Eq.eq at T=Int64) reached from inside Wi221Box's body must be
    // classified as Deferred even though stdlib has `fact Eq[T = Int64]`
    // (Int64 as the impl) — the impl chosen at runtime depends on which
    // requirement value the caller of Wi221Box passes.
    //
    // Without the WI-221 patch, find_unique_impl_op would return
    // Unique(Int64.eq) and Pin-now-rewrite the call, even though the
    // dispatch should go through frame.requirements at runtime.
    let mut kb = load_with(r#"
        namespace test.wi221.open_bound
          import anthill.prelude.{Eq, Int64}
          export Wi221Box
          sort Wi221Box
            requires Eq[T = Int64]
          end
        end
    "#);

    let eq_op = kb.try_resolve_symbol("anthill.prelude.Eq.eq")
        .expect("Eq.eq registered by stdlib");
    let spec_sort = lookup_spec_op_dispatch(&kb, eq_op)
        .expect("Eq.eq is a spec op");
    let subst = subst_with_param(
        &mut kb,
        "anthill.prelude.Eq",
        "T",
        "anthill.prelude.Int64",
    );
    let op_short = kb.intern("eq");

    let enclosing = kb.try_resolve_symbol("test.wi221.open_bound.Wi221Box")
        .expect("Wi221Box registered");

    // Sanity check: with no enclosing sort, the existing Pin-now path
    // resolves Eq[T=Int64] to a Unique impl (Int64's `fact Eq[T = Int64]`).
    let pin_now = find_unique_impl_op(&mut kb, &subst, spec_sort, op_short, &[]);
    assert!(matches!(pin_now, DispatchOutcome::Unique(_)),
        "without enclosing sort, expected Unique (Pin-now); got {pin_now:?}");

    // WI-221 patch: with Wi221Box as enclosing sort (whose `requires`
    // chain covers Eq[T=Int64]), dispatch must defer.
    let chain = requires_chain_flat(&kb, enclosing);
    let deferred = find_unique_impl_op(&mut kb, &subst, spec_sort, op_short, &chain);
    assert_eq!(deferred, DispatchOutcome::Deferred,
        "WI-221: expected Deferred when call reaches Eq.eq via Wi221Box's \
         `requires Eq[T = Int64]` clause; got {deferred:?}");
}

#[test]
fn dispatch_pins_when_enclosing_sort_does_not_require_spec() {
    // Counter-test: an enclosing sort whose `requires` chain does NOT
    // mention the spec must still produce the Pin-now rewrite. WI-221's
    // open-bound check is narrow — it triggers only when the spec is
    // genuinely reached via `requires`.
    let mut kb = load_with(r#"
        namespace test.wi221.no_require
          export Wi221Plain
          sort Wi221Plain
            entity wi221_plain
          end
        end
    "#);

    let eq_op = kb.try_resolve_symbol("anthill.prelude.Eq.eq")
        .expect("Eq.eq registered by stdlib");
    let spec_sort = lookup_spec_op_dispatch(&kb, eq_op)
        .expect("Eq.eq is a spec op");
    let subst = subst_with_param(
        &mut kb,
        "anthill.prelude.Eq",
        "T",
        "anthill.prelude.Int64",
    );
    let op_short = kb.intern("eq");

    let enclosing = kb.try_resolve_symbol("test.wi221.no_require.Wi221Plain")
        .expect("Wi221Plain registered");
    let chain = requires_chain_flat(&kb, enclosing);

    let outcome = find_unique_impl_op(&mut kb, &subst, spec_sort, op_short, &chain);
    assert!(matches!(outcome, DispatchOutcome::Unique(_)),
        "WI-221: enclosing sort without `requires Eq[T=Int64]` must not \
         defer — Pin-now still applies. Got {outcome:?}");
}

#[test]
fn dispatch_defers_when_requires_uses_open_param() {
    // Variant: the enclosing sort's `requires` clause uses its own
    // open type-param (`requires Eq[T]` where T is the sort's parameter).
    // A per-call subst that ground-binds that param to Int64 should still
    // be deferred — the impl chosen at runtime depends on whichever
    // Eq requirement the caller passes for the chosen T.
    let mut kb = load_with(r#"
        namespace test.wi221.open_t
          import anthill.prelude.Eq
          export Wi221Generic
          sort Wi221Generic
            sort T = ?
            requires Eq[T]
          end
        end
    "#);

    let eq_op = kb.try_resolve_symbol("anthill.prelude.Eq.eq")
        .expect("Eq.eq registered by stdlib");
    let spec_sort = lookup_spec_op_dispatch(&kb, eq_op)
        .expect("Eq.eq is a spec op");
    let subst = subst_with_param(
        &mut kb,
        "anthill.prelude.Eq",
        "T",
        "anthill.prelude.Int64",
    );
    let op_short = kb.intern("eq");

    let enclosing = kb.try_resolve_symbol("test.wi221.open_t.Wi221Generic")
        .expect("Wi221Generic registered");
    let chain = requires_chain_flat(&kb, enclosing);

    let outcome = find_unique_impl_op(&mut kb, &subst, spec_sort, op_short, &chain);
    assert_eq!(outcome, DispatchOutcome::Deferred,
        "WI-221: `requires Eq[T]` (with T as the sort's open param) must \
         defer for any per-call ground binding — the impl varies per \
         requirement. Got {outcome:?}");
}

//! WI-222 Phase C+D / WI-234 (Model 1) / WI-237 (names model) —
//! defer-to-requirement IR rewrite.
//!
//! When a spec-op call is reached via the enclosing sort's `requires`
//! chain (open-bound trigger from WI-221), the typer must rewrite the
//! `apply(fn = spec_op, args = ...)` term into the runtime form
//! `apply_within(fn = Ref(spec_op_qn), args = ...,
//!  requirements = [<dispatching dict>])`. The runtime dispatches via
//! the dispatching dict at `requirements[0]` — reads its functor (the
//! impl sort name) and looks up `<functor>.<op_short>` for the impl op.
//!
//! Names model shape (WI-237): the dispatching dict is sourced via
//! `var_ref(name = Ref(__req_<spec>))` — a named requirement-param
//! read against the caller's frame, replacing the prior positional
//! `requirement_at_current(slot=N+1)`. The synthesized name comes from
//! `synth_req_names`/`req_name_for_chain_index` — `__req_<spec short
//! name, lowercased>` for the entry's position in the enclosing sort's
//! transitive `requires_chain`.
//!
//! Reference: docs/design/operation-call-model.md
//! §"Names model", §"Channel cardinality (v0)".

mod common;

use anthill_core::kb::term::Term;
use anthill_core::kb::typing::get_named_arg;
use common::interp_for;

#[test]
fn deferred_call_rewrites_to_apply_within_with_spec_op_fn() {
    // Sort `Wi222Box` declares `requires Eq[T]` and an op `use_eq` that
    // calls `eq(a, b)`. With the sort's `requires` chain in scope, the
    // call must classify as Deferred and emit names-model shape:
    // `apply_within(fn = Ref(Eq.eq), args = ...,
    //  requirements = [var_ref(name = Ref(__req_eq))])`.
    // The dispatching-dict expression reads the caller's frame
    // requirement-param `__req_eq` by name (no positional slot).
    let src = r#"
namespace test.wi222.defer_rewrite
  import anthill.prelude.Eq.{eq}
  import anthill.prelude.{Eq, Bool}
  export Wi222Box
  sort Wi222Box
    sort T = ?
    requires Eq[T]
    operation use_eq(a: T, b: T) -> Bool = eq(a, b)
  end
end
"#;
    let mut interp = interp_for(src);
    let expected_name = interp.kb_mut().intern("__req_eq");
    let kb = interp.kb();

    let eq_sym = kb.try_resolve_symbol("anthill.prelude.Eq.eq")
        .expect("Eq.eq registered");

    // Find the rewrite recorded against Eq.eq's spec-op symbol — there
    // must be exactly one (use_eq's body has one eq() call).
    let mut rewritten_for_eq: Option<_> = None;
    for (rewritten_tid, spec_sym) in kb.dispatch_origin_iter() {
        if spec_sym == eq_sym {
            assert!(rewritten_for_eq.is_none(),
                "expected exactly one defer rewrite for Eq.eq; saw a second");
            rewritten_for_eq = Some(rewritten_tid);
        }
    }
    let rewritten_tid = rewritten_for_eq
        .expect("Eq.eq call inside `requires Eq[T]` sort must be rewritten");

    let aw_sym = kb.try_resolve_symbol("anthill.reflect.Expr.apply_within")
        .expect("apply_within in stdlib");
    let var_ref_sym = kb.try_resolve_symbol("anthill.reflect.Expr.var_ref")
        .expect("var_ref in stdlib");
    let cons_sym = kb.try_resolve_symbol("anthill.prelude.List.cons")
        .expect("List.cons in stdlib");
    let nil_sym = kb.try_resolve_symbol("anthill.prelude.List.nil")
        .expect("List.nil in stdlib");

    let (functor, named_args) = match kb.get_term(rewritten_tid) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        other => panic!("rewritten term must be a Fn; got {other:?}"),
    };
    assert_eq!(functor, aw_sym,
        "deferred call must rewrite to apply_within; got functor {}",
        kb.qualified_name_of(functor));

    // fn = Ref(eq_sym) — names model: fn is the spec-op symbol directly,
    // dispatch happens at apply_within reduction via the dispatching dict.
    let fn_tid = get_named_arg(kb, &named_args, "fn")
        .expect("apply_within must carry `fn`");
    match kb.get_term(fn_tid) {
        Term::Ref(s) => assert_eq!(*s, eq_sym,
            "fn-position must be Ref(Eq.eq); got Ref({})",
            kb.qualified_name_of(*s)),
        other => panic!("apply_within fn must be Term::Ref(spec_op); got {other:?}"),
    }

    // requirements = cons(var_ref(name=Ref(__req_eq)), nil) — single
    // named-requirement read; Wi222Box's transitive chain is [Eq], the
    // synthesized name for slot 0 is `__req_eq`.
    let reqs_tid = get_named_arg(kb, &named_args, "requirements")
        .expect("apply_within must carry `requirements`");
    let (reqs_functor, reqs_named) = match kb.get_term(reqs_tid) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        other => panic!("requirements must be a list term; got {other:?}"),
    };
    assert_eq!(reqs_functor, cons_sym,
        "single dispatching dict must be wrapped in cons(..., nil); got {}",
        kb.qualified_name_of(reqs_functor));

    let head_tid = get_named_arg(kb, &reqs_named, "head")
        .expect("cons must carry `head`");
    let (head_functor, head_named) = match kb.get_term(head_tid) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        other => panic!("dispatching dict must be a Fn; got {other:?}"),
    };
    assert_eq!(head_functor, var_ref_sym,
        "dispatching dict for Defer must be var_ref (names model); got {}",
        kb.qualified_name_of(head_functor));
    let name_tid = get_named_arg(kb, &head_named, "name")
        .expect("var_ref must carry `name`");
    match kb.get_term(name_tid) {
        Term::Ref(s) => assert_eq!(*s, expected_name,
            "var_ref name for slot 0 (Eq) must be Ref(__req_eq); got Ref({})",
            kb.qualified_name_of(*s)),
        other => panic!("name must be Term::Ref(<sym>); got {other:?}"),
    }

    let tail_tid = get_named_arg(kb, &reqs_named, "tail")
        .expect("cons must carry `tail`");
    let tail_functor = match kb.get_term(tail_tid) {
        Term::Fn { functor, .. } => *functor,
        other => panic!("tail must be a Fn (nil); got {other:?}"),
    };
    assert_eq!(tail_functor, nil_sym,
        "single-entry list's tail must be nil; got {}",
        kb.qualified_name_of(tail_functor));

    // args must be carried over (non-nil — use_eq passes two args).
    let args_tid = get_named_arg(kb, &named_args, "args")
        .expect("apply_within must carry `args`");
    let args_functor = match kb.get_term(args_tid) {
        Term::Fn { functor, .. } => *functor,
        other => panic!("args must be a list term; got {other:?}"),
    };
    assert_ne!(args_functor, nil_sym,
        "use_eq's `eq(a, b)` has two args, so args list must be non-nil");
}

#[test]
fn requirement_name_tracks_requires_chain_entry() {
    // Sort declares two requires: `Eq[T]` then `Ordered[T]`. A call to
    // `Ordered.compare(...)` from inside the sort's body must emit a
    // dispatching-dict expression `var_ref(name = Ref(__req_ordered))`
    // — Ordered's slot in the transitive `requires_chain` (chain shape
    // `[Eq, Ordered, Eq]` here, with Ordered at index 1) is named via
    // `synth_req_names` as `__req_ordered` (no collision: only one
    // Ordered in the chain).
    let src = r#"
namespace test.wi222.multi_requires
  import anthill.prelude.Ordered.{compare}
  import anthill.prelude.{Eq, Ordered, Int}
  export Wi222Multi
  sort Wi222Multi
    sort T = ?
    requires Eq[T]
    requires Ordered[T]
    operation use_compare(a: T, b: T) -> Int = compare(a, b)
  end
end
"#;
    let mut interp = interp_for(src);
    let expected_name = interp.kb_mut().intern("__req_ordered");
    let kb = interp.kb();

    let compare_sym = kb.try_resolve_symbol("anthill.prelude.Ordered.compare")
        .expect("Ordered.compare registered");
    let var_ref_sym = kb.try_resolve_symbol("anthill.reflect.Expr.var_ref")
        .expect("var_ref in stdlib");

    let mut rewritten_for_compare = None;
    for (rewritten_tid, spec_sym) in kb.dispatch_origin_iter() {
        if spec_sym == compare_sym {
            rewritten_for_compare = Some(rewritten_tid);
        }
    }
    let rewritten_tid = rewritten_for_compare
        .expect("Ordered.compare call inside multi-requires sort must be rewritten");

    // Drill into the rewritten apply_within's requirements[0] to find
    // the dispatching dict's name.
    let named_args = match kb.get_term(rewritten_tid) {
        Term::Fn { named_args, .. } => named_args.clone(),
        other => panic!("rewritten must be Fn; got {other:?}"),
    };
    let reqs_tid = get_named_arg(kb, &named_args, "requirements")
        .expect("apply_within must carry `requirements`");
    let reqs_named = match kb.get_term(reqs_tid) {
        Term::Fn { named_args, .. } => named_args.clone(),
        other => panic!("requirements must be Fn (cons); got {other:?}"),
    };
    let head_tid = get_named_arg(kb, &reqs_named, "head")
        .expect("cons must carry `head`");
    let (head_functor, head_named) = match kb.get_term(head_tid) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        other => panic!("dispatching dict must be Fn (var_ref); got {other:?}"),
    };
    assert_eq!(head_functor, var_ref_sym,
        "dispatching dict must be var_ref (names model); got {}",
        kb.qualified_name_of(head_functor));
    let name_tid = get_named_arg(kb, &head_named, "name")
        .expect("var_ref must carry `name`");
    match kb.get_term(name_tid) {
        Term::Ref(s) => assert_eq!(*s, expected_name,
            "Ordered's chain slot maps to synthesized `__req_ordered`; got Ref({})",
            kb.qualified_name_of(*s)),
        other => panic!("name must be Term::Ref(<sym>); got {other:?}"),
    }
}

#[test]
fn dispatching_dict_is_caller_direct_requirement_var_ref() {
    // Wi222Outer declares `requires Ordered[T]`; Ordered itself declares
    // `requires Eq[T]` (from stdlib). Wi222Outer's transitive chain is
    // [Ordered, Eq], synthesized names [`__req_ordered`, `__req_eq`].
    //
    // The body calls `compare(a, b)`. Names-model emit: the apply_within
    // carries a single-entry requirements channel with the dispatching
    // Ordered dictionary, sourced as `var_ref(name = Ref(__req_ordered))`
    // — the caller's own Ordered slot, by name. The callee's `__req_eq`
    // binding is populated at runtime by expanding the dispatching
    // dict's `sub_requires[0]` (Ordered's bundled Eq), not by an IR-time
    // projection. See operation-call-model.md §"Channel cardinality
    // (v0)" — every apply_within has exactly one requirements entry.
    let src = r#"
namespace test.wi222.proj_deps
  import anthill.prelude.Ordered.{compare}
  import anthill.prelude.{Ordered, Int}
  export Wi222Outer
  sort Wi222Outer
    sort T = ?
    requires Ordered[T]
    operation use_compare(a: T, b: T) -> Int = compare(a, b)
  end
end
"#;
    let mut interp = interp_for(src);
    let expected_name = interp.kb_mut().intern("__req_ordered");
    let kb = interp.kb();

    let compare_sym = kb.try_resolve_symbol("anthill.prelude.Ordered.compare")
        .expect("Ordered.compare registered");
    let var_ref_sym = kb.try_resolve_symbol("anthill.reflect.Expr.var_ref")
        .expect("var_ref registered");
    let cons_sym = kb.try_resolve_symbol("anthill.prelude.List.cons")
        .expect("List.cons registered");
    let nil_sym = kb.try_resolve_symbol("anthill.prelude.List.nil")
        .expect("List.nil registered");

    let mut rewritten_for_compare = None;
    for (rewritten_tid, spec_sym) in kb.dispatch_origin_iter() {
        if spec_sym == compare_sym {
            rewritten_for_compare = Some(rewritten_tid);
        }
    }
    let rewritten_tid = rewritten_for_compare
        .expect("Ordered.compare call inside `requires Ordered[T]` sort must be rewritten");

    let named_args = match kb.get_term(rewritten_tid) {
        Term::Fn { named_args, .. } => named_args.clone(),
        other => panic!("rewritten must be Fn; got {other:?}"),
    };

    // requirements list must be `cons(head=var_ref(name=Ref(__req_ordered)), tail=nil)`
    // — single dispatching dict naming the caller's own Ordered slot.
    let reqs_tid = get_named_arg(kb, &named_args, "requirements")
        .expect("apply_within must carry `requirements`");
    let (cons_functor, cons_named) = match kb.get_term(reqs_tid) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        other => panic!("requirements must be a Fn (cons); got {other:?}"),
    };
    assert_eq!(cons_functor, cons_sym,
        "names model: requirements list must be a single-entry cons; got {}",
        kb.qualified_name_of(cons_functor));

    let head_tid = get_named_arg(kb, &cons_named, "head")
        .expect("cons must carry `head`");
    let (head_functor, head_named) = match kb.get_term(head_tid) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        other => panic!("head must be Fn (var_ref); got {other:?}"),
    };
    assert_eq!(head_functor, var_ref_sym,
        "dispatching dict for Defer must be var_ref (names model); got {}",
        kb.qualified_name_of(head_functor));

    let name_tid = get_named_arg(kb, &head_named, "name")
        .expect("var_ref must carry `name`");
    match kb.get_term(name_tid) {
        Term::Ref(s) => assert_eq!(*s, expected_name,
            "var_ref must name the caller's Ordered slot (`__req_ordered`); got Ref({})",
            kb.qualified_name_of(*s)),
        other => panic!("name must be Term::Ref(<sym>); got {other:?}"),
    }

    // Tail must be nil — single-entry channel under v0.
    let tail_tid = get_named_arg(kb, &cons_named, "tail")
        .expect("cons must carry `tail`");
    let tail_functor = match kb.get_term(tail_tid) {
        Term::Fn { functor, .. } => *functor,
        other => panic!("tail must be Fn (nil); got {other:?}"),
    };
    assert_eq!(tail_functor, nil_sym,
        "single-entry channel's tail must be nil; got {}",
        kb.qualified_name_of(tail_functor));
}

#[test]
fn pin_now_upgrades_to_apply_within_when_impl_parent_has_requires() {
    // Phase E (i): when Pin-now resolves to an impl whose parent sort
    // declares any `requires`, the impl body needs a populated
    // `frame.requirements`. The typer must emit `apply_within(fn =
    // Ref(impl), …)` instead of plain `apply` so the runtime threads
    // the requirements channel.
    //
    // Setup: a generic spec `Wi222ESpec` with one body-less op `act`,
    // and an impl sort `Wi222EImpl` that hosts `fact Wi222ESpec[T = Int]`
    // AND declares its own `requires Eq[T = Int]`. A driver sort
    // calls `act(x)` at T=Int — Pin-now resolves to Wi222EImpl.act.
    // Because Wi222EImpl declares `requires Eq[T = Int]`, the call must
    // upgrade to apply_within.
    let src = r#"
namespace test.wi222.phase_e_pin_now
  import anthill.prelude.{Eq, Int, Bool}
  export Wi222ESpec, Wi222EImpl, Wi222EDriver
  sort Wi222ESpec
    sort T = ?
    operation act(x: T) -> Bool
  end
  sort Wi222EImpl
    fact Wi222ESpec[T = Int]
    requires Eq[T = Int]
    operation act(x: Int) -> Bool = true
  end
  sort Wi222EDriver
    import test.wi222.phase_e_pin_now.Wi222ESpec.{act}
    operation drive(x: Int) -> Bool = act(x)
  end
end
"#;
    let interp = interp_for(src);
    let kb = interp.kb();

    let spec_act = kb.try_resolve_symbol("test.wi222.phase_e_pin_now.Wi222ESpec.act")
        .expect("Wi222ESpec.act registered");
    let aw_sym = kb.try_resolve_symbol("anthill.reflect.Expr.apply_within")
        .expect("apply_within in stdlib");
    let impl_act = kb.try_resolve_symbol("test.wi222.phase_e_pin_now.Wi222EImpl.act")
        .expect("Wi222EImpl.act registered");

    // Find the rewrite recorded against the spec op symbol.
    let mut rewritten_for_act = None;
    for (rewritten_tid, spec_sym) in kb.dispatch_origin_iter() {
        if spec_sym == spec_act {
            rewritten_for_act = Some(rewritten_tid);
        }
    }
    let rewritten_tid = rewritten_for_act
        .expect("Pin-now of Wi222ESpec.act must rewrite (impl resolves uniquely to Wi222EImpl.act)");

    // Phase E (i): the rewritten term must be apply_within (not plain apply),
    // with fn = Ref(Wi222EImpl.act) (concrete fn, not requirement_at_current).
    let (functor, named_args) = match kb.get_term(rewritten_tid) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        other => panic!("rewritten must be Fn; got {other:?}"),
    };
    assert_eq!(functor, aw_sym,
        "Pin-now to impl with requires must emit apply_within (not plain apply); \
         got functor {}", kb.qualified_name_of(functor));

    let fn_tid = get_named_arg(kb, &named_args, "fn")
        .expect("apply_within must carry `fn`");
    match kb.get_term(fn_tid) {
        Term::Ref(s) => assert_eq!(*s, impl_act,
            "Pin-now's apply_within fn must be a plain Ref to the impl op; got Ref({})",
            kb.qualified_name_of(*s)),
        other => panic!("Pin-now apply_within fn must be Term::Ref(impl); got {other:?}"),
    }
}

#[test]
fn pinned_call_does_not_get_apply_within_rewrite() {
    // Counter-test: when an enclosing sort doesn't declare `requires
    // Eq[T]`, a ground `eq(a, b)` call must be Pin-now-rewritten (WI-218,
    // direct fn-symbol substitution) — NOT defer-to-requirement-rewritten
    // to apply_within.
    let src = r#"
namespace test.wi222.no_defer
  import anthill.prelude.Eq.{eq}
  import anthill.prelude.Bool
  operation pin_call(a: Int, b: Int) -> Bool = eq(a, b)
end
"#;
    let interp = interp_for(src);
    let kb = interp.kb();

    let aw_sym = kb.try_resolve_symbol("anthill.reflect.Expr.apply_within")
        .expect("apply_within in stdlib");

    // Walk every dispatch_origin entry and assert none of the rewritten
    // terms is an apply_within (would mean we mis-classified a ground
    // call as deferred). Pin-now's rewrite target is a plain `apply` term
    // with the impl symbol substituted into `fn`.
    for (rewritten_tid, _spec_sym) in kb.dispatch_origin_iter() {
        if let Term::Fn { functor, .. } = kb.get_term(rewritten_tid) {
            assert_ne!(*functor, aw_sym,
                "pin_call has no enclosing requires; the eq() call must \
                 Pin-now-rewrite, not defer to apply_within");
        }
    }
}

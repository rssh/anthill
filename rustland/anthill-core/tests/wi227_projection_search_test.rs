//! WI-227 — recursive projection search for `apply_within.requirements`.
//!
//! The requirement-insertion pass must turn each callee dep into one of
//! three IR forms:
//!
//! 1. **Flat** — `requirement_at_current(slot=i)` when the dep is at top
//!    level of the caller's frame requirements (the v0 stdlib case).
//! 2. **Nested** — `requirement_at_sort(requirement_at_current(slot=i), slot=k)`
//!    when the dep is bundled inside caller slot i's requirement value.
//! 3. **Static** — `construct_requirement(impl, [<sub-projections>])`
//!    when the dep is fully ground and `SortProvidesInfo` resolves it.
//!
//! WI-222's transitive-flat `requires_chain` only naturally exercises
//! the flat path; the nested and static paths fire through synthetic
//! scenarios that hand `build_dep_projection` non-flat inputs or set
//! up a top-level call whose callee has a fully-ground `requires`.
//!
//! Reference: docs/design/operation-call-model.md §"Call rewrite cases",
//! §"Two primitives".

mod common;

use anthill_core::kb::term::{Term, Literal};
use anthill_core::kb::typing::{
    build_dep_projection, get_named_arg, ProjectionSyms, RequiresEntry,
};
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;
use smallvec::SmallVec;

use common::{collect_stdlib_and_rust_bindings, interp_for};

/// Load stdlib + Rust host bindings only — no user source. Used by the
/// nested-handle synthetic which constructs its `RequiresEntry`s by
/// hand against stdlib symbols (Eq, Ordered).
fn load_stdlib_only() -> KnowledgeBase {
    let files = collect_stdlib_and_rust_bindings();
    let parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p).expect("read stdlib file");
            parse::parse(&src).expect("parse stdlib file")
        })
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).expect("load stdlib");
    kb
}

#[test]
fn flat_path_emits_requirement_at_current() {
    // Regression for WI-222 Phase D: a sort declaring `requires Eq[T]`
    // and calling `eq(...)` must project its own Eq slot via
    // `requirement_at_current(slot=0)` — the dep is at top level of the
    // caller's flat chain.
    //
    // After WI-227's refactor, Strategy 1 (flat slot match) must still
    // fire first and emit a plain `requirement_at_current` — not the
    // nested or static forms.
    let src = r#"
namespace test.wi227.flat
  import anthill.prelude.Eq.{eq}
  import anthill.prelude.{Eq, Bool}
  export Wi227Flat
  sort Wi227Flat
    sort T = ?
    requires Eq[T]
    operation use_eq(a: T, b: T) -> Bool = eq(a, b)
  end
end
"#;
    let interp = interp_for(src);
    let kb = interp.kb();

    let eq_sym = kb.try_resolve_symbol("anthill.prelude.Eq.eq").expect("Eq.eq");
    let raac_sym = kb
        .try_resolve_symbol("anthill.reflect.Expr.requirement_at_current")
        .expect("requirement_at_current");
    let ras_sym = kb
        .try_resolve_symbol("anthill.reflect.Expr.requirement_at_sort")
        .expect("requirement_at_sort");
    let cr_sym = kb
        .try_resolve_symbol("anthill.reflect.Expr.construct_requirement")
        .expect("construct_requirement");
    let nil_sym = kb.try_resolve_symbol("anthill.prelude.List.nil").expect("List.nil");

    // Locate the eq() defer rewrite — its apply_within.requirements
    // list must be nil (Eq has no transitive deps). Strategy 1 stops
    // at the flat-match step before ever consulting Strategy 2 or 3.
    let mut rewritten_for_eq = None;
    for (rewritten_tid, spec_sym) in kb.dispatch_origin_iter() {
        if spec_sym == eq_sym {
            rewritten_for_eq = Some(rewritten_tid);
        }
    }
    let rewritten_tid = rewritten_for_eq.expect("eq() must be rewritten");

    // fn = requirement_at_current(slot=0, op=some(eq)) — the deferred
    // dispatch form. Pins WI-222 Phase C output too.
    let named_args = match kb.get_term(rewritten_tid) {
        Term::Fn { named_args, .. } => named_args.clone(),
        other => panic!("rewritten must be Fn; got {other:?}"),
    };
    let fn_tid = get_named_arg(kb, &named_args, "fn").expect("fn arg");
    let (fn_functor, _) = match kb.get_term(fn_tid) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        other => panic!("fn must be Fn; got {other:?}"),
    };
    assert_eq!(
        fn_functor, raac_sym,
        "fn-position must be requirement_at_current (Strategy 1 form), not {} \
         or {}",
        kb.qualified_name_of(ras_sym),
        kb.qualified_name_of(cr_sym)
    );

    // requirements list = nil (Eq.eq has no transitive deps).
    let reqs_tid = get_named_arg(kb, &named_args, "requirements").expect("requirements arg");
    let reqs_functor = match kb.get_term(reqs_tid) {
        Term::Fn { functor, .. } => *functor,
        other => panic!("requirements must be Fn; got {other:?}"),
    };
    assert_eq!(reqs_functor, nil_sym, "empty deps → nil list");
}

#[test]
fn nested_handle_emits_requirement_at_sort_chain() {
    // Synthetic Strategy 2 scenario: the dep we're projecting is NOT in
    // caller_requires at top level, but IS in the transitive
    // `requires_chain` of one of those entries. WI-222's loader always
    // produces flat chains (transitive closure), so we hand
    // `build_dep_projection` a deliberately non-flat caller_requires
    // = [RequiresEntry { required_sort: Ordered, ... }] and ask for
    // a projection for `Eq` — Ordered's chain in stdlib carries Eq, so
    // Strategy 2 must fire and emit
    // `requirement_at_sort(requirement_at_current(slot=0), slot=0)`.
    let mut kb = load_stdlib_only();
    let syms = ProjectionSyms::resolve(&mut kb).expect("stdlib must define IR symbols");

    let eq_sym = kb.try_resolve_symbol("anthill.prelude.Eq").expect("Eq sort");
    let ordered_sym = kb
        .try_resolve_symbol("anthill.prelude.Ordered")
        .expect("Ordered sort");

    // Hand-built caller_requires holding Ordered at slot 0 (and NOT Eq
    // at top level). Each entry's `spec` is a plain sort term — the
    // search keys on `required_sort` for Strategies 1 and 2.
    let ordered_ref = kb.alloc(Term::Ref(ordered_sym));
    let caller_requires = vec![RequiresEntry {
        required_sort: ordered_sym,
        spec: ordered_ref,
    }];

    // The dep we're searching for: Eq. Strategy 1 fails (Eq not in
    // caller_requires). Strategy 2 walks Ordered's requires_chain in
    // stdlib — which carries Eq[T] — and matches at slot 0.
    let eq_ref = kb.alloc(Term::Ref(eq_sym));
    let dep = RequiresEntry {
        required_sort: eq_sym,
        spec: eq_ref,
    };

    let caller_sub_chains: Vec<Vec<RequiresEntry>> = caller_requires
        .iter()
        .map(|ar| anthill_core::kb::typing::requires_chain(&kb, ar.required_sort))
        .collect();
    let projection = build_dep_projection(
        &mut kb, &dep, &caller_requires, &caller_sub_chains, &syms,
    )
        .expect("Strategy 2 must emit a projection for Eq nested inside Ordered");

    // Top-level must be requirement_at_sort.
    let (functor, named_args) = match kb.get_term(projection) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        other => panic!("projection must be Fn; got {other:?}"),
    };
    assert_eq!(
        functor, syms.ras,
        "Strategy 2 emits requirement_at_sort; got {}",
        kb.qualified_name_of(functor)
    );

    // chain = requirement_at_current(slot=0). No op-wrap (value position).
    let chain_tid = get_named_arg(&kb, &named_args, "chain").expect("chain arg");
    let (chain_functor, chain_named) = match kb.get_term(chain_tid) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        other => panic!("chain must be Fn; got {other:?}"),
    };
    assert_eq!(
        chain_functor, syms.raac,
        "chain must be requirement_at_current; got {}",
        kb.qualified_name_of(chain_functor)
    );
    let chain_slot_tid = get_named_arg(&kb, &chain_named, "slot").expect("inner slot");
    match kb.get_term(chain_slot_tid) {
        Term::Const(Literal::Int(0)) => {}
        other => panic!("inner slot must be 0 (Ordered is at caller_requires[0]); got {other:?}"),
    }
    assert!(
        get_named_arg(&kb, &chain_named, "op").is_none(),
        "value-position requirement_at_current must omit `op`"
    );

    // slot=0 — Eq is the first (and only) entry in Ordered's requires
    // chain in stdlib.
    let outer_slot_tid = get_named_arg(&kb, &named_args, "slot").expect("outer slot");
    match kb.get_term(outer_slot_tid) {
        Term::Const(Literal::Int(0)) => {}
        other => panic!("outer slot must be 0 (Eq is first in Ordered's chain); got {other:?}"),
    }
}

#[test]
fn ground_dep_emits_construct_requirement() {
    // Synthetic Strategy 3 scenario: an empty caller chain (no enclosing
    // requires) plus a fully-ground dep `Eq[T = Int]`. Strategies 1 and 2
    // both fail (nothing to scan); Strategy 3 runs SLD resolution
    // against `SortProvidesInfo` — the rustland binding registers
    // `fact Eq[T = Int]` via a leaf impl carrier — and emits
    // `construct_requirement(<IntEq>, nil)`.
    //
    // Done as a direct `build_dep_projection` call against a hand-built
    // `RequiresEntry`. The natural Pin-now path that ends up here in
    // user code currently passes the spec sort (not the impl's parent)
    // to `build_projected_requirements_list`, so the requirements list
    // there projects against the spec's empty chain — a pre-existing
    // call-site asymmetry orthogonal to WI-227's projection-search
    // scope. The synthetic call here exercises the search itself.
    let mut kb = load_stdlib_only();
    let syms = ProjectionSyms::resolve(&mut kb).expect("stdlib must define IR symbols");

    let eq_sym = kb.try_resolve_symbol("anthill.prelude.Eq").expect("Eq sort");
    let int_sym = kb.try_resolve_symbol("anthill.prelude.Int").expect("Int sort");
    let sort_view_sym = kb
        .try_resolve_symbol("anthill.reflect.SortView")
        .expect("SortView sort");
    let t_field = kb.intern("T");
    let eq_ref = kb.alloc(Term::Ref(eq_sym));
    let int_ref = kb.alloc(Term::Ref(int_sym));

    // dep = SortView(Eq, T = Int) — Strategy 3 reads bindings from the
    // spec field to seed the SLD goal.
    let mut pos: SmallVec<[anthill_core::kb::term::TermId; 4]> = SmallVec::new();
    pos.push(eq_ref);
    let mut named: SmallVec<[(_, _); 2]> = SmallVec::new();
    named.push((t_field, int_ref));
    let dep_spec = kb.alloc(Term::Fn {
        functor: sort_view_sym,
        pos_args: pos,
        named_args: named,
    });
    let dep = RequiresEntry {
        required_sort: eq_sym,
        spec: dep_spec,
    };

    let caller_requires: Vec<RequiresEntry> = Vec::new();

    let caller_sub_chains: Vec<Vec<RequiresEntry>> = caller_requires
        .iter()
        .map(|ar| anthill_core::kb::typing::requires_chain(&kb, ar.required_sort))
        .collect();
    let projection = build_dep_projection(
        &mut kb, &dep, &caller_requires, &caller_sub_chains, &syms,
    )
        .expect("Strategy 3 must resolve Eq[T=Int] via SortProvidesInfo");

    // Top-level must be construct_requirement(impl_functor=Ref(<Eq impl>),
    // requirements=nil).
    let (functor, named_args) = match kb.get_term(projection) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        other => panic!("projection must be Fn; got {other:?}"),
    };
    assert_eq!(
        functor, syms.construct,
        "Strategy 3 emits construct_requirement; got {}",
        kb.qualified_name_of(functor)
    );

    let impl_tid = get_named_arg(&kb, &named_args, "impl_functor").expect("impl_functor arg");
    let impl_sym = match kb.get_term(impl_tid) {
        Term::Ref(s) | Term::Ident(s) => *s,
        Term::Fn { functor, pos_args, named_args }
            if pos_args.is_empty() && named_args.is_empty() =>
        {
            *functor
        }
        other => panic!("impl_functor must be a sort reference; got {other:?}"),
    };
    // The rustland binding (anthill-stl/anthill/int.anthill) declares
    // `provides Int … fact Eq[T = Int]` — Int IS the Eq carrier for
    // T = Int. SortProvidesInfo's `sort_ref` is therefore the Int
    // symbol, so the construct_requirement's `impl_functor` Ref's Int.
    assert_eq!(
        impl_sym, int_sym,
        "Eq[T = Int]'s SortProvidesInfo carrier is Int itself; \
         construct_requirement.impl_functor must point to it. Got {}",
        kb.qualified_name_of(impl_sym)
    );

    // requirements list = nil — Eq has no transitive deps in stdlib.
    let sub_reqs_tid =
        get_named_arg(&kb, &named_args, "requirements").expect("requirements arg");
    let sub_functor = match kb.get_term(sub_reqs_tid) {
        Term::Fn { functor, .. } => *functor,
        other => panic!("requirements must be Fn (list); got {other:?}"),
    };
    assert_eq!(
        sub_functor, syms.nil,
        "Eq has no transitive deps; nested requirements list must be nil"
    );
}

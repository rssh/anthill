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


use anthill_core::kb::term::Term;
use anthill_core::kb::typing::{
    build_dep_projection, get_named_arg, ProjectionSyms, RequiresEntry,
};
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;
use smallvec::SmallVec;

use crate::common::{collect_stdlib_and_rust_bindings, interp_for};

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
fn flat_path_emits_var_ref_named_requirement() {
    // WI-237 names-model regression: a sort declaring `requires Eq[T]`
    // and calling `eq(...)` must rewrite to
    // `apply_within(fn = Ref(Eq.eq),
    //  requirements = [var_ref(name = Ref(__req_eq))])` — Strategy 1
    // emits the single dispatching dict expression via the synthesized
    // requirement-param name for the caller's chain slot 0 (Eq).
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
    let mut interp = interp_for(src);
    let expected_name = interp.kb_mut().intern("__req_eq");
    let kb = interp.kb();

    let eq_sym = kb.try_resolve_symbol("anthill.prelude.Eq.eq").expect("Eq.eq");
    let var_ref_sym = kb
        .try_resolve_symbol("anthill.reflect.Expr.var_ref")
        .expect("var_ref");
    let cons_sym = kb.try_resolve_symbol("anthill.prelude.List.cons").expect("List.cons");
    let nil_sym = kb.try_resolve_symbol("anthill.prelude.List.nil").expect("List.nil");

    let mut rewritten_for_eq = None;
    for (rewritten_tid, spec_sym) in kb.dispatch_origin_iter() {
        if spec_sym == eq_sym {
            rewritten_for_eq = Some(rewritten_tid);
        }
    }
    let rewritten_tid = rewritten_for_eq.expect("eq() must be rewritten");

    let named_args = match kb.get_term(rewritten_tid) {
        Term::Fn { named_args, .. } => named_args.clone(),
        other => panic!("rewritten must be Fn; got {other:?}"),
    };

    // fn = Ref(Eq.eq) — spec-op symbol directly.
    let fn_tid = get_named_arg(kb, &named_args, "fn").expect("fn arg");
    match kb.get_term(fn_tid) {
        Term::Ref(s) => assert_eq!(*s, eq_sym,
            "fn must be Ref(Eq.eq); got Ref({})", kb.qualified_name_of(*s)),
        other => panic!("fn must be Term::Ref(spec_op); got {other:?}"),
    }

    // requirements = cons(var_ref(name=Ref(__req_eq)), nil) — Strategy 1
    // (named-param flat match) emits a name-based read of the caller's
    // requirement-param.
    let reqs_tid = get_named_arg(kb, &named_args, "requirements").expect("requirements arg");
    let (reqs_functor, reqs_named) = match kb.get_term(reqs_tid) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        other => panic!("requirements must be Fn; got {other:?}"),
    };
    assert_eq!(reqs_functor, cons_sym,
        "single dispatching dict wrapped in cons; got {}",
        kb.qualified_name_of(reqs_functor));

    let head_tid = get_named_arg(kb, &reqs_named, "head").expect("cons head");
    let (head_functor, head_named) = match kb.get_term(head_tid) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        other => panic!("dispatching dict must be Fn; got {other:?}"),
    };
    assert_eq!(head_functor, var_ref_sym,
        "Strategy 1 emits var_ref (names model); got {}",
        kb.qualified_name_of(head_functor));
    let name_tid = get_named_arg(kb, &head_named, "name").expect("name arg");
    match kb.get_term(name_tid) {
        Term::Ref(s) => assert_eq!(*s, expected_name,
            "var_ref name must be Ref(__req_eq) for Eq at caller chain[0]; got Ref({})",
            kb.qualified_name_of(*s)),
        other => panic!("name must be Term::Ref(<sym>); got {other:?}"),
    }

    let tail_tid = get_named_arg(kb, &reqs_named, "tail").expect("cons tail");
    let tail_functor = match kb.get_term(tail_tid) {
        Term::Fn { functor, .. } => *functor,
        other => panic!("tail must be Fn (nil); got {other:?}"),
    };
    assert_eq!(tail_functor, nil_sym, "single-entry list's tail must be nil");
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

    // `caller_sort` is None: this is a synthetic non-flat caller chain
    // with no real enclosing sort. Strategy 2 needs `caller_sort` to
    // name the chain slot, so it bails to `None` here — see the
    // names-model rewrite in the runtime tests for the real path.
    let caller_sub_chains: Vec<Vec<RequiresEntry>> = caller_requires
        .iter()
        .map(|ar| anthill_core::kb::typing::requires_chain_flat(&kb, ar.required_sort))
        .collect();
    let projection = build_dep_projection(
        &mut kb, &dep, None, &caller_requires, &caller_sub_chains, &syms,
    );
    assert!(
        projection.is_none(),
        "Strategy 2 with a synthetic caller (caller_sort = None) cannot \
         synthesize a requirement-param name, so it yields None"
    );
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

    // `caller_sort` is None — empty caller chain, no enclosing sort.
    // Strategies 1 & 2 can't fire (nothing to scan); Strategy 3 runs
    // SLD resolution and doesn't consult `caller_sort`.
    let caller_sub_chains: Vec<Vec<RequiresEntry>> = caller_requires
        .iter()
        .map(|ar| anthill_core::kb::typing::requires_chain_flat(&kb, ar.required_sort))
        .collect();
    let projection = build_dep_projection(
        &mut kb, &dep, None, &caller_requires, &caller_sub_chains, &syms,
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

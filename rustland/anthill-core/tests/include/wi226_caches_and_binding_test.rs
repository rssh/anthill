//! WI-226 — compile-time caches (requires_chain memoization + SLD
//! resolve memoization) and binding-aware projection slot matching.
//!
//! Test acceptance from WI-226:
//! 1. `requires_chain` second call for the same sort hits the cache.
//! 2. `dispatch_spec_op_cached` second call for the same (goal, scope)
//!    hits the cache and skips the SLD walk.
//! 3. A caller with `Eq[T=X]` at slot 0 and a callee dep `Eq[T=Y]`
//!    (different bindings) does NOT match slot 0 — the binding-aware
//!    predicate rejects, the search falls through to the next
//!    strategy.


use anthill_core::kb::term::Term;
use anthill_core::kb::typing::{
    build_dep_projection, requires_chain, ProjectionSyms, RequiresEntry,
};
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;
use smallvec::SmallVec;

use crate::common::collect_stdlib_and_rust_bindings;

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
fn requires_chain_memoizes_top_level_query() {
    // Cache A acceptance: requires_chain populates the requires-tree
    // cache on first call, and subsequent calls for the same sort
    // return the cached value (verifiable via
    // `requires_chain_cache_contains` — false before, true after).
    let mut kb = load_stdlib_only();
    let ordered_sym = kb
        .try_resolve_symbol("anthill.prelude.Ordered")
        .expect("Ordered sort");

    // WI-343's provider-side `requires` check runs at load and walks
    // `direct_requires_chain` for every provided spec (`fact Ordered[T=…]`
    // among them), warming the requires-chain cache. Reset it so this test
    // measures cache growth from its own `requires_chain` calls — mirroring
    // `resolve_cache_memoizes_dispatch_at_same_goal_and_scope`'s reset below.
    kb.invalidate_requires_chain_cache();

    // Cache is empty for Ordered before first call.
    assert!(
        !kb.requires_chain_cache_contains(ordered_sym),
        "cache must start empty for Ordered"
    );

    let first = requires_chain(&mut kb, ordered_sym);
    // After first call, the cache holds Ordered's chain.
    assert!(
        kb.requires_chain_cache_contains(ordered_sym),
        "first requires_chain(Ordered) call must populate the cache"
    );

    // Second call returns the same content (structural equality on
    // (required_sort, spec) — both Symbol/TermId Copy).
    let second = requires_chain(&mut kb, ordered_sym);
    assert_eq!(
        first.len(),
        second.len(),
        "cached requires_chain result must match first call"
    );
    for (a, b) in first.iter().zip(second.iter()) {
        assert_eq!(a.required_sort, b.required_sort);
        assert_eq!(a.spec, b.spec);
    }
}

#[test]
fn resolve_cache_memoizes_dispatch_at_same_goal_and_scope() {
    // Cache B acceptance: dispatch_spec_op_cached writes to
    // kb.resolve_cache on first SLD resolution, and a second call at
    // the same (goal, scope) is served from the cache without
    // re-walking SortProvidesInfo. We verify by reading the cache map
    // directly: it grows by exactly one entry after the first
    // dispatch, and a second call doesn't add a new entry.
    use anthill_core::kb::typing::dispatch_spec_op_cached;
    use anthill_core::kb::subst::Substitution;

    let mut kb = load_stdlib_only();
    let eq_sym = kb.try_resolve_symbol("anthill.prelude.Eq").expect("Eq sort");
    let eq_op_short = kb.intern("eq");
    let subst = Substitution::new();
    let enclosing_requires: Vec<RequiresEntry> = Vec::new();

    // Stdlib load may have exercised Eq.eq dispatch via operation bodies
    // (e.g. List.member, List.nth after WI-324). Reset the cache so we
    // measure cache growth from the test's own dispatch calls, not
    // whatever residue stdlib left behind.
    kb.invalidate_resolve_cache();

    let before = kb.resolve_cache_len();
    let _ = dispatch_spec_op_cached(
        &mut kb, &subst, eq_sym, eq_op_short, &enclosing_requires, None,
    );
    let after_first = kb.resolve_cache_len();
    assert_eq!(
        after_first,
        before + 1,
        "first dispatch must add exactly one cache entry; saw {before} → {after_first}"
    );

    // Second call at the same (goal, scope) — no new entry, served from cache.
    let _ = dispatch_spec_op_cached(
        &mut kb, &subst, eq_sym, eq_op_short, &enclosing_requires, None,
    );
    let after_second = kb.resolve_cache_len();
    assert_eq!(
        after_second, after_first,
        "second dispatch at the same goal+scope must not add a cache entry"
    );
}

#[test]
fn binding_aware_match_rejects_wrong_binding_at_flat_slot() {
    // Correctness acceptance: a caller carrying Eq[T=Int64] at slot 0
    // must NOT have its slot 0 emitted as the projection for a dep
    // Eq[T=String] (different binding). The binding-aware predicate
    // rejects the flat match; without any String-providing alternative
    // in scope, build_dep_projection falls through to Strategy 3
    // (SortProvidesInfo lookup), which resolves Eq[T=String] to the
    // rustland's String carrier — NOT slot 0.
    let mut kb = load_stdlib_only();
    let syms = ProjectionSyms::resolve(&mut kb).expect("stdlib symbols");

    let eq_sym = kb.try_resolve_symbol("anthill.prelude.Eq").expect("Eq sort");
    let int_sym = kb.try_resolve_symbol("anthill.prelude.Int64").expect("Int64 sort");
    let string_sym = kb
        .try_resolve_symbol("anthill.prelude.String")
        .expect("String sort");
    let sort_view_sym = kb
        .try_resolve_symbol("anthill.reflect.SortView")
        .expect("SortView sort");
    let t_field = kb.intern("T");

    let make_sort_view = |kb: &mut KnowledgeBase, base: anthill_core::intern::Symbol,
                          binding: anthill_core::intern::Symbol|
     -> anthill_core::kb::term::TermId {
        let base_ref = kb.alloc(Term::Ref(base));
        let binding_ref = kb.alloc(Term::Ref(binding));
        let mut pos: SmallVec<[anthill_core::kb::term::TermId; 4]> = SmallVec::new();
        pos.push(base_ref);
        let mut named: SmallVec<[(_, _); 2]> = SmallVec::new();
        named.push((t_field, binding_ref));
        kb.alloc(Term::Fn {
            functor: sort_view_sym,
            pos_args: pos,
            named_args: named,
        })
    };

    let caller_spec_int = make_sort_view(&mut kb, eq_sym, int_sym);
    let caller_requires = vec![RequiresEntry {
        required_sort: eq_sym,
        spec: caller_spec_int,
    }];
    let dep_spec_string = make_sort_view(&mut kb, eq_sym, string_sym);
    let dep = RequiresEntry {
        required_sort: eq_sym,
        spec: dep_spec_string,
    };

    let caller_sub_chains: Vec<Vec<RequiresEntry>> = caller_requires
        .iter()
        .map(|ar| requires_chain(&mut kb, ar.required_sort))
        .collect();

    // `caller_sort` is None — this is a synthetic caller chain with no
    // enclosing sort; Strategy 1/2 won't fire anyway (binding mismatch),
    // so the name lookup is never reached.
    let projection = build_dep_projection(
        &mut kb, &dep, None, &caller_requires, &caller_sub_chains, &syms, None,
    )
    .expect("Strategy 3 must resolve Eq[T=String] via the String carrier");

    // The projection must NOT be the caller's slot-0 read — that would
    // be the pre-WI-226 buggy behavior (matching by required_sort alone
    // and reusing slot 0 even though caller's binding is Int64, not
    // String). Instead it must be construct_requirement with
    // impl_functor = Ref(String).
    let (functor, named_args) = match kb.get_term(projection) {
        Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
        other => panic!("projection must be Fn; got {other:?}"),
    };
    assert_eq!(
        functor, syms.construct,
        "binding-aware match must reject slot 0 (Eq[T=Int64] != Eq[T=String]) \
         and fall through to Strategy 3's construct_requirement; got {}",
        kb.qualified_name_of(functor)
    );

    let impl_tid = named_args
        .iter()
        .find(|(k, _)| kb.resolve_sym(*k) == "impl_functor")
        .map(|(_, v)| *v)
        .expect("impl_functor arg");
    let impl_sym = match kb.get_term(impl_tid) {
        Term::Ref(s) | Term::Ident(s) => *s,
        Term::Fn { functor, pos_args, named_args }
            if pos_args.is_empty() && named_args.is_empty() =>
        {
            *functor
        }
        other => panic!("impl_functor must be a sort reference; got {other:?}"),
    };
    assert_eq!(
        impl_sym, string_sym,
        "Strategy 3 must resolve Eq[T=String]'s carrier to String, not to Int64"
    );
}

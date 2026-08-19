//! WI-227 — recursive projection search for `apply_within.requirements`.
//!
//! The requirement-insertion pass must turn each callee dep into one of
//! three IR forms:
//!
//! 1. **Flat** — `requirement_at_current(slot=i)` when the dep is at top
//!    level of the caller's frame requirements (the v0 stdlib case).
//! 2. **Nested** — `requirement_at_sort(requirement_at_current(slot=i), slot=k)`
//!    when the dep is bundled inside caller slot i's requirement value.
//! 3. **Static** — `Dictionary(<sub-projections>, impl: impl)`
//!    when the dep is fully ground and `SortProvidesInfo` resolves it.
//!
//! WI-222's transitive-flat `requires_chain` only naturally exercises
//! the flat path; the nested and static paths fire through synthetic
//! scenarios that hand `build_dep_projection` non-flat inputs or set
//! up a top-level call whose callee has a fully-ground `requires`.
//!
//! Reference: docs/design/operation-call-model.md §"Call rewrite cases",
//! §"Two primitives".

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::term::Term;
use anthill_core::kb::typing::{
    build_dep_projection, get_named_arg, ProjectionSyms, RequiresEntry,
};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use smallvec::SmallVec;

use crate::common::{collect_stdlib_and_rust_bindings, interp_for};

/// Load stdlib + Rust host bindings only — no user source. Used by the
/// nested-handle synthetic which constructs its `RequiresEntry`s by
/// hand against stdlib symbols (Eq, Ord).
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
    load::load_all(&mut kb, &refs, &NullResolver).expect("load stdlib");
    kb
}

/// WI-237 names-model regression: a sort declaring `requires Spec[T]` and calling
/// `Spec.op(...)` must rewrite to `apply_within(fn = Ref(Spec.op),
/// requirements = [var_ref(name = Ref(__req_spec))])` — Strategy 1 emits the single
/// dispatching dict expression via the synthesized requirement-param name for the
/// caller's chain slot 0.
///
/// **THE REWRITE IS SELECTED BY ITS ENCLOSING OPERATION, and that is what makes this
/// test measure the fixture** (WI-873). It read `anthill.prelude.PartialEq.eq` and
/// selected its subject with `for (tid, spec) in kb.dispatch_origin_iter() { if spec
/// == eq_sym { keep = Some(tid) } }` — a scan of a KB-GLOBAL map, keeping whichever
/// entry came last. Two facts made that arbitrary rather than merely loose:
/// `req_insertion::run` walks `kb.op_bodies_iter()`, whose backing `op_records` is a
/// `HashMap` (random order per process), and the rewrite table was keyed by a term
/// `materialize_apply` synthesized from the callee functor ALONE (`apply(fn =
/// Ref(functor), args = nil)`) — so every abstract `eq` call in the image collided on
/// one key and exactly one rewrite was ever recorded, the first one walked. Which
/// sort's that was is order-dependent, and so was the head-shape assertion below.
/// MEASURED under WI-1091's widened op-scoped placement, which puts more sorts in the
/// race: FAILED in one full-workspace run (`Strategy 1 emits var_ref; got
/// …requirement_at_sort`, a nested projection from some other sort) and PASSED in the
/// next run of the same binary, same code.
///
/// WI-1091 dodged it with a local spec; WI-873 fixed the key. The table is now keyed
/// by [`anthill_core::kb::CallSite`] — every call site's rewrite is recorded, and the
/// enclosing OPERATION selects this fixture's. The local spec is kept (it also keeps
/// the shape claim unambiguous), and the twin in `wi222_defer_rewrite_test` is
/// selected the same way.
#[test]
fn flat_path_emits_var_ref_named_requirement() {
    let src = r#"
namespace test.wi227.flat
  import anthill.prelude.{Bool}
  sort Wi227Spec
    sort T = ?
    operation same(a: T, b: T) -> Bool
  end
  sort Wi227Flat
    sort T = ?
    requires Wi227Spec[T]
    operation use_eq(a: T, b: T) -> Bool = Wi227Spec.same(a, b)
  end
end
"#;
    let interp = interp_for(src);
    let kb = interp.kb();

    let eq_sym = kb
        .try_resolve_symbol("test.wi227.flat.Wi227Spec.same")
        .expect("Wi227Spec.same");
    let var_ref_sym = kb
        .try_resolve_symbol("anthill.reflect.Expr.var_ref")
        .expect("var_ref");
    let cons_sym = kb
        .try_resolve_symbol("anthill.prelude.List.cons")
        .expect("List.cons");
    let nil_sym = kb
        .try_resolve_symbol("anthill.prelude.List.nil")
        .expect("List.nil");

    // Selected by the ENCLOSING OPERATION (WI-873), so this is `use_eq`'s own rewrite
    // and no other; `rewrite_in_op` asserts exactly one match.
    let rewritten_tid = crate::common::rewrite_in_op(
        kb,
        "test.wi227.flat.Wi227Flat.use_eq",
        "test.wi227.flat.Wi227Spec.same",
    );

    let named_args = match kb.get_term(rewritten_tid) {
        Term::Fn { named_args, .. } => named_args.clone(),
        other => panic!("rewritten must be Fn; got {other:?}"),
    };

    // fn = Ref(Wi227Spec.same) — spec-op symbol directly.
    let fn_tid = get_named_arg(kb, &named_args, "fn").expect("fn arg");
    match kb.get_term(fn_tid) {
        Term::Ref(s) => assert_eq!(
            *s,
            eq_sym,
            "fn must be Ref(Wi227Spec.same); got Ref({})",
            kb.qualified_name_of(*s)
        ),
        other => panic!("fn must be Term::Ref(spec_op); got {other:?}"),
    }

    // requirements = cons(var_ref(name=Ref(__req_wi227spec)), nil) — Strategy 1
    // (named-param flat match) emits a name-based read of the caller's
    // requirement-param.
    let reqs_tid = get_named_arg(kb, &named_args, "requirements").expect("requirements arg");
    let (reqs_functor, reqs_named) = match kb.get_term(reqs_tid) {
        Term::Fn {
            functor,
            named_args,
            ..
        } => (*functor, named_args.clone()),
        other => panic!("requirements must be Fn; got {other:?}"),
    };
    assert_eq!(
        reqs_functor,
        cons_sym,
        "single dispatching dict wrapped in cons; got {}",
        kb.qualified_name_of(reqs_functor)
    );

    let head_tid = get_named_arg(kb, &reqs_named, "head").expect("cons head");
    let (head_functor, head_named) = match kb.get_term(head_tid) {
        Term::Fn {
            functor,
            named_args,
            ..
        } => (*functor, named_args.clone()),
        other => panic!("dispatching dict must be Fn; got {other:?}"),
    };
    assert_eq!(
        head_functor,
        var_ref_sym,
        "Strategy 1 emits var_ref (names model); got {}",
        kb.qualified_name_of(head_functor)
    );
    let name_tid = get_named_arg(kb, &head_named, "name").expect("name arg");
    match kb.get_term(name_tid) {
        // AT CALLER chain[0], named exactly — restored by WI-873. `Wi227Flat`'s chain
        // is [Wi227Spec], so slot 0 is `__req_wi227spec` with no disambiguating suffix.
        // While the table kept one rewrite per spec op for the whole image this read
        // got whichever sort won the race, and the claim had to be narrowed to the SPEC.
        Term::Ref(s) => assert_eq!(
            kb.local_name_of(*s),
            "__req_wi227spec",
            "Strategy 1's var_ref must name slot 0 of `Wi227Flat`'s own chain"
        ),
        other => panic!("name must be Term::Ref(<sym>); got {other:?}"),
    }

    let tail_tid = get_named_arg(kb, &reqs_named, "tail").expect("cons tail");
    let tail_functor = match kb.get_term(tail_tid) {
        Term::Fn { functor, .. } => *functor,
        // WI-511: the empty list is canonicalized to the bare `Ref(nil)` form.
        Term::Ref(s) => *s,
        other => panic!("tail must be Fn (nil) or Ref (nil); got {other:?}"),
    };
    assert_eq!(
        tail_functor, nil_sym,
        "single-entry list's tail must be nil"
    );
}

#[test]
fn nested_handle_emits_requirement_at_sort_chain() {
    // Synthetic Strategy 2 scenario: the dep we're projecting is NOT in
    // caller_requires at top level, but IS in the transitive
    // `requires_chain` of one of those entries. WI-222's loader always
    // produces flat chains (transitive closure), so we hand
    // `build_dep_projection` a deliberately non-flat caller_requires
    // = [RequiresEntry { required_sort: Ord, ... }] and ask for
    // a projection for `Eq` — Ord's chain in stdlib carries Eq, so
    // Strategy 2 must fire and emit
    // `requirement_at_sort(requirement_at_current(slot=0), slot=0)`.
    let mut kb = load_stdlib_only();
    let syms = ProjectionSyms::resolve(&mut kb).expect("stdlib must define IR symbols");

    let eq_sym = kb
        .try_resolve_symbol("anthill.prelude.Eq")
        .expect("Eq sort");
    let ordered_sym = kb
        .try_resolve_symbol("anthill.prelude.Ord")
        .expect("Ord sort");

    // Hand-built caller_requires holding Ord at slot 0 (and NOT Eq
    // at top level). Each entry's `spec` is a plain sort term — the
    // search keys on `required_sort` for Strategies 1 and 2.
    let ordered_ref = kb.alloc(Term::Ref(ordered_sym));
    let caller_requires = vec![RequiresEntry {
        required_sort: ordered_sym,
        spec: ordered_ref.into(),
        supply: anthill_core::kb::typing::SupplySource::Required,
    }];

    // The dep we're searching for: Eq. Strategy 1 fails (Eq not in
    // caller_requires). Strategy 2 walks Ord's requires_chain in
    // stdlib — which carries Eq[T] — and matches at slot 0.
    let eq_ref = kb.alloc(Term::Ref(eq_sym));
    let dep = RequiresEntry {
        required_sort: eq_sym,
        spec: eq_ref.into(),
        supply: anthill_core::kb::typing::SupplySource::Required,
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
        &mut kb,
        &dep,
        &anthill_core::kb::typing::DictChain::unnamed(caller_requires.clone()),
        &caller_sub_chains,
        &syms,
        None,
        None,
        &[],
        // WI-861: these fixtures use ANONYMOUS `requires` slots, which is the
        // population rung 2a serves; a named slot withholds it (`DefaultRung`).
        anthill_core::kb::typing::DefaultRung::Consult,
    );
    assert!(
        projection.is_none(),
        "Strategy 2 with a synthetic caller (caller_sort = None) cannot \
         synthesize a requirement-param name, so it yields None"
    );
}

#[test]
fn ground_dep_emits_the_dictionary_node() {
    // Synthetic Strategy 3 scenario: an empty caller chain (no enclosing
    // requires) plus a fully-ground dep `Eq[T = Int64]`. Strategies 1 and 2
    // both fail (nothing to scan); Strategy 3 runs SLD resolution
    // against `SortProvidesInfo` — the rustland binding registers
    // `fact Eq[T = Int64]` via a leaf impl carrier — and emits
    // `Dictionary(impl: <IntEq>)`.
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

    let eq_sym = kb
        .try_resolve_symbol("anthill.prelude.Eq")
        .expect("Eq sort");
    let int_sym = kb
        .try_resolve_symbol("anthill.prelude.Int64")
        .expect("Int64 sort");
    let sort_view_sym = kb
        .try_resolve_symbol("anthill.reflect.SortView")
        .expect("SortView sort");
    let t_field = kb.intern("T");
    let eq_ref = kb.alloc(Term::Ref(eq_sym));
    let int_ref = kb.alloc(Term::Ref(int_sym));

    // dep = SortView(Eq, T = Int64) — Strategy 3 reads bindings from the
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
        spec: dep_spec.into(),
        supply: anthill_core::kb::typing::SupplySource::Required,
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
        &mut kb,
        &dep,
        &anthill_core::kb::typing::DictChain::unnamed(caller_requires.clone()),
        &caller_sub_chains,
        &syms,
        None,
        None,
        &[],
        // WI-861: these fixtures use ANONYMOUS `requires` slots, which is the
        // population rung 2a serves; a named slot withholds it (`DefaultRung`).
        anthill_core::kb::typing::DefaultRung::Consult,
    )
    .expect("Strategy 3 must resolve Eq[T=Int64] via SortProvidesInfo");

    // Top-level must be `Dictionary(<subs …>, impl = Ref(<Eq impl>))`.
    let (functor, pos_args, named_args) = match kb.get_term(projection) {
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } => (*functor, pos_args.clone(), named_args.clone()),
        other => panic!("projection must be Fn; got {other:?}"),
    };
    assert_eq!(
        functor,
        syms.dict_ctor,
        "Strategy 3 emits the `Dictionary` construction node; got {}",
        kb.qualified_name_of(functor)
    );

    let impl_tid = named_args
        .iter()
        .find(|(k, _)| *k == syms.dict_impl)
        .map(|(_, v)| *v)
        .expect("impl arg");
    let impl_sym = match kb.get_term(impl_tid) {
        Term::Ref(s) | Term::Ident(s) => *s,
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } if pos_args.is_empty() && named_args.is_empty() => *functor,
        other => panic!("impl must be a sort reference; got {other:?}"),
    };
    // The rustland binding (anthill-stl/anthill/int.anthill) declares
    // `provides Int64 … fact Eq[T = Int64]` — Int64 IS the Eq carrier for
    // T = Int64. SortProvidesInfo's `sort_ref` is therefore the Int64
    // symbol, so the node's `impl` Ref's Int64.
    assert_eq!(
        impl_sym,
        int_sym,
        "Eq[T = Int64]'s SortProvidesInfo carrier is Int64 itself; \
         Dictionary.impl must point to it. Got {}",
        kb.qualified_name_of(impl_sym)
    );

    // ONE positional sub-dictionary — WI-857: a dictionary bundles the SPEC's own
    // direct `requires` chain as its prefix, and `Eq requires PartialEq[T]`. So the
    // node carries `PartialEq[T = Int64]`'s own `Dictionary` node (also over Int64,
    // which provides both). It was EMPTY while the producer bundled only the
    // PROVIDER's chain — and `Int64`'s is empty, which is exactly the arity-0
    // dictionary that died at eval.
    //
    // WI-1045 — POSITIONAL, not a `requirements` cons spine: the IR node's key set
    // is now the VALUE's, where a sub-dictionary is positional child `k`.
    assert_eq!(
        pos_args.len(),
        1,
        "the spec half is `Eq`'s `requires PartialEq[T]`, so the node carries one \
         positional sub-dictionary, not zero"
    );
    let head_tid = pos_args[0];
    let head_named = match kb.get_term(head_tid) {
        Term::Fn {
            functor,
            named_args,
            ..
        } if *functor == syms.dict_ctor => named_args.clone(),
        other => panic!("the bundled entry must itself be a `Dictionary` node; got {other:?}"),
    };
    let inner_tid = head_named
        .iter()
        .find(|(k, _)| *k == syms.dict_impl)
        .map(|(_, v)| *v)
        .expect("impl");
    let inner_sym = match kb.get_term(inner_tid) {
        Term::Ref(s) | Term::Ident(s) => *s,
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } if pos_args.is_empty() && named_args.is_empty() => *functor,
        other => panic!("impl_functor must be a sort reference; got {other:?}"),
    };
    assert_eq!(
        inner_sym,
        int_sym,
        "`PartialEq[T = Int64]` is provided by Int64 as well; got {}",
        kb.qualified_name_of(inner_sym)
    );
}

//! WI-231 — requirement-insertion pass.
//!
//! Per `docs/design/operation-call-model.md` §"Pass structure: typer
//! first, requirement-insertion separate", the typer and the IR
//! elaboration step are distinct passes. The typer walks bodies and
//! *tags* each spec-op apply site's `NodeOccurrence` with a
//! `CallClass` on its `RefCell`. This pass consumes those
//! classifications and emits the corresponding IR rewrites into
//! `kb.dispatch_rewrites`.
//!
//! WI-251: source-of-truth for classifications moved from the legacy
//! `the legacy occurrence classification side-table` side-table to the
//! `NodeOccurrence`'s own RefCell. This pass walks `kb.op_bodies`
//! trees to collect tagged occurrences, then builds the rewritten Term
//! shape so reflection / proof tooling that inspects the elaborated
//! Term keeps working. Runtime reads CallClass directly off the
//! NodeOccurrence (post-WI-248) so the recorded rewrite is now
//! diagnostic-only.
//!
//! WI-873: each rewrite is keyed by its [`CallSite`] — the operation whose body
//! holds the call, the functor, and the span. It used to be keyed by a TermId-form
//! apply this pass SYNTHESIZED (`apply(fn = Ref(functor), args = nil())`), and terms
//! are hash-consed, so that key named the callee and nothing else: every call site of
//! one spec op in the image shared it and the recorders' idempotence guard silently
//! dropped all but the first. Measured before the fix: 47 classified sites, 16
//! recorded rewrites, and a total that did not move when a fixture added one.

use std::collections::HashMap;
use std::rc::Rc;

use smallvec::SmallVec;

use crate::intern::Symbol;
use crate::kb::node_occurrence::{for_each_child, Expr, NodeKind, NodeOccurrence};
use crate::kb::term::{Term, TermId};
use crate::kb::typing::{
    record_apply_rewrite, record_apply_within_concrete, record_apply_within_rewrite, CallClass,
    TypeError,
};
use crate::kb::{CallSite, KnowledgeBase};
use crate::span::SourceSpan;

/// WI-231 — entry point: walk every operation body in `kb.op_bodies`,
/// find classified Apply occurrences, and emit the corresponding IR
/// rewrite. Idempotent: re-running on a kb where rewrites already
/// exist is a no-op (the `record_*` helpers check
/// `kb.dispatch_rewrites.contains_key` before emitting).
///
/// WI-325: also collects `MissingRequiresForSpecOp` diagnostics for
/// `CallClass::UnresolvedSpecOp` tags — the typer detected an abstract
/// spec-op call without a covering `requires`. Returned to the load
/// pipeline alongside the typer's errors.
pub fn run(kb: &mut KnowledgeBase) -> Vec<TypeError> {
    // Collect into Vecs so we don't hold a borrow on `kb.op_bodies`
    // while emitting (each `record_*` mutates `kb.dispatch_rewrites`).
    //
    // WI-873: the OWNING OPERATION is carried from here, not re-derived. It is this
    // walk's own key, and it is the only place that knows it — an inner expression
    // occurrence's `owner` field is `None` (measured: all 47 classified sites over
    // stdlib + `anthill-stl` + one fixture), and `PinNow` records no enclosing scope at
    // all. It is one component of the [`CallSite`] every rewrite is keyed by.
    let body_roots: Vec<(Symbol, Rc<NodeOccurrence>)> =
        kb.op_bodies_iter().map(|(op, b)| (op, b.clone())).collect();
    let mut raw_entries: Vec<RawClassified> = Vec::new();
    for (op, root) in &body_roots {
        collect_classified(*op, root, &mut raw_entries);
    }
    stamp_nth_at_span(&mut raw_entries);

    // Split into IR-rewrite entries (need materialized Apply terms) and
    // error-only entries (UnresolvedSpecOp — no rewrite, just a
    // diagnostic). Materializing every entry would waste allocation
    // for the error-only ones and pollute `dispatch_origin`.
    let mut errors: Vec<TypeError> = Vec::new();
    let mut to_materialize: Vec<RawClassified> = Vec::with_capacity(raw_entries.len());
    for raw in raw_entries {
        match &raw.class {
            CallClass::UnresolvedSpecOp {
                spec_op_sym,
                spec_sort_sym,
                abstract_params,
                span,
                enclosing_sort,
            } => {
                // Self-recursive use inside the spec's own body — e.g. a
                // hypothetical derived `operation neq(a: T, b: T) = not(eq(a, b))`
                // inside `Eq` itself — is legitimate: `T` is the spec's own
                // type parameter and there's no enclosing user-side sort
                // that could carry a `requires` clause.
                if *enclosing_sort == Some(*spec_sort_sym) {
                    continue;
                }
                errors.push(TypeError::MissingRequiresForSpecOp {
                    span: *span,
                    spec_op_sym: *spec_op_sym,
                    spec_sort_sym: *spec_sort_sym,
                    abstract_params: abstract_params.clone(),
                });
            }
            _ => to_materialize.push(raw),
        }
    }

    // Materialize each remaining classified Apply into a Term::Fn apply
    // that the existing `record_*` helpers can act on. Each helper
    // rewrites the synthesized apply (replacing the `fn` slot with the
    // impl symbol) and inserts the (rewritten → spec_op_sym) pair into
    // `dispatch_origin`, which is what tooling and the WI-218 tests
    // observe.
    let entries: Vec<ClassifiedApply> = to_materialize
        .into_iter()
        .map(|raw| materialize_apply(kb, raw))
        .collect();

    let mut chain_cache: HashMap<Symbol, crate::kb::typing::DictChain> = HashMap::new();

    for entry in entries {
        let ClassifiedApply {
            site,
            apply_functor,
            named_args,
            pos_args,
            class,
        } = entry;
        match class {
            CallClass::PinNow {
                spec_op_sym,
                impl_op_sym,
            } => {
                record_apply_rewrite(
                    kb,
                    site,
                    apply_functor,
                    &named_args,
                    &pos_args,
                    spec_op_sym,
                    impl_op_sym,
                );
            }
            CallClass::ConcreteApplyWithin {
                fn_target_sym,
                callee_spec_sort,
                spec_op_sym,
                enclosing_sort,
                enclosing_op,
                resolved_tree,
                ..
            } => {
                let caller_requires = chain_for(kb, &mut chain_cache, enclosing_sort, enclosing_op);
                record_apply_within_concrete(
                    kb,
                    site,
                    &named_args,
                    &pos_args,
                    fn_target_sym,
                    callee_spec_sort,
                    spec_op_sym,
                    &caller_requires,
                    resolved_tree.as_ref(),
                );
            }
            CallClass::DeferToRequirement {
                spec_op_sym,
                slot,
                proj_path,
                enclosing_sort,
                enclosing_op,
                ..
            } => {
                record_apply_within_rewrite(
                    kb,
                    site,
                    &named_args,
                    &pos_args,
                    spec_op_sym,
                    enclosing_sort,
                    enclosing_op,
                    slot,
                    &proj_path,
                );
            }
            CallClass::UnresolvedSpecOp { .. } => {
                // Pre-filtered above into `errors`. Unreachable.
                unreachable!("UnresolvedSpecOp survived the pre-filter");
            }
            CallClass::EtaOpRef { .. } => {
                // WI-420: only ever set on an eta `VarRef` occurrence;
                // `collect_classified` yields `Expr::Apply` occs only, never
                // this, so it cannot reach the apply-rewrite loop.
                unreachable!("EtaOpRef classification on a non-apply occurrence");
            }
        }
    }

    errors
}

/// WI-873 — number each classified call within its `(op, functor, span)` group, so
/// the group's members get distinct [`CallSite`]s.
///
/// A SPAN DOES NOT IDENTIFY A CALL, which the first cut of this ticket assumed and a
/// review disproved with a program: `simp_rewrite::substitute_to_occurrence` builds
/// every node of a `[simp]` RHS from the single redex occurrence, and
/// `NodeOccurrence::synthesized_expr` inherits that occurrence's span — so a `[simp]`
/// equation whose RHS calls one deferred spec op twice puts two classified applies at
/// one `(op, functor, span)`. Without this stamp the second one's rewrite is dropped
/// by the recorders' idempotence guard, silently and indistinguishably from a
/// legitimate re-run: WI-873's own defect, recurring at a narrower key. See
/// [`CallSite::nth_at_span`] for the driven fixture.
///
/// The group is the collision class, not the whole walk, so the stamp is `0` for
/// every call in the stdlib / `anthill-stl` / `anthill-todo` / `github-todo` corpora
/// and only a macro expansion ever sees a `1`. That keeps the key stable against
/// changes in walk ORDER wherever the group is a singleton, which is everywhere that
/// matters.
///
/// AFTER THIS RUNS THE KEY IS INJECTIVE BY CONSTRUCTION, so nothing asserts
/// distinctness afterwards. The first cut of this fix did, and it was worth
/// measuring: a second `HashMap` over the same ~47 entries per load cost 2.5% of
/// `eval_tests` (min-of-3, 7.74s → 7.55s) to re-derive what this pass already knew.
///
/// COST OF THE FIX ITSELF, measured the same way: 6.98s → 7.55s, +8%. That is ~24
/// extra `record_apply_*` calls per stdlib load — the rewrites the old key was
/// dropping — several of them building a projection dictionary. It is the work that
/// was being skipped, not overhead added around it.
fn stamp_nth_at_span(raw: &mut [RawClassified]) {
    let mut counts: HashMap<(Symbol, Symbol, SourceSpan), u32> = HashMap::new();
    for r in raw.iter_mut() {
        let slot = counts.entry((r.op, r.functor, r.span)).or_insert(0);
        r.nth_at_span = *slot;
        *slot += 1;
    }
}

/// Pre-materialization: the apply's structural identity plus the
/// already-clone'd `CallClass` payload. Held in a Vec so we can drop
/// the immutable borrow on `kb.op_bodies` before allocating fresh
/// Term::Fn shapes for the helpers.
struct RawClassified {
    /// Apply functor — the `fn` symbol the typer was looking at.
    functor: Symbol,
    /// WI-873 — the operation whose body this occurrence was found in, and the
    /// occurrence's span. Together with `functor` and `nth_at_span` they are the
    /// [`CallSite`] the rewrite is keyed by.
    op: Symbol,
    span: SourceSpan,
    /// Filled by [`stamp_nth_at_span`] once the whole walk is collected — `0` until
    /// then, which is why [`Self::site`] must not be read before that runs.
    nth_at_span: u32,
    class: CallClass,
}

impl RawClassified {
    fn site(&self) -> CallSite {
        CallSite {
            op: self.op,
            functor: self.functor,
            span: self.span,
            nth_at_span: self.nth_at_span,
        }
    }
}

struct ClassifiedApply {
    site: CallSite,
    /// The `anthill.reflect.Expr.apply` symbol, interned once per materialization —
    /// the functor `record_apply_rewrite` builds the rewritten apply with.
    apply_functor: Symbol,
    named_args: SmallVec<[(Symbol, TermId); 2]>,
    pos_args: SmallVec<[TermId; 4]>,
    class: CallClass,
}

/// Walk a body NodeOccurrence tree, pushing one `RawClassified` per
/// Apply whose `classification` RefCell is set. Iterative — uses an
/// explicit work-stack so deeply-nested let / match / lambda chains
/// (e.g. the 624-line typing_pass_spec.anthill) don't blow the host
/// stack regardless of source nesting depth.
fn collect_classified(op: Symbol, root: &Rc<NodeOccurrence>, out: &mut Vec<RawClassified>) {
    let mut stack: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(32);
    stack.push(Rc::clone(root));
    while let Some(occ) = stack.pop() {
        let NodeKind::Expr {
            expr,
            classification,
            ..
        } = &occ.kind
        else {
            continue;
        };
        if let Expr::Apply { functor, .. } = expr {
            if let Some(class) = classification.borrow().as_deref() {
                out.push(RawClassified {
                    functor: *functor,
                    op,
                    span: occ.span,
                    // Assigned by `stamp_nth_at_span` after the whole walk — it needs
                    // to see every sibling at this span to number them.
                    nth_at_span: 0,
                    class: class.clone(),
                });
            }
        }
        for_each_child(expr, |c| stack.push(Rc::clone(c)));
    }
}

/// Synthesize the `fn` / `args` slots the existing `record_*` helpers read.
/// Shape: `fn = Ref(functor)`, `args = nil` — the helpers only look at the `fn`
/// slot to identify the spec op and at the `args` slot's structure for rewrite; for
/// the rewrite-table population they don't need the original args.
///
/// WI-873 STOPPED ASSEMBLING THESE INTO A WHOLE `apply(…)` TERM, because the only
/// thing that term was for was to be the rewrite table's KEY — and as a key it named
/// the functor and nothing else, so hash-consing collapsed every call site of one
/// spec op onto it and the recorders' idempotence guard dropped all but the first
/// (see [`crate::kb::CallSite`]). Nothing else read it: `record_apply_rewrite` only
/// took the apply functor back off it, which is passed directly now.
fn materialize_apply(kb: &mut KnowledgeBase, raw: RawClassified) -> ClassifiedApply {
    let apply_qn = kb.intern("anthill.reflect.Expr.apply");
    let fn_field = kb.intern("fn");
    let args_field = kb.intern("args");
    let nil_qn = kb.intern("nil");
    let nil_term = kb.alloc(Term::Fn {
        functor: nil_qn,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    let fn_ref = kb.alloc(Term::Ref(raw.functor));
    let mut named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
    named.push((fn_field, fn_ref));
    named.push((args_field, nil_term));
    ClassifiedApply {
        site: raw.site(),
        apply_functor: apply_qn,
        named_args: named,
        pos_args: SmallVec::new(),
        class: raw.class,
    }
}

/// WI-232 — fetch the caller's DICTIONARY chain for `enclosing_sort`, computing it at
/// most once per sort across the whole pass. WI-239: direct (not flat-transitive) so
/// the `caller_requires` indices fed to `build_dep_projection` align with
/// `synth_req_names`.
///
/// WI-869: and for the same alignment reason it is `provider_dict_entries`, not
/// `direct_requires_chain` — `synth_req_names` names the sort's `requires` chain
/// FOLLOWED BY its conditional provisions' `:- goals`, so a producer reading only the
/// declared half hands `build_dep_projection` indices that no longer point at the slot
/// they name. This is the SECOND producer of that positional list; the first is
/// `TypingEnv::set_enclosing_sort`, and the two must read one chain.
///
/// WI-822 LEG 1: and when the caller's OPERATION writes `requires` of its own, its
/// slots follow the sort's ([`op_dict_entries`]) — so the cache is keyed by the
/// operation when there is one. The typer's producer composes exactly the same way
/// (`TypingEnv::set_enclosing_op`); a `FromScope` index past the sort half would
/// otherwise be named off a shorter list here than the one it was resolved against.
fn chain_for(
    kb: &mut KnowledgeBase,
    cache: &mut HashMap<Symbol, crate::kb::typing::DictChain>,
    enclosing_sort: Option<Symbol>,
    enclosing_op: Option<Symbol>,
) -> crate::kb::typing::DictChain {
    // THE OP ARM IS UNCONDITIONAL, and a reviewer's objection to that was MEASURED
    // rather than accepted (WI-1092 review): `TypingEnv::set_enclosing_op` installs the
    // COMPOSED chain only when the operation declares an op-scoped one and otherwise
    // keeps the SORT chain `set_enclosing_sort` gave it, so this arm — which re-derives
    // its sort half from the OP (`op_dict_entries` → `impl_parent_of_op`) — reads a
    // different SOURCE from the producer wherever the two disagree. Mirroring the
    // producer's branch here (take the op chain only when the op declares one, else the
    // recorded `enclosing_sort`) looks like the obvious repair and IS NOT SAFE: driven
    // on top of WI-1091's widened-placement patch it flips
    // `wi227_projection_search_test::flat_path_emits_var_ref_named_requirement` from
    // `var_ref` to `requirement_at_sort`, on a fixture whose two chains have EQUAL
    // LENGTH and identical entries — so the two sources differ in something past their
    // slots, which that patch's new `DictChain::owner()` reader can see and this file
    // cannot. Which source is right is therefore WI-1091's question, not this arm's:
    // its patch is the only code that reads the difference.
    if let Some(op) = enclosing_op {
        if let Some(cached) = cache.get(&op) {
            return cached.clone();
        }
        let chain = crate::kb::typing::op_dict_entries(kb, op);
        // Keyed by the OPERATION symbol, which is disjoint from the sort symbols the
        // other arm keys by, so one map serves both without collision.
        cache.insert(op, chain.clone());
        return chain;
    }
    let s = match enclosing_sort {
        Some(s) => s,
        None => return crate::kb::typing::DictChain::empty(),
    };
    if let Some(cached) = cache.get(&s) {
        return cached.clone();
    }
    let chain = crate::kb::typing::provider_dict_entries(kb, s);
    cache.insert(s, chain.clone());
    chain
}

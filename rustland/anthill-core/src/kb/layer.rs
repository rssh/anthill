//! WI-SPGBP — a DISCARDABLE LAYER over a knowledge base.
//!
//! `execute(loaded(sources), q)` loads sources into a scope that can be thrown away.
//! The ticket states the rule for what "thrown away" has to mean, and it is stronger
//! than dropping the clauses: dropping the layer must make a name the load introduced
//! **unresolvable again**, not merely clause-less. A partial discard is worse than none,
//! because the safety claim then reads as total while a resolvable name is left behind.
//!
//! # Snapshot, not persistent structures
//!
//! The ticket left "persistent-vs-high-water-mark" open and asked for a measurement.
//! Measured on a debug build against `load_stdlib_and_stl` (the whole stdlib plus the
//! Rust host bindings, 1722 ms): a FULL deep clone of everything a layer must scope is
//! **2.7 ms — 0.16 % of one load**. Of that, `by_qualified_name` + `scopes` is 2.0 ms and
//! every clause-side index together is 0.12 ms; [`crate::kb::discrim::SubstTree`] needs
//! nothing at all, since WI-537's Γ overlay already made it `Rc`-COW (37 µs).
//!
//! So the KB's `HashMap`s are NOT retyped as `imbl` HAMTs. That would tax every load and
//! every resolution — the hot paths — to save 2.7 ms on an operation invoked once per
//! `loaded(…)`, whose own cost (parsing and loading the scoped sources) is orders of
//! magnitude larger. A layer is a snapshot of the mutable state, applied to the
//! interpreter's own KB in place and restored on discard.
//!
//! # What that buys, and what it costs
//!
//! In-place means the INTERNERS are not rolled back, and that is the sound direction
//! rather than a shortcut. A `TermId`, `Symbol` or `SourceId` minted inside the layer can
//! ride out on a `Solution` the caller keeps; after the discard it must still NAME
//! something. Rolling an interner back would leave such a value indexing a slot that had
//! been reissued to a different term — a silent wrong answer, where the leak we take
//! instead (the layer's terms keep their refcounts) is merely memory.
//!
//! One `RuleId` needs more than that, because it is the only index the KB hands OUT:
//! `stored_facts_of` mints a `FactRef` over it, and `rules` is scoped. See
//! [`KnowledgeBase::tombstone_layer_rules`].
//!
//! # Layers are dynamically scoped, and compose in creation order
//!
//! This is the consequence of applying in place, and a caller has to know it. While a
//! layer is applied it IS the interpreter's knowledge base, so `kb()` — the ambient
//! accessor — and the layer value denote the same thing: `KB.sorts(kb(), …)` written
//! between `loaded(srcs)` and `execute(…)` sees the layer's sorts. Two live layers means
//! the second sees the first, because there is one KB underneath both.
//!
//! It OVER-reports and can never make the base lose anything, so nothing a trusted goal
//! relies on disappears. But it is not the "two independent KB values" the shape of the
//! API might suggest, and a reader who assumes that will be wrong. Making `kb()` denote
//! the base while a layer is live needs a genuinely separate layered KB object — which
//! costs the interner sharing that makes a caller's goal legal in the layer at all, the
//! property the ticket chose the layer form to get.
//!
//! Discard is likewise DEFERRED rather than immediate, and layers unwind innermost-first;
//! [`crate::eval::layer_arena`] carries that half, including why waiting is correct
//! rather than merely tolerated.

use super::*;

/// The scoped half of a [`KnowledgeBase`], captured for restore.
///
/// A `KnowledgeBase` is its carrier only because that spares this file a second copy of
/// ~70 field types; the interner half of the value inside is a FRESH EMPTY ONE and means
/// nothing. It must never be used as a KB, which is what the newtype is for.
pub(crate) struct KbScopedSnapshot {
    /// A `KnowledgeBase` is the carrier only because that spares this file a second copy
    /// of ~70 field types. Boxed: it is a large struct and a snapshot is moved around.
    kb: Box<KnowledgeBase>,
    /// The definition half — see [`crate::intern::SymbolScopeSnapshot`], which explains
    /// why `defs` and `intern_map` are treated differently from the scope tables.
    symbols: crate::intern::SymbolScopeSnapshot,
    /// The mount half — see [`crate::kb::extent::ExtentScopeSnapshot`]. Separate for the
    /// same reason as `symbols`: the registry holds live host backends that cannot be
    /// cloned, beside mount tables that must be rolled back.
    extents: crate::kb::extent::ExtentScopeSnapshot,
}

/// The scoped field list — the single place it is written.
///
/// Every field named here is cloned at [`KnowledgeBase::snapshot_scoped`] and assigned
/// back at [`KnowledgeBase::restore_scoped`]. A field NOT named here is monotone, and
/// [`classify_every_field_for_layering`] is where each such omission has to state its
/// reason — that function fails to compile until a newly added field is classified.
macro_rules! kb_scoped_fields {
    ($($f:ident),* $(,)?) => {
        impl KnowledgeBase {
            /// WI-SPGBP — capture the scoped state (see the module docs).
            pub(crate) fn snapshot_scoped(&mut self) -> KbScopedSnapshot {
                // Freezing the term store is part of TAKING the snapshot, not an
                // afterthought: from here until the matching restore, `rules` can be
                // rolled back over ids the store must therefore not have reissued. See
                // `TermStore::release`.
                self.terms.pin();
                let mut kb = Box::new(KnowledgeBase::new());
                $( kb.$f = self.$f.clone(); )*
                KbScopedSnapshot {
                    kb,
                    symbols: self.symbols.snapshot_scoped(),
                    extents: self.extents.snapshot_scoped(),
                }
            }

            /// WI-SPGBP — discard everything the layer defined and asserted.
            pub(crate) fn restore_scoped(&mut self, snap: KbScopedSnapshot) {
                // Taken BEFORE the restore overwrites `rules` — see
                // [`KnowledgeBase::tombstone_layer_rules`] for why the layer's clause
                // slots must not simply vanish.
                let layer_rules = std::mem::take(&mut self.rules);
                let KbScopedSnapshot { kb, symbols, extents } = snap;
                // Move each field OUT of the owned snapshot rather than `mem::take` it:
                // `SubstTree` has no `Default`, and a take would leave the snapshot in a
                // half-emptied state that means nothing. `KnowledgeBase` has no `Drop`,
                // so the partial move is legal.
                let kb = *kb;
                $( self.$f = kb.$f; )*
                self.symbols.restore_scoped(symbols);
                self.extents.restore_scoped(extents);
                self.tombstone_layer_rules(layer_rules);
                // The other half of the pin taken in `snapshot_scoped`. LAST, after the
                // rollback that needed it.
                self.terms.unpin();
            }
        }
    };
}

kb_scoped_fields!(
    // ── clauses and their indexes ──────────────────────────────
    rules,
    rules_by_functor,
    by_domain,
    rules_by_label,
    bodied_rule_counts,
    discrim,
    fact_dedup,
    value_fact_dedup,
    synth_rule_memo,
    guards,
    guards_by_sort,
    rule_head_captures,
    resolved_requires_facts,
    judged_row_binding_clauses,
    unbacked_derived_provisions,
    derived_provision_origin,
    // ── declarations: what makes a name MEAN something ─────────
    builtins,
    entity_fields,
    entity_field_types,
    constructor_symbols,
    sort_entities,
    entity_parent,
    sort_info,
    sort_base_subst,
    op_records,
    op_decl_sites,
    op_capture_params,
    decl_sites,
    scope_text_files,
    named_requirement_slots,
    type_param_canonical_var,
    const_types,
    const_bodies,
    existential_return_ops,
    field_wise_noneq_carriers,
    sort_ops,
    host_mapped_ops,
    interpreter_mapped_ops,
    host_op_mappings,
    host_op_registrations,
    host_const_mappings,
    default_providers,
    provides_clause_seen,
    // ── derived indexes and well-known symbols ─────────────────
    sort_alias_index,
    provides_index,
    sort_info_index,
    requires_index,
    sort_sort,
    entity_of_sort,
    eq_connective_sym,
    unify_connective_sym,
    or_connective_sym,
    and_connective_sym,
    tuple_literal_sym,
    has_dot_applies,
    simp_gate_cache,
    absence_records,
    absence_marker_syms,
    // ── spans and diagnostics accumulated by a load ────────────
    term_spans,
    functor_spans,
    parameterized_type_sites,
    rigid_projection_formations,
    unsuppliable_requirements,
    dispatch_rewrites,
    // ── memo caches ────────────────────────────────────────────
    //
    // SCOPED, and this is not bookkeeping tidiness. Each memoizes an answer COMPUTED
    // UNDER the layer's declarations; leaving one behind lets a layer's dispatch
    // decision be served to the base after the discard, from a cache the base can no
    // longer justify. That is the "resolvable name left behind" failure wearing a
    // different hat.
    requires_chain_cache,
    requires_tree_cache,
    synth_req_names_cache,
    op_requires_chain_cache,
    synth_op_req_names_cache,
    op_dict_chain_cache,
    op_frame_names_cache,
    provider_dict_chain_cache,
    sort_param_pairs_cache,
    spec_carrier_param_cache,
    resolve_cache,
);

impl KbScopedSnapshot {
    /// WI-5XBBQ — `SymbolTable::defs.len()` as it stood before the layer.
    pub(crate) fn symbol_mark(&self) -> u32 {
        self.symbols.defs_mark()
    }

    /// WI-5XBBQ — `KnowledgeBase::rules.len()` as it stood before the layer.
    ///
    /// Read off the snapshot's own clause vector, which is the pre-layer one: this is
    /// the same mark [`KnowledgeBase::tombstone_layer_rules`] uses to decide which slots
    /// the layer issued.
    pub(crate) fn clause_mark(&self) -> usize {
        self.kb.rules.len()
    }
}

impl KnowledgeBase {
    /// WI-SPGBP — a `RuleId` a layer issued is NEVER REUSED.
    ///
    /// Restoring `rules` shortens the vector, and `RuleId` is an index into it. Left at
    /// that, the next clause asserted after a discard takes a slot the layer had already
    /// handed out — and a `FactRef` minted inside the layer (`stored_facts_of` returns
    /// them) would then name a DIFFERENT row, silently. Every other index in the KB is
    /// rebuilt from the snapshot and cannot alias; this one is issued to callers, so it
    /// is the only one that can.
    ///
    /// So the layer's slots are kept as TOMBSTONES — the same `retracted: true` state
    /// [`Self::retract`] produces, entry unchanged — rather than truncated away. That
    /// introduces no new state for a reader to know about: a stale `FactRef` finds a
    /// retracted row, which every reader already handles, instead of a live wrong one.
    /// The indexes come from the snapshot and never mention these slots, which is also
    /// what `retract` leaves behind.
    ///
    /// The cost is that `rules` does not shrink on a discard. That is a leak in the same
    /// family as the layer's interned terms (see the module docs): bounded by what the
    /// layer actually loaded, and memory rather than a wrong answer.
    fn tombstone_layer_rules(&mut self, layer_rules: Vec<RuleEntry>) {
        let base_len = self.rules.len();
        for mut entry in layer_rules.into_iter().skip(base_len) {
            entry.retracted = true;
            self.rules.push(entry);
        }
    }
}

/// WI-SPGBP — the completeness check for the layer discipline.
///
/// It does nothing at runtime and is never called. It exists because it destructures
/// [`KnowledgeBase`] with **no `..` rest-pattern**: adding a field fails to compile here
/// until its author has said which half it is in — listed in `kb_scoped_fields!` above,
/// or bound to `_` here beneath a comment saying why it is monotone.
///
/// The ticket calls the definition side "the part that can be silently wrong". This is
/// the structural answer to that, in place of a comment asking the next author to
/// remember.
#[allow(dead_code)]
fn classify_every_field_for_layering(kb: &KnowledgeBase) {
    let KnowledgeBase {
        // ── MONOTONE: the interners ────────────────────────────
        //
        // A `TermId` minted inside the layer can leave it on a `Solution` the caller
        // keeps. Roll the store back and that id names a slot the free-list has since
        // reissued to a different term — a silent wrong answer. The leak we take instead
        // (the layer's terms keep their refcounts) is only memory.
        terms: _,
        // The SAME rule, one level down, and it is why `SymbolTable` gets its own
        // snapshot rather than being cloned wholesale here: its `defs` and `intern_map`
        // are monotone for exactly the reason above, while its scope tables are scoped.
        // See `SymbolScopeSnapshot`.
        symbols: _,
        // Fresh-`VarId` counter. Rolling it back reissues ids that the layer's escaped
        // substitutions still use, so two distinct variables would collide.
        next_var: _,
        // `SourceId` is an index into this registry and rides inside every `SourceSpan`.
        // An interner by another name: truncating it makes a layer-minted span report a
        // different file, or none.
        sources: _,
        // Registered by the EMBEDDER through a Rust API, never by loading a file
        // (WI-1122), and sealed once the loader has built its host-mapping cache. A
        // scoped load cannot add one, so there is nothing here for a discard to undo.
        host_fns: _,
        // SPLIT, like `symbols`: the live host backends in it are monotone, its mount
        // tables are scoped. See `ExtentScopeSnapshot`.
        extents: _,
        // `#[cfg(test)]` knob for the carrier-`eq` sub-proof budget (WI-628) — a test
        // instrument, not KB state.
        #[cfg(test)]
            sem_eq_sub_depth: _,

        // ── SCOPED: every field to the NEXT HEADER is in `kb_scoped_fields!` ─
        rules: _,
        rules_by_functor: _,
        by_domain: _,
        rules_by_label: _,
        bodied_rule_counts: _,
        discrim: _,
        fact_dedup: _,
        value_fact_dedup: _,
        synth_rule_memo: _,
        guards: _,
        guards_by_sort: _,
        rule_head_captures: _,
        resolved_requires_facts: _,
        // WI-20260831-V25N3 — which clause facts the written-row-label walk has already
        // judged, so a later load does not re-report an earlier batch's clause.
        //
        // SCOPED, like `resolved_requires_facts` directly above and for its reason: both
        // record that a LOAD PASS has already acted on a given fact, and a discarded
        // layer's load is one that did not happen as far as the base is concerned.
        //
        // It was first bound here under a MONOTONE comment — INSIDE this section, whose
        // header says otherwise, and citing `resolved_requires_facts` (a scoped field) as
        // its precedent for being monotone. The behavioural half of that argument was
        // "an entry can only ever be ADDED, and a leaked addition merely suppresses a
        // re-report of a row that no longer exists". WI-20260901-EA6KS made it false in
        // kind: the set is now REMOVED from as well, by
        // [`KnowledgeBase::note_metadata_fact_presented`], and a leaked REMOVAL is the
        // opposite failure — a base clause the layer un-claimed and the discard did not
        // restore would be re-reported by a later batch that presented nothing, which is
        // the bug the set exists to prevent.
        //
        // NOTHING DRIVES THE DIFFERENCE TODAY, and this says so rather than crediting a
        // fixture: every removal is followed by the walk's own re-claim inside the SAME
        // `load_phase_inner`, which has no early return between the two, so a layer
        // cannot currently end with a base rid removed-but-unclaimed. What is fixed here
        // is the CLASSIFICATION — this function's whole purpose is that the next author
        // adding a field below this one reads the section header and is right.
        judged_row_binding_clauses: _,
        unbacked_derived_provisions: _,
        derived_provision_origin: _,
        builtins: _,
        entity_fields: _,
        entity_field_types: _,
        constructor_symbols: _,
        sort_entities: _,
        entity_parent: _,
        sort_info: _,
        sort_base_subst: _,
        op_records: _,
        op_decl_sites: _,
        op_capture_params: _,
        decl_sites: _,
        scope_text_files: _,
        named_requirement_slots: _,
        type_param_canonical_var: _,
        const_types: _,
        const_bodies: _,
        existential_return_ops: _,
        field_wise_noneq_carriers: _,
        sort_ops: _,
        host_mapped_ops: _,
        interpreter_mapped_ops: _,
        host_op_mappings: _,
        // WI-880 — SCOPED, and it MUST be, because it is a memo of `host_op_mappings`
        // directly above and that field is scoped. A memo is scoped exactly when the
        // thing it caches is: leave it out and a discard rolls the mappings back to the
        // base while the memo keeps the LAYER's derivation, which is a desync the
        // per-interpreter re-derivation used to hide.
        //
        // FOUND BY /code-review, and the comment this replaced justified the omission
        // with a claim that is FALSE: "a layer does not run the post-load pass". It
        // does — `kb_loaded` reaches `load_all` into a live KB -> `load_phase_inner` ->
        // `build_host_op_mappings` -> `set_host_op_mappings`. The worst case is not a
        // stale registration but a POISONED base: a layer whose `operation_map` names an
        // unknown `host_fn` memoizes the refusal (the whole point of caching the `Err`),
        // and after the discard every interpreter built over the base KB fails
        // permanently for a mapping the base no longer has — defeating `kb_loaded`'s own
        // contract that a failed `loaded` leaves the KB as it found it.
        host_op_registrations: _,
        host_const_mappings: _,
        default_providers: _,
        provides_clause_seen: _,
        sort_alias_index: _,
        provides_index: _,
        sort_info_index: _,
        requires_index: _,
        sort_sort: _,
        entity_of_sort: _,
        eq_connective_sym: _,
        unify_connective_sym: _,
        or_connective_sym: _,
        and_connective_sym: _,
        tuple_literal_sym: _,
        has_dot_applies: _,
        simp_gate_cache: _,
        absence_records: _,
        absence_marker_syms: _,
        term_spans: _,
        functor_spans: _,
        parameterized_type_sites: _,
        rigid_projection_formations: _,
        unsuppliable_requirements: _,
        dispatch_rewrites: _,
        requires_chain_cache: _,
        requires_tree_cache: _,
        synth_req_names_cache: _,
        op_requires_chain_cache: _,
        synth_op_req_names_cache: _,
        op_dict_chain_cache: _,
        op_frame_names_cache: _,
        provider_dict_chain_cache: _,
        sort_param_pairs_cache: _,
        spec_carrier_param_cache: _,
        resolve_cache: _,

        // ── NEITHER: in-flight stack state, in NO list ─────────
        //
        // A THIRD CLASS, and it needs its own header rather than a comment inside the
        // SCOPED block. This destructure's whole contract is that a field's POSITION
        // declares its class, so a field sitting under "every field below is in
        // `kb_scoped_fields!`" while deliberately absent from that list makes the header
        // false and tells an auditor of the scoped block that this one is snapshotted and
        // rolled back. It is not (found by /code-review).
        //
        // WI-20260829-N01PY — NEITHER MONOTONE NOR SCOPED, because it is neither derived
        // state nor a memo: it holds the `(carrier, spec)` questions currently ON THE
        // STACK, and every insert is paired with a remove on the way out. Outside a
        // `witness_provides_admissibly` call it is EMPTY, so a layer has nothing of it to
        // roll back — the rule the memos above obey ("a memo is scoped exactly when the
        // thing it caches is") does not reach it, because it caches nothing.
        witness_admissibility_in_flight: _,
    } = kb;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kb::load::{self, NullResolver};
    use crate::kb::term::{Literal, Var};
    use crate::parse;

    /// A scoped load: one namespace contributing a DEFINITION (`Widget`, `gadget`), a
    /// CLAUSE (the `gadget` fact) and a RULE whose head is a name of its own (`wide`).
    /// All three halves of what a layer has to be able to forget.
    const LAYER_SRC: &str = r#"
namespace spgbp.layer_demo
  sort Widget
    entity gadget(id: Int64)
  end

  fact gadget(id: 7)

  rule wide(?i)
    :- gadget(id: ?i)
end
"#;

    fn load_layer_src(kb: &mut KnowledgeBase) {
        let parsed = parse::parse(LAYER_SRC).expect("parse layer fixture");
        if let Err(errs) = load::load_all(kb, &[&parsed], &NullResolver) {
            panic!(
                "layer load errors: {:?}",
                errs.iter().map(|e| e.to_string()).collect::<Vec<_>>()
            );
        }
    }

    /// Solutions for `spgbp.layer_demo.wide(?x)`, or `None` when the name does not even
    /// resolve. The two answers are deliberately DISTINCT: "the name is gone" and "the
    /// name is there with no clauses" are exactly the two states the ticket says a
    /// partial discard confuses, so the test must be able to tell them apart.
    fn wide_solutions(kb: &mut KnowledgeBase) -> Option<usize> {
        let wide = kb.try_resolve_symbol("spgbp.layer_demo.wide")?;
        let x_name = kb.intern("x");
        let v = kb.fresh_var(x_name);
        let arg = kb.alloc(Term::Var(Var::Global(v)));
        let goal = kb.alloc(Term::Fn {
            functor: wide,
            pos_args: SmallVec::from_slice(&[arg]),
            named_args: SmallVec::new(),
        });
        Some(
            kb.resolve(&[goal], &crate::kb::resolve::ResolveConfig::default())
                .iter()
                .filter(|s| s.residual.is_empty())
                .count(),
        )
    }

    /// A BASE fact that must survive the discard untouched — the control for
    /// over-restoring. `anthill.prelude.Option.some` is a prelude entity constructor, so
    /// it is defined long before any layer exists.
    fn base_name_resolves(kb: &KnowledgeBase) -> bool {
        kb.try_resolve_symbol("anthill.prelude.Option.some")
            .is_some()
    }

    /// A LAYER'S `operation_map` MUST NOT OUTLIVE THE LAYER — WI-880, found by
    /// /code-review.
    ///
    /// `host_op_registrations` is a memo of `host_op_mappings`, which is scoped; the memo
    /// was not, so a discard rolled the mappings back to the base while the memo kept the
    /// LAYER's derivation. The per-interpreter re-derivation it replaced was self-healing,
    /// which is why nothing noticed.
    ///
    /// THE POISONED-BASE SHAPE, driven here because it is the worst one and the only one
    /// visible from outside: a binding block naming an unknown `host_fn` LOADS CLEAN —
    /// `build_host_op_mappings` checks that the operation is declared, never that the key
    /// resolves, because which functions a runtime exposes is only that runtime's to know
    /// (kernel-language.md §10.2). The refusal lands when an interpreter is built, and it
    /// is CACHED, so without the fix every later interpreter over the BASE KB fails
    /// permanently for a mapping the base does not have — defeating the discard's own
    /// contract.
    ///
    /// WHAT FAILS WHEN THE FIX IS BACKED OUT (drop `host_op_registrations` from
    /// `kb_scoped_fields!`): the LAST assertion, and only it. Everything before the
    /// restore passes either way — those lines exist to prove the layer's broken mapping
    /// really did poison the memo, so that "the base is clean afterwards" is not vacuously
    /// true of a memo that was never populated.
    ///
    /// `register_standard_builtins` IS THE PROBE, not a full evaluation: it is the one
    /// step that reads the memo, and reading it is the whole question.
    #[test]
    fn wi880_a_discarded_layers_operation_map_does_not_poison_the_base() {
        // A carrier declaring one body-less operation, mapped to a key `HOST_FNS` and the
        // embedder registry both lack.
        const BROKEN_BINDING: &str = r#"
namespace wi880.layerpoison
  sort Widget3
    import anthill.prelude.{Int64}
    entity widget3(id: Int64)
    operation squish(a: Widget3) -> Int64
  end

  provides Widget3 language rust
    artifact "rustland/anthill-stl/src/prelude/int.rs"
    operation_map { squish: "no_such_host_function" }
  end
end
"#;
        let interp_builds = |kb: &mut KnowledgeBase| -> Result<(), String> {
            // `Interpreter::new` MOVES the KB, so hand it a taken one and put it back —
            // the same `mem::take` shape `run_in_bridge_interp` uses, and the reason the
            // memo rides the KB at all.
            let taken = std::mem::take(kb);
            let mut interp = crate::eval::Interpreter::new(taken);
            let verdict = crate::eval::builtins::register_standard_builtins(&mut interp)
                .map_err(|e| format!("{e:?}"));
            *kb = interp.into_kb();
            verdict
        };

        let mut kb = crate::kb::test_support::load_stdlib(None);
        assert!(
            interp_builds(&mut kb).is_ok(),
            "the base KB must build an interpreter before the layer — otherwise the \
             assertion after the discard would hold for a reason that has nothing to \
             do with the layer"
        );

        let snap = kb.snapshot_scoped();
        let parsed = parse::parse(BROKEN_BINDING).expect("parse broken binding");
        assert!(
            load::load_all(&mut kb, &[&parsed], &NullResolver).is_ok(),
            "an unknown `host_fn` is NOT a load error — the loader cannot know which \
             functions a runtime exposes. If this starts failing the fixture no longer \
             reaches the memo and the last assertion means nothing"
        );
        let err = interp_builds(&mut kb).expect_err(
            "the layer's mapping names a function no registry has, so building an \
             interpreter over the LAYER must refuse — and that refusal is what gets \
             memoized",
        );
        assert!(
            err.contains("no_such_host_function"),
            "the refusal must name the key, or the memo below holds something else: {err}"
        );

        kb.restore_scoped(snap);

        // THE ASSERTION. The base KB has no such mapping, so it must build interpreters
        // again exactly as it did above.
        assert!(
            interp_builds(&mut kb).is_ok(),
            "a discarded layer's `operation_map` must not survive in the registration \
             memo — the base KB never named `no_such_host_function`"
        );
    }

    /// WI-SPGBP — the headline: a discard makes a name the layer introduced
    /// UNRESOLVABLE again, not merely clause-less.
    ///
    /// WHAT FAILS WHEN THE CHANGE IS BACKED OUT: every assertion after `restore_scoped`.
    /// With no restore at all, `Widget` still resolves and `wide` still answers 1 — the
    /// pre-ticket behaviour.
    ///
    /// MEASURED, not asserted: with `restore_scoped` left in place but its
    /// `symbols.restore_scoped` call removed — a CLAUSES-ONLY discard, exactly the
    /// partial one the ticket refuses — this test fails at the first post-restore
    /// assertion (`Widget` is still resolvable) while the other two tests in this module
    /// stay green. That is the whole of "a partial discard is worse than none", and it is
    /// what makes the definition half worth its own snapshot.
    ///
    /// WHAT PASSES EITHER WAY, BY DESIGN: the three assertions before the restore; they
    /// exist to prove the layer actually took effect, so that "it is gone afterwards" is
    /// not vacuously true of a load that never happened.
    #[test]
    fn spgbp_a_discarded_layer_leaves_no_resolvable_name() {
        let mut kb = crate::kb::test_support::load_stdlib(None);
        let snap = kb.snapshot_scoped();

        // The layer took effect: definitions, clauses and rule-head names all live.
        load_layer_src(&mut kb);
        assert!(
            kb.try_resolve_symbol("spgbp.layer_demo.Widget").is_some(),
            "the layer's sort must be resolvable while the layer is live"
        );
        assert!(
            kb.try_resolve_symbol("spgbp.layer_demo.Widget.gadget")
                .is_some(),
            "the layer's entity constructor must be resolvable while the layer is live"
        );
        assert_eq!(
            wide_solutions(&mut kb),
            Some(1),
            "the layer's rule must answer off the layer's fact while the layer is live"
        );

        kb.restore_scoped(snap);

        // The definition half — the part the ticket calls "the part that can be silently
        // wrong". A layer that only dropped its clauses would still answer `Some` here.
        assert_eq!(
            kb.try_resolve_symbol("spgbp.layer_demo.Widget"),
            None,
            "a discarded layer's sort must be UNRESOLVABLE, not merely clause-less"
        );
        assert_eq!(
            kb.try_resolve_symbol("spgbp.layer_demo.Widget.gadget"),
            None,
            "a discarded layer's entity constructor must be UNRESOLVABLE"
        );
        assert_eq!(
            wide_solutions(&mut kb),
            None,
            "a discarded layer's rule-head name must be UNRESOLVABLE — `Some(0)` here \
             would mean the name survived with its clauses dropped, which is the \
             partial discard the ticket refuses"
        );

        // The control for over-restoring: the base is untouched.
        assert!(
            base_name_resolves(&kb),
            "the discard must not take the BASE's definitions with it"
        );
    }

    /// WI-SPGBP — the base's own clauses still answer after a discard.
    ///
    /// The name-resolution control above cannot see a clause-side over-restore: rolling
    /// `rules` back too far leaves every name resolvable and every query empty. This
    /// drives a BASE goal across the discard.
    ///
    /// WHAT FAILS WHEN BACKED OUT: nothing — this is a pure control, and it passes both
    /// with and without `restore_scoped`. It is here to catch the opposite error, a
    /// restore that reaches past the layer.
    #[test]
    fn spgbp_a_discard_does_not_reach_past_the_layer() {
        let mut kb = crate::kb::test_support::load_stdlib(None);

        let before = prelude_entity_of_count(&mut kb);
        assert!(
            before > 0,
            "the fixture must have base clauses to lose, or this control measures nothing"
        );

        let snap = kb.snapshot_scoped();
        load_layer_src(&mut kb);
        kb.restore_scoped(snap);

        assert_eq!(
            prelude_entity_of_count(&mut kb),
            before,
            "a discard must restore the base's clause count exactly"
        );
        assert!(base_name_resolves(&kb));
    }

    /// How many entity constructors the prelude's `Option` sort has — a base clause-side
    /// reading that a too-eager restore would drop to zero.
    fn prelude_entity_of_count(kb: &mut KnowledgeBase) -> usize {
        let opt = kb
            .try_resolve_symbol("anthill.prelude.Option")
            .expect("prelude Option");
        kb.sort_children(opt).len()
    }

    /// WI-SPGBP — a `RuleId` the layer issued is never handed out again.
    ///
    /// `RuleId` is an index into `rules`, and `rules` is SCOPED — so a naive restore
    /// shortens it and the next clause asserted takes a slot the layer already gave to a
    /// caller (`stored_facts_of` mints `FactRef`s over exactly these ids). The layer's
    /// slots are kept as tombstones instead. This drives the property from both ends: the
    /// vector does not shrink, and every slot the layer added reads as retracted — so a
    /// stale reference finds a RETRACTED row, not a live wrong one.
    ///
    /// WHAT FAILS WHEN BACKED OUT: delete the `tombstone_layer_rules` call and the first
    /// assertion fails (the vector is back to `base_len`), which is precisely the state in
    /// which the next assert aliases a layer-issued id.
    ///
    /// WHAT PASSES EITHER WAY, BY DESIGN: `rule_count` / `live_rule_ids` filter on
    /// `retracted` already, so the live counts are the same under both — asserted here so
    /// that the tombstones are shown to be invisible to every ordinary reader.
    #[test]
    fn spgbp_a_layer_issued_rule_id_is_never_reused() {
        let mut kb = crate::kb::test_support::load_stdlib(None);
        let base_len = kb.rules.len();
        let live_before = kb.live_rule_ids().len();

        let snap = kb.snapshot_scoped();
        load_layer_src(&mut kb);
        let layered_len = kb.rules.len();
        assert!(
            layered_len > base_len,
            "the fixture must add clauses, or this measures nothing"
        );

        kb.restore_scoped(snap);

        assert_eq!(
            kb.rules.len(),
            layered_len,
            "the clause vector must NOT shrink — a reused RuleId would silently rename a \
             row a FactRef minted inside the layer still points at"
        );
        assert!(
            (base_len..layered_len).all(|i| kb.rules[i].retracted),
            "every slot the layer added must read as retracted"
        );
        assert_eq!(
            kb.live_rule_ids().len(),
            live_before,
            "tombstones are invisible to every live-clause reader"
        );
    }

    /// WI-SPGBP — a base fact RETRACTED while a layer is live does not come back
    /// pointing at a reissued term slot.
    ///
    /// The monotone-interner argument runs one way only: an id that ESCAPES the layer
    /// stays valid because the store never shrinks. An id can also RE-ENTER. `rules` IS
    /// rolled back, so a base row retracted during the layer's life — its head dropping
    /// to refcount 0, the slot freed and handed to one of the layer's own terms — is
    /// reinstated by the discard still naming that slot. Silently a different fact, or a
    /// panic in `TermStore::get` on a freed slot. `TermStore::release` is therefore a
    /// no-op while a layer is applied.
    ///
    /// WHAT FAILS WHEN BACKED OUT: remove the `pin`/`unpin` pair and the last assertion
    /// reads a term the layer's own loading has since been given, or panics outright.
    /// The middle assertion (the slot still readable while the layer is live) fails first.
    #[test]
    fn spgbp_a_retract_under_a_layer_does_not_free_a_slot_the_discard_restores() {
        const BASE: &str = r#"
namespace spgbp.pin_demo
  sort Gauge
    entity gauge(id: Int64)
  end

  fact gauge(id: 4242)
end
"#;
        let mut kb = crate::kb::test_support::load_stdlib(Some(BASE));
        let gauge = kb
            .try_resolve_symbol("spgbp.pin_demo.Gauge.gauge")
            .expect("base constructor");

        // The base fact's own rule and the term its head interned to.
        let rule = *kb
            .rules_by_functor
            .get(&gauge)
            .and_then(|ids| ids.first())
            .expect("the base fact is stored under its functor");
        let head = match kb.rule_head_value(rule) {
            crate::eval::value::Value::Term { id, .. } => *id,
            other => panic!("expected a Term-carried head, got {other:?}"),
        };
        let head_before = kb.get_term(head).clone();

        let snap = kb.snapshot_scoped();
        load_layer_src(&mut kb);

        // The retract that used to free the slot. Under the pin the row goes away but
        // the term does not.
        kb.retract(rule);
        assert_eq!(
            *kb.get_term(head),
            head_before,
            "a term released under a live layer must not be freed — the discard is about \
             to reinstate a row that still names it"
        );

        kb.restore_scoped(snap);

        assert_eq!(
            *kb.get_term(head),
            head_before,
            "the restored base row must still name ITS OWN term, not one the layer was \
             handed after the slot was freed"
        );
        assert!(
            kb.live_rule_ids().contains(&rule),
            "the discard restores the base row the retract removed"
        );
    }

    /// WI-SPGBP — the interners are MONOTONE across a discard, and that is what keeps a
    /// value the layer produced meaningful afterwards.
    ///
    /// WHAT FAILS WHEN BACKED OUT: this fails if `terms` or `SymbolTable::defs` is ever
    /// added to the scoped list — the term id and the symbol would then name a slot that
    /// no longer exists (or, worse, one reissued to something else).
    #[test]
    fn spgbp_a_layer_minted_term_still_names_something_after_the_discard() {
        let mut kb = crate::kb::test_support::load_stdlib(None);
        let snap = kb.snapshot_scoped();
        load_layer_src(&mut kb);

        let widget = kb
            .try_resolve_symbol("spgbp.layer_demo.Widget")
            .expect("layer sort resolves while live");
        let seven = kb.alloc(Term::Const(Literal::Int(7)));
        let escaped = kb.alloc(Term::Fn {
            functor: widget,
            pos_args: SmallVec::from_slice(&[seven]),
            named_args: SmallVec::new(),
        });
        let name_before = kb.local_name_of(widget).to_string();

        kb.restore_scoped(snap);

        assert_eq!(
            kb.local_name_of(widget),
            name_before,
            "a Symbol minted inside the layer must still NAME something after the discard"
        );
        assert!(
            matches!(kb.get_term(escaped), Term::Fn { functor, .. } if *functor == widget),
            "a TermId minted inside the layer must still resolve to its own term"
        );
    }
}

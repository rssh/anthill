//! The requires chain: `RequiresEntry`/`RequiresNode`, dictionary chains and layouts,
//! provision conditions, conversions, and obligation checking.

use super::*;

// ── Requires chain ─────────────────────────────────────────────

/// A direct requires entry: sort A requires spec B with the given SortView.
///
/// WI-662: `spec` is carrier-faithful — a ground spec rides as `Value::Term`, a
/// denoted-bearing binding (`requires Foo[E = Modify[c]]`) as a `Value::Node`
/// occurrence. The pre-WI-662 `TermId` field could not carry the latter, so the
/// producers (`direct_requires`, `op_requires_entries`) silently dropped
/// effect-bearing `requires` clauses; they now flow through and the readers
/// decode the spec via `TermView` (ground path unchanged, denoted path new).
#[derive(Clone, Debug)]
pub struct RequiresEntry {
    /// The base sort symbol of the required spec (e.g., Eq in `requires Eq[T=Int]`).
    pub required_sort: Symbol,
    /// The full SortView spec value (carries bindings like T=Int, combine=add).
    pub spec: Value,
    /// WI-1110 — where this slot's dictionary COMES FROM. See [`SupplySource`].
    pub supply: SupplySource,
}

/// WI-1110 — a chain entry's SUPPLY SOURCE: who fills the slot.
///
/// The two clauses that put a spec in a sort's chain answer different questions, and
/// before this they were spelled as one thing (`requires`) plus a separate, searchable
/// provider row (`provides`) that meant something a spec cannot mean.
///
///   `requires A[T]`  the `A` dictionary is PASSED IN — an inbound slot the caller fills.
///   `provides A[T]`  on a SPEC: the `A` dictionary is BUILT FROM SELF. "We know how to
///                    obtain an `A` from a `B`" — a CONVERSION, which is what `B <: A`
///                    means operationally.
///
/// A CARRIER's `provides` is a different clause with the same keyword and is NOT
/// represented here: `Int64 provides Ord[T = Int64]` is a fact about the world and
/// belongs in the searchable provider table. A SPEC's `provides` is a conversion and
/// belongs in the chain. Putting a conversion in the provider table is what made `Ord`
/// answer every `WeakOrd` goal (WI-1110's measurement) and is what forced `Ord` to
/// carry `requires WeakOrd` as well, closing a cycle over one edge written twice.
///
/// At DICTIONARY-CONSTRUCTION time the two are deliberately identical — both are slots,
/// both are filled by resolving the spec at the goal's bindings, and a self-supplied
/// slot is answered by the provider's own DERIVED row
/// ([`derive_forwarded_provisions`]). The distinction is read in exactly one place, and
/// it is a SEARCH question: [`collect_provides_candidates`] must not offer a conversion
/// as a provider. Recorded on the entry rather than recomputed there so the two readers
/// cannot drift, and so a diagnostic can say which clause put the slot there.
///
/// THAT IDENTITY WAS A CHOICE AND WI-1111 DECIDED IT: SEARCH STAYS. The alternative was
/// real and is written down here rather than lost — "built from self" literally says the
/// slot is a PROJECTION of the dictionary already held, not a goal (an `Ord[Int64]`
/// dictionary IS a `WeakOrd[Int64]` one plus a law), and filling it by SEARCH is why the
/// same edge is traversed both ways: the conversion says `PartialEq` comes from `Eq`, the
/// chain says `Eq` CONTAINS `PartialEq`. That round trip IS the `construction is cyclic`
/// the candidate exclusion breaks, and a projected slot would start no search, so the
/// cycle would not exist. What does NOT follow — and this is the measurement that decided
/// it — is that the exclusion would not be needed either.
///
///   * THE EXCLUSION ANSWERS A QUESTION NO SLOT-FILLING CHANGE CAN. A conversion is a row
///     in the provider relation whatever fills the slot, so at an ABSTRACT element it is
///     still offered and still the ONLY candidate: WI-1110 measured `WeakOrd[T = <rigid>]`
///     returning `[Ord]` alone with the skip removed, and `wi1110`'s
///     `a_weakord_dispatch_with_no_requires_is_refused` is the driver that fails without
///     it. Projection removes one traversal of the edge; it does not remove the row.
///     WI-1111 then measured that the exclusion had FOUR reachable holes — a renaming
///     forwarding, a permuting one, a derived spec-to-spec row, and an opless
///     multi-parameter floor — each of which loaded clean and trapped at eval. It needed
///     COMPLETING, which is the opposite of needing removing.
///   * THE EAGER ROWS HAVE A SECOND READER A LAZY EDGE CANNOT SERVE.
///     `build_sort_ops_table` inherits a forwarded spec's operations onto every carrier
///     that gained a row (kb/load.rs, at the `build_sort_ops_table (derived-provision
///     delta)` mark) — it is what makes `WeakOrd.compare` dispatch on a carrier that wrote
///     only `provides Ord`. Driven by
///     `q5_the_derived_row_is_what_makes_the_operation_dispatch`.
///   * AND THE SLOT IS FILLED BY THOSE SAME ROWS, so a projection would add a third path
///     without retiring either of the first two. Driven, with a REVERSED order so the
///     answer names which dictionary arrived, by
///     `q5_the_self_supplied_slot_carries_the_carriers_own_dictionary`.
///   * THE LAYOUT COUNT IS 1 AND THE VALUE FLOWS THROUGH IT
///     (`q5_the_conversion_slot_is_one_slot_and_the_value_flows_through_it`, cross-checked
///     against what `resolve` bundles). Making it 0 means teaching `DictLayout::slots_for`,
///     `synth_req_names` and eval's frame push to project — three sites, to remove a slot
///     that measurably works.
///
/// So `SupplySource` stays a LABEL read at the two places that must tell a conversion from
/// a membership claim, not a decision about how a slot is filled. Reopen it only with a
/// measurement that beats these four.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SupplySource {
    /// Written `requires` — the caller supplies the dictionary.
    Required,
    /// Written `provides` on a SPEC — the provider supplies it from itself.
    SelfSupplied,
    /// WI-20260921-EE0EP — SYNTHESIZED, not written: a named requirement slot the
    /// PARAMETER named here leaves unwritten (`s: MySet[T = String]` over
    /// `enum MySet requires O: WeakOrd[T]`). The dictionary is the ARGUMENT'S OWN —
    /// the caller holds the argument's type with the slot pinned, so this slot is
    /// filled by READING that type, never by re-resolving the spec. §3.4's "omitting
    /// a named slot means ANY provider" with the channel §3.9 leaves open.
    ///
    /// The `Symbol` is the PARAMETER, which is what makes the fill possible: at the
    /// call site it keys `param_arg_types`, and two parameters of one carrier stay
    /// apart (the coarse-gate defect [`build_op_scoped_dicts`] records for the
    /// projection channel, where `b` and `c` could not be told apart).
    FromParam {
        /// The parameter whose argument type carries the witness.
        param: Symbol,
        /// The slot's BINDER on the carrier (`O`), which is the key to read in that
        /// argument's type. Recorded rather than re-derived: the spec cannot name it —
        /// one carrier may declare two slots of one spec (058 §3.3's `OA`/`OB`).
        binder: Symbol,
    },
}

/// A kb-free identity for a `RequiresEntry.spec`, so `RequiresEntry` can key the
/// `resolve_cache` scope (mod.rs) without `Value` gaining a structural `Eq`/`Hash`
/// (WI-486 deliberately routes value equality through `views_structurally_equal`,
/// which needs a `kb`). A ground `Value::Term` keys by its hash-cons `TermId`
/// (exact, alloc-free). A denoted spec (`Value::Entity` / `Value::Node`) has no
/// hash-cons id and MUST NOT be keyed by `Debug`, for TWO independent reasons,
/// BOTH still live. (1) The derived `Debug` prints the `span`, so
/// structurally-identical specs at different spans would never collide. (2) It also
/// prints INTERIOR-MUTABLE state, so a live map key's hash would mutate in place —
/// an unsound `HashMap` key. `NodeOccurrence` and `NodeKind` both
/// `#[derive(Debug)]`, and `NodeKind::Expr` holds FOUR `RefCell` channels the typer
/// fills in AFTER an entry is already in `resolve_cache`: `classification`,
/// `op_dicts`, `inferred_type`, `lowered_receiver`.
///
/// A WI-815 edit narrowed this to "only the span half is still live", on the
/// grounds that the `Cell<(KbId, TermId)>` `term_cache` had been deleted. That was
/// WRONG and is corrected here rather than dropped: `term_cache` was never the only
/// interior-mutable thing `Debug` printed, and a maintainer trusting the narrowed
/// claim could reintroduce a `Debug`-derived key for these arms — the `Other(String)`
/// arm below already keys by `format!("{other:?}")`, so the pattern is one arm away.
///
/// Key it instead by ALLOCATION identity — the `Rc` data
/// pointer(s), stable under interior mutation. Same-`Rc` clones (the requires-chain
/// caches hand back clones of one allocation) collide correctly; two distinct
/// allocations key distinctly (a sound false MISS = a recompute, never a false
/// HIT). Total and reflexive. WI-662.
#[derive(PartialEq, Eq, Hash)]
enum SpecEqKey {
    Term(TermId),
    /// `Rc` data pointer(s): a `Value::Node` occurrence (second field 0), or a
    /// `Value::Entity`/`Tuple`'s `pos`+`named` slice pointers.
    Ptr(usize, usize),
    /// A non-spec carrier (never a real requires spec) — a defensive fallback.
    Other(String),
}

fn spec_eq_key(spec: &Value) -> SpecEqKey {
    match spec {
        Value::Term { id, .. } => SpecEqKey::Term(*id),
        Value::Node(occ) => SpecEqKey::Ptr(Rc::as_ptr(occ) as usize, 0),
        Value::Entity { pos, named, .. } | Value::Tuple { pos, named, .. } => {
            SpecEqKey::Ptr(pos.as_ptr() as usize, named.as_ptr() as usize)
        }
        other => SpecEqKey::Other(format!("{other:?}")),
    }
}

impl PartialEq for RequiresEntry {
    fn eq(&self, other: &Self) -> bool {
        self.required_sort == other.required_sort
            && spec_eq_key(&self.spec) == spec_eq_key(&other.spec)
    }
}

impl Eq for RequiresEntry {}

impl std::hash::Hash for RequiresEntry {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.required_sort.hash(state);
        spec_eq_key(&self.spec).hash(state);
    }
}

/// WI-230 — tree-shaped declaration of a sort's `requires` chain. Each
/// node holds one `RequiresEntry` plus a recursive `Vec` of sub-entries
/// (the required spec's *own* `requires`, transitively). Substitution
/// is composed top-down so each node's `entry.spec` carries the
/// *root-scoped* view of bindings — Eq in `Wi222Outer requires Ord
/// requires Eq` reads `T = Wi222Outer.T` directly, not `T = Ord.T`.
///
/// This mirrors the runtime arena's `RequirementSlot` tree shape (slot
/// = node, sub-handles = sub_requires) and the typer's
/// `ResolvedRequiresNode::Conditional { sub_resolutions }`. All three layers
/// now share one tree skeleton; consumers can walk them by the same
/// recursion.
#[derive(Clone, Debug)]
pub struct RequiresNode {
    pub entry: RequiresEntry,
    pub sub_requires: Vec<RequiresNode>,
}

impl RequiresNode {
    /// Walk the tree and accumulate every node's entry into a flat list
    /// (pre-order). Back-compat for callers that consumed the old
    /// `Vec<RequiresEntry>` shape; new code should walk the tree directly.
    pub fn flatten_into(&self, out: &mut Vec<RequiresEntry>) {
        out.push(self.entry.clone());
        for sub in &self.sub_requires {
            sub.flatten_into(out);
        }
    }
}

/// WI-230 flatten helper for a forest of top-level nodes (the shape
/// `requires_tree` returns).
pub fn flatten_requires_tree(nodes: &[RequiresNode]) -> Vec<RequiresEntry> {
    let mut out = Vec::new();
    for node in nodes {
        node.flatten_into(&mut out);
    }
    out
}

/// Collect the full transitive requires chain for a sort.
/// Returns all (required_sort_sym, spec_term) pairs reachable from `sort_sym`.
///
/// WI-230: now a thin wrapper over `requires_tree` + `flatten_requires_tree`.
/// Substituted bindings flow through (each entry's spec is root-scoped),
/// which differs from the pre-WI-230 behavior of returning each entry
/// in its *declaring* sort's view. Consumers that compared bindings via
/// `dispatch_values_match` continue to work — the equivalence is
/// preserved under symmetric matching with type-param wildcards.
///
/// Takes `&mut KnowledgeBase` because substitution composition may
/// allocate freshly-substituted `Term::Fn` nodes. Consumers that only
/// read `required_sort` (and never compare bindings) should use
/// [`transitive_required_sorts`] instead — it doesn't substitute and so
/// preserves the `&KnowledgeBase` signature.
pub fn requires_chain(kb: &mut KnowledgeBase, sort_sym: Symbol) -> Vec<RequiresEntry> {
    let tree = requires_tree(kb, sort_sym);
    flatten_requires_tree(&tree)
}

/// WI-239 — a sort's **direct** `requires` entries: the top-level
/// `requires_tree` nodes' entries, substitution-composed/root-scoped
/// (same per-entry form `requires_chain` produces, but without the
/// transitive descent and without the pre-order duplication of shared
/// subtrees).
///
/// This is the tree-native requirement ABI: under the names model a
/// body reads only its DIRECT requires by `__req_<spec>` name; a
/// transitive require lives inside a direct requirement's tree-shaped
/// dict value, reached at runtime via `requirement_at_sort`. The
/// duplication the flat chain suffers — `requires Eq, Ord` with
/// `Ord requires Eq` flattening to `[Eq, Ord, Eq]` — does not
/// arise here: the result is exactly `[Eq, Ord]`.
///
/// Consumers that must remain transitive (resolution-tree subgoals are
/// recursive per-level, obligation checks, the `sort_refines` reach
/// relation) use `requires_chain` / `transitive_required_sorts` instead.
pub fn direct_requires_chain(kb: &mut KnowledgeBase, sort_sym: Symbol) -> Vec<RequiresEntry> {
    (*direct_requires_chain_rc(kb, sort_sym)).clone()
}

/// WI-657(12): the flattened direct `requires` chain as a shared `Rc`, memoized on
/// the (previously dormant) `requires_chain_cache`. `set_enclosing_sort` runs once
/// per op-body in `check_operation_bodies` and stored the chain by VALUE, rebuilding
/// a fresh `Vec` + cloning every `RequiresEntry` off the already-cached
/// `requires_tree` each time; caching the flattened `Rc` makes the per-op snapshot an
/// `Rc` bump. Shares the `requires_tree` cache's lifetime exactly — both are cleared
/// together by `invalidate_requires_chain_cache` whenever `SortRequiresInfo` changes,
/// so the flattened chain can never outlive the tree it was flattened from.
/// WI-20260921-28TAT — does a `requires` clause naming `required` put a DICTIONARY SLOT
/// in the chain, or is it a REFINEMENT declaration?
///
/// ONE KEYWORD, TWO RELATIONS, and until this predicate they were conflated. Both are
/// written `requires X` on a sort and both ride the same `SortRequiresInfo` fact:
///
///   `sort Narrow requires Boom`   `Narrow <: Boom` — a REFINEMENT. It is read by
///                                 [`sort_refines`], through `transitive_required_sorts`,
///                                 and that is the whole of its meaning.
///   `sort C requires Eq[T]`       a SPEC DEMAND — an inbound dictionary slot the
///                                 caller fills, read by every dispatch site.
///
/// A SPEC IS A SORT WITH AT LEAST ONE TYPE PARAMETER. That is not a criterion invented
/// here: it is `enclosing_is_spec`'s (WI-840) and `spec_op_parent_sort`'s own reading,
/// and it is exactly the right question for THIS one, because a dictionary is selected
/// BY the carrier its parameters name. A sort with no type parameter has no carrier to
/// dispatch on, nothing can `provides` it, and no member could be reached through a slot
/// held for it — so a slot for it can never be filled by anything.
///
/// WHAT THE CONFLATION COST, measured. `sort Narrow requires Boom` put an unfillable
/// `Boom` slot in `Narrow`'s dictionary chain, so building ANY dictionary whose impl is
/// `Narrow` failed with `no impl provides test.reify.Boom` — advice the author cannot
/// act on, since `Boom` is a closed ADT and `provides Boom[…]` is not a thing that can
/// be written. It surfaced through `TypeValue[T = Narrow]` (WI-20260921-28TAT's reify
/// boundary) only because nothing had asked for a dictionary at a refinement sort
/// before; `Narrow provides Eq` would have failed identically. The cost was not confined
/// to the diagnostic: an unresolved op-scoped dep is a SILENTLY absent slot, so the
/// boundary simply stopped narrowing.
///
/// FILTERED HERE, on the DICTIONARY side alone. `transitive_required_sorts` — which
/// [`sort_refines`] and [`check_obligations`] read — is built from the tree by its own
/// path and is deliberately left whole, so `Narrow` still refines `Boom` and the
/// subsumption a boundary written at `Boom` performs on a `Narrow` payload is unchanged.
pub(crate) fn clause_is_dispatchable(kb: &KnowledgeBase, required: Symbol) -> bool {
    !kb.type_params_of_sort(required).is_empty()
}

pub fn direct_requires_chain_rc(
    kb: &mut KnowledgeBase,
    sort_sym: Symbol,
) -> Rc<Vec<RequiresEntry>> {
    if let Some(cached) = kb.requires_chain_cache.borrow().get(&sort_sym) {
        return cached.clone();
    }
    let tree = requires_tree(kb, sort_sym);
    let chain: Vec<RequiresEntry> = tree.iter().map(|n| n.entry.clone()).collect();
    let rc = Rc::new(chain);
    kb.requires_chain_cache
        .borrow_mut()
        .insert(sort_sym, rc.clone());
    rc
}

/// Proposal 066 §7 (WI-20260919-1Z3E7) — **THE** layout key of a carrier's dictionary
/// chain: which provision's conditions follow the sort-level `requires`.
///
/// `Some(P)` exactly when the carrier provides `P` through ONE written clause and that
/// clause has conditions; `None` otherwise — the sort-level chain alone. The key is
/// NORMALIZED here, once, so that every chain of a carrier with no conditional
/// provision is literally the sort-level chain (one `Rc`, one set of names), whatever
/// provision a caller asked about: nothing outside the conditional carriers can observe
/// that layouts became per provision.
///
/// TWO OR MORE CLAUSES OF ONE SPEC ARE ALTERNATIVES (WI-1033), and no body reads their
/// conditions — a `where` block is refused on such a spec (§7.5) — so they contribute
/// no slot. Whether one of them holds is decided at the dispatch
/// ([`alternative_condition_goals`]), not by a slot.
pub(crate) fn provision_layout_key(
    kb: &KnowledgeBase,
    sort: Symbol,
    provision: Option<Symbol>,
) -> Option<Symbol> {
    let p = provision?;
    if let Some(hit) = kb.provision_layout_key_cache.borrow().get(&(sort, p)) {
        return *hit;
    }
    let key = if kb.provides_clause_count(sort, p) > 1 {
        None
    } else {
        let p_canon = kb.canonical_sort_sym(p);
        provision_conditions(kb, sort)
            .iter()
            .any(|g| kb.canonical_sort_sym(g.provided) == p_canon && !g.conditions.is_empty())
            .then_some(p_canon)
    };
    kb.provision_layout_key_cache
        .borrow_mut()
        .insert((sort, p), key);
    key
}

/// Proposal 066 §7 — the entries of `sort`'s chain under layout key `key`
/// ([`provision_layout_key`], already normalized): the sort-level `requires`
/// (`direct_requires_chain`), then — for `Some(P)` — the conditions of `P`'s one clause,
/// deduplicated against what is already placed (a condition restating a sort-level
/// `requires` is that same slot). Memoized per `(sort, key)`; for `None` it is the
/// sort-level `Rc` itself.
///
/// This replaced WI-869's ONE chain per carrier — every provision's conditions in one
/// slot set, with a per-dispatch strictness mask leaving a sibling's slots
/// `Unavailable`. A layout per provision is what makes a `where` block the
/// dictionary-holder it reads as: its members' frame holds exactly their evidence, and
/// a dispatch through a provision builds exactly that frame.
pub(super) fn provider_dict_chain(
    kb: &mut KnowledgeBase,
    sort_sym: Symbol,
    key: Option<Symbol>,
) -> Rc<Vec<RequiresEntry>> {
    let base = direct_requires_chain_rc(kb, sort_sym);
    let Some(p) = key else {
        return base;
    };
    if let Some(cached) = kb.provider_dict_chain_cache.borrow().get(&(sort_sym, p)) {
        return cached.clone();
    }
    let mut entries: Vec<RequiresEntry> = (*base).clone();
    for prov in provision_conditions(kb, sort_sym) {
        if !same_sort_canonical(kb, prov.provided, p) {
            continue;
        }
        for spec in &prov.conditions {
            // Loud, not a skip: the loader refuses a condition whose spec has no
            // readable base (`load_provides_clause`), so reaching here is an internal
            // disagreement between the two decoders.
            let Some(required_sort) = spec_base_functor(kb, spec) else {
                debug_assert!(
                    false,
                    "WI-869: a `provides … :- …` condition of `{}` has no readable \
                     spec head, so it conditions nothing",
                    kb.qualified_name_of(sort_sym),
                );
                continue;
            };
            // Dedup STRUCTURALLY (`views_structurally_equal`, WI-486's single owner), not
            // through `RequiresEntry`'s own `PartialEq` — that one is the `resolve_cache`
            // key and prefers a false miss, and a false miss here is a DUPLICATED SLOT
            // the namer cannot split.
            if entries.iter().any(|e| {
                e.required_sort == required_sort
                    && crate::kb::term_view::views_structurally_equal(kb, &e.spec, spec)
            }) {
                continue;
            }
            entries.push(RequiresEntry {
                required_sort,
                spec: spec.clone(),
                // A per-provision condition is inbound, like every `:- goals` tail.
                supply: SupplySource::Required,
            });
        }
    }
    let rc = Rc::new(entries);
    kb.provider_dict_chain_cache
        .borrow_mut()
        .insert((sort_sym, p), rc.clone());
    rc
}

/// Proposal 066 §7 — the operation-scoped half of the diagnostic
/// [`TypeError::ProvisionConditionOutOfScope`]: the provisions of `op_sym`'s carrier
/// holding a `spec_sort` condition that `op_sym`'s own chain does not — the evidence
/// the body would have had, written in one of those provisions' `where` blocks. Empty
/// leaves the refusal as it was.
pub(crate) fn hidden_conditions_over(
    kb: &mut KnowledgeBase,
    op_sym: Symbol,
    spec_sort: Symbol,
) -> SmallVec<[Symbol; 2]> {
    let mut out: SmallVec<[Symbol; 2]> = SmallVec::new();
    let Some(sort) = impl_parent_of_op(kb, op_sym) else {
        return out;
    };
    let own = op_dict_entries(kb, op_sym);
    let spec_canon = kb.canonical_sort_sym(spec_sort);
    for prov in provision_conditions(kb, sort) {
        let over_spec = prov.conditions.iter().any(|c| {
            spec_base_functor(kb, c).is_some_and(|b| kb.canonical_sort_sym(b) == spec_canon)
        });
        let visible = own
            .entries()
            .iter()
            .any(|e| kb.canonical_sort_sym(e.required_sort) == spec_canon);
        if over_spec && !visible && !out.contains(&prov.provided) {
            out.push(prov.provided);
        }
    }
    out
}

/// Proposal 066 §7.5 — a `where` block belongs to a spec the carrier provides through
/// ONE written clause. Two clauses of one spec are two alternatives (WI-1033), and a
/// member is still named `Carrier.op`: a block on one of them would back that member
/// for its clause only (§7.3), leaving the other clause unbacked, and a block on each
/// would declare `Carrier.op` twice. Members per clause is blocks-as-instances work,
/// recorded as 066's direction. Counted from the loader's clause record
/// ([`KnowledgeBase::provides_clause_count`]), not from `SortProvidesInfo` rows: two
/// clauses of one spec write one row, and a DERIVED row is no clause at all.
pub(super) fn check_member_blocks_have_one_clause(kb: &KnowledgeBase, errors: &mut Vec<LoadError>) {
    let Some(entity) = kb.try_resolve_symbol("anthill.reflect.ProvisionMemberInfo") else {
        return;
    };
    let mut reported: Vec<(Symbol, Symbol)> = Vec::new();
    for rid in kb.rules_by_functor(entity) {
        if !kb.is_fact(rid) {
            continue;
        }
        let head = kb.rule_head_value(rid);
        let Some(op) = crate::kb::op_info::head_field_term(kb, head, "operation")
            .and_then(|t| crate::kb::load::sort_ref_functor(kb, t))
        else {
            continue;
        };
        let (Some(carrier), Some(spec)) = (impl_parent_of_op(kb, op), provision_member_of(kb, op))
        else {
            continue;
        };
        let (carrier, spec) = (kb.canonical_sort_sym(carrier), kb.canonical_sort_sym(spec));
        let clauses = kb.provides_clause_count(carrier, spec);
        if clauses > 1 && !reported.contains(&(carrier, spec)) {
            reported.push((carrier, spec));
            errors.push(LoadError::Other {
                message: format!(
                    "`{carrier}` provides `{spec}` in {clauses} clauses, and one of them has a \
                     `where` block: a block member backs only its own clause, so the other \
                     clauses would have no `{member}`. Alternative provisions of one spec \
                     cannot carry member blocks yet (proposal 066 §7.5)",
                    carrier = kb.qualified_name_of(carrier),
                    spec = kb.qualified_name_of(spec),
                    member = kb.qualified_name_of(op).rsplit('.').next().unwrap_or(""),
                ),
            });
        }
    }
}

/// Proposal 066 §7.3 — the provision `carrier.op_short` is a block member of, when that
/// is NOT `spec`: the carrier's operation of this name belongs to another provision and
/// cannot back `spec`'s. `None` when the carrier has no such operation, or it is written
/// outside every block, or in `spec`'s own block.
pub(super) fn foreign_block_member(
    kb: &KnowledgeBase,
    carrier_qn: &str,
    op_short: &str,
    spec: Symbol,
) -> Option<Symbol> {
    let op = kb.try_resolve_symbol(&format!("{carrier_qn}.{op_short}"))?;
    let owner = provision_member_of(kb, op)?;
    (kb.canonical_sort_sym(owner) != kb.canonical_sort_sym(spec)).then_some(owner)
}

/// Proposal 066 — the provision `op_sym` is a member of: the base sort of the spec
/// whose `where` block it is written in (`ProvisionMemberInfo`), or `None` for an
/// operation written anywhere else.
fn provision_member_of(kb: &KnowledgeBase, op_sym: Symbol) -> Option<Symbol> {
    if let Some(hit) = kb.provision_member_cache.borrow().get(&op_sym) {
        return *hit;
    }
    let found = provision_member_of_uncached(kb, op_sym);
    kb.provision_member_cache.borrow_mut().insert(op_sym, found);
    found
}

fn provision_member_of_uncached(kb: &KnowledgeBase, op_sym: Symbol) -> Option<Symbol> {
    let entity = kb.try_resolve_symbol("anthill.reflect.ProvisionMemberInfo")?;
    let op_canon = kb.canonical_sort_sym(op_sym);
    for rid in kb.rules_by_functor(entity) {
        if !kb.is_fact(rid) {
            continue;
        }
        let head = kb.rule_head_value(rid);
        let (Some(op), Some(provided)) = (
            crate::kb::op_info::head_field_term(kb, head, "operation"),
            crate::kb::op_info::head_field_term(kb, head, "provided"),
        ) else {
            continue;
        };
        let (Some(op), Some(provided)) = (
            crate::kb::load::sort_ref_functor(kb, op),
            crate::kb::load::sort_ref_functor(kb, provided),
        ) else {
            debug_assert!(
                false,
                "066: a `ProvisionMemberInfo` row with an unreadable field"
            );
            continue;
        };
        if kb.canonical_sort_sym(op) == op_canon {
            return Some(provided);
        }
    }
    None
}

/// WI-1033 — one carrier's conditional provisions, read from the
/// `ProvidesConditionInfo` FACTS the loader emits. Grouped per provision (keyed by the
/// provided spec's base sort) and in fact order, which is the same referent
/// [`direct_requires`] uses for the sort-level half — they are separate per-functor
/// scans, so they cannot interleave.
///
/// Grouped per CLAUSE — the `clause` field — and NOT per provided base. The first cut
/// merged by base and it was WRONG for the one reader that refuses: a provision's
/// conditions are a CONJUNCTION within a clause and a DISJUNCTION across clauses, so
/// `provides Lo[D] :- SA[P]` beside `provides Lo[D] :- SB[Q]` is two ways for `Lo[D]`
/// to hold, and merging them demanded both. MEASURED: adding the second clause — which
/// can only WIDEN where `Lo[D]` holds — turned a clean load into a
/// `ProvisionConditionsTooWeak` refusal.
///
/// Proposal 066 §7 reads these groups two ways: a spec provided through ONE clause
/// lays that clause's conditions out as slots ([`provider_dict_chain`]); a spec with
/// several clauses has them decided as alternatives at the dispatch
/// ([`alternative_condition_goals`]).
pub(crate) fn provision_conditions(
    kb: &KnowledgeBase,
    sort_sym: Symbol,
) -> Vec<ProvisionConditions> {
    let mut out: Vec<ProvisionConditions> = Vec::new();
    // WI-20260920-E3DC5: the canonical-`sort_ref` bucket when `provides_index` is built,
    // else every condition fact — which is why the `same_sort_canonical` re-filter below
    // stays. This predicate answers about ONE sort and is asked ~877 times per stdlib
    // load; without a bucket each of those walked the whole relation, so its cost was
    // `calls × relation` and grew with any pass that adds conditioned provisions.
    for rid in condition_rids_by_carrier(kb, sort_sym) {
        // [`decoded_condition_row`] — the shared decode, so this predicate and the bucket
        // it now reads through cannot answer about different sets of facts.
        let Some((owner, provided_base, condition)) = decoded_condition_row(kb, rid) else {
            continue;
        };
        // The per-fact re-filter the bucket's contract requires: `rids_or_scan`'s no-index
        // arm returns EVERY condition fact, so this is what scopes the answer to one sort
        // before the index exists.
        if !same_sort_canonical(kb, owner, sort_sym) {
            continue;
        }
        let head = kb.rule_head_value(rid);
        // The clause index is what separates two provisions of one spec at one
        // application; without it they merge and their conditions read as a conjunction.
        let clause = crate::kb::op_info::head_field_term(kb, head, "clause")
            .and_then(|t| match kb.get_term(t) {
                Term::Const(Literal::Int(n)) => Some(*n),
                _ => None,
            })
            .unwrap_or(-1);
        match out
            .iter_mut()
            .find(|g| g.clause == clause && same_sort_canonical(kb, g.provided, provided_base))
        {
            Some(g) => g.conditions.push(condition),
            None => out.push(ProvisionConditions {
                provided: provided_base,
                clause,
                conditions: vec![condition],
            }),
        }
    }
    out
}

/// WI-20260919-9KYPA — does `carrier` provide `spec` only UNDER CONDITIONS?
///
/// The question separates a partial LEAF (`Float`, a `Partial` composite — an
/// unconditional `NonEq`) from a carrier that is partial only at some arguments
/// (`NonEq[List] :- NonEq[T]`). Two readers need that separation and would be wrong
/// without it, each measured:
///
///  * [`check_eq_noneq_exclusive`] — a conditional `Eq` beside a conditional `NonEq` is
///    not a contradiction (they hold at different arguments), while an unconditional
///    claim on either side does contradict the other.
///  * `eq_derive::noneq_provider_sorts` — the `Partial` fixpoint's SEED. A conditional
///    `NonEq` is not a partial leaf, and seeding from one made every composite with a
///    `List` field `Partial` on the second load phase (the rows persist), which then
///    collided with those composites' own `provides Eq`.
///
/// COARSE, deliberately and identically for both: "has a clause with conditions", not
/// "has no clause without them". A carrier mixing an unconditional clause with a
/// conditional one for the SAME spec reads as conditional. Nothing writes that today,
/// and the two readers have to agree — a split where one calls such a carrier a leaf and
/// the other does not is exactly the disagreement `EqClassification`'s comment forbids.
pub(crate) fn provision_is_conditional(kb: &KnowledgeBase, carrier: Symbol, spec: Symbol) -> bool {
    let spec_canon = kb.canonical_sort_sym(spec);
    provision_conditions(kb, carrier)
        .iter()
        .any(|g| kb.canonical_sort_sym(g.provided) == spec_canon && !g.conditions.is_empty())
}

/// WI-1033 — one conditional provision's goals, decoded out of its
/// `ProvidesConditionInfo` facts. The in-memory shape [`provision_conditions`] hands
/// [`provider_dict_chain`]; the facts are the record.
pub(crate) struct ProvisionConditions {
    /// Base sort of the spec this provision provides — the key a chain is laid out by.
    pub(crate) provided: Symbol,
    /// Which `provides` clause of the carrier, in source order. Two clauses may provide
    /// one spec, and their condition lists are ALTERNATIVES.
    pub(crate) clause: i64,
    /// The condition views of THIS clause, in fact order. A conjunction.
    pub(crate) conditions: Vec<Value>,
}

/// WI-869 — does a body owned by `sort` READ requirement slots, i.e. must a call
/// into it thread a dictionary? The gate every "does this callee need a dict" test
/// asks, in ONE place because there are three of them and they must agree with what
/// [`synth_req_names`] names.
///
/// Was spelled `!requires_chain(s).is_empty()` — the TRANSITIVE chain, whose
/// emptiness is the direct chain's (transitive ⊇ direct, and it is built by
/// descending from direct), so the swap changes nothing for a sort with no
/// conditional provision. It changes everything for one that has ONLY conditional
/// provisions: `Pair` declares no sort-level `requires` at all, so the old test said
/// "needs no dictionary" and its bodies got an EMPTY frame while reading the slots
/// its provisions' `:- goals` put there.
///
/// Proposal 066 §7: asked of the OPERATION, because the owner half of its frame is its
/// sort's chain under the provision it is a member of — a `Pair.fst` outside every
/// block reads nothing, `Pair.eq` in the `PartialEq` block reads two slots.
pub(crate) fn op_reads_requirement_slots(kb: &mut KnowledgeBase, op: Symbol) -> bool {
    !op_owner_dict_entries(kb, op).is_empty()
}

/// WI-1033 — a chain a dictionary is LAID OUT by, carrying the sort whose slot NAMES
/// it goes with. THE type that makes the layout invariant enforceable rather than
/// merely written down.
///
/// The invariant is "a producer that zips entries against `__req_*` names must take
/// both from ONE chain", and WI-869 broke it four times by repointing the namer while
/// four producers kept reading `direct_requires_chain`. Three were invisible to a green
/// suite. A newtype over the entries ALONE would not have caught them — no site *passes*
/// a chain to the namer, each one *calls* it with a `Symbol` and the namer re-derives —
/// so the fix is that the chain OWNS its namer: [`Self::names`] answers for the same
/// `owner` [`Self::entries`] was built from, and a caller cannot spell one without the
/// other.
///
/// EXACTLY WHAT THAT BUYS, stated precisely because a looser version of this comment
/// said "come from the same value" and "`provider_dict_entries` is the only way to make
/// one", and both were false. `names()` RE-DERIVES from `owner` through the memoized
/// `provider_dict_chain`; it agrees with `entries` because both memos are cleared
/// together by `invalidate_requires_chain_cache`, which has no production caller — a
/// `DictChain` snapshot held across a pass (`req_insertion::chain_for`,
/// `TypingEnv.enclosing`) is therefore stable, and would need re-examining if
/// invalidation ever ran mid-pass. And `unnamed`/`empty` are constructors too; what no
/// constructor offers is a chain whose entries and names come from DIFFERENT sorts.
///
/// `owner: None` is the no-enclosing-sort case: names empty, so every `name_at` is
/// `None`.
///
/// WI-822 LEG 1 — A CHAIN MAY ALSO BE KEYED BY AN OPERATION. An op-scoped `requires`
/// (WI-448/WI-562, written on the operation rather than its sort) contributes frame
/// slots too, and they are that OPERATION's, not its sort's: two members of one sort
/// have different op chains, so a per-sort layout cannot hold them. The layout is
/// therefore `owner`'s chain FOLLOWED BY `op`'s own — the sort half keeps its indices
/// and its names, which is what lets every sort-keyed reader stay correct while the
/// op half is appended (see [`op_dict_entries`]).
#[derive(Clone)]
pub struct DictChain {
    pub(super) owner: Option<Symbol>,
    /// WI-822 LEG 1 — the OPERATION whose own op-scoped chain occupies the entries
    /// after the first [`Self::sort_len`]. `None` for a plain sort chain, which is
    /// every chain of an operation that writes no `requires` of its own.
    pub(super) op: Option<Symbol>,
    /// How many leading entries belong to `owner`. Equals `entries.len()` whenever
    /// `op` is `None`, so the split is structural rather than a convention two
    /// readers must keep.
    pub(super) sort_len: usize,
    pub(super) entries: Rc<Vec<RequiresEntry>>,
    /// Proposal 066 §7 — the provision whose conditions follow `owner`'s sort-level
    /// `requires` ([`provision_layout_key`], normalized: `None` is the sort-level chain,
    /// which is every chain of a carrier with no conditional provision). Part of the
    /// OWNER, not an annotation: [`Self::names`] answers for `(owner, provision)`.
    pub(super) provision: Option<Symbol>,
}

impl DictChain {
    /// The chain of a call with no enclosing sort.
    pub fn empty() -> Self {
        DictChain::unnamed(Vec::new())
    }

    /// A chain whose slots have NO NAMES — a caller with no enclosing sort, and the
    /// synthetic callers the projection tests build.
    ///
    /// Every [`Self::name_at`] answers `None`, so a projection that needs a name falls
    /// through instead of indexing a naming that belongs to a different list: through
    /// this constructor a wrong chain yields no dictionary rather than a mis-indexed
    /// one. That claim was written before it was true — the `FromScope` path named its
    /// slot from a separately-passed `caller_sort` and would happily have indexed the
    /// other list; `emit_tree_as_projection` takes the chain now, which is what closed
    /// the last of the three naming paths.
    pub fn unnamed(entries: Vec<RequiresEntry>) -> Self {
        let sort_len = entries.len();
        DictChain {
            owner: None,
            op: None,
            sort_len,
            entries: Rc::new(entries),
            provision: None,
        }
    }

    pub fn entries(&self) -> &[RequiresEntry] {
        &self.entries
    }

    /// Proposal 066 §7 — the provision layout key of the owner half (see the field).
    pub fn provision(&self) -> Option<Symbol> {
        self.provision
    }

    /// The sort whose chain the prefix is — `None` for an unnamed chain.
    pub fn owner(&self) -> Option<Symbol> {
        self.owner
    }

    /// WI-822 LEG 1 — how many leading entries are the OWNER SORT's. Slots at or
    /// past it are the operation's own (see the type doc). Every sort-keyed
    /// producer — a dictionary's [`DictLayout`], `expand_dispatching_dict`'s
    /// `slots_for` slice — fills exactly this prefix.
    pub fn sort_len(&self) -> usize {
        self.sort_len
    }

    /// The op-scoped tail: the entries this chain's OPERATION contributed, or empty
    /// for a plain sort chain.
    pub fn op_entries(&self) -> &[RequiresEntry] {
        &self.entries[self.sort_len..]
    }

    /// The shared `Rc` — for a consumer that stores the chain (a per-op-body snapshot)
    /// rather than reading it once.
    pub fn entries_rc(&self) -> Rc<Vec<RequiresEntry>> {
        Rc::clone(&self.entries)
    }

    /// The `__req_<spec>` frame-slot names for THIS chain, index for index.
    ///
    /// WI-822 LEG 1: the owner sort's names then the operation's own, which is the
    /// order [`Self::entries`] is in. The two halves are named by two functions on
    /// purpose — `synth_req_names_of` must keep answering the SAME list for a sort
    /// whether or not some member of it also writes `requires`, since every
    /// sort-keyed producer (a dictionary's layout, `expand_dispatching_dict`) names
    /// its slots from it. A collision between the halves is therefore resolved on
    /// the OP side (see [`synth_op_req_names_of`]).
    pub fn names(&self, kb: &mut KnowledgeBase) -> Rc<Vec<Symbol>> {
        match (self.owner, self.op) {
            (Some(o), None) => synth_req_names_of(kb, o, self.provision),
            (owner, Some(op)) => {
                // Memoized: this is a per-dispatch read (the op-scoped frame push, the
                // caller-slot strip, the deferred-slot lookup), and concatenating two
                // memoized halves on every one of them is the whole cost.
                if let Some(cached) = kb.op_frame_names_cache.borrow().get(&op) {
                    return cached.clone();
                }
                let mut out: Vec<Symbol> = match owner {
                    Some(o) => (*synth_req_names_of(kb, o, self.provision)).clone(),
                    None => Vec::new(),
                };
                out.extend_from_slice(&synth_op_req_names_of(kb, op));
                let rc = Rc::new(out);
                kb.op_frame_names_cache.borrow_mut().insert(op, rc.clone());
                rc
            }
            (None, None) => Rc::new(Vec::new()),
        }
    }

    /// Slot `idx`'s name; `None` iff out of range.
    pub fn name_at(&self, kb: &mut KnowledgeBase, idx: usize) -> Option<Symbol> {
        self.names(kb).get(idx).copied()
    }
}

impl std::ops::Deref for DictChain {
    type Target = [RequiresEntry];
    fn deref(&self) -> &[RequiresEntry] {
        &self.entries
    }
}

/// The dictionary chain of `sort_sym` under `provision` — the ONLY constructor of a
/// non-empty [`DictChain`], and the drop-in for the `direct_requires_chain_rc` reads
/// that are dictionary LAYOUT rather than a sort's declared contract.
///
/// Proposal 066 §7: `provision` is the provision the chain is laid out FOR — the
/// provided spec of a dispatch, or the provision whose `where` block an operation is
/// written in ([`op_owner_provision`]); `None` is the sort-level chain, the frame of an
/// operation outside every block. Normalized through [`provision_layout_key`], so a
/// carrier with no conditional provision answers the sort-level `Rc` for any of them.
pub fn provider_dict_entries(
    kb: &mut KnowledgeBase,
    sort_sym: Symbol,
    provision: Option<Symbol>,
) -> DictChain {
    let key = provision_layout_key(kb, sort_sym, provision);
    let entries = provider_dict_chain(kb, sort_sym, key);
    let sort_len = entries.len();
    DictChain {
        owner: Some(sort_sym),
        op: None,
        sort_len,
        entries,
        provision: key,
    }
}

/// Proposal 066 §7 — the provision whose `where` block `op_sym` is written in, as the
/// `provision` argument of [`provider_dict_entries`]: the owner half of the
/// operation's frame. `None` for an operation outside every block.
pub fn op_owner_provision(kb: &KnowledgeBase, op_sym: Symbol) -> Option<Symbol> {
    provision_member_of(kb, op_sym)
}

/// Proposal 066 §7.4 — the normalized layout key of `op_sym`'s owner half.
pub(super) fn callee_frame_key(kb: &mut KnowledgeBase, op_sym: Symbol) -> Option<Symbol> {
    op_owner_dict_entries(kb, op_sym).provision()
}

/// Proposal 066 §7.4 — may a callee OF THE CALLER'S OWN SORT, laid out under
/// `callee_key`, read the caller's frame as its own (WI-418's same-sort inherit)? Yes
/// when its chain is the sort-level one — the prefix every chain of the sort shares,
/// named alike in each — or the caller's own. Otherwise the callee's provision holds
/// conditions the caller's frame does not, and it needs a dictionary of its own.
pub(super) fn frame_serves_callee(caller: &DictChain, callee_key: Option<Symbol>) -> bool {
    callee_key.is_none() || callee_key == caller.provision()
}

/// Proposal 066 §7 — the OWNER half of `op_sym`'s frame: its sort's chain under the
/// provision it is a member of. Empty for a free operation.
pub fn op_owner_dict_entries(kb: &mut KnowledgeBase, op_sym: Symbol) -> DictChain {
    match impl_parent_of_op(kb, op_sym) {
        Some(s) => {
            let p = op_owner_provision(kb, op_sym);
            provider_dict_entries(kb, s, p)
        }
        None => DictChain::empty(),
    }
}

/// WI-822 LEG 1 — **THE** frame layout of an OPERATION: its parent sort's dictionary
/// chain followed by the operation's OWN op-scoped `requires` (WI-448/WI-562).
///
/// An op-scoped `requires` had no frame slot at all before this: [`synth_req_names`]
/// is keyed by the parent SORT, so `List.member requires Eq[T]` named nothing and the
/// requirement was served by VALUE-DIRECTED dispatch instead — correctly, wherever a
/// receiver value can direct it (WI-817's relay chain computes its 551 with no
/// dictionary anywhere, and still does). It cannot be served where NO value can: a
/// spec op with no receiver argument (`zero() -> T`) whose two providers therefore
/// tie, which was refused AT LOAD while its sort-level twin loaded and was right.
/// That asymmetry is what this chain closes.
///
/// CONTAINMENT, and it is the property everything else rests on: for an operation
/// that writes no `requires` of its own this returns [`provider_dict_entries`]'
/// value VERBATIM — the same `Rc`, the same `owner`, `op: None`, so `names()` is the
/// same memoized list. Only an op that actually declares `requires` gains slots, and
/// only after its sort's, so no sort-keyed index or name moves.
pub fn op_dict_entries(kb: &mut KnowledgeBase, op_sym: Symbol) -> DictChain {
    // `impl_parent_of_op`, NOT the Sort-kind-filtered `impl_parent_sort_of_op`, because
    // this must name the SAME owner every other producer of this frame names:
    // `TypingEnv::set_enclosing_sort` (through the loader's `parent_sym`),
    // `seed_entry_requirements`, `expand_dispatching_dict` and `start_apply_same_sort`'s
    // inherit test all read the unfiltered parent. A namespace-level `requires` is a
    // real chain — `load_requires_decl` asserts `SortRequiresInfo` with the NAMESPACE as
    // its `sort_ref` — so the kind filter would drop slots those producers do fill, and
    // would then not count their bases when disambiguating an op slot's name.
    let sort = impl_parent_of_op(kb, op_sym);
    let base = match sort {
        // Proposal 066 §7: the owner half is the chain of the provision whose block the
        // operation is written in — the sort-level chain outside every block.
        Some(s) => {
            let p = op_owner_provision(kb, op_sym);
            provider_dict_entries(kb, s, p)
        }
        // A free operation with no parent segment at all: no sort half, but it may
        // still write its own `requires`, and those slots are as real as any.
        None => DictChain::empty(),
    };
    let op_entries = op_requires_chain_rc(kb, op_sym);
    if op_entries.is_empty() {
        return base;
    }
    let sort_len = base.entries.len();
    // The cache read is its OWN statement: a `match` over `borrow()` holds the guard
    // across both arms, and the miss arm's `borrow_mut()` then panics `RefCell already
    // borrowed` — which is exactly what it did, on 3681 tests.
    let cached = kb.op_dict_chain_cache.borrow().get(&op_sym).cloned();
    let entries = match cached {
        Some(hit) => hit,
        None => {
            let mut v: Vec<RequiresEntry> = (*base.entries).clone();
            v.extend(op_entries.iter().cloned());
            let rc = Rc::new(v);
            kb.op_dict_chain_cache
                .borrow_mut()
                .insert(op_sym, rc.clone());
            rc
        }
    };
    DictChain {
        owner: base.owner,
        op: Some(op_sym),
        sort_len,
        entries,
        provision: base.provision,
    }
}

/// WI-822 LEG 1 — re-spell an OP-SCOPED `requires` entry in the SORT-level shape, so
/// the composed chain has ONE entry shape and every chain predicate reads it.
///
/// [`RequiresEntry::spec`] has two shapes, and this is the fork
/// [`goal_from_op_requires_entry`]'s doc documented without owning: a SORT-level
/// requirement's spec is `SortView(Base, T = …)`, while `push_op_requires_clause_term`
/// stores an op-scoped clause as the BARE APPLICATION the author wrote (`Desc[MT]`,
/// `Monoid[T = HT]`), whose head IS the spec base. `unwrap_spec_view` answers
/// `(functor, no bindings)` for a bare one — and "no bindings" is a WILDCARD to every
/// reader that consumes it, so an unnormalized op entry would cover ANY dep of its
/// spec in `entries_cover`, resolve to a binding-free goal in Strategy 3, and
/// substitute nothing under `substitute_spec_via_subst`. MEASURED before this: the
/// three op-scoped WI-817 witnesses each built a `var_ref` forward against a caller
/// slot that no call site had filled, and died `var_ref(__req_desc) unbound`.
///
/// NORMALIZED HERE, at the chain composition, and NOT at the producer. The producer
/// fix is the wider one that doc names, and it would move every OTHER reader of
/// `op_requires_entries` at the same time — `op_requires_covers`' carrier map,
/// `goal_from_op_requires_entry`, `callee_requirement_slots`,
/// `requirement_ranges_over_owner_tparams` — each of which decodes the bare shape on
/// purpose today. The chain is the one place the two shapes must be interchangeable,
/// because it is the one place they are indexed and named together.
///
/// Positionals fill the parameters no named binding took, in declaration order —
/// the same rule [`goal_from_op_requires_entry`] applies, and the stdlib's own
/// spelling (`requires Eq[T]`) is positional. A positional this cannot read (a
/// denoted `Value::Node` carrier, WI-662) leaves the entry AS WRITTEN: the slot
/// still exists and is still named, so nothing desynchronizes, but it carries the
/// bare shape and reads as binding-free — loud in debug, since a clause the loader
/// accepted should decode here.
fn normalize_op_requires_entry(kb: &mut KnowledgeBase, entry: &RequiresEntry) -> RequiresEntry {
    let Some(sort_view) = kb.try_resolve_symbol("anthill.reflect.SortView") else {
        // No `anthill.reflect` in this KB — nothing reads a `SortView` either.
        return entry.clone();
    };
    // Already sort-shaped: nothing to do. `unwrap_spec_view_value` cannot answer this —
    // it reports `(functor, no bindings)` for a BARE application too, which is the very
    // shape being normalized — so the test is on the HEAD FUNCTOR being `SortView`.
    // Total and cheap, so a future producer that emits the normalized shape (the wider
    // fix `goal_from_op_requires_entry`'s doc names) passes straight through here.
    if matches!(
        entry.spec.head(kb),
        ViewHead::Functor { functor: Some(f), .. } if is_sort_view_functor(kb, f)
    ) {
        return entry.clone();
    }
    let spec_qn = kb.qualified_name_of(entry.required_sort).to_string();
    let mut bindings: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
    for key in entry.spec.named_keys(kb) {
        if !is_type_param_binding(kb, key, &spec_qn) {
            continue;
        }
        if let Some(v) = entry.spec.named_arg(kb, key).and_then(|it| it.as_term_id()) {
            bindings.push((key, v));
        }
    }
    let pos_arity = match entry.spec.head(kb) {
        ViewHead::Functor { pos_arity, .. } => pos_arity,
        _ => 0,
    };
    if pos_arity > 0 {
        let declared = kb.type_params_of_sort(entry.required_sort);
        let slots = KnowledgeBase::positional_param_slots(
            &declared,
            |d| bindings.iter().any(|(k, _)| kb.local_name_of(*k) == d),
            pos_arity,
        );
        let mut vals: Vec<TermId> = Vec::with_capacity(pos_arity);
        for i in 0..pos_arity {
            match entry.spec.pos_arg(kb, i).and_then(|it| it.as_term_id()) {
                Some(v) => vals.push(v),
                // See the doc: leave it as written rather than pair positionals with
                // the WRONG parameter names, which would be a fabricated binding.
                None => return entry.clone(),
            }
        }
        // MORE positionals than the spec has free parameters: not a spec application
        // at all. Reached from real source, so NOT a `debug_assert` — MEASURED on
        // `wi840_named_requires_slot_test`'s `operation div[neq](…) requires neq(b, 0)`,
        // where a type parameter named `neq` CAPTURES the head of the operation's own
        // value precondition, so [`is_value_precondition_clause`] sees a `Sort`-kinded
        // functor and does not filter the clause. That program is refused at load by
        // WI-840's own collision check; this leaves its entry as written in the
        // meantime rather than aborting the typer on the way to that refusal.
        let Some(slots) = slots.into_iter().collect::<Option<Vec<usize>>>() else {
            return entry.clone();
        };
        for (val, i) in vals.into_iter().zip(slots) {
            let name = &declared[i];
            // The spec's OWN parameter symbol, which is what a `SortView`'s named args
            // are keyed by and what `substitute_impl_params_alloc` matches on. A BARE
            // `intern` is not a substitute for it — an interned name is not the
            // registered qualified one, so such a key matches nothing in
            // `is_type_param_binding` and the binding would be silently inert. If the
            // spec's parameter cannot be named, leave the entry as written, which is
            // what every other undecodable case here does.
            let Some(key) = kb.try_resolve_symbol(&format!("{spec_qn}.{name}")) else {
                return entry.clone();
            };
            bindings.push((key, val));
        }
    }
    let base_ref = kb.alloc(Term::Ref(entry.required_sort));
    let spec = kb.alloc(Term::Fn {
        functor: sort_view,
        pos_args: SmallVec::from_elem(base_ref, 1),
        named_args: bindings,
    });
    RequiresEntry {
        required_sort: entry.required_sort,
        spec: Value::term(spec),
        supply: entry.supply,
    }
}

/// WI-822 LEG 1 — `op_sym`'s OWN op-scoped `requires` entries **that are dictionary
/// slots**, memoized. The decode itself is [`op_requires_entries`]; this is the read
/// every per-call-site and per-frame-push consumer takes, where re-walking
/// `OperationInfo` (which clones params, return type, effects, …) to answer
/// `is_empty()` for the overwhelmingly common requires-free operation is the whole
/// cost.
///
/// VALUE PRECONDITIONS ARE NOT SLOTS, and the filter is not an optimization. One
/// `requires` keyword writes two different things (§5.4 / WI-539): a spec
/// requirement (`Zeroable[HT]`, whose head resolves to a Sort) and a goal over the
/// operation's own PARAMETERS (`neq(b, 0)`, `gt(a, b)`, `known(x)`). Only the first
/// is evidence a caller can supply; the second is proved against Γ at the call site
/// and has no dictionary at all. MEASURED without the filter: `PartialOrd.gt`'s
/// `requires gt(a, b)` was read as a spec application binding TWO positionals over
/// `gt`'s ZERO type parameters, and 20 tests died on the resulting slot. The same
/// filter, the same predicate, as [`callee_requirement_slots`]' — the other list of
/// "what can a caller name".
/// WI-20260921-EE0EP — the chain entries a PARAMETER's carrier leaves UNWRITTEN, so the
/// caller can hand over the ARGUMENT's own dictionary instead of the call being refused.
///
/// THE DEFECT THIS CLOSES. `operation has(s: MySet[T = String], x: String) = MySet.contains(s, x)`
/// over `enum MySet requires O: WeakOrd[T]` was a LOAD ERROR: the body's `contains` needs
/// `MySet`'s `O` dictionary, the signature declares no slot to carry one, and WI-1094
/// refused rather than construct a rival for a value that already chose
/// (`ErasedRequirementSlot`). §3.9 left two repairs — forward the value's own dictionary,
/// or refuse — and WI-1094 shipped the refusal because forwarding had no channel. This is
/// the channel, and it is the ORDINARY op-scoped one: a synthesized entry per unwritten
/// slot, in the op half, filled at the call from the argument's type.
///
/// WHY THE ARGUMENT'S TYPE IS ENOUGH, which is the measurement that makes this cheap
/// rather than a new representation. WI-1059's `rigidify_unwritten_sort_params` mints the
/// slot for the BODY as the projection `s.O` and leaves the call-side `OperationInfo`
/// slot FLEXIBLE — so at every call the argument's own type binds it, with no bracket
/// written. MEASURED (`probe_no_bracket_written_slot`): the same program with the slot
/// DECLARED runs and the two rival orderings disagree, at no call-site bracket at all.
/// So nothing has to be recovered from the VALUE, and nothing added to the dictionary's
/// shape; the caller already holds what the callee is missing.
///
/// [`SupplySource::FromParam`] keys the entry to the PARAMETER rather than to the spec,
/// and that is load-bearing in two directions: the fill reads that parameter's argument
/// type, and two parameters over one carrier at different providers stay apart.
///
/// WHAT IS DELIBERATELY NOT HERE. A slot written CONCRETE, or written as one of this
/// signature's own declared parameters (058 §7.1's form, which already forwards), is not
/// an unwritten slot and gets no entry. An EXISTENTIAL RETURN is not reached at all: it is
/// a return, not a parameter, so there is no argument whose type could name a provider —
/// that one stays refused (WI-1063), which is WI-EE0EP decision (c).
pub(super) fn param_derived_requires(kb: &mut KnowledgeBase, op_sym: Symbol) -> Vec<RequiresEntry> {
    let Some(rec) = crate::kb::op_info::lookup_operation_info(kb, op_sym) else {
        return Vec::new();
    };
    let params: Vec<(Symbol, Value)> = rec.params.clone();
    let mut out: Vec<RequiresEntry> = Vec::new();
    for (pname, pty) in params {
        // ONLY a type APPLICATION carries bindings to read; a bare `Ref(S)` leaves every
        // slot unwritten and is handled by the same walk, through `Parameterized`'s empty
        // binding list only when the loader materialized one. A bare reference that never
        // materializes reaches `SortRef` and is skipped — its slots are unwritten too, but
        // nothing here can say at WHAT bindings the spec should be demanded, and guessing
        // is the construction this ticket exists to avoid.
        let (carrier, written) = match extract_type(kb, &pty) {
            TypeExtractor::Parameterized { base, bindings } => (base, bindings),
            _ => continue,
        };
        let slots = kb.named_requirement_slots(carrier).to_vec();
        if slots.is_empty() {
            continue;
        }
        // The carrier's own chain, whose INDEX is the slot's declaration position
        // (`dict_chain_index_of_named_slot` argues that identity; this reads the same one).
        let chain = provider_dict_entries(kb, carrier, None);
        for slot in slots {
            // WRITTEN? Two spellings count as written and neither may take an entry: a
            // concrete or author-written binding, and 058 §7.1's own-parameter form. What
            // is NOT written is an absent binding, or the WI-1059 PROJECTION the rigidify
            // pass fills in — `s.O` is the slot's NAME, not a supply, which is exactly the
            // asymmetry this ticket was filed on.
            let unwritten = match written.iter().find(|(k, _)| *k == slot.binder) {
                None => true,
                Some((_, v)) => is_self_projection_of(kb, v, pname, slot.binder),
            };
            if !unwritten {
                continue;
            }
            // THE VERIFIED INDEX, through the typer's one owner of it. A raw
            // `entries().get(slot.slot)` was the first cut and is exactly what
            // [`dict_chain_index`]'s own doc refuses: the declaration order and the
            // dictionary order coincide BY CONSTRUCTION, and where they drift, pinning the
            // wrong slot "resolves a real goal with a real provider and computes the wrong
            // answer". Here the damage would be a synthesized entry demanding some OTHER
            // spec, under which `param_slot_witness` then pins the argument's witness — a
            // wrong dictionary built out of a right reading. `None` skips (no channel, so
            // the call keeps WI-1094's refusal) rather than raising: this runs while the
            // CHAIN is being built, with no call site to report at, which is precisely the
            // caller `dict_chain_index` exists for.
            let Some(entry) =
                dict_chain_index(kb, carrier, &slot).and_then(|i| chain.entries().get(i).cloned())
            else {
                continue;
            };
            // The spec AT THE PARAMETER'S OWN BINDINGS: `WeakOrd[T = MySet.T]` under
            // `s: MySet[T = String]` is `WeakOrd[T = String]`. Same composition
            // [`build_child_subst_map`] does one level up, keyed off the CARRIER's
            // qualified parameter names.
            // A BINDING THAT DOES NOT LOWER DROPS THE WHOLE SLOT, not just that binding.
            // `continue`ing the inner loop was the first cut and review MEASURED it wrong:
            // control still reached `substitute_in_spec` and `out.push`, so the entry was
            // synthesized with a PARTIALLY substituted spec still naming the carrier's own
            // parameter (`WeakOrd[T = MySet.T]` where the call means `WeakOrd[T = String]`).
            // That entry then feeds the collision screen and `param_slot_witness`'s pin
            // under a spec the call never meant — a wrong dictionary built out of a right
            // reading, which is the hazard the `dict_chain_index` paragraph above refuses.
            let mut map: HashMap<Symbol, TermId> = HashMap::new();
            let carrier_qn = kb.qualified_name_of(carrier).to_string();
            let mut lowered_all = true;
            for (short_sym, value) in &written {
                let short = kb.local_name_of(*short_sym).to_string();
                let Some(q) = kb.try_resolve_symbol(&format!("{carrier_qn}.{short}")) else {
                    lowered_all = false;
                    break;
                };
                // [`crate::kb::node_occurrence::value_to_term`], the faithful boundary — NOT
                // `expect_term`, which panics on a denoted binding (`MySet[T = Modify[c]]`),
                // and not `alloc_from_value`, which rejects every `Node`. Its `Err` residue
                // is the opaque runtime handles, which cannot appear in a declared parameter
                // type; an entry whose binding does not lower is dropped, and the slot then
                // keeps today's refusal rather than being supplied at a guessed binding.
                let Ok(t) = crate::kb::node_occurrence::value_to_term(kb, value) else {
                    lowered_all = false;
                    break;
                };
                map.insert(q, t);
            }
            if !lowered_all {
                continue;
            }
            let spec = substitute_in_spec(kb, &entry.spec, &map);
            out.push(RequiresEntry {
                required_sort: entry.required_sort,
                spec,
                supply: SupplySource::FromParam {
                    param: pname,
                    binder: slot.binder,
                },
            });
        }
    }
    out
}

pub(crate) fn op_requires_chain_rc(
    kb: &mut KnowledgeBase,
    op_sym: Symbol,
) -> Rc<Vec<RequiresEntry>> {
    if let Some(cached) = kb.op_requires_chain_cache.borrow().get(&op_sym) {
        return cached.clone();
    }
    let raw: Vec<RequiresEntry> = op_requires_entries(kb, op_sym)
        .into_iter()
        .filter(|e| !is_value_precondition_clause(kb, &e.spec))
        .collect();
    // NORMALIZED HERE, once per operation, so the re-spelling is not redone at every
    // frame push and every call-site build: [`normalize_op_requires_entry`] allocates
    // a `SortView` term per entry, and this read is on the per-dispatch path.
    let mut entries: Vec<RequiresEntry> = raw
        .iter()
        .map(|e| normalize_op_requires_entry(kb, e))
        .collect();
    // WI-20260921-EE0EP — the synthesized slots, AFTER the written ones and never among
    // them: the order IS the frame's slot order, so an entry the author wrote keeps the
    // index it had before this ticket and a synthesized one can only be appended.
    //
    // AND A CHAIN THAT ALREADY HOLDS AUTHOR-WRITTEN SLOTS IS SYNTHESIZED INTO, which it
    // was not when this ticket shipped. The early return here declined that case because
    // `whole_frame` was conditional and could not be admitted for a mixed chain;
    // WI-20260921-3G1YT made it unconditional and the reason lapsed. Driven by
    // `wi_ee0ep_param_dictionary_test::a_mixed_chain_takes_the_channel_too`.
    //
    // SCREENED AGAINST WHAT ALREADY COVERS, and this screen is the difference between a
    // fix and a silent wrong answer. The body reads a GOAL (`WeakOrd[T = String]`), not a
    // parameter: where a second entry covers the same goal, the forward takes the first
    // and the call runs on a dictionary that is not this parameter's. MEASURED both ways —
    // an author's own anonymous `requires WeakOrd[T = String]` beside `s: MySet[T = String]`
    // read `false` where `s`'s `ByLength` says `true`, and two parameters of one carrier
    // are the same collision between two synthesized slots. It is the coarse-gate defect
    // [`build_op_scoped_dicts`] records for the projection channel (`b.E` answered out of
    // `c`'s slot), reached from the other side.
    //
    // REFUSED RATHER THAN RANKED. Ranking would need the READ to say which parameter it
    // means, which is decision (d) — the `s.O` spelling — and is a separate ticket.
    // Dropping the entry leaves WI-1094's refusal exactly where it was
    // ([`param_supplied_slot`] then finds no slot, so the call is refused rather than
    // forwarded), and every such program was refused before this ticket too — so nothing
    // that loads today stops loading.
    //
    // COMPARED AFTER NORMALIZATION, which is not a detail: a declared clause and a
    // chain-derived one spell one spec differently (`normalize_op_requires_entry` is what
    // makes them comparable), and screening before it MEASURED as missing the collision
    // entirely — the anonymous-`requires` program loaded and answered wrong.
    // THE SCREEN READS THE WHOLE FRAME, SORT HALF INCLUDED, and leaving the sort half out
    // was MEASURED as re-opening the exact wrong answer WI-1094 closed: `Loose requires
    // WeakOrd[LT]` is declared on the SORT, so an op-only screen added a second covering
    // entry, the forward took the sort-level one — an anonymous dictionary that records
    // nothing about the argument — and the program LOADED and answered **3** where the
    // value's own `Descending` says **7**.

    let sort_half: Vec<RequiresEntry> = match impl_parent_of_op(kb, op_sym) {
        Some(parent) => {
            let provision = op_owner_provision(kb, op_sym);
            provider_dict_entries(kb, parent, provision)
                .entries()
                .to_vec()
        }
        None => Vec::new(),
    };
    for d in param_derived_requires(kb, op_sym) {
        let dn = normalize_op_requires_entry(kb, &d);
        // ASKED WITH THE PREDICATE THE FORWARD ITSELF USES, so the screen and the thing it
        // screens for cannot drift. `views_structurally_equal` was the first cut and
        // MEASURED WRONG: a declared clause and a chain-derived one for ONE spec are two
        // distinct hash-consed terms that RENDER IDENTICALLY
        // (`anthill.prelude.WeakOrd[T = anthill.prelude.String]` both, different `TermId`),
        // so the compare said "different", the entry was appended, and the program loaded
        // and answered out of the wrong slot. `requires_entry_covers_goal` is what
        // [`resolve`] asks when it picks a forward — if it says an existing entry covers
        // this goal, that entry is exactly what the body's read would take.
        let collides = match goal_from_requires_entry(kb, &dn) {
            Some(goal) => entries
                .iter()
                .chain(sort_half.iter())
                .any(|e| requires_entry_covers_goal(kb, e, &goal, None)),
            // No decodable goal: nothing can be said about a collision, so the
            // conservative direction is to add no channel and keep today's refusal.
            None => true,
        };
        if !collides {
            entries.push(dn);
        }
    }
    let rc: Rc<Vec<RequiresEntry>> = Rc::new(entries);
    kb.op_requires_chain_cache
        .borrow_mut()
        .insert(op_sym, rc.clone());
    rc
}

/// WI-822 LEG 1 — the `__req_<spec>` names of the slots `op_sym`'s OWN chain
/// contributes, in chain order. The CONTINUATION of `synth_req_names_of(parent)`,
/// never a replacement for it.
///
/// Disambiguation is the whole subtlety. A base (`__req_desc`) that occurs twice
/// must be split, and the sort half's naming is FIXED — every sort-keyed producer
/// re-derives it from the sort alone and would not see an op's influence — so a
/// collision is always resolved on the OP side: the sort slot keeps `__req_desc` and
/// the op slot becomes `__req_desc_<spec hash-cons id>`. Op-vs-op collisions split
/// the same way, by the same content-derived key `synth_req_names_of` uses, so a
/// name stays a pure function of `(kb, op)`.
fn synth_op_req_names_of(kb: &mut KnowledgeBase, op_sym: Symbol) -> Rc<Vec<Symbol>> {
    if let Some(cached) = kb.synth_op_req_names_cache.borrow().get(&op_sym) {
        return cached.clone();
    }
    let op_entries = op_requires_chain_rc(kb, op_sym);
    // The sort half's bases, so an op slot that collides with one is the side that
    // moves. Empty for a namespace-level operation.
    let mut counts: HashMap<String, usize> = HashMap::new();
    // The same parent [`op_dict_entries`] composes with — see there.
    if impl_parent_of_op(kb, op_sym).is_some() {
        let sort_chain = op_owner_dict_entries(kb, op_sym);
        for entry in sort_chain.entries() {
            let mut s = String::from("__req_");
            push_short_lc(kb, entry.required_sort, &mut s);
            *counts.entry(s).or_default() += 1;
        }
    }
    let mut bases: Vec<String> = Vec::with_capacity(op_entries.len());
    for entry in op_entries.iter() {
        let mut s = String::from("__req_");
        push_short_lc(kb, entry.required_sort, &mut s);
        *counts.entry(s.clone()).or_default() += 1;
        bases.push(s);
    }
    let mut out: Vec<Symbol> = Vec::with_capacity(op_entries.len());
    for (idx, (entry, base)) in op_entries.iter().zip(bases.iter()).enumerate() {
        let name = if counts[base.as_str()] > 1 {
            // MARKED `_o`, where the sort half's namer writes the bare id. Without the
            // marker an op slot could mint a name the sort half ALREADY minted: the sort
            // namer suffixes by hash-cons id whenever its own chain has two same-base
            // entries, and an op-scoped clause normalizes to a `SortView` that may hash-
            // cons to the very same `TermId` (`requires Desc[T = HT]` written on the sort
            // and on one of its members). Two slots under one name, and `find_requirement`
            // takes the first — silently the other instance's dictionary.
            //
            // THE `_o<id>` FORM IS NOT ITSELF COLLISION-FREE, and stays that way on
            // purpose (asked of it by the WI-1092 review, then re-derived): two OP
            // entries can mint this same name, but only by sharing a base AND a
            // hash-cons id — and a shared id IS structural identity, i.e. the same
            // requirement written twice. Identical entries substitute to one concrete
            // goal, hence one resolved tree and one dictionary, so first-wins hands the
            // second slot exactly what resolving it again would have produced. What
            // makes two slots want DIFFERENT dictionaries is a difference in the spec
            // term — another type-param binding, an operation binding — and every such
            // difference is a different `TermId`, which this suffix already separates.
            // Position would separate the names without separating anything real.
            match &entry.spec {
                Value::Term { id, .. } => format!("{base}_o{}", id.raw()),
                // WI-662: a denoted spec has no hash-cons id — the op-chain position is
                // stable and deterministic across the typer and eval passes, which both
                // come through this one cached function. `_od` and not `_o`, so a
                // position cannot collide with a `TermId` of the same numeric value.
                _ => format!("{base}_od{idx}"),
            }
        } else {
            base.clone()
        };
        out.push(kb.intern(&name));
    }
    let rc = Rc::new(out);
    kb.synth_op_req_names_cache
        .borrow_mut()
        .insert(op_sym, rc.clone());
    rc
}

/// Synthesize the requirement-param name for each entry of
/// `parent_sort`'s **direct** `requires` chain (WI-239). Returns
/// `Rc<Vec<Symbol>>` in chain order — index `k` is direct-require slot
/// `k`. Memoized on `synth_req_names_cache`; invalidated alongside
/// `requires_chain` caches when new `SortRequiresInfo` facts are
/// asserted.
///
/// The name is `__req_<spec short name, lowercased>`; chain entries that
/// share that base (two-of-the-same-spec, or two specs with the same
/// short name) are disambiguated by the entry's hash-consed `spec`
/// TermId — content-derived, never positional, so the name stays a pure
/// function of `(kb, parent_sort)`. Both the IR emitter (`req_insertion`)
/// and eval's frame-push call this, so they compute identical names. The
/// Self slot (`__req_self`) is not part of the chain — frame-push and
/// the emitter handle it separately.
///
/// WI-239: walks the DIRECT requires (top-level `requires_tree` nodes),
/// not the flattened transitive chain. The flat chain duplicated shared
/// subtrees — `requires Eq, Ord` with `Ord requires Eq` flattened
/// to `[Eq, Ord, Eq]`, yielding a benign `__req_eq` name collision —
/// whereas the direct chain is exactly `[Eq, Ord]`. A transitive
/// require is not a frame slot under this model; it lives inside a direct
/// requirement's tree-shaped dict value, reached via `requirement_at_sort`.
///
/// Uses `direct_requires_chain` (always substitution-composed) so the
/// names are deterministic across the typer and eval passes.
/// WI-1033: PRIVATE, and reached through [`DictChain::names`]. Public it was one half
/// of a pair a caller could take from two different chains — which is exactly what
/// WI-869 did, four times.
///
/// WI-822 LEG 1: STILL KEYED BY THE SORT ALONE, and that is load-bearing rather than
/// a leftover. An operation's own `requires` adds slots AFTER these
/// ([`op_dict_entries`]), and its names come from [`synth_op_req_names_of`] — because
/// this list is re-derived from the sort by producers that never see an operation
/// (`dict_layout`'s halves, `expand_dispatching_dict`'s frame slice), so a member
/// writing `requires` must not be able to rename its sort's slots. MEASURED: naming
/// the composed list in one pass renames the sort half on a base collision, and the
/// reader then looks for `__req_zeroable_c` in a frame the producer filled with
/// `__req_zeroable` (`wi822_op_scoped_supply_test::
/// a_colliding_op_slot_name_does_not_move_the_sort_slot`).
fn synth_req_names_of(
    kb: &mut KnowledgeBase,
    parent_sort: Symbol,
    // Proposal 066 §7 — the chain's normalized layout key ([`DictChain::provision`]).
    provision: Option<Symbol>,
) -> Rc<Vec<Symbol>> {
    if let Some(cached) = kb
        .synth_req_names_cache
        .borrow()
        .get(&(parent_sort, provision))
    {
        return cached.clone();
    }
    // THE SORT-LEVEL HALF IS NAMED ALONE, exactly as it was before provisions had
    // layouts of their own, so it carries ONE set of names in every chain of the
    // carrier: a frame handed between two bodies of the carrier (the same-sort inherit,
    // a member calling a helper) is read by name, and a sort-level slot that renamed
    // itself per provision would vanish from the reader's view.
    let sort_level = direct_requires_chain_rc(kb, parent_sort);
    let mut bases: Vec<String> = Vec::with_capacity(sort_level.len());
    for entry in sort_level.iter() {
        let mut s = String::from("__req_");
        push_short_lc(kb, entry.required_sort, &mut s);
        bases.push(s);
    }
    let mut counts: HashMap<String, usize> = HashMap::new();
    for b in &bases {
        *counts.entry(b.clone()).or_default() += 1;
    }
    let mut out: Vec<Symbol> = Vec::new();
    for (idx, (entry, base)) in sort_level.iter().zip(bases.iter()).enumerate() {
        let name = if counts[base] > 1 {
            match &entry.spec {
                // Ground: the hash-cons id, unchanged from the pre-WI-662 field.
                Value::Term { id, .. } => format!("{base}_{}", id.raw()),
                // WI-662: a denoted spec has no hash-cons id — disambiguate by chain
                // position (stable and deterministic across the typer/eval passes,
                // which both derive names through this one cached function).
                _ => format!("{base}_d{idx}"),
            }
        } else {
            base.clone()
        };
        out.push(kb.intern(&name));
    }
    // THE PROVISION'S CONDITIONS, named after it — so a collision is resolved on THEIR
    // side, as the op half resolves one ([`synth_op_req_names_of`]). Marked `_c` so a
    // condition can never mint a name the sort-level namer minted by its own suffix rule.
    let full = provider_dict_chain(kb, parent_sort, provision);
    let conditions = &full[sort_level.len()..];
    let mut cond_bases: Vec<String> = Vec::with_capacity(conditions.len());
    for entry in conditions {
        let mut s = String::from("__req_");
        push_short_lc(kb, entry.required_sort, &mut s);
        *counts.entry(s.clone()).or_default() += 1;
        cond_bases.push(s);
    }
    for (k, (entry, base)) in conditions.iter().zip(cond_bases.iter()).enumerate() {
        let name = if counts[base] > 1 {
            match &entry.spec {
                Value::Term { id, .. } => format!("{base}_c{}", id.raw()),
                _ => format!("{base}_cd{}", sort_level.len() + k),
            }
        } else {
            base.clone()
        };
        out.push(kb.intern(&name));
    }
    let rc = Rc::new(out);
    kb.synth_req_names_cache
        .borrow_mut()
        .insert((parent_sort, provision), rc.clone());
    rc
}

/// WI-857 — **THE** layout of a requirement dictionary's bundled sub-requirements.
/// One owner, because a producer and three consumers must agree on it, and before
/// this ticket they did not: the producer bundled the PROVIDER's `requires` chain
/// while `expand_dispatching_dict` named the frame from whatever chain the
/// dispatched target's parent declared and `requirement_at_sort` indexed the SPEC's
/// — so a carrier-keyed provision (`fact Ord[T = Int64]`, whose provider
/// `Int64` declares no `requires`) produced an arity-0 dictionary where two spec
/// slots were wanted, and every spec with a non-empty chain died at eval.
///
/// A dictionary for spec `S` supplied by provider `P` bundles, in this order:
///
/// 1. **the spec half** — `direct_requires_chain(S)` at the goal's bindings. This
///    is `S`'s own contract: what `requirement_at_sort(chain, slot = k)` indexes
///    (WI-239 — a transitively-required spec lives inside its direct requirement's
///    value, and `k` indexes the required spec's OWN chain), and what a body owned
///    by `S` itself reads when dispatch lands on the spec's op because `P`
///    contributes no member.
/// 2. **the provider half** — [`provider_dict_chain`]`(P)` at the matched impl
///    substitution: `P`'s conditional evidence, which `P`'s own member body reads.
///    WI-869 widened this from `direct_requires_chain(P)` to include `P`'s
///    conditional provisions' `:- goals`; the two coincide for a `P` that declares
///    none, and they are the same read [`synth_req_names`] names.
///
/// The spec half is the PREFIX so that reader — a projection path computed from
/// `requires_tree`, where a node's children are the required spec's chain — needs no
/// offset and no knowledge of the provider.
///
/// `P == S` contributes ONE list, not two. Two shapes reach that: a sort that
/// provides its own spec, and — the load-bearing one — a **parent-bundle**
/// dictionary (`build_dispatching_dict_from_chain`, WI-415), which is not a spec
/// instance at all but the frame bundle of a directly-called op's parent sort, so
/// its "spec" and its provider are the same sort and its single list is that sort's
/// chain, exactly as before this ticket. WI-869 reads that single list off the
/// **provider** rather than the spec, which is what `dict_sub_goals` actually
/// produces there (it skips the spec half entirely and emits only
/// `candidate_provider_sub_goals`); the two differ only when the same sort is reached
/// through two interned copies, and the provider is the one the sub-goals came from.
#[derive(Clone, Copy, Debug)]
pub struct DictLayout {
    pub(super) spec: Symbol,
    pub(super) provider: Symbol,
    /// Proposal 066 §7 — the provision the SELF case's one list is laid out for (see
    /// [`dict_layout`]); a dispatch's provider half is laid out for `spec` itself.
    pub(super) self_provision: Option<Symbol>,
    pub(super) spec_len: usize,
    pub(super) provider_len: usize,
}

/// WI-857 — the `EffectsRuntime` kind-anchor that every effect-row parameter
/// (`effects E = ?`) synthesizes as a `requires` entry. It is satisfied
/// STRUCTURALLY by the effect-row machinery and never by a carrier `fact`, so it is
/// never resolved: it rides as a structural leaf, occupying its dictionary slot so
/// the [`DictLayout`] halves stay positionally exact.
///
/// One owner for the FOUR readers that must agree about the ANCHOR'S SLOT — the
/// resolver's slot placement, `check_provider_requires`' exemption,
/// `build_dep_projection`'s synthetic projection, and (WI-20260830-DQD5W)
/// [`resolve_bridge_requirements`]'s structural leaf. They previously spelled the name
/// two ways (`try_resolve_symbol` and a qualified-name comparison) and, worse,
/// DISAGREED about the slot: the provider half dropped the anchor while the
/// parent-bundle projection kept it, so a provider with an effect-row param built a
/// dictionary SHORTER than the chain it is indexed by (MEASURED: 144 such
/// dictionaries across the suite — `Iterable`-over-`Stream` alone accounts for 140).
///
/// The FOURTH was the one that had never been written, and its absence had a
/// different shape: the bridge did not drop the slot, it tried to RESOLVE it — so a
/// bodied spec op reached from a rule body (`Iterable.isEmpty` at a `List`) suspended
/// on "`EffectsRuntime[Effects = Iterable.E]` is not fully pinned by the argument
/// types", which no argument type ever could be.
/// Other checks look the anchor up for their own purposes (`check_provider_-
/// operations`, `sort_param_is_effect_row`); they decide nothing about slots.
pub(crate) fn effects_runtime_sym(kb: &KnowledgeBase) -> Option<Symbol> {
    kb.try_resolve_symbol("anthill.prelude.EffectsRuntime")
}

/// True iff `spec` is the [`effects_runtime_sym`] kind-anchor. Via
/// [`same_sort_canonical`], NOT raw `==`: this replaced a qualified-NAME comparison
/// in `build_dep_projection`, which bridged a differently-interned copy of the
/// anchor sort, and a raw symbol compare would silently stop recognizing one — the
/// anchor would lose its slot and the dictionary would again come out shorter than
/// the chain it is indexed by.
pub(crate) fn is_effects_runtime(kb: &KnowledgeBase, spec: Symbol) -> bool {
    effects_runtime_sym(kb).is_some_and(|er| same_sort_canonical(kb, spec, er))
}

/// WI-866 — raise unless a PRODUCED layout is the one [`dict_layout`] predicts for the
/// same `(spec, provider)`. THE one owner of that comparison, because two producers
/// must state the invariant identically: `dict_sub_goals` (the resolver's sub-goal
/// list) and `build_dispatching_dict_from_chain` (the WI-415 parent bundle, whose
/// slots the IR emitter turns into the runtime dictionary a frame is pushed with).
///
/// ALWAYS ON, unlike the pre-WI-866 `debug_assert_eq!` this replaced, and for the
/// reason that assert was the wrong instrument: its violation is a WRONG-SLOT READ,
/// not a crash, so switching it off in release switches off the only thing that would
/// ever notice. `dict_layout` reads two memoized chains and compares two symbols, so
/// what release pays is a pair of cache hits per dictionary built.
///
/// A PANIC, AND THAT IS A DECISION — recorded here because a reviewer will ask, and
/// because the answer could change. Loud is not in question; the mechanism is. The
/// alternative is an internal-error arm on [`ResolutionResult`], which would let a
/// hosting process report instead of die. It is NOT taken, on two grounds. (1) The
/// condition is programmer error, not input: both halves are built 1:1 with the very
/// chains the prediction counts — `provider_requires_subgoals` emits one goal per
/// `direct_requires_chain` entry and `candidate_provider_sub_goals` one per
/// `provider_dict_chain` entry, each KEEPING the slot on its unreadable-head branch
/// rather than dropping it — so no KB can part them and only an edit to one of those
/// functions can. (2) `ResolutionResult` is a SEMANTIC verdict (no provider, a tie, a
/// cycle) that 27 match arms in the typer and three test files translate into
/// user-facing prose; a mechanism failure none of them can act on would have to be
/// given an arm at every one. The same trade is settled the same way, for the same
/// kind of inconsistent-KB condition, at [`crate::kb::term_view`]'s reflect-key reads.
///
/// AND IT IS THE OPPOSITE ANSWER TO THE ONE ITS TWO NEIGHBOURS GIVE — not an
/// inconsistency but the rule, which is WHOSE MISTAKE THIS CAN BE:
///
///  * `expand_dispatching_dict` checks the same property of a runtime dictionary VALUE
///    and returns `EvalError::Internal`, because a HOST can hand it a wrong-shaped one.
///    That is data, and data gets reported.
///  * `anthill-todo`'s host loop reports its own `alloc_dictionary` refusal and exits
///    rather than panicking, for the same reason one step further out: the mistake
///    belongs to the binary being told about it.
///  * This check's two sides are BOTH computed here, from the same memoized chains, on
///    inputs no caller supplies. Nothing outside the typer can part them. A panic says
///    that; an error variant would ask every caller to handle a case none of them can
///    cause or repair.
///
/// If a future edit gives either half an input a caller controls, the answer moves with
/// it — the rule decides, not this precedent.
pub(super) fn check_against_prediction(kb: &mut KnowledgeBase, produced: DictLayout, what: &str) {
    let predicted = dict_layout(
        kb,
        produced.spec,
        produced.provider,
        produced.self_provision,
    );
    if let Some(why) = produced.divergence_from(kb, &predicted) {
        panic!(
            "WI-866: {what} for `{}` supplied by `{}` — {why}",
            kb.qualified_name_of(produced.spec),
            kb.qualified_name_of(produced.provider),
        );
    }
}

/// Compute [`DictLayout`] for a dictionary of `spec` supplied by `provider`.
pub fn dict_layout(
    kb: &mut KnowledgeBase,
    spec: Symbol,
    provider: Symbol,
    // Proposal 066 §7 — the provision the SELF case is laid out for: a WI-415 parent
    // bundle is the frame of the operation it is built for, so this is that operation's
    // owner provision ([`op_owner_provision`]). Read ONLY when `spec == provider`; a
    // dispatch's provider half is laid out for `spec`, the provision dispatched.
    self_provision: Option<Symbol>,
) -> DictLayout {
    // WI-869: BOTH halves come from the chain the dictionary is actually laid out by.
    // The self case (a self-provision, or a parent bundle) is the provider's own
    // dictionary chain: `dict_sub_goals` skips the spec half entirely there and emits
    // only `candidate_provider_sub_goals`, so counting the spec's DECLARED chain would
    // be short by the provision conditions that half produces.
    if same_sort_canonical(kb, spec, provider) {
        let n = provider_dict_entries(kb, provider, self_provision).len();
        return DictLayout {
            spec,
            provider,
            self_provision,
            spec_len: n,
            provider_len: 0,
        };
    }
    let spec_len = direct_requires_chain_rc(kb, spec).len();
    let provider_len = provider_dict_entries(kb, provider, Some(spec)).len();
    DictLayout {
        spec,
        provider,
        self_provision: None,
        spec_len,
        provider_len,
    }
}

impl DictLayout {
    /// WI-866 — the layout a PRODUCER actually built, from the lengths of the two
    /// half-lists it emitted. [`dict_layout`] is the same shape PREDICTED from the
    /// two sorts alone, for the consumers that hold no goal (`expand_dispatching_dict`
    /// at the frame push, `stand_in_requirement`); this is the one derived from the
    /// list itself, so the NUMBER has the same single source the ORDER does.
    ///
    /// FOLDS THE SELF CASE, exactly as [`dict_layout`] does, so a produced and a
    /// predicted layout are directly comparable. `dict_sub_goals` emits the whole list
    /// from `candidate_provider_sub_goals` there — it skips the spec half outright —
    /// and so hands in `(0, n)`, while `dict_layout` counts the same one list as
    /// `(n, 0)`. Two encodings of ONE list, both right for their own reader; folding
    /// picks the layout's, which is what [`Self::slots_for`] indexes by. The
    /// PRODUCER's split point does not fold and is not this — see
    /// [`DictSubGoals::provider_half_start`].
    pub(super) fn from_halves(
        kb: &KnowledgeBase,
        spec: Symbol,
        provider: Symbol,
        // See [`dict_layout`]'s parameter of the same name.
        self_provision: Option<Symbol>,
        spec_len: usize,
        provider_len: usize,
    ) -> DictLayout {
        if same_sort_canonical(kb, spec, provider) {
            return DictLayout {
                spec,
                provider,
                self_provision,
                spec_len: spec_len + provider_len,
                provider_len: 0,
            };
        }
        DictLayout {
            spec,
            provider,
            self_provision: None,
            spec_len,
            provider_len,
        }
    }

    /// WI-866 — how `self` (a PRODUCED layout) differs from `predicted`
    /// ([`dict_layout`]'s), or `None` when they agree. The bridge between the two
    /// faces of one layout, and the ONLY thing that ties them together — see
    /// [`check_against_prediction`], the one caller that raises on a `Some`.
    ///
    /// BOTH HALVES, not just [`Self::arity`]. The pre-WI-866 assert compared totals,
    /// which is blind to the divergence that actually reads the wrong slots: a
    /// produced `(2, 3)` against a predicted `(3, 2)` passes an arity check, passes
    /// `expand_dispatching_dict`'s own arity guard, passes its `slots.len() ==
    /// names.len()` guard — and hands the callee's frame a slice of the dictionary
    /// that belongs to the other half.
    ///
    /// LENGTHS ONLY, because the two symbols cannot differ: `check_against_prediction`
    /// derives `predicted` from `self`'s OWN `(spec, provider)`, so comparing them
    /// would be checking the compiler. An earlier draft compared them
    /// `same_sort_canonical`ly and documented a guard nothing could trip.
    pub(super) fn divergence_from(
        &self,
        kb: &KnowledgeBase,
        predicted: &DictLayout,
    ) -> Option<String> {
        if self.spec_len == predicted.spec_len && self.provider_len == predicted.provider_len {
            return None;
        }
        Some(format!(
            "produced {} but `dict_layout` predicts {}",
            self.describe(kb),
            predicted.describe(kb),
        ))
    }

    /// How many sub-requirements a well-formed dictionary of this shape bundles.
    pub fn arity(&self) -> usize {
        self.spec_len + self.provider_len
    }

    /// WI-867 — `None` when a dictionary bundling `got` sub-slots is layout-valid for
    /// this shape, else the refusal, naming both halves.
    ///
    /// ONE OWNER for the question "is this dictionary the right shape", because it is
    /// now asked at two points on the HOST's side of the boundary and they must not
    /// come to disagree: [`Interpreter::alloc_dictionary`] asks it at CONSTRUCTION, so
    /// a short dictionary is refused where it is built, and
    /// [`Interpreter::call_with_requirements`] asks it again per chain slot at the
    /// entry, which is the only guard left for a value that did not come from the
    /// constructor. Before WI-867 only the second existed, so a host learned about a
    /// dictionary it built wrong at a frame push several calls later, attributed to
    /// the callee.
    ///
    /// The COUNT, one level. It does not descend: a sub-slot's own shape is its own
    /// layout's question, and a slot legitimately holds shapes that answer nothing —
    /// a `NoProvider` marker (WI-865) and the `EffectsRuntime` anchor (WI-857) both
    /// bundle nothing whatever their slot's spec declares.
    ///
    /// The spec and the provider are named ONCE, by [`Self::describe`], which is the
    /// owner of that rendering and the only half of the message that knows whether
    /// this is a two-half supply or a self-provider's single list.
    pub fn refuse_arity(&self, kb: &KnowledgeBase, got: usize) -> Option<String> {
        if got == self.arity() {
            return None;
        }
        Some(format!(
            "a dictionary bundling {got} sub-requirement(s) is not the shape this \
             supply calls for: {}",
            self.describe(kb),
        ))
    }

    /// The dictionary slots whose names are `synth_req_names(owner)` — the frame
    /// slice for an operation owned by `owner`. `None` when `owner` is neither the
    /// spec nor the provider: [`resolve_op_target`] can land on a THIRD sort (a
    /// same-short-name default the carrier merely inherits, or a WI-431
    /// instance-fact binding whose target lives elsewhere), and this dictionary
    /// says nothing about such an owner's chain. Harmless when that owner declares
    /// no `requires`; the caller must be loud when it does.
    pub(crate) fn slots_for(&self, kb: &KnowledgeBase, owner: Symbol) -> Option<Range<usize>> {
        // Spec first: when spec == provider the two halves are one list and the
        // spec arm answers for both.
        if same_sort_canonical(kb, owner, self.spec) {
            Some(0..self.spec_len)
        } else if same_sort_canonical(kb, owner, self.provider) {
            Some(self.spec_len..self.arity())
        } else {
            None
        }
    }

    /// Render the two halves for the arity diagnostic — a bare "expected N" cannot
    /// say WHICH half is short, which is the whole difficulty this layout resolves.
    pub fn describe(&self, kb: &KnowledgeBase) -> String {
        // `dict_layout` forces `provider_len = 0` for a self-provider, so ONE list is
        // exactly the same-sort case — tested canonically, like `slots_for`, so two
        // interned copies of one sort do not render as two halves.
        if same_sort_canonical(kb, self.spec, self.provider) {
            return format!(
                "{} slot(s) — `{}`'s own requires chain",
                self.arity(),
                kb.qualified_name_of(self.spec),
            );
        }
        format!(
            "{} slot(s) — {} for spec `{}`'s requires chain then {} for provider `{}`'s",
            self.arity(),
            self.spec_len,
            kb.qualified_name_of(self.spec),
            self.provider_len,
            kb.qualified_name_of(self.provider),
        )
    }
}

/// Append `sym`'s short name (last dotted segment), lowercased with
/// non-alphanumeric characters mapped to `_`, to `out` — for building
/// identifier-safe synthesized names.
fn push_short_lc(kb: &KnowledgeBase, sym: Symbol, out: &mut String) {
    let name = kb.local_name_of(sym);
    let short = name.rsplit('.').next().unwrap_or(name);
    for ch in short.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch.to_ascii_lowercase());
        } else {
            out.push('_');
        }
    }
}

/// Every sort `sort_sym` reaches through `requires`, transitively — each ONCE, in
/// first-reached depth-first order. The reader for the questions that are about WHICH
/// specs a sort refines: [`sort_refines`], [`check_obligations`], requirement coverage
/// (`op_requirements`), the loader's `capture_is_excused`. None of them reads a binding; a
/// reader that needs the bindings wants [`requires_chain`], whose entries are substituted
/// into `sort_sym`'s own scope.
///
/// WI-20260923-N3W68 (#8) — THIS WAS `requires_chain_flat`, and it returned
/// [`RequiresEntry`]s computed TWO WAYS, chosen by whether [`requires_tree`] had already run
/// for `sort_sym`: the flattened tree (bindings substituted; a sort reached along two paths
/// walked, and listed, once per PATH) or an unsubstituted walk with a global visited set
/// (raw bindings; a shared sub-requirement's subtree walked once). One question, two
/// answers, decided by cache warmth. MEASURED with a probe comparing the two lengths
/// wherever the cache was warm: they differed 14072 times across the workspace suite, and
/// `check_obligations`, which reported one obligation per ENTRY, grew with the cache.
/// Every source consumer read `required_sort` alone, which is why nothing else noticed.
/// Returning the sorts, deduplicated, makes the two paths one answer by construction: both
/// are a depth-first pre-order over the same `direct_requires` lists, and they differ only
/// in how far a REVISIT is re-walked — which adds nothing a first visit had not.
///
/// `&KnowledgeBase` because the function is read-only (WI-326 / WI-339): the tree cache is
/// the fast path when warm, and without it the walk reads `direct_requires` itself and
/// leaves the cache alone.
pub fn transitive_required_sorts(kb: &KnowledgeBase, sort_sym: Symbol) -> Vec<Symbol> {
    let mut out: Vec<Symbol> = Vec::new();
    if let Some(cached) = kb.requires_tree_cache.borrow().get(&sort_sym) {
        collect_tree_sorts(cached, &mut out);
        return out;
    }
    let mut visited: Vec<Symbol> = Vec::new();
    collect_required_sorts(kb, sort_sym, &mut out, &mut visited);
    out
}

/// [`transitive_required_sorts`]' warm path: the cached tree's sorts, pre-order, deduplicated.
fn collect_tree_sorts(nodes: &[RequiresNode], out: &mut Vec<Symbol>) {
    for node in nodes {
        if !out.contains(&node.entry.required_sort) {
            out.push(node.entry.required_sort);
        }
        collect_tree_sorts(&node.sub_requires, out);
    }
}

/// [`transitive_required_sorts`]' cold path: the walk over `direct_requires`, each sort's
/// own requirements read once.
fn collect_required_sorts(
    kb: &KnowledgeBase,
    sort_sym: Symbol,
    out: &mut Vec<Symbol>,
    visited: &mut Vec<Symbol>,
) {
    if visited.contains(&sort_sym) {
        return;
    }
    visited.push(sort_sym);
    for entry in direct_requires(kb, sort_sym) {
        if !out.contains(&entry.required_sort) {
            out.push(entry.required_sort);
        }
        collect_required_sorts(kb, entry.required_sort, out, visited);
    }
}

/// WI-230 — build the substitution-composed `requires` tree for
/// `sort_sym`. Top-level memoized on `kb.requires_tree_cache`: first
/// call walks `SortRequiresInfo` and substitutes; subsequent calls
/// for the same sort return the same `Rc<Vec<RequiresNode>>` from cache.
pub fn requires_tree(kb: &mut KnowledgeBase, sort_sym: Symbol) -> Rc<Vec<RequiresNode>> {
    if let Some(cached) = kb.requires_tree_cache.borrow().get(&sort_sym) {
        return cached.clone();
    }
    let mut visited: Vec<Symbol> = Vec::new();
    let nodes = build_requires_tree(kb, sort_sym, &HashMap::new(), &mut visited);
    let rc = Rc::new(nodes);
    kb.requires_tree_cache
        .borrow_mut()
        .insert(sort_sym, rc.clone());
    rc
}

/// WI-230 internal: recursive tree builder. Threads a substitution map
/// (`subst`) from parent into the child level — at each step, the
/// child's raw spec gets its `Ref(<parent's-param-qualified>)` atoms
/// rewritten to whatever the parent bound them to. Returns the list
/// of top-level RequiresNodes (one per direct `requires` of `sort_sym`).
pub(super) fn build_requires_tree(
    kb: &mut KnowledgeBase,
    sort_sym: Symbol,
    subst: &HashMap<Symbol, TermId>,
    visited: &mut Vec<Symbol>,
) -> Vec<RequiresNode> {
    if visited.contains(&sort_sym) {
        // Cycle break — return empty so siblings still get walked.
        return Vec::new();
    }
    visited.push(sort_sym);

    let raw_entries = direct_requires(kb, sort_sym);
    let mut nodes = Vec::with_capacity(raw_entries.len());
    for raw in raw_entries {
        let substituted_spec = substitute_in_spec(kb, &raw.spec, subst);
        let entry = RequiresEntry {
            required_sort: raw.required_sort,
            spec: substituted_spec,
            supply: raw.supply,
        };
        let child_subst = build_child_subst_map(kb, &entry);
        let sub_requires = build_requires_tree(kb, raw.required_sort, &child_subst, visited);
        nodes.push(RequiresNode {
            entry,
            sub_requires,
        });
    }

    visited.pop();
    nodes
}

/// WI-230 internal: walk `SortRequiresInfo` for one sort and return
/// its direct (non-transitive) requires entries. Same logic as the
/// pre-WI-230 `collect_requires` but without the recursive descent —
/// the tree builder owns recursion.
/// WI-662: the base sort symbol a `requires` SortView spec describes, read
/// carrier-agnostically via [`TermView`] so a denoted `Value::Node` spec decodes
/// identically to a ground `Value::Term`. Mirrors the arms `direct_requires`
/// previously matched on the hash-consed spec term: a `SortView(base, …)`
/// application (positional arg 0 is the base sort), or a bare nullary sort.
pub(crate) fn spec_base_functor(kb: &KnowledgeBase, spec: &impl TermView) -> Option<Symbol> {
    match spec.head(kb) {
        ViewHead::Functor { pos_arity, .. } if pos_arity > 0 => {
            match spec.pos_arg(kb, 0)?.head(kb) {
                ViewHead::Functor { functor, .. } => functor,
                _ => None,
            }
        }
        ViewHead::Functor {
            functor,
            pos_arity: 0,
            named_arity: 0,
        } => functor,
        _ => None,
    }
}

pub(super) fn direct_requires(kb: &KnowledgeBase, sort_sym: Symbol) -> Vec<RequiresEntry> {
    let mut out = Vec::new();
    // NOT A `return` ON AN UNREGISTERED `SortRequiresInfo`, and the difference is
    // WI-1110's: the conversion half below reads `SortProvidesInfo` and has nothing to do
    // with this functor, so bailing on a KB that registered one reflect relation and not
    // the other would silently drop every self-supplied slot — conversions would be
    // offered as providers again and the cycle WI-1110 removes would come back with no
    // diagnostic. WI-1112: the `if let` that used to say this is now inside
    // `requires_rids_by_sort` (its `rids_or_scan` fallback resolves the functor and
    // answers empty when it is absent), so the property is unchanged and stated once.
    collect_sort_requires(kb, sort_sym, &mut out);

    // WI-1110 — AND THE SPEC'S OWN CONVERSIONS, which are chain entries too.
    //
    // ONE EDGE, ONE SLOT. A sort that writes BOTH `requires A[T]` and `provides A[T = T]`
    // names one relation twice, and two equal entries are a slot `synth_req_names` cannot
    // name apart (its disambiguator keys on the spec's hash-cons id, so it cannot tell
    // them apart either). The `requires` spelling placed first keeps the slot; the
    // conversion adds nothing to the LAYOUT and is already recorded in the provider
    // relation, which is where its other reader looks.
    //
    // MATCHED BY SPEC BASE AND CARRIER BINDING, not by `views_structurally_equal`: the
    // two clauses are loaded through different paths and their bindings carry DIFFERENT
    // SYMBOLS for the same parameter (`resolve_requires_bindings` re-keys a `requires`
    // spec by the required spec's own param symbols), so a structural comparison —
    // which compares keys by symbol — never fires. That is why the sibling
    // `is_identity_forwarding` compares LOCAL NAMES, and why this does too. Driven by
    // `a_sort_writing_both_clauses_gets_one_slot`.
    for entry in self_supplied_entries(kb, sort_sym) {
        let Some((_, conv_bindings)) = unwrap_spec_view_value(kb, &entry.spec) else {
            continue;
        };
        if out.iter().any(|e| {
            same_sort_canonical(kb, e.required_sort, entry.required_sort)
                && unwrap_spec_view_value(kb, &e.spec).is_some_and(|(_, req)| {
                    conv_bindings.iter().all(|(ck, _)| {
                        req.iter()
                            .any(|(rk, _)| kb.local_name_of(*rk) == kb.local_name_of(*ck))
                    })
                })
        }) {
            continue;
        }
        out.push(entry);
    }
    out
}

/// The `SortRequiresInfo` half of [`direct_requires`] — every `requires` clause written
/// on `sort_sym`, in fact order.
///
/// WI-1112 — THE SORT INDEX, not `rules_by_functor`, for the reason its sibling
/// `self_supplied_entries` already gives about the provider index: this runs once per
/// node of the requires TREE (the per-sort `requires_chain_cache` memo sits ABOVE the
/// recursion, so it does not cover this), which made the raw scan O(chain-nodes ×
/// |SortRequiresInfo|). MEASURED with the two arms ALTERNATING in one process (min of 5
/// pairs, warmup dropped, stdlib + host bindings, 3148 calls per load): debug 69.4 ms →
/// 1.55 ms, taking the whole load 657.8 ms → 586.2 ms; release 7.4 ms → 0.17 ms, load
/// 85.9 ms → 67.1 ms. `self_supplied_entries` beside it, untouched by the change, moved
/// 10.8 → 10.2 ms and 0.8 → 0.8 ms — the control that says the rest is not machine drift.
/// `rids_or_scan` still falls back to the scan when
/// `requires_index` is `None`, which is the state across every load-time window in which
/// the relation (or the provision relation the other half reads) can still change.
pub(super) fn collect_sort_requires(
    kb: &KnowledgeBase,
    sort_sym: Symbol,
    out: &mut Vec<RequiresEntry>,
) {
    for rid in requires_rids_by_sort(kb, sort_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        // WI-662: read the head carrier-agnostically. A value-fact SortRequiresInfo
        // (denoted-bearing spec, e.g. `requires Foo[E = Modify[c]]`) now flows
        // through — the spec rides as a `Value::Node` on `RequiresEntry.spec`
        // rather than being skipped for want of a `TermId` (the pre-WI-662 gap
        // that silently excluded effect-bearing sort-level requires).
        let head = kb.rule_head_value(rid);

        // Check that this SortRequiresInfo is for our sort. `sort_ref` is always a
        // ground SortView of the enclosing (resolved) sort. WI-672: compare by
        // `canonical_sort_sym`, not `same_symbol` — canonical identity keeps a fact for
        // anthill.cli.Main distinct from one about anthill.todo.Main without any
        // last-segment matching (spec §8.6).
        let Some(sort_ref_tid) = crate::kb::op_info::head_field_term(kb, head, "sort_ref") else {
            continue;
        };
        // WI-20260923-N3W68 (#11) — decoded by `sort_ref_functor`, as every provides-side
        // reader decodes the same field, and NOT by a `Term::Fn` shape test. The field is
        // `make_name_term_from_sym(owner)`, which applies the WI-511 / CZJ2N canon: `Fn` for
        // a `SymbolKind::Sort` owner, `Ref` for any other — so the shape test was an unnamed
        // "is the owner a sort" read (the convention in `rustland/CLAUDE.md`). And the owner
        // need not be one: a `requires` in a NAMESPACE body is legal (kernel-language.md,
        // "Requires declaration") and emits its fact scoped to the namespace, whose `Ref`
        // this scan and `build_requires_index` both skipped — a declared requirement no
        // reader could see, with no diagnostic. MEASURED: `namespace N … requires
        // Spec[T = Int64] … end` loaded clean and `direct_requires(N)` answered nothing.
        // No corpus writes one (a probe on the skip fired zero times across the workspace
        // suite).
        let Some(sr_functor) = crate::kb::load::sort_ref_functor(kb, sort_ref_tid) else {
            continue;
        };
        if !same_sort_canonical(kb, sr_functor, sort_sym) {
            continue;
        }

        // Extract the spec (SortView) carrier-faithfully and the base sort it
        // describes. `head_field_value` yields a `Value::Term` for a ground spec
        // and a `Value::Node` for a denoted-bearing one, preserving occurrence.
        let Some(spec_value) = crate::kb::op_info::head_field_value(kb, head, "spec") else {
            continue;
        };
        let Some(base_functor) = spec_base_functor(kb, &spec_value) else {
            continue;
        };

        out.push(RequiresEntry {
            required_sort: base_functor,
            spec: spec_value,
            supply: SupplySource::Required,
        });
    }
}

/// WI-1110 — is this `provides` row a CONVERSION (a spec's, [`SupplySource::SelfSupplied`])
/// rather than a claim of membership (a carrier's, which belongs in the provider table)?
///
/// THE QUESTION IS WHERE THE TARGET'S CARRIER CAME FROM. A spec that constrains an
/// external thing has a CARRIER PARAMETER — `WeakOrd`'s `T`, `PartialEq`'s `T`,
/// `Iterable`'s `C` — and [`spec_carrier_param_or_sole`] is the typer's one owner of
/// which parameter that is. A row binding that parameter to one of the SUBJECT'S OWN
/// type parameters says "whatever satisfies me at this parameter satisfies the target at
/// it": a conversion between two constraints on one thing, and exactly what `B <: A`
/// means operationally. A row binding it to a concrete sort — `Int64 provides
/// Ord[T = Int64]`, `Set provides Eq[T = Set]`, `Pair provides Ord[Pair] :- …`,
/// `Stream provides Iterable[C = Stream, …]` — says "THIS thing is a target", which is a
/// fact about the world.
///
/// A SELF-REPRESENTING spec has no carrier parameter and so is never a conversion
/// target. That is not an exemption bolted on, it is the same sentence: `Stream`,
/// `FiniteStream` and `LogicalStream` ARE their own carriers (WI-614's
/// [`spec_is_self_representing`], read here through the ladder), so `LogicalStream
/// provides Stream[T = T, E = E]` binds Stream's ELEMENT and EFFECT rows and says
/// nothing about a carrier — it is the membership claim "a LogicalStream is a Stream",
/// and value-directed dispatch reaches `Stream.splitFirst` on a `Relation` THROUGH it.
/// MEASURED: reading those rows as conversions (the first cut, which keyed on
/// [`is_identity_forwarding`] — bindings alone) put a slot in `Relation`'s,
/// `FiniteStream`'s and `LogicalStream`'s dictionaries and broke six tests across
/// wi210/wi224/wi411/wi474, element threading included.
///
/// AND THE ROW'S SHAPE IS NOT ENOUGH — a PARAMETRIC WITNESS has it too. `sort AnyM {
/// sort E = ?  provides Monoid[T = E]  operation combine(a: E, b: E) = 99 }` (wi841)
/// binds Monoid's carrier to its own type parameter exactly as `Ord` binds WeakOrd's,
/// and it is not a conversion: `AnyM` IS a Monoid dictionary, it carries `combine`.
/// MEASURED — with the shape test alone, `AnyM`'s own `Monoid[T = E]` slot resolved by
/// search straight back to `AnyM` and all three wi841 selection tests failed with
/// `construction is cyclic: Monoid[T = Int64] -> Monoid[T = Int64]`.
///
/// So there are two questions and the predicate asks both. What is the row ABOUT — an
/// abstract parameter (conversion) or the subject itself (membership)? And can the
/// subject ANSWER it — does it supply the target's operations? A subject that supplies
/// none of them is not a dictionary for the target and the row cannot be a witness;
/// there is nothing left for it to mean but "hold one of me and you can obtain one of
/// those". `Ord` declares no operation at all, which is why its whole content is a
/// relation between two constraints.
///
/// RELATION TO THE DERIVATION'S PREDICATE, which is NOT the same one and must not be
/// made so. [`forwarded_rows_to_derive`] keys on [`forwarding_param_map`], a strictly
/// WIDER set (every conversion is a parameter forwarding; the Stream family and `AnyM`
/// are parameter forwardings and not conversions). The direction that has to hold is
/// `conversion ⟹ derived-through`: a row this excludes from the provider search
/// ([`collect_provides_candidates`]) must have its carriers' direct rows materialized,
/// or the exclusion would delete an answer instead of relocating it. The converse is
/// deliberately false — a Stream-family row keeps BOTH its derived rows and its search
/// role.
pub(super) fn provision_is_conversion(
    kb: &KnowledgeBase,
    subject: Symbol,
    target: Symbol,
    bindings: &[(Symbol, TermId)],
) -> bool {
    if same_sort_canonical(kb, subject, target) {
        return false;
    }
    // A PARAMETER FORWARDING FIRST, WHICH IS THE DERIVATION'S OWN PREDICATE, and this
    // conjunct is what makes the ticket's invariant true BY CONSTRUCTION rather than by
    // assertion: `conversion ⟹ derived-through`. A row this predicate accepts is excluded
    // from the provider search, so its carriers' own rows must be materialized by
    // [`forwarded_rows_to_derive`] — and that reads [`forwarding_param_map`]. A first
    // cut asked only about the CARRIER binding and was therefore NOT a subset of it: a
    // MIXED row (`provides Sp[T = A, U = Concrete]`) passed here and derived nothing, so
    // the answer would have been DELETED rather than relocated. WI-1109 also excluded a
    // RENAMED forward (`sort Ord2 { sort E = ?  provides WeakOrd[T = E] }`) for the same
    // reason; WI-1111 taught the derivation to translate instead, so a rename is now
    // derived-through and belongs on this side of the line — measured, the exclusion was
    // costing the rename an eval-time `OperationBodyMissing` rather than an answer.
    //
    // It also closes the OP-BINDING channel, which the operation test below cannot see.
    // A provision may supply the target's operations by BINDING them
    // (`provides Monoid[T = E, combine = myCombine]`, WI-431) instead of by declaring a
    // same-named member; `supplies_any_operation_of` reads only the declaration channel
    // and would call such a witness a conversion. A parameter forwarding has no binding
    // whose value is not a type parameter, so no op binding can hide inside one.
    //
    // And it is the CHEAP test, which matters: this runs for every provision row of every
    // sort whose chain is built, and both questions below are walks —
    // `spec_carrier_param_or_sole` falls through to `spec_is_self_representing`, which is
    // not memoized, and `supplies_any_operation_of` walks two operation surfaces.
    if !is_param_forwarding(kb, subject, target, bindings) {
        return false;
    }
    // AND THE TARGET MUST BE A CONSTRAINT ON SOMETHING, NOT A THING IN ITS OWN RIGHT. A
    // SELF-REPRESENTING spec is the latter: `Stream`, `FiniteStream` and `LogicalStream`
    // ARE their own carriers, so `LogicalStream provides Stream[T = T, E = E]` binds
    // Stream's ELEMENT and EFFECT rows and is the membership claim "a LogicalStream is a
    // Stream" — which value-directed dispatch reaches on a `Relation` (WI-714 / WI-495 /
    // WI-496). MEASURED: reading those three rows as conversions put a slot in their
    // dictionaries and broke six tests across wi210/wi224/wi411/wi474, element threading
    // included.
    //
    // WI-1111 SPLITS THE `None`, and does it INSIDE the `else` rather than ahead of the
    // question, which matters for two separate reasons.
    //
    // THE MEANING. `spec_carrier_param_or_sole` answers `None` for TWO different reasons
    // and only one of them belongs here — the "one name, two questions" shape. One is
    // SELF-REPRESENTING (above). The other is "no operation names a carrier AND there is
    // not exactly one parameter to be it", which is an OPLESS MULTI-PARAMETER spec:
    // `sort Mid { sort T = ?  sort E = ?  provides Low[T = T, E = E] }`. Conflated,
    // `Top provides Mid[T = T, E = E]` was no conversion, so `Top` stayed in the search
    // and — MEASURED — answered `Low[T = Car, E = Int64]` and the mirrored
    // `Low[T = Bool, E = Car]` with `["Top"]` ALONE, a spec declaring no operation offered
    // as the sole answer to a goal nothing provides. Split, `Mid` is what it looks like: a
    // constraint with two parameters and no members of its own. MEASURED over stdlib +
    // host bindings: ZERO rows change class, so the corpus cannot witness it and
    // `an_opless_multi_parameter_floor_is_still_a_conversion` is the only driver.
    //
    // AND THE ORDER IS THE POINT, not a formatting choice. Asking
    // `spec_is_self_representing` FIRST — as a first cut did — reaches a NON-MEMOIZED
    // walk of the target's whole operation surface on every provision row of every chain
    // build, where `spec_carrier_param_or_sole`'s rung 1 is MEMOIZED and answers `Some`
    // for the overwhelming majority. MEASURED on 525 identical tests: the eager form cost
    // ~1 %, and this shape gives it back. It also keeps the change a strict WIDENING —
    // every row that was a conversion before still is, and only the `None` arm gains
    // members — where the eager form silently NARROWED the class for a target that is
    // both self-representing and names a rung-1 parameter (`Set.insert(s: Set, x: T)`),
    // a population the CONJUNCT2-NEW inventory did not count because it only counted the
    // widening direction.
    let Some(carrier_param) = spec_carrier_param_or_sole(kb, target) else {
        return !spec_is_self_representing(kb, kb.canonical_sort_sym(target))
            && !supplies_any_operation_of(kb, subject, target);
    };
    // WHEN THE TARGET DOES NAME A CARRIER PARAMETER, THE ROW MUST BIND IT: a row
    // forwarding only the ELEMENT parameters says nothing about the carrier and converts
    // nothing.
    let carrier_name = kb.local_name_of(carrier_param);
    let about_a_parameter = bindings
        .iter()
        .any(|(name, _)| kb.local_name_of(*name) == carrier_name);
    about_a_parameter && !supplies_any_operation_of(kb, subject, target)
}

/// WI-1110 — is THIS ROW of `subject provides target[…]` a CONVERSION? Asked of the
/// CHAIN, where [`self_supplied_entries`] has already decided it and written the answer
/// on the entry, AND of the row's own bindings.
///
/// ONE OWNER OF THE PREDICATE, and the two readers below are why that matters: they must
/// agree with the chain or the ticket's own invariant breaks — a row excluded from the
/// provider search ([`collect_provides_candidates`]) and a provision excused from the
/// load check ([`check_provider_requires`]) must be exactly a row that put a slot in the
/// subject's chain, or an obligation is dropped with nothing carrying it. Re-deriving the
/// predicate at each site would let them disagree; reading [`SupplySource`] cannot.
///
/// The chain is memoized, so this is a hash lookup and a walk of a two-or-three element
/// vector — cheaper than the operation-surface comparison the predicate itself does, and
/// the candidate loop runs it per provision row.
///
/// PER ROW, NOT PER (subject, target) PAIR, and the difference is a soundness one: one
/// sort may write a conversion AND a concrete membership claim for the SAME spec —
/// `sort S { sort T = ?  provides A[T = T]  provides A[T = Concrete] }`. The pair reading
/// dropped BOTH from dispatch and excused BOTH from the load check, deleting a real
/// answer. So [`chain_has_conversion`] says "this sort has a conversion to `target`" and
/// [`row_forwards_a_param`] says "and this row is it": a conversion entry is a PARAMETER
/// forwarding by construction ([`provision_is_conversion`]), so a row binding anything
/// else is a different row. Driven by
/// `a_conversion_does_not_hide_a_sibling_concrete_row`, which fails `got []` with the
/// pair reading restored.
///
/// TWO ENTRY POINTS BECAUSE THE TWO READERS HOLD THE BINDINGS DIFFERENTLY — a decoded row
/// keys by `Symbol`, a `Provision`'s σ by short-name `String` — and the row test must run
/// on `&KnowledgeBase` BEFORE the chain lookup takes it mutably. Sharing the two halves
/// rather than the signature is what keeps the answer one answer. Since WI-1111 widened
/// the shape half from an identity to a MAP, neither entry point reads the key any more;
/// the two signatures survive because the CALLERS still differ.
///
/// WI-1111 — AND A DERIVED ROW IS ASKED THROUGH ITS ORIGIN, at the one caller that has
/// the `RuleId` to ask with. See [`collect_provides_candidates`]'s second skip: the chain
/// deliberately holds no entry for a derived row ([`self_supplied_entries`]), so this
/// function answers `false` for one, and a two-floor conversion tower materializes
/// exactly such a row with a spec as its carrier.
///
/// WI-1111 REVIEWED WHETHER THIS SKIP SHOULD EXIST AT ALL, and the answer is YES — the
/// question being whether a self-supplied slot filled by PROJECTION rather than by search
/// would dissolve it along with the cycle it was introduced to break. It would not: a
/// conversion is a row in the provider relation however the slot is filled, so at an
/// abstract element it is still the only candidate offered and the vacuous dispatch still
/// resolves. The full argument, with its four measurements, is at [`SupplySource`]. What
/// WI-1111 did instead was COMPLETE the skip over the shapes the search can actually
/// reach — a renaming forwarding, a permuting one, a derived spec-to-spec row and an
/// opless multi-parameter floor — each of which loaded clean and trapped at eval with
/// `OperationBodyMissing`. `wi1111_provision_chain_search_test` drives all four.
pub(super) fn is_conversion_edge_at(
    kb: &mut KnowledgeBase,
    subject: Symbol,
    target: Symbol,
    bindings: &[(Symbol, TermId)],
) -> bool {
    if !bindings.is_empty() && bindings.iter().all(|(_, v)| row_forwards_a_param(kb, *v)) {
        chain_has_conversion(kb, subject, target)
    } else {
        false
    }
}

/// [`is_conversion_edge_at`] over a `Provision`'s σ, which keys by the spec's type-param
/// SHORT NAME (see `Provision::sigma`).
pub(super) fn is_conversion_edge_named(
    kb: &mut KnowledgeBase,
    subject: Symbol,
    target: Symbol,
    bindings: &[(String, TermId)],
) -> bool {
    if !bindings.is_empty() && bindings.iter().all(|(_, v)| row_forwards_a_param(kb, *v)) {
        chain_has_conversion(kb, subject, target)
    } else {
        false
    }
}

/// One binding of a row, tested for the shape a conversion has: the value is a type
/// parameter. The per-binding half of [`forwarding_param_map`], which the whole-row form
/// there applies the same way.
fn row_forwards_a_param(kb: &KnowledgeBase, value: TermId) -> bool {
    type_param_local_name(kb, value).is_some()
}

/// Does `subject` declare a CONVERSION to `target` — i.e. did [`self_supplied_entries`]
/// classify one of its `provides` clauses one?
///
/// ASKED OF [`self_supplied_entries`] DIRECTLY, NOT OF THE CHAIN (WI-1111 review), and
/// the difference is a hole the chain reading had. `direct_requires`' "one edge, one
/// slot" dedup drops the conversion entry when the sort ALSO writes `requires A[T]` —
/// the shape its own comment sanctions and `a_sort_writing_both_clauses_gets_one_slot`
/// pins — keeping the `requires` one, whose supply is `Required`. Reading the chain then
/// found no `SelfSupplied` entry, so [`is_conversion_edge_at`] answered `false` and the
/// spec went back into the provider search: WI-1110's headline defect, reachable through
/// the one shape it explicitly allows. MEASURED — `Low[T = Car]` offered
/// `["High", "Car"]` with the `requires` written and `["Car"]` without it. Driven by
/// `a_sort_writing_both_clauses_is_still_not_a_candidate`.
///
/// STILL ONE OWNER, which is what WI-1110's `SupplySource` doc asks for: the deciding
/// predicate is [`provision_is_conversion`] either way, and this now reads the function
/// that applies it rather than a LAYOUT derived from it. The layout may legitimately
/// collapse two spellings of one edge; the question "is this row a conversion" may not.
pub(super) fn chain_has_conversion(kb: &KnowledgeBase, subject: Symbol, target: Symbol) -> bool {
    let target_canon = kb.canonical_sort_sym(target);
    self_supplied_entries(kb, subject)
        .iter()
        .any(|e| kb.canonical_sort_sym(e.required_sort) == target_canon)
}

/// WI-1110 — does `subject` DECLARE an operation of `target`'s surface, i.e. is it (at
/// least partly) a dictionary for it? By operation SHORT NAME, which is the same
/// identity `find_operation_in_scope` and `build_sort_ops_table` use to decide that a
/// carrier's member backs a spec op.
fn supplies_any_operation_of(kb: &KnowledgeBase, subject: Symbol, target: Symbol) -> bool {
    // BORROWED, NOT OWNED (WI-1111), AND TIGHTENED HERE BECAUSE HERE IS WHERE THE PER-ROW
    // USE BEGAN. `local_name_of` hands back a `&str` into the symbol table and `kb` is
    // borrowed immutably for the whole call, so the short names need no `String`. WI-1110
    // put this function on a per-provision-row path — `direct_requires` reads the
    // provision relation for every chain build, and every row reaching
    // [`provision_is_conversion`]'s last conjunct lands here — where before it was asked
    // once per question.
    //
    // NOT TODAY'S BOTTLENECK, and the number is here so nobody re-derives it: MEASURED
    // over a stdlib load, 62 calls totalling 0.4 ms, against `direct_requires`' own
    // 97 ms. A first cut of this comment claimed this was where WI-1109/WI-1110's 11 %
    // and 18 % phase costs landed; instrumenting the load REFUTED that. The cost was in
    // the sibling half — `collect_sort_requires` scanned the whole `SortRequiresInfo`
    // relation per call, ~3000 times per load, because `SortRequiresInfo` was the one
    // reflect relation with no `SymbolKeyedFactIndex` while `SortProvidesInfo`,
    // `SortInfo` and `SortAlias` all had one.
    //
    // WI-1112 GAVE IT ONE (`requires_index`), which is why the paragraph above is in the
    // past tense: that half is now 1.55 ms of a 586 ms debug load, and THIS function's
    // 0.4 ms is no longer being compared against a 70 ms neighbour. The reading that
    // still holds is the one it was written for — a per-row path whose cost is real but
    // small — so do not read the old ratio as licence to put work here.
    //
    // The allocation goes anyway: it buys nothing on a path that is now per row.
    let target_ops: Vec<&str> =
        crate::kb::op_requirements::operations_of_sort(kb, kb.canonical_sort_sym(target))
            .iter()
            .map(|&op| short_op_name(kb, op))
            .collect();
    if target_ops.is_empty() {
        return false;
    }
    crate::kb::op_requirements::operations_of_sort(kb, kb.canonical_sort_sym(subject))
        .iter()
        .any(|&op| target_ops.contains(&short_op_name(kb, op)))
}

/// The last dotted segment of an operation's local name — the identity
/// `find_operation_in_scope` and `build_sort_ops_table` use to decide that a carrier's
/// member backs a spec op.
fn short_op_name(kb: &KnowledgeBase, op: Symbol) -> &str {
    kb.local_name_of(op).rsplit('.').next().unwrap_or("")
}

/// WI-1110 — `sort_sym`'s SELF-SUPPLIED chain entries: the slots its own `provides`
/// clauses put there, read from the same `SortProvidesInfo` facts the provider table
/// reads.
///
/// THE PREDICATE IS [`provision_is_conversion`], and a CONDITIONAL row contributes
/// nothing, for the reason [`forwarded_rows_to_derive`] gives about the derivation: a
/// `:- goals` tail rides in separate `ProvidesConditionInfo` facts, so reading the row
/// alone would make a conditional edge an unconditional slot.
fn self_supplied_entries(kb: &KnowledgeBase, sort_sym: Symbol) -> Vec<RequiresEntry> {
    let mut out = Vec::new();
    let mut conditioned: Option<Vec<Symbol>> = None;
    // THE CARRIER INDEX, not `rules_by_functor` — this runs once per SORT and the
    // provision relation is the largest in the KB, so the raw scan is O(sorts x
    // provisions). MEASURED: the scanning form took a stdlib load from 0.10 s to 0.18 s,
    // an 80 % regression on the whole load. `rids_or_scan` still falls back to the scan
    // when `provides_index` is `None`, which is the state during the derivation pass —
    // and in that window its per-fact carrier RE-FILTER (inside
    // [`provides_rows_of_provider`]) is what keeps a row belonging to ANOTHER carrier
    // out: without it `Ord provides WeakOrd[T = T]`, read while querying an unrelated
    // `Foo`, handed `Foo` a self-supplied slot it never declared (WI-660/WI-672).
    for row in provides_rows_of_provider(kb, sort_sym) {
        let (base, bindings) = (row.spec_base, &row.bindings);
        if !provision_is_conversion(kb, sort_sym, base, bindings) {
            continue;
        }
        // Decoded lazily: the overwhelming majority of sorts have no conversion at all,
        // and this walks every `ProvidesConditionInfo` fact.
        let conds = conditioned.get_or_insert_with(|| {
            provision_conditions(kb, sort_sym)
                .into_iter()
                .map(|c| c.provided)
                .collect()
        });
        if conds.iter().any(|c| same_sort_canonical(kb, *c, base)) {
            continue;
        }
        // A DERIVED ROW IS NOT A WRITTEN CLAUSE, and only a written one puts a slot in a
        // chain. `derive_forwarded_provisions` walks a tower transitively, so a
        // two-conversion tower (`A provides B[T = T]`, `B provides C[T = T]`) makes it
        // assert `A provides C[T = T]` — a row whose carrier is itself a spec and whose
        // shape is a conversion's. Reading it back here would give `A` a SECOND slot for
        // a dictionary already reachable inside its first, changing `DictLayout::slots_for`,
        // `synth_req_names` and every projection path through `A`. `mark_derived_provision`
        // records exactly which rows the pass minted (WI-1109's provenance channel), so
        // this asks it rather than guessing from the shape.
        if kb.derived_provision_origin_of(row.rid).is_some() {
            continue;
        }
        out.push(RequiresEntry {
            required_sort: base,
            spec: Value::term(row.spec_view),
            supply: SupplySource::SelfSupplied,
        });
    }
    out
}

/// WI-20260923-32XFQ — rewrite `t`'s LEAVES. `leaf` answers `Some(new)` for a term it
/// rewrites — `Some(t)` keeps one whole and stops the descent there — and `None` to descend:
/// a `Fn` is rebuilt through [`KnowledgeBase::map_fn_children`] (hash-cons identity kept when
/// nothing below changed), anything else is kept.
///
/// The one walk under the term-level σ substitutions, each of which spelled it. `leaf`
/// carries the site's LEAF SET, and the sets differ on purpose: {`Ref`, nullary `Fn`} for
/// [`substitute_in_spec`] and [`substitute_spec_via_subst`]; those plus `Ident` where the
/// leaf is read through [`view_ref_symbol`] (`substitute_impl_params_alloc`,
/// `subst_requires_value`); a bare `Ref` (and `Ident`) beside a `var_ref` wrapper that is
/// kept or replaced WHOLE, never descended, in the two binder-aware passes
/// (`substitute_ref_syms`, [`substitute_ref_terms`]). Merging ACROSS two sets changes an
/// answer unless `Ident` is shown absent from what the narrower one reads; this owns only
/// the walk.
pub(super) fn rewrite_term_leaves(
    kb: &mut KnowledgeBase,
    t: TermId,
    leaf: &impl Fn(&mut KnowledgeBase, TermId) -> Option<TermId>,
) -> TermId {
    if let Some(new) = leaf(kb, t) {
        return new;
    }
    // A declined non-`Fn` is kept as it is. Asked here and not left to `map_fn_children`,
    // which clones the term before it looks — a `String` literal's allocation per leaf.
    if !matches!(kb.get_term(t), Term::Fn { .. }) {
        return t;
    }
    kb.map_fn_children(t, |kb, child| rewrite_term_leaves(kb, child, leaf))
}

/// WI-20260923-32XFQ — [`rewrite_term_leaves`]' carrier-faithful spec walk (WI-662): a
/// ground `Value::Term` spec is rewritten by `term`; a denoted `Value::Entity` spec is
/// rebuilt with each child walked the same way, so a co-carried type binding (`Foo[T =
/// ParentT, E = Modify[c]]`) is still rewritten; anything else — a denoted `Value::Node`
/// child — is kept verbatim (its Expr-occurrence σ is the deferred parametric-effect
/// handling). The walk [`substitute_in_spec`] and [`substitute_spec_via_subst`] each spelled.
pub(super) fn rewrite_spec_value(
    kb: &mut KnowledgeBase,
    spec: &Value,
    term: &impl Fn(&mut KnowledgeBase, TermId) -> TermId,
) -> Value {
    match spec {
        Value::Term { id, .. } => Value::term(term(kb, *id)),
        Value::Entity {
            functor,
            pos,
            named,
        } => {
            let new_pos: Vec<Value> = pos
                .iter()
                .map(|v| rewrite_spec_value(kb, v, term))
                .collect();
            let new_named: Vec<(Symbol, Value)> = named
                .iter()
                .map(|(k, v)| (*k, rewrite_spec_value(kb, v, term)))
                .collect();
            Value::Entity {
                functor: *functor,
                pos: new_pos.into(),
                named: new_named.into(),
            }
        }
        other => other.clone(),
    }
}

/// The bare-name symbol of a `Ref(s)` or the nullary `Fn{s}` — the loader's alternative
/// encoding for a bare name (see WI-224's `substitute_impl_params_alloc`) — and NOT of an
/// `Ident`: the {`Ref`, nullary `Fn`} LEAF SET the two spec substitutions read (see
/// [`rewrite_term_leaves`] for why that set is theirs and not [`view_ref_symbol`]'s).
pub(super) fn ref_or_nullary_name(term: &Term) -> Option<Symbol> {
    match term {
        Term::Ref(s) => Some(*s),
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } if pos_args.is_empty() && named_args.is_empty() => Some(*functor),
        _ => None,
    }
}

/// WI-230 internal: substitution-aware deep walk. Replaces both
/// `Term::Ref(s)` AND nullary `Term::Fn(s, [], [])` (the loader's
/// alternative encoding for a bare name reference; see WI-224's
/// `substitute_impl_params_alloc`) where `s` is in `map` with the
/// mapped TermId. Recurses into non-nullary `Term::Fn` children.
/// Allocates fresh `Term::Fn` nodes only when a child was actually
/// rewritten (preserves hash-cons identity for unchanged sub-terms).
/// A denoted spec is walked carrier-faithfully ([`rewrite_spec_value`], WI-662 — the
/// WI-230 root-scope composition); `substitute_spec_via_subst` is the per-call-subst twin.
pub(super) fn substitute_in_spec(
    kb: &mut KnowledgeBase,
    spec: &Value,
    map: &HashMap<Symbol, TermId>,
) -> Value {
    if map.is_empty() {
        return spec.clone();
    }
    rewrite_spec_value(kb, spec, &|kb, t| {
        rewrite_term_leaves(kb, t, &|kb, t| {
            let s = ref_or_nullary_name(kb.get_term(t))?;
            Some(map.get(&s).copied().unwrap_or(t))
        })
    })
}

/// WI-230 internal: from an entry whose spec has already been
/// substituted to the current scope, build the substitution map to
/// pass into the entry's required_sort sub-tree. Maps each binding's
/// *qualified* param symbol (e.g. `anthill.prelude.Eq.T`) to its
/// substituted value, so the child's raw spec (which uses qualified
/// `Ref(Eq.T)`) translates one more level toward root scope.
pub(super) fn build_child_subst_map(
    kb: &KnowledgeBase,
    entry: &RequiresEntry,
) -> HashMap<Symbol, TermId> {
    let mut map = HashMap::new();
    let Some((base_sort, bindings)) = unwrap_spec_view_value(kb, &entry.spec) else {
        return map;
    };
    let base_qn = kb.qualified_name_of(base_sort).to_string();
    for (short_sym, value) in &bindings {
        let short_name = kb.local_name_of(*short_sym);
        let param_qn = format!("{base_qn}.{short_name}");
        if let Some(param_qualified) = kb.try_resolve_symbol(&param_qn) {
            map.insert(param_qualified, *value);
        }
    }
    map
}

/// Check if sort A refines sort B via `requires` chain.
pub(super) fn sort_refines(kb: &KnowledgeBase, a_sym: Symbol, b_sym: Symbol) -> bool {
    transitive_required_sorts(kb, a_sym)
        .into_iter()
        .any(|required| same_sort_canonical(kb, required, b_sym))
}

// ── Obligation checking ────────────────────────────────────────

/// A missing obligation: sort declares `requires` but doesn't provide an operation.
#[derive(Clone, Debug)]
pub struct MissingObligation {
    /// The sort that declared `requires`.
    pub sort_name: String,
    /// The required spec sort (e.g., "Eq").
    pub required_sort: String,
    /// The missing operation name.
    pub operation: String,
}

/// Check that all operations required by `requires` clauses are provided.
/// Returns a list of missing obligations.
pub fn check_obligations(kb: &KnowledgeBase, sort_sym: Symbol) -> Vec<MissingObligation> {
    let mut missing = Vec::new();
    let sort_name = kb.local_name_of(sort_sym).to_string();
    // One obligation per (required sort, operation): the sorts come deduplicated
    // (WI-20260923-N3W68 #8 — per chain ENTRY, the report's length followed cache warmth).
    let required = transitive_required_sorts(kb, sort_sym);

    // Collect operations provided by this sort
    let provided_ops = sort_operation_names(kb, sort_sym);

    for required_sort in required {
        // Get operations required by the spec sort
        let required_ops = sort_operation_names(kb, required_sort);
        let required_sort_name = kb.local_name_of(required_sort).to_string();

        for op in &required_ops {
            if !provided_ops.iter().any(|p| p == op) {
                missing.push(MissingObligation {
                    sort_name: sort_name.clone(),
                    required_sort: required_sort_name.clone(),
                    operation: op.clone(),
                });
            }
        }
    }

    missing
}

/// Get operation names defined in a sort (from SortInfo.operations): the `operations`
/// half of [`find_sort_info`], by local name — one SortInfo reader, not two.
fn sort_operation_names(kb: &KnowledgeBase, sort_sym: Symbol) -> Vec<String> {
    find_sort_info(kb, sort_sym).map_or_else(Vec::new, |(_, ops)| {
        ops.iter()
            .map(|op| kb.local_name_of(*op).to_string())
            .collect()
    })
}

/// The sort symbol of a BARE sort type — a nullary head, `Ref(S)` or the `Fn{S}` a
/// `SymbolKind::Sort` name keeps under the CZJ2N canon, both classified
/// [`TypeHead::SortRef`] by [`type_head`]. `None` for anything else: a parameterized or
/// structural type, a meta-constructor (`Nothing`), a variable.
///
/// NOT the deep `sort_ref(name: Ref(S))` wrapper, which this doc used to name and a comment
/// here claimed [`type_head`] reads as `SortRef` (WI-20260923-N3W68, stale docs): it reads
/// as `Parameterized { base: sort_ref }`, and nothing mints the form since the WI-361
/// producer flip (`KnowledgeBase::make_sort_ref` builds `Ref(S)`).
pub fn extract_sort_ref_sym<V: TermView>(kb: &KnowledgeBase, ty: &V) -> Option<Symbol> {
    // WI-342: carrier-agnostic over `TermView` (input principle) so a `Value`
    // sort type reads identically without re-grounding.
    match type_head(kb, ty) {
        TypeHead::SortRef(s) => Some(s),
        _ => None,
    }
}

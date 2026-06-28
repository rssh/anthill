/// Substitution — maps logic variables to runtime `Value`s.
///
/// Per proposal 026.1 Q1, bindings carry `Value` rather than raw `TermId`,
/// so the resolver and evaluator speak the same runtime representation.
/// `Value::Term(tid)` remains the dominant variant (facts / rule heads /
/// KB-resident data) and preserves O(1) structural equality via hash-consing
/// in the `TermStore`. Non-`Term` variants appear when the source is an
/// external-backed stream (`Value::Entity`), a literal in a rule body
/// (`Value::Int`, etc.), or an evaluator-bound value threaded through.
///
/// See: docs/stage0/rust-term-store-design.md §3.4, docs/proposals/026.1

use imbl::HashMap as ImHashMap;

use super::term::{Term, TermId, TermStore, Var, VarId};
use super::term_view::{views_structurally_equal, TermView};
use super::KnowledgeBase;
use crate::eval::value::Value;

/// WI-502 Step 1 — a tagged constraint on a logic variable, held in the
/// per-branch constraint store on [`Substitution`]. Generalizes the WI-328
/// `lacks` side-table into the constraint substrate of
/// `docs/design/constrained-term-substrate.md` (M2: *type is one kind of
/// constraint*). Each variant is a distinct constraint *kind*; the store keys a
/// `Vec<Constraint>` per variable, so a variable may carry several.
///
/// The answer generalizes `σ → (σ, residual C)` (M2): an undischarged
/// constraint here is a residual `C` in the answer, surfaced by
/// [`Substitution::residual_constraints`]. Lifetime is branch-scoped — the
/// store rides the per-frame `subst.clone()` exactly as `bindings`/`lacks`
/// always have (M7), now O(1) because the store is persistent (`imbl`,
/// WI-569 / Step 0).
#[derive(Clone, Debug)]
pub enum Constraint {
    /// Kind #1 (WI-328, proposal 045 §5.5 / §7.1) — an effect-row-tail `lacks`
    /// label: the variable (a row tail `ρ`) may never present this effect-type
    /// label, stored as a carrier-agnostic effect-type [`Value`] (a ground
    /// label is a `Value::Term`, a denoted-bearing one a `Value::Node`).
    Lacks(Value),
    /// Kind #2 (WI-502) — a residual type-constraint: a reified type-guard
    /// [`Value`] the variable's eventual binding must satisfy (e.g.
    /// `subsort(min_sort(?x), Numeric)`, `min_sort(?x) = T`, or a disequality —
    /// the decidable fragment of M2), carried carrier-agnostically like the
    /// answer's delayed `residual` goals. **Write-mostly:** no producer wires it
    /// (Step 3+ widens the typing boundary) and no consumer discharges it
    /// (Step 5 fires Shape-B guards) yet; Step 1 lands only the substrate.
    Type(Value),
}

#[derive(Clone, Debug)]
pub struct Substitution {
    /// WI-569: persistent (`imbl`) map — `Clone` is O(1) structural sharing,
    /// so the per-step `frame.subst.clone()` in the resolver no longer deep-copies
    /// the accumulated bindings (that copy was O(bindings) per step, i.e.
    /// O(depth × bindings) over a derivation). Same lookup/insert semantics as
    /// `std`, but the iteration ORDER differs (HAMT vs `RandomState`) and
    /// `iter_mut` is unavailable — see `bind_compressed`. Resolution does not
    /// depend on binding order: reads chase var-chains via `KnowledgeBase::walk`
    /// / `reify`, so a less-flattened chain still resolves identically.
    pub bindings: ImHashMap<VarId, Value>,
    pub parent: Option<Box<Substitution>>,
    /// Set to true when a variable is bound to two different concrete terms.
    pub contradiction: bool,
    /// WI-374: contradicting rebinds recorded for diagnostics — every
    /// conflicting `(prior, attempted)` pair, deduplicated by structurally
    /// equal `attempted` per var. Per-var completeness matters twice over: a
    /// single detail for the whole substitution would let a conflict on one
    /// var mask one on another, and a single detail PER var would let a
    /// benign first conflict (a `?_` wildcard pair) mask a later genuine one
    /// on the same var. Growth is bounded by distinct attempted values per
    /// var, and contradicted substitutions are discarded promptly on every
    /// consumer path. Empty on the happy path; direct `contradiction = true`
    /// writers record nothing (readers must tolerate an empty list with the
    /// flag set).
    pub contradiction_details: Vec<(VarId, Value, Value)>,
    /// WI-502 Step 1 — the per-branch **tagged constraint store** (see
    /// `docs/design/constrained-term-substrate.md`). Generalizes the WI-328
    /// `lacks` side-table: each [`Constraint`] is tagged by kind (`Lacks` #1,
    /// `Type` #2) and keyed by the (usually unbound) variable it constrains, so
    /// one variable may carry several constraints of mixed kinds.
    ///
    /// Persistent (`imbl`) so `Clone` is O(1) structural sharing — it rides the
    /// per-step `frame.subst.clone()` for free alongside `bindings` (WI-569 /
    /// Step 0), the prerequisite that keeps carrying a *growing* constraint
    /// store from re-introducing an O(depth × store) copy.
    ///
    /// Living on `Substitution` gives every constraint the same branch lifetime
    /// as a binding (M7): the snapshot/restore rollback (`subst.clone()` …
    /// `*subst = snapshot`) that WI-338's `pair_present_labels` /
    /// `cover_present_labels` already exercise discards a failed
    /// row-unification's tentative constraints, and a backtracked frame drops
    /// its branch-specific ones. The `lacks` accessors ([`Self::add_lacks`] /
    /// [`Self::lacks_of`]) are now thin views over the `Constraint::Lacks`
    /// entries of this store; once a tail binds, its `lacks` has already been
    /// checked against (and propagated through) the binding by
    /// [`crate::kb::typing`]'s `bind_row_tail`.
    pub constraints: ImHashMap<VarId, Vec<Constraint>>,
}

/// Push `c` onto a per-var constraint list, deduping a `Lacks` against an
/// existing scalar-equal `Lacks` (the only kind with a dedup story — see
/// [`Substitution::add_lacks`]). `Type` is never deduped (no dedup key yet; see
/// [`Substitution::add_type_constraint`]). Shared by every constraint-writing
/// path (`add_lacks`, `absorb_constraints`, merge-on-alias) so the dedup rule
/// lives in exactly one place.
fn push_constraint_deduped(entry: &mut Vec<Constraint>, c: Constraint) {
    if let Constraint::Lacks(l) = &c {
        if entry.iter().any(|e| matches!(e, Constraint::Lacks(x) if x.scalar_eq(l))) {
            return;
        }
    }
    entry.push(c);
}

/// WI-502 Step 2 — if `val` denotes a logic VARIABLE of kind `Global`, return
/// its `VarId`. Used by merge-on-alias: binding `?x := ?y` aliases the two, so
/// `?x`'s constraints must follow onto `?y`.
///
/// Delegates to the canonical carrier-agnostic var extractor
/// (`TermView::index_var`) so EVERY variable carrier is recognized — not only
/// `Value::Var(Global)` and `Value::Term(Var::Global)` but also a var riding as
/// `Value::Node(Expr::Var(Global))`, which fact-match `tree_subst` non-`Term`
/// bindings actually carry; a bespoke `Var`/`Term`-only match would silently
/// mis-read that as concrete and drop the wakeup (the "loud over silent"
/// failure mode). A non-variable value (a constructed term, a scalar) and a
/// Rigid/DeBruijn var both return `None`: a rigid/DeBruijn var is not an alias
/// target here, its constraints are enforced at its own instantiation site
/// (the same conservatism as the typer's row machinery).
fn value_as_global_var(kb: &KnowledgeBase, val: &Value) -> Option<VarId> {
    match val.index_var(kb) {
        Some(Var::Global(vid)) => Some(vid),
        _ => None,
    }
}

impl Substitution {
    pub fn new() -> Self {
        Self {
            bindings: ImHashMap::new(),
            parent: None,
            contradiction: false,
            contradiction_details: Vec::new(),
            constraints: ImHashMap::new(),
        }
    }

    pub fn with_parent(parent: Substitution) -> Self {
        Self {
            bindings: ImHashMap::new(),
            parent: Some(Box::new(parent)),
            contradiction: false,
            contradiction_details: Vec::new(),
            constraints: ImHashMap::new(),
        }
    }

    /// Covering resolve: returns any binding as a `Value` — the
    /// `Value::Term(tid)` variant (the dominant KB-resident case) and the
    /// non-`Term` variants produced by external stream sources, rule-body
    /// literals, or a denoted/occurrence answer (`Value::Node`). The single
    /// substitution reader (WI-348 retired the term-only `resolve_with_term`,
    /// which silently dropped non-`Term` bindings); a caller that genuinely
    /// needs a `TermId` narrows explicitly at the site (`if let
    /// Some(Value::Term(t)) = …`), so a non-`Term` binding is consciously
    /// handled, not silently erased (WI-477 removed the blanket `Value::as_term`
    /// downgrade for the same reason).
    pub fn resolve_as_value(&self, var: VarId) -> Option<&Value> {
        if let Some(v) = self.bindings.get(&var) {
            return Some(v);
        }
        if let Some(ref parent) = self.parent {
            return parent.resolve_as_value(var);
        }
        None
    }

    /// Bind a variable to a `TermId` — the dominant resolver path. Wraps
    /// the `TermId` as `Value::Term(tid)` for storage. If the variable is
    /// already bound to a different concrete term, marks the substitution
    /// as contradictory.
    pub fn bind_term(&mut self, kb: &KnowledgeBase, var: VarId, term: TermId) {
        if let Some(existing) = self.bindings.get(&var) {
            let consistent = match existing {
                // Both hash-consed terms: structural equality IS `TermId` identity
                // (the store dedups by structure), so a `u32` compare is exact AND
                // skips decoding two possibly-deep terms on the conflict path.
                Value::Term { id: t, .. } => *t == term,
                // WI-486: cross-carrier re-bind — an existing `Value::Node`/`Entity`
                // structurally equal to `term` (same logical value, different
                // carrier) is consistent, not a conflict. Decide via the
                // carrier-aware comparator, NOT the carrier-blind `==` that would
                // false-flag the cross-carrier-equal case.
                _ => views_structurally_equal(kb, existing, &Value::term(term)),
            };
            if consistent {
                return;
            }
            // Record every DISTINCT conflict per var (an identical repeat records
            // nothing); see the field doc for why first-per-var is not enough.
            let attempted = Value::term(term);
            if !self
                .contradiction_details
                .iter()
                .any(|(v, _, a)| *v == var && views_structurally_equal(kb, a, &attempted))
            {
                let prior = existing.clone();
                self.contradiction_details.push((var, prior, attempted));
            }
            self.contradiction = true;
            return;
        }
        self.bindings.insert(var, Value::term(term));
    }

    /// Bind a variable to a runtime `Value`. Used when the source is not
    /// KB-resident: external stream rows, interpreter-evaluated values, or
    /// literals decoded from rule bodies. Preserves lineage — an incoming
    /// `Value::Entity` stays as such rather than being promoted to
    /// `Value::Term` via `TermStore::alloc`.
    pub fn bind_value(&mut self, kb: &KnowledgeBase, var: VarId, val: Value) {
        if let Some(existing) = self.bindings.get(&var) {
            // WI-486: carrier-aware structural compare — a `Value::Term` existing
            // and a structurally-equal `Value::Node`/`Entity` incoming (or vice
            // versa) are the same logical value, not a contradiction. The blind
            // `Value::structural_eq` returned `false` on every cross-carrier pair.
            // Two hash-consed terms fast-path to a `TermId` compare (exact, no decode).
            let consistent = match (existing, &val) {
                (Value::Term { id: a, .. }, Value::Term { id: b, .. }) => a == b,
                _ => views_structurally_equal(kb, existing, &val),
            };
            if !consistent {
                // Every distinct conflict per var — see `bind_term`.
                if !self
                    .contradiction_details
                    .iter()
                    .any(|(v, _, a)| *v == var && views_structurally_equal(kb, a, &val))
                {
                    let prior = existing.clone();
                    self.contradiction_details.push((var, prior, val));
                }
                self.contradiction = true;
            }
            return;
        }
        self.bindings.insert(var, val);
    }

    /// Legacy alias for `bind_term`. New code should prefer the explicit
    /// name to make the fast-path vs. value-path choice visible.
    #[inline]
    pub fn bind(&mut self, kb: &KnowledgeBase, var: VarId, term: TermId) {
        self.bind_term(kb, var, term);
    }

    /// Whether this substitution contains a contradiction
    /// (a variable bound to two different concrete terms).
    pub fn is_contradiction(&self) -> bool {
        self.contradiction
    }

    /// Whether the substitution holds no bindings, walking the parent chain.
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
            && self.parent.as_ref().is_none_or(|p| p.is_empty())
    }

    /// Add bindings with path compression in one operation. Operates over
    /// the `Value::Term` subset — non-`Term` entries are never
    /// path-compression sources or targets. Mixed bindings are left
    /// untouched (their walker, if ever needed, handles them structurally).
    ///
    /// For each `(vid, term)` in `new_bindings`:
    /// 1. Scan existing `Value::Term` entries: any `?w → Var(vid)` becomes
    ///    `?w → term`.
    /// 2. Insert `vid → term`.
    pub fn bind_compressed<I>(&mut self, new_bindings: I, terms: &TermStore)
    where
        I: IntoIterator<Item = (VarId, TermId)>,
    {
        // WI-502 Step 2 — loud-on-bypass. `bind_compressed` is the synthetic
        // path-compression path (resolver-only: fresh DeBruijn / answer-link
        // vars getting their first concrete binding). A constraint-carrying var
        // must NEVER bind here — it has to route through `bind_waking` so its
        // constraints wake (M7(a)). If one reaches here it is a routing bug;
        // fail LOUDLY rather than silently drop the wakeup. Gated on a non-empty
        // store so the universal (empty) case pays only one O(1) check.
        let guard = !self.constraints.is_empty();
        for (vid, term) in new_bindings {
            // Path compression. `imbl` is immutable (no `iter_mut`), so collect
            // the existing `?w → Var(vid)` entries, then functionally re-point
            // each to `term`. The fold of `insert`s shares structure, keeping
            // `clone` O(1); the per-new-binding scan is the same O(n) as before.
            let to_repoint: Vec<VarId> = self
                .bindings
                .iter()
                .filter_map(|(w, existing)| match existing {
                    Value::Term { id: existing_tid, .. } => match terms.get(*existing_tid) {
                        Term::Var(Var::Global(ev)) if *ev == vid => Some(*w),
                        _ => None,
                    },
                    _ => None,
                })
                .collect();
            for w in to_repoint {
                if guard {
                    self.assert_no_constraints(w, "bind_compressed path-compression repoint");
                }
                self.bindings.insert(w, Value::term(term));
            }
            if guard {
                self.assert_no_constraints(vid, "bind_compressed direct bind");
            }
            self.bindings.insert(vid, Value::term(term));
        }
    }

    /// WI-502 Step 2 — loud-on-bypass guard: panic if `var` carries a constraint
    /// that the caller is about to silently drop by binding it on a non-waking
    /// path. Constrained binds must route through [`Self::bind_waking`].
    fn assert_no_constraints(&self, var: VarId, site: &str) {
        assert!(
            !self.constraints.contains_key(&var),
            "WI-502: {site} bound constraint-carrying var {var:?}; route it \
             through bind_waking so its constraints wake (loud-on-bypass, M7(a))",
        );
    }

    /// WI-328 — record `lacks` labels (kind #1) on a row-tail variable, as
    /// `Constraint::Lacks` entries in the unified store. The labels are
    /// effect-type [`Value`]s the tail `var` may never present. Order is not
    /// significant (a row is a set).
    ///
    /// WI-342 P4-B: `Value` has no `PartialEq`, so dedup is best-effort —
    /// ground labels (`Value::Term`, the only label form today) dedup by
    /// `TermId` via `scalar_eq`, preserving the pre-P4 bound on a tail's lacks
    /// set (important: `bind_row_tail` propagates the whole parent-chain union
    /// onto each fresh continuation, so un-deduped ground labels would
    /// accumulate superlinearly across open-row chains). A `Value::Node` label
    /// has no structural `Eq` here and is always pushed — harmless
    /// (`label_violates_lacks` is idempotent), and not yet reachable (no
    /// producer mints denoted-bearing absents into a tail). Dedup is against
    /// THIS level's `Lacks` entries only (matching the pre-WI-502
    /// `self.lacks.entry(var)` semantics; cross-level union is `lacks_of`'s job).
    pub fn add_lacks<I>(&mut self, var: VarId, labels: I)
    where
        I: IntoIterator<Item = Value>,
    {
        // `imbl`'s `entry` copy-on-writes internally (path-copies a shared node
        // before handing out `&mut`), so we push IN PLACE — no explicit `Vec`
        // clone — while a prior `subst.clone()` stays isolated (the M7
        // snapshot/restore invariant; `constraint_store_clone_is_isolated`
        // guards it). Mirrors the pre-WI-502 `self.lacks.entry(var).or_default()`.
        let entry = self.constraints.entry(var).or_default();
        for l in labels {
            // Dedup carrier-agnostically via `Value::scalar_eq` against existing
            // `Lacks` entries (ground labels by `TermId`; `Value::Node` has no
            // structural `Eq` → always pushed, harmless).
            push_constraint_deduped(entry, Constraint::Lacks(l));
        }
    }

    /// WI-328 — the full `lacks` set on a row-tail variable: the `Value` labels
    /// of this level's `Constraint::Lacks` entries, unioned across the parent
    /// chain (a tail's constraints may have been recorded in an ancestor before
    /// a child was forked). Returns an owned `Vec` since the union may span
    /// levels; callers iterate it read-only. (WI-342 P4-B: no dedup across
    /// levels — see [`Self::add_lacks`].)
    pub fn lacks_of(&self, var: VarId) -> Vec<Value> {
        let mut out: Vec<Value> = self
            .constraints
            .get(&var)
            .map(|cs| {
                cs.iter()
                    .filter_map(|c| match c {
                        Constraint::Lacks(v) => Some(v.clone()),
                        Constraint::Type(_) => None,
                    })
                    .collect()
            })
            .unwrap_or_default();
        if let Some(ref parent) = self.parent {
            out.extend(parent.lacks_of(var));
        }
        out
    }

    /// WI-502 Step 1 — record a residual type-constraint (kind #2) on `var`:
    /// the reified type-guard [`Value`] `guard` (e.g. `subsort(min_sort(?x),
    /// Numeric)`) that `var`'s eventual binding must satisfy. The kind-#2
    /// parallel to [`Self::add_lacks`], writing a `Constraint::Type`.
    ///
    /// **Write-mostly** (M2 / Step 1): the substrate carries the constraint;
    /// no producer mints one (Step 3+ widens the typing boundary) and no
    /// consumer discharges it (Step 5 fires Shape-B guards) yet. No dedup —
    /// unlike `lacks` there is no propagation loop to bound the set, and
    /// committing to a dedup key now would prejudge the future guard shape.
    pub fn add_type_constraint(&mut self, var: VarId, guard: Value) {
        // In-place push via `imbl`'s copy-on-write `entry` (see `add_lacks`).
        self.constraints
            .entry(var)
            .or_default()
            .push(Constraint::Type(guard));
    }

    /// WI-502 Step 3 — the `Type` constraint payloads recorded on `var`, unioned
    /// across the parent chain (the kind-#2 read dual of [`Self::lacks_of`]).
    /// The value-level type reader (`var_type_term`, in `typed`) reads these as the
    /// store-fallback for an unbound-but-constrained var. Owned `Vec` since the
    /// union spans levels.
    pub fn type_constraints_of(&self, var: VarId) -> Vec<Value> {
        let mut out: Vec<Value> = self
            .constraints
            .get(&var)
            .map(|cs| {
                cs.iter()
                    .filter_map(|c| match c {
                        Constraint::Type(v) => Some(v.clone()),
                        Constraint::Lacks(_) => None,
                    })
                    .collect()
            })
            .unwrap_or_default();
        if let Some(ref parent) = self.parent {
            out.extend(parent.type_constraints_of(var));
        }
        out
    }

    /// WI-502 Step 2 — union another substitution's TOP-LEVEL constraint store
    /// into this one (M7(b): carry the store through a merge). The resolver's
    /// `SuccessWithBindings` lift and the reflect `compose` ops build a result
    /// from another subst's *bindings* and previously dropped its constraints
    /// silently; this carries them. **Top-level only**, deliberately: like the
    /// lift that threads `extra.bindings` and ignores `extra.parent` (the parent
    /// σ's constraints already live in the destination), the parent chain is not
    /// descended. Dedup follows [`push_constraint_deduped`] against the
    /// destination's TOP LEVEL only — sufficient, and unable to re-introduce a
    /// cross-level duplicate `Lacks`, because every wired destination is a *flat*
    /// (parent-free) subst: the resolver lift's `frame.subst.clone()` (hot-path
    /// frame substs are always `parent = None`) and the reflect compose's fresh
    /// `Substitution::new()`. A parented destination would need `lacks_of`-style
    /// chain dedup; none is wired.
    pub fn absorb_constraints(&mut self, other: &Substitution) {
        for (var, cs) in other.constraints.iter() {
            let entry = self.constraints.entry(*var).or_default();
            for c in cs {
                push_constraint_deduped(entry, c.clone());
            }
        }
    }

    /// WI-502 Step 2 — the constraint-waking bind choke-point. Binds `var := val`
    /// and **wakes** any constraints carried on `var` (M5: explicit wakeup, no
    /// attributed-variable cells; M7(a): the gap `bind_compressed` leaves open).
    /// The resolver-side analog of the typer's `bind_row_tail`: a site that may
    /// bind a constraint-carrying var routes through HERE so the constraint is
    /// never silently dropped. Constraint-FREE binds may use the raw
    /// `bind_value`/`bind_compressed` directly (cheaper) — and `bind_compressed`
    /// asserts loudly if a constrained var reaches it (loud-on-bypass).
    ///
    /// The store is almost always empty (no resolver-side producer until Step 3),
    /// so the `is_empty` gate makes this exactly `bind_value` on the hot path.
    pub fn bind_waking(&mut self, kb: &KnowledgeBase, var: VarId, val: Value) {
        if !self.constraints.contains_key(&var) {
            // Fast path: this var carries no constraints — exactly `bind_value`,
            // and no `val` clone. O(1) on the persistent map; this is the
            // universal case (no resolver-side producer until Step 3), even when
            // the store holds constraints on *other* vars.
            self.bind_value(kb, var, val);
            return;
        }
        // (Step 5 inserts the per-kind CHECK *here*, BEFORE the commit, with
        // reject power: a `Type` guard that `val` violates fails the bind; an
        // under-determined guard suspends as residual `C`. Step 2 has no check.)
        self.bind_value(kb, var, val.clone());
        // Propagate (merge-on-alias) only on a LIVE branch. A contradicting bind
        // poisons the subst and the branch is discarded, so moving constraints
        // would be wasted work on a doomed branch — and the move is destructive
        // (`remove` then re-`insert`), so skipping it leaves the contradicted
        // store untouched. Closes the "move-before-bind not discarded on
        // contradiction" gap.
        if !self.contradiction {
            self.wake_constraints(kb, var, &val);
        }
    }

    /// Wake the constraints carried on `var` against the value it is about to be
    /// bound to. Step 2 implements the generic, kind-agnostic action —
    /// **merge-on-alias**: binding `var := ?y` (a variable) MOVES var's
    /// constraints onto the alias `?y` so they follow the union chain (one hop
    /// per bind; the next hop wakes when `?y` itself binds).
    ///
    /// The per-kind CHECK (does a CONCRETE `val` satisfy the constraint?) is
    /// staged elsewhere and is a deliberate no-op here:
    /// - `Type` → Step 5 (`subsort(min_sort(val), T)`, suspend if
    ///   under-determined — the WI-067 var_ref-non-ground hazard one level up).
    /// - `Lacks` → the typer's `bind_row_tail`, whose check needs effect-row
    ///   decomposition vocabulary not available in `subst.rs`.
    ///
    /// So a constraint reaching a CONCRETE bind here is carried inert for now
    /// (Step 5 fills the `Type` check). This is NOT a silent skip of a handled
    /// case: there is no resolver-side constraint producer yet (Step 3), so the
    /// concrete-bind path is exercised only by tests until then.
    fn wake_constraints(&mut self, kb: &KnowledgeBase, var: VarId, val: &Value) {
        if !self.constraints.contains_key(&var) {
            return;
        }
        match value_as_global_var(kb, val) {
            // Merge-on-alias: `var := ?y` with `?y` an UNBOUND variable moves
            // var's constraints onto `?y` so they ride the union chain (the next
            // hop wakes when `?y` itself binds). Guard on `?y` unbound: moving
            // onto an already-bound `?y` would be pointless (it never binds
            // again), so leave them on `var` instead — `residual_constraints`
            // still surfaces them and Step 5 derefs `var` to its representative
            // value for the per-kind CHECK.
            Some(alias) if alias != var && self.resolve_as_value(alias).is_none() => {
                if let Some(cs) = self.constraints.remove(&var) {
                    let entry = self.constraints.entry(alias).or_default();
                    for c in cs {
                        push_constraint_deduped(entry, c);
                    }
                }
            }
            // Carry inert: a concrete bind, a self-alias, or a bound alias. The
            // constraint stays recorded on `var` (NOT dropped) for Step 5's
            // deref-and-check; the per-kind CHECK is staged (Type → Step 5,
            // Lacks → the typer's bind_row_tail).
            _ => {}
        }
    }

    /// WI-502 Step 1 — the residual constraints `C` carried by this
    /// substitution and its parent chain, as `(VarId, Constraint)` pairs. The
    /// answer generalizes `σ → (σ, residual C)` (M2); this surfaces the `C`.
    /// Both kinds are returned (a consumer filters by variant — `Lacks` for the
    /// effect machinery, `Type` for type-directed firing). **No consumer reads
    /// it yet** (Step 1 is write-mostly); it makes the answer *able* to carry
    /// `C`. Owned `Vec` since the union spans the parent chain.
    pub fn residual_constraints(&self) -> Vec<(VarId, Constraint)> {
        let mut out: Vec<(VarId, Constraint)> = self
            .constraints
            .iter()
            .flat_map(|(v, cs)| cs.iter().map(move |c| (*v, c.clone())))
            .collect();
        if let Some(ref parent) = self.parent {
            out.extend(parent.residual_constraints());
        }
        out
    }

    /// Iterate over all bindings. Yields `(VarId, Value)` references;
    /// callers that only care about `Value::Term` entries should filter.
    pub fn iter(&self) -> impl Iterator<Item = (&VarId, &Value)> {
        self.bindings.iter()
    }

    /// Iterate over only the `Value::Term` bindings, yielding
    /// `(VarId, TermId)` — the ergonomic form for resolver-internal code
    /// that wants to stay in the TermId world.
    pub fn iter_terms(&self) -> impl Iterator<Item = (VarId, TermId)> + '_ {
        self.bindings.iter().filter_map(|(v, val)| match val {
            Value::Term { id: tid, .. } => Some((*v, *tid)),
            _ => None,
        })
    }
}

impl Default for Substitution {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intern::Symbol;
    use crate::kb::term::Literal;

    fn vid(id: u32) -> VarId {
        VarId::new(id, Symbol::from_raw(0))
    }

    #[test]
    fn bind_term_roundtrips_as_value_term() {
        let mut s = Substitution::new();
        let kb = KnowledgeBase::new();
        let v = vid(1);
        let t = TermId::from_raw(42);
        s.bind_term(&kb, v, t);
        assert_eq!(s.resolve_as_value(v).map(|v| v.expect_term()), Some(t));
        match s.resolve_as_value(v) {
            Some(Value::Term { id: tid, .. }) => assert_eq!(*tid, t),
            other => panic!("expected Value::Term, got {other:?}"),
        }
    }

    #[test]
    fn bind_value_accepts_non_term() {
        let mut s = Substitution::new();
        let kb = KnowledgeBase::new();
        let v = vid(1);
        s.bind_value(&kb, v, Value::Int(42));
        // resolve (TermId-only path) returns None for non-Term bindings.
        assert!(!matches!(s.resolve_as_value(v), Some(Value::Term { .. })));
        // lookup surfaces the full Value.
        match s.resolve_as_value(v) {
            Some(Value::Int(42)) => {}
            other => panic!("expected Value::Int(42), got {other:?}"),
        }
    }

    #[test]
    fn bind_twice_same_term_is_not_contradiction() {
        let mut s = Substitution::new();
        let kb = KnowledgeBase::new();
        let v = vid(1);
        let t = TermId::from_raw(7);
        s.bind_term(&kb, v, t);
        s.bind_term(&kb, v, t);
        assert!(!s.is_contradiction());
    }

    #[test]
    fn bind_twice_different_term_is_contradiction() {
        let mut kb = KnowledgeBase::new();
        let mut s = Substitution::new();
        let v = vid(1);
        // WI-486: the contradiction check now decodes the terms (carrier-aware),
        // so use REAL distinct hash-consed terms rather than opaque raw ids.
        let t1 = kb.alloc(Term::Const(Literal::Int(1)));
        let t2 = kb.alloc(Term::Const(Literal::Int(2)));
        s.bind_term(&kb, v, t1);
        s.bind_term(&kb, v, t2);
        assert!(s.is_contradiction());
    }

    #[test]
    fn bind_term_then_value_is_contradiction_when_distinct() {
        let mut kb = KnowledgeBase::new();
        let mut s = Substitution::new();
        let v = vid(1);
        let t1 = kb.alloc(Term::Const(Literal::Int(1)));
        s.bind_term(&kb, v, t1);
        // WI-486: a Term and a structurally-DISTINCT non-Term value still
        // conflict (Term `Int(1)` vs scalar `Int(99)`). NB WI-486 also made a
        // Term and a structurally-EQUAL non-Term compare equal — see the
        // typing-side `bind_value_structural_eq_no_false_contradiction` test.
        s.bind_value(&kb, v, Value::Int(99));
        assert!(s.is_contradiction());
    }

    #[test]
    fn bind_value_equal_scalar_not_contradiction() {
        let mut s = Substitution::new();
        let kb = KnowledgeBase::new();
        let v = vid(1);
        s.bind_value(&kb, v, Value::Int(42));
        s.bind_value(&kb, v, Value::Int(42));
        assert!(!s.is_contradiction());
    }

    #[test]
    fn lookup_walks_parent_chain() {
        let mut parent = Substitution::new();
        let kb = KnowledgeBase::new();
        parent.bind_term(&kb, vid(1), TermId::from_raw(10));
        let child = Substitution::with_parent(parent);
        assert_eq!(child.resolve_as_value(vid(1)).map(|v| v.expect_term()), Some(TermId::from_raw(10)));
        matches!(child.resolve_as_value(vid(1)), Some(Value::Term { .. }));
    }

    #[test]
    fn iter_terms_filters_out_non_term_values() {
        let mut s = Substitution::new();
        let kb = KnowledgeBase::new();
        s.bind_term(&kb, vid(1), TermId::from_raw(100));
        s.bind_value(&kb, vid(2), Value::Int(42));
        s.bind_term(&kb, vid(3), TermId::from_raw(300));
        let pairs: Vec<(VarId, TermId)> = s.iter_terms().collect();
        assert_eq!(pairs.len(), 2);
        // Sort for deterministic compare (HashMap iter order isn't stable).
        let mut raws: Vec<u32> = pairs.iter().map(|(v, _)| v.raw()).collect();
        raws.sort();
        assert_eq!(raws, vec![1, 3]);
    }

    #[test]
    fn bind_value_stores_structured_entity() {
        let mut s = Substitution::new();
        let kb = KnowledgeBase::new();
        let v = vid(1);
        let functor = Symbol::from_raw(7);
        let key = Symbol::from_raw(8);
        let entity = Value::Entity {
            functor,
            pos: vec![Value::Int(10), Value::Str("hi".into())].into(),
            named: vec![(key, Value::Bool(true))].into(),
            ty: None,
        };
        s.bind_value(&kb, v, entity);
        assert!(!matches!(s.resolve_as_value(v), Some(Value::Term { .. })));
        match s.resolve_as_value(v) {
            Some(Value::Entity { functor: f, pos, named, .. }) => {
                assert_eq!(*f, functor);
                assert!(matches!(&pos[..], [Value::Int(10), Value::Str(_)]));
                assert_eq!(named.len(), 1);
                assert_eq!(named[0].0, key);
                assert!(matches!(named[0].1, Value::Bool(true)));
            }
            other => panic!("expected Value::Entity, got {other:?}"),
        }
    }

    #[test]
    fn bind_value_stores_structured_tuple() {
        let mut s = Substitution::new();
        let kb = KnowledgeBase::new();
        let v = vid(1);
        let tuple = Value::Tuple {
            pos: vec![Value::Int(1), Value::Int(2), Value::Int(3)].into(),
            named: vec![].into(),
            ty: None,
        };
        s.bind_value(&kb, v, tuple);
        assert!(!matches!(s.resolve_as_value(v), Some(Value::Term { .. })));
        match s.resolve_as_value(v) {
            Some(Value::Tuple { pos, named, .. }) => {
                assert_eq!(pos.len(), 3);
                assert!(named.is_empty());
            }
            other => panic!("expected Value::Tuple, got {other:?}"),
        }
    }

    #[test]
    fn bind_value_equal_entity_not_contradiction() {
        let mut s = Substitution::new();
        let kb = KnowledgeBase::new();
        let v = vid(1);
        let make_entity = || Value::Entity {
            functor: Symbol::from_raw(7),
            pos: vec![Value::Int(10), Value::Str("hi".into())].into(),
            named: vec![(Symbol::from_raw(8), Value::Bool(true))].into(),
            ty: None,
        };
        s.bind_value(&kb, v, make_entity());
        s.bind_value(&kb, v, make_entity());
        assert!(!s.is_contradiction());
    }

    #[test]
    fn bind_value_different_entity_is_contradiction() {
        let mut s = Substitution::new();
        let kb = KnowledgeBase::new();
        let v = vid(1);
        s.bind_value(&kb, 
            v,
            Value::Entity {
                functor: Symbol::from_raw(7),
                pos: vec![Value::Int(10)].into(),
                named: vec![].into(),
                ty: None,
            },
        );
        s.bind_value(&kb,
            v,
            Value::Entity {
                functor: Symbol::from_raw(7),
                pos: vec![Value::Int(11)].into(),
                named: vec![].into(),
                ty: None,
            },
        );
        assert!(s.is_contradiction());
    }

    /// WI-486 — the core cross-carrier fix. Binding a var once as a hash-consed
    /// `Value::Term` and once as the structurally-EQUAL `Value::Entity` (the same
    /// logical value in two carriers) must NOT be a contradiction. Before WI-486
    /// the carrier-blind `Value::structural_eq` returned `false` on the
    /// `(Term, Entity)` pair, so this consistent rebind was wrongly flagged as a
    /// conflict (and a downstream WI-512 consumer would drop the substitution).
    #[test]
    fn bind_cross_carrier_equal_term_and_entity_not_contradiction() {
        let mut kb = KnowledgeBase::new();
        let v = vid(1);
        let foo = kb.intern("foo");
        let entity = Value::Entity {
            functor: foo,
            pos: vec![Value::Int(1)].into(),
            named: vec![].into(),
            ty: None,
        };
        // The faithful Term form of `entity` — same structure, `Term` carrier.
        let t = crate::kb::node_occurrence::value_to_term(&mut kb, &entity).unwrap();
        let mut s = Substitution::new();
        s.bind_term(&kb, v, t);
        s.bind_value(&kb, v, entity);
        assert!(
            !s.is_contradiction(),
            "a Term and its structurally-equal Entity twin must agree across carriers",
        );
    }

    /// WI-486 negative peer: structurally DISTINCT values still conflict across
    /// carriers (`foo(1)` as a `Term` vs `foo(2)` as an `Entity`).
    #[test]
    fn bind_cross_carrier_distinct_term_and_entity_is_contradiction() {
        let mut kb = KnowledgeBase::new();
        let v = vid(1);
        let foo = kb.intern("foo");
        let one =
            Value::Entity { functor: foo, pos: vec![Value::Int(1)].into(), named: vec![].into(), ty: None };
        let two =
            Value::Entity { functor: foo, pos: vec![Value::Int(2)].into(), named: vec![].into(), ty: None };
        let t1 = crate::kb::node_occurrence::value_to_term(&mut kb, &one).unwrap();
        let mut s = Substitution::new();
        s.bind_term(&kb, v, t1);
        s.bind_value(&kb, v, two);
        assert!(s.is_contradiction());
    }

    #[test]
    fn bind_value_nested_entity_equal_not_contradiction() {
        let mut s = Substitution::new();
        let kb = KnowledgeBase::new();
        let v = vid(1);
        let make = || Value::Entity {
            functor: Symbol::from_raw(7),
            pos: vec![Value::Tuple {
                pos: vec![Value::Int(1), Value::Str("x".into())].into(),
                named: vec![].into(),
                ty: None,
            }].into(),
            named: vec![].into(),
            ty: None,
        };
        s.bind_value(&kb, v, make());
        s.bind_value(&kb, v, make());
        assert!(!s.is_contradiction());
    }

    // ── WI-502 Step 1: tagged constraint store ──────────────────────

    /// `lacks` (kind #1) and a type-constraint (kind #2) coexist on the same
    /// variable in the unified store; each read view sees only its own kind.
    #[test]
    fn lacks_and_type_share_one_store() {
        let mut s = Substitution::new();
        let v = vid(1);
        s.add_lacks(v, [Value::Int(7)]);
        s.add_type_constraint(v, Value::Str("subsort(min_sort(x), Numeric)".into()));

        // lacks_of surfaces only the Lacks label, not the Type guard.
        let lacks = s.lacks_of(v);
        assert_eq!(lacks.len(), 1);
        assert!(lacks[0].scalar_eq(&Value::Int(7)));

        // residual_constraints surfaces both kinds.
        let residual = s.residual_constraints();
        assert_eq!(residual.len(), 2);
        assert_eq!(residual.iter().filter(|(_, c)| matches!(c, Constraint::Lacks(_))).count(), 1);
        assert_eq!(residual.iter().filter(|(_, c)| matches!(c, Constraint::Type(_))).count(), 1);
    }

    /// `add_lacks` dedups within a level (behavior preserved through the store
    /// migration); a repeated ground label is recorded once.
    #[test]
    fn add_lacks_dedups_within_level() {
        let mut s = Substitution::new();
        let v = vid(1);
        s.add_lacks(v, [Value::Int(5)]);
        s.add_lacks(v, [Value::Int(5)]); // duplicate
        s.add_lacks(v, [Value::Int(9)]);
        let lacks = s.lacks_of(v);
        assert_eq!(lacks.len(), 2, "duplicate ground label must dedup");
    }

    /// `lacks_of` unions across the parent chain without dedup across levels
    /// (behavior preserved); `residual_constraints` likewise spans the chain.
    #[test]
    fn lacks_and_residual_union_parent_chain() {
        let mut parent = Substitution::new();
        let v = vid(1);
        parent.add_lacks(v, [Value::Int(1)]);
        let mut child = Substitution::with_parent(parent);
        child.add_lacks(v, [Value::Int(1)]); // same label, different level → NOT deduped
        child.add_type_constraint(v, Value::Int(2));

        // Cross-level union: two Int(1) lacks (one per level).
        assert_eq!(child.lacks_of(v).len(), 2);
        // residual spans the chain: 2 lacks + 1 type = 3.
        assert_eq!(child.residual_constraints().len(), 3);
    }

    /// The constraint store is persistent: a clone taken before adding a
    /// constraint does not observe the later write (branch isolation, the
    /// snapshot/restore rollback M7 relies on).
    #[test]
    fn constraint_store_clone_is_isolated() {
        let mut s = Substitution::new();
        let v = vid(1);
        s.add_lacks(v, [Value::Int(1)]);
        let snapshot = s.clone();
        s.add_type_constraint(v, Value::Int(2));
        // The snapshot keeps only the pre-clone lacks; the live subst has both.
        assert_eq!(snapshot.residual_constraints().len(), 1);
        assert_eq!(s.residual_constraints().len(), 2);
    }

    // ── WI-502 Step 2: carry + wakeup in the bind path ──────────────

    /// Merge-on-alias via a value-level `Value::Var`: binding `?x := ?y` MOVES
    /// `?x`'s constraints onto `?y` (they follow the union chain).
    #[test]
    fn bind_waking_merges_constraints_on_var_alias() {
        let kb = KnowledgeBase::new();
        let mut s = Substitution::new();
        let (x, y) = (vid(1), vid(2));
        s.add_type_constraint(x, Value::Int(7));
        s.bind_waking(&kb, x, Value::Var(Var::Global(y)));
        assert!(s.constraints.get(&x).is_none(), "x's constraints must move to the alias");
        let resid = s.residual_constraints();
        assert_eq!(resid.len(), 1);
        assert_eq!(resid[0].0, y);
        assert!(matches!(resid[0].1, Constraint::Type(_)));
    }

    /// Merge-on-alias via a `Value::Term` carrying a `Var::Global` (the resolver's
    /// usual variable carrier) — same move semantics.
    #[test]
    fn bind_waking_merges_on_term_var_alias() {
        let mut kb = KnowledgeBase::new();
        let (x, y) = (vid(1), vid(2));
        let y_term = kb.alloc(Term::Var(Var::Global(y)));
        let mut s = Substitution::new();
        s.add_lacks(x, [Value::Int(5)]);
        s.bind_waking(&kb, x, Value::term(y_term));
        assert!(s.constraints.get(&x).is_none());
        let resid = s.residual_constraints();
        assert_eq!(resid.len(), 1);
        assert_eq!(resid[0].0, y);
        assert!(matches!(resid[0].1, Constraint::Lacks(_)));
    }

    /// A CONCRETE bind carries the constraint inert (no alias to move to; the
    /// per-kind check is staged to Step 5). The constraint stays recorded — it
    /// is NOT silently dropped.
    #[test]
    fn bind_waking_concrete_carries_inert() {
        let kb = KnowledgeBase::new();
        let mut s = Substitution::new();
        let x = vid(1);
        s.add_type_constraint(x, Value::Int(7));
        s.bind_waking(&kb, x, Value::Int(99));
        let resid = s.residual_constraints();
        assert_eq!(resid.len(), 1, "concrete bind must carry the constraint, not drop it");
        assert_eq!(resid[0].0, x);
    }

    /// A contradicting bind (var already bound to a distinct value) must NOT
    /// move constraints onto the alias: the branch is doomed (discarded) and the
    /// move is destructive, so `bind_waking` skips the wake when `bind_value`
    /// flagged a contradiction.
    #[test]
    fn bind_waking_does_not_move_on_contradiction() {
        let kb = KnowledgeBase::new();
        let mut s = Substitution::new();
        let (x, y) = (vid(1), vid(2));
        s.add_type_constraint(x, Value::Int(7));
        s.bind_value(&kb, x, Value::Int(1)); // x := concrete Int(1)
        // bind_waking(x := ?y) CONTRADICTS (Int(1) ≠ ?y) → the move must be skipped.
        s.bind_waking(&kb, x, Value::Var(Var::Global(y)));
        assert!(s.is_contradiction());
        assert!(
            !s.residual_constraints().iter().any(|(v, _)| *v == y),
            "constraints must not move onto the alias on a contradicting bind",
        );
    }

    /// Merge-on-alias only moves onto an UNBOUND alias: binding `?x := ?y` when
    /// `?y` is already bound leaves `?x`'s constraints on `?x` (surfaced for
    /// Step 5's deref-and-check) rather than stranding them on a var that never
    /// binds again.
    #[test]
    fn bind_waking_keeps_constraints_when_alias_is_bound() {
        let kb = KnowledgeBase::new();
        let mut s = Substitution::new();
        let (x, y) = (vid(1), vid(2));
        s.bind_value(&kb, y, Value::Int(3)); // ?y already bound
        s.add_type_constraint(x, Value::Int(7));
        s.bind_waking(&kb, x, Value::Var(Var::Global(y)));
        // Not moved onto the bound ?y; still recorded on ?x.
        let resid = s.residual_constraints();
        assert!(resid.iter().any(|(v, _)| *v == x), "constraint stays on x");
        assert!(!resid.iter().any(|(v, _)| *v == y), "must not strand onto bound y");
    }

    /// `absorb_constraints` unions another subst's top-level store (the
    /// carry-through-merge primitive used by the resolver lift / reflect compose).
    #[test]
    fn absorb_constraints_unions_stores() {
        let (x, y) = (vid(1), vid(2));
        let mut a = Substitution::new();
        a.add_type_constraint(x, Value::Int(1));
        let mut b = Substitution::new();
        b.add_type_constraint(y, Value::Int(2));
        b.add_lacks(x, [Value::Int(3)]);
        a.absorb_constraints(&b);
        let resid = a.residual_constraints();
        assert_eq!(resid.len(), 3);
        assert_eq!(resid.iter().filter(|(v, _)| *v == x).count(), 2); // own Type + b's Lacks
        assert_eq!(resid.iter().filter(|(v, _)| *v == y).count(), 1);
    }

    /// Loud-on-bypass: binding a CONSTRAINT-CARRYING var via `bind_compressed`
    /// (the synthetic path that never wakes) panics rather than silently drop it.
    #[test]
    #[should_panic(expected = "constraint-carrying var")]
    fn bind_compressed_panics_on_constrained_var() {
        let store = TermStore::new();
        let x = vid(1);
        let mut s = Substitution::new();
        s.add_type_constraint(x, Value::Int(7));
        s.bind_compressed(std::iter::once((x, TermId::from_raw(999))), &store);
    }

    /// The loud guard is per-var: `bind_compressed` of an UNCONSTRAINED var is
    /// fine even when the store is non-empty (a different var carries a constraint).
    #[test]
    fn bind_compressed_ok_when_other_var_constrained() {
        let store = TermStore::new();
        let (x, other) = (vid(1), vid(2));
        let target = TermId::from_raw(999);
        let mut s = Substitution::new();
        s.add_type_constraint(other, Value::Int(7));
        s.bind_compressed(std::iter::once((x, target)), &store);
        assert_eq!(s.resolve_as_value(x).map(|v| v.expect_term()), Some(target));
    }

    #[test]
    fn bind_compressed_leaves_non_term_entries_untouched() {
        let mut store = TermStore::new();
        let v1 = vid(1);
        let v2 = vid(2);
        let var_v1 = store.alloc(Term::Var(Var::Global(v1)));
        let target = TermId::from_raw(999);

        let mut s = Substitution::new();
        s.bindings.insert(v2, Value::term(var_v1));  // v2 → Var(v1)
        s.bindings.insert(vid(3), Value::Int(77));   // non-Term: untouched
        s.bind_compressed(std::iter::once((v1, target)), &store);

        // v2's binding now points through to `target`.
        assert_eq!(s.resolve_as_value(v2).map(|v| v.expect_term()), Some(target));
        // v3's non-Term binding is preserved as-is.
        assert!(matches!(s.resolve_as_value(vid(3)), Some(Value::Int(77))));
    }
}

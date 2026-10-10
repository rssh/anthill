//! Building requirement dictionaries for a call: dispatching and op-scoped dictionaries,
//! refusal reporting, held spec views and caller rigid carriers.

use super::*;

/// WI-227: interned stdlib symbols + field names needed to allocate
/// the three requirement-projection IR forms. Resolved once at the
/// entry point so the recursive search doesn't re-look-up per dep.
/// `pub` only so the WI-227 test file can drive `build_dep_projection`
/// directly with synthetic inputs.
pub struct ProjectionSyms {
    /// `anthill.reflect.Expr.var_ref` — named requirement-param read
    /// (names model; replaced the positional `requirement_at_current`).
    pub var_ref: Symbol,
    /// `anthill.reflect.Expr.requirement_at_sort`
    pub ras: Symbol,
    /// WI-1045 — the DICTIONARY constructor, `anthill.realization.runtime.Dictionary`.
    ///
    /// ONE SPELLING (`requirement-channel.md` §9): the IR construction node and the
    /// value it evaluates to are the same constructor with the same key set —
    /// positional sub-dictionaries, one named `impl`. It used to be
    /// `anthill.reflect.Expr.construct_requirement(impl_functor =, requirements =)`:
    /// a different functor and different key names for one thing, which is a second
    /// identity to keep in step by hand. Both names come from
    /// [`crate::kb::term_view::dictionary_view_syms`], so producer and reader cannot drift.
    pub dict_ctor: Symbol,
    /// The `impl` key of a dictionary — the named child naming the provider.
    ///
    /// WI-1045 also RETIRED this struct's `nil` / `cons` / `head` / `tail`: the
    /// emitter built its sub-dictionaries as a cons SPINE under a `requirements`
    /// key, and they are positional children now. Nothing here spells a list any
    /// more, so `resolve` no longer gates on `anthill.prelude.List` either.
    pub dict_impl: Symbol,
    pub slot: Symbol,
    pub chain: Symbol,
    /// `name` field of `var_ref`.
    pub name: Symbol,
}

impl ProjectionSyms {
    pub fn resolve(kb: &mut KnowledgeBase) -> Option<Self> {
        let (dict_ctor, dict_impl) = crate::kb::term_view::dictionary_view_syms(kb)?;
        Some(Self {
            var_ref: kb.try_resolve_symbol("anthill.reflect.Expr.var_ref")?,
            ras: kb.try_resolve_symbol("anthill.reflect.Expr.requirement_at_sort")?,
            dict_ctor,
            dict_impl,
            slot: kb.intern("slot"),
            chain: kb.intern("chain"),
            name: kb.intern("name"),
        })
    }
}

/// WI-234 (Model 1): build the dispatching-dict expression for the
/// Direct path — `Dictionary(<one projection per callee chain entry>, impl:
/// callee_spec_sort)`. Each projection sources its sub-instance from
/// `caller_requires` via the three-strategy search in
/// `build_dep_projection`. The caller wraps the result in a
/// single-entry cons-list to form the `apply_within.requirements`
/// channel.
pub(super) fn build_dispatching_dict_direct(
    kb: &mut KnowledgeBase,
    callee_spec_sort: Symbol,
    // Proposal 066 §7 — the provision the called operation is a member of
    // ([`op_owner_provision`]): a parent bundle is the callee's FRAME, which is its
    // sort's chain under that provision.
    callee_provision: Option<Symbol>,
    caller_requires: &DictChain,
    syms: &ProjectionSyms,
) -> Option<TermId> {
    // WI-239: the callee's DIRECT requires — one projection per slot the
    // callee body reads by `__req_<spec>` name. Matches `synth_req_names`
    // (also direct) so the constructed dict's arity equals the callee's
    // direct-require count, satisfying eval's `expand_dispatching_dict`
    // arity invariant. Transitive callee requires are bundled recursively
    // inside each direct projection, not flattened into this list.
    //
    // WI-857: this is a PARENT-BUNDLE dictionary, not a spec instance — its functor
    // IS the frame owner — so under [`dict_layout`] its spec and provider coincide
    // and the single list above is exactly the layout. Unchanged by that ticket for
    // that reason; the consumer computes the same one-list layout from the
    // classification's `spec_op_sym`, which on this route is the callee itself.
    // WI-869: the DICTIONARY chain — a callee whose parent declares a conditional
    // provision reads its `:- goals` slots by name too, so a chain short of them
    // would be short of what `synth_req_names` names.
    let callee_chain = provider_dict_entries(kb, callee_spec_sort, callee_provision);
    build_dispatching_dict_from_chain(
        kb,
        // Diagnostic-only path (`require_complete = false`): it cannot act on an `Err`.
        None,
        &[],
        callee_spec_sort,
        callee_provision,
        &callee_chain,
        caller_requires,
        syms,
        false,
        // WI-419: req-insertion diagnostic path — the call-site subst is gone
        // here, so Strategy 1 keeps its first-match behavior.
        None,
        // WI-841: and with it the call-site bracket, so there is no selection to
        // apply. This path's output is the diagnostic-only `dispatch_rewrites` term;
        // the dict eval actually threads was built at the call site, WITH the pin.
        &[],
        RequirementUse::Call,
        // WI-945: nowhere to report an unsuppliable element and nothing to report —
        // `require_complete = false` returns before that arm, and the σ it needs to
        // name the element is exactly what this path does not have.
        None,
    )
    // WI-828: a refusal needs the σ context (`disambig = Some`), so the σ-less
    // diagnostic path cannot produce one.
    .expect("σ-less dict build (disambig = None) never refuses")
}

/// WI-828: the structured reason the WI-415 concrete dict build REFUSED a
/// requirement, carried to the call site so the refusal surfaces as a located
/// load diagnostic instead of the silent `dispatch_dict: None` that loaded
/// clean and died at eval reading an unbound `__req_*` (or, on the eta path,
/// a WI-420 error naming neither the σ refusal nor the element). Produced by
/// [`explain_dep_refusal`] on the failure path only, so the fields are
/// pre-rendered Strings.
#[derive(Clone, Debug)]
pub struct RequirementRefusal {
    /// The requirement that failed to project, rendered (`Desc[T = MT]`).
    pub(super) dep_text: String,
    /// Dep elements still an UNBOUND type param under the call-site σ
    /// (`T = MT`) — what makes neither forwarding nor construction pickable.
    pub(super) unconstrained: Vec<String>,
    /// Caller `requires` entries covering the dep COARSELY but σ-refused
    /// (WI-821) — the entries the pre-gate code would have blindly forwarded.
    pub(super) refused_covers: Vec<String>,
    /// How Strategy-3 construction terminated, rendered — the `Ambiguous`
    /// provider set when there is one, else the `NoMatch`/`Cyclic` account.
    pub(super) construction: String,
    /// WI-456 — [`Self::construction`] ALREADY ENDS IN A REPAIR, so the generic tail must
    /// not add a second one that contradicts it. True exactly where the account came from
    /// a tie whose `tie_repair_advice` is attachable ([`failure_carries_repair`]).
    ///
    /// THIS IS THE `None`-PINNED PEER OF [`PinnedWitness::TiedInside`], which covers the
    /// same contradiction for a refusal that DID pin a witness. That enum is a value rather
    /// than a flag for a stated reason — a flag beside a `Symbol` could pair `Unusable`'s
    /// advice with a tie's account — and that reason does not reach here: this says nothing
    /// about a witness, only whether the account is self-sufficient, and there is no
    /// witness at this site to mismatch it against.
    ///
    /// NARROW, exactly as `TiedInside`'s own doc requires: it suppresses the tail ONLY when
    /// [`Self::unconstrained`] is empty. That tail is the repair for an UNCONSTRAINED
    /// ELEMENT, which a tie's advice does not cover — suppressing on "the construction said
    /// something" rather than on WHICH clause it answered would silence that one too.
    ///
    /// **NOT DRIVEN BY A TEST, AND SAID SO RATHER THAN IMPLIED.** No program I could write
    /// reaches the op-scoped tie with an ATTACHABLE repair, and no existing test does
    /// either — wi870 / wi858 / wi456_sorted_set_collection / wi1026 / wi822 all pass
    /// untouched by this field (58 rows). THREE fixtures were tried and each LOADED CLEAN:
    ///
    ///   1. an op-scoped `requires WeakOrd[T = Boxed[E = String]]` over the witness
    ///      `ByInner` with its named slot `OI`;
    ///   2. the same against wi456's own `BY_INNER` / `Boxed` fixture verbatim;
    ///   3. an element sort providing `Eq` + `PartialOrd` but NOT `WeakOrd`, with two rival
    ///      witnesses over it, so nothing could be defaulted to.
    ///
    /// All three are answered by rung 2a (058 §3.2) before a tie can form — the carrier's
    /// own provision wins and the rivals stay opt-in by bracket, which is WI-861's flip.
    /// So the path may not be reachable on today's surface at all. The guarantee here is
    /// STRUCTURAL — one predicate, one suppression, gated on one emptiness test — which is
    /// the same standing WI-456(b) recorded for its own at-call-goal-tie-under-a-pin shape.
    /// A reader who finds a reaching fixture should turn this paragraph into a driver.
    pub(super) construction_carries_repair: bool,
    /// [`Self::construction`] NAMES EVERY REPAIR THIS REFUSAL HAS, the unconstrained element's
    /// included, so [`Self::render`] appends nothing after it. The rule-body account's
    /// ([`unrescuable_rule_body_refusal`]), and the reason is what the generic tail offers
    /// there: an explicit type argument, which a rule-body call refuses as its own load
    /// error, and an enclosing `requires` to align, which a rule has not got. Wider than
    /// [`Self::construction_carries_repair`], which stands aside for an unconstrained element
    /// because a tie's advice does not cover one; this account's does.
    pub(super) account_names_every_repair: bool,
    /// The enclosing scope offers NO ROUTE to this dep — no chain entry covers it, no
    /// sub-chain projection reaches it, construction found nothing, and none of the four
    /// signatures above explains why. The plainest shape was a signature that QUANTIFIES a
    /// type parameter and declares no `requires` to carry its dictionary
    /// (`f[T, O](s: SortedSet[T = T, O = O])`): [`carried_slot`] reads the binder as
    /// `Forwarded` because the signature declared it, but declaring a type PARAMETER is
    /// not declaring a SLOT, so the scope has nothing to forward. Before this, such a
    /// call took the silent `Ok(None)` and died at eval with `Internal(DeferToRequirement:
    /// __req_* not bound … frame binds [])`, naming neither the requirement nor a repair.
    ///
    /// WI-20260923-WN9P8 — that shape is a FORWARD, and [`Self::untied`] refuses it before
    /// any strategy runs, with this arm's advice. What reaches this arm now is a dep that
    /// forwards nothing: an anonymous requirement, or a slot no parameter binds (measured,
    /// seven rows across the suite, e.g. `wi456 strategy_2b_declines_a_witness_provider`).
    ///
    /// It changes only the ADVICE. "Pin the element at the call site" is the repair for an
    /// UNCONSTRAINED element and is not this one: here the element is a rigid the caller
    /// already pinned, and what is missing is the slot to carry its dictionary.
    pub(super) no_scope_route: bool,
    /// WI-841: the witness this call-site bracket PINNED for the dep, when it did.
    /// A pinned dep that fails to project can never degrade to "no dict, carry on":
    /// the author named a provider and it was not used, so the refusal is
    /// unconditional rather than gated on the σ signature the other fields describe.
    /// A `Symbol`, rendered by `render` like every other name here — the other fields
    /// are pre-rendered because they are LISTS built during the walk; a single name is
    /// not, and `render` already holds the `kb`.
    ///
    /// WI-456 — and WHY it could not be used, because the two reasons take opposite
    /// advice. See [`PinnedWitness`].
    pub(super) pinned: Option<PinnedWitness>,
    /// WI-1102: the carrier this call PINNED and the provision it lacks — 058 §3.10's
    /// use-site discharge. Present exactly on the signature `unconstrained` is the
    /// complement of: every element determined, and the named carrier providing
    /// nothing. The other fields describe why a dictionary could not be ASSEMBLED;
    /// this one says the program never had one to assemble.
    pub(super) unprovided: Option<UnprovidedProvision>,
    /// WI-20260923-WN9P8 — the dep FORWARDS a named slot bound to one of the enclosing
    /// signature's own parameters, and the frame holds no dictionary for that parameter
    /// ([`binder_frame_slot`]). What covers the goal by spec, if anything, is another
    /// parameter's, so it is not forwarded and nothing is constructed in its place. It
    /// replaces every tail below, as [`Self::unprovided`] does, because theirs are repairs
    /// for a search and this dep never reaches one.
    pub(super) untied: Option<UntiedForward>,
}

/// WI-1102 — a fully-pinned requirement, and the CARRIER the call named for it.
///
/// Carried as SYMBOLS rather than a pre-rendered string because [`RequirementRefusal`]
/// is built on a path that already holds the `kb` for its other names; there is no list
/// here to pre-render.
///
/// `has_a_row` IS THE DIFFERENCE BETWEEN A CLAIM AND AN ASSERTION, and the first cut of
/// this ticket got it wrong (found by /code-review): "the goal ended `NoMatch`" is NOT
/// "this carrier provides nothing". A CONDITIONAL provision (058 §3.8) whose side
/// condition fails produces the identical `NoMatch` at the top goal — `wi855`'s `Quiet`
/// provides `Desc[T = Box[B = E]] :- Desc[T = E]`, so `Box` HAS a `Desc` provider and
/// `Desc[Box[B = Mystery]]` fails only because `Mystery` has none. Told "`Box` provides
/// no `Desc` — declare `provides Desc[…]` on `Box`", the author would be sent to the
/// container when the gap is on the type argument, to write a second row for a carrier
/// that already has one. So the row is LOOKED UP, and the two cases get two sentences.
///
/// WHAT IT DELIBERATELY DOES NOT SAY — that a missing provision is IMPOSSIBLE rather
/// than merely absent. The ticket's class (3) is a `Float`-bearing composite, whose
/// derived `NonEq` would make `provides Eq[…]` a line the loader then refuses
/// (`check_eq_noneq_exclusive`). The classification that knows is
/// [`crate::kb::eq_derive::EqClassification`], a `load.rs` local held between
/// `derive_total_eq` and `eq_derive::run` — and `run`, which asserts the `NonEq` half,
/// stands AFTER this diagnostic is rendered. Reading the provision relation for `NonEq`
/// here would therefore answer `false` for exactly the carriers it is meant to catch,
/// and threading the classification through the typer would give the rule the second
/// owner its own doc forbids. The impossible half already has a home that runs late
/// enough: WI-644's `check_use_site_requires_eq`, which refuses a `NonEq` carrier bound
/// into a `requires Eq` position. Left as-is rather than half-answered.
#[derive(Clone, Debug)]
pub struct UnprovidedProvision {
    /// The sort the call pinned into the spec's carrier parameter.
    pub(super) carrier: Symbol,
    /// The spec the requirement names.
    pub(super) spec: Symbol,
    /// Does `carrier` already have a provision row for `spec` — by any route
    /// ([`carrier_has_provision_row`])? `true` ⇒ the row exists and its CONDITION failed
    /// at these bindings, so the advice must point at the bindings and not at this sort.
    has_a_row: bool,
    /// The provision as a clause the author can paste — `Spec[T = Int64]`, each binding the
    /// type it is and never the alias a `requires` wrote it through, which need not be in
    /// scope where the provision goes. `None` where the requirement does not write every
    /// element of the spec: a refusal raised over a requirement with elements still open —
    /// the carrier having no provision to say them is the very reason they are.
    provision_in_full: Option<String>,
}

/// WI-1102 — does any provision of `spec` dispatch at `carrier`?
///
/// The question the refusal's sentence asserts, asked of the relation rather than
/// inferred from a failed goal. BOTH provenances count, because both are rows the author
/// would be told to duplicate: a SELF-provision / instance fact, whose dispatch carrier
/// is the provider itself, and a WITNESS, whose carrier is in the spec's own binding
/// (WI-1069 — provider and carrier are two questions, and [`witness_dispatch_carrier`]
/// is the reader that keeps them apart). Keyed by BASE, so a row for `Box[B = E]`
/// answers for `Box[B = Mystery]`: the question is whether this SORT has a provision,
/// not whether this instantiation resolves — the goal already answered that, with `No`.
/// That is also the limit of what the `true` answer licenses, and the message it selects
/// says no more than it (see the `has_a_row` arm in [`RequirementRefusal::render`]).
///
/// IT MUST DECODE THE CARRIER ON THE SAME LADDER AS [`unprovided_provision`], which is
/// why it reads [`spec_carrier_param_or_sole`] rather than calling
/// [`witness_dispatch_carrier`]. That reader stops at rung 1
/// ([`provision_carrier_binding`] → [`spec_carrier_param`]) and is right to: its other
/// callers must not take rung 2 (WI-1076). But here rung 1 answers `None` for exactly
/// the lawfulness family this diagnostic serves — `Eq`, `NonEq` — so every witness row
/// for one would decode to the PROVIDER, `has_a_row` could never be `true`, and a
/// carrier whose provision is a witness elsewhere would be told to write a row it
/// already has. The two questions "which parameter holds the carrier" get ONE answer.
/// WI-456 — is `carrier` itself the PROVIDER of `spec` at `carrier`, with no rival?
///
/// NOT [`carrier_has_provision_row`], and the difference is the whole soundness of
/// [`provider_half_projection`]. That predicate asks whether any provision DISPATCHES at
/// this carrier — which a WITNESS does (`ByLength provides WeakOrd[T = String]` dispatches
/// at `String`) — and its own doc says both provenances count on purpose, because the
/// diagnostic it serves wants exactly that. Strategy 2b needs the other question: whose
/// `requires` chain is the PROVIDER HALF of the dictionary sitting in that slot. For a
/// witness that is the WITNESS's chain, not the carrier's, so reading the carrier's would
/// index a real dictionary at the wrong slot.
///
/// MEASURED before this predicate existed (found by /code-review): with `ShowBox[E]
/// requires Tagged[T = Box[E = E]] provides Shown[T = Box[E = E]]`, a body requiring
/// `Shown[T = Box[E = E]]` took Strategy 2b, read `Box`'s chain where the dictionary held
/// `ShowBox`'s, and RAN — answering 99 (the witness's own requirement) where 7 was
/// correct. With Strategy 2b backed out the same program is refused at load. A silently
/// wrong answer from a correctly-refused program is the worst trade the typer can make.
///
/// TWO CONDITIONS, and the second is not redundant. A self-provision must exist AND no
/// OTHER provider may dispatch at this carrier: 058 tier 3 lets nameable witnesses coexist
/// with a carrier's own row, and where one does, which dictionary the slot holds is the
/// resolution's answer and not this syntactic read's. So a rival makes Strategy 2b decline
/// and fall through, rather than guess.
pub(super) fn carrier_is_its_own_sole_provider(
    kb: &KnowledgeBase,
    carrier: Symbol,
    spec: Symbol,
) -> bool {
    let carrier_param = spec_carrier_param_or_sole(kb, spec);
    let mut saw_self = false;
    for row in provides_rows_of_spec(kb, spec) {
        let dispatch_carrier = carrier_param
            .and_then(|p| provision_binding_at_param(kb, p, &row.spec_view))
            .map_or(row.provider, |(_, base)| base);
        if !same_sort_canonical(kb, dispatch_carrier, carrier) {
            continue;
        }
        if same_sort_canonical(kb, row.provider, carrier) {
            saw_self = true;
        } else {
            // A witness dispatching at this carrier: the slot may hold ITS dictionary.
            return false;
        }
    }
    saw_self
}

pub(super) fn carrier_has_provision_row(kb: &KnowledgeBase, carrier: Symbol, spec: Symbol) -> bool {
    let carrier_param = spec_carrier_param_or_sole(kb, spec);
    provides_rows_of_spec(kb, spec).any(|row| {
        // No carrier parameter to read ⇒ the provision's dispatch carrier IS the
        // provider (a self-provision, an instance fact, or a row that names no other
        // sort) — the same default `witness_dispatch_carrier`'s `None` stands for.
        let dispatch_carrier = carrier_param
            .and_then(|p| provision_binding_at_param(kb, p, &row.spec_view))
            .map_or(row.provider, |(_, base)| base);
        same_sort_canonical(kb, dispatch_carrier, carrier)
    })
}

impl RequirementRefusal {
    /// One renderer for both error faces ([`TypeError::format`] and
    /// [`TypeError::to_load_error`]): name the dep, the unconstrained
    /// element(s), the σ-refused covering entries (or the ambiguous provider
    /// set), and the author-side fix.
    pub(super) fn render(
        &self,
        kb: &KnowledgeBase,
        op: Symbol,
        callee_sort: Symbol,
        usage: RequirementUse,
    ) -> String {
        let op_qn = kb.qualified_name_of(op);
        let site = usage.site();
        let is_construction = usage == RequirementUse::Construction;
        // What the author does instead, where the repair is not to add the provision.
        let (elsewhere, pin) = match usage {
            RequirementUse::Construction => (
                "build the value over a sort that provides it",
                " — fix the element where the value is built (through an argument or the \
                 expected type), or require it in the enclosing scope",
            ),
            RequirementUse::Call | RequirementUse::FunctionValue => (
                "call an operation that does not require it",
                " — pin the element at the call site (bind it through an argument or an \
                 explicit type argument), or align the enclosing `requires` element with the \
                 callee's",
            ),
        };
        let usage = match usage {
            RequirementUse::FunctionValue => format!("`{}` used as a function value", op_qn),
            RequirementUse::Call => format!("call to `{}`", op_qn),
            RequirementUse::Construction => format!("the construction `{}`", op_qn),
        };
        // WI-1091: an OP-SCOPED requirement is owned by the operation itself, so the
        // owner and the callee are one name and "requirement `X` of `f` cannot be
        // supplied for call to `f`" says it twice. Drop the owner clause there — which is
        // also the only honest option, since the alternative spellings would attribute
        // the clause to a parent sort that did not write it.
        let owner = if callee_sort == op {
            String::new()
        } else {
            format!(" of `{}`", kb.qualified_name_of(callee_sort))
        };
        let mut msg = match &self.pinned {
            Some(w) => format!(
                "requirement `{}`{} cannot be supplied for {} from the selected \
                 witness `{}`",
                self.dep_text,
                owner,
                usage,
                kb.qualified_name_of(w.witness()),
            ),
            None => format!(
                "requirement `{}`{} cannot be supplied for {}",
                self.dep_text, owner, usage,
            ),
        };
        if !self.unconstrained.is_empty() {
            msg.push_str(&format!(
                ": element {} is unconstrained at this {site}",
                self.unconstrained.join(", "),
            ));
        }
        if !self.refused_covers.is_empty() {
            let list: Vec<String> = self
                .refused_covers
                .iter()
                .map(|e| format!("`requires {e}`"))
                .collect();
            let under = if is_construction { "construction" } else { "call" };
            msg.push_str(&format!(
                "; the enclosing scope's {} covers only as a wildcard and is not forwarded — its element is a different type parameter under this {under} (WI-821)",
                list.join(", "),
            ));
        }
        if !self.construction.is_empty() {
            msg.push_str(&format!("; {}", self.construction));
        }
        if let Some(u) = &self.untied {
            msg.push_str(": ");
            msg.push_str(&u.render(kb));
            return msg;
        }
        // WI-1102 — the carrier clause and its OWN advice, which replaces the generic
        // one below: "pin the element at the call site" is exactly the thing this
        // author already did, and repeating it would send them looking for a second
        // binding that is not missing.
        if let Some(u) = &self.unprovided {
            let carrier = kb.qualified_name_of(u.carrier);
            let spec = kb.qualified_name_of(u.spec);
            // The repair line carries the WHOLE requirement, not just its carrier
            // binding: a multi-parameter spec written with one binding omitted fills the
            // rest from its own parameters, which §5.2 legislates as its own load error
            // — advice that trades one refusal for another. `provision_in_full` is the goal
            // as rendered, so `provides <it>` is complete by construction.
            // WI-1102 — this arm says ONLY what the lookup established: a row exists for
            // this sort, and none of its rows answers at these bindings. It used to name
            // the mechanism ("its provision is conditional and the condition fails on a
            // type argument above"), which `carrier_has_provision_row` does not check and
            // which is false for the other shape that reaches here — an UNCONDITIONAL row
            // at a different instantiation (`Box provides Desc[T = Box[B = Int64]]`, call
            // needs `Desc[Box[B = String]]`), where a second row on `Box` IS the repair
            // the old sentence explicitly ruled out. So it points at the bindings and
            // names both repairs, which is the whole of what is known here.
            msg.push_str(&if u.has_a_row {
                format!(
                    "; `{carrier}` does provide `{spec}`, but no row of it answers at \
                     these bindings — check the type arguments above: either one of them \
                     lacks the provision a conditional row requires, or `{carrier}` needs \
                     a row at this instantiation"
                )
            } else {
                // EVERY place a provision can be written, and NOT `fact`: since
                // WI-20260917-S8JYF a `fact Spec[…]` is an ordinary fact and provides
                // nothing, so the "(or assert the `fact`)" this used to offer was a repair
                // that re-raises this very refusal — MEASURED, WI-20260918-CKD4J's probes.
                // The `namespace` half is what an author who cannot edit the carrier needs
                // (a secondary entry, 059 R2/R3); `provides_needs_sort_message` words the
                // same two places. The WITNESS half is the 058 route and is often the
                // smallest repair — a sort that already holds the `PartialEq` row takes
                // the `Eq` one in a line (MEASURED on wi1102's `WITNESS_PROVISION`).
                //
                // "AT THE FILE'S TOP LEVEL" IS LOAD-BEARING. A `namespace` name nested in
                // another namespace is read RELATIVE to it — MEASURED: `namespace a.b.S`
                // pasted inside `namespace a` opens `a.a.b.S`, the clause is refused as
                // carrier-less and this refusal still stands. The qualified address printed
                // here is a repair only where it is absolute.
                let clause = match &u.provision_in_full {
                    Some(provision) => format!("`provides {provision}`"),
                    None => {
                        format!("a `provides {spec}[…]` for it, each element of `{spec}` written")
                    }
                };
                format!(
                    "; `{carrier}` provides no `{spec}` — declare {clause}: on \
                     `{carrier}` itself (in its own declaration, or, if it is declared \
                     elsewhere, in a `namespace {carrier}` block at the file's TOP LEVEL \
                     — nested in another namespace that name is read relative to it), or \
                     on a witness sort — or {elsewhere}",
                )
            });
            return msg;
        }
        // The advice differs by branch: an author who already WROTE a witness cannot be
        // told to pin one.
        //
        // WI-456 — and a witness that TIED INSIDE gets no tail at all, because
        // [`Self::construction`] already carries the tie's own repair and the `Unusable`
        // sentence would contradict it. NARROW ON PURPOSE: the `None` tail is the repair
        // for an UNCONSTRAINED ELEMENT, which a tie's advice does not cover and which
        // `explain_dep_refusal` reports through this very branch — suppressing on "the
        // construction clause said something" rather than on WHICH clause it answered
        // would have silenced that one too.
        // The NO-ROUTE advice replaces the generic one for the reason the `unprovided`
        // clause above replaces it: the generic tail tells the author to pin an element,
        // and here the element is already pinned — to a type parameter of their own
        // signature. What is missing is a slot to carry the dictionary for it.
        if self.no_scope_route {
            // EITHER SCOPE, SINCE WI-20260921-159S9 — and the tail this replaces is the
            // reason the ticket existed. It used to end "a slot declared on the OPERATION
            // does not reach this call", which was true of the sort-half read
            // `build_concrete_dispatch_dict` then had, and is FALSE now that the builder
            // reads the caller's whole frame: an author who declares the clause on the
            // operation gets a working program.
            //
            // A REFUSAL MUST NOT NAME A REPAIR THAT IS NOT ONE, in either direction. The
            // earlier correction (by /code-review) was to DROP "or its operation" for
            // exactly that reason — advising the operation told an author to do the thing
            // they had already done, the WI-1102 failure the typer warns about ("repeating
            // it would send them looking for a second binding that is not missing"). Both
            // spellings carry it today, so naming both is now the accurate advice rather
            // than the misleading one. `wi456_no_scope_route_test::the_refusal_names_the_
            // repair_and_not_a_witness_choice` drives the text.
            msg.push_str(
                " — nothing in the enclosing scope supplies it: declare a requirement slot \
                 for it on the enclosing SORT (`requires <name>: <the spec above>`) or on \
                 this OPERATION, and write `<name>` where the parameter's type names that \
                 slot",
            );
            return msg;
        }
        // WI-456 — …AND THE SAME SUPPRESSION WHERE NO WITNESS WAS PINNED. `TiedInside`
        // reaches only a refusal that pinned one; an op-scoped tie pins none, so its account
        // carried the tie's repair and the `None` arm appended a contradicting second.
        // GATED ON `unconstrained` BEING EMPTY, which is what keeps it from silencing the
        // case that arm exists for — see [`Self::construction_carries_repair`].
        if self.account_names_every_repair
            || (self.construction_carries_repair && self.unconstrained.is_empty())
        {
            return msg;
        }
        msg.push_str(match self.pinned {
            Some(PinnedWitness::TiedInside(_)) => "",
            Some(PinnedWitness::Unusable(_)) => " — select a witness that provides this requirement at these bindings, or drop the selection and let it resolve",
            None => pin,
        });
        msg
    }
}

/// Render a `RequiresEntry` for a diagnostic (`Desc[T = MT]`) via the same
/// goal rendering Strategy 3's own diagnostics use; entries that do not form
/// a goal fall back to the spec sort's name. The requirement as its clause wrote it: a
/// binding written through a type alias is led by the alias's name
/// ([`format_goal_as_written`]).
pub(super) fn render_requires_entry(kb: &KnowledgeBase, entry: &RequiresEntry) -> String {
    match goal_from_requires_entry(kb, entry) {
        Some(goal) => format_goal_as_written(kb, &goal),
        None => kb.qualified_name_of(entry.required_sort).to_string(),
    }
}

/// WI-945 — a call site whose parent-bundle dictionary could not be built because a
/// requirement element is left GENUINELY UNCONSTRAINED (§5.2), parked for the verdict
/// pass that runs once every operation body is typed ([`report_unsuppliable_requirements`]).
///
/// PARKED, NOT RAISED, because the two halves of the verdict are knowable in two
/// different places and neither knows both:
///
///  - "nothing at this call pins the element" needs the per-call σ, which is alive
///    only inside the typer's call check and is gone by `req_insertion` (the same
///    reason [`build_concrete_dispatch_dict`] runs where it does). Hence the refusal
///    is BUILT here, fully rendered.
///  - "no route discharges it" needs the CALLEE, and an operation may be called before
///    its own body has been classified. Hence the refusal is DECIDED later, in
///    [`report_unsuppliable_requirements`].
///
/// WHAT THE SECOND HALF ASKS CHANGED, AND THE PARK DID NOT. It used to ask whether the
/// callee's PRESENT BODY reads the slot, and dropped the refusal when it did not —
/// WI-20260921-3G1YT deleted that question and the two walks behind it, because a
/// declared `requires` is owed by the caller BECAUSE IT IS DECLARED. Every parked
/// refusal is now reported; a dep some route discharges
/// ([`scope_contract_covers_dep`] and the two rule-body rescues) never parks at all. The
/// park itself survives for the reason above, which is about WHEN the answer exists and
/// not about what the question is.
#[derive(Clone)]
pub(crate) struct UnsuppliableRequirement {
    /// The call, for the diagnostic's location. `source` rides beside `span` because
    /// this error is emitted outside the per-op loop that stamps `sources`.
    pub(crate) span: Option<Span>,
    pub(crate) source: crate::span::SourceId,
    /// The operation called — the one whose body decides whether the missing
    /// dictionary is a defect or an irrelevance.
    pub(crate) callee_op: Symbol,
    /// Its parent sort: the owner of the `requires` chain this dictionary would fill.
    pub(crate) callee_sort: Symbol,
    pub(crate) refusal: Box<RequirementRefusal>,
}

/// WI-945 — the verdict on every call site [`build_concrete_dispatch_dict`] parked: a
/// requirement element nothing at the call pins is a LOAD error (§5.2) when the callee
/// would actually miss the dictionary, and nothing at all when it would not.
///
/// Runs after BOTH `check_operation_bodies` sweeps, which is the earliest point at
/// which every callee has been classified — an operation is routinely called before
/// its own body is checked, so asking at the call site would answer from whatever the
/// sort-iteration order happened to be.
pub(super) fn report_unsuppliable_requirements(
    kb: &mut KnowledgeBase,
    errors: &mut Vec<TypeError>,
    sources: &mut Vec<Option<crate::span::SourceId>>,
) {
    let parked = std::mem::take(&mut kb.unsuppliable_requirements);
    if parked.is_empty() {
        return;
    }
    // `sources` is parallel to `errors` on entry (the callers' contract) and must stay
    // so: each error pushed here pairs with the span's own file, which is not the file
    // the surrounding pass happens to be tagging.
    sources.resize(errors.len(), None);
    for entry in parked {
        // WI-20260921-3G1YT — EVERY PARKED REFUSAL IS REPORTED. There was a gate here —
        // `if !op_body_reads_…_requirement_slot(callee) { continue; }` — which asked
        // whether the CALLEE'S PRESENT BODY happens to read the slot, and dropped the
        // refusal when it did not. It is deleted, with both walks behind it, because a
        // declared `requires` is OWED BY THE CALLER BECAUSE IT IS DECLARED: a caller
        // admitted on the strength of a body it does not own breaks when that body
        // changes, with nothing at the call site having moved.
        //
        // WHAT REPLACES IT IS NOT A LOOSER GATE BUT THREE DISCHARGE ROUTES, all read at
        // the call site from the signature, and stated in full at kernel-language.md §8.7:
        // the caller's own `requires` ([`build_dep_projection`] Strategies 1/2); a
        // dictionary the CLAUSE declares, a written `require[Spec[…]]`
        // ([`scope_contract_covers_dep`], over what [`held_spec_views`] collects); and
        // provider facts that uniquely determine one
        // ([`dep_completes_to_a_unique_provider`]). A dep no route discharges never parks.
        // A value in scope is not a route: its type says nothing a dictionary could be
        // built from (WI-20261005-KSSA4).
        //
        // THE LAST TWO REPLACED A PAIR THAT APPEALED TO RUN TIME. Until WI-20260922-0DK3H
        // the rule-body half read `spec_has_value_directed_route` ("some value can name a
        // provider at fire time") and `dep_has_searchable_pin`. Both are DELETED, on the
        // ground that ticket settled: a rule body's evidence is owed at LOAD, so the gate
        // may ask only what load can see.
        errors.push(TypeError::UnsatisfiableRequirement {
            span: entry.span,
            op: entry.callee_op,
            callee_sort: entry.callee_sort,
            usage: RequirementUse::Call,
            refusal: entry.refusal,
        });
        sources.push(Some(entry.source));
    }
}

/// The dep's own elements that NOTHING at this call determines, rendered
/// `` `F = HolderVS.F` `` for a diagnostic. `goal.bindings` is already
/// type-param-filtered by [`goal_from_requires_entry`] — the same extraction the
/// resolution itself used — and [`sigma_class_terminal`]'s second component is the
/// distinction that matters: `false` = the chase ended at an unbound global, i.e.
/// an element neither the arguments nor an explicit type argument nor the
/// enclosing scope's own parameters pin. An element that IS an enclosing-scope
/// parameter terminates at a rigid (`true`) and is constrained in context, so it
/// is absent from this list — which is what keeps the WI-418 abstract cross-sort
/// forward (a sort's own param, covered by its `requires`) out of it.
///
/// Empty is the load-bearing answer: WI-945 reads it as the §5.2 verdict for a
/// projection that failed with no σ-refused cover and no `Ambiguous` — non-empty
/// means no supply can ever exist, empty means the dep is fully determined and
/// merely unprovided.
///
/// WI-456 — AND "MERELY UNPROVIDED" NO LONGER MEANS SILENT. That gap used to fall
/// through to a no-dict classification that loaded clean and died at eval; it is now
/// parked as [`RequirementRefusal::no_scope_route`] and decided against the callee's
/// body. So an empty answer here selects WHICH refusal, not whether there is one.
fn unconstrained_elements(
    kb: &mut KnowledgeBase,
    dep: &RequiresEntry,
    ctx: &SigmaCtx,
) -> Vec<String> {
    let Some(goal) = goal_from_requires_entry(kb, dep) else {
        return Vec::new();
    };
    let mut out: Vec<String> = Vec::new();
    for (k, v) in &goal.bindings {
        if !is_type_param_view(kb, v) {
            continue;
        }
        if matches!(sigma_class_terminal(kb, ctx, v), Some((_, false))) {
            out.push(format!(
                "`{} = {}`",
                kb.local_name_of(*k),
                format_value_for_goal(kb, v),
            ));
        }
    }
    out
}

/// WI-828: classify WHY a `require_complete` dict build failed a dep on the
/// σ-gated path. Returns `Some` only for the σ-refusal signature this ticket
/// surfaces as a load diagnostic — a coarsely-covering entry the σ-gate
/// refused (WI-821), directly (Strategy 1) or through a slot's composed
/// sub-chain (Strategy 2), or an `Ambiguous` Strategy-3 construction (an
/// unconstrained element among multiple providers). The pre-existing
/// silent-`None` classes — bare `NoMatch` (the WI-415/418 uncovered abstract
/// call) and `Cyclic` (WI-827's sphere) — keep today's behavior and return
/// `None`.
///
/// `s3_failure` is the terminal `resolve` outcome the projection search
/// itself observed, threaded out of `build_dep_projection` — never re-run
/// here. The cover re-scan, by contrast, MIRRORS Strategies 1/2's walks
/// (Strategy-2 candidates compared COMPOSED into caller scope, the same
/// one-level composition the strategy matches with): a walk-shape change
/// there must be mirrored here, or the diagnostic silently stops firing for
/// that spelling. Diagnostic strings are built only after the refusal
/// signature is confirmed.
///
/// WI-826's orientation fix landed on the OTHER walk
/// ([`requires_entry_covers_goal`], Strategy 3's scope cover), which this
/// function does not re-scan — a refusal there surfaces through `s3_failure`
/// instead. What `entries_cover` decides is unchanged, so this mirror still
/// holds.
fn explain_dep_refusal(
    kb: &mut KnowledgeBase,
    dep: &RequiresEntry,
    caller_requires: &[RequiresEntry],
    caller_sub_chains: &[Vec<RequiresEntry>],
    ctx: &SigmaCtx,
    s3_failure: Option<ResolutionResult>,
) -> Option<RequirementRefusal> {
    // A cover that holds coarsely but not under σ is precisely the entry the
    // pre-WI-821 code would have blindly forwarded.
    //
    // WI-20260918-CKD4J — BUT ONLY FOR A DEP WHOSE ELEMENT IS STILL OPEN. A fully
    // CONCRETE dep (`PartialEq[T = Int64]`, the `PartialOrd` chain of `gt(i, 0)`) was
    // never forwardable to a wildcard `requires PartialEq[T]`, so that entry is not why
    // it failed — the dep failed CONSTRUCTION, and the verdict belongs to the arms
    // below, exactly as it does when no such entry is in scope. MEASURED: with the
    // entry counted, an unrelated `requires PartialEq[T]` (sort-level, or a conditional
    // provision's `:- PartialEq[T]`) turned a call that loads without it into this
    // refusal, whose "its element is a different type parameter" was false. `Ambiguous`
    // is untouched — it is its own signature.
    let dep_is_concrete = goal_from_requires_entry(kb, dep)
        .is_some_and(|g| g.bindings.iter().all(|(_, v)| type_is_ground(kb, v)));
    let caller_requires: &[RequiresEntry] = if dep_is_concrete {
        &[]
    } else {
        caller_requires
    };
    let caller_sub_chains: &[Vec<RequiresEntry>] = if dep_is_concrete {
        &[]
    } else {
        caller_sub_chains
    };
    let mut refused_entries: Vec<RequiresEntry> = Vec::new();
    for entry in caller_requires {
        if entries_cover(kb, entry, dep, None) && !entries_cover(kb, entry, dep, Some(ctx)) {
            refused_entries.push(entry.clone());
        }
    }
    for (i, sub_chain) in caller_sub_chains.iter().enumerate() {
        let mut slot_map: Option<HashMap<Symbol, Value>> = None;
        for sub in sub_chain {
            if !same_sort_canonical(kb, sub.required_sort, dep.required_sort) {
                continue;
            }
            if slot_map.is_none() {
                slot_map = Some(build_child_subst_map(kb, &caller_requires[i]));
            }
            let map = slot_map.as_ref().expect("filled on the preceding line");
            let composed = RequiresEntry {
                required_sort: sub.required_sort,
                spec: substitute_in_spec(kb, &sub.spec, map),
                supply: sub.supply,
            };
            if entries_cover(kb, &composed, dep, None)
                && !entries_cover(kb, &composed, dep, Some(ctx))
            {
                refused_entries.push(composed);
            }
        }
    }
    // NOT [`failure_carries_repair`], and the difference is the point: that one asks
    // whether a REPAIR can be attached (`at_call_goal` included), while this gate asks
    // the wider question of whether construction tied AT ALL — narrowing it here would
    // stop producing refusals for at-call-goal ties entirely.
    let ambiguous = matches!(s3_failure, Some(ResolutionResult::Ambiguous { .. }));
    if refused_entries.is_empty() && !ambiguous {
        return None;
    }
    // Refusal confirmed — everything below is cold diagnostic rendering.
    let construction = s3_failure
        .as_ref()
        .map(|r| describe_resolution_failure(kb, r))
        .unwrap_or_default();
    let goal = goal_from_requires_entry(kb, dep);
    let dep_text = match &goal {
        Some(g) => format_goal(kb, g),
        None => kb.qualified_name_of(dep.required_sort).to_string(),
    };
    let unconstrained = unconstrained_elements(kb, dep, ctx);
    let refused_covers: Vec<String> = refused_entries
        .iter()
        .map(|e| render_requires_entry(kb, e))
        .collect();
    // WI-841: this explainer is the σ-signature one; a PIN refusal is built by the
    // caller, which is the only place that knows a pin was in force.
    Some(RequirementRefusal {
        account_names_every_repair: false,
        no_scope_route: false,
        construction_carries_repair: false,
        dep_text,
        unconstrained,
        refused_covers,
        construction,
        pinned: None,
        // WI-1102's carrier signature is the COMPLEMENT of this explainer's (every
        // element determined vs. one left open) and is built where that is known.
        unprovided: None,
        untied: None,
    })
}

/// Shared core of the Direct-path dict build (`build_dispatching_dict_direct`)
/// and the WI-415 concrete build (`build_concrete_dispatch_dict`): emit
/// `Dictionary(<one projection per `chain` entry>, impl: callee_spec_sort)`,
/// sourcing each projection from `caller_requires` via the three-strategy search
/// in `build_dep_projection`.
///
/// `chain` is the callee's DIRECT requires — one projection per slot the
/// callee body reads by `__req_<spec>` name, matching `synth_req_names` (also
/// direct) so the dict's arity equals the callee's direct-require count
/// (eval's `expand_dispatching_dict` invariant — for a PARENT-BUNDLE dictionary
/// [`dict_layout`] reads that same single list, WI-857). Transitive requires are
/// bundled recursively inside each direct projection, not flattened. The
/// Direct path passes `direct_requires_chain` verbatim; WI-415 passes a copy
/// with the call-site bindings substituted in so each entry resolves
/// concretely.
///
/// `require_complete`: when true, a dep that fails to project aborts the whole
/// dict — WI-415 needs every slot present (a short dict fails eval's arity
/// check). WI-828: on the σ-gated path (`disambig` present) an abort with the
/// σ-refusal signature is returned as `Err(RequirementRefusal)` so the call
/// site surfaces a located load diagnostic; every other abort stays the
/// silent `Ok(None)` fall-back. The Direct path passes false and silently
/// drops un-projected deps (its output is the diagnostic-only
/// `dispatch_rewrites` term), so it can never see `Err`.
///
/// WI-841 adds ONE unconditional abort to that: a dep the call site PINNED and that
/// did not project is `Err` whatever the σ signature says. The `Ok(None)` fall-back
/// means "no dictionary here; eval will inherit or value-direct", which is a
/// defensible answer to a requirement nobody spoke about and no answer at all to one
/// the author named a provider for. Measured before: such a call loaded clean and
/// died `Internal(… __req_monoid not bound …)` at eval.
fn build_dispatching_dict_from_chain(
    kb: &mut KnowledgeBase,
    // WI-20260921-3G1YT — THE CALLEE OP, but ONLY when this call site is a RULE BODY and
    // the general no-route rule may therefore apply. `None` everywhere else, and each
    // caller's `None` says why:
    //  * an OPERATION-body site passes `None` because its unsuppliable deps are PARKED
    //    and decided by [`report_unsuppliable_requirements`], which is the right machinery
    //    and already covers them;
    //  * the ETA route and [`build_dispatching_dict_direct`] pass `None` because neither
    //    can act on the verdict — the eta's `Ok(None)` is already a load error (WI-420)
    //    and the Direct path is diagnostic-only (`require_complete = false`).
    //
    // A RULE BODY is the one site that can neither park (the queue is drained before rule
    // bodies are typed) nor be rescued by value-direction when the spec has no receiver.
    // See the use below.
    rule_body_callee: Option<Symbol>,
    // WI-20260921-3G1YT — the bracket route's slot source; see
    // [`build_concrete_dispatch_dict`]'s own note on this parameter.
    held: &[HeldSpecView],
    callee_spec_sort: Symbol,
    // Proposal 066 §7 — the provision the called operation is a member of
    // ([`op_owner_provision`]): a parent bundle is the callee's FRAME, which is its
    // sort's chain under that provision.
    callee_provision: Option<Symbol>,
    chain: &[RequiresEntry],
    // WI-1033: no `caller_sort` beside this — the caller's slot NAMES now come off the
    // chain itself, so there is no second way to spell "whose slots are these".
    caller_requires: &DictChain,
    syms: &ProjectionSyms,
    require_complete: bool,
    // WI-419: call-site context for Strategy 1 same-spec disambiguation; `None`
    // on the req-insertion diagnostic path (`build_dispatching_dict_direct`).
    disambig: Option<&SigmaCtx>,
    // WI-841: the call site's explicit provider selections, per slot (§4.5).
    selected: &[InstanceSelection],
    // WI-20261005-KSSA4: which site owes this chain. A CONSTRUCTION is judged on what it
    // fixes — see the arm that reads it.
    usage: RequirementUse,
    // WI-945: where to report a dep that fails to project because an element is
    // genuinely unconstrained (§5.2) — a no-dict outcome NOTHING can later fill, as
    // opposed to the WI-415/418 gap this arm otherwise reports by staying silent.
    // `None` from the req-insertion path, which passes `require_complete = false` and
    // so never reaches this arm at all.
    mut unsuppliable: Option<&mut Option<Box<RequirementRefusal>>>,
) -> Result<Option<TermId>, Box<RequirementRefusal>> {
    // Hoist Strategy 2's per-slot direct-requires walk out of the dep loop:
    // it depends only on `caller_requires`, not on the current dep, so the
    // worst-case cost drops from O(deps × slots × |SortRequiresInfo|) to
    // O(slots × |SortRequiresInfo|). DIRECT (not transitive, WI-239): a
    // requirement value bundles only its own direct sub-requires, so
    // `requirement_at_sort(__req_i, k)`'s `k` indexes the i-th caller
    // require's *direct* sub-chain; a deeper dep falls through to Strategy 3.
    let caller_sub_chains: Vec<Vec<RequiresEntry>> = caller_requires
        .iter()
        .map(|ar| direct_requires_chain(kb, ar.required_sort))
        .collect();
    let mut proj_terms: Vec<TermId> = Vec::with_capacity(chain.len());
    // A dep some bracket in scope HOLDS, or one a construction leaves to the use that
    // fixes it: no dictionary is built for this callee.
    let mut held_any = false;
    for (j, dep) in chain.iter().enumerate() {
        // WI-20260923-WN9P8 — A FORWARD IS ANSWERED BY ITS PARAMETER'S OWN DICTIONARY,
        // before any strategy runs. `callee_spec_sort` owns this chain, so its named slot
        // at `j` is the slot this dep fills; see [`project_forwarded_slot`].
        if let Some(ctx) = disambig {
            if let Some(slot) = named_slot_of_chain(kb, callee_spec_sort, j) {
                match project_forwarded_slot(
                    kb,
                    callee_spec_sort,
                    &slot,
                    dep,
                    caller_requires,
                    ctx,
                    syms,
                ) {
                    Some(Ok(t)) => {
                        proj_terms.push(t);
                        continue;
                    }
                    Some(Err(refusal)) => return Err(refusal),
                    None => {}
                }
            }
        }
        // WI-828: have Strategy 3 hand out its terminal failure so a refusal
        // is explained from what the search itself saw, not a re-run.
        // Requested only where the explanation has a consumer.
        let pinned_witness = pinned_witness_for(kb, selected, dep.required_sort);
        let mut s3_failure: Option<ResolutionResult> = None;
        // WI-841: a PINNED dep wants the account too — its refusal is unconditional,
        // and the account is what makes it say more than "it did not work".
        let s3_slot = (require_complete && (disambig.is_some() || pinned_witness.is_some()))
            .then_some(&mut s3_failure);
        match build_dep_projection(
            kb,
            dep,
            caller_requires,
            &caller_sub_chains,
            syms,
            disambig,
            s3_slot,
            selected,
            // WI-861 — `callee_spec_sort` OWNS this chain, so it is the sort whose named
            // slots decide whether a default may answer this dep.
            rung_for_dep(kb, callee_spec_sort, dep.required_sort),
        ) {
            Some(t) => proj_terms.push(t),
            None if require_complete => {
                // WI-841: the call NAMED a provider for this dep and it did not land.
                // Unconditional — `Ok(None)` would classify a dict-less call that
                // loads clean and dies at eval, which is the WI-828 shape with an
                // explicit instruction ignored on top.
                if let Some(w) = pinned_witness {
                    return Err(Box::new(RequirementRefusal {
                        account_names_every_repair: false,
                        no_scope_route: false,
                        construction_carries_repair: false,
                        dep_text: render_requires_entry(kb, dep),
                        unconstrained: Vec::new(),
                        refused_covers: Vec::new(),
                        construction: s3_failure
                            .as_ref()
                            .map(|r| describe_resolution_failure(kb, r))
                            .unwrap_or_default(),
                        pinned: Some(if failure_carries_repair(s3_failure.as_ref()) {
                            PinnedWitness::TiedInside(w)
                        } else {
                            PinnedWitness::Unusable(w)
                        }),
                        // An author who NAMED a witness is told about the witness, not
                        // sent to write a `provides` line on the carrier.
                        unprovided: None,
                        untied: None,
                    }));
                }
                // WI-20260921-3G1YT — THE OBLIGATION IS HELD, by a `require[Spec[…]]`
                // bracket the clause declares: the clause itself saying which instance
                // its goals are at.
                //
                // FIRST among the arms below, because it is a DISCHARGE and they are all
                // verdicts on a dep nothing supplies. The outcome is the silent
                // `Ok(None)`: no dictionary is built here, and the bracket's own supplies
                // the frame.
                //
                // A VALUE IN SCOPE HELD ONE TOO, until WI-20261005-KSSA4: `total(c:
                // FiniteCollection) = size(c)` owed `Iterable[…]` and `c`'s type was taken
                // to say it held one. A value typed at a spec over a parameter is not a
                // value of that parameter, the call is refused where it is written, and
                // what the reading served is a `requires` clause's, which has a dictionary
                // ([`scope_contract_covers_dep`]).
                //
                // THE REST OF THE CHAIN IS STILL JUDGED (WI-20261005-2KV4Y). A held dep
                // means no dictionary for this callee — the bundle is all-or-nothing — but
                // not that the requirements declared after it are met. Returning here left
                // them unasked: `User requires Tag[T = K]` then `requires Store[State = S]`
                // with `Tag` held never looked at `Store`, and loaded on an `S` nothing
                // fixes — refused with the two clauses in the other order (MEASURED;
                // `wi_2kv4y_unfixed_carrier_test
                // …a_requirement_declared_after_a_held_one_is_still_owed`).
                if let Some(sigma) = disambig {
                    if scope_contract_covers_dep(kb, held, dep, sigma) {
                        held_any = true;
                        continue;
                    }
                    // WI-20261005-KSSA4 — A CONSTRUCTION IS JUDGED ON WHAT IT FIXES. A call
                    // needs its dictionary now, so an element it leaves open is refused
                    // here (§5.2). A construction needs none: the value is typed with
                    // the slot open, and the use that fixes it — the call it is passed
                    // to — supplies the requirement there. MEASURED on the first cut,
                    // which asked the construction as a call is asked: `run(user(buf(v:
                    // 1)))` at `u: User[S = Buf[T = Int64, N = 3]]` was refused as a tie
                    // between the providers at `N = 3` and `N = 4`, the argument being
                    // typed before the parameter says `N`. What a construction is refused
                    // over is a requirement NO provision could answer at what it did fix
                    // ([`some_provision_could_answer`]) — the value no operation of the
                    // sort could ever be handed a dictionary for — and one it fixed in
                    // full, where the search's own verdict stands: nothing is left for a
                    // later use to say ([`dep_leaves_something_open`]).
                    //
                    // A TIE IS NOT SUCH A VERDICT. Two providers that both answer are two
                    // dictionaries a use may be handed, and which of them is the use's to
                    // say — `Folder.twice[Monoid = AddM](acc(seed: 3))`, or a named slot
                    // the value's own type carries. A construction selects nothing.
                    if usage == RequirementUse::Construction
                        && (matches!(s3_failure, Some(ResolutionResult::Ambiguous { .. }))
                            || (dep_leaves_something_open(kb, dep, sigma)
                                && some_provision_could_answer(kb, dep, sigma)))
                    {
                        held_any = true;
                        continue;
                    }
                }
                // WI-20260919-N31XX — A `TypeValue` DEP IS NEVER BENIGNLY UNFILLED,
                // the SORT-half twin of the leg in `build_op_scoped_dicts`.
                //
                // Falling through to the silent `Ok(None)` is safe for a dep the callee
                // never reads, and most are — that is the whole reason this arm has
                // three narrower signatures before it rather than one refusal. But since
                // 065 §1's lowering, a value read of a rigid IS a dispatch through its
                // slot, so a body holding `TypeValue` evidence demonstrably reads it, and
                // an unfilled slot is an eval-time `Internal` no handler can catch.
                // MEASURED exactly so: `Holder[U = List].tyb()`, where a bare parametric
                // bracket value expands to `List[T = ?t]` (WI-20260911-RS2G4) and the
                // conditional derived instance then wants `TypeValue[T = ?t]` for a `?t`
                // nothing pins, LOADED and died
                // `Internal("… `__req_typevalue` not bound in caller frame")`.
                //
                // RAISED, not parked: the three signatures below defer because only the
                // callee's body can say whether the slot is read, and here that question
                // is already answered by the lowering.
                // WI-20260921-3G1YT — A RULE-BODY GOAL AT A SPEC NO VALUE CAN NAME.
                // The SORT-half twin of the rule in [`build_op_scoped_dicts`], and the
                // last of N31XX's two hardcodes to go: this asked
                // `dep.required_sort == anthill.reflect.TypeValue`, so one spec was
                // guarded and no other. It now asks the property that made `TypeValue`
                // need guarding, and `TypeValue` is an instance of it.
                //
                // THE THREE CONDITIONS, each doing work:
                //  * a RULE BODY (`rule_body_callee` is `Some`) — an operation-body site
                //    PARKS instead, and is decided against the callee's body by
                //    [`report_unsuppliable_requirements`], which already covers it.
                //    MEASURED: making this arm unconditional is not needed for the
                //    operation-body shapes (`test.n31xx.twobad`, `test.rs2g4x`) — they
                //    are refused by the park path either way, which is what let the
                //    hardcode be deleted at all;
                //  * NO VALUE-DIRECTED ROUTE — WI-945 exempts a rule-body site because
                //    the SLD bridge resolves dictionaries from the CONCRETE ARGUMENT
                //    VALUES at fire time. That premise fails where no value can name the
                //    carrier, and there the bridge has nothing to resolve from;
                //  * THE CALLEE'S BODY READS THE SLOT — asked here rather than parked,
                //    and sound because a rule body is typed after EVERY operation body,
                //    so the answer exists. A callee that never reads it still loads.
                //
                // MEASURED as the gap this closes: a SORT-level `requires Stamp[T = U]`
                // at a nullary user typeclass, reached from a rule body, LOADED CLEAN
                // before this arm while the `TypeValue` spelling was refused.
                if let Some(callee_op) = rule_body_callee.filter(|&op| !kb.is_builtin(op)) {
                    if !spec_is_a_marker(kb, dep.required_sort)
                        && !dep_completes_to_a_unique_provider(kb, dep, callee_spec_sort)
                    {
                        let unconstrained = disambig
                            .map(|ctx| unconstrained_elements(kb, dep, ctx))
                            .unwrap_or_default();
                        let dep_text = render_requires_entry(kb, dep);
                        let holder =
                            sort_is_a_provided_spec(kb, callee_spec_sort).then_some(callee_spec_sort);
                        return Err(Box::new(unrescuable_rule_body_refusal(
                            kb,
                            dep,
                            dep_text,
                            unconstrained,
                            callee_op,
                            holder,
                        )));
                    }
                }
                // WI-828: with a σ in hand, a refusal-signature failure (a
                // σ-refused cover / an Ambiguous construction of an
                // unconstrained element) is a load diagnostic, not a silent
                // no-dict classification that dies at eval.
                if let Some(refusal) = disambig.and_then(|ctx| {
                    explain_dep_refusal(
                        kb,
                        dep,
                        caller_requires,
                        &caller_sub_chains,
                        ctx,
                        s3_failure.clone(),
                    )
                }) {
                    return Err(Box::new(refusal));
                }
                // WI-945 — §5.2's THIRD signature, and the one that had no reader:
                // "a requirement element left genuinely unconstrained at the call …
                // is a load-time error naming the requirement, the unconstrained
                // element, ANY σ-refused covering entry, and the construction
                // outcome". The `any` is what the two arms above do not cover — they
                // fire only WITH a σ-refused cover or an `Ambiguous` construction, so
                // the plainest spelling of the rule (a caller that declares no
                // `requires` at all, an element nothing pins, no provider to tie) fell
                // through to the silent `Ok(None)` and died at eval. MEASURED as such:
                // a `sort HolderVS` with `sort V = ? / sort F = ? / requires
                // VectorSpace[V, F]`, called at a `Vec3` that pins `V` and nothing that
                // pins `F`.
                //
                // Reported through the out-parameter rather than `Err`: unlike the two
                // arms above, this one is not yet a verdict — see
                // [`UnsuppliableRequirement`] for the half of it only the callee's body
                // can answer.
                if let (Some(ctx), Some(slot)) = (disambig, unsuppliable.as_deref_mut()) {
                    let unconstrained = unconstrained_elements(kb, dep, ctx);
                    // WI-20261005-KSSA4 — AN ELEMENT OPEN FOR WANT OF A PROVISION IS
                    // REPORTED AS THE PROVISION. Where the carrier is a sort that is no
                    // instance of the spec by any route, a row is what would have said the
                    // element ([`bind_clause_params_at_carrier`]); "pin the element" then
                    // sends the author after a binding no row will ever accept. The
                    // carrier alone is read ([`unclassified_goal_carrier`]) —
                    // [`unprovided_provision`] wants every element pinned, which is the
                    // one thing this goal is not.
                    let unprovided_at_all = if unconstrained.is_empty() {
                        None
                    } else {
                        sort_carrier_providing_nothing(kb, dep).map(|carrier| {
                            UnprovidedProvision {
                                carrier,
                                spec: dep.required_sort,
                                has_a_row: false,
                                provision_in_full: None,
                            }
                        })
                    };
                    if let Some(unprovided) = unprovided_at_all {
                        *slot = Some(Box::new(RequirementRefusal {
                            account_names_every_repair: false,
                            no_scope_route: false,
                            construction_carries_repair: false,
                            dep_text: render_requires_entry(kb, dep),
                            unconstrained: Vec::new(),
                            refused_covers: Vec::new(),
                            construction: String::new(),
                            pinned: None,
                            unprovided: Some(unprovided),
                            untied: None,
                        }));
                    } else if !unconstrained.is_empty() {
                        *slot = Some(Box::new(RequirementRefusal {
                            account_names_every_repair: false,
                            no_scope_route: false,
                            construction_carries_repair: false,
                            dep_text: render_requires_entry(kb, dep),
                            unconstrained,
                            refused_covers: Vec::new(),
                            construction: s3_failure
                                .as_ref()
                                .map(|r| describe_resolution_failure(kb, r))
                                .unwrap_or_default(),
                            pinned: None,
                            unprovided: None,
                            untied: None,
                        }));
                    } else if let Some(nomatch @ ResolutionResult::NoMatch { .. }) = &s3_failure {
                        // WI-1102 — §5.2's unconstrained-element refusal and 058 §3.10's
                        // use-site discharge are COMPLEMENTS, which is why they are one
                        // `if/else` and not two passes: the first fires when an element
                        // is left open, the second exactly when none is and the carrier
                        // the call DID name provides nothing. Reaching the second used
                        // to mean falling through to `Ok(None)` — the silent no-dict
                        // that loads clean and dies at eval.
                        //
                        // BOTH SPELLINGS OF ONE PROGRAM MUST AGREE (WI-855): the
                        // op-scoped `requires` on the callee and the sort-level one on
                        // its parent are the same claim written twice, and `wi855
                        // a_body_that_reads_an_unsuppliable_slot_agrees_on_both_
                        // spellings` is the row that says so. Parking only the op half
                        // would have split them.
                        if let Some(unprovided) = unprovided_provision(kb, dep) {
                            let construction = describe_resolution_failure(kb, nomatch);
                            *slot = Some(Box::new(RequirementRefusal {
                                account_names_every_repair: false,
                                no_scope_route: false,
                                construction_carries_repair: false,
                                dep_text: render_requires_entry(kb, dep),
                                unconstrained: Vec::new(),
                                refused_covers: Vec::new(),
                                construction,
                                pinned: None,
                                unprovided: Some(unprovided),
                                untied: None,
                            }));
                        }
                    }
                    // …AND THE PLAIN CASE, which had no reader either: the scope offers NO
                    // ROUTE and none of the signatures above says why. The four arms are
                    // each about a REASON the search failed (a named witness that did not
                    // land, a σ-refused cover, an unconstrained element, a carrier with no
                    // provision); this one is the absence of any route at all, whose
                    // commonest spelling is a signature quantifying a type parameter with
                    // no `requires` to carry its dictionary (see [`RequirementRefusal::
                    // no_scope_route`]). It fell through to `Ok(None)` and died at eval as
                    // `Internal(DeferToRequirement: … not bound … frame binds [])`.
                    //
                    // PARKED like its siblings, not raised: whether the missing dictionary
                    // is a defect or an irrelevance is the CALLEE BODY's answer
                    // ([`UnsuppliableRequirement`]), and a callee that never reads the slot
                    // must keep running exactly as it did — `SortedSet.collect` reaches
                    // here on the very programs where `SortedSet.insert` must not.
                    //
                    // THE ACCOUNT IS KEPT FOR THE ARMS THAT ARE FREE, and dropped only for
                    // the one that is not (corrected by /code-review; the first cut dropped
                    // it wholesale). `describe_resolution_failure`'s whole-KB
                    // `sorts_with_constructors` scan — WI-456(b)'s measured +9% — lives ONLY
                    // in its `Ambiguous` arm. `NoMatch` is a `hint.clone()` and `Cyclic` a
                    // `path.join`, both already computed. Dropping those cost nothing and
                    // LOST the cause: a cyclic construction rendered as "nothing in the
                    // enclosing scope supplies it — declare a requirement slot", advice that
                    // cannot repair a cycle, with `construction is cyclic: A -> B -> A`
                    // printed nowhere.
                    if slot.is_none() {
                        let construction = match &s3_failure {
                            Some(
                                f @ (ResolutionResult::NoMatch { .. }
                                | ResolutionResult::Cyclic { .. }),
                            ) => describe_resolution_failure(kb, f),
                            _ => String::new(),
                        };
                        // WI-P962X: a clause over a signature member now forwards
                        // evidence. Advise that clause directly; a member still has
                        // no declaration on which to put a named slot.
                        let member_clause = dep_member_param(kb, dep, ctx).and_then(|_| {
                            let goal = goal_from_requires_entry(kb, dep)?;
                            let bindings = goal
                                .bindings
                                .iter()
                                .map(|(key, value)| {
                                    let value = match sigma_class_terminal(kb, ctx, value) {
                                        Some((v, true)) => type_param_display_name(kb, v.name()),
                                        _ => format_value_for_goal(kb, value),
                                    };
                                    format!("{} = {value}", kb.local_name_of(*key))
                                })
                                .collect::<Vec<_>>()
                                .join(", ");
                            Some(format!(
                                "{}[{bindings}]",
                                kb.qualified_name_of(goal.spec_sort)
                            ))
                        });
                        let (construction, no_scope_route) = match member_clause {
                            Some(clause) => (
                                format!("{construction}{sep}nothing in the enclosing scope supplies it: declare `requires {clause}` on the enclosing operation so the evidence is passed in",
                                    sep = if construction.is_empty() { "" } else { " — " }),
                                false,
                            ),
                            None => (construction, true),
                        };
                        *slot = Some(Box::new(RequirementRefusal {
                            account_names_every_repair: false,
                            no_scope_route,
                            construction_carries_repair: !no_scope_route,
                            dep_text: render_requires_entry(kb, dep),
                            unconstrained: Vec::new(),
                            refused_covers: Vec::new(),
                            construction,
                            pinned: None,
                            unprovided: None,
                            untied: None,
                        }));
                    }
                }
                return Ok(None);
            }
            // WI-866 — NO SHORT DICTIONARY, on this path either. This arm used to be
            // `{}`: the dep was dropped and the loop went on, so a chain entry that
            // did not project left a dictionary with FEWER slots than
            // `dict_layout(callee_spec_sort, callee_spec_sort)` counts — the exact
            // WI-857 shape (a dictionary shorter than the chain it is indexed by) at
            // the one producer WI-857 did not touch.
            //
            // MEASURED, not feared: 2434 of 100641 dictionaries emitted here across
            // the `anthill-core` suite were short — 2401 of them EMPTY where one slot
            // was wanted (`anthill.prelude.PartialOrd` alone accounts for 2101,
            // `SortedSet` 130), 25 empty where two were, and one PARTIAL
            // (`wi817.dsets.BOps`, 1 of 2), which is the shape that would mis-slot if
            // anything indexed it. All on the `require_complete = false` route, whose
            // output is `build_dispatching_dict_direct`'s — and that term is
            // diagnostic-only (`req_insertion.rs`: "Runtime reads CallClass directly
            // off the NodeOccurrence (post-WI-248) so the term-keyed redirect is now
            // diagnostic-only"), which is why 2434 malformed dictionaries could sit in
            // `kb.dispatch_rewrites` with the suite green.
            //
            // WHAT CHANGES, and it is a diagnostic surface rather than an executed
            // one: those calls now record NO rewrite instead of one whose dictionary
            // states a false shape — an empty bundle is indistinguishable from a
            // legitimately chain-free one, so the old entry told a reflection consumer
            // "this call needs no requirements" precisely where one could not be
            // built. This is the rule the function's own `require_complete` arm
            // already states ("else fall back to no dict"), applied to the path that
            // was exempt from it. MEASURED green: 4534 tests, 0 failures — no fixture
            // reads those entries, which is also why nothing had noticed.
            None => return Ok(None),
        }
    }
    // …and a construction is asked for the verdict alone: the value carries no dictionary.
    if held_any || usage == RequirementUse::Construction {
        return Ok(None);
    }
    // WI-866 — and now it can be SAID: one slot per chain entry, and the chain is the
    // one the layout counts. Both callers pass `provider_dict_entries(callee_spec_sort)`
    // (WI-869 made them), so this checks the caller's chain CHOICE as much as the loop.
    check_against_prediction(
        kb,
        DictLayout::from_halves(
            kb,
            callee_spec_sort,
            callee_spec_sort,
            callee_provision,
            proj_terms.len(),
            0,
        ),
        "the parent-bundle slot list",
    );
    Ok(Some(build_dictionary_term(
        kb,
        syms,
        callee_spec_sort,
        &proj_terms,
    )))
}

/// WI-415/WI-418: build, at COMPILE stage, the parent-bundle dispatching dict a
/// directly-called op needs in its frame when it is called from OUTSIDE its sort
/// (so the same-sort requirement-inheritance path does not apply). The op's
/// parent sort `requires Spec[T]`; each direct requirement is projected into the
/// dict two ways, per the call site:
///
/// - **Concrete (WI-415):** the per-call `subst` pins `T` (`member(2, [1,2,3])`
///   ⇒ `List.T := Int`), so the abstract `Eq[T]` requirement substitutes to the
///   concrete `Eq[Int]` and resolves against `fact Eq[Int]` (Strategy 3).
/// - **Abstract cross-sort (WI-418):** the element stays abstract but the
///   ENCLOSING sort's own `requires` covers the dep (a sort `Coll requires
///   Eq[T]` whose op delegates to `List.member` on its abstract element), so the
///   dep is FORWARDED via a Strategy-1/2 `var_ref` that reads the caller frame's
///   `__req_*` at eval — threading `Coll`'s `__req_eq` onward to `member`.
///
/// Reuses the exact projection/construction helpers `build_dispatching_dict_direct`
/// (the requirement-insertion pass) uses; the difference is the call-site
/// bindings are substituted into the callee chain FIRST — which is why this runs
/// here, in the typer, where the subst is alive (it is gone by `req_insertion`).
///
/// Returns `Ok(None)` (⇒ no dict; eval keeps its same-sort-inherit /
/// plain-apply behavior) for a SAME-SORT call (eval inherits the enclosing
/// frame's requirements) or when a requirement fails to project outside the
/// WI-828 refusal signature — rather than emit an under-arity dict eval would
/// reject. A projection failure WITH the refusal signature (a σ-refused
/// cover / an Ambiguous construction of an unconstrained element) is
/// `Err(RequirementRefusal)`: the call site must surface it as a located
/// load diagnostic (WI-828) instead of classifying a dict-less call that
/// loads clean and dies at eval.
pub(super) fn build_concrete_dispatch_dict(
    kb: &mut KnowledgeBase,
    // WI-20260921-3G1YT — THE CALLEE OP, but ONLY when this call site is a RULE BODY and
    // the general no-route rule may therefore apply. `None` everywhere else, and each
    // caller's `None` says why:
    //  * an OPERATION-body site passes `None` because its unsuppliable deps are PARKED
    //    and decided by [`report_unsuppliable_requirements`], which is the right machinery
    //    and already covers them;
    //  * the ETA route and [`build_dispatching_dict_direct`] pass `None` because neither
    //    can act on the verdict — the eta's `Ok(None)` is already a load error (WI-420)
    //    and the Direct path is diagnostic-only (`require_complete = false`).
    //
    // A RULE BODY is the one site that can neither park (the queue is drained before rule
    // bodies are typed) nor be rescued by value-direction when the spec has no receiver.
    // See the use below.
    rule_body_callee: Option<Symbol>,
    // WI-20260921-3G1YT — the bracket route's slot source: the spec instances the
    // clause's `require[…]` brackets declare ([`held_spec_views`]). Empty in an operation
    // body, which declares none, and on the ETA and Direct paths, which have no
    // environment to read one from; empty is simply "no bracket here", never a wrong
    // verdict.
    held: &[HeldSpecView],
    subst: &Substitution,
    callee_spec_sort: Symbol,
    // Proposal 066 §7 — the provision the called operation is a member of
    // ([`op_owner_provision`]): a parent bundle is the callee's FRAME, which is its
    // sort's chain under that provision.
    callee_provision: Option<Symbol>,
    caller_sort: Option<Symbol>,
    caller_requires: &DictChain,
    // WI-419: the body's param→rigid map (`env.param_rigids()`), needed to
    // disambiguate a forward among two+ same-spec caller requires (a callee element
    // unified with a rigidified caller param). WI-942: the FULL bridge — an
    // operation's own type params as well as its sort's.
    param_rigids: &[(VarId, TermId)],
    // WI-841 (058 §4.5): what the call's own bracket selected. This is the path a
    // Direct call's dictionary is BUILT on, so it is where a construction-site
    // selection (§5.3) actually decides which provider lands in the callee's frame.
    selected: &[InstanceSelection],
    // WI-20261005-KSSA4: which site owes the chain — see
    // [`build_dispatching_dict_from_chain`]'s parameter of the same name.
    usage: RequirementUse,
    // WI-945: see [`build_dispatching_dict_from_chain`]'s parameter of the same name.
    // A caller that passes `None` accepts today's silent no-dict for an unconstrained
    // element — the eta site does, because its own `Ok(None)` arm is already loud.
    unsuppliable: Option<&mut Option<Box<RequirementRefusal>>>,
) -> Result<Option<TermId>, Box<RequirementRefusal>> {
    // WI-418: a SAME-SORT call inherits the enclosing frame's requirements at
    // eval (`start_apply_same_sort` checks `inherit` — callee parent == caller
    // sort — first), so any dict built here would be ignored. Skip it. Every
    // other call (cross-sort, or no enclosing sort) builds a dict: a CONCRETE
    // dep resolves against its `fact` via Strategy 3 (WI-415); an ABSTRACT dep
    // the enclosing sort's own `requires` covers is FORWARDED via a Strategy-1/2
    // `var_ref` reading the caller frame's `__req_*` (WI-418 — e.g. a sort
    // `Coll requires Eq[T]` whose op delegates to `List.member` on its abstract
    // element, so `member` needs `Coll`'s `__req_eq` threaded onward).
    // WI-841: unless this call PINNED something the callee's chain demands. Inheriting
    // is a FORWARD — the caller's own `__req_*` — so it is the same tier-1 case as the
    // three defer/FromScope gates, and it was the one not enumerated: MEASURED, a
    // sibling call `S.inner[Monoid = AnyM](a, b)` inside `S` computed the SEARCHED
    // answer, silently, because control returned here before `selected` was read.
    // WI-869: the DICTIONARY chain, for `build_dispatching_dict_direct`'s reason —
    // this list must have one slot per name `synth_req_names(callee_spec_sort)` gives.
    let abstract_chain = provider_dict_entries(kb, callee_spec_sort, callee_provision);
    let pins_this_chain = abstract_chain
        .iter()
        .any(|e| pinned_witness_for(kb, selected, e.required_sort).is_some());
    // Proposal 066 §7.4: and only where the caller's frame IS the callee's — its chain,
    // or a chain the callee's is a prefix of. A helper calling a member of a provision
    // it is not in holds none of that provision's conditions, so the member's
    // dictionary is built here, its conditions resolved in the caller's scope, exactly
    // as a call from another carrier builds it.
    if caller_sort == Some(callee_spec_sort)
        && !pins_this_chain
        && frame_serves_callee(caller_requires, abstract_chain.provision())
        && call_is_at_callers_instance(
            kb,
            callee_spec_sort,
            &SigmaCtx {
                subst,
                param_rigids,
            },
        )
    {
        return Ok(None);
    }
    if abstract_chain.is_empty() {
        return Ok(None);
    }
    // Substitute the call-site bindings into each direct requirement so a
    // concretely-pinned dep (`Eq[T]` ⇒ `Eq[Int]`) resolves against its `fact`;
    // an abstract dep is left open for the caller-frame `var_ref` forwarding.
    let concrete_chain: Vec<RequiresEntry> = abstract_chain
        .iter()
        .map(|entry| RequiresEntry {
            required_sort: entry.required_sort,
            spec: substitute_spec_via_subst(kb, &entry.spec, subst),
            supply: entry.supply,
        })
        .collect();
    let Some(syms) = ProjectionSyms::resolve(kb) else {
        return Ok(None);
    };
    // `require_complete = true`: every direct requirement must project into the
    // dict, else fall back to no dict (a short dict fails eval's arity check).
    // WI-419: pass the call-site context so Strategy 1 can disambiguate a caller
    // that declares two+ `requires` of the same spec over distinct element
    // params (forward the dict for the element this call actually uses).
    let disambig = SigmaCtx {
        subst,
        param_rigids,
    };
    build_dispatching_dict_from_chain(
        kb,
        rule_body_callee,
        held,
        callee_spec_sort,
        callee_provision,
        &concrete_chain,
        caller_requires,
        &syms,
        true,
        Some(&disambig),
        selected,
        usage,
        unsuppliable,
    )
}

/// WI-20260921-28TAT — THE ONE WRITER of an occurrence's op-scoped evidence: build the
/// dictionaries this call site owes its callee's OWN `requires` slots, and stamp them.
///
/// WHY A FUNCTION OF ITS OWN, replacing three inline `build_op_scoped_dicts` calls that
/// each fed a `CallClass` field. An operation-level `requires` is an INPUT THE CALLER
/// OWES THE CALLEE — a fact about the callee's SIGNATURE. It has nothing to do with
/// WHERE the call dispatches, which is the only thing a `CallClass` records: all five
/// variants are rewrites ("send this call somewhere else"). While the evidence rode
/// inside `ConcreteApplyWithin`, an operation that HAS a requirement but needs NO
/// rewrite fell between the two and was handed NOTHING — silently. MEASURED on
/// `Error.reify requires TypeValue[T = T1]`: it loads clean, the typer accepts the
/// clause, every reify row still passes, and the dispatch site sees `reqs=[]`. The
/// prelude declares `reify` body-less ON PURPOSE (the boundary is a FRAME the
/// interpreter installs by symbol), so there is nothing to redirect and no
/// classification is right — which left it with no way to be handed its input.
///
/// A STAMP is what makes the two independent: the classification says where the call
/// goes, this says what it carries, and a call may need either, both or neither.
#[allow(clippy::too_many_arguments)]
pub(super) fn stamp_op_scoped_dicts(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    subst: &Substitution,
    callee_op: Symbol,
    caller_requires: &DictChain,
    param_rigids: &[(VarId, TermId)],
    selected: &[InstanceSelection],
    park: Option<OpSlotParkSite>,
    param_arg_types: &HashMap<Symbol, Value>,
    // WI-20260921-3G1YT — the bracket route's slot source; see [`build_op_scoped_dicts`].
    held: &[HeldSpecView],
    span: Option<Span>,
    usage: RequirementUse,
) -> Result<(), TypeError> {
    let dicts = build_op_scoped_dicts(
        kb,
        subst,
        callee_op,
        caller_requires,
        param_rigids,
        selected,
        park,
        param_arg_types,
        held,
    )
    // WI-1091: a TIE in the op half is a load refusal, as the sort half's is.
    .map_err(|refusal| TypeError::UnsatisfiableRequirement {
        span,
        op: callee_op,
        callee_sort: callee_op,
        usage,
        refusal,
    })?;
    // EMPTY IS NOT WRITTEN, and the asymmetry is deliberate rather than an
    // optimization: `carry_typer_stamps_from` reads an empty cell as "unstamped" and
    // leaves the destination's alone, so writing an empty vector over a carried stamp
    // would be the one way to CLEAR one. `build_op_scoped_dicts` returns empty for
    // every callee with no op half, which is nearly all of them.
    if !dicts.is_empty() {
        occ.set_op_dicts(dicts);
    }
    Ok(())
}

/// WI-20260921-EE0EP — WHY an erased named slot could not be supplied, so the diagnostic
/// names the repair that exists rather than the one that used to.
///
/// Before this ticket there was one cause and one sentence. Now the common case — a
/// top-level unwritten slot on a parameter — is SUPPLIED, and what is left are three
/// residues with three different repairs. Printing the old shared sentence at them is
/// actively misleading: it says *"write `O` in the parameter's type"* at a call whose
/// argument is not a parameter at all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErasedSlotReason {
    /// The binder IS the projection `p.<slot>` off a parameter, so the channel applies —
    /// but some other entry of the frame already covers this spec (an anonymous
    /// `requires` of the same spec, or a second parameter of the same carrier), and the
    /// body reads a GOAL rather than a parameter. Which dictionary it means is not
    /// decidable, so no slot was synthesized. See [`param_derived_requires`]'s screen.
    AmbiguousWithFrame,
    /// The binder is a skolem NOTHING SPELLS, so no argument's type can name a provider:
    /// WI-1061's nested slot (`List[T = MySet]` takes a fresh rigid per slot) or
    /// WI-1063's existential return, opened per use.
    ///
    /// MEASURED, and the message says it because an author will otherwise try the
    /// obvious thing first: a bracket AT THIS CALL does not help. `MySet[O = ByLength]
    /// .contains(mk(), x)` and `MySet.contains[O = ByLength](mk(), x)` both pin the
    /// PARAMETER's type and leave the argument's own reading `?O`, a skolem that unifies
    /// with nothing but itself — so both are refused at the argument, one step later and
    /// less clearly. The choice has to be un-erased where the value is PRODUCED.
    NoReceiver,
}

/// WI-20260921-EE0EP — the WITNESS a [`SupplySource::FromParam`] slot is filled at:
/// the provider written for `binder` in the ARGUMENT's own type.
///
/// This is the whole of "receive the argument's dictionary". The callee's parameter type
/// omits the slot, but the ARGUMENT's does not — WI-1059 leaves the call-side slot FLEX,
/// so `s: MySet[T = String]` accepts a `MySet[T = String, O = ByLength]` and the binding
/// rides in the argument's type where this reads it. No search, no construction, and so
/// no rival: the provider named here is the one the value's own construction site chose.
///
/// `None` where the argument's type names no provider either — the caller is itself
/// abstract over the slot, or the value came from an EXISTENTIAL RETURN (WI-1063), whose
/// opened skolem names nothing. Both keep the pre-existing refusal, which is decision (c).
fn param_slot_witness(
    kb: &KnowledgeBase,
    param_arg_types: &HashMap<Symbol, Value>,
    param: Symbol,
    binder: Symbol,
) -> Option<(Symbol, Value)> {
    let arg_ty = param_arg_types.get(&param)?;
    let TypeExtractor::Parameterized { bindings, .. } = extract_type(kb, arg_ty) else {
        return None;
    };
    let (_, v) = bindings.iter().find(|(k, _)| *k == binder)?;
    // THE BASE AND THE WHOLE VALUE, and the pair is what [`selections_from_slot_bindings`]
    // reads for the same reason: a witness may carry type arguments (§4.5), its BASE is
    // what identifies it, and its own named slots live in the rest
    // (`O = ByInner[OI = ByLength]`, WI-870's shape). Returning only the base drops the
    // nested binding, which that producer's doc calls out as "the very asymmetry WI-844
    // built this producer to close" — so the caller re-reads the slots off this value.
    sort_functor_of_view(kb, v).map(|base| (base, v.clone()))
}

/// WI-20260921-EE0EP — does `op`'s chain hold a slot filled from a parameter's argument
/// ([`SupplySource::FromParam`])? The gate on populating `param_arg_types`, which IS the
/// channel: a `FromParam` slot is filled by READING that map, so an empty one is not a
/// slower path but no supply at all.
///
/// **`any`, AND IT USED TO BE `all`** — a restriction that WI-20260921-3G1YT dissolved
/// rather than this ticket lifting it. While `whole_frame` was CONDITIONAL, admitting it
/// for an operation whose chain also held AUTHOR-written slots would have forwarded those
/// too, so the channel was refused for a mixed chain (and `op_requires_chain_rc` declined
/// to synthesize into one, so the two agreed). 3G1YT deleted the conditional — every call
/// now takes the whole frame chain by the general rule — and with it the reason. MEASURED
/// after the merge: with both halves relaxed, an operation writing its own `requires`
/// beside a parameter with an unwritten slot answers `true`/`false` at the two rival
/// orderings, where the `all` form left it refused. Driven by
/// [`a_mixed_chain_takes_the_channel_too`].
pub(super) fn op_has_param_derived_slot(kb: &mut KnowledgeBase, op: Symbol) -> bool {
    op_requires_chain_rc(kb, op)
        .iter()
        .any(|e| matches!(e.supply, SupplySource::FromParam { .. }))
}

/// WI-20260921-EE0EP — is the unwritten named slot whose binder value is `bound` — the
/// WI-1059 projection off one of `enclosing_op`'s parameters — carried by a `FromParam`
/// slot of that operation's own chain?
///
/// TAKES NO SLOT NAME, and that is a claim rather than a shortcut: `bound` IS the binder
/// value of the slot being asked about, and WI-1059 mints it from that slot's own short
/// name, so the projection identifies the slot. An entry for a DIFFERENT slot of the same
/// carrier does not match it (`s.P` against `FromParam { param: s, binder: O }` is
/// `false`), which is the discrimination a separate name compare would have added.
///
/// The two halves must BOTH hold, and neither implies the other. The projection says
/// which parameter the slot hangs off; the chain says a dictionary for it will actually
/// arrive. [`param_derived_requires`] builds the entry from the same condition that mints
/// the projection, so they normally agree — and this is written as a lookup rather than a
/// shape test precisely so that a day they DISAGREE is a refusal kept, not a slot read
/// out of an empty frame.
pub(super) fn param_supplied_slot(
    kb: &mut KnowledgeBase,
    enclosing_op: Option<Symbol>,
    bound: TermId,
) -> bool {
    let Some(op) = enclosing_op else {
        return false;
    };
    // The binder as the projection `p.<short>` — [`UnwrittenFill::Projection`]'s mint,
    // read back by the same `ExprCarried` decode `is_self_projection_of` uses.
    let bv = Value::term(bound);
    // [`is_self_projection_of`] is the typer's owner of "is `v` exactly `⟨recv⟩.<key>`",
    // and asking it per entry is what keeps this from hand-rolling the same shape test a
    // second time. It compares the member by SHORT name, which is what the WI-1059 mint
    // produces, and that is also what discriminates two slots of one carrier: asked of a
    // `FromParam { param: s, binder: O }` entry, the value `s.P` answers false.
    //
    op_requires_chain_rc(kb, op).iter().any(|e| match e.supply {
        SupplySource::FromParam { param, binder: b } => is_self_projection_of(kb, &bv, param, b),
        SupplySource::Required | SupplySource::SelfSupplied => false,
    })
}

/// WI-822 LEG 1 — the dictionary each OP-SCOPED requirement slot of `callee_op`
/// gets, in op-chain order, built at the call site from the per-call substitution.
/// Empty for an operation that writes no `requires` of its own, which is nearly all
/// of them and costs one memoized `is_empty()`.
///
/// The op half's supply is the CALL's, not the instance's, and that is why it is
/// built here and not folded into the dispatching dictionary. A dictionary is a
/// SPEC INSTANCE — `Dictionary(spec half ++ provider half, impl: P)`, indexed by
/// `requirement_at_sort` and laid out by [`DictLayout`] — whereas an op-scoped
/// requirement is evidence about THIS CALL of THIS OPERATION, belonging to no
/// instance. Appending it to the instance would make every layout reader op-aware
/// for a thing no instance has.
///
/// BEST-EFFORT, PER SLOT, and deliberately not `require_complete`: a slot that does
/// not project is `None` and is simply absent from the callee's frame. That is the
/// decision WI-822 LEG 2 already measured and recorded for the same channel — "has
/// an unpinnable chain" and "needs it" are different questions and only the body
/// answers the second, and refusing here broke 29 green stdlib tests whose bodies
/// never read the slot. A body that DOES read an absent slot raises the
/// frame-naming `DeferToRequirement: … not bound` from `start_apply_deferred`. The
/// all-or-nothing shape the sort half uses is wrong here for a second reason too:
/// these slots are keyed by NAME, so a partial supply cannot mis-index the rest.
///
/// EXCEPT FOR A TIE (WI-1091), which is the one absence that is a VERDICT rather than
/// a gap. "Best-effort" answers the question "could this call supply the slot?", and for
/// every other cause the honest answer is "no, and maybe nobody needs it". A tie answers
/// a DIFFERENT question — 058 tier 3 let two providers coexist and this call names
/// neither — and nothing else in the pipeline will ever report it: the load-time
/// coherence checks exempt these pairs BY DESIGN, so a tie reaching a route with no
/// bracket is exactly the case that must go loud where it is found (WI-855's rule).
/// Refusing it here is what makes the op-scoped spelling AGREE with the sort-level one,
/// which has refused the identical program at load since WI-828 —
/// `build_dispatching_dict_from_chain`'s `require_complete` arm, through the same
/// [`explain_dep_refusal`] and with the same `RequirementRefusal` payload.
///
/// MEASURED as the row that needs it: `wi855 tie_through_value_directed_dispatch_names_
/// the_requirement_and_both_providers` drives `Holder.probe(wrap(twig()))` from a WRITTEN
/// call site, so the supply is this function's and not the bridge's. Silent, its slot was
/// absent and the widened read said `__req_desc not bound … frame binds []`, naming
/// neither the tie nor the two witnesses that caused it.
///
/// AND SINCE WI-1102, a `NoMatch` at a FULLY-PINNED carrier is PARKED rather than silent
/// — 058 §3.10's use-site discharge, "'provides nothing at all' stops being an accepting
/// state". That does NOT reopen the paragraph above: "best-effort" still answers "could
/// this call supply the slot?", and the parked refusal is REPORTED by
/// [`report_unsuppliable_requirements`]. Since WI-20260921-3G1YT it is reported
/// unconditionally — the old "does the callee's body READ it?" gate is gone, and what
/// keeps a legitimate call out of the park is a DISCHARGE ROUTE
/// ([`scope_contract_covers_dep`]) rather than an excuse. See [`unprovided_provision`]
/// for the three conditions and [`OpSlotParkSite`] for the two the caller supplies.
// WI-20260909-S8CBV added the 8th parameter (`param_arg_types`). Allowed rather than
// bundled: the seven that were here are each a distinct call-site fact this function
// reads once, and a struct around them would be a carrier invented for a lint.
#[allow(clippy::too_many_arguments)]
pub(super) fn build_op_scoped_dicts(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    callee_op: Symbol,
    caller_requires: &DictChain,
    param_rigids: &[(VarId, TermId)],
    selected: &[InstanceSelection],
    // WI-1102: the call's location, `Some` exactly when this call site may PARK a
    // fully-pinned-carrier refusal — see [`OpSlotParkSite`].
    park: Option<OpSlotParkSite>,
    // WI-20260909-S8CBV: the call's param→argument-type map, for δ-grounding a
    // requirement written at a projection. Empty for every callee whose chain carries
    // none, which is all of them but this ticket's shape.
    param_arg_types: &HashMap<Symbol, Value>,
    // WI-20260921-3G1YT — the bracket route's slot source, the OP half's copy of the sort
    // half's parameter ([`held_spec_views`]). Both halves ask the one predicate
    // [`scope_contract_covers_dep`], so a dep discharged on one cannot be refused on the
    // other.
    held: &[HeldSpecView],
) -> Result<SmallVec<[Option<TermId>; 2]>, Box<RequirementRefusal>> {
    // THE NORMALIZED entries, off the very chain whose slots these dictionaries fill
    // ([`op_dict_entries`]) — not the raw `op_requires_chain_rc`, whose bare-application
    // spec every predicate below reads as binding-free. Same list, same order, same
    // shape as the sort half; the WI-1033 discipline, one channel over.
    let chain = op_dict_entries(kb, callee_op);
    let op_chain: Vec<RequiresEntry> = chain.op_entries().to_vec();
    if op_chain.is_empty() {
        return Ok(SmallVec::new());
    }
    let Some(syms) = ProjectionSyms::resolve(kb) else {
        return Ok(SmallVec::new());
    };
    let caller_sub_chains: Vec<Vec<RequiresEntry>> = caller_requires
        .iter()
        .map(|ar| direct_requires_chain(kb, ar.required_sort))
        .collect();
    let disambig = SigmaCtx {
        subst,
        param_rigids,
    };
    // WI-1102 — the queue mark this call's parks start at. A LATER slot may still raise
    // the WI-1091 tie, and that `Err` aborts the whole classification: the earlier parks
    // are then refusals for a call the caller is already refusing, and reporting both
    // gives one call site two errors. Truncated on the `Err` path below.
    let parked_mark = kb.unsuppliable_requirements.len();
    let mut out: SmallVec<[Option<TermId>; 2]> = SmallVec::new();
    // WI-20260921-3G1YT — NO LONGER ENUMERATED. The index existed for the READ
    // question: a parked op-slot refusal recorded WHICH slot it was about (a
    // `SlotToRead::Op(i)`) because this half is best-effort and name-keyed, so a body
    // reading a DIFFERENT slot was no evidence about this one. Every parked refusal is
    // now reported, so there is no per-slot question left to key.
    for (j, entry) in op_chain.iter().enumerate() {
        // Same substitution the sort half takes: a call-site-pinned element
        // (`Zeroable[HT]` at `HT := Pebble`) becomes concrete and Strategy 3
        // constructs it; one left abstract stays open for a Strategy-1/2 forward
        // out of the caller's own chain — which, WI-822, now includes the
        // CALLER's op slots, so an op-scoped requirement relays hop to hop.
        // WI-20260909-S8CBV — δ BEFORE σ, and the order is the point. A requirement
        // written at a PROJECTION (`requires Desc[T = x.E]`) names a member of the
        // RECEIVER's type, which no substitution over type VARIABLES can reach: `x` is a
        // parameter, not a tvar, so `substitute_spec_via_subst` walks straight past the
        // `ExprCarried` and the dep stays un-pinned.
        let mut delta_error: Option<String> = None;
        let projected = if param_arg_types.is_empty() || !value_contains_projection(kb, &entry.spec)
        {
            entry.spec.clone()
        } else {
            let ctx = TypeErrorContext::OperationReturn {
                op_name: callee_op,
                surface: None,
            };
            // `arg_syms` IS `None`, and that is measured rather than assumed. WI-459's
            // re-key exists for a neutral that stays keyed to the callee's formal, and it
            // is not what makes the comparison below work: the argument's OWN type
            // already carries the caller's projection (`b : Box[E = outer.b.E]`), so δ
            // GROUNDS the member to `outer.b.E` and never reaches the neutral arm.
            // MEASURED by passing the map and backing it out — ZERO rows moved, and the
            // `projected` spec read `outer.b` either way. A branch that cannot be driven
            // is not in the diff.
            match eliminate_type_projections(kb, &entry.spec, param_arg_types, None, &ctx, None) {
                Ok(v) => v,
                Err(e) => {
                    // KEPT, not swallowed — see [`delta_failure_text`]. The spec still
                    // rides on un-eliminated, so the verdict is unchanged; what changes is
                    // that the refusal says δ FAILED rather than blaming the receiver.
                    delta_error = Some(delta_failure_text(&e));
                    entry.spec.clone()
                }
            }
        };
        // A PROJECTION THAT SURVIVED δ CANNOT BE SUPPLIED FROM HERE, and this call site is
        // the only place that can say so before the program runs.
        //
        // δ grounds `x.E` when THIS call names a receiver whose element type is known
        // (`pick(box(v: red()))` ⟹ `Red`). It cannot when the caller passed its OWN
        // abstract parameter (`operation outer(b: Box) = pick(b)`): the receiver is still
        // a variable, so the slot pins nothing and is skipped — and `pick`'s body reads it
        // immediately. MEASURED: that program LOADED CLEAN and then died
        // `DeferToRequirement: __req_desc not bound in caller frame`, raised as
        // `EvalError::Internal`, which trips `bridge_op_to_eval`'s `debug_assert` and
        // ABORTS a debug build. Loading clean and aborting is the worst of the outcomes
        // available here, so it is refused where it is written.
        //
        // UNLESS THE CALLER CARRIES THE REQUIREMENT ITSELF, which is the case that WORKS
        // and must not be refused with it: `operation outer(b: Box) requires Desc[T = b.E]
        // = pick(b)` answers `7`, because the caller's own slot supplies what this call
        // cannot ground. The gate is therefore "does the caller declare a projection-
        // carried requirement at this same spec base", not "did δ fail" — measured in
        // both directions, one row each.
        //
        // THE COMPARISON IS EXACT — the whole re-keyed spec against the caller's own,
        // through `views_structurally_equal`, the codebase's one structural compare.
        //
        // A COARSER GATE ADMITS A WRONG ANSWER, measured: matching on the spec BASE plus
        // "the caller also writes a projection" let `operation outer(b: Box, c: Box)
        // requires Desc[T = c.E] = pick(b)` load, and it answered **9** — `c`'s
        // dictionary — where `b`'s `7` is the only correct answer. The caller holds ONE
        // `__req_desc` slot and the callee reads it whatever receiver it was declared at,
        // so a gate that cannot tell `b.E` from `c.E` is not merely incomplete: it is the
        // silent class this whole channel exists to avoid.
        //
        // NOT a hand-rolled key. S4 wrote one for the same question and `/code-review`
        // found it wrong twice — a head-only SHORT name made `Box[E = Leaf]` and `Box[E =
        // Other]` compare equal. `views_structurally_equal` compares deeply and
        // carrier-blind, which is what the re-keyed neutrals need: both sides are now
        // `ExprCarried(Ref(<caller's own binder>), M)`, so equal receivers compare equal
        // and different ones do not.
        // THE NARROW PREDICATE — see [`value_contains_expr_carried`]. A pre-existing
        // `RigidTypeProjection` chain entry must reach the ordinary unpinnable path, not
        // this refusal, or widening the chain takes away a supply that used to work.
        if value_contains_expr_carried(kb, &projected) {
            let caller_covers = caller_requires
                .iter()
                .any(|ar| views_structurally_equal(kb, &projected, &ar.spec));
            if !caller_covers {
                kb.unsuppliable_requirements.truncate(parked_mark);
                // RENDERED FROM THE RE-KEYED SPEC, not from `entry`. The author reads this
                // message at THEIR call site, where the receiver is their own binder
                // (`outer.b`); printing the callee's formal (`pick.x`) would name a
                // parameter of a different declaration and read as an internal detail.
                let shown = RequiresEntry {
                    required_sort: entry.required_sort,
                    spec: projected.clone(),
                    supply: entry.supply,
                };
                return Err(Box::new(RequirementRefusal {
                    account_names_every_repair: false,
                    no_scope_route: false,
                    construction_carries_repair: false,
                    dep_text: render_requires_entry(kb, &shown),
                    unconstrained: Vec::new(),
                    refused_covers: Vec::new(),
                    construction: match &delta_error {
                        Some(d) => format!(
                            "its carrier is a projection that could not be eliminated \
                             here: {d}"
                        ),
                        None => "its carrier is a projection this call does not ground, \
                                 and no `requires` of the caller names that same receiver \
                                 — annotate the caller with this exact requirement, or \
                                 pass a receiver whose member is known here"
                            .to_owned(),
                    },
                    pinned: None,
                    unprovided: None,
                    untied: None,
                }));
            }
        }
        let dep = RequiresEntry {
            required_sort: entry.required_sort,
            spec: substitute_spec_via_subst(kb, &projected, subst),
            supply: entry.supply,
        };
        let dep = dep_completed_at_carrier(kb, &dep).unwrap_or(dep);
        // WI-20260923-WN9P8 — the sort half's forward rule, on the op half: a slot of the
        // callee's OWN bound to one of the caller's parameters is that parameter's
        // dictionary or a refusal. MEASURED without it: a set typed `O = P` passed into
        // `add[E, OE](…) requires OE: WeakOrd[E]` got the caller's `OX` and inserted in
        // its order.
        if let Some(slot) = named_slot_of_chain(kb, callee_op, j) {
            match project_forwarded_slot(
                kb,
                callee_op,
                &slot,
                &dep,
                caller_requires,
                &disambig,
                &syms,
            ) {
                Some(Ok(t)) => {
                    out.push(Some(t));
                    continue;
                }
                Some(Err(refusal)) => {
                    kb.unsuppliable_requirements.truncate(parked_mark);
                    return Err(refusal);
                }
                None => {}
            }
        }
        // WI-1091: ask the search for its terminal outcome, so the tie below is the one
        // THIS search saw rather than a re-run that could disagree with it — the same
        // discipline (and the same out-parameter) `build_dispatching_dict_from_chain`
        // uses on the sort half.
        let mut s3_failure: Option<ResolutionResult> = None;
        // WI-20260921-EE0EP — A PARAM-DERIVED SLOT IS PINNED BY ITS ARGUMENT, and the pin
        // REPLACES the call's selection list for this dep rather than joining it.
        //
        // It is a PIN rather than a separate construction so that everything downstream is
        // the pipeline that already exists: Strategy 3 builds the dictionary, the tie and
        // the refusal diagnostics stay the ones an author already reads, and a slot whose
        // argument names no provider falls through to exactly today's verdict.
        //
        // AN `InstanceSelection` IS KEYED BY THE SPEC, which is the whole reason: as
        // [`selections_from_slot_bindings`]' doc puts it, "a sort with two same-spec named
        // slots carries two witnesses in one type … and first-matching would pin one onto
        // both deps". `pinned_selection_for` is a `.find`, so a selection already in the
        // list for this spec BASE wins over anything appended after it — and the two need
        // not even agree on the element. MEASURED: a callee declaring
        // `requires O: WeakOrd[String]` (whose `a: MySet[T = String, O = O]` derives
        // `WeakOrd -> Alphabetical`) beside an unwritten `b: MySet[T = Int64]` answered
        // `b`'s `WeakOrd[T = Int64]` dep with `Alphabetical` — loud here only by luck,
        // because `Alphabetical` provides nothing at `Int64`; a witness that provided at
        // both elements would have answered from the wrong parameter in silence.
        //
        // A ONE-ENTRY LIST LOSES NOTHING. Strategies 1 and 2 are skipped for a pinned dep
        // by construction, and the call's other selections steer OTHER deps and this dep's
        // sub-goals — which no bracket can reach here, since the callee declares no slot
        // for it (058 §4.2). So the entries dropped are exactly the ones that must not
        // answer this dep.
        let mut pinned_by_arg: Vec<InstanceSelection> = Vec::new();
        let selected: &[InstanceSelection] = match dep.supply {
            SupplySource::FromParam { param, binder } => {
                // THE CHANNEL NOT BEING POPULATED IS NOT THE SAME AS THE ARGUMENT NOT
                // NAMING A PROVIDER, and collapsing them is a silent wrong answer
                // (review). `param_slot_witness` answers `None` for both: the legitimate
                // case is a caller that is itself abstract over the slot — the relay hop,
                // where the FORWARD answers — and the illegitimate one is a
                // `param_arg_types` map that was never filled for this parameter, which
                // means the fill cannot read anything and Strategy 3 CONSTRUCTS instead,
                // producing the rival WI-1094 refused with no diagnostic at all.
                //
                // `needs_param_arg_types` is computed for the operation NAMED AT THE CALL,
                // while `classify_pin_or_apply_within` stamps the op a dispatch was
                // REDIRECTED TO — so a spec op whose own parameters are type variables
                // gates the map off, and an override carrying a synthesized slot then
                // reads an empty one. The eta site passes an explicitly empty map for its
                // own reason. Neither can be told from a legitimate `None` at the fill, so
                // the map is asked directly: absent KEY means no channel, and that is
                // loud.
                if !param_arg_types.contains_key(&param) {
                    kb.unsuppliable_requirements.truncate(parked_mark);
                    return Err(Box::new(RequirementRefusal {
                        account_names_every_repair: false,
                        no_scope_route: false,
                        construction_carries_repair: false,
                        dep_text: render_requires_entry(kb, &dep),
                        unconstrained: Vec::new(),
                        refused_covers: Vec::new(),
                        construction: format!(
                            "it is supplied from the parameter `{}`, whose argument type \
                             this call site does not carry — so the provider the value's \
                             own construction chose cannot be read here, and constructing \
                             one would answer for this signature and not for the value. \
                             This is a call route that does not thread argument types (a \
                             redirected dispatch, or an operation used as a function \
                             value); write `{}` in the parameter's type and declare a slot \
                             for it so the evidence is passed in",
                            kb.local_name_of(param),
                            kb.local_name_of(binder),
                        ),
                        pinned: None,
                        unprovided: None,
                        untied: None,
                    }));
                }
                match param_slot_witness(kb, param_arg_types, param, binder) {
                    Some((witness, witness_value)) => {
                        // The witness's OWN named slots, off the same value — finding 6.
                        // `Err` is §4.4 check 1 on a sub-slot and belongs to the author,
                        // so it is raised rather than dropped to an empty `slots`.
                        let slots = witness_value_slot_selections(
                            kb,
                            callee_op,
                            witness,
                            &witness_value,
                            park.as_ref().and_then(|p| p.span),
                        )
                        .map_err(|e| {
                            Box::new(RequirementRefusal {
                                account_names_every_repair: false,
                                no_scope_route: false,
                                construction_carries_repair: false,
                                dep_text: render_requires_entry(kb, &dep),
                                unconstrained: Vec::new(),
                                refused_covers: Vec::new(),
                                construction: format!(
                                    "the witness this parameter's own type names carries a \
                                     slot binding that does not check: {}",
                                    e.format(kb)
                                ),
                                pinned: None,
                                unprovided: None,
                                untied: None,
                            })
                        })?;
                        pinned_by_arg.push(InstanceSelection {
                            spec_sort: dep.required_sort,
                            witness,
                            slots,
                        });
                        pinned_by_arg.as_slice()
                    }
                    None => selected,
                }
            }
            SupplySource::Required | SupplySource::SelfSupplied => selected,
        };
        let projected = build_dep_projection(
            kb,
            &dep,
            caller_requires,
            &caller_sub_chains,
            &syms,
            Some(&disambig),
            Some(&mut s3_failure),
            selected,
            // WI-861 — an OP-scoped chain: `callee_op` is the declaration that owns
            // these slots, so it is the one whose named slots decide.
            rung_for_dep(kb, callee_op, dep.required_sort),
        );
        if projected.is_none() {
            // WI-20260921-3G1YT — THE OBLIGATION IS HELD, by a `require[…]` bracket the
            // clause declares. The OP half's copy of the arm
            // [`build_dispatching_dict_from_chain`] states in full; one predicate
            // ([`scope_contract_covers_dep`]) serves both, so a dep discharged on one
            // half cannot be refused on the other.
            //
            // THE SLOT STAYS ABSENT, which is this half's own `Ok(None)`: the op half
            // is best-effort and NAME-keyed, so a discharged dep leaves its own slot
            // empty and its siblings supplied — where the sort half, being
            // all-or-nothing (`require_complete`), drops the whole dictionary. Both mean
            // "no dictionary here; the bracket's own supplies the frame".
            if scope_contract_covers_dep(kb, held, &dep, &disambig) {
                out.push(None);
                continue;
            }
            // WI-20260919-N31XX (proposal 065) — AN UNFILLED `TypeValue` SLOT IS NEVER
            // BENIGN, which is what takes it out of the silent-absence rule below.
            //
            // That rule exists for a measured reason its own comment gives: 29 stdlib
            // bodies declare a chain and NEVER READ IT, so a slot no dictionary could
            // fill costs them nothing. `TypeValue` cannot be one of them.
            // `type_value()` is NULLARY (WI-20260919-HXGXF's fact 1), so no argument and
            // no receiver names the type and the DISPATCHING DICTIONARY is the only
            // carrier of the answer — a body holding this evidence necessarily reads it
            // through the slot, and an unfilled slot is therefore either an eval-time
            // `Internal` death no handler can catch, or a clause that was pure noise.
            //
            // SO IT IS REFUSED AT THE CALL, where the information is: `mid[U](y: U) =
            // tyOf(y)` forwards its own rigid into an operation that requires evidence
            // about it, holding none and having declared none. That is 065's
            // parametricity rule at the one site that can see both halves — the callee's
            // demand and the caller's (empty) supply. Without it the rule covers the
            // READ and not the FORWARD, and a signature could still quietly depend on a
            // type it promises nothing about.
            //
            // RAISED, NOT PARKED, unlike the WI-1102 leg below: that one parks because
            // whether the callee MISSES the slot lives in its body, which may not be
            // typed yet. Here there is nothing to wait for — the answer cannot exist.
            if let Some(tie @ ResolutionResult::Ambiguous { .. }) = &s3_failure {
                // ONLY the tie is raised HERE. A σ-refused cover and a `Cyclic` stay
                // silent absences, which is what keeps the 29 stdlib bodies that have a
                // chain and never read it running. A `NoMatch` is PARKED just below —
                // it is not silent any more, but neither is it decided here.
                kb.unsuppliable_requirements.truncate(parked_mark);
                return Err(Box::new(RequirementRefusal {
                    account_names_every_repair: false,
                    no_scope_route: false,
                    // WI-456 — the account below carries the TIE'S OWN repair, so the
                    // generic tail must not append a second one contradicting it. This is
                    // the `pinned: None` peer of `PinnedWitness::TiedInside`: the sort half
                    // gets that suppression through the witness it pinned, and this route
                    // pins none — so before this flag the message printed BOTH "bind that
                    // slot in the VALUE position" and "pin the element at the call site".
                    // That is the two-checks-disagree defect WI-456(b) closed on the other
                    // two routes and left open on this one. Found by /code-review.
                    construction_carries_repair: failure_carries_repair(Some(tie)),
                    dep_text: render_requires_entry(kb, &dep),
                    unconstrained: Vec::new(),
                    refused_covers: Vec::new(),
                    construction: describe_resolution_failure(kb, tie),
                    pinned: None,
                    unprovided: None,
                    untied: None,
                }));
            }
            // TWO PARKED VERDICTS, DECIDED BY ONE `match` so a slot cannot be reported
            // twice. They are disjoint by construction — WI-1102's needs every element
            // of the dep GROUND ([`unprovided_provision`]), XSVCS's needs one of them to
            // be a caller RIGID — but writing them as two independent `if`s would leave
            // that disjointness as a fact to re-derive at every later edit, and a
            // double push is one call site with two errors.
            // WI-20260921-3G1YT — THE RULE-BODY EXEMPTION IS LIFTED FOR A DEP THE BRIDGE
            // CANNOT RESCUE. [`OpSlotParkSite::for_call`] declines a rule-body site on
            // WI-945's reason: such a goal reaches eval through the SLD bridge, which
            // resolves real provider dictionaries from the CONCRETE ARGUMENT VALUES and
            // suspends when it cannot, so an unpinned element is the ordinary case there.
            //
            // THAT PREMISE APPEALED TO RUN TIME, and WI-20260922-0DK3H WITHDREW THE
            // APPEAL: a rule body's evidence is owed at LOAD. What survives of it asks
            // only what load can see — one STRUCTURAL exemption, a MARKER spec
            // ([`spec_is_a_marker`]), which declares no operations at all and so leaves
            // its callers nothing to miss; and one question about the KB, whether the
            // provider facts determine a dictionary
            // ([`dep_completes_to_a_unique_provider`]). Neither asks what a value might
            // name at fire time. The deleted `spec_has_value_directed_route` did, which
            // is why it is gone rather than merely renamed.
            //
            // THIS IS WHAT N31XX's HARDCODE WAS, GENERALIZED. That arm asked
            // `dep.required_sort == anthill.reflect.TypeValue` and raised before this gate,
            // which is why `TypeValue` alone was protected. MEASURED: a USER typeclass of
            // the identical shape — `sort Stamp { sort T = ?; operation stamp() -> Int64 }`
            // with `stampOf[B](x: B) requires Stamp[T = B] = Stamp.stamp()` forwarded from
            // `rule names(?x, ?n) :- ?n = stampOf(?x)` — LOADED CLEAN while the `TypeValue`
            // spelling was refused. Nothing is special about `TypeValue` here except that
            // someone wrote a check for it.
            //
            // THE READ QUESTION IS STILL THE BODY'S. Parking does not refuse; it defers to
            // [`report_unsuppliable_requirements`], so a callee that never reads the slot
            // still loads and answers — which is what keeps `test.xsvcs.fwd.TT`,
            // `wi1102.witnessrow.Lawful` and `nx4fd_disc.Marked` green. "No route" makes an
            // unfilled slot UNRESCUABLE, not read.
            // WI-20260921-3G1YT — A RULE-BODY GOAL AT A SPEC NO VALUE CAN NAME: RAISED
            // HERE, NOT PARKED, AND THE PASS ORDER IS WHY.
            //
            // [`OpSlotParkSite::for_call`] declines a rule-body site on WI-945's reason —
            // such a goal reaches eval through the SLD bridge, which resolves provider
            // dictionaries from the CONCRETE ARGUMENT VALUES at fire time and suspends
            // when it cannot, so an unpinned element is the ordinary case there. That
            // premise appealed to RUN TIME, and WI-20260922-0DK3H withdrew the appeal —
            // a rule body's evidence is owed at LOAD — so the gate below asks only what
            // load can see: is the spec a MARKER ([`spec_is_a_marker`]), and do the
            // provider facts determine a dictionary
            // ([`dep_completes_to_a_unique_provider`])?
            //
            // PARKING CANNOT SERVE IT. MEASURED, by widening the park gate and watching
            // the refusal vanish: `report_unsuppliable_requirements` runs BEFORE rule
            // bodies are typed, so a rule-body park lands in an already-drained queue and
            // is dropped in silence. `check_sorts`' own `debug_assert!` says this in the
            // other direction ("nothing may park after it"), and it cannot catch the case
            // because it runs before the offending push.
            //
            // AND IT IS THE THREE RESCUE ROUTES THAT BOUND IT, not a walk of the
            // callee's body. This arm once carried a fourth conjunct asking whether that
            // body reads the slot; WI-20260921-3G1YT deleted it with both walks, because
            // a declared `requires` is owed BECAUSE IT IS DECLARED and a callee that
            // ignores its own clause should DELETE it. The conjuncts left are the two
            // above plus the site gate, and each says why at its own line.
            //
            // THIS IS N31XX's HARDCODE, GENERALIZED. That arm asked `dep.required_sort ==
            // anthill.reflect.TypeValue` and raised above this block, which is why one
            // spec was protected and no other. MEASURED: a USER typeclass of identical
            // shape — `sort Stamp { sort T = ?; operation stamp() -> Int64 }` with
            // `stampOf[B](x: B) requires Stamp[T = B] = Stamp.stamp()` reached from
            // `rule names(?x, ?n) :- ?n = stampOf(?x)` — LOADED CLEAN while the
            // `TypeValue` spelling was refused.
            if park.is_some_and(|s| s.enclosing_op.is_none())
                && !spec_is_a_marker(kb, dep.required_sort)
                && !dep_completes_to_a_unique_provider(kb, &dep, callee_op)
            {
                kb.unsuppliable_requirements.truncate(parked_mark);
                let dep_text = render_requires_entry(kb, &dep);
                return Err(Box::new(unrescuable_rule_body_refusal(
                    kb,
                    &dep,
                    dep_text,
                    Vec::new(),
                    callee_op,
                    None,
                )));
            }
            if let Some(site) = park.filter(|s| s.enclosing_op.is_some()) {
                // WI-1102 (058 §3.10) — the use-site discharge: this call PINNED a
                // carrier and the goal `Spec[T = Carrier]` has no provider. PARKED, not
                // raised, for WI-945's reason exactly one channel over — the σ that
                // proves the element is pinned lives only here, and whether the callee
                // will MISS the slot lives only in its body, which may not be typed yet.
                // See [`UnsuppliableRequirement`].
                let unprovided = match &s3_failure {
                    Some(nomatch @ ResolutionResult::NoMatch { .. }) => {
                        unprovided_provision(kb, &dep)
                            .map(|u| (u, describe_resolution_failure(kb, nomatch)))
                    }
                    _ => None,
                };
                let refusal = match unprovided {
                    Some((unprovided, construction)) => Some(RequirementRefusal {
                        account_names_every_repair: false,
                        no_scope_route: false,
                        construction_carries_repair: false,
                        dep_text: render_requires_entry(kb, &dep),
                        unconstrained: Vec::new(),
                        refused_covers: Vec::new(),
                        construction,
                        pinned: None,
                        unprovided: Some(unprovided),
                        untied: None,
                    }),
                    // WI-20260927-YCPAJ — a PARTLY pinned dep that no provision row
                    // agrees with at the elements it does pin. See
                    // [`no_provision_agrees_with_pins`].
                    // FIRST in this arm, and only a `NoMatch` asks it; a `None` falls
                    // through to the two verdicts below.
                    None => {
                        let partly_pinned = match &s3_failure {
                            Some(ResolutionResult::NoMatch { .. }) => {
                                no_provision_agrees_with_pins(kb, &dep).map(|construction| {
                                    RequirementRefusal {
                                        account_names_every_repair: false,
                                        no_scope_route: false,
                                        construction_carries_repair: true,
                                        dep_text: render_requires_entry(kb, &dep),
                                        unconstrained: Vec::new(),
                                        refused_covers: Vec::new(),
                                        construction,
                                        pinned: None,
                                        unprovided: None,
                                        untied: None,
                                    }
                                })
                            }
                            _ => None,
                        };
                        // WI-20260920-XSVCS — THE FORWARD: the carrier is a type
                        // parameter of the CALLER, and the caller declared no `requires`
                        // that covers it. See [`caller_rigid_carrier`] for why that is a
                        // verdict and not a gap.
                        let rigid = partly_pinned.or_else(|| {
                            site.enclosing_op.and_then(|enclosing_op| {
                                caller_rigid_carrier(kb, &dep, &disambig, enclosing_op).map(|c| {
                                    RequirementRefusal {
                                        account_names_every_repair: false,
                                        // RENDERED IN THE CALLER'S SPELLING, not `dep`'s. The entry
                                        // still names the CALLEE's formal (`tyOf.B`), and an author
                                        // told to declare `requires TT[T = tyOf.B]` would be copying
                                        // a parameter of a declaration that is not theirs. Same rule,
                                        // and the same reason, as the projection arm above.
                                        no_scope_route: false,
                                        construction_carries_repair: false,
                                        dep_text: c.clause.clone(),
                                        unconstrained: Vec::new(),
                                        refused_covers: Vec::new(),
                                        construction: format!(
                                            "its carrier is `{}`, a type parameter of the CALLING \
                                     operation `{}`, which declares no `requires` that \
                                     covers it — the caller's frame is the only thing that \
                                     could ever fill this slot, and it holds nothing for \
                                     `{}`. {}, or call `{}` with a type whose provision is \
                                     known here",
                                            c.carrier,
                                            kb.qualified_name_of(enclosing_op),
                                            c.carrier,
                                            c.repair(kb),
                                            kb.qualified_name_of(callee_op),
                                        ),
                                        pinned: None,
                                        unprovided: None,
                                        untied: None,
                                    }
                                })
                            })
                        });
                        // PROPOSAL 065 OPEN QUESTION 3 — LAST, because it is the arm for
                        // a carrier the two above could not name, and asking it first
                        // would take a SORT carrier's repair line ("declare `provides`
                        // on …") away from [`unprovided_provision`], which can name the
                        // declaration this one cannot. See [`former_carrier`].
                        match rigid {
                            Some(r) => Some(r),
                            None => former_carrier(kb, &dep, callee_op).map(|former| {
                                RequirementRefusal {
                                    account_names_every_repair: false,
                                    no_scope_route: false,
                                    // THE ACCOUNT CARRIES ITS OWN REPAIR — there is no
                                    // `provides` to suggest, so the generic "declare it on
                                    // the carrier" tail would name a declaration that cannot
                                    // exist. Same flag, same reason, as the tie arm above.
                                    construction_carries_repair: true,
                                    dep_text: render_requires_entry(kb, &dep),
                                    unconstrained: Vec::new(),
                                    refused_covers: Vec::new(),
                                    construction: format!(
                                        "its carrier is `{former}`, a STRUCTURAL FORMER — a \
                                     tuple or an arrow — and nothing provides `{spec}` \
                                     at it. A former cannot CARRY a provision itself (a \
                                     `provides` row is written on a sort), and the \
                                     derived instances cover sorts only, so this slot \
                                     stays empty and the call would load and then die \
                                     reading a requirement the frame never bound. Give \
                                     some sort the row that names this former — \
                                     `provides {spec}[… = {former}]` — or pass a value \
                                     whose type is a sort",
                                        spec = kb.qualified_name_of(dep.required_sort),
                                    ),
                                    pinned: None,
                                    unprovided: None,
                                    untied: None,
                                }
                            }),
                        }
                    }
                };
                if let Some(refusal) = refusal {
                    kb.unsuppliable_requirements.push(UnsuppliableRequirement {
                        span: site.span,
                        source: site.source,
                        callee_op,
                        // The OPERATION owns an op-scoped clause; its parent sort did
                        // not write it, so naming the parent would attribute the
                        // requirement to a declaration that has none.
                        callee_sort: callee_op,
                        refusal: Box::new(refusal),
                    });
                }
            }
        }
        out.push(projected);
    }
    Ok(out)
}

/// WI-20261005-KSSA4 — the refusal a call owes where one of the callee's type parameters
/// stays open because the requirement that would have said it has NO PROVISION at the
/// carrier the call names.
///
/// `total(c: FiniteCollection.C) effects FiniteCollection.E` reads `E` off the provision of
/// `FiniteCollection` at `c`'s sort. Called with a bare `Stream`, which provides none, `E`
/// was reported as an unconstrained type parameter with the advice to write it at the call
/// — `total[E = …](…)` — which answers the wrong question and, followed, only then reports
/// this requirement. `None` wherever the open parameter is not one such a clause binds, or
/// the carrier is not a sort the call has named, or some provision could answer there — the
/// carrier's own, or a generic witness's, which answers at every carrier and leaves the
/// element to the call: the unconstrained parameter is then what there is to say.
///
/// `open` IS THE PARAMETER'S VARIABLE, not its name: the member sugar mints one parameter
/// per member, and two specs with a member of one name give an operation two parameters
/// called `E`.
pub(super) fn unconstrained_for_want_of_a_provision(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    fn_sym: Symbol,
    (name, open): (Symbol, Var),
    span: Option<Span>,
) -> Option<TypeError> {
    let (spec, carrier_param, carrier_ty) = clause_binding_param_at_carrier(kb, subst, fn_sym, open)?;
    let carrier = sort_functor_of_view(kb, &carrier_ty)?;
    let carrier_pvid = type_param_global_var(kb, carrier_param)?;
    if spec_instance_at_receiver(kb, spec, carrier_pvid, &carrier_ty).is_some() {
        return None;
    }
    let carrier_short = short_name_of(kb.local_name_of(carrier_param)).to_owned();
    if some_row_could_answer(
        kb,
        spec,
        &[(carrier_short.clone(), carrier_ty.clone(), ElementAt::Type)],
    ) {
        return None;
    }
    let spec_qn = kb.qualified_name_of(spec).to_owned();
    let carrier_text = type_display_name_value(kb, &carrier_ty);
    Some(TypeError::UnsatisfiableRequirement {
        span,
        op: fn_sym,
        callee_sort: fn_sym,
        usage: RequirementUse::Call,
        refusal: Box::new(RequirementRefusal {
            account_names_every_repair: false,
            no_scope_route: false,
            construction_carries_repair: false,
            dep_text: format!("{spec_qn}[{carrier_short} = {carrier_text}]"),
            unconstrained: Vec::new(),
            refused_covers: Vec::new(),
            construction: format!(
                "no provision of `{spec_qn}` answers at `{carrier_text}`, so nothing says \
                 the `{}` this requirement determines",
                type_param_display_name(kb, name),
            ),
            pinned: None,
            unprovided: Some(UnprovidedProvision {
                carrier,
                spec,
                has_a_row: carrier_has_provision_row(kb, carrier, spec),
                provision_in_full: None,
            }),
            untied: None,
        }),
    })
}

/// WI-20261005-KSSA4 — a requirement whose clause leaves parameters of its spec UNWRITTEN,
/// at a carrier the call names: the same requirement with each of them written as that
/// carrier's provision says. `None` where the clause writes every parameter, where the
/// carrier is not a sort the call has named, or where its provision does not say one of
/// them.
///
/// The member sugar is what writes such a clause: `total(c: FiniteCollection.C) effects
/// FiniteCollection.E` requires `FiniteCollection[C = P, E = Q]` and says nothing of
/// `Element`. A parameter the clause does not write is the instance's own — there is no
/// variable for a call to fix, so only the carrier can say it. A goal that omits a
/// parameter matches no provider ([`unique_provider_completion`]'s doc says why that is
/// not relaxed), so as written the slot was left absent and the body read it (MEASURED:
/// `total(rows())` refused, by the arm that then took the pinned row for a tuple or an
/// arrow).
///
/// THE READING IS THE ONE THAT FIXED THE CLAUSE'S WRITTEN ELEMENTS
/// ([`spec_instance_at_receiver`], through `bind_op_type_params_from_op_requires`), so the
/// dictionary built is at the instance the operation's type parameters were bound from.
///
/// The carrier is the parameter those two readers of a clause take for it
/// ([`clause_carrier_param`]).
fn dep_completed_at_carrier(kb: &mut KnowledgeBase, dep: &RequiresEntry) -> Option<RequiresEntry> {
    // Read through the view, each binding on the carrier it rides: a clause's carrier may be
    // a type that holds a value, and what its provision says of an unwritten parameter may
    // be one too (a row that names a cell).
    let ViewHead::Functor {
        functor: Some(functor),
        pos_arity,
        ..
    } = dep.spec.head(kb)
    else {
        return None;
    };
    if !is_sort_view_functor(kb, functor) {
        return None;
    }
    let spec = dep.required_sort;
    let spec_params = sort_type_params_as_pairs(kb, spec).to_vec();
    let mut completed: Vec<(Symbol, Value)> = view_named_children(kb, &dep.spec).into_vec();
    let written = |kb: &KnowledgeBase, vid: VarId| {
        completed
            .iter()
            .find(|(k, _)| type_param_vid_in_sort(kb, spec, *k) == Some(vid))
            .map(|(_, v)| v.clone())
    };
    let unwritten: Vec<(Symbol, VarId)> = spec_params
        .iter()
        .filter_map(|(p, _)| Some((*p, type_param_global_var(kb, *p)?)))
        .filter(|(_, vid)| written(kb, *vid).is_none())
        .collect();
    if unwritten.is_empty() {
        return None;
    }
    let carrier_pvid = type_param_global_var(kb, clause_carrier_param(kb, spec)?)?;
    let carrier = written(kb, carrier_pvid)?;
    let instance = spec_instance_at_receiver(kb, spec, carrier_pvid, &carrier)?;
    for (param, vid) in unwritten {
        let said = instance.resolve_as_value(vid)?;
        let said = resolve_type_deep_value(kb, &instance, &said);
        completed.push((param, said));
    }
    kb.canonicalize_record_named_args(functor, &mut completed);
    let pos = view_pos_children(kb, &dep.spec, pos_arity).into_vec();
    Some(RequiresEntry {
        required_sort: spec,
        spec: kb.fn_value(functor, pos, completed),
        supply: dep.supply,
    })
}

/// WI-20260921-3G1YT — the refusal a RULE-body goal gets at a dep NOTHING can supply.
/// Written once because both halves raise it: [`build_dispatching_dict_from_chain`] for a
/// SORT-level clause and [`build_op_scoped_dicts`] for an operation-level one. They differ
/// only in which read predicate gates them (per-sort vs per-slot); the verdict and its
/// wording are one thing, and a copy would let the two drift the way WI-456(b) records for
/// the tie repairs.
///
/// `holder`: the spec whose `require[…]` bracket would hold this dep, where there is one to
/// name — the callee's own sort, on the sort half, when it is a spec some sort provides. A
/// bracket holds what its spec REQUIRES ([`scope_contract_covers_dep`] walks the declared
/// spec's direct chain), so a bracket of the dep's own spec holds nothing here. The advice
/// named that one until WI-20260925-P7VP4 ran it — MEASURED: `require[Iterable[C = List[T =
/// String]]], size(?ls, ?n)` is refused with this same message where
/// `require[FiniteCollection[C = List[T = String]]]` loads, and `require[WeakOrd[T]]` beside
/// `?c = Util.sign(?a, ?b)` is refused the same way. An operation-level clause, and a
/// sort-level one whose sort nothing provides, have no bracket to name and get none.
fn unrescuable_rule_body_refusal(
    kb: &KnowledgeBase,
    dep: &RequiresEntry,
    dep_text: String,
    unconstrained: Vec<String>,
    callee_op: Symbol,
    holder: Option<Symbol>,
) -> RequirementRefusal {
    let repairs = match holder {
        Some(holder) => format!(
            "Declare `require[{}[…]]` in the clause, whose `requires` hold it, pin the \
             element at this call",
            kb.qualified_name_of(holder),
        ),
        None => "Pin the element at this call".to_string(),
    };
    RequirementRefusal {
        account_names_every_repair: true,
        no_scope_route: false,
        construction_carries_repair: false,
        dep_text,
        unconstrained,
        refused_covers: Vec::new(),
        construction: format!(
            "this is a RULE-body goal, and nothing in the clause determines which \
             `{spec}` instance it means: no `require[…]` the clause declares holds it, \
             this call pins no element, and `{spec}`'s provider facts do not decide one \
             either. Taking the dictionary from the argument's RUNTIME VALUE instead \
             would turn a load error into a run-time one — the clause would load and \
             then report by not answering (WI-20260922-0DK3H) — so it is refused where \
             it is written. {repairs}, or call `{callee}` from an operation that \
             declares the matching `requires`",
            spec = kb.qualified_name_of(dep.required_sort),
            callee = kb.qualified_name_of(callee_op),
        ),
        pinned: None,
        unprovided: None,
        untied: None,
    }
}

/// WI-20260922-0DK3H — DO THE PROVIDER FACTS DETERMINE A DICTIONARY FOR THIS DEP?
///
/// THIS REPLACES `dep_has_searchable_pin`, and the replacement is the ticket. That
/// predicate asked whether any binding was GROUND — "so a goal built from it has
/// something to match a provider fact against at fire time". That is a RUNTIME answer to
/// a LOAD-time question: it admitted a program on the strength of the resolver *having a
/// key*, never on its *finding* anything, so a clause whose dictionary nothing determines
/// loaded and then reported by not answering. This asks instead whether the facts leave
/// exactly one answer, which is a proof.
///
/// IT IS THE SAME PROOF EVAL ALREADY RUNS, deliberately, so the two cannot drift:
/// [`unique_provider_completion`] is [`resolve_bridge_requirements`]' own step. It reads
/// provider FACTS only, excludes a provider that disagrees on an element the call DID
/// pin, declines one that leaves an open element abstract (it would answer at more than
/// one completion, which is proof the arguments do not decide), and returns `None` on a
/// second surviving completion. What the bridge does at fire time, this does at load.
///
/// THE EMPTY SCOPE IS THE POINT, not an omission: the question is what the FACTS decide,
/// and a caller slot is not a fact. Every forwarding route has already run — this is
/// reached only after [`build_dep_projection`] declined — so passing the scope would
/// re-ask, with the same inputs, a question answered `no` one call up.
///
/// A FULLY PINNED DEP NEEDS NO ARM OF ITS OWN, and that was MEASURED rather than reasoned
/// into the diff. [`unique_provider_completion`] answers `None` the moment `open` is
/// empty, so a first cut added `resolve_bridge_requirements`' `if all_pinned { goal }`
/// branch beside it, on the theory that such a dep would otherwise be refused although
/// its goal resolves. Backing that branch out moved ZERO rows over the whole crate
/// (4886 pass either way): the fully-pinned case cannot reach here, because Strategy 3 —
/// the static resolution inside [`build_dep_projection`] — has already answered it, and a
/// fully-pinned dep that Strategy 3 could not resolve is one this would not resolve
/// either. A branch that cannot be driven is not in the diff.
fn dep_completes_to_a_unique_provider(
    kb: &mut KnowledgeBase,
    dep: &RequiresEntry,
    owner: Symbol,
) -> bool {
    let Some(goal) = goal_from_requires_entry(kb, dep) else {
        return false;
    };
    // The EMPTY scope is the point, not an omission: this asks what the PROVIDER FACTS
    // decide, and a caller slot is not one. Every forwarding route ran already — this
    // arm is reached only after [`build_dep_projection`] declined — so consulting the
    // scope here would re-ask a question that was answered `no` one call up.
    let scope = ResolutionScope {
        available_requires: &[],
        sigma: None,
        selected: &[],
        sub_goal_requires: &[],
    };
    let rung = rung_for_dep(kb, owner, dep.required_sort);
    let goal = match unique_provider_completion(kb, &goal, &scope, rung) {
        Some(completed) => completed,
        None => return false,
    };
    matches!(
        resolve_with_rung(kb, &goal, &scope, rung),
        ResolutionResult::Resolved(_)
    )
}

/// WI-20260922-0DK3H — A DECLARED `require[Spec[…]]` BRACKET HOLDS THAT SPEC'S `requires`
/// CHAIN: §8.7's route (3). `require[FiniteCollection[C = List[T = String]]]` over a rule
/// body supplies the `Iterable[…]` that `FiniteCollection` itself requires.
///
/// The other routes are the caller's own `requires` — (1), which
/// [`build_dep_projection`]'s Strategies 1/2 answer by FORWARDING a slot — and, at a rule
/// body, the provider facts, (4) ([`dep_completes_to_a_unique_provider`]). This one is
/// neither a forward nor a search: it is a DISCHARGE.
///
/// NO DICTIONARY IS BUILT HERE. The obligation is met by what the clause states, and the
/// callee is entered with the slot unfilled; a rule-body goal reaches its provider through
/// the bridge, which resolves it from the argument values.
///
/// IT IS STRATEGY 2 WITH A DIFFERENT SLOT SOURCE, and deliberately so: Strategy 2 walks
/// `direct_requires_chain` of each spec the caller's frame holds a DICTIONARY for; this
/// walks the same chain for each spec the clause DECLARES. The composition is Strategy 2's
/// with the map read off the bracket ([`held_view_subst_map`] + [`substitute_in_spec`]),
/// the cover is its key walk ([`supply_covers_demanded_keys`]), the σ is the call's. So
/// "binding-aware" is not a property re-implemented here — it is the one the forwarding
/// strategies already enforce, asked of a second source.
///
/// BINDING-AWARENESS IS LOAD-BEARING AND WAS MEASURED TO BE. A first probe matched on the
/// spec SORT alone (`does anything in scope require an Ord at all?`), and two rows are
/// exactly that looseness biting: `wi456 …an_undeclared_ordering_is_refused_at_load` and
/// `…the_refusal_names_the_repair_and_not_a_witness_choice` hold an `Ord[T = X]` while the
/// dep wants `Ord[T = Y]`, and the sort-only cover wrongly silenced both refusals. With
/// the key walk they stay refused.
///
/// A BRACKET IS ASKED FOR WHAT THE GOAL SAYS. It is the clause itself saying which
/// instance its goals are at, over a body whose variables are untyped, so every element of
/// the goal's requirement is open by construction (§5.2): the elements the call leaves
/// open are left out of the demand, and the bracket supplies them.
///
/// A VALUE IN SCOPE HOLDS NOTHING (WI-20261005-KSSA4). This walk used to be asked of every
/// value typed at a spec as well — `total(c: FiniteCollection) = size(c)` "held"
/// `Iterable[…]` because `c`'s type said so — on the reading that a value typed at a spec
/// is a value of the spec's carrier. It is not ([`spec_has_carrier_param`]): the call is
/// refused where it is written, and what such a value was taken to hold is supplied by a
/// `requires` clause, which has a dictionary.
///
/// ONE LEVEL, NOT TRANSITIVE, for Strategy 2's own reason: a dictionary bundles its spec's
/// DIRECT sub-requires, and a dep reachable only past a second level is not something the
/// declared instance's provision necessarily carries. A deeper dep falls through and is
/// refused, which is a refusal WITHHELD from nothing — it is the conservative half.
pub(super) fn scope_contract_covers_dep(
    kb: &mut KnowledgeBase,
    held: &[HeldSpecView],
    dep: &RequiresEntry,
    sigma: &SigmaCtx,
) -> bool {
    // The demand, decoded ONCE: it does not vary with the holder, and a dep whose spec
    // does not decode is not a cover question for any of them.
    let Some((_, demand)) = unwrap_spec_view_value(kb, &dep.spec) else {
        return false;
    };
    // What the call SAYS of the requirement — [`sigma_class_terminal`]'s second component,
    // the one `unconstrained_elements` reports from: `false` is a chase that ended at an
    // unbound variable, an element nothing at this call determines, and it is left out. A
    // RIGID ends `true` and is said.
    let said: SmallVec<[(Symbol, Value); 2]> = demand
        .iter()
        .filter(|(_, v)| !matches!(sigma_class_terminal(kb, sigma, v), Some((_, false))))
        .cloned()
        .collect();
    let spec_qn = kb.qualified_name_of(dep.required_sort).to_string();
    for holder in held {
        // The same same-sort pre-filter Strategies 2 and 2b apply, and for the same
        // reason: composition never changes `required_sort`, so a chain with no
        // same-sort entry must cost a symbol compare rather than a `HashMap` plus a
        // substitution walk. This runs per dep, per call, on the load-time path.
        let chain = direct_requires_chain(kb, holder.spec_sort);
        if !chain
            .iter()
            .any(|e| same_sort_canonical(kb, e.required_sort, dep.required_sort))
        {
            continue;
        }
        let map = held_view_subst_map(kb, holder.spec_sort, &holder.view);
        for entry in chain.iter() {
            if !same_sort_canonical(kb, entry.required_sort, dep.required_sort) {
                continue;
            }
            let composed = substitute_in_spec(kb, &entry.spec, &map);
            // [`entries_cover`]'s key walk — its `same_sort_canonical` is already settled
            // by the filter above — asked of the demand the call states.
            let Some((_, supply)) = unwrap_spec_view_value(kb, &composed) else {
                continue;
            };
            if supply_covers_demanded_keys(
                kb,
                Some(sigma),
                &spec_qn,
                Supply(&supply),
                Demand(&said),
            ) {
                return true;
            }
        }
    }
    false
}

/// WI-20260921-3G1YT — IS `s` A SPEC, in the only sense a held bracket needs: something
/// a CARRIER provides, as opposed to something that IS a carrier. A bracket over a carrier
/// (`require[SortedSet[…]]`) declares no provision row to hold a chain.
///
/// Both legs are cheap and the first is a pre-filter for the second: a sort with no type
/// parameter has no carrier to dispatch on, so nothing could ever provide it
/// ([`clause_is_dispatchable`], WI-20260921-28TAT).
fn sort_is_a_provided_spec(kb: &KnowledgeBase, s: Symbol) -> bool {
    clause_is_dispatchable(kb, s) && spec_has_any_providers(kb, s)
}

/// WI-20260921-3G1YT — the composition map for a HELD view: the spec's own type
/// parameters ↦ what this value's type binds them to, so a chain entry written in the
/// spec's vocabulary (`Iterable[C = FiniteCollection.C, …]`) is rewritten into the
/// value's (`Iterable[C = XC, …]`).
///
/// NOT [`build_child_subst_map`], and the difference is the whole reason this exists.
/// That one decodes through [`unwrap_spec_view_value`], which recognizes the
/// `SortView(base, …)` term a `requires` entry carries and answers "NO BINDINGS" for the
/// PLAIN applied type `S[C = κ, …]`. A value's TYPE wears the plain spelling — MEASURED,
/// `c: FiniteCollection` arrives as `Fn{FiniteCollection, C: …, Element: …, E: …}` — so
/// composing through that one produced an EMPTY map, left every binding at the spec's own
/// formal (`Iterable[C = FiniteCollection.C]`), and no cover could ever match.
///
/// Read over [`TermView`] so the three carriers (`Value::Term` / `Entity` / `Node`) decode
/// identically, each binding on the carrier it rides: a type that holds a value (`Hold[C =
/// Buf[T = Int64, N = 3]]`), and an argument of a written `require[…]` bracket, ride as
/// occurrences and compose like any other. Non-type-param keys (the auto-bound `iterator`,
/// `find`, …) are harmless: they key on `<spec>.<name>`, and a chain entry's own op
/// bindings name the REQUIRED spec's operations, which no key here can collide with.
///
/// WHAT A BRACKET'S ARGUMENTS COMPOSE TO IS COMPARED WITH NOTHING YET. The demand a
/// clause's goal makes of a bracket says none of the required spec's type parameters,
/// whether or not the head types the goal's variables (MEASURED: the four asks in
/// `wi_tests`, all `require[FiniteCollection[C = List[T = String]]]` over `size(?ls, ?n)`,
/// and their typed twins), so [`scope_contract_covers_dep`] covers on the entry's sort
/// alone. Kept to the term bindings, as this was — which is none of a bracket's — no row
/// and no program found answers differently.
fn held_view_subst_map(kb: &KnowledgeBase, base: Symbol, ty: &Value) -> HashMap<Symbol, Value> {
    let mut map = HashMap::new();
    let base_qn = kb.qualified_name_of(base).to_string();
    for (key, v) in view_named_children(kb, ty) {
        let qn = format!("{base_qn}.{}", kb.local_name_of(key));
        if let Some(param) = kb.try_resolve_symbol(&qn) {
            map.insert(param, v);
        }
    }
    map
}

/// WI-20260922-0DK3H — one spec instance the clause DECLARES, as
/// [`scope_contract_covers_dep`]'s slot source: the spec, and the bracket's view of it.
#[derive(Clone)]
pub(crate) struct HeldSpecView {
    pub(super) spec_sort: Symbol,
    pub(super) view: Value,
}

/// WI-20260922-0DK3H — the spec instances this clause's written `require[Spec[…]]`
/// brackets declare ([`TypingEnv::rule_declared_specs`]): each a contract the clause holds.
///
/// IT IS A SPEC THAT HOLDS A CHAIN, NOT ANY PARAMETERISED SORT ([`sort_is_a_provided_spec`]).
/// A declared instance's provision is what contains the spec's `requires` chain; a carrier
/// has no provision row to hold a slot.
///
/// A VALUE'S TYPE IS NOT A SOURCE (WI-20261005-KSSA4) — see [`scope_contract_covers_dep`].
pub(super) fn held_spec_views(kb: &KnowledgeBase, env: &TypingEnv) -> Vec<HeldSpecView> {
    env.rule_declared_specs()
        .iter()
        .filter_map(|view| {
            let spec_sort = sort_functor_of_view(kb, view)?;
            sort_is_a_provided_spec(kb, spec_sort).then(|| HeldSpecView {
                spec_sort,
                view: view.clone(),
            })
        })
        .collect()
}

/// WI-20260922-0DK3H — DOES THIS SPEC DECLARE NO OPERATIONS AT ALL? A spec that does not
/// is a MARKER: a proof obligation with nothing to read, so an unfilled slot for one
/// costs its callers nothing and a rule-body goal is not refused over it.
///
/// THIS IS THE SURVIVING HALF OF `spec_has_value_directed_route`, and the split is the
/// ticket's own finding. That predicate bundled two unrelated claims under one name and
/// one `||`. Its receiver arm — "some operation takes a receiver eval could classify a
/// carrier from, so a VALUE can name a provider at fire time" — was the runtime dispatch
/// WI-20260922-0DK3H removes, and it is gone with its two eval readers
/// (`self_receiver_param_index`, `spec_carrier_param_candidates`, still eval's own and
/// unchanged there). Its empty-operations arm is not an appeal to run time at all: it is
/// a STRUCTURAL FACT about the declaration, decidable at load, and deleting it with the
/// rest would have been a different change wearing the same name.
///
/// MEASURED, and why the arm is kept rather than argued for: without it 42 rows fail —
/// all 16 `wi_9wvt7_error_reify_test` rows on `ErrorTag[T = <tuple>]`, and
/// `eval_test::m3_float_comparison_and_max` on an `Eq[T = Float]` that `Float provides Eq`
/// answers. `anthill.prelude.Eq` declares only `sort T = ?` (eq/neq live on `PartialEq`,
/// WI-644) and `anthill.prelude.ErrorTag` declares nothing at all.
///
/// NOT A VERDICT ON ITS OWN, in either direction: it EXEMPTS, and the refusal it guards
/// needs [`dep_completes_to_a_unique_provider`] to fail as well.
fn spec_is_a_marker(kb: &KnowledgeBase, spec_sort: Symbol) -> bool {
    crate::kb::op_requirements::operations_of_sort(kb, spec_sort).is_empty()
}

/// WI-883 — does `spec` declare an operation with NO IMPLEMENTATION OF ITS OWN — no body,
/// and none the host owes ([`host_implements`])? Only then does calling into it need an
/// INSTANCE: that member's code is what a provision supplies.
///
/// A sort whose every operation runs by itself is a PARAMETERIZED MODULE, not an
/// interface. `sort SortHolder { sort T = ?  requires Ord[T]  operation cmp(a: T, b: T)
/// = WeakOrd.compare(a, b) }` is called at `Int64` by
/// `vec3_ops_test::one_parameter_spec_op_scoped_requires_now_agrees_and_dispatches` and
/// answers: what it owes is its DECLARED `requires Ord[T]`, which WI-1102 discharges, and
/// nobody provides — or could be asked to provide — a `SortHolder`. `WeakOrd` is the
/// other kind: `compare` is body-less, so its defaulted `max` needs the carrier's.
///
/// A STRUCTURAL FACT about the declaration, decidable at load — the sibling of
/// [`spec_is_a_marker`], which exempts the other end (no operations at all).
pub(super) fn spec_has_an_abstract_member(kb: &KnowledgeBase, spec: Symbol) -> bool {
    crate::kb::op_requirements::operations_of_sort(kb, spec)
        .iter()
        .any(|&op| !host_implements(kb, op) && !op_has_runnable_body(kb, op))
}

/// WI-1102 — a call site permitted to PARK an op-slot refusal, and the location it would
/// carry. `None` means "do not park here", which is a decision about the SITE and not
/// about the dep; each caller's `None` says why at its own site.
///
/// TWO GATES LIVE HERE rather than in [`build_op_scoped_dicts`], because neither is
/// visible from the dep:
///
///  * **AN OPERATION BODY ONLY.** A RULE-body goal reaches eval through the SLD bridge,
///    which resolves real provider dictionaries from the CONCRETE argument values at fire
///    time and suspends when it cannot — so a carrier that provides nothing is the
///    ORDINARY case there, not a defect. This is WI-945's own gate, one channel over,
///    and it is load-bearing: stdlib `platform.needs_rebuild`'s `gt(?t_in, ?t_out)`
///    compares two `Timestamp`s and `Ord[Timestamp]` has no provider, measured.
///  * **NOT A RESOLVER BUILTIN.** `PartialOrd.gt`/`gte`/`lt`/`lte` are registered as
///    builtins and resolve STRUCTURALLY; the default body carrying the `requires Ord[T]`
///    is never entered, so the slot is never consulted and no `provides` line would
///    change the outcome. The same exemption, for the same reason and with the same
///    witness, that [`check_one_spec_op_requirement`] takes at its own `is_builtin` gate
///    — see `wi642 builtin_comparison_op_on_concrete_no_instance_loads`. Measured
///    without it: `SortedSet.insertSorted`'s `gt(c, 0)` at `Int64` is refused in every
///    stdlib-only KB, `fact Ord[T = Int64]` living in the Rust bindings.
#[derive(Clone, Copy)]
pub(super) struct OpSlotParkSite {
    pub(super) span: Option<Span>,
    pub(super) source: crate::span::SourceId,
    /// The operation whose body wrote this call — the CALLER, or `None` in a RULE body.
    /// A refusal about a slot the caller could have declared must name the caller, so the
    /// arm that says that is gated on `Some`; the WI-1102 arm names only the callee and
    /// runs either way.
    ///
    /// WI-20260921-3G1YT made it optional. It was `Symbol`, with `for_call` returning
    /// `None` for a rule body — see the gate's own note for why that stopped being right
    /// for every dep.
    pub(super) enclosing_op: Option<Symbol>,
}

impl OpSlotParkSite {
    /// The site, or `None` when either gate above closes it.
    pub(super) fn for_call(
        kb: &KnowledgeBase,
        callee_op: Symbol,
        enclosing_op: Option<Symbol>,
        span: Option<Span>,
        source: crate::span::SourceId,
    ) -> Option<Self> {
        (!kb.is_builtin(callee_op)).then_some(Self {
            span,
            source,
            enclosing_op,
        })
    }
}

/// WI-1102 (058 §3.10, the use-site discharge) — the carrier this call pinned and the
/// provision it lacks, or `None` when this dep is not that signature.
///
/// THREE CONDITIONS, and each is a distinct population the refusal must not swallow:
///
///  1. **FULLY PINNED** — every type-parameter the spec declares is bound, and bound to a
///     fully-CONCRETE type. The same two-part test [`bridge_requirements`]' `all_pinned`
///     gate makes of a bridged goal (`type_params_of_sort` × [`type_value_is_ground`]).
///     It is the line between "this call NAMES a carrier and the carrier has no
///     provider" — a program condition an author can act on — and "a type-parameter
///     stayed abstract", where the caller's own chain or a later instantiation may still
///     supply it and no refusal is owed here. An UNPARAMETERIZED spec passes the `all`
///     vacuously and is excluded outright: there is no carrier to name.
///  2. **A NAMEABLE CARRIER PARAMETER** — [`spec_carrier_param`], bound to a sort. The
///     diagnostic's whole content is "*this sort* lacks *this provision*"; a spec whose
///     carrier parameter cannot be identified has no such sentence to make.
///  3. Decided by the caller, not here: the construction terminated `NoMatch` (no
///     provider AT these bindings — an `Ambiguous` is the tie WI-1091 already refuses and
///     a `Cyclic` is a third verdict), the callee is not a resolver builtin, and the
///     callee's body actually reads the slot.
///
/// The ticket's class (3) — a carrier for which the provision is IMPOSSIBLE, not merely
/// absent — is refused by exactly the same sentence as its class (2); see
/// [`UnprovidedProvision`] for why the distinction cannot be drawn from here.
fn unprovided_provision(
    kb: &mut KnowledgeBase,
    dep: &RequiresEntry,
) -> Option<UnprovidedProvision> {
    let goal = goal_from_requires_entry(kb, dep)?;
    let carrier = pinned_goal_carrier(kb, &goal)?;
    Some(UnprovidedProvision {
        carrier,
        spec: dep.required_sort,
        has_a_row: carrier_has_provision_row(kb, carrier, dep.required_sort),
        provision_in_full: Some(format_goal(kb, &goal)),
    })
}

/// WI-20260927-YCPAJ — the verdict [`unprovided_provision`] cannot give for a dep the call
/// pins only PART of (`Spec2[B = WIS]` with `A` left open — the bare-spec sugar's `b:
/// Spec2.B`, or the explicit `requires Spec2[B = P]`): `Some(account)` when EVERY provision
/// row of the spec provably cannot answer at some element the call did pin, so no
/// completion of the open ones can answer.
///
/// NOT THE SEARCH'S `NoMatch`, which is not evidence here: a goal that omits a type
/// parameter matches no candidate at all (see [`unique_provider_completion`]'s doc), so it
/// ends `NoMatch` although `Both provides Spec2[A = WIS, B = NoSp]` answers `Spec2[B =
/// NoSp]`. MEASURED — both calls reached this arm with the identical `NoMatch`. So the rows
/// are read, and only a row that provably cannot answer is excluded — the filter
/// [`unique_provider_completion`] applies to its rivals ([`row_binding_could_answer`]).
/// Any row this cannot read (a rule rather than a fact, a head it cannot decode) or does
/// not provably exclude (a binding that is a parameter, a conditional row at the pinned
/// sort) keeps the call admitted: this may only refuse what no row could answer.
///
/// `None` also for a dep with nothing pinned (no row can be excluded) and for a fully
/// pinned one, which [`unprovided_provision`] answers with its carrier.
fn no_provision_agrees_with_pins(kb: &mut KnowledgeBase, dep: &RequiresEntry) -> Option<String> {
    let goal = goal_from_requires_entry(kb, dep)?;
    let pinned: Vec<(String, Value)> = goal
        .bindings
        .iter()
        .filter(|(_, v)| type_is_ground(kb, v))
        .map(|(k, v)| (kb.local_name_of(*k).to_string(), v.clone()))
        .collect();
    let tparams = kb.type_params_of_sort(goal.spec_sort);
    if pinned.is_empty() || tparams.iter().all(|tp| pinned.iter().any(|(k, _)| k == tp)) {
        return None;
    }
    let spec_canon = kb.canonical_sort_sym(goal.spec_sort);
    let mut rows: Vec<String> = Vec::new();
    for rid in provides_rids_by_spec(kb, spec_canon) {
        if !kb.is_fact(rid) {
            return None;
        }
        let spec_view = provision_fact_spec(kb, rid)?;
        let provider = crate::kb::op_info::head_field_term(kb, kb.rule_head_value(rid), "sort_ref");
        let (base, row_bindings) = unwrap_spec_view_value(kb, &spec_view)?;
        if kb.canonical_sort_sym(base) != spec_canon {
            continue;
        }
        let excluded = pinned.iter().any(|(short, goal_value)| {
            row_bindings.iter().any(|(k, cand)| {
                kb.local_name_of(*k) == short.as_str()
                    && !row_binding_could_answer(kb, goal_value, cand)
            })
        });
        if !excluded {
            return None;
        }
        let provider = provider
            .and_then(|t| ref_or_nullary_name(kb.get_term(t)))
            .map(|p| kb.qualified_name_of(p).to_string())?;
        let row = SortGoal {
            spec_sort: base,
            bindings: row_bindings,
            ..goal.clone()
        };
        rows.push(format!(
            "`{provider}` provides `{}`",
            format_goal_as_written(kb, &row)
        ));
    }
    let spec = kb.qualified_name_of(goal.spec_sort);
    Some(if rows.is_empty() {
        format!("nothing provides `{spec}` at any bindings")
    } else {
        format!(
            "no provision of `{spec}` answers at these bindings, whatever the elements they \
             leave open: {} — pass arguments of a provided type, or declare the provision \
             this call needs",
            rows.join(", "),
        )
    })
}

/// How far a construction has determined one element of its sort's requirement.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ElementAt {
    /// Nothing has said it yet: a variable, or the declaring sort's own parameter left as
    /// written (an abstract binding is left as the callee's own parameter, for the
    /// caller-frame forward).
    Open,
    /// A type parameter of the constructing scope.
    ScopeParam,
    /// A sort, ground or applied.
    Type,
}

/// [`ElementAt`] of the element `t` under `ctx`.
///
/// THE TYPE VARIABLE A CONSTRUCTED VALUE KEEPS FOR A SLOT NO FIELD FIXED IS A TYPE HERE —
/// `Buf[T = Int64, N = ?]`'s `N`, which is in no value. The search reads it as it reads
/// any type that fits every provider: one provider at the instance answers, two tie, and
/// a tie is left to the use ([`build_dispatching_dict_from_chain`]'s construction arm).
/// Read as open here as well, it changed no verdict (MEASURED over this change's rows).
fn element_at<V: TermView>(kb: &KnowledgeBase, ctx: &SigmaCtx, t: &V) -> ElementAt {
    if !is_type_param_view(kb, t) {
        return ElementAt::Type;
    }
    match sigma_class_terminal(kb, ctx, t) {
        Some((_, true)) => ElementAt::ScopeParam,
        _ => ElementAt::Open,
    }
}

/// WI-20261005-KSSA4 — does `dep` leave anything to be determined: a slot, at the top or
/// inside a binding, that is neither a type nor a parameter of the scope?
///
/// `Iterable[C = Stream[…], Element = Int64, E = ?]` does — nothing the construction was
/// given says the row, and the call it is passed to may. `Store[State = Buf[T = Int64, N =
/// 5]]` does not, and neither does a requirement over the scope's own `P`. Where nothing is
/// open the search has asked the whole question, and its `NoMatch` is the answer. The row
/// census below reads each element by itself, so a row that ties two of them through one
/// parameter of its own — `Bag provides Walk[C = Self, Element = T]` — fits `Walk[C =
/// Bag[T = Int64], Element = String]` element by element and answers at no such instance
/// (MEASURED: a construction over that pair loaded).
fn dep_leaves_something_open(kb: &KnowledgeBase, dep: &RequiresEntry, ctx: &SigmaCtx) -> bool {
    // Read through the view, so a binding that holds a value is looked into as its term
    // twin is.
    fn open_leaf<V: TermView>(kb: &KnowledgeBase, ctx: &SigmaCtx, t: &V) -> bool {
        match element_at(kb, ctx, t) {
            ElementAt::Open => true,
            ElementAt::ScopeParam => false,
            ElementAt::Type => match t.head(kb) {
                ViewHead::Functor { pos_arity, .. } => {
                    view_any_child(kb, t, pos_arity, |c| open_leaf(kb, ctx, c))
                }
                _ => false,
            },
        }
    }
    unwrap_spec_view_value(kb, &dep.spec)
        .is_some_and(|(_, bindings)| bindings.iter().any(|(_, v)| open_leaf(kb, ctx, v)))
}

/// WI-20261005-KSSA4 — could ANY provision of `dep`'s spec answer at what `dep` fixes,
/// whatever its other elements turn out to be?
///
/// WHAT A DEP FIXES. A binding to a sort — ground, or an application, compared with a
/// row's argument by argument, an argument left open excluding nothing — and a binding to
/// a PARAMETER OF THE SCOPE: `mapped(p, f)` over an operation's own `P` is as fixed at `P`
/// as `mapped(5, f)` is at `Int64`, and no row written for a sort answers there. Only a row
/// that leaves the element to its own parameter does. A binding nothing has determined yet
/// fixes nothing and excludes no row ([`ElementAt`]).
fn some_provision_could_answer(
    kb: &mut KnowledgeBase,
    dep: &RequiresEntry,
    ctx: &SigmaCtx,
) -> bool {
    let Some(goal) = goal_from_requires_entry(kb, dep) else {
        return true;
    };
    let fixed: Vec<(String, Value, ElementAt)> = goal
        .bindings
        .iter()
        .map(|(k, v)| (kb.local_name_of(*k).to_string(), v.clone(), element_at(kb, ctx, v)))
        .filter(|(_, _, at)| *at != ElementAt::Open)
        .collect();
    some_row_could_answer(kb, goal.spec_sort, &fixed)
}

/// Could any `provides` row of `spec` answer at the elements `fixed` names — each by the
/// short name of the spec's parameter, the type it is fixed to, and what kind of type that
/// is?
///
/// Admitting where it cannot tell, as [`no_provision_agrees_with_pins`] is, whose row
/// reading this shares: a row that is a rule, or whose head does not decode, counts as
/// able to answer. This may only say "none could" of rows it has read. A GENERIC witness
/// is a row like any other here — its binding is its own parameter, which answers
/// anywhere — and that is what the carrier-keyed readers do not see
/// ([`carrier_is_an_instance`]).
fn some_row_could_answer(
    kb: &mut KnowledgeBase,
    spec: Symbol,
    fixed: &[(String, Value, ElementAt)],
) -> bool {
    let spec_canon = kb.canonical_sort_sym(spec);
    for rid in provides_rids_by_spec(kb, spec_canon) {
        if !kb.is_fact(rid) {
            return true;
        }
        let Some((base, row_bindings)) =
            provision_fact_spec(kb, rid).and_then(|view| unwrap_spec_view_value(kb, &view))
        else {
            return true;
        };
        if kb.canonical_sort_sym(base) != spec_canon {
            continue;
        }
        let excluded = fixed.iter().any(|(short, goal_value, at)| {
            row_bindings.iter().any(|(k, cand)| {
                kb.local_name_of(*k) == short.as_str()
                    && !match at {
                        ElementAt::ScopeParam => is_type_param_view(kb, cand),
                        _ => row_binding_could_answer(kb, goal_value, cand),
                    }
            })
        });
        if !excluded {
            return true;
        }
    }
    false
}

/// WI-20261005-KSSA4 — the carrier of `dep` where it is a SORT that is no instance of the
/// spec by any route, whatever the requirement's other elements hold.
///
/// A TYPE PARAMETER IS NOT ONE. An abstract carrier stays in the dep as the declaring
/// sort's own parameter (a concretely pinned dep is substituted, an abstract one is left
/// for the caller-frame forward), and read by its head it is a symbol like any other —
/// MEASURED: `mapped(p, f)` over an operation's own `P` was told to declare `provides
/// Iterable[…]` "on `MappedStream.Source` itself". What an abstract carrier lacks is a
/// `requires` in scope, which the unconstrained-element refusal already says.
///
/// A carrier a GENERIC witness covers does not reach this: the witness is a candidate of
/// the search, which completes the requirement from it or ties (MEASURED: `Keeper.read(
/// keep(opaque(…)))` beside `AnyCap provides Cap[C = S, Element = Int64]` answers).
fn sort_carrier_providing_nothing(kb: &KnowledgeBase, dep: &RequiresEntry) -> Option<Symbol> {
    let goal = goal_from_requires_entry(kb, dep)?;
    let param = spec_carrier_param_or_sole(kb, goal.spec_sort)?;
    let (_, bound) = goal
        .bindings
        .iter()
        .find(|(k, _)| kb.local_name_of(*k) == kb.local_name_of(param))?;
    if is_type_param_view(kb, bound) {
        return None;
    }
    unclassified_goal_carrier(kb, &goal)
}

/// Conditions 1 and 2 of [`unprovided_provision`], on a goal: the sort a FULLY PINNED
/// goal names in its spec's carrier parameter, or `None` when some parameter is still
/// open or the carrier is not a sort. Shared with [`unprovided_spec_at_carrier`] so the
/// two refusals cannot disagree about which carrier a call named.
fn pinned_goal_carrier(kb: &KnowledgeBase, goal: &SortGoal) -> Option<Symbol> {
    if !goal_pins_every_param(kb, goal) {
        return None;
    }
    goal_carrier_sort(kb, goal)
}

/// Condition 1 of [`unprovided_provision`]: the spec declares type parameters and the goal
/// binds each of them to a fully concrete type. Such a goal, rendered, is a `provides`
/// clause as it would be written ([`UnprovidedProvision::provision_in_full`]).
fn goal_pins_every_param(kb: &KnowledgeBase, goal: &SortGoal) -> bool {
    let tparams = kb.type_params_of_sort(goal.spec_sort);
    !tparams.is_empty()
        && tparams.iter().all(|tp| {
            goal.bindings
                .iter()
                .any(|(k, v)| kb.local_name_of(*k) == tp && type_is_ground(kb, v))
        })
}

/// Condition 2 of [`unprovided_provision`] ALONE: the sort a goal names in its spec's
/// carrier parameter, whatever the other parameters hold.
///
/// Split out for [`unclassified_goal_carrier`] (WI-20260926-0RPRV), whose verdict —
/// "not an instance BY ANY ROUTE, at any bindings" — never reads the other parameters, so
/// requiring them pinned only hid the carrier it is about. A carrier providing NOTHING of
/// the spec has no provision to project them from: `FiniteCollection.size(n)` at a bare
/// `Nats` leaves `Element` and `E` open, the fully-pinned test answered `None`, and the
/// call was refused only by the effect error its open `E` left behind.
fn goal_carrier_sort(kb: &KnowledgeBase, goal: &SortGoal) -> Option<Symbol> {
    // WHICH parameter the carrier goes in, on the two-rung ladder the established reader
    // cannot answer for the spec this ticket is about: [`spec_carrier_param`] finds the
    // param some declared OPERATION receives on, and `Eq` declares no operation at all
    // (its `eq` lives on the `PartialEq` it requires; `eq.anthill` has only the dormant
    // `eq_refl` law), so it answers `None` for `Eq`, `NonEq`, and every other spec that
    // is a pure lawfulness claim over a surface it inherits. The ladder — including why
    // rung 2 must exclude a SELF-REPRESENTING spec — lives at
    // [`spec_carrier_param_or_sole`], which `carrier_has_provision_row` reads too so the
    // two halves of this diagnostic cannot disagree about which parameter that is.
    // The param is read for the CARRIER alone; the repair line quotes the whole
    // requirement, so a multi-parameter spec is not narrowed to one binding.
    let param = spec_carrier_param_or_sole(kb, goal.spec_sort)?;
    let bound = goal
        .bindings
        .iter()
        .find(|(k, _)| kb.local_name_of(*k) == kb.local_name_of(param))
        .map(|(_, v)| v)?;
    // The carrier's own sort symbol: `Eq[T = Hold]` names `Hold`, and
    // `Eq[T = Box[B = Leaf]]` names `Box` — the sort that would carry the provision, so
    // the parametric case suggests the line on the container, which is where a
    // conditional provision goes (058 §3.8).
    sort_functor_of_view(kb, bound)
}

/// WI-883 (058 §3.9) — the refusal for calling an operation OF spec `goal.spec_sort` at
/// `carrier`, when no provision of that spec answers there.
///
/// THE ONE REQUIREMENT NOBODY WRITES. [`unprovided_provision`] discharges a callee's
/// DECLARED `requires` — the spec's own chain and the operation's own clauses. Calling a
/// spec's operation at `C` also asserts `Spec[T = C]` itself, and no chain carries that
/// entry, so before this a carrier providing everything the spec REQUIRES but not the spec
/// loaded clean and died at eval: `Show.show(1)` with no `Show` row on `Int64` ran into
/// "operation has no body: Show.show", and `max(p, q)` on a `P` providing `Eq` and
/// `PartialOrd` but not `WeakOrd` entered the default body and died the same way on
/// `WeakOrd.compare`. `Float` was refused only by accident — `WeakOrd` also `requires
/// Eq[T]`, which `Float` cannot meet — so the message named `Eq` and not the spec.
///
/// THE SAME SENTENCE AS WI-1102's, deliberately: the dep IS a fully pinned requirement and
/// the carrier IS what lacks it. `callee_sort` is the operation, which drops the "of
/// `Spec`" owner clause — the requirement is the spec itself, not one of its clauses.
///
/// A CALLEE THE HOST IMPLEMENTS ([`host_implements`]) is exempt, and so `None`: a host
/// implementation of the operation itself (`Error.raise`) serves every carrier, whose
/// parameter is then a payload. MEASURED: without it the stdlib's own
/// `raise(EmptyStream…)` is refused.
///
/// THE VERDICT IS "NOT AN INSTANCE BY ANY ROUTE" ([`carrier_is_an_instance`]), and not a
/// failed resolution at the call's bindings alone. MEASURED: a binding-level `NoMatch`
/// also fires where the carrier IS an instance and the call simply leaves something open
/// — `isEmpty(nil)` (element unbound), `FiniteCollection.size` over a `MutableStack.new()`,
/// a provider at a different `Relation` schema, an existential `O = ?` — and every one of
/// those loads and answers. WI-1102's "`C` does provide `S`, but no row answers here" is
/// the right sentence for a DECLARED requirement; for the implicit one it was a false
/// refusal every time it fired, so it is not asked.
pub(super) fn unprovided_spec_at_carrier(
    kb: &KnowledgeBase,
    goal: &SortGoal,
    carrier: Symbol,
    callee_op: Symbol,
    span: Option<Span>,
) -> Option<TypeError> {
    if host_implements(kb, callee_op) || carrier_is_an_instance(kb, carrier, goal.spec_sort) {
        return None;
    }
    Some(TypeError::UnsatisfiableRequirement {
        span,
        op: callee_op,
        callee_sort: callee_op,
        usage: RequirementUse::Call,
        refusal: Box::new(RequirementRefusal {
            account_names_every_repair: false,
            no_scope_route: false,
            construction_carries_repair: false,
            dep_text: format_goal_as_written(kb, goal),
            unconstrained: Vec::new(),
            refused_covers: Vec::new(),
            construction: String::new(),
            pinned: None,
            unprovided: Some(UnprovidedProvision {
                carrier,
                spec: goal.spec_sort,
                has_a_row: false,
                provision_in_full: goal_pins_every_param(kb, goal).then(|| format_goal(kb, goal)),
            }),
            untied: None,
        }),
    })
}

/// WI-883 — is `carrier` an instance of `spec` by ANY route, at any bindings? The union of
/// the readers that each see part: [`carrier_has_provision_row`] sees a WITNESS row (filed
/// under the witness, dispatching here) and misses a TRANSITIVE one; `sort_provides` sees
/// the transitive chain (`List provides Stream`, `Stream provides Iterable`) and misses a
/// witness. MEASURED: the row reader alone refused the stdlib's own `Iterable.find` at
/// `List`. (No REFLEXIVE leg: a sort's own member on its own value never reaches here in an
/// operation body — measured, `Box.get(box(1))` loads with or without one; the rule-body
/// pass, which does read the self-receiver as the carrier, exempts it itself.)
///
/// A GENERIC witness (`sort AnyM { sort E = ?  provides Monoid[T = E] }`) is an instance
/// everywhere and none of these sees it — its row binds a type parameter, not a sort. That
/// is why this is only HALF of either arm's verdict; the other half is a resolution that
/// finds such a witness (the body-less arm's dispatch, the defaulted arm's `resolve`).
pub(super) fn carrier_is_an_instance(kb: &KnowledgeBase, carrier: Symbol, spec: Symbol) -> bool {
    carrier_has_provision_row(kb, carrier, spec)
        || sort_provides(kb, carrier, spec)
}

/// WI-883 — does the HOST owe `op`'s implementation, for every carrier? A resolver builtin
/// (`PartialOrd.gt` answers structurally), an `operation_map` entry on the operation itself,
/// or the declaration's own `@[host_implemented]` claim. ONE reader, for the refusal's
/// callee exemption and for [`spec_has_an_abstract_member`] — two spellings of it
/// disagreed on the canonical symbol and on the claim (found by /code-review).
///
/// THE CLAIM IS READ AS WELL AS THE EVIDENCE, and for a different question than the one
/// WI-20260922-BRT4Y keeps to the evidence. That rule is about whether an implementation
/// EXISTS; this asks who OWES one — the host or an instance — and `@[host_implemented]`
/// is the declaration's own answer. Whether the host then supplies it is BRT4Y's check,
/// which holds claim and mapping together and refuses either without the other; asking
/// only the mapping here gives a binding-less load a SECOND diagnosis of that same absence
/// (measured: `wi931…::stdlib_alone_declares_no_store_provision`, whose load must fail for
/// the unsupplied claims only).
pub(super) fn host_implements(kb: &KnowledgeBase, op: Symbol) -> bool {
    kb.is_builtin(op)
        || kb.is_host_mapped_op(kb.canonical_sym(op))
        || crate::kb::op_info::lookup_operation_info(kb, op).is_some_and(|rec| {
            crate::kb::load::meta_has_flag(kb, rec.meta, crate::kb::load::HOST_IMPLEMENTED_ATTR)
        })
}

/// WI-883 — the carrier a spec-op call names through its GOAL when nothing classified one:
/// the sort bound at the spec's carrier parameter ([`goal_carrier_sort`]), the other
/// parameters left as they are (WI-20260926-0RPRV).
///
/// WHY NOT THE CLASSIFIER'S. `carrier_param_receiver` recognizes a carrier only through a
/// provision view, so a carrier providing NOTHING — the case [`unprovided_spec_at_carrier`]
/// is for — is never classified, and its call arrives with no statically pinned carrier.
///
/// ONLY FOR A SPEC THAT IS NOT SELF-REPRESENTING ([`spec_is_self_representing`]). Where an
/// operation receives the sort itself (`List.contains(l: List, x: T)`), the RECEIVER is
/// the carrier and the parameter is its ELEMENT — reading `List[T = Int64]` as "`Int64`
/// must provide `List`" is WI-1076's defect, and MEASURED here as ~20 refused programs
/// over `List`'s own operations. The receiver speaks for those calls, or nothing does.
/// And the answer passes the filter [`statically_pinned_carrier`] applies to a classified
/// carrier, so an abstract-spec value or the spec itself (whose runtime value is some
/// provider) is never named.
///
/// `None` TOO FOR A CARRIER THAT IS AN INSTANCE ([`carrier_is_an_instance`]) — there is
/// nothing to name — and that test runs FIRST: it is decisive at nearly every call and
/// cheap, where the two filters after it walk every operation of the spec and scan the
/// symbol table (`sort_has_constructors`). Found by /code-review on the typer's hot path.
pub(super) fn unclassified_goal_carrier(kb: &KnowledgeBase, goal: &SortGoal) -> Option<Symbol> {
    let from_goal = goal_carrier_sort(kb, goal)?;
    if carrier_is_an_instance(kb, from_goal, goal.spec_sort)
        || spec_is_self_representing(kb, kb.canonical_sort_sym(goal.spec_sort))
    {
        return None;
    }
    statically_pinned_carrier(
        kb,
        &ReceiverCarrier::NotApplicable,
        Some(from_goal),
        Some(goal.spec_sort),
    )
    .map(|c| c.sort)
}

/// PROPOSAL 065 OPEN QUESTION 3 — is this unfilled op slot's carrier a STRUCTURAL FORMER
/// (a tuple, an arrow), which no `provides` row can ever name?
///
/// A VERDICT, not a gap: the dep is GROUND, so no later instantiation can change what it
/// names, and the search for a provider has already failed by the time this is asked.
///
/// WHAT IT DOES NOT CLAIM, because the claim is FALSE and was measured so during review:
/// that a former can never be provided. A former cannot CARRY a provision — a `provides`
/// row is written on a sort — but a SORT may carry one whose spec binding IS a former,
/// and that satisfies the requirement:
///
/// ```text
/// sort Wrapper { entity wrap(n: Int64)  provides TT[T = (a: Int64, b: String)] … }
/// tyOf((a: 1, b: "x"))    -- against `tyOf[B](x: B) requires TT[T = B]`: LOADS
/// ```
///
/// Such a program never reaches here, because [`build_dep_projection`] finds that row.
/// So this arm says only "nothing provides it", which is what was searched for, and its
/// repair names the row an author could write. An earlier draft said "no instance can
/// ever name it" and advised wrapping the former in a sort — a different program from
/// the one that actually works.
///
/// WHY IT NEEDS ITS OWN ARM. The two arms beside it both answer `None` here and neither
/// is wrong to. [`unprovided_provision`] asks the same question for a SORT carrier and
/// bails at `sort_functor_of_view`, because a former has no declaration its repair line
/// could name. [`caller_rigid_carrier`] bails because the carrier is GROUND, not a
/// caller parameter. With both silent the slot fell through to the ordinary
/// silent-absence rule — and MEASURED, that is not benign here:
///
/// ```text
/// operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = Cell[V = B]
/// operation ask() -> Type = tyOf((1, 2))
/// ```
///
/// LOADED CLEAN and then died `DeferToRequirement: __req_typevalue not bound in caller
/// frame`, an `EvalError::Internal` that `bridge_op_to_eval` raises as a PANIC. Loading
/// clean and aborting is the worst outcome available, which is the verdict the
/// projection arm in [`build_op_scoped_dicts`] already reaches for this same death.
///
/// NOT KEYED TO `TypeValue`, applying WI-20260921-3G1YT's lesson rather than re-learning
/// it: that ticket deleted a `dep.required_sort == anthill.reflect.TypeValue` hardcode
/// after measuring that a user typeclass of identical shape loaded clean while the
/// `TypeValue` spelling was refused. The reason a former cannot be provided is about the
/// CARRIER, so this arm is too.
///
/// THE SORT HALF NEEDS NONE OF IT, measured, and that is this arm's control: the same
/// program with a sort-level `requires` is already refused, because
/// `build_dispatching_dict_from_chain` is all-or-nothing (`require_complete` drops an
/// incomplete dictionary whole) where this half is best-effort and per-slot.
///
/// 065 open question 3 proposed refusing "at the read, naming the row". This refuses at
/// the CALL, which is where the carrier is known — a body reading `B` cannot see that
/// some caller will pass a tuple. The former is named in the message either way.
fn former_carrier(kb: &KnowledgeBase, dep: &RequiresEntry, callee_op: Symbol) -> Option<String> {
    // A BODY-LESS CALLEE'S ABSENT DICTIONARY IS THE HOST'S TO INTERPRET, and this guard
    // is the whole reason the arm is not simply "a former cannot be provided".
    //
    // MEASURED, and it cost 20 red rows to learn: `Error.reify` declares
    // `requires ErrorTag[T = T1]` and is body-less ON PURPOSE — the boundary is a frame
    // the interpreter installs by symbol — and a TUPLE payload is a LIVE, CORRECT corpus
    // program. `wi_9wvt7_error_reify_test`'s fixture says so at its own line: "a tuple
    // type's head is the ENTITY `TypeExtractor.NamedTuple`, which names no sort, so this
    // boundary CANNOT be narrowed and must catch wide — as every boundary did before the
    // narrowing existed". The host NARROWS when the evidence is there and catches WIDE
    // when it is not, so the missing dictionary is not a death, it is the wide case.
    //
    // AN ANTHILL BODY HAS NO SUCH FALLBACK: 065 §1 lowers a value read to a dispatch
    // through the slot, so an absent one is the `DeferToRequirement` abort this arm
    // exists to prevent.
    //
    // THIS IS NOT THE BODY WALK WI-20260921-3G1YT DELETED. That one asked what a body
    // CONTAINS — whether it reads the slot — and was deleted because a declared
    // `requires` is owed because it is declared. This asks only whether an anthill body
    // EXISTS, which decides WHO interprets the absence, not whether the clause is owed.
    kb.op_body_node(callee_op)?;
    let goal = goal_from_requires_entry(kb, dep)?;
    // EVERY BINDING, not just the carrier one. `spec_carrier_param_or_sole` names the
    // parameter a declared OPERATION receives on, which is the right question for
    // [`unprovided_provision`]'s repair line ("declare `provides` on THAT sort") and the
    // wrong one here: a former in ANY ground position makes the goal unmatchable, and
    // reading only the carrier left a multi-parameter spec — a former in `U` while `T`
    // is an ordinary sort — falling through to the silent absence this arm exists to
    // close. Found by /code-review.
    let former = goal.bindings.iter().find_map(|(_, v)| {
        // A FORMER BY ITS HEAD (WI-20261005-KSSA4): an arrow or a tuple, whatever stands
        // inside it. The test was "ground, and no sort" — which read an effect ROW as a
        // former (`requires Iterable[C = P, E = {}]` at a bare list was refused naming the
        // row as "its carrier, a tuple or an arrow"), and let a former with an open part
        // through: `ti(c: Iterable.C)` called with `lambda x -> 7` loaded, an arrow being
        // the `C` of no `Iterable` whatever `x` is (MEASURED; the capability matrix's
        // `lambda / through a provision chain` cell). A sort binding is not this arm's —
        // a provision could name it, and [`unprovided_provision`] says so — nor is a
        // variable, which is one of the open cases the arms beside this one own.
        matches!(type_head(kb, v), TypeHead::Arrow | TypeHead::NamedTuple).then_some(v)
    })?;
    Some(format_value_for_goal(kb, former))
}

/// WI-20260920-XSVCS — a dep whose carrier is the CALLER's own type parameter, written
/// as the caller would have to declare it.
pub(crate) struct CallerRigidCarrier {
    /// The parameter, spelled as the CALLER wrote it (`U`, `T`) — never the callee's
    /// formal, which is a name from a declaration the author does not own.
    pub(super) carrier: String,
    /// The whole requirement re-keyed into that spelling, ready to be pasted after
    /// `requires`. The WHOLE clause and not just the carrier binding, for
    /// [`RequirementRefusal::render`]'s own measured reason one arm over: a
    /// multi-parameter spec written with a binding omitted fills the rest from its own
    /// parameters, which §5.2 legislates as a second load error — advice that trades one
    /// refusal for another.
    pub(super) clause: String,
    /// WHERE that clause goes — the calling OPERATION when the carrier is one of its
    /// `[…]` brackets, the enclosing SORT when it is one of the sort's parameters. The
    /// distinction is not cosmetic: an operation cannot declare its sort's parameter out
    /// from under it, and the corpus has one of each (`test.xsvcs.fwd.mid`'s `U`,
    /// `test.wi416.Coll`'s `T`).
    declare_on: Symbol,
}

impl CallerRigidCarrier {
    /// WI-P962X: clauses over signature members forward just as named parameters do.
    fn repair(&self, kb: &KnowledgeBase) -> String {
        let on = kb.qualified_name_of(self.declare_on);
        format!(
            "Declare `requires {}` on `{on}` so the evidence is passed in",
            self.clause
        )
    }
}

/// WI-20260920-XSVCS — is this unfilled op slot's carrier a type parameter of the
/// CALLER, which the caller declared nothing about?
///
/// THE ONE DISCRIMINATION THIS TICKET IS, and it is a VERDICT where the rest of
/// [`build_op_scoped_dicts`]' unfilled slots are a GAP. Reaching this function at all
/// means [`build_dep_projection`] found no forward, so the caller's own chain — the
/// COMPOSED one, its sort half included — covers nothing here. A carrier that is the
/// caller's rigid can be filled from NOWHERE ELSE: it is not ground, so no provider can
/// be constructed for it (that is WI-1102's case, and the `match` above takes it first);
/// it is not open, so it is not the WI-415/418 abstract-call gap that a later, more
/// pinned call site still resolves. The caller's frame is the only possible supplier and
/// it declared no slot. Nothing downstream will ever fill it, and a body that reads it
/// dies `EvalError::Internal` — not a `Raised`, so no handler sees it, and a debug build
/// ABORTS through `bridge_op_to_eval`'s `debug_assert`.
///
/// STILL PARKED, NOT RAISED, and since WI-20260921-3G1YT for ONE reason rather than two.
/// The refusal is BUILT here, where the σ that proves the carrier is a caller rigid is
/// alive, and REPORTED in [`report_unsuppliable_requirements`] once every body is typed —
/// an operation is routinely called before its own body is classified, so raising at the
/// call would answer from the sort-iteration order. What it is no longer DECIDED against
/// is the callee's body: that walk, and the 29-stdlib-bodies measurement it rested on,
/// are deleted. A body that declares a chain and never reads it is a clause to DELETE.
///
/// THE CENSUS THAT CHOSE THIS GATE over "ask whether the body reads it and refuse every
/// unfilled slot that does": instrumented at this site, a full workspace run yields 57
/// distinct unfilled op slots, of which **31 have a body that READS** the slot and stay
/// green today — the concrete-carrier population, which other routes still supply. Only
/// **4** name a caller rigid, and all four are this defect:
/// `test.n31xx.twobad` (065's own forward, refused one arm above), `test.n31xx.othersp`
/// (the same shape over a plain spec, which this ticket turns from "loads" into
/// "refused"), this ticket's `test.xsvcs.fwd`, and — the one nobody wrote as a test —
/// `test.wi416.Coll.contains`, which calls `List.contains(items, x)` on its own `T`
/// while `contains` declares `requires Eq[T]` and its body reads it. That fixture has
/// loaded clean since WI-416 and would have died `Internal` had anything called it.
///
/// IT NOW SUBSUMES N31XX's `TypeValue` ARM for every site it reaches. That leg was a
/// hardcoded `dep.required_sort == anthill.reflect.TypeValue` raising above this one; both
/// its call sites are deleted (WI-20260921-3G1YT), and the shape they shared —
/// `test.n31xx.twobad` — is refused by THIS arm, whose wording says the same thing for any
/// spec and additionally names where to declare the evidence.
///
/// WHAT IT DOES NOT REACH IS A RULE BODY, and that is the one case the hardcode was really
/// carrying. This arm needs `enclosing_op` to say "the CALLER declared no `requires`", and
/// a rule body has no operation to name — nor can it park, since
/// [`report_unsuppliable_requirements`] drains the queue before rule bodies are typed. So
/// that site RAISES at its own gate instead, on the two properties LOAD can see —
/// [`spec_is_a_marker`] and [`dep_completes_to_a_unique_provider`] (WI-20260922-0DK3H
/// replaced the single `spec_has_value_directed_route` with that pair); see
/// [`build_op_scoped_dicts`] and [`build_dispatching_dict_from_chain`] for the two
/// halves.
///
/// `None` for every other unfilled slot, which is the pre-existing behaviour those
/// classes have and not a decision this ticket makes about them.
fn caller_rigid_carrier(
    kb: &KnowledgeBase,
    dep: &RequiresEntry,
    ctx: &SigmaCtx,
    caller_op: Symbol,
) -> Option<CallerRigidCarrier> {
    let goal = goal_from_requires_entry(kb, dep)?;
    let params = caller_param_rigids(kb, caller_op, ctx.param_rigids);
    let mut found: Option<(Symbol, Symbol)> = None;
    let mut member: Option<Symbol> = None;
    let mut bindings: Vec<String> = Vec::new();
    for (k, v) in &goal.bindings {
        // EVERY BINDING MUST BE WRITEABLE BY THE CALLER, or there is no clause to print
        // and this function answers `None`. Two spellings qualify and nothing else does:
        // a parameter the CALLER declares (rendered as the caller's own name) and a
        // GROUND type (rendered as itself). `format_term_for_goal`'s fallback prints an
        // unrecognized term as `<term#N>`, and an element that is merely OPEN prints the
        // CALLEE's parameter (`anthill.prelude.List.T`) — the first does not parse and
        // the second is the wrong clause, and the message's whole contract is that what
        // it prints can be pasted.
        //
        // A REFUSAL WITHHELD, never a wrong value: such a call keeps exactly the
        // behaviour it has today, eval's own `not bound` raise included. The census
        // found no row of this shape, so the arm costs nothing it was catching.
        let rendered = match sigma_class_terminal(kb, ctx, v) {
            // A binding that terminates at a RIGID is an enclosing-scope parameter
            // ([`sigma_class_terminal`]'s second component) — but only one the caller
            // DECLARES can be named, a WI-424 body skolem having no written name.
            Some((cls, true)) => {
                let (_, name, owner) = params.iter().find(|(r, _, _)| *r == cls)?;
                // THE FIRST such binding is the carrier for the message's purposes. A
                // spec with two caller-parameter elements is repaired by declaring the
                // one clause either way — `clause` carries both — so naming one of them
                // is a choice of wording, not of verdict.
                if found.is_none() {
                    found = Some((*name, *owner));
                }
                if member.is_none() && kb.member_param_head(*name).is_some() {
                    member = Some(*name);
                }
                type_param_display_name(kb, *name)
            }
            // Concrete: no σ-class, and it renders as the sort it names.
            None if type_is_ground(kb, v) => format_value_for_goal(kb, v),
            // Open (the WI-415/418 gap), or a carrier this function cannot name.
            _ => return None,
        };
        bindings.push(format!("{} = {}", kb.local_name_of(*k), rendered));
    }
    // `found` is armed only by a binding, so reaching here means `bindings` is non-empty
    // and the bracket is unconditional — a `!bindings.is_empty()` guard here would be a
    // branch nothing can take.
    let (carrier, declare_on) = found?;
    let clause = format!(
        "{}[{}]",
        kb.qualified_name_of(goal.spec_sort),
        bindings.join(", ")
    );
    Some(CallerRigidCarrier {
        carrier: type_param_display_name(kb, carrier),
        clause,
        // A member is the calling operation's own, and a clause that names its bracket's
        // parameter goes on that operation whatever declares the carrier.
        declare_on: if member.is_some() { caller_op } else { declare_on },
    })
}

/// WI-20261006-XQGEW — the first element of `dep` that this use binds to a parameter the
/// member sugar minted, by the parameter's name.
///
/// Read off the variable the element terminates at: a member's rigid carries the
/// member's own name ([`fresh_rigid_named`]), which is no other parameter's.
fn dep_member_param(kb: &KnowledgeBase, dep: &RequiresEntry, ctx: &SigmaCtx) -> Option<Symbol> {
    let goal = goal_from_requires_entry(kb, dep)?;
    goal.bindings.iter().find_map(|(_, v)| {
        let (cls, at_rigid) = sigma_class_terminal(kb, ctx, v)?;
        (at_rigid && kb.member_param_head(cls.name()).is_some()).then(|| cls.name())
    })
}

/// WI-20260920-XSVCS — the caller's declared type parameters as `(the rigid its body
/// skolemized the parameter to, the name the author wrote, the declaration that owns
/// it)`.
///
/// THE NAME IS THE PARAMETER'S KEY, rendered by its reader (`type_param_display_name`):
/// one the member sugar minted was written `Tagger.C` (WI-20261006-XQGEW), and by the
/// bare `C` its key reads as, the clause the message printed was `requires Tag[T = C]`,
/// naming nothing in the caller's scope (MEASURED, `f(x: Tagger.C) = g(x)` over
/// `g[P](y: P) requires Tag[T = P]`).
///
/// BOTH FAMILIES, because `ctx.param_rigids` is the concatenation of exactly those two
/// (see [`TypingEnv::param_rigids`]) and the corpus has a live instance of each. Reading
/// only the operation's brackets would answer `None` for `test.wi416.Coll.contains`,
/// whose carrier is its SORT's `T`, and the diagnostic would silently fall back to
/// printing the callee's formal.
///
/// KEYED BY THE RIGID, not by symbol: [`sigma_class_terminal`] hands back a canonical
/// variable that has already been through [`canonical_global_var`], so the lookup must
/// put each declared parameter through the same map or a written `Var::Global` and the
/// call site's `Var::Rigid` never meet.
fn caller_param_rigids(
    kb: &KnowledgeBase,
    caller_op: Symbol,
    param_rigids: &[(VarId, TermId)],
) -> Vec<(VarId, Symbol, Symbol)> {
    let mut declared: Vec<(Symbol, VarId, Symbol)> = Vec::new();
    if let Some(info) = lookup_operation_info_full(kb, caller_op) {
        for (name, var) in &info.type_params {
            if let Var::Global(v) = var {
                declared.push((*name, *v, caller_op));
            }
        }
    }
    // THE NARROWED READER (WI-956), not `impl_parent_of_op`: this asks which SORT
    // declares the caller, and the un-narrowed one answers with the NAMESPACE for a free
    // operation — which declares no type parameters and could never carry the `requires`
    // this function's `declare_on` names.
    if let Some(parent) = impl_parent_sort_of_op(kb, caller_op) {
        for (name, term) in sort_type_params_as_pairs(kb, parent).iter() {
            if let Some((v, _)) = elem_var_step(kb, &TermIdView(*term)) {
                declared.push((*name, v, parent));
            }
        }
    }
    declared
        .into_iter()
        .map(|(name, v, owner)| (canonical_global_var(kb, v, param_rigids), name, owner))
        .collect()
}

/// WI-415: substitute the per-call type bindings into a `requires`-entry spec
/// term. A sort-parameter `Ref` (e.g. the `Ref(List.T)` inside
/// `Eq[T = Ref(List.T)]`) whose logical variable the call-site `subst` bound
/// to a CONCRETE type (`List.T := Int`) is replaced by that type — turning
/// the enclosing sort's abstract `Eq[T]` requirement into the concrete
/// `Eq[Int]` the call actually needs. Mirrors `substitute_in_spec`'s
/// structural walk, but resolves the param→value mapping through
/// `resolve_sort_alias` + the live `subst` (no precomputed qualified-name
/// map, so it makes no assumption about how the param symbol is spelled). A
/// param left abstract (`is_type_param_value`) or unbound is preserved. A bare `Global`
/// var leaf — the bare-spec sugar's minted carrier, which has no param symbol — is read
/// from `subst` directly, under the same preservation rule (WI-20260927-YCPAJ).
///
/// A spec that holds a value is walked on the carrier it rides ([`rewrite_type_leaves`]): a
/// co-carried type-param binding (`Foo[T = ParentT, E = Modify[c]]`) is root-scoped so the
/// concrete call type reaches the `SortGoal`, and what a parameter is replaced by is the
/// type σ binds it to, on its own carrier.
pub(super) fn substitute_spec_via_subst(
    kb: &mut KnowledgeBase,
    spec: &Value,
    subst: &Substitution,
) -> Value {
    rewrite_type_leaves(kb, spec, &|kb, leaf| {
        // WI-20260927-YCPAJ — the bare-spec sugar's carrier (`b: Spec.B`, WI-201) is a
        // BARE `Global` var with no declared symbol, so the name rung below never saw
        // it: the synthesized `requires Spec[B = ?P]` stayed unpinned at every call and
        // was skipped, where the explicit `[P] … requires Spec[B = P]` is checked.
        if let ViewHead::Var(Var::Global(vid)) = leaf.head(kb) {
            return resolve_var_value_via_subst(kb, vid, subst);
        }
        let s = ref_or_nullary_name_view(kb, leaf)?;
        resolve_param_value_via_subst(kb, s, subst)
    })
    .unwrap_or_else(|| spec.clone())
}

/// WI-415: the concrete type a sort-parameter symbol's logical variable is
/// bound to in `subst`, or `None` when `sym` is not a sort parameter, is
/// unbound, or is bound to another abstract type parameter (the call is not
/// concrete in that position — the enclosing sort's own `requires` carries
/// it). The σ read is the dispatch goal's own, [`spec_param_binding`] — so a type
/// holding a value (`User.S ↦ Buf[T = Int64, N = 3]`) is substituted as the type it is,
/// where it was once left abstract and the supply refused its element as "unconstrained"
/// while the typed twin ran (WI-20260929-WBHTM, MEASURED).
pub(super) fn resolve_param_value_via_subst(
    kb: &mut KnowledgeBase,
    sym: Symbol,
    subst: &Substitution,
) -> Option<Value> {
    // WI-822 LEG 1 / WI-943 — [`type_param_global_var`], not `resolve_sort_alias`.
    // An OPERATION's own bracket parameter (`probe[PT](x: PT) requires Desc[PT]`) has
    // no `SortAlias` fact by construction, so the alias ladder resolved it to nothing
    // and this substitution silently left `Desc[T = PT]` abstract — a dep that then
    // could not be constructed at the call site and left the op-scoped slot unfilled.
    // The map answers for BOTH declaration spellings, and it is the STRICTER of the
    // two in the other direction as well: a top-level opaque `sort Term = ?` has a
    // `SortAlias` but declares no parameter, and this reader (unlike the alias
    // ladder's other callers) never gated on `is_sort_param_symbol`.
    let vid = type_param_global_var(kb, sym)?;
    resolve_var_value_via_subst(kb, vid, subst)
}

/// [`resolve_param_value_via_subst`] from the parameter's variable itself — read through
/// the same [`spec_param_binding`], so the bare-spec sugar's minted carrier
/// (WI-20260927-YCPAJ) substitutes a type holding a value as a declared parameter
/// does (WI-20260929-WBHTM).
fn resolve_var_value_via_subst(
    kb: &mut KnowledgeBase,
    vid: VarId,
    subst: &Substitution,
) -> Option<Value> {
    let val = spec_param_binding(kb, subst, vid)?;
    if is_type_param_view(kb, &val) {
        None
    } else {
        Some(val)
    }
}

/// Wrap a single dispatching-dict expression in the single-entry
/// cons-list shape used for `apply_within.requirements` under Model 1.
pub(super) fn wrap_dispatch_channel(kb: &mut KnowledgeBase, dict_term: TermId) -> TermId {
    kb.build_list(&[dict_term])
}

/// WI-1091 — is `dep` the sort `owner`'s OWN spec at `owner`'s OWN parameters, i.e.
/// exactly what the frame's `__req_self` holds?
///
/// True when every type-param binding the dep states σ-agrees with the enclosing
/// sort's parameter of that name. A dep that states NO binding is also true: a
/// bracket-less `requires Ord` says nothing about which instantiation it wants, and
/// §5.2 makes that the callee's wildcard, which `__req_self` answers.
pub(super) fn dep_is_owner_self_instance(
    kb: &mut KnowledgeBase,
    ctx: &SigmaCtx,
    dep: &RequiresEntry,
    owner: Symbol,
) -> bool {
    let Some((_, bindings)) = unwrap_spec_view_value(kb, &dep.spec) else {
        return false;
    };
    let spec_qn = kb.qualified_name_of(dep.required_sort).to_string();
    let own_params = sort_type_params_as_pairs(kb, owner);
    for (key, value) in bindings {
        if !is_type_param_binding(kb, key, &spec_qn) {
            continue;
        }
        let short = kb.local_name_of(key).to_string();
        let short = short_name_of(&short).to_string();
        let Some((_, own_var)) = own_params
            .iter()
            .find(|(p, _)| short_name_of(kb.local_name_of(*p)) == short)
            .copied()
        else {
            return false;
        };
        if !sigma_pair_precise(kb, ctx, &value, &TermIdView(own_var)) {
            return false;
        }
    }
    true
}

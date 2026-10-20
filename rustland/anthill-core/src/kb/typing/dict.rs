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
    /// A requirement of the library's two specs in `spec`'s own contract that holds nowhere
    /// at these bindings, rendered: no row of `spec` here can answer, so no row is the
    /// repair ([`library_contract_unheld`]). `None` where none fails, or where the
    /// requirement leaves an element open.
    contract_unheld: Option<(String, LibraryInstances)>,
    /// The spec of the goal the search failed at: `spec` itself where no provision of it
    /// answered, or the spec of a condition a provision of it needed — the carrier's own
    /// `requires` included — which a row of `spec` would not repair.
    failed_at: Symbol,
}

/// The spec of the goal a failed resolution failed at ([`UnprovidedProvision::failed_at`]):
/// a `NoMatch` carries it, the requirement's own where nothing answered and a sub-goal's
/// where a provision's condition did not hold.
fn failed_spec(failure: &ResolutionResult, requirement: Symbol) -> Symbol {
    match failure {
        ResolutionResult::NoMatch { spec, .. } => *spec,
        _ => requirement,
    }
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
        // The library's two specs take no written row, and every element is pinned here, so
        // a `requires` in scope only hands the same refusal to the caller: their repair
        // replaces the search's account, whose advice is that `requires`, and every tail
        // below.
        if let Some(u) = &self.unprovided {
            // Where the search failed at the library's spec itself. A provision of it whose
            // carrier's own `requires` failed (`Keyed requires Desc[T = K]` at `Keyed[K =
            // Float]`) is repaired as that requirement is, which the search's account names.
            if let Some(library) = library_instances(kb, u.spec) {
                if library_instances(kb, u.failed_at).is_some() {
                    msg.push_str("; ");
                    msg.push_str(library.unprovided_repair());
                } else if !self.construction.is_empty() {
                    // That requirement's account is the repair, and no row of the library's
                    // spec is one.
                    msg.push_str(&format!("; {}", self.construction));
                }
                return msg;
            }
            // No row of the program's spec can answer here, for a requirement of its contract
            // no row can answer, so the same repair stands, said of that requirement.
            if let Some((requirement, library)) = &u.contract_unheld {
                msg.push_str(&format!(
                    "; no row of `{}` at these bindings can answer, its own contract asking \
                     `{requirement}`: {}",
                    kb.qualified_name_of(u.spec),
                    library.unprovided_repair()
                ));
                return msg;
            }
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

/// WI-20261013-50ZMN — the refusal of a dep [`forward_by_name`] refuses. Its account is
/// the whole of it: the generic tails advise a search, and this dep is not searched for.
pub(super) fn refused_by_name(
    kb: &KnowledgeBase,
    dep: &RequiresEntry,
    account: String,
) -> RequirementRefusal {
    RequirementRefusal {
        account_names_every_repair: true,
        no_scope_route: false,
        construction_carries_repair: false,
        dep_text: render_requires_entry(kb, dep),
        unconstrained: Vec::new(),
        refused_covers: Vec::new(),
        construction: account,
        pinned: None,
        unprovided: None,
        untied: None,
    }
}

/// Render a `RequiresEntry` for a diagnostic (`Desc[T = MT]`) via the same
/// goal rendering Strategy 3's own diagnostics use; entries that do not form
/// a goal fall back to the spec sort's name. The requirement as its clause wrote it: a
/// binding written through a type alias is led by the alias's name
/// ([`format_goal_as_written`]).
///
/// WI-20261013-50ZMN — UNDER ITS NAME where the declaration gives it one (`Times:
/// Mon[T = Int64]`), as the `requires` line writes it: of two requirements of one sort
/// at one type the goal is one text, and a refusal that printed it alone did not say
/// which of the two it was about.
pub(crate) fn render_requires_entry(kb: &KnowledgeBase, entry: &RequiresEntry) -> String {
    let goal = match goal_from_requires_entry(kb, entry) {
        Some(goal) => format_goal_as_written(kb, &goal),
        None => kb.qualified_name_of(entry.required_sort).to_string(),
    };
    under_its_name(kb, entry, goal)
}

/// `goal`, the rendered requirement of `entry`, under the name its declaration gives it
/// ([`render_requires_entry`]).
fn under_its_name(kb: &KnowledgeBase, entry: &RequiresEntry, goal: String) -> String {
    match entry.binder {
        Some(binder) => format!("{}: {goal}", kb.local_name_of(binder)),
        None => goal,
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
    /// The operation called, which the diagnostic names.
    pub(crate) callee_op: Symbol,
    /// Its parent sort: the owner of the `requires` chain this dictionary would fill.
    pub(crate) callee_sort: Symbol,
    pub(crate) refusal: Box<RequirementRefusal>,
}

/// WI-945 — the verdict on every call site [`build_concrete_dispatch_dict`] parked: a
/// requirement element nothing at the call pins is a LOAD error (§5.2).
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
        // WI-20261003-QGVB1 — a slot the requirement leaves open is no element of the call: it
        // is any type, said by the provisions that answer the rest.
        if !is_type_param_view(kb, v) || is_open_requires_slot(kb, goal.spec_sort, *k, v) {
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
                binder: sub.binder,
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
    let dep_text = under_its_name(
        kb,
        dep,
        match &goal {
            Some(g) => format_goal(kb, g),
            None => kb.qualified_name_of(dep.required_sort).to_string(),
        },
    );
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
        // WI-20261013-0K8WD: the selection for THIS requirement of the callee, by its
        // name where it has one — `callee_spec_sort` owns the chain, so `j` says which.
        let pin = selection_for_chain_entry(
            kb,
            selected,
            callee_spec_sort,
            callee_provision,
            j,
            dep.required_sort,
        );
        // WI-20261013-50ZMN — and what the caller's frame says about the dep BY NAME: a
        // requirement of the enclosing declaration the call named for it, or two that
        // cover it with the call naming neither ([`forward_by_name`]). Asked where a
        // call site is in hand, which is where a frame is.
        if disambig.is_some() {
            match forward_by_name(kb, dep, caller_requires, syms, disambig, pin) {
                NamedForward::Forward(t) => {
                    proj_terms.push(t);
                    continue;
                }
                NamedForward::Refused(account) => {
                    return Err(Box::new(refused_by_name(kb, dep, account)));
                }
                NamedForward::Unsaid => {}
            }
        }
        let pinned_witness = pin.and_then(InstanceSelection::witness);
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
            pin,
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
                // WI-20260921-3G1YT — A RULE-BODY GOAL AT A SPEC NO VALUE CAN NAME, the
                // SORT-half twin of the rule in [`build_op_scoped_dicts`], where the argument
                // is stated in full. It is N31XX's hardcode generalized: that arm asked
                // `dep.required_sort == anthill.reflect.TypeValue`, so a SORT-level `requires
                // Stamp[T = U]` at a nullary user typeclass, reached from a rule body, LOADED
                // CLEAN while the `TypeValue` spelling was refused (MEASURED).
                //
                // THE CONDITIONS, each doing work:
                //  * a RULE BODY (`rule_body_callee` is `Some`) — an operation-body site
                //    PARKS instead, and [`report_unsuppliable_requirements`] reports it; a
                //    rule body is typed after that pass has drained its queue, so a park
                //    from here would be dropped in silence. The operation-body shapes
                //    N31XX measured (`test.n31xx.twobad`, `test.rs2g4x`) are refused by the
                //    park;
                //  * the spec is no MARKER ([`spec_is_a_marker`]) and the provider facts do
                //    not determine a dictionary ([`dep_completes_to_a_unique_provider`]) —
                //    what load can see, since a rule body's evidence is owed at load
                //    (WI-20260922-0DK3H).
                //
                // Whether the callee's body reads the slot is no condition: a declared
                // `requires` is owed because it is declared.
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
                                contract_unheld: None,
                                failed_at: dep.required_sort,
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
                        //
                        // A library spec at a sort holding a structural former is the
                        // former's refusal, as at a call.
                        if let Some(former @ FormerCarrier::Within { .. }) =
                            former_carrier(kb, dep).filter(|former| {
                                former_is_the_cause(kb, dep, former, Some(nomatch))
                            })
                        {
                            *slot = Some(Box::new(former_refusal(kb, dep, &former)));
                        } else if let Some(unprovided) =
                            unprovided_provision(kb, dep, failed_spec(nomatch, dep.required_sort))
                        {
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
                    // PARKED like its siblings, not raised, and reported with them once
                    // every callee is classified ([`UnsuppliableRequirement`] says why the
                    // report waits).
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
                        // A binding that is or holds a structural former is that refusal's,
                        // as at a call, where the former is what no provision answered: a
                        // scope route would carry evidence nothing can give, so a requirement
                        // slot declared for it moves the refusal to the caller.
                        if let Some(former) = former_carrier(kb, dep).filter(|former| {
                            former_is_the_cause(kb, dep, former, s3_failure.as_ref())
                        }) {
                            *slot = Some(Box::new(former_refusal(kb, dep, &former)));
                            return Ok(None);
                        }
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
                        // WI-20261003-QGVB1 — a requirement whose open slots two provisions
                        // name apart: the account (the resolver's hint) names them and the
                        // repair, and no scope route is what is missing.
                        let apart = goal_from_requires_entry(kb, dep)
                            .and_then(|goal| OpenSlotsNamedApart::of(kb, &goal))
                            .is_some();
                        // A CYCLE's account names its repair, and no slot breaks a cycle: one
                        // declared moves the cycle to the caller.
                        let cyclic = matches!(s3_failure, Some(ResolutionResult::Cyclic { .. }));
                        // Nor does a slot answer a requirement that holds no parameter of
                        // the scope: no caller can say it either, so the slot moves the
                        // refusal to the caller, and the account's own repair stands.
                        let no_caller_says_it = !construction.is_empty()
                            && goal_from_requires_entry(kb, dep).is_some_and(|goal| {
                                !goal.bindings.iter().any(|(_, v)| holds_scope_parameter(kb, v))
                            });
                        let (construction, no_scope_route) = match member_clause {
                            _ if apart || cyclic => (construction, false),
                            Some(clause) => (
                                format!("{construction}{sep}nothing in the enclosing scope supplies it: declare `requires {clause}` on the enclosing operation so the evidence is passed in",
                                    sep = if construction.is_empty() { "" } else { " — " }),
                                false,
                            ),
                            None => (construction, !no_caller_says_it),
                        };
                        *slot = Some(Box::new(RequirementRefusal {
                            account_names_every_repair: apart || cyclic,
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
    let chain_sorts: Vec<Symbol> = abstract_chain.iter().map(|e| e.required_sort).collect();
    let pins_this_chain = chain_sorts.iter().enumerate().any(|(j, required)| {
        selection_for_chain_entry(
            kb,
            selected,
            callee_spec_sort,
            callee_provision,
            j,
            *required,
        )
        .is_some()
    });
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
    // WI-20261003-QGVB1 — and each slot a requirement leaves open said by the provision
    // at the carrier the call names ([`dep_completed_at_carrier`]), as on the op half.
    let concrete_chain: Vec<RequiresEntry> = abstract_chain
        .iter()
        .map(|entry| {
            let dep = RequiresEntry {
                required_sort: entry.required_sort,
                spec: substitute_spec_via_subst(kb, &entry.spec, subst),
                supply: entry.supply,
                binder: entry.binder,
            };
            // A sort's clause writes every slot but those it holds open.
            let leaves_one_open = view_named_children(kb, &dep.spec)
                .iter()
                .any(|(k, v)| is_open_requires_slot(kb, dep.required_sort, *k, v));
            if leaves_one_open {
                dep_completed_at_carrier(kb, &dep).unwrap_or(dep)
            } else {
                dep
            }
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
            match eliminate_type_projections(
                kb,
                &entry.spec,
                param_arg_types,
                Receivers::Call,
                None,
                &ctx,
                None,
            ) {
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
                    binder: entry.binder,
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
            binder: entry.binder,
        };
        let dep = dep_completed_at_carrier(kb, &dep).unwrap_or(dep);
        // WI-20260923-WN9P8 — the sort half's forward rule, on the op half: a slot of the
        // callee's OWN bound to one of the caller's parameters is that parameter's
        // dictionary or a refusal. MEASURED without it: a set typed `O = P` passed into
        // `add[E, OE](…) requires OE: WeakOrd[E]` got the caller's `OX` and inserted in
        // its order.
        //
        // WI-20261013-50ZMN — AND AN ENTRY THAT STATES AGAIN, UNDER NO NAME, A REQUIREMENT
        // ITS SORT NAMES is that requirement ([`named_slot_of_frame_entry`]): `fold3(…)
        // requires Mon[T = HT]` under `requires m: Mon[T = HT]`, called `[m = Plus]`.
        // It was answered by the goal, the first of the caller's entries that covers it
        // — `Plus` where the call said `[m = Times]`, once a caller could hold both.
        if let Some((owner, slot)) = named_slot_of_frame_entry(kb, callee_op, chain.sort_len() + j) {
            match project_forwarded_slot(
                kb,
                owner,
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
        // WI-20260921-EE0EP — A PARAM-DERIVED SLOT IS PINNED BY ITS ARGUMENT, and by
        // nothing the call selected.
        //
        // It is a PIN rather than a separate construction so that everything downstream is
        // the pipeline that already exists: Strategy 3 builds the dictionary, the tie and
        // the refusal diagnostics stay the ones an author already reads, and a slot whose
        // argument names no provider falls through to exactly today's verdict.
        //
        // NOTHING THE CALL SELECTED IS THIS DEP'S: the callee declares no slot for it
        // (058 §4.2), so no bracket key names it, and the call's selections are each for
        // a requirement the callee does declare. MEASURED while a selection was kept by
        // its required sort alone: a callee declaring `requires O: WeakOrd[String]` (whose
        // `a: MySet[T = String, O = O]` derives `WeakOrd -> Alphabetical`) beside an
        // unwritten `b: MySet[T = Int64]` answered `b`'s `WeakOrd[T = Int64]` dep with
        // `Alphabetical`.
        let pinned_by_arg: Option<InstanceSelection>;
        let pin: Option<&InstanceSelection> = match dep.supply {
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
                        pinned_by_arg = Some(InstanceSelection {
                            spec_sort: dep.required_sort,
                            slot: SelectedSlot::Named(binder),
                            provider: SelectedProvider::Witness(witness),
                            slots,
                        });
                        pinned_by_arg.as_ref()
                    }
                    // WI-20261013-50ZMN — THE ARGUMENT'S OWN TYPE BINDS THE SLOT TO A
                    // PARAMETER OF THE CALLER'S (`s: Via[T = E, M = A]` handed to a
                    // parameter that leaves `M` unwritten): a forward, answered by the
                    // frame's dictionary FOR that parameter as a callee's named slot
                    // bound to it is ([`project_param_forward`]). By the goal, as it was
                    // read, a caller holding `A` and `B` on one sort at one type handed
                    // on whichever was written first.
                    None => {
                        if let Some(t) = project_param_forward(
                            kb,
                            param_arg_types,
                            param,
                            binder,
                            &dep,
                            caller_requires,
                            &disambig,
                            &syms,
                        ) {
                            out.push(Some(t));
                            continue;
                        }
                        None
                    }
                }
            }
            // WI-20261013-0K8WD: a requirement the operation declares, by its name where
            // it has one, and by the name of the requirement it restates where it
            // restates one — `callee_op`'s frame says which ([`selection_for_frame_entry`]).
            SupplySource::Required | SupplySource::SelfSupplied => selection_for_frame_entry(
                kb,
                selected,
                callee_op,
                chain.sort_len() + j,
                dep.required_sort,
            ),
        };
        // WI-20261013-50ZMN — by name first, as the sort half asks ([`forward_by_name`]).
        match forward_by_name(kb, &dep, caller_requires, &syms, Some(&disambig), pin) {
            NamedForward::Forward(t) => {
                out.push(Some(t));
                continue;
            }
            NamedForward::Refused(account) => {
                kb.unsuppliable_requirements.truncate(parked_mark);
                return Err(Box::new(refused_by_name(kb, &dep, account)));
            }
            NamedForward::Unsaid => {}
        }
        let projected = build_dep_projection(
            kb,
            &dep,
            caller_requires,
            &caller_sub_chains,
            &syms,
            Some(&disambig),
            Some(&mut s3_failure),
            pin,
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
            // AN `ErrorTag` SLOT A RULE BODY CANNOT FILL IS REFUSED, whatever left it
            // empty — the exception to the marker exemption the rule-body arm below
            // grants. The slot is the payload sort an `Error.reify` boundary catches, read
            // at run time out of this evidence, and a boundary with none refuses to run
            // (`EvalError::ReifyPayloadUnread`), so a call that builds none here can never
            // answer. An operation body is handed the evidence by its caller (the forward
            // arms above) or refused naming the clause to add; a rule-body call's
            // `ErrorTag` is no condition of its clause, since no argument carries its type,
            // so what the call does not build here no caller supplies later: a payload type
            // that is a rule variable's or none at all, a tuple, a collection whose element
            // is open.
            // Keyed by the SLOT, not the callee, so an operation that reifies at its own
            // `P` (`requires ErrorTag[T = P]`) is held to it as `Error.reify` is.
            if park.is_some_and(|s| s.enclosing_op.is_none())
                && is_error_tag_spec(kb, dep.required_sort)
            {
                kb.unsuppliable_requirements.truncate(parked_mark);
                return Err(Box::new(unfilled_error_tag_refusal(kb, &dep)));
            }
            // WI-20260919-N31XX (proposal 065) — AN UNFILLED `TypeValue` SLOT IS NEVER
            // BENIGN, which is what takes it out of the silent-absence rule below.
            //
            // That rule exists for a measured reason its own comment gives: 29 stdlib
            // bodies declare a chain and NEVER READ IT, so a slot no dictionary could
            // fill costs them nothing. `TypeValue` cannot be one of them.
            // `type_value[X]()` takes no argument, so the DISPATCHING DICTIONARY of the
            // instance its bracket names is the only carrier of the answer — a body holding
            // this evidence necessarily reads it
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
            if let Some(
                tie @ (ResolutionResult::Ambiguous { .. } | ResolutionResult::Cyclic { .. }),
            ) = &s3_failure
            {
                // A tie and a cycle are raised HERE: neither has an answer a later call could
                // supply, and the construction path refuses both, so the two spellings of one
                // program agree. A cycle left silent loaded clean and died at run time
                // (MEASURED: `A provides Desc[T = A] :- Desc[T = B]` and its mirror, `Reader.
                // probe(a)`). A σ-refused cover stays a silent absence. A `NoMatch` is PARKED
                // just below — it is not silent any more, but neither is it decided here.
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
                    // A cycle's account names its repair, and a pin breaks no cycle.
                    construction_carries_repair: failure_carries_repair(Some(tie))
                        || matches!(tie, ResolutionResult::Cyclic { .. }),
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
                // proves the element is pinned lives only here, and the refusal is
                // reported with the rest once every callee is classified. See
                // [`UnsuppliableRequirement`].
                // A library spec at a type holding a structural former is the former arm's
                // below, not this one's: that arm names the former, which is why no row
                // answers there.
                let former = former_carrier(kb, &dep);
                // The former's refusal, where the former is what no provision answered and the
                // scope could not supply it ([`former_is_the_cause`]): before every account
                // below, as at a construction, so the two spellings of one requirement agree.
                let former_cause = former
                    .as_ref()
                    .filter(|former| former_is_the_cause(kb, &dep, former, s3_failure.as_ref()))
                    .is_some();
                let unprovided = match (&s3_failure, &former) {
                    _ if former_cause => None,
                    (
                        Some(nomatch @ ResolutionResult::NoMatch { .. }),
                        None | Some(FormerCarrier::At(_)),
                    ) => {
                        unprovided_provision(kb, &dep, failed_spec(nomatch, dep.required_sort))
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
                            _ if former_cause => None,
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
                            (!former_cause).then_some(())?;
                            site.enclosing_op.and_then(|enclosing_op| {
                                caller_rigid_carrier(
                                    kb,
                                    &dep,
                                    former.is_some(),
                                    &disambig,
                                    enclosing_op,
                                    caller_requires,
                                )
                                .map(|c| {
                                    let (requirement, construction) = match c {
                                        // A part no evidence of the caller's would answer at:
                                        // said by the goal its instance failed at, where that is
                                        // another spec's (`Keyed[K = Float]` needs `Desc[T =
                                        // Float]`), which no row of the library's spec repairs.
                                        CallerRigidCarrier::NoInstance {
                                            carrier,
                                            requirement,
                                            part: NoInstance { part, failure },
                                            library,
                                        } => {
                                            let why = match failure.as_ref().filter(|f| {
                                                library_instances(kb, failed_spec(f, dep.required_sort))
                                                    .is_none()
                                            }) {
                                                Some(f) => describe_resolution_failure(kb, f),
                                                None => library.unprovided_repair().to_string(),
                                            };
                                            let construction = if part == carrier {
                                                format!("its carrier is `{carrier}`, and {why}")
                                            } else {
                                                format!("its carrier `{carrier}` holds `{part}`, and {why}")
                                            };
                                            (requirement, construction)
                                        }
                                        CallerRigidCarrier::LacksEvidence {
                                            carrier,
                                            within,
                                            requirement,
                                            clauses,
                                            declare_on,
                                        } => {
                                            let construction = format!(
                                                "{}, a type parameter of the CALLING \
                                     operation `{}`, which declares no `requires` that \
                                     covers it — the caller's frame is the only thing that \
                                     could ever fill this slot, and it holds nothing for \
                                     `{carrier}`. {}, or call `{}` with a type whose provision \
                                     is known here",
                                                match &within {
                                                    Some(within) => {
                                                        format!("its carrier `{within}` holds `{carrier}`")
                                                    }
                                                    None => format!("its carrier is `{carrier}`"),
                                                },
                                                kb.qualified_name_of(enclosing_op),
                                                declare_on.repair(kb, &clauses),
                                                kb.qualified_name_of(callee_op),
                                            );
                                            (requirement, construction)
                                        }
                                    };
                                    RequirementRefusal {
                                        account_names_every_repair: false,
                                        // RENDERED IN THE CALLER'S SPELLING, not `dep`'s. The entry
                                        // still names the CALLEE's formal (`tyOf.B`), and an author
                                        // told to declare `requires TT[T = tyOf.B]` would be copying
                                        // a parameter of a declaration that is not theirs. Same rule,
                                        // and the same reason, as the projection arm above.
                                        no_scope_route: false,
                                        // The account names the repair; "pin the element at the
                                        // call site" is advice for an element left open, and this
                                        // one is a parameter the caller already pinned.
                                        construction_carries_repair: true,
                                        dep_text: requirement,
                                        unconstrained: Vec::new(),
                                        refused_covers: Vec::new(),
                                        construction,
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
                        match (rigid, &s3_failure) {
                            (Some(r), _) => Some(r),
                            // A provision answered at the former and a condition of its own did
                            // not hold: the condition's account, as at a construction, which
                            // names what to provide (`P provides Apply[F = (A) -> Int64] :-
                            // Lbl[T = A]` at `String` asks for `Lbl[T = String]`).
                            (None, Some(nomatch @ ResolutionResult::NoMatch { .. }))
                                if former.is_some() && !former_cause =>
                            {
                                Some(RequirementRefusal {
                                    account_names_every_repair: false,
                                    no_scope_route: false,
                                    construction_carries_repair: true,
                                    dep_text: render_requires_entry(kb, &dep),
                                    unconstrained: Vec::new(),
                                    refused_covers: Vec::new(),
                                    construction: describe_resolution_failure(kb, nomatch),
                                    pinned: None,
                                    unprovided: None,
                                    untied: None,
                                })
                            }
                            (None, _) => former.map(|former| former_refusal(kb, &dep, &former)),
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
                contract_unheld: None,
                failed_at: spec,
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
///
/// WI-20261003-QGVB1 — and only where the provisions answering the written parameters say
/// the rest alike ([`open_slots_said`]), whose types are then the ones written: beside a second
/// provision naming other types for them, the carrier's own reading is one answer of two, and
/// the slot is left unwritten for the requirement to be refused as saying neither.
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
    // WI-20261003-QGVB1 — a slot a SORT's clause leaves out is held as the spec's own
    // parameter, and one written `?` as a variable ([`is_open_requires_slot`]): unwritten
    // both, as the operation's clause that names no binding for it.
    completed.retain(|(k, v)| !is_open_requires_slot(kb, spec, *k, v));
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
    let asked = SortGoal {
        spec_sort: spec,
        bindings: completed.iter().cloned().collect(),
        carrier: None,
    };
    let open: Vec<Symbol> = unwritten.iter().map(|(p, _)| *p).collect();
    let said = match open_slots_said(kb, &asked, &open) {
        OpenSlotsSaid::Apart(_) => return None,
        OpenSlotsSaid::One(said) => said,
        OpenSlotsSaid::Nothing => vec![None; open.len()],
    };
    let instance = spec_instance_at_receiver(kb, spec, carrier_pvid, &carrier)?;
    for ((param, vid), said) in unwritten.into_iter().zip(said) {
        let said = match said {
            Some(said) => said,
            None => {
                let value = instance.resolve_as_value(vid)?;
                resolve_type_deep_value(kb, &instance, &value)
            }
        };
        completed.push((param, said));
    }
    kb.canonicalize_record_named_args(functor, &mut completed);
    let pos = view_pos_children(kb, &dep.spec, pos_arity).into_vec();
    Some(RequiresEntry {
        required_sort: spec,
        spec: kb.fn_value(functor, pos, completed),
        supply: dep.supply,
        binder: dep.binder,
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

/// Is `spec` `anthill.prelude.ErrorTag`, the evidence an `Error.reify` boundary reads? Asked
/// only where a slot could not be built, so the name is resolved there.
pub(super) fn is_error_tag_spec(kb: &KnowledgeBase, spec: Symbol) -> bool {
    kb.try_resolve_symbol("anthill.prelude.ErrorTag")
        .is_some_and(|tag| kb.canonical_sort_sym(tag) == kb.canonical_sort_sym(spec))
}

/// The refusal of a rule-body call whose `ErrorTag` slot it could not build — see the gate
/// in [`build_op_scoped_dicts`]. Each repair it names is driven by
/// `wi_9wvt7_reify_rule_body_test::the_advised_repairs_answer`.
fn unfilled_error_tag_refusal(kb: &KnowledgeBase, dep: &RequiresEntry) -> RequirementRefusal {
    RequirementRefusal {
        account_names_every_repair: false,
        no_scope_route: false,
        construction_carries_repair: true,
        dep_text: render_requires_entry(kb, dep),
        unconstrained: Vec::new(),
        refused_covers: Vec::new(),
        construction: "its carrier is the payload sort an `Error.reify` boundary catches, \
                       and this call builds no evidence of it. A rule-body call's \
                       `ErrorTag` is no condition its clause can be handed, and without it \
                       the boundary has no payload sort to catch and refuses to run. Raise, \
                       in the thunk, a value of a sort the call names — a type written on a \
                       rule variable does not reach here, and a tuple, or a collection whose \
                       element is open, has no instance; write an operation named bare as \
                       `lambda () -> f()`, \
                       since a rule body reads the bare name as its zero-argument call; and \
                       a thunk that raises no `Error` label needs no boundary"
            .to_owned(),
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
        pin: None,
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
/// Both legs are cheap and the first says what a bracket can HOLD: a sort with no type
/// parameter gives a bracket no carrier to name, whichever sorts provide it, and nothing
/// provides a sort with constructors ([`clause_is_dispatchable`], WI-20260921-28TAT).
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
///     a `Cyclic` is a third verdict) and the callee is not a resolver builtin.
///
/// The ticket's class (3) — a carrier for which the provision is IMPOSSIBLE, not merely
/// absent — is refused by exactly the same sentence as its class (2); see
/// [`UnprovidedProvision`] for why the distinction cannot be drawn from here.
fn unprovided_provision(
    kb: &mut KnowledgeBase,
    dep: &RequiresEntry,
    failed_at: Symbol,
) -> Option<UnprovidedProvision> {
    let goal = goal_from_requires_entry(kb, dep)?;
    let carrier = pinned_goal_carrier(kb, &goal)?;
    let contract_unheld = library_contract_unheld(kb, &goal);
    Some(UnprovidedProvision {
        carrier,
        spec: dep.required_sort,
        has_a_row: carrier_has_provision_row(kb, carrier, dep.required_sort),
        provision_in_full: Some(format_goal(kb, &goal)),
        contract_unheld,
        failed_at,
    })
}

/// The first requirement of the library's two specs in `goal`'s spec's own contract that no
/// row answers at `goal`'s bindings, rendered — `Desc requires TypeValue[T = T]` at `Desc[T =
/// Option[T = (Int64, Int64)]]` asks `TypeValue[T = Option[T = (Int64, Int64)]]`, which holds
/// nowhere. The contract is read through the program's own specs it names (`Desc2 requires
/// Desc[T = T]`), as a provision's is checked. No row of the spec at those bindings can
/// answer, so the row the refusal would advise is no repair. Only the library's specs, which
/// no row of the program's can supply; a contract of a program's own spec the program can
/// still provide.
///
/// The spec's transitive chain ([`requires_chain`]), composed to its own parameters and read
/// at the goal's bindings: a spec already on a path is kept as an entry and not expanded
/// again, the rule [`scope_chain_cover`] reads a requirement by, so a contract that asks for
/// a spec again at a larger type (`Desc2 requires Desc2[T = List[T = T]]`) is read once.
fn library_contract_unheld(
    kb: &mut KnowledgeBase,
    goal: &SortGoal,
) -> Option<(String, LibraryInstances)> {
    library_instances(kb, goal.spec_sort).is_none().then_some(())?;
    // Keyed by the spec's short parameter name, `provider_requires_subgoals`' convention.
    let sigma: Vec<(String, Value)> = goal
        .bindings
        .iter()
        .map(|(k, v)| (kb.local_name_of(*k).to_string(), v.clone()))
        .collect();
    let chain = requires_chain(kb, goal.spec_sort);
    for sub in requires_chain_goals(kb, &chain, &|kb, v| subst_requires_value(kb, v, &sigma)) {
        let Some(library) = library_instances(kb, sub.spec_sort) else {
            continue;
        };
        if !spec_resolves_at_bindings(kb, sub.spec_sort, sub.bindings.clone()) {
            return Some((format_goal(kb, &sub), library));
        }
    }
    None
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
    // The carrier's own sort symbol: `Eq[T = Hold]` names `Hold`, and
    // `Eq[T = Box[B = Leaf]]` names `Box` — the sort that would carry the provision, so
    // the parametric case suggests the line on the container, which is where a
    // conditional provision goes (058 §3.8).
    sort_functor_of_view(kb, goal_carrier_binding(kb, goal)?)
}

/// What a goal binds its spec's carrier parameter to — a sort ([`goal_carrier_sort`]), or
/// a type that names none ([`unprovided_spec_at_former`]).
fn goal_carrier_binding<'g>(kb: &KnowledgeBase, goal: &'g SortGoal) -> Option<&'g Value> {
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
    goal.bindings
        .iter()
        .find(|(k, _)| kb.local_name_of(*k) == kb.local_name_of(param))
        .map(|(_, v)| v)
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
    kb: &mut KnowledgeBase,
    goal: &SortGoal,
    carrier: Symbol,
    callee_op: Symbol,
    span: Option<Span>,
) -> Option<TypeError> {
    if host_implements(kb, callee_op) || carrier_is_an_instance(kb, carrier, goal.spec_sort) {
        return None;
    }
    let in_full = goal_pins_every_param(kb, goal);
    let contract_unheld = if in_full { library_contract_unheld(kb, goal) } else { None };
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
                provision_in_full: in_full.then(|| format_goal(kb, goal)),
                contract_unheld,
                failed_at: goal.spec_sort,
            }),
            untied: None,
        }),
    })
}

/// WI-883's refusal where the carrier the call names is a TUPLE or an ARROW, and no provision
/// of the spec matched the call (WI-20260929-12NKG).
///
/// [`unprovided_spec_at_carrier`] is asked of a carrier SORT, and a tuple or an arrow names
/// none, so such a call fell through to the pass-through a host-implemented callee takes —
/// and nothing implements it: a value of such a type has no sort whose member could answer
/// when the call runs, so a provision matched where the call is typed is the only supplier
/// there is. MEASURED: `Apply.run(lambda (x: String) -> 1)` beside a provider at `(Int64) ->
/// Int64` alone loaded and died `OperationBodyMissing`, and so did `Apply.run(lambda x ->
/// 1)` beside it — a provision is matched at the type as the call states it, and a lambda's
/// parameter written without its type states none.
///
/// It was reached more often once a requirement at ANOTHER arrow stopped covering such a
/// call: that call used to run the requirement's provider, on a value of a type it does not
/// provide for.
///
/// A FORMER BY ITS HEAD, whatever stands inside it, as [`former_carrier`] reads a declared
/// requirement's — and with the sort's exemption for a callee the host implements, which
/// serves every carrier. MEASURED with it backed out: 22 rows refuse, the stdlib's
/// `Error.reify` over a tuple payload among them (`wi_9wvt7_error_reify_test`).
///
/// NOT the sort's other exemption, for a self-representing spec
/// ([`unclassified_goal_carrier`]). The parameter read here is the one the spec's
/// operations RECEIVE on ([`spec_carrier_param_or_sole`]), which is no parameter at all
/// where they all receive on `Self`, so the question is not reached for such a spec. It is
/// reached for one that receives on `Self` in one operation and on a parameter in another,
/// and there the exemption only kept `Mixed.at((1, 2))` loading with nothing to run.
/// MEASURED: with it in place no row of the workspace moved, and no program found that it
/// protects.
pub(super) fn unprovided_spec_at_former(
    kb: &KnowledgeBase,
    goal: &SortGoal,
    callee_op: Symbol,
    span: Option<Span>,
) -> Option<TypeError> {
    if host_implements(kb, callee_op) {
        return None;
    }
    let former = goal_carrier_binding(kb, goal).filter(|v| is_structural_former(kb, *v))?;
    let spec = kb.qualified_name_of(goal.spec_sort);
    let former_text = format_value_for_goal(kb, former);
    let library = library_instances(kb, goal.spec_sort);
    // THREE REPAIRS, by what the call states. A type stated in full is one a sort could
    // provide the spec at. One that names a type parameter of the declaration the call is
    // written in is each caller's to supply for, which is what a `requires` there says.
    // One with a part nothing has said is no type a row could name, and the part is the
    // author's to write — a provision is matched at the type as the call states it, so
    // one that would answer once the part is written is not looked for.
    //
    // None of them for a spec whose instances only the library supplies: a row is
    // refused or never read there, and no caller can supply one at a former.
    let repair = if let Some(library) = library {
        library.former_repair_at_call().to_owned()
    } else if type_is_ground(kb, former) {
        format!(
            "Give some sort the row that names this type — `provides {spec}[… = \
             {former_text}]` — or pass a value whose type is a sort"
        )
    } else if type_is_determined(kb, former) {
        format!(
            "It names a type parameter of the declaration the call is written in, so the \
             provision is each caller's to supply: declare `requires {spec}[…]` at this type \
             on that declaration"
        )
    } else {
        // THE BRACKET AS WELL AS THE PARAMETER. A lambda of several binders takes their
        // types from the type around it and states none of its own, written or not:
        // MEASURED, `Apply.run(lambda (x: Int64, y: Int64) -> x)` is at `(?) -> Int64`
        // beside a provider at `(Int64, Int64) -> Int64`, and runs once the call says
        // `[F = (Int64, Int64) -> Int64]` or the lambda is bound to a name of that type.
        let param = spec_carrier_param_or_sole(kb, goal.spec_sort)
            .map(|p| short_name_of(kb.local_name_of(p)).to_string())
            .unwrap_or_default();
        format!(
            "It leaves a part unsaid, and a provision is matched at the type as the call \
             states it: write the type of the lambda's parameter, or the whole type in the \
             call's brackets (`[{param} = …]`), which is where a lambda of several \
             parameters states its own"
        )
    };
    Some(TypeError::UnsatisfiableRequirement {
        span,
        op: callee_op,
        callee_sort: callee_op,
        usage: RequirementUse::Call,
        refusal: Box::new(RequirementRefusal {
            account_names_every_repair: false,
            no_scope_route: false,
            // The account ends in its own repair: there is no `provides` to suggest on a
            // carrier that is no sort.
            construction_carries_repair: true,
            dep_text: format_goal_as_written(kb, goal),
            unconstrained: Vec::new(),
            refused_covers: Vec::new(),
            construction: format!(
                "its carrier is `{former_text}`, a tuple or an arrow, and no provision of \
                 `{spec}` answers at it. A tuple or an arrow carries no provision itself (a \
                 `provides` row is written on a sort) {why}. {repair}",
                why = if library.is_some() {
                    "and the derived instances cover sorts only, so the call would load and \
                     then have no instance to answer from"
                } else {
                    "and its value has no sort whose member could answer when the call runs, \
                     so the call would load and then find no operation"
                },
            ),
            pinned: None,
            unprovided: None,
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
///
/// A BUILTIN WHOSE ANSWER IS ITS INSTANCE'S DICTIONARY IS NO SUCH IMPLEMENTATION, whatever
/// its declaration claims ([`crate::kb::resolve::BuiltinTag::answers_from_its_dictionary`]):
/// `TypeValue.type_value[X]()`, `@[host_implemented]`, answers only where `X` has an
/// instance. Counted as one, `type_value[T = (Int64, String)]()` loaded with nothing to
/// hand it, and inside a member of a sort it answered that sort, through the dictionary its
/// own frame was entered with (MEASURED).
pub(super) fn host_implements(kb: &KnowledgeBase, op: Symbol) -> bool {
    if kb.builtin_of(op).is_some_and(|tag| tag.answers_from_its_dictionary()) {
        return false;
    }
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
    if carrier_is_an_instance(kb, from_goal, goal.spec_sort) {
        return None;
    }
    goal_pinned_carrier(kb, goal)
}

/// The carrier a spec-op call's goal pins, an instance or not: the sort at the spec's carrier
/// parameter, for a spec that is not self-representing, where it passes
/// [`statically_pinned_carrier`]'s filter — an abstract-spec value, or the spec itself, is
/// some provider at run time and pins none ([`unclassified_goal_carrier`] says why both).
pub(super) fn goal_pinned_carrier(kb: &KnowledgeBase, goal: &SortGoal) -> Option<Symbol> {
    let from_goal = goal_carrier_sort(kb, goal)?;
    if spec_is_self_representing(kb, kb.canonical_sort_sym(goal.spec_sort)) {
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
/// THE SORT HALF READS IT TOO: a sort-level `requires` at a former, at a call or at a
/// construction, gets the same refusal from `build_dispatching_dict_from_chain`, where no
/// provision answered at the former and the former names no parameter of the constructing
/// scope ([`former_is_the_cause`]); the two spellings of one requirement agree
/// (`wi_0gyw1_arrow_provision_labels_test::two_lists_of_unrelated_names_stay_two_arrows`).
///
/// 065 open question 3 proposed refusing "at the read, naming the row". This refuses at
/// the CALL, or at the construction, which is where the carrier is known — a body reading
/// `B` cannot see that some caller will pass a tuple. The former is named in the message
/// either way.
///
/// A BODY-LESS CALLEE IS HELD TO IT TOO (user, 2026-10-16). One was exempt, on the reading
/// that its host interprets an absent slot: `Error.reify` (`requires ErrorTag[T = T1]`,
/// body-less on purpose) caught WIDE where it had no evidence, and the row was taken to
/// guarantee what it may catch. MEASURED false for a thunk whose row holds a second
/// `Error` label: `Error.reify(lambda () -> raiseTup(n))` over `{Error[(Int64, Int64)],
/// Error[Other]}` caught `other(n: 7)` as the tuple's `err`, past the boundary at `Other`
/// around it. The boundary refuses evidence that names no payload sort now
/// (`Interpreter::enter_reify_boundary`), so there is no wide case left for an exemption
/// to protect (WI-20260908-9WVT7).
fn former_carrier(kb: &KnowledgeBase, dep: &RequiresEntry) -> Option<FormerCarrier> {
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
        is_structural_former(kb, v).then_some(v)
    });
    if let Some(former) = former {
        return Some(FormerCarrier::At(format_value_for_goal(kb, former)));
    }
    let library = library_instances(kb, dep.required_sort)?;
    // Through sort applications only, the positions a sort's instance is conditioned on.
    let holds_former = |v: &Value| {
        type_any_part(kb, v, &|te| match te {
            TypeExtractor::Arrow { .. } | TypeExtractor::NamedTuple(_) => Some(true),
            TypeExtractor::Parameterized { .. } => None,
            _ => Some(false),
        })
    };
    goal.bindings.iter().find_map(|(_, v)| {
        holds_former(v).then(|| FormerCarrier::Within {
            within: format_value_for_goal(kb, v),
            library,
        })
    })
}

/// Is the structural former `former`, which a binding of `dep` is or holds, what the
/// requirement cannot be supplied for?
///
/// * For the library's two specs, the only ones that read a former within a binding
///   ([`FormerCarrier::Within`]): where the search failed at one of them, since no instance
///   of either is derived at a former, whatever the scope holds.
/// * For a program's spec, whose binding IS the former ([`FormerCarrier::At`]): where no
///   provision answered AT
///   the former — a failure forwarded from a provision's own condition says one did, and the
///   condition's account repairs it (`P provides Apply[F = (A) -> Int64] :- Lbl[T = A]`, the
///   condition at `Apply` itself too) — and the scope cannot supply it: the former holds no
///   parameter of the constructing scope, or no provision answers a former of its shape
///   whatever that parameter is. `holder((x, 1))` over `x: C` is told the requirement slot
///   only where some row answers at a pair; told it with none, the slot moved the refusal to
///   the caller. The parameter of a lambda written without its type is an inference variable,
///   no parameter of the scope.
fn former_is_the_cause(
    kb: &mut KnowledgeBase,
    dep: &RequiresEntry,
    former: &FormerCarrier,
    failure: Option<&ResolutionResult>,
) -> bool {
    if matches!(former, FormerCarrier::Within { .. })
        || library_instances(kb, dep.required_sort).is_some()
    {
        return failure
            .is_none_or(|f| library_instances(kb, failed_spec(f, dep.required_sort)).is_some());
    }
    if failure.is_some_and(|f| f.is_forwarded()) {
        return false;
    }
    let Some(goal) = goal_from_requires_entry(kb, dep) else {
        return true;
    };
    let Some((key, value)) = goal
        .bindings
        .iter()
        .find(|(_, v)| is_structural_former(kb, v))
        .cloned()
    else {
        return true;
    };
    if !holds_scope_parameter(kb, &value) {
        return true;
    }
    let Some(opened) = open_scope_parameters(kb, &value) else {
        return true;
    };
    !some_row_meets_opened(kb, dep.required_sort, key, &opened)
}

/// Is there a provision of `spec` whose binding at `key` meets `opened` — a former with the
/// scope's parameters made fresh ([`open_scope_parameters`]) — at some instantiation of both:
/// one a later caller's evidence could select. By unification, the row's own parameters made
/// fresh as well, since either side may hold the parameter (`provides Desc[T = (A, Int64)]`).
fn some_row_meets_opened(kb: &mut KnowledgeBase, spec: Symbol, key: Symbol, opened: &Value) -> bool {
    let key_name = kb.local_name_of(key).to_string();
    let rows: Vec<ProvidesRow> = provides_rows_of_spec(kb, spec)
        .filter(|row| !is_conversion_row(kb, row))
        .collect();
    for row in rows {
        let Some(at) = row
            .bindings(kb)
            .into_iter()
            .find(|(k, _)| kb.local_name_of(*k) == key_name)
            .map(|(_, v)| v)
        else {
            continue;
        };
        let fresh: Vec<(Symbol, Value)> = impl_param_symbols(kb, row.provider)
            .into_iter()
            .map(|p| {
                let name = kb.intern("_");
                let var = kb.fresh_var(name);
                (p, Value::term(kb.alloc(Term::Var(Var::Global(var)))))
            })
            .collect();
        let at = sigma_subst_type(kb, &at, &fresh);
        if unify_types(kb, &mut Substitution::new(), opened, &at) {
            return true;
        }
    }
    false
}

/// Does the type `v` hold a parameter of the scope it is written in — the body's rigid for
/// one, a reference to one, or its canonical variable — and not merely an inference variable?
fn holds_scope_parameter<V: TermView>(kb: &KnowledgeBase, v: &V) -> bool {
    match v.head(kb) {
        ViewHead::Var(Var::Rigid(_)) => true,
        ViewHead::Var(Var::Global(var)) => kb.type_param_of_canonical_var(var).is_some(),
        ViewHead::Ident(s) => is_sort_param_symbol(kb, s),
        ViewHead::Functor {
            functor, pos_arity, ..
        } => {
            functor.is_some_and(|f| is_sort_param_symbol(kb, f))
                || view_any_child(kb, v, pos_arity, |c| holds_scope_parameter(kb, c))
        }
        _ => false,
    }
}

/// `v` with each parameter of the scope it holds ([`holds_scope_parameter`]) replaced by a fresh
/// variable: the type at any instantiation of the scope.
fn open_scope_parameters(kb: &mut KnowledgeBase, v: &Value) -> Option<Value> {
    try_rewrite_type_terms(kb, v, &|kb, part| {
        Some(rewrite_term_leaves(kb, part, &|kb, leaf| {
            let open = match kb.get_term(leaf) {
                Term::Var(Var::Rigid(_)) => true,
                Term::Var(Var::Global(var)) => kb.type_param_of_canonical_var(*var).is_some(),
                Term::Ref(s) => is_sort_param_symbol(kb, *s),
                _ => false,
            };
            open.then(|| {
                let name = kb.intern("_");
                let fresh = kb.fresh_var(name);
                kb.alloc(Term::Var(Var::Global(fresh)))
            })
        }))
    })
}

/// The refusal of a requirement whose binding is or holds a structural former
/// ([`former_carrier`]), at a call or at a construction.
fn former_refusal(
    kb: &KnowledgeBase,
    dep: &RequiresEntry,
    former: &FormerCarrier,
) -> RequirementRefusal {
    let spec = kb.qualified_name_of(dep.required_sort);
    let repair = former_repair(kb, dep.required_sort, former);
    RequirementRefusal {
        account_names_every_repair: false,
        no_scope_route: false,
        // THE ACCOUNT CARRIES ITS OWN REPAIR — there is no `provides` to suggest, so the
        // generic "declare it on the carrier" tail would name a declaration that cannot
        // exist. Same flag, same reason, as the tie arm of the call path.
        construction_carries_repair: true,
        dep_text: render_requires_entry(kb, dep),
        unconstrained: Vec::new(),
        refused_covers: Vec::new(),
        construction: match former {
            FormerCarrier::At(at) => format!(
                "its carrier is `{at}`, a STRUCTURAL FORMER — a tuple or an arrow — and \
                 nothing provides `{spec}` at it. A former cannot CARRY a provision itself (a \
                 `provides` row is written on a sort), and the derived instances cover sorts \
                 only, so this slot stays empty, and the program would load and then die reading \
                 a requirement the frame never bound. {repair}",
            ),
            FormerCarrier::Within { within, .. } => format!(
                "its carrier `{within}` has a STRUCTURAL FORMER — a tuple or an arrow — among \
                 its type arguments, and nothing provides `{spec}` at it: a sort's instance \
                 holds only where each of its type arguments has one, and a former has none. \
                 {repair}",
            ),
        },
        pinned: None,
        unprovided: None,
        untied: None,
    }
}

/// Where [`former_carrier`] found the structural former, rendered.
enum FormerCarrier {
    /// A binding IS the former: `(a: Int64, b: String)`.
    At(String),
    /// A binding holds one among its type arguments: `Option[T = (a: Int64, b: String)]`.
    /// Only for the two specs whose instances the library supplies ([`library_instances`]):
    /// a sort's instance of either holds only where each type argument has one, so none
    /// reaches the type, and no row can stand in. For any other spec a row naming the
    /// whole type may answer, where the spec's own requirements hold at it, and
    /// [`unprovided_provision`] advises it.
    Within {
        within: String,
        library: LibraryInstances,
    },
}

/// The two specs whose instances only the library supplies: `TypeValue`, derived for
/// every sort and refused when written, and `ErrorTag`, whose one reader, an `Error.reify`
/// boundary, takes the payload's sort from the `TypeValue` evidence of `Error`'s own
/// provision and refuses to run without it.
#[derive(Clone, Copy, Debug)]
enum LibraryInstances {
    TypeValue,
    ErrorTag,
}

impl LibraryInstances {
    /// The account and repair where a requirement of this spec at a sort finds no row that
    /// answers: a value whose type has the evidence, since no row can stand in.
    fn unprovided_repair(self) -> &'static str {
        match self {
            LibraryInstances::TypeValue => {
                "no row of `anthill.reflect.TypeValue` answers here, and none may be written: \
                 every instance is derived, one for a sort that is no spec, for a parametric \
                 sort only where each of its type arguments has one. Pass a value whose type \
                 is such a sort, every type argument of it written"
            }
            LibraryInstances::ErrorTag => {
                "no row of `anthill.prelude.ErrorTag` answers here, and a written one is no \
                 repair: an `Error.reify` boundary reads `Error`'s own provision alone, which \
                 answers wherever the payload's type has a `TypeValue`, one derived for a \
                 sort that is no spec, for a parametric sort only where each of its type \
                 arguments has one. Raise, in the thunk, a value whose type is such a sort, \
                 every type argument of it written"
            }
        }
    }

    /// The structural-former refusal's repair at a call of this spec's own member: the call
    /// names a sort, since no row works. `ErrorTag` declares no member, so a call of one
    /// is never refused here.
    fn former_repair_at_call(self) -> &'static str {
        match self {
            LibraryInstances::TypeValue => {
                "Name a sort in the call's bracket, with no tuple or arrow among its type \
                 arguments: every `TypeValue` instance is derived, one for a sort, and none \
                 may be written"
            }
            LibraryInstances::ErrorTag => self.former_repair(),
        }
    }

    /// The structural-former refusal's repair for this spec: a value, since no row works.
    fn former_repair(self) -> &'static str {
        match self {
            LibraryInstances::TypeValue => {
                "Pass a value whose type is a sort with no tuple or arrow among its type \
                 arguments: every `TypeValue` instance is derived, and none may be written"
            }
            LibraryInstances::ErrorTag => {
                "Raise, in the thunk, a value whose type is a sort with no tuple or arrow \
                 among its type arguments: an `Error.reify` boundary takes the payload's sort \
                 from the `TypeValue` evidence of `Error`'s own provision, which neither a \
                 former nor a written row has"
            }
        }
    }
}

fn library_instances(kb: &KnowledgeBase, spec: Symbol) -> Option<LibraryInstances> {
    let canon = kb.canonical_sort_sym(spec);
    if type_value_spec_sym(kb).is_some_and(|tv| kb.canonical_sort_sym(tv) == canon) {
        Some(LibraryInstances::TypeValue)
    } else if is_error_tag_spec(kb, spec) {
        Some(LibraryInstances::ErrorTag)
    } else {
        None
    }
}

/// The repair the structural-former refusal names: a sort's row that names the former, as
/// `control_a_former_carrier_with_a_provision_loads` writes one, or a value whose type is a
/// sort. Not the row for the two specs whose instances come from the library
/// ([`library_instances`]), where it would be refused in turn or never read.
fn former_repair(kb: &KnowledgeBase, spec: Symbol, former: &FormerCarrier) -> String {
    match former {
        FormerCarrier::Within { library, .. } => library.former_repair().to_owned(),
        FormerCarrier::At(at) => match library_instances(kb, spec) {
            Some(library) => library.former_repair().to_owned(),
            None => format!(
                "Give some sort the row that names this former — `provides {}[… = {at}]` — \
                 or pass a value whose type is a sort",
                kb.qualified_name_of(spec)
            ),
        },
    }
}

/// A tuple or an arrow, by its head and whatever stands inside it: a type no `provides`
/// row can be written ON, so a spec is provided at one only by a sort whose row names it.
fn is_structural_former(kb: &KnowledgeBase, ty: &Value) -> bool {
    matches!(type_head(kb, ty), TypeHead::Arrow | TypeHead::NamedTuple)
}

/// WI-20260920-XSVCS — a dep whose carrier is the CALLER's own type parameter, written
/// as the caller would have to declare it. `requirement` is the whole requirement in the
/// caller's spelling: what the refusal says cannot be supplied.
enum CallerRigidCarrier {
    /// The caller lacks evidence for `carrier`, the first such parameter, spelled as the
    /// CALLER wrote it (`U`, `T`) — never the callee's formal, which is a name from a
    /// declaration the author does not own.
    LacksEvidence {
        carrier: String,
        /// Where the carrier stands inside a sort application the call passes — `Option[T =
        /// C]` for `tyOf(some(x))` over `x: C` — that application in the caller's spelling;
        /// `None` where a binding is the carrier itself.
        within: Option<String>,
        requirement: String,
        /// What to declare, each ready to be pasted after `requires`: the whole
        /// requirement, and not just the carrier binding, for [`RequirementRefusal::render`]'s
        /// own measured reason one arm over — a multi-parameter spec written with a binding
        /// omitted fills the rest from its own parameters, which §5.2 legislates as a second
        /// load error, advice that trades one refusal for another. For the library's two
        /// specs at a carrier inside an application it is `TypeValue` at each parameter the
        /// caller holds none for: their instances are derived per type argument, so the
        /// evidence the caller lacks is that.
        clauses: Vec<String>,
        declare_on: DeclareOn,
    },
    /// For the library's two specs, a part of the requirement no instance answers at
    /// whatever the caller supplies (a spec, a type with no `TypeValue`): no clause is the
    /// repair, and the refusal says why the part has none. `carrier` is the application the
    /// part stands in.
    NoInstance {
        carrier: String,
        requirement: String,
        part: NoInstance,
        library: LibraryInstances,
    },
}

/// WHERE the clauses go — the calling OPERATION when the carrier is one of its `[…]`
/// brackets, the enclosing SORT when it is one of the sort's parameters, and the operation
/// when they name parameters of both. The distinction is not cosmetic: an operation cannot
/// declare its sort's parameter out from under it, and the corpus has one of each
/// (`test.xsvcs.fwd.mid`'s `U`, `test.wi416.Coll`'s `T`).
#[derive(Clone, Copy)]
enum DeclareOn {
    Operation(Symbol),
    Sort(Symbol),
}

impl DeclareOn {
    /// WI-P962X: clauses over signature members forward just as named parameters do. On a
    /// sort each clause is a declaration of its own; an operation's takes a list.
    fn repair(self, kb: &KnowledgeBase, clauses: &[String]) -> String {
        let (on, declare) = match self {
            DeclareOn::Sort(on) => (
                on,
                clauses
                    .iter()
                    .map(|c| format!("`requires {c}`"))
                    .collect::<Vec<_>>()
                    .join(" and "),
            ),
            DeclareOn::Operation(on) => (on, format!("`requires {}`", clauses.join(", "))),
        };
        format!(
            "Declare {declare} on `{}` so the evidence is passed in",
            kb.qualified_name_of(on)
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
    kb: &mut KnowledgeBase,
    dep: &RequiresEntry,
    has_former: bool,
    ctx: &SigmaCtx,
    caller_op: Symbol,
    caller_requires: &DictChain,
) -> Option<CallerRigidCarrier> {
    let goal = goal_from_requires_entry(kb, dep)?;
    let params = caller_param_rigids(kb, caller_op, ctx.param_rigids);
    let library = library_instances(kb, dep.required_sort);
    // `TypeValue`, where the spec is one of the library's two, whose instances it derives.
    let library_type_value = library.and_then(|_| type_value_spec_sym(kb));
    // Each parameter of the caller's a binding names, in binding order, with the application
    // it stands in where it stands in one.
    let mut met: Vec<MetParam> = Vec::new();
    // A part of an application that no instance of the library's spec answers at, whatever
    // the caller supplies: a spec, a sort applied to nothing its parameters need.
    let mut no_instance: Option<NoInstance> = None;
    let mut bindings: Vec<String> = Vec::new();
    for (k, v) in &goal.bindings {
        // EVERY BINDING MUST BE WRITEABLE BY THE CALLER, or there is no clause to print
        // and this function answers `None`. A parameter the CALLER declares (rendered as the
        // caller's own name), a GROUND type (rendered as itself), and a sort applied to
        // these qualify, and nothing else does: `format_term_for_goal`'s fallback prints an
        // unrecognized term as `<term#N>`, and an element that is merely OPEN prints the
        // CALLEE's parameter (`anthill.prelude.List.T`) — the first does not parse and the
        // second is the wrong clause, and the message's whole contract is that what it
        // prints can be pasted.
        //
        // A REFUSAL WITHHELD, never a wrong value: such a call keeps exactly the
        // behaviour it has today, eval's own `not bound` raise included.
        let rendered = match sigma_class_terminal(kb, ctx, v) {
            // A binding that terminates at a RIGID is an enclosing-scope parameter
            // ([`sigma_class_terminal`]'s second component) — but only one the caller
            // DECLARES can be named, a WI-424 body skolem having no written name.
            Some((cls, true)) => {
                let (_, name, owner) = params.iter().find(|(r, _, _)| *r == cls)?;
                met.push(MetParam {
                    name: *name,
                    owner: *owner,
                    rigid: cls,
                    within: None,
                });
                type_param_display_name(kb, *name)
            }
            // Concrete: no σ-class, and it renders as the sort it names.
            None if type_is_ground(kb, v) => format_value_for_goal(kb, v),
            // A sort applied to what the caller can write, holding a parameter of the
            // caller's (`tyOf(some(x))` over `x: C`): that parameter is still the one the
            // caller holds no evidence for, inside the application.
            None => {
                let before = met.len();
                let rendered = caller_writeable_application(
                    kb,
                    ctx,
                    &params,
                    v,
                    library_type_value,
                    &mut met,
                    &mut no_instance,
                )?;
                for m in &mut met[before..] {
                    m.within = Some(rendered.clone());
                }
                rendered
            }
            // Open (the WI-415/418 gap), or a carrier this function cannot name.
            Some((_, false)) => return None,
        };
        bindings.push(format!("{} = {}", kb.local_name_of(*k), rendered));
    }
    let requirement = format!(
        "{}[{}]",
        kb.qualified_name_of(goal.spec_sort),
        bindings.join(", ")
    );
    // The library's two specs inside an application: their instances are derived per type
    // argument, so the evidence the caller lacks is `TypeValue` at each parameter it holds
    // none for — and where a part has no instance at all, or a structural former stands
    // among the parts (the former refusal's, which names it), no evidence of the caller's
    // would answer.
    let per_parameter = library.is_some() && met.iter().any(|m| m.within.is_some());
    if per_parameter && has_former {
        return None;
    }
    // A part without an instance: no evidence of the caller's answers there. The library's
    // two specs have one binding, so every parameter met stands in the one application.
    if let (Some(part), Some(library)) = (no_instance, library) {
        let carrier = met.first()?.within.clone().unwrap_or_else(|| requirement.clone());
        return Some(CallerRigidCarrier::NoInstance {
            carrier,
            requirement,
            part,
            library,
        });
    }
    let lacking: Vec<&MetParam> = if per_parameter {
        met.iter()
            .filter(|m| !caller_holds_type_value(kb, caller_requires, ctx, m.rigid))
            .collect()
    } else {
        met.iter().collect()
    };
    // Every parameter covered: the requirement failed for a reason this arm does not read.
    let first = *lacking.first()?;
    let clauses: Vec<String> = match library_type_value.filter(|_| per_parameter) {
        Some(tv) => {
            let mut seen: HashSet<Symbol> = HashSet::new();
            lacking
                .iter()
                .filter(|m| seen.insert(m.name))
                .map(|m| {
                    format!(
                        "{}[T = {}]",
                        kb.qualified_name_of(tv),
                        type_param_display_name(kb, m.name)
                    )
                })
                .collect()
        }
        None => vec![requirement.clone()],
    };
    // A member is the calling operation's own, and a clause that names its bracket's
    // parameter goes on that operation whatever declares the carrier; so do clauses over
    // parameters of two declarations, since an operation's clause may name its sort's
    // parameters and a sort's may not name the operation's.
    let declare_on = if met.iter().any(|m| kb.member_param_head(m.name).is_some())
        || lacking.iter().any(|m| m.owner != first.owner)
        || first.owner == caller_op
    {
        DeclareOn::Operation(caller_op)
    } else {
        DeclareOn::Sort(first.owner)
    };
    Some(CallerRigidCarrier::LacksEvidence {
        carrier: type_param_display_name(kb, first.name),
        within: first.within.clone(),
        requirement,
        clauses,
        declare_on,
    })
}

/// A parameter of the caller's that a binding of a requirement names
/// ([`caller_rigid_carrier`]): its name and the declaration that owns it, the rigid its body
/// skolemized it to, and the application of the binding it stands in, rendered, where it
/// stands in one.
struct MetParam {
    name: Symbol,
    owner: Symbol,
    rigid: VarId,
    within: Option<String>,
}

/// Does the caller's scope answer `TypeValue` at the parameter `rigid`: a `requires
/// TypeValue[T = P]` of the calling operation or its sort, or a requirement whose contract
/// holds one (`requires Desc[T = P]` under `Desc requires TypeValue[T = T]`) — asked of the
/// resolver with the caller's chain for its scope, so the cover is the one a call reads.
fn caller_holds_type_value(
    kb: &mut KnowledgeBase,
    caller_requires: &DictChain,
    ctx: &SigmaCtx,
    rigid: VarId,
) -> bool {
    let Some(tv) = type_value_spec_sym(kb) else {
        return false;
    };
    let Some(param) = kb.type_params_of_sort(tv).into_iter().next() else {
        return false;
    };
    let key = kb.intern(&param);
    let at = Value::term(kb.alloc(Term::Var(Var::Rigid(rigid))));
    let goal = SortGoal {
        spec_sort: tv,
        bindings: smallvec::smallvec![(key, at)],
        carrier: None,
    };
    let scope = ResolutionScope {
        available_requires: caller_requires.entries(),
        sigma: Some(ctx),
        pin: None,
        sub_goal_requires: &[],
    };
    // The call's own goal reads the chain beneath a scope entry only as a sub-goal does
    // (`resolve_inner`), so it is asked here too.
    matches!(resolve(kb, &goal, &scope), ResolutionResult::Resolved(_))
        || scope_chain_cover(kb, &scope, &goal).is_some()
}

/// A type argument of a call that is a sort applied to what the caller can write, rendered
/// in the caller's spelling — a parameter the caller declares, a ground type, or such an
/// application again — with each parameter met pushed onto `met`. For the library's two
/// specs (`library_type_value` is `TypeValue`, which derives their instances) a parametric
/// variant is read at its sort, and a part no instance answers at whatever the caller
/// supplies — a spec, a ground type with no `TypeValue` — is recorded in `no_instance`, the
/// first one met. `None` for anything else, a binding nothing here may name.
fn caller_writeable_application(
    kb: &mut KnowledgeBase,
    ctx: &SigmaCtx,
    params: &[(VarId, Symbol, Symbol)],
    v: &Value,
    library_type_value: Option<Symbol>,
    met: &mut Vec<MetParam>,
    no_instance: &mut Option<NoInstance>,
) -> Option<String> {
    // A variable σ bound to the application is read through.
    let bound;
    let v = match v.head(kb) {
        ViewHead::Var(Var::Global(vid)) => {
            bound = ctx.subst.resolve_as_value(vid)?.clone();
            &bound
        }
        _ => v,
    };
    // A TUPLE, for a spec of the program's: a row can be written at one through a sort that
    // names it, and the caller's parameter in it is still the one it holds no evidence for
    // (`Reader.probe((x, 1))` over `x: C`). Its parts are read as an application's. The
    // library's two specs have no instance at a former, which the former refusal says.
    if library_type_value.is_none() {
        if let TypeExtractor::NamedTuple(fields) = extract_type(kb, v) {
            let mut parts: Vec<String> = Vec::with_capacity(fields.len());
            for (label, a) in &fields {
                let rendered = match sigma_class_terminal(kb, ctx, a) {
                    Some((cls, true)) => {
                        let (_, name, owner) = params.iter().find(|(r, _, _)| *r == cls)?;
                        met.push(MetParam {
                            name: *name,
                            owner: *owner,
                            rigid: cls,
                            within: None,
                        });
                        type_param_display_name(kb, *name)
                    }
                    Some((_, false)) => return None,
                    None if type_is_ground(kb, a) => format_value_for_goal(kb, a),
                    None => caller_writeable_application(
                        kb,
                        ctx,
                        params,
                        a,
                        library_type_value,
                        met,
                        no_instance,
                    )?,
                };
                let label = kb.local_name_of(*label);
                parts.push(if crate::intern::positional_label_index(label).is_some() {
                    rendered
                } else {
                    format!("{label}: {rendered}")
                });
            }
            return Some(format!("({})", parts.join(", ")));
        }
    }
    let TypeExtractor::Parameterized { base, bindings } = extract_type(kb, v) else {
        return None;
    };
    // For the library's two specs a parametric variant (`Wrap.wrap[V = C]`) is its sort at
    // the same arguments, whose derived instance answers for it. For any other spec the
    // requirement is said as the call states it: a scope clause covers a goal at the type it
    // names, and one at the variant's sort does not cover the variant (the clause advised so
    // brought the same refusal back).
    let at_its_sort = library_type_value.and_then(|_| variant_at_its_sort(kb, base, &bindings));
    let (base, bindings) = match at_its_sort {
        Some(at_sort) => match extract_type(kb, &at_sort) {
            TypeExtractor::Parameterized { base, bindings } => (base, bindings),
            _ => return None,
        },
        None => (base, bindings),
    };
    let mut parts: Vec<String> = Vec::with_capacity(bindings.len());
    for (k, a) in &bindings {
        let rendered = match sigma_class_terminal(kb, ctx, a) {
            Some((cls, true)) => {
                let (_, name, owner) = params.iter().find(|(r, _, _)| *r == cls)?;
                met.push(MetParam {
                    name: *name,
                    owner: *owner,
                    rigid: cls,
                    within: None,
                });
                type_param_display_name(kb, *name)
            }
            Some((_, false)) => return None,
            None if type_is_ground(kb, a) => {
                let rendered = format_value_for_goal(kb, a);
                if let (Some(tv), None) = (library_type_value, no_instance.as_ref()) {
                    if let Some(failure) = type_value_failure_at(kb, tv, a) {
                        *no_instance = Some(NoInstance {
                            part: rendered.clone(),
                            failure: Some(failure),
                        });
                    }
                }
                rendered
            }
            None => caller_writeable_application(
                kb,
                ctx,
                params,
                a,
                library_type_value,
                met,
                no_instance,
            )?,
        };
        parts.push(format!("{} = {rendered}", kb.local_name_of(*k)));
    }
    let rendered = format!("{}[{}]", kb.qualified_name_of(base), parts.join(", "));
    // A spec is no sort a `TypeValue` is derived for, whatever its arguments.
    if let (Some(tv), None) = (library_type_value, no_instance.as_ref()) {
        if !carrier_has_provision_row(kb, base, tv) {
            *no_instance = Some(NoInstance {
                part: rendered.clone(),
                failure: None,
            });
        }
    }
    Some(rendered)
}

/// A part of a library requirement that no instance answers at ([`CallerRigidCarrier`]):
/// the part, rendered, and the resolution that failed for it, where one was asked — a spec
/// base has no row of `TypeValue` at all, and none is.
pub(super) struct NoInstance {
    pub(super) part: String,
    pub(super) failure: Option<ResolutionResult>,
}

/// The resolution of `TypeValue[T = ty]`, `ty` ground, where it does not resolve: why the part
/// has no instance, which may be a goal of another spec (`Keyed[K = Float]`'s instance needs
/// `Desc[T = Float]`).
fn type_value_failure_at(kb: &mut KnowledgeBase, type_value: Symbol, ty: &Value) -> Option<ResolutionResult> {
    resolve_spec_at(kb, type_value, ty).filter(|r| !matches!(r, ResolutionResult::Resolved(_)))
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

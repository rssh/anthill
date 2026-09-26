//! `TypeError` — every refusal the typer can raise — with its context types and
//! its rendering (`format`, and the `LoadError` conversion).

use super::*;

// ── TypeError ──────────────────────────────────────────────────

/// WI-1119 — a dot receiver that is a `requires`-constrainable TYPE PARAMETER: what the
/// [`TypeError::DotDispatchNoMatch`] refusal names when the member reached no spec. Both
/// halves are computed where the ladder ran, not re-derived at rendering: `specs` is the
/// set [`constraining_spec_definers`] actually searched, so an EMPTY one says "the
/// parameter is unconstrained" and a populated one says "these constrain it and none
/// declares the member" — two different repairs.
#[derive(Clone, Debug)]
pub struct ConstrainedParamReceiver {
    /// The parameter as written, rendered — `?PT`.
    pub param: String,
    /// The specs constraining it, from both chain sources, transitively.
    pub specs: Vec<Symbol>,
}

/// WI-1119 — the half of a [`TypeError::DotDispatchNoMatch`] on a type-parameter receiver
/// that says what to DO, shared by the `format` and `LoadError` faces so the two cannot
/// drift. Two repairs, told apart by whether anything constrains the parameter at all:
/// write a `requires` clause, or reach for a member one of the clauses actually declares.
fn constrained_param_repair(kb: &KnowledgeBase, specs: &[Symbol], member: &str) -> String {
    if specs.is_empty() {
        return format!(
            "no `requires` clause constrains it, so no spec declares '{member}' for it — \
             add one on the operation or its sort",
        );
    }
    format!(
        "the specs constraining it declare no '{}' ({})",
        member,
        specs
            .iter()
            .map(|s| kb.qualified_name_of(*s).to_string())
            .collect::<Vec<_>>()
            .join(", "),
    )
}

/// WI-1119 — [`TypeError::AmbiguousConstrainedParamMember`]'s body, shared by both faces.
/// Names each tied spec and the qualified spelling that settles it: unlike a supplier tie
/// (`AmbiguousSpecOpDispatch`), this one always HAS a repair the author can write, because
/// the ambiguity is in the member NAME and qualifying the call removes it.
fn ambiguous_constrained_param_message(
    kb: &KnowledgeBase,
    member: &str,
    receiver: &str,
    specs: &[Symbol],
) -> String {
    format!(
        "ambiguous member '{}' on `{}`: {} constrain it and each declares '{}' — \
         neither refines the other, so write the call qualified ({}) to say which",
        member,
        receiver,
        specs
            .iter()
            .map(|s| kb.qualified_name_of(*s).to_string())
            .collect::<Vec<_>>()
            .join(" and "),
        member,
        // QUALIFIED, not short-named: two tied specs may share a short name in different
        // namespaces (`a.Desc` and `b.Desc`), and the short form would then print the same
        // suggestion twice — neither of which disambiguates at the call site either. The
        // qualified name is a writable spelling, so the repair stays one the author can
        // paste.
        specs
            .iter()
            .map(|s| format!("{}.{}(…)", kb.qualified_name_of(*s), member))
            .collect::<Vec<_>>()
            .join(" or "),
    )
}

#[derive(Clone, Debug)]
pub enum TypeError {
    /// Canonical type mismatch from `assert_compatible`. `context` is where
    /// in the program the mismatch was detected so the user-facing message
    /// can name the field/operation rather than just "type mismatch".
    TypeMismatch {
        span: Option<Span>,
        context: TypeErrorContext,
        // WI-342 (S2): carrier-agnostic `Value` — a denoted-bearing type
        // (a lambda's `Value::Node` arrow) flows straight into the diagnostic
        // without re-grounding. Rendered via `type_display_name_value`.
        expected: Value,
        actual: Value,
        // WI-510: source location of the `TypeError::TypeMismatch { … }`
        // construction, captured via the `#[track_caller]` `here()` helper.
        // `TypeMismatch`/`Other` both flatten a `TypeErrorContext` + `Value`s
        // into `LoadError::TypeMismatch` display strings, so two structurally
        // different checks can render identically (WI-509 debugging cost). This
        // marker is threaded into `LoadError::TypeMismatch.origin` so a mismatch
        // can be traced to its construction site without hand-instrumenting.
        site: &'static std::panic::Location<'static>,
        /// WI-20260824-Q0093 (`docs/design/055-implementation.md` §8, *wrong
        /// destination*) — WHAT THE REJECTED EXPRESSION DENOTES, rendered, when it is a
        /// proposal-055 classified type value: `Some("Cell[V = Int64]")`, printed as
        /// `expected String, got Type (Cell[V = Int64])`.
        ///
        /// It cannot be read off `actual`, and that is the whole reason for the field.
        /// `actual` is the expression's TYPE, and every classified type value has the
        /// same one — `Type` — so the pair renderer can only ever say `got Type`. What
        /// the author needs to see is the VALUE: which sort the name they wrote now
        /// denotes, since a bare `Leaf` in a `String` slot is most often a `Leaf()` with
        /// the parentheses left off, and §8 asks for exactly that to be visible.
        ///
        /// `None` at every site that has no expression occurrence to ask — a check run
        /// between two types alone (a branch join, a declared/actual signature pair)
        /// knows the types and nothing about what produced them. Filled by
        /// [`conformance_error`], which is the one renderer the op-argument,
        /// entity-field, let-annotation and op-return channels all route through.
        denoted: Option<String>,
    },
    NoParentSort {
        name: Symbol,
    },
    UnresolvedName {
        span: Option<Span>,
        name: Symbol,
    },
    /// Constructor symbol has no declared entity-field-types entry.
    /// Reported from `check_constructor_iter` when `entity_field_types`
    /// returns None for what looked like a constructor invocation.
    NoConstructor {
        span: Option<Span>,
        name: Symbol,
    },
    /// `check_apply_iter` was handed a functor symbol that is neither
    /// a known operation, a constructor, nor a var-bound arrow type.
    UnknownApplyFunctor {
        span: Option<Span>,
        name: Symbol,
    },
    /// WI-1058 — a compound term in a RULE BODY'S DATA slot whose functor names nothing.
    /// The argument-position half of WI-895, and a DIFFERENT claim from
    /// [`Self::UnknownApplyFunctor`]: a data slot is not a call site, so "expected a
    /// known operation" would be advice about the wrong thing. What is wrong is that the
    /// name resolves to no declaration at all, so the term can never match and the redex
    /// can never fire. Its goal-position twin is `LoadError::UndefinedRuleBodyGoal`, and
    /// the two share one head test (`KnowledgeBase::undefined_functor`).
    UndefinedDataFunctor {
        span: Option<Span>,
        name: Symbol,
    },
    /// WI-565: the refinement of [`TypeError::UnknownApplyFunctor`] for the specific case
    /// where the unresolved bare functor IS the short name of a MEMBER operation
    /// of one or more sorts (`owning_sorts`). A member's bare name is in scope
    /// only WITHIN its defining sort (a sibling member can bare-call it); from
    /// outside it must be qualified `Sort.member(…)` or dot-dispatched
    /// `receiver.member(…)`. The scoping is correct — this variant only carries a
    /// better diagnostic that names the owning sort(s) and the qualified/dot
    /// remedy, instead of the terse "unknown functor". `owning_sorts` is deduped
    /// (by qualified name) and sorted for a deterministic message.
    ///
    /// WI-898 widened it past member OPERATIONS to member EQUATION FUNCTORS (`ite`
    /// on `Bool`), which is why `dot_dispatchable` exists: only an operation answers
    /// `receiver.member(…)`, so the remedy names that spelling only when one is
    /// among the candidates.
    BareMemberCall {
        span: Option<Span>,
        member: Symbol,
        owning_sorts: SmallVec<[Symbol; 2]>,
        dot_dispatchable: bool,
    },
    /// WI-898: a citation of an EQUATION-INTRODUCED functor
    /// ([`crate::intern::SymbolKind::EquationFunctor`]) — `ite(gte(a, b), a, b)` —
    /// that the `@[simp]` rewriter left standing. Such a name denotes a function
    /// DEFINED BY REWRITING; a citation of it is answered before dispatch or not at
    /// all, so one that survives to the typer has nothing left to mean.
    ///
    /// IT IS THE DIAGNOSTIC WI-898 EXISTS FOR. The kind used to be `Goal`, which
    /// routed the name into WI-714's relation machinery; that found zero clauses
    /// (an equation's clauses are indexed under the `eq`/`unify` connective) and
    /// reported [`Self::UnresolvedName`] — a name that resolved perfectly well,
    /// described as unresolved, on exactly the spelling WI-894 recommends.
    ///
    /// `census` is [`crate::kb::simp_rewrite::equation_clause_census`]'s, taken at
    /// construction (the message needs a `&mut KnowledgeBase` the renderers do not
    /// have) — it decides WHICH of the two failures this is: inert clauses that want
    /// a `@[simp]` tag, or firing clauses none of which matched.
    UnreducedEquationFunctor {
        span: Option<Span>,
        functor: Symbol,
        census: crate::kb::simp_rewrite::ClauseCensus,
    },
    /// Spec-op dispatch found no impl whose per-call bindings match the
    /// inferred type arguments. `op` is the qualified spec-op symbol
    /// (e.g. `anthill.prelude.Additive.add`).
    ///
    /// WI-869 — `unmet` is the goal the search actually failed on, as the search
    /// itself rendered it (never re-derived here; the WI-828 rule). For a
    /// CONDITIONAL provision that is the condition, not the call: `Ord.compare`
    /// on a `Pair[Float, Int64]` is refused because `Ord[T = Float]` has no
    /// provider, and without naming it the message says only that the pair has no
    /// ordering — true, and useless for finding out why.
    DispatchNoMatch {
        span: Option<Span>,
        op: Symbol,
        unmet: Option<Box<DispatchFailure>>,
    },
    /// Spec-op dispatch found multiple impls and the call selected none —
    /// proposal 058 §4.1 **tier 3**, the refusal WI-843 moved here from load time.
    ///
    /// Before that move this variant said only "multiple impls match (coherence
    /// rule)", which was enough because the *declarations* had already been refused
    /// — the author's repair was to delete one, and the load error naming the pair
    /// said so. Now the pair is legal and this is the whole diagnostic, so it
    /// carries what the author needs AT the call: which providers answered, and the
    /// bracket that picks one. See [`crate::kb::load::LoadError::UnselectedInstance`].
    DispatchAmbiguous {
        span: Option<Span>,
        op: Symbol,
        /// The tie, by SYMBOL and stamped at the level it was observed — see
        /// [`InstanceTie`] for why both matter. Rendering (and the concreteness
        /// scan it needs) happens at `format` / `to_load_error`, not here.
        tie: InstanceTie,
    },
    /// WI-1012 — the STATIC face of [`crate::eval::EvalError::AmbiguousSpecOpDispatch`]:
    /// a statically CONCRETE carrier has two or more runnable suppliers of one spec op
    /// ([`carrier_override_suppliers`]), so the WI-444 override pin declines and the
    /// program has not said which implementation to run. Same name as the eval variant
    /// on purpose — one refusal with two faces, like `MacroRejected` (WI-757).
    ///
    /// WHY IT IS NOT [`Self::DispatchAmbiguous`], verified rather than assumed: that
    /// variant's [`InstanceTie`] carries PROVIDER symbols, and for a route-1-vs-route-2
    /// tie both providers canonicalize to the SAME carrier — `render_instance_tie`
    /// would print `Leaf, Leaf` and, both being concrete, choose
    /// [`TieRepair::ValueDirected`], whose message ("each is a CONCRETE provider …
    /// pin the carrier through the call's receiver") describes a different failure
    /// entirely. This tie is between TEXTS supplying one carrier, so its candidates
    /// are rendered by SUPPLY ROUTE ([`SpecOpSupplier::render`]) — the only wording
    /// that can name an instance fact, which has no name of its own (058 §4.3).
    ///
    /// WHY AT LOAD AT ALL, given eval refuses it too: raising only at the call means
    /// `anthill check` passes on a program the interpreter will refuse, a tie in a
    /// branch that never runs never reports, and — the reason this exists — on the SLD
    /// path the refusal DEGRADES TO SILENCE, since `resolve.rs`'s bridge residualizes
    /// `AmbiguousSpecOpDispatch` to `None` and the enclosing rule simply stops
    /// answering. The eval site STAYS: the WI-444 block fires only on a statically
    /// concrete carrier, so an unpinnable one still needs the late refusal. That is an
    /// argument for SHARING the message body
    /// ([`ambiguous_spec_op_dispatch_message`]), not for having only one site.
    ///
    /// Candidates are rendered at CONSTRUCTION, unlike `DispatchAmbiguous`'s symbols,
    /// for a reason stronger than the one first written here: [`SpecOpSupplier`] and
    /// [`SupplyRoute`] are `pub(crate)` while this enum is `pub`, so carrying them
    /// would leak a private type through a public interface. (The eval face also has
    /// no `&KnowledgeBase` at `Display` time, which is what fixes the shared body's
    /// `&[String]` signature — but that alone would not rule out symbols HERE.)
    /// What pre-rendering does discard is the routes, so the repair that depends on
    /// them is computed at the same moment and carried beside the strings.
    /// WI-1119 — a dot on a `requires`-constrained TYPE-PARAMETER receiver whose member
    /// name is declared by TWO of the specs constraining it, with neither refining the
    /// other (§8.7's requires-REFINEMENT rule, [`most_refined_spec`], already settled the
    /// orderable case). Refused rather than resolved by the order the clauses are written
    /// — see [`find_spec_op_for_constrained_param`], which owns the reasoning.
    ///
    /// NOT [`Self::AmbiguousSpecOpDispatch`], which is a different question at a different
    /// moment: there ONE operation is named and two TEXTS supply an implementation of it
    /// for one carrier, so its candidates render by supply route. Here two distinct
    /// operations answer to one member NAME and no implementation has been looked for yet;
    /// naming the specs is the whole repair, since qualifying the call (`Desc.describe(x)`)
    /// is what resolves it.
    AmbiguousConstrainedParamMember {
        span: Option<Span>,
        /// The member name written after the dot.
        member: Symbol,
        /// The receiver's rendered type — the parameter, e.g. `?PT`.
        receiver: String,
        /// The tied constraining specs, in the order their clauses are written.
        specs: Vec<Symbol>,
    },
    AmbiguousSpecOpDispatch {
        span: Option<Span>,
        /// The spec op being dispatched, e.g. `ns.Desc.describe`.
        op: Symbol,
        /// The one carrier every candidate supplies an implementation FOR.
        carrier: Symbol,
        /// Each supplier rendered by its route — see [`render_suppliers`].
        candidates: Vec<String>,
        /// Whether any rival can be NAMED — see [`SupplierTieRepair`].
        repair: SupplierTieRepair,
    },
    /// `op[bindings](args)` named a binding key that doesn't correspond
    /// to any of the op's declared type-parameters. Replaces the
    /// WI-269 Phase D silent-drop site in `seed_op_type_args`.
    ///
    /// WI-839: raised for a callee with NO op-level type parameters too. That case
    /// used to return early (`op.type_params.is_empty()`), so `plain[Bogus = Int64](n)`
    /// loaded clean and meant nothing — and proposal 058 reuses this very channel for
    /// instance selection, so an accepted-but-inert spelling is the hazard the arc
    /// starts by closing (058 §2.2 / §9 phase 0).
    NoSuchTypeParam {
        span: Option<Span>,
        op: Symbol,
        name: Symbol,
    },
    /// WI-839: a call-site bracket supplies more POSITIONAL type arguments than the
    /// callee has parameters left to bind — `plain[Int64](n)` on a param-less callee,
    /// `idy[Int64, String](n)` on a one-param one, `idy[T = Int64, String](n)` where a
    /// NAMED binding already took the only slot. The named twin of this drop is
    /// [`Self::NoSuchTypeParam`]; positionals had their own silent `continue` in
    /// `seed_op_type_args` and needed a diagnostic of their own, since an
    /// unmatched positional has no key to name.
    ExcessCallTypeArgs {
        span: Option<Span>,
        op: Symbol,
        /// Positional bindings written in the bracket.
        given: usize,
        /// Parameters left for them — declared MINUS those a named key already took,
        /// not simply declared: `idy[T = Int64, String]` over-applies a ONE-param
        /// callee, and counting against `declared` would call that within budget.
        free: usize,
    },
    /// WI-839: one call-site bracket binds the same type parameter TWICE —
    /// `two[A = Int64, A = String](…)`. Both keys resolve to the same parameter var,
    /// so the second unification contradicts the first and its failure is discarded:
    /// `A = String` is written and means nothing. The same defect WI-805 / WI-808 /
    /// WI-809 refused for tuple labels, entity fields and named ARGUMENT lists —
    /// this is the type-argument list, which had no such guard.
    DuplicateCallTypeArg {
        span: Option<Span>,
        op: Symbol,
        name: Symbol,
    },
    /// WI-20260911-RS2G4 (058 rule 1, the SORT half of the BINDING): a form-(3)
    /// companion receiver's bracket and the CALLEE's own bracket bind one of the
    /// enclosing sort's type parameters to two different types —
    /// `Map[K = Bool, V = Bool].empty[K = String, V = Int64]()`.
    ///
    /// Both spellings bind the SAME variable now (rule 1 spans the operation's scope
    /// and its enclosing sort's, and the receiver reaches that seeding as of this
    /// ticket), so two disagreeing brackets are a contradiction the author wrote, not
    /// a precedence question. Before, the receiver silently won and the arguments were
    /// checked against its claim — one written binding meant nothing, which is exactly
    /// the silent drop WI-839 refused for the other channel.
    ///
    /// ITS OWN VARIANT rather than a [`Self::TypeMismatch`]: the two sides are two
    /// BRACKETS, not an expression and the context that rejected it, and the message
    /// has to say which spelling said what — a bare `expected X, got Y` would send the
    /// author to neither.
    ReceiverBracketConflict {
        span: Option<Span>,
        /// The callee — whose call carries both brackets.
        op: Symbol,
        /// The enclosing sort's parameter both brackets bind.
        param: Symbol,
        /// What the RECEIVER's bracket wrote for it.
        receiver: Value,
        /// What the call had ALREADY bound it to when the receiver was read. The only
        /// earlier writer at this point is [`seed_op_type_args`] — `subst` is fresh and
        /// nothing else has touched it — so this is the callee bracket's value.
        callee: Value,
    },
    /// WI-839: a call-site bracket on a callee that is not an OPERATION at all — a
    /// function VALUE (arrow-typed variable or lambda), an applied rule citation
    /// (WI-714), a bare-functor constructor invocation. Only an operation carries the
    /// type-parameter list a bracket binds, so no key could ever match; this is
    /// deliberately NOT [`Self::NoSuchTypeParam`], which would imply that some OTHER
    /// key would have been accepted and would render a local binder through
    /// `qualified_name_of` as though it were an operation.
    TypeArgsOnNonOperation {
        span: Option<Span>,
        callee: Symbol,
    },
    /// WI-841 (058 §4.2 rule 2): a bracket key matched the SPEC SHORT NAME of two or
    /// more of the callee's anonymous requirement slots — `requires Monoid[T],
    /// Monoid[U]`, or two specs sharing a last segment. The short name is a GATED
    /// shorthand: the gate is exactly "unambiguous among the remaining anonymous
    /// slots", and without it this would be the short-name identity comparison
    /// WI-672 deleted. The fix is to NAME the slot (§4.7), which makes it a type
    /// parameter and so puts it under rule (1) — the complete mechanism.
    AmbiguousRequirementKey {
        span: Option<Span>,
        op: Symbol,
        /// The written key.
        name: Symbol,
        /// The qualified spec of each slot it matched.
        slots: Vec<String>,
    },
    /// WI-841: `f[Spec = 42](…)` — a key that names a requirement SLOT, bound to
    /// something that is not a sort. The value position of a slot binding denotes a
    /// WITNESS, so there is no provider to check and no impl to pin. Its own variant
    /// rather than [`Self::WitnessDoesNotProvide`], which would have to name the
    /// non-sort as the witness and would render "Spec does not provide Spec".
    SelectionValueNotASort {
        span: Option<Span>,
        op: Symbol,
        spec: Symbol,
    },
    /// WI-870: `f[Spec = W[Slot = X]](…)` where `W`'s named slot `Slot` cannot be
    /// located in `W`'s DICTIONARY chain. The two indexings coincide by construction
    /// ([`dict_chain_index_of_named_slot`] states why), so this is an internal
    /// disagreement rather than an author error — and it is an ERROR rather than a
    /// dropped binding because pinning the wrong slot is silent: it resolves a real
    /// goal with a real provider and computes a wrong answer.
    SlotSelectionUnindexable {
        span: Option<Span>,
        op: Symbol,
        /// The witness whose slot could not be indexed.
        owner: Symbol,
        /// The slot's binder as written.
        binder: Symbol,
    },
    /// WI-1094 (058 §3.4/§3.9): a call whose callee declares a NAMED requirement slot
    /// the enclosing signature left UNIVERSALLY QUANTIFIED — `size(s: SortedSet[T =
    /// String])` calling `SortedSet.toList(s)` — with nothing in the frame supplying its
    /// dictionary. §3.4 makes omission in TYPE position mean "any", so the value flowing
    /// in already chose; §3.9 leaves two lawful answers, forward the value's dictionary
    /// or refuse, and forwarding is unavailable BY CONSTRUCTION — a dictionary rides in a
    /// FRAME, never in a value, so a signature declaring no slot for it has nothing to
    /// forward. Constructing one instead is a rival for a decision made elsewhere:
    /// MEASURED, a `Descending` set read back in ascending order.
    ///
    /// COUNT-INDEPENDENT, deliberately. Before this ticket the same shape was refused
    /// only when two or more providers happened to TIE
    /// ([`TypeError::DispatchAmbiguous`]); with one provider it loaded and constructed
    /// silently. `provider` is what the construction WOULD have picked — named because
    /// "it would have used this one" is what makes the refusal actionable, not because
    /// the count matters.
    ErasedRequirementSlot {
        span: Option<Span>,
        op: Symbol,
        /// The slot's binder as the callee declared it (`O`).
        binder: Symbol,
        /// The spec the slot demands (`Ord`).
        spec: Symbol,
        /// The provider a construction would have chosen at this call's bindings, when
        /// one exists. `None` where the element is abstract and only a FORWARD was
        /// available — the case whose wrong dictionary comes out of the caller's own
        /// chain rather than out of a search.
        provider: Option<Symbol>,
        /// WI-20260921-EE0EP — which residue this is, and therefore which repair the
        /// message names. See [`ErasedSlotReason`].
        reason: ErasedSlotReason,
    },
    /// WI-841 (058 §4.4 check 1): `f[Spec = W](…)` named a witness that does not
    /// provide that spec at all — no `SortProvidesInfo(sort_ref = W, spec = Spec[…])`
    /// exists. Names BOTH, since either half can be the typo.
    WitnessDoesNotProvide {
        span: Option<Span>,
        op: Symbol,
        witness: Symbol,
        spec: Symbol,
        /// WI-841: the witness DOES provide the spec, just not at this call's
        /// bindings. Distinguished because the two need opposite advice — MEASURED,
        /// one message told the author of `[Monoid = StrM]` (which declares `fact
        /// Monoid[T = String]`) to add a `fact Monoid[…]` that already existed, and
        /// never named the bindings, which are the whole content of the mismatch.
        at_bindings: bool,
    },
    /// WI-841 (058 §4.4 check 3, now §3.5): `f[Spec = W](…)` where `W` is a CONCRETE
    /// provider — a sort with constructors, whose values carry their own sort. Where
    /// those values are the arguments the VALUE decides the dispatch (§1.1, the same
    /// exemption the witness-coherence check applies), so an explicit witness could only
    /// agree redundantly or contradict silently. Refuse, do not prefer. The test is the
    /// SORT's, so it also refuses a concrete provider whose values are not the
    /// arguments; that is decided, see [`validate_instance_selection`].
    ValueDirectedSelection {
        span: Option<Span>,
        op: Symbol,
        witness: Symbol,
        spec: Symbol,
    },
    /// WI-841 (058 §4.2): one bracket selected two DIFFERENT witnesses for one spec
    /// — two keys (a binder and the spec's short name, or two binders of same-spec
    /// slots) resolving to the same `spec_sort`. A selection is keyed by the SPEC at
    /// [`resolve`]'s step 0, so two witnesses under one key have no meaning to give.
    /// Reachable only through a program with two coexisting providers, which stays a
    /// LOAD error until 058 phase 3b moves the coherence refusal to the use site;
    /// refused here so that move does not silently turn it into a first-match.
    ///
    /// WI-844: and the same refusal for the OTHER producer of a selection — the
    /// ARGUMENT TYPES. A named slot is a type parameter, so a sort with two same-spec
    /// named slots can carry two witnesses in ONE type: `Both[T = String, A = ByLength,
    /// B = Alphabetical]`, which a bracket cannot spell (this very error refuses that
    /// spelling) but a parameter ANNOTATION can — measured, it loads. Reading such a
    /// value's slots back would first-match one witness onto both deps, which is
    /// exactly what this variant exists to prevent.
    ///
    /// The message names the two witnesses and NOT which producer wrote each, and that
    /// is deliberate: a MIXED pair is reachable (one slot bracketed, its same-spec
    /// sibling read off the argument's type), so any sentence attributing both to one
    /// producer would be false for it. [`push_selection`] owns the rule for all of them.
    ConflictingSelection {
        span: Option<Span>,
        op: Symbol,
        spec: Symbol,
        first: Symbol,
        second: Symbol,
    },
    /// WI-709: a parameterized type WRITTEN AS A VALUE (WI-707 —
    /// `is_modifiable(Cell[W = Int64])`) whose type arguments do not fit the sort's
    /// declared params. The value-position face of
    /// [`LoadError::InvalidTypeArgument`]:
    /// both are decided by [`KnowledgeBase::check_sort_type_args`], so the written and
    /// the evaluated spelling of one type agree on what is admissible — without which
    /// they would build DIFFERENT terms for the same source text, defeating the
    /// hash-consing identity WI-707 established. Raised here rather than left to eval's
    /// `finish_sort_type` guard, so a typo is heard at load.
    InvalidTypeArgument {
        span: Option<Span>,
        sort: Symbol,
        problem: crate::kb::TypeArgProblem,
    },
    /// A call's type-param could not be pinned from explicit bindings,
    /// from caller-side expected type, or from argument inference. Names
    /// the unconstrained parameter so the user can fix the call by
    /// writing `op[T = …](args)`.
    UnconstrainedTypeParam {
        span: Option<Span>,
        op: Symbol,
        type_param: Symbol,
    },
    /// WI-20260911-5G28A S1 — WI-270's rule at a RULE CITATION. The cited relation's
    /// columns mention a type parameter of its enclosing SORT, and nothing at the citation
    /// fixed it: not the receiver bracket, not an applied argument, not the type the
    /// consumer expects, and not an enclosing instance of the same sort. The relation
    /// value would carry a variable its consumer cannot recover. Names the one spelling
    /// that always fixes it — the receiver bracket — because a rule citation takes no
    /// callee bracket, which is what [`Self::UnconstrainedTypeParam`]'s message suggests.
    UnconstrainedCitationParam {
        span: Option<Span>,
        /// The cited relation.
        relation: Symbol,
        /// The sort that declares it, whose parameter this is.
        sort: Symbol,
        type_param: Symbol,
    },
    /// WI-325: a spec-op call left at least one type parameter abstract
    /// AND the enclosing operation's `requires` chain does not cover the
    /// spec sort. Without a covering `requires`, the runtime has no impl
    /// to dispatch to — so we name this at body-load time rather than at
    /// the first call site that hits a fresh carrier. `spec_op_sym` is the
    /// spec op (e.g. `anthill.prelude.PartialEq.eq`), `spec_sort_sym` is the spec
    /// sort (e.g. `anthill.prelude.Eq`), and `abstract_params` lists the
    /// spec's short type-param names the call left abstract — used to
    /// suggest the exact `requires {spec}[{T = …}]` clause to add.
    MissingRequiresForSpecOp {
        span: Option<Span>,
        spec_op_sym: Symbol,
        spec_sort_sym: Symbol,
        abstract_params: SmallVec<[Symbol; 2]>,
    },
    /// Proposal 066 (WI-20260919-1Z3E7) — [`Self::MissingRequiresForSpecOp`] where the
    /// carrier DOES hold the evidence, as a condition of one of its provisions, and the
    /// body is not written in that provision's `where` block. The same refusal, told
    /// the way the author can act on: the repair is to move the operation into the
    /// block (or give it its own `requires`), not to add a sort-level `requires` that
    /// would condition every provision of the carrier.
    ProvisionConditionOutOfScope {
        span: Option<Span>,
        /// The operation whose body made the call.
        op: Symbol,
        spec_op_sym: Symbol,
        spec_sort_sym: Symbol,
        /// The provisions (base specs) whose `:- goals` hold a `spec_sort_sym` condition.
        provisions: SmallVec<[Symbol; 2]>,
    },
    /// WI-20260917-NR6FJ — a rule body CALLS an operation whose declared `requires`
    /// names a CONCRETE carrier that provides no such spec, and this clause neither
    /// declares the obligation itself.
    ///
    /// THE SIBLING OF [`Self::MissingRequiresForSpecOp`] one call-shape over. That one
    /// refuses a rule-body call to a SPEC OP whose carrier provides nothing; this one
    /// refuses a call to an ORDINARY operation that declared the same obligation — the
    /// slot is inbound, the caller fills it, and here nothing can.
    ///
    /// MEASURED BEFORE IT, and the two outcomes are why this is load-blocking: with a
    /// BODY-LESS spec op the callee's body defers to its slot, the frame binds nothing
    /// and `bridge_op_to_eval` raises `EvalError::Internal` — a debug-build ABORT from a
    /// program that type-checked. With a DEFAULTED one the call silently folds the
    /// spec's default instead. The eval site's own comment asks for exactly this
    /// refusal: "it wants a LOAD refusal naming the carrier sort and the missing
    /// provision … WI-1102 puts the refusal at the CALL, at load, where the typer has
    /// both."
    ///
    /// AT THE CALL, NEVER AT THE DECLARATION. An operation may be declared here and its
    /// provision supplied by whoever loads the file — `wi840_named_requires_slot_test`
    /// declares a two-slot op over a spec no carrier provides and never calls it, which
    /// is a legitimate program and stays one.
    UnfillableOperationRequirement {
        span: Option<Span>,
        callee_op: Symbol,
        spec_sort_sym: Symbol,
        carrier_sym: Symbol,
    },
    /// WI-20260925-PRVA2 (c) — a rule-body call to a spec operation whose carriers, known at
    /// load, stand at spec parameters other than its carrier parameter, and NO provision
    /// binds them together: `Conv.conv(m(v: 3), 5)` where `Conv[A, B]`'s one provision is
    /// `sort Meters provides Conv[A = Meters, B = String]`.
    ///
    /// THE SIBLING OF [`Self::UnfillableOperationRequirement`], whose sentence is about ONE
    /// carrier — "`X` provides no `Spec`" — and is false here: `Int64` at `B` is a
    /// provision's binding, never a provider, and a sort that provides `Conv` at other
    /// bindings is not helped by providing it again. The repair is a provision at the
    /// combination.
    NoProvisionAtCarriers {
        span: Option<Span>,
        callee_op: Symbol,
        spec_sort_sym: Symbol,
        /// `(spec parameter, carrier sort)` for each known carrier, in parameter order.
        bindings: Vec<(Symbol, Symbol)>,
    },
    /// WI-20260919-N31XX (proposal 065, "The rule") — a RIGID TYPE IS READ AS A VALUE
    /// AND NOTHING IN SCOPE SAYS IT MAY BE.
    ///
    /// `operation bad[B](x: B) -> Type = Cell[V = B]` reads `B` in value position. Under
    /// 065 that is well-formed only under `requires TypeValue[T = B]` among the
    /// requirements in scope — the operation's own, or its enclosing sort's. Otherwise
    /// the signature `f[B](x: B) -> R` would promise nothing about whether `f` inspects
    /// `B`, which is 065's opening complaint: parametricity is false, a provider's own
    /// parameter reached through a slot has no call site that could supply it, and an
    /// erasing backend has nothing to read.
    ///
    /// EXPLICIT, NOT INFERRED (user decision, 2026-09-19): the clause is part of the
    /// SIGNATURE, because the signature is what a caller — and a spec — reads. Inferring
    /// it from the body is deferred, not rejected (065 open question 1), and it could not
    /// apply to a body-less spec operation at all.
    ///
    /// WHAT IT DOES NOT COVER, each because the read is not a value read: a TYPE position
    /// (`x: B`, `-> List[T = B]`, a `requires` bracket) is static and erasable; a CONCRETE
    /// sort in value position (`Cell[V = Int64]`) reads no rigid and its `TypeValue` is
    /// discharged statically; and a RULE BODY unifies types rather than reading them.
    ///
    /// `param` is the parameter as the author wrote it; `op` is the operation whose
    /// signature must gain the clause.
    TypeValueReadUnbacked {
        span: Option<Span>,
        param: Symbol,
        op: Symbol,
    },
    /// WI-828: a cross-sort call (direct or op-as-function-value) to an
    /// operation of a `requires`-carrying sort whose requirement the call site
    /// can neither CONSTRUCT (no unique provider at the call's instantiation)
    /// nor FORWARD (every coarsely-covering caller entry σ-disagrees — the
    /// WI-821 gate) because a requirement element is genuinely UNCONSTRAINED
    /// at the call. Pre-WI-821 a sole covering wildcard entry silently
    /// forwarded a σ-disagreeing dictionary here (unsound); post-gate the
    /// refusal landed as a silent `dispatch_dict: None` that loaded clean and
    /// died at EVAL reading the unbound `__req_*`. This is the load-time face
    /// the loud-error principle demands. `eta` marks the function-value
    /// spelling (the WI-420 site) so the message names the usage.
    UnsatisfiableRequirement {
        span: Option<Span>,
        op: Symbol,
        callee_sort: Symbol,
        eta: bool,
        /// Boxed so the cold refusal payload doesn't widen every
        /// `Result<_, TypeError>` on the typer's hot faces.
        refusal: Box<RequirementRefusal>,
    },
    /// WI-583: a NON-Bool-returning operation used bare as a rule-body goal
    /// (goal position) — e.g. `:- length(?l)` where `length: List -> Int`. A
    /// Bool-returning op in goal position IS meaningful: it is the operation's
    /// relational view, gated to `eq(op(args), true)` by WI-580's
    /// [`KnowledgeBase::bare_bodied_bool_relation`] (true ⇒ success, false ⇒
    /// fail, unground ⇒ suspend). A NON-Bool op has no such reading — today it
    /// falls through to a SILENT failed relation lookup (the goal never
    /// resolves, no diagnostic), which the repo principle "prefer a loud error
    /// over a silent skip" rejects. This is the static, load-time face of that
    /// resolve-time routing. `return_sort` is the op's declared (non-Bool)
    /// return sort head, for the diagnostic.
    NonBoolOpInGoalPosition {
        span: Option<Span>,
        op_sym: Symbol,
        /// The op's declared return sort head — always a concrete non-`Bool`
        /// sort (a non-concrete return is not flagged; see `check_goal_atom_reading`).
        return_sort: Symbol,
    },
    /// WI-20260822-J38JE item 4: a NON-BOOLEAN CONSTANT written in a rule-body GOAL
    /// position — `:- 42`, `:- "hello"`, `:- 1.5`.
    ///
    /// The sibling of [`Self::NonBoolOpInGoalPosition`] for the population that names
    /// NO NAME, and the reason it needed a variant of its own: WI-1034's "rule-body
    /// goal names nothing" refusal tests a goal's FUNCTOR, and a constant has none, so
    /// a literal fell through every existing gate. MEASURED before this: `rule p(1) :-
    /// 42` loaded clean and answered nothing, indistinguishable from a deliberate
    /// `:- false`, and `rule p(1) :- not(42)` answered ONE — a negation succeeding over
    /// a goal with no meaning.
    ///
    /// `true` / `false` are NOT this error: a BOOLEAN constant in goal position is a
    /// search (§5.3, the decided half of this ticket) — `true` succeeds, `false` fails.
    /// That is the one constant reading, and this variant is its complement.
    ConstantInGoalPosition {
        span: Option<Span>,
        /// The constant as written, for the diagnostic — `42`, `"hello"`, `1.5`.
        literal: String,
    },
    /// WI-20260902-8K4RB: the subject of a bodyless EQUATION
    /// ([`crate::intern::SymbolKind::EquationFunctor`]) written in a rule-body GOAL
    /// position — `rule reader(1) :- tauX` beside `rule tauX <=> 7 @[simp]`.
    ///
    /// The third member of the "this term has no goal reading" family, beside
    /// [`Self::NonBoolOpInGoalPosition`] and [`Self::ConstantInGoalPosition`], and it
    /// is the same argument: an equation's clauses are indexed under the `eq`/`unify`
    /// CONNECTIVE, never under its subject (WI-898, spec §5.3), so the subject owns no
    /// clause and a goal naming it matches nothing — in any program, in any branch,
    /// under any binding. That is why it is refused where a goal that merely NAMES
    /// NOTHING in a tolerated branch is not.
    ///
    /// NOT [`Self::UnreducedEquationFunctor`], though both are equation citations, and
    /// the difference is the REPAIR. That one is a VALUE-position citation the rewriter
    /// left standing, so its three branches send the author to tag the equation `@[simp]`
    /// or to inspect the left-hand patterns. Here the equation may be tagged AND firing
    /// and the goal still cannot answer, because `@[simp]` rewrites a VALUE and a goal is
    /// MATCHED rather than rewritten — so those repairs would send an author to inspect
    /// a clause that is fine. (Not "a rule body is not a rewrite site": measured, it IS
    /// one in a value slot — `?v = tauX()` stores the already-inlined `eq(?_, 7)`.)
    /// MEASURED on the ticket's own fixture, which is `@[simp]`-tagged with one defining
    /// clause: that census reaches the third branch, "none of its 1 `@[simp]` clause(s)
    /// fired here".
    ///
    /// WHY IT WAS SILENT UNTIL NOW: the name RESOLVES, so WI-1034's "names nothing"
    /// refusal declines it ([`KnowledgeBase::symbol_declares_nothing`] is false — the
    /// mint stamped a kind), and the goal-reading pass below fell through its
    /// `op_record` gate because an equation subject declares no operation.
    EquationSubjectInGoalPosition {
        span: Option<Span>,
        /// The equation subject, for the diagnostic — rendered QUALIFIED, the spelling
        /// that locates the equations.
        functor: Symbol,
    },
    /// WI-650: an `PartialEq.eq`/`PartialEq.neq` (`=`/`neq`) call whose operand's sort declares
    /// its OWN `eq` override with NO backing — no runnable body and no non-fact
    /// rules (e.g. `Map` once the relational eq/binds/strip_is apparatus was
    /// dropped: its `Eq` provision is real at the spec-op/builtin layer, but the
    /// override op is a bodyless placeholder the WI-625 host bridge will fill).
    /// Such a compare type-checks (`PartialEq.eq` is a total builtin — no missing
    /// requirement) yet would SILENTLY misdecide at resolution: `sem_eq_dispatch`
    /// targets the empty override, exhausts the sub-search, and returns
    /// "not equal". `BuiltinResult` has no error channel (Success/Delay/Failure),
    /// so this is the loud TYPE-TIME face. `carrier_sort` is the operand's sort.
    EqOverrideUnbacked {
        span: Option<Span>,
        carrier_sort: Symbol,
    },
    /// Bottom or other post-elaboration expression seen by the surface
    /// typer — emitted only by `req_insertion`, never user-written.
    BottomExpr {
        span: Option<Span>,
    },
    /// WI-279: a value-receiver dot form `?x.member(args)` / `?x.member`
    /// whose `member` resolves to no operation declared on the receiver's
    /// least sort (the dot-dispatch default fallback found nothing).
    /// `receiver_sort` is the receiver's `min_sort`, or `None` when the
    /// receiver's type is unresolved (dispatch then undecidable). Reported
    /// at the dot's source span.
    DotDispatchNoMatch {
        span: Option<Span>,
        member: Symbol,
        receiver_sort: Option<Symbol>,
        /// WI-1119 — the receiver's rendered TYPE, when it has no sort head but IS a type
        /// PARAMETER declared in scope, together with the specs a `requires` clause
        /// constrains that parameter by. `None` for every other unresolved receiver.
        ///
        /// The split is not cosmetic and is not read off the rendering: an anonymous
        /// unification variable renders `??logical_var` and genuinely has nothing to name,
        /// while `?PT` is a parameter the author wrote and whose constraints are the whole
        /// content of the repair — either "no clause constrains it" or "these do, and none
        /// of them declares this member". Membership in [`TypingEnv::param_rigids`] is what
        /// tells the two apart, not the string.
        receiver_param: Option<ConstrainedParamReceiver>,
    },
    /// WI-369: a cross-scope projection (`s.field`) of a field whose owning
    /// entity is declared `internal`. The field name resolves, but the entity
    /// that declares it is hidden from the access scope (kernel-language.md
    /// §8.6), so reading the field would alias encapsulated state. `entity` is
    /// the owning (internal) constructor. Reported at the dot span.
    ForbiddenInternalField {
        span: Option<Span>,
        entity: Symbol,
        field: Symbol,
        /// WI-977 — the scope the projection was WRITTEN IN, so the `LoadError`
        /// conversion can name it. Carried rather than re-derived: it is the very
        /// scope [`hidden_field_owner`] asked the visibility question against, and
        /// the conversion runs far from the frame that knew it — which is why that
        /// conversion used to fill the slot with the literal `"another scope"`.
        /// A `ScopeId` and not the enclosing sort's `Symbol`, because top-level code
        /// has no enclosing sort and is written in the global scope, which no symbol
        /// from the frame names.
        from_scope: ScopeId,
    },
    /// WI-757 (the WI-722 macro contract's diagnostic channel): a `@[simp]` lowering
    /// whose macro-headed RHS was expanded here, and the MACRO rejected the
    /// occurrences it was handed — `where(λ c -> ite(true, true, false))`, whose
    /// condition is `Bool`-valued but not goal-expressible.
    ///
    /// Reported at the sub-expression the macro named, with the macro's own
    /// `expected`/`got` text. Its own variant, not [`Self::Other`]: the failing
    /// check ran in a MACRO, whose vocabulary is the source syntax it was handed,
    /// not the typer's expected-vs-inferred TYPES — flattening it through
    /// `TypeErrorContext` would have to name an operation parameter (`guarded_of.r`)
    /// the author never wrote, which is exactly the residual-template message this
    /// channel replaces.
    MacroRejected {
        span: Option<Span>,
        /// The macro that rejected — the `@[simp]` RHS head.
        macro_name: Symbol,
        /// The macro's own words, already rendered — see
        /// [`MacroRejection::detail`](crate::kb::simp_rewrite::MacroRejection).
        detail: String,
    },
    /// Aggregation node — collects multiple sibling failures
    /// (e.g. a list literal with two ill-typed elements).
    Multiple {
        errors: Vec<TypeError>,
    },
    /// WI-539 (proposal 050 "operation call" rule): a callee's VALUE precondition
    /// (`requires neq(b, 0)`) could not be proved from the local interpretation
    /// environment Γ at the call site — an undischarged obligation. `op` is the
    /// callee, `clause` the unproved precondition goal. Reported at the call span.
    UnsatisfiedPrecondition {
        span: Option<Span>,
        op: Symbol,
        clause: Value,
        /// WI-K88TN — which of the two ways the obligation went undischarged. They
        /// want OPPOSITE repairs, so they are two messages and not one message with a
        /// suffix (the WI-1049 shape the declared-effects error already uses).
        kind: PreconditionFailure,
    },
    /// Catchall for auxiliary typing-pass checks (effect declarations,
    /// match exhaustiveness, HO pattern fragment, rule var consistency).
    ///
    /// (See [`PreconditionFailure`] below for the `requires` split.)
    /// Promote to a dedicated variant when a consumer discriminates on it.
    Other {
        span: Option<Span>,
        context: TypeErrorContext,
        expected: String,
        actual: String,
        // WI-510: construction site — see `TypeMismatch::site`.
        site: &'static std::panic::Location<'static>,
    },
}

#[derive(Clone, Copy, Debug)]
pub enum RuleField {
    Head,
    Body,
    Whole,
}

impl RuleField {
    pub(super) fn name(self) -> &'static str {
        match self {
            RuleField::Head => "head",
            RuleField::Body => "body",
            RuleField::Whole => "rule",
        }
    }
}

#[derive(Clone, Debug)]
pub enum TypeErrorContext {
    EntityField {
        entity: Symbol,
        field: Symbol,
    },
    /// WI-385: an operation ARGUMENT whose inferred type does not conform to
    /// the declared parameter type. `op_name` is the called operation,
    /// `param` the declared parameter the argument was bound to.
    OperationArgument {
        op_name: Symbol,
        param: Symbol,
    },
    OperationReturn {
        op_name: Symbol,
        /// WI-20260820-5R2XT — the name the AUTHOR wrote at this call site, when
        /// `op_name` is a LOWERING of it and so names an operation no one wrote: the
        /// `join` behind a spliced `join_run`, the `where` behind a `where_run`. `None`
        /// when the callee IS what was written, which is every ordinary call.
        ///
        /// A required field, not an `Option` defaulted somewhere central, so that every
        /// construction site has to answer "does this site know what was written?" —
        /// most do not, because they have no call occurrence to ask.
        /// [`NodeOccurrence::surface_call_name`] is the one that does.
        surface: Option<Symbol>,
    },
    OperationEffects {
        op_name: Symbol,
    },
    OperationMatch {
        op_name: Symbol,
    },
    Rule {
        name: Symbol,
        field: RuleField,
    },
    LetBinding {
        var: Symbol,
    },
    /// WI-420: a bare operation reference rejected as a first-class function
    /// value (eta-expansion) because its enclosing sort carries a `requires`
    /// chain — the runtime `Value::OpRef` cannot carry the requirement
    /// dictionary yet, so it would crash at eval on an unbound `__req_*`.
    OperationAsFunctionValue {
        op_name: Symbol,
    },
    /// WI-374: a call whose arguments bind a SHARED type parameter
    /// inconsistently — the §3 parametricity tie, enforced:
    /// `append(intList, strList)` binds `List.T` to both elements.
    OperationTypeParams {
        op_name: Symbol,
    },
    /// WI-759: a dot projection `x.m` whose MEMBER is what is at fault, located by that
    /// member's name. Two populations, and the second is why this is not simply
    /// `DotDispatchNoMatch`:
    ///  - the member RESOLVES but its type does not — an abstract field type with no readable
    ///    interface, a variant-divergent field type. Naming it as MISSING would point the
    ///    user at the wrong thing, since it is right there.
    ///  - WI-20260818-7X7NK: the member is missing AND the surface says the author meant a
    ///    COLUMN — a `.( )` projection over a relation. `DotDispatchNoMatch` is true of it
    ///    and answers a question they did not ask; the projection's own message, which lists
    ///    the schema's columns, is the one that repairs the program.
    ///
    /// For a RENAME `r.(a: f)` the member is the SOURCE `f`, never the result key `a` — the
    /// key is the author's to invent, so it cannot be the thing that is wrong.
    DotProjection {
        member: Symbol,
    },
    /// WI-794: a pattern binder whose WRITTEN `: Type` annotation contradicts the type
    /// the context threads into that slot (a callback parameter, a tuple component, a
    /// destructured field). The binder is named because the annotation is per-BINDER —
    /// pointing at the whole lambda would leave the reader hunting which one is wrong.
    BinderAnnotation {
        binder: Symbol,
    },
    /// WI-20260824-Q0093 (`docs/design/055-implementation.md` §3, the `conditionals`
    /// and `matching` rows) — a position whose destination is `Bool`: an `if`
    /// CONDITION and a `match` arm GUARD.
    ///
    /// Its own variant rather than a [`TypeErrorContext::Rule`] with a borrowed
    /// [`RuleField`], because the two neighbouring slots of the same construct are
    /// already spoken for: the `if`/`match` branch JOIN renders as `if.rule` /
    /// `match.rule` ([`compute_branch_join_type`]), so reusing that context would give
    /// a condition mismatch and a branch mismatch one name and make the two
    /// indistinguishable in a diagnostic — the defect [`TypeMismatchOrigin`] exists to
    /// undo.
    BooleanPosition {
        /// `"if"` / `"match"` — the enclosing construct.
        construct: &'static str,
        /// `"condition"` / `"guard"` — which of its slots.
        slot: &'static str,
    },
    /// WI-20260826-7JDWY — an ELEMENT of a `[…]` / `{…}` literal, checked against the
    /// element type its position declares or its siblings join to.
    ///
    /// It carries the element's INDEX because a literal names its elements nothing, and
    /// the position is the only way to say which one is wrong. Reporting the whole list
    /// instead — `expected List[T = Int64], got List[T = String]` at the slot — says a
    /// list is wrong without saying which element made it so.
    CollectionElement {
        /// `"list"` / `"set"` — which literal surface.
        construct: &'static str,
        /// The element's 0-based position, rendered 1-based.
        index: usize,
        /// WI-20260829-WBXGX — where the type on the `expected` side CAME FROM, which
        /// changes what the message means and so is in the tag rather than left for a
        /// reader to guess.
        source: ElementTypeSource,
    },
}

/// WI-20260829-WBXGX — where the type a collection literal's element was judged against
/// came from.
///
/// A message reading `expected Int64, got String` means two different things depending on
/// the answer, and a reader repairing the program needs to know which: with a DECLARATION
/// the fix is usually the element, with a JOIN it may equally be any earlier element or the
/// declaration that is missing. [`TypeErrorContext::kind_tag`] renders them apart.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ElementTypeSource {
    /// The position's own declaration — a `List`/`Set`-headed expected type
    /// ([`declared_element_type`], WI-20260826-7JDWY).
    Declared,
    /// The JOIN of the literal's EARLIER elements; the position declares nothing
    /// (WI-20260829-WBXGX).
    Siblings,
}

impl TypeErrorContext {
    pub fn entity_name(&self, kb: &KnowledgeBase) -> String {
        match self {
            TypeErrorContext::EntityField { entity, .. } => kb.local_name_of(*entity).to_string(),
            TypeErrorContext::OperationArgument { op_name, .. } => {
                kb.local_name_of(*op_name).to_string()
            }
            // WI-20260820-5R2XT: a LOWERED call names BOTH — the `join` the author wrote
            // and the `join_run` the macro spliced. Not `join` alone: when the failure is
            // in the runner's own signature rather than in the operands, the internal
            // name is the only thing that leads a reader to it. `surface` is `None` for
            // every ordinary call, where the two would be the same name twice.
            TypeErrorContext::OperationReturn {
                op_name,
                surface: Some(surface),
            } => format!(
                "{} (expanded to {})",
                kb.local_name_of(*surface),
                kb.local_name_of(*op_name),
            ),
            TypeErrorContext::OperationReturn { op_name, .. }
            | TypeErrorContext::OperationEffects { op_name }
            | TypeErrorContext::OperationMatch { op_name } => {
                kb.local_name_of(*op_name).to_string()
            }
            TypeErrorContext::Rule { name, .. } => kb.local_name_of(*name).to_string(),
            TypeErrorContext::LetBinding { var } => kb.local_name_of(*var).to_string(),
            TypeErrorContext::OperationAsFunctionValue { op_name }
            | TypeErrorContext::OperationTypeParams { op_name } => {
                kb.local_name_of(*op_name).to_string()
            }
            // The receiver's identity is not carried — the member name is what locates the
            // projection for the reader, and it rides in `field_name` below.
            TypeErrorContext::DotProjection { .. } => "<dot projection>".to_string(),
            // The binder IS the subject here; there is no enclosing named entity to
            // report (a lambda is anonymous), so the name rides in `field_name` below.
            TypeErrorContext::BinderAnnotation { .. } => "<binder>".to_string(),
            TypeErrorContext::BooleanPosition { construct, .. } => (*construct).to_string(),
            TypeErrorContext::CollectionElement { construct, .. } => (*construct).to_string(),
            // (the `source` rides in `kind_tag`)
        }
    }

    /// WI-510: a stable, variant-identifying tag rendered alongside the
    /// flattened `entity.field` strings so two structurally different checks
    /// that happen to flatten to the same names (an `EntityField` field-arg
    /// check and an `OperationArgument` arg check both surfacing as
    /// `field_access.field`, WI-509) are distinguishable in the diagnostic.
    pub fn kind_tag(&self) -> &'static str {
        match self {
            TypeErrorContext::EntityField { .. } => "entity-field",
            TypeErrorContext::OperationArgument { .. } => "op-arg",
            TypeErrorContext::OperationReturn { .. } => "op-return",
            TypeErrorContext::OperationEffects { .. } => "op-effects",
            TypeErrorContext::OperationMatch { .. } => "op-match",
            TypeErrorContext::Rule { .. } => "rule",
            TypeErrorContext::LetBinding { .. } => "let-binding",
            TypeErrorContext::OperationAsFunctionValue { .. } => "op-as-fn-value",
            TypeErrorContext::OperationTypeParams { .. } => "op-type-params",
            TypeErrorContext::DotProjection { .. } => "dot-projection",
            TypeErrorContext::BinderAnnotation { .. } => "binder-annotation",
            TypeErrorContext::BooleanPosition { .. } => "boolean-position",
            TypeErrorContext::CollectionElement {
                source: ElementTypeSource::Declared,
                ..
            } => "collection-element",
            TypeErrorContext::CollectionElement {
                source: ElementTypeSource::Siblings,
                ..
            } => "collection-element-join",
        }
    }

    pub fn field_name(&self, kb: &KnowledgeBase) -> String {
        match self {
            TypeErrorContext::EntityField { field, .. } => kb.local_name_of(*field).to_string(),
            TypeErrorContext::OperationArgument { param, .. } => {
                kb.local_name_of(*param).to_string()
            }
            TypeErrorContext::OperationReturn { .. } => "return".to_string(),
            TypeErrorContext::OperationEffects { .. } => "effects".to_string(),
            TypeErrorContext::OperationMatch { .. } => "match".to_string(),
            TypeErrorContext::Rule { field, .. } => field.name().to_string(),
            TypeErrorContext::LetBinding { .. } => "annotation".to_string(),
            TypeErrorContext::OperationAsFunctionValue { .. } => "function-value".to_string(),
            TypeErrorContext::OperationTypeParams { .. } => "type_args".to_string(),
            TypeErrorContext::DotProjection { member } => kb.local_name_of(*member).to_string(),
            TypeErrorContext::BinderAnnotation { binder } => kb.local_name_of(*binder).to_string(),
            TypeErrorContext::BooleanPosition { slot, .. } => (*slot).to_string(),
            // 1-BASED, because it is read by whoever wrote the literal and they counted
            // from one. The 0-based `index` is kept in the variant so the value is the
            // element's position in `pos_args` and needs no reader to undo the display.
            TypeErrorContext::CollectionElement { index, .. } => format!("element {}", index + 1),
        }
    }
}

/// WI-K88TN — WHY a `requires` goal went undischarged, which decides what the author
/// is told to do about it.
///
/// The two are told apart by ONE question — does the judged clause still carry a
/// `Var::Rigid`? — and that is the same question [`value_carries_undecided_var`] asks to
/// let the clause through the gate at all, read at the other end.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PreconditionFailure {
    /// The call decided every variable in the clause and the resulting goal is not
    /// provable from Γ + KB. The repair is at THIS call: establish the fact.
    AtCallSite,
    /// The clause is universally quantified over a type variable the ENCLOSING
    /// operation's signature binds — `relay(t: Text[L = ?m]) = send(t)` raising
    /// `∀m. flows_to(m, Public)` — and holds for no instantiation. Nothing at this call
    /// can establish it, because the caller of the ENCLOSING operation is what picks
    /// `?m`; the repair is to declare the clause on that operation, which propagates it
    /// to those callers (and is then discharged here from Γ — [`op_requires_gamma`]).
    /// `enclosing` is the operation that owes the declaration — NOT the callee the
    /// obligation came from, which is what the error is otherwise attributed to.
    UndeclaredInWrapper { enclosing: Symbol },
    /// The clause carries a rigid variable NO signature in scope binds, so there is no
    /// declaration that could name it and no call that could instantiate it.
    ///
    /// A `Var::Rigid` HAS TWO PRODUCERS WITH OPPOSITE QUANTIFIERS, and telling them
    /// apart is what this third case is for. `rigidify_op_type_params` /
    /// `rigidify_unwritten_sort_params` skolemize a signature's own parameters — ∀,
    /// declarable, the case above. `open_existential_return` mints a FRESH ρ per use as
    /// an ∃ WITNESS for a variable in a callee's return (`pick() -> Text[L = ?k]`), and
    /// that one is bound by nothing: `f() = send(pick())` cannot be repaired by writing
    /// `requires flows_to(?k, Public)` on `f`, because `?k` there is a new flex variable
    /// of `f`'s own and never meets ρ. MEASURED — the prescribed repair returned the
    /// BYTE-IDENTICAL error, which is a loop, not a diagnostic.
    ///
    /// The refusal itself is right either way (nothing may be assumed about an opaque
    /// witness, which is what makes the opening sound); only the repair differs, so this
    /// case says what is actually wrong instead of naming a line that will not help.
    /// Membership in [`TypingEnv::param_rigids`] is the discriminator, and
    /// [`constrained_param_receiver_type`] already states why that list is the precise
    /// question: it holds "exactly the parameters in scope", and such a variable "IS a
    /// parameter a `requires` clause can name and a call can instantiate".
    UndischargeableWitness,
}

impl TypeError {
    /// WI-510: capture the caller's source location. `#[track_caller]` makes
    /// `Location::caller()` return the location of *this* call — i.e. the
    /// `TypeError::TypeMismatch { site: TypeError::here(), … }` construction
    /// site — so every lossy `TypeError` records where it was built. Zero
    /// runtime cost (a `&'static` pointer).
    #[track_caller]
    pub fn here() -> &'static std::panic::Location<'static> {
        std::panic::Location::caller()
    }

    pub fn format(&self, kb: &KnowledgeBase) -> String {
        match self {
            TypeError::TypeMismatch {
                expected,
                actual,
                denoted,
                ..
            } => {
                // WI-795: the SAME pair renderer `to_load_error` uses. This is a
                // second, currently-unreached rendering of the same two values —
                // rendering them independently here would silently reintroduce the
                // `expected X, got X` arity blindness on whichever path reaches it
                // first. WI-20260824-Q0093: and the same denotation suffix, for the
                // same reason — two renderings of one error may not say different
                // things about it.
                let (expected, actual) = render_mismatch_pair(kb, expected, actual);
                let actual = match denoted {
                    Some(d) => format!("{actual} ({d})"),
                    None => actual,
                };
                format!("type mismatch: expected {expected}, got {actual}")
            }
            TypeError::NoParentSort { name } => {
                format!("entity has no parent sort: {}", kb.local_name_of(*name))
            }
            TypeError::UnresolvedName { name, .. } => {
                format!("unresolved name: {}", kb.local_name_of(*name))
            }
            TypeError::NoConstructor { name, .. } => {
                format!("no constructor: {}", kb.local_name_of(*name))
            }
            TypeError::UnknownApplyFunctor { name, .. } => {
                format!("unknown apply functor: {}", kb.local_name_of(*name))
            }
            TypeError::UndefinedDataFunctor { name, .. } => {
                crate::kb::load::undefined_rule_body_term_message(kb.qualified_name_of(*name))
            }
            TypeError::BareMemberCall {
                member,
                owning_sorts,
                dot_dispatchable,
                ..
            } => {
                let sort_names: Vec<String> = owning_sorts
                    .iter()
                    .map(|s| kb.local_name_of(*s).to_string())
                    .collect();
                bare_member_call_message(kb.local_name_of(*member), &sort_names, *dot_dispatchable)
            }
            TypeError::UnreducedEquationFunctor {
                functor, census, ..
            } => unreduced_equation_functor_message(kb.qualified_name_of(*functor), *census),
            TypeError::DispatchNoMatch { op, unmet, .. } => {
                format!(
                    "dispatch failed: no impl of {} for the per-call bindings{}",
                    kb.qualified_name_of(*op),
                    render_unmet(unmet),
                )
            }
            TypeError::DispatchAmbiguous { op, tie, .. } => {
                let (candidates, repair) = render_instance_tie(kb, tie);
                unselected_instance_message(
                    kb.qualified_name_of(*op),
                    kb.qualified_name_of(tie.spec),
                    &candidates,
                    &repair,
                )
            }
            // WI-1012: rendered by the channel's own owner, shared with the eval
            // `Display` and both `LoadError` renderings (the `MacroRejected` /
            // `unselected_instance_message` discipline).
            TypeError::AmbiguousSpecOpDispatch {
                op,
                carrier,
                candidates,
                repair,
                ..
            } => ambiguous_spec_op_dispatch_message(
                kb.qualified_name_of(*op),
                kb.qualified_name_of(*carrier),
                candidates,
                *repair,
            ),
            TypeError::NoSuchTypeParam { op, name, .. } => {
                format!(
                    "{} has no type parameter named '{}'",
                    kb.qualified_name_of(*op),
                    kb.local_name_of(*name),
                )
            }
            TypeError::ExcessCallTypeArgs {
                op, given, free, ..
            } => {
                format!(
                    "{} is over-applied at its type-argument bracket: {given} positional \
                     type argument(s) but {free} type parameter(s) left to bind",
                    kb.qualified_name_of(*op),
                )
            }
            TypeError::DuplicateCallTypeArg { op, name, .. } => {
                format!(
                    "{} binds the type parameter '{}' more than once in one call-site \
                     bracket",
                    kb.qualified_name_of(*op),
                    kb.local_name_of(*name),
                )
            }
            TypeError::ReceiverBracketConflict {
                op,
                param,
                receiver,
                callee,
                ..
            } => {
                format!(
                    "the receiver bracket and the callee bracket on the call to {} bind \
                     '{}' differently: '{}' at the receiver, '{}' at the callee",
                    kb.qualified_name_of(*op),
                    kb.local_name_of(*param),
                    type_display_name_value(kb, receiver),
                    type_display_name_value(kb, callee),
                )
            }
            TypeError::TypeArgsOnNonOperation { callee, .. } => {
                format!(
                    "'{}' is not an operation, so it has no type-parameter list a \
                     call-site `[…]` bracket could bind",
                    short_name_of(kb.qualified_name_of(*callee)),
                )
            }
            TypeError::AmbiguousRequirementKey {
                op, name, slots, ..
            } => {
                format!(
                    "'{}' names more than one requirement slot of {} ({}) — a spec's \
                     SHORT NAME selects a provider only when it picks out ONE anonymous \
                     slot; name the slot you mean (`requires <name>: {0}[…]`) and bind \
                     that name instead",
                    kb.local_name_of(*name),
                    kb.qualified_name_of(*op),
                    slots.join(", "),
                )
            }
            TypeError::SelectionValueNotASort { op, spec, .. } => {
                let spec_qn = kb.qualified_name_of(*spec);
                format!(
                    "the `[{} = …]` binding on {} selects a provider, so its value must \
                     name a WITNESS SORT — a sort declaring `provides {2}[…]`",
                    short_name_of(spec_qn),
                    kb.qualified_name_of(*op),
                    spec_qn,
                )
            }
            TypeError::SlotSelectionUnindexable {
                op, owner, binder, ..
            } => {
                format!(
                    "the `[{} = …]` binding on `{}` at {} names a requirement slot whose \
                     position in that sort's dictionary chain could not be established, \
                     so it cannot be honoured",
                    kb.local_name_of(*binder),
                    kb.qualified_name_of(*owner),
                    kb.qualified_name_of(*op),
                )
            }
            TypeError::ErasedRequirementSlot {
                op,
                binder,
                spec,
                provider,
                reason,
                ..
            } => {
                let would_take = match provider {
                    Some(p) => format!(
                        "; a construction here would answer for {}",
                        kb.qualified_name_of(*p)
                    ),
                    None => String::new(),
                };
                // WI-20260921-EE0EP — the common case is SUPPLIED now (a top-level
                // unwritten slot on a parameter takes that argument's own dictionary), so
                // these two arms are the residues, and each names the repair that exists.
                match reason {
                    ErasedSlotReason::AmbiguousWithFrame => format!(
                        "the call to {0} reads the named requirement slot `{1}: {2}` off a \
                         parameter whose type omits it — which would be supplied from \
                         that argument's own type, except that something else in this \
                         frame already answers `{2}` here (an anonymous `requires` of the \
                         same spec, or a second parameter of the same carrier){3}. A body \
                         reads a GOAL and not a parameter, so there is no way to say which \
                         of them is meant, and answering from the wrong one is a silent \
                         wrong order. Name the slot and write that name in the parameter's \
                         type (`requires {1}: {2}[…]`, `… {1} = {1} …`) so the read is \
                         unambiguous",
                        kb.qualified_name_of(*op),
                        kb.local_name_of(*binder),
                        kb.qualified_name_of(*spec),
                        would_take,
                    ),
                    ErasedSlotReason::NoReceiver => format!(
                        "the call to {0} leaves its named requirement slot `{1}: {2}` \
                         universally quantified, and NOTHING HERE CAN SUPPLY IT: the \
                         argument's type names no provider either, so there is no \
                         dictionary to forward and any construction would answer for a \
                         value that already chose{4}. A bracket at THIS call does not \
                         reach it — `{3}[{1} = …]` and `{0}[{1} = …]` pin the PARAMETER's \
                         type while the argument's own stays a skolem, which unifies with \
                         nothing but itself. Write `{1}` where the value is PRODUCED: in \
                         the return type of the operation that builds it \
                         (`-> {3}[…, {1} = <witness>]`), or, for an element reached by a \
                         pattern match, in the element type itself",
                        kb.qualified_name_of(*op),
                        kb.local_name_of(*binder),
                        kb.qualified_name_of(*spec),
                        short_name_of(kb.qualified_name_of(*op)),
                        would_take,
                    ),
                }
            }
            TypeError::WitnessDoesNotProvide {
                op,
                witness,
                spec,
                at_bindings,
                ..
            } => {
                let spec_qn = kb.qualified_name_of(*spec);
                if *at_bindings {
                    format!(
                        "{} provides {}, but not at the bindings this call to {} needs \
                         — the selected witness must provide the spec AS INSTANTIATED \
                         here, not merely somewhere",
                        kb.qualified_name_of(*witness),
                        spec_qn,
                        kb.qualified_name_of(*op),
                    )
                } else {
                    // CHANNEL-NEUTRAL, and that is a correction (WI-20260911-6B67S).
                    // This read "a call-site `[Spec = W]` on {op}", which was true while
                    // the only producer was a written bracket. It is not: a selection is
                    // equally made by a TYPE that carries the slot — an argument's
                    // declared `s: SortedSet[T = Int64, O = NotOrd]`, with no bracket
                    // anywhere in the author's file — and once
                    // [`selections_from_slot_bindings`] runs check 1 that channel reaches
                    // this arm too. Telling that author to fix a bracket on a stdlib
                    // operation names syntax they never wrote, which is the same species
                    // of false diagnostic this ticket exists to remove. `Spec = W` is
                    // the SELECTION, which both channels really do make; the repair
                    // clause is what stays actionable and is unchanged.
                    format!(
                        "{} does not provide {} — a selection of `{} = {}` at {} must \
                         name a sort that declares `provides {1}[…]`",
                        kb.qualified_name_of(*witness),
                        spec_qn,
                        short_name_of(spec_qn),
                        short_name_of(kb.qualified_name_of(*witness)),
                        kb.qualified_name_of(*op),
                    )
                }
            }
            TypeError::ValueDirectedSelection {
                op, witness, spec, ..
            } => {
                // CHANNEL-NEUTRAL, for the reason the arm above gives (WI-20260911-TX0G6).
                // This read "an explicit `[Spec = W]`", which names a bracket neither
                // spelling of a NAMED slot writes: the callee writes `[O = W]` and the
                // receiver writes `SortedSet[…, O = W]`, and both now reach this arm.
                //
                // AND IT STATES THE RULE, NOT A CLAIM ABOUT THIS CALL. It used to say the
                // dispatch "is already directed by the value" and the selection "cannot
                // change it". That is true where the provider's values are the arguments,
                // and MEASURED false where they are not: `[WeakOrd = ConcOrd]` on two
                // `String`s answers ConcOrd's order when admitted. The rule is kept as a
                // property of the named sort (see [`validate_instance_selection`]), so the
                // message gives its reason conditionally.
                format!(
                    "{} is a CONCRETE provider of {} (a sort with constructors), and a call \
                     may not select one: its values carry their own sort, so where they are \
                     the arguments of {} they already direct the dispatch, and an explicit \
                     selection of `{} = {}` is refused rather than preferred",
                    kb.qualified_name_of(*witness),
                    kb.qualified_name_of(*spec),
                    kb.qualified_name_of(*op),
                    short_name_of(kb.qualified_name_of(*spec)),
                    short_name_of(kb.qualified_name_of(*witness)),
                )
            }
            TypeError::ConflictingSelection {
                op,
                spec,
                first,
                second,
                ..
            } => {
                format!(
                    "two providers are selected for {} at the call to {}: {} and {} — \
                     one spec, one witness per call",
                    kb.qualified_name_of(*spec),
                    kb.qualified_name_of(*op),
                    kb.qualified_name_of(*first),
                    kb.qualified_name_of(*second),
                )
            }
            TypeError::InvalidTypeArgument { sort, problem, .. } => problem.describe(kb, *sort),
            TypeError::UnconstrainedTypeParam { op, type_param, .. } => {
                let op_name = kb.qualified_name_of(*op);
                format!(
                    "type parameter '{0}' of {1} is unconstrained — use `{2}[{0} = …](…)`",
                    kb.local_name_of(*type_param),
                    op_name,
                    short_name_of(op_name),
                )
            }
            TypeError::UnconstrainedCitationParam {
                relation,
                sort,
                type_param,
                ..
            } => citation_param_message(kb, *relation, *sort, *type_param),
            TypeError::MissingRequiresForSpecOp {
                spec_op_sym,
                spec_sort_sym,
                abstract_params,
                ..
            } => {
                let op_qn = kb.qualified_name_of(*spec_op_sym);
                let spec_qn = kb.qualified_name_of(*spec_sort_sym);
                let spec_short = short_name_of(spec_qn);
                let params_list: Vec<String> = abstract_params
                    .iter()
                    .map(|p| format!("{0} = …", kb.local_name_of(*p)))
                    .collect();
                format!(
                    "spec op `{}` called at abstract type — add `requires {}[{}]` to the enclosing sort, or specialize to a concrete carrier",
                    op_qn,
                    spec_short,
                    params_list.join(", "),
                )
            }
            TypeError::ProvisionConditionOutOfScope {
                op,
                spec_op_sym,
                spec_sort_sym,
                provisions,
                ..
            } => {
                let spec_short = short_name_of(kb.qualified_name_of(*spec_sort_sym)).to_string();
                let blocks: Vec<String> = provisions
                    .iter()
                    .map(|p| {
                        format!(
                            "`provides {}[…] :- … where … end`",
                            short_name_of(kb.qualified_name_of(*p))
                        )
                    })
                    .collect();
                format!(
                    "`{}` calls `{}`, whose `{}` evidence is a condition of {} — and a \
                     provision's conditions are in scope only for the operations written in \
                     its `where` block (proposal 066). Move `{}` into that block, or give it \
                     its own `requires {}[…]`",
                    kb.qualified_name_of(*op),
                    kb.qualified_name_of(*spec_op_sym),
                    spec_short,
                    blocks.join(" or "),
                    short_name_of(kb.qualified_name_of(*op)),
                    spec_short,
                )
            }
            TypeError::UnfillableOperationRequirement {
                callee_op,
                spec_sort_sym,
                carrier_sym,
                ..
            } => {
                let spec_qn = kb.qualified_name_of(*spec_sort_sym);
                format!(
                    "`{}` requires `{}` at carrier `{}`, and this clause can neither \
                     supply it nor declare it — `{}` provides no `{}`. Add a `provides \
                     {}[…]` for `{}` (or a witness sort that provides it), or write \
                     `requires({}[…])` in this clause to take the obligation on",
                    kb.qualified_name_of(*callee_op),
                    spec_qn,
                    kb.qualified_name_of(*carrier_sym),
                    kb.qualified_name_of(*carrier_sym),
                    spec_qn,
                    short_name_of(spec_qn),
                    kb.qualified_name_of(*carrier_sym),
                    short_name_of(spec_qn),
                )
            }
            TypeError::NoProvisionAtCarriers {
                callee_op,
                spec_sort_sym,
                bindings,
                ..
            } => {
                let spec_qn = kb.qualified_name_of(*spec_sort_sym);
                let at = carrier_bindings_text(kb, bindings);
                format!(
                    "`{}` requires `{}` at `{at}`, and no provision binds that — this clause \
                     can neither supply it nor declare it. Add a `provides {}[{at}]` (on a \
                     sort, or a witness sort), or write `requires({}[…])` in this clause to \
                     take the obligation on",
                    kb.qualified_name_of(*callee_op),
                    spec_qn,
                    short_name_of(spec_qn),
                    short_name_of(spec_qn),
                )
            }
            // WI-20260919-N31XX — 065's message verbatim: the parameter, the read, and
            // the clause to add, on the operation that must carry it.
            TypeError::TypeValueReadUnbacked { param, op, .. } => {
                let p = short_name_of(kb.local_name_of(*param));
                format!(
                    "`{p}` is read as a VALUE here, and nothing in scope requires \
                     `TypeValue[T = {p}]` — so the signature of `{}` promises nothing \
                     about whether it inspects `{p}` (proposal 065). Add `requires \
                     anthill.reflect.TypeValue[T = {p}]` to `{}`, or use `{p}` only in \
                     type position",
                    kb.qualified_name_of(*op),
                    short_name_of(kb.qualified_name_of(*op)),
                )
            }
            TypeError::UnsatisfiableRequirement {
                op,
                callee_sort,
                eta,
                refusal,
                ..
            } => refusal.render(kb, *op, *callee_sort, *eta),
            TypeError::NonBoolOpInGoalPosition {
                op_sym,
                return_sort,
                ..
            } => {
                let op_qn = kb.qualified_name_of(*op_sym);
                format!(
                    "operation `{}` returns `{}`, not `Bool` — it cannot be used as a rule-body condition (goal position). Only a Bool-returning operation is gated there as `eq({}(…), true)`; a non-Bool operation has no relational reading",
                    op_qn,
                    kb.qualified_name_of(*return_sort),
                    short_name_of(op_qn),
                )
            }
            TypeError::ConstantInGoalPosition { literal, .. } => {
                crate::kb::load::constant_in_goal_position_message(literal)
            }
            TypeError::EquationSubjectInGoalPosition { functor, .. } => {
                crate::kb::load::equation_subject_in_goal_position_message(
                    kb.qualified_name_of(*functor),
                )
            }
            TypeError::EqOverrideUnbacked { carrier_sort, .. } => {
                let carrier_qn = kb.qualified_name_of(*carrier_sort);
                format!(
                    "Eq[{}] declared but unimplemented (pending WI-625 host bridge): comparing two `{}` values via `=`/`eq`/`neq` would silently misdecide — the carrier declares an `eq` override with no rules or runnable body",
                    carrier_qn,
                    short_name_of(carrier_qn),
                )
            }
            TypeError::BottomExpr { .. } => {
                "bottom or post-elaboration expression in surface IR".to_string()
            }
            TypeError::DotDispatchNoMatch {
                member,
                receiver_sort,
                receiver_param,
                ..
            } => {
                let m = kb.local_name_of(*member);
                match (receiver_sort, receiver_param) {
                    (Some(s), _) => format!(
                        "no member '{}' on {}: dot dispatch found no operation '{}' declared on the receiver's sort",
                        m, kb.qualified_name_of(*s), m,
                    ),
                    // WI-1119 — a type PARAMETER receiver: name it, and say what does or
                    // does not constrain it. `<unresolved receiver>` was true and useless
                    // here — the parameter is written right there in the signature.
                    (None, Some(p)) => format!(
                        "no member '{}' on `{}`: {}",
                        m,
                        p.param,
                        constrained_param_repair(kb, &p.specs, m),
                    ),
                    (None, None) => format!(
                        "cannot dispatch `.{}`: the receiver's type is unresolved",
                        m,
                    ),
                }
            }
            TypeError::AmbiguousConstrainedParamMember {
                member,
                receiver,
                specs,
                ..
            } => {
                ambiguous_constrained_param_message(kb, kb.local_name_of(*member), receiver, specs)
            }
            TypeError::ForbiddenInternalField {
                entity,
                field,
                from_scope,
                ..
            } => {
                // WI-977 — names the scope, as the `LoadError` rendering of this same
                // diagnostic does. "another scope" was honest prose here (this is a
                // sentence, not a name slot) but it told the author nothing they did
                // not already know, and the variant now carries the scope.
                format!(
                    "'{}' is an internal field of {} and cannot be projected from scope '{}'",
                    kb.local_name_of(*field),
                    kb.qualified_name_of(*entity),
                    kb.scope_display_name(*from_scope),
                )
            }
            // WI-757: rendered by the channel's own owner (`eval::macro_rejection_message`),
            // shared with the eval `Display` and both `LoadError` renderings.
            TypeError::MacroRejected {
                macro_name, detail, ..
            } => crate::eval::macro_rejection_message(
                Some(kb.qualified_name_of(*macro_name)),
                detail,
            ),
            TypeError::Multiple { errors } => {
                let parts: Vec<String> = errors.iter().map(|e| e.format(kb)).collect();
                parts.join("; ")
            }
            TypeError::UnsatisfiedPrecondition {
                op,
                clause,
                kind: PreconditionFailure::AtCallSite,
                ..
            } => {
                format!(
                    "unsatisfied precondition `{}` for call to `{}`: the `requires` goal could not be proved at the call site (establish it with an enclosing `if`/`match` guard, a prior `ensures`, or a KB fact)",
                    format_precondition_clause(kb, clause),
                    kb.qualified_name_of(*op),
                )
            }
            TypeError::UnsatisfiedPrecondition {
                op,
                clause,
                kind: PreconditionFailure::UndeclaredInWrapper { enclosing },
                ..
            } => {
                // NOT the call-site advice: none of a guard / a prior `ensures` / a KB
                // fact can establish a goal universally quantified over a variable the
                // enclosing operation's own CALLER picks. The one repair is to declare
                // it, so the message is the line to write and the operation to write it
                // on — both named, since the obligation came from a THIRD operation.
                let goal = format_precondition_clause(kb, clause);
                format!(
                    "undischarged precondition `{goal}` from the call to `{}`: it is universally quantified over a type variable `{}`'s signature binds, so it holds for every instantiation or for none — declare it on `{}` (`requires {goal}`) to pass the obligation to its callers",
                    kb.qualified_name_of(*op),
                    kb.qualified_name_of(*enclosing),
                    kb.qualified_name_of(*enclosing),
                )
            }
            TypeError::UnsatisfiedPrecondition {
                op,
                clause,
                kind: PreconditionFailure::UndischargeableWitness,
                ..
            } => {
                // NEITHER repair applies, and saying so is the whole point of this case
                // (WI-K88TN): the variable is an opaque witness opened from a callee's
                // return, so no `requires` can name it and no call can instantiate it.
                // Prescribing a declaration here returned the byte-identical error.
                format!(
                    "undischargeable precondition `{}` from the call to `{}`: it names a type variable no signature in scope binds — an opaque witness from a callee's return type — so no `requires` clause can name it and no call can decide it. Give the value a type whose parameter is known here, or take it as a parameter so the caller's own decides it",
                    format_precondition_clause(kb, clause),
                    kb.qualified_name_of(*op),
                )
            }
            TypeError::Other {
                expected, actual, ..
            } => {
                format!("expected {}, got {}", expected, actual)
            }
        }
    }

    pub fn span(&self, _kb: &KnowledgeBase) -> Option<Span> {
        match self {
            TypeError::TypeMismatch { span, .. }
            | TypeError::UnresolvedName { span, .. }
            | TypeError::NoConstructor { span, .. }
            | TypeError::UnknownApplyFunctor { span, .. }
            | TypeError::UndefinedDataFunctor { span, .. }
            | TypeError::BareMemberCall { span, .. }
            | TypeError::UnreducedEquationFunctor { span, .. }
            | TypeError::DispatchNoMatch { span, .. }
            | TypeError::DispatchAmbiguous { span, .. }
            | TypeError::AmbiguousSpecOpDispatch { span, .. }
            | TypeError::UnfillableOperationRequirement { span, .. }
            | TypeError::NoProvisionAtCarriers { span, .. }
            | TypeError::TypeValueReadUnbacked { span, .. }
            | TypeError::AmbiguousConstrainedParamMember { span, .. }
            | TypeError::NoSuchTypeParam { span, .. }
            | TypeError::ExcessCallTypeArgs { span, .. }
            | TypeError::DuplicateCallTypeArg { span, .. }
            | TypeError::ReceiverBracketConflict { span, .. }
            | TypeError::TypeArgsOnNonOperation { span, .. }
            | TypeError::AmbiguousRequirementKey { span, .. }
            | TypeError::SelectionValueNotASort { span, .. }
            | TypeError::SlotSelectionUnindexable { span, .. }
            | TypeError::ErasedRequirementSlot { span, .. }
            | TypeError::WitnessDoesNotProvide { span, .. }
            | TypeError::ValueDirectedSelection { span, .. }
            | TypeError::ConflictingSelection { span, .. }
            | TypeError::InvalidTypeArgument { span, .. }
            | TypeError::UnconstrainedTypeParam { span, .. }
            | TypeError::UnconstrainedCitationParam { span, .. }
            | TypeError::MissingRequiresForSpecOp { span, .. }
            | TypeError::ProvisionConditionOutOfScope { span, .. }
            | TypeError::UnsatisfiableRequirement { span, .. }
            | TypeError::NonBoolOpInGoalPosition { span, .. }
            | TypeError::ConstantInGoalPosition { span, .. }
            | TypeError::EquationSubjectInGoalPosition { span, .. }
            | TypeError::EqOverrideUnbacked { span, .. }
            | TypeError::DotDispatchNoMatch { span, .. }
            | TypeError::ForbiddenInternalField { span, .. }
            | TypeError::UnsatisfiedPrecondition { span, .. }
            | TypeError::MacroRejected { span, .. }
            | TypeError::BottomExpr { span } => *span,
            TypeError::Other { span, .. } => *span,
            TypeError::NoParentSort { .. } => None,
            TypeError::Multiple { errors } => errors.iter().find_map(|e| e.span(_kb)),
        }
    }

    /// Flatten a `Multiple` into its leaf errors; non-`Multiple` becomes
    /// a single-element vec. Lets the operation-body driver push each
    /// sibling failure as its own load error.
    pub fn flatten(self) -> Vec<TypeError> {
        match self {
            TypeError::Multiple { errors } => {
                let mut out = Vec::with_capacity(errors.len());
                for e in errors {
                    out.extend(e.flatten());
                }
                out
            }
            other => vec![other],
        }
    }

    /// Lossy conversion to LoadError for legacy callers (load.rs, CLI).
    /// Resolves spans, formats type terms via `type_display_name`.
    pub fn to_load_error(&self, kb: &KnowledgeBase) -> crate::kb::load::LoadError {
        use crate::kb::load::{LoadError, TypeMismatchOrigin};
        match self {
            TypeError::TypeMismatch {
                context,
                expected,
                actual,
                denoted,
                site,
                ..
            } => {
                // WI-795: rendered as a PAIR, not as two independent sides — an
                // arity-only arrow mismatch is invisible to the per-side
                // renderer. See [`render_mismatch_pair`].
                let (expected_type, actual_type) = render_mismatch_pair(kb, expected, actual);
                // WI-20260824-Q0093: …and the DENOTATION after the type, when the rejected
                // expression was a classified type value — `got Type (Cell[V = Int64])`
                // (design 055 §8). Appended rather than folded into the pair renderer:
                // that renderer answers about the two TYPES, and this is the third thing.
                let actual_type = match denoted {
                    Some(d) => format!("{actual_type} ({d})"),
                    None => actual_type,
                };
                LoadError::TypeMismatch {
                    origin: Some(TypeMismatchOrigin {
                        error_kind: "TypeMismatch",
                        context_kind: context.kind_tag(),
                        site: *site,
                    }),
                    entity_name: context.entity_name(kb),
                    field_name: context.field_name(kb),
                    expected_type,
                    actual_type,
                    span: self.span(kb),
                }
            }
            TypeError::NoParentSort { name } => LoadError::TypeMismatch {
                origin: None,
                entity_name: kb.local_name_of(*name).to_string(),
                field_name: "parent_sort".to_string(),
                expected_type: "parent sort".to_string(),
                actual_type: "none".to_string(),
                span: None,
            },
            TypeError::UnresolvedName { name, .. } => LoadError::TypeMismatch {
                origin: None,
                entity_name: kb.local_name_of(*name).to_string(),
                field_name: "name".to_string(),
                expected_type: "resolved name".to_string(),
                actual_type: "unresolved".to_string(),
                span: self.span(kb),
            },
            TypeError::NoConstructor { name, .. } => LoadError::TypeMismatch {
                origin: None,
                entity_name: kb.local_name_of(*name).to_string(),
                field_name: "constructor".to_string(),
                expected_type: "known constructor".to_string(),
                actual_type: "unknown".to_string(),
                span: self.span(kb),
            },
            // WI-20260901-92VA4 — SAYS WHAT THE RULE BODY SAYS. The phrase "unknown
            // functor" is kept verbatim and in place: ~15 assertions match on it, and
            // `wi557::genuinely_unknown_bare_functor_stays_terse` uses it to separate this
            // from WI-565's `BareMemberCall` member hint. What is added around it is the
            // census and the repair, from the same two functions
            // `undefined_rule_body_goal_message` reads — so an author who writes
            // `field_access(q, q)` in an operation body and one who writes it as a
            // rule-body goal are told the same thing about the same name. Before 92VA4 the
            // operation body did not reach this at all for that spelling: the accessor
            // ladder rescued it (`kb/load.rs`, the `is_minted` gate).
            //
            // NOT MERGED INTO `UndefinedRuleBodyGoal`. That variant's sentence states a
            // consequence this position does not have ("the rule it is written in can
            // never fire"), and this one is a `TypeMismatch` carrying the `.apply` field
            // slot its readers key on.
            TypeError::UnknownApplyFunctor { name, .. } => LoadError::TypeMismatch {
                origin: None,
                entity_name: kb.local_name_of(*name).to_string(),
                field_name: "apply".to_string(),
                expected_type: "known operation or arrow-typed variable".to_string(),
                actual_type: if kb.symbol_declares_nothing(*name) {
                    format!(
                        "unknown functor — {}. {}",
                        crate::kb::load::no_declaration_census(),
                        crate::kb::load::undefined_name_repair(kb.local_name_of(*name)),
                    )
                } else {
                    "unknown functor".to_string()
                },
                span: self.span(kb),
            },
            TypeError::UndefinedDataFunctor { name, .. } => LoadError::UndefinedRuleBodyTerm {
                functor: kb.qualified_name_of(*name).to_string(),
                span: self
                    .span(kb)
                    .unwrap_or_else(|| crate::span::Span::new(0, 0)),
            },
            TypeError::BareMemberCall {
                member,
                owning_sorts,
                dot_dispatchable,
                ..
            } => LoadError::BareMemberCall {
                span: self.span(kb),
                member: kb.local_name_of(*member).to_string(),
                owning_sorts: owning_sorts
                    .iter()
                    .map(|s| kb.local_name_of(*s).to_string())
                    .collect(),
                dot_dispatchable: *dot_dispatchable,
            },
            TypeError::UnreducedEquationFunctor {
                functor, census, ..
            } => LoadError::UnreducedEquationFunctor {
                span: self.span(kb),
                functor: kb.qualified_name_of(*functor).to_string(),
                census: *census,
            },
            TypeError::DispatchNoMatch { op, unmet, .. } => LoadError::TypeMismatch {
                origin: None,
                entity_name: kb.qualified_name_of(*op).to_string(),
                field_name: "dispatch".to_string(),
                expected_type: "matching impl for per-call bindings".to_string(),
                // WI-869: the unmet goal is APPENDED, never substituted — several
                // suites assert on the "no impl matches" text, and a conditional
                // provision's refusal is an addition to that story, not a different
                // one.
                actual_type: format!("no impl matches{}", render_unmet(unmet)),
                span: self.span(kb),
            },
            // WI-843: its OWN variant, not a `TypeMismatch` — nothing here is a
            // type mismatch (every candidate typed fine; the program just never
            // said which to run), and the "expected X, got Y" frame has no room
            // for the candidate list and the repair syntax that make a use-site
            // refusal actionable.
            TypeError::DispatchAmbiguous { op, tie, .. } => {
                let (candidates, repair) = render_instance_tie(kb, tie);
                LoadError::UnselectedInstance {
                    op: kb.qualified_name_of(*op).to_string(),
                    spec: kb.qualified_name_of(tie.spec).to_string(),
                    candidates,
                    repair,
                    span: self.span(kb),
                }
            }
            // WI-1012: its OWN variant for WI-843's reason one ticket over — the
            // "expected X, got Y" frame has no room for the candidate list, which is
            // the whole diagnostic (the author has to know which of three syntaxes to
            // delete). Spanned: the typer holds the call's span at the moment it
            // declines to pin.
            TypeError::AmbiguousSpecOpDispatch {
                op,
                carrier,
                candidates,
                repair,
                ..
            } => LoadError::AmbiguousSpecOpDispatch {
                op: kb.qualified_name_of(*op).to_string(),
                carrier: kb.qualified_name_of(*carrier).to_string(),
                candidates: candidates.clone(),
                repair: *repair,
                span: self.span(kb),
            },
            TypeError::NoSuchTypeParam { op, name, .. } => LoadError::TypeMismatch {
                origin: None,
                entity_name: kb.qualified_name_of(*op).to_string(),
                field_name: "type_arg".to_string(),
                expected_type: "declared type-param name".to_string(),
                actual_type: format!("unknown type-param '{}'", kb.local_name_of(*name)),
                span: self.span(kb),
            },
            TypeError::ExcessCallTypeArgs {
                op, given, free, ..
            } => LoadError::TypeMismatch {
                origin: None,
                entity_name: kb.qualified_name_of(*op).to_string(),
                field_name: "type_arg".to_string(),
                expected_type: format!("at most {free} positional type argument(s)"),
                actual_type: format!("{given} — the callee is over-applied"),
                span: self.span(kb),
            },
            TypeError::DuplicateCallTypeArg { op, name, .. } => LoadError::TypeMismatch {
                origin: None,
                entity_name: kb.qualified_name_of(*op).to_string(),
                field_name: "type_arg".to_string(),
                expected_type: "each type parameter bound at most once".to_string(),
                actual_type: format!(
                    "type-param '{}' bound twice in one bracket",
                    kb.local_name_of(*name),
                ),
                span: self.span(kb),
            },
            TypeError::ReceiverBracketConflict {
                op,
                param,
                receiver,
                callee,
                ..
            } => LoadError::TypeMismatch {
                origin: None,
                entity_name: kb.qualified_name_of(*op).to_string(),
                field_name: "type_args".to_string(),
                expected_type: format!(
                    "the receiver bracket's {} = {}",
                    kb.local_name_of(*param),
                    type_display_name_value(kb, receiver),
                ),
                actual_type: format!(
                    "the callee bracket's {} = {}",
                    kb.local_name_of(*param),
                    type_display_name_value(kb, callee),
                ),
                span: self.span(kb),
            },
            TypeError::TypeArgsOnNonOperation { callee, .. } => LoadError::TypeMismatch {
                origin: None,
                entity_name: kb.qualified_name_of(*callee).to_string(),
                field_name: "type_arg".to_string(),
                expected_type: "an operation, which declares the type parameters a \
                                call-site `[…]` bracket binds"
                    .to_string(),
                actual_type: "a callee with no type-parameter list (a function value, \
                              an applied rule, a constructor)"
                    .to_string(),
                span: self.span(kb),
            },
            // WI-841 — the four selection refusals. Each renders through `format`, so
            // the load-facing text and the typer-facing text are ONE string: these
            // messages carry the whole explanation (which slots, which witness, which
            // spec), and a second hand-written summary here could only drift from it.
            TypeError::AmbiguousRequirementKey { op, name, .. } => LoadError::TypeMismatch {
                origin: None,
                entity_name: kb.qualified_name_of(*op).to_string(),
                field_name: "type_arg".to_string(),
                expected_type: format!(
                    "'{}' to name ONE requirement slot",
                    kb.local_name_of(*name),
                ),
                actual_type: self.format(kb),
                span: self.span(kb),
            },
            // `selection`, not `type_arg`, for the reason given at
            // [`TypeError::WitnessDoesNotProvide`] above — WI-20260911-6B67S gave this
            // refusal the same two channels.
            TypeError::SelectionValueNotASort { op, spec, .. } => LoadError::TypeMismatch {
                origin: None,
                entity_name: kb.qualified_name_of(*op).to_string(),
                field_name: "selection".to_string(),
                expected_type: format!("a witness sort for {}", kb.qualified_name_of(*spec),),
                actual_type: self.format(kb),
                span: self.span(kb),
            },
            TypeError::SlotSelectionUnindexable {
                op, owner, binder, ..
            } => LoadError::TypeMismatch {
                origin: None,
                entity_name: kb.qualified_name_of(*op).to_string(),
                field_name: "type_arg".to_string(),
                expected_type: format!(
                    "a locatable requirement slot `{}` on {}",
                    kb.local_name_of(*binder),
                    kb.qualified_name_of(*owner),
                ),
                actual_type: self.format(kb),
                span: self.span(kb),
            },
            TypeError::ErasedRequirementSlot {
                op, binder, spec, ..
            } => LoadError::TypeMismatch {
                origin: None,
                entity_name: kb.qualified_name_of(*op).to_string(),
                field_name: "requires".to_string(),
                expected_type: format!(
                    "a supplied `{}: {}` slot (write it in the type, or declare it)",
                    kb.local_name_of(*binder),
                    kb.qualified_name_of(*spec),
                ),
                actual_type: self.format(kb),
                span: self.span(kb),
            },
            // WI-20260911-6B67S: `selection`, not `type_arg` — the SAME rule WI-844 states
            // three arms down for `ConflictingSelection`, and for the same reason. Once
            // `selections_from_slot_bindings` runs check 1, this refusal is reached by a
            // selection carried in an ARGUMENT'S TYPE as well as by a written bracket, so
            // `type_arg` named where it was written and got it wrong: MEASURED,
            // `type mismatch in …SortedSet.toList.type_arg` on a program with no type arg
            // anywhere. The field names WHAT is wrong.
            TypeError::WitnessDoesNotProvide { op, spec, .. } => LoadError::TypeMismatch {
                origin: None,
                entity_name: kb.qualified_name_of(*op).to_string(),
                field_name: "selection".to_string(),
                expected_type: format!("a provider of {}", kb.qualified_name_of(*spec)),
                actual_type: self.format(kb),
                span: self.span(kb),
            },
            // WI-20260911-TX0G6: `selection`, the rule the two arms above follow. The
            // receiver spelling reaches this refusal too, and its three refusals of one
            // written selection should name one field.
            TypeError::ValueDirectedSelection { op, .. } => LoadError::TypeMismatch {
                origin: None,
                entity_name: kb.qualified_name_of(*op).to_string(),
                field_name: "selection".to_string(),
                expected_type: "no explicit selection of a concrete provider".to_string(),
                actual_type: self.format(kb),
                span: self.span(kb),
            },
            // WI-844: `selection`, not `type_arg` — a conflicting pair can be written
            // in a bracket, carried in an argument's TYPE, or one of each, so the field
            // names what is wrong rather than where it was written.
            TypeError::ConflictingSelection { op, spec, .. } => LoadError::TypeMismatch {
                origin: None,
                entity_name: kb.qualified_name_of(*op).to_string(),
                field_name: "selection".to_string(),
                expected_type: format!("one witness for {}", kb.qualified_name_of(*spec)),
                actual_type: self.format(kb),
                span: self.span(kb),
            },
            // WI-709: the SAME `LoadError` the type position raises — one written type,
            // one diagnostic, wherever it appears.
            TypeError::InvalidTypeArgument { sort, problem, .. } => {
                LoadError::InvalidTypeArgument {
                    detail: problem.describe(kb, *sort),
                    span: self.span(kb),
                }
            }
            TypeError::UnconstrainedTypeParam { op, type_param, .. } => {
                let op_qn = kb.qualified_name_of(*op);
                let suggestion = format!(
                    "unconstrained — use `{}[{} = …](…)`",
                    short_name_of(op_qn),
                    kb.local_name_of(*type_param),
                );
                LoadError::TypeMismatch {
                    origin: None,
                    entity_name: op_qn.to_string(),
                    field_name: "type_arg".to_string(),
                    expected_type: format!("a type for '{}'", kb.local_name_of(*type_param)),
                    actual_type: suggestion,
                    span: self.span(kb),
                }
            }
            TypeError::UnconstrainedCitationParam {
                relation,
                sort,
                type_param,
                ..
            } => LoadError::TypeMismatch {
                origin: None,
                entity_name: kb.qualified_name_of(*relation).to_string(),
                field_name: "type_arg".to_string(),
                expected_type: format!("a type for '{}'", kb.local_name_of(*type_param)),
                actual_type: citation_param_message(kb, *relation, *sort, *type_param),
                span: self.span(kb),
            },
            TypeError::MissingRequiresForSpecOp {
                spec_op_sym,
                spec_sort_sym,
                abstract_params,
                ..
            } => {
                let op_qn = kb.qualified_name_of(*spec_op_sym);
                let spec_qn = kb.qualified_name_of(*spec_sort_sym);
                let spec_short = short_name_of(spec_qn);
                let params_list: Vec<String> = abstract_params
                    .iter()
                    .map(|p| format!("{0} = …", kb.local_name_of(*p)))
                    .collect();
                let suggestion = format!(
                    "missing `requires {}[{}]` on enclosing sort",
                    spec_short,
                    params_list.join(", "),
                );
                LoadError::TypeMismatch {
                    origin: None,
                    entity_name: op_qn.to_string(),
                    field_name: "requires".to_string(),
                    expected_type: format!(
                        "`requires {}[…]` covering abstract type parameter",
                        spec_short
                    ),
                    actual_type: suggestion,
                    span: self.span(kb),
                }
            }
            TypeError::ProvisionConditionOutOfScope {
                op, spec_sort_sym, ..
            } => LoadError::TypeMismatch {
                origin: None,
                entity_name: kb.qualified_name_of(*op).to_string(),
                field_name: "requires".to_string(),
                expected_type: format!(
                    "`{}` evidence in scope for this body",
                    short_name_of(kb.qualified_name_of(*spec_sort_sym)),
                ),
                actual_type: self.format(kb),
                span: self.span(kb),
            },
            // WI-20260919-N31XX — the operation is the entity (it is the signature that
            // must change) and `requires` the field, as the sibling above has it.
            TypeError::TypeValueReadUnbacked { param, op, .. } => {
                let p = short_name_of(kb.local_name_of(*param));
                LoadError::TypeMismatch {
                    origin: None,
                    entity_name: kb.qualified_name_of(*op).to_string(),
                    field_name: "requires".to_string(),
                    expected_type: format!("`requires anthill.reflect.TypeValue[T = {p}]`"),
                    actual_type: format!(
                        "`{p}` is read as a VALUE and nothing in scope requires \
                         `TypeValue[T = {p}]`, so the signature promises nothing about \
                         whether this operation inspects `{p}` (proposal 065). Add the \
                         clause, or use `{p}` only in type position"
                    ),
                    span: self.span(kb),
                }
            }
            TypeError::UnfillableOperationRequirement {
                callee_op,
                spec_sort_sym,
                carrier_sym,
                ..
            } => {
                let spec_qn = kb.qualified_name_of(*spec_sort_sym);
                let carrier_qn = kb.qualified_name_of(*carrier_sym);
                LoadError::TypeMismatch {
                    origin: None,
                    entity_name: kb.qualified_name_of(*callee_op).to_string(),
                    field_name: "requires".to_string(),
                    expected_type: format!(
                        "a `{spec_qn}` this clause can supply for carrier `{carrier_qn}`"
                    ),
                    actual_type: format!(
                        "`{carrier_qn}` provides no `{spec_qn}`, and this clause declares \
                         no `requires({}[…])` of its own — so no call here can discharge \
                         it. Add a `provides {}[…]` for `{carrier_qn}` (or a witness sort \
                         that provides it), or take the obligation on in this clause",
                        short_name_of(spec_qn),
                        short_name_of(spec_qn),
                    ),
                    span: self.span(kb),
                }
            }
            TypeError::NoProvisionAtCarriers {
                callee_op,
                spec_sort_sym,
                bindings,
                ..
            } => {
                let spec_qn = kb.qualified_name_of(*spec_sort_sym);
                let short = short_name_of(spec_qn);
                let at = carrier_bindings_text(kb, bindings);
                LoadError::TypeMismatch {
                    origin: None,
                    entity_name: kb.qualified_name_of(*callee_op).to_string(),
                    field_name: "requires".to_string(),
                    expected_type: format!("a `{spec_qn}` provision binding `{at}`"),
                    actual_type: format!(
                        "no provision of `{spec_qn}` binds `{at}`, and this clause declares \
                         no `requires({short}[…])` of its own — so no call here can \
                         discharge it. Add a `provides {short}[{at}]` (on a sort, or a \
                         witness sort), or take the obligation on in this clause"
                    ),
                    span: self.span(kb),
                }
            }
            TypeError::UnsatisfiableRequirement {
                op,
                callee_sort,
                eta,
                refusal,
                ..
            } => LoadError::TypeMismatch {
                origin: None,
                entity_name: kb.qualified_name_of(*op).to_string(),
                field_name: "requires".to_string(),
                expected_type: "a requirement suppliable at this call site".to_string(),
                actual_type: refusal.render(kb, *op, *callee_sort, *eta),
                span: self.span(kb),
            },
            TypeError::NonBoolOpInGoalPosition {
                op_sym,
                return_sort,
                ..
            } => {
                let op_qn = kb.qualified_name_of(*op_sym).to_string();
                let ret = kb.qualified_name_of(*return_sort).to_string();
                LoadError::TypeMismatch {
                    origin: None,
                    entity_name: op_qn,
                    field_name: "goal".to_string(),
                    expected_type:
                        "a Bool-returning operation (gated as `eq(op(…), true)`) or a relation"
                            .to_string(),
                    actual_type: format!(
                        "operation returning `{ret}` in rule-body goal position — no relational reading"
                    ),
                    span: self.span(kb),
                }
            }
            TypeError::ConstantInGoalPosition { literal, .. } => {
                LoadError::ConstantInGoalPosition {
                    literal: literal.clone(),
                    // WI-1034's convention: the span is the GOAL's own text, which is
                    // where the author must look. A constant carries no functor to name
                    // a citing rule by, so the location is the whole diagnostic's anchor.
                    span: self.span(kb).unwrap_or_default(),
                }
            }
            TypeError::EquationSubjectInGoalPosition { functor, .. } => {
                LoadError::EquationSubjectInGoalPosition {
                    functor: kb.qualified_name_of(*functor).to_string(),
                    // WI-1034's convention, as the neighbour above: the span is the
                    // GOAL's own text — the citation, not the equation it names.
                    span: self.span(kb).unwrap_or_default(),
                }
            }
            TypeError::EqOverrideUnbacked { carrier_sort, .. } => {
                let carrier_qn = kb.qualified_name_of(*carrier_sort).to_string();
                LoadError::TypeMismatch {
                    origin: None,
                    entity_name: carrier_qn.clone(),
                    field_name: "eq".to_string(),
                    expected_type: format!(
                        "an implemented `Eq[{}]` instance (rules or a runnable `eq` body, or the WI-625 host bridge)",
                        carrier_qn,
                    ),
                    actual_type: "`Eq` override declared but unimplemented — comparing two of these would silently misdecide".to_string(),
                    span: self.span(kb),
                }
            }
            TypeError::BottomExpr { .. } => LoadError::TypeMismatch {
                origin: None,
                entity_name: "<bottom>".to_string(),
                field_name: "expr".to_string(),
                expected_type: "surface expression".to_string(),
                actual_type: "bottom / post-elaboration form".to_string(),
                span: self.span(kb),
            },
            TypeError::DotDispatchNoMatch {
                member,
                receiver_sort,
                receiver_param,
                ..
            } => LoadError::TypeMismatch {
                origin: None,
                entity_name: match (receiver_sort, receiver_param) {
                    (Some(s), _) => kb.qualified_name_of(*s).to_string(),
                    // WI-1119 — the parameter as written, not `<unresolved receiver>`.
                    (None, Some(p)) => p.param.clone(),
                    (None, None) => "<unresolved receiver>".to_string(),
                },
                field_name: kb.local_name_of(*member).to_string(),
                expected_type: match receiver_param {
                    // WI-1119 — what the author must supply differs by receiver: a sort
                    // needs the member declared ON it, a constrained parameter needs a
                    // constraining SPEC to declare it.
                    Some(_) => "operation declared by a spec constraining the receiver's \
                                type parameter"
                        .to_string(),
                    None => "operation declared on the receiver's sort".to_string(),
                },
                actual_type: match receiver_param {
                    Some(p) => format!(
                        "no such member (dot dispatch) — {}",
                        constrained_param_repair(kb, &p.specs, kb.local_name_of(*member)),
                    ),
                    None => "no such member (dot dispatch)".to_string(),
                },
                span: self.span(kb),
            },
            // WI-1119 — its OWN variant for the reason `AmbiguousSpecOpDispatch` is one:
            // the candidate list IS the diagnostic, and the "expected X, got Y" frame has
            // no room for it. Rendered through the shared body so the `format` face and
            // this one cannot drift.
            TypeError::AmbiguousConstrainedParamMember {
                member,
                receiver,
                specs,
                ..
            } => LoadError::TypeMismatch {
                origin: None,
                entity_name: receiver.clone(),
                field_name: kb.local_name_of(*member).to_string(),
                expected_type: "one spec constraining the receiver's type parameter to \
                                declare this member"
                    .to_string(),
                actual_type: ambiguous_constrained_param_message(
                    kb,
                    kb.local_name_of(*member),
                    receiver,
                    specs,
                ),
                span: self.span(kb),
            },
            TypeError::ForbiddenInternalField {
                entity,
                field,
                from_scope,
                ..
            } => {
                let declared_in = {
                    let q = kb.qualified_name_of(*entity);
                    q.rsplit_once('.')
                        .map(|(p, _)| p.to_string())
                        .unwrap_or_else(|| q.to_string())
                };
                LoadError::ForbiddenInternalAccess {
                    name: kb.local_name_of(*field).to_string(),
                    declared_in,
                    // WI-977 — the scope the projection was written in. Was the
                    // literal `"another scope"`, which the renderer wrapped as
                    // `from scope 'another scope'`: a `scope_name` slot filled with
                    // prose, reading as a scope so named. The variant carries the
                    // real one now, so this is the same answer as every other site.
                    scope_name: kb.scope_display_name(*from_scope).to_string(),
                    span: self.span(kb).unwrap_or_default(),
                }
            }
            // WI-757: SPANNED and its own variant, for the reason WI-819 gave —
            // it is user-reachable, and an unspanned diagnostic renders with no
            // `line:col` at all.
            TypeError::MacroRejected {
                macro_name, detail, ..
            } => LoadError::MacroRejected {
                macro_name: kb.qualified_name_of(*macro_name).to_string(),
                detail: detail.clone(),
                span: self.span(kb).unwrap_or_default(),
            },
            TypeError::Multiple { errors } => {
                // Lossy: keep the first error's structured form so legacy
                // single-error consumers see something. Callers that care
                // about all errors call `flatten()` and convert per-element.
                if let Some(first) = errors.first() {
                    first.to_load_error(kb)
                } else {
                    LoadError::TypeMismatch {
                        origin: None,
                        entity_name: "<empty>".to_string(),
                        field_name: "".to_string(),
                        expected_type: String::new(),
                        actual_type: String::new(),
                        span: None,
                    }
                }
            }
            TypeError::UnsatisfiedPrecondition {
                op, clause, kind, ..
            } => LoadError::TypeMismatch {
                origin: None,
                // WI-K88TN — THE DECLARATION THE AUTHOR MUST EDIT, which for the wrapper
                // case is not the callee. `<entity>.<field>` heads the message, and
                // naming `send.requires` there says "send's contract is wrong" when
                // send's contract is fine and `relay`'s is missing; the span already
                // points inside `relay`'s body, so the two now agree. The other two
                // cases keep the callee: an unsatisfied obligation IS the callee's
                // `requires`, and for an opaque witness there is no declaration to name.
                entity_name: match kind {
                    PreconditionFailure::UndeclaredInWrapper { enclosing } => {
                        kb.qualified_name_of(*enclosing).to_string()
                    }
                    _ => kb.qualified_name_of(*op).to_string(),
                },
                field_name: "requires".to_string(),
                expected_type: match kind {
                    PreconditionFailure::AtCallSite => format!(
                        "precondition `{}` provable at the call site",
                        format_precondition_clause(kb, clause)
                    ),
                    // WI-K88TN: says what is WANTED, and the want is a declaration —
                    // "provable at the call site" would send the author to a line whose
                    // repair does not exist.
                    PreconditionFailure::UndeclaredInWrapper { .. } => format!(
                        "precondition `{}` declared here or provable for every instantiation",
                        format_precondition_clause(kb, clause)
                    ),
                    PreconditionFailure::UndischargeableWitness => format!(
                        "precondition `{}` over a type variable some signature in scope binds",
                        format_precondition_clause(kb, clause)
                    ),
                },
                actual_type: match kind {
                    PreconditionFailure::AtCallSite => "unsatisfied precondition".to_string(),
                    PreconditionFailure::UndeclaredInWrapper { .. } => {
                        "undischarged precondition over a universally quantified type variable"
                            .to_string()
                    }
                    PreconditionFailure::UndischargeableWitness => {
                        "undischargeable precondition over an opaque witness from a callee's return"
                            .to_string()
                    }
                },
                span: self.span(kb),
            },
            TypeError::Other {
                context,
                expected,
                actual,
                site,
                ..
            } => LoadError::TypeMismatch {
                origin: Some(TypeMismatchOrigin {
                    error_kind: "Other",
                    context_kind: context.kind_tag(),
                    site: *site,
                }),
                entity_name: context.entity_name(kb),
                field_name: context.field_name(kb),
                expected_type: expected.clone(),
                actual_type: actual.clone(),
                span: self.span(kb),
            },
        }
    }
}

/// WI-20260911-5G28A S1 — the wording of [`TypeError::UnconstrainedCitationParam`], ONE
/// owner for both renderings (the type error's own message and the `LoadError` it becomes),
/// so the repair the two print cannot drift.
fn citation_param_message(
    kb: &KnowledgeBase,
    relation: Symbol,
    sort: Symbol,
    type_param: Symbol,
) -> String {
    let sort_short = short_name_of(kb.qualified_name_of(sort)).to_string();
    format!(
        "type parameter '{param}' of `{sort_qn}` is not determined at this citation of `{rel}` \
         — no bracket, argument or expected type fixes it; write it: `{sort_short}[{param} = …].{rel_short}`",
        param = kb.local_name_of(type_param),
        sort_qn = kb.qualified_name_of(sort),
        rel = kb.qualified_name_of(relation),
        rel_short = short_name_of(kb.qualified_name_of(relation)),
    )
}

/// `A = Meters, B = anthill.prelude.Int64` — a [`TypeError::NoProvisionAtCarriers`]'s
/// carriers as the bracket a provision would write, each parameter by its short name.
fn carrier_bindings_text(kb: &KnowledgeBase, bindings: &[(Symbol, Symbol)]) -> String {
    bindings
        .iter()
        .map(|&(param, carrier)| {
            format!(
                "{} = {}",
                short_name_of(kb.qualified_name_of(param)),
                kb.qualified_name_of(carrier)
            )
        })
        .collect::<Vec<_>>()
        .join(", ")
}

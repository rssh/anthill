//! The typing environment: `TypingEnv` (per-body bindings and caches) and proposal 050's
//! `FlowEnv` (the local logical storage Γ) and `Env` (the carrier the typer threads).

use super::*;

// ── TypingEnv ──────────────────────────────────────────────────

#[derive(Clone)]
pub struct TypingEnv {
    // WI-259: Symbol-keyed (was String-keyed). Symbol is a Copy
    // u32 newtype that's already interned and trivially hashable;
    // String keys cost a fresh allocation per bind + a hash over
    // the name's bytes at every lookup, and TypingEnv gets cloned
    // on every Visit push of the iterative typer.
    // WI-341 Stage A: a var's TYPE is carrier-agnostic (`Value`) — a callback
    // parameter whose arrow effect is denoted-bearing (`Modify[a]`) is a
    // `Value::Node` arrow and cannot be a hash-consed `TermId`. Ground bindings
    // are `Value::Term`.
    pub(super) var_bindings: HashMap<Symbol, Value>,
    /// WI-400 increment C (eager let-alias): the canonical receiver PATH a let-bound
    /// name aliases. `let y = z` records `y → [z]`; `let y = s.provider` records
    /// `y → [s, provider]` — populated only for a STABLE receiver path (a value reference
    /// / field-access chain; immutable `let` ⟹ the aliased names denote one runtime
    /// value, the §3 soundness note). A projection `y.M` formed at the env-bearing let
    /// site is canonicalized through this map (`canonicalize_projection_receivers`) so it
    /// carries the SAME receiver as `z.M` / `s.provider.M` and the ζ arm equates them
    /// (`let y = z ⟹ y.M ≡ z.M`, the Scala divergence). Heads are stored already
    /// de-aliased (transitive `let y = z; let w = y` ⟹ `w → [z]`).
    pub(super) receiver_aliases: HashMap<Symbol, Vec<Symbol>>,
    /// WI-20260824-PAPX0 (proposal 055 umbrella A step 4, design §4) — the
    /// `Expr::TypeValue` occurrence a let-bound name DENOTES: `let t = Box[V =
    /// Int64]` records `t → that node`. Read at the `DotApply` frame, where
    /// option B says a dot on a type value resolves its member in the DENOTED
    /// sort's scope rather than among `Type`'s own members.
    ///
    /// A SECOND CHANNEL BESIDE `receiver_aliases`, NOT A WIDENING OF IT, and the
    /// reason is that they answer different questions. `receiver_aliases` maps a
    /// binder to another VALUE PATH so a type projection off it canonicalizes to
    /// the same receiver (`let y = z ⟹ y.M ≡ z.M`); this maps a binder to a
    /// DENOTED SORT. A `let t = Box[V = Int64]` has no aliased receiver path at
    /// all — `stable_receiver_path` answers `None` for a `TypeValue` — so
    /// overloading the alias map would have to invent a path that means "not a
    /// path, a denotation", which is the one-name-two-questions defect this
    /// repo has paid for repeatedly (WAHB6 states the same rule for
    /// `NodeKind::Expr.classification`).
    ///
    /// The NODE, not just its `head`: the type ARGUMENTS are part of the
    /// denotation (`Box[V = Int64]` and `Box[V = String]` denote different
    /// instantiations), and the companion call the frame synthesizes carries
    /// them as its `recv_type` exactly as the written form `Box[V =
    /// Int64].tag()` does. Storing only the head would silently drop the
    /// bindings and type the result at the wrong instantiation.
    type_denotations: HashMap<Symbol, Rc<NodeOccurrence>>,
    /// WI-424/WI-942 — every type-param canonical var IN SCOPE for this body,
    /// mapped to the per-body `Var::Rigid` term `check_operation_bodies` minted
    /// for it (the WI-392 skolemization, extended to the enclosing SORT's params
    /// and to the operation's OWN). Two scopes, ONE list, in the order §5.2's key
    /// rule states them: the ENCLOSING SORT's params first — `sort_rigid_len` of
    /// them — then the operation's. Empty outside a parametric sort's or a
    /// type-parameterized op's body check. `Rc`: the env is cloned on every Visit
    /// push of the iterative typer and this is set once per body, so clones are a
    /// refcount bump, not a Vec copy.
    ///
    /// "THE OPERATION'S" IS THREE SPELLINGS, NOT ONE (WI-1FKR2). Its own `[A]`
    /// brackets, and the logical variables it WROTE INLINE in a parameter type
    /// (`via(b: Box[?t]) -> Box[?t]`) — §5.4 quantifies both the same way, so
    /// [`inline_signature_type_params`] adds the second to the op half. Still TWO
    /// SCOPES: an inline variable is per-call and caller-instantiated, which is
    /// what the op half means and what the sort prefix is not. Nothing about
    /// `sort_rigid_len` or either view below changes; what changes is that
    /// "the operation's own type parameters" must be read as §5.4 defines them
    /// and not as "whatever `[A]` was written".
    ///
    /// Read through the two NAMED views, never directly, because the halves are
    /// not interchangeable:
    ///  * [`Self::param_rigids`] — ALL of it, for every σ-class question ("are
    ///    these two written type elements the same parameter?"). WI-942: with only
    ///    the sort half recorded, an op-declared param's canonical `Global` had no
    ///    bridge to the `Rigid` its own body was checked at, so
    ///    [`op_requires_covers`] could not see that `cmp[T](a: T, …) requires
    ///    Ord[T]` covers its own `Ord.compare(a, b)` — the call was refused
    ///    `MissingRequiresForSpecOp` demanding a `requires` "on enclosing sort"
    ///    that the author had already written on the operation.
    ///  * [`Self::enclosing_instance_param_rigids`] — the SORT prefix alone, whose
    ///    one consumer is `check_apply_iter`'s same-sort sibling-call seeding: it
    ///    means "THIS instance's params" (`iterator(c)` inside an `Iterable` member
    ///    body returns `Stream[Element, E]` at the enclosing rigids instead of
    ///    dangling fresh `?_`), and a per-call op param is not one of them.
    ///    `enforce_member_tie` and `carrier_provision_short_bindings` also take
    ///    this view, but are indifferent to the choice: both look up only vids they
    ///    got from `sort_type_params_as_pairs`, which an op param's vid never is.
    pub(super) param_rigids: Rc<Vec<(VarId, TermId)>>,
    /// How many leading entries of [`Self::param_rigids`] are the enclosing SORT's
    /// (see that field). The producer appends the op's own after them, so the
    /// prefix relation is structural rather than a convention two lists must keep.
    pub(super) sort_rigid_len: usize,
    local_resources: Vec<Symbol>,
    /// Enclosing sort for defer-to-requirement detection.
    pub(super) enclosing_sort: Option<Symbol>,

    /// WI-977 — the scope a RULE BODY is written in (the rule's `domain`), for
    /// diagnostics only. Its own field rather than a reuse of `enclosing_sort`
    /// because the rule-body sweep leaves that empty ON PURPOSE — a rule body carries
    /// no lexical params and must not acquire a sort's requirement frame — and this
    /// must not change what defers to what. Read only by
    /// [`Self::referencing_scope`]. `None` outside the rule-body sweep.
    rule_scope: Option<Symbol>,
    /// WI-20260922-0DK3H — the spec VIEWS this RULE BODY DECLARES, as `require[X]` /
    /// `requires(X)` brackets (the `find_dictionary` goals the converter lowered them to,
    /// whose slot 0 carries the instance WHOLE — `lower_require`'s "WHOLE, not stripped").
    ///
    /// ROUTE 4's SLOT SOURCE, ONE SOURCE OVER, and that is why it rides here rather than
    /// in a predicate of its own: [`held_spec_views`] already asks "what contracts does
    /// this caller hold?", and a clause that WRITES `require[FiniteCollection[C = …]]`
    /// holds one for the same reason a parameter's type does — it is evidence read off
    /// the clause's own text, not a walk of somebody else's body. Feeding it through the
    /// one channel is also what makes the TRANSITIVE leg work for free:
    /// [`scope_contract_covers_dep`] walks `direct_requires_chain`, so a declared
    /// `FiniteCollection` discharges the `Iterable` that `FiniteCollection` itself
    /// requires. Exactly the carrier-aware transitive suppression
    /// [`check_one_spec_op_requirement`]'s doc defers as "a clean follow-up gated on an
    /// actual driver" — WI-20260922-0DK3H is that driver, and the cover walk supplies the
    /// carriers its exact-symbol match could not.
    ///
    /// Empty outside the rule-body sweep, where it is `None` for the same reason
    /// [`Self::rule_scope`] is.
    pub(super) rule_declared_specs: Rc<Vec<Value>>,
    /// The enclosing SORT's dictionary chain, snapshotted once per body. It is
    /// consulted at every spec-op call site under this body; caching it here avoids
    /// re-walking `SortRequiresInfo` per apply.
    ///
    /// THE SORT HALF. It is still exactly that — a SORT's chain — but since
    /// WI-20260921-159S9 it is no longer what the INSTANCE-DICTIONARY builders are
    /// handed: `check_apply_iter`'s cross-sort site passes
    /// [`Self::enclosing_frame_chain`], so a slot declared on the OPERATION carries a
    /// forwarded dictionary exactly as one declared on the sort does.
    ///
    /// WI-822 LEG 1 narrowed that read to this field and the narrowing was load-bearing
    /// while it stood: the instance channel is consulted STRICTLY at eval — a `var_ref`
    /// in it must resolve or the dispatch has no target — and four routes into an
    /// operation filled no op slot, so forwarding one turned WI-828's LOAD-time
    /// `UnsatisfiableRequirement` into an eval-time unbound `var_ref`. All four now
    /// fill: a host `interp.call` (WI-1091 `seed_entry_op_requirements`), an eta'd
    /// `OpRef` (`push_captured_op_scoped_slots`), value-directed dispatch (which reads
    /// the composed chain), and the DEFERRED route (159S9's
    /// `Interpreter::fill_missing_op_scoped_slots`, at `enter_operation`). The premise
    /// went away before the narrowing did.
    ///
    /// WHAT STILL READS THIS FIELD ALONE is [`Self::enclosing_requires`] — the DEFER
    /// decision, "is this call served by a frame slot or by value-direction" — and that
    /// one is untouched. Widening IT was measured at 30 failures across
    /// wi842/wi843/wi855/wi876/wi886/wi869, and the two questions stay separate: which
    /// chain a dictionary PROJECTS FROM is not which channel a call DISPATCHES THROUGH.
    enclosing_chain: DictChain,
    /// WI-822 LEG 1 — the FRAME chain of the body being checked: [`Self::enclosing_chain`]
    /// followed by the enclosing OPERATION's own op-scoped slots ([`op_dict_entries`]).
    /// `None` for the operations that write no `requires` of their own, which is nearly
    /// all of them, and where it would be the same value.
    ///
    /// THREE readers since WI-20260921-159S9, the third being the one the other two
    /// were once defined against: [`op_scoped_defer_location`] (which slot a body call
    /// defers to), [`build_op_scoped_dicts`]' caller chain (what a callee's op slot may
    /// forward FROM — the caller's own op slots included, which is how an op-scoped
    /// requirement relays hop to hop), and now `check_apply_iter`'s cross-sort
    /// INSTANCE-DICTIONARY build. This doc used to say the instance dictionary must not
    /// be a reader; see [`Self::enclosing_chain`] for the premise that changed.
    enclosing_op_chain: Option<DictChain>,
    /// WI-562: the enclosing OPERATION's own op-scoped `requires` chain (WI-448),
    /// snapshotted for the body about to be checked. Consulted (before provider
    /// dispatch) to LICENSE the body's abstract spec-op calls against an
    /// op-type-param the op `requires` — `List.member requires Eq[E]` covering
    /// its `eq(head, x)` — the op-scoped dual of the sort-level
    /// defer-to-requirement. `Rc`: set once per body; the env is cloned on every
    /// Visit push of the iterative typer.
    pub(super) op_requires: Rc<Vec<RequiresEntry>>,
    /// WI-822 LEG 1 — the OPERATION whose body is being checked. Carried into
    /// [`CallClass::DeferToRequirement`] and [`CallClass::ConcreteApplyWithin`]
    /// beside `enclosing_sort`, because a frame's slot NAMES are the operation's
    /// (its sort's chain then its own) and a sort alone cannot name the op half.
    /// `None` outside an operation body — the rule-body dot-dispatch sweep.
    pub(super) enclosing_op: Option<Symbol>,
    /// WI-282: the enclosing RULE's De Bruijn variable types, keyed by De Bruijn
    /// index — the rule-body analog of `var_bindings` (which is keyed by the
    /// SYMBOL name a param/let/lambda binds under). A rule body has no lexical
    /// param env; a body var is an `Expr::Var(Var::DeBruijn(i))` whose type is
    /// inferred from its use in the goals (`collect_occurrence_type_constraints`).
    /// Installed so a value-receiver `?x.field` / `?x.method(...)` in a rule body
    /// resolves `?x` to a concrete sort and dispatches, exactly as an op-body dot
    /// does ("dot means the same in all expression positions"). Empty outside a
    /// rule-body dot-dispatch walk. `Rc`: the env is cloned on every Visit push of
    /// the iterative typer and this is set once per rule, so clones are a refcount
    /// bump, not a map copy.
    debruijn_types: Rc<HashMap<u32, Value>>,
    /// WI-557 / WI-622: set ONLY by the rule-body dot-dispatch sweep
    /// (`type_rule_bodies`). A rule body is SLD/relational — it has no
    /// call-site Γ and no imperative Hoare semantics — so an OP-BODY call-site
    /// obligation over a symbolic rule-body variable legitimately FLOATS and must
    /// not fire as a hard load error. `check_apply_iter` consults this to scope
    /// two such obligations (op-body checking, the flag `false`, is unchanged):
    ///   * WI-539 value-precondition `requires`-check — skipped for a FLOAT but
    ///     still raised on a ground-REFUTED precondition (WI-602: definite raises,
    ///     float defers — the WI-067/WI-292 polarity);
    ///   * WI-270 `UnconstrainedTypeParam` — skipped entirely, because the dot is
    ///     typed with `expected: None` so a return-only param has no call-site pin,
    ///     yet SLD resolution unifies it against the goal context. There is no
    ///     DEFINITE sub-case (unlike the precondition): "unconstrained" means "no
    ///     binding at all", exactly the float condition; a genuine type CONFLICT
    ///     surfaces as a contradiction / `TypeMismatch`, not here.
    /// The sibling spec-op `DispatchNoMatch` needs NO gate: dot dispatch resolves
    /// a spec op only on a CONCRETE (or abstract-spec) receiver, never an abstract
    /// type-param, so every rule-body dot that reaches that raise has a concrete
    /// carrier — a DEFINITE failure that must stay loud (WI-622 finding).
    /// A plain `bool` rides through every `Visit`-push /
    /// let / lambda / match env clone exactly as `debruijn_types` does — the same
    /// path the receiver-var dispatch already depends on. NOT inferred from
    /// `debruijn_types.is_empty()` / `enclosing.is_none()`: a variable-free rule
    /// body has an empty `debruijn_types`, and a namespace-level op body has
    /// `enclosing_sort = None`, so neither is a precise discriminator (explicit over
    /// implicit — see the loud-over-silent principle).
    pub(super) rule_body_dispatch: bool,
    pub diagnostics: Vec<String>,
    /// WI-20260830-JM7A8 — WHERE A VALUE PRECONDITION'S FAILURE IS RECORDED INSTEAD OF
    /// RAISED, so the SAME call's effects are still attributed and an independent effect
    /// violation at that call is still reported.
    ///
    /// The two verdicts are independent: a precondition is a proof obligation over the
    /// KB, an effect is a row the body incurs, and the call's effects are read off the
    /// callee's DECLARATION and do not depend on the precondition holding. Raising the
    /// precondition as an `Err` from [`check_apply_iter`] aborts the call's typing before
    /// the effect row is built, so the body result is `Err`, `check_operation_bodies`
    /// takes its error-only arm, and the op-boundary coverage check never runs — one
    /// diagnostic reported, the other silently dropped, and the survivor looks complete.
    ///
    /// `None` IS THE DEFAULT AND MEANS "RAISE", which is what makes this safe rather than
    /// a silent swallow: a sink exists only where a DRAINER installed one
    /// ([`Self::collect_deferred_preconditions`], called once per operation body by
    /// `check_operation_bodies`, drained by it in both arms). Every other entry into the
    /// typer — the rule-body dispatch walk, the public `type_check_expr` shim — carries
    /// `None` and keeps the hard `Err` it has always had. The gate is therefore the
    /// consumer's own question ("is anyone going to report this?"), not a re-reading of
    /// some neighbouring predicate.
    ///
    /// SHARED ACROSS EVERY CLONE (`Rc<RefCell<…>>`), AND THE `Err` ARM IS WHY. A by-value
    /// channel could only be read back out of the walk's `TypeResult` — and a body that
    /// failed to type produces no `TypeResult` at all, so the precondition it recorded on
    /// the way in would have nowhere to come from. A shared sink is reachable from the
    /// operation's OWN handle whatever the walk returned, which is what lets the drain
    /// sit after the match instead of inside its `Ok` arm.
    ///
    /// THE OTHER REASON THIS CARRIER LOOKED NECESSARY IS NOT ONE, and it is recorded
    /// because it is the natural guess: the build frames return the FRAME's env, so an
    /// argument's own `TypingEnv` is dropped (which is why the neighbouring
    /// [`Self::diagnostics`] channel was not reused). MEASURED, a by-value field survives
    /// that anyway — a Visit that binds nothing hands its children the same
    /// `Rc<TypingEnv>`, so an argument's write already lands in the allocation the parent
    /// clones out. `wi_jm7a8_precondition_effect_test`'s header carries the three
    /// back-outs and which fixture each one reds.
    ///
    /// Op-scoped by construction: `check_operation_bodies` builds a fresh `TypingEnv` per
    /// body, so nothing leaks between operations.
    deferred_preconditions: Option<Rc<std::cell::RefCell<Vec<TypeError>>>>,
}

impl TypingEnv {
    pub fn empty() -> Self {
        Self {
            var_bindings: HashMap::new(),
            receiver_aliases: HashMap::new(),
            type_denotations: HashMap::new(),
            param_rigids: Rc::new(Vec::new()),
            sort_rigid_len: 0,
            local_resources: Vec::new(),
            enclosing_sort: None,
            rule_scope: None,
            rule_declared_specs: Rc::new(Vec::new()),
            enclosing_chain: DictChain::empty(),
            enclosing_op_chain: None,
            op_requires: Rc::new(Vec::new()),
            enclosing_op: None,
            debruijn_types: Rc::new(HashMap::new()),
            rule_body_dispatch: false,
            diagnostics: Vec::new(),
            // WI-20260830-JM7A8: OFF by default — see the field doc. Only a caller that
            // drains installs a sink.
            deferred_preconditions: None,
        }
    }

    /// WI-20260830-JM7A8 — install this body's sink for deferred value-precondition
    /// failures. The caller MUST drain it ([`Self::take_deferred_preconditions`]) on
    /// every path out of the body check, including the one where the body failed to type
    /// for an unrelated reason.
    ///
    /// `pub(crate)`, WITH THE REST OF `TypingEnv` PUBLIC, because installing without
    /// draining is the one way to lose a diagnostic here and there is no compile-time
    /// guard against it (review-found). Keeping the pair inside the crate bounds the
    /// obligation to the one caller that owns it — `check_operation_bodies` — instead of
    /// resting it on a doc contract an out-of-crate caller never reads. Nothing outside
    /// `kb::typing` calls either half; the public typer entries (`type_check_expr`,
    /// `type_check_node`) build envs with no sink and keep the hard `Err`.
    pub(crate) fn collect_deferred_preconditions(&mut self) {
        self.deferred_preconditions = Some(Rc::new(std::cell::RefCell::new(Vec::new())));
    }

    /// WI-20260830-JM7A8 — hand a precondition failure to this body's sink. Returns
    /// `None` when the sink took it (the caller continues, so the call's effects are
    /// still attributed) and hands the error BACK when there is no sink, so the only way
    /// to lose one is to install a sink and not drain it.
    pub(super) fn defer_precondition(&self, err: TypeError) -> Option<TypeError> {
        match &self.deferred_preconditions {
            Some(sink) => {
                sink.borrow_mut().push(err);
                None
            }
            None => Some(err),
        }
    }

    /// WI-20260830-JM7A8 — take what this body deferred, leaving the sink empty.
    pub(crate) fn take_deferred_preconditions(&self) -> Vec<TypeError> {
        match &self.deferred_preconditions {
            Some(sink) => std::mem::take(&mut *sink.borrow_mut()),
            None => Vec::new(),
        }
    }

    /// WI-557: mark this env as the rule-body dot-dispatch context (see the
    /// `rule_body_dispatch` field doc). Called once by `type_rule_bodies`;
    /// the flag rides every env clone from there to `check_apply_iter`.
    pub fn mark_rule_body_dispatch(&mut self) {
        self.rule_body_dispatch = true;
    }

    /// WI-557: is this a rule-body dot-dispatch walk? When true, the WI-539
    /// value-precondition `requires`-check is skipped (a rule body is relational,
    /// not an imperative call site over Γ).
    pub(super) fn in_rule_body(&self) -> bool {
        self.rule_body_dispatch
    }

    /// WI-562 / WI-822 LEG 1: install the enclosing OPERATION — its own op-scoped
    /// `requires` chain (see [`Self::op_requires`]) and, when it declares one, the
    /// composed frame chain [`op_dict_entries`] gives it (the sort's slots then its
    /// own). ONE setter for both, because the two must describe the same operation:
    /// the coverage LICENCE (`op_requires`) and the frame SLOT the licence may now
    /// defer to are two readings of one clause, and taking them from different
    /// operations is the drift this call shape forbids.
    ///
    /// Must run AFTER [`Self::set_enclosing_sort`], which installs the sort half.
    pub fn set_enclosing_op(&mut self, kb: &mut KnowledgeBase, op_sym: Symbol) {
        self.enclosing_op = Some(op_sym);
        // Proposal 066 §7: the body's sort half is the chain of the provision whose
        // `where` block it is written in — its conditions and no other provision's — or
        // the sort-level chain outside every block.
        if let Some(sort) = self.enclosing_sort {
            let p = op_owner_provision(kb, op_sym);
            self.enclosing_chain = provider_dict_entries(kb, sort, p);
        }
        // The LICENCE reads every clause the operation wrote — [`op_requires_covers`]
        // walks `required_sort`s looking for spec reachability, and a value
        // precondition simply reaches nothing. The SLOTS read only the spec ones
        // ([`op_requires_chain_rc`]). Two questions, two lists, deliberately: taking
        // the licence from the slot list would silently narrow what WI-562 licenses.
        self.op_requires = Rc::new(op_requires_entries(kb, op_sym));
        if op_requires_chain_rc(kb, op_sym).is_empty() {
            // The sort chain `set_enclosing_sort` installed IS the frame chain here,
            // and it is literally the same value `op_dict_entries` would return.
            self.enclosing_op_chain = None;
            return;
        }
        self.enclosing_op_chain = Some(op_dict_entries(kb, op_sym));
    }

    pub(super) fn op_requires(&self) -> &[RequiresEntry] {
        &self.op_requires
    }

    /// WI-822 LEG 1 — the operation whose body is being checked (see the field doc).
    pub(super) fn enclosing_op(&self) -> Option<Symbol> {
        self.enclosing_op
    }

    /// WI-282: install the enclosing rule's De Bruijn var → type map (see the
    /// field doc). `Rc` clone is a refcount bump.
    pub fn set_debruijn_types(&mut self, types: Rc<HashMap<u32, Value>>) {
        self.debruijn_types = types;
    }

    /// WI-282: the type a rule body's `Expr::Var(Var::DeBruijn(idx))` was
    /// constrained to by the goals, or `None` for a genuinely-free body var.
    pub(super) fn lookup_debruijn(&self, idx: u32) -> Option<Value> {
        self.debruijn_types.get(&idx).cloned()
    }

    /// WI-424/WI-942 — install the body's param-var → rigid map (see the
    /// [`Self::param_rigids`] field doc). `sort_rigid_len` is how many leading
    /// entries belong to the enclosing SORT; the rest are the operation's own.
    pub fn set_param_rigids(&mut self, rigids: Rc<Vec<(VarId, TermId)>>, sort_rigid_len: usize) {
        debug_assert!(
            sort_rigid_len <= rigids.len(),
            "sort prefix longer than the list"
        );
        self.param_rigids = rigids;
        self.sort_rigid_len = sort_rigid_len;
    }

    /// EVERY type param in scope for this body — the bridge every σ-class
    /// comparison must use, since an op-declared param is as much a parameter as
    /// a sort-declared one (§5.2: "both scopes, one list").
    pub(super) fn param_rigids(&self) -> &[(VarId, TermId)] {
        &self.param_rigids
    }

    /// The ENCLOSING SORT's params alone — "this instance's parameters". The
    /// same-sort sibling-call seeding wants exactly these; see the field doc.
    pub(super) fn enclosing_instance_param_rigids(&self) -> &[(VarId, TermId)] {
        &self.param_rigids[..self.sort_rigid_len]
    }

    /// Set the sort whose body is currently being type-checked and
    /// snapshot its **direct** `requires` chain (cheap-ish: one
    /// `SortRequiresInfo` scan via `direct_requires_chain`). `check_apply`
    /// reads the cached chain per spec-op dispatch without re-walking
    /// facts.
    ///
    /// WI-239: direct (not flat-transitive) so the slot indices
    /// `find_requires_slot` / `build_dep_projection` / `FromScope`
    /// produce line up with `synth_req_names` (also direct). A transitive
    /// spec reached through a direct require is located by
    /// `find_requires_location` instead.
    /// WI-869 / proposal 066 §7: the snapshot is a DICTIONARY chain
    /// (`provider_dict_chain`), not the declared `requires` chain — here the SORT-LEVEL
    /// one; [`Self::set_enclosing_op`] replaces it with the chain of the provision the
    /// operation is written in, whose `:- goals` are the evidence its member bodies
    /// dispatch through (`Pair.compare` reads `WeakOrd[A]` from a slot only `provides
    /// WeakOrd[Pair] :- WeakOrd[A], …` puts there). Identical for a sort with no
    /// conditional provision.
    ///
    /// WI-822 LEG 1: this installs the SORT half only. [`Self::set_enclosing_op`]
    /// runs next and appends the operation's own `requires` when it writes any, so
    /// the two calls must stay in that order — the op setter composes ONTO what this
    /// one left.
    pub fn set_enclosing_sort(&mut self, kb: &mut KnowledgeBase, sort: Option<Symbol>) {
        self.enclosing_sort = sort;
        // Proposal 066 §7: the SORT-LEVEL chain until [`Self::set_enclosing_op`] names
        // the provision the body is a member of — the safe default, so a body checked
        // with a sort and no operation reads no provision's conditions.
        self.enclosing_chain = match sort {
            Some(s) => provider_dict_entries(kb, s, None),
            None => DictChain::empty(),
        };
    }

    pub fn enclosing_sort(&self) -> Option<Symbol> {
        self.enclosing_sort
    }

    /// WI-977 — THE SCOPE THE CODE BEING CHECKED IS WRITTEN IN, for a diagnostic that
    /// must name it (§8.6) and for the `internal` visibility question that diagnostic
    /// reports. TWO contexts reach it today, each carrying its own answer:
    ///
    ///  * an OPERATION body — `enclosing_op`, the operation's own scope;
    ///  * a RULE body — `rule_scope`, the rule's `domain`;
    ///  * `None` everywhere else, which [`hidden_field_owner`] reads as the GLOBAL
    ///    scope — the scope a file's top-level declarations are written in.
    ///
    /// The `enclosing_sort` arm is a THIRD answer that nothing currently selects, and
    /// it is kept deliberately rather than as an oversight: `set_enclosing_sort` has
    /// one caller, the operation-body loop, which unconditionally calls
    /// `set_enclosing_op` twelve lines later, so `enclosing_op` is `Some` whenever
    /// `enclosing_sort` is. A future sweep that installs only the sort would then get
    /// the right granularity's nearest available answer instead of falling through to
    /// the global scope — but it would still be one scope OUT from where its code is
    /// written, which is the split this ticket closed. A sweep in that position should
    /// set its own scope, as `type_rule_bodies` does.
    ///
    /// Not `enclosing_sort` alone, which is one scope OUT of an operation body and
    /// made the typer disagree with the loader about the same code. MEASURED, one
    /// file, two rows: `unresolved name 'Nope' in scope 'wi977r.peek.Peeker.other'`
    /// from the loader (which reads `current_scope`, the operation's) beside
    /// `cannot be referenced from scope 'wi977r.peek.Peeker'` from here — one
    /// question, two answers, which is the split this ticket exists to close.
    ///
    /// THE RULE-BODY ARM IS NOT COSMETIC, and assuming it was cost a regression:
    /// `set_enclosing_sort` has ONE caller, the operation-body loop, so before
    /// `rule_scope` existed EVERY rule body answered `None` here — not just top-level
    /// code, as this doc then claimed. With [`hidden_field_owner`] reading `None` as
    /// the global scope, a rule written INSIDE the declaring sort and projecting its
    /// own `internal` field became a hard load error
    /// (`'x' is internal to '…Point' and cannot be referenced from scope '<global>'`).
    /// The whole workspace stayed green: no fixture projected an internal field from a
    /// rule body until `a_rule_inside_the_declaring_sort_sees_its_internal_field`.
    ///
    /// THE TWO ARMS CHANGE THE VISIBILITY VERDICT DIFFERENTLY, and only one of them is
    /// a narrowing. For an OPERATION body this is purely a rename: `scan_operation_params`
    /// installs an `is_enclosing` link from each op scope to its declaring scope, so an
    /// op scope's chain is a strict SUPERSET of its sort's and
    /// [`crate::intern::SymbolTable::internal_visible_from`] cannot hide a name that was
    /// visible before. For a RULE body it is a WIDENING — from no check at all — so
    /// programs that loaded before can now be refused; that is the §8.6 rule finally
    /// being enforced there, pinned by
    /// `a_rule_outside_the_declaring_sort_is_refused_naming_the_rules_scope`, and its
    /// in-scope counterpart by `a_rule_inside_the_declaring_sort_sees_its_internal_field`.
    /// Migration risk measured: one `internal entity` exists across `stdlib/`,
    /// `examples/` and `anthill-todo/`, projected only inside its own sort.
    pub(super) fn referencing_scope(&self) -> Option<Symbol> {
        self.enclosing_op
            .or(self.rule_scope)
            .or(self.enclosing_sort)
    }

    /// WI-977 — see [`Self::rule_scope`]. Set once per rule by the rule-body sweep.
    pub(super) fn set_rule_scope(&mut self, domain: Symbol) {
        self.rule_scope = Some(domain);
    }

    /// WI-20260922-0DK3H — see [`Self::rule_declared_specs`]. Set once per rule by the
    /// rule-body sweep, which is the one place holding the `RuleId` the brackets are
    /// collected from.
    pub(super) fn set_rule_declared_specs(&mut self, specs: Vec<Value>) {
        self.rule_declared_specs = Rc::new(specs);
    }

    pub(super) fn rule_declared_specs(&self) -> &[Value] {
        &self.rule_declared_specs
    }

    /// The enclosing SORT's slots alone.
    ///
    /// WI-822 LEG 1 — THE SORT HALF, and the narrowing is the ticket's central
    /// decision rather than an omission. Every reader of this list decides whether a
    /// body call DEFERS to a frame slot instead of being served by VALUE-DIRECTED
    /// dispatch, and for an op-scoped requirement value-direction is the right
    /// channel and demonstrably works: WI-817's relay chain computes its 551 with no
    /// dictionary anywhere, and `Holder.probe(leaf())` called straight from the HOST
    /// — where no call site exists to build one, and a stand-in rooted at the parent
    /// sort would mis-dispatch — can be served by nothing else. Widening this to the
    /// composed chain was MEASURED: 30 tests across wi842/wi843/wi855/wi876/wi886/
    /// wi869 flipped from a working value-directed dispatch to an unbound slot.
    ///
    /// The op half is consulted at exactly one place, [`op_scoped_defer_location`],
    /// on the one route value-direction CANNOT serve — see there.
    pub(super) fn enclosing_requires(&self) -> &[RequiresEntry] {
        self.enclosing_chain.entries()
    }

    /// WI-1033 — the enclosing SORT's chain AS A [`DictChain`]. A chain's slot INDICES
    /// and its slot NAMES must come from one value or they drift, which is why a reader
    /// that needs both takes this rather than [`Self::enclosing_requires`]'s entries.
    ///
    /// WI-20260921-159S9 — NO LONGER THE INSTANCE-DICTIONARY BUILDERS' CHAIN. They take
    /// [`Self::enclosing_frame_chain`] now, so an op-scoped slot forwards a dictionary
    /// too; this remains the SORT half for the readers that genuinely mean the sort's
    /// own — the eta same-sort test, the `__req_self` capture, and `serves`.
    pub(super) fn enclosing_dict_chain(&self) -> &DictChain {
        &self.enclosing_chain
    }

    /// WI-822 LEG 1 — the enclosing OPERATION's frame chain: the sort's slots then its
    /// own. Identical to [`Self::enclosing_dict_chain`] for an operation that writes no
    /// `requires`, which is nearly all of them.
    ///
    /// WI-20260921-159S9 — **AND THIS IS NOW THE INSTANCE-DICTIONARY BUILDERS' CHAIN
    /// TOO.** The `enclosing_op_chain` field doc used to name two readers and say the
    /// builders must NOT be a third; that restriction is lifted, and the field doc on
    /// [`Self::enclosing_chain`] records what replaced its premise. The DEFER decision
    /// ([`Self::enclosing_requires`]) is still the sort half and is a different question.
    pub(super) fn enclosing_frame_chain(&self) -> &DictChain {
        self.enclosing_op_chain
            .as_ref()
            .unwrap_or(&self.enclosing_chain)
    }

    /// WI-20260918-CKD4J — the operation's own `requires`, as the resolver's
    /// [`ResolutionScope::sub_goal_requires`]. Their `FromScope` index is offset by
    /// [`Self::enclosing_requires`]'s length, which names the right frame slot only
    /// because that sort half IS the frame chain's prefix — asserted, not assumed.
    pub(super) fn sub_goal_requires(&self) -> &[RequiresEntry] {
        let frame = self.enclosing_frame_chain();
        debug_assert_eq!(
            frame.sort_len(),
            self.enclosing_requires().len(),
            "CKD4J: the frame chain's sort half must be the enclosing sort's chain, or \
             an op-half `FromScope` index names the wrong slot"
        );
        frame.op_entries()
    }

    pub fn bind_var(&mut self, name: Symbol, ty: Value) {
        self.var_bindings.insert(name, ty);
    }

    pub fn lookup_var(&self, name: Symbol) -> Option<Value> {
        self.var_bindings.get(&name).cloned()
    }

    /// WI-20260904-50B2K part (c), step 2 — every TYPE this environment binds a name to.
    /// The one reader is [`WalkSolutions::generalize_for_arrow`]'s side condition, which
    /// must not quantify a variable the environment still holds.
    ///
    /// **BOTH MAPS.** An environment holds types in two: `var_bindings` for a lexical name
    /// and `debruijn_types` for a rule body's `?x`. The first cut yielded only the first,
    /// which made a SOUNDNESS side condition a census of half its subject — and a
    /// half-census is exactly how the first version of this guard failed (it read the arrow
    /// and not the environment at all, and quantified an enclosing lambda's binder).
    /// /code-review found it. No witness: today's rule-body var types are inert
    /// placeholders, so nothing in the corpus separates one map from two.
    pub(crate) fn bound_types(&self) -> impl Iterator<Item = &Value> {
        self.var_bindings
            .values()
            .chain(self.debruijn_types.values())
    }

    /// WI-400 increment C: record that `name` aliases the canonical receiver `path`
    /// (`let y = z` ⟹ `name = y`, `path = [z]`). The path's head is de-aliased first, so
    /// the stored path is fully canonical (transitive `let w = y` resolves to `y`'s
    /// target). A path that is already the name itself (`let y = y`, degenerate) records
    /// nothing — and **clears** any stale alias under `name`, since a re-bind of a
    /// previously-aliased name must not keep pointing at the old receiver (soundness: a
    /// shadowing `let y = …` rebinds `y`'s identity).
    pub(super) fn bind_receiver_alias(&mut self, name: Symbol, path: Vec<Symbol>) {
        let canon = self.canonicalize_receiver_path(path);
        if canon.first() == Some(&name) && canon.len() == 1 {
            self.receiver_aliases.remove(&name);
            return;
        }
        self.receiver_aliases.insert(name, canon);
    }

    /// WI-400 increment C: drop any receiver alias under `name`. Called when `name` is
    /// re-bound to an UNSTABLE value (`let y = f()`): the old alias is stale and keeping it
    /// would canonicalize `y`'s projection to the previous receiver — a false accept.
    pub(super) fn clear_receiver_alias(&mut self, name: Symbol) {
        self.receiver_aliases.remove(&name);
    }

    /// WI-400 increment C: rewrite a receiver path's HEAD through the alias map (the head
    /// is replaced by its canonical path, the trailing field segments preserved):
    /// `[y, f]` with `y → [s, provider]` ⟹ `[s, provider, f]`. One hop suffices because
    /// stored aliases are already de-aliased at record time.
    pub(super) fn canonicalize_receiver_path(&self, path: Vec<Symbol>) -> Vec<Symbol> {
        let Some((head, rest)) = path.split_first() else {
            return path;
        };
        match self.receiver_aliases.get(head) {
            Some(canon_head) => {
                let mut out = canon_head.clone();
                out.extend_from_slice(rest);
                out
            }
            None => path,
        }
    }

    pub(super) fn receiver_aliases(&self) -> &HashMap<Symbol, Vec<Symbol>> {
        &self.receiver_aliases
    }

    /// WI-20260824-PAPX0: record that `name` denotes the type `node` names.
    pub(super) fn bind_type_denotation(&mut self, name: Symbol, node: Rc<NodeOccurrence>) {
        self.type_denotations.insert(name, node);
    }

    /// WI-20260824-PAPX0: drop any denotation under `name`. Called when `name` is
    /// re-bound to anything that is NOT a written type, for the same soundness
    /// reason [`Self::clear_receiver_alias`] states: a shadowing `let t = …`
    /// rebinds `t`'s identity, and keeping the outer denotation would resolve
    /// `t.m` in a sort the inner `t` has nothing to do with — a false accept,
    /// not a missed one.
    pub(super) fn clear_type_denotation(&mut self, name: Symbol) {
        self.type_denotations.remove(&name);
    }

    /// WI-20260824-PAPX0: the `Expr::TypeValue` occurrence `name` denotes, if any.
    pub(super) fn type_denotation(&self, name: Symbol) -> Option<&Rc<NodeOccurrence>> {
        self.type_denotations.get(&name)
    }

    pub fn declare_local_resource(&mut self, name: Symbol) {
        self.local_resources.push(name);
    }

    pub fn is_local_resource(&self, name: Symbol) -> bool {
        self.local_resources.iter().any(|r| *r == name)
    }
}

// ── Proposal 050 (WI-537): FlowEnv — the local logical storage Γ ────
//
// Γ, the flow-sensitive logical environment: the facts that hold at a program
// point. This is LOGICAL storage (proved / refuted by the SLD resolver) — a
// DIFFERENT thing from `TypingEnv` (a set of types, driven by type deduction),
// because type deduction is not logical deduction. The two are bundled by
// `Env` and forked together with control flow, but kept distinct concerns.
//
// Backed by a discrimination tree — the same structure the KB indexes facts
// with — so Γ membership is a structural query in the same vocabulary a `rule`
// body / 048 guard speaks, and a fact over an op parameter (which skolemizes to
// `Var::Rigid`) indexes as a `RigidVar` constant (WI-537's `ViewHead` refactor)
// rather than collapsing to the un-insertable `Opaque`.
#[derive(Clone)]
pub struct FlowEnv {
    /// Γ as a discrimination-tree fact index. Leaf = the fact `Value` itself,
    /// so a membership match resolves the fact head faithfully (the WI-348
    /// named-order path via `query_resolved_value`). `Rc`: an unchanged Γ
    /// clones as a refcount bump on the per-Visit `Env` clone; `assume` is
    /// copy-on-write — `Rc::make_mut` clones the (shallow) tree only at a fork.
    pub(super) facts: Rc<SubstTree<Value>>,
    /// The EIGENVARIABLES of the proof this environment belongs to — the opaque
    /// constants `proof_verify`'s contract σ substituted for the operation's
    /// parameters, so that discharging the contract about them discharges it for every
    /// input.
    ///
    /// HERE, NOT ON THE KB, and the placement is the point. These are per-proof and
    /// dead the moment the proof returns; they have exactly `gamma`'s scope, and
    /// `ResolveConfig::gamma`'s own doc states that criterion — "`None` for every
    /// ordinary resolution … global to one resolve call, so it rides the config". On
    /// the KB the set grew for the KB's lifetime, forced a `layer.rs` monotone-vs-scoped
    /// decision that need not exist, and — because the typer calls `prove_from_gamma`
    /// for every `if`/`match` guard discharge, not only for contract proofs — made
    /// every later Γ-bridge goal pay a skolem walk for constants no contract had put
    /// there. Riding the env makes "empty outside a contract proof" structural rather
    /// than an argument about symbol uniqueness.
    ///
    /// `Rc` for the same reason `facts` is: an unchanged env clones as a refcount bump.
    pub(super) skolems: Rc<std::collections::HashSet<Symbol>>,
}

impl FlowEnv {
    /// Γ₀ — the empty seed at body entry.
    pub fn empty() -> Self {
        FlowEnv {
            facts: Rc::new(SubstTree::new()),
            skolems: Rc::new(std::collections::HashSet::new()),
        }
    }

    /// Record `sym` as one of this proof's eigenvariables — see [`Self::skolems`].
    /// Copy-on-write, like [`Self::assume`].
    pub fn with_skolem(&self, sym: Symbol) -> FlowEnv {
        let mut next = self.clone();
        Rc::make_mut(&mut next.skolems).insert(sym);
        next
    }

    /// This env's eigenvariables, for seeding [`crate::kb::resolve::ResolveConfig`].
    pub(crate) fn skolems(&self) -> Rc<std::collections::HashSet<Symbol>> {
        Rc::clone(&self.skolems)
    }

    /// No facts yet (distinguishes the Γ₀ seed from a narrowed branch env).
    ///
    /// Deliberately says nothing about [`Self::skolems`]: this asks whether the flow
    /// has NARROWED anything, and a contract proof's eigenvariables are a property of
    /// the goal's vocabulary, not a fact anyone assumed.
    pub fn is_empty(&self) -> bool {
        self.facts.is_empty()
    }

    /// Extend Γ with one more known fact, returning the narrowed env (the `if`
    /// fork puts the branch condition / its negation here). Copy-on-write
    /// path-copy: `Rc::make_mut` clones only the nodes along the inserted path —
    /// the discrim tree is persistent ([`crate::kb::discrim`]) — sharing the rest of
    /// Γ with the parent.
    ///
    /// EVERY fact is normalized to the Γ vocabulary ([`goal_form`]) on the way
    /// in — WI-756, and the reason this takes `&mut KnowledgeBase`. A producer
    /// hands over a raw source occurrence, in which a nullary constructor and a
    /// binder are the same `var_ref` shape; a consumer's goal has crossed the
    /// goal-lowering boundary, where they are not. Γ is matched STRUCTURALLY, so
    /// the two must be in one form or a fact simply never discharges its goal.
    ///
    /// A fact the discrim tree cannot index — a raw `if`-condition occurrence
    /// with an elaborated / `Opaque` (or functor-less tuple/unit) head ANYWHERE
    /// in its structure, not just at the top — is NOT inserted, and that loses
    /// nothing: it could never unify with a clean goal-shaped membership query
    /// (the goal heads as a `Functor`), so it could never discharge anything.
    /// We skip it here (`view_is_indexable`) rather than weaken
    /// `insert_pattern`'s rule-head invariant (it rightly panics on such heads).
    ///
    /// WI-814 SHRANK the skipped set rather than changing this rule: an `if` /
    /// `let` / `lambda` / `match` condition (and the patterns they bind) now
    /// heads as a `Functor`, so such a fact is INSERTED where it used to be
    /// dropped — and the losslessness argument above is what says that is safe,
    /// since a goal of the same shape now heads as a `Functor` too and can
    /// actually match it. Γ grows in exchange; the dedup probe below is what
    /// keeps that from compounding.
    pub fn assume(&self, kb: &mut KnowledgeBase, fact: Value) -> FlowEnv {
        // HERE rather than at each producer, so the two sides share the vocabulary
        // by construction: `if` / `match` / `let` / an in-body proof's conclusion
        // all arrive through this one door, and so does a NEGATED `if` condition
        // (`negate_goal` rebuilds from the raw children — normalized on the way in).
        let fact = goal_form(kb, fact);
        if !crate::kb::discrim::view_is_indexable(kb, &fact) {
            return self.clone();
        }
        // Γ is a SET: re-assuming a structurally-identical fact adds nothing, so
        // skip both the insert and the `Rc::make_mut` path-copy. The `is_empty`
        // guard skips the membership probe outright for the common shallow-`if`
        // case (Γ₀ has nothing to match against). This keeps a deep chain of
        // *identical* branch conditions (`if true then … else (if true …)`)
        // O(depth): without dedup the repeated fact piles up duplicate leaves at
        // one terminal node and each path-copy clones that growing `leaves` Vec
        // → O(depth²). A *distinct* fact per level still grows Γ by one (the
        // genuine flow-sensitive cost); only exact repeats are elided.
        if !self.facts.is_empty()
            && self
                .facts
                .query_raw(kb, &fact)
                .iter()
                .any(|(stored, _)| views_structurally_equal(kb, stored, &fact))
        {
            return self.clone();
        }
        let mut next = self.clone();
        Rc::make_mut(&mut next.facts).insert_pattern(kb, &fact, fact.clone());
        next
    }

    /// The Γ index, to hand to the resolver as its [`ResolveConfig::gamma`]
    /// overlay (the bridge below). `Rc` clone — a refcount bump.
    pub(super) fn index(&self) -> Rc<SubstTree<Value>> {
        Rc::clone(&self.facts)
    }
}

// ── Proposal 050 (WI-537): Env — the threaded carrier ──────────────
//
// The typer threads ONE `Env` bundling the two distinct environments:
// `TypingEnv` (a set of types — type deduction) and `FlowEnv` (Γ, the local
// logical storage — logical deduction). They fork together with control flow
// but stay separate concerns. `Env` is cheap to clone (two `Rc` bumps) so it
// is threaded by value; `Deref<Target = TypingEnv>` keeps every existing
// type-deduction access (`env.var_binding(..)`, and `check_apply(kb, &env, ..)`
// via deref coercion) untouched, while the new logical-storage access is the
// explicit `env.flow`.
#[derive(Clone)]
pub struct Env {
    pub types: Rc<TypingEnv>,
    pub flow: FlowEnv,
}

impl Env {
    /// Seed at the typer boundary: a borrowed `TypingEnv` + the Γ₀ its entry point
    /// supplies.
    ///
    /// WI-K88TN made Γ₀ a PARAMETER rather than always [`FlowEnv::empty`]. Proposal 050
    /// reads a precondition as a Hoare ASSUMPTION inside the body, so an operation's own
    /// value `requires` is knowledge its body may use; [`op_requires_gamma`] builds that
    /// seed and `check_operation_bodies` is its one supplier. Every other entry passes
    /// the empty Γ₀ — a rule body and a nested type-check have no enclosing contract to
    /// assume — and passes it EXPLICITLY, so a new entry point has to say which it means
    /// instead of inheriting an invisible default.
    pub(super) fn with_gamma(types: &TypingEnv, flow: FlowEnv) -> Self {
        Env {
            types: Rc::new(types.clone()),
            flow,
        }
    }

    /// Re-wrap with an extended type context (entering a let / lambda / match
    /// arm), carrying the SAME Γ forward (the binding narrows types, not Γ).
    pub(super) fn with_types(&self, types: TypingEnv) -> Self {
        Env {
            types: Rc::new(types),
            flow: self.flow.clone(),
        }
    }

    /// Re-wrap with a narrowed Γ (the `if` fork), sharing the SAME types.
    pub(super) fn with_flow(&self, flow: FlowEnv) -> Self {
        Env {
            types: Rc::clone(&self.types),
            flow,
        }
    }
}

impl std::ops::Deref for Env {
    type Target = TypingEnv;
    fn deref(&self) -> &TypingEnv {
        &self.types
    }
}

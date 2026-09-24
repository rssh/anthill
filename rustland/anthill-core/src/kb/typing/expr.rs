//! Typer entry points (`type_check_expr`, `type_check_node*`), the iterative typer's
//! work-stack vocabulary (`TypeWorkOp`, `TypeBuildFrame`), and bare-reference typing.

use super::*;

// ── Iterative-typer work ops ───────────────────────────────────
//
// Let / Match / Lambda body recursion is the dominant deep-nesting
// source on typing_pass_spec.anthill. Convert just those three
// recursion paths to a Visit/Build work-stack walker so chained
// `let A = …; let B = …; …` and nested matches stay flat on the
// host stack. Other variants (Apply, Constructor, If, ListLit,
// SetLit, TupleLit) keep their existing `check_*` helpers; their
// recursion is bounded by argument count / branch count rather than
// source nesting depth.

/// WI-1104 — is the node at this Visit a rule-body GOAL, or a VALUE?
///
/// The typer's half of [`BodyPos`], and only the half it can act on: the rule-body walk
/// ([`dispatch_calls_in_occ`]) owns goal DESCENT and hands the typer ONE node at a time,
/// so within a `type_check_node` walk the only goal is the node handed over — every
/// sub-expression beneath it is data.
///
/// **It rides the `Visit` frame rather than the [`TypingEnv`], and that is the whole
/// point.** [`TypingEnv::rule_body_dispatch`] is a PER-RULE flag: it is set once per rule
/// and inherited by every env clone, so a call NESTED inside a goal reads it exactly as
/// the goal itself does. WI-1100 scoped the functional-relation arity + 1 by that flag,
/// which admitted the tolerance in VALUE position too — MEASURED, `rule r(?y) :-
/// leaf().describe(?d), ?y = concat("a", "b", "c")` loaded clean while the same
/// expression in an operation body was refused. This rides the frame beside `expected`
/// and `fuel`, which are per-node for the same reason.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum NodePos {
    /// The atom [`dispatch_calls_in_occ`] handed over at [`BodyPos::Goal`] /
    /// [`BodyPos::GoalTuple`] — and whatever REPLACES it while it is typed (a `@[simp]`
    /// fire's RHS, the call a dot lowers to, a WI-411 spec-op redirect), since a rewrite
    /// of the goal is still the goal. Carried only by the three build frames that can BE
    /// the handed-over atom or produce its replacement (`Apply` / `ApplyHints` /
    /// `DotApply`); no other form reaches the typer at a goal position
    /// ([`call_dispatch_shape`] admits `Expr::Apply` and `Expr::DotApply` alone).
    RuleBodyGoal,
    /// Everything else: an operation body, an entity fact, a standalone typer entry —
    /// and every argument of a goal, however deep.
    Value,
}

pub(super) enum TypeWorkOp {
    /// `expected` is the WI-270 top-down type hint — the caller's
    /// expected type for the value at this position. It seeds Apply /
    /// Constructor return-type unification, threads through Let /
    /// Match / If branches, and decomposes through Lambda arrows.
    /// `None` at the root Visit and at positions where no hint is
    /// available (leaf args, scrutinees, conditions).
    Visit {
        occ: Rc<NodeOccurrence>,
        env: Env,
        expected: Option<Value>,
        /// WI-283: remaining `@[simp]` fire-fuel for this node. Inherited
        /// unchanged by child Visits; spent (`fuel - 1`) only when an
        /// Apply/Constructor fires and re-`Visit`s its synthesized RHS.
        /// Bounds the fire chain (→ termination) without host recursion.
        fuel: usize,
        /// WI-1104: where this node sits in its rule body. [`NodePos::Value`] for every
        /// CHILD visit ([`push_visit`] supplies it), inherited only by a re-Visit that
        /// REPLACES the node ([`push_visit_at`]).
        pos: NodePos,
    },
    Build(TypeBuildFrame),
}

/// Push a node Visit preceded *underneath* by a [`TypeBuildFrame::Stamp`]
/// frame (WI-284). The Stamp sits just below the Visit on the work
/// stack, so it pops only after the Visit and all of its sub-work have
/// produced this node's `TypeResult` — at which point it records the
/// inferred type onto that result's `node` (WI-283: the *resulting*,
/// possibly-rewritten occurrence, not the input — identical until a
/// `@[simp]` rule fires). Routing every node visit through here stamps
/// each typed occurrence exactly once, uniformly across all iterative
/// arms (Apply / Constructor / Let / Match / Lambda / If / collection
/// literals — every form is a work-stack Build frame after WI-285, so
/// there is no recursive `type_check_node` re-entry).
///
/// WI-1104: this is the CHILD push — the node visited here is a sub-expression of the
/// node that pushes it, so it is [`NodePos::Value`] by construction. A push that
/// REPLACES a node (a `@[simp]` fire's RHS, a dot's lowered call) keeps the replaced
/// node's position and goes through [`push_visit_at`].
pub(super) fn push_visit(
    work: &mut Vec<TypeWorkOp>,
    occ: Rc<NodeOccurrence>,
    env: Env,
    expected: Option<Value>,
    fuel: usize,
) {
    push_visit_at(work, occ, env, expected, fuel, NodePos::Value);
}

/// WI-1104: [`push_visit`] at an explicit [`NodePos`]. Two kinds of caller, and only
/// two: the typer's ENTRY (which is told the position by the rule-body walk) and a
/// re-Visit that REPLACES the node it was reached from, which inherits that node's
/// position because a rewrite of a goal is still the goal.
pub(super) fn push_visit_at(
    work: &mut Vec<TypeWorkOp>,
    occ: Rc<NodeOccurrence>,
    env: Env,
    expected: Option<Value>,
    fuel: usize,
    pos: NodePos,
) {
    work.push(TypeWorkOp::Build(TypeBuildFrame::Stamp));
    work.push(TypeWorkOp::Visit {
        occ,
        env,
        expected,
        fuel,
        pos,
    });
}

/// Push a Visit with no top-down hint. Used at positions where the
/// caller's expected doesn't bound the child's type — Apply / Ctor
/// args (constrained by op.params / entity_field_types), the
/// scrutinee of a Match (drives the branch envs but takes no hint
/// from outside), and the condition of an If (always `Bool`).
pub(super) fn push_visit_no_hint(
    work: &mut Vec<TypeWorkOp>,
    occ: Rc<NodeOccurrence>,
    env: Env,
    fuel: usize,
) {
    push_visit(work, occ, env, None, fuel);
}

// WI-258: env-carrying frames hold `Rc<TypingEnv>`. Sibling Visits
// share the same Rc; only the mutating sites (LetAfterValue body env,
// LambdaBody body env, MatchAfterScrutinee branch envs) clone the
// inner `TypingEnv` via `Rc::make_mut`. Saves N-1 HashMap clones per
// multi-arg call site on deep specs.
pub(super) enum TypeBuildFrame {
    /// All Apply args finished; drain N = `pos_count + named_keys.len()`
    /// results, hand them to `check_apply_iter` which runs the
    /// non-recursive subst / dispatch / classify logic. `expected`
    /// (WI-270) is unified with the op's return type before the
    /// unconstrained-param check so caller context flows into the seed.
    /// Proposal 055 — the drain frame for [`Expr::TypeValue`]. Carries no
    /// `expected`: a classified type value's DENOTATION is settled (the loader
    /// settled it), so this frame's only job is to check the type arguments and
    /// answer `Type`. Whether the enclosing position ACCEPTS a `Type` is the
    /// caller's ordinary unification, exactly as for any other result sort.
    TypeValue {
        occ: Rc<NodeOccurrence>,
        head: Symbol,
        pos_args: Vec<Rc<NodeOccurrence>>,
        named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
        env: Env,
    },
    Apply {
        occ: Rc<NodeOccurrence>,
        fn_sym: Symbol,
        pos_args: Vec<Rc<NodeOccurrence>>,
        named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
        env: Env,
        expected: Option<Value>,
        /// WI-283: fire-fuel inherited from this node's `Visit`; on a fire
        /// the RHS is re-`Visit`ed with `fuel - 1` (bounds the chain).
        fuel: usize,
        /// WI-793: results for arguments typed AHEAD of the others, keyed by their
        /// unified `pos_args ++ named_args` index — a projection receiver whose type
        /// the hints needed (see [`known_arg_types_and_staged`]). EMPTY for every
        /// ordinary call, in which case the results stack is drained in natural order
        /// exactly as before staging existed.
        staged_results: Vec<(usize, Result<TypeResult, TypeError>)>,
        /// WI-1104: this call's own [`NodePos`] — read by [`check_apply_iter`] (the
        /// functional-relation arity + 1 is legal at a rule-body GOAL and nowhere else)
        /// and inherited by the two re-Visits this frame can push.
        pos: NodePos,
    },
    /// WI-793: the staged half of an `Apply`. Reached once the projection-receiver
    /// arguments have been typed: it completes the param→argument-type map with their
    /// types, builds the hints for EVERY argument, then pushes the `Apply` frame and the
    /// Visits for the arguments not yet typed. Exists because an argument hint can depend
    /// on a SIBLING argument's type, which the single-phase "hint everything, then visit
    /// everything" order could not express.
    ApplyHints {
        occ: Rc<NodeOccurrence>,
        fn_sym: Symbol,
        pos_args: Vec<Rc<NodeOccurrence>>,
        named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
        env: Env,
        expected: Option<Value>,
        fuel: usize,
        /// Unified argument indices, ASCENDING — the order their results sit in on the
        /// results stack.
        staged: Vec<usize>,
        /// The callee's declared parameters. Non-empty whenever `staged` is (staging is
        /// keyed off them), carried so the hint pass need not look the operation up twice.
        op_params: Vec<(Symbol, Value)>,
        sort_app_hint: Option<Value>,
        /// What the no-typing readers already answered, to be completed with the staged
        /// results rather than recomputed.
        known: HashMap<Symbol, Value>,
        /// WI-1104: carried through to the [`TypeBuildFrame::Apply`] this frame pushes —
        /// staging changes WHEN the arguments are typed, never where the call sits.
        pos: NodePos,
    },
    /// All Constructor args finished; drain results and call
    /// `check_constructor_iter`. WI-270: `expected` flows into the
    /// parent-type unification so a caller-side `Option[Int]`
    /// constrains `some(?)`'s inferred T.
    Constructor {
        occ: Rc<NodeOccurrence>,
        ctor_sym: Symbol,
        pos_args: Vec<Rc<NodeOccurrence>>,
        named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
        env: Env,
        span: Option<Span>,
        expected: Option<Value>,
        /// WI-283: fire-fuel — see [`TypeBuildFrame::Apply::fuel`].
        fuel: usize,
    },
    /// WI-279: the DotApply RECEIVER finished (the only pre-typed child).
    /// Resolve `member` against the receiver's least sort (`min_sort`, read
    /// from the receiver child's result type), then synthesize the
    /// dispatched `Apply` from the RAW arg occurrences carried here and
    /// re-`Visit` it — so the produced call rides normal Apply typing +
    /// type-param inference + req_insertion. WI-443: the args are
    /// deliberately NOT pre-typed at this frame — a callback argument (a
    /// lambda) needs the callee's param-type hint, which exists only inside
    /// the synthesized call; pre-typing it hintless mis-fired dispatch
    /// (`gt` coherence on an untyped lambda param). No match ⇒ a
    /// `DotDispatchNoMatch` diagnostic at the dot span.
    DotApply {
        occ: Rc<NodeOccurrence>,
        member: Symbol,
        pos_args: Vec<Rc<NodeOccurrence>>,
        named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
        env: Env,
        expected: Option<Value>,
        /// WI-283: fire-fuel inherited from this node's `Visit`; spent
        /// (`fuel - 1`) on the re-`Visit` of the synthesized call.
        fuel: usize,
        /// WI-1104: this dot's own [`NodePos`], inherited by each of the three calls it
        /// can lower to (a fired dot rule, the dispatched method, a `field_access`) —
        /// `?x.describe(?r)` written as a rule-body goal IS that goal, so the
        /// functional-relation column reaching `check_apply_iter` through the lowering
        /// must arrive with the same position the qualified spelling does.
        pos: NodePos,
    },
    /// Value finished; compute the body's ext_env and schedule the
    /// body Visit, plus a `LetFinal` frame to combine results. If the
    /// value's TypeResult is `None`, the let propagates failure up
    /// without visiting the body (see WI-204 feedback — no fallbacks).
    /// `body_expected` is the let's own `expected` (the outer hint),
    /// passed forward to the body Visit per WI-270.
    LetAfterValue {
        occ: Rc<NodeOccurrence>,
        // WI-511: the let pattern occurrence, read occurrence-native by
        // `bind_and_label_pattern` / `extract_pattern_var_name`.
        pattern: Rc<NodeOccurrence>,
        annotation: Option<Value>,
        body_occ: Rc<NodeOccurrence>,
        body_expected: Option<Value>,
        /// WI-283: fire-fuel to propagate onto the body `Visit`.
        fuel: usize,
        /// WI-537: the let-site's Γ. The body's type context comes from the
        /// value result's `env` (a `TypingEnv`, no flow), so the enclosing flow
        /// is stashed here to rebuild the body's `Env` (a `let` extends types,
        /// not Γ — the body runs under the same flow as the let site).
        outer_flow: FlowEnv,
    },
    /// Body finished; merge `value_effects` (captured at
    /// `LetAfterValue` time so we didn't need to keep `value_r`
    /// alive — its `env` was moved into the body's ext_env, which is
    /// the whole point of WI-258's COW) with `body_r.effects` and
    /// return the let's TypeResult.
    LetFinal {
        occ: Rc<NodeOccurrence>,
        /// The let value's (possibly-rewritten) node, captured at
        /// `LetAfterValue` (its `TypeResult` is consumed there); paired
        /// with the body's node to reassemble the `Let` (WI-283).
        value_node: Rc<NodeOccurrence>,
        value_effects: Vec<Value>,
        /// WI-803: the binder pattern as `bind_and_label_pattern` returned it at
        /// `LetAfterValue` — relabelled, when it is a tuple binder list over a
        /// known named-tuple type. Carried rather than re-read off `occ`, which
        /// still holds the unlabelled written form.
        pattern: Rc<NodeOccurrence>,
    },
    /// Scrutinee finished; walk the branch patterns for coverage,
    /// compute each branch's env, schedule body Visits + a
    /// `MatchFinal` frame. `body_expected` flows to every branch body.
    MatchAfterScrutinee {
        occ: Rc<NodeOccurrence>,
        branches: Vec<MatchBranch>,
        outer_env: Env,
        body_expected: Option<Value>,
        /// WI-283: fire-fuel to propagate onto each branch-body `Visit`.
        fuel: usize,
    },
    /// All branch bodies finished; pop `branch_count` results, filter
    /// per-branch effects against each branch's local resources,
    /// emit non-exhaustiveness diagnostics, return the match's
    /// TypeResult.
    MatchFinal {
        occ: Rc<NodeOccurrence>,
        /// The scrutinee's (possibly-rewritten) node, captured at
        /// `MatchAfterScrutinee`; paired with the branch bodies to
        /// reassemble the `Match` (WI-283). Guards aren't typed/visited,
        /// so they're re-read from `occ` unchanged.
        scr_node: Rc<NodeOccurrence>,
        scr_effects: Vec<Value>,
        branch_envs: Vec<Env>,
        branch_count: usize,
        outer_env: Env,
        /// WI-342: the scrutinee type, carrier-agnostic (`Value`) — read for
        /// the exhaustiveness sort lookup below via [`TermView`]. WI-20260829-1SSXM:
        /// NOT an `Option` — a match whose scrutinee did not type never builds this
        /// frame, it returns the scrutinee's `Err` at `MatchAfterScrutinee`.
        scr_ty: Value,
        covered_entities: Vec<Symbol>,
        has_wildcard: bool,
        /// WI-803: each branch's pattern as `bind_and_label_pattern` returned it
        /// — relabelled, when it is a tuple binder list over a known scrutinee
        /// type. In branch order. `reassemble_match` uses these instead of
        /// re-reading `occ`'s written patterns, which carry no labels.
        branch_patterns: Vec<Rc<NodeOccurrence>>,
        /// WI-20260827-EJ5F5: each branch's guard with references to the binders the
        /// constructor rewrite REMOVED re-pointed at those constructors, in branch order
        /// (`None` where the arm has no guard). `reassemble_match` uses these instead of
        /// re-reading `occ`'s written guards, for the same reason `branch_patterns` above
        /// exists: the written form is not the one that was type-checked, and storing it
        /// would leave a name the arm no longer binds to be read at eval.
        branch_guards: Vec<Option<Rc<NodeOccurrence>>>,
        /// WI-287: the match's own expected type (the parent's hint).
        /// `Some` ⇒ checked mode (every branch must conform); `None` ⇒
        /// synthesis mode (result is the join — a common supertype — of
        /// the branch types).
        body_expected: Option<Value>,
    },
    /// Lambda body finished; build the `arrow(param, body_ty,
    /// body_effects)` type and return a pure result (creating a
    /// lambda is itself effect-free).
    ///
    /// `param_type` is the type the param was bound to in the body env
    /// (annotation, the expected arrow's param slot, or a fresh type
    /// var). Threading it here keeps the arrow's param slot identical
    /// to what the body referenced — without it, `build` would re-derive
    /// a *different* fresh var and the arrow would claim `?a -> T` while
    /// the body was typed under a distinct `?b`.
    ///
    /// WI-794: `binder_error` carries a contradicting binder annotation detected when the
    /// body env was built. It rides the frame rather than being reported at the visit
    /// because a visit cannot push a result — it has already pushed this frame and the
    /// body's Visit, and an extra result there would desynchronize the stack.
    LambdaBody {
        occ: Rc<NodeOccurrence>,
        param_type: Value,
        outer_env: Env,
        binder_error: Option<TypeError>,
        /// WI-803: the param pattern as `bind_and_label_pattern` returned it —
        /// relabelled, when it is a tuple binder list over a known named-tuple
        /// type. This is the child the lambda is reassembled from; `occ`'s own
        /// `param` is still the unlabelled written form.
        param: Rc<NodeOccurrence>,
    },
    /// WI-285: all three If sub-expressions finished (drained in
    /// `[condition, then, else]` order); merge their effects and return
    /// the if's `TypeResult`. WI-287: the type is the join of the then /
    /// else branch types (checked against `expected` when present), not
    /// just the then-branch type. Replaces the recursive-helper arm so a
    /// deep else-if chain stays on the heap.
    IfExpr {
        occ: Rc<NodeOccurrence>,
        env: Rc<TypingEnv>,
        expected: Option<Value>,
    },
    /// WI-538: an in-body proof reassembles to `Expr::Proof` with its
    /// (possibly `@[simp]`-rewritten) `conclude?` + `body` children; its
    /// type is the continuation's. `env` is the pre-proof type env.
    ProofStmt {
        occ: Rc<NodeOccurrence>,
        env: Rc<TypingEnv>,
        has_conclude: bool,
    },
    /// WI-285: all list elements finished; drain `count` and build `List[T = elem]`
    /// (former `check_list_literal`). BOTH halves of "what is `elem`" moved to
    /// [`seq_literal_element_type`], and both changed: `element_hint` is the element type
    /// the position DECLARES (head-gated, WI-20260826-7JDWY) and every element is CHECKED
    /// against it rather than overwritten by it; with no hint the type is the JOIN of the
    /// elements, not the first one's (WI-20260829-WBXGX).
    ListLit {
        occ: Rc<NodeOccurrence>,
        env: Rc<TypingEnv>,
        element_hint: Option<Value>,
        count: usize,
    },
    /// WI-285: as [`TypeBuildFrame::ListLit`], for `Set[T = elem]`.
    SetLit {
        occ: Rc<NodeOccurrence>,
        env: Rc<TypingEnv>,
        element_hint: Option<Value>,
        count: usize,
    },
    /// WI-285: all tuple fields finished (positional then named);
    /// drain `pos_count + named_names.len()`, building the named-tuple
    /// type (`_0`, `_1`, … for positional fields, declared names for
    /// named ones; former `check_tuple_literal`).
    TupleLit {
        occ: Rc<NodeOccurrence>,
        env: Rc<TypingEnv>,
        pos_count: usize,
        named_names: Vec<Symbol>,
    },
    /// WI-284: record a node's inferred type. Pushed by [`push_visit`]
    /// just under the node's Visit, so when it pops the node's
    /// `TypeResult` is on top of `results`. Peeks that result — never
    /// pops or pushes, so it is results-neutral and doesn't perturb the
    /// Apply / Constructor / MatchFinal drains or the final
    /// single-result invariant — and writes the type onto the result's
    /// `node` (WI-283: the resulting occurrence, which the result itself
    /// carries — so the frame needs no stored `occ`).
    Stamp,
}

// ── type_check_expr ────────────────────────────────────────────

/// Infer the type of an expression. Returns TypeResult with type, env, and effects.
/// Public back-compat entry point. The typer's canonical dispatch flow
/// now walks `Rc<NodeOccurrence>` trees via [`type_check_node`]; this
/// shim materializes a NodeOccurrence (from a Handle wrapper or by
/// converting a raw `Term::Fn` shape used by hand-built test inputs)
/// and delegates.
pub fn type_check_expr(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    expr: TermId,
) -> Result<TypeResult, TypeError> {
    type_check_expr_expected(kb, env, expr, None)
}

/// WI-270: variant of [`type_check_expr`] that threads a top-down
/// `expected` hint from the caller. Use this from the operation-body
/// driver (passing `op.return_type`) and from any other site with a
/// declared expected type.
pub fn type_check_expr_expected(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    expr: TermId,
    expected: Option<Value>,
) -> Result<TypeResult, TypeError> {
    let node = materialize_from_handle(kb, expr);
    type_check_node(kb, env, &node, expected)
}

/// Move out of `Rc<TypingEnv>` without cloning when sole owner; else
/// clone the inner `TypingEnv`. Used at TypeResult-construction sites
/// where we need an owned `TypingEnv` for `TypeResult.env`.
#[inline]
pub(super) fn unwrap_env(env: Env) -> TypingEnv {
    // The flow is dropped here: a `TypeResult` carries only the type context
    // (`TypingEnv`). Γ is threaded forward through the frames' `Env`, never out
    // of a result — see [`Env`].
    unwrap_types(env.types)
}

/// Move out of an `Rc<TypingEnv>` without cloning when sole owner, else clone.
/// Used for the post-order leaf-assembly frames `IfExpr` / `ListLit` / `SetLit`
/// / `TupleLit`: they build a result type from already-typed children and
/// neither re-Visit a child nor read `env`, so the `flow` they would otherwise
/// carry is dead state — they hold the bare `Rc<TypingEnv>`. (With the
/// persistent Γ tree this is a tidiness boundary, not a perf necessity: N shared
/// Γ snapshots are O(N) via path-copying, so retaining `flow` would cost only an
/// `Rc` bump, not a clone. The branch flows the typer actually needs ride the
/// branch Visits, not the join frame.)
#[inline]
pub(super) fn unwrap_types(types: Rc<TypingEnv>) -> TypingEnv {
    Rc::unwrap_or_clone(types)
}

/// Canonical typer entry — walk a `Rc<NodeOccurrence>` and produce a
/// `TypeResult`. Runs a Visit/Build work-stack so the Let / Match /
/// Lambda body-recursion paths stay flat on the host stack regardless
/// of source nesting depth. Other variants delegate to their existing
/// `check_*` helpers (which may call back through here, adding ≤ 1
/// host frame per Apply / Constructor / If / collection level — those
/// recursions are bounded by argument count, not source depth).
///
/// WI-1104: this entry types a node at [`NodePos::Value`], which is what an operation
/// body, an entity fact and a standalone typer call all are. **A RULE-BODY GOAL MUST NOT
/// COME THROUGH HERE** — it would silently lose the functional-relation arity + 1
/// tolerance and be refused for a count the spec allows (review-found: the default is
/// safe for every caller that exists, but it is not something a caller can be defaulted
/// INTO correctly). The goal entry is [`type_check_node_at`], and the one thing that
/// knows the answer is [`dispatch_calls_in_occ`].
pub fn type_check_node(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    occ: &Rc<NodeOccurrence>,
    expected: Option<Value>,
) -> Result<TypeResult, TypeError> {
    type_check_node_at(kb, env, occ, expected, NodePos::Value)
}

/// WI-1104: [`type_check_node`] told WHERE the node sits ([`NodePos`]). The rule-body
/// dispatch walk is the one caller that answers anything but [`NodePos::Value`] — it
/// owns goal descent, so it is the only place that knows.
pub(super) fn type_check_node_at(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    occ: &Rc<NodeOccurrence>,
    expected: Option<Value>,
    pos: NodePos,
) -> Result<TypeResult, TypeError> {
    // WI-283: gate the in-typer `@[simp]` firing on whether any rule can fire —
    // read once per walk. WI-443: a loaded `dot_apply` also enables the gate —
    // DotApply nodes are always rewritten (to the dispatched call). Tree
    // REASSEMBLY is no longer gated on this (WI-408): the typer itself now
    // synthesizes rewrites (`some(...)` coercion insertion), so every wrapper
    // frame reassembles from its children's `TypeResult.node`s unconditionally
    // — `reassemble`'s ptr-eq short-circuit keeps the no-rewrite case
    // allocation-free.
    let simp_enabled = crate::kb::simp_rewrite::has_simp_equations(kb) || kb.has_dot_applies;
    // WI-646: gather the eq+unify simp candidate ids ONCE per walk (only when
    // firing is enabled) and thread them into every per-node `fire_simp`, so the
    // Apply/Constructor build frames no longer re-scan the functor buckets at each
    // node. Empty when `simp_enabled` is false — `fire_simp` is then never called.
    let simp_rids: Vec<RuleId> = if simp_enabled {
        kb.simp_equation_rids()
    } else {
        Vec::new()
    };
    type_check_node_gated_at(
        kb,
        env,
        occ,
        expected,
        simp_enabled,
        &simp_rids,
        pos,
        FlowEnv::empty(),
    )
}

/// WI-657(9): [`type_check_node`] with the `@[simp]` gate (`simp_enabled` +
/// `simp_rids`) supplied by the caller instead of recomputed. The eq/unify rule set
/// is LOOP-INVARIANT across a whole `check_operation_bodies` pass (typing rewrites
/// bodies, never asserts/retracts an equation), so the per-op-body driver computes
/// the gate ONCE before its loop and threads it in — dropping a `has_simp_equations`
/// + two `simp_equation_rids` bucket scans (each an allocating `rules_by_functor`)
/// per checked operation. [`type_check_node`] stays the gate-computing entry for
/// standalone callers.
///
/// WI-1104: [`NodePos::Value`], for the reason spelled out at [`type_check_node`] — its
/// two callers are an operation body and a match-arm guard, and a rule-body goal added
/// here would silently lose the arity + 1 tolerance.
pub fn type_check_node_gated(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    occ: &Rc<NodeOccurrence>,
    expected: Option<Value>,
    simp_enabled: bool,
    simp_rids: &[RuleId],
) -> Result<TypeResult, TypeError> {
    type_check_node_gated_at(
        kb,
        env,
        occ,
        expected,
        simp_enabled,
        simp_rids,
        NodePos::Value,
        FlowEnv::empty(),
    )
}

/// WI-K88TN — [`type_check_node_gated`] with Γ SUPPLIED rather than empty.
///
/// Two callers, and they are the two places a check starts INSIDE a body that already
/// has a Γ: the operation-body driver, which seeds the op's own value preconditions
/// ([`op_requires_gamma`]), and the match-arm GUARD, whose Γ is the arm's. A guard is
/// re-entrant rather than a work-stack `Visit`, so it is the one position where the
/// walk's threaded Γ has to be handed over explicitly — and it must be, now that a
/// rigid obligation is DECIDED there instead of floating: checking a guard under an
/// empty Γ refuses a `requires` its enclosing operation declared. MEASURED — `case
/// mk(r) | check(t)` was refused while the identical call in the arm BODY loaded.
pub fn type_check_node_gated_in_gamma(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    occ: &Rc<NodeOccurrence>,
    expected: Option<Value>,
    simp_enabled: bool,
    simp_rids: &[RuleId],
    gamma0: FlowEnv,
) -> Result<TypeResult, TypeError> {
    type_check_node_gated_at(
        kb,
        env,
        occ,
        expected,
        simp_enabled,
        simp_rids,
        NodePos::Value,
        gamma0,
    )
}

/// WI-1104: [`type_check_node_gated`] told WHERE the node sits — see [`type_check_node_at`].
fn type_check_node_gated_at(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    occ: &Rc<NodeOccurrence>,
    expected: Option<Value>,
    simp_enabled: bool,
    simp_rids: &[RuleId],
    pos: NodePos,
    gamma0: FlowEnv,
) -> Result<TypeResult, TypeError> {
    let mut work: Vec<TypeWorkOp> = Vec::with_capacity(32);
    let mut results: Vec<Result<TypeResult, TypeError>> = Vec::with_capacity(32);
    // WI-283: `@[simp]` fire-fuel rides on each `Visit` (not the host stack).
    // When an Apply/Constructor fires, the synthesized RHS is re-`Visit`ed
    // with `fuel - 1` on this same work-stack — so a non-terminating /
    // non-confluent `@[simp]` rule (e.g. a commutative law mistagged
    // `@[simp]`) bottoms out at `fuel == 0` leaving a partial redex (exactly
    // as the fuel-bounded `simp_rewrite::run` did) instead of recursing the
    // host stack to overflow. Children inherit the fuel unchanged; only a
    // fire spends it. Matches the WI-285 iterative discipline.
    push_visit_at(
        &mut work,
        Rc::clone(occ),
        Env::with_gamma(env, gamma0),
        expected,
        crate::kb::simp_rewrite::SIMP_FUEL,
        pos,
    );
    // WI-20260904-50B2K part (c) — WHAT THE BODY'S OWN CALLS SOLVED, so a frame that
    // built a type BEFORE its body ran can read what the body decided.
    //
    // THE ONE CHANNEL THAT DID NOT EXIST. `TypeResult` carries no substitution,
    // `check_apply_iter` takes `env` immutably, and `bind_var` is called at binder-binding
    // sites only — so a call's solving was minted per call and dropped with it. MEASURED
    // before building this: on `let f = lambda v -> twice(v)`, `?param` IS bound (once, to
    // `Int64`) by the body's `twice(v)` — the evidence existed and had nowhere to go, which
    // is why an un-annotated binder could be contradicted by a declaration
    // (`known_gap_the_declaration_may_solve_a_binder_the_body_contradicts`).
    //
    // SCOPED BY A VARIABLE WATERMARK, and the first cut's "no scoping rule needed" was
    // MEASURED WRONG — see [`report_call_solutions`] for the three populations that
    // falsified it. `var_watermark` is read once here; a binding is reported only when its
    // variable and every variable inside its value were minted DURING this walk. The
    // distinction the per-call σ exists to keep is thereby preserved rather than assumed.
    //
    // THIS IS THE GENERAL CHANNEL, CONSUMED BY ONE FRAME SO FAR: `LambdaBody` reads it to
    // build an arrow that reflects its body. Widening the readership needs no change here.
    // SCOPED BY A VARIABLE WATERMARK the container carries — see [`WalkSolutions`].
    let mut solving = WalkSolutions::new(kb);
    while let Some(op) = work.pop() {
        match op {
            TypeWorkOp::Visit {
                occ,
                env,
                expected,
                fuel,
                pos,
            } => visit_type(
                kb,
                occ,
                env,
                expected,
                fuel,
                pos,
                &mut solving,
                &mut work,
                &mut results,
            ),
            TypeWorkOp::Build(frame) => build_type(
                kb,
                frame,
                simp_enabled,
                simp_rids,
                &mut work,
                &mut results,
                &mut solving,
            ),
        }
    }
    // WI-20260904-50B2K part (c) — THE DISCHARGE. A spec-op dispatch this walk held
    // because its carrier was a lambda binder is answered now, against what the binder's
    // own uses solved. See [`WalkSolutions::discharge`].
    solving.discharge(kb);
    debug_assert_eq!(
        results.len(),
        1,
        "iterative typer: expected exactly one result"
    );
    results
        .pop()
        .expect("iterative typer: missing final result")
}

/// Type-check a bare-identifier reference (Ref / Ident / VarRef) by
/// dispatching across the resolution paths: env-bound var,
/// constructor, zero-arg operation. Returns `Err(UnresolvedName)`
/// when none match — the strict equivalent of the pre-WI-264 silent-
/// None bail.
/// WI-20260904-50B2K part (c), step 2 — ∀-ELIMINATION AT AN ENVIRONMENT READ, and THE ONE
/// OWNER, because a schema that escapes ANY reader meets a conformance relation with no arm
/// for it and is compatible with everything.
///
/// **THE FIRST CUT PUT THIS AT ONE READER AND THERE ARE THREE.** `check_bare_ref` had it and
/// `visit_type`'s `Expr::Var` arm — the `?g` spelling of the very same binding, which the
/// WI-279/WI-487 comment there says resolves the same let/lambda/match names — did not. So
/// `needs_b(g)` was refused and `needs_b(?g)` LOADED, one program with two verdicts a
/// question mark apart; and the escaped schema reached a user diagnostic as raw internals
/// (`got PolyType[binders = cons[…], context = cons[…]]`). /code-review drove it.
///
/// `Err` when the eliminated context finds no deferred requirement to claim it: that means
/// the constraint would be dropped here, which is the wrong accept this whole slice exists
/// to prevent.
pub(super) fn eliminate_env_schema(
    kb: &mut KnowledgeBase,
    solving: &mut WalkSolutions,
    // The NAME AS WRITTEN, for the diagnostic. `None` where the carrier has none (a
    // De Bruijn or rigid variable), which reads better than a stand-in: the first cut
    // interned `?var` there, and a message naming a variable the author never wrote is
    // worse than one that does not name it at all. /code-review raised both halves.
    name: Option<Symbol>,
    span: Option<Span>,
    ty: Value,
) -> Result<Value, TypeError> {
    let Some(inst) = instantiate_poly_type(kb, &ty) else {
        // A ∀ THAT DECLINES TO ELIMINATE IS AN ERROR HERE TOO, matching `check_bare_ref`'s
        // eta arm. `extract_type` answers `Error` for a present-but-undecodable `context`, so
        // this `None` can mean "malformed schema" as well as "not a schema at all" — and
        // returning the raw type in the first case hands a consumer the very ∀ this function
        // exists to keep out. Unreachable while `build_value_list` is the only context
        // producer; it was the one silent `None` of the three ∀-readers. /code-review.
        if matches!(type_head(kb, &ty), TypeHead::PolyType) {
            return Err(TypeError::Other {
                site: TypeError::here(),
                span,
                context: TypeErrorContext::LetBinding {
                    var: name.unwrap_or_else(|| kb.intern("?")),
                },
                expected: "a well-formed quantified type for this binding".to_string(),
                actual: "a `PolyType` whose binders or context could not be read \
                         (WI-20260904-50B2K part (c))"
                    .to_string(),
            });
        }
        return Ok(ty);
    };
    if !inst.obligations.is_empty() && solving.note_instantiation(&inst.binder_map) == 0 {
        let named = match name {
            Some(n) => format!("`{}`", kb.local_name_of(n)),
            None => "this reference".to_string(),
        };
        return Err(TypeError::Other {
            site: TypeError::here(),
            span,
            context: TypeErrorContext::LetBinding {
                // A LET-BOUND LOCAL, NOT AN OPERATION, which is what the first cut's context
                // said. The value whose schema this is was written as a `let`, and the
                // context a reader sees should be the construct they wrote.
                var: name.unwrap_or_else(|| kb.intern("?")),
            },
            expected: "a quantified type whose constraints this walk can discharge".to_string(),
            actual: format!(
                "{named} has a `PolyType` carrying {} constraint(s) no deferred requirement \
                 claims (WI-20260904-50B2K part (c))",
                inst.obligations.len()
            ),
        });
    }
    Ok(inst.ty)
}

pub(super) fn check_bare_ref(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    flow: &FlowEnv,
    sym: Symbol,
    span: Option<Span>,
    occ: &Rc<NodeOccurrence>,
    expected: Option<&Value>,
    solving: &mut WalkSolutions,
) -> Result<TypeResult, TypeError> {
    if let Some(ty) = env.lookup_var(sym) {
        // WI-20260904-50B2K part (c), step 2 — ∀-ELIMINATION FOR A LET-BOUND POLYMORPHIC
        // VALUE. Until step 2 nothing could put a ∀ in the value environment, so this path
        // handed the type back untouched; a generalized lambda arrow
        // (`∀a. Additive[a] => (a) -> a`) now can be here, and a ∀ handed to a consumer
        // that expects an ARROW is not merely imprecise — `Applier.ap(g, leaf())` compares
        // the schema against `Function[A = Leaf, B = Int64]` and refuses a program that
        // works.
        //
        // Per REFERENCE, as at the eta arm below and for its reason (§5.6: instantiating is
        // the caller's job), and the obligations go to the walk rather than being tested
        // here — this site does not yet know what the surrounding unification will pin the
        // fresh carrier to. `Applier.ap(g, leaf())` pins it to `Leaf` in the argument check
        // that follows and the discharge sees it there; the generic `ap[X](…)` pins it to a
        // type PARAMETER, which is not a carrier that can provide anything, so that one is
        // still refused — correctly, since `ap` declares no `requires` to carry the
        // obligation across its boundary.
        //
        // **AT EVERY REFERENCE, AND THE NARROWER GATE I TRIED IS A MEASURED WRONG ACCEPT.**
        // Instantiating only where `expected` is `Some` reads as let-polymorphism — keep
        // the schema where nothing asks for an instance — and it does fix a real wart:
        // `let g = lambda x -> x + x  let h = g  1` is REFUSED while the same program
        // without the unused alias LOADS, because the alias mints an instance nothing will
        // ever pin. But `expected` is NOT "a consumer needs a type" here: an argument slot
        // is hinted only when it is CALLABLE (part (b)), so `needs_b(g)` against
        // `needs_b(b: Bool)` arrives with no expectation — and with the gate in place that
        // program LOADED, a function value accepted into a `Bool` slot. Measured, both
        // ways round. A ∀ that escapes this site meets a conformance relation with no arm
        // for it, so the schema must not leave here; the wart is a REFUSAL and the gate was
        // a WRONG ACCEPT, and between those two this slice takes the refusal.
        //
        // The wart's real fix is let-GENERALIZATION — re-quantifying at the `let` a
        // variable still free in the bound value's type — which is a producer this slice
        // does not add. Pinned as `known_gap_an_unused_alias_of_a_generalized_lambda_is_
        // refused`.
        let ty = eliminate_env_schema(kb, solving, Some(sym), span, ty)?;
        return Ok(TypeResult::pure_value(ty, env.clone(), Rc::clone(occ)));
    }
    // Proposal 039 / WI-084: a bare reference to a term-level constant is
    // value-denoting — it types as the const's DECLARED type, read fold-free off
    // the symbol (NO body evaluation here; folding is eval/codegen, Phase 3). A
    // local (handled above) still shadows it; §8.6 resolution already arbitrates
    // the candidate set, so an ambiguous same-name tie errored before we got here.
    if let Some(ty) = kb.const_type(sym).cloned() {
        return Ok(TypeResult::pure_value(ty, env.clone(), Rc::clone(occ)));
    }
    if kb.is_constructor_symbol(sym) {
        // WI-20260826-JSFHG: the caller's `expected` is THREADED, where this passed a hard
        // `None`. A 0-ary constructor reached bare took no checking direction at all, so
        // `takeRed(red)` classified at the parent while `takeRed(red())` — the same value,
        // one pair of parentheses apart — classified at the variant. The applied spelling
        // has always been given the hint; this is the bare one catching up, not a new
        // channel.
        let expected = expected.cloned();
        return check_constructor_iter(kb, env, flow, sym, &[], &[], &[], &[], span, expected, occ);
    }
    // WI-275: a bare operation reference used where a function type is expected
    // denotes the operation as a first-class function value (eta-expansion) —
    // its `Function[A, B, E]` arrow type, not its return type. Fires only in a
    // function-typed context; elsewhere a bare op name keeps denoting its return
    // type (the zero-arg-call reading below), unchanged.
    if let Some(exp) = expected {
        if arrow_parts(kb, exp).is_some() {
            if let Some(fn_ty) = operation_as_function_value(kb, sym, occ) {
                // WI-1083: kept because the ∀-elimination below SHADOWS `fn_ty`, while the
                // dictionary pin must still see the un-instantiated one.
                let original_fn_ty = fn_ty.clone();
                // WI-700: a NULLARY op reference in an arrow-typed slot is AMBIGUOUS —
                // the eta reading `() -> ret` competes with the zero-arg-call reading
                // `ret`. When `ret` itself already conforms to the expected arrow
                // (`makeInc() -> (Int64 -> Int64)` into an `Int64 -> Int64` slot), the
                // eta arrow `() -> ret` must NOT shadow it: prefer the return-type
                // reading below (its pre-WI-700 behavior). A non-nullary op is never a
                // zero-arg call, so it always eta-lifts (the check short-circuits on
                // `operation_is_nullary`, which alone has both readings).
                let eta_shadows_return_type = operation_is_nullary(kb, sym)
                    && lookup_operation_return_type(kb, sym).is_some_and(|ret| {
                        types_compatible(kb, &mut Substitution::new(), &TermIdView(ret), exp)
                    });
                if !eta_shadows_return_type {
                    // WI-1083 — ∀-ELIMINATION AT THE REFERENCE, and this is the ONE site:
                    // §5.6 says an operation's type parameter is "the CALLER's to
                    // instantiate", and a bare reference IS the caller. `fn_ty` is the
                    // OPERATION's type (a ∀ whenever its signature binds anything); what
                    // this occurrence has is one INSTANCE of it, freshened here so two
                    // references to the same operation share no variable.
                    //
                    // HERE RATHER THAN AT THE CONSUMERS, which the first cut tried and
                    // MEASURED wrong: instantiating inside `unify_types` /
                    // `types_compatible` gives each RELATION its own fresh variables, so
                    // the binding the argument-unify loop makes (`?A := Int64`) lands on a
                    // variable the conformance check that follows has never seen — and the
                    // holes below stayed open. One instantiation per occurrence is what
                    // lets the two steps agree.
                    //
                    // A ∀ THAT FAILS TO ELIMINATE IS AN ERROR, not a value type. The head
                    // says `PolyType` and the elimination declined, which means the node is
                    // malformed (an unreadable child, an empty binder list, a binder that is
                    // not a variable — see `extract_type`'s arm and
                    // [`instantiate_poly_type`]). Returning the schema instead would hand
                    // the author a mismatch against a form they never wrote.
                    //
                    // AND IT IS RAISED BEFORE `attach_eta_dispatch_dict`, which is an
                    // ORDERING that matters (code review): that function reads the ∀'s BODY
                    // (`poly_type_body`), which is likewise `None` for a malformed node, so
                    // its element-type pin silently would not happen and a `requires`-
                    // carrying op would report `UnsatisfiableRequirement` (WI-420) instead
                    // of the malformed-∀ error written here for it.
                    let fn_ty = match instantiate_poly_type(kb, &fn_ty) {
                        // WI-20260904-50B2K part (c) — ∀-ELIMINATION IS WHERE A CONTEXT
                        // COMES DUE: `instantiate_poly_type` hands the constraints back with
                        // the binders made concrete, which is exactly what makes them
                        // answerable, and discharging them is this reference's job. The
                        // empty case is every ∀ that exists today.
                        Some(inst) if inst.obligations.is_empty() => inst.ty,
                        // WI-20260904-50B2K part (c) — A CONTEXT THAT REACHES ∀-ELIMINATION
                        // WITH NOWHERE TO GO IS A LOUD ERROR, not a `debug_assert`. The
                        // first cut asserted, which is silent in release — and the failure
                        // it guards is a WRONG ACCEPT: a constraint dropped here is a
                        // program that type-checks without its requirement. The repo's own
                        // rule ("prefer a loud error over a silent skip") applies exactly.
                        // /code-review raised it.
                        //
                        // UNREACHABLE IN THIS SLICE and written anyway: the one mint
                        // (`generalize_eta_arrow`) builds the empty context, so nothing
                        // produces a non-empty one yet. The slice that starts producing them
                        // must deliver the discharge FIRST or every such reference is
                        // refused here — which is the ordering this error enforces.
                        Some(inst) => {
                            return Err(TypeError::Other {
                                site: TypeError::here(),
                                span,
                                context: TypeErrorContext::OperationAsFunctionValue {
                                    op_name: sym,
                                },
                                expected: "a quantified type whose constraints this \
                                           reference can discharge"
                                    .to_string(),
                                actual: format!(
                                    "a `PolyType` carrying {} undischarged constraint(s) \
                                     (WI-20260904-50B2K part (c))",
                                    inst.obligations.len()
                                ),
                            });
                        }
                        None if matches!(type_head(kb, &fn_ty), TypeHead::PolyType) => {
                            return Err(TypeError::Other {
                                site: TypeError::here(),
                                span,
                                context: TypeErrorContext::OperationAsFunctionValue {
                                    op_name: sym,
                                },
                                expected: "a well-formed quantified type for this operation \
                                           used as a function value"
                                    .to_string(),
                                actual: "a `PolyType` whose binders could not be read \
                                         (WI-1083)"
                                    .to_string(),
                            });
                        }
                        None => fn_ty,
                    };
                    // WI-420: resolve + attach the op's requirement dispatch dict
                    // (the `expected` arrow pins its element type) so eval captures
                    // it on the OpRef. A cross-sort unsatisfiable requirement is a
                    // loud error here.
                    //
                    // WI-1083: handed the ORIGINAL `fn_ty` — the ∀ — not the instantiation
                    // above, because the dictionary's dependencies are keyed by the
                    // declaring sort's canonical variables. See [`poly_type_body`].
                    attach_eta_dispatch_dict(kb, env, sym, occ, &original_fn_ty, exp)?;
                    return Ok(TypeResult::pure_value(fn_ty, env.clone(), Rc::clone(occ)));
                }
            }
        }
    }
    // WI-20260828-2TMB5 — THE ZERO-ARG-CALL READING BELOW IS A CALL, AND A CALL WITH NO
    // ARGUMENTS IS WELL-FORMED ONLY FOR A NULLARY OPERATION. It was never gated on that, so
    // a bare NON-nullary name in a slot the eta arm above declined — an ordinary value slot,
    // or an arrow slot whose op has no runnable body — silently took the operation's RETURN
    // type. `entity plain(v: Int64)` fed `plain(inc)` (where `inc(x: Int64) -> Int64`)
    // loaded CLEAN: `inc` typed as `Int64`, which is exactly the declared field type, so the
    // WI-385 field validation had nothing to object to. The applied spelling of the same
    // reading, `plain(inc())`, is an arity error — the bare one skipped the arity check by
    // never being routed through a call.
    //
    // THE SAME FALL-THROUGH, THE THIRD TIME. WI-1063 found it laundering an existential
    // return (`takes_pure(mk)` clean where `takes_pure(mk())` was refused) and WI-1083 found
    // it laundering a ∀ (`idp[A](x: A) -> A` typing as a bare flexible `?A` that unifies
    // with anything). Both repaired the arm ABOVE so that fewer references reached this one.
    // This repairs the arm ITSELF, which is what makes the rule hold on every path rather
    // than on the paths the typer usually takes.
    //
    // A NON-NULLARY BARE NAME HAS EXACTLY ONE READING — the eta lift — because the other is
    // an arity error. So take it here WITHOUT requiring an arrow-shaped `expected`: the arm
    // above needs that arrow because a NULLARY op's two readings genuinely compete (`() ->
    // ret` against `ret`, WI-700's `eta_shadows_return_type`), and nothing competes here.
    // The ticket's program is then refused by the ORDINARY field check with the ordinary
    // message — `expected Int64, got Int64 -> Int64` — the same one its inline-lambda twin
    // `plain(lambda x -> x)` has always produced. No new refusal site and no new diagnostic
    // for it: the fix is to hand the existing check the type the author actually wrote.
    //
    // AND THE POLYMORPHIC SLOT IS REFUSED TOO, which is the case worth naming because the
    // first cut of this ticket accepted it. `some(sub2)` / `cons(sub2, nil())` reach this
    // arm as well — no hint is computed for a field type that is not callable by head, so
    // `expected` is `None` — and a slot that declares no arrow cannot pin one. See the
    // refusal below for why lifting there is not an option.
    //
    // THAT ONE IS A LIMIT RATHER THAN A RULE, and WI-20260828-5NSZY carries it: the author
    // DID pin an arrow, one level out (`o: Option[T = Function[…]]`), and it fails to reach
    // the reference because `one_arg_hint` pushes a declared parameter type into a
    // CONSTRUCTOR-APPLICATION argument only when that type names an ENTITY. The repair is to
    // make the arrow arrive, never to lift without one.
    //
    // THE GATE SITS INSIDE THE ARM IT GUARDS, reading the operation record only once the
    // consumer's own lookup has succeeded. [`lookup_operation_return_type`] and
    // [`lookup_operation_info_full`] are two DIFFERENT readers of the `OperationInfo` facts
    // — the first scans for one field, the second decodes a whole signature through a cache
    // tier the first has not got. Gating OUTSIDE on the second would let any symbol the two
    // disagree about fall straight through to the reading this repairs, which is the shape
    // of fail-open being fixed here. A record the consumer can read a return type out of but
    // no parameter list is not a case to guess at either: `params` is what decides which
    // reading applies, so an unreadable one is a loud error rather than a silent default to
    // either side.
    if let Some(ret_ty) = lookup_operation_return_type(kb, sym) {
        let Some(op_info) = lookup_operation_info_full(kb, sym) else {
            return Err(TypeError::Other {
                site: TypeError::here(),
                span,
                context: TypeErrorContext::OperationAsFunctionValue { op_name: sym },
                expected: format!(
                    "a readable parameter list for `{}`, which decides whether a bare \
                     reference to it is a zero-arg call or a function value",
                    kb.qualified_name_of(sym)
                ),
                actual: "an `OperationInfo` record carrying a return type whose signature \
                         could not be decoded"
                    .to_string(),
            });
        };
        if !op_info.params.is_empty() {
            // NO CONTEXT-FREE LIFT. The eta reading needs an arrow to lift AGAINST, and
            // reaching here means there is none: the WI-275 arm above returns whenever
            // `expected` is an arrow AND the operation has a function-value form, and for a
            // non-nullary operation its `eta_shadows_return_type` guard is `false` by
            // construction. So either `expected` is not an arrow, or the operation has no
            // function-value form — and in both cases there is nothing to lift against.
            //
            // LIFTING ANYWAY IS REFUTED, MEASURED, and this is the first cut of this ticket:
            // it minted the arrow and pinned the dictionary against the operation's OWN
            // arrow for want of anything better. Self-pinning imposes nothing, which is
            // exactly the problem — `attach_eta_dispatch_dict` reads the expected arrow to
            // pin BOTH the requirement dictionary and the argument-spread labels
            // (`function_slot_spread_labels`, WI-1087), and an arrow unified with itself
            // pins neither. `via_option(some(sub2))`, with `sub2(x, acc)` reaching an
            // `Option[T = Function[A = (x: Int64, acc: Int64), …]]` field and applied to
            // `(acc: 3, x: 10)`, returned **-7** where its arrow-slot twin `direct(sub2)`
            // returned 7 — the labels went unpinned and eval spread by source order. On
            // main the same program is a LOAD ERROR (`got Option[T = Int64]`), so the lift
            // did not restore a capability; it turned a correct refusal into a silently
            // wrong answer. A `requires`-carrying operation is the same defect one step
            // louder: a dict-less `OpRef` escapes to a foreign apply frame and dies there,
            // against WI-420's rule that a dict missing at mint is missing for good.
            //
            // SO THE REFERENCE DENOTES NOTHING HERE and says so. This is not a narrowing of
            // the eta reading — every position that could lift before still lifts, through
            // the arm above, which is the only one that has ever had an arrow to lift
            // against.
            // WI-1102 review: [`op_has_runnable_body`] rather than
            // [`operation_as_function_value`], which answers the same question here — the
            // record was read above, so the lift declines exactly when the body is missing
            // — but answers it by MINTING: it opens the existential return, allocating a
            // fresh skolem into the KB, and builds an arrow, all to be discarded. A
            // diagnostic must not leave a skolem behind.
            //
            // AND THE TWO HALVES OF THE MESSAGE BRANCH TOGETHER. Computing `expected`
            // independently of which case fired told the author of a body-less operation to
            // find an arrow slot for it, when no arrow slot will ever accept it — the two
            // halves render as one sentence (`expected …, got …`), so one condition has to
            // write both.
            let (expected_txt, actual_txt) = if op_has_runnable_body(kb, sym) {
                (
                    match expected {
                        Some(e) => format!(
                            "a value of type {}, this position declaring no arrow",
                            type_display_name_value(kb, e)
                        ),
                        None => {
                            "a slot declaring the arrow to lift this operation against".to_string()
                        }
                    },
                    format!(
                        "a bare reference to the {}-parameter operation `{}`, which denotes \
                         it as a function value; this position supplies no function type to \
                         lift it against, and the zero-arg-call reading belongs to a NULLARY \
                         operation",
                        op_info.params.len(),
                        kb.qualified_name_of(sym)
                    ),
                )
            } else {
                (
                    // The slot type is NAMED here even though no slot can accept this
                    // operation, and `wi275_hof_inference_test::body_less_builtin_in_-
                    // function_slot_is_rejected_not_crashed` asserts it: the author needs to
                    // see which slot they were filling. What the wording must not do is
                    // advise finding an arrow slot, since none exists — hence the clause
                    // that follows it.
                    match expected {
                        Some(e) => format!(
                            "a value of type {}, which no bare reference to this operation \
                             can supply",
                            type_display_name_value(kb, e)
                        ),
                        None => "an operation carrying an anthill body — the only kind with \
                                 a function-value form, so that the typer's accepted set \
                                 stays a subset of the evaluator's"
                            .to_string(),
                    },
                    {
                        // The REPAIR advice needs the slot's answer too. A lambda is what to
                        // write where an arrow was wanted; where the slot declares no arrow
                        // at all (a body-less operation named in an `Int64` field) a lambda
                        // is equally inadmissible, and advising one sends the author in a
                        // direction the very same rule refuses. Computed BEFORE the format!
                        // so its `&mut kb` does not overlap the `qualified_name_of` borrow.
                        let advice = match expected {
                            Some(e) if arrow_parts(kb, e).is_some() => {
                                ". Write a lambda that calls it instead"
                            }
                            _ => "",
                        };
                        format!(
                            "a bare reference to `{}`, which carries no body: a builtin, a \
                             spec declaration, or an operation defined only by rule \
                             clauses{}",
                            kb.qualified_name_of(sym),
                            advice
                        )
                    },
                )
            };
            return Err(TypeError::Other {
                site: TypeError::here(),
                span,
                context: TypeErrorContext::OperationAsFunctionValue { op_name: sym },
                expected: expected_txt,
                actual: actual_txt,
            });
        }
        // WI-1063: this IS a call — the zero-arg-call reading of a bare operation name — so
        // its result opens the callee's existential return exactly as `mk()` does. Without it
        // the whole rule was bypassable by deleting two characters: `takes_pure(mk())` was
        // refused and `takes_pure(mk)` loaded clean, on the same two declarations. Not the
        // eta reading, which returned above with an arrow type; here the return type is the
        // result and it is genuinely checked (a wrong ELEMENT type is refused at this site
        // today), so the row must be too.
        let ret = Value::term(ret_ty);
        let ret = open_existential_return(
            kb,
            impl_parent_sort_of_op(kb, sym),
            sym,
            &ret,
            occ.span,
            occ.owner,
        )
        .unwrap_or(ret);
        return Ok(TypeResult::pure_value(ret, env.clone(), Rc::clone(occ)));
    }
    // A bare reference to a free-standing entity denotes the entity as a type,
    // not a construction — its type is the reflect `Type` sort, so it can be
    // passed to operations taking a `Type` (e.g. `facts_of(kb(), WorkItem)`).
    if kb.is_free_standing_entity(sym) {
        let type_ty = kb.make_sort_ref_by_name("anthill.prelude.Type");
        return Ok(TypeResult::pure(type_ty, env.clone(), Rc::clone(occ)));
    }
    // WI-206: the SORT peer of the arm above — a bare sort name in a slot that
    // expects a `Type` denotes the sort as a type value (`is_modifiable(Cell)`,
    // `sort_template(kb(), Color)`). Unlike an entity, a sort name has no other
    // value reading to compete with, but it also has no value reading OUTSIDE a
    // `Type` slot: gating on the expected type keeps a stray sort name in an
    // ordinary value position the loud `UnresolvedName` it is today, rather than
    // silently typing as a type value.
    if kb.kind_of(sym) == Some(crate::intern::SymbolKind::Sort)
        && expects_reflect_type(kb, expected)
    {
        let type_ty = kb.make_sort_ref_by_name("anthill.prelude.Type");
        return Ok(TypeResult::pure(type_ty, env.clone(), Rc::clone(occ)));
    }
    // WI-714 (proposal 052): a bare reference to a RULE — its head functor
    // (`SymbolKind::Goal`, an unlabeled rule) or a rule label (`SymbolKind::Rule`)
    // — denotes the relation as a first-class `Relation[T]` VALUE: the typed,
    // composable face of its `LogicalQuery`, consumed as a stream via
    // `provides LogicalStream`. Eval's `reduce_var` twin builds the runtime value.
    // Sits before the `UnresolvedName` fall-through: a rule name is none of the
    // readings above, so it reached here as an unresolved name today.
    if kb.cites_a_relation(sym) {
        // WI-20260911-5G28A S1: in functional code the citation reads its sort's parameters
        // (see [`CitationSite`]); a rule body's keeps the relation's own variables.
        let site = (!env.in_rule_body()).then_some(CitationSite { env, expected });
        let ty = relation_reference_type(kb, sym, span, occ, site)?;
        return Ok(TypeResult::pure_value(ty, env.clone(), Rc::clone(occ)));
    }
    // WI-898: an EQUATION-introduced functor that owns no clauses is NOT a relation,
    // so the arm above declined it rather than reporting it unresolved. It has no
    // bare value reading either (a rewrite rule is not first-class), so this is where
    // it ends, with a diagnostic that says what it actually is.
    if kb.has_kind(sym, crate::intern::SymbolKind::EquationFunctor) {
        let census = crate::kb::simp_rewrite::equation_clause_census(kb, sym);
        return Err(TypeError::UnreducedEquationFunctor {
            span,
            functor: sym,
            census,
        });
    }
    Err(TypeError::UnresolvedName { span, name: sym })
}

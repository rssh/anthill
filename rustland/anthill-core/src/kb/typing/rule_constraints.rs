//! Collecting type constraints on rule variables from declared types.

use super::*;

/// WI-9C2PZ — ONE APPLICATION's instantiation of the type parameters its callee's
/// signature binds: canonical parameter variable (`VarId::raw()`) → the fresh variable
/// THIS call site stands it up as.
///
/// Per APPLICATION, not per parameter position, which is the whole point: `eq(?x, ?y)`
/// declares both arguments at one `T`, so both must land on ONE fresh variable and stay
/// correlated, while the NEXT `eq` in the same rule body gets a different one and is
/// independent.
///
/// Usually empty and allocated lazily for that reason — a concrete signature
/// (`parent(of: String, is: String)`, `Int64.lt(a: Int64, b: Int64)`) mentions no
/// parameter and mints nothing.
pub(super) type ParamInstantiation = HashMap<u32, TermId>;

/// WI-9C2PZ — the variables whose recorded type came from a callee's INSTANTIATED
/// PARAMETER, i.e. from a call, rather than from a declared position of the variable
/// itself.
///
/// The distinction decides who owns a disagreement, and getting it wrong loses a located
/// error. `var_types` answers "what do this variable's own positions say"; a per-call
/// parameter says nothing about the variable and is recorded only as a placeholder — so
/// when a declared position arrives it takes over, and when the two cannot be reconciled
/// the fault is the CALL's, not the variable's. See [`constrain_vid`].
pub(super) type ParamBackedVars = HashSet<u32>;

/// What one clause's typing is collected into: what each variable's own positions say
/// (`var_types`, keyed by De Bruijn index), which of those records are a call's placeholder
/// ([`ParamBackedVars`]), the one substitution over the clause, and the positions read once
/// the walk is done ([`LatePosition`]).
pub(super) struct ClauseConstraints {
    pub(super) var_types: HashMap<u32, Value>,
    pub(super) param_backed: ParamBackedVars,
    pub(super) subst: Substitution,
    late: Vec<LatePosition>,
    /// The arguments of goals that read nothing — on the clause's own relation, or another of
    /// its cycle ([`rule_goal_columns_at`]): their types, and the variables nothing types.
    pub(super) unread: Vec<Value>,
    pub(super) unread_vars: HashSet<u32>,
    /// What the walk found that does not fit — a construction's argument against its field.
    pub(super) found: Vec<ClauseDisagreement>,
    /// Variables only a demand has typed so far — a call's argument at a parameter of a
    /// stated type —; any other position, a test among them (`domain(?v, T)`, `<=>` against a
    /// construction or a literal, a head's bound), takes a variable off. The arguments a
    /// column of some type meets ([`ColumnType::Some`]), read once every other position is,
    /// and the variables nothing types that such a column takes.
    pub(super) demand_only: HashSet<u32>,
    pub(super) some_args: Vec<Rc<NodeOccurrence>>,
    pub(super) some_typed: HashSet<u32>,
    /// Where a term the walk reads was written, for a term that carries no place of its own
    /// (a head's, a fact's).
    pub(super) at: Option<crate::span::SourceSpan>,
    /// Whether a construction's arguments are checked against its fields, and the reflect
    /// syntax a term stores is read as data: not in an equation's head ([`walk_clause`]).
    pub(super) checks_constructions: bool,
}

impl ClauseConstraints {
    pub(super) fn new() -> Self {
        ClauseConstraints {
            var_types: HashMap::new(),
            param_backed: HashSet::new(),
            subst: Substitution::new(),
            late: Vec::new(),
            unread: Vec::new(),
            unread_vars: HashSet::new(),
            found: Vec::new(),
            demand_only: HashSet::new(),
            some_args: Vec::new(),
            some_typed: HashSet::new(),
            at: None,
            checks_constructions: true,
        }
    }

    /// A copy to try one position on: kept where the position fits ([`Self::commit`]),
    /// dropped where it does not, so a position that does not fit pins nothing.
    fn trial(&self) -> Self {
        let mut subst = self.subst.clone();
        subst.contradiction = false;
        ClauseConstraints {
            var_types: self.var_types.clone(),
            param_backed: self.param_backed.clone(),
            subst,
            late: Vec::new(),
            unread: self.unread.clone(),
            unread_vars: self.unread_vars.clone(),
            found: Vec::new(),
            demand_only: self.demand_only.clone(),
            some_args: self.some_args.clone(),
            some_typed: self.some_typed.clone(),
            at: self.at,
            checks_constructions: self.checks_constructions,
        }
    }

    /// Keep what `trial` learnt, the positions its own walk found included. The flag a
    /// contradiction of the walk set stays as the walk left it: a late position never
    /// sets it.
    fn commit(&mut self, trial: ClauseConstraints) {
        let contradiction = self.subst.contradiction;
        self.var_types = trial.var_types;
        self.param_backed = trial.param_backed;
        self.subst = trial.subst;
        self.subst.contradiction = contradiction;
        self.late.extend(trial.late);
        self.unread = trial.unread;
        self.unread_vars = trial.unread_vars;
        self.found.extend(trial.found);
        self.demand_only = trial.demand_only;
        self.some_args = trial.some_args;
        self.some_typed = trial.some_typed;
    }
}

/// A position of a clause that types a variable and is read once the walk is done: on a
/// copy of the clause's typing, kept only where it fits. So what these positions say is
/// added to what the walk found, and never makes the walk's contradiction — the one a
/// clause is refused or left undispatched for.
enum LatePosition {
    /// An operation's application in a slot that declares a type (`?c <=> Mk.mk4()`, the
    /// `T` of `<=>`): the call's result is of that type.
    CallResult {
        position: Value,
        result: CallResult,
        at: crate::span::SourceSpan,
    },
    /// `f(a₁…aₙ, ?r)` at goal position, read as the call (§5.3): the last argument is the
    /// call's result.
    ResultColumn {
        arg: Rc<NodeOccurrence>,
        result: CallResult,
    },
    /// A goal on a relation: each argument is at the callee's column.
    RuleGoal {
        functor: Symbol,
        goal: Rc<NodeOccurrence>,
    },
    /// A dot whose value fills a slot that declares a type (`?y <=> ?p.t`): its type, once
    /// the clause types its receiver.
    DotResult {
        dot: Rc<NodeOccurrence>,
        position: Value,
    },
}

/// An operation application's result type at the application's instantiation, and the
/// argument each parameter is filled with — what a projection the result names (`head(s:
/// Self) -> s.T`) is read off.
pub(super) struct CallResult {
    ty: Value,
    params: Vec<(Symbol, ArgType)>,
}

/// The type of a call's argument as a projection reads it: a variable's, once the clause is
/// typed, or the type the argument is known at where it is read.
enum ArgType {
    Var(u32),
    Of(Value),
}

/// A late position that did not fit what the clause already said, and so pinned nothing.
#[derive(Clone, Debug)]
pub(super) struct ClauseDisagreement {
    pub(super) class: DisagreementClass,
    pub(super) span: Option<crate::span::SourceSpan>,
}

/// Which position of a clause did not fit ([`ClauseDisagreement`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum DisagreementClass {
    /// A construction's argument against the field it fills.
    ConstructionField,
    /// A variable a column of some type takes, which only a demand types.
    SomeTypeDemand,
    /// A head's written bound against what the body says of its variable.
    HeadBound,
    /// The same, where the bound fits once the enclosing sort's parameter it names is let
    /// vary: the body fixes the parameter.
    SortParameterFixed,
    /// An operation call's result against the slot it fills.
    CallResult,
    /// The result column of `f(args, ?r)` against the call's result.
    ResultColumn,
    /// A rule goal's argument against the callee's column.
    RuleGoal,
    /// A dot's value against the slot it fills.
    DotResult,
}

/// One clause's typing: each variable's type by De Bruijn index, whether the walk found
/// two declared positions of one variable that disagree, and the late positions that did
/// not fit.
pub(super) struct ClauseTyping {
    pub(super) var_types: HashMap<u32, Value>,
    pub(super) contradiction: bool,
    pub(super) disagreements: Vec<ClauseDisagreement>,
    /// The arguments of goals that read nothing: their types, as `var_types` resolves, and
    /// the variables nothing types.
    pub(super) unread: Vec<Value>,
    pub(super) unread_vars: HashSet<u32>,
}

/// WI-9C2PZ — the canonical type-parameter VARIABLE a declared-type node denotes, if it
/// denotes one.
///
/// Named `declared_type_param_var` until WI-20260923-N3W68, which is also the name of
/// [`crate::kb::op_info::declared_type_param_var`] — a DIFFERENT question (the variable an
/// operation's own bracket declares, by short name) asked of different arguments. Two
/// functions, one name, in one crate.
///
/// The question is NOT "does this look like a type parameter" but "is this a VARIABLE
/// that [`walk_type`] collapses into one canonical identity KB-wide" — because that
/// collapse is exactly the conflation being repaired, so its set is exactly the set to
/// instantiate. Two spellings reach it and both answer here: a parameter already stored
/// as a `Var::Global` (an operation's bracket parameter, WI-1082's elaborated self
/// slot), and one written as its NAME (`T`, `List.T`), which the loader records against
/// its canonical variable through the WI-954 channel [`type_param_global_var`] reads.
///
/// A name with NO canonical variable — a namespace-level opaque `sort Term = ?` — is
/// `None`, and that is a real distinction rather than a miss: it denotes a rigid abstract
/// type, one thing for every reader, so nothing about it conflates and instantiating it
/// would DESTROY information. `walk_type` leaves it alone for the same reason.
///
/// A HIGHER-KINDED PARAMETER IN FUNCTOR POSITION (`M[T = A]`, where `M` is the `Monad`
/// spec's own parameter — `stdlib/anthill/prelude/delay.anthill` writes it) is likewise
/// `None`, and it is the one spelling this cannot reach. Raised by /code-review; the
/// answer is that there is nothing to reach: `Term::Fn`'s functor is a `Symbol`, not a
/// child term, so no variable is representable there — and `walk_type` does not collapse
/// it either (its `extract_sort_ref_sym` answers `None` for a parameterized type and it
/// returns the term unchanged), so the position never conflates in the first place. The
/// ARGUMENTS of such a type are ordinary children and ARE instantiated. Reaching the
/// functor would take a representation change, not a wider predicate here.
///
/// THE FUNCTOR OF A PARAMETERIZED TYPE IS NOT REACHED, and that is a representation limit
/// rather than an omission (found by /code-review). `Monad.flatMap(m: M[T = A], …)` writes
/// its own parameter `M` in the functor position of a `Term::Fn`, which holds a `Symbol`
/// — there is no term there for a variable to occupy, so a higher-kinded parameter cannot
/// be instantiated in this spelling at all. Nothing conflates through it either:
/// `walk_type` reaches its collapse only via `extract_sort_ref_sym`, which answers `None`
/// for anything parameterized, so `M` is left as itself on both paths. The type's
/// ARGUMENTS are ordinary types and are instantiated normally. Making the functor
/// instantiable is a change to `Term::Fn`, not to this function.
///
/// THE TWO CHANNELS AGREE, MEASURED rather than argued. `walk_type` decides "this name is
/// a variable" by `is_sort_param_symbol` plus a `resolve_sort_alias` target that IS a
/// `Var::Global`; this reads the WI-954 canonical map instead, which WI-954 made the
/// single channel precisely so that route would stop being re-derived. A name the first
/// test accepts and the map does not answer for would be a residual conflation, so it was
/// counted: instrumented across the whole `wi_tests` corpus (3151 tests, full stdlib plus
/// every fixture), ZERO names diverged.
pub(super) fn denoted_type_param_var(kb: &KnowledgeBase, t: TermId) -> Option<VarId> {
    match kb.get_term(t) {
        Term::Var(Var::Global(v)) => Some(*v),
        Term::Ref(sym) | Term::Ident(sym) => type_param_global_var(kb, *sym),
        // WI-359: a bare parameter name also surfaces as a nullary `Fn` — the third
        // spelling WI-359 records for a bare parameter name, for the same reason.
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } if pos_args.is_empty() && named_args.is_empty() => type_param_global_var(kb, *functor),
        _ => None,
    }
}

/// WI-9C2PZ — does `t` mention anything [`instantiate_declared_term`] would rewrite?
///
/// A NON-ALLOCATING pre-scan, and it earns its place: the rewrite has to clone a `Fn`'s
/// argument vectors to release the `kb` borrow before recursing, so without this gate
/// every concrete parameter type in every rule-body call would pay a rebuild to produce
/// itself. Measured on a full stdlib load, the large majority of declared parameter /
/// field types mention no parameter at all (`String`, `Int64`, `List[Term]`).
fn declared_type_mentions_param(kb: &KnowledgeBase, t: TermId) -> bool {
    term_any_subterm(kb, t, &|t, _| denoted_type_param_var(kb, t).is_some())
}

/// WI-9C2PZ — the fresh variable `inst` stands `canonical` up as, minted on first use.
///
/// Named after the parameter it instantiates, so a diagnostic reading the resulting type
/// still says `?T` rather than an anonymous id.
fn instantiated_param_var(
    kb: &mut KnowledgeBase,
    canonical: VarId,
    inst: &mut ParamInstantiation,
) -> TermId {
    if let Some(t) = inst.get(&canonical.raw()) {
        return *t;
    }
    let v = kb.fresh_var(canonical.name());
    let t = kb.alloc(Term::Var(Var::Global(v)));
    inst.insert(canonical.raw(), t);
    t
}

/// WI-9C2PZ — [`instantiate_declared_type`]'s term half: rebuild `t` with every type
/// parameter it mentions replaced by this application's fresh variable for it.
fn instantiate_declared_term(
    kb: &mut KnowledgeBase,
    t: TermId,
    inst: &mut ParamInstantiation,
) -> TermId {
    if let Some(canonical) = denoted_type_param_var(kb, t) {
        return instantiated_param_var(kb, canonical, inst);
    }
    let Term::Fn {
        functor,
        pos_args,
        named_args,
    } = kb.get_term(t)
    else {
        return t;
    };
    let functor = *functor;
    let pos_args = pos_args.clone();
    let named_args = named_args.clone();
    let pos_args: SmallVec<[TermId; 4]> = pos_args
        .into_iter()
        .map(|a| instantiate_declared_term(kb, a, inst))
        .collect();
    let named_args: SmallVec<[(Symbol, TermId); 2]> = named_args
        .into_iter()
        .map(|(k, a)| (k, instantiate_declared_term(kb, a, inst)))
        .collect();
    kb.alloc(Term::Fn {
        functor,
        pos_args,
        named_args,
    })
}

/// WI-9C2PZ — a callee's declared parameter / field type with ITS OWN type parameters
/// instantiated by `inst`, so what this call site records is a type of something HERE.
///
/// WHAT WAS WRONG WITHOUT IT. [`collect_rule_var_types`] reads the declared type straight
/// out of the signature, and every written occurrence of one parameter denotes ONE
/// canonical variable KB-wide (WI-954). So every `eq` call in every rule in the KB
/// recorded the same `anthill.prelude.PartialEq.T` — for variables of unrelated types.
/// WI-741 made that survivable (a bare parameter neither displaces nor contradicts a
/// concrete type, and [`relation_clause_columns`] normalized it to a variable keyed BY
/// THE PARAMETER SYMBOL so column correlation survived) without touching the conflation
/// itself, which cost three things: two independent calls were treated as ONE correlation
/// class (`rule twoeq(?x, ?n) :- gen(?x, ?n), eq(?x, "a"), eq(?n, 1)` gave its two columns
/// one variable, so the CORRECT citation `twoeq("a", 1)` was refused); a variable forced
/// equal to a concrete one did not inherit its type; and which correlation class a
/// variable joined was decided by whichever parameter reached it first.
///
/// Instantiating per application retires all three at the producer, and retires WI-741's
/// two special cases with them: a per-call variable is an ordinary unification variable,
/// so [`constrain_vid`] can just unify. That unification is where `eq(?x, ?y), parent(of:
/// ?x, is: ?)` learns that BOTH variables are `String` — but it learns it into the
/// SUBSTITUTION, so the answer only reaches `var_types` because
/// [`collect_rule_var_types`] now resolves the map through it. The two halves are one
/// change and neither is separately correct; the measurement is at
/// `wi_9c2pz_per_application_type_params_test`'s control table.
///
/// The second half of the answer is WHETHER anything was instantiated — the gate on
/// [`constrain_literal_arg`]'s channel. It is threaded rather than re-derived by walking
/// the result for variables: the two questions have the same answer (after this runs, a
/// declared type carries a flexible variable exactly when this call minted one for it),
/// and only the threaded one says which question is being asked.
///
/// A `Value::Node` type carrier goes through the shared σ walk rather than the term
/// rebuild — the same [`crate::kb::node_occurrence::subst_value_type`] that
/// [`instantiate_poly_type`] freshens a ∀'s binders with, and for its reason: a
/// hand-rolled Node walk drifts from the σ every other rewriter uses.
///
/// NOTHING DRIVES THAT ARM, and saying so is better than letting the green suite imply
/// otherwise. Instrumented across the whole `wi_tests` corpus, a Node-carried declared
/// type reached here exactly TWICE, both times carrying zero variables — so both took the
/// early return and the freshening below has never run. Two bounds follow and neither is
/// a silent skip: the arm is written for the case rather than verified on it, and it
/// reaches the VARIABLE spelling ONLY — a parameter NAME nested inside a Node-carried type
/// (an arrow parameter's `S`, say) would not be reached, and would stay conflated as it is
/// today. Both become live together, when the WI-342 P4 producers start handing this
/// collector Node-carried parameterized types; the population to re-measure is this
/// counter.
pub(super) fn instantiate_declared_type(
    kb: &mut KnowledgeBase,
    ty: &Value,
    inst: &mut ParamInstantiation,
) -> (Value, bool) {
    match ty {
        Value::Term { id, .. } => {
            if !declared_type_mentions_param(kb, *id) {
                return (ty.clone(), false);
            }
            (Value::term(instantiate_declared_term(kb, *id, inst)), true)
        }
        _ => {
            let mut vars: Vec<VarId> = Vec::new();
            let mut seen = HashSet::new();
            crate::kb::node_occurrence::collect_value_type(kb, ty, &mut vars, &mut seen);
            if vars.is_empty() {
                return (ty.clone(), false);
            }
            let mut sigma = Substitution::new();
            for v in vars {
                let t = instantiated_param_var(kb, v, inst);
                sigma.bind_term(kb, v, t);
            }
            (
                crate::kb::node_occurrence::subst_value_type(kb, ty, &sigma).0,
                true,
            )
        }
    }
}

/// WI-20260923-32XFQ — an applied ARGUMENT as the two constraint walkers read it: a rule
/// head's `TermId` argument ([`collect_term_type_constraints`]) or a body OCCURRENCE
/// ([`collect_occurrence_type_constraints`]). The two questions either asks of one, and all
/// that differed between the twins they used to keep "in step on purpose": is it a
/// literal, and is it a variable — keyed by a `Global`'s raw id or a De Bruijn index, the
/// one key space a rule's head term and its body occurrences share.
pub(super) trait ConstrainedArg {
    fn literal(&self, kb: &KnowledgeBase) -> Option<Literal>;
    fn var_key(&self, kb: &KnowledgeBase) -> Option<u32>;
    /// The constructor an entity construction applies, or a constant constructor names.
    fn constructor(&self, kb: &KnowledgeBase) -> Option<Symbol>;
    /// Where the argument was written, where it carries a place.
    fn span(&self) -> Option<crate::span::SourceSpan>;
}

impl ConstrainedArg for TermId {
    fn literal(&self, kb: &KnowledgeBase) -> Option<Literal> {
        match kb.get_term(*self) {
            Term::Const(lit) => Some(lit.clone()),
            _ => None,
        }
    }
    fn var_key(&self, kb: &KnowledgeBase) -> Option<u32> {
        match kb.get_term(*self) {
            Term::Var(Var::Global(vid)) => Some(vid.raw()),
            Term::Var(Var::DeBruijn(idx)) => Some(*idx),
            _ => None,
        }
    }
    fn constructor(&self, kb: &KnowledgeBase) -> Option<Symbol> {
        match kb.get_term(*self) {
            Term::Fn { functor, .. } | Term::Ref(functor) => Some(*functor),
            _ => None,
        }
        .filter(|f| is_construction_functor(kb, *f))
    }
    fn span(&self) -> Option<crate::span::SourceSpan> {
        None
    }
}

impl ConstrainedArg for Rc<NodeOccurrence> {
    fn literal(&self, _kb: &KnowledgeBase) -> Option<Literal> {
        match self.as_expr() {
            Some(Expr::Const(lit)) => Some(lit.clone()),
            _ => None,
        }
    }
    fn var_key(&self, _kb: &KnowledgeBase) -> Option<u32> {
        match self.as_expr() {
            Some(Expr::Var(Var::Global(vid))) => Some(vid.raw()),
            Some(Expr::Var(Var::DeBruijn(idx))) => Some(*idx),
            _ => None,
        }
    }
    fn constructor(&self, kb: &KnowledgeBase) -> Option<Symbol> {
        let expr = self.as_expr()?;
        match expr {
            Expr::Ref(name) => Some(*name),
            _ => expr_call_parts(expr).map(|(functor, _, _)| functor),
        }
        .filter(|f| is_construction_functor(kb, *f))
    }
    fn span(&self) -> Option<crate::span::SourceSpan> {
        Some(self.span)
    }
}

/// WI-9C2PZ — constrain one applied ARGUMENT position: [`constrain_vid`] for a variable,
/// plus the LITERAL channel a variable position does not need — for either walker's
/// carrier ([`ConstrainedArg`]), which is what used to be two twins kept in step by hand.
///
/// A literal argument is not a variable, so it recorded nothing at all — and for a
/// parameter that is the difference between knowing the parameter's type and never
/// knowing it. `rule twoeq(?x, ?n) :- gen(?x, ?n), eq(?x, "a"), eq(?n, 1)` has no other
/// typing source for either column (a rule subgoal types nothing), so without this the
/// two columns instantiate to two unconstrained variables — independent, which is the
/// repair, but also untyped, so `twoeq(1, "a")` would be accepted as readily as
/// `twoeq("a", 1)`. Reading the literal makes the columns `String` and `Int64`. The gate
/// that scopes it is [`constrain_literal_arg`]'s.
///
/// Anything neither a literal nor a variable constrains nothing here, and the answer is
/// `false`: the position's type is then the argument's own to meet, where its walker
/// reaches it ([`NestedPositions`]).
pub(super) fn constrain_arg<A: ConstrainedArg>(
    kb: &mut KnowledgeBase,
    arg: &A,
    expected_type: &Value,
    instantiated: bool,
    // Whether the position is a call's argument, which needs its value's type known.
    demand: bool,
    st: &mut ClauseConstraints,
) -> bool {
    if says_nothing_of_a_value(kb, expected_type) {
        return true;
    }
    if let Some(lit) = arg.literal(kb) {
        constrain_literal_arg(kb, &lit, expected_type, instantiated, &mut st.subst);
        return true;
    }
    if let Some(vid) = arg.var_key(kb) {
        constrain_vid(kb, vid, expected_type, instantiated, demand, st);
        return true;
    }
    false
}

/// Shared core of [`constrain_arg`]'s variable arm: record the
/// var's expected type, or unify against an existing one (keyed by the var's
/// raw id / De Bruijn idx — the same key space for a rule's head term and its
/// body occurrences, both closed against the same `vars`).
///
/// WI-9C2PZ — A PER-CALL PARAMETER IS A PLACEHOLDER, NOT A STATEMENT ABOUT THE VARIABLE,
/// and the two arms below are what that costs. Every position is UNIFIED now (WI-741's
/// "a bare parameter never unifies" arms are gone — they existed because the parameter
/// was one variable shared by every call in the KB, and [`instantiate_declared_type`]
/// removed that), but two things still turn on where a type came from:
///
///   * A DECLARED position TAKES OVER from a parameter placeholder. `var_types` answers
///     "what do this variable's own positions say", and a callee's parameter says
///     nothing — it is recorded so the correlation survives (`eq(?x, ?y)` puts both
///     variables on one variable), not as an answer.
///   * A DISAGREEMENT INVOLVING A PARAMETER IS THE CALL'S FAULT, NOT THE VARIABLE'S, so
///     it must NOT set `subst.contradiction`. That flag makes [`type_rule_bodies`] skip
///     the rule entirely — no dispatch, no WI-603 stamping, and for a namespace-level
///     rule no report at all — which SUPPRESSES the located error the ordinary call
///     check would raise. MEASURED, three shapes, all found by /code-review after the
///     first cut set the flag unconditionally:
///
///     | rule | before | first cut |
///     |---|---|---|
///     | `row(a: ?a, s: ?s), eq(?a, ?s)` | `eq.b (op-arg): expected Int64, got String` | LOADS CLEAN |
///     | `holder(f: ?f), eq(?f, 0)` | `eq.b (op-arg): expected Float, got Int64` | LOADS CLEAN |
///     | `eq(?x, "s"), scored(pts: ?x)` | `eq.b (op-arg): expected Int64, got String` | LOADS CLEAN |
///
///     The third is why the test is on the RECORD's provenance and not just on this
///     call's: the placeholder was pinned to `String` by a literal, and it is the
///     `scored` position arriving afterwards that must take over so the `eq` call is
///     still checked against `Int64`.
///
/// What still sets the flag is what always did and what nothing else reports: two
/// DECLARED positions of one variable that disagree (`parent(of: ?x, is: ?), scored(who:
/// ?, pts: ?x)`). Entity constructors in goal position are not calls, so no located check
/// covers them — measured, that shape loads clean at namespace level on both trees.
fn constrain_vid(
    kb: &mut KnowledgeBase,
    vid: u32,
    expected_type: &Value,
    from_param: bool,
    demand: bool,
    st: &mut ClauseConstraints,
) {
    if !demand {
        st.demand_only.remove(&vid);
    } else if !st.var_types.contains_key(&vid) {
        st.demand_only.insert(vid);
    }
    let Some(existing) = st.var_types.get(&vid).cloned() else {
        // Nothing known yet — record what this position says.
        st.var_types.insert(vid, expected_type.clone());
        if from_param {
            st.param_backed.insert(vid);
        }
        return;
    };
    let existing_from_param = st.param_backed.contains(&vid);
    // Unify either way: that is what binds a call's parameter to the variable's concrete
    // type, so a SIBLING argument of the same call inherits it.
    if !unify_types(kb, &mut st.subst, &existing, expected_type)
        && !from_param
        && !existing_from_param
    {
        st.subst.contradiction = true;
    }
    // A declared position takes over from a placeholder — including when the two just
    // disagreed, because the declared type is what the variable is and recording it is
    // what leaves the offending CALL checkable.
    if !from_param && existing_from_param {
        st.var_types.insert(vid, expected_type.clone());
        st.param_backed.remove(&vid);
    }
}

/// WI-246: occurrence-body twin of [`collect_term_type_constraints`] — walk a
/// rule-body goal OCCURRENCE, constraining op-arg (positional) / entity-field
/// (named) var positions to their declared types. Mirrors the term walker's
/// op/entity functor dispatch and recursion, reading `Expr` instead of
/// `Term::Fn` so the typer no longer reads the term body. Control-flow / reflect
/// forms add no constraints themselves but are recursed into via their children.
///
/// Reflect-data forms carry their sub-pattern / param / type-annotation as
/// `TermId` fields (not occ children), which `for_each_child` does not
/// enumerate. They are closed to the rule's De Bruijn space by
/// `node_to_debruijn`, so we type-check them via the term collector — covering
/// op/entity calls nested in a pattern/param exactly as the term walker did.
pub(super) fn collect_occurrence_type_constraints(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    // The declared type of the position `occ` fills, where its parent is an application
    // that declares one ([`NestedPositions`]); `None` for a top-level goal.
    position: Option<&Value>,
    // Where in the body `occ` sits, as the dispatch walk reads it ([`BodyPos`]): a goal is
    // read as a relation, a call's result column or a call, and data as data.
    pos: BodyPos,
    // Whether `occ` is part of a goal the clause commits to — a conjunct, not a `|` branch,
    // a quantifier's body or a negation ([`GoalCommit::Top`]). Only such a goal's positions
    // are read after the walk: a branch types a variable for the branch alone, so
    // `(pi(?x) | ps(?x))` over an `Int64` and a `String` column would make `?x` the first.
    committed: bool,
    st: &mut ClauseConstraints,
) {
    // WI-298: descend into Pattern children so a var living in a pattern's
    // nested type-annotation Expr leaf gets the same op-arg / entity-field
    // constraint walk applied to the rest of the rule. Symmetric with
    // `node_to_debruijn` and `collect_occurrence_global_vars_ordered`.
    if occ.as_pattern().is_some() {
        for_each_pattern_child(occ, |c| {
            collect_occurrence_type_constraints(kb, c, None, BodyPos::Untyped, false, st)
        });
        return;
    }
    let Some(expr) = occ.as_expr() else { return };
    // A type written as a term — the spec instance of a `require[…]`, a projection in it,
    // a sort's bracket written as a value — is no data, and nothing in it is typed.
    if type_written_as_term(kb, expr) {
        return;
    }
    let goal = matches!(pos, BodyPos::Goal(_) | BodyPos::GoalTuple(_));
    let nested = match expr_call_parts(expr) {
        Some((functor, pos_args, named_args)) => {
            if goal && committed {
                constrain_domain_test(kb, functor, pos_args, st);
            }
            let bracket = call_bracket_instances(kb, occ, expr, functor);
            let (nested, result) =
                constrain_application(kb, functor, pos_args, named_args, &bracket, position, st);
            // THE CALL'S RESULT IS OF THE SLOT IT FILLS, and at goal position the extra
            // argument of `f(a₁…aₙ, ?r)` is that result (§5.3's functional relation): what
            // the resolver reads the goal as, asked of the resolver. A goal is no value, so
            // the slot a connective declares for it (`not(query: Term)`) is not its type.
            if let Some(result) = result.filter(|_| committed) {
                if goal {
                    if let Some((_, n)) = kb.functional_relation_goal(&Value::Node(Rc::clone(occ)))
                    {
                        if let Some(arg) = pos_args.get(n) {
                            st.late.push(LatePosition::ResultColumn {
                                arg: Rc::clone(arg),
                                result,
                            });
                        }
                    }
                } else if let Some(position) = position {
                    st.late.push(LatePosition::CallResult {
                        position: position.clone(),
                        result,
                        at: occ.span,
                    });
                }
            }
            if goal && committed {
                if let Some(functor) = rule_goal_functor(kb, expr, pos) {
                    st.late.push(LatePosition::RuleGoal {
                        functor,
                        goal: Rc::clone(occ),
                    });
                }
            }
            nested
        }
        None => {
            match expr {
                Expr::Ref(name) => {
                    constrain_constant_constructor(kb, *name, position, &mut st.subst)
                }
                Expr::DotApply { .. } => {
                    if let Some(position) = position.filter(|_| committed) {
                        st.late.push(LatePosition::DotResult {
                            dot: Rc::clone(occ),
                            position: position.clone(),
                        });
                    }
                }
                _ => {}
            }
            NestedPositions::new()
        }
    };
    // Every other form adds no constraint of its own and is reached through the child
    // walk below.
    //
    // WI-819: `Expr::Let` no longer has a type-positional field. Its
    // annotation is an Expr-kind child of the PATTERN occurrence, and the
    // pattern arm at the top of this function already descends into it — so
    // a ground annotation's nested op/entity calls are constrained through
    // the SAME recursion, not a parallel term-collector call.
    // WI-318: Lambda / LambdaWithin params AND MatchBranch.pattern
    // are now Pattern-kind occurrences walked by `for_each_child`
    // below. Any nested TermId-typed children (e.g. a Var pattern's
    // type_ann Expr-kind occurrence) are reached via that recursion;
    // no explicit term-level call needed here.
    //
    // An application's children are its arguments, positional then named
    // (`for_each_child`), which is the order [`NestedPositions`] counts in.
    let mut children: SmallVec<[Rc<NodeOccurrence>; 8]> = SmallVec::new();
    for_each_child(expr, |c| children.push(Rc::clone(c)));
    let child_pos = child_body_positions(kb, expr, pos, children.len());
    for (index, (c, p)) in children.iter().zip(child_pos).enumerate() {
        let position = nested_position(&nested, index);
        let child_committed = match p {
            BodyPos::Goal(commit) | BodyPos::GoalTuple(commit) => {
                committed && commit == GoalCommit::Top
            }
            BodyPos::Value => committed,
            BodyPos::Untyped => false,
        };
        collect_occurrence_type_constraints(kb, c, position, p, child_committed, st);
    }
}

/// What an operation call's own bracket binds its type parameters to, read as the call's
/// typing reads it ([`seed_op_type_args`]: a key by its name, a positional by the next
/// parameter no key took, the operation's own and then its sort's). Empty where the call
/// writes no bracket, or one its typing refuses — which that typing reports.
fn call_bracket_instances(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    expr: &Expr,
    functor: Symbol,
) -> Vec<(VarId, TermId)> {
    let Expr::Apply { type_args, .. } = expr else {
        return Vec::new();
    };
    if type_args.is_empty() {
        return Vec::new();
    }
    let Some(op) = lookup_operation_info_full(kb, functor) else {
        return Vec::new();
    };
    let mut seeded = Substitution::new();
    if seed_op_type_args(kb, &mut seeded, &TypingEnv::empty(), &op, occ, functor, None).is_err() {
        return Vec::new();
    }
    let bound: Vec<(VarId, Value)> = seeded
        .bindings
        .iter()
        .map(|(v, val)| (*v, val.clone()))
        .collect();
    bound
        .into_iter()
        .filter_map(|(v, val)| {
            crate::kb::node_occurrence::value_to_term(kb, &val)
                .ok()
                .map(|t| (v, t))
        })
        .collect()
}

/// The relation a goal at `pos` is a goal on, read as the resolver reads it: an application
/// whose functor heads clauses and is neither a connective, an operation, an entity, a
/// builtin nor a sort — each of those is read by its own declaration.
pub(super) fn rule_goal_functor(kb: &KnowledgeBase, expr: &Expr, pos: BodyPos) -> Option<Symbol> {
    let Expr::Apply {
        functor, pos_args, ..
    } = expr
    else {
        return None;
    };
    let functor = *functor;
    let wrapper = matches!(pos, BodyPos::GoalTuple(_)) && kb.local_name_of(functor) == "tuple";
    if wrapper
        || !kb.goal_slot_readings(functor, pos_args.len()).is_empty()
        || lookup_operation_info_full(kb, functor).is_some()
        || kb.is_entity_constructor(functor)
        || kb.builtin_of(functor).is_some()
        || kb.has_kind(functor, crate::intern::SymbolKind::Sort)
    {
        return None;
    }
    kb.rules_by_functor_iter(functor).next().map(|_| functor)
}

/// The positions of one application whose argument is neither a literal nor a variable,
/// each with the declared type of the parameter or field it fills: the argument's index
/// among the application's arguments, positional then named, and that type at this
/// application's instantiation.
///
/// [`constrain_arg`] reads a literal and a variable against the declared type where the
/// application is read. Any other argument is a term of its own, read when its walker
/// reaches it, and it is handed the type here so that what it constructs meets the
/// position it stands in ([`constrain_application`]).
pub(super) type NestedPositions = SmallVec<[(usize, Value); 2]>;

/// The declared type [`NestedPositions`] holds for argument `index`, if any.
pub(super) fn nested_position(nested: &NestedPositions, index: usize) -> Option<&Value> {
    nested.iter().find(|(i, _)| *i == index).map(|(_, t)| t)
}

/// Constrain the op-arg (positional) / entity-field (named) argument positions of one
/// application — of a rule head's `Term::Fn` or a body occurrence alike: the op/entity
/// dispatch both walkers share ([`ConstrainedArg`]). Answers the positions left to the
/// arguments themselves ([`NestedPositions`]).
///
/// A CONSTRUCTOR'S APPLICATION IS OF ITS SORT, at the parameters this application's fields
/// are read at, and that type is unified with the declared type of the position the
/// application fills (`position`). In `?p <=> box(a: ?x, b: ?y)` the two sides of `<=>`
/// are one `T`, and `box` constructs `Box[T = t]` over fields typed `t`: so `?p` is
/// `Box[T = t]` and `?x` is `t`, one variable, which a citation's argument for `?p` then
/// binds for `?x` as well. Without it `?p` stayed the bare `T` of `<=>` and nothing said
/// that `?x` is at `Box`'s parameter, so a condition of the clause witnessed by `?x` could
/// not be met from the caller's own `requires`.
///
/// A disagreement is not recorded as a contradiction of the rule, for the reason
/// [`constrain_literal_arg`] gives: it is the enclosing call's argument error, and flagging
/// the rule would skip the check that reports it. A constructor that does not fit its
/// position pins nothing, the parameters it does share with the position included
/// ([`constrain_constructed`]).
///
/// The second half of the answer is an operation's result type at this application's
/// instantiation, for the walker to give to the slot the call fills.
pub(super) fn constrain_application<A: ConstrainedArg>(
    kb: &mut KnowledgeBase,
    functor: Symbol,
    pos_args: &[A],
    named_args: &[(Symbol, A)],
    // What the call's own bracket binds its type parameters to (`f[T = Int64](…)`,
    // [`call_bracket_instances`]): each the type that parameter is instantiated at here.
    bracket: &[(VarId, TermId)],
    position: Option<&Value>,
    st: &mut ClauseConstraints,
) -> (NestedPositions, Option<CallResult>) {
    // WI-9C2PZ: ONE [`ParamInstantiation`] per application — see
    // [`instantiate_declared_type`].
    let mut inst = ParamInstantiation::new();
    let mut nested = NestedPositions::new();
    let mut result = None;
    if let Some(op) = lookup_operation_info_full(kb, functor) {
        for &(param, ty) in bracket {
            inst.insert(param.raw(), ty);
        }
        // The parameter a positional argument FILLS, not the one at its index: it ranks
        // among the parameters the labels left open ([`positional_param_indices`]). By
        // index, `pick(?l, k: 1)` over `(k: Int64, l: Leaf)` typed `?l` as `Int64`, and a
        // later `Desc.describe(?l, ?r)` was refused for a carrier the clause never had.
        let pos_params = positional_param_indices(kb, &op.params, pos_args.len(), named_args);
        let mut params: Vec<(Symbol, ArgType)> = Vec::new();
        for (index, (arg, param)) in pos_args.iter().zip(pos_params).enumerate() {
            // WI-341 Stage A: seed inference from the param type carrier-agnostically.
            if let Some((param_sym, param_type)) = param.and_then(|p| op.params.get(p)) {
                let (param_type, instantiated) =
                    instantiate_declared_type(kb, param_type, &mut inst);
                let arg_type = match (arg.var_key(kb), arg.literal(kb)) {
                    (Some(d), _) => ArgType::Var(d),
                    (None, Some(lit)) => ArgType::Of(literal_sort(kb, &lit)),
                    (None, None) => ArgType::Of(param_type.clone()),
                };
                params.push((*param_sym, arg_type));
                // A parameter the argument converts to — `Option[T]`, which a bare `T` is
                // wrapped into — says what the call takes, not what the variable is: it is
                // the call's placeholder, as a parameter of the callee's own type is.
                let placeholder = instantiated || is_option_type(kb, &param_type);
                // A demand is a parameter of a stated type: one of the callee's own type
                // parameters — a spec's carrier, dispatched by the value — takes any value.
                let demand = !instantiated && !kb.is_equality_connective_functor(functor);
                if !constrain_arg(kb, arg, &param_type, placeholder, demand, st) {
                    nested.push((index, param_type));
                }
            }
        }
        result = Some(CallResult {
            ty: instantiate_declared_type(kb, &op.return_type, &mut inst).0,
            params,
        });
    } else if let Some(ty) =
        collection_literal_type(kb, functor, pos_args, named_args, &mut nested, st)
    {
        // A tuple, list or set literal, stored as the reflect entity that writes it, is of
        // the collection's type, which the entity's fields do not declare.
        if let Some(position) = position {
            let mut trial = st.subst.clone();
            if unify_types(kb, &mut trial, position, &ty) {
                st.subst = trial;
            }
        }
    } else if !st.checks_constructions && is_reflect_syntax(kb, functor) {
        // An equation's sides are stored as the reflect terms that write them (`?b.v` as a
        // `dot_apply`): syntax, whose fields say nothing of the variables in them.
    } else if let Some(field_types) = kb.entity_field_types(functor) {
        let field_types = field_types.to_vec();
        for (field_sym, field_type) in &field_types {
            if let Some(named) = named_args.iter().position(|(s, _)| s == field_sym) {
                // WI-341 Stage A: field type is a carrier-agnostic `Value` —
                // constrain directly, no re-grounding to a term.
                let (field_type, instantiated) =
                    instantiate_declared_type(kb, field_type, &mut inst);
                let arg = &named_args[named].1;
                if st.checks_constructions && !argument_fits_field(kb, arg, &field_type, st) {
                    st.found.push(ClauseDisagreement {
                        class: DisagreementClass::ConstructionField,
                        span: arg.span().or(st.at),
                    });
                }
                if !constrain_arg(kb, arg, &field_type, instantiated, false, st) {
                    nested.push((pos_args.len() + named, field_type));
                }
            }
        }
        if let Some(position) = position {
            constrain_constructed(kb, functor, position, &mut inst, &mut st.subst);
        }
    }
    (nested, result)
}

/// Unify `position` with the sort `constructor` constructs, at the parameters `inst`
/// reads this application's fields at ([`constrain_application`]).
///
/// ON A COPY, kept only where the two unify. A unification that fails has bound what it
/// met before the disagreement: `holder(h: w2(a: ?x, b: "s"))` over `h: W2[A = E, B =
/// Int64]` agrees on `A` and then refuses `B`, and the agreement on `A` would tie `?x` to
/// `holder`'s `E` on the word of a term that is no `holder` field at all.
///
/// A sort one of whose declared parameters has no variable says nothing here. The loader
/// has refused it — a dotted `sort Inner.T = ?` in a secondary entry registers such a
/// parameter — and [`own_application`] asserts that every parameter has one.
fn constrain_constructed(
    kb: &mut KnowledgeBase,
    constructor: Symbol,
    position: &Value,
    inst: &mut ParamInstantiation,
    subst: &mut Substitution,
) {
    let Some(sort) = kb.sort_of_constructor(constructor) else {
        return;
    };
    let published = kb
        .type_param_syms_of(sort)
        .iter()
        .all(|&param| kb.canonical_type_param_var(param).is_some());
    if !published {
        return;
    }
    let own = Value::term(own_application(kb, sort));
    let (constructed, _) = instantiate_declared_type(kb, &own, inst);
    let mut trial = subst.clone();
    if unify_types(kb, &mut trial, position, &constructed) {
        *subst = trial;
    }
}

/// A constructor that takes no field is written as its name, with no argument list to
/// apply: `red`, `none`. It is of its sort as an application is
/// ([`constrain_application`]), at parameters of its own. A constructor that has fields,
/// written as its name, is the function that constructs, and says nothing here.
pub(super) fn constrain_constant_constructor(
    kb: &mut KnowledgeBase,
    name: Symbol,
    position: Option<&Value>,
    subst: &mut Substitution,
) {
    let Some(position) = position else { return };
    if kb.entity_field_types(name).is_some_and(|fields| fields.is_empty()) {
        constrain_constructed(kb, name, position, &mut ParamInstantiation::new(), subst);
    }
}

/// WI-9C2PZ — the LITERAL channel itself, one copy for both walkers so the gate that
/// scopes it cannot come to mean two things. Pins `expected_type` to the literal's own
/// sort, and a disagreement is a genuine contradiction in the rule.
///
/// `instantiated` is that gate: the literal is read ONLY into a parameter THIS application
/// just instantiated. That is scope, not caution — against a concrete parameter an
/// argument's type is the ordinary type-check's business, which this pre-pass has no
/// standing to re-decide (and could not, for anything but a literal); against an
/// instantiated one this pre-pass owns the only channel that says what the parameter is.
/// Ungated it would also start manufacturing refusals in reflect-shaped code, where a
/// `Bool` literal in a `Term` slot is ordinary.
fn constrain_literal_arg(
    kb: &mut KnowledgeBase,
    lit: &Literal,
    expected_type: &Value,
    instantiated: bool,
    subst: &mut Substitution,
) {
    if !instantiated {
        return;
    }
    // A DISAGREEMENT HERE IS NOT RECORDED as a rule-wide contradiction — see
    // [`constrain_vid`], whose table's second row is exactly this shape. `eq(?f, 0)`
    // beside `holder(f: Float)` is an argument error at the `eq` call, which the ordinary
    // call check reports at the literal's own span; flagging the rule would skip that
    // check and lose it. The failed unification simply pins nothing.
    let lit_type = literal_sort(kb, lit);
    unify_types(kb, subst, expected_type, &lit_type);
}

/// `domain(?v, T)`, the run-time type test: `?v` is a `T` where the test holds, as a position
/// that declares `T` says, and it is narrowed. A `T` the loader refuses — naming no sort, a spec
/// over its parameter — says nothing.
fn constrain_domain_test(
    kb: &mut KnowledgeBase,
    functor: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    st: &mut ClauseConstraints,
) {
    if kb.builtin_of(functor) != Some(crate::kb::resolve::BuiltinTag::TypeDomain) {
        return;
    }
    let [value, ty] = pos_args else { return };
    let Some(d) = value.var_key(kb) else { return };
    let Ok(ty) = crate::kb::node_occurrence::value_to_term(kb, &Value::Node(Rc::clone(ty))) else {
        return;
    };
    let ty = Value::term(ty);
    if type_mentions_unresolved_name(kb, &ty) || parameter_spec_written_as_type(kb, &ty).is_some() {
        return;
    }
    constrain_vid(kb, d, &ty, false, false, st);
}

/// `found` with each place's disagreement of one class once: a late position reads an
/// argument the walk read already.
pub(super) fn found_once(found: Vec<ClauseDisagreement>) -> Vec<ClauseDisagreement> {
    let mut once: Vec<ClauseDisagreement> = Vec::with_capacity(found.len());
    for d in found {
        if !once.iter().any(|o| o.class == d.class && o.span == d.span) {
            once.push(d);
        }
    }
    once
}

/// Read the constructions a fact writes, as a clause's are read ([`argument_fits_field`]),
/// and count what does not fit ([`count_clause_disagreements`]). A fact the loader made, which
/// carries no place, is not read.
pub(super) fn check_fact_constructions(kb: &mut KnowledgeBase, rid: RuleId) {
    let (Some(at), Some(head)) = (kb.rule_head_span(rid), kb.fact_head_term(rid)) else {
        return;
    };
    if is_equation(kb, rid) {
        return;
    }
    let mut st = ClauseConstraints::new();
    st.at = Some(at);
    collect_term_type_constraints(kb, head, None, &mut st);
    count_clause_disagreements(kb, &found_once(st.found));
}

/// Whether `rid` is an equation — directional (`@[simp]`) or a guarded `lhs = rhs :- g`, its
/// head an application of an equality connective: a rewrite pattern, not data.
pub(super) fn is_equation(kb: &KnowledgeBase, rid: RuleId) -> bool {
    kb.is_directional_equation(rid)
        || kb
            .rule_head_value(rid)
            .head(kb)
            .functor_sym()
            .is_some_and(|f| kb.is_equality_connective_functor(f))
}

/// Whether `functor` is one of the reflect `Expr` forms a term writes syntax as.
fn is_reflect_syntax(kb: &KnowledgeBase, functor: Symbol) -> bool {
    kb.sort_of_constructor(functor)
        .is_some_and(|s| kb.qualified_name_of(s) == "anthill.reflect.Expr")
}

/// Whether `functor` builds a value of an entity: a constructor, and not a type written as a
/// value — a sort's type face (`Item[]`), one of `TypeExtractor`'s forms.
fn is_construction_functor(kb: &KnowledgeBase, functor: Symbol) -> bool {
    kb.entity_field_types(functor).is_some() && !is_type_form_functor(kb, functor)
}

/// Whether a construction's argument fits the field it fills, as an operation's argument is
/// checked against its parameter: a literal's sort and a construction's sort, with the
/// argument conversions (a `Term` field admits every value, an `Option[T]` field a bare `T`,
/// a field at a bare spec a value of a sort that provides it). Any other argument — a variable, a call, a
/// collection literal, a type written as a term — is met by its own position.
fn argument_fits_field<A: ConstrainedArg>(
    kb: &mut KnowledgeBase,
    arg: &A,
    field: &Value,
    st: &ClauseConstraints,
) -> bool {
    if says_nothing_of_a_value(kb, field) {
        return true;
    }
    let actual = if let Some(lit) = arg.literal(kb) {
        literal_sort(kb, &lit)
    } else if let Some(ctor) = arg.constructor(kb) {
        if kb.is_ordered_product_functor(ctor) || SeqLiteral::of_constructor(kb, ctor).is_some()
        {
            return true;
        }
        let Some(sort) = kb.sort_of_constructor(ctor) else {
            return true;
        };
        let published = kb
            .type_param_syms_of(sort)
            .iter()
            .all(|&param| kb.canonical_type_param_var(param).is_some());
        if !published {
            return true;
        }
        let own = Value::term(own_application(kb, sort));
        instantiate_declared_type(kb, &own, &mut ParamInstantiation::new()).0
    } else {
        return true;
    };
    // A field of the construction's own parameter reads what the clause has bound; one with
    // no variable in it needs nothing of the clause's substitution.
    let reads_subst = type_mentions_flex_var(kb, field);
    let scratch = |st: &ClauseConstraints| {
        if reads_subst {
            st.subst.clone()
        } else {
            Substitution::new()
        }
    };
    if unify_types(kb, &mut scratch(st), field, &actual)
        || types_compatible(kb, &mut scratch(st), &actual, field)
    {
        return true;
    }
    // A value of a sort that provides the field's bare spec, as at an operation's argument.
    if let (Some(actual_base), Some(spec)) =
        (type_base_sort_view(kb, &actual), extract_sort_ref_sym(kb, field))
    {
        if sort_provides_admissibly(kb, actual_base, spec) {
            return true;
        }
    }
    if is_option_type(kb, field) && !is_option_type(kb, &actual) {
        if let Some(element) = extract_type_param(kb, field, "T") {
            if unify_types(kb, &mut scratch(st), &element, &actual)
                || types_compatible(kb, &mut scratch(st), &actual, &element)
            {
                return true;
            }
        }
    }
    note_disagreement(kb, &st.subst, field, &actual);
    false
}

/// The type of a tuple, list or set literal — `functor` the reflect entity it is stored as —
/// from its elements: each element typed at a component of its own, a tuple's by its label, a
/// list's and a set's all at one element type; `None` for any other functor. An element that
/// is neither a literal nor a variable is given its component as its position (`nested`).
fn collection_literal_type<A: ConstrainedArg>(
    kb: &mut KnowledgeBase,
    functor: Symbol,
    pos_args: &[A],
    named_args: &[(Symbol, A)],
    nested: &mut NestedPositions,
    st: &mut ClauseConstraints,
) -> Option<Value> {
    let component = |kb: &mut KnowledgeBase| {
        let name = kb.intern("element");
        let fresh = kb.fresh_var(name);
        Value::term(kb.alloc(Term::Var(Var::Global(fresh))))
    };
    let mut meet = |kb: &mut KnowledgeBase, index: usize, arg: &A, ty: &Value, st: &mut _| {
        if !constrain_arg(kb, arg, ty, true, false, st) {
            nested.push((index, ty.clone()));
        }
    };
    if kb.is_ordered_product_functor(functor) {
        let mut pos = Vec::with_capacity(pos_args.len());
        for (i, arg) in pos_args.iter().enumerate() {
            let ty = component(kb);
            meet(kb, i, arg, &ty, st);
            pos.push(ty);
        }
        let mut named = Vec::with_capacity(named_args.len());
        for (j, (label, arg)) in named_args.iter().enumerate() {
            let ty = component(kb);
            meet(kb, pos_args.len() + j, arg, &ty, st);
            named.push((*label, ty));
        }
        return Some(tuple_value_type(kb, pos, named));
    }
    let kind = SeqLiteral::of_constructor(kb, functor)?;
    let element = component(kb);
    for (i, arg) in pos_args.iter().enumerate() {
        meet(kb, i, arg, &element, st);
    }
    let span = crate::span::SourceSpan::new(crate::span::SourceId::from_raw(0), 0, 0);
    Some(seq_literal_type(kb, kind, element, span, None))
}

/// Whether a position typed `ty` says nothing of the value that fills it: `Term`, which
/// every value converts to, as an operation's argument does at a parameter of that type.
fn says_nothing_of_a_value(kb: &KnowledgeBase, ty: &Value) -> bool {
    is_reflect_term_type(kb, ty)
}

/// Whether `expr` is a type written as a term: an application of one of the structural
/// type forms (`TypeExtractor`'s constructors, an arrow), or a sort's type face (`Box[…]`
/// written as a value).
fn type_written_as_term(kb: &KnowledgeBase, expr: &Expr) -> bool {
    let (Expr::Apply { functor, .. } | Expr::Ref(functor)) = expr else {
        return false;
    };
    rule_body_type_term(kb, expr) || is_type_form_functor(kb, *functor)
}

/// Whether `functor` writes a type as a value: a sort's type face (`Item[]`), or one of
/// `TypeExtractor`'s structural forms.
fn is_type_form_functor(kb: &KnowledgeBase, functor: Symbol) -> bool {
    functor.is_type_face()
        || kb
            .sort_of_constructor(functor)
            .is_some_and(|s| kb.qualified_name_of(s) == "anthill.prelude.TypeExtractor")
}

/// Read the positions of a clause the walk left for after it ([`LatePosition`]): the head's
/// written bounds first, then the rest in the order they were written, and a dot last, once
/// what types its receiver has been read. Each on a trial copy, kept where it fits and
/// recorded as a [`ClauseDisagreement`] where it does not. Answers the rigids the bounds
/// were read at, which the caller lets vary again once the clause is typed
/// ([`unrigidify_clause_types`]).
///
/// THE ENCLOSING SORT'S PARAMETER A BOUND NAMES IS RIGID HERE, as it is in an operation
/// body: the clause holds at every instance, so its body may not fix the parameter. Read as
/// an ordinary variable, `rule pr(?x: Self) :- ?x <=> b3(v: 5)` in `sort Box3[T]` bound `T`
/// to `Int64`, and every type that names `T` in the clause read `Int64` with it.
pub(super) fn settle_late_positions(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    head: TermId,
    st: &mut ClauseConstraints,
    disagreements: &mut Vec<ClauseDisagreement>,
) -> Vec<(VarId, VarId)> {
    let span = kb.rule_head_span(rid);
    let rigids = settle_head_bounds(kb, rid, st, disagreements, span);
    let own = kb.head_functor(head);
    // What can be read only once something else is: a dot, whose receiver must be typed,
    // and a result whose type is computed from its operands (`field_access`'s `FieldOf`,
    // the field's type once the receiver's is known).
    let mut waiting: Vec<LatePosition> = Vec::new();
    while !st.late.is_empty() {
        for late in std::mem::take(&mut st.late) {
            if let LatePosition::RuleGoal { functor, goal } = &late {
                let Some(columns) = rule_goal_columns_at(kb, own, *functor) else {
                    note_unread_goal(kb, st, goal);
                    continue;
                };
                let mut trial = st.trial();
                if constrain_goal_at_columns(kb, &mut trial, goal, &columns) {
                    st.commit(trial);
                } else {
                    let fixed = fits_once_parameters_vary(kb, st, &rigids, |kb, varying| {
                        constrain_goal_at_columns(kb, varying, goal, &columns)
                    });
                    disagreements.push(ClauseDisagreement {
                        class: if fixed {
                            DisagreementClass::SortParameterFixed
                        } else {
                            DisagreementClass::RuleGoal
                        },
                        span: Some(goal.span),
                    });
                }
                continue;
            }
            let computed = match &late {
                LatePosition::CallResult { result, .. }
                | LatePosition::ResultColumn { result, .. } => {
                    value_contains_projection(kb, &result.ty)
                        || return_reducible_ctors(kb, &result.ty).iter().any(|f| *f)
                }
                LatePosition::DotResult { .. } => true,
                LatePosition::RuleGoal { .. } => false,
            };
            if computed || !settle_typed_position(kb, rid, st, &late, &rigids, disagreements) {
                waiting.push(late);
            }
        }
    }
    // Each round reads what the last one made readable.
    loop {
        let before = waiting.len();
        for late in std::mem::take(&mut waiting) {
            if !settle_typed_position(kb, rid, st, &late, &rigids, disagreements) {
                waiting.push(late);
            }
        }
        if waiting.is_empty() || waiting.len() == before {
            break;
        }
    }
    demands_on_some_type(kb, rid, st);
    rigids
}

/// Read one late position that types a slot by a type ([`LatePosition::CallResult`],
/// [`LatePosition::ResultColumn`], [`LatePosition::DotResult`]), or answer `false` where that
/// type cannot be read yet ([`settle_late_positions`]).
fn settle_typed_position(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    st: &mut ClauseConstraints,
    late: &LatePosition,
    rigids: &[(VarId, VarId)],
    disagreements: &mut Vec<ClauseDisagreement>,
) -> bool {
    let (slot, ty, class, at) = match late {
        LatePosition::CallResult {
            position,
            result,
            at,
        } => {
            let Some(result) = computed_result_type(kb, rid, st, result, *at) else {
                return false;
            };
            (
                SlotOf::Type(position),
                result,
                DisagreementClass::CallResult,
                *at,
            )
        }
        LatePosition::ResultColumn { arg, result } => {
            let Some(result) = computed_result_type(kb, rid, st, result, arg.span) else {
                return false;
            };
            (
                SlotOf::Arg(arg),
                result,
                DisagreementClass::ResultColumn,
                arg.span,
            )
        }
        LatePosition::DotResult { dot, position } => {
            let Some(ty) = dot_value_type(kb, rid, st, dot) else {
                return false;
            };
            (
                SlotOf::Type(position),
                ty,
                DisagreementClass::DotResult,
                dot.span,
            )
        }
        LatePosition::RuleGoal { .. } => unreachable!("a rule goal is read by its columns"),
    };
    let mut trial = st.trial();
    let fits = match slot {
        SlotOf::Type(position) if says_nothing_of_a_value(kb, position) => true,
        SlotOf::Type(position) => unify_types(kb, &mut trial.subst, position, &ty),
        SlotOf::Arg(arg) => constrain_occurrence_at(kb, &mut trial, arg, &ty),
    };
    if fits {
        st.commit(trial);
    } else {
        match slot {
            SlotOf::Type(position) => note_disagreement(kb, &st.subst, position, &ty),
            SlotOf::Arg(arg) => note_arg_disagreement(kb, &st.subst, st, arg, &ty),
        }
        let fixed = fits_once_parameters_vary(kb, st, rigids, |kb, varying| match slot {
            SlotOf::Type(position) => {
                let position = unrigidify_clause_types(kb, rigids, position);
                let ty = unrigidify_clause_types(kb, rigids, &ty);
                unify_types(kb, &mut varying.subst, &position, &ty)
            }
            SlotOf::Arg(arg) => {
                let ty = unrigidify_clause_types(kb, rigids, &ty);
                constrain_occurrence_at(kb, varying, arg, &ty)
            }
        });
        disagreements.push(ClauseDisagreement {
            class: if fixed {
                DisagreementClass::SortParameterFixed
            } else {
                class
            },
            span: Some(at),
        });
    }
    true
}

/// Record a goal's variable arguments when the goal reads nothing — each one's type, or the
/// variable where nothing types it: what such a variable says of a column is what the
/// relation's other clauses say.
fn note_unread_goal(kb: &KnowledgeBase, st: &mut ClauseConstraints, goal: &Rc<NodeOccurrence>) {
    let Some(Expr::Apply {
        pos_args,
        named_args,
        ..
    }) = goal.as_expr()
    else {
        return;
    };
    for arg in pos_args.iter().chain(named_args.iter().map(|(_, a)| a)) {
        let Some(d) = arg.var_key(kb) else {
            continue;
        };
        match st.var_types.get(&d) {
            Some(ty) => st.unread.push(ty.clone()),
            None => {
                st.unread_vars.insert(d);
            }
        }
    }
}

/// Whether a late position that did not fit does once the enclosing sort's parameters the
/// head's bounds name are let vary: then the body fixes the parameter, which is a class of
/// its own. On a copy.
fn fits_once_parameters_vary(
    kb: &mut KnowledgeBase,
    st: &ClauseConstraints,
    rigids: &[(VarId, VarId)],
    fits: impl FnOnce(&mut KnowledgeBase, &mut ClauseConstraints) -> bool,
) -> bool {
    if rigids.is_empty() {
        return false;
    }
    let mut varying = st.trial();
    let vars: Vec<u32> = varying.var_types.keys().copied().collect();
    for d in vars {
        let ty = walk_type_deep_value(kb, &varying.subst, &varying.var_types[&d]);
        let ty = unrigidify_clause_types(kb, rigids, &ty);
        varying.var_types.insert(d, ty);
    }
    fits(kb, &mut varying)
}

/// What a late position's type is given to: a slot's declared type, or an argument.
enum SlotOf<'a> {
    Type(&'a Value),
    Arg(&'a Rc<NodeOccurrence>),
}

/// A call's result type as the call computes it: a type constructor its signature writes
/// (`field_access`'s `FieldOf[T = R, Name = Name]`) reduced at what the clause has given its
/// operands, as an operation body reduces it at the call's return. `None` while an operand
/// is not known yet, or where the reduction refuses — the dispatch walk reports that.
fn computed_result_type(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    st: &ClauseConstraints,
    result: &CallResult,
    at: crate::span::SourceSpan,
) -> Option<Value> {
    let ctx = TypeErrorContext::Rule {
        name: kb.rule_domain(rid),
        field: RuleField::Body,
    };
    // A PROJECTION ON A PARAMETER (`s.T`) is read off the type the argument there has, as
    // the call reads it; read as a type of its own it made `head(cons(7, nil)) = ?r`'s `?r`
    // an `s.T`, and the `eq` beside it was refused.
    let mut ty = result.ty.clone();
    if value_contains_projection(kb, &ty) {
        let mut args: HashMap<Symbol, Value> = HashMap::with_capacity(result.params.len());
        for (param, arg) in &result.params {
            let ty = match arg {
                ArgType::Var(d) => match st.var_types.get(d) {
                    Some(ty) => ty.clone(),
                    None => continue,
                },
                ArgType::Of(ty) => ty.clone(),
            };
            args.insert(*param, walk_type_deep_value(kb, &st.subst, &ty));
        }
        ty = eliminate_type_projections(kb, &ty, &args, Receivers::Call, None, &ctx, None).ok()?;
        if value_contains_projection(kb, &ty) {
            return None;
        }
    }
    let mut flags = return_reducible_ctors(kb, &ty);
    if !flags.iter().any(|f| *f) {
        return Some(ty);
    }
    let mut reduced = walk_type_deep_value(kb, &st.subst, &ty);
    let site = CtorReduceSite {
        sp: at,
        span: Some(at.span),
        scope: kb.symbols.scope_id(kb.rule_domain(rid)),
    };
    for _ in 0..TYPE_CTORS.len() * 4 {
        for (cfg, wrote) in TYPE_CTORS.iter().zip(flags.iter()) {
            if *wrote {
                reduced = reduce_type_ctor(kb, &reduced, &ctx, &site, cfg).ok()?;
            }
        }
        let next = return_reducible_ctors(kb, &reduced);
        if !next.iter().any(|f| *f) {
            return Some(reduced);
        }
        if next == flags {
            return None;
        }
        flags = next;
    }
    None
}

/// The head's written bounds, each opened per collection — a variable the bound writes is
/// fresh, as a citation opens it — with the enclosing sort's parameters it names made rigid,
/// and unified with what the body says of its variable. Answers the `(rigid, parameter)`
/// pairs.
fn settle_head_bounds(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    st: &mut ClauseConstraints,
    disagreements: &mut Vec<ClauseDisagreement>,
    span: Option<crate::span::SourceSpan>,
) -> Vec<(VarId, VarId)> {
    let stored = kb.rule_type_bounds(rid).to_vec();
    if stored.is_empty() {
        return Vec::new();
    }
    let globals: Vec<VarId> = kb.rule_globals(rid).to_vec();
    let frame: Vec<VarId> = globals
        .iter()
        .rev()
        .map(|&v| {
            if kb.is_canonical_type_param_var(v) {
                v
            } else {
                kb.fresh_var(v.name())
            }
        })
        .collect();
    let mut rigidify = Substitution::new();
    let mut rigids: Vec<(VarId, VarId)> = Vec::new();
    for (d, bound) in stored {
        // A bound naming a sort the loader could not resolve is reported once and read as
        // unwritten, as an annotation is; one at a spec over its parameter is refused where
        // it is written (`check_rule_sort_uses`); one at `Term` admits every value.
        if says_nothing_of_a_value(kb, &bound)
            || type_mentions_unresolved_name(kb, &bound)
            || parameter_spec_written_as_type(kb, &bound).is_some()
        {
            continue;
        }
        let opened = crate::kb::node_occurrence::open_value_type(kb, &bound, &frame).0;
        let mut vars: Vec<VarId> = Vec::new();
        let mut seen = HashSet::new();
        crate::kb::node_occurrence::collect_value_type(kb, &opened, &mut vars, &mut seen);
        for v in vars {
            if kb.is_canonical_type_param_var(v) && !rigids.iter().any(|(_, p)| *p == v) {
                let r = kb.fresh_var(v.name());
                let rigid = kb.alloc(Term::Var(Var::Rigid(r)));
                rigidify.bind_term(kb, v, rigid);
                rigids.push((r, v));
            }
        }
        let rigid_bound = walk_type_deep_value(kb, &rigidify, &opened);
        let mut trial = st.trial();
        if constrain_var_at(kb, &mut trial, d, &rigid_bound) {
            st.commit(trial);
            continue;
        }
        // Where the bound fits once its parameters vary, it is the parameter the body fixes.
        let mut varying = st.trial();
        let class = if constrain_var_at(kb, &mut varying, d, &opened) {
            DisagreementClass::SortParameterFixed
        } else {
            DisagreementClass::HeadBound
        };
        if let Some(has) = st.var_types.get(&d).cloned() {
            note_disagreement(kb, &st.subst, &rigid_bound, &has);
        }
        disagreements.push(ClauseDisagreement { class, span });
    }
    rigids
}

/// Every rigid of `rigids` in `ty` read as the parameter it stands for again
/// ([`settle_late_positions`]).
pub(super) fn unrigidify_clause_types(
    kb: &mut KnowledgeBase,
    rigids: &[(VarId, VarId)],
    ty: &Value,
) -> Value {
    if rigids.is_empty() {
        return ty.clone();
    }
    let leaf = |kb: &mut KnowledgeBase, v: &Value| -> Option<Value> {
        let r = match v {
            Value::Term { id, .. } => match kb.get_term(*id) {
                Term::Var(Var::Rigid(r)) => *r,
                _ => return None,
            },
            Value::Var(Var::Rigid(r)) => *r,
            _ => return None,
        };
        let (_, param) = rigids.iter().find(|(rigid, _)| *rigid == r)?;
        Some(Value::term(kb.alloc(Term::Var(Var::Global(*param)))))
    };
    rewrite_type_leaves(kb, ty, &leaf).unwrap_or_else(|| ty.clone())
}

/// Type variable `d` at `ty`, as a declared position does ([`constrain_vid`]): recorded where
/// nothing was, unified where something was, and taking over from a call's placeholder.
///
/// A PLACEHOLDER THE TYPE CONFORMS TO is taken over where the two do not unify: `?l: List[T =
/// Int64]` passed to `head(s: Self)` of `Stream` is a `List`, though the placeholder `Stream[T
/// = t, E = e]` does not unify with it. Any other is what the clause says the variable is, and
/// the type does not fit: `?x <=> b3(v: 5)` makes the `T` of `<=>` a `Box3[T = Int64]`, which a
/// bound `Box3[T = T]` is not, and `gt(?x, 1)` pins `?x` at the literal's `Int64`, which a goal
/// on `fact tag("a")` is not.
fn constrain_var_at(
    kb: &mut KnowledgeBase,
    st: &mut ClauseConstraints,
    d: u32,
    ty: &Value,
) -> bool {
    let Some(existing) = st.var_types.get(&d).cloned() else {
        st.var_types.insert(d, ty.clone());
        return true;
    };
    let mut trial = st.subst.clone();
    if unify_types(kb, &mut trial, &existing, ty) {
        st.subst = trial;
        st.demand_only.remove(&d);
        if st.param_backed.remove(&d) {
            st.var_types.insert(d, ty.clone());
        }
        return true;
    }
    if !st.param_backed.contains(&d) {
        return false;
    }
    let placeholder = walk_type_deep_value(kb, &st.subst, &existing);
    // The question an operation body's argument is asked of its parameter, which admits a
    // carrier that provides the spec a parameter is written at.
    let context = TypeErrorContext::Rule {
        name: kb.intern("clause"),
        field: RuleField::Body,
    };
    let conforms = matches!(
        validate_arg_against_param(
            kb,
            &mut st.subst.clone(),
            ty,
            &placeholder,
            None,
            context,
            None,
        ),
        ArgValidation::Ok | ArgValidation::WrapSome { .. }
    );
    if conforms {
        // A bare value meets an `Option[X]` placeholder as its element (the some-coercion), so
        // `X` is the value's type — a parameter of the callee's own type the call's other
        // arguments read.
        if is_option_type(kb, &placeholder) && !is_option_type(kb, ty) {
            if let Some(element) = extract_type_param(kb, &placeholder, "T") {
                let mut trial = st.subst.clone();
                if unify_types(kb, &mut trial, &element, ty) {
                    st.subst = trial;
                }
            }
        }
        st.param_backed.remove(&d);
        st.var_types.insert(d, ty.clone());
    }
    conforms
}

/// Type the argument `arg` at `ty`: a variable as a declared position, a literal at its own
/// sort, anything else walked as a term that fills a slot of that type.
fn constrain_occurrence_at(
    kb: &mut KnowledgeBase,
    st: &mut ClauseConstraints,
    arg: &Rc<NodeOccurrence>,
    ty: &Value,
) -> bool {
    if says_nothing_of_a_value(kb, ty) {
        return true;
    }
    if let Some(lit) = arg.literal(kb) {
        let lit_type = literal_sort(kb, &lit);
        return unify_types(kb, &mut st.subst, ty, &lit_type);
    }
    if let Some(d) = arg.var_key(kb) {
        return constrain_var_at(kb, st, d, ty);
    }
    collect_occurrence_type_constraints(kb, arg, Some(ty), BodyPos::Value, true, st);
    !st.subst.contradiction
}

/// Each argument of the rule goal `goal` at the column of its slot.
fn constrain_goal_at_columns(
    kb: &mut KnowledgeBase,
    st: &mut ClauseConstraints,
    goal: &Rc<NodeOccurrence>,
    columns: &[(SlotKey, ColumnType)],
) -> bool {
    let Some(Expr::Apply {
        pos_args,
        named_args,
        ..
    }) = goal.as_expr()
    else {
        return true;
    };
    let slots = pos_args
        .iter()
        .enumerate()
        .map(|(i, a)| (SlotKey::Pos(i), a))
        .chain(named_args.iter().map(|(k, a)| (SlotKey::Named(*k), a)));
    for (slot, arg) in slots {
        let Some((_, column)) = columns.iter().find(|(s, _)| *s == slot) else {
            continue;
        };
        let ty = match column {
            ColumnType::Of(ty) => ty,
            ColumnType::Some => {
                meet_some_type(st, arg);
                continue;
            }
        };
        // A column of occurrences quotes the argument written there, as a `Term` position
        // does: `synth_int(42, ?n)` over `synth_int(?e, 1) :- occurrence_term(?e, …)` reads
        // `42`'s occurrence.
        if is_occurrence_type(kb, ty) {
            continue;
        }
        let before = disagreements_printed().then(|| st.subst.clone());
        if !constrain_occurrence_at(kb, st, arg, ty) {
            if let Some(before) = before {
                note_arg_disagreement(kb, &before, st, arg, ty);
            }
            return false;
        }
    }
    true
}

/// An argument at a column of some type ([`ColumnType::Some`]): a filter, which types nothing,
/// read once every other position of the clause is ([`demands_on_some_type`]).
fn meet_some_type(st: &mut ClauseConstraints, arg: &Rc<NodeOccurrence>) {
    st.some_args.push(Rc::clone(arg));
}

/// The demands on a value a column of some type gives: a variable there that only a demand
/// types is recorded ([`DisagreementClass::SomeTypeDemand`]), and one nothing types is the
/// column's — a dot on it is recorded too. A variable a test or any other position types is
/// read at that type.
fn demands_on_some_type(kb: &KnowledgeBase, rid: RuleId, st: &mut ClauseConstraints) {
    for arg in std::mem::take(&mut st.some_args) {
        let Some(d) = arg.var_key(kb) else { continue };
        if st.demand_only.contains(&d) {
            st.found.push(ClauseDisagreement {
                class: DisagreementClass::SomeTypeDemand,
                span: Some(arg.span),
            });
        } else if !st.var_types.contains_key(&d) {
            st.some_typed.insert(d);
        }
    }
    if st.some_typed.is_empty() {
        return;
    }
    fn walk(kb: &KnowledgeBase, occ: &Rc<NodeOccurrence>, st: &mut ClauseConstraints) {
        let Some(expr) = occ.as_expr() else { return };
        if let Expr::DotApply { receiver, .. } = expr {
            if let Some(d) = receiver.var_key(kb) {
                if st.some_typed.contains(&d) && !st.var_types.contains_key(&d) {
                    st.found.push(ClauseDisagreement {
                        class: DisagreementClass::SomeTypeDemand,
                        span: Some(occ.span),
                    });
                }
            }
        }
        for_each_child(expr, |c| walk(kb, c, st));
    }
    for node in kb.rule_body_nodes(rid).to_vec() {
        walk(kb, &node, st);
    }
}

/// [`note_disagreement`] for an argument: the slot's type against what the clause says of
/// the argument — a variable's type, a literal's sort.
fn note_arg_disagreement(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    st: &ClauseConstraints,
    arg: &Rc<NodeOccurrence>,
    ty: &Value,
) {
    if !disagreements_printed() {
        return;
    }
    let has = if let Some(lit) = arg.literal(kb) {
        Some(literal_sort(kb, &lit))
    } else {
        arg.var_key(kb).and_then(|d| st.var_types.get(&d).cloned())
    };
    match has {
        Some(has) => note_disagreement(kb, subst, ty, &has),
        None => eprintln!("  {} against a construction", type_display_name_value(kb, ty)),
    }
}

/// The columns a goal on `functor` reads from a clause of `own`: nothing for a goal on another
/// relation of its cycle, and the callee's, opened fresh, for any other
/// ([`rule_goal_columns`]). A goal on its own relation reads its columns as one type: while
/// they are being read the goal reads nothing, and each clause's column is the relation's.
fn rule_goal_columns_at(
    kb: &mut KnowledgeBase,
    own: Option<Symbol>,
    functor: Symbol,
) -> Option<Vec<(SlotKey, ColumnType)>> {
    if own.is_some_and(|f| same_rule_goal_cycle(kb, f, functor)) {
        return None;
    }
    rule_goal_columns(kb, functor)
}

/// The type of the dot `dot`, typed as the dispatch walk types it, at the types the clause
/// has given its variables so far; `None` where it does not type — its receiver is one the
/// clause has not typed yet, or the dot is refused, which the dispatch walk reports.
fn dot_value_type(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    st: &ClauseConstraints,
    dot: &Rc<NodeOccurrence>,
) -> Option<Value> {
    let mut types: HashMap<u32, Value> = HashMap::with_capacity(st.var_types.len());
    for (d, ty) in &st.var_types {
        types.insert(*d, walk_type_deep_value(kb, &st.subst, ty));
    }
    let mut env = TypingEnv::empty();
    env.set_debruijn_types(Rc::new(types));
    env.set_rule_scope(kb.rule_domain(rid));
    env.mark_rule_body_dispatch();
    type_check_node_at(kb, &env, dot, None, NodePos::Value)
        .ok()
        .map(|r| r.ty)
}

thread_local! {
    /// The late positions that did not fit, by class, over every clause this thread typed
    /// ([`clause_disagreements_by_this_thread`]).
    static CLAUSE_DISAGREEMENTS: std::cell::RefCell<HashMap<&'static str, usize>> =
        std::cell::RefCell::new(HashMap::new());
}

/// Whether `ANTHILL_CLAUSE_DISAGREEMENTS` is set: each disagreement is then printed.
fn disagreements_printed() -> bool {
    std::env::var_os("ANTHILL_CLAUSE_DISAGREEMENTS").is_some()
}

/// With `ANTHILL_CLAUSE_DISAGREEMENTS=1`, print the two types a late position failed on.
fn note_disagreement(kb: &mut KnowledgeBase, subst: &Substitution, a: &Value, b: &Value) {
    if !disagreements_printed() {
        return;
    }
    let a = walk_type_deep_value(kb, subst, a);
    let b = walk_type_deep_value(kb, subst, b);
    eprintln!(
        "  {} against {}",
        type_display_name_value(kb, &a),
        type_display_name_value(kb, &b)
    );
}

/// Tally `found` ([`clause_disagreements_by_this_thread`]); with
/// `ANTHILL_CLAUSE_DISAGREEMENTS=1`, also print each with where it was written; with
/// `ANTHILL_CLAUSE_DISAGREEMENTS_TO=<file>`, also append each to the file as a line of
/// class, test (the thread's name), place and the source from there — what the count of a
/// whole suite run is taken from, since a passing test's printing is not shown.
pub(super) fn count_clause_disagreements(kb: &KnowledgeBase, found: &[ClauseDisagreement]) {
    if found.is_empty() {
        return;
    }
    let print = disagreements_printed();
    let record = std::env::var_os("ANTHILL_CLAUSE_DISAGREEMENTS_TO");
    let mut lines = String::new();
    CLAUSE_DISAGREEMENTS.with(|tally| {
        let mut tally = tally.borrow_mut();
        for d in found {
            *tally.entry(d.class.name()).or_default() += 1;
            if !print && record.is_none() {
                continue;
            }
            let (at, from) = disagreement_place(kb, d);
            if print {
                eprintln!("clause disagreement {}: {at}", d.class.name());
            }
            if record.is_some() {
                let test = std::thread::current().name().unwrap_or("").to_owned();
                lines.push_str(&format!("{}\t{test}\t{at}\t{from}\n", d.class.name()));
            }
        }
    });
    if let Some(file) = record {
        use std::io::Write;
        let appended = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&file)
            .and_then(|mut f| f.write_all(lines.as_bytes()));
        if let Err(e) = appended {
            panic!("ANTHILL_CLAUSE_DISAGREEMENTS_TO={}: {e}", file.to_string_lossy());
        }
    }
}

/// Where a disagreement was written, as `path:line:column`, and the first sixty characters of
/// the source from there on one line.
fn disagreement_place(kb: &KnowledgeBase, d: &ClauseDisagreement) -> (String, String) {
    d.span
        .and_then(|sp| {
            let (path, text) = kb.sources.provenance(sp.source)?;
            let start = (sp.span.start as usize).min(text.len());
            let line = text[..start].matches('\n').count() + 1;
            let col = start - text[..start].rfind('\n').map_or(0, |i| i + 1) + 1;
            let path = path.map(|p| p.display().to_string()).unwrap_or_default();
            let from: String = text[start..].chars().take(60).collect();
            Some((format!("{path}:{line}:{col}"), from.replace('\n', " ")))
        })
        .unwrap_or_else(|| (format!("{:?}", d.span), String::new()))
}

/// The late positions of a clause that did not fit, by class, over every clause this thread
/// has typed since it started.
pub fn clause_disagreements_by_this_thread() -> Vec<(&'static str, usize)> {
    CLAUSE_DISAGREEMENTS.with(|tally| {
        let mut out: Vec<(&'static str, usize)> =
            tally.borrow().iter().map(|(k, v)| (*k, *v)).collect();
        out.sort();
        out
    })
}

impl DisagreementClass {
    fn name(self) -> &'static str {
        match self {
            DisagreementClass::ConstructionField => "construction field",
            DisagreementClass::SomeTypeDemand => "some type demand",
            DisagreementClass::HeadBound => "head bound",
            DisagreementClass::SortParameterFixed => "sort parameter fixed",
            DisagreementClass::CallResult => "call result",
            DisagreementClass::ResultColumn => "result column",
            DisagreementClass::RuleGoal => "rule goal",
            DisagreementClass::DotResult => "dot result",
        }
    }
}

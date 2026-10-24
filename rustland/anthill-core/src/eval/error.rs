use crate::span::SourceSpan;

use super::Value;

#[derive(Debug)]
pub enum EvalError {
    UnboundVar {
        name: String,
        span: Option<SourceSpan>,
    },
    UnknownOperation {
        name: String,
    },
    /// An operation was invoked that has neither a body nor a registered
    /// builtin. The typer is supposed to guarantee this never happens, so
    /// hitting it is an invariant violation (a typer/loader bug) — NOT a
    /// recoverable domain error, and it does not ride the `Error` effect
    /// channel. Carries a captured backtrace to locate the bad dispatch.
    OperationBodyMissing {
        name: String,
        /// Clauses are indexed under the operation. They are its definition and they
        /// answer a goal; a call runs a body, a host function or a builtin, so the
        /// operation is defined and still has nothing for this call to enter. Carried
        /// because the two messages differ: one names a definition that is missing, the
        /// other a definition a call cannot run.
        defined_by_clauses: bool,
        backtrace: std::backtrace::Backtrace,
    },
    TypeMismatch {
        expected: &'static str,
        got: String,
    },
    ArityMismatch {
        op: &'static str,
        expected: usize,
        got: usize,
    },
    Overflow {
        op: &'static str,
    },
    /// WI-20261017-JRHZ0 — `anthill.prelude.todo()` was reached: the body of an
    /// operation not written yet. A HOLE, not a domain failure, so it rides no `Error`
    /// row and nothing catches it — as `Overflow` is reached from a pure `Int64.add`.
    /// `running` is the operation whose body called it (a builtin enters no frame, so the
    /// top frame is the caller's); `None` when no frame was running — a rule-body goal
    /// the bridge reduced directly.
    NotImplemented {
        running: Option<String>,
    },
    /// WI-20260827-T2470 — a constructor APPLICATION in an evaluated body gives more
    /// positional arguments than the entity has unfilled fields. The eval twin of
    /// [`crate::kb::execute::LowerError::OverArityConstructor`], raised from
    /// `finish_constructor`'s positional→named desugar for the same reason that one
    /// exists: leaving the surplus in `pos` would build an entity that silently never
    /// matches the canonical named form anywhere (the loud-error principle). Its own
    /// variant rather than [`EvalError::ArityMismatch`], whose `op` is a `&'static str`
    /// and so cannot name the offending constructor.
    ///
    /// Unreached by any test, and by any source program: the loader refuses the same
    /// shape at load time, so this is the broken-invariant backstop its two siblings
    /// are. See the raise site for the measurement.
    OverArityConstructor {
        functor: String,
        given: usize,
        unfilled: usize,
        declared: String,
    },
    DepthExceeded {
        cap: usize,
    },
    /// The `step_cap` work budget was exhausted: a non-terminating computation
    /// (a tail loop, OR a dispatch/deliver value-cascade — both now iterate on
    /// the heap trampoline and tick one step per iteration), or a real
    /// computation that genuinely needs a higher cap. `chain` is the
    /// recent-dispatch ring (most recent last); since a loop repeats its
    /// operations, it names the offending sources so they can be located
    /// quickly. Empty when no `step_cap` was set (the ring is only maintained
    /// when a cap could fire).
    StepsExhausted {
        cap: u64,
        chain: Vec<String>,
    },
    /// An effect operation was dispatched with NO HANDLER registered for its effect
    /// sort — or over a KB that does not declare the effect, where none can be. NOT an
    /// evaluator-invariant bug: the SLD→eval bridge's scratch interpreter has an EMPTY
    /// effect registry BY CONSTRUCTION (resolution must not perform effects), and so has
    /// the one a load runs a `const_map` value source on. The bridge declines the goal and
    /// reports the effect (`BridgeDisposition::Fault`); the load refuses the const, naming
    /// it (`ConstUnavailableWhy::HostPerformsEffect`).
    ///
    /// WI-20260911-0V0F7 GAVE IT ITS PRODUCER. `invoke_effect_handler` raised
    /// `Internal("no handler registered for effect …")` instead, and `bridge_op_to_eval`
    /// `debug_assert`s on `Internal`, so a program that merely instantiated a parametric
    /// effect row with a real effect — the case `docs/kernel-language.md` admits into the
    /// `Bool` relational view because the bridge declines it — ABORTED a debug build.
    UnhandledEffect {
        /// The effect sort's qualified name, captured at the raise site: `Display` has no
        /// `KnowledgeBase`, the name IS the diagnostic, and over a KB that does not declare
        /// the effect there is no symbol to carry.
        name: String,
    },
    /// An anthill-level `Error` effect was raised (proposal 027 §Error).
    /// Produced at the effect-dispatch site from a handler's
    /// `HandlerAction::Throw(payload)`. The payload is an ordinary opaque
    /// `Value` — error-ness lives in *this variant* (the channel), not in
    /// the value itself. A raise travels to the innermost `Error.reify` boundary
    /// whose pattern admits `raised_type`, and aborts evaluation if none does.
    ///
    /// A host function raises through `Interpreter::raise_error`, which takes the type
    /// from the requirement channel its operation was handed.
    Raised {
        payload: Value,
        /// The type the raise carries (proposal 071 §1.3), which a boundary asks its
        /// pattern about.
        raised_type: RaisedType,
    },
    /// A handler returned a continuation-manipulating action (`Fail`,
    /// `Choice`, or `Suspend`) that the runtime cannot yet honor — those
    /// need the Branch / suspend-resume substrate (WI-075). Hitting one is
    /// a runtime-internal not-yet-implemented state, so it carries the
    /// dispatch context (effect sort + operation) and a captured backtrace
    /// to locate the offending call site.
    UnsupportedHandlerAction {
        action: &'static str,
        effect: String,
        op: String,
        /// Action-specific explanation — for `Fail`, the reason carried by
        /// the action (the "why" of the branch abort). `None` for actions
        /// that carry no reason payload.
        detail: Option<String>,
        backtrace: std::backtrace::Backtrace,
    },
    /// Proposal 039 / WI-084: a `const`'s value was demanded while it is already
    /// being forced — a dependency cycle (`const A = B + 1; const B = A + 1`).
    /// The value cache's forcing sentinel detects this dynamically; `name` is the
    /// const whose forcing re-entered.
    ConstCycle {
        name: String,
    },
    /// Proposal 039 / WI-084: a host-supplied (bodyless) `const`'s value was
    /// demanded but no reflect builtin is registered to produce it. The const
    /// type-checks (its declared type is known) — only the runtime VALUE is
    /// unavailable in this build (the spec-only-vs-codegen axis).
    ConstValueUnavailable {
        name: String,
    },
    /// WI-625 gap 1 (SLD→eval bridge): a semantic comparison inside a bridged
    /// op-body evaluation reached a genuinely UNDECIDED point — a truncated
    /// sub-proof, or an eq-overriding carrier buried under non-overriding
    /// structure (`some({1,2})` vs `some({2,1})`) where the structural verdict
    /// would be membership-wrong. This is a resolver-bridge CONTROL SIGNAL, not
    /// a domain error: it is produced ONLY when `EvalConfig::bridge_mode` is set
    /// (the interpreter was lent to the resolver, which CAN residualize), and it
    /// unwinds via the ordinary `?` propagation — the evaluator is thereby
    /// "interruptible" with no bespoke control flow — up to the resolver's
    /// `bridge_op_to_eval`, which turns it into a delay (the resolver's own
    /// SUSPEND). Distinct from the WI-075 effect-handler `Suspend` action
    /// (`UnsupportedHandlerAction`). Top-level eval never sets `bridge_mode`, so
    /// it never produces this and its structural fallback is unchanged.
    ///
    /// WI-628 — `truncated` distinguishes WHY the comparison could not decide, so
    /// the resolver can propagate genuine incompleteness: `true` when the suspend
    /// carries a depth-TRUNCATED sub-search (a nested carrier-`eq` whose closed
    /// sub-proof hit `sem_eq_sub_depth`), `false` for an ordinary flounder (an
    /// unbound operand / a buried override / an unresolvable dictionary). Without
    /// this bit a nested truncation would reach `bridge_eq_op_to_eval` as an
    /// indistinguishable flounder and the outer stream's `truncated` flag would
    /// stay clear — the exact WI-628 hole, one bridge level up.
    Suspended {
        detail: String,
        truncated: bool,
    },
    /// WI-855: value-directed dispatch reached an impl whose own `requires` slot is
    /// covered by TWO OR MORE providers at these argument types, with no rule to
    /// pick between them ([`crate::kb::typing::BridgeRequirements::Ambiguous`]).
    ///
    /// A PROGRAM error, not an evaluator-invariant one — hence its own variant
    /// rather than [`Self::Internal`], whose `debug_assert` in the resolver bridge
    /// would (correctly) fire on an evaluator bug and must not fire on incoherent
    /// user instances. Why a tie raises here while every other unresolvable cause
    /// enters the frame unsupplied is argued once, where the choice is made:
    /// `Interpreter::requirements_for_value_directed_impl`.
    AmbiguousRequirement {
        op: String,
        requirement: String,
        candidates: Vec<String>,
    },
    /// WI-857: a dictionary slot that pins NO provider was used — dispatched
    /// through, projected into, or enumerated. The slot carries an empty bundle over
    /// the `NoProvider` marker because its goal did not resolve when the dictionary
    /// was built, because the strictness rule declined to search it, or because it is
    /// a host-entry stand-in that supplied no dictionary at all.
    ///
    /// The THIRD member of the family above, and a variant for the same reason: this
    /// is a PROGRAM (or host-entry) error, not an evaluator-invariant one, so the
    /// resolver bridge's `debug_assert` on [`Self::Internal`] must not fire on it —
    /// a bridged rule DELAYS instead. It was `Internal` when first written, which
    /// would have aborted any test whose rule body dispatched through such a slot.
    ///
    /// `detail` is pre-rendered by `kb::typing::marker_refusal`, the one owner of the
    /// sentence. WI-865 stopped it hedging: the marker now names the
    /// `kb::typing::AbsenceRecord` its mint filed, so each cause above gets its own
    /// wording — a two-provider TIE names the providers that tied instead of reading
    /// as "no provider".
    UnpinnedRequirement {
        detail: String,
        /// The marker the read met — the functor of the dictionary that pins no provider —
        /// whose filed record says why ([`crate::kb::typing::absence_is_unprovided`]).
        marker: crate::intern::Symbol,
    },
    /// WI-842 (proposal 058 §4.9): value-directed dispatch found TWO OR MORE
    /// suppliers of one spec op for the runtime receiver's carrier — the carrier's
    /// own member, an instance fact's binding, a witness sort's member — and this
    /// call site names none of them.
    ///
    /// The SIBLING of [`Self::AmbiguousRequirement`], one selection step earlier:
    /// that one is a tie over the providers of an impl's `requires` slot, this one a
    /// tie over the providers of the OP being dispatched. Both are PROGRAM errors
    /// (incoherent instances), not evaluator-invariant ones, hence variants of their
    /// own rather than [`Self::Internal`].
    ///
    /// Each candidate is rendered by its SUPPLY ROUTE
    /// ([`crate::kb::typing::render_suppliers`]) because the three are written
    /// in three syntaxes and the author must know which text to delete.
    ///
    /// WI-1012 gave this refusal a LOAD face
    /// ([`crate::kb::typing::TypeError::AmbiguousSpecOpDispatch`]) for a statically
    /// concrete carrier; this one keeps the carriers the typer cannot pin, and the two
    /// share one message body. `repair` is what that sharing made explicit: whether a
    /// rival can be NAMED differs between the two value-directed readers below, so it
    /// is a typed field rather than a sentence each site assumes.
    AmbiguousSpecOpDispatch {
        op: String,
        carrier: String,
        candidates: Vec<String>,
        repair: crate::kb::typing::SupplierTieRepair,
    },
    /// WI-757 — the WI-722 macro contract's DIAGNOSTIC channel for a HOST macro:
    /// it read its argument occurrences, found them definitively untranslatable,
    /// and says why. An anthill-written macro reaches the same channel by
    /// RAISING (proposal 043.1 §3.6) — `Raised`'s payload renders through
    /// [`render_raised_payload`] into the same `detail`.
    ///
    /// The distinction this variant exists to draw: every OTHER failure of a
    /// macro is a DECLINE — the macro is merely not applicable (or not ready
    /// yet), so the `@[simp]` template call is kept and whatever downstream check
    /// the residual fails is the diagnostic. A rejection is the opposite: the
    /// macro IS the right one, the input is the user's, and the reason is known
    /// HERE and nowhere downstream. Before this channel existed, `where(λ c ->
    /// ite(…))` reported `guarded_of.r (op-arg): expected NodeOccurrence, got
    /// Relation[…]` — the residual template's type error, naming neither the
    /// offending condition nor the reason, while the macro's own "cannot
    /// translate" text was discarded.
    ///
    /// `span` is the OFFENDING SUB-EXPRESSION's, not the macro call's: the macro
    /// holds the argument occurrences, so it can point at the one condition atom
    /// that does not translate. `None` leaves the redex span to the reporter —
    /// which is what a RAISED rejection gets, since `raise` carries a payload and
    /// no occurrence. `simp_rewrite::try_expand_macro` carries this out as a
    /// [`crate::kb::simp_rewrite::MacroRejection`] and the typer reports it as a
    /// load error; at a RUNTIME call of the same op it renders like any other
    /// eval error.
    MacroRejected {
        detail: String,
        span: Option<SourceSpan>,
    },
    /// WI-20260918-R541X (D) — a body read of a TYPE PARAMETER (an operation's `[P]`
    /// or a sort's `sort T = ?`) found no binding on the running frame's type-argument
    /// channel. A parameter with no binding is not a type: delivering `Ref(T)` — what
    /// the bare-head arms did before — answered a type the program never asked for,
    /// silently. The typer writes every binding it can prove onto the call site
    /// (WI-272's type-arg stamp, since removed), so reaching here is a channel that route does not fill
    /// yet, and the author is told which parameter and which frame.
    UnboundTypeParam {
        param: String,
        running: String,
    },
    /// WI-20260923-9R5HN — a reflect KB reader (`KB.sorts`, `KB.descriptions`,
    /// `KB.stored_facts_of`, …) asked the extent seam for a relation's FACTS and the seam
    /// refused — the program asserts a BODIED rule under that functor (`rule
    /// DescriptionInfo(…) :- …`) — or a mounted source failed. The program's data or its
    /// backend, not an evaluator invariant, so not [`Self::Internal`], which the SLD
    /// bridge asserts against. MEASURED before it existed: the refusal was a PANIC in the
    /// reader, and `stored_facts_of`'s was `Internal`, each reachable from inside
    /// resolution once the readers became reducible at a rule-body operand.
    KbReadFailed(crate::kb::reflect_reader::ReflectReadError),
    /// A call evaluated against a KB its caller lent it — a rule body's, through the
    /// SLD→eval bridge — answered a value, or raised a payload, still holding a scoped KB
    /// (`KB.loaded`). The layer is applied to the caller's own KB, so it cannot stay
    /// applied past the call, and a handle to a discarded layer refers to nothing: the call
    /// has no value (`Interpreter::release_layers_for_handback`). `raised` is the payload's
    /// text when the call raised. A PROGRAM limit, not an evaluator invariant, so not
    /// [`Self::Internal`].
    ScopedKbOutlivesCall {
        raised: Option<String>,
    },
    /// Proposal 027.4 — `Error.reify` was entered without the pattern it catches by: no
    /// `TypePattern` slot in the call's requirement channel (proposal 071 §1.4) — a host
    /// entry that hands none, or a call entered from argument values that do not pin the
    /// payload — or a dictionary there that is no `TypePattern` instance, such as the
    /// stand-in a host entry seeds for a sort-level `requires`. Read as "cannot narrow", it
    /// would catch every payload, including a label the thunk's row leaves to the caller.
    /// `detail` is pre-rendered at the boundary. A PROGRAM limit, not an evaluator
    /// invariant, so not [`Self::Internal`].
    ReifyPayloadUnread {
        detail: String,
    },
    /// Proposal 071 §1.3 — a raise whose type is not in hand: `Error.raise`, or a host
    /// operation that raises, entered with no `TypeValue` evidence in its requirement channel
    /// (a call entered from argument values that do not pin the payload), or a host raise
    /// outside any host operation. Caught by a boundary that reads the payload's sort
    /// alone, it would land inside a `Result` typed at other arguments (WI-20260911-3MV2C).
    /// `detail` is pre-rendered where the type was asked for. A PROGRAM limit, not an
    /// evaluator invariant, so not [`Self::Internal`].
    RaiseTypeUnread {
        detail: String,
    },
    /// Proposal 071 — `anthill.reflect.type_admits` (the test `TypePattern.admits` runs) was
    /// asked about a pair its predicate does not judge (`kb::typing::type_pattern_admits`,
    /// whose `form` lists what it does not). An answer there would be a guess. `detail` is
    /// the predicate's. A PROGRAM limit, not an evaluator invariant, so not
    /// [`Self::Internal`].
    TypePatternUnjudged {
        detail: String,
    },
    Internal(String),
}

/// The type a raise carries (proposal 071 §1.3): what a boundary asks its pattern's `admits`
/// about (`Interpreter::recover_at_reify_boundary`). Built into a `Type` at the first
/// boundary that asks, not at the raise (071 open question 4, user 2026-10-24): a raise no
/// boundary sees builds nothing. Never read off the payload: a value records the sort its
/// constructor belongs to and none of the type arguments it was built at.
#[derive(Clone, Debug)]
pub enum RaisedType {
    /// The `TypeValue` evidence of the payload's type, threaded to the raise as every
    /// requirement is: the dictionary `Error.raise`'s `requires TypeValue[T = T]` was handed,
    /// the one a raising host operation's `requires TypeValue[T = X]` was handed, or the
    /// constant of a payload the runtime raises with no operation behind it (`ErrorLayer`).
    /// Its type is the whole type, arguments and all, so a boundary at `Box[V = Int64]`
    /// declines a raised `Box[V = String]`.
    Evidence(crate::eval::value::Dictionary),
    /// The payload's type is not known: the raise of an operation whose row says `Error`,
    /// which is `Error[T = ?]`, or a host effect handler's throw. No pattern but one at `?`
    /// admits it — the unknown type of WI-20260910-6ARRN — and no boundary has such a pattern
    /// yet, as no row discharges a bare `Error` label.
    Unknown,
}

/// WI-20260911-0V0F7 — which of three things an [`EvalError`] escaping the SLD→eval
/// bridge ([`crate::kb::KnowledgeBase::bridge_op_to_eval`]) IS.
///
/// THE BRIDGE USED TO ANSWER ONE THING FOR ALL OF THEM: `None`, i.e. residualize and
/// say nothing. That is right for exactly one of the three — and for the other two it
/// reports a goal whose callee RAN AND RAISED as a relation with nothing in it, which
/// is a definite claim the resolver has no grounds for. MEASURED on an operation whose
/// effect row is EMPTY so nothing else warns: `rule answer(?r) :- guardExhaustible(0,
/// ?r)` over `operation guardExhaustible(n: Int64) -> Int64 = match n case k | k > 0 ->
/// k` answered `no solutions` with `stats.errors` empty, beside `guardExhaustible(5,
/// ?r)` answering `?r = 5`.
///
/// AN EXHAUSTIVE MATCH IS THE POINT, not a convenience. A new [`EvalError`] variant
/// must PICK A SIDE here or the crate does not compile — where the `Err(e) => None`
/// it replaces absorbed every future variant into silence by default.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BridgeDisposition {
    /// The answer is not available YET, and the search that asked is COMPLETE without
    /// it: delay the goal and claim nothing.
    ///
    /// The bridge's pre-existing reading, kept for the population it was written for —
    /// a bridge-mode suspend (an undecided semantic compare), an UNREDUCED call (a spec
    /// operation at a carrier no provider supplies, `OperationBodyMissing` — an operation
    /// that nothing could EVER run is refused at load since WI-20260909-M8QWJ), a const
    /// value this build does not carry, and the two RAISES that are not domain errors at
    /// all (see [`Self::Fault`]).
    Schedule,
    /// A search BELOW was cut short, so this answer set is INCOMPLETE — but nothing
    /// here has a sentence worth printing.
    ///
    /// One producer: `EvalError::Suspended { truncated: true }`, a nested carrier-`eq`
    /// whose closed sub-proof hit its depth cap. THE BRIDGE DROPPED THAT BIT — it
    /// matched `Suspended { .. }` and returned `None`, so a truncation that
    /// [`crate::kb::KnowledgeBase::bridge_eq_op_to_eval`] reads through (WI-628) died
    /// at this bridge instead. An eager NAF/guard consumer then read the short result
    /// as a refutation, which is the WI-628 hole one bridge over.
    Truncation,
    /// The callee could not be RUN TO AN ANSWER: it raised, overflowed, exhausted its
    /// budget, or found its dispatch incoherent. The answer set is INCOMPLETE **and**
    /// there is a sentence the author needs.
    ///
    /// THE PARTITION OF `Raised` IS BY CAUSE, NOT BY CHANNEL, and a first attempt at
    /// this got it wrong by testing the variant. `raise_relation_floundered` (WI-737 —
    /// an eval-side relation drain whose sub-search stayed undischarged) and
    /// `raise_load_failed` (WI-SPGBP — `KB.loaded` reporting that its sources do not
    /// load) ride `Raised` and are not domain failures of the callee; they answer
    /// [`Self::Schedule`]. The payload's constructor is the cause: both are runtime
    /// accounts no program constructs ([`crate::kb::RuntimeAccount`]), so the same value
    /// raised again by the program that caught it is still that account. Every other
    /// payload — a user `Error.raise`, the host raises `match_failed` / `division_by_zero`
    /// that ride a row they never appear in, and the runtime's `evaluation_failure` — is a
    /// fault.
    Fault,
    /// The callee's body read a requirement slot whose goal the arguments pinned and no
    /// provider answers: the requirement is known not to be available, so the call has no
    /// value at these arguments, as `div(1, 0)` has none, and whatever reads it fails. No
    /// fault: nothing ran short and nothing raised.
    NoProvider,
}

impl EvalError {
    /// WI-20260911-0V0F7 — which [`BridgeDisposition`] this error has when it escapes
    /// the SLD→eval bridge. See that enum for why each side exists.
    ///
    /// BESIDE `Display` AND NOT INSIDE THE BRIDGE, so the list that must be revisited
    /// when a variant is added sits with the variants. `kb` partitions [`Self::Raised`] by
    /// its payload's constructor and reads an absence's marker.
    pub fn bridge_disposition(&self, kb: &crate::kb::KnowledgeBase) -> BridgeDisposition {
        match self {
            // ── Schedule: nothing is wrong, the answer is merely not here ──
            //
            // The bridge-mode control signal, whose own doc says this: "produced ONLY
            // when `EvalConfig::bridge_mode` is set … turned into a delay (the
            // resolver's own SUSPEND)". Its `truncated` bit is the one thing that must
            // still cross (WI-628).
            EvalError::Suspended { truncated: false, .. } => BridgeDisposition::Schedule,
            EvalError::Suspended { truncated: true, .. } => BridgeDisposition::Truncation,
            // AN OPERATION NOTHING RAN, reached at run time: the UNREDUCED population
            // (kernel-language.md §8.3) — a body-less spec operation at a carrier no
            // provider supplies, which the resolver PARKS as undecided so that a failing
            // sibling still refutes the clause.
            //
            // IT WAS READ AS A CAPABILITY GAP IN THE SCRATCH INTERPRETER while anthill-stl's
            // reflect builtins were registered only by the CLI's runtime; WI-20260923-9R5HN
            // made them `HOST_FNS` rows every bridge interpreter registers. What then still
            // landed here beside the UNREDUCED rows was a DEFECT delayed in silence — an
            // operation declared and defined nowhere (`operation undef(n: Int64) -> Int64`,
            // `wrap(n) = undef(n)`, `wrap(1) = 1` suspended with no warning; MEASURED
            // 2026-09-24). WI-20260909-M8QWJ refuses what of that population a load can
            // decide — at the declaration, the provision or the call — and what still arrives
            // is a dispatch only the run decides (a carrier reached by value, a dictionary a
            // caller built), plus whatever those three checks do not yet see.
            //
            // AND IT STAYS `Schedule`, MEASURED under the same ticket: as a `Fault` the
            // answer set is marked incomplete, and `wi_cynpe_waiting_goals_test`'s
            // `?s <=> "km", Conv.tag(?s, ?r), 1 = 2` — `Conv` provided at no `String` —
            // stopped being a definite refutation. That is the UNREDUCED contract broken,
            // not a defect reported.
            EvalError::OperationBodyMissing { .. } => BridgeDisposition::Schedule,
            // Proposal 039 / WI-084: the const type-checks and only its runtime VALUE
            // is absent from this build — a spec-only build of a program a codegen'd one
            // carries the value for.
            EvalError::ConstValueUnavailable { .. } => BridgeDisposition::Schedule,

            // ── Fault: the callee could not be run to an answer ──
            EvalError::Raised { payload, .. } => raised_disposition(kb, payload),
            // ── NoProvider: the requirement is known not to be available ──
            //
            // A slot the argument types pinned and no provider answers: the call has no
            // value at these arguments, and no binding can give it one.
            EvalError::UnpinnedRequirement { marker, .. }
                if crate::kb::typing::absence_is_unprovided(kb, *marker) =>
            {
                BridgeDisposition::NoProvider
            }
            // AN EFFECT A RULE BODY REACHED is declined there — the scratch interpreter's
            // registry is empty, so the operation asking a handler stops — and REPORTED:
            // scheduled, it left a bare residual, and a drain of the relation died
            // `relation_floundered`, reading as an unbound variable (user, 2026-10-16).
            // The goal still delays (a fault's value answer is `None` as a schedule's is),
            // which `docs/kernel-language.md`'s WI-20260830-DQD5W argument rests on: a
            // parametric row admitted into a relational view instantiates to a real effect,
            // raises it here, and the goal residualizes. The message names the effect
            // (`KnowledgeBase::bridge_fault_message`), not a `reify`. As a fault it marks the
            // WHOLE search incomplete from the moment the goal is first tried, a branch a
            // later goal refutes included — so a negation over it is conditional, a drain of
            // it fails, a quantified constraint over it is undecidable and does not load, and
            // the verdict follows the goal order. Kept so (user, 2026-10-16), as a raise
            // already behaves; `wi_9wvt7_clock_handler_test`'s refuted-branch rows pin each.
            EvalError::UnhandledEffect { .. }
            | EvalError::UnboundVar { .. }
            | EvalError::UnknownOperation { .. }
            | EvalError::TypeMismatch { .. }
            | EvalError::ArityMismatch { .. }
            | EvalError::Overflow { .. }
            // A hole a rule body reached: the goal has no value, and the author is told
            // which operation is not written yet.
            | EvalError::NotImplemented { .. }
            | EvalError::OverArityConstructor { .. }
            // THE TWO BUDGET EXHAUSTIONS AGREE, and an earlier draft had them
            // disagreeing — `DepthExceeded` as a silent truncation beside
            // `StepsExhausted` as a fault. Both mean the CALLEE did not finish, both
            // have a cap worth naming, and a `Fault` already marks the stream
            // incomplete, so the truncation reading gave up the message for nothing.
            | EvalError::DepthExceeded { .. }
            | EvalError::StepsExhausted { .. }
            | EvalError::UnsupportedHandlerAction { .. }
            | EvalError::ConstCycle { .. }
            | EvalError::AmbiguousRequirement { .. }
            | EvalError::UnpinnedRequirement { .. }
            | EvalError::AmbiguousSpecOpDispatch { .. }
            | EvalError::MacroRejected { .. }
            | EvalError::UnboundTypeParam { .. }
            | EvalError::KbReadFailed(_)
            | EvalError::ScopedKbOutlivesCall { .. }
            | EvalError::ReifyPayloadUnread { .. }
            | EvalError::RaiseTypeUnread { .. }
            | EvalError::TypePatternUnjudged { .. }
            | EvalError::Internal(_) => BridgeDisposition::Fault,
        }
    }
}

/// Which of the runtime's accounts a raised `payload` is: an APPLICATION of one of their
/// constructors, as the runtime raises each, its field written. A bare reference to the
/// constructor names no account — a symbol a program holds (`lookup_symbol`'s answer, a
/// clause's bare name) — and is none: raised, it is the program's own payload. Read through
/// the carrier-neutral view, so a payload riding as a term answers as one riding as an
/// entity.
pub(crate) fn raised_runtime_account(
    kb: &crate::kb::KnowledgeBase,
    payload: &Value,
) -> Option<crate::kb::RuntimeAccount> {
    use crate::kb::term_view::{TermView, ViewHead};
    let value = payload.carried();
    match value {
        Value::Entity { .. } | Value::Term { .. } | Value::Node(_) => match value.head(kb) {
            ViewHead::Functor {
                functor: f,
                pos_arity,
                named_arity,
            } if pos_arity + named_arity > 0 => kb.runtime_account_of(f),
            _ => None,
        },
        _ => None,
    }
}

/// The `Raised` half of [`EvalError::bridge_disposition`]: a raise is a FAULT unless its
/// payload is the runtime's account of a drain that did not decide or of a load that did not
/// happen. No program constructs one of the runtime's accounts ([`crate::kb::RuntimeAccount`]),
/// so the payload names its cause wherever it is raised, also where a boundary caught it and
/// the program raised it again, in that operation or in a later goal of the rule.
///
/// KEYED BY SYMBOL, never by name (WI-897), and read by [`raised_runtime_account`]. An
/// unresolved account matches no payload, which is the loud side: a fault. A construction of
/// one at run time is refused where it is built (`make_fn`, `replace_named_arg`), and one
/// written in a query pattern or a data file where it is read.
fn raised_disposition(kb: &crate::kb::KnowledgeBase, payload: &Value) -> BridgeDisposition {
    match raised_runtime_account(kb, payload) {
        // WI-737 — an eval-side relation drain that stayed undischarged. The sub-search did
        // not decide; that is [`BridgeDisposition::Schedule`]'s exact meaning, and calling
        // it a fault would report "the callee failed" for a goal nothing has answered yet.
        // WI-SPGBP — `KB.loaded` reporting that the sources it was handed do not load. A
        // verdict the operation was asked for, delivered on the channel the language gives
        // it; the rule that called it without an `Error.reify` gets no value, and that is
        // the missing reify rather than a failure of the load.
        Some(crate::kb::RuntimeAccount::RelationFloundered | crate::kb::RuntimeAccount::LoadFailed) => {
            BridgeDisposition::Schedule
        }
        // A search behind a stream that faulted: the account of a search the runtime could
        // not finish, which a boundary around the call does not repair.
        Some(crate::kb::RuntimeAccount::EvaluationFailure) | None => BridgeDisposition::Fault,
    }
}

impl std::fmt::Display for EvalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EvalError::UnboundVar { name, .. } => write!(f, "unbound variable: {name}"),
            EvalError::UnknownOperation { name } => write!(f, "unknown operation: {name}"),
            // WI-1092 — the "typer-guaranteed invariant violation (should be
            // unreachable)" this said is no longer true, and saying it misdirects the
            // author who now reaches it: an ordinary program that declares an
            // operation and defines it nowhere lands here, and used to be answered
            // `false` instead. The three things a call runs are named because which one
            // is missing is the repair, and the equation trap is named because it is
            // the shape that looks like a definition and is not.
            //
            // WI-20261011-CR6GD — CLAUSES ARE NOT A FOURTH. This listed "no rule clause
            // indexed under it" beside the three, for every operation, and eval looks for
            // one only where a carrier's `eq` is proved; an operation with clauses and
            // nothing else was told it had none. What the clauses are is said apart from
            // what a call runs, and by whether there are any.
            EvalError::OperationBodyMissing {
                name,
                defined_by_clauses,
                backtrace,
            } => {
                write!(
                    f,
                    "operation has no body: {name} — nothing this runtime can run is \
                     registered for it: no operation body, no host `operation_map` entry \
                     for this language, and no builtin. "
                )?;
                if *defined_by_clauses {
                    write!(
                        f,
                        "It is defined by the clauses indexed under it, and clauses answer \
                         a goal in a rule body, not a call: the one call they run is a \
                         carrier's `eq` over two ground values of that carrier — \
                         kernel-language.md §5.3."
                    )?;
                } else {
                    write!(
                        f,
                        "No clause is indexed under it either. (An untagged `<=>` \
                         equation is indexed under the CONNECTIVE, so its subject owns no \
                         clause — kernel-language.md §5.3.)"
                    )?;
                }
                write!(f, "\nbacktrace:\n{backtrace}")
            }
            EvalError::TypeMismatch { expected, got } => {
                write!(f, "type mismatch: expected {expected}, got {got}")
            }
            EvalError::ArityMismatch { op, expected, got } => {
                write!(f, "{op}: expected {expected} args, got {got}")
            }
            EvalError::Overflow { op } => write!(f, "{op}: integer overflow"),
            EvalError::NotImplemented { running: Some(op) } => {
                write!(f, "not implemented: `{op}` reached `todo()`")
            }
            EvalError::NotImplemented { running: None } => {
                write!(f, "not implemented: `todo()` reached")
            }
            EvalError::OverArityConstructor {
                functor,
                given,
                unfilled,
                declared,
            } => write!(
                f,
                "constructor '{functor}' given {given} positional argument(s) but has \
                 {unfilled} unfilled field(s) (declares: {declared})",
            ),
            EvalError::DepthExceeded { cap } => {
                write!(f, "activation stack depth exceeded cap of {cap}")
            }
            EvalError::StepsExhausted { cap, chain } => {
                write!(
                    f,
                    "evaluation exceeded the step budget of {cap} (a non-terminating loop, or a \
                     real computation needing a higher step_cap)"
                )?;
                if !chain.is_empty() {
                    // Distinct ops in the ring are the loop body — surface them
                    // up front, then the ordered chain that exhibits the cycle.
                    let mut distinct: Vec<&String> = Vec::new();
                    for op in chain {
                        if !distinct.contains(&op) {
                            distinct.push(op);
                        }
                    }
                    write!(
                        f,
                        ".\n  operations involved: {}\n  recent dispatches (most recent last): {}",
                        distinct
                            .iter()
                            .map(|s| s.as_str())
                            .collect::<Vec<_>>()
                            .join(", "),
                        chain
                            .iter()
                            .map(|s| s.as_str())
                            .collect::<Vec<_>>()
                            .join(" -> "),
                    )?;
                }
                Ok(())
            }
            EvalError::UnhandledEffect { name, .. } => {
                write!(f, "no handler registered for effect `{name}`")
            }
            EvalError::Raised { .. } => write!(f, "raised error"),
            EvalError::UnsupportedHandlerAction {
                action,
                effect,
                op,
                detail,
                backtrace,
            } => {
                write!(
                    f,
                    "handler for effect `{effect}` returned the `{action}` action while \
                     dispatching operation `{op}`, but the runtime cannot honor it yet: \
                     `{action}` needs the Branch / suspend-resume substrate (WI-075). \
                     This is a runtime-internal not-yet-implemented path."
                )?;
                if let Some(detail) = detail {
                    write!(f, " reason: {detail}")?;
                }
                write!(f, "\nbacktrace:\n{backtrace}")
            }
            EvalError::ConstCycle { name } => write!(
                f,
                "const `{name}` depends on itself (cycle detected while forcing its value)"
            ),
            EvalError::ConstValueUnavailable { name } => write!(
                f,
                "const `{name}` has no value source in this build: it is host-supplied \
                 (bodyless) and no reflect builtin is registered for it"
            ),
            EvalError::Suspended { detail, .. } => {
                write!(f, "semantic comparison suspended (undecided): {detail}")
            }
            // WI-843: neither message may say "the instances are incoherent" any
            // more — two NAMEABLE providers coexist by design (058 tier 3), and the
            // defect is that THIS route cannot select. Both fire on value-directed
            // dispatch, which has no call-site bracket (§4.2 leaves rule bodies out
            // of selection), so the repair is to give the call a selecting site or
            // to keep one provision.
            EvalError::UnpinnedRequirement { detail, .. } => write!(f, "{detail}"),
            EvalError::AmbiguousRequirement {
                op,
                requirement,
                candidates,
            } => write!(
                f,
                "dispatch to `{op}`: its requirement `{requirement}` is provided by \
                 tied providers ({}) and this route selects none — value-directed \
                 dispatch carries no `[Spec = Witness]` bracket, so route the call \
                 through an operation that can write one, or keep a single provision",
                candidates.join(", "),
            ),
            // WI-1012: rendered by the channel's own owner
            // (`kb::typing::ambiguous_spec_op_dispatch_message`), shared with
            // `TypeError::AmbiguousSpecOpDispatch` and both `LoadError` renderings —
            // the same tie is refused at LOAD when the carrier is statically concrete
            // and here when it is not, so the two faces must quote one sentence.
            EvalError::AmbiguousSpecOpDispatch {
                op,
                carrier,
                candidates,
                repair,
            } => write!(
                f,
                "{}",
                crate::kb::typing::ambiguous_spec_op_dispatch_message(
                    op, carrier, candidates, *repair,
                ),
            ),
            // WI-757: the same sentence the typer renders into a load error, so a
            // macro invoked at runtime and one expanded at compile time report the
            // rejection identically (only the location wrapper differs).
            EvalError::MacroRejected { detail, span } => {
                write!(f, "{}", macro_rejection_message(None, detail))?;
                // Byte offsets, like the sibling `LoadError` `Display`s: this face has
                // no source text to resolve `line:col` against, and dropping the span
                // entirely would throw away the precision the variant exists to carry.
                match span {
                    Some(s) => write!(f, " at {}..{}", s.span.start, s.span.end),
                    None => Ok(()),
                }
            }
            EvalError::UnboundTypeParam { param, running } => write!(
                f,
                "type parameter `{param}` has no binding in the frame of `{running}` — \
                 a body read of a type parameter needs the call site to have bound it, \
                 and this call route did not; a parameter with no binding is not a type"
            ),
            EvalError::KbReadFailed(e) => write!(f, "{e}"),
            EvalError::ScopedKbOutlivesCall { raised } => {
                const WHY: &str = "a scoped KB (`KB.loaded`) cannot leave the call that made it \
                                   here: a rule-body call runs against its caller's own KB, \
                                   each operation application in a run of its own, arguments \
                                   first, so the layer is discarded when the call ends";
                match raised {
                    Some(payload) => write!(
                        f,
                        "it raised {payload}, whose payload holds a scoped KB, and {WHY}"
                    ),
                    None => write!(
                        f,
                        "its value holds a scoped KB, and {WHY} — load and read it in one \
                         operation, or in a lambda, and call that from the rule"
                    ),
                }
            }
            EvalError::ReifyPayloadUnread { detail } => write!(f, "{detail}"),
            EvalError::RaiseTypeUnread { detail } => write!(f, "{detail}"),
            EvalError::TypePatternUnjudged { detail } => write!(f, "type_admits: {detail}"),
            EvalError::Internal(s) => write!(f, "internal evaluator error: {s}"),
        }
    }
}

impl std::error::Error for EvalError {}

/// WI-757 — the ONE wording of a macro rejection, shared by every face it has:
/// [`EvalError::MacroRejected`]'s `Display` (the RUNTIME face, which has no macro
/// name to give), `kb::typing::TypeError::MacroRejected`'s `format`, and both
/// renderings of `kb::load::LoadError::MacroRejected`. WI-852's rule that a
/// diagnostic has one owner — the sentence used to be written twice, so rewording
/// the load-side copy would have silently diverged the eval-side one.
///
/// The sentence names the MACRO, not the surface spelling that expanded to it
/// (`where` → `guarded_of`): the macro is what read the syntax and what the author
/// must satisfy, and the `@[simp]` rule connecting the two is greppable from the
/// name. `detail` is the macro's own words, verbatim.
pub fn macro_rejection_message(macro_name: Option<&str>, detail: &str) -> String {
    match macro_name {
        Some(name) => {
            format!("compile-time macro `{name}` cannot expand this expression: {detail}")
        }
        None => format!("macro cannot expand this expression: {detail}"),
    }
}

/// Render a raised `Error` payload ([`EvalError::Raised`]) as a human-readable
/// line. Store-I/O builtins raise `Str` payloads (printed verbatim); WI-467 made
/// div-by-zero raise the structured `division_by_zero(op: "Int64.div")` entity,
/// and user code can `Error.raise` any `Value`. Renders an entity as
/// `functor(pos…, field: val…)` using `kb` to resolve the interned functor/field
/// symbols to their short names — so an unhandled `10 / 0` prints
/// `division_by_zero(op: "Int64.div")` rather than a `Symbol`-index debug dump.
///
/// `Raised`'s own `Display` drops the payload (the payload is an opaque `Value`;
/// error-ness lives in the CHANNEL, not the value), so every consumer that wants
/// the payload's text comes here. WI-757 moved this out of `anthill-stl`'s
/// runner, which was its only caller: a **macro** that raises at compile time now
/// reports through the same words (`kb::simp_rewrite::try_expand_macro`), and
/// `anthill-core` is the only crate both it and the binaries can share.
pub fn render_raised_payload(kb: &crate::kb::KnowledgeBase, v: &Value) -> String {
    render_payload_at(kb, v, 0)
}

/// The recursion behind [`render_raised_payload`]; `depth` bounds it against
/// pathological nesting and selects the top-level `Str` spelling.
fn render_payload_at(kb: &crate::kb::KnowledgeBase, v: &Value, depth: usize) -> String {
    const MAX_DEPTH: usize = 6;
    match v {
        Value::Unit => "()".to_string(),
        Value::Entity {
            functor,
            pos,
            named,
            ..
        } => {
            let name = kb.local_name_of(*functor);
            if (pos.is_empty() && named.is_empty()) || depth >= MAX_DEPTH {
                return name.to_string();
            }
            let mut parts: Vec<String> = pos
                .iter()
                .map(|p| render_payload_at(kb, p, depth + 1))
                .collect();
            for (fname, fv) in named.iter() {
                parts.push(format!(
                    "{}: {}",
                    kb.local_name_of(*fname),
                    render_payload_at(kb, fv, depth + 1)
                ));
            }
            format!("{}({})", name, parts.join(", "))
        }
        // WI-20260911-0V0F7 — A `Term` / `Node` CARRIER IS READ, not named. Every arm
        // above matches a `Value` variant, so a payload field carried as a hash-consed
        // `Value::Term` or an occurrence `Value::Node` fell to the carrier-kind
        // fallback: `raise_match_failed` puts the scrutinee there, and the resolver's
        // own fault line read `match_failed(occurrence: Node, scrutinee: Node)` —
        // neither the payload nor its sort, which is exactly what this function exists
        // to stop printing. Read through [`crate::kb::term_view::TermView`] instead,
        // which is how the rest of the codebase reads a value whose carrier it does not
        // care about.
        //
        // A LITERAL comes here too, on every carrier — native scalars included
        // (WI-20260907-VM9Q7). They had arms of their own above, mirroring
        // `render_literal_at` by hand; the depth-0 `String` spelling those arms were
        // kept for lives in `render_literal_at`, which takes the depth.
        other => {
            use crate::kb::term_view::{TermView, ViewHead};
            match other.head(kb) {
                ViewHead::Const(lit) => render_literal_at(&lit, depth),
                ViewHead::Ident(s) => kb.local_name_of(s).to_string(),
                ViewHead::Functor {
                    functor,
                    pos_arity,
                    named_arity,
                } => {
                    // A tuple is written as its literal: `(1, 2)`, `()`.
                    let tuple = kb.qualified_name_of(functor)
                        == crate::parse::desugar_target::qualified(
                            crate::parse::desugar_target::TUPLE_LITERAL,
                        );
                    let name = if tuple {
                        String::new()
                    } else {
                        kb.local_name_of(functor).to_string()
                    };
                    if (pos_arity + named_arity) == 0 || depth >= MAX_DEPTH {
                        return if tuple { "()".to_string() } else { name };
                    }
                    let mut parts: Vec<String> = Vec::with_capacity(pos_arity + named_arity);
                    for i in 0..pos_arity {
                        parts.push(match other.pos_arg(kb, i) {
                            Some(c) => render_payload_at(kb, &c.to_value(), depth + 1),
                            None => "?".to_string(),
                        });
                    }
                    let keys = other.named_keys(kb);
                    let unlabelled = tuple
                        && keys.len() > 1
                        && keys.iter().enumerate().all(|(i, k)| {
                            crate::intern::is_positional_label_at(kb.local_name_of(*k), i)
                        });
                    for key in keys {
                        let rendered = match other.named_arg(kb, key) {
                            Some(c) => render_payload_at(kb, &c.to_value(), depth + 1),
                            None => "?".to_string(),
                        };
                        if unlabelled {
                            parts.push(rendered);
                        } else {
                            parts.push(format!("{}: {rendered}", kb.local_name_of(key)));
                        }
                    }
                    format!("{name}({})", parts.join(", "))
                }
                // A variable, `⊥`, and the genuinely opaque carriers (closures,
                // streams, substitutions) have no readable surface form; name the
                // carrier kind rather than leaking a debug dump, as before.
                _ => other.type_name().to_string(),
            }
        }
    }
}

/// A literal in a payload, on whatever carrier it arrived — so `div(1, 0)`'s operands
/// print the same whether they reached the payload boxed or hash-consed.
///
/// A bare top-level `String` prints VERBATIM (store-I/O raises these, and they are the
/// message); every other literal is spelled by `write_literal`, the one surface
/// spelling the CLI's answer printer and `TermPrinter` share (WI-20260907-VM9Q7). This
/// used to be a copy of its own — `Float` through `Display`, so `f(v: 3.0)` printed
/// `f(v: 3)`, and a nested `String` through Rust's `{:?}`.
fn render_literal_at(lit: &crate::kb::term::Literal, depth: usize) -> String {
    match lit {
        crate::kb::term::Literal::String(s) if depth == 0 => s.clone(),
        other => {
            let mut buf = String::new();
            crate::persistence::print::write_literal(other, &mut buf);
            buf
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kb::KnowledgeBase;
    use std::rc::Rc;

    /// WI-467: the `division_by_zero(op:)` entity payload an unhandled
    /// `10 / 0` carries renders as a readable line — `local_name_of` turns the
    /// interned functor/field symbols into names — not the `Symbol`-index
    /// debug dump the old `format!("{payload:?}")` fallback produced.
    #[test]
    fn render_payload_renders_division_by_zero_entity_readably() {
        let mut kb = KnowledgeBase::new();
        let functor = kb.intern("division_by_zero");
        let op_field = kb.intern("op");
        let payload = Value::Entity {
            functor,
            pos: Rc::from([]),
            named: Rc::from([(op_field, Value::Str("Int64.div".to_string()))]),
        };
        assert_eq!(
            render_raised_payload(&kb, &payload),
            r#"division_by_zero(op: "Int64.div")"#,
        );
    }

    /// A bare top-level `Str` payload (store-I/O builtins raise these) still
    /// prints verbatim — unquoted — as before WI-467's renderer landed.
    #[test]
    fn render_payload_prints_bare_string_verbatim() {
        let kb = KnowledgeBase::new();
        assert_eq!(
            render_raised_payload(&kb, &Value::Str("persist failed: disk full".to_string())),
            "persist failed: disk full",
        );
    }
}

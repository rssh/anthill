use crate::intern::Symbol;
use crate::kb::term::TermId;
use crate::span::SourceSpan;

use super::Value;

#[derive(Debug)]
pub enum EvalError {
    UnboundVar { name: String, span: Option<SourceSpan> },
    UnknownOperation { name: String },
    /// An operation was invoked that has neither a body nor a registered
    /// builtin. The typer is supposed to guarantee this never happens, so
    /// hitting it is an invariant violation (a typer/loader bug) — NOT a
    /// recoverable domain error, and it does not ride the `Error` effect
    /// channel. Carries a captured backtrace to locate the bad dispatch.
    OperationBodyMissing { name: String, backtrace: std::backtrace::Backtrace },
    TypeMismatch { expected: &'static str, got: String },
    ArityMismatch { op: &'static str, expected: usize, got: usize },
    Overflow { op: &'static str },
    DepthExceeded { cap: usize },
    /// The `step_cap` work budget was exhausted: a non-terminating computation
    /// (a tail loop, OR a dispatch/deliver value-cascade — both now iterate on
    /// the heap trampoline and tick one step per iteration), or a real
    /// computation that genuinely needs a higher cap. `chain` is the
    /// recent-dispatch ring (most recent last); since a loop repeats its
    /// operations, it names the offending sources so they can be located
    /// quickly. Empty when no `step_cap` was set (the ring is only maintained
    /// when a cap could fire).
    StepsExhausted { cap: u64, chain: Vec<String> },
    UnhandledEffect { effect: Symbol, payload: Option<TermId> },
    /// An anthill-level `Error` effect was raised (proposal 027 §Error).
    /// Produced at the effect-dispatch site from a handler's
    /// `HandlerAction::Throw(payload)`. The payload is an ordinary opaque
    /// `Value` — error-ness lives in *this variant* (the channel), not in
    /// the value itself. Until catch/recover constructs land (WI-195+), a
    /// raised Error aborts evaluation carrying its payload here.
    Raised { payload: Value },
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
    CyclicReference,
    /// Proposal 039 / WI-084: a `const`'s value was demanded while it is already
    /// being forced — a dependency cycle (`const A = B + 1; const B = A + 1`).
    /// The value cache's forcing sentinel detects this dynamically; `name` is the
    /// const whose forcing re-entered.
    ConstCycle { name: String },
    /// Proposal 039 / WI-084: a host-supplied (bodyless) `const`'s value was
    /// demanded but no reflect builtin is registered to produce it. The const
    /// type-checks (its declared type is known) — only the runtime VALUE is
    /// unavailable in this build (the spec-only-vs-codegen axis).
    ConstValueUnavailable { name: String },
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
    Suspended { detail: String, truncated: bool },
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
    AmbiguousRequirement { op: String, requirement: String, candidates: Vec<String> },
    /// WI-857: a dictionary slot that pins NO provider was used — dispatched
    /// through, projected into, or enumerated. The slot carries an empty bundle over
    /// the `NoProvider` marker because its goal did not resolve when the dictionary
    /// was built (nothing provides that spec at those bindings, or more than one
    /// does), or because it is a host-entry stand-in that supplied no dictionary at
    /// all.
    ///
    /// The THIRD member of the family above, and a variant for the same reason: this
    /// is a PROGRAM (or host-entry) error, not an evaluator-invariant one, so the
    /// resolver bridge's `debug_assert` on [`Self::Internal`] must not fire on it —
    /// a bridged rule DELAYS instead. It was `Internal` when first written, which
    /// would have aborted any test whose rule body dispatched through such a slot.
    ///
    /// `detail` is pre-rendered by `kb::typing::marker_refusal`, the one owner of the
    /// sentence (the marker carries no payload, so the wording must hedge over the
    /// three causes — narrowing it is what carrying the reason to runtime would buy).
    UnpinnedRequirement { detail: String },
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
    /// ([`crate::kb::typing::SpecOpSupplier::render`]) because the three are written
    /// in three syntaxes and the author must know which text to delete.
    AmbiguousSpecOpDispatch { op: String, carrier: String, candidates: Vec<String> },
    /// WI-757 — the WI-722 macro contract's DIAGNOSTIC channel: a compile-time
    /// MACRO read its argument occurrences, found them definitively
    /// untranslatable, and says why.
    ///
    /// The distinction this variant exists to draw: every OTHER failure of a
    /// macro is a DECLINE — the macro is merely not applicable (or not ready
    /// yet), so the `[simp]` template call is kept and whatever downstream check
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
    /// that does not translate. `None` leaves the redex span to the reporter.
    /// `simp_rewrite::try_expand_macro` carries this out as a
    /// [`crate::kb::simp_rewrite::MacroRejection`] and the typer reports it as a
    /// load error; at a RUNTIME call of the same op it renders like any other
    /// eval error.
    MacroRejected { expected: &'static str, got: String, span: Option<SourceSpan> },
    Internal(String),
}

impl std::fmt::Display for EvalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EvalError::UnboundVar { name, .. } => write!(f, "unbound variable: {name}"),
            EvalError::UnknownOperation { name } => write!(f, "unknown operation: {name}"),
            EvalError::OperationBodyMissing { name, backtrace } => write!(
                f,
                "operation has no body: {name} — this is a typer-guaranteed invariant \
                 violation (should be unreachable).\nbacktrace:\n{backtrace}"
            ),
            EvalError::TypeMismatch { expected, got } => write!(f, "type mismatch: expected {expected}, got {got}"),
            EvalError::ArityMismatch { op, expected, got } => write!(f, "{op}: expected {expected} args, got {got}"),
            EvalError::Overflow { op } => write!(f, "{op}: integer overflow"),
            EvalError::DepthExceeded { cap } => write!(f, "activation stack depth exceeded cap of {cap}"),
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
                        distinct.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(", "),
                        chain.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(" -> "),
                    )?;
                }
                Ok(())
            }
            EvalError::UnhandledEffect { .. } => write!(f, "unhandled effect"),
            EvalError::Raised { .. } => write!(f, "raised error"),
            EvalError::UnsupportedHandlerAction { action, effect, op, detail, backtrace } => {
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
            EvalError::CyclicReference => write!(f, "cyclic reference detected"),
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
            EvalError::UnpinnedRequirement { detail } => write!(f, "{detail}"),
            EvalError::AmbiguousRequirement { op, requirement, candidates } => write!(
                f,
                "dispatch to `{op}`: its requirement `{requirement}` is provided by \
                 tied providers ({}) and this route selects none — value-directed \
                 dispatch carries no `[Spec = Witness]` bracket, so route the call \
                 through an operation that can write one, or keep a single provision",
                candidates.join(", "),
            ),
            EvalError::AmbiguousSpecOpDispatch { op, carrier, candidates } => write!(
                f,
                "value-directed dispatch of `{op}` on carrier `{carrier}`: {} supply an \
                 implementation ({}) and this call selects none — value-directed \
                 dispatch carries no `[Spec = Witness]` bracket, so route the call \
                 through an operation that can write one, or keep a single provision",
                candidates.len(),
                candidates.join(", "),
            ),
            // WI-757: the same sentence the typer renders into a load error, so a
            // macro invoked at runtime and one expanded at compile time report the
            // rejection identically (only the location wrapper differs).
            EvalError::MacroRejected { expected, got, .. } => {
                write!(f, "macro cannot expand this expression: expected {expected}, got {got}")
            }
            EvalError::Internal(s) => write!(f, "internal evaluator error: {s}"),
        }
    }
}

impl std::error::Error for EvalError {}

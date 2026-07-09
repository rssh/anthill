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
            EvalError::Internal(s) => write!(f, "internal evaluator error: {s}"),
        }
    }
}

impl std::error::Error for EvalError {}

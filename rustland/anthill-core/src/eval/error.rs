use crate::intern::Symbol;
use crate::kb::term::TermId;
use crate::span::SourceSpan;

use super::Value;

#[derive(Debug)]
pub enum EvalError {
    UnboundVar { name: String, span: Option<SourceSpan> },
    UnknownOperation { name: String },
    OperationBodyMissing { name: String },
    TypeMismatch { expected: &'static str, got: String },
    ArityMismatch { op: &'static str, expected: usize, got: usize },
    DivisionByZero { op: &'static str },
    Overflow { op: &'static str },
    DepthExceeded { cap: usize },
    StepsExhausted { cap: u64 },
    MatchFailed { scrutinee: String },
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
    Internal(String),
}

impl std::fmt::Display for EvalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EvalError::UnboundVar { name, .. } => write!(f, "unbound variable: {name}"),
            EvalError::UnknownOperation { name } => write!(f, "unknown operation: {name}"),
            EvalError::OperationBodyMissing { name } => write!(f, "operation has no body: {name}"),
            EvalError::TypeMismatch { expected, got } => write!(f, "type mismatch: expected {expected}, got {got}"),
            EvalError::ArityMismatch { op, expected, got } => write!(f, "{op}: expected {expected} args, got {got}"),
            EvalError::DivisionByZero { op } => write!(f, "{op}: division by zero"),
            EvalError::Overflow { op } => write!(f, "{op}: integer overflow"),
            EvalError::DepthExceeded { cap } => write!(f, "activation stack depth exceeded cap of {cap}"),
            EvalError::StepsExhausted { cap } => write!(f, "step budget exhausted after {cap} steps"),
            EvalError::MatchFailed { scrutinee } => write!(f, "pattern match failed on {scrutinee}"),
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
            EvalError::Internal(s) => write!(f, "internal evaluator error: {s}"),
        }
    }
}

impl std::error::Error for EvalError {}

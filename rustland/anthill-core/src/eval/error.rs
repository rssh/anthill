use crate::intern::Symbol;
use crate::kb::term::TermId;
use crate::span::SourceSpan;

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
            EvalError::CyclicReference => write!(f, "cyclic reference detected"),
            EvalError::Internal(s) => write!(f, "internal evaluator error: {s}"),
        }
    }
}

impl std::error::Error for EvalError {}

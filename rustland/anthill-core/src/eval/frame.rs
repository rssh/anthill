//! Activation stack: explicit, heap-allocated, no native recursion.
//!
//! Per proposal 026 §Activation stack. Each `Frame` either (a) has a
//! fresh `expr` to reduce (`awaiting == None`) or (b) is suspended while
//! a child frame computes a sub-value (`awaiting == Some(...)`). The
//! single `Interpreter::step()` loop drives one transition at a time, so
//! depth is bounded by `ActivationStack::depth_cap` rather than by the
//! host Rust stack.

use smallvec::SmallVec;

use crate::intern::Symbol;
use crate::kb::term::TermId;

use super::value::Value;

/// State a frame is in while waiting for a child frame to produce a value.
/// When the child delivers, the matching variant says how to consume the
/// value and what the frame should do next.
#[derive(Debug)]
pub enum AwaitState {
    /// `if_expr` cond is being evaluated; on delivery pick a branch and
    /// reduce it in this frame.
    ChooseBranch { then_branch: TermId, else_branch: TermId },
    /// `let_expr` rhs is being evaluated; on delivery match the pattern,
    /// extend locals, and reduce the body in this frame.
    LetBind { pattern: TermId, body: TermId },
    /// `match_expr` scrutinee is being evaluated; on delivery try each
    /// branch against the value until one matches.
    MatchDispatch { branches: Vec<TermId> },
    /// An apply node is collecting arg values one at a time. `remaining`
    /// holds the ApplyArg terms still to evaluate (in order).
    ApplyArgs {
        target: Symbol,
        buffered: Vec<Value>,
        remaining: Vec<TermId>,
    },
    /// A constructor node is collecting (possibly named) field values.
    ConstructorArgs {
        ctor_sym: Symbol,
        is_tuple_literal: bool,
        buffered_pos: Vec<Value>,
        buffered_named: Vec<(Symbol, Value)>,
        /// Remaining `ApplyArg` terms paired with their decoded name hint.
        remaining: Vec<(Option<Symbol>, TermId)>,
    },
    /// The frame has dispatched an apply to an anthill-defined operation
    /// body (child frame pushed). When the body produces a value, that
    /// value is the apply's result — cascade it up without re-evaluating
    /// anything in this frame.
    OperationResult,
}

/// A single activation.
pub struct Frame {
    /// Operation the frame is running inside (for error reporting).
    pub op: Symbol,
    /// Expression currently under reduction. Only meaningful when `awaiting`
    /// is `None`; unused while this frame is suspended above a child.
    pub expr: TermId,
    /// Lexical bindings in this frame.
    pub locals: SmallVec<[(Symbol, Value); 4]>,
    /// None = fresh (ready to reduce `expr`); Some = suspended, waiting for
    /// the child frame above to deliver a value.
    pub awaiting: Option<AwaitState>,
}

pub struct ActivationStack {
    frames: Vec<Frame>,
    depth_cap: usize,
}

impl ActivationStack {
    /// Heap-allocated frames are ~200 bytes each; 1M = ~200MB worst case but
    /// only materialized for deep non-tail recursion. Tail calls stay O(1)
    /// under TCO (WI-061), so the cap is a loud-failure safety valve, not a
    /// correctness limit. Tests override via `ActivationStack::set_cap`.
    pub const DEFAULT_DEPTH_CAP: usize = 1_000_000;

    pub fn new() -> Self { Self::with_cap(Self::DEFAULT_DEPTH_CAP) }

    pub fn with_cap(depth_cap: usize) -> Self {
        Self { frames: Vec::new(), depth_cap }
    }

    pub fn depth(&self) -> usize { self.frames.len() }
    pub fn is_empty(&self) -> bool { self.frames.is_empty() }

    pub fn push(&mut self, frame: Frame) -> Result<(), super::error::EvalError> {
        if self.frames.len() >= self.depth_cap {
            return Err(super::error::EvalError::DepthExceeded { cap: self.depth_cap });
        }
        self.frames.push(frame);
        Ok(())
    }

    pub fn pop(&mut self) -> Option<Frame> { self.frames.pop() }

    pub fn top(&self) -> Option<&Frame> { self.frames.last() }
    pub fn top_mut(&mut self) -> Option<&mut Frame> { self.frames.last_mut() }

    /// Override the depth cap (test hook). Lets a test drive the stack
    /// past the cap without waiting for the ~1024-deep default.
    pub fn set_cap(&mut self, cap: usize) { self.depth_cap = cap; }
}

impl Default for ActivationStack {
    fn default() -> Self { Self::new() }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intern::Symbol;
    use crate::kb::term::TermId;

    fn dummy_frame() -> Frame {
        Frame {
            op: Symbol::from_raw(0),
            expr: TermId::from_raw(0),
            locals: SmallVec::new(),
            awaiting: None,
        }
    }

    #[test]
    fn push_pop() {
        let mut s = ActivationStack::new();
        assert!(s.is_empty());
        s.push(dummy_frame()).unwrap();
        assert_eq!(s.depth(), 1);
        assert!(s.pop().is_some());
        assert!(s.is_empty());
    }

    #[test]
    fn depth_cap() {
        let mut s = ActivationStack::with_cap(2);
        s.push(dummy_frame()).unwrap();
        s.push(dummy_frame()).unwrap();
        let err = s.push(dummy_frame()).unwrap_err();
        assert!(matches!(err, super::super::error::EvalError::DepthExceeded { cap: 2 }));
    }
}

//! Activation stack: explicit, heap-allocated, no native recursion.
//!
//! Per proposal 026 §Activation stack. Each `Frame` either (a) has a
//! fresh `expr` to reduce (`awaiting == None`) or (b) is suspended while
//! a child frame computes a sub-value (`awaiting == Some(...)`). The
//! single `Interpreter::step()` loop drives one transition at a time, so
//! depth is bounded by `ActivationStack::depth_cap` rather than by the
//! host Rust stack.

use std::rc::Rc;

use smallvec::SmallVec;

use crate::intern::Symbol;
use crate::kb::node_occurrence::{MatchBranch, NodeOccurrence};
use crate::kb::term::TermId;

use super::value::Value;

/// Operation type-argument channel — one entry per declared `[T_i]`
/// in the callee's declaration order, paired with the typer-resolved
/// type term. Inline capacity 2 matches the requirements channel
/// (proposal 042 §"Two channels, deterministic ordering"). Used on
/// `Frame.type_args`, both `ApplyArgs` variants, and threaded through
/// every apply/dispatch path in `eval::eval`.
pub type FrameTypeArgs = SmallVec<[(Symbol, TermId); 2]>;

/// State a frame is in while waiting for a child frame to produce a value.
/// When the child delivers, the matching variant says how to consume the
/// value and what the frame should do next.
///
/// WI-078 (proposal 027, Phase A step a): `Clone` so a frame — and the whole
/// `ActivationStack` — can be snapshotted for continuation capture. Every field
/// is already cloneable: `Value` (`value.rs`), `Dictionary`
/// (`dictionary.rs`), `MatchBranch` (`node_occurrence.rs`), and the
/// `Rc<NodeOccurrence>` / `Symbol` / `TermId` leaves.
#[derive(Debug, Clone)]
pub enum AwaitState {
    /// `if_expr` cond is being evaluated; on delivery pick a branch and
    /// reduce it in this frame.
    ChooseBranch {
        then_branch: Rc<NodeOccurrence>,
        else_branch: Rc<NodeOccurrence>,
    },
    /// `let_expr` rhs is being evaluated; on delivery match the pattern,
    /// extend locals, and reduce the body in this frame. WI-511: `pattern` is
    /// the `NodeKind::Pattern` occurrence, read directly by `match_pattern`.
    LetBind {
        pattern: Rc<NodeOccurrence>,
        body: Rc<NodeOccurrence>,
    },
    /// `match_expr` scrutinee is being evaluated; on delivery try each
    /// branch against the value until one matches. `scrutinee_occ` is the
    /// scrutinee expression's occurrence, kept so an exhausted match can raise
    /// `Error[MatchFailed]` with a source-anchored payload (WI-610).
    MatchDispatch {
        branches: Vec<MatchBranch>,
        scrutinee_occ: Rc<NodeOccurrence>,
    },
    /// WI-20260907-0QV5A: a guarded arm whose PATTERN matched is waiting for its
    /// GUARD's value. Its own state rather than a flag on
    /// [`AwaitState::MatchDispatch`] because a guard is an arbitrary expression —
    /// it may call an operation, raise, or suspend — so the arm scan cannot stay
    /// synchronous once it reaches one.
    ///
    /// On delivery (`eval.rs`, `AwaitState::MatchGuard`): a `true` guard installs
    /// `bindings` on the frame and reduces `body`; a `false` one resumes the scan
    /// at `rest` — the arms AFTER the guarded one — against `scrutinee`, with
    /// `bindings` dropped unread. They can be dropped rather than unwound because
    /// they were never installed on this frame: the guard reads them through the
    /// CHILD frame's locals, which the delivery pops. That is what keeps a false
    /// guard's bindings out of a later arm's environment.
    ///
    /// `scrutinee` is the already-computed match subject, carried so a fallthrough
    /// does not re-evaluate the scrutinee expression, and `scrutinee_occ` is kept
    /// for the same reason `MatchDispatch` keeps it — an exhausted scan raises
    /// `Error[MatchFailed]` anchored at the source (WI-610), and running out of
    /// arms because every guard was false is exhaustion just as much as running
    /// out because no pattern fit.
    MatchGuard {
        bindings: crate::eval::pattern::Bindings,
        body: Rc<NodeOccurrence>,
        rest: Vec<MatchBranch>,
        scrutinee: Value,
        scrutinee_occ: Rc<NodeOccurrence>,
    },
    /// An apply node is collecting arg values one at a time. `remaining`
    /// holds the argument occurrences still to evaluate (in order).
    /// `type_args` carries the typer-resolved operation type
    /// arguments forward to dispatch, paralleling the requirements
    /// channel on `ApplyWithinArgs` (WI-272). Empty when the callee
    /// has no declared type params.
    ApplyArgs {
        target: Symbol,
        buffered: Vec<Value>,
        remaining: Vec<Rc<NodeOccurrence>>,
        type_args: FrameTypeArgs,
    },
    /// WI-223: an `apply_within` node — like ApplyArgs but threads the
    /// callee's name-keyed `requirements` channel through to the callee
    /// frame at dispatch time. Per `docs/design/operation-call-model.md`
    /// §"Eval mechanics: AwaitState with requirements", requirements
    /// are evaluated before args; this variant carries them forward.
    /// `start_apply_within` builds it as the expanded named frame
    /// requirements (WI-237 names model).
    /// `type_args` rides alongside the requirements channel —
    /// positional in the callee's `[T1, T2, ...]` declaration order,
    /// each entry `(declared-name, resolved-type-term)`. Installed on
    /// the callee's `Frame.type_args` at dispatch (WI-272).
    ApplyWithinArgs {
        target: Symbol,
        buffered: Vec<Value>,
        remaining: Vec<Rc<NodeOccurrence>>,
        requirements: SmallVec<[(Symbol, crate::eval::value::Dictionary); 2]>,
        type_args: FrameTypeArgs,
    },
    /// A constructor node is collecting (possibly named) field values.
    ConstructorArgs {
        ctor_sym: Symbol,
        is_tuple_literal: bool,
        buffered_pos: Vec<Value>,
        buffered_named: Vec<(Symbol, Value)>,
        /// Remaining argument occurrences paired with their decoded
        /// name hint. The first entry's expression is a placeholder —
        /// only its name is read (it identifies the value about to
        /// arrive on delivery).
        remaining: Vec<(Option<Symbol>, Rc<NodeOccurrence>)>,
    },
    /// WI-707: a SORT-headed application (`Cell[V = Int64]`) in a `Type` slot is a
    /// parameterized TYPE, not a call — it collects its type arguments the way a
    /// constructor collects fields, then assembles a `Value::Term` type value
    /// (`finish_sort_type`).
    ///
    /// Its own variant rather than a flag on [`AwaitState::ConstructorArgs`]: the
    /// assembled carrier differs (a type TERM, not an entity), and the slots being
    /// filled are type PARAMETERS, not declared fields — so none of the
    /// constructor's field canonicalization / list-literal / tuple handling applies.
    ///
    /// The arguments are EVALUATED (not read off the syntax) because a type argument
    /// need not be a literal sort name — it can be any expression that denotes a
    /// type, and evaluation is what routes each through the frame (locals, the
    /// type-argument channel, a nested application).
    ///
    /// Substituting a type param read here (WI-708): inside a GENERIC operation,
    /// `Cell[V = T]` now builds `Cell[V = Int64]` from the frame's type-arg channel
    /// (`T ⇒ Int64`). Because the argument is EVALUATED, `T` reaches `reduce_var`,
    /// which consults the channel via `find_type_arg`. The channel is keyed by the
    /// op-scoped symbol a body reference to `T` resolves to — NOT the bare
    /// `OperationInfo.type_params` name (they differ; see `op_scoped_type_param_symbol`
    /// in `kb/typing.rs`) — so the identity match hits. Before WI-708 it missed and the
    /// WI-206 bare-sort arm delivered a dangling `Ref(T)`.
    SortTypeArgs {
        sort_sym: Symbol,
        buffered_pos: Vec<Value>,
        buffered_named: Vec<(Symbol, Value)>,
        /// Remaining type-argument occurrences paired with their name hint
        /// (`None` for a positional `Cell[Int64]`). As in `ConstructorArgs`, the
        /// first entry's expression is a placeholder — only its name is read.
        remaining: Vec<(Option<Symbol>, Rc<NodeOccurrence>)>,
    },
    /// WI-714 (proposal 052): an APPLIED rule reference (`queens(board)`,
    /// `queryTwoParams(x: 3)`) evaluates its supplied arguments (each BINDS a head
    /// parameter, narrowing the relation's schema) the way `SortTypeArgs` evaluates
    /// type arguments, then assembles the `Value::Relation` via `build_relation_value`
    /// with the bound slots spliced into the query's goal atom. The arguments are
    /// EVALUATED (not read off the syntax) because a bound value is any expression —
    /// a local, a literal, a nested call.
    RelationArgs {
        ref_sym: Symbol,
        buffered_pos: Vec<Value>,
        buffered_named: Vec<(Symbol, Value)>,
        /// Remaining argument occurrences paired with their name hint (`None` for a
        /// positional `queens(board)`). As in `SortTypeArgs`, the first entry's
        /// expression is a placeholder — only its name is read on delivery.
        remaining: Vec<(Option<Symbol>, Rc<NodeOccurrence>)>,
    },
    /// The frame has dispatched an apply to an anthill-defined operation
    /// body (child frame pushed). When the body produces a value, that
    /// value is the apply's result — cascade it up without re-evaluating
    /// anything in this frame.
    OperationResult,
    /// Proposal 027.4 — an `Error.reify` BOUNDARY: the frame that dispatched
    /// `reify` is suspended here while the thunk runs in the frame above, and
    /// this frame is the marker a raise unwinds to. 047 §4: *"`reset` is a
    /// frame (a boundary marker on the stack)"*.
    ///
    /// Its own state rather than [`AwaitState::OperationResult`] — which
    /// nothing sets, TCO having replaced every operation entry in place — for
    /// two reasons that are the whole of the mechanism:
    ///
    ///  * `reify` is the ONE dispatch that must NOT be TCO'd. The extra frame
    ///    is not overhead to be dropped; it is what
    ///    [`ActivationStack::reify_boundaries`] finds.
    ///  * The two exits differ. A normal delivery wraps the thunk's value as
    ///    `ok(v)`; the raise path truncates to this frame and delivers
    ///    `err(payload)`. Both then pop it and hand the `Result` to its parent,
    ///    so the boundary is answered exactly once either way.
    ///
    /// Only `EvalError::Raised` is caught here, and only a raise whose PAYLOAD IS OF
    /// THE TYPE THIS BOUNDARY WAS TYPED AT. `Internal`, `StepsExhausted`,
    /// `UnhandledEffect` and the rest pass through: a reify boundary handles the
    /// `Error` EFFECT, not interpreter faults.
    ReifyBoundary {
        /// The payload SORT this boundary discharges — `Some(Boom)` for a `reify` typed
        /// at `Error[Boom]`, read off the type-argument channel as `T1` at the call site.
        ///
        /// CARRIED BECAUSE THE TYPE SYSTEM ALREADY DRAWS THIS LINE AND THE RUNTIME MUST
        /// TOO. `reify`'s row shares its tail: a body raising `{Error[Boom],
        /// Error[Other]}` reified at `Boom` leaves `Error[Other]` in the CALLER's row,
        /// and the typer refuses a caller that does not declare it. Without this field
        /// the unwind caught on the error's CARRIER — "is this a raise" — so it
        /// swallowed `Other` too and delivered it inside a `Result[E = Boom]`, which
        /// surfaced one step later as a match failure on a value that could never
        /// legally be there. Measured, before this: `caughtBoom(7)` answered
        /// `match_failed(scrutinee: other(n: 7))`.
        ///
        /// A `Symbol` AND NOT THE TYPE TERM: the narrowing is a question about a
        /// value's SORT, which is all `runtime_carrier_sort` can answer, so resolving
        /// `T1` to that sort once at INSTALL keeps the catch path total.
        ///
        /// `None` IS "THIS BOUNDARY CANNOT BE NARROWED", AND IT CATCHES WIDE — exactly
        /// what every boundary did before the narrowing existed. Three shapes reach it,
        /// all ordinary: a `T1` still standing for an enclosing operation's type
        /// parameter (a generic `reify` entered from a host `interp.call` or a rule-body
        /// bridge, where the frame channel is empty and nothing can ground it), a `T1`
        /// whose head names no sort (a TUPLE payload's head is the ENTITY
        /// `TypeExtractor.NamedTuple`), and a `T1` absent from the channel altogether.
        ///
        /// NOT A FALLBACK PAPERING OVER AN ERROR — the ROW is the guarantee either way.
        /// The typer discharged this label by the signature (WI-329), and the narrowing
        /// is an ADDITIONAL check available only where the payload is nominal. Refusing
        /// instead was measured and is worse than useless: `rule viaGenericRule(?r) :-
        /// catchIt(lambda () -> mayFail(0 - 1), ?r)` aborted on a `debug_assert` in debug
        /// and SILENTLY LOST ITS ANSWER in release, for a program that worked before.
        payload: Option<Symbol>,
    },
}

/// A single activation.
///
/// WI-078 (Phase A step a): `Clone` — a cloned frame shares its immutable
/// `Rc<NodeOccurrence>` sub-trees and deep-copies its mutable `locals` /
/// `buffered` value vectors, which is exactly the snapshot semantics
/// `snapshot_eval_state` needs (the snapshot must not alias the live frame's
/// evolving bindings).
#[derive(Clone)]
pub struct Frame {
    /// Operation the frame is running inside (for error reporting).
    pub op: Symbol,
    /// Expression currently under reduction. Only meaningful when `awaiting`
    /// is `None`; unused while this frame is suspended above a child.
    pub expr: Rc<NodeOccurrence>,
    /// Lexical bindings in this frame.
    pub locals: SmallVec<[(Symbol, Value); 4]>,
    /// WI-223 / WI-237: name-keyed requirement values available to this
    /// body. Populated on frame push from the call site's expanded
    /// `apply_within.requirements` channel (or `closure.requirements`
    /// for HO calls). Each entry is `(synthesized __req_* name, handle)`;
    /// the eval resolves a body's `var_ref(name)` requirement reads
    /// against it. Per `docs/design/operation-call-model.md` §"Runtime:
    /// frame, requirement value, closure".
    pub requirements: SmallVec<[(Symbol, crate::eval::value::Dictionary); 2]>,
    /// Operation-level type arguments for the call that pushed this
    /// frame (WI-272). Per `docs/design/operation-call-model.md`
    /// §"Operation type arguments", sequenced *after* sort-level
    /// requirements; held as a separate channel rather than collapsing
    /// into `requirements` (the "polymorphic value" alternative). Each
    /// entry is `(declared-param-name, resolved-type-term)`, in the
    /// callee's `[T1, T2, ...]` declaration order. Body-side
    /// `var_ref(T)` reads consult this list alongside `requirements`.
    pub type_args: FrameTypeArgs,
    /// None = fresh (ready to reduce `expr`); Some = suspended, waiting for
    /// the child frame above to deliver a value.
    pub awaiting: Option<AwaitState>,
}

/// Captured context for pushing a child frame: everything the eval
/// inherits from the parent's locals/requirements/type-args scope.
/// `expr` is supplied separately by each caller (it's the child
/// sub-expression about to be reduced).
pub struct ChildFrameContext {
    pub op: Symbol,
    pub locals: SmallVec<[(Symbol, Value); 4]>,
    pub requirements: SmallVec<[(Symbol, crate::eval::value::Dictionary); 2]>,
    pub type_args: FrameTypeArgs,
}

impl Frame {
    /// Snapshot this frame's context for a child push. Centralises the
    /// otherwise-fivefold `(op, locals.clone(), requirements.clone(),
    /// type_args.clone())` destructure in `eval::eval`.
    pub fn child_context(&self) -> ChildFrameContext {
        ChildFrameContext {
            op: self.op,
            locals: self.locals.clone(),
            requirements: self.requirements.clone(),
            type_args: self.type_args.clone(),
        }
    }
}

/// WI-078 (Phase A step a): `Clone` — the whole activation stack is the
/// continuation. `snapshot_eval_state` (Phase A step c) clones it to capture
/// "the rest of the computation" for later `resume_with`; multi-shot `Choice`
/// re-enters a cloned snapshot per alternative.
#[derive(Clone)]
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

    pub fn new() -> Self {
        Self::with_cap(Self::DEFAULT_DEPTH_CAP)
    }

    pub fn with_cap(depth_cap: usize) -> Self {
        Self {
            frames: Vec::new(),
            depth_cap,
        }
    }

    pub fn depth(&self) -> usize {
        self.frames.len()
    }
    pub fn is_empty(&self) -> bool {
        self.frames.is_empty()
    }

    pub fn push(&mut self, frame: Frame) -> Result<(), super::error::EvalError> {
        if self.frames.len() >= self.depth_cap {
            return Err(super::error::EvalError::DepthExceeded {
                cap: self.depth_cap,
            });
        }
        self.frames.push(frame);
        Ok(())
    }

    pub fn pop(&mut self) -> Option<Frame> {
        self.frames.pop()
    }

    pub fn top(&self) -> Option<&Frame> {
        self.frames.last()
    }
    pub fn top_mut(&mut self) -> Option<&mut Frame> {
        self.frames.last_mut()
    }

    /// Override the depth cap (test hook). Lets a test drive the stack
    /// past the cap without waiting for the ~1024-deep default.
    pub fn set_cap(&mut self, cap: usize) {
        self.depth_cap = cap;
    }

    /// Proposal 027.4 — every [`AwaitState::ReifyBoundary`] at or above `floor`,
    /// INNERMOST FIRST, paired with the payload type each was typed at.
    ///
    /// A LIST AND NOT THE TOPMOST, because a boundary may DECLINE: a raise is caught
    /// by the innermost boundary whose payload type it matches, and travels past the
    /// ones it does not — the same rule the row already states statically, since a
    /// label a `reify` does not discharge stays in the caller's row. The caller
    /// decides acceptance (it needs the KB, which this type does not hold), so the
    /// candidates are collected here and judged there.
    ///
    /// `floor` is NOT decoration. `run()` drains until the stack is EMPTY and has
    /// no per-run base, so a builtin's `interp.call` pushes its frames on top of
    /// its caller's; a boundary BELOW the floor belongs to an outer `run()`, and
    /// answering it from an inner one would hand that outer frame's `Result` back
    /// as the inner call's value. (The wider defect — `deliver` popping past the
    /// base — is pre-existing; bounding this scan is what 027.4 owes.)
    pub fn reify_boundaries(&self, floor: usize) -> SmallVec<[(usize, Option<Symbol>); 2]> {
        self.frames
            .iter()
            .enumerate()
            .skip(floor)
            .rev()
            .filter_map(|(i, f)| match &f.awaiting {
                Some(AwaitState::ReifyBoundary { payload }) => Some((i, *payload)),
                _ => None,
            })
            .collect()
    }

    /// Drop back to `depth` frames, discarding everything above.
    ///
    /// FOR AN ERROR EXIT ONLY, and one caller by design: [`Interpreter::run`] restoring
    /// the `floor` it entered at when the trampoline returned `Err` — see the comment
    /// there for what leaking those frames cost, and for why the repair sits at the
    /// trampoline rather than at any of its three drivers. A no-op when the stack is
    /// already at or below `depth`.
    pub(crate) fn truncate_to(&mut self, depth: usize) {
        if self.frames.len() > depth {
            self.frames.truncate(depth);
        }
    }

    /// Discard every frame above `idx` and leave the boundary there no longer
    /// awaiting — the raise it was waiting for has arrived, so the caller
    /// delivers `err(payload)` FROM this frame, which pops it and cascades to
    /// its parent exactly as the success path does.
    ///
    /// `idx` must come from [`Self::reify_boundaries`] — hence `pub(crate)`
    /// where the rest of this type is `pub`. `ActivationStack` is re-exported, so a
    /// `pub` spelling would put a precondition nothing outside the crate can honour
    /// on the public surface, guarded only by a `debug_assert` that is absent from
    /// the shipped binary: out of range, the `truncate` is a no-op and the next line
    /// is a raw index panic; in range but not a boundary, it silently clears an
    /// unrelated frame's `awaiting` and surfaces one delivery later as
    /// "deliver: parent frame had no awaiting state".
    pub(crate) fn unwind_to_boundary(&mut self, idx: usize) {
        debug_assert!(matches!(
            self.frames.get(idx).map(|f| &f.awaiting),
            Some(Some(AwaitState::ReifyBoundary { .. }))
        ));
        self.frames.truncate(idx + 1);
        self.frames[idx].awaiting = None;
    }
}

impl Default for ActivationStack {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intern::Symbol;
    use crate::kb::node_occurrence::{Expr, MatchBranch, NodeOccurrence};
    use crate::span::{SourceId, SourceSpan};

    fn dummy_occ() -> Rc<NodeOccurrence> {
        let span = SourceSpan::new(SourceId::from_raw(0), 0, 0);
        NodeOccurrence::new_expr(Expr::Bottom, span, None)
    }

    fn dummy_frame() -> Frame {
        Frame {
            op: Symbol::from_raw(0),
            expr: dummy_occ(),
            locals: SmallVec::new(),
            requirements: SmallVec::new(),
            type_args: SmallVec::new(),
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
        assert!(matches!(
            err,
            super::super::error::EvalError::DepthExceeded { cap: 2 }
        ));
    }

    /// WI-078 (Phase A step a): the activation stack is `Clone` — the operation
    /// `snapshot_eval_state` (step c) will use to capture a continuation. The
    /// clone must (1) preserve the full frame structure, including the
    /// `MatchDispatch` `AwaitState` whose `MatchBranch` `Clone` was the
    /// derive-chain blocker, and (2) be independent of subsequent mutation of
    /// the live stack (a snapshot must not track later pushes/pops).
    #[test]
    fn clone_snapshots_stack_independently() {
        let span = SourceSpan::new(SourceId::from_raw(0), 0, 0);
        // A frame suspended on a match dispatch (exercises MatchBranch clone).
        let mut waiting = dummy_frame();
        waiting.awaiting = Some(AwaitState::MatchDispatch {
            branches: vec![MatchBranch {
                pattern: dummy_occ(),
                guard: None,
                body: dummy_occ(),
                span,
            }],
            scrutinee_occ: dummy_occ(),
        });
        let mut s = ActivationStack::new();
        s.push(waiting).unwrap();
        s.push(dummy_frame()).unwrap();

        let snap = s.clone(); // continuation capture

        // Later live-stack mutation does not touch the snapshot.
        s.pop();
        assert_eq!(s.depth(), 1);
        assert_eq!(
            snap.depth(),
            2,
            "a snapshot must not track the live stack's frames"
        );

        // The MatchDispatch AwaitState round-tripped through the clone.
        match &snap.frames[0].awaiting {
            Some(AwaitState::MatchDispatch { branches, .. }) => assert_eq!(branches.len(), 1),
            other => panic!("expected a cloned MatchDispatch frame, got {other:?}"),
        }
    }

    /// Proposal 027.4 — THE FLOOR, driven directly. `run()` has no per-run base, so a
    /// nested `run()` (a builtin's `interp.call`, the SLD bridge's `bridge_op_to_eval`)
    /// pushes its frames on top of its caller's; the scan must stop at the frames THIS
    /// run owns, or an inner run answers an outer run's boundary and truncates frames
    /// the host still holds.
    ///
    /// Driven here rather than through a program because no anthill spelling reaches
    /// that shape yet: the operation that re-enters `run()` on a live stack is reached
    /// from the RESOLVER, and a rule body's raise appears in no caller's effect row, so
    /// a typed `reify` cannot be wrapped around it. So this test is the ONLY thing in
    /// the tree that pins the bound: delete `floor` and nothing else goes red, which is
    /// precisely why it is written.
    #[test]
    fn the_boundary_scan_stops_at_the_floor() {
        let boundary = || {
            let mut f = dummy_frame();
            f.awaiting = Some(AwaitState::ReifyBoundary {
                payload: Some(Symbol::from_raw(1)),
            });
            f
        };
        let mut s = ActivationStack::new();
        s.push(boundary()).unwrap(); // 0 — an OUTER run's boundary
        s.push(dummy_frame()).unwrap(); // 1 — the outer run's own frame
        s.push(boundary()).unwrap(); // 2 — this run's boundary
        s.push(dummy_frame()).unwrap(); // 3 — the thunk

        let idx = |v: SmallVec<[(usize, Option<Symbol>); 2]>| -> Vec<usize> {
            v.into_iter().map(|(i, _)| i).collect()
        };
        // A run whose floor is 2 sees only its own.
        assert_eq!(idx(s.reify_boundaries(2)), vec![2]);
        // A run entered ABOVE both must not reach down for one.
        assert_eq!(
            idx(s.reify_boundaries(3)),
            Vec::<usize>::new(),
            "a nested run must not answer its caller's boundary"
        );
        // The outer run owns both, and sees them INNERMOST FIRST — the order the
        // acceptance walk consumes, so a raise the inner one declines reaches the
        // outer one and no other.
        assert_eq!(idx(s.reify_boundaries(0)), vec![2, 0]);
    }

    /// The unwind: everything above the boundary is discarded and the boundary itself
    /// stops awaiting, so the caller delivers `err(payload)` FROM it — the same last
    /// step the success path takes.
    #[test]
    fn unwinding_leaves_the_boundary_on_top_and_answered() {
        let mut s = ActivationStack::new();
        s.push(dummy_frame()).unwrap();
        let mut b = dummy_frame();
        b.awaiting = Some(AwaitState::ReifyBoundary {
            payload: Some(Symbol::from_raw(1)),
        });
        s.push(b).unwrap();
        s.push(dummy_frame()).unwrap();
        s.push(dummy_frame()).unwrap();

        let (idx, _) = s.reify_boundaries(0)[0];
        s.unwind_to_boundary(idx);

        assert_eq!(s.depth(), 2, "every frame above the boundary is discarded");
        assert!(
            s.top().expect("the boundary is now the top").awaiting.is_none(),
            "the boundary is answered, so `deliver` may pop it to its parent"
        );
    }
}

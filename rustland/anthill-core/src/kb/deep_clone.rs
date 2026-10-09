//! WI-20261009-D0SD4 — an INDEPENDENT COPY of a knowledge base.
//!
//! [`KnowledgeBase::deep_clone`] returns a KB that answers what the original answers
//! and shares NO `Rc` with it: every body tree and every `Value` payload is allocated
//! anew. Two reasons, and either alone would be enough.
//!
//! * **A copy that shared body trees would not be independent.** The typer writes its
//!   verdict about a call INTO the call's node, through `&self` (`classification`,
//!   `op_dicts`, `inferred_type`, `lowered_receiver` on
//!   [`NodeKind::Expr`]), and a later `load_all` re-types every operation body already
//!   in the KB (the free-op sweep, `typing/sorts.rs`). Two KBs holding one tree would
//!   each stamp the nodes the other reads.
//! * **A copy that shares no `Rc` may be handed to another thread.** `Rc` is what makes
//!   a `KnowledgeBase` not `Send`. That is how the test suites keep ONE loaded stdlib
//!   per binary and give each test a copy of its own (WI-059); the wrapper that makes
//!   the claim is in `anthill-core/tests/common`, with the one `unsafe` it needs, and
//!   what it rests on is this module being right.
//!
//! # How "shares nothing" is kept true
//!
//! The copy is a struct literal over EVERY field of [`KnowledgeBase`] with no `..`, so
//! a new field does not compile until it is placed here. A field goes one of two ways:
//!
//! * through [`plain`], which is bounded `Clone + Send`. `Send` is the compiler's own
//!   statement that the type holds no `Rc` (and no other thread-bound state), so an
//!   ordinary `clone` of it cannot share one. Adding an `Rc` to such a type turns the
//!   line into a compile error rather than into a shared allocation.
//! * through a copier written here, for the types that do hold an `Rc`. Each is an
//!   exhaustive match or destructuring for the same reason, and each of its leaves
//!   goes through [`plain`] again.
//!
//! What `Send` does not rule out is an `Arc`, and two things ARE shared between a copy
//! and its original through one: a source's text (`SourceRegistry`, an `Arc<str>`), and
//! the subtrees of the discrimination tree (`discrim::SubstTree`, `Arc` children, each
//! side path-copying what it later writes). Both are immutable where shared and counted
//! atomically, so this is sharing neither reason above objects to. The interners
//! (`TermStore`, `SymbolTable`, `SourceRegistry`) are not `Clone` on purpose and are
//! copied by a `duplicate` of their own, written under the same two rules.
//!
//! # Sharing WITHIN the copy is kept
//!
//! A node or a payload the original reaches twice is copied once ([`Copier::shared`],
//! a memo by address). Without it a type value stamped on a thousand nodes would
//! become a thousand copies, and two holders of one node — a body and whatever index
//! names it — would stop seeing each other's stamps, which is the one thing a copy
//! must not change.
//!
//! # What is refused, and what starts empty
//!
//! Not `impl Clone`, because some KBs cannot be copied and the answer for those is an
//! error, not a copy that is quietly missing something ([`DeepCloneError`]).
//!
//! The memo caches whose rows hold an `Rc` (`requires_chain_cache` and its eight
//! siblings, and `resolve_cache`: ten) START EMPTY in the copy. Each memoizes an answer
//! computed from the declarations, each already has an invalidation the load calls
//! (`invalidate_requires_chain_cache`, `invalidate_resolve_cache`), so "empty" is a
//! state every reader meets anyway — and a copier per row type would be ten more
//! places for the claim above to be wrong. A cache whose rows are plain is copied.
//!
//! # Depth
//!
//! The copiers RECURSE over a body tree's and a value's depth, where `Drop for
//! NodeOccurrence` was made iterative because that depth can outrun a thread's stack.
//! So the recursion is given a budget of native stack ([`STACK_BUDGET`]) and a tree
//! that would spend it is REFUSED ([`DeepCloneError::TooDeep`]) instead of aborting
//! the process.

use std::any::{Any, TypeId};
use std::rc::Weak;

use super::node_occurrence::{
    EffectExprNode, Expr, MatchBranch, NodeKind, OccurrenceOrigin, Pattern, TypeChild, TypeNode,
};
use super::op_info::{OpSignature, OperationRecord};
use super::typing::{CallClass, RequiresEntry, ResolvedRequiresNode};
use super::*;
use crate::eval::value::Value;

/// Why a knowledge base could not be copied. Each is state a copy could neither
/// duplicate nor honestly leave out.
///
/// ORDERED, and the order is used: a KB that gives several reasons reports the LEAST
/// of them, so the answer does not follow the iteration order of a `HashMap`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum DeepCloneError {
    /// A value held by the KB is a handle into ONE interpreter's arena — a closure, a
    /// stream, a substitution, a map, a cell, a KB layer. The arena is not part of the
    /// KB, so the copy's handle would name a slot of an arena it does not have.
    ArenaHandle { carrier: &'static str },
    /// A host function registered as a CLOSURE over the embedder's state
    /// (`KnowledgeBase::register_host_fn`).
    DynamicHostFn { key: String },
    /// A mounted extent source or mirror store — a live host backend — or a RECORD of
    /// one (a mount, a profile, a mirror's coverage) with the backend lent out.
    LiveBackend {
        sources: usize,
        mirrors: usize,
        records: usize,
    },
    /// A scoped-KB layer is applied (`execute(loaded(..), q)` in flight). The snapshot
    /// that discards it is the interpreter's, and is not copied with the KB.
    LayerApplied,
    /// An import audit is live on the symbol table (`begin_import_audit`).
    ImportAuditLive,
    /// The KB is in the middle of a load or a search: `field` holds work a pass has
    /// queued, or a depth or a guard a call has raised and not yet lowered. Nothing in
    /// a copy would ever run the other half.
    LoadInFlight { field: &'static str },
    /// A body tree or a value is nested deeper than the copy's stack budget.
    TooDeep,
    /// An occurrence's lowered receiver twin is alive but not owned by the KB — held
    /// by an interpreter's body cache, say — so the copy has no twin to point at.
    ReceiverTwinNotOwned,
}

impl std::fmt::Display for DeepCloneError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DeepCloneError::ArenaHandle { carrier } => write!(
                f,
                "a value in the knowledge base is a {carrier} handle into an interpreter's \
                 arena, which is not part of the knowledge base and cannot be copied with it"
            ),
            DeepCloneError::DynamicHostFn { key } => write!(
                f,
                "host function `{key}` is a closure over the embedder's state, which a copy \
                 of the knowledge base can neither duplicate nor share"
            ),
            DeepCloneError::LiveBackend {
                sources,
                mirrors,
                records,
            } => write!(
                f,
                "the knowledge base has {sources} mounted extent source(s), {mirrors} \
                 mirror store(s) and {records} record(s) of them; a live backend cannot \
                 be copied"
            ),
            DeepCloneError::LayerApplied => write!(
                f,
                "a scoped layer is applied over the knowledge base; the snapshot that \
                 discards it belongs to the interpreter and is not copied"
            ),
            DeepCloneError::ImportAuditLive => {
                write!(f, "an import audit is live on the knowledge base's symbol table")
            }
            DeepCloneError::LoadInFlight { field } => write!(
                f,
                "the knowledge base is in the middle of a load or a search: `{field}` is \
                 not at rest"
            ),
            DeepCloneError::TooDeep => write!(
                f,
                "a body or a value in the knowledge base is nested deeper than a copy \
                 can follow within its stack budget"
            ),
            DeepCloneError::ReceiverTwinNotOwned => write!(
                f,
                "an occurrence's lowered receiver is alive but is not owned by the \
                 knowledge base, so a copy has nothing to point at"
            ),
        }
    }
}

impl std::error::Error for DeepCloneError {}

/// A value with no `Rc` in it, copied by its own `Clone`. THE BOUND IS THE POINT: `Send`
/// is the compiler's statement that `T` holds no `Rc`, so this cannot share one — and a
/// type that grows an `Rc` later stops compiling here instead of starting to share it.
pub(crate) fn plain<T: Clone + Send>(x: &T) -> T {
    x.clone()
}

/// How much native stack the copiers' recursion may spend below where the copy began.
/// A test thread has 2 MiB and the copy starts near its top; this leaves the other
/// half for whatever called it. Measured in ADDRESSES, not levels, so it holds for
/// both builds — a level costs several times more at opt-level 0.
const STACK_BUDGET: usize = 1 << 20;

/// Roughly where the stack is now.
#[inline(never)]
fn stack_mark() -> usize {
    let marker = 0_u8;
    std::ptr::from_ref(&marker) as usize
}

/// The state of one copy: what has been copied already, and what could not be.
pub(crate) struct Copier {
    /// Address of an ORIGINAL `Rc` allocation → its copy, boxed as the `Rc<T>` it is.
    /// The originals are borrowed for the whole copy, so an address names one
    /// allocation throughout; the `TypeId` makes the downcast total rather than
    /// trusted.
    shared: HashMap<(*const (), TypeId), Box<dyn Any>>,
    /// `(copy, ORIGINAL twin)` for every node whose `lowered_receiver` was live. The
    /// twin may not have been copied yet when its holder is, so the slot is re-pointed
    /// at the end ([`Self::finish`]). Holding the original keeps its address taken.
    receivers: Vec<(Rc<NodeOccurrence>, Rc<NodeOccurrence>)>,
    /// The LEAST of the things that could not be copied ([`DeepCloneError`] is
    /// ordered). A copier that meets one returns a placeholder and goes on;
    /// [`Self::finish`] turns it into the error.
    refusal: Option<DeepCloneError>,
    /// [`stack_mark`] where the copy began.
    stack_top: usize,
}

impl Copier {
    fn new() -> Self {
        Copier {
            shared: HashMap::new(),
            receivers: Vec::new(),
            refusal: None,
            stack_top: stack_mark(),
        }
    }

    /// Record that something could not be copied.
    pub(crate) fn refuse(&mut self, why: DeepCloneError) {
        self.refusal = Some(match self.refusal.take() {
            Some(earlier) => earlier.min(why),
            None => why,
        });
    }

    /// Has the recursion spent its budget? Then the caller returns a placeholder, and
    /// the copy is refused.
    fn too_deep(&mut self) -> bool {
        let spent = self.stack_top.abs_diff(stack_mark()) > STACK_BUDGET;
        if spent {
            self.refuse(DeepCloneError::TooDeep);
        }
        spent
    }

    /// Re-point every live `lowered_receiver` at its twin's COPY, and report a refusal.
    ///
    /// A twin the KB does not own — alive only because something outside it holds it,
    /// an interpreter's body cache say — has no copy to point at. The copy would answer
    /// `None` where the original answers a node, so it is REFUSED.
    fn finish(mut self) -> Result<(), DeepCloneError> {
        for (copy, twin) in std::mem::take(&mut self.receivers) {
            match self.shared.get(&Self::key(&twin)) {
                Some(twin_copy) => copy.set_lowered_receiver(Self::downcast(twin_copy)),
                None => self.refuse(DeepCloneError::ReceiverTwinNotOwned),
            }
        }
        match self.refusal.take() {
            Some(why) => Err(why),
            None => Ok(()),
        }
    }

    fn key<T: ?Sized + 'static>(rc: &Rc<T>) -> (*const (), TypeId) {
        (Rc::as_ptr(rc) as *const (), TypeId::of::<Rc<T>>())
    }

    fn downcast<T: ?Sized + 'static>(boxed: &Box<dyn Any>) -> &Rc<T> {
        boxed
            .downcast_ref::<Rc<T>>()
            .expect("a memo row is keyed by the type it holds")
    }

    /// The copy of one `Rc` allocation — made by `build` the first time the original is
    /// met, and the SAME copy every time after. This is what keeps the copy's sharing
    /// the original's (see the module docs).
    fn shared<T: ?Sized + 'static>(
        &mut self,
        rc: &Rc<T>,
        build: impl FnOnce(&mut Self, &T) -> Rc<T>,
    ) -> Rc<T> {
        let key = Self::key(rc);
        if let Some(done) = self.shared.get(&key) {
            return Rc::clone(Self::downcast(done));
        }
        let copy = build(self, rc);
        self.shared.insert(key, Box::new(Rc::clone(&copy)));
        copy
    }

    // ── values ──────────────────────────────────────────────────

    pub(crate) fn value(&mut self, v: &Value) -> Value {
        if self.too_deep() {
            return Value::Unit;
        }
        match v {
            Value::Int(n) => Value::Int(plain(n)),
            Value::BigInt(n) => Value::BigInt(plain(n)),
            Value::Float(x) => Value::Float(plain(x)),
            Value::Bool(b) => Value::Bool(plain(b)),
            Value::Str(s) => Value::Str(plain(s)),
            Value::Unit => Value::Unit,
            Value::Tuple { pos, named } => Value::Tuple {
                pos: self.values(pos),
                named: self.named_values(named),
            },
            Value::Entity {
                functor,
                pos,
                named,
            } => Value::Entity {
                functor: plain(functor),
                pos: self.values(pos),
                named: self.named_values(named),
            },
            Value::OpRef {
                op,
                dict,
                named,
                spread_labels,
                op_reqs,
            } => Value::OpRef {
                op: plain(op),
                dict: dict
                    .as_ref()
                    .map(|d| self.shared(d, |c, d| Rc::new(d.deep_clone_with(c)))),
                named: plain(named),
                spread_labels: spread_labels.as_ref().map(|l| self.symbols(l)),
                op_reqs: op_reqs.as_ref().map(|reqs| {
                    self.shared(reqs, |c, reqs| {
                        reqs.iter()
                            .map(|d| d.as_ref().map(|d| d.deep_clone_with(c)))
                            .collect()
                    })
                }),
            },
            Value::FactRef(r) => Value::FactRef(plain(r)),
            Value::Term { id } => Value::Term { id: plain(id) },
            Value::Var(var) => Value::Var(plain(var)),
            Value::SymbolRef(sym) => Value::SymbolRef(plain(sym)),
            Value::Node(occ) => Value::Node(self.node(occ)),
            Value::Relation { query, columns } => Value::Relation {
                query: self.shared(query, |c, q| Rc::new(c.value(q))),
                columns: self.shared(columns, |_, cols| cols.iter().map(plain).collect()),
            },
            // Handles into ONE interpreter's arenas. See `DeepCloneError::ArenaHandle`.
            Value::Closure(_) => self.arena_handle("closure"),
            Value::Stream(_) => self.arena_handle("stream"),
            Value::Substitution(_) => self.arena_handle("substitution"),
            Value::Map(_) => self.arena_handle("map"),
            Value::Cell(_) => self.arena_handle("cell"),
            Value::Kb(_) => self.arena_handle("knowledge-base layer"),
        }
    }

    fn arena_handle(&mut self, carrier: &'static str) -> Value {
        self.refuse(DeepCloneError::ArenaHandle { carrier });
        Value::Unit
    }

    fn values(&mut self, vs: &Rc<[Value]>) -> Rc<[Value]> {
        self.shared(vs, |c, vs| vs.iter().map(|v| c.value(v)).collect())
    }

    fn named_values(&mut self, vs: &Rc<[(Symbol, Value)]>) -> Rc<[(Symbol, Value)]> {
        self.shared(vs, |c, vs| c.keyed_values(vs))
    }

    pub(crate) fn symbols(&mut self, syms: &Rc<[Symbol]>) -> Rc<[Symbol]> {
        self.shared(syms, |_, syms| syms.iter().map(plain).collect())
    }

    fn value_vec(&mut self, vs: &[Value]) -> Vec<Value> {
        vs.iter().map(|v| self.value(v)).collect()
    }

    /// `(key, value)` rows — named arguments, bindings, type arguments, fields — each
    /// key copied as the plain thing it is and each value by [`Self::value`].
    fn keyed_values<'a, K, C>(&mut self, rows: impl IntoIterator<Item = &'a (K, Value)>) -> C
    where
        K: Clone + Send + 'a,
        C: FromIterator<(K, Value)>,
    {
        rows.into_iter().map(|(key, v)| (plain(key), self.value(v))).collect()
    }

    // ── occurrences ─────────────────────────────────────────────

    /// The copy of one occurrence, its typer stamps with it. RECURSIVE over the tree's
    /// depth, within [`STACK_BUDGET`].
    pub(crate) fn node(&mut self, occ: &Rc<NodeOccurrence>) -> Rc<NodeOccurrence> {
        self.shared(occ, Self::build_node)
    }

    fn build_node(&mut self, occ: &NodeOccurrence) -> Rc<NodeOccurrence> {
        let NodeOccurrence { kind, span, owner } = occ;
        if self.too_deep() {
            return NodeOccurrence::new_expr(Expr::Bottom, plain(span), plain(owner));
        }
        // `Some(Some(twin))` — written and alive; `Some(None)` — written, twin gone.
        let mut receiver: Option<Option<Rc<NodeOccurrence>>> = None;
        let kind = match kind {
            NodeKind::Expr {
                expr,
                origin,
                dot_chain,
                classification,
                op_dicts,
                inferred_type,
                lowered_receiver,
            } => {
                receiver = lowered_receiver.borrow().as_ref().map(Weak::upgrade);
                NodeKind::Expr {
                    expr: self.expr(expr),
                    origin: match origin {
                        OccurrenceOrigin::Source => OccurrenceOrigin::Source,
                        OccurrenceOrigin::Synthesized { from, by } => {
                            OccurrenceOrigin::Synthesized {
                                from: self.node(from),
                                by: plain(by),
                            }
                        }
                    },
                    dot_chain: plain(dot_chain),
                    classification: RefCell::new(
                        classification
                            .borrow()
                            .as_deref()
                            .map(|class| Box::new(self.call_class(class))),
                    ),
                    op_dicts: RefCell::new(plain(&*op_dicts.borrow())),
                    inferred_type: RefCell::new(
                        inferred_type.borrow().as_ref().map(|ty| self.value(ty)),
                    ),
                    // WRITTEN-ness is kept here; the pointer is `Self::finish`'s.
                    lowered_receiver: RefCell::new(receiver.as_ref().map(|_| Weak::new())),
                }
            }
            NodeKind::RuleHead {
                functor,
                pos_args,
                named_args,
            } => NodeKind::RuleHead {
                functor: plain(functor),
                pos_args: plain(pos_args),
                named_args: plain(named_args),
            },
            NodeKind::Pattern { pattern, type_ann } => NodeKind::Pattern {
                pattern: self.pattern(pattern),
                type_ann: type_ann.as_ref().map(|ann| self.node(ann)),
            },
            NodeKind::Type(tn) => NodeKind::Type(self.type_node(tn)),
            NodeKind::EffectExpr(en) => NodeKind::EffectExpr(self.effect_node(en)),
        };
        let copy = Rc::new(NodeOccurrence {
            kind,
            span: plain(span),
            owner: plain(owner),
        });
        if let Some(Some(twin)) = receiver {
            self.receivers.push((Rc::clone(&copy), twin));
        }
        copy
    }

    fn nodes(&mut self, occs: &[Rc<NodeOccurrence>]) -> Vec<Rc<NodeOccurrence>> {
        occs.iter().map(|occ| self.node(occ)).collect()
    }

    fn named_nodes(
        &mut self,
        occs: &[(Symbol, Rc<NodeOccurrence>)],
    ) -> Vec<(Symbol, Rc<NodeOccurrence>)> {
        occs.iter().map(|(name, occ)| (plain(name), self.node(occ))).collect()
    }

    fn expr(&mut self, e: &Expr) -> Expr {
        match e {
            Expr::Apply {
                functor,
                pos_args,
                named_args,
                type_args,
                recv_type,
            } => Expr::Apply {
                functor: plain(functor),
                pos_args: self.nodes(pos_args),
                named_args: self.named_nodes(named_args),
                type_args: self.keyed_values(type_args),
                recv_type: recv_type.as_ref().map(|ty| self.value(ty)),
            },
            Expr::TypeValue {
                head,
                pos_args,
                named_args,
            } => Expr::TypeValue {
                head: plain(head),
                pos_args: self.nodes(pos_args),
                named_args: self.named_nodes(named_args),
            },
            Expr::HoApply { predicate, args } => Expr::HoApply {
                predicate: self.node(predicate),
                args: self.nodes(args),
            },
            Expr::Constructor {
                name,
                pos_args,
                named_args,
                from_projection,
            } => Expr::Constructor {
                name: plain(name),
                pos_args: self.nodes(pos_args),
                named_args: self.named_nodes(named_args),
                from_projection: plain(from_projection),
            },
            Expr::Match {
                scrutinee,
                branches,
            } => Expr::Match {
                scrutinee: self.node(scrutinee),
                branches: branches
                    .iter()
                    .map(|branch| {
                        let MatchBranch {
                            pattern,
                            guard,
                            body,
                            span,
                        } = branch;
                        MatchBranch {
                            pattern: self.node(pattern),
                            guard: guard.as_ref().map(|g| self.node(g)),
                            body: self.node(body),
                            span: plain(span),
                        }
                    })
                    .collect(),
            },
            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => Expr::If {
                condition: self.node(condition),
                then_branch: self.node(then_branch),
                else_branch: self.node(else_branch),
            },
            Expr::Let {
                pattern,
                value,
                body,
            } => Expr::Let {
                pattern: self.node(pattern),
                value: self.node(value),
                body: self.node(body),
            },
            Expr::Lambda { param, body } => Expr::Lambda {
                param: self.node(param),
                body: self.node(body),
            },
            Expr::Proof {
                target,
                strategy,
                using,
                conclude,
                body,
            } => Expr::Proof {
                target: plain(target),
                strategy: plain(strategy),
                using: plain(using),
                conclude: conclude.as_ref().map(|c| self.node(c)),
                body: self.node(body),
            },
            Expr::Instantiation {
                name,
                pos_args,
                named_args,
            } => Expr::Instantiation {
                name: plain(name),
                pos_args: self.nodes(pos_args),
                named_args: self.named_nodes(named_args),
            },
            Expr::DotApply {
                receiver,
                name,
                pos_args,
                named_args,
            } => Expr::DotApply {
                receiver: self.node(receiver),
                name: plain(name),
                pos_args: self.nodes(pos_args),
                named_args: self.named_nodes(named_args),
            },
            Expr::ListLit(items) => Expr::ListLit(self.nodes(items)),
            Expr::SetLit(items) => Expr::SetLit(self.nodes(items)),
            Expr::TupleLit { positional, named } => Expr::TupleLit {
                positional: self.nodes(positional),
                named: self.named_nodes(named),
            },
            Expr::ApplyWithin {
                functor,
                args,
                named_args,
                requirements,
                type_args,
            } => Expr::ApplyWithin {
                functor: plain(functor),
                args: self.nodes(args),
                named_args: self.named_nodes(named_args),
                requirements: self.nodes(requirements),
                type_args: self.keyed_values(type_args),
            },
            Expr::HoApplyWithin {
                predicate,
                args,
                requirements,
            } => Expr::HoApplyWithin {
                predicate: self.node(predicate),
                args: self.nodes(args),
                requirements: self.nodes(requirements),
            },
            Expr::ConstructorWithin {
                name,
                pos_args,
                named_args,
                requirements,
            } => Expr::ConstructorWithin {
                name: plain(name),
                pos_args: self.nodes(pos_args),
                named_args: self.named_nodes(named_args),
                requirements: self.nodes(requirements),
            },
            Expr::LambdaWithin {
                param,
                body,
                requirements,
            } => Expr::LambdaWithin {
                param: self.node(param),
                body: self.node(body),
                requirements: self.nodes(requirements),
            },
            Expr::RequirementAtSort { chain, slot } => Expr::RequirementAtSort {
                chain: self.node(chain),
                slot: plain(slot),
            },
            Expr::Dictionary { impl_sort, subs } => Expr::Dictionary {
                impl_sort: plain(impl_sort),
                subs: self.nodes(subs),
            },
            Expr::VarRef { name } => Expr::VarRef { name: plain(name) },
            Expr::Var(var) => Expr::Var(plain(var)),
            Expr::Const(lit) => Expr::Const(plain(lit)),
            Expr::Spliced(v) => Expr::Spliced(self.value(v)),
            Expr::Ref(sym) => Expr::Ref(plain(sym)),
            Expr::Ident(sym) => Expr::Ident(plain(sym)),
            Expr::Bottom => Expr::Bottom,
        }
    }

    fn pattern(&mut self, p: &Pattern) -> Pattern {
        match p {
            Pattern::Var { name } => Pattern::Var { name: plain(name) },
            Pattern::Wildcard => Pattern::Wildcard,
            Pattern::Literal { value } => Pattern::Literal { value: plain(value) },
            Pattern::Constructor {
                name,
                pos_args,
                named_args,
            } => Pattern::Constructor {
                name: plain(name),
                pos_args: self.nodes(pos_args),
                named_args: self.named_nodes(named_args),
            },
            Pattern::Tuple { positional, labels } => Pattern::Tuple {
                positional: self.nodes(positional),
                labels: plain(labels),
            },
        }
    }

    fn type_child(&mut self, child: &TypeChild) -> TypeChild {
        match child {
            TypeChild::Interned(t) => TypeChild::Interned(plain(t)),
            TypeChild::Node(occ) => TypeChild::Node(self.node(occ)),
        }
    }

    fn type_node(&mut self, tn: &TypeNode) -> TypeNode {
        match tn {
            TypeNode::Var(var) => TypeNode::Var(plain(var)),
            TypeNode::Denoted { value } => TypeNode::Denoted {
                value: self.node(value),
            },
            TypeNode::Parameterized { base, bindings } => TypeNode::Parameterized {
                base: self.type_child(base),
                bindings: bindings
                    .iter()
                    .map(|(name, child)| (plain(name), self.type_child(child)))
                    .collect(),
            },
            TypeNode::EffectsRows { effects_expr } => TypeNode::EffectsRows {
                effects_expr: self.type_child(effects_expr),
            },
            TypeNode::Arrow {
                param,
                result,
                effects,
                arity,
            } => TypeNode::Arrow {
                param: self.type_child(param),
                result: self.type_child(result),
                effects: self.type_child(effects),
                arity: self.type_child(arity),
            },
            TypeNode::NamedTuple { fields } => TypeNode::NamedTuple {
                fields: self.value(fields),
            },
            TypeNode::PolyType {
                binders,
                context,
                body,
            } => TypeNode::PolyType {
                binders: self.value(binders),
                context: self.value(context),
                body: self.type_child(body),
            },
            TypeNode::ExprCarried { value, member } => TypeNode::ExprCarried {
                value: self.type_child(value),
                member: self.type_child(member),
            },
        }
    }

    fn effect_node(&mut self, en: &EffectExprNode) -> EffectExprNode {
        match en {
            EffectExprNode::Merge { left, right } => EffectExprNode::Merge {
                left: self.type_child(left),
                right: self.type_child(right),
            },
            EffectExprNode::Present { label } => EffectExprNode::Present {
                label: self.type_child(label),
            },
            EffectExprNode::Guarded { label, guard } => EffectExprNode::Guarded {
                label: self.type_child(label),
                guard: self.value(guard),
            },
            EffectExprNode::Absent { label } => EffectExprNode::Absent {
                label: self.type_child(label),
            },
            EffectExprNode::Open { tail } => EffectExprNode::Open {
                tail: self.type_child(tail),
            },
            EffectExprNode::EmptyRow => EffectExprNode::EmptyRow,
        }
    }

    // ── what the typer stamps on a call ─────────────────────────

    fn call_class(&mut self, class: &CallClass) -> CallClass {
        match class {
            CallClass::PinNow {
                spec_op_sym,
                impl_op_sym,
            } => CallClass::PinNow {
                spec_op_sym: plain(spec_op_sym),
                impl_op_sym: plain(impl_op_sym),
            },
            CallClass::ConcreteApplyWithin {
                fn_target_sym,
                callee_spec_sort,
                spec_op_sym,
                enclosing_sort,
                resolved_tree,
                frame,
                enclosing_op,
            } => CallClass::ConcreteApplyWithin {
                fn_target_sym: plain(fn_target_sym),
                callee_spec_sort: plain(callee_spec_sort),
                spec_op_sym: plain(spec_op_sym),
                enclosing_sort: plain(enclosing_sort),
                resolved_tree: resolved_tree.as_ref().map(|tree| self.resolved_requires(tree)),
                frame: plain(frame),
                enclosing_op: plain(enclosing_op),
            },
            CallClass::DeferToRequirement {
                spec_op_sym,
                op_short_sym,
                resolved_spec,
                slot,
                proj_path,
                enclosing_sort,
                enclosing_op,
            } => CallClass::DeferToRequirement {
                spec_op_sym: plain(spec_op_sym),
                op_short_sym: plain(op_short_sym),
                resolved_spec: self.requires_entry(resolved_spec),
                slot: plain(slot),
                proj_path: plain(proj_path),
                enclosing_sort: plain(enclosing_sort),
                enclosing_op: plain(enclosing_op),
            },
            CallClass::UnresolvedSpecOp {
                spec_op_sym,
                spec_sort_sym,
                abstract_params,
                span,
                enclosing_sort,
            } => CallClass::UnresolvedSpecOp {
                spec_op_sym: plain(spec_op_sym),
                spec_sort_sym: plain(spec_sort_sym),
                abstract_params: plain(abstract_params),
                span: plain(span),
                enclosing_sort: plain(enclosing_sort),
            },
            CallClass::EtaOpRef {
                dict,
                spread_labels,
            } => CallClass::EtaOpRef {
                dict: plain(dict),
                spread_labels: spread_labels.as_ref().map(|labels| self.symbols(labels)),
            },
        }
    }

    fn resolved_requires(&mut self, node: &ResolvedRequiresNode) -> ResolvedRequiresNode {
        match node {
            ResolvedRequiresNode::Leaf {
                impl_sort,
                spec_sort,
                bindings,
            } => ResolvedRequiresNode::Leaf {
                impl_sort: plain(impl_sort),
                spec_sort: plain(spec_sort),
                bindings: self.keyed_values(bindings),
            },
            ResolvedRequiresNode::Conditional {
                impl_sort,
                spec_sort,
                bindings,
                sub_resolutions,
            } => ResolvedRequiresNode::Conditional {
                impl_sort: plain(impl_sort),
                spec_sort: plain(spec_sort),
                bindings: self.keyed_values(bindings),
                sub_resolutions: sub_resolutions
                    .iter()
                    .map(|sub| self.resolved_requires(sub))
                    .collect(),
            },
            ResolvedRequiresNode::FromScope {
                scope_index,
                spec_sort,
                projection,
            } => ResolvedRequiresNode::FromScope {
                scope_index: plain(scope_index),
                spec_sort: plain(spec_sort),
                projection: plain(projection),
            },
        }
    }

    fn requires_entry(&mut self, entry: &RequiresEntry) -> RequiresEntry {
        let RequiresEntry {
            required_sort,
            spec,
            supply,
        } = entry;
        RequiresEntry {
            required_sort: plain(required_sort),
            spec: self.value(spec),
            supply: plain(supply),
        }
    }

    // ── the KB's own records ────────────────────────────────────

    fn rule_entry(&mut self, rule: &RuleEntry) -> RuleEntry {
        let RuleEntry {
            head,
            body_nodes,
            clause_kind,
            domain,
            meta,
            retracted,
            arity,
            globals,
            shared_arity,
            label,
            type_bounds,
            provider_requirements,
            head_vars,
            head_span,
            rhs_node,
            origin,
        } = rule;
        RuleEntry {
            head: self.value(head),
            body_nodes: self.nodes(body_nodes),
            clause_kind: plain(clause_kind),
            domain: plain(domain),
            meta: plain(meta),
            retracted: plain(retracted),
            arity: plain(arity),
            globals: plain(globals),
            shared_arity: plain(shared_arity),
            label: plain(label),
            type_bounds: plain(type_bounds),
            provider_requirements: plain(provider_requirements),
            head_vars: plain(head_vars),
            head_span: plain(head_span),
            rhs_node: rhs_node.as_ref().map(|rhs| self.node(rhs)),
            origin: plain(origin),
        }
    }

    fn guard(&mut self, guard: &Guard) -> Guard {
        let Guard {
            id,
            query,
            kind,
            trigger_sorts,
            label,
        } = guard;
        Guard {
            id: plain(id),
            query: self.value(query),
            kind: plain(kind),
            trigger_sorts: plain(trigger_sorts),
            label: plain(label),
        }
    }

    fn operation_record(&mut self, record: &OperationRecord) -> OperationRecord {
        let OperationRecord { signature, body } = record;
        OperationRecord {
            signature: signature.as_ref().map(|signature| {
                let OpSignature {
                    params,
                    return_type,
                    effects,
                    type_params,
                    requires,
                    ensures,
                    meta,
                } = signature;
                OpSignature {
                    params: self.keyed_values(params),
                    return_type: self.value(return_type),
                    effects: self.value_vec(effects),
                    type_params: plain(type_params),
                    requires: self.value_vec(requires),
                    ensures: self.value_vec(ensures),
                    meta: plain(meta),
                }
            }),
            body: body.as_ref().map(|body| self.node(body)),
        }
    }

    fn parameterized_site(&mut self, site: &ParameterizedSite) -> ParameterizedSite {
        let ParameterizedSite {
            base,
            bindings,
            span,
        } = site;
        ParameterizedSite {
            base: plain(base),
            bindings: self.keyed_values(bindings),
            span: plain(span),
        }
    }

    fn written_provides_clause(&mut self, clause: &WrittenProvidesClause) -> WrittenProvidesClause {
        let WrittenProvidesClause {
            provider,
            spec,
            spec_view,
            span,
        } = clause;
        WrittenProvidesClause {
            provider: plain(provider),
            spec: plain(spec),
            spec_view: self.value(spec_view),
            span: plain(span),
        }
    }

    /// The loader's host-mapping cache: a `fn` entry is copied, a closure refused
    /// ([`host_fns::HostFn::deep_clone_with`]).
    fn host_op_registrations(
        &mut self,
        cell: &std::cell::OnceCell<Result<Vec<(Symbol, host_fns::HostFn)>, String>>,
    ) -> std::cell::OnceCell<Result<Vec<(Symbol, host_fns::HostFn)>, String>> {
        let copy = std::cell::OnceCell::new();
        if let Some(built) = cell.get() {
            let built = match built {
                Ok(entries) => Ok(entries
                    .iter()
                    .map(|(op, f)| (plain(op), f.deep_clone_with("a mapped operation", self)))
                    .collect()),
                Err(why) => Err(plain(why)),
            };
            // A fresh cell: `set` cannot find it taken.
            let _ = copy.set(built);
        }
        copy
    }
}

impl KnowledgeBase {
    /// WI-20261009-D0SD4 — an independent copy of this knowledge base: it answers what
    /// this one answers, and shares no `Rc` with it. See the module docs
    /// ([`crate::kb::deep_clone`]) for why both halves matter and how the second is
    /// kept true, and [`DeepCloneError`] for the KBs that cannot be copied.
    pub fn deep_clone(&self) -> Result<KnowledgeBase, DeepCloneError> {
        // Everything that can be known without copying is asked first: a KB with one
        // closure registered should not pay for a copy of its term store to be told so.
        if let Some(why) = self.deep_clone_refusal() {
            return Err(why);
        }
        let terms = self.terms.duplicate().ok_or(DeepCloneError::LayerApplied)?;
        let symbols = self.symbols.duplicate().map_err(|busy| match busy {
            crate::intern::SymbolTableBusy::ImportAudit => DeepCloneError::ImportAuditLive,
            crate::intern::SymbolTableBusy::FilePass => DeepCloneError::LoadInFlight {
                field: "the symbol table's asking file",
            },
        })?;
        let mut c = Copier::new();
        let copy = KnowledgeBase {
            terms,
            symbols,
            #[cfg(test)]
            sem_eq_sub_depth: plain(&self.sem_eq_sub_depth),
            rules: self.rules.iter().map(|rule| c.rule_entry(rule)).collect(),
            rules_by_functor: plain(&self.rules_by_functor),
            by_domain: plain(&self.by_domain),
            rules_by_label: plain(&self.rules_by_label),
            loaded_rule_frontier: plain(&self.loaded_rule_frontier),
            bodied_rule_counts: plain(&self.bodied_rule_counts),
            sort_entities: plain(&self.sort_entities),
            entity_parent: plain(&self.entity_parent),
            sort_info: plain(&self.sort_info),
            discrim: plain(&self.discrim),
            fact_dedup: plain(&self.fact_dedup),
            value_fact_dedup: plain(&self.value_fact_dedup),
            synth_rule_memo: plain(&self.synth_rule_memo),
            builtins: plain(&self.builtins),
            entity_fields: plain(&self.entity_fields),
            constructor_symbols: plain(&self.constructor_symbols),
            head_argument_sites: plain(&self.head_argument_sites),
            absence_records: plain(&self.absence_records),
            absence_marker_syms: plain(&self.absence_marker_syms),
            next_var: plain(&self.next_var),
            sort_base_subst: plain(&self.sort_base_subst),
            sort_sort: plain(&self.sort_sort),
            entity_of_sort: plain(&self.entity_of_sort),
            guards: self.guards.iter().map(|guard| c.guard(guard)).collect(),
            guards_by_sort: plain(&self.guards_by_sort),
            term_spans: plain(&self.term_spans),
            functor_spans: plain(&self.functor_spans),
            op_records: self.op_records.iter().map(|(op, record)| (plain(op), c.operation_record(record))).collect(),
            op_decl_sites: plain(&self.op_decl_sites),
            decl_sites: plain(&self.decl_sites),
            scope_text_files: plain(&self.scope_text_files),
            op_capture_params: plain(&self.op_capture_params),
            rule_head_captures: plain(&self.rule_head_captures),
            named_requirement_slots: plain(&self.named_requirement_slots),
            type_param_canonical_var: plain(&self.type_param_canonical_var),
            type_param_canonical_vids: plain(&self.type_param_canonical_vids),
            member_param_heads: plain(&self.member_param_heads),
            domain_params: plain(&self.domain_params),
            sort_domains: plain(&self.sort_domains),
            fill_relations: plain(&self.fill_relations),
            domain_jobs: plain(&self.domain_jobs),
            domain_value_face_declined: plain(&self.domain_value_face_declined),
            sort_domain_declined: plain(&self.sort_domain_declined),
            sort_alias_index: plain(&self.sort_alias_index),
            alias_targets: plain(&self.alias_targets),
            alias_heads: plain(&self.alias_heads),
            aliases_applying: plain(&self.aliases_applying),
            scan_alias_decls: plain(&self.scan_alias_decls),
            provides_index: self.provides_index.as_ref().map(|index| index.deep_clone_with(&mut c)),
            sort_info_index: plain(&self.sort_info_index),
            requires_index: plain(&self.requires_index),
            op_info_index: plain(&self.op_info_index),
            const_types: self.const_types.iter().map(|(name, ty)| (plain(name), c.value(ty))).collect(),
            const_bodies: self.const_bodies.iter().map(|(name, body)| (plain(name), c.node(body))).collect(),
            const_sources: plain(&self.const_sources),
            const_slot_values: plain(&self.const_slot_values),
            has_dot_applies: plain(&self.has_dot_applies),
            simp_gate_cache: plain(&self.simp_gate_cache),
            // ── at rest, or the copy was refused above (`deep_clone_refusal`) ──
            simp_guard_depth: 0,
            spec_as_providers_depth: 0,
            type_var_provider_requirements: plain(&self.type_var_provider_requirements),
            eq_connective_sym: plain(&self.eq_connective_sym),
            unify_connective_sym: plain(&self.unify_connective_sym),
            or_connective_sym: plain(&self.or_connective_sym),
            and_connective_sym: plain(&self.and_connective_sym),
            tuple_literal_sym: plain(&self.tuple_literal_sym),
            unrouted_read_sym: plain(&self.unrouted_read_sym),
            rigid_projection_formations: plain(&self.rigid_projection_formations),
            existential_return_ops: plain(&self.existential_return_ops),
            field_wise_noneq_carriers: plain(&self.field_wise_noneq_carriers),
            partial_transparent_carriers: plain(&self.partial_transparent_carriers),
            conditional_eq_params: plain(&self.conditional_eq_params),
            derived_type_value_carriers: plain(&self.derived_type_value_carriers),
            entity_field_types: self.entity_field_types.iter().map(|(entity, fields)| (plain(entity), c.keyed_values(fields))).collect(),
            parameterized_type_sites: self.parameterized_type_sites.iter().map(|site| c.parameterized_site(site)).collect(),
            written_provides_clauses: self.written_provides_clauses.iter().map(|clause| c.written_provides_clause(clause)).collect(),
            bare_spec_narrowings: plain(&self.bare_spec_narrowings),
            rule_sort_uses: plain(&self.rule_sort_uses),
            resolved_requires_facts: plain(&self.resolved_requires_facts),
            judged_row_binding_clauses: plain(&self.judged_row_binding_clauses),
            unbacked_derived_provisions: plain(&self.unbacked_derived_provisions),
            derived_provision_origin: plain(&self.derived_provision_origin),
            equality_signatures: plain(&self.equality_signatures),
            sources: self.sources.duplicate(),
            // Bare, or the copy was refused above (`ExtentRegistry::deep_clone_refusal`).
            extents: extent::ExtentRegistry::default(),
            host_fns: self.host_fns.deep_clone_with(&mut c),
            dispatch_rewrites: plain(&self.dispatch_rewrites),
            unsuppliable_requirements: plain(&self.unsuppliable_requirements),
            pending_citation_routes: Vec::new(),
            // ── memo caches whose rows hold an `Rc` START EMPTY — see the module docs.
            requires_chain_cache: RefCell::new(HashMap::new()),
            requires_tree_cache: RefCell::new(HashMap::new()),
            synth_req_names_cache: RefCell::new(HashMap::new()),
            op_requires_chain_cache: RefCell::new(HashMap::new()),
            synth_op_req_names_cache: RefCell::new(HashMap::new()),
            op_dict_chain_cache: RefCell::new(HashMap::new()),
            op_frame_names_cache: RefCell::new(HashMap::new()),
            provider_dict_chain_cache: RefCell::new(HashMap::new()),
            provision_layout_key_cache: plain(&self.provision_layout_key_cache),
            provision_member_cache: plain(&self.provision_member_cache),
            sort_param_pairs_cache: RefCell::new(HashMap::new()),
            spec_carrier_param_cache: plain(&self.spec_carrier_param_cache),
            spec_self_representing_cache: plain(&self.spec_self_representing_cache),
            witness_admissibility_in_flight: RefCell::new(HashSet::new()),
            resolve_cache: RefCell::new(HashMap::new()),
            sort_ops: plain(&self.sort_ops),
            host_mapped_ops: plain(&self.host_mapped_ops),
            interpreter_mapped_ops: plain(&self.interpreter_mapped_ops),
            host_op_mappings: plain(&self.host_op_mappings),
            host_op_registrations: c.host_op_registrations(&self.host_op_registrations),
            host_const_mappings: plain(&self.host_const_mappings),
            default_providers: plain(&self.default_providers),
            provides_clause_seen: plain(&self.provides_clause_seen),
            provides_clause_counts: self.provides_clause_counts.iter().map(|(key, clauses)| (plain(key), clauses.iter().map(|clause| c.value_vec(clause)).collect())).collect(),
        };
        c.finish()?;
        Ok(copy)
    }

    /// What makes this KB uncopyable and can be read off it without copying anything:
    /// state a call has raised and not yet lowered, a closure host function, a host
    /// backend. The least of them, by [`DeepCloneError`]'s order.
    fn deep_clone_refusal(&self) -> Option<DeepCloneError> {
        // In-flight state, each ZERO OR EMPTY outside the call that raises it
        // (`kb/layer.rs` classifies the first three so). A copy would carry the raised
        // half and never run the other: a depth that stays up, a guard that never
        // comes out, a queue nothing drains.
        let in_flight = [
            ("simp_guard_depth", self.simp_guard_depth != 0),
            ("spec_as_providers_depth", self.spec_as_providers_depth != 0),
            (
                "witness_admissibility_in_flight",
                !self.witness_admissibility_in_flight.borrow().is_empty(),
            ),
            // Queued by one typer pass and drained by the same pass (`typing/relation.rs`).
            ("pending_citation_routes", !self.pending_citation_routes.is_empty()),
        ];
        let in_flight = in_flight
            .into_iter()
            .filter(|(_, raised)| *raised)
            .map(|(field, _)| DeepCloneError::LoadInFlight { field });
        let closure = self
            .host_fns
            .first_closure()
            .map(|key| DeepCloneError::DynamicHostFn { key: key.to_string() });
        in_flight
            .chain(closure)
            .chain(self.extents.deep_clone_refusal())
            .min()
    }
}

#[cfg(test)]
mod tests {
    //! The controls. MEASURED 2026-10-09: each back-out below was made alone and the
    //! rows run against it; every row passes with none of them.
    //!
    //! | back-out | fails |
    //! |---|---|
    //! | `operation_record` shares the body (`body.clone()`) | `holds_nothing`, `stamps` |
    //! | `rule_entry` shares the body nodes | `holds_nothing` |
    //! | `node` keeps the original's `inferred_type` | `holds_nothing` |
    //! | `value` shares an entity's `pos` payload, or its `named` one | `holds_nothing`, `every_payload` |
    //! | `value` shares a `Relation`'s query or columns, an `OpRef`'s dictionary, labels or requirements — five, one at a time | `every_payload` |
    //! | `shared` does not memoize | `holds_nothing`, `stamps` |
    //! | `node` drops the `classification` | `stamps` |
    //! | `finish` does not re-point the receiver twins | `stamps` |
    //! | a pinned store is copied | `refused` |
    //! | the stack budget is not read | `too_deep` — by ABORTING the test binary |
    //!
    //! A row not named beside a back-out passes with it, by design: a row reads one
    //! thing.
    //!
    //! NOT UNDER A ROW, and so resting on the two rules of the module docs alone:
    //! `ProvidesIndex::deep_clone_with` (its `witness_carriers` rows go through
    //! [`Copier::symbols`], which IS under one) and the `resolved_requires` /
    //! `requires_entry` arms of a call's classification.

    use super::super::node_occurrence::{for_each_child, for_each_pattern_child};
    use super::*;
    use crate::kb::test_support::load_stdlib;

    /// The occurrences a KB's operation, rule and constant bodies start from.
    fn roots(kb: &KnowledgeBase) -> Vec<&Rc<NodeOccurrence>> {
        let mut roots: Vec<&Rc<NodeOccurrence>> = Vec::new();
        let mut ops: Vec<_> = kb.op_records.iter().collect();
        ops.sort_by_key(|(op, _)| op.index());
        roots.extend(ops.into_iter().filter_map(|(_, record)| record.body.as_ref()));
        for rule in &kb.rules {
            roots.extend(rule.body_nodes.iter());
            roots.extend(rule.rhs_node.as_ref());
        }
        let mut consts: Vec<_> = kb.const_bodies.iter().collect();
        consts.sort_by_key(|(name, _)| name.index());
        roots.extend(consts.into_iter().map(|(_, body)| body));
        roots
    }

    /// The children THIS walk knows of. NOT THE COPIER'S WALK, on purpose: it is the
    /// crate's own child visitors, so a child the copier forgot to copy is still
    /// found here.
    fn children(occ: &Rc<NodeOccurrence>) -> Vec<Rc<NodeOccurrence>> {
        let mut out = Vec::new();
        out.extend(occ.synthesized_from().cloned());
        // A type that is not ground is itself an occurrence (`Value::Node`).
        if let Some(Value::Node(ty)) = occ.inferred_type() {
            out.push(ty);
        }
        if let Some(expr) = occ.as_expr() {
            for_each_child(expr, |child| out.push(Rc::clone(child)));
        } else if occ.as_pattern().is_some() {
            for_each_pattern_child(occ, |child| out.push(Rc::clone(child)));
        }
        out
    }

    /// Every occurrence the bodies reach, by address, each held WEAKLY.
    fn occurrences(kb: &KnowledgeBase) -> HashMap<*const NodeOccurrence, Weak<NodeOccurrence>> {
        let mut seen = HashMap::new();
        let mut todo: Vec<Rc<NodeOccurrence>> = roots(kb).into_iter().cloned().collect();
        while let Some(occ) = todo.pop() {
            if seen.insert(Rc::as_ptr(&occ), Rc::downgrade(&occ)).is_none() {
                todo.extend(children(&occ));
            }
        }
        seen
    }

    /// The positional `Rc` payloads of a value, held weakly. (Every OTHER payload a
    /// value can carry is `every_payload_of_a_value_is_made_anew`'s.)
    fn payloads(v: &Value, out: &mut Vec<Weak<[Value]>>) {
        if let Value::Tuple { pos, named } | Value::Entity { pos, named, .. } = v {
            out.push(Rc::downgrade(pos));
            pos.iter().for_each(|v| payloads(v, out));
            named.iter().for_each(|(_, v)| payloads(v, out));
        }
    }

    /// The payloads of the values a KB holds outside its bodies — clause heads, guard
    /// queries, what it records about operations and constants — and of the types
    /// stamped on its occurrences.
    fn value_payloads(kb: &KnowledgeBase) -> Vec<Weak<[Value]>> {
        let mut out = Vec::new();
        kb.rules.iter().for_each(|rule| payloads(&rule.head, &mut out));
        kb.guards.iter().for_each(|guard| payloads(&guard.query, &mut out));
        for fields in kb.entity_field_types.values() {
            fields.iter().for_each(|(_, ty)| payloads(ty, &mut out));
        }
        for record in kb.op_records.values() {
            if let Some(signature) = &record.signature {
                signature.params.iter().for_each(|(_, ty)| payloads(ty, &mut out));
                payloads(&signature.return_type, &mut out);
            }
        }
        kb.const_types.values().for_each(|ty| payloads(ty, &mut out));
        for occ in occurrences(kb).values().filter_map(Weak::upgrade) {
            if let Some(ty) = occ.inferred_type() {
                payloads(&ty, &mut out);
            }
        }
        out
    }

    /// The same position in two KBs' bodies, walked in step.
    fn in_step(a: &KnowledgeBase, b: &KnowledgeBase) -> Vec<(Rc<NodeOccurrence>, Rc<NodeOccurrence>)> {
        let (ra, rb) = (roots(a), roots(b));
        assert_eq!(ra.len(), rb.len(), "the two KBs have the same bodies");
        let mut todo: Vec<_> = ra.into_iter().cloned().zip(rb.into_iter().cloned()).collect();
        let mut seen = HashSet::new();
        let mut pairs = Vec::new();
        while let Some((x, y)) = todo.pop() {
            if !seen.insert(Rc::as_ptr(&x)) {
                continue;
            }
            let (cx, cy) = (children(&x), children(&y));
            assert_eq!(cx.len(), cy.len(), "a copied occurrence has its original's children");
            todo.extend(cx.into_iter().zip(cy));
            pairs.push((x, y));
        }
        pairs
    }

    /// THE CLAIM THE `unsafe impl Send` IN `tests/common` RESTS ON: the copy holds no
    /// `Rc` of the original's.
    ///
    /// Read two ways. While both live, no occurrence of the copy is at an address of
    /// the original's. And once the original is dropped, every occurrence and every
    /// value payload it held is FREED — which a copy sharing one, by any path, this
    /// walk's or not, would prevent.
    ///
    /// The back-outs this fails on are listed at the end of the module.
    #[test]
    fn the_copy_holds_nothing_of_the_original() {
        let original = load_stdlib(None);
        let held = occurrences(&original);
        let held_payloads = value_payloads(&original);
        assert!(
            held.len() > 1_000 && held_payloads.len() > 100,
            "the walk has to find the stdlib's bodies and values to say anything: \
             {} occurrences, {} payloads",
            held.len(),
            held_payloads.len()
        );

        let copy = original.deep_clone().expect("a loaded stdlib copies");
        let copied = occurrences(&copy);
        assert_eq!(
            copied.len(),
            held.len(),
            "the copy reaches as many distinct occurrences as the original: what was \
             shared within the original is shared within the copy, and nothing is lost"
        );
        let shared = copied.keys().filter(|addr| held.contains_key(*addr)).count();
        assert_eq!(shared, 0, "an occurrence of the copy IS one of the original's");

        drop(original);
        let alive = held.values().filter(|w| w.strong_count() > 0).count();
        assert_eq!(alive, 0, "occurrences of the dropped original are still held");
        let alive = held_payloads.iter().filter(|w| w.strong_count() > 0).count();
        assert_eq!(alive, 0, "value payloads of the dropped original are still held");
        // And the copy is whole without it.
        assert_eq!(occurrences(&copy).len(), copied.len());
    }

    /// The typer's stamps come across, and from then on each KB's are its own.
    ///
    /// The first half fails when `node` drops a stamp or leaves a receiver twin
    /// un-pointed; the second, a stamp written on one not reaching the other, when a
    /// body tree is shared. The module's table has each.
    #[test]
    fn the_stamps_are_copied_and_then_independent() {
        let original = load_stdlib(None);
        let copy = original.deep_clone().expect("a loaded stdlib copies");
        let pairs = in_step(&original, &copy);

        let (mut classified, mut typed, mut received) = (0, 0, 0);
        for (a, b) in &pairs {
            assert_eq!(a.classification_is_none(), b.classification_is_none());
            assert_eq!(a.apply_dispatch(), b.apply_dispatch());
            assert_eq!(a.op_dicts(), b.op_dicts());
            assert_eq!(a.inferred_type().is_some(), b.inferred_type().is_some());
            classified += usize::from(!a.classification_is_none());
            typed += usize::from(a.inferred_type().is_some());
            // A live twin of the original is a live twin of the COPY's, in the copy.
            match (a.lowered_receiver(), b.lowered_receiver()) {
                (Some(twin_a), Some(twin_b)) => {
                    received += 1;
                    assert!(!Rc::ptr_eq(&twin_a, &twin_b), "the copy points into the original");
                    assert_eq!(Rc::ptr_eq(&twin_a, a), Rc::ptr_eq(&twin_b, b));
                }
                (None, None) => {}
                (a, b) => panic!("a receiver twin is live on one side only: {a:?} / {b:?}"),
            }
        }
        assert!(
            classified > 50 && typed > 1_000 && received > 0,
            "the stdlib has to carry stamps for this to compare any: {classified} \
             classified calls, {typed} typed occurrences, {received} receiver twins"
        );

        let (a, b) = pairs
            .iter()
            .find(|(a, _)| a.as_expr().is_some() && a.inferred_type().is_some())
            .expect("a typed expression");
        let before = format!("{:?}", a.inferred_type());
        b.set_inferred_type(Value::Str("stamped on the copy".to_string()));
        b.set_op_dicts(smallvec::smallvec![None, None, None]);
        assert_eq!(format!("{:?}", a.inferred_type()), before, "the original read the copy's stamp");
        assert_ne!(a.op_dicts().len(), 3, "the original read the copy's dictionaries");
        a.set_inferred_type(Value::Str("stamped on the original".to_string()));
        assert!(
            matches!(b.inferred_type(), Some(Value::Str(s)) if s == "stamped on the copy"),
            "the copy read the original's stamp"
        );
    }

    /// What a copy could neither duplicate nor honestly leave out is an error.
    ///
    /// Fails, a refusal at a time, when its check is removed: the copy is then `Ok`
    /// (measured for the pinned store). `LiveBackend` needs a host backend to build
    /// and is driven from `wi_d0sd4_deep_clone_test` — a mounted SOURCE; a mirror
    /// store, and a record left behind by a lent-out one, are not driven anywhere.
    /// Nor are `LoadInFlight`'s `pending_citation_routes` (its record is private to
    /// `typing/relation.rs`) and asking file, nor `ReceiverTwinNotOwned`.
    #[test]
    fn what_cannot_be_copied_is_refused() {
        assert!(KnowledgeBase::new().deep_clone().is_ok(), "the control: an empty KB copies");

        let mut layered = KnowledgeBase::new();
        layered.terms.pin();
        assert_eq!(layered.deep_clone().err(), Some(DeepCloneError::LayerApplied));

        let audited = KnowledgeBase::new();
        audited.begin_import_audit();
        assert_eq!(audited.deep_clone().err(), Some(DeepCloneError::ImportAuditLive));

        let mut embedded = KnowledgeBase::new();
        embedded
            .register_host_fn("test.d0sd4.closure", 0, |_, _| Ok(Value::Unit))
            .expect("a fresh KB takes a host function");
        assert_eq!(
            embedded.deep_clone().err(),
            Some(DeepCloneError::DynamicHostFn {
                key: "test.d0sd4.closure".to_string()
            })
        );

        // State a call raised and has not lowered. Two at once report the LEAST, so
        // the answer is the same whatever order they were found in.
        let mut searching = KnowledgeBase::new();
        searching.spec_as_providers_depth = 1;
        assert_eq!(
            searching.deep_clone().err(),
            Some(DeepCloneError::LoadInFlight {
                field: "spec_as_providers_depth"
            })
        );
        searching.simp_guard_depth = 2;
        assert_eq!(
            searching.deep_clone().err(),
            Some(DeepCloneError::LoadInFlight {
                field: "simp_guard_depth"
            })
        );

        // A value that is a slot of ONE interpreter's arena, held by the KB.
        let mut holding = KnowledgeBase::new();
        let name = holding.intern("test.d0sd4.held");
        let cell = crate::eval::cell_arena::CellArenaRef::new().alloc(Value::Unit);
        holding.const_types.insert(name, Value::Cell(cell));
        assert_eq!(
            holding.deep_clone().err(),
            Some(DeepCloneError::ArenaHandle { carrier: "cell" })
        );
    }

    /// Every `Rc` a `Value` can carry is made anew by [`Copier::value`]: the original
    /// is dropped, and nothing it held is still alive.
    ///
    /// The stdlib's KB does not hold every carrier (no `OpRef`, no `Relation`), so the
    /// values are built here. FAILS on each of the seven payload-sharing back-outs in
    /// the module's table, one at a time.
    #[test]
    fn every_payload_of_a_value_is_made_anew() {
        use crate::eval::dictionary::Dictionary;

        let mut kb = KnowledgeBase::new();
        let name = kb.intern("test.d0sd4.name");
        let mut alive: Vec<Box<dyn Fn() -> bool>> = Vec::new();
        // Hand back `rc`, having noted how to ask later whether it is still held.
        fn watched<T: ?Sized + 'static>(alive: &mut Vec<Box<dyn Fn() -> bool>>, rc: Rc<T>) -> Rc<T> {
            let weak = Rc::downgrade(&rc);
            alive.push(Box::new(move || weak.strong_count() > 0));
            rc
        }

        let pos: Rc<[Value]> = watched(&mut alive, [Value::Int(1)].into());
        let named: Rc<[(Symbol, Value)]> =
            watched(&mut alive, [(name, Value::Str("x".to_string()))].into());
        let tuple = Value::Tuple { pos, named };
        let dict = watched(&mut alive, Rc::new(Dictionary::wrapping_for_test(tuple.clone())));
        let op_reqs: Rc<[Option<Dictionary>]> = watched(
            &mut alive,
            [None, Some(Dictionary::wrapping_for_test(Value::Int(2)))].into(),
        );
        let op_ref = Value::OpRef {
            op: name,
            dict: Some(dict),
            named: Some(name),
            spread_labels: Some(watched(&mut alive, [name].into())),
            op_reqs: Some(op_reqs),
        };
        let relation = Value::Relation {
            query: watched(&mut alive, Rc::new(tuple.clone())),
            columns: watched(&mut alive, Vec::new().into()),
        };
        let original = Value::Entity {
            functor: name,
            pos: watched(&mut alive, [tuple, op_ref, relation].into()),
            named: watched(&mut alive, Vec::new().into()),
        };
        assert_eq!(alive.len(), 9, "one watch for each `Rc` built above");

        let shown = format!("{original:?}");
        let copy = Copier::new().value(&original);
        assert_eq!(format!("{copy:?}"), shown, "the copy is the value it was copied from");
        drop(original);
        let held = alive.iter().filter(|still_held| still_held()).count();
        assert_eq!(held, 0, "the copy holds payloads of the dropped original");
        assert_eq!(format!("{copy:?}"), shown, "and is whole without it");
    }

    /// A body nested deeper than the copy's stack budget is REFUSED, where a recursion
    /// with no budget would abort the process. The chain is 400 000 lambdas deep —
    /// built and dropped in loops, as `Drop for NodeOccurrence` allows.
    ///
    /// FAILS, by taking the whole test binary down with a stack overflow, when
    /// `too_deep` does not read the budget (`let spent = false`).
    #[test]
    fn a_body_deeper_than_the_stack_budget_is_refused() {
        let span = crate::kb::node_occurrence::empty_span();
        let mut kb = KnowledgeBase::new();
        let name = kb.intern("test.d0sd4.deep");
        let mut body = NodeOccurrence::new_expr(Expr::Bottom, span, None);
        assert!(
            {
                kb.const_bodies.insert(name, Rc::clone(&body));
                kb.deep_clone().is_ok()
            },
            "the control: a shallow body copies"
        );
        for _ in 0..400_000 {
            let param = NodeOccurrence::new_expr(Expr::Bottom, span, None);
            body = NodeOccurrence::new_expr(Expr::Lambda { param, body }, span, None);
        }
        kb.const_bodies.insert(name, body);
        assert_eq!(kb.deep_clone().err(), Some(DeepCloneError::TooDeep));
    }
}

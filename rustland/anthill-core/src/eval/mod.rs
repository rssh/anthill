//! Tree-walking interpreter for anthill expression bodies. Proposal 026.
//!
//! Supports: literals, variables, `if`, `let`, operation call, pattern
//! match, lambda + closures, list / tuple literals. Streams and effect
//! handlers are deferred.

pub mod builtins;
pub mod cell_arena;
pub mod closure;
pub mod effects;
pub mod error;
pub mod eval;
pub mod frame;
pub mod map_arena;
pub mod pattern;
pub mod requirement_arena;
pub mod stream;
pub mod subst_arena;
pub mod value;

use std::collections::HashMap;

use crate::intern::Symbol;
use crate::kb::KnowledgeBase;
use crate::persistence::Store;

pub use error::EvalError;
pub use frame::{ActivationStack, Frame};
pub use value::Value;

use cell_arena::CellArenaRef;
use closure::ClosureArenaRef;
use effects::EffectRegistry;
use map_arena::MapArenaRef;
use requirement_arena::RequirementArenaRef;
use stream::StreamArenaRef;

/// Runtime resource limits. Each cap is optional so different embeddings
/// can trade safety against throughput independently.
///
/// - `depth_cap` bounds the activation stack. Non-tail recursion needs
///   O(n) frames and will trip this; tail recursion (TCO) stays O(1) and
///   is unaffected.
/// - `step_cap` bounds the total number of `step()` iterations, i.e.
///   wall-time work. TCO turns `loop() = loop()` into a constant-depth
///   infinite loop that `depth_cap` alone can't catch — only `step_cap`
///   can. Off by default so ordinary batch evaluation isn't capped.
#[derive(Clone, Copy, Debug)]
pub struct EvalConfig {
    pub depth_cap: Option<usize>,
    pub step_cap: Option<u64>,
}

impl Default for EvalConfig {
    fn default() -> Self {
        Self {
            depth_cap: Some(1_000_000),
            step_cap: None,
        }
    }
}

impl EvalConfig {
    pub fn unbounded() -> Self {
        Self { depth_cap: None, step_cap: None }
    }
}

/// Rust-side builtin: takes the interpreter and evaluated arg `Value`s,
/// returns a `Value` or an error. Mirrors `kb::resolve::builtins` in shape.
pub type BuiltinFn =
    std::sync::Arc<dyn Fn(&mut Interpreter, &[Value]) -> Result<Value, EvalError>>;

/// Cached `Symbol`s for the reflect expression / pattern entities. Populated
/// at `Interpreter::new` via `kb.try_resolve_symbol`. An entry stays `None`
/// when the corresponding stdlib entity hasn't been loaded — the evaluator
/// surfaces a clear "unhandled functor" error instead of misbehaving.
#[derive(Default, Debug)]
pub(crate) struct ReflectSymbols {
    // Expression entities
    pub int_lit: Option<Symbol>,
    pub float_lit: Option<Symbol>,
    pub bigint_lit: Option<Symbol>,
    pub string_lit: Option<Symbol>,
    pub bool_lit: Option<Symbol>,
    pub var_ref: Option<Symbol>,
    pub apply: Option<Symbol>,
    pub if_expr: Option<Symbol>,
    pub let_expr: Option<Symbol>,
    pub match_expr: Option<Symbol>,
    pub lambda: Option<Symbol>,
    pub constructor: Option<Symbol>,
    // WI-222 / WI-223 — requirement-aware IR variants and primitives.
    // Resolved if `reflect.anthill` declares them; remain `None`
    // otherwise so older stdlibs surface a clean "unhandled functor"
    // error rather than misbehaving. The three remaining `_within`
    // fields are reserved for higher-order / constructor / lambda
    // dispatch wiring.
    pub apply_within: Option<Symbol>,
    #[allow(dead_code)] pub ho_apply_within: Option<Symbol>,
    #[allow(dead_code)] pub constructor_within: Option<Symbol>,
    #[allow(dead_code)] pub lambda_within: Option<Symbol>,
    pub requirement_at_current: Option<Symbol>,
    pub requirement_at_sort: Option<Symbol>,
    pub construct_requirement: Option<Symbol>,

    // Pattern entities
    pub var_pattern: Option<Symbol>,
    pub wildcard: Option<Symbol>,
    pub literal_pattern: Option<Symbol>,
    pub constructor_pattern: Option<Symbol>,
    pub tuple_pattern: Option<Symbol>,

    // Collection / list constructors
    pub list_literal: Option<Symbol>,
    pub tuple_literal: Option<Symbol>,
    pub set_literal: Option<Symbol>,
    pub cons: Option<Symbol>,
    pub nil: Option<Symbol>,
}

impl ReflectSymbols {
    fn resolve(kb: &KnowledgeBase) -> Self {
        let r = |qn: &str| kb.try_resolve_symbol(qn);
        Self {
            int_lit: r("anthill.reflect.Expr.int_lit"),
            float_lit: r("anthill.reflect.Expr.float_lit"),
            bigint_lit: r("anthill.reflect.Expr.bigint_lit"),
            string_lit: r("anthill.reflect.Expr.string_lit"),
            bool_lit: r("anthill.reflect.Expr.bool_lit"),
            var_ref: r("anthill.reflect.Expr.var_ref"),
            apply: r("anthill.reflect.Expr.apply"),
            if_expr: r("anthill.reflect.Expr.if_expr"),
            let_expr: r("anthill.reflect.Expr.let_expr"),
            match_expr: r("anthill.reflect.Expr.match_expr"),
            lambda: r("anthill.reflect.Expr.lambda"),
            constructor: r("anthill.reflect.Expr.constructor"),
            apply_within: r("anthill.reflect.Expr.apply_within"),
            ho_apply_within: r("anthill.reflect.Expr.ho_apply_within"),
            constructor_within: r("anthill.reflect.Expr.constructor_within"),
            lambda_within: r("anthill.reflect.Expr.lambda_within"),
            requirement_at_current: r("anthill.reflect.Expr.requirement_at_current"),
            requirement_at_sort: r("anthill.reflect.Expr.requirement_at_sort"),
            construct_requirement: r("anthill.reflect.Expr.construct_requirement"),

            var_pattern: r("anthill.reflect.Pattern.var_pattern"),
            wildcard: r("anthill.reflect.Pattern.wildcard"),
            literal_pattern: r("anthill.reflect.Pattern.literal_pattern"),
            constructor_pattern: r("anthill.reflect.Pattern.constructor_pattern"),
            tuple_pattern: r("anthill.reflect.Pattern.tuple_pattern"),

            list_literal: r("anthill.reflect.ListLiteral"),
            tuple_literal: r("anthill.reflect.TupleLiteral"),
            set_literal: r("anthill.reflect.SetLiteral"),
            cons: r("anthill.prelude.List.cons"),
            nil: r("anthill.prelude.List.nil"),
        }
    }
}

/// Cached `Symbol`s for common named-arg field keys. Resolved once at
/// `Interpreter::new` via `kb.intern` so per-step lookups compare `Symbol`s
/// instead of scanning strings.
#[derive(Debug)]
#[allow(dead_code)]  // params/type_name/guard are reserved for future arms
pub(crate) struct FieldSymbols {
    pub value: Symbol,
    pub name: Symbol,
    pub cond: Symbol,
    pub then_branch: Symbol,
    pub else_branch: Symbol,
    pub pattern: Symbol,
    pub body: Symbol,
    pub fn_: Symbol,
    pub args: Symbol,
    pub params: Symbol,
    pub type_name: Symbol,
    pub scrutinee: Symbol,
    pub branches: Symbol,
    pub guard: Symbol,
    pub elements: Symbol,
    pub param: Symbol,
    pub head: Symbol,
    pub tail: Symbol,
    // WI-222 / WI-223 — requirement IR field keys.
    pub slot: Symbol,
    pub op: Symbol,
    pub chain: Symbol,
    pub impl_functor: Symbol,
    pub requirements: Symbol,
    pub predicate: Symbol,
}

impl FieldSymbols {
    fn resolve(kb: &mut KnowledgeBase) -> Self {
        Self {
            value: kb.intern("value"),
            name: kb.intern("name"),
            cond: kb.intern("cond"),
            then_branch: kb.intern("then_branch"),
            else_branch: kb.intern("else_branch"),
            pattern: kb.intern("pattern"),
            body: kb.intern("body"),
            fn_: kb.intern("fn"),
            args: kb.intern("args"),
            params: kb.intern("params"),
            type_name: kb.intern("type_name"),
            scrutinee: kb.intern("scrutinee"),
            branches: kb.intern("branches"),
            guard: kb.intern("guard"),
            elements: kb.intern("elements"),
            param: kb.intern("param"),
            head: kb.intern("head"),
            tail: kb.intern("tail"),
            slot: kb.intern("slot"),
            op: kb.intern("op"),
            chain: kb.intern("chain"),
            impl_functor: kb.intern("impl_functor"),
            requirements: kb.intern("requirements"),
            predicate: kb.intern("predicate"),
        }
    }
}

/// Top-level interpreter state. Owns the KB so builtins and effect handlers
/// can mutate it; host code takes it back via `Interpreter::into_kb()` when
/// evaluation is done.
pub struct Interpreter {
    pub(crate) kb: KnowledgeBase,
    pub(crate) stack: ActivationStack,
    pub(crate) builtins: HashMap<Symbol, BuiltinFn>,
    pub(crate) reflect: ReflectSymbols,
    pub(crate) fields: FieldSymbols,
    pub(crate) closures: ClosureArenaRef,
    pub(crate) streams: StreamArenaRef,
    pub(crate) substs: subst_arena::SubstArenaRef,
    pub(crate) maps: MapArenaRef,
    pub(crate) cells: CellArenaRef,
    pub(crate) requirements: RequirementArenaRef,
    pub(crate) effect_handlers: EffectRegistry,
    /// Registered persistence backends (proposal 007). Keyed by the
    /// canonical printed form of the store's `Value::Entity` so anthill
    /// code referencing the same shape (e.g. `FileStore(root: "x",
    /// convention: Flat)`) routes to the same instance across calls.
    /// The shim populates this before invoking `main` (see
    /// `Self::register_store`); persistence builtins look entries up.
    pub(crate) store_registry: HashMap<String, Box<dyn Store>>,
    pub(crate) config: EvalConfig,
    /// Monotonically increasing step counter, reset on each `call()`.
    /// `run()` increments it once per `step()` and compares against
    /// `config.step_cap`. Not a permanent counter — after a call returns
    /// the host can inspect and reset via `config_mut()`.
    pub(crate) step_count: u64,
}

impl Interpreter {
    pub fn new(kb: KnowledgeBase) -> Self {
        Self::with_config(kb, EvalConfig::default())
    }

    pub fn with_config(mut kb: KnowledgeBase, config: EvalConfig) -> Self {
        let reflect = ReflectSymbols::resolve(&kb);
        let fields = FieldSymbols::resolve(&mut kb);
        let stack = match config.depth_cap {
            Some(cap) => ActivationStack::with_cap(cap),
            None => ActivationStack::with_cap(usize::MAX),
        };
        Self {
            kb,
            stack,
            builtins: HashMap::new(),
            reflect,
            fields,
            closures: ClosureArenaRef::new(),
            streams: StreamArenaRef::new(),
            substs: subst_arena::SubstArenaRef::new(),
            maps: MapArenaRef::new(),
            cells: CellArenaRef::new(),
            requirements: RequirementArenaRef::new(),
            effect_handlers: EffectRegistry::new(),
            store_registry: HashMap::new(),
            config,
            step_count: 0,
        }
    }

    pub fn config(&self) -> &EvalConfig { &self.config }

    pub fn config_mut(&mut self) -> &mut EvalConfig { &mut self.config }

    pub fn kb(&self) -> &KnowledgeBase { &self.kb }
    pub fn kb_mut(&mut self) -> &mut KnowledgeBase { &mut self.kb }
    pub fn into_kb(self) -> KnowledgeBase { self.kb }

    /// Number of live closure-arena slots. Exposed so refcount/GC tests can
    /// assert reclamation after evaluation (see WI-055, WI-058). Useful
    /// diagnostic at runtime too.
    pub fn closure_arena_live_count(&self) -> usize { self.closures.live() }

    /// Register a Rust builtin keyed by the fully-qualified operation name.
    /// Returns `Err` if the name can't be resolved in the KB's symbol table.
    pub fn register_builtin<F>(&mut self, qualified_name: &str, f: F) -> Result<(), EvalError>
    where
        F: Fn(&mut Interpreter, &[Value]) -> Result<Value, EvalError> + 'static,
    {
        let sym = self.kb.try_resolve_symbol(qualified_name).ok_or_else(|| {
            EvalError::UnknownOperation { name: qualified_name.to_string() }
        })?;
        self.builtins.insert(sym, std::sync::Arc::new(f));
        Ok(())
    }

    /// Register a persistence backend, keyed by its canonical store-value
    /// form. Anthill code that calls `persist`/`retract`/`flush` with a
    /// `Value::Entity` whose canonical form matches `key` routes to this
    /// instance. Replaces any prior registration under the same key.
    /// Use [`Self::store_canonical_key`] to compute the key from the
    /// store's value representation.
    pub fn register_store(&mut self, key: String, store: Box<dyn Store>) {
        self.store_registry.insert(key, store);
    }

    /// Compute the canonical-key string for a store value (`Value::Entity`).
    /// Same string for any two values that compare equal under
    /// `Value::structural_eq` modulo named-arg ordering.
    pub fn store_canonical_key(&self, v: &Value) -> Result<String, EvalError> {
        let mut buf = String::new();
        self.write_value_canonical(v, &mut buf)?;
        Ok(buf)
    }

    /// Recursive helper for [`Self::store_canonical_key`].
    fn write_value_canonical(&self, v: &Value, buf: &mut String) -> Result<(), EvalError> {
        match v {
            Value::Int(n) => buf.push_str(&n.to_string()),
            Value::BigInt(n) => buf.push_str(&n.to_string()),
            Value::Float(f) => {
                let s = f.to_string();
                buf.push_str(&s);
                if !s.contains('.') { buf.push_str(".0"); }
            }
            Value::Bool(b) => buf.push_str(if *b { "true" } else { "false" }),
            Value::Str(s) => crate::persistence::print::write_anthill_string(s, buf),
            Value::Entity { functor, pos, named } => {
                buf.push_str(self.kb.resolve_sym(*functor));
                if pos.is_empty() && named.is_empty() {
                    return Ok(());
                }
                buf.push('(');
                let mut first = true;
                for p in pos {
                    if !first { buf.push_str(", "); }
                    first = false;
                    self.write_value_canonical(p, buf)?;
                }
                let mut sorted: Vec<&(Symbol, Value)> = named.iter().collect();
                sorted.sort_by(|a, b| {
                    self.kb.resolve_sym(a.0).cmp(self.kb.resolve_sym(b.0))
                });
                for (sym, val) in sorted {
                    if !first { buf.push_str(", "); }
                    first = false;
                    buf.push_str(self.kb.resolve_sym(*sym));
                    buf.push_str(": ");
                    self.write_value_canonical(val, buf)?;
                }
                buf.push(')');
            }
            Value::Term(tid) => {
                buf.push_str(&crate::persistence::print::TermPrinter::new(&self.kb).print_term(*tid));
            }
            Value::Unit
            | Value::Tuple { .. }
            | Value::Closure(_)
            | Value::Stream(_)
            | Value::Lazy(_)
            | Value::Substitution(_)
            | Value::Map(_)
            | Value::Cell(_)
            | Value::Requirement(_) => {
                return Err(EvalError::TypeMismatch {
                    expected: "store-shaped Value (Entity / scalar / Term)",
                    got: v.type_name().to_string(),
                });
            }
        }
        Ok(())
    }

    /// Invoke an anthill operation by qualified name with the given argument
    /// values. The operation is looked up via `OperationInfo` facts — the
    /// stdlib + user code must already be loaded. If the operation is
    /// backed by a registered Rust builtin (no anthill body), the builtin
    /// runs directly without a frame push.
    pub fn call(&mut self, qualified_name: &str, args: &[Value]) -> Result<Value, EvalError> {
        let sym = self.kb.try_resolve_symbol(qualified_name).ok_or_else(|| {
            EvalError::UnknownOperation { name: qualified_name.to_string() }
        })?;
        if let Some(builtin) = self.builtins.get(&sym).cloned() {
            return (builtin)(self, args);
        }
        let (body_term, params) = eval::lookup_operation_body(&self.kb, sym)
            .ok_or_else(|| EvalError::OperationBodyMissing {
                name: qualified_name.to_string(),
            })?;
        if args.len() != params.len() {
            return Err(EvalError::ArityMismatch {
                op: "operation call",
                expected: params.len(),
                got: args.len(),
            });
        }
        let mut locals: smallvec::SmallVec<[(Symbol, Value); 4]> = smallvec::SmallVec::new();
        for (i, (pname, _)) in params.iter().enumerate() {
            locals.push((*pname, args[i].clone()));
        }
        // Entry-point requirement seeding: if `sym`'s parent sort
        // declares any `requires`, the WI-222 requirement-insertion
        // pass will have rewritten internal calls inside the body to
        // read `requirement_at_current(i)` against the body's frame
        // requirements. For an externally-driven entry call (e.g.
        // `anthill run … --` invoking a sort's `main`), the caller
        // has no requirement values to pass — but the body still
        // expects the slots to exist. Seed self-referential requirement
        // values whose functor = parent sort. Same-sort recursion
        // resolves <parent_sort>.<op> to the impl op correctly; mutual-
        // sort dispatch is undefined for this no-context entry (and
        // would need a richer entry API to express which impls back
        // the parent's `requires`).
        let requirements = self.seed_entry_requirements(sym);
        self.step_count = 0;
        self.stack.push(Frame {
            op: sym,
            expr: body_term,
            locals,
            requirements,
            awaiting: None,
        })?;
        self.run()
    }

    /// Build the initial `frame.requirements` for an entry-point call
    /// to `op_sym`. Walks the parent sort's `requires_chain` and
    /// allocates one `Requirement{functor: parent_sort, requirements:
    /// []}` per slot — a self-referential placeholder sufficient for
    /// same-sort recursion. Returns empty if the op's parent has no
    /// `requires` (the common case).
    fn seed_entry_requirements(
        &self,
        op_sym: Symbol,
    ) -> smallvec::SmallVec<[value::RequirementHandle; 2]> {
        let op_qn = self.kb.qualified_name_of(op_sym);
        let Some((parent_qn, _)) = op_qn.rsplit_once('.') else {
            return smallvec::SmallVec::new();
        };
        let Some(parent_sym) = self.kb.try_resolve_symbol(parent_qn) else {
            return smallvec::SmallVec::new();
        };
        let chain = crate::kb::typing::requires_chain(&self.kb, parent_sym);
        let mut out: smallvec::SmallVec<[value::RequirementHandle; 2]> =
            smallvec::SmallVec::new();
        for _ in &chain {
            // Self-referential: functor = parent sort, no bundled deps.
            // Adequate for same-sort recursion (the dominant case for
            // CLI entry-point bodies); cross-sort dispatch through the
            // requirement would need a richer entry API.
            let h = self.requirements.alloc(parent_sym, smallvec::SmallVec::new());
            out.push(h);
        }
        out
    }

    /// Override the activation-stack depth cap. Kept as a convenience wrapper
    /// over `config_mut()` for tests that only care about the depth limit.
    pub fn set_stack_depth_cap(&mut self, cap: usize) {
        self.config.depth_cap = Some(cap);
        self.stack.set_cap(cap);
    }

    /// Number of live stream-arena slots. Diagnostic for refcount tests.
    pub fn stream_arena_live_count(&self) -> usize { self.streams.live() }

    /// Number of live substitution-arena slots. Diagnostic for refcount tests.
    pub fn subst_arena_live_count(&self) -> usize { self.substs.live() }

    /// Number of live map-arena slots. Diagnostic for refcount tests.
    pub fn map_arena_live_count(&self) -> usize { self.maps.live() }

    /// Allocate a fresh map slot and return a handle.
    pub fn alloc_map(&self, body: map_arena::MapBody) -> value::MapHandle {
        self.maps.alloc(body)
    }

    /// Run `f` with a shared reference to the map body behind `h`.
    pub fn with_map<R>(
        &self,
        h: &value::MapHandle,
        f: impl FnOnce(&map_arena::MapBody) -> R,
    ) -> R {
        self.maps.with_body(h, f)
    }

    /// Clone the map-arena handle. Same rationale as `subst_arena()`.
    pub fn map_arena(&self) -> MapArenaRef {
        self.maps.clone()
    }

    /// Number of live cell-arena slots. Diagnostic for refcount tests.
    pub fn cell_arena_live_count(&self) -> usize { self.cells.live() }

    /// Number of live requirement-arena slots. Diagnostic for refcount
    /// and cascade-drop tests under the WI-223 runtime support.
    pub fn requirement_arena_live_count(&self) -> usize { self.requirements.live() }

    /// Allocate a fresh requirement slot bundling `(functor, requirements)`
    /// and return an owning handle. Used by the eval to reduce
    /// `construct_requirement(impl, [...])` IR forms.
    pub fn alloc_requirement(
        &self,
        functor: Symbol,
        requirements: smallvec::SmallVec<[value::RequirementHandle; 1]>,
    ) -> value::RequirementHandle {
        self.requirements.alloc(functor, requirements)
    }

    /// Test-only: read a closure's snapshotted `requirements` channel.
    /// Used to verify that lambda construction captures the enclosing
    /// frame's requirements (acceptance #4 of WI-223).
    #[doc(hidden)]
    pub fn closure_requirements_for_test(
        &self,
        h: &value::ClosureHandle,
    ) -> smallvec::SmallVec<[value::RequirementHandle; 1]> {
        self.closures.with(h, |c| c.requirements.clone())
    }

    /// Test-only entry point: drive a single expression as the body of an
    /// ad-hoc operation, with `frame.requirements` pre-seeded. Used to
    /// verify the WI-223 requirement IR reductions
    /// (`requirement_at_current` / `requirement_at_sort` /
    /// `construct_requirement`) before WI-222's rewrite pass produces them
    /// from real call sites.
    #[doc(hidden)]
    pub fn run_with_requirements(
        &mut self,
        expr: crate::kb::term::TermId,
        requirements: smallvec::SmallVec<[value::RequirementHandle; 2]>,
    ) -> Result<Value, EvalError> {
        let op = self.kb.intern("__test_requirement_eval");
        self.step_count = 0;
        self.stack.push(Frame {
            op,
            expr,
            locals: smallvec::SmallVec::new(),
            requirements,
            awaiting: None,
        })?;
        self.run()
    }

    /// Clone the requirement-arena handle. Same rationale as
    /// `subst_arena()`: lets a caller hold a borrow on the arena while
    /// `&mut self` on the interpreter is in flight.
    pub fn requirement_arena(&self) -> RequirementArenaRef {
        self.requirements.clone()
    }

    /// Allocate a fresh cell slot and return an owning handle.
    pub fn alloc_cell(&self, value: Value) -> value::CellHandle {
        self.cells.alloc(value)
    }

    /// Snapshot the value held in `h`.
    pub fn read_cell(&self, h: &value::CellHandle) -> Value {
        self.cells.read(h)
    }

    /// Replace the value in `h`; returns the prior value.
    pub fn write_cell(&self, h: &value::CellHandle, new: Value) -> Value {
        self.cells.write(h, new)
    }

    /// Clone the cell-arena handle (cheap `Rc` bump). Same rationale as
    /// `subst_arena()`: lets a caller hold a borrow on the arena while
    /// `&mut self` on the interpreter is in flight.
    pub fn cell_arena(&self) -> CellArenaRef {
        self.cells.clone()
    }

    /// Allocate a fresh substitution slot and return a handle.
    pub fn alloc_subst(&self, s: crate::kb::subst::Substitution) -> value::SubstHandle {
        self.substs.alloc(s)
    }

    /// Run `f` with a shared reference to the substitution behind `h`.
    pub fn with_subst<R>(
        &self,
        h: &value::SubstHandle,
        f: impl FnOnce(&crate::kb::subst::Substitution) -> R,
    ) -> R {
        self.substs.with_subst(h, f)
    }

    /// Clone the substitution-arena handle. Useful when a caller needs to
    /// borrow a substitution through the arena while also mutably borrowing
    /// `kb`; both fields are independent, so the cloned `Rc` decouples the
    /// arena borrow from any `&mut self` on the interpreter.
    pub fn subst_arena(&self) -> subst_arena::SubstArenaRef {
        self.substs.clone()
    }

    /// Allocate a stream source, returning an owning handle.
    pub fn alloc_stream(&self, src: stream::StreamSource) -> value::StreamHandle {
        self.streams.alloc(src)
    }

    /// Pump a stream by one step. Returns `Some((value, continuation))` for
    /// a yielded element, or `None` on exhaustion. The continuation is a
    /// fresh handle sharing the underlying arena slot(s) — for `Resolver`
    /// it's the same slot advanced in place; for `MPlus` with `left`
    /// exhausted, it's the `right` child's handle.
    ///
    /// Resolver yields land as `Value::Substitution(handle)` pointing into
    /// the per-interpreter substitution arena; anthill code reads individual
    /// bindings via `Substitution.apply`.
    pub fn stream_split_first(
        &mut self,
        handle: &value::StreamHandle,
    ) -> Result<Option<(Value, value::StreamHandle)>, EvalError> {
        use stream::StreamSource;
        enum Action {
            Done,
            YieldSelf(Value),
            PumpResolver(crate::kb::resolve::SearchStream),
            PumpLeft { left: value::StreamHandle, right: value::StreamHandle },
        }

        let arena = self.streams.clone();
        let action = arena.with_source_mut(handle, |src| match src {
            StreamSource::Empty => (StreamSource::Empty, Action::Done),
            StreamSource::Resolver(None) => (StreamSource::Resolver(None), Action::Done),
            StreamSource::Resolver(Some(stream)) => (
                StreamSource::Resolver(None),
                Action::PumpResolver(stream),
            ),
            StreamSource::Pure(mut slot) => match slot.take() {
                Some(v) => (StreamSource::Empty, Action::YieldSelf(v)),
                None => (StreamSource::Empty, Action::Done),
            },
            StreamSource::MPlus { left, right } => (
                StreamSource::MPlus { left: left.clone(), right: right.clone() },
                Action::PumpLeft { left, right },
            ),
            StreamSource::Native(mut f) => match f() {
                Some(v) => (StreamSource::Native(f), Action::YieldSelf(v)),
                None => (StreamSource::Empty, Action::Done),
            },
            StreamSource::External(mut s) => match s.next() {
                Some(v) => (StreamSource::External(s), Action::YieldSelf(v)),
                None => (StreamSource::Empty, Action::Done),
            },
        });

        match action {
            Action::Done => Ok(None),
            Action::YieldSelf(v) => Ok(Some((v, handle.clone()))),
            Action::PumpResolver(stream) => {
                let result = stream.split_first(&mut self.kb);
                let stream_arena = self.streams.clone();
                match result {
                    Some((sol, rest)) => {
                        stream_arena.with_source_mut(handle, |_| {
                            (StreamSource::Resolver(Some(rest)), ())
                        });
                        let subst_handle = self.substs.alloc(sol.subst);
                        Ok(Some((Value::Substitution(subst_handle), handle.clone())))
                    }
                    None => {
                        stream_arena.with_source_mut(handle, |_| (StreamSource::Empty, ()));
                        Ok(None)
                    }
                }
            }
            Action::PumpLeft { left, right } => match self.stream_split_first(&left)? {
                Some((v, left_rest)) => {
                    let arena = self.streams.clone();
                    arena.with_source_mut(handle, |_| {
                        (StreamSource::MPlus { left: left_rest, right: right.clone() }, ())
                    });
                    Ok(Some((v, handle.clone())))
                }
                None => self.stream_split_first(&right),
            },
        }
    }
}

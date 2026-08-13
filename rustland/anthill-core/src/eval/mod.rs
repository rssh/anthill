//! Tree-walking interpreter for anthill expression bodies. Proposal 026.
//!
//! Supports: literals, variables, `if`, `let`, operation call, pattern
//! match, lambda + closures, list / tuple literals. Streams and effect
//! handlers are deferred.

pub mod builtins;
pub mod cell_arena;
pub mod closure;
pub mod dictionary;
pub mod effects;
pub mod error;
pub mod eval;
pub mod frame;
pub mod map_arena;
pub mod pattern;
pub mod stream;
pub mod subst_arena;
pub mod value;

use std::collections::HashMap;

use crate::intern::Symbol;
use crate::kb::KnowledgeBase;

pub use error::{macro_rejection_message, render_raised_payload, EvalError};
pub use eval::value_functor;
pub use frame::{ActivationStack, Frame, FrameTypeArgs};
pub use value::Value;

use cell_arena::CellArenaRef;
use closure::ClosureArenaRef;
use effects::EffectRegistry;
use map_arena::MapArenaRef;
use stream::StreamArenaRef;

/// Runtime resource limits. Each cap is optional so different embeddings
/// can trade safety against throughput independently.
///
/// - `depth_cap` bounds the activation stack. Non-tail recursion needs
///   O(n) frames and will trip this; tail recursion (TCO) stays O(1) and
///   is unaffected.
/// - `step_cap` bounds total interpreter work — one tick per `run()` trampoline
///   iteration, covering BOTH a `step()` reduction AND a value delivery. TCO
///   turns `loop() = loop()` into a constant-depth infinite loop that
///   `depth_cap` can't catch; likewise a dispatch/deliver value-cascade that
///   re-dispatches forever (a mis-resolved spec op) stays at constant
///   activation depth — both iterate on the trampoline, so each costs one step
///   and `step_cap` is the single guard that bounds them. On exhaustion the
///   `StepsExhausted` error carries the recent-dispatch ring, naming the
///   looping operations. Off by default so ordinary batch evaluation isn't
///   capped; the CLI binaries opt into a backstop cap (see `anthill::runner`).
#[derive(Clone, Copy, Debug)]
pub struct EvalConfig {
    pub depth_cap: Option<usize>,
    pub step_cap: Option<u64>,
    /// WI-625 gap 1 (SLD→eval bridge): this interpreter was lent to the resolver
    /// to run a host-bodied op at resolution. Because the resolver above CAN
    /// residualize (delay), a semantic comparison that reaches a genuinely
    /// undecided point must SUSPEND (`EvalError::Suspended`) rather than force a
    /// possibly-membership-wrong structural verdict — the resolver then delays.
    /// Off for every top-level eval (which has nowhere to suspend *to*, so its
    /// structural fallback is the documented behaviour).
    pub bridge_mode: bool,
}

impl Default for EvalConfig {
    fn default() -> Self {
        Self {
            depth_cap: Some(1_000_000),
            step_cap: None,
            bridge_mode: false,
        }
    }
}

impl EvalConfig {
    pub fn unbounded() -> Self {
        Self {
            depth_cap: None,
            step_cap: None,
            bridge_mode: false,
        }
    }
}

/// Rust-side builtin: takes the interpreter and evaluated arg `Value`s,
/// returns a `Value` or an error. Mirrors `kb::resolve::builtins` in shape.
pub type BuiltinFn = std::sync::Arc<dyn Fn(&mut Interpreter, &[Value]) -> Result<Value, EvalError>>;

/// Proposal 039 / WI-084 — a term-level constant's memoized value state in
/// `Interpreter::const_cache`. `Forcing` marks a const whose value source is
/// currently being evaluated; re-entering it is a dependency cycle.
#[derive(Clone)]
pub(crate) enum ConstCacheEntry {
    /// The value is being computed right now — the dynamic cycle sentinel.
    Forcing,
    /// The forced value, shared by every later reference.
    Cached(Value),
}

/// Cached `Symbol`s for the reflect expression / pattern entities. Populated
/// at `Interpreter::new` via `kb.try_resolve_symbol`. An entry stays `None`
/// when the corresponding stdlib entity hasn't been loaded — the evaluator
/// surfaces a clear "unhandled functor" error instead of misbehaving.
///
/// Post-WI-248: most expression-form fields are no longer read by the
/// eval (NodeOccurrence dispatch is structural on the `Expr` variant,
/// not symbol-keyed). The fields remain populated for backwards-
/// compat and for any future passes that want a stable handle on the
/// canonical reflect entities — `#[allow(dead_code)]` lets the build
/// stay warning-clean. Pattern entities and collection literals are
/// still read directly (pattern matching and Value construction).
#[derive(Default, Debug)]
#[allow(dead_code)]
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
    pub apply_within: Option<Symbol>,
    pub ho_apply_within: Option<Symbol>,
    pub constructor_within: Option<Symbol>,
    pub lambda_within: Option<Symbol>,
    pub requirement_at_sort: Option<Symbol>,

    // Pattern entities — still consulted by `eval::pattern::match_pattern`.
    pub var_pattern: Option<Symbol>,
    pub wildcard: Option<Symbol>,
    pub literal_pattern: Option<Symbol>,
    pub constructor_pattern: Option<Symbol>,
    pub tuple_pattern: Option<Symbol>,

    // Collection / list constructors — still consulted by Value
    // construction in `finish_constructor` / `build_list_value`.
    pub list_literal: Option<Symbol>,
    pub tuple_literal: Option<Symbol>,
    pub set_literal: Option<Symbol>,
    pub cons: Option<Symbol>,
    pub nil: Option<Symbol>,
    // WI-531: reflect `Solution` variants — the element shape `KB.execute`
    // streams now yield (`definite(subst)` / `undecided(subst, residual)`).
    pub solution_definite: Option<Symbol>,
    pub solution_undecided: Option<Symbol>,
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
            lambda: r("anthill.reflect.Expr.lambda_expr"),
            constructor: r("anthill.reflect.Expr.constructor"),
            apply_within: r("anthill.reflect.Expr.apply_within"),
            ho_apply_within: r("anthill.reflect.Expr.ho_apply_within"),
            constructor_within: r("anthill.reflect.Expr.constructor_within"),
            lambda_within: r("anthill.reflect.Expr.lambda_within"),
            requirement_at_sort: r("anthill.reflect.Expr.requirement_at_sort"),

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
            solution_definite: r("anthill.reflect.Solution.definite"),
            solution_undecided: r("anthill.reflect.Solution.undecided"),
        }
    }
}

/// Cached `Symbol`s for common named-arg field keys. Resolved once at
/// `Interpreter::new` via `kb.intern` so per-step lookups compare `Symbol`s
/// instead of scanning strings.
#[derive(Debug)]
#[allow(dead_code)] // params/type_name/guard are reserved for future arms
pub(crate) struct FieldSymbols {
    pub value: Symbol,
    pub reference: Symbol,
    pub name: Symbol,
    pub cond: Symbol,
    pub then_branch: Symbol,
    pub else_branch: Symbol,
    pub pattern: Symbol,
    pub body: Symbol,
    pub fn_: Symbol,
    pub args: Symbol,
    /// WI-445: `constructor_pattern.named` — the `List[NamedPattern]` of
    /// `Foo(field: pat)` named sub-patterns.
    pub named: Symbol,
    pub params: Symbol,
    pub type_name: Symbol,
    pub scrutinee: Symbol,
    pub branches: Symbol,
    pub guard: Symbol,
    pub elements: Symbol,
    pub param: Symbol,
    pub head: Symbol,
    pub tail: Symbol,
    // WI-531 — reflect `Solution` field keys.
    pub subst: Symbol,
    pub residual: Symbol,
    // WI-222 / WI-223 — requirement IR field keys.
    pub slot: Symbol,
    pub op: Symbol,
    pub chain: Symbol,
    pub impl_functor: Symbol,
    pub requirements: Symbol,
    pub predicate: Symbol,
    /// WI-857 — `anthill.reflect.NoProvider`, the functor a dictionary slot carries
    /// when the spec's requirement had no provider at the goal's bindings. Interned
    /// ONCE here, like every other well-known name, so eval never re-derives it: it is
    /// what `port_resolved_tree` allocates (removing a `lookup_symbol(..)?` that would
    /// have silently residualized a whole resolved tree if nothing had interned the
    /// name yet). NOTE the typer-side readers still test by NAME
    /// (`kb::typing::is_no_provider`) because they hold only a `&KnowledgeBase`, so
    /// there are two spellings, not one; see that function for the cost.
    pub no_provider: Symbol,
    /// `__req_self` — the Self-slot requirement-param name (WI-237
    /// names model). Interned, not a stdlib symbol.
    pub req_self: Symbol,
}

impl FieldSymbols {
    fn resolve(kb: &mut KnowledgeBase) -> Self {
        Self {
            value: kb.intern("value"),
            reference: kb.intern("reference"),
            name: kb.intern("name"),
            cond: kb.intern("cond"),
            then_branch: kb.intern("then_branch"),
            else_branch: kb.intern("else_branch"),
            pattern: kb.intern("pattern"),
            body: kb.intern("body"),
            fn_: kb.intern("fn"),
            args: kb.intern("args"),
            named: kb.intern("named"),
            params: kb.intern("params"),
            type_name: kb.intern("type_name"),
            scrutinee: kb.intern("scrutinee"),
            branches: kb.intern("branches"),
            guard: kb.intern("guard"),
            elements: kb.intern("elements"),
            param: kb.intern("param"),
            head: kb.intern("head"),
            tail: kb.intern("tail"),
            subst: kb.intern("subst"),
            residual: kb.intern("residual"),
            slot: kb.intern("slot"),
            op: kb.intern("op"),
            chain: kb.intern("chain"),
            impl_functor: kb.intern("impl_functor"),
            requirements: kb.intern("requirements"),
            predicate: kb.intern("predicate"),
            no_provider: crate::kb::typing::no_provider_sym(kb),
            req_self: kb.intern("__req_self"),
        }
    }
}

/// WI-1045 — why [`Interpreter::frame_requirements_from_trees`] could not build a
/// frame's requirement channel. Two causes with different owners, kept apart
/// because collapsing them reported a missing stdlib namespace as an unresolvable
/// requirement of the named slot.
pub(crate) enum FrameReqFailure {
    /// This slot's tree names a CALLER scope (`FromScope`), which cannot arise
    /// from the empty-scope resolution these callers run.
    CallerScopeSlot(Symbol),
    /// No dictionary is constructible at all: the KB never loaded
    /// `anthill.realization.runtime.Dictionary`. Not the slot's fault.
    NoDictionarySort,
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
    pub(crate) effect_handlers: EffectRegistry,
    /// Memoized operation-body lookups. `lookup_operation_body` linear-scans
    /// every `OperationInfo` fact to find the one matching the op symbol, so
    /// without this cache every operation call is O(num_operations) — which
    /// dominates interpreted runtime once a program makes many calls. The
    /// `OperationInfo` facts are static across a run (only data facts get
    /// persisted/retracted), so memoizing by op `Symbol` is sound.
    pub(crate) op_body_cache: HashMap<Symbol, eval::OpBody>,
    /// Proposal 039 / WI-084 — memoized term-level-constant values, keyed by the
    /// const's `SymbolKind::Const` symbol. THE memoization the proposal calls for:
    /// a const's value source is forced AT MOST ONCE and shared by every
    /// reference (referentially transparent — the source is pure). The `Forcing`
    /// sentinel is the dynamic cycle detector: re-demanding a const already being
    /// forced is `ConstCycle`, not an infinite fold. Distinct from
    /// `op_body_cache` (which caches body *lookups*, not values).
    pub(crate) const_cache: HashMap<Symbol, ConstCacheEntry>,
    /// Whether the `ANTHILL_PROFILE` profiler is active. Read once from the
    /// environment at construction (it can't change mid-run) so the per-step
    /// and per-dispatch profiling gates are a plain field test, not an env
    /// lookup. See `eval::OP_PROF` / `Self::dump_profile`.
    pub(crate) profiling: bool,
    /// Whether `ANTHILL_TRACE_REQ` requirement tracing is active. Read once at
    /// construction for the same reason as `profiling`: the gate sits on the
    /// per-dispatch path in `requirements_for_value_directed_impl`, where every
    /// leaf-impl call would otherwise pay an env lookup to print nothing.
    pub(crate) trace_requirements: bool,
    pub(crate) config: EvalConfig,
    /// Monotonically increasing step counter, reset on each `call()`.
    /// `run()` increments it once per `step()` and compares against
    /// `config.step_cap`. Not a permanent counter — after a call returns
    /// the host can inspect and reset via `config_mut()`.
    pub(crate) step_count: u64,
    /// Bounded ring of the most recent dispatch targets (newest at the back),
    /// reset per top-level call. Maintained only when a `step_cap` is set (its
    /// sole reader is `StepsExhausted`, which can only fire under a cap); on
    /// that error its contents name the looping operations (a loop repeats its
    /// ops, so they fill the ring).
    pub(crate) recent_dispatches: std::collections::VecDeque<Symbol>,
}

/// Collect the top-`n` profiler entries from a thread-local counter map,
/// sorted descending by the second field (reductions or wall nanos), and
/// clear the map for the next run. Shared by `dump_profile`'s op + builtin
/// tables. See `eval::OP_PROF` / `eval::BUILTIN_PROF`.
fn drain_top<V: Copy + Ord>(
    prof: &'static std::thread::LocalKey<std::cell::RefCell<HashMap<Symbol, (u64, V)>>>,
    n: usize,
) -> Vec<(Symbol, (u64, V))> {
    prof.with(|p| {
        let mut rows: Vec<(Symbol, (u64, V))> = p.borrow().iter().map(|(k, v)| (*k, *v)).collect();
        rows.sort_by(|a, b| b.1 .1.cmp(&a.1 .1));
        rows.truncate(n);
        p.borrow_mut().clear();
        rows
    })
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
            effect_handlers: EffectRegistry::new(),
            op_body_cache: HashMap::new(),
            const_cache: HashMap::new(),
            profiling: std::env::var_os("ANTHILL_PROFILE").is_some(),
            trace_requirements: std::env::var_os("ANTHILL_TRACE_REQ").is_some(),
            config,
            step_count: 0,
            recent_dispatches: std::collections::VecDeque::new(),
        }
    }

    pub fn config(&self) -> &EvalConfig {
        &self.config
    }

    pub fn config_mut(&mut self) -> &mut EvalConfig {
        &mut self.config
    }

    pub fn kb(&self) -> &KnowledgeBase {
        &self.kb
    }
    pub fn kb_mut(&mut self) -> &mut KnowledgeBase {
        &mut self.kb
    }
    pub fn into_kb(self) -> KnowledgeBase {
        self.kb
    }

    /// Number of live closure-arena slots. Exposed so refcount/GC tests can
    /// assert reclamation after evaluation (see WI-055, WI-058). Useful
    /// diagnostic at runtime too.
    pub fn closure_arena_live_count(&self) -> usize {
        self.closures.live()
    }

    /// Register a Rust builtin keyed by the fully-qualified operation name.
    /// Returns `Err` if the name can't be resolved in the KB's symbol table.
    pub fn register_builtin<F>(&mut self, qualified_name: &str, f: F) -> Result<(), EvalError>
    where
        F: Fn(&mut Interpreter, &[Value]) -> Result<Value, EvalError> + 'static,
    {
        let sym = self.kb.try_resolve_symbol(qualified_name).ok_or_else(|| {
            EvalError::UnknownOperation {
                name: qualified_name.to_string(),
            }
        })?;
        self.builtins.insert(sym, std::sync::Arc::new(f));
        Ok(())
    }

    /// [`Self::register_builtin`] for a caller that already holds the operation's
    /// `Symbol` — no name resolution, and no "does it resolve?" question to answer,
    /// because the caller resolved it. WI-876's `operation_map` registration takes
    /// this: its symbols are resolved ONCE at load and cached on the KB, and it runs
    /// again for every fresh interpreter.
    pub fn register_builtin_sym<F>(&mut self, sym: crate::intern::Symbol, f: F)
    where
        F: Fn(&mut Interpreter, &[Value]) -> Result<Value, EvalError> + 'static,
    {
        self.builtins.insert(sym, std::sync::Arc::new(f));
    }

    /// Register a durability mirror, keyed by its canonical store-value
    /// form. Anthill code that calls `persist`/`retract`/`flush` with a
    /// `Value::Entity` whose canonical form matches `key` routes to this
    /// instance. Replaces any prior registration under the same key.
    /// Use [`Self::store_canonical_key`] to compute the key from the
    /// store's value representation.
    ///
    /// Its intrinsic per-functor write policy is held by `kb.extents`, alongside
    /// the mirror itself; the evaluator owns neither persistence registry. Registration
    /// resolves that policy's declared functor names and REFUSES one that denotes
    /// nothing — see [`KnowledgeBase::register_mirror`] for why a drop cannot be silent.
    pub fn register_mirror(
        &mut self,
        key: String,
        mirror: Box<dyn crate::persistence::Store>,
    ) -> Result<(), crate::kb::extent::ExtentRegError> {
        self.kb.register_mirror(key, mirror)
    }

    /// Compute the canonical-key string for a store value (`Value::Entity`).
    /// Same string for any two values that compare equal under
    /// `views_structurally_equal` modulo named-arg ordering.
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
            Value::Entity { functor, pos, named, .. } => {
                buf.push_str(self.kb.local_name_of(*functor));
                if pos.is_empty() && named.is_empty() {
                    return Ok(());
                }
                buf.push('(');
                let mut first = true;
                for p in pos.iter() {
                    if !first { buf.push_str(", "); }
                    first = false;
                    self.write_value_canonical(p, buf)?;
                }
                let mut sorted: Vec<&(Symbol, Value)> = named.iter().collect();
                sorted.sort_by(|a, b| {
                    self.kb.local_name_of(a.0).cmp(self.kb.local_name_of(b.0))
                });
                for (sym, val) in sorted {
                    if !first { buf.push_str(", "); }
                    first = false;
                    buf.push_str(self.kb.local_name_of(*sym));
                    buf.push_str(": ");
                    self.write_value_canonical(val, buf)?;
                }
                buf.push(')');
            }
            Value::Term { id: tid, .. } => {
                buf.push_str(&crate::persistence::print::TermPrinter::new(&self.kb).print_term(*tid));
            }
            // Through the SAME owner the `Term::Ref` twin prints by, so the two
            // carriers of one symbol cannot key differently.
            Value::SymbolRef(sym) => {
                crate::persistence::print::TermPrinter::new(&self.kb).write_symbol_ref(*sym, buf);
            }
            Value::Unit
            | Value::Tuple { .. }
            | Value::Closure(_)
            | Value::OpRef { .. }
            | Value::Stream(_)
            | Value::Substitution(_)
            | Value::Map(_)
            | Value::Cell(_)
            | Value::FactRef(_)
            | Value::Node(_)
            // WI-714: a `Relation` is a query value, never persisted store data.
            | Value::Relation { .. }
            // WI-109: an unbound logic variable has no canonical store key.
            | Value::Var(_) => {
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
    ///
    /// Requirements (dictionary values for the parent sort's `requires`
    /// chain) are auto-seeded as self-referential placeholders: each slot
    /// is a `Requirement { functor: parent_sort, requirements: [] }`. That
    /// shape covers same-sort recursion (the dominant CLI entry case) but
    /// not cross-sort dispatch — when the parent sort's `requires` names a
    /// different sort (e.g. `requires WorkItemStore[State]`), the
    /// placeholder won't reach the named impl and the body will surface a
    /// dispatch/slot mismatch at runtime. Use
    /// [`Self::call_with_requirements`] to supply real impl-rooted
    /// dictionaries from the host. See `docs/design/operation-call-model.md`
    /// §"Host-to-entry-op boundary".
    pub fn call(&mut self, qualified_name: &str, args: &[Value]) -> Result<Value, EvalError> {
        let sym = self.kb.try_resolve_symbol(qualified_name).ok_or_else(|| {
            EvalError::UnknownOperation {
                name: qualified_name.to_string(),
            }
        })?;
        self.call_op_sym(sym, args)
    }

    /// Symbol-keyed body of [`Self::call`]: dispatch to a registered builtin,
    /// else seed the entry op's `requires` chain with self-referential
    /// placeholders and invoke it. Private — host callers use `call` (by name);
    /// the resolver bridge uses [`Self::call_op_bridged`] (which does NOT seed
    /// placeholders — see there for why).
    fn call_op_sym(&mut self, sym: Symbol, args: &[Value]) -> Result<Value, EvalError> {
        if let Some(builtin) = self.builtins.get(&sym).cloned() {
            return (builtin)(self, args);
        }
        let mut requirements = self.seed_entry_requirements(sym)?;
        // WI-1091: the OP-SCOPED half, RESOLVED at the concrete argument types rather
        // than stood in for. See `seed_entry_op_requirements`.
        self.seed_entry_op_requirements(sym, args, &mut requirements)?;
        self.invoke_op_with_requirements(sym, args, requirements)
    }

    /// WI-625 gap 1 + Layer B: the resolver→eval bridge entry
    /// ([`crate::kb::KnowledgeBase::bridge_op_to_eval`]). Like [`Self::call`] but
    /// invoked BY SYMBOL (the resolver holds it already).
    ///
    /// The requirement dictionaries are RESOLVED at the concrete argument types
    /// ([`crate::kb::typing::resolve_bridge_requirements`], WI-300 Tier B / gap 3),
    /// NOT seeded with [`Self::seed_entry_requirements`]'s self-referential
    /// placeholders — a placeholder can misdispatch a `requires` op to a
    /// wrong-but-non-erroring impl and return a plausibly-WRONG value, which the
    /// resolver would import as a definite `eq`/`cmp` answer (an unsoundness the
    /// pre-bridge delay never had). Instead:
    ///   * a requirement-FREE op runs with empty dicts (the gap-1 behavior);
    ///   * a requires-carrying op gets REAL provider dicts, so its body's spec-op
    ///     dispatch reaches the right impl and DECIDES (the gap-3 win);
    ///   * a requirement that cannot be resolved uniquely at these arg types
    ///     ([`BridgeRequirements::Unresolvable`], or WI-855's
    ///     [`BridgeRequirements::Ambiguous`] tie) SUSPENDS → the bridge residualizes,
    ///     never running with a wrong or missing dict. The two suspend for different
    ///     REASONS and say so, but a bridged eval may not abort the enclosing
    ///     resolution either way (WI-483), so both delay.
    pub(crate) fn call_op_bridged(
        &mut self,
        sym: Symbol,
        args: &[Value],
    ) -> Result<Value, EvalError> {
        if let Some(builtin) = self.builtins.get(&sym).cloned() {
            return (builtin)(self, args);
        }
        use crate::kb::typing::BridgeRequirements;
        let requirements =
            match crate::kb::typing::resolve_bridge_requirements(&mut self.kb, sym, args) {
                BridgeRequirements::NoneNeeded => smallvec::SmallVec::new(),
                BridgeRequirements::Unresolvable { detail } => {
                    return Err(EvalError::Suspended {
                        detail: format!(
                            "bridge: cannot resolve a required dictionary for `{}` at these \
                         argument types: {detail}",
                            self.kb.qualified_name_of(sym),
                        ),
                        // A missing dictionary is a flounder, not a truncated search.
                        truncated: false,
                    });
                }
                // WI-855 — a TIE, kept apart from its siblings above so this consumer
                // says WHICH failure it is. It still SUSPENDS rather than raising, and
                // that is the difference from the value-directed consumer: this one runs
                // inside SLD resolution, where WI-483 substitution transparency says a
                // bridged eval's failure must not break the enclosing rule — the caller
                // (`bridge_op_to_eval`) delays either way, so raising would only trade a
                // named delay for an unnamed one.
                //
                // The SENTENCE has one owner — `AmbiguousRequirement`'s `Display` — and
                // this arm adds only its `bridge:` prefix, the same division the
                // `Unresolvable` arm above uses with typing.rs's `detail`. Two hand-kept
                // copies of one message would drift, and only the `Display` copy is under
                // test — MEASURED, nothing in the crate destructures `Suspended.detail`
                // at all (the bridge's two readers take `..` / `truncated`, `simp_rewrite`
                // residualizes), so this text is the record left for whoever first
                // surfaces one, not something a test could pin today.
                BridgeRequirements::Ambiguous {
                    requirement,
                    candidates,
                    slot: _,
                } => {
                    let tie = EvalError::AmbiguousRequirement {
                        op: self.kb.qualified_name_of(sym).to_string(),
                        requirement,
                        candidates,
                    };
                    return Err(EvalError::Suspended {
                        detail: format!("bridge: {tie}"),
                        // An ambiguity is a flounder, not a truncated search.
                        truncated: false,
                    });
                }
                BridgeRequirements::Resolved(parent, trees) => {
                    self.frame_requirements_from_trees(parent, &trees)
                        .map_err(|f| {
                            EvalError::Suspended {
                                detail: match f {
                                    FrameReqFailure::CallerScopeSlot(name) => format!(
                                        "bridge: requirement `{}` for `{}` resolved to a \
                                 caller-scope slot with no caller frame",
                                        self.kb.local_name_of(name),
                                        self.kb.qualified_name_of(sym),
                                    ),
                                    FrameReqFailure::NoDictionarySort => format!(
                                        "bridge: cannot build any requirement dictionary for \
                                 `{}` — this KB never loaded \
                                 `anthill.realization.runtime.Dictionary`",
                                        self.kb.qualified_name_of(sym),
                                    ),
                                },
                                // A missing caller frame is a flounder, not truncation.
                                truncated: false,
                            }
                        })?
                }
            };
        self.invoke_op_with_requirements(sym, args, requirements)
    }

    /// The frame `requirements` channel for a [`BridgeRequirements::Resolved`]
    /// payload: slot 0 = the Self placeholder over the op's own parent sort, then
    /// one real provider handle per `requires` slot, keyed by the
    /// `synth_req_names` name each tree came back under. The same layout
    /// `call_with_requirements` assembles for a host caller and
    /// `expand_dispatching_dict` assembles from a dispatching dict.
    ///
    /// `Err` names WHICH of the two things went wrong, because they want different
    /// messages: a slot whose tree names a caller scope (only ever a `FromScope`,
    /// which cannot arise from an empty-scope resolution), or a KB with no
    /// `anthill.realization.runtime.Dictionary` to name, where NO dictionary is
    /// constructible and the slot is not at fault (WI-1045 — collapsing the second
    /// into the first reported a missing stdlib namespace as an unresolvable
    /// requirement, the WI-855 mis-attribution shape). The SPELLING of each is the
    /// caller's: the WI-625 bridge residualizes (`Suspended`), WI-822's
    /// value-directed dispatch raises (`Internal`). Both otherwise built this list
    /// identically, so it has one owner.
    fn frame_requirements_from_trees(
        // `&mut` since WI-857: the `__req_self` stand-in reads the dictionary layout,
        // which memoizes the requires chain on `kb`.
        &mut self,
        parent: Symbol,
        trees: &[(Symbol, crate::kb::typing::ResolvedRequiresNode)],
    ) -> Result<smallvec::SmallVec<[(Symbol, value::Dictionary); 2]>, FrameReqFailure> {
        let mut out: smallvec::SmallVec<[(Symbol, value::Dictionary); 2]> =
            smallvec::SmallVec::with_capacity(trees.len() + 1);
        // WI-857: layout-valid — see `stand_in_requirement`.
        let self_slot = self
            .stand_in_requirement(parent, parent)
            .map_err(|_| FrameReqFailure::NoDictionarySort)?;
        out.push((self.fields.req_self, self_slot));
        for (name, tree) in trees {
            // `port_resolved_tree` answers `None` for a `FromScope` AND for the
            // missing-sort case; the `stand_in_requirement` above already ruled the
            // second one out, so reaching here names the slot.
            out.push((
                *name,
                self.port_resolved_tree(tree)
                    .ok_or(FrameReqFailure::CallerScopeSlot(*name))?,
            ));
        }
        Ok(out)
    }

    /// WI-625 Layer B: port a resolved requirement tree
    /// ([`crate::kb::typing::ResolvedRequiresNode`]) to a runtime
    /// [`value::Dictionary`].
    ///
    /// WI-1045 — this had its OWN recursion over the tree, structurally identical
    /// to the resolver-side [`crate::kb::typing::dictionary_of_tree`] and
    /// differing only in which carrier it built. With one representation there is
    /// nothing left to differ in, so there is one walk: a `Leaf`'s impl with no
    /// sub-dictionaries, WI-857's marker for an `Unavailable`, and a
    /// `Conditional` recursing first so the arity matches the DICTIONARY LAYOUT
    /// (the spec's own `requires` chain then the impl's, WI-857 — which is what
    /// the eval dispatcher's cross-check measures).
    ///
    /// `None` for a `FromScope`, which cannot arise here (the bridge resolves
    /// with an empty scope) — the caller residualizes if it somehow does.
    fn port_resolved_tree(
        &mut self,
        tree: &crate::kb::typing::ResolvedRequiresNode,
    ) -> Option<value::Dictionary> {
        crate::kb::typing::dictionary_of_tree(&mut self.kb, tree)
    }

    /// WI-625 gap 1: is this interpreter running as the resolver's op-body
    /// bridge? When set, semantic comparisons that reach an undecided point
    /// suspend ([`EvalError::Suspended`]) instead of forcing a structural
    /// verdict. See [`EvalConfig::bridge_mode`].
    pub(crate) fn bridge_mode(&self) -> bool {
        self.config.bridge_mode
    }

    /// WI-625 gap 1: materialize a term-carried value into the interpreter's
    /// NATIVE form — a `Value::Term(Ref/Fn ctor)` becomes a `Value::Entity`
    /// (recursively), literals become scalars. The resolver hands the bridge its
    /// operands as term carriers (`Value::Term`), but eval builtins like
    /// `field_access` require a real `Value::Entity`; without this a bridged body
    /// that reads a field errors with "receiver is not an entity (got Term)".
    /// A non-term value (already native) passes through.
    ///
    /// WI-685: a `Value::Node` occurrence operand (a rule-body `eq`/`neq` operand,
    /// which the resolver no longer collapses to a `Value::Term` before the bridge)
    /// is lowered the same way — to a term, then to the native form — so a bridged
    /// body reads a real `Value::Entity`, not an occurrence.
    pub(crate) fn materialize_value(&mut self, v: Value) -> Value {
        match v {
            Value::Term { id, .. } => builtins::term_to_value(self, id),
            Value::Node(occ) => {
                let tid = crate::kb::node_occurrence::occurrence_to_term(&mut self.kb, &occ);
                builtins::term_to_value(self, tid)
            }
            other => other,
        }
    }

    /// Variant of [`Self::call`] that lets the host supply real
    /// impl-rooted dictionaries for the entry op's `requires` chain,
    /// instead of [`Self::seed_entry_requirements`]'s self-referential
    /// placeholders.
    ///
    /// `chain_dicts` is one handle per entry in the parent sort's
    /// flattened `requires` chain (in declaration order). The frame's
    /// Self slot (slot 0) is auto-allocated by this method as a
    /// self-referential placeholder for the parent sort — host callers
    /// don't see it. The supplied handles populate slots 1..=N.
    ///
    /// Required when the parent sort declares `requires X[…]` for a
    /// different sort X (e.g. `sort Main { requires
    /// WorkItemStore[State] }`): plain [`Self::call`] would seed slot 1
    /// with `Requirement{ functor: Main, … }`, and body-side
    /// `WorkItemStore.lookup(…)` would dispatch through the placeholder
    /// — wrong impl, runtime mis-dispatch.
    ///
    /// Use [`Self::alloc_requirement`] to build each handle. See
    /// `docs/design/operation-call-model.md` §"Host-to-entry-op boundary".
    ///
    /// WI-822 LEG 1: the count is the PARENT SORT's chain, not the entry op's composed
    /// one — an op-scoped `requires` has no host-boundary spelling, for the reason
    /// [`Self::seed_entry_requirements`] records, and widening this would ask every
    /// host for handles it has no way to build. Nothing in tree declares an entry op
    /// with its own `requires`; if one ever does, its slots stay unfilled here and the
    /// body's own read is what says so.
    pub fn call_with_requirements(
        &mut self,
        qualified_name: &str,
        args: &[Value],
        chain_dicts: smallvec::SmallVec<[value::Dictionary; 2]>,
    ) -> Result<Value, EvalError> {
        let sym = self.kb.try_resolve_symbol(qualified_name).ok_or_else(|| {
            EvalError::UnknownOperation {
                name: qualified_name.to_string(),
            }
        })?;
        if let Some(builtin) = self.builtins.get(&sym).cloned() {
            return (builtin)(self, args);
        }
        // Names model: `__req_self` → a self-referential placeholder for
        // the parent sort; `__req_<spec>` → each host-supplied chain
        // dict, zipped against `synth_req_names`. The arity check uses
        // the same name list as the bind step so the two can't diverge
        // (a prior version used `requires_chain_flat` here, which can
        // see different cache state than `synth_req_names`'s
        // substitution-composed walk). See operation-call-model.md
        // §"Host-to-entry-op boundary".
        let parent_sym = crate::kb::typing::impl_parent_of_op(&self.kb, sym);
        let names = parent_sym
            .map(|p| crate::kb::typing::provider_dict_entries(&mut self.kb, p).names(&mut self.kb));
        let expected = names.as_ref().map_or(0, |n| n.len());
        if chain_dicts.len() != expected {
            return Err(EvalError::Internal(format!(
                "call_with_requirements({qualified_name}): expected {expected} \
                 requirement slot(s) (the parent sort's requires chain), got {got}",
                got = chain_dicts.len(),
            )));
        }
        // WI-857: each supplied dictionary must also be layout-VALID for its slot's
        // spec, not merely present. The count check above is the pre-existing guard and
        // does not look inside. Checked HERE because this is the host boundary: a
        // hand-built dict that claims a provider and bundles nothing is the shape that
        // dies later at a frame push, attributed to the callee rather than to the
        // caller that built it. Today's in-tree host is layout-valid only because the
        // chains involved are empty — the same chain-free accident this ticket is about
        // — so the check is what keeps it valid when 058 phase 7 gives those specs
        // chains.
        if let Some(p) = parent_sym {
            // WI-869: the DICTIONARY chain, matching the `synth_req_names` count check
            // above — the divergence this file's own comment warns about three lines up
            // is precisely what a declared-chain read reintroduces here, silently
            // validating fewer dicts than were supplied.
            let chain = crate::kb::typing::provider_dict_entries(&mut self.kb, p);
            for (entry, dict) in chain.iter().zip(chain_dicts.iter()) {
                let want = crate::kb::typing::dict_layout(
                    &mut self.kb,
                    entry.required_sort,
                    dict.impl_sort(),
                );
                if dict.arity() != want.arity() {
                    return Err(EvalError::Internal(format!(
                        "call_with_requirements({qualified_name}): the dictionary \
                         supplied for `{}` has arity {} but its layout wants {}",
                        self.kb.qualified_name_of(entry.required_sort),
                        dict.arity(),
                        want.describe(&self.kb),
                    )));
                }
            }
        }
        let mut requirements: smallvec::SmallVec<[(Symbol, value::Dictionary); 2]> =
            smallvec::SmallVec::new();
        if let (Some(p), Some(names)) = (parent_sym, names) {
            // WI-857: layout-valid — see `stand_in_requirement`.
            let placeholder = self.stand_in_requirement(p, p)?;
            requirements.push((self.fields.req_self, placeholder));
            for (name, dict) in names.iter().zip(chain_dicts) {
                requirements.push((*name, dict));
            }
        }
        self.invoke_op_with_requirements(sym, args, requirements)
    }

    /// WI-818 (review): the ONE classifier for "this call target cannot run",
    /// shared by the host-entry direct path
    /// ([`Self::invoke_op_with_requirements`]) and the in-body dispatch
    /// fall-through (`dispatch_resolved_operation`), so the two paths report
    /// the SAME verdict for the same target and cannot drift:
    ///   - a DECLARED operation (it has an `OperationInfo` signature) with no
    ///     runnable backing → [`EvalError::OperationBodyMissing`], qualified —
    ///     a missing implementation, not an unknown name;
    ///   - anything else (a sort, an entity, a rule label, a truly unknown
    ///     symbol) → [`EvalError::UnknownOperation`].
    ///
    /// Presence-only signature probe + `Backtrace::capture()` (env-gated), not
    /// a full record build + `force_capture`: the dispatch fall-through sits
    /// on a path the resolver bridge hits speculatively per candidate and
    /// residualizes (`bridge_op_to_eval`), where an unconditional stack walk
    /// and six discarded Vec clones per probe are pure cost.
    pub(crate) fn unrunnable_target_error(&self, sym: Symbol) -> EvalError {
        if crate::kb::op_info::operation_is_declared(&self.kb, sym) {
            EvalError::OperationBodyMissing {
                name: self.kb.qualified_name_of(sym).to_string(),
                backtrace: std::backtrace::Backtrace::capture(),
            }
        } else {
            EvalError::UnknownOperation {
                name: self.kb.qualified_name_of(sym).to_string(),
            }
        }
    }

    /// Shared body of [`Self::call`] and [`Self::call_with_requirements`]:
    /// validate arity, build the frame's locals, push, run.
    fn invoke_op_with_requirements(
        &mut self,
        sym: Symbol,
        args: &[Value],
        requirements: smallvec::SmallVec<[(Symbol, value::Dictionary); 2]>,
    ) -> Result<Value, EvalError> {
        // WI-1057 — `sym` and `requirements` are REBOUND rather than passed to a
        // recursive call. When the body-less arm below dispatches value-directed, the
        // impl it picks is run by falling through to the frame push at the BOTTOM OF
        // THIS SAME FUNCTION. Re-entering `invoke_op_with_requirements` reads
        // identically and costs one more native frame per crossing on a path with no
        // room for one: this entry is what `bridge_op_to_eval` calls, and the eval↔SLD
        // ping-pong nests real Rust frames per crossing up to `BRIDGE_REENTRY_CAP`.
        //
        // THIS IS A MEASURED STACK BUDGET, not a style preference.
        // `wi625…::eval_undecidable_instance_fact_eq_is_loud_not_false` is the
        // circular-`eq` fixture that exhausts that cap, and it is this path's canary:
        // at the old cap of 32 it already needed essentially all of libtest's default
        // 2 MiB thread stack, the recursive spelling of this arm pushed it past 2.6
        // MiB, and the whole `wi_tests` binary died with `fatal runtime error: stack
        // overflow` — 2463 tests reported as nothing. The cap is now 16 (see
        // `BRIDGE_REENTRY_CAP`, which records all three measurements). Nothing on this
        // path may grow without re-measuring that test under `RUST_MIN_STACK`.
        let mut requirements = requirements;
        let (sym, body_term, params) = match self.cached_operation_body(sym) {
            Some((body, params)) => (sym, body, params),
            None => {
                // WI-1057 — the VALUE-DIRECTED escape, matching the in-body dispatch
                // fall-through (step 3b of `dispatch_resolved_operation`) in ORDER and
                // in READER: `resolve_spec_op_target_by_value` is WI-842's collected
                // supplier set, which refuses a tie rather than picking by route
                // order, and the `!= sym` filter rejects the INHERITED SELF-ENTRY that
                // a body-less spec op's own `sort_ops` row points back at.
                //
                // Without it the two faces disagreed about one call: an OPERATION BODY
                // reached a WI-431 instance-fact supplier through step 3b, while this
                // entry — the one the resolver's `bridge_op_to_eval` calls — answered
                // `OperationBodyMissing`. That is why a RULE BODY could not reach a
                // fact-route supplier: such a supplier writes no typer pin
                // (`dispatch_spec_op_cached` does not read instance-fact op-bindings,
                // WI-431 inc 2), so it is discoverable BY VALUE alone, and this was
                // the one crossing that never looked.
                let impl_target = self
                    .resolve_spec_op_target_by_value(sym, args)?
                    .filter(|t| *t != sym);
                let runnable = match impl_target {
                    Some(t) => {
                        if let Some(builtin) = self.builtins.get(&t).cloned() {
                            return (builtin)(self, args);
                        }
                        self.cached_operation_body(t)
                            .map(|(body, params)| (t, body, params))
                    }
                    None => None,
                };
                match runnable {
                    Some((t, body, params)) => {
                        // WI-822 leg 2, as at step 3b: the impl's OWN `requires` chain,
                        // resolved at the runtime argument types.
                        //
                        // The incoming channel is DISCARDED here, and that is the one
                        // place this site cannot copy step 3b. There, `requirements` is
                        // the CALL's channel and is EMPTY for the abstract call that
                        // reached value-direction — which is the case
                        // `requirements_for_value_directed_impl` fills; it returns a
                        // non-empty channel untouched, on the premise that a caller who
                        // built one "knew the callee". At a HOST ENTRY that premise is
                        // false: `call_op_sym` seeds `__req_self` for any op with a
                        // parent sort, and `call_op_bridged` resolves the chain of the
                        // SPEC op — both keyed to the sort we are dispatching AWAY from,
                        // carrying none of the impl's own `__req_<spec>` names. Passing
                        // it through would silence leg 2 at every host entry and enter a
                        // conditional impl (`WrapDesc requires Desc[T = E]`) with a
                        // channel its first dictionary read cannot satisfy.
                        // WI-1091: `built_for` is `t` itself, since the channel handed
                        // in is EMPTY — this site discards the incoming one for the
                        // reason above, so there is no other operation's supply here to
                        // re-key. The two arguments coincide and the short-circuit is
                        // not reached either way.
                        requirements = self.requirements_for_value_directed_impl(
                            t,
                            t,
                            args,
                            smallvec::SmallVec::new(),
                        )?;
                        (t, body, params)
                    }
                    // Nothing runnable came back — fall through to the classifiers
                    // below, which is exactly what step 3b does.
                    //
                    // WI-625 (eval→SLD bridge): a host-invoked body-less carrier `eq`
                    // op (e.g. `Set.eq`/`Map.eq` resolved from a dictionary — gap 4)
                    // has no body to run, but the SLD resolver can prove it. The
                    // host-entry twin of the in-body dispatch bridge; anything else
                    // classifies through the shared [`Self::unrunnable_target_error`]
                    // (WI-818): a declared op is a loud `OperationBodyMissing`, a
                    // resolvable NON-operation (a sort, an entity, a rule label) is
                    // `UnknownOperation` — not a missing-body claim about something
                    // that never was an operation.
                    None => match self.eq_bridge_target(sym, args) {
                        Some(pred) => return self.prove_rule_predicate_value(pred, args),
                        None => return Err(self.unrunnable_target_error(sym)),
                    },
                }
            }
        };
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
        self.step_count = 0;
        self.recent_dispatches.clear();
        self.stack.push(Frame {
            op: sym,
            expr: body_term,
            locals,
            requirements,
            type_args: smallvec::SmallVec::new(),
            awaiting: None,
        })?;
        let result = self.run();
        if self.profiling {
            self.dump_profile(sym);
        }
        result
    }

    /// Dump the exact operation/builtin profile collected during the last
    /// top-level run (env `ANTHILL_PROFILE`). Clears the counters so a
    /// subsequent top-level call starts fresh.
    fn dump_profile(&self, entry: Symbol) {
        eprintln!(
            "[profile] entry={} total-reductions={}",
            self.kb.qualified_name_of(entry),
            self.step_count,
        );
        eprintln!("[profile] top operations (by self-reductions):");
        for (sym, (calls, steps)) in drain_top(&eval::OP_PROF, 20) {
            eprintln!(
                "[profile]   {:<46} self-reductions={:<9} calls={}",
                self.kb.qualified_name_of(sym),
                steps,
                calls,
            );
        }
        eprintln!("[profile] top builtins (by wall time):");
        for (sym, (calls, nanos)) in drain_top(&eval::BUILTIN_PROF, 15) {
            eprintln!(
                "[profile]   {:<46} {:>8.3}ms  calls={}",
                self.kb.qualified_name_of(sym),
                nanos as f64 / 1.0e6,
                calls,
            );
        }
    }

    /// Build the initial `frame.requirements` for an entry-point call.
    /// Per WI-234 / Model 1 the layout is: slot 0 = Self (the entry op's
    /// parent sort), slots 1..=N = one per entry in the parent's flattened
    /// `requires` chain. Both Self and chain entries are self-referential
    /// STAND-INS over `parent_sort` — adequate for same-sort recursion but
    /// mis-dispatching when the parent's `requires` clause names a different
    /// sort. Cross-sort entries should use [`Self::call_with_requirements`].
    ///
    /// WI-857: a stand-in is `functor = parent_sort` with
    /// `dict_layout(..).arity()` `NoProvider` marker sub-slots, NOT the empty
    /// `sub_requires` it once had — see [`Self::stand_in_requirement`] for why
    /// the empty form is a claim the layout reads as false.
    ///
    /// WI-822 LEG 1 — THE OP-SCOPED HALF IS DELIBERATELY NOT SEEDED. An entry op's own
    /// `requires` (`Holder.probe requires Desc[HT]`) names frame slots too, but a
    /// stand-in for one would be rooted at the PARENT SORT — `Holder`, which provides
    /// no `Desc` — so a body reading it would dispatch through a dictionary that
    /// answers for nothing. That is the mis-dispatch this function's own doc warns
    /// about for a cross-sort sort-level `requires`, and here there is no
    /// `call_with_requirements` escape: the host passes VALUES, and the element type
    /// an op-scoped requirement ranges over is not among them. Value-direction is what
    /// serves this route (MEASURED: `wi842_bracketless_readers_test` calls
    /// `Holder.probe(leaf())` straight from the host and gets its answer), and a body
    /// that genuinely needs the dictionary raises at the read naming the frame.
    fn seed_entry_requirements(
        &mut self,
        op_sym: Symbol,
    ) -> Result<smallvec::SmallVec<[(Symbol, value::Dictionary); 2]>, EvalError> {
        let Some(parent_sym) = crate::kb::typing::impl_parent_of_op(&self.kb, op_sym) else {
            return Ok(smallvec::SmallVec::new());
        };
        // WI-1033: the names come OFF the chain, so the zip below cannot pair a
        // dictionary chain with a declared-chain naming (WI-869 did exactly that at
        // four producers). WI-657(12): no owned clone — only `required_sort` is read.
        let chain = crate::kb::typing::provider_dict_entries(&mut self.kb, parent_sym);
        let names = chain.names(&mut self.kb);
        let mut out: smallvec::SmallVec<[(Symbol, value::Dictionary); 2]> =
            smallvec::SmallVec::with_capacity(names.len() + 1);
        let self_slot = self.stand_in_requirement(parent_sym, parent_sym)?;
        out.push((self.fields.req_self, self_slot));
        // `names` and `chain` are ONE `DictChain`, so the zip cannot truncate — that is
        // now a property of the type rather than of these two lines being adjacent.
        // (`expand_dispatching_dict` still checks its analogous pair at runtime, because
        // there the two sides come from DIFFERENT symbols, bridged by canonicalization.)
        for (name, entry) in names.iter().zip(chain.iter()) {
            let slot = self.stand_in_requirement(entry.required_sort, parent_sym)?;
            out.push((*name, slot));
        }
        Ok(out)
    }

    /// WI-1091 — the entry op's OWN op-scoped slots, resolved at the concrete argument
    /// types, appended after [`Self::seed_entry_requirements`]' sort half.
    ///
    /// A host `interp.call` is one of the four routes WI-822 measured as unable to fill
    /// an op slot: there is no call site to build one, and a STAND-IN cannot serve it
    /// (it is rooted at the PARENT SORT, which provides nothing the op-scoped clause
    /// names, so it would mis-dispatch — that is why the sort half's stand-ins are not
    /// simply extended). But the route is not information-free: the host handed us
    /// GROUND VALUES, and an op-scoped requirement ranges over the operation's own
    /// parameters, so they pin it. That is literally the bridge's problem — "concrete
    /// op, real argument values, no caller dictionary" — so it is the bridge's
    /// resolution, [`crate::kb::typing::resolve_bridge_requirements`], shared with
    /// WI-625 and WI-822 LEG 2.
    ///
    /// BEST-EFFORT, and the sort half is untouched by a failure here: an op-scoped
    /// element the arguments cannot pin leaves its slot ABSENT, which is what every
    /// other producer of this channel does ([`super::eval::Interpreter`]'s
    /// `push_op_scoped_slots`), and the body's own read is what reports it. Only the OP
    /// half is taken out of the resolution — the sort half's stand-ins are already in
    /// `out`, and replacing them with resolved dictionaries would change what a
    /// requires-carrying entry op has always been given.
    fn seed_entry_op_requirements(
        &mut self,
        op_sym: Symbol,
        args: &[Value],
        out: &mut smallvec::SmallVec<[(Symbol, value::Dictionary); 2]>,
    ) -> Result<(), EvalError> {
        use crate::kb::typing::BridgeRequirements;
        let chain = crate::kb::typing::op_dict_entries(&mut self.kb, op_sym);
        let sort_len = chain.sort_len();
        let names = chain.names(&mut self.kb);
        if sort_len >= names.len() {
            // No op half — the universal case, and not even a resolution.
            return Ok(());
        }
        let op_names: std::collections::HashSet<Symbol> =
            names[sort_len..].iter().copied().collect();
        let (parent, trees) =
            match crate::kb::typing::resolve_bridge_requirements(&mut self.kb, op_sym, args) {
                BridgeRequirements::Resolved(parent, trees) => (parent, trees),
                // WI-1091 — A TIE IS RAISED, not entered-unsupplied, and this is the same
                // rule `requirements_for_value_directed_impl` applies to the sort half
                // (WI-855): a tie is a coherence verdict with no earlier owner, so the
                // route that finds it is the one that must report it. Entering unsupplied
                // would turn a message naming the requirement and both providers into the
                // frame-naming `not bound` at the read, which names neither — and a HOST
                // ENTRY is precisely a route with no bracket channel to decide it.
                // …AND ONLY WHERE THE TIED SLOT IS ONE OF THIS FUNCTION'S. A tie in the
                // SORT half is not the op half's verdict to raise: `seed_entry_
                // requirements` has already installed that half's stand-ins, the host
                // entry never asked this function about it, and raising would fail an
                // entry that used to run. Its own consumer —
                // `requirements_for_value_directed_impl`, which supplies both halves —
                // still raises on either (found by /code-review; the doc above claimed
                // "only the OP half is taken out of the resolution" while the code
                // raised for both).
                BridgeRequirements::Ambiguous {
                    requirement,
                    candidates,
                    slot,
                } if op_names.contains(&slot) => {
                    return Err(EvalError::AmbiguousRequirement {
                        op: self.kb.qualified_name_of(op_sym).to_string(),
                        requirement,
                        candidates,
                    })
                }
                // Unresolvable / nothing needed: enter with the sort half alone. "Has a
                // chain" and "needs it" are different questions and only the body answers
                // the second; a body that DOES read the absent slot raises at the read.
                _ => {
                    if self.trace_requirements {
                        eprintln!(
                            "[req] host entry to `{}`: op-scoped slots NOT seeded — the \
                             argument types do not pin them",
                            self.kb.qualified_name_of(op_sym),
                        );
                    }
                    return Ok(());
                }
            };
        let seeded = self.frame_requirements_from_trees(parent, &trees).map_err(|f| {
            EvalError::Internal(match f {
                FrameReqFailure::CallerScopeSlot(name) => format!(
                    "entry `{}`: requirement `{}` resolved to a caller-scope slot, but \
                     the resolution ran with no scope",
                    self.kb.qualified_name_of(op_sym),
                    self.kb.local_name_of(name),
                ),
                FrameReqFailure::NoDictionarySort => format!(
                    "entry `{}`: cannot build any requirement dictionary — this KB never \
                     loaded `anthill.realization.runtime.Dictionary`",
                    self.kb.qualified_name_of(op_sym),
                ),
            })
        })?;
        out.extend(seeded.into_iter().filter(|(n, _)| op_names.contains(n)));
        Ok(())
    }

    /// WI-857 — a **stand-in** dictionary for `spec` under the functor `functor`:
    /// layout-valid (its bundled count is `dict_layout(spec, functor).arity()`) with
    /// every sub-slot a `NoProvider` marker, since a stand-in has no evidence for
    /// any of them.
    ///
    /// Producers of a dictionary must produce a layout-valid one — that is the
    /// invariant the arity cross-check enforces, and this is what lets a stand-in
    /// satisfy it without pretending to carry evidence. The stand-ins are the host
    /// entry points' self-referential slots ([`Self::seed_entry_requirements`],
    /// [`Self::call_with_requirements`]'s `__req_self`): adequate for same-sort
    /// recursion, and for a cross-sort `requires` they dispatch onto the spec's own
    /// op, whose value-directed resolution reads the real carrier (WI-350/WI-822).
    /// Before this they were `functor` with NO sub-slots, which the layout reads as
    /// a dictionary claiming `functor`'s whole `requires` chain and bundling none.
    fn stand_in_requirement(
        &mut self,
        spec: Symbol,
        functor: Symbol,
    ) -> Result<value::Dictionary, EvalError> {
        let arity = crate::kb::typing::dict_layout(&mut self.kb, spec, functor).arity();
        if arity == 0 {
            // The common `__req_self` case. Short-circuited so a requires-free sort
            // does not build a marker dictionary per frame entry and discard it.
            return self.build_dictionary(functor, []);
        }
        // ONE marker value, SHARED across the sub-slots: they are empty and
        // interchangeable, and a dictionary's children are `Rc`-backed, so sharing
        // is a refcount bump exactly as the arena's shared slot was.
        let marker = self.build_dictionary(self.fields.no_provider, [])?;
        self.build_dictionary(functor, std::iter::repeat_n(marker, arity))
    }

    /// WI-1045 — build `Dictionary(subs…, impl: impl_sort)`, the ONE way eval
    /// produces a dictionary. Delegates to the shared
    /// [`value::Dictionary::build`], so eval and the resolver spell the shape in
    /// one place.
    ///
    /// LOUD, not silent: a KB that never loaded `anthill.realization.runtime` has
    /// no name for a dictionary to carry, and answering with some other shape
    /// would put a value into `frame.requirements` that no reader can read.
    pub(crate) fn build_dictionary(
        &self,
        impl_sort: Symbol,
        subs: impl IntoIterator<Item = value::Dictionary>,
    ) -> Result<value::Dictionary, EvalError> {
        value::Dictionary::build(&self.kb, impl_sort, subs).ok_or_else(|| {
            EvalError::Internal(format!(
                "cannot build a requirement dictionary for `{}`: this KB never loaded \
                 `anthill.realization.runtime.Dictionary`",
                self.kb.qualified_name_of(impl_sort),
            ))
        })
    }

    /// Override the activation-stack depth cap. Kept as a convenience wrapper
    /// over `config_mut()` for tests that only care about the depth limit.
    pub fn set_stack_depth_cap(&mut self, cap: usize) {
        self.config.depth_cap = Some(cap);
        self.stack.set_cap(cap);
    }

    /// Number of live stream-arena slots. Diagnostic for refcount tests.
    pub fn stream_arena_live_count(&self) -> usize {
        self.streams.live()
    }

    /// Number of live substitution-arena slots. Diagnostic for refcount tests.
    pub fn subst_arena_live_count(&self) -> usize {
        self.substs.live()
    }

    /// Number of live map-arena slots. Diagnostic for refcount tests.
    pub fn map_arena_live_count(&self) -> usize {
        self.maps.live()
    }

    /// Allocate a fresh map slot and return a handle.
    pub fn alloc_map(&self, body: map_arena::MapBody) -> value::MapHandle {
        self.maps.alloc(body)
    }

    /// Run `f` with a shared reference to the map body behind `h`.
    pub fn with_map<R>(&self, h: &value::MapHandle, f: impl FnOnce(&map_arena::MapBody) -> R) -> R {
        self.maps.with_body(h, f)
    }

    /// Clone the map-arena handle. Same rationale as `subst_arena()`.
    pub fn map_arena(&self) -> MapArenaRef {
        self.maps.clone()
    }

    /// Number of live cell-arena slots. Diagnostic for refcount tests.
    pub fn cell_arena_live_count(&self) -> usize {
        self.cells.live()
    }

    /// Build `Dictionary(subs…, impl: functor)` — the host/test-facing face of
    /// [`Self::build_dictionary`]. `None` in a KB with no
    /// `anthill.realization.runtime.Dictionary` to name.
    pub fn alloc_requirement(
        &self,
        functor: Symbol,
        requirements: impl IntoIterator<Item = value::Dictionary>,
    ) -> Option<value::Dictionary> {
        value::Dictionary::build(&self.kb, functor, requirements)
    }

    /// Test-only: read a closure's snapshotted `requirements` channel.
    /// Used to verify that lambda construction captures the enclosing
    /// frame's requirements (acceptance #4 of WI-223).
    #[doc(hidden)]
    pub fn closure_requirements_for_test(
        &self,
        h: &value::ClosureHandle,
    ) -> smallvec::SmallVec<[(Symbol, value::Dictionary); 1]> {
        self.closures.with(h, |c| c.requirements.clone())
    }

    /// Test-only: snapshot the top frame's operation type-arg
    /// channel. Acceptance fixtures observe what the eval installed
    /// on `Frame.type_args` after a call entry (WI-272). Empty when
    /// the stack is empty or the top frame has no type params.
    #[doc(hidden)]
    pub fn top_frame_type_args_for_test(&self) -> FrameTypeArgs {
        self.stack
            .top()
            .map(|f| f.type_args.clone())
            .unwrap_or_default()
    }

    /// Test-only entry point: drive a single expression as the body of an
    /// ad-hoc operation, with `frame.requirements` pre-seeded. Used to
    /// verify the WI-223 requirement IR reductions
    /// (`requirement_at_current` / `requirement_at_sort` /
    /// the `Dictionary` node) before WI-222's rewrite pass produces them
    /// from real call sites.
    #[doc(hidden)]
    pub fn run_with_requirements(
        &mut self,
        expr: crate::kb::term::TermId,
        requirements: smallvec::SmallVec<[(Symbol, value::Dictionary); 2]>,
    ) -> Result<Value, EvalError> {
        let op = self.kb.intern("__test_requirement_eval");
        self.step_count = 0;
        self.recent_dispatches.clear();
        // Test-entry materializes a NodeOccurrence from the test's
        // legacy Term::Fn input. The materializer handles both Handle-
        // wrapped trees (loader output) and naked Fn shapes (test
        // construction); see materialize_from_handle for the fallback.
        let expr_node = crate::kb::node_occurrence::materialize_from_handle(&self.kb, expr);
        self.stack.push(Frame {
            op,
            expr: expr_node,
            locals: smallvec::SmallVec::new(),
            requirements,
            type_args: smallvec::SmallVec::new(),
            awaiting: None,
        })?;
        self.run()
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
    /// Resolver yields land as a reflect `Solution` value (WI-531) —
    /// `definite(subst)` or `undecided(subst, residual)` — built by
    /// [`Self::make_solution_value`]. `subst` is a `Value::Substitution`
    /// handle into the per-interpreter arena (read via `Substitution.lookup` /
    /// `.apply`); the floundered `undecided` case additionally carries the
    /// undischarged goals as a `List[Term]`, so the residual is no longer
    /// silently dropped here.
    pub fn stream_split_first(
        &mut self,
        handle: &value::StreamHandle,
    ) -> Result<Option<(Value, value::StreamHandle)>, EvalError> {
        use stream::StreamSource;
        enum Action {
            Done,
            YieldSelf(Value),
            PumpResolver(crate::kb::resolve::SearchStream),
            // WI-714: pump the resolver one step, then MATERIALIZE the yielded
            // Solution onto `columns` into a named-tuple row (see below).
            PumpMaterialized {
                search: crate::kb::resolve::SearchStream,
                columns: std::rc::Rc<[(crate::intern::Symbol, crate::kb::term::VarId)]>,
            },
            PumpLeft {
                left: value::StreamHandle,
                right: value::StreamHandle,
            },
        }

        let arena = self.streams.clone();
        let action = arena.with_source_mut(handle, |src| match src {
            StreamSource::Empty => (StreamSource::Empty, Action::Done),
            StreamSource::Resolver(None) => (StreamSource::Resolver(None), Action::Done),
            StreamSource::Resolver(Some(stream)) => {
                (StreamSource::Resolver(None), Action::PumpResolver(stream))
            }
            // WI-714: a materializing resolver — same pump lifecycle as `Resolver`
            // (take the `SearchStream`, leave `None` transiently), but its yielded
            // element is the materialized named-tuple row, not the raw `Solution`.
            StreamSource::MaterializedResolver {
                search: None,
                columns,
            } => (
                StreamSource::MaterializedResolver {
                    search: None,
                    columns,
                },
                Action::Done,
            ),
            StreamSource::MaterializedResolver {
                search: Some(stream),
                columns,
            } => (
                StreamSource::MaterializedResolver {
                    search: None,
                    columns: columns.clone(),
                },
                Action::PumpMaterialized {
                    search: stream,
                    columns,
                },
            ),
            StreamSource::Pure(mut slot) => match slot.take() {
                Some(v) => (StreamSource::Empty, Action::YieldSelf(v)),
                None => (StreamSource::Empty, Action::Done),
            },
            StreamSource::MPlus { left, right } => (
                StreamSource::MPlus {
                    left: left.clone(),
                    right: right.clone(),
                },
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
                        stream_arena
                            .with_source_mut(handle, |_| (StreamSource::Resolver(Some(rest)), ()));
                        let solution = self.make_solution_value(sol)?;
                        Ok(Some((solution, handle.clone())))
                    }
                    None => {
                        stream_arena.with_source_mut(handle, |_| (StreamSource::Empty, ()));
                        Ok(None)
                    }
                }
            }
            Action::PumpMaterialized { search, columns } => {
                // WI-714: pump one resolver step, then materialize the answer onto
                // the relation's free variables (`columns`) — the one place a
                // relation solution becomes a value row.
                let result = search.split_first(&mut self.kb);
                let stream_arena = self.streams.clone();
                match result {
                    Some((sol, rest)) => {
                        let cols = columns.clone();
                        stream_arena.with_source_mut(handle, move |_| {
                            (
                                StreamSource::MaterializedResolver {
                                    search: Some(rest),
                                    columns: cols,
                                },
                                (),
                            )
                        });
                        let row = self.materialize_solution(sol, &columns)?;
                        Ok(Some((row, handle.clone())))
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
                        (
                            StreamSource::MPlus {
                                left: left_rest,
                                right: right.clone(),
                            },
                            (),
                        )
                    });
                    Ok(Some((v, handle.clone())))
                }
                None => self.stream_split_first(&right),
            },
        }
    }

    /// WI-531: wrap a resolver [`Solution`](crate::kb::resolve::Solution) as a
    /// reflect `Solution` value. A *definite* solution (empty residual) becomes
    /// `definite(subst)`; a *floundered* one becomes `undecided(subst,
    /// residual)`, carrying its undischarged goals as a `List[Term]` so anthill
    /// consumers (the WI-010 self-hosted type resolver) can inspect WHICH goals
    /// stayed pending — keeping reflect a faithful description of the core.
    /// Undecidedness is a third logical outcome carried as DATA, never raised
    /// on `execute`'s `E = Error` channel.
    ///
    /// WI-737 — the DATA half of a deliberate split; the raising half is
    /// [`Self::materialize_solution`]. This RAW face can afford a third outcome
    /// because `Solution` is an enum with an `undecided` arm to carry it. The TYPED
    /// Relation face cannot: `Relation[T]` promises rows of `T`, and `T` has no such
    /// arm — so there a floundered answer RAISES rather than materializing a row
    /// that would hold a logic variable in a typed column. Same fact, two faces, each
    /// as honest as its type allows.
    fn make_solution_value(
        &mut self,
        sol: crate::kb::resolve::Solution,
    ) -> Result<Value, EvalError> {
        let definite = sol.is_definite();
        // Resolve the variant functor BEFORE allocating into the subst arena, so
        // a missing-stdlib early-return can't strand a freshly-allocated slot.
        let functor = if definite {
            self.reflect.solution_definite
        } else {
            self.reflect.solution_undecided
        }
        .ok_or_else(|| {
            EvalError::Internal(
                "anthill.reflect.Solution not loaded — stdlib missing the Solution enum".into(),
            )
        })?;
        let residual = sol.residual;
        let subst_value = Value::Substitution(self.substs.alloc(sol.subst));
        let mut named = if definite {
            vec![(self.fields.subst, subst_value)]
        } else {
            // Carrier-faithful (WI-348): the residual goals stay as their original
            // `Value`s — a goal mentioning a `Value::Node` keeps its source
            // occurrence rather than being reified to a bare `TermId` (which would
            // drop span/identity that the core deliberately preserves). Surfaced as
            // `List[Term]`: a pending goal IS a term, occurrence-carried or not, and
            // is inspected through the occurrence-aware reflect / `TermView` ops.
            let residual_list = self.build_list_value(residual, &[])?;
            vec![
                (self.fields.subst, subst_value),
                (self.fields.residual, residual_list),
            ]
        };
        // Canonical (declared) field order — mirrors `finish_constructor` — so a
        // positional pattern (`case undecided(subst, residual)`) binds the right
        // field; `subst`/`residual` are NOT in alphabetical order.
        self.kb.canonicalize_record_named_args(functor, &mut named);
        Ok(Value::Entity {
            functor,
            pos: Vec::new().into(),
            named: named.into(),
        })
    }

    /// WI-714 (proposal 052 §Typing 2): materialize one resolver `Solution` onto a
    /// relation's free variables — the ONE place a relation answer becomes a value
    /// row. `columns` is `(column name, free VarId)` in the relation's declaration
    /// order; each column reads its bound value out of the answer substitution (a
    /// flat lookup by `VarId`, mirroring `Substitution.lookup`; an unbound free var
    /// carries as itself, a `Value::Var`). The row is a named-tuple `Value::Tuple`,
    /// keyed by column name (order-faithful, §4.6), 1-COLLAPSED to the element value
    /// for a single column and to `Value::Unit` for zero (a boolean/membership
    /// relation — non-empty ⇔ provable). NotFound is just the empty stream, no
    /// bespoke nil arm.
    ///
    /// WI-737 — a FLOUNDERED answer does not materialize: it RAISES. A `Relation[T]`
    /// promises rows of `T`, and `T` has no room for a third "undecided" outcome, so
    /// a solution the search never DECIDED has no honest row. Materializing it anyway
    /// told two lies: a column typed `Int64` came back holding `Var(Global(…))` — a
    /// type-level lie in the very face built to REPLACE raw `Substitution` walking
    /// with typed rows — and a 0-column membership answer came back `unit`, reading a
    /// floundered residual as a positive membership answer. Both are the hazard
    /// [`relation_negate`](crate::eval::builtins) already refused to risk locally, and
    /// the residual honesty (WI-519) that `make_solution_value` and anthill-todo's
    /// hand-written `case undecided(_, _)` walk both keep — this face had silently
    /// lost it. `E ⊇ {Error}` on every relation already, so the raise is in the type.
    ///
    /// THE SPLIT this settles: the RAW reflect / `LogicalStream` face keeps
    /// undecidedness as DATA ([`Self::make_solution_value`] reifies `undecided(subst,
    /// residual)`, never raised on `execute`'s `E` channel, so WI-010's self-hosted
    /// resolver can inspect which goals stayed pending); the TYPED Relation face
    /// raises. Same fact, two faces — the honest split, not a divergence. Mirrored on
    /// `anthill.prelude.RelationFloundered` in `stdlib/anthill/prelude/effects.anthill`.
    ///
    /// The gate is on the SOLUTION (`is_definite`), and deliberately says nothing about
    /// the stream-level WI-628 `truncated` flag: truncation is a property of the SEARCH,
    /// not of this answer, and its danger point is stream EXHAUSTION (where "no more
    /// rows" is the lie an `isEmpty` reads as refutation), not materialization. That is
    /// the filed WI-628 eager-consumer hole — the same shape as a constraint guard
    /// reading `is_empty()` as a refutation — and it belongs there, uniformly, rather
    /// than bolted onto this message. (`split_first` consumes the stream on exhaustion
    /// and drops `truncated` outright, so it is not a message-wording choice here but a
    /// separate structural fix.)
    fn materialize_solution(
        &mut self,
        sol: crate::kb::resolve::Solution,
        columns: &[(crate::intern::Symbol, crate::kb::term::VarId)],
    ) -> Result<Value, EvalError> {
        use crate::kb::term::Var;
        // WI-737: gate BEFORE the zero-column early return — a membership relation is
        // exactly where a floundered residual would otherwise read as `unit`, a
        // positive answer to a question the search never decided.
        if !sol.is_definite() {
            return Err(self.raise_relation_floundered(sol.residual));
        }
        // Zero free variables → Unit (membership relation).
        if columns.is_empty() {
            return Ok(Value::Unit);
        }
        let mut named: Vec<(crate::intern::Symbol, Value)> = Vec::with_capacity(columns.len());
        for &(name, vid) in columns {
            // Read the binding through `resolve_as_value` — the single canonical
            // substitution reader (WI-348), which chases the PARENT frame chain. A
            // plain `bindings` scan would miss a binding held in a parent frame and
            // wrongly report the column unbound. The resolver binds a var to a
            // hash-consed `Value::Term`; REIFY it to a native value (scalar const →
            // scalar Value, constructor → entity) so the column reads as its element
            // sort, not a raw Term handle — a `Relation[String]` yields `Value::Str`,
            // a `Relation[Board]` an entity.
            //
            // An unbound free var still carries as itself. Post-WI-737 this is no
            // longer the flounder path (that raised above) but the narrower DEFINITE-
            // yet-unbound one: a head var no body goal constrains (`rule p(?x) :-
            // num(v: 1)`) yields a residual-FREE answer that genuinely binds nothing —
            // logically "for all x", a range-restriction violation Datalog rejects at
            // load time. Still a var in a typed column, so still a lie; but it is a
            // STATIC property of the rule, not an undecided search, so it wants a
            // load-time check rather than this drain-time gate. Not WI-737's scope.
            let bound = match sol.subst.resolve_as_value(vid).cloned() {
                Some(Value::Term { id, .. }) => crate::eval::builtins::term_to_value(self, id),
                Some(v) => v,
                None => Value::Var(Var::Global(vid)),
            };
            named.push((name, bound));
        }
        // One free variable → the element value (1-collapse).
        if named.len() == 1 {
            return Ok(named.pop().unwrap().1);
        }
        // A named tuple is an ORDERED PRODUCT — its field order IS the relation
        // schema (§4.6). So, unlike `make_solution_value` (which canonicalizes a
        // Solution ENTITY into its declared field order), the row is built in
        // column / declaration order and deliberately NOT re-sorted by field name.
        Ok(Value::Tuple {
            pos: Vec::<Value>::new().into(),
            named: named.into(),
        })
    }
}

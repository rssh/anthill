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
mod instance;
pub mod layer_arena;
pub mod map_arena;
pub mod pattern;
pub(crate) mod reflect_builtins;
pub mod stream;
pub mod subst_arena;
pub mod value;

use std::collections::HashMap;

use crate::intern::Symbol;
use crate::kb::KnowledgeBase;
use crate::parse::desugar_target as dt;

pub use error::{
    macro_rejection_message, render_raised_payload, BridgeDisposition, EvalError, HandlerErrorReason,
    RaisePoint, RaisedType, ThrowRoute, UnrunnableHostBinding, UnrunnableHostBindingWhy,
};
pub use eval::{type_value_decl, value_functor};
pub use frame::{ActivationStack, Frame};
pub use value::Value;

use cell_arena::CellArenaRef;
use closure::ClosureArenaRef;
use effects::EffectRegistry;
use map_arena::MapArenaRef;
use stream::StreamArenaRef;

/// Proposal 074 §1.4 — a value a host holds, with its anthill type. A host call is typed as the
/// same call written in a body is ([`Interpreter::call`]), so a value keeps the type it was
/// produced at across the host: `mk() -> MySet[T = String, O = ByLength]` hands back its set at
/// that type, and `has(s, "aa")` called with it reads `s.O = ByLength` off it, as a typed caller
/// reads it off `s`'s type. The type travels beside the value on the host's side; no value
/// inside the run holds one (073 §6.2).
///
/// A value the host builds itself is at the type its value reads as
/// ([`HostValue::from`]): `2` at `Int64`, a list at its elements' type. Where its value says
/// less than its type — a symbol value, a set's ordering — the host gives the type
/// ([`HostValue::typed`]).
#[derive(Clone, Debug)]
pub struct HostValue {
    pub value: Value,
    ty: Option<Value>,
}

impl HostValue {
    /// `value` at `ty`.
    pub fn typed(value: Value, ty: Value) -> Self {
        HostValue { value, ty: Some(ty) }
    }

    /// The type the value is held at; `None` for a value at the type its value reads as,
    /// which the call reads off it.
    pub fn ty(&self) -> Option<&Value> {
        self.ty.as_ref()
    }

    /// Each of `values` at the type its value reads as.
    pub fn all(values: &[Value]) -> Vec<HostValue> {
        values.iter().cloned().map(HostValue::from).collect()
    }
}

impl From<Value> for HostValue {
    /// `value` at the type its value reads as.
    fn from(value: Value) -> Self {
        HostValue { value, ty: None }
    }
}

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
///
/// WI-20260827-1ZG70 — TWO KINDS, told apart by the SIGNATURE, so what a function is
/// handed cannot disagree with what it was written to handle. Groundness is a property
/// of an argument; this is one of the function: whether it can be handed a variable of
/// the caller's that is not filled yet, and ask ([`HostEnv`]).
#[derive(Clone)]
pub enum BuiltinFn {
    /// Never handed one of the caller's unfilled variables: [`Interpreter::call_host`]
    /// waits before calling it when any argument holds one, anywhere. Right for a function
    /// whose answer reads the whole argument — `Int64.add`, `term_to_string` — and the
    /// kind every registration gets unless it says otherwise.
    Ground(std::sync::Arc<dyn Fn(&mut Interpreter, &[Value]) -> Result<Value, EvalError>>),
    /// Handed its arguments as they are, unfilled variables included. It asks the
    /// [`HostEnv`] at each position it READS and waits there ([`HostEnv::read`]); a
    /// variable at a position it does not read it passes along, so its answer holds
    /// whatever the variable is bound to later — `term_functor_name(some(?x))` is
    /// `some("some")`, and `term_functor_name(?x)` waits.
    SeesVars(
        std::sync::Arc<dyn Fn(&mut Interpreter, &[Value], &HostEnv) -> Result<Value, EvalError>>,
    ),
}

/// What a variable-seeing host function ([`BuiltinFn::SeesVars`]) may ask of its caller:
/// is the variable at a position it reads filled? READ-ONLY — it binds nothing.
///
/// The bridge applies σ to the arguments before the call, so a variable the rule has bound
/// is its value by then, and what is still a variable of the rule's is one the rule has not
/// filled: one of [`Interpreter::bridge_unknowns`]. Outside a bridged run there are none,
/// and a variable an argument holds is the data it is (a `fresh_var()` an operation body
/// made), as it was before.
pub struct HostEnv {
    unfilled: std::rc::Rc<[crate::kb::term::VarId]>,
}

impl HostEnv {
    /// Is `v` itself one of the caller's unfilled variables — on any carrier?
    pub fn is_unfilled(&self, kb: &KnowledgeBase, v: &Value) -> bool {
        is_one_of(kb, &self.unfilled, v)
    }

    /// Read the position `v` stands at: `Err(Suspended)` when it is one of the caller's
    /// unfilled variables, so the call waits as a ground host function's does. `what`
    /// names the read, for the suspension's detail.
    pub fn read(&self, kb: &KnowledgeBase, v: &Value, what: &str) -> Result<(), EvalError> {
        if self.is_unfilled(kb, v) {
            return Err(unfilled_read(what));
        }
        Ok(())
    }
}

/// Is `v` itself one of `unknowns` (a flexible variable of the caller's)?
fn is_one_of(kb: &KnowledgeBase, unknowns: &[crate::kb::term::VarId], v: &Value) -> bool {
    use crate::kb::term_view::TermView;
    !unknowns.is_empty()
        && matches!(
            v.index_var(kb),
            Some(crate::kb::term::Var::Global(vid)) if unknowns.contains(&vid)
        )
}

/// The suspension of a read of one of the caller's unfilled variables (068 §2).
fn unfilled_read(what: &str) -> EvalError {
    EvalError::Suspended {
        detail: format!("bridge: {what} reads a variable the rule has not bound yet"),
        truncated: false,
    }
}

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
            if_expr: r(dt::qualified(dt::IF_EXPR)),
            let_expr: r(dt::qualified(dt::LET_EXPR)),
            match_expr: r(dt::qualified(dt::MATCH_EXPR)),
            lambda: r(dt::qualified(dt::LAMBDA_EXPR)),
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

            list_literal: r(dt::qualified(dt::LIST_LITERAL)),
            tuple_literal: r(dt::qualified(dt::TUPLE_LITERAL)),
            set_literal: r(dt::qualified(dt::SET_LITERAL)),
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
    /// when it pins no provider. Interned ONCE here, like every other well-known
    /// name, so eval never re-derives it.
    ///
    /// WI-865 narrowed WHICH marker this is: eval's ONE remaining producer of a marker
    /// is [`Interpreter::stand_in_requirement`]'s host-entry sub-slots, so this is
    /// that record's symbol and no other. The resolver's markers are minted per
    /// absence by `kb::typing::absence_marker_sym` and travel on the tree
    /// (`port_resolved_tree` no longer needs a marker of its own). NOTE the typer-side
    /// readers still test by NAME (`kb::typing::is_absence_marker`) because they hold
    /// only a `&KnowledgeBase`, so there are two spellings, not one; see that
    /// function for the cost.
    pub no_provider: Symbol,
    /// `__req_self` — the Self-slot requirement-param name (WI-237
    /// names model). Interned, not a stdlib symbol.
    pub req_self: Symbol,
    /// Proposal 073 §2 — `anthill.realization.runtime.Instance`, the functor of a value of
    /// an abstract type (`eval::instance`); `None` in a knowledge base without the stdlib.
    pub instance: Option<Symbol>,
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
            no_provider: crate::kb::typing::absence_marker_sym(
                kb,
                crate::kb::typing::AbsenceRecord::StandIn,
            ),
            req_self: kb.intern("__req_self"),
            instance: kb.try_resolve_symbol("anthill.realization.runtime.Instance"),
        }
    }
}

/// A typed host call's key in `Interpreter::host_calls`: the operation, the hash-consed type of
/// each argument, the bracket's entries, each its key and its type's term, and whether the host
/// vouched for the operation's preconditions ([`Interpreter::call_assuming_requires`]) — a call
/// typed under that vouching is no typing of the call a plain [`Interpreter::call`] makes, which
/// must still be refused.
type HostCallKey = (
    Symbol,
    Vec<crate::kb::term::TermId>,
    Vec<(Option<Symbol>, crate::kb::term::TermId)>,
    Preconditions,
);

/// WI-20261126-7BJGQ — who establishes a host call's value preconditions: the typing of the
/// call, as for a call written in a body ([`Interpreter::call`]), or the host, which vouches
/// for them ([`Interpreter::call_assuming_requires`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Preconditions {
    Proved,
    Vouched,
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

/// Proposal 027.4 — the `Error` monad layer: the `reify` operation the dispatch arms
/// intercept, the two `Result` constructors its boundary delivers, and what the boundary
/// catches by (proposal 071 §1.4) — the slot its `requires TypePattern[T = T1]` fills, the
/// spec operation `admits`, and the one row's provider and member.
///
/// Resolved once at construction, like [`ReflectSymbols`], for both of the
/// reasons that pattern exists: an operation's meaning is its `Symbol` and never
/// its name (WI-897), and the dispatch test sits on the per-call path, where it
/// must cost one comparison rather than a qualified-name lookup.
///
/// ALL OR NONE, AND NONE ONLY WHERE THERE IS NO `reify` — the whole struct rides an
/// `Option`, and the fields inside it do not. A half-resolved layer would be a state where
/// `reify` dispatches, the thunk RUNS (console output, cell writes, KB layers), and only at
/// delivery does a missing `Result` constructor surface — discarding the `Raised` payload
/// on the way out. A KB without the prelude declares no `reify`, and the layer is `None`.
/// One that declares it and disagrees with this layer about the rest — a `Result`
/// constructor, `TypePattern`'s operation or row, the clause `reify` requires — is a
/// standard library this evaluator was not written for, and constructing an interpreter
/// over it PANICS, naming what is missing: as `None`, `Error.reify` would be a body-less
/// operation, which the SLD bridge reads as a goal not decided yet, in silence (found by
/// /code-review).
pub(crate) struct ErrorLayer {
    pub reify: Symbol,
    pub result_ok: Symbol,
    pub result_err: Symbol,
    /// The FRAME SLOT NAME `Error.reify`'s own `requires TypePattern[T = T1]` fills
    /// (proposal 071 §1.4; WI-20260921-28TAT put the boundary's evidence on the
    /// requirement channel). The boundary takes the pattern it catches by out of THAT
    /// dictionary.
    ///
    /// RESOLVED HERE rather than spelled at the boundary: the slot name is DERIVED from
    /// the required spec's name (`op_dict_entries(reify).names()`), so it changes if the
    /// clause is rewritten or removed. Read ad hoc at the boundary, a clause deleted from
    /// `stdlib/anthill/prelude/effects.anthill` would make every boundary in the program
    /// refuse to run, naming its caller for evidence the caller was never asked for.
    pub reify_payload_slot: Symbol,
    /// `anthill.reflect.TypePattern.admits`, the API of what the boundary requires: a raise
    /// is caught where the boundary's dictionary answers it yes for the raised type
    /// ([`Interpreter::boundary_admits`]).
    pub admits: Symbol,
    /// `anthill.reflect.TypeValuePattern`, the provider of `TypePattern`'s ONE row. No other
    /// row of the spec may be written (071 §1.2), so a dictionary is a `TypePattern`
    /// instance exactly when this is its `impl` (`Interpreter::enter_reify_boundary`). A
    /// transitive "provides `TypePattern`" is not that: a sort that writes `provides
    /// TypeValuePattern[T = P]` provides `TypePattern` through it, and its own `admits`
    /// would have decided every catch (found by /code-review).
    pub pattern_provider: Symbol,
    /// The row's member that answers `admits` — the dispatch a body's
    /// `TypePattern.admits[T = T1](t)` makes through the row's dictionary
    /// (`resolve_op_target`), made once here: every boundary's dictionary has this `impl`.
    pub admits_member: Symbol,
    /// The `TypeValue` evidence of the payload sorts the RUNTIME raises a value of with no
    /// operation behind the raise to thread one (proposal 071 §1.3; user, 2026-10-24): a
    /// pattern that fails (`MatchFailed`), a relation drain that stayed undecided
    /// (`RelationFloundered`), a stream pulled past a fault or misused
    /// (`ResolveStreamFailure`). Each sort is fixed and has no type parameter, so its evidence
    /// is a constant, resolved here once from its derived row.
    pub match_failed_type: crate::eval::value::Dictionary,
    pub relation_floundered_type: crate::eval::value::Dictionary,
    pub resolve_stream_failure_type: crate::eval::value::Dictionary,
    /// The type a raise of the unknown type is asked about, and the type a pattern's open slot
    /// names at run time (`KnowledgeBase::run_time_pattern_slot`).
    pub open_slot: crate::kb::term::TermId,
}

impl ErrorLayer {
    /// `None` for a KB without the prelude — such a program declares no `reify`
    /// to call, so the boundary is simply absent rather than broken. See the type's doc for
    /// why a prelude that declares `reify` and disagrees with the rest panics.
    fn resolve(kb: &mut KnowledgeBase) -> Option<Self> {
        let reify = kb.reify_operation()?;
        let disagree = |what: &str| -> ! {
            panic!(
                "the standard library declares `anthill.prelude.Error.reify`, and this \
                 evaluator's error layer finds {what}: the library and the evaluator disagree \
                 (eval/mod.rs, `ErrorLayer`)"
            )
        };
        let r = |kb: &KnowledgeBase, qn: &str| {
            kb.try_resolve_symbol(qn)
                .unwrap_or_else(|| disagree(&format!("no `{qn}`")))
        };
        let result_ok = r(kb, "anthill.prelude.Result.ok");
        let result_err = r(kb, "anthill.prelude.Result.err");
        let pattern = r(kb, "anthill.reflect.TypePattern");
        let admits = r(kb, "anthill.reflect.TypePattern.admits");
        let pattern_provider = r(kb, "anthill.reflect.TypeValuePattern");
        // The op half's SOLE slot. `op_entries()` is `reify`'s own `requires` chain; exactly
        // one clause is declared, and taking it positionally rather than by spelling the
        // `__req_*` name keeps this in step with whatever `op_dict_entries` names it. Its
        // spec is checked: a clause rewritten to another spec would hand `admits` a
        // dictionary of something else.
        let reify_payload_slot = {
            let chain = crate::kb::typing::op_dict_entries(kb, reify);
            let sort_len = chain.sort_len();
            let [entry] = chain.op_entries() else {
                disagree("a `requires` other than the one clause `TypePattern[T = T1]`")
            };
            if kb.canonical_sort_sym(entry.required_sort) != kb.canonical_sort_sym(pattern) {
                disagree("a `requires` of a spec other than `anthill.reflect.TypePattern`")
            }
            chain
                .names(kb)
                .get(sort_len)
                .copied()
                .unwrap_or_else(|| disagree("no slot name for its `requires`"))
        };
        let account = |kb: &mut KnowledgeBase, qn: &str| {
            let sort = r(kb, qn);
            crate::kb::typing::account_type_value_evidence(kb, sort).unwrap_or_else(|| {
                disagree(&format!(
                    "no unconditional `TypeValue` row of `{qn}`, a payload the runtime raises"
                ))
            })
        };
        let match_failed_type = account(kb, "anthill.prelude.MatchFailed");
        let relation_floundered_type = account(kb, "anthill.prelude.RelationFloundered");
        let resolve_stream_failure_type = account(kb, "anthill.reflect.ResolveStreamFailure");
        let admits_member = crate::kb::typing::resolve_op_target(kb, pattern_provider, admits)
            .unwrap_or_else(|_| {
                disagree("no single member of `anthill.reflect.TypeValuePattern` that answers `admits`")
            });
        if admits_member == admits {
            disagree("no member of `anthill.reflect.TypeValuePattern` that answers `admits`");
        }
        Some(Self {
            reify,
            result_ok,
            result_err,
            reify_payload_slot,
            admits,
            pattern_provider,
            admits_member,
            match_failed_type,
            relation_floundered_type,
            resolve_stream_failure_type,
            open_slot: kb.run_time_pattern_slot(),
        })
    }
}

/// The requirement channel a builtin call carries ([`Interpreter::running_builtin`]), read
/// only where its host function raises (`Interpreter::raise_error`).
pub(crate) struct RunningBuiltin {
    /// The builtin's own operation.
    pub op: Symbol,
    /// The channel as the call handed it. Where a route built it for the spec operation a
    /// value directed the call through, its slots are named as the member's are wherever the
    /// two chains agree — a member restates its spec operation's `requires` — and a slot
    /// named otherwise reads as missing.
    pub requirements: smallvec::SmallVec<[(Symbol, value::Dictionary); 2]>,
}

/// Top-level interpreter state. Owns the KB so builtins and effect handlers
/// can mutate it; host code takes it back via `Interpreter::into_kb()` when
/// evaluation is done.
pub struct Interpreter {
    pub(crate) kb: KnowledgeBase,
    pub(crate) stack: ActivationStack,
    pub(crate) builtins: HashMap<Symbol, BuiltinFn>,
    pub(crate) reflect: ReflectSymbols,
    pub(crate) error_layer: Option<ErrorLayer>,
    /// `anthill.prelude.PartialEq.eq`, the spec operation a call reaches when no member was
    /// found for it: one no type reaches. The spec declares no implementation, and every
    /// provision of it has a member (kernel-language §8.3), so `dispatch_resolved_operation`
    /// raises such a call ([`Self::eq_with_no_member`]). Resolved once, under both
    /// spellings one qualified name can be interned with — the name's own and the
    /// declaration's — as a host registration is ([`Self::is_eq_spec_op`]).
    pub(crate) eq_spec_op: [Option<Symbol>; 2],
    /// WI-20260919-HXGXF — the dispatching DICTIONARY of the builtin currently running,
    /// or `None` outside one.
    ///
    /// A builtin is the ONE backing kind that receives no frame:
    /// `dispatch_resolved_operation` calls it as `(builtin)(self, &args)` and drops the
    /// `requirements` that `expand_dispatching_dict` just built, where every other kind
    /// gets them pushed onto a `Frame`. That is right for every builtin that existed
    /// before — an arithmetic primitive reads its operands and nothing else — and wrong
    /// for one whose ANSWER IS ITS EVIDENCE. `TypeValue.type_value[X]()` takes no argument,
    /// so nothing but the dictionary of the instance its bracket names carries the type it
    /// must return.
    ///
    /// Set and RESTORED around the builtin call, so it is a parameter in everything but
    /// spelling — a builtin that calls back into anthill (legal since
    /// WI-20260913-2858G) sees its own dictionary on the way in and the caller's again on
    /// the way out, rather than inheriting whatever ran last.
    pub(crate) builtin_dispatch_dict: Option<crate::eval::value::Dictionary>,
    /// Proposal 073 §6.1, STAGE 4'S — set while the host entry's own call is dispatched
    /// ([`Self::invoke_op_with_requirements`]). With a frame typed with no caller to pass a
    /// dictionary (`Frame::untyped`: a rule-written lambda, a reflected form) it is what
    /// `untyped_caller` reads: the dispatches where a spec operation's implementation is
    /// still found from the argument values (`dispatch_resolved_operation`'s steps 3 and 3b),
    /// until a host call passes the dictionaries its callee reads or is refused
    /// (WI-20261105-CBRD2). A call made from a typed body is decided at load and never
    /// reaches them.
    pub(crate) host_entry_dispatch: bool,
    /// Proposal 074 §1.4 — a host call typed once per operation and argument types
    /// ([`Self::call_bracketed`]): the typed call node and its result type, keyed by the
    /// operation, the hash-consed type of each argument and the call's bracket. Typing mints
    /// type terms and fresh variables, so a host calling one operation repeatedly would
    /// otherwise grow the term store per call.
    /// Only a ground key is kept: a call at a type holding a variable is typed again. Cleared
    /// where a layer is loaded or discarded, as `op_body_cache` is: a layer's provision changes
    /// what a call dispatches to.
    host_calls: HashMap<HostCallKey, (std::rc::Rc<crate::kb::node_occurrence::NodeOccurrence>, Value)>,
    /// Proposal 071 §1.3 — the requirement channel of the builtin currently running, or
    /// `None` outside one. A builtin enters no frame, and a host function that raises takes
    /// the `TypeValue` of what it raises out of this channel ([`Self::raise_error`]), as an
    /// operation body reads a slot of its frame. Set and RESTORED around the builtin call
    /// ([`Self::call_host`]), for [`Self::builtin_dispatch_dict`]'s reason.
    pub(crate) running_builtin: Option<RunningBuiltin>,
    pub(crate) fields: FieldSymbols,
    pub(crate) closures: ClosureArenaRef,
    pub(crate) streams: StreamArenaRef,
    pub(crate) substs: subst_arena::SubstArenaRef,
    pub(crate) maps: MapArenaRef,
    /// WI-SPGBP — live scoped-KB layers (`KB.loaded`). See `eval::layer_arena`.
    pub(crate) layers: layer_arena::LayerArenaRef,
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
    /// Per operation: is it a body written in a spec whose `requires` the provision taking it
    /// passes (`kb::typing::spec_body_requires_are_the_provisions`)? Asked at every frame push
    /// through a dictionary (`push_spec_body_slots`); a declaration's answer, which nothing
    /// changes while the program runs.
    pub(crate) spec_body_ops: HashMap<Symbol, bool>,
    /// Proposal 073 §2 — per `(operation of an abstract sort, member)`: the conversion of the
    /// member's result to the type a call on an instance was typed at
    /// (`kb::typing::member_result_conversion`).
    pub(crate) member_result_conversions:
        HashMap<(Symbol, Symbol), Option<crate::kb::typing::InstanceConversion>>,
    /// Proposal 073 §2 — per `(operation called, member entered)` through a dictionary: the
    /// argument positions paired with it (`Interpreter::positions_to_pair`).
    pub(crate) pair_positions: HashMap<(Symbol, Symbol), Option<smallvec::SmallVec<[usize; 2]>>>,
    pub(crate) config: EvalConfig,
    /// 068 §2 — the rule world's UNKNOWNS a bridged call was handed: the unbound logic
    /// variables of its arguments. Empty everywhere else, and then nothing below changes
    /// anything. While it is not empty the evaluation SUSPENDS where it would READ one of
    /// them — a pattern that tests it, a host function handed it, an `if` or a guard on it,
    /// a dispatch on its carrier, a call through it — and runs everywhere it only passes
    /// one along: `List.splitFirst(cons(head: f(), tail: ?t))` is `some(pair(f(), ?t))`. A
    /// variable the body makes itself is not one of them.
    pub(crate) bridge_unknowns: std::rc::Rc<[crate::kb::term::VarId]>,
    /// Set by [`pattern::match_pattern`] when a position it would test held one of
    /// `bridge_unknowns`, so its caller can tell "does not match" from "cannot tell yet".
    pub(crate) pattern_read_unknown: std::cell::Cell<bool>,
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

/// What the typer refuses about a host call, in the sentence the same call's load error has in a
/// body, one line per error. The call has no source: each is rendered against an empty one and
/// the position, the first there is, is dropped.
fn host_refusal_text(kb: &crate::kb::KnowledgeBase, e: crate::kb::typing::TypeError) -> String {
    let index = crate::span::LineIndex::new("");
    e.flatten()
        .iter()
        .map(|leaf| {
            let err = leaf.to_load_error(kb);
            let text = err.format_at(&index);
            match err.user_span().map(|sp| format!("{}: ", index.format_start(sp))) {
                Some(at) => text.strip_prefix(&at).map(str::to_string).unwrap_or(text),
                None => text,
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
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
        let error_layer = ErrorLayer::resolve(&mut kb);
        let eq_spec_op = {
            let named = kb.try_resolve_symbol("anthill.prelude.PartialEq.eq");
            let short = kb.intern("eq");
            let declared = kb
                .try_resolve_symbol("anthill.prelude.PartialEq")
                .and_then(|spec| kb.sort_ops_lookup(spec, short))
                .filter(|d| Some(*d) != named);
            [named, declared]
        };
        let fields = FieldSymbols::resolve(&mut kb);
        let stack = match config.depth_cap {
            Some(cap) => ActivationStack::with_cap(cap),
            None => ActivationStack::with_cap(usize::MAX),
        };
        Self {
            builtin_dispatch_dict: None,
            host_entry_dispatch: false,
            host_calls: HashMap::new(),
            running_builtin: None,
            kb,
            stack,
            builtins: HashMap::new(),
            reflect,
            error_layer,
            eq_spec_op,
            fields,
            closures: ClosureArenaRef::new(),
            streams: StreamArenaRef::new(),
            substs: subst_arena::SubstArenaRef::new(),
            maps: MapArenaRef::new(),
            layers: layer_arena::LayerArenaRef::new(),
            cells: CellArenaRef::new(),
            effect_handlers: EffectRegistry::new(),
            op_body_cache: HashMap::new(),
            const_cache: HashMap::new(),
            profiling: std::env::var_os("ANTHILL_PROFILE").is_some(),
            trace_requirements: std::env::var_os("ANTHILL_TRACE_REQ").is_some(),
            spec_body_ops: HashMap::new(),
            member_result_conversions: HashMap::new(),
            pair_positions: HashMap::new(),
            config,
            bridge_unknowns: std::rc::Rc::from([]),
            pattern_read_unknown: std::cell::Cell::new(false),
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
        self.builtins.insert(sym, BuiltinFn::Ground(std::sync::Arc::new(f)));
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
        self.builtins.insert(sym, BuiltinFn::Ground(std::sync::Arc::new(f)));
    }

    /// [`Self::register_builtin_sym`] for a function that SEES the caller's unfilled
    /// variables ([`BuiltinFn::SeesVars`]) — WI-20260827-1ZG70. Its one caller is
    /// `HostFn::register_on`, for a row of the runtime's own table of such functions.
    pub(crate) fn register_builtin_seeing_vars_sym<F>(&mut self, sym: crate::intern::Symbol, f: F)
    where
        F: Fn(&mut Interpreter, &[Value], &HostEnv) -> Result<Value, EvalError> + 'static,
    {
        self.builtins.insert(sym, BuiltinFn::SeesVars(std::sync::Arc::new(f)));
    }

    /// The caller's unfilled variables, as a variable-seeing host function is handed them.
    pub(crate) fn host_env(&self) -> HostEnv {
        HostEnv {
            unfilled: std::rc::Rc::clone(&self.bridge_unknowns),
        }
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
    ///
    /// `covers` names the functors this mirror durably backs; see
    /// [`KnowledgeBase::register_mirror`] for why coverage is declared rather than
    /// asked of the backend.
    pub fn register_mirror(
        &mut self,
        key: String,
        mirror: Box<dyn crate::persistence::Store>,
        covers: &[&str],
    ) -> Result<(), crate::kb::extent::ExtentRegError> {
        self.kb.register_mirror(key, mirror, covers)
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
            // Through `write_literal`, the spelling the `Value::Term` arm below reaches
            // via `print_term` — so the two carriers of one literal key identically by
            // construction. This was an inline copy of it (WI-20260907-VM9Q7).
            Value::Int(_) | Value::BigInt(_) | Value::Float(_) | Value::Bool(_) | Value::Str(_) => {
                use crate::kb::term_view::TermView;
                let lit = v
                    .as_literal(&self.kb)
                    .expect("a native scalar views as the literal it holds");
                crate::persistence::print::write_literal(&lit, buf);
            }
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
            // WI-SPGBP — a layer handle is session-scoped; it has no durable key.
            | Value::Kb(_)
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

    /// Invoke an anthill operation by qualified name — proposal 074 §1.4, the host call typed
    /// as the same call written in a body: `op(x1, …, xn)`, each `xi` a local at the type its
    /// argument is held at, typed by the typer as any body's call is — its type parameters
    /// fixed, its dictionaries built and put on the call — and run with each `xi` bound to the
    /// argument's value. So nothing in the call is chosen by a value: `has(s, "aa")` reads
    /// `s.O` off `s`'s type, and `Desc.describe(leaf)` goes through `Desc[T = Leaf]`. What
    /// the typer refuses about the call, and what it parks for the report after every body is
    /// typed (a requirement element nothing at the call fixes), is refused here, before
    /// anything runs ([`EvalError::HostCallRefused`]). The result is at the type the typer
    /// gave the call.
    ///
    /// A type variable left open in a bare value's type (`nil`'s element) is the call's to fix,
    /// as for a literal written in a body; a value whose type the typer gave it holds rigid what
    /// it does not say (an existential's `O`).
    ///
    /// A host-implemented operation with no declared signature has nothing to type, and reads
    /// no requirement: it is called with the values.
    ///
    /// The call writes no bracket; [`Self::call_bracketed`] is the call that writes one. They
    /// and their twins for a host that vouches for the callee's preconditions
    /// ([`Self::call_assuming_requires`], [`Self::call_bracketed_assuming_requires`]) are the
    /// host's only entries: a host hands an operation no dictionary by hand
    /// (`docs/design/operation-call-model.md` §"Host-to-entry-op boundary").
    pub fn call(&mut self, qualified_name: &str, args: &[HostValue]) -> Result<HostValue, EvalError> {
        self.call_entry(qualified_name, &[], args, Preconditions::Proved)
    }

    /// WI-20261126-7BJGQ — [`Self::call`] for a host that has decided the operation's
    /// `requires` itself, on the values it passes: the call is typed as if each of its value
    /// preconditions were established, the host taking them on itself as a caller outside the
    /// language. [`Self::call`] types `op(x1, …, xn)` where nothing can establish a
    /// precondition over a parameter — no enclosing guard, no prior `ensures`, no fact about
    /// the names — so it refuses every operation with one, whatever the values.
    ///
    /// WHAT THE HOST TAKES ON IS THE CALLEE'S value goals, and those of the defaults spliced
    /// into the call, which hold wherever the callee's do — not those of a call a `@[simp]`
    /// equation rewrites it into, which are proved as in a body — and nothing checks them when
    /// the call runs: a value that does not satisfy one runs the body. A requirement over a spec (`requires Ord[T = X]`) is no value goal — its
    /// dictionary is still owed, and a call nothing at its types supplies one for is refused
    /// as by [`Self::call`]. An operation run through a spec — a provider's member, or the
    /// spec operation's own body — is vouched for by the precondition of the operation the
    /// host names, the one the call is typed against.
    pub fn call_assuming_requires(
        &mut self,
        qualified_name: &str,
        args: &[HostValue],
    ) -> Result<HostValue, EvalError> {
        self.call_entry(qualified_name, &[], args, Preconditions::Vouched)
    }

    /// [`Self::call_bracketed`] for a host that has decided the operation's `requires`
    /// itself ([`Self::call_assuming_requires`]).
    pub fn call_bracketed_assuming_requires(
        &mut self,
        qualified_name: &str,
        bracket: &[(Option<&str>, Value)],
        args: &[HostValue],
    ) -> Result<HostValue, EvalError> {
        self.call_entry(qualified_name, bracket, args, Preconditions::Vouched)
    }

    /// [`Self::call`] with the call's bracket: `op[k1 = t1, …](x1, …, xn)`, each entry a key
    /// (`Some("Store")`, as a body writes `Store = …`) or a position (`None`) with the type the
    /// host holds for it. The entries are the call's type arguments as a body's bracket gives
    /// them, read by the typer as there: `call_bracketed("anthill.persistence.Store.persist",
    /// &[(Some("Store"), non_monotonic_store)], &[s, f, m])` is `Store.persist[Store =
    /// NonMonotonicStore](s, f, m)`, and `zeroOf` with `[(Some("X"), int64)]` is
    /// `zeroOf[X = Int64]()`. A key is a label, matched as a body's is. A host has no scope, so
    /// a key is not read through a type alias as a body's is: it is the spec's or the
    /// parameter's own name.
    ///
    /// Whether a call that selects `W` for a spec (`Spec.op[Spec = W](…)`) can be built is asked
    /// before any call by [`crate::kb::typing::dictionary_at_selection`] (WI-20261127-3R78F),
    /// which answers as this call's selection and dispatch do, with no operation and no argument.
    pub fn call_bracketed(
        &mut self,
        qualified_name: &str,
        bracket: &[(Option<&str>, Value)],
        args: &[HostValue],
    ) -> Result<HostValue, EvalError> {
        self.call_entry(qualified_name, bracket, args, Preconditions::Proved)
    }

    /// The host's four entries' one body: [`Self::call_bracketed`], with `preconditions`
    /// saying whether the host vouches for the callee's value preconditions.
    fn call_entry(
        &mut self,
        qualified_name: &str,
        bracket: &[(Option<&str>, Value)],
        args: &[HostValue],
        preconditions: Preconditions,
    ) -> Result<HostValue, EvalError> {
        let sym = self.kb.try_resolve_symbol(qualified_name).ok_or_else(|| {
            EvalError::UnknownOperation {
                name: qualified_name.to_string(),
            }
        })?;
        let refused = |kb: &crate::kb::KnowledgeBase, detail: String| EvalError::HostCallRefused {
            op: kb.qualified_name_of(sym).to_string(),
            detail,
        };
        let declared: Option<Vec<Value>> = crate::kb::op_info::lookup_operation_info(&self.kb, sym)
            .map(|rec| rec.params.into_iter().map(|(_, t)| t).collect());
        if declared.is_none() {
            if let Some(builtin) = self.builtins.get(&sym).cloned() {
                if !bracket.is_empty() {
                    return Err(refused(
                        &self.kb,
                        "it declares no signature, so a bracket has nothing to bind".to_string(),
                    ));
                }
                let values: Vec<Value> = args.iter().map(|a| a.value.clone()).collect();
                let value = self.call_host(sym, &builtin, &values, smallvec::SmallVec::new())?;
                return Ok(value.into());
            }
        }
        let declared = declared.unwrap_or_default();
        let type_args: Vec<(Option<Symbol>, Value)> = bracket
            .iter()
            .map(|(k, t)| (k.map(|k| self.kb.intern(k)), t.clone()))
            .collect();
        let names: Vec<Symbol> = (0..args.len())
            .map(|i| self.kb.intern(&format!("__host_argument_{i}")))
            .collect();
        let mut values: Vec<Value> = Vec::with_capacity(args.len());
        let mut types: Vec<Value> = Vec::with_capacity(args.len());
        for (i, a) in args.iter().enumerate() {
            let (value, ty) = match a.ty() {
                Some(ty) => (a.value.clone(), ty.clone()),
                // A bare instance is its carrier's value, at the carrier's type: where the
                // parameter takes the abstract sort, the typer converts it there again.
                None => {
                    let value = match self.open_instance(&a.value) {
                        Some((_, carried)) => carried,
                        None => a.value.clone(),
                    };
                    let ty = self
                        .host_arg_type(&value, declared.get(i))
                        .map_err(|detail| refused(&self.kb, detail))?;
                    // A name is handed over on a name's carrier: a nullary term read from a
                    // local is the evaluator's own type-parameter read, and refused unbound.
                    let symbol = self.kb.try_resolve_symbol("anthill.reflect.Symbol");
                    let at_symbol = crate::kb::typing::sort_functor_of_view(&self.kb, &ty)
                        .is_some_and(|t| Some(t) == symbol);
                    let value = match crate::kb::term_view::TermView::head(&value, &self.kb) {
                        crate::kb::term_view::ViewHead::Functor {
                            functor,
                            pos_arity: 0,
                            named_arity: 0,
                        } if at_symbol => Value::SymbolRef(functor),
                        _ => value,
                    };
                    (value, ty)
                }
            };
            values.push(value);
            types.push(ty);
        }
        // The key: each type's hash-consed term, the arguments' and the bracket's, where every
        // one is ground.
        let ground = |kb: &crate::kb::KnowledgeBase, t: &Value| match t {
            Value::Term { id, .. } if crate::kb::typing::type_is_ground(kb, t) => Some(*id),
            _ => None,
        };
        let key: Option<HostCallKey> = types
            .iter()
            .map(|t| ground(&self.kb, t))
            .collect::<Option<Vec<_>>>()
            .zip(
                type_args
                    .iter()
                    .map(|(k, t)| ground(&self.kb, t).map(|id| (*k, id)))
                    .collect::<Option<Vec<_>>>(),
            )
            .map(|(arguments, bracket)| (sym, arguments, bracket, preconditions));
        let cached = key.as_ref().and_then(|k| self.host_calls.get(k).cloned());
        let (node, result_ty) = match cached {
            Some(hit) => hit,
            None => {
                let span = crate::kb::node_occurrence::empty_span();
                let call = crate::kb::node_occurrence::NodeOccurrence::new_expr(
                    crate::kb::node_occurrence::Expr::Apply {
                        functor: sym,
                        pos_args: names
                            .iter()
                            .map(|n| {
                                crate::kb::node_occurrence::NodeOccurrence::new_expr(
                                    crate::kb::node_occurrence::Expr::Ident(*n),
                                    span,
                                    None,
                                )
                            })
                            .collect(),
                        named_args: Vec::new(),
                        type_args,
                        recv_type: None,
                    },
                    span,
                    None,
                );
                // The call is the body of an operation of the host's, which requires nothing:
                // typed where an operation body is, it is held to what an operation body's
                // call is.
                let host_op = self.kb.intern("anthill.host.call");
                let mut env = crate::kb::typing::TypingEnv::empty();
                env.set_enclosing_op(&mut self.kb, host_op);
                if preconditions == Preconditions::Vouched {
                    env.vouch_for_preconditions_of(sym);
                }
                for (n, ty) in names.iter().zip(&types) {
                    env.bind_var(*n, ty.clone());
                }
                let parked_before = self.kb.unsuppliable_requirements.len();
                let typed = crate::kb::typing::type_check_node(&mut self.kb, &env, &call, None);
                // What the typing parked is decided here, as the report after every body is
                // typed decides it for a body's call: a parked refusal refuses the call.
                let parked: Vec<_> = self.kb.unsuppliable_requirements.drain(parked_before..).collect();
                let typed = typed.map_err(|e| refused(&self.kb, host_refusal_text(&self.kb, e)))?;
                let parked: Vec<_> = parked
                    .into_iter()
                    .map(|entry| crate::kb::typing::TypeError::UnsatisfiableRequirement {
                        span: entry.span,
                        op: entry.callee_op,
                        callee_sort: entry.callee_sort,
                        usage: entry.usage,
                        refusal: entry.refusal,
                    })
                    .collect();
                if !parked.is_empty() {
                    let e = crate::kb::typing::TypeError::Multiple { errors: parked };
                    return Err(refused(&self.kb, host_refusal_text(&self.kb, e)));
                }
                let hit = (std::rc::Rc::clone(&typed.node), typed.ty);
                if let Some(k) = key {
                    self.host_calls.insert(k, hit.clone());
                }
                hit
            }
        };
        let top_level = self.begin_host_entry();
        self.stack.push(Frame {
            op: sym,
            expr: node,
            locals: names.iter().copied().zip(values).collect(),
            requirements: smallvec::SmallVec::new(),
            awaiting: None,
            untyped: false,
        })?;
        let value = self.run();
        self.end_host_entry(top_level, sym);
        Ok(HostValue::typed(value?, result_ty))
    }

    /// `v` with every instance in it opened to its carrier's value (proposal 073 §2): what a
    /// host works on where it reads the value itself — the stream a `Stream` result is — rather
    /// than passing it back, which hands the instance over whole ([`Self::call`]).
    pub fn carried(&self, v: Value) -> Value {
        self.opened_throughout(v)
    }

    /// `v` at the type its value reads as (`2` at `Int64`, an entity at its sort with the
    /// arguments its fields fix), as a [`HostValue`] holds it ([`Self::host_arg_type`] with no
    /// parameter to read against).
    pub fn host_value(&mut self, v: Value) -> Result<HostValue, EvalError> {
        let ty = self.host_arg_type(&v, None).map_err(|detail| EvalError::HostCallRefused {
            op: "<host value>".to_string(),
            detail,
        })?;
        Ok(HostValue::typed(v, ty))
    }

    /// The type a bare value the host passes reads as, against the type `declared` of the
    /// parameter it is passed to, where there is one — as a value written in a body is read
    /// against the type its parameter expects.
    ///
    /// A name — a symbol, or the bare name of a sort or an operation, the nullary application
    /// a name is — is at `Type` where the parameter takes a `Type`, and at `Symbol` otherwise:
    /// never a value of that sort, which only a constructor's nullary application (`nil`,
    /// `leaf()`) is. A run-time handle is at its reflect sort: a KB at `KB`, a fact reference
    /// at `FactRef`, a substitution at `Substitution`. Anything else is at the type its value
    /// reads as (`value_type_term`).
    fn host_arg_type(&mut self, v: &Value, declared: Option<&Value>) -> Result<Value, String> {
        use crate::kb::term_view::{TermView, ViewHead};
        let is_name = match v {
            // A constructor's symbol is its nullary value (`none`), a name only below, where
            // the parameter takes one.
            Value::SymbolRef(s) => self.kb.sort_of_constructor(*s).is_none(),
            _ => match v.head(&self.kb) {
                ViewHead::Functor {
                    functor,
                    pos_arity: 0,
                    named_arity: 0,
                } => {
                    self.kb.sort_of_constructor(functor).is_none()
                        && (self.kb.has_kind(functor, crate::intern::SymbolKind::Sort)
                            || crate::kb::op_info::lookup_operation_info(&self.kb, functor).is_some())
                }
                _ => false,
            },
        };
        let declared_is = |kb: &crate::kb::KnowledgeBase, qn: &str| {
            let want = kb.try_resolve_symbol(qn).map(|t| kb.canonical_sort_sym(t));
            declared
                .and_then(|d| crate::kb::typing::sort_functor_of_view(kb, d))
                .is_some_and(|d| Some(kb.canonical_sort_sym(d)) == want)
        };
        let type_sort = self.kb.try_resolve_symbol("anthill.prelude.Type");
        let declared_is_type = declared_is(&self.kb, "anthill.prelude.Type");
        let declared_is_symbol = declared_is(&self.kb, "anthill.reflect.Symbol");
        // A bare name at a parameter that takes a name or a type is that name or that type,
        // whatever it names — a constructor's included (an eponymous entity's sort, `red`).
        let nullary = matches!(
            v.head(&self.kb),
            ViewHead::Functor { pos_arity: 0, named_arity: 0, .. }
        ) || matches!(v, Value::SymbolRef(_));
        let is_name = is_name || (nullary && (declared_is_type || declared_is_symbol));
        // The ambient KB is the nullary application of `kb()` itself.
        let ambient_kb = self.kb.try_resolve_symbol("anthill.reflect.KB.kb");
        let is_ambient_kb = matches!(
            v.head(&self.kb),
            ViewHead::Functor { functor, pos_arity: 0, named_arity: 0 } if Some(functor) == ambient_kb
        );
        let handle_sort = match v {
            _ if is_ambient_kb => Some("anthill.reflect.KB"),
            _ if is_name && declared_is_type => Some("anthill.prelude.Type"),
            _ if is_name => Some("anthill.reflect.Symbol"),
            Value::Kb(_) => Some("anthill.reflect.KB"),
            Value::FactRef(_) => Some("anthill.reflect.FactRef"),
            Value::Substitution(_) => Some("anthill.reflect.Substitution"),
            // A resolved operation where the parameter takes the reflect sort `OpRef`
            // (`OpRef.op(r)`), as `Dictionary.resolveOp` gives it; elsewhere it is a function
            // value, below.
            Value::OpRef { .. } if declared_is(&self.kb, "anthill.realization.runtime.OpRef") => {
                Some("anthill.realization.runtime.OpRef")
            }
            _ => None,
        };
        if let Some(sort) = handle_sort.and_then(|qn| self.kb.try_resolve_symbol(qn)) {
            return Ok(Value::term(self.kb.make_sort_ref(sort)));
        }
        // A type written as a value (`Cell[V = Int64]`, or the occurrence of one) where the
        // parameter takes a `Type`.
        if declared_is_type && matches!(v, Value::Node(occ) if occ.as_expr().is_none()) {
            if let Some(t) = type_sort {
                return Ok(Value::term(self.kb.make_sort_ref(t)));
            }
        }
        if declared_is_type {
            if let ViewHead::Functor { functor, .. } = v.head(&self.kb) {
                if self.kb.has_kind(functor, crate::intern::SymbolKind::Sort) {
                    if let Some(t) = type_sort {
                        return Ok(Value::term(self.kb.make_sort_ref(t)));
                    }
                }
            }
        }
        // A function value naming an operation is at that operation's arrow, as the typer reads
        // a bare reference to it against the parameter's type (a builtin's, which no bare
        // reference lifts, is handed over at its arrow by the host: `HostValue::typed`); and an operation applied, held unevaluated (`insert(insert(
        // empty(), 1), 2)`, a term of a symbolic algebra), at the operation's declared result at
        // the type parameters its arguments' types fix.
        if let Value::OpRef { op, .. } = v {
            let node = crate::kb::node_occurrence::NodeOccurrence::new_expr(
                crate::kb::node_occurrence::Expr::Ref(*op),
                crate::kb::node_occurrence::empty_span(),
                None,
            );
            let env = crate::kb::typing::TypingEnv::empty();
            let ty = crate::kb::typing::type_check_node(&mut self.kb, &env, &node, declared.cloned())
                .map(|typed| typed.ty)
                .map_err(|e| {
                    format!(
                        "a function value of `{}` does not type: {}",
                        self.kb.qualified_name_of(*op),
                        host_refusal_text(&self.kb, e)
                    )
                })?;
            // A bare reference to a nullary operation with no anthill body reads as a call of
            // it, at its result: not the type of the function value the host holds.
            if !crate::kb::typing::is_callable_type(&mut self.kb, &ty) {
                return Err(format!(
                    "a function value of `{}`, which has no anthill body, has no type a bare \
                     reference to it gives: hand it over at its arrow (`HostValue::typed`)",
                    self.kb.qualified_name_of(*op)
                ));
            }
            return Ok(ty);
        }
        Ok(crate::kb::typing::host_value_type(&mut self.kb, v))
    }

    /// WI-625 gap 1 + Layer B: the resolver→eval bridge entry
    /// ([`crate::kb::KnowledgeBase::bridge_op_to_eval`]). Like [`Self::call`] but
    /// invoked BY SYMBOL (the resolver holds it already).
    ///
    /// The requirement dictionaries are RESOLVED at the concrete argument types
    /// ([`crate::kb::typing::resolve_bridge_requirements`], WI-300 Tier B / gap 3),
    /// NOT seeded with self-referential placeholders, as the untyped host entry's frame
    /// was — a placeholder can misdispatch a `requires` op to a
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
    /// [`Self::call_op_bridged`] for a call that carries the TYPER's evidence for its
    /// callee's own `requires` (`NodeOccurrence::op_dicts`, one expression per op-scoped
    /// slot): each is evaluated as eval's apply evaluates it ([`Self::push_op_scoped_slots`]'s
    /// reading), and supplies its slot; one this frame-less entry cannot read — a forward
    /// into a caller's frame — leaves its slot to the derivation, as an unfilled read does.
    pub(crate) fn call_op_bridged_stamped(
        &mut self,
        sym: Symbol,
        args: &[Value],
        dispatched_through: Option<(Symbol, &value::Dictionary)>,
        stamps: &[Option<crate::kb::term::TermId>],
    ) -> Result<Value, EvalError> {
        let slots = self.stamped_slots(sym, stamps)?;
        self.call_op_bridged(sym, args, dispatched_through, &slots)
    }

    /// The call site's op-scoped stamps for `sym`, evaluated, as the slots of `sym`'s whole
    /// chain ([`Self::call_op_bridged`]'s `supplied_slots`): `None` at each of its sort's
    /// slots and at a stamp this frame-less entry cannot read. Empty where it can read none.
    fn stamped_slots(
        &mut self,
        sym: Symbol,
        stamps: &[Option<crate::kb::term::TermId>],
    ) -> Result<Vec<Option<value::Dictionary>>, EvalError> {
        let mut op_slots: Vec<Option<value::Dictionary>> = Vec::with_capacity(stamps.len());
        for stamp in stamps {
            op_slots.push(match stamp {
                Some(tid) => {
                    let node = crate::kb::node_occurrence::materialize_from_handle(&self.kb, *tid);
                    self.try_eval_requirement_chain_node(&node)?
                }
                None => None,
            });
        }
        if op_slots.iter().all(Option::is_none) {
            return Ok(Vec::new());
        }
        let chain = crate::kb::typing::op_dict_entries(&mut self.kb, sym);
        let sort_len = chain.sort_len();
        if chain.len() != sort_len + op_slots.len() {
            return Err(EvalError::Internal(format!(
                "bridge: the call site supplied {} op-scoped slot(s) for `{}`, whose chain has {}",
                op_slots.len(),
                self.kb.qualified_name_of(sym),
                chain.len() - sort_len.min(chain.len()),
            )));
        }
        let mut slots: Vec<Option<value::Dictionary>> = vec![None; sort_len];
        slots.extend(op_slots);
        Ok(slots)
    }

    /// [`Self::call_op_bridged`] for a call the TYPER built its callee's dictionary for
    /// (`CalleeFrame::Dict`), entered as eval's apply enters it (`start_apply_same_sort` →
    /// `start_apply_within`): the dictionary evaluated and the callee's frame expanded from
    /// it, then the call's `stamps` for the callee's own `requires` placed after it. A
    /// dictionary this frame-less entry cannot read — a forward into a caller's frame —
    /// leaves the frame to the derivation, as [`Self::call_op_bridged_stamped`] leaves a stamp
    /// it cannot read.
    pub(crate) fn call_op_bridged_through(
        &mut self,
        sym: Symbol,
        args: &[Value],
        spec_op: Symbol,
        dict: crate::kb::term::TermId,
        stamps: &[Option<crate::kb::term::TermId>],
    ) -> Result<Value, EvalError> {
        let node = crate::kb::node_occurrence::materialize_from_handle(&self.kb, dict);
        let slots = self.stamped_slots(sym, stamps)?;
        match self.try_eval_requirement_chain_node(&node)? {
            Some(dict) => self.call_op_bridged(sym, args, Some((spec_op, &dict)), &slots),
            None => self.call_op_bridged(sym, args, None, &slots),
        }
    }

    /// The slots `target`'s frame takes from `dict`, a dictionary the call dispatched from
    /// `spec_op` hands it — what eval's apply installs before it enters the body
    /// ([`Self::expand_dispatching_dict`]), by slot name. For a reader that runs a part of
    /// `target`'s body elsewhere and owes that part the same dictionaries (the resolver's
    /// unfold).
    pub(crate) fn frame_through_dictionary(
        &mut self,
        spec_op: Symbol,
        target: Symbol,
        dict: &value::Dictionary,
    ) -> Result<Vec<(Symbol, value::Dictionary)>, EvalError> {
        Ok(self.expand_dispatching_dict(spec_op, target, dict)?.into_vec())
    }

    pub(crate) fn call_op_bridged(
        &mut self,
        sym: Symbol,
        args: &[Value],
        dispatched_through: Option<(Symbol, &value::Dictionary)>,
        // WI-20260925-P7VP4 — the calling clause's conditions for `sym`'s dictionary chain,
        // one per slot in chain order (`op_dict_entries`): `Some` stands in for what the
        // argument values would derive for that slot, `None` leaves the derivation below
        // in charge of it. Empty for every caller that is not a woven rule-body call or one
        // carrying the call site's stamps. Beside `dispatched_through` only its op-scoped
        // half is read: the dictionary lays out the sort's.
        supplied_slots: &[Option<value::Dictionary>],
    ) -> Result<Value, EvalError> {
        // WI-20260923-9R5HN — THE RESOLVER→EVAL BOUNDARY CANCELS A SPLICED WRAPPER. A
        // runtime value bound in σ (a closure, a map, a substitution) reaches the next
        // rule-body call σ-applied INTO the goal occurrence, so the argument arrives as
        // `Node(Spliced(v))`; eval reads those values by carrier, and they refused it —
        // MEASURED, `adder(10) <=> ?f, apply1(?f, 1) = 11` bound the parameter to a node
        // ("unknown operation: …apply1.f") and `Map.put(..) <=> ?m, Map.size(?m) = 1`
        // refused its receiver, both SUSPENDED. Cancelled here and not upstream in the
        // σ-walk: the resolver's own builtins (the occurrence readers) are handed the
        // carrier the goal holds, and read it as such. `Value::carried` strips every
        // wrapper layer, whichever path the argument came by.
        let unwrapped: Vec<Value>;
        let args = if args.iter().any(|a| !std::ptr::eq(a.carried(), a)) {
            unwrapped = args.iter().map(|a| a.carried().clone()).collect();
            &unwrapped[..]
        } else {
            args
        };
        if let Some(builtin) = self.builtins.get(&sym).cloned() {
            // The calling clause's conditions for the builtin's own chain stand in for what
            // its argument values would give, as they do for a body below (WI-20260925-P7VP4).
            let requirements = self.supplied_channel(sym, supplied_slots);
            // A host member entered through a dictionary reads it, as one dispatched in a body
            // does (`eval.rs`'s registered-builtin step): a tuple's `eq`, its sub-dictionaries.
            let saved_dict = self.builtin_dispatch_dict.take();
            self.builtin_dispatch_dict = dispatched_through.map(|(_, dict)| dict.clone());
            // Proposal 073 §2 — handed back to the host as the carrier's value.
            let result = self
                .call_host(sym, &builtin, args, requirements)
                .map(|v| self.carried_for_host(sym, v));
            self.builtin_dispatch_dict = saved_dict;
            return result;
        }
        // 068 §2: an operation whose carrier the call would be dispatched by, reached with
        // that carrier one of the caller's unknowns, cannot be chosen yet — run as it is, a
        // defaulted spec operation answered with its default for a carrier nobody knows.
        // Needed HERE only: inside the run a spec call's carrier comes through its
        // requirement dictionary, and the clause's read of that dictionary waits on an
        // unknown before the bridge runs (MEASURED, one provider and two).
        if !self.bridge_unknowns.is_empty()
            && eval::spec_call_reads(&self.kb, sym, args, &|v| self.is_unknown(v))
        {
            return Err(self.reads_unknown(&format!(
                "dispatching `{}`",
                self.kb.qualified_name_of(sym)
            )));
        }
        use crate::kb::typing::BridgeRequirements;
        // Proposal 073 §1 (WI-20261105-CBRD2) — a call nothing in the knowledge base can run
        // here ends where its dispatch would, unreduced (`Set.insert(Set.empty(), 1)`, a member
        // only another language implements), before a dictionary is derived from its argument
        // values, or a member found from them, for nothing this interpreter runs.
        let builtins = &self.builtins;
        let runs_here = |kb: &crate::kb::KnowledgeBase, member: Symbol| {
            builtins.contains_key(&member) || crate::kb::typing::op_is_interpretable(kb, member)
        };
        if dispatched_through.is_none() && crate::kb::typing::no_call_of_it_runs(&self.kb, sym, runs_here) {
            return Err(self.unrunnable_target_error(sym));
        }
        // WI-20260909-NAR1X — THE CALLER'S DICTIONARY, WHERE THE CALLER HAS ONE.
        //
        // The resolution below pins the callee's chain FROM THE ARGUMENT TYPES, and
        // `reduce_op_value`'s own note says why that is "the one entry that can" — for a
        // call the resolver classified from its operands. A WOVEN call
        // (`Expr::ApplyWithin`, WI-1040) is the other kind: the clause's `require[X]`
        // resolved a dictionary at run time and that dictionary, not the arguments, is
        // what says which instance the call means. For a CARRIER-LESS spec op
        // (`Monoid.unit()`) the arguments say nothing at all — there are none — so the
        // two are not even competing readings; one of them is the only one.
        //
        // So the woven route hands the dictionary here and the channel is EXPANDED from
        // it — `expand_dispatching_dict`, the same projection an operation-body dispatch
        // performs, so the frame `Wrap.zero()` is entered with is byte-identical whether
        // the call came from an operation body or from a rule clause. Without it the
        // impl's OWN chain (`Wrap provides Zeroable[T = Wrap] :- Zeroable[E]`) has
        // nothing to pin `E` from and the call residualizes: MEASURED, `require[
        // Zeroable[T]], Zeroable.zero(?r)` over `wrap(inner: sum())` answered ONE
        // INDEFINITE solution where the value is `103`.
        //
        // AN ERROR HERE IS NOT SWALLOWED. `expand_dispatching_dict` reports an
        // `EvalError::Internal` for a dictionary whose arity disagrees with the layout,
        // and `bridge_op_to_eval`'s `debug_assert` makes that loud in a debug build
        // rather than residualizing quietly — the same treatment every other
        // evaluator-invariant failure gets on this path.
        //
        // THAT ARM IS UNREACHED IN THE CORPUS, MEASURED rather than argued, because a
        // debug abort on a legal program would be the worst of the outcomes available
        // (the sentence WI-20260909-S8CBV's projection gate records): with the failure
        // instrumented, `wi_tests` (4579 tests) reaches it ZERO times. The two lists it
        // compares have one producer each and the dictionary is the one the clause's own
        // `find_dictionary` resolved for this spec at this carrier, so a disagreement
        // between them is an inconsistency rather than a program shape — which is what
        // makes the loud treatment the right one, and the census what says it is not
        // firing on something ordinary today.
        //
        // The callee's OWN `requires` follow the dictionary's half, as eval's apply places
        // them (`push_op_scoped_slots`): what the call supplied for a slot, after what the
        // dictionary's provision passes a body written in a spec (`push_spec_body_slots`,
        // inside `expand_dispatching_dict`). A default body reading its own `requires`
        // (`both() -> C requires Unit[T = Element]`) runs on the provision's `Unit`.
        if let Some((dispatched_from, dict)) = dispatched_through {
            let mut requirements = self.expand_dispatching_dict(dispatched_from, sym, dict)?;
            if !supplied_slots.is_empty() {
                let chain = crate::kb::typing::op_dict_entries(&mut self.kb, sym);
                let sort_len = chain.sort_len();
                let names = chain.names(&mut self.kb);
                for (name, supplied) in names.iter().zip(supplied_slots).skip(sort_len) {
                    if let Some(supplied) = supplied {
                        requirements.push((*name, supplied.clone()));
                    }
                }
            }
            // Proposal 073 §2 — a default body of a sort with abstract values the dictionary
            // sends the call to reads the receiver the call made at another type as the
            // instance the dictionary is (`Iterable.isEmpty(c: C)` at `List` reaching
            // `Stream.isEmpty(s: Self)`), as a body's call through the dictionary pairs it
            // (`positions_to_pair`): the value's own sort is not asked. A receiver paired
            // where the call was typed (a rule body's, at the member's `Self`) is the instance
            // it was made.
            let mut paired: Vec<Value> = Vec::new();
            if let Some(positions) = self.positions_to_pair(dispatched_from, sym) {
                paired = args.to_vec();
                for i in positions {
                    if let Some(slot) = paired.get_mut(i).filter(|v| self.open_instance(v).is_none()) {
                        let raw = std::mem::replace(slot, Value::Unit);
                        *slot = self.pair_with(dict.clone(), raw)?;
                    }
                }
            }
            let args = if paired.is_empty() { args } else { &paired[..] };
            return self.invoke_op_with_requirements(sym, args, requirements);
        }
        // WI-20260925-P7VP4 — the calling clause's conditions stand in for their slots
        // (`BridgeSlot::Supplied`), in place: the derivation leaves those slots out, so a tie
        // or an unpinnable element at a slot the caller already chose for cannot suspend the
        // call, and with every slot supplied nothing is derived at all.
        let requirements =
            match crate::kb::typing::resolve_bridge_requirements_supplied(
                &mut self.kb,
                sym,
                args,
                crate::kb::typing::NamedSlotTies::Raise,
                supplied_slots,
            ) {
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
                BridgeRequirements::Ambiguous { requirement, candidates } => {
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
                    let p = crate::kb::typing::op_owner_provision(&self.kb, sym);
                    self.frame_requirements_from_trees(parent, p, &trees)
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
        // Proposal 066 §7 — the provision the frame's operation is a member of; the
        // `__req_self` stand-in is that frame's parent bundle.
        self_provision: Option<Symbol>,
        trees: &[(Symbol, crate::kb::typing::BridgeSlot)],
    ) -> Result<smallvec::SmallVec<[(Symbol, value::Dictionary); 2]>, FrameReqFailure> {
        let mut out: smallvec::SmallVec<[(Symbol, value::Dictionary); 2]> =
            smallvec::SmallVec::with_capacity(trees.len() + 1);
        // WI-857: layout-valid — see `stand_in_requirement`.
        let self_slot = self
            .stand_in_requirement(parent, parent, self_provision)
            .map_err(|_| FrameReqFailure::NoDictionarySort)?;
        out.push((self.fields.req_self, self_slot));
        for (name, slot) in trees {
            let dict = match slot {
                // `port_resolved_tree` answers `None` for a `FromScope` AND for the
                // missing-sort case; the `stand_in_requirement` above already ruled the
                // second one out, so reaching here names the slot.
                crate::kb::typing::BridgeSlot::Resolved(tree) => self
                    .port_resolved_tree(tree)
                    .ok_or(FrameReqFailure::CallerScopeSlot(*name))?,
                // WI-857's marker, minted for THIS absence (WI-865), refused at any read.
                crate::kb::typing::BridgeSlot::Absent { spec_sort, why } => {
                    crate::kb::typing::dictionary_of_absence(&mut self.kb, *spec_sort, why.clone())
                        .ok_or(FrameReqFailure::NoDictionarySort)?
                }
                // The calling clause's condition for this slot (WI-20260925-P7VP4).
                crate::kb::typing::BridgeSlot::Supplied(dict) => dict.clone(),
            };
            out.push((*name, dict));
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
    /// sub-dictionaries, and a
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

    /// Is `v` itself one of the caller's unknowns ([`Self::bridge_unknowns`])?
    pub(crate) fn is_unknown(&self, v: &Value) -> bool {
        is_one_of(&self.kb, &self.bridge_unknowns, v)
    }

    /// Does `v` hold one of the caller's unknowns anywhere in it?
    pub(crate) fn mentions_unknown(&self, v: &Value) -> bool {
        !self.bridge_unknowns.is_empty()
            && self.kb.mentions_var(v, &|var| {
                matches!(var, crate::kb::term::Var::Global(vid) if self.bridge_unknowns.contains(&vid))
            })
    }

    /// The slots a woven rule-body call SUPPLIED for `op`'s chain (`call_op_bridged`'s
    /// `supplied_slots`, one per slot in chain order), named as the chain names them.
    fn supplied_channel(
        &mut self,
        op: Symbol,
        supplied_slots: &[Option<value::Dictionary>],
    ) -> smallvec::SmallVec<[(Symbol, value::Dictionary); 2]> {
        let mut requirements = smallvec::SmallVec::new();
        if supplied_slots.iter().any(Option::is_some) {
            let names = crate::kb::typing::op_dict_entries(&mut self.kb, op).names(&mut self.kb);
            for (name, dict) in names.iter().zip(supplied_slots) {
                if let Some(dict) = dict {
                    requirements.push((*name, dict.clone()));
                }
            }
        }
        requirements
    }

    /// Run a host function — the one door every host call goes through. 068 §2: a host
    /// function reads whatever it is handed (`eq` over an unknown answered `false`,
    /// arithmetic over one a type mismatch), so a [`BuiltinFn::Ground`] one handed any of
    /// the caller's unknowns waits, as the bridge's whole call used to. Checked here and
    /// nowhere else, no route of the dispatch — a direct target, an override, a spec
    /// implementation chosen by value, a dictionary sibling, the bridge's own entry — can
    /// hand one an unknown.
    ///
    /// A [`BuiltinFn::SeesVars`] one is handed them, with the [`HostEnv`] it asks at each
    /// position it reads (WI-20260827-1ZG70): the wait moves from the whole argument to the
    /// positions the function's answer depends on.
    ///
    /// `requirements` is the channel the route handed. A builtin enters no frame, so the
    /// channel is kept for the call ([`Self::running_builtin`]), where a host function that
    /// raises reads it (proposal 071 §1.3).
    pub(crate) fn call_host(
        &mut self,
        sym: Symbol,
        builtin: &BuiltinFn,
        args: &[Value],
        requirements: smallvec::SmallVec<[(Symbol, value::Dictionary); 2]>,
    ) -> Result<Value, EvalError> {
        if matches!(builtin, BuiltinFn::Ground(_))
            && args.iter().any(|a| self.mentions_unknown(a))
        {
            return Err(self.reads_unknown(&format!("host `{}`", self.kb.qualified_name_of(sym))));
        }
        let saved = self.running_builtin.replace(RunningBuiltin {
            op: sym,
            requirements,
        });
        let opened = self.open_host_arguments(sym, args);
        let args = opened.as_deref().unwrap_or(args);
        let result = match builtin {
            BuiltinFn::Ground(f) => f(self, args),
            BuiltinFn::SeesVars(f) => {
                let env = self.host_env();
                f(self, args, &env)
            }
        };
        self.running_builtin = saved;
        match result {
            Ok(v) => self.pair_host_result(sym, v),
            err => err,
        }
    }

    /// Proposal 073 §2 — the host works on its own values: an argument at a parameter typed at a
    /// sort with abstract values is handed to it as the carrier's value. `None` where nothing
    /// is opened.
    fn open_host_arguments(&self, op: Symbol, args: &[Value]) -> Option<Vec<Value>> {
        let info = crate::kb::op_info::lookup_operation_info(&self.kb, op)?;
        let mut out: Option<Vec<Value>> = None;
        for (i, (_, ty)) in info.params.iter().enumerate() {
            if !self.typed_at_abstract_carrier(ty) {
                continue;
            }
            if let Some((_, carried)) = args.get(i).and_then(|a| self.open_instance(a)) {
                out.get_or_insert_with(|| args.to_vec())[i] = carried;
            }
        }
        out
    }

    /// Proposal 073 §2 — a host operation's result at a sort with abstract values (`KB.execute`
    /// answering `Stream[…]`) is the instance of the host carrier it built: the host's value says
    /// which (a stream handle is a `LogicalStream`), and that carrier's dictionary is paired with
    /// it.
    fn pair_host_result(&mut self, op: Symbol, v: Value) -> Result<Value, EvalError> {
        let Some(info) = crate::kb::op_info::lookup_operation_info(&self.kb, op) else {
            return Ok(v);
        };
        let ret = info.return_type.clone();
        if !self.typed_at_abstract_carrier(&ret) || self.open_instance(&v).is_some() {
            return Ok(v);
        }
        let Some(abstract_sort) = crate::kb::typing::sort_functor_of_view(&self.kb, &ret) else {
            return Ok(v);
        };
        let abstract_sort = self.kb.canonical_sort_sym(abstract_sort);
        let Some(carrier) = eval::runtime_carrier_sort(&self.kb, &v) else {
            return Err(EvalError::Internal(format!(
                "host `{}` answered a {} where its result is a `{}`, which names no carrier",
                self.kb.qualified_name_of(op),
                v.type_name(),
                self.kb.qualified_name_of(abstract_sort),
            )));
        };
        let carrier = self.kb.canonical_sort_sym(carrier);
        let carrier_ty = Value::term(self.kb.make_sort_ref(carrier));
        let term = crate::kb::typing::dictionary_at_in_scope(
            &mut self.kb,
            abstract_sort,
            carrier,
            &carrier_ty,
            &ret,
            &[],
            &crate::kb::typing::DictChain::empty(),
            &[],
        )
        .map_err(|why| {
            EvalError::Internal(format!("the result of host `{}`: {why}", self.kb.qualified_name_of(op)))
        })?;
        let occ = crate::kb::node_occurrence::materialize_from_handle(&self.kb, term);
        let dict = self.eval_requirement_chain_node(&occ)?;
        self.make_instance(dict, v)
    }

    /// Proposal 073 §2 — the result of `op` handed to the host: an instance is handed as its
    /// carrier's value, wherever it stands in the result (`snd` of `Stream.splitFirst`'s
    /// pair), the host working on its own values. Walked only where `op`'s declared result
    /// names a sort with abstract values.
    pub(crate) fn carried_for_host(&self, op: Symbol, v: Value) -> Value {
        let holds_instances = crate::kb::op_info::lookup_operation_info(&self.kb, op)
            .is_some_and(|info| {
                crate::kb::typing::type_names_abstract_carrier(&self.kb, &info.return_type)
            });
        if holds_instances {
            self.opened_throughout(v)
        } else {
            v
        }
    }

    /// `v` with every instance in it opened to its carrier's value, at any depth.
    fn opened_throughout(&self, v: Value) -> Value {
        if let Some((_, carried)) = self.open_instance(&v) {
            return self.opened_throughout(carried);
        }
        match v {
            Value::Entity {
                functor,
                pos,
                named,
            } => Value::Entity {
                functor,
                pos: pos.iter().map(|c| self.opened_throughout(c.clone())).collect::<Vec<_>>().into(),
                named: named
                    .iter()
                    .map(|(k, c)| (*k, self.opened_throughout(c.clone())))
                    .collect::<Vec<_>>()
                    .into(),
            },
            Value::Tuple { pos, named } => Value::Tuple {
                pos: pos.iter().map(|c| self.opened_throughout(c.clone())).collect::<Vec<_>>().into(),
                named: named
                    .iter()
                    .map(|(k, c)| (*k, self.opened_throughout(c.clone())))
                    .collect::<Vec<_>>()
                    .into(),
            },
            other => other,
        }
    }

    /// Is `ty` headed by a sort with abstract values (`kb::typing::is_abstract_carrier_sort`)?
    fn typed_at_abstract_carrier(&self, ty: &Value) -> bool {
        crate::kb::typing::sort_functor_of_view(&self.kb, ty).is_some_and(|h| {
            let h = self.kb.canonical_sort_sym(self.kb.type_arg_owner(h).unwrap_or(h));
            crate::kb::typing::is_abstract_carrier_sort(&self.kb, h)
        })
    }

    /// Is `sym` `PartialEq.eq` ([`Self::eq_spec_op`])?
    pub(crate) fn is_eq_spec_op(&self, sym: Symbol) -> bool {
        self.eq_spec_op.contains(&Some(sym))
    }

    /// `PartialEq.eq` reached with no member ([`Self::eq_spec_op`]): a call no type reached,
    /// an error (`EvalError::EqualityWithNoMember`, kernel-language §8.3) — its operands are
    /// not compared by their values. One that reads a variable the rule has not bound waits
    /// first, as a host call does ([`Self::call_host`]).
    pub(crate) fn eq_with_no_member(&mut self, args: &[Value]) -> EvalError {
        if args.iter().any(|a| self.mentions_unknown(a)) {
            return self.reads_unknown("`anthill.prelude.PartialEq.eq`");
        }
        crate::kb::resolve::note_untyped_equality();
        let printer = crate::persistence::print::TermPrinter::new(&self.kb);
        let operands = args.iter().map(|a| printer.print_value(a)).collect::<Vec<_>>().join(", ");
        EvalError::EqualityWithNoMember { operands }
    }

    /// The suspension a read of one of the caller's unknowns raises: the call cannot be
    /// evaluated YET, and the resolver delays it until a binding wakes it (068 §2.2).
    pub(crate) fn reads_unknown(&self, what: &str) -> EvalError {
        unfilled_read(what)
    }

    /// WI-625 gap 1: is this interpreter running as the resolver's op-body
    /// bridge? When set, semantic comparisons that reach an undecided point
    /// suspend ([`EvalError::Suspended`]) instead of forcing a structural
    /// verdict. See [`EvalConfig::bridge_mode`].
    pub(crate) fn bridge_mode(&self) -> bool {
        self.config.bridge_mode
    }

    /// WI-818 (review): the ONE classifier for "this call target cannot run", the
    /// fall-through of the dispatch (`dispatch_resolved_operation`) a body's call and a
    /// host call ([`Self::invoke_op_with_requirements`]) both take:
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
                defined_by_clauses: self.kb.has_clauses_under(self.kb.canonical_sym(sym)),
                backtrace: std::backtrace::Backtrace::capture(),
            }
        } else {
            EvalError::UnknownOperation {
                name: self.kb.qualified_name_of(sym).to_string(),
            }
        }
    }

    /// The start of a host entry's run ([`Self::invoke_op_with_requirements`]): answers
    /// whether it is TOP-LEVEL, for [`Self::end_host_entry`].
    ///
    /// WI-20260913-2858G — ONLY A TOP-LEVEL ENTRY STARTS A NEW BUDGET. A host function
    /// calling back in from inside a body lands here with the caller's frames still on
    /// the stack, and its work is the OUTER run's work: resetting `step_count` there
    /// let a loop whose every pass makes such a call run for ever under `step_cap`, and
    /// clearing the dispatch ring or dumping the profile would split the one run's
    /// record at each nested call. Before 2858G that path could not complete at all,
    /// so nothing relied on the reset.
    ///
    /// INLINED ALWAYS, as [`Self::run_from`] is: both entries are on the bridge's path, whose
    /// native stack per crossing is a measured budget (`BRIDGE_REENTRY_CAP`).
    #[inline(always)]
    fn begin_host_entry(&mut self) -> bool {
        let top_level = self.stack.depth() == 0;
        if top_level {
            self.step_count = 0;
            self.recent_dispatches.clear();
        }
        top_level
    }

    /// The end of a host entry's run: a top-level run's profile is dumped where it ends.
    #[inline(always)]
    fn end_host_entry(&self, top_level: bool, entry: Symbol) {
        if self.profiling && top_level {
            self.dump_profile(entry);
        }
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



    /// WI-857 — a **stand-in** dictionary for `spec` under the functor `functor`:
    /// layout-valid (its bundled count is `dict_layout(spec, functor).arity()`) with
    /// every sub-slot a `NoProvider` marker, since a stand-in has no evidence for
    /// any of them.
    ///
    /// Producers of a dictionary must produce a layout-valid one — that is the
    /// invariant the arity cross-check enforces, and this is what lets a stand-in
    /// satisfy it without pretending to carry evidence. The stand-ins are a frame's
    /// self-referential `__req_self` slots (a bridged call's, a woven call's): adequate for
    /// same-sort recursion, and for a cross-sort `requires` they dispatch onto the spec's own
    /// op, whose value-directed resolution reads the real carrier (WI-350/WI-822).
    /// Before this they were `functor` with NO sub-slots, which the layout reads as
    /// a dictionary claiming `functor`'s whole `requires` chain and bundling none.
    ///
    /// # WI-868 — THE TWO REPRESENTATIONS OF "NO EVIDENCE" STAY SEPARATE
    ///
    /// WI-857 left two, and WI-868 asked whether they should be one:
    ///
    ///  * a recorded ABSENCE — then the resolver's `ResolvedRequiresNode::Unavailable`,
    ///    since WI-20260925-4ZZKZ only a value-only route's
    ///    [`crate::kb::typing::BridgeSlot::Absent`] — emitted as an empty bundle over an
    ///    `anthill.reflect.NoProvider` marker, which `resolve_op_target_checked` REFUSES
    ///    to dispatch through;
    ///  * this STAND-IN — marker sub-slots, but its own functor is a real sort, which is a
    ///    claim that can mis-dispatch.
    ///
    /// The ticket's hypothesis: they cannot be merged only because the refusal sits
    /// BEFORE the WI-350/WI-822 value-directed rescue, and moving it after the rescue
    /// fails would let one representation serve both. MEASURED, that is FALSE, and the
    /// obstacle is not the ordering. Three experiments, each run over the whole
    /// `anthill-core` suite (4534 tests):
    ///
    /// 1. MERGE ALONE (this function mints the marker as its own functor, refusal
    ///    untouched): 2 failures. `wi818 variant_b_carrier_impl_loads_and_evaluates` —
    ///    a WORKING program — is refused, and `requires_path_reports_missing_body_-
    ///    like_direct_call` reports a missing BODY as an unpinned REQUIREMENT. One
    ///    representation, two outcomes collapsed into one message.
    ///
    /// 2. MERGE + MOVE THE REFUSAL after the rescue: the two do NOT recover. They
    ///    become `Internal("dispatching dict for … has arity 1 but its requires chain
    ///    wants 0 slot(s) — … provider `anthill.reflect.NoProvider`")`. THAT is the real
    ///    obstacle: a dictionary's layout is computed FROM ITS FUNCTOR, so a marker
    ///    functor erases which provider's chain the dictionary stands in for — the
    ///    merged form is layout-incoherent, before any question of ordering. Nine more
    ///    rows fail with it (`wi857`, `wi865` ×7, `wi869`), each a refusal that used to
    ///    name its cause and now reports an arity mismatch or, in
    ///    `a_spec_half_with_no_provider_…`, "operation has no body" — a repair pointing
    ///    at the wrong file.
    ///
    /// 3. THE BUILTIN CASE, which the ticket asked to be measured rather than assumed.
    ///    With the refusal off the dispatch path, a body reading a marker slot to call
    ///    a BUILTIN-backed spec op gets the host's structural verdict, silently:
    ///    `PartialEq.eq` over a `PartialEq[Wrap[E = Int64]]` that NOTHING provides
    ///    answered `Ok(Int(1))` for equal operands and `Ok(Int(0))` for distinct ones.
    ///    Both polarities, because `eq(x, x)` alone can be answered by reflexivity
    ///    before dispatch. Driven and pinned by
    ///    `wi868_a_builtin_read_through_a_marker_slot_is_refused`, which is the control
    ///    for those two numbers and the tripwire for a future merge.
    ///
    /// SO THE DECISION IS: two representations, because they answer two questions. A
    /// marker says "nothing pins this slot, and here is why" — a verdict, refused at
    /// every dispatch. A stand-in says "this frame was entered from a host that named
    /// no dictionary; the receiver VALUE may still say which impl" — an invitation to
    /// the rescue, which is the only reason `interp.call` works at all on a sort with a
    /// `requires`. Merging them would have to give the marker a second meaning that
    /// depends on what the callee turns out to be, and experiment 3 is what that costs
    /// when the callee is builtin-backed.
    ///
    /// WHAT WOULD RE-OPEN IT: a stand-in that keeps the provider's identity while
    /// carrying an absence — i.e. the layout question and the evidence question
    /// answered by different fields rather than by one functor. That is a change to the
    /// dictionary VALUE, not a re-ordering of the refusal, and experiment 2 is the
    /// measurement that says so.
    fn stand_in_requirement(
        &mut self,
        spec: Symbol,
        functor: Symbol,
        // Proposal 066 §7 — [`crate::kb::typing::dict_layout`]'s parameter of the same
        // name: read only for a `__req_self` stand-in (`spec == functor`).
        self_provision: Option<Symbol>,
    ) -> Result<value::Dictionary, EvalError> {
        let arity =
            crate::kb::typing::dict_layout(&mut self.kb, spec, functor, self_provision).arity();
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
        self.build_dictionary_at(impl_sort, subs, None, None)
    }

    /// [`Self::build_dictionary`] with a tuple's labels and the application the dictionary is
    /// for ([`value::Dictionary::build_at`]).
    pub(crate) fn build_dictionary_at(
        &self,
        impl_sort: Symbol,
        subs: impl IntoIterator<Item = value::Dictionary>,
        labels: Option<&[Symbol]>,
        at: Option<crate::kb::term::TermId>,
    ) -> Result<value::Dictionary, EvalError> {
        value::Dictionary::build_at(&self.kb, impl_sort, subs, labels, at).ok_or_else(|| {
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

    /// Clone the map-arena handle (cheap `Rc` bump), so a caller can hold it while
    /// `&mut self` on the interpreter is in flight.
    pub fn map_arena(&self) -> MapArenaRef {
        self.maps.clone()
    }

    /// Number of live cell-arena slots. Diagnostic for refcount tests.
    pub fn cell_arena_live_count(&self) -> usize {
        self.cells.live()
    }

    /// Build `Dictionary(subs…, impl: functor)` with NO layout check — the value
    /// carrier alone. `None` in a KB with no
    /// `anthill.realization.runtime.Dictionary` to name.
    ///
    /// Not a host's way to hand an operation its requirements: a host call is typed as the
    /// same call in an operation body, and the typer builds its dictionaries ([`Self::call`]).
    /// What is unchecked is that `subs` is the number the (spec, provider) layout wants,
    /// which is what makes a dictionary usable as EVIDENCE. Its callers build a dictionary
    /// to exercise the value machinery — `Dictionary.impl` reading a symbol back, a
    /// projection reading slot `k` — where the pair is not a claim about any spec.
    pub fn alloc_dictionary_unchecked(
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
        h.with(|c| c.requirements.clone())
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
            awaiting: None,
            untyped: false,
        })?;
        self.run()
    }

    /// Allocate a fresh cell slot and return an owning handle.
    pub fn alloc_cell(&self, value: Value) -> value::CellHandle {
        self.cells.alloc(value)
    }

    /// Snapshot the value held in `h`.
    pub fn read_cell(&self, h: &value::CellHandle) -> Value {
        // The HANDLE's arena, not `self.cells` — see `CellHandle::read`.
        h.read()
    }

    /// Replace the value in `h`; returns the prior value.
    pub fn write_cell(&self, h: &value::CellHandle, new: Value) -> Value {
        h.write(new)
    }

    /// Clone the cell-arena handle (cheap `Rc` bump), so a caller can hold it while
    /// `&mut self` on the interpreter is in flight.
    pub fn cell_arena(&self) -> CellArenaRef {
        self.cells.clone()
    }

    /// Allocate a fresh substitution slot and return a handle.
    pub fn alloc_subst(&self, s: crate::kb::subst::Substitution) -> value::SubstHandle {
        self.substs.alloc(s)
    }

    // No `with_subst` / `subst_arena` here (WI-20260923-9R5HN): a substitution is read
    // through its HANDLE (`SubstHandle::with_subst`), which carries the arena that minted
    // it. An interpreter-side reader indexed `self.substs` with a handle another
    // interpreter may have minted — see that method.

    /// Allocate a stream source, returning an owning handle.
    pub fn alloc_stream(&self, src: stream::StreamSource) -> value::StreamHandle {
        self.streams.alloc(src)
    }

    /// The symbols currently bound to a host builtin.
    ///
    /// Exposed so a test can hold the registry to the mapping index: every operation
    /// registered here must be one `is_interpreter_mapped_op` can see
    /// (`wi_brt4y_host_implemented_test`). It was exposed first to check that TWO
    /// registries stayed disjoint — [`Self::register_builtin`] is a plain map insert,
    /// LAST WINS, and WI-759 found `field_access` shadowed by anthill-stl's second set —
    /// until WI-20260923-9R5HN folded that set into the one.
    pub fn registered_builtin_symbols(&self) -> Vec<Symbol> {
        self.builtins.keys().copied().collect()
    }

    /// WI-SPGBP — discard every scoped-KB layer (`KB.loaded`) whose last holder has
    /// gone, innermost first.
    ///
    /// Called once per iteration of [`Self::run`]'s trampoline, so an anthill program
    /// that lets a layer value go out of scope has it discarded promptly. It costs one
    /// `Cell` read when there are no layers, which is every run that never called
    /// `KB.loaded`.
    ///
    /// IT IS NOT `KbHandle::drop`, and cannot be: restoring a layer needs
    /// `&mut KnowledgeBase`, which a `Drop` impl has no way to reach. A release only
    /// RETIRES the slot; this is the nearest point that holds the KB. A HOST driving
    /// `call` directly (rather than through `run`) therefore has to call this itself —
    /// which is also what makes the discard observable from a test.
    pub fn sweep_layers(&mut self) {
        // The gate FIRST, before any borrow or refcount traffic: one `Cell` read, which
        // is the whole cost for a program that never called `KB.loaded`.
        if !self.layers.has_retired() {
            return;
        }
        // Past the gate a layer is genuinely being discarded, so the `Rc` bump that lets
        // the arena be read while `self.kb` is borrowed mutably is free in context.
        let layers = self.layers.clone();
        if layers.sweep(&mut self.kb) == 0 {
            return;
        }
        // A discard also has to take the INTERPRETER-side memos with it. Both were
        // populated while the layer was applied, and both are keyed by a `Symbol` that
        // outlives the layer (symbols are monotone — see `crate::kb::layer`), so neither
        // goes stale on its own:
        //
        //   * `op_body_cache` holds bodies read from the scoped `op_records`, including
        //     any a layer's `@[simp]` write-back rewrote — so a BASE operation could keep
        //     running the layer's version of its own body.
        //   * `const_cache` holds const values forced under the layer's declarations.
        //   * `host_calls` holds host calls typed under the layer's provisions.
        //
        // Cleared wholesale rather than per-symbol: a layer discard is rare (it costs a
        // load), and knowing which entries a layer influenced would mean tracking a
        // dependency edge at every memo write on the hot path.
        self.op_body_cache.clear();
        self.host_calls.clear();
        // NOT a `clear()`: an in-flight `Forcing` sentinel must survive. `force_const`
        // inserts one and then evaluates the const's body through `eval_node_isolated`,
        // which runs a NESTED `run()` — and `run` sweeps every iteration. So any layer
        // discarded while a const is being forced would drop that const's own marker, and
        // a self-referential const would then recurse to `StepsExhausted` instead of the
        // loud `ConstCycle` the sentinel exists to report. Only computed VALUES can go
        // stale under a layer; a marker is control state, not a memo.
        self.const_cache
            .retain(|_, entry| matches!(entry, ConstCacheEntry::Forcing));
    }

    /// The KB this interpreter was lent goes back to its owner — the resolver, for a
    /// bridged run (`KnowledgeBase::run_in_bridge_interp`) — with no scoped-KB layer
    /// (`KB.loaded`) still applied to it.
    ///
    /// A layer is applied IN PLACE, to the one KB, and undone only when its last holder is
    /// gone ([`Self::sweep_layers`]). The interpreter's own holders go first — a const forced
    /// in the run caches its value — and a run whose holders all went inside it has nothing
    /// left. What still holds a layer is then the `outcome`: the value it answers, or the
    /// payload of the raise it reports. Neither may leave, since the layer is discarded
    /// here and a handle to it would refer to nothing, so the outcome becomes
    /// [`EvalError::ScopedKbOutlivesCall`], naming the raise when there was one.
    pub(crate) fn release_layers_for_handback(&mut self, outcome: &mut Result<Value, EvalError>) {
        self.const_cache
            .retain(|_, entry| matches!(entry, ConstCacheEntry::Forcing));
        self.sweep_layers();
        if self.layers.depth() == 0 {
            return;
        }
        let refused = match outcome {
            Ok(_) => Some(EvalError::ScopedKbOutlivesCall { raised: None }),
            Err(EvalError::Raised { payload, .. }) => Some(EvalError::ScopedKbOutlivesCall {
                raised: Some(render_raised_payload(&self.kb, payload)),
            }),
            // An error that carries no value holds no layer: what holds it is an arena of
            // this interpreter, and it goes with the interpreter.
            Err(_) => None,
        };
        if let Some(refused) = refused {
            *outcome = Err(refused);
        }
        let layers = self.layers.clone();
        layers.discard_all(&mut self.kb);
    }

    /// WI-SPGBP — how many scoped-KB layers are currently applied.
    pub fn layer_depth(&self) -> usize {
        self.layers.depth()
    }

    /// WI-20260913-2858G — how many activation frames are live. `0` between top-level
    /// calls. A run ends at its own FLOOR rather than at an empty stack, so a frame a run
    /// leaves behind no longer makes the next call fault — it is silent, and this is what
    /// makes it observable.
    pub fn activation_depth(&self) -> usize {
        self.stack.depth()
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
    /// handle into this interpreter's arena, read through the handle wherever it
    /// travels (`Substitution.lookup` / `.apply`, WI-20260923-9R5HN); the floundered
    /// `undecided` case additionally carries the undischarged goals as a
    /// `List[Term]`, so the residual is no longer silently dropped here.
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
            // WI-20260911-8Y5BE — a pull on a stream whose search faulted.
            Faulted,
        }

        // Through the HANDLE's arena (`StreamHandle::with_source_mut`, WI-20260923-9R5HN).
        let action = handle.with_source_mut(|src| match src {
            StreamSource::Empty => (StreamSource::Empty, Action::Done),
            StreamSource::Faulted => (StreamSource::Faulted, Action::Faulted),
            StreamSource::Resolver {
                search: None,
                layer,
            } => (
                StreamSource::Resolver {
                    search: None,
                    layer,
                },
                Action::Done,
            ),
            StreamSource::Resolver {
                search: Some(stream),
                layer,
            } => {
                // The layer stays in the slot across the pump: `search` is taken and put
                // back as the continuation, and the layer must outlive both halves.
                (
                    StreamSource::Resolver {
                        search: None,
                        layer,
                    },
                    Action::PumpResolver(stream),
                )
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
            Action::Faulted => Err(self.raise_stream_misused(
                "a pull on a stream whose search already raised".to_string(),
            )),
            Action::YieldSelf(v) => Ok(Some((v, handle.clone()))),
            Action::PumpResolver(stream) => {
                let result = stream.split_first(&mut self.kb);
                match result {
                    Err(failure) => Err(self.fault_stream(handle, failure)),
                    Ok(Some((sol, rest))) => {
                        handle.with_source_mut(|prev| {
                            // Carry the layer forward onto the continuation — the
                            // rest of the search reads the same scoped KB.
                            let layer = match prev {
                                StreamSource::Resolver { layer, .. } => layer,
                                _ => unreachable!(
                                    "WI-SPGBP: a pumped resolver slot holds a Resolver"
                                ),
                            };
                            (
                                StreamSource::Resolver {
                                    search: Some(rest),
                                    layer,
                                },
                                (),
                            )
                        });
                        let solution = self.make_solution_value(sol)?;
                        Ok(Some((solution, handle.clone())))
                    }
                    Ok(None) => {
                        handle.with_source_mut(|_| (StreamSource::Empty, ()));
                        Ok(None)
                    }
                }
            }
            Action::PumpMaterialized { search, columns } => {
                // WI-714: pump one resolver step, then materialize the answer onto
                // the relation's free variables (`columns`) — the one place a
                // relation solution becomes a value row.
                let result = search.split_first(&mut self.kb);
                match result {
                    // WI-20260911-8Y5BE — the RELATION face takes the same fault arm. It
                    // used to raise `relation_floundered` for a faulted goal (which
                    // residualizes) — "never decided" for a goal that could not be asked,
                    // and a payload the SLD bridge SCHEDULES rather than reports — or,
                    // for a faulted branch that yielded nothing, to drop the fault.
                    Err(failure) => Err(self.fault_stream(handle, failure)),
                    Ok(Some((sol, rest))) => {
                        let cols = columns.clone();
                        handle.with_source_mut(move |_| {
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
                    Ok(None) => {
                        handle.with_source_mut(|_| (StreamSource::Empty, ()));
                        Ok(None)
                    }
                }
            }
            Action::PumpLeft { left, right } => match self.stream_split_first(&left)? {
                Some((v, left_rest)) => {
                    handle.with_source_mut(|_| {
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

    /// WI-20260911-8Y5BE — a resolver search behind `handle` reported a FAULT, or
    /// (WI-20260913-P9QBF) ran dry with a branch cut at a depth limit: park the slot as
    /// [`stream::StreamSource::Faulted`] and raise the declared `evaluation_failure` or
    /// `search_truncated`. The one arm both resolver pumps take, so the execute face and
    /// the relation face cannot disagree about a faulted or a truncated search.
    ///
    /// THE CONTINUATION IS NOT KEPT, and the slot is not `Empty` either: a caller that
    /// catches the raise and pulls again is refused with `stream_misused` (as on the host
    /// bridge) rather than told the stream ended, which would read the rows it already
    /// has as a complete answer set — and an `mplus` over it would move silently on to
    /// its right half.
    fn fault_stream(
        &mut self,
        handle: &value::StreamHandle,
        failure: crate::kb::resolve::SearchFailure,
    ) -> EvalError {
        use crate::kb::resolve::SearchFailure;
        handle.with_source_mut(|_| (stream::StreamSource::Faulted, ()));
        match failure {
            SearchFailure::Faulted(fault) => {
                self.raise_evaluation_failure(fault.residual, fault.error.message, fault.error.at)
            }
            SearchFailure::Truncated { limit } => self.raise_search_truncated(limit),
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
    /// keyed by column name (order-faithful, §4.6) at EVERY arity ≥ 1 (WI-20260818-YQB1Y
    /// dropped the 1-collapse — see the note at the `Value::Tuple` build below) and
    /// `Value::Unit` for zero columns (a boolean/membership relation — non-empty ⇔
    /// provable). NotFound is just the empty stream, no bespoke nil arm.
    ///
    /// WI-20260827-3ZNBC — A COLUMN IS THE BOUND VALUE ON ITS OWN CARRIER, and this
    /// REPLACES WI-714's original sentence ("REIFY it to a native value … so the
    /// column reads as its element sort, not a raw Term handle — a `Relation[String]`
    /// yields `Value::Str`, a `Relation[Board]` an entity"). A column typed `String`
    /// still DENOTES that string; what changed is that it may denote it as a
    /// hash-consed `Value::Term`, a `Value::Node` occurrence, or a native `Value::Str`
    /// — whichever the search proved it on — and the reader asks
    /// [`TermView::literal_string`](crate::kb::term_view::TermView::literal_string)
    /// (or `literal_int64` / `head` / `pos_arg` / …) rather than matching one variant.
    ///
    /// WHY, since the reification was cheap and the readers were not: the duty to
    /// convert was UNENFORCED AT EVERY PRODUCER. Nothing made a new site that hands a
    /// binding onward call the normalizer, and forgetting failed at RUNTIME with a
    /// type error rather than at compile time — which is exactly how this drain came
    /// to hand `Int64.add` a `Value::Term` it could not read (WI-20260827-2YHZ3).
    /// Moving the read to the point of USE makes the consumer's own code the
    /// enforcement: a reader that asks `literal_string` cannot be handed a carrier it
    /// fails to understand, because the question it asks is the one every carrier
    /// answers. The reification also interned a term per bridged occurrence operand —
    /// a store write for a read, pinned for the KB's lifetime, and the occurrence's
    /// span discarded.
    ///
    /// THE ONE SERVICE THAT WENT WITH IT, stated so it is not rediscovered as a bug:
    /// the reifier bottomed out in `builtins::materialize_entity`, which DEFAULTS a
    /// declared `Option[T]` field the fact leaves unsupplied to `none()` (the loader
    /// fills such a slot with a synthetic `Var` so the discrim tree can index the fact
    /// uniformly — `kb/load.rs`'s partial-named-arg expansion). A handle-carried entity
    /// column keeps that `Var`, so `row.item.context` on an omitted optional field now
    /// reads the var rather than `none()`. It fails LOUDLY — a `case some(v)`/`case
    /// none()` over a var matches neither arm and raises `MatchFailed` — and no path
    /// in the corpus reaches it (no relation ranges over an entity with unsupplied
    /// optional fields). The defaulting is not lost, only no longer applied HERE: it
    /// stays where it belongs, on `term_as_entity`, the reflect operation whose whole
    /// job is Term → Entity. If a column ever needs it, the honest home is the field
    /// READ (`reflect_field_access`), where it would serve every carrier at once —
    /// that is a capability, not part of this move.
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
            // A `Solution` can now say WHY it is not definite (`Solution::undecided` —
            // no ANSWER, as opposed to no BINDING), and this face does not read it,
            // deliberately: BOTH producers of an undecided answer (the resolver's
            // open-world guard and its opaque-skolem reconsideration) fire ONLY under a
            // Γ overlay, and `gamma` is set at exactly one site in the tree
            // (`typing::prove_from_gamma`'s bridge). No resolve that reaches THIS face
            // has it set, so a branch here would be one nothing can drive. What would
            // change that is a producer OUTSIDE the Γ bridge, not merely a second cause
            // — an earlier draft of this note said "a second producer", and the same
            // change then added one without making this face reachable.
            // `prove_from_gamma_verdict` is the reader that exists today.
            return Err(self.raise_relation_floundered(sol.residual));
        }
        // Zero free variables → Unit (membership relation).
        if columns.is_empty() {
            return Ok(Value::Unit);
        }
        let mut named: Vec<(crate::intern::Symbol, Value)> = Vec::with_capacity(columns.len());
        for &(name, vid) in columns {
            // Read the binding through `answer_binding` — the single canonical
            // ANSWER reader (WI-20260827-2YHZ3), which chases the PARENT frame chain
            // AND the uncompressed var links a builtin bind leaves behind. A plain
            // `bindings` scan would miss a binding held in a parent frame; the bare
            // `resolve_as_value` this used to call missed the other half, and missed
            // it SILENTLY — a column bound by a rule-body builtin (`rule r(?x) :- ?x
            // <=> 6`) came back `Value::Var`, i.e. reported unbound, and fell into
            // the "genuinely binds nothing" arm below that the paragraph after this
            // one describes. The binding rides on WHATEVER CARRIER THE SEARCH PROVED
            // IT ON — a hash-consed `Value::Term` from a fact match, a `Value::Node`
            // occurrence from a rule-body builtin (WI-246: a rule body's atoms ride as
            // occurrences), a native `Value::Entity` from an external extent row —
            // and it is handed on unconverted, with ONE exception `answer_binding`
            // owns: a LITERAL on either of the first two carriers folds to its native
            // scalar (WI-20260904-EMVCB for the occurrence, WI-20260907-VM9Q7 for the
            // hash-consed term). See this method's doc for why the column is a HANDLE
            // the reader views through rather than a reified native value
            // (WI-20260827-3ZNBC, replacing WI-714's contract).
            //
            // An unbound free var still carries as itself. Post-WI-737 this is no
            // longer the flounder path (that raised above) but the narrower DEFINITE-
            // yet-unbound one: a head var no body goal constrains (`rule p(?x) :-
            // num(v: 1)`) yields a residual-FREE answer that genuinely binds nothing —
            // logically "for all x", a range-restriction violation Datalog rejects at
            // load time. Still a var in a typed column, so still a lie; but it is a
            // STATIC property of the rule, not an undecided search, so it wants a
            // load-time check rather than this drain-time gate. Not WI-737's scope.
            // That arm is now reached ONLY by that static case — which is what makes
            // a load-time check the right home for it.
            let bound = match self.kb_mut().answer_binding(vid, &sol.subst) {
                Some(v) => v,
                None => Value::Var(Var::Global(vid)),
            };
            named.push((name, bound));
        }
        // WI-20260818-YQB1Y — NO 1-COLLAPSE. A one-column row used to return the bare
        // element value here, dropping the column name; it is now the one-field tuple
        // `(age: 30)`, so the row a caller receives has exactly the columns the schema
        // type states at EVERY arity. This is the VALUE half of the paired convention
        // kernel-language.md §6.8 required to move together with the type half
        // (`relation_schema_type`, kb/typing.rs) and the term half (the `.( )` desugar,
        // parse/convert.rs).
        //
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

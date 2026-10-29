//! Effect handler dispatch (proposal 026 §Effects, M5).
//!
//! An `EffectHandler` is a `FnMut` keyed by *effect-sort* qualified name.
//! When an operation is invoked whose effect row names that sort, the
//! handler is called with `(interp, op_sym, args)` and produces the
//! operation's return `Value`. The handler closure owns the resource it
//! represents — `Stdout` for `ConsoleOutput`, a test buffer for capture,
//! the wall clock for `Clock`, etc. Replacing a handler replaces the
//! resource; the interpreter itself holds no effect-specific state.

use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::HashMap;
use std::io::{self, BufRead, Write};
use std::rc::Rc;

use crate::intern::Symbol;
use crate::kb::node_occurrence::NodeOccurrence;

use super::value::Dictionary;
use super::error::{RaisePoint, ThrowRoute};
use super::{EvalError, HandlerErrorReason, Interpreter, RaisedType, Value};

/// Where a handler's raise is judged: the raise the `Error` handler answers, or the `Error`
/// label of the operation a handler of another effect performs (`None`: its row declares
/// none).
enum RaiseAt<'a> {
    Raise {
        payload: &'a Value,
        raised_type: &'a RaisedType,
    },
    Row(Option<&'a RaisedType>),
}

impl RaiseAt<'_> {
    /// The type the raise point admits; `None` where it admits nothing.
    fn admits(&self) -> Option<&RaisedType> {
        match self {
            RaiseAt::Raise { raised_type, .. } => Some(raised_type),
            RaiseAt::Row(admits) => *admits,
        }
    }
}

/// Opaque marker for a resolver-level alternative continuation the runtime
/// can re-enter on backtrack. Placeholder until the Branch substrate
/// (WI-075: `push_choice` + activation-stack snapshots) lands — no handler
/// constructs one yet, so `HandlerAction::Choice` is unreachable today.
#[derive(Debug, Clone)]
pub struct AltMarker;

/// Snapshot of the activation stack at an operation call site, used to
/// suspend and later resume evaluation. Placeholder until the
/// suspend/resume substrate lands — no handler constructs one yet, so
/// `HandlerAction::Suspend` is unreachable today.
#[derive(Debug, Clone)]
pub struct ContSnapshot;

/// What a handler tells the runtime to do with the (implicit) continuation
/// when it returns — proposal 027 §Outputs, the `HandlerAction` carrier.
/// The handler never receives the continuation as a value; it returns one
/// of these variants and the dispatch site (`Interpreter::run_effect_handler`, under
/// `Interpreter::dispatch_effect_operation` and [`Interpreter::invoke_effect_handler`])
/// interprets it.
///
/// Only `Pure` and `Throw` are interpreted today (WI-389). `Fail`,
/// `Choice`, and `Suspend` need the Branch / suspend-resume substrate
/// (WI-075); the dispatch site rejects them with a clear error until then.
#[derive(Debug)]
pub enum HandlerAction {
    /// Resume the current path with this value (linear — the common case).
    Pure(Value),
    /// Raise `payload` at the type its type value holds: the `TypeValue` dictionary of that
    /// type (proposal 071 §1.3), the one the `Error` handler was handed for a re-raise, or
    /// [`Interpreter::type_value_of`] for a value of the handler's own. The dispatch site
    /// turns this into [`EvalError::Raised`]. Error-ness lives *here*, in the channel — the
    /// payload is an ordinary opaque `Value`, untagged.
    ///
    /// Applied only where the raise point admits the type, by the test a boundary runs
    /// (`TypePattern.admits`): for the `Error` handler the raise it answers, so every boundary
    /// that would catch that raise still catches the throw; for a handler of another effect
    /// the `Error` label of the operation it performs, none where its row declares none.
    /// Otherwise [`HandlerErrorReason::ThrowNotAdmitted`](super::HandlerErrorReason).
    Throw(Value, super::value::Dictionary),
    /// The `Error` handler's answer to `raise`: let the raise it was handed continue,
    /// unchanged — its payload and the type it carries. What a handler that only observes
    /// raises (one that logs them) answers, and what the default handler answers. A handler of
    /// any other effect has no raise to rethrow, and its `Rethrow` is refused.
    Rethrow,
    /// Abort the current resolver branch (resolver-level failure). The
    /// `Value` is the failure reason/diagnostic — symmetric with `Throw`,
    /// it records *why* the branch was abandoned so an exhausted search can
    /// explain itself. (`Throw` propagates past choice points as an error;
    /// `Fail` backtracks to the nearest alternative.)
    Fail(Value),
    /// Resume now with `value`; on backtrack, try `alts` in list order.
    Choice(Value, Vec<AltMarker>),
    /// Paused: the runtime returns to its driver and resumes later via the
    /// snapshot.
    Suspend(ContSnapshot),
}

impl HandlerAction {
    /// The variant name, for diagnostics.
    fn kind_name(&self) -> &'static str {
        match self {
            HandlerAction::Pure(_) => "Pure",
            HandlerAction::Throw(..) => "Throw",
            HandlerAction::Rethrow => "Rethrow",
            HandlerAction::Fail(_) => "Fail",
            HandlerAction::Choice(..) => "Choice",
            HandlerAction::Suspend(..) => "Suspend",
        }
    }
}

/// Handler for a single effect sort. Dispatched on the operation symbol
/// (e.g., `print` vs `println` both fall into `ConsoleOutput`). Returns a
/// [`HandlerAction`] describing what the runtime should do with the
/// continuation; the `Err` channel is reserved for genuine internal faults
/// (I/O errors, arity mismatches), *not* for anthill-level errors — those
/// ride out through `HandlerAction::Throw`. A raise that leaves a handler through `Err` all
/// the same (one of anthill code it calls) is held to the raise point as a `Throw` is.
///
/// The `Error` handler answers a raise, and is handed `[payload, type_value]`: the raised
/// value and the `TypeValue` dictionary of the type the raise carries
/// ([`super::value::Dictionary::from_value`] reads it back) — `[payload]` alone for a raise of
/// the unknown type, which has none ([`RaisedType::Unknown`]).
pub type EffectHandler =
    Box<dyn FnMut(&mut Interpreter, Symbol, &[Value]) -> Result<HandlerAction, EvalError>>;

// ── Default Console handlers (stdio) ───────────────────────────

/// Short name of an op ends with "println" — matches both the stdout
/// `println` and stderr `eprintln` variants, which both append a newline.
fn op_appends_newline(op_name: &str) -> bool {
    op_name == "println" || op_name == "eprintln"
}

/// The text a Console write handler was handed, read on WHATEVER CARRIER it
/// arrived on.
///
/// WI-20260827-14EV6. This used to be `args.get(1).and_then(Value::as_str)`,
/// which saw the native `Value::Str` alone — so `println(c, s)` raised
/// `TypeMismatch { expected: "String", got: "missing or non-String argument" }`
/// for a string that WAS a string, whenever it reached the handler hash-consed
/// or as an occurrence. The message was wrong twice: it blamed the argument for
/// the reader's blindness, and it named "non-String" for a String.
///
/// It is reachable from the language, not only from a host `interp.call`:
/// WI-20260827-3ZNBC stopped normalizing relation columns, so
/// `println(c, person_name.head.n)` hands this a `Value::Term`. See
/// `wi14ev6_carrier_neutral_scalar_read_test`.
///
/// The two "cannot read it" cases stay APART, because they are different bugs
/// in the caller: an argument that is absent (a handler bound to an operation
/// of the wrong arity) and one that denotes something other than a string.
/// That is the whole reason this is not simply `builtins::str_operand` — the
/// READ is shared with it (`str_operand_opt`), only the refusals differ.
///
/// `Cow`, not `String`: a native `Value::Str` still BORROWS, so `print` in a
/// loop allocates nothing it did not allocate before. Only a handle carrier
/// pays a clone, and that carrier could not be printed at all previously.
fn console_text<'a>(interp: &Interpreter, args: &'a [Value]) -> Result<Cow<'a, str>, EvalError> {
    let arg = args.get(1).ok_or_else(|| EvalError::TypeMismatch {
        expected: "String",
        got: format!("no argument at index 1 (got {} argument(s))", args.len()),
    })?;
    super::builtins::str_operand_opt(interp.kb(), arg).ok_or_else(|| EvalError::TypeMismatch {
        expected: "String",
        got: format!("a {} that denotes no string", arg.type_name()),
    })
}

/// Default `ConsoleOutput` handler — writes to `io::stdout()`. `print` and
/// `println` differ only in the trailing newline.
pub fn stdio_console_output_handler() -> EffectHandler {
    stdio_console_write_handler(io::stdout())
}

/// Default `ConsoleError` handler — writes to `io::stderr()`.
pub fn stdio_console_error_handler() -> EffectHandler {
    stdio_console_write_handler(io::stderr())
}

fn stdio_console_write_handler<W: Write + 'static>(sink: W) -> EffectHandler {
    let sink = Rc::new(RefCell::new(sink));
    Box::new(move |interp, op_sym, args| {
        let s = console_text(interp, args)?;
        let mut out = sink.borrow_mut();
        out.write_all(s.as_bytes())
            .map_err(|e| EvalError::Internal(e.to_string()))?;
        if op_appends_newline(interp.kb().local_name_of(op_sym)) {
            out.write_all(b"\n")
                .map_err(|e| EvalError::Internal(e.to_string()))?;
        }
        out.flush()
            .map_err(|e| EvalError::Internal(e.to_string()))?;
        Ok(HandlerAction::Pure(Value::Unit))
    })
}

/// Default `Clock` handler — the wall clock, in RFC-3339-with-Z form
/// (`YYYY-MM-DDTHH:MM:SSZ`, UTC, second granularity), which `Time.now` answers.
pub fn system_clock_handler() -> EffectHandler {
    Box::new(|_interp, _op_sym, _args| {
        Ok(HandlerAction::Pure(Value::Str(
            chrono::Utc::now().format("%Y-%m-%dT%H:%M:%SZ").to_string(),
        )))
    })
}

/// Default `ConsoleInput` handler — reads a line from `io::stdin()`.
/// The trailing newline is stripped to match common user expectation.
pub fn stdio_console_input_handler() -> EffectHandler {
    let stdin = Rc::new(RefCell::new(io::BufReader::new(io::stdin())));
    Box::new(move |_interp, _op_sym, _args| {
        let mut buf = String::new();
        stdin
            .borrow_mut()
            .read_line(&mut buf)
            .map_err(|e| EvalError::Internal(e.to_string()))?;
        if buf.ends_with('\n') {
            buf.pop();
        }
        if buf.ends_with('\r') {
            buf.pop();
        }
        Ok(HandlerAction::Pure(Value::Str(buf)))
    })
}

/// Storage for a captured-output handler — shared with test code so it
/// can inspect what was written. Thread-local only (Rc), same constraint
/// as the rest of the evaluator.
pub type SharedBuffer = Rc<RefCell<String>>;

/// Build a Console write handler that appends to a shared buffer.
/// Use for ConsoleOutput or ConsoleError — the caller picks which by
/// passing the returned handler to `register_effect_handler` with the
/// corresponding effect-sort qualified name.
pub fn buffered_console_handler(buf: SharedBuffer) -> EffectHandler {
    Box::new(move |interp, op_sym, args| {
        let s = console_text(interp, args)?;
        buf.borrow_mut().push_str(&s);
        if op_appends_newline(interp.kb().local_name_of(op_sym)) {
            buf.borrow_mut().push('\n');
        }
        Ok(HandlerAction::Pure(Value::Unit))
    })
}

/// Queue of pre-scripted input lines — shared with test code so it can
/// inspect remaining / unused entries.
pub type SharedInputScript = Rc<RefCell<std::collections::VecDeque<String>>>;

/// Build a `ConsoleInput` handler that drains a scripted queue. Returns
/// an `EOF` internal error when the queue is empty — tests that hit this
/// have supplied fewer lines than the program consumed.
pub fn scripted_console_input_handler(script: SharedInputScript) -> EffectHandler {
    Box::new(move |_interp, _op_sym, _args| {
        script
            .borrow_mut()
            .pop_front()
            .map(|s| HandlerAction::Pure(Value::Str(s)))
            .ok_or_else(|| EvalError::Internal("scripted console input exhausted".into()))
    })
}

// ── Default Error handler ──────────────────────────────────────

/// Default `Error` handler (proposal 027 §Error, WI-073). `raise(error: T)`
/// carries the error payload as `args[0]` and its type value as `args[1]`; the handler
/// answers [`HandlerAction::Rethrow`], and the raise continues as
/// [`EvalError::Raised`], with the type it carries (proposal 071 §1.3), to the innermost
/// `Error.reify` boundary that admits it.
pub fn default_error_handler() -> EffectHandler {
    Box::new(|_interp, _op_sym, args| {
        if args.is_empty() {
            return Err(EvalError::ArityMismatch {
                op: "Error.raise",
                expected: 1,
                got: 0,
            });
        }
        Ok(HandlerAction::Rethrow)
    })
}

// ── Interpreter integration ────────────────────────────────────

/// Where a raise the runtime builds takes its type (proposal 071 §1.3; user, 2026-10-24).
#[derive(Clone, Copy)]
pub(crate) enum RaiseBy {
    /// From the running host operation, whose `requires TypeValue[T = X]` its caller
    /// threads to it ([`Interpreter::raise_error`]).
    Operation,
    /// A payload the runtime raises with no operation behind the raise — a pattern that
    /// fails, a stream pulled: its sort's constant evidence, which the error layer holds.
    Account(fn(&super::ErrorLayer) -> &super::value::Dictionary),
}

/// The handler map. Stored behind an `Option` inside `Interpreter` so we
/// can `.take()` the handler out of the map, invoke it (which needs
/// `&mut Interpreter`), and put it back — without fighting the borrow
/// checker over a simultaneously-borrowed map entry.
pub(crate) struct EffectRegistry {
    handlers: HashMap<Symbol, Option<EffectHandler>>,
}

impl EffectRegistry {
    pub fn new() -> Self {
        Self {
            handlers: HashMap::new(),
        }
    }

    pub fn insert(&mut self, effect_sym: Symbol, h: EffectHandler) -> Option<EffectHandler> {
        self.handlers.insert(effect_sym, Some(h)).and_then(|o| o)
    }

    pub fn remove(&mut self, effect_sym: Symbol) -> Option<EffectHandler> {
        self.handlers.remove(&effect_sym).and_then(|o| o)
    }

    /// Whether an effect handler is currently installed for `effect_sym`.
    /// Used by `raise_error` to decide between routing through the handler
    /// and the default Throw fallback.
    pub fn has(&self, effect_sym: Symbol) -> bool {
        self.handlers
            .get(&effect_sym)
            .map_or(false, |o| o.is_some())
    }

    /// Temporarily take the handler out of the map so the caller can run
    /// it with `&mut Interpreter` access. The caller must put it back via
    /// [`Self::return_handler`] (or it stays torn out and subsequent
    /// lookups fail with the standard "no handler" error).
    pub fn take_for_invoke(&mut self, effect_sym: Symbol) -> Option<EffectHandler> {
        self.handlers.get_mut(&effect_sym).and_then(|o| o.take())
    }

    /// Put a handler back into its slot without re-hashing — assumes the
    /// slot was just vacated by [`Self::take_for_invoke`] and therefore
    /// already exists in the map.
    pub fn return_handler(&mut self, effect_sym: Symbol, h: EffectHandler) {
        if let Some(slot) = self.handlers.get_mut(&effect_sym) {
            *slot = Some(h);
        } else {
            self.handlers.insert(effect_sym, Some(h));
        }
    }
}

impl Interpreter {
    /// Register an effect handler. Overwrites any existing handler for the
    /// same effect sort.
    pub fn register_effect_handler(
        &mut self,
        effect_qname: &str,
        h: EffectHandler,
    ) -> Result<(), EvalError> {
        let sym = self.kb.try_resolve_symbol(effect_qname).ok_or_else(|| {
            EvalError::UnknownOperation {
                name: effect_qname.to_string(),
            }
        })?;
        self.effect_handlers.insert(sym, h);
        Ok(())
    }

    /// Remove and return a previously registered handler. Returns `None`
    /// if no handler was registered for this effect sort.
    pub fn take_effect_handler(&mut self, effect_qname: &str) -> Option<EffectHandler> {
        let sym = self.kb.try_resolve_symbol(effect_qname)?;
        self.effect_handlers.remove(sym)
    }

    /// Invoke the handler for `effect_qname` with an operation symbol already resolved
    /// and the arguments: a test's route. A raise is routed by [`Self::raise_typed`], which
    /// reads the `Error` handler's [`HandlerAction::Rethrow`] itself. The builtins of
    /// an effect operation go through `Self::dispatch_effect_operation` instead, which
    /// takes the handler before it resolves the operation.
    pub fn invoke_effect_handler(
        &mut self,
        effect_qname: &str,
        op_sym: Symbol,
        args: &[Value],
    ) -> Result<Value, EvalError> {
        let (effect_sym, handler) = self.take_handler_for_invoke(effect_qname)?;
        self.run_effect_handler(effect_sym, handler, effect_qname, op_sym, args)
    }

    /// [`Self::invoke_effect_handler`] for the operation named `op_qname`: the entry of the
    /// builtins that dispatch an effect operation (`effect_dispatcher!`). The handler is
    /// taken before the operation is resolved, so a run with none says which effect it
    /// needed whatever its KB holds — a rule body's run, and a load's run of a `const_map`
    /// value source over an empty KB (`builtins::host_const_literal`).
    pub(crate) fn dispatch_effect_operation(
        &mut self,
        effect_qname: &str,
        op_qname: &str,
        op_short: &str,
        args: &[Value],
    ) -> Result<Value, EvalError> {
        let (effect_sym, handler) = self.take_handler_for_invoke(effect_qname)?;
        match crate::eval::builtins::require_symbol(self, op_qname, op_short) {
            Ok(op_sym) => self.run_effect_handler(effect_sym, handler, effect_qname, op_sym, args),
            Err(e) => {
                self.effect_handlers.return_handler(effect_sym, handler);
                Err(e)
            }
        }
    }

    /// The handler registered for `effect_qname`, taken for one invocation. A KB that does
    /// not declare the effect has no handler registered for it either, so both misses are
    /// [`EvalError::UnhandledEffect`].
    fn take_handler_for_invoke(
        &mut self,
        effect_qname: &str,
    ) -> Result<(Symbol, EffectHandler), EvalError> {
        let unhandled = || EvalError::UnhandledEffect {
            name: effect_qname.to_string(),
        };
        let effect_sym = self
            .kb
            .try_resolve_symbol(effect_qname)
            .ok_or_else(unhandled)?;
        let handler = self
            .effect_handlers
            .take_for_invoke(effect_sym)
            .ok_or_else(unhandled)?;
        Ok((effect_sym, handler))
    }

    fn run_effect_handler(
        &mut self,
        effect_sym: Symbol,
        handler: EffectHandler,
        effect_qname: &str,
        op_sym: Symbol,
        args: &[Value],
    ) -> Result<Value, EvalError> {
        match self.run_handler(effect_sym, handler, op_sym, args) {
            Ok(action) => self.interpret_handler_action(action, effect_qname, op_sym),
            // A raise leaving the handler through its `Err` channel is held to the operation's
            // row as its `Throw` is.
            Err(EvalError::Raised {
                payload,
                raised_type,
            }) => {
                let admits = self.raise_point_admits()?;
                let at = RaiseAt::Row(admits.as_ref());
                Err(self.admitted_throw(effect_qname, op_sym, at, ThrowRoute::Err, payload, raised_type))
            }
            Err(e) => Err(e),
        }
    }

    /// Run `handler` for `op_sym` and put it back. The `Error` handler answers a raise and
    /// performs no operation, so it runs with no builtin's channel: what it throws is at the
    /// type value it gives, held to the raise it answers. Any other handler performs the effect
    /// operation running, and keeps its channel, whose row says what its throw may raise.
    fn run_handler(
        &mut self,
        effect_sym: Symbol,
        mut handler: EffectHandler,
        op_sym: Symbol,
        args: &[Value],
    ) -> Result<HandlerAction, EvalError> {
        let answers_a_raise = self.kb.error_sort_sym() == Some(effect_sym);
        let channel = if answers_a_raise { self.running_builtin.take() } else { None };
        let action = handler(self, op_sym, args);
        if answers_a_raise {
            self.running_builtin = channel;
        }
        self.effect_handlers.return_handler(effect_sym, handler);
        action
    }

    /// What a handler's `action` means for the call that invoked it — a handler of any effect
    /// but `Error`, whose answer to a raise [`Self::raise_typed`] reads.
    fn interpret_handler_action(
        &mut self,
        action: HandlerAction,
        effect_qname: &str,
        op_sym: Symbol,
    ) -> Result<Value, EvalError> {
        match action {
            HandlerAction::Pure(v) => Ok(v),
            // A raise of the effect operation the handler performs, held to the `Error` label
            // its row declares — to nothing, where it declares none.
            HandlerAction::Throw(payload, type_value) => {
                let admits = self.raise_point_admits()?;
                let thrown = RaisedType::Evidence(type_value);
                let at = RaiseAt::Row(admits.as_ref());
                Err(self.admitted_throw(effect_qname, op_sym, at, ThrowRoute::Throw, payload, thrown))
            }
            HandlerAction::Rethrow => {
                Err(self.handler_error(effect_qname, op_sym, HandlerErrorReason::NoRaiseToRethrow))
            }
            unsupported => Err(self.not_yet_supported(effect_qname, op_sym, unsupported)),
        }
    }

    /// `payload`, raised by a handler at the type `thrown` carries — its `Throw`'s type value,
    /// or the type of a raise that leaves it through its `Err` channel (`route`) — as the raise
    /// it is where the raise point admits that type, and the refusal otherwise.
    fn admitted_throw(
        &mut self,
        effect_qname: &str,
        op_sym: Symbol,
        at: RaiseAt<'_>,
        route: ThrowRoute,
        payload: Value,
        thrown: RaisedType,
    ) -> EvalError {
        match self.throw_admitted(&at, &thrown) {
            Ok(true) => EvalError::Raised {
                payload,
                raised_type: thrown,
            },
            Ok(false) => match self.throw_not_admitted(at, route, &payload, &thrown) {
                Ok(reason) => self.handler_error(effect_qname, op_sym, reason),
                Err(e) => e,
            },
            Err(e) => e,
        }
    }

    /// Whether the raise point `at` admits `thrown`: the test a boundary runs
    /// (`TypePattern.admits`), on the types the two carry as a boundary reads a raise's
    /// ([`Self::raised_type_value`]) — so a raise of the unknown type is admitted only where
    /// the raise point's type is unknown too.
    fn throw_admitted(&mut self, at: &RaiseAt<'_>, thrown: &RaisedType) -> Result<bool, EvalError> {
        let Some(admits) = at.admits() else {
            return Ok(false);
        };
        let pattern = self.raised_type_value(admits)?;
        let thrown = self.raised_type_value(thrown)?;
        crate::kb::typing::type_pattern_admits(&self.kb, &pattern, &thrown)
            .map_err(|u| EvalError::TypePatternUnjudged { detail: u.detail(&self.kb) })
    }

    fn throw_not_admitted(
        &mut self,
        at: RaiseAt<'_>,
        route: ThrowRoute,
        thrown: &Value,
        thrown_type: &RaisedType,
    ) -> Result<HandlerErrorReason, EvalError> {
        let raise_point = match at {
            RaiseAt::Raise {
                payload,
                raised_type,
            } => {
                let ty = self.raised_type_value(raised_type)?;
                RaisePoint::Raise {
                    payload: self.print_value(payload),
                    ty: crate::kb::typing::type_display_name_value(&self.kb, &ty),
                }
            }
            RaiseAt::Row(admits) => RaisePoint::Row {
                label: match admits {
                    Some(admits) => {
                        let ty = self.raised_type_value(admits)?;
                        Some(crate::kb::typing::type_display_name_value(&self.kb, &ty))
                    }
                    None => None,
                },
            },
        };
        let thrown_type = self.raised_type_value(thrown_type)?;
        Ok(HandlerErrorReason::ThrowNotAdmitted {
            raise_point,
            route,
            thrown: self.print_value(thrown),
            thrown_type: crate::kb::typing::type_display_name_value(&self.kb, &thrown_type),
        })
    }

    fn print_value(&self, v: &Value) -> String {
        crate::persistence::print::TermPrinter::new(&self.kb).print_value(v)
    }

    fn handler_error(&self, effect_qname: &str, op_sym: Symbol, reason: HandlerErrorReason) -> EvalError {
        EvalError::HandlerError {
            effect: effect_qname.to_owned(),
            op: self.kb.qualified_name_of(op_sym).to_string(),
            reason,
        }
    }

    /// `Fail`, `Choice` and `Suspend` manipulate the continuation and need the Branch /
    /// suspend-resume substrate (WI-075): until then a loud error with the dispatch context
    /// and a captured backtrace, so the offending call site is locatable.
    fn not_yet_supported(&self, effect_qname: &str, op_sym: Symbol, action: HandlerAction) -> EvalError {
        // `Fail` carries a reason (the "why" of the branch abort), surfaced so the diagnostic
        // explains the failure though the resolver-fail path is not wired yet.
        let detail = match &action {
            HandlerAction::Fail(reason) => Some(format!("{reason:?}")),
            _ => None,
        };
        let reason = HandlerErrorReason::NotYetSupported {
            action: action.kind_name(),
            detail,
            backtrace: std::backtrace::Backtrace::force_capture(),
        };
        self.handler_error(effect_qname, op_sym, reason)
    }

    /// Raise an anthill-level `Error` effect carrying `payload`, routing it
    /// through the registered Error handler (proposal 027 RuntimeAPI
    /// `raise_error`, WI-195). A native builtin whose anthill signature
    /// declares `effects Error` uses this to surface a host-side failure as
    /// an anthill error — the same channel `Error.raise(x)` takes — instead
    /// of a raw `EvalError::Internal`. Routes through a custom Error handler
    /// if one is installed (catch / logging), else falls back to the default
    /// Throw semantics so the payload is never lost. Returns the resulting
    /// `EvalError` (`Raised { payload }` in the default case).
    ///
    /// This is *only* for failures an operation's `effects Error` actually
    /// covers. Internal-only conditions a builtin can hit (a missing store
    /// registration, a lowering bug) are NOT routed here — they stay
    /// `EvalError::Internal` faults, since no `effects Error` declared them.
    ///
    /// THE TYPE OF WHAT IT RAISES IS THREADED TO IT (proposal 071 §1.3; user, 2026-10-24):
    /// a host operation whose row raises `Error[X]` declares `requires TypeValue[T = X]` —
    /// refused at load if it does not (`LoadError::HostRaiseWithoutTypeValue`) — and the
    /// raise carries the dictionary its call was handed for that clause
    /// ([`Self::host_raised_type`]). One whose row says only `Error` raises a payload of a
    /// type not known ([`RaisedType::Unknown`]). Nothing is read off the payload.
    /// `Error.raise` is such an operation — its builtin raises through here, with the
    /// `TypeValue[T = T]` its call was handed — and a payload the runtime raises with no
    /// operation behind it carries its sort's constant ([`Self::raise_error_payload`]'s
    /// [`RaiseBy::Account`]).
    pub fn raise_error(&mut self, payload: Value) -> EvalError {
        match self.host_raised_type() {
            Ok(raised_type) => self.raise_typed(payload, raised_type),
            Err(e) => e,
        }
    }

    /// The type a raise of the running host function carries ([`Self::raise_point_admits`]).
    /// A host function whose operation's row declares no `Error` may not raise: a caller is
    /// typed as catching nothing from it, and the raise is refused where it happens.
    fn host_raised_type(&mut self) -> Result<RaisedType, EvalError> {
        match self.raise_point_admits()? {
            Some(raised_type) => Ok(raised_type),
            None => {
                let op = self.running_builtin.as_ref().map(|b| b.op);
                let name = op.map_or_else(String::new, |op| self.kb.qualified_name_of(op).to_string());
                Err(EvalError::RaiseTypeUnread {
                    detail: format!(
                        "`{name}` raised, and its row declares no `Error`: a caller is typed as \
                         catching nothing from it. Declare the `Error[…]` it raises on `{name}`, \
                         or report the failure as a fault"
                    ),
                })
            }
        }
    }

    /// The `TypeValue` dictionary of `value`'s type, read off the value as a host's own
    /// `interp.call("anthill.prelude.Error.raise", [value])` reads it: the type value a handler
    /// throws a value of its own at ([`HandlerAction::Throw`]).
    pub fn type_value_of(&mut self, value: &Value) -> Result<Dictionary, EvalError> {
        let raise =
            crate::eval::builtins::require_symbol(self, "anthill.prelude.Error.raise", "raise")?;
        match self.raise_type_of(raise, smallvec::SmallVec::new(), Some(vec![value.clone()])) {
            Ok(Some(RaisedType::Evidence(evidence))) => Ok(evidence),
            Ok(_) => Err(EvalError::Internal(
                "type_value_of: `Error.raise` states its payload's type by `requires \
                 TypeValue[T = T]`, and answered none"
                    .into(),
            )),
            // The reading's own words are about a raise and a call; nothing raised here.
            Err(EvalError::RaiseTypeUnread { .. } | EvalError::UnpinnedRequirement { .. }) => Err(EvalError::RaiseTypeUnread {
                detail: format!(
                    "no type value can be read off {}: the value does not pin its type. A \
                     handler re-raising passes the type value it was handed",
                    self.print_value(value)
                ),
            }),
            Err(e) => Err(e),
        }
    }

    /// What the running host function's raise point admits: the `TypeValue` dictionary its
    /// operation's `requires TypeValue[T = X]` slot holds in the channel its call was handed
    /// (`Interpreter::running_builtin`), [`RaisedType::Unknown`] where its row says only
    /// `Error`, and `None` where its row declares no `Error`.
    ///
    /// A HOST RAISE OUTSIDE ANY HOST FUNCTION — the `Error` handler's, which runs with no
    /// channel (`Interpreter::run_effect_handler`), or a host's direct
    /// [`Self::invoke_effect_handler`] — is of the unknown type: no operation states what it
    /// raises.
    fn raise_point_admits(&mut self) -> Result<Option<RaisedType>, EvalError> {
        let Some((op, requirements, args)) = self
            .running_builtin
            .as_ref()
            .map(|b| (b.op, b.requirements.clone(), b.args.clone()))
        else {
            return Ok(Some(RaisedType::Unknown));
        };
        self.raise_type_of(op, requirements, args)
    }

    /// [`Self::raise_point_admits`] of `op`, called with `requirements` and `args`.
    ///
    /// THE CHANNEL IS READ HERE, AS A BODY'S IS ON ENTRY, AND ONLY HERE: a call that does not
    /// raise resolves nothing. The type is the running operation's — the member's, where a
    /// value directed the call to it through its spec operation — and a slot its route
    /// stamped none for is filled from the argument values (`fill_missing_op_scoped_slots`):
    /// a host's call, the SLD bridge. What is still missing has no type in hand and is refused
    /// ([`EvalError::RaiseTypeUnread`]), before anything is raised.
    fn raise_type_of(
        &mut self,
        op: Symbol,
        requirements: smallvec::SmallVec<[(Symbol, Dictionary); 2]>,
        args: Option<Vec<Value>>,
    ) -> Result<Option<RaisedType>, EvalError> {
        let unread = |detail: String| EvalError::RaiseTypeUnread { detail };
        let slot = match crate::kb::typing::host_raise_type(&mut self.kb, op) {
            crate::kb::typing::HostRaiseType::Slot(i) => i,
            crate::kb::typing::HostRaiseType::Unknown => return Ok(Some(RaisedType::Unknown)),
            crate::kb::typing::HostRaiseType::NoErrorLabel => return Ok(None),
            crate::kb::typing::HostRaiseType::Projected => {
                return Err(unread(format!(
                    "`{}` raised, and its row names what it raises through a projection or a \
                     row variable: the type is the call's, which nothing threads to a host \
                     function. A host operation that raises names its `Error[X]` and requires \
                     `TypeValue[T = X]`",
                    self.kb.qualified_name_of(op)
                )))
            }
            crate::kb::typing::HostRaiseType::Unanswered { .. } => {
                return Err(unread(format!(
                    "`{}` raises `Error[…]` and requires no `TypeValue` of the payload, or \
                     raises more than one: the load refuses that of a `@[host_implemented]` \
                     operation, and a builtin registered over this one raises with no type in \
                     hand",
                    self.kb.qualified_name_of(op)
                )))
            }
            crate::kb::typing::HostRaiseType::NoDeclaration => {
                return Err(unread(format!(
                    "`{}` raised and is no declared operation: nothing states what it raises",
                    self.kb.qualified_name_of(op)
                )))
            }
        };
        let unpinned_detail = format!(
            "`{}` raised with no `TypeValue` evidence of its payload's type: its caller had none \
             to hand — a call whose arguments do not pin it",
            self.kb.qualified_name_of(op)
        );
        let mut requirements = requirements;
        if let Some(args) = args {
            self.fill_missing_op_scoped_slots(op, &args, &mut requirements)?;
        }
        let name = crate::kb::typing::op_dict_entries(&mut self.kb, op).name_at(&mut self.kb, slot);
        let Some(evidence) =
            name.and_then(|name| super::eval::find_requirement(&requirements, name).cloned())
        else {
            return Err(unread(unpinned_detail));
        };
        if let Err(detail) = crate::kb::typing::marker_refusal(&self.kb, evidence.impl_sort()) {
            return Err(EvalError::UnpinnedRequirement {
                detail,
                marker: evidence.impl_sort(),
            });
        }
        Ok(Some(RaisedType::Evidence(evidence)))
    }

    /// [`Self::raise_error`] for a raise that carries `raised_type`, routed through the `Error`
    /// handler where one is registered.
    ///
    /// The handler is handed the payload and its type value. IT SAYS WHETHER THE RAISE
    /// CONTINUES ([`HandlerAction::Rethrow`]) — this raise, with its type — or is replaced by a
    /// value it throws at a type value it gives ([`HandlerAction::Throw`]), which the raise's
    /// type must admit (user, 2026-10-27): a handler that logs and re-raises leaves every
    /// boundary catching what it caught. Told apart by the answer and never by comparing the
    /// thrown value with the raised one, which a payload holding an opaque value (a closure, a
    /// stream) never equals.
    pub(crate) fn raise_typed(&mut self, payload: Value, raised_type: RaisedType) -> EvalError {
        let error_sym = self.kb.error_sort_sym();
        if !error_sym.is_some_and(|s| self.effect_handlers.has(s)) {
            return EvalError::Raised {
                payload,
                raised_type,
            };
        }
        let op_sym = match self.kb.try_resolve_symbol("anthill.prelude.Error.raise") {
            Some(s) => s,
            None => self.kb_mut().intern("raise"),
        };
        let (effect_sym, handler) = match self.take_handler_for_invoke("anthill.prelude.Error") {
            Ok(h) => h,
            Err(e) => return e,
        };
        // The handler is handed the type value with the payload; a raise of the unknown type
        // has none.
        let mut args = vec![payload];
        if let RaisedType::Evidence(evidence) = &raised_type {
            args.push(evidence.as_value().clone());
        }
        let answer = self.run_handler(effect_sym, handler, op_sym, &args);
        let payload = args.swap_remove(0);
        const EFFECT: &str = "anthill.prelude.Error";
        let at = RaiseAt::Raise {
            payload: &payload,
            raised_type: &raised_type,
        };
        match answer {
            Ok(HandlerAction::Rethrow) => EvalError::Raised {
                payload,
                raised_type,
            },
            Ok(HandlerAction::Throw(thrown, type_value)) => self.admitted_throw(
                EFFECT,
                op_sym,
                at,
                ThrowRoute::Throw,
                thrown,
                RaisedType::Evidence(type_value),
            ),
            // `raise` returns `Nothing`: a raise does not resume.
            Ok(HandlerAction::Pure(v)) => self.handler_error(
                EFFECT,
                op_sym,
                HandlerErrorReason::ResumedARaise {
                    returned: v.type_name(),
                },
            ),
            Ok(other) => self.not_yet_supported(EFFECT, op_sym, other),
            // A raise leaving the handler through its `Err` channel — one it makes itself, or
            // one of anthill code it calls — is held to the raise it answered as a throw is.
            Err(EvalError::Raised {
                payload: thrown,
                raised_type: thrown_type,
            }) => self.admitted_throw(EFFECT, op_sym, at, ThrowRoute::Err, thrown, thrown_type),
            Err(e) => e,
        }
    }

    /// Build an `Error`-effect payload entity `ctor(field: value, …)` and raise it, its type
    /// taken as `by` says (WI-467 / WI-610) — the shared core of
    /// [`Self::raise_division_by_zero`] and [`Self::raise_match_failed`].
    ///
    /// Resolving the payload constructor is LOUD, not fallback-interned: a
    /// fabricated same-name symbol would read as `ctor(...)` yet not be the
    /// sort's real constructor, so a handler couldn't destructure it — a silent
    /// degradation the repo's "prefer a loud error" rule forbids. If the
    /// effects prelude isn't loaded (so no program could declare or handle the
    /// effect anyway), `require_symbol` surfaces an `Internal` "not in scope".
    ///
    /// Field names are plainly interned (matching the loader) and the named
    /// args canonicalized to the sort's declared field order via
    /// `canonicalize_record_named_args`, so the payload hash-conses / discrim-matches
    /// identically to one the constructor syntax would build.
    fn raise_error_payload(
        &mut self,
        ctor_qname: &str,
        ctor_short: &str,
        named: Vec<(&str, Value)>,
        by: RaiseBy,
    ) -> EvalError {
        let functor = match crate::eval::builtins::require_symbol(self, ctor_qname, ctor_short) {
            Ok(s) => s,
            Err(e) => return e,
        };
        let mut named_syms: Vec<(Symbol, Value)> = Vec::with_capacity(named.len());
        for (name, v) in named {
            let sym = self.kb_mut().intern(name);
            named_syms.push((sym, v));
        }
        self.kb
            .canonicalize_record_named_args(functor, &mut named_syms);
        let payload = Value::Entity {
            functor,
            pos: Rc::from([]),
            named: named_syms.into(),
        };
        match by {
            RaiseBy::Operation => self.raise_error(payload),
            RaiseBy::Account(evidence_of) => {
                let Some(evidence) = self.error_layer.as_ref().map(|l| evidence_of(l).clone())
                else {
                    return EvalError::Internal(format!(
                        "raising `{ctor_qname}` with no error layer: the runtime raises it \
                         with its sort's `TypeValue` evidence, which the layer holds"
                    ));
                };
                self.raise_typed(payload, RaisedType::Evidence(evidence))
            }
        }
    }

    /// Raise a division-by-zero as an anthill `Error[DivisionByZero]` effect
    /// (WI-467): payload `division_by_zero(op: "Int64.div")` names the failing
    /// op. Routed so an installed `Error` handler catches it; unhandled it is
    /// `EvalError::Raised`. Was a bespoke `EvalError::DivisionByZero` the
    /// declared `effects Error[DivisionByZero]` (WI-066) could never catch.
    pub fn raise_division_by_zero(&mut self, op: &str) -> EvalError {
        self.raise_error_payload(
            "anthill.prelude.DivisionByZero.division_by_zero",
            "division_by_zero",
            vec![("op", Value::Str(op.to_string()))],
            RaiseBy::Operation,
        )
    }

    /// Raise a pattern-match failure as an anthill `Error[MatchFailed]` effect
    /// (WI-610): payload `match_failed(occurrence, scrutinee)`, where
    /// `occurrence` is the failure-site `NodeOccurrence` (the closure/let
    /// pattern, or the match scrutinee) and `scrutinee` is the runtime value
    /// that failed to match, carried verbatim — a `Value` is a faithful reflect
    /// `Term`, so no reification is needed. Routed so an installed `Error`
    /// handler catches it; unhandled it is `EvalError::Raised`. Was a bespoke
    /// `EvalError::MatchFailed` the declared `effects Error[MatchFailed]` could
    /// never catch.
    pub fn raise_match_failed(
        &mut self,
        occurrence: Rc<NodeOccurrence>,
        scrutinee: Value,
    ) -> EvalError {
        self.raise_error_payload(
            "anthill.prelude.MatchFailed.match_failed",
            "match_failed",
            vec![
                ("occurrence", Value::Node(occurrence)),
                ("scrutinee", scrutinee),
            ],
            // A `match`, a `let` or a parameter pattern raises it, and no operation.
            RaiseBy::Account(|l| &l.match_failed_type),
        )
    }

    /// Raise a floundered relation drain as an anthill `Error[RelationFloundered]`
    /// effect (WI-737): payload `relation_floundered(goals)`, naming the
    /// undischarged goals the search delayed and never decided. Routed so an
    /// installed `Error` handler catches it; unhandled it is `EvalError::Raised`.
    ///
    /// `residual` rides carrier-faithfully (WI-348), exactly as
    /// [`Self::make_solution_value`] surfaces it: a goal mentioning a
    /// `Value::Node` keeps its source occurrence rather than being reified to a
    /// bare `TermId`. Surfaced as `List[Term]` — a pending goal IS a term,
    /// occurrence-carried or not.
    pub fn raise_relation_floundered(&mut self, residual: Vec<Value>) -> EvalError {
        let goals = match self.build_list_value(residual, &[]) {
            Ok(v) => v,
            Err(e) => return e,
        };
        self.raise_error_payload(
            crate::kb::RuntimeAccount::RelationFloundered.qualified_name(),
            "relation_floundered",
            vec![("goals", goals)],
            // Raised as a typed relation is drained: by the pull, under the row the
            // relation carries, and no operation's.
            RaiseBy::Account(|l| &l.relation_floundered_type),
        )
    }

    /// WI-SPGBP — raise a failed SCOPED LOAD as an anthill `Error[LoadFailed]` effect:
    /// payload `load_failed(diagnostics)`, the located messages the parse or the load
    /// produced.
    ///
    /// `anthill.reflect.KB.loaded` declares `effects Error`, and this is what makes that
    /// declaration true. Routed through [`Self::raise_error`] so an installed `Error`
    /// handler actually catches it — a checker's whole job is to CATCH this and report
    /// the diagnostics, so building an `EvalError::Raised` directly would have been a
    /// bespoke error the declared effect could never handle. That is the WI-467 /
    /// WI-610 defect exactly, and this is the seam those tickets built to avoid it.
    ///
    /// An ENTITY rather than a bare string, for the same reason: a handler that fires
    /// must be able to destructure the payload, which `Value::Str` gives it no way to do.
    pub fn raise_load_failed(&mut self, diagnostics: Vec<String>) -> EvalError {
        let entries: Vec<Value> = diagnostics.into_iter().map(Value::Str).collect();
        let list = match self.build_list_value(entries, &[]) {
            Ok(v) => v,
            Err(e) => return e,
        };
        self.raise_error_payload(
            crate::kb::RuntimeAccount::LoadFailed.qualified_name(),
            "load_failed",
            vec![("diagnostics", list)],
            RaiseBy::Operation,
        )
    }

    /// WI-20260911-8Y5BE — raise a query that could not be LOWERED as the declared
    /// `Error[ResolveStreamFailure]`, the interpreter-face twin of the host bridge's
    /// refusal. The one door `KB.execute` and `Relation.splitFirst` both lower through.
    ///
    /// `NotYetImplemented` is `unsupported_operation`, for the reason `LowerError` keeps
    /// it apart: a well-formed query this face has not wired is a gap in the face, not
    /// the caller's mistake. Everything else is `malformed_query`.
    ///
    /// `by` is the door's: `KB.execute` raises it as the operation it is, with the evidence
    /// its `requires TypeValue[T = ResolveStreamFailure]` was handed; `Relation.splitFirst`
    /// lowers on the stream's first pull, under the row the relation carries.
    pub(crate) fn raise_query_lowering(
        &mut self,
        e: crate::kb::execute::LowerError,
        by: RaiseBy,
    ) -> EvalError {
        let ctor = match e {
            crate::kb::execute::LowerError::NotYetImplemented(_) => "unsupported_operation",
            _ => "malformed_query",
        };
        self.raise_resolve_stream_failure(ctor, e.to_string(), by)
    }

    /// WI-20260911-8Y5BE — raise a pull on a stream that can no longer answer as the
    /// declared `Error[ResolveStreamFailure]`: payload `stream_misused(detail)`.
    pub fn raise_stream_misused(&mut self, detail: String) -> EvalError {
        self.raise_resolve_stream_failure(
            "stream_misused",
            detail,
            RaiseBy::Account(|l| &l.resolve_stream_failure_type),
        )
    }

    /// A `ResolveStreamFailure` variant that carries only prose `detail`.
    fn raise_resolve_stream_failure(&mut self, ctor: &str, detail: String, by: RaiseBy) -> EvalError {
        self.raise_error_payload(
            &format!("anthill.reflect.ResolveStreamFailure.{ctor}"),
            ctor,
            vec![("detail", Value::Str(detail))],
            by,
        )
    }

    /// WI-20260911-8Y5BE — raise a `KB.execute` stream whose search recorded a FAULT as
    /// the declared `Error[ResolveStreamFailure]`: payload
    /// `evaluation_failure(goals, reason, at)`, the interpreter-face twin of the host
    /// bridge's `EvaluationFailure` (see `ResolveStreamFailure` in `reflect.anthill`).
    ///
    /// `goals` rides carrier-faithfully, as [`Self::raise_relation_floundered`]'s does.
    /// `at` is `some(occurrence)` for a positioned goal and `none()` otherwise — never an
    /// occurrence with a fabricated span.
    pub fn raise_evaluation_failure(
        &mut self,
        goals: Vec<Value>,
        reason: String,
        at: Option<Rc<NodeOccurrence>>,
    ) -> EvalError {
        let goals = match self.build_list_value(goals, &[]) {
            Ok(v) => v,
            Err(e) => return e,
        };
        use crate::eval::builtins::{option_none, option_some, require_symbol};
        let at = match at {
            Some(occ) => match require_symbol(self, "anthill.prelude.Option.some", "some") {
                Ok(some) => {
                    let value_key = self.kb_mut().intern("value");
                    option_some(some, value_key, Value::Node(occ))
                }
                Err(e) => return e,
            },
            None => match require_symbol(self, "anthill.prelude.Option.none", "none") {
                Ok(none) => option_none(none),
                Err(e) => return e,
            },
        };
        self.raise_error_payload(
            crate::kb::RuntimeAccount::EvaluationFailure.qualified_name(),
            "evaluation_failure",
            vec![("goals", goals), ("reason", Value::Str(reason)), ("at", at)],
            // A pull whose search faulted.
            RaiseBy::Account(|l| &l.resolve_stream_failure_type),
        )
    }

    /// WI-20260913-P9QBF — raise a resolver stream whose search ran dry with a branch cut
    /// at a depth limit as the declared `Error[ResolveStreamFailure]`: payload
    /// `search_truncated(max_depth)`, the interpreter-face twin of the host bridge's
    /// `SearchTruncated`.
    pub fn raise_search_truncated(&mut self, max_depth: i64) -> EvalError {
        self.raise_error_payload(
            crate::kb::RuntimeAccount::SearchTruncated.qualified_name(),
            "search_truncated",
            vec![("max_depth", Value::Int(max_depth))],
            // A pull whose search was cut.
            RaiseBy::Account(|l| &l.resolve_stream_failure_type),
        )
    }

    /// Register the standard effect handlers. Includes real-stdio
    /// Console handlers (call explicitly for programs that need terminal
    /// access; tests usually skip this and inject buffered handlers), the
    /// `Error` handler, and the wall-clock `Clock` handler (a test reading
    /// the clock registers it, or one of its own). No base modifiable sort
    /// has a handler here: `Cell`'s operations are host functions over the
    /// interpreter's arena (proposal 037 §4.1, §4.2).
    ///
    /// Each by its qualified name, and a name the KB does not declare is an error
    /// (`UnknownOperation`), not a handler left out: the five are the standard library's,
    /// and a KB loaded without it has no program to run with them.
    pub fn register_standard_effect_handlers(&mut self) -> Result<(), EvalError> {
        let entries: [(&str, fn() -> EffectHandler); 5] = [
            (
                "anthill.prelude.Console.ConsoleOutput",
                stdio_console_output_handler,
            ),
            (
                "anthill.prelude.Console.ConsoleError",
                stdio_console_error_handler,
            ),
            (
                "anthill.prelude.Console.ConsoleInput",
                stdio_console_input_handler,
            ),
            ("anthill.prelude.Error", default_error_handler),
            ("anthill.prelude.Time.Clock", system_clock_handler),
        ];
        for (qname, factory) in entries {
            self.register_effect_handler(qname, factory())?;
        }
        Ok(())
    }
}

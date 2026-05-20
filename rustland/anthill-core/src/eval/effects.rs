//! Effect handler dispatch (proposal 026 §Effects, M5).
//!
//! An `EffectHandler` is a `FnMut` keyed by *effect-sort* qualified name.
//! When an operation is invoked whose effect row names that sort, the
//! handler is called with `(interp, op_sym, args)` and produces the
//! operation's return `Value`. The handler closure owns the resource it
//! represents — `Stdout` for `ConsoleOutput`, a test buffer for capture,
//! a `Modify` arena for stateful cells, etc. Replacing a handler replaces
//! the resource; the interpreter itself holds no effect-specific state.

use std::cell::RefCell;
use std::collections::HashMap;
use std::io::{self, BufRead, Write};
use std::rc::Rc;

use crate::intern::Symbol;

use super::{EvalError, Interpreter, Value};

/// Handler for a single effect sort. Dispatched on the operation symbol
/// (e.g., `print` vs `println` both fall into `ConsoleOutput`).
pub type EffectHandler =
    Box<dyn FnMut(&mut Interpreter, Symbol, &[Value]) -> Result<Value, EvalError>>;

// ── Default Console handlers (stdio) ───────────────────────────

/// Short name of an op ends with "println" — matches both the stdout
/// `println` and stderr `eprintln` variants, which both append a newline.
fn op_appends_newline(op_name: &str) -> bool {
    op_name == "println" || op_name == "eprintln"
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
        let s = args.get(1).and_then(Value::as_str).ok_or_else(|| {
            EvalError::TypeMismatch { expected: "String", got: "missing or non-String argument".into() }
        })?;
        let mut out = sink.borrow_mut();
        out.write_all(s.as_bytes()).map_err(|e| EvalError::Internal(e.to_string()))?;
        if op_appends_newline(interp.kb().resolve_sym(op_sym)) {
            out.write_all(b"\n").map_err(|e| EvalError::Internal(e.to_string()))?;
        }
        out.flush().map_err(|e| EvalError::Internal(e.to_string()))?;
        Ok(Value::Unit)
    })
}

/// Default `ConsoleInput` handler — reads a line from `io::stdin()`.
/// The trailing newline is stripped to match common user expectation.
pub fn stdio_console_input_handler() -> EffectHandler {
    let stdin = Rc::new(RefCell::new(io::BufReader::new(io::stdin())));
    Box::new(move |_interp, _op_sym, _args| {
        let mut buf = String::new();
        stdin.borrow_mut().read_line(&mut buf)
            .map_err(|e| EvalError::Internal(e.to_string()))?;
        if buf.ends_with('\n') { buf.pop(); }
        if buf.ends_with('\r') { buf.pop(); }
        Ok(Value::Str(buf))
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
        let s = args.get(1).and_then(Value::as_str).ok_or_else(|| {
            EvalError::TypeMismatch { expected: "String", got: "missing or non-String argument".into() }
        })?;
        buf.borrow_mut().push_str(s);
        if op_appends_newline(interp.kb().resolve_sym(op_sym)) {
            buf.borrow_mut().push('\n');
        }
        Ok(Value::Unit)
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
        script.borrow_mut().pop_front()
            .map(Value::Str)
            .ok_or_else(|| EvalError::Internal("scripted console input exhausted".into()))
    })
}

// ── Default Modify handler (per-resource dispatch) ─────────────

/// Default handler for the `Modify` effect. Per WI-205's per-resource
/// dispatch architecture, routes `get` / `set` based on the target
/// Value's variant:
///
/// - `Value::Cell(h)` → reads/writes go through the interpreter's
///   `cell_arena` (allocation-time uid; one slot per `Cell.new`).
/// - `Value::Entity { functor, .. }` or `Value::Term` wrapping a nullary
///   functor → fallback functor-keyed map. The functor symbol is the
///   key; mixing types for the same resource is not rejected (runtime
///   is dynamically typed; the typer is the place to catch mismatches).
///
/// The Cell path matches what `Cell.set` does directly; routing
/// `Modify.set(cell, v)` here gives the same arena semantics, so user
/// code calling `Modify.set` on a Cell handle behaves identically to
/// calling `Cell.set`.
///
/// Cycle detection surfaces as [`EvalError::CyclicReference`] when a
/// functor-keyed `set` would store a value that transitively references
/// itself via `Value::Term` or entity args. Cell-routed `set` skips the
/// runtime walk — proposal 037 §"Cell[V]" and WI-207's typer-side
/// `acyclic_cell` rule make cycles inexpressible at the type level.
pub fn default_modify_handler() -> EffectHandler {
    let cells: Rc<RefCell<HashMap<Symbol, Value>>> =
        Rc::new(RefCell::new(HashMap::new()));

    Box::new(move |interp, op_sym, args| {
        let target = args.first().ok_or_else(|| EvalError::ArityMismatch {
            op: "Modify", expected: 1, got: 0,
        })?;
        let op_name = interp.kb().resolve_sym(op_sym);

        // Cell arm: route through the cell arena. Identity is the slot,
        // not the functor; two Cell.new calls produce distinct handles.
        if let Value::Cell(h) = target {
            let handle = h.clone();
            return match op_name {
                "get" => Ok(interp.read_cell(&handle)),
                "set" => {
                    let new_val = args.get(1).cloned().ok_or_else(|| {
                        EvalError::ArityMismatch {
                            op: "Modify.set", expected: 2, got: args.len(),
                        }
                    })?;
                    interp.write_cell(&handle, new_val);
                    Ok(Value::Unit)
                }
                other => Err(EvalError::Internal(
                    format!("Modify[Cell] handler: unknown op `{}`", other),
                )),
            };
        }

        // Fallback: functor-keyed map for anonymous resources.
        let key = resource_key(interp, Some(target))?;
        match op_name {
            "get" => {
                cells.borrow()
                    .get(&key)
                    .cloned()
                    .ok_or_else(|| EvalError::Internal(
                        format!("Modify.get: no value set for `{}`",
                                interp.kb().resolve_sym(key))
                    ))
            }
            "set" => {
                let new_val = args.get(1).cloned().ok_or_else(|| {
                    EvalError::ArityMismatch { op: "Modify.set", expected: 2, got: args.len() }
                })?;
                detect_cycle(interp, key, &new_val, 0)?;
                cells.borrow_mut().insert(key, new_val);
                Ok(Value::Unit)
            }
            other => Err(EvalError::Internal(format!("Modify handler: unknown op `{}`", other))),
        }
    })
}

fn resource_key(interp: &Interpreter, arg: Option<&Value>) -> Result<Symbol, EvalError> {
    let v = arg.ok_or_else(|| EvalError::ArityMismatch {
        op: "Modify", expected: 1, got: 0,
    })?;
    crate::eval::eval::value_functor(interp.kb(), v).ok_or_else(|| EvalError::TypeMismatch {
        expected: "Entity, Cell, or nullary Term (resource identifier)",
        got: v.type_name().to_string(),
    })
}

/// Bounded structural walk checking whether `value` transitively
/// references the cell keyed by `target`. `depth` is a budget guarding
/// against pathological structures even without a genuine cycle.
fn detect_cycle(
    interp: &Interpreter,
    target: Symbol,
    value: &Value,
    depth: usize,
) -> Result<(), EvalError> {
    const MAX_DEPTH: usize = 1024;
    if depth >= MAX_DEPTH {
        return Err(EvalError::CyclicReference);
    }
    match value {
        Value::Entity { functor, pos, named } => {
            if *functor == target {
                return Err(EvalError::CyclicReference);
            }
            for v in pos.iter().chain(named.iter().map(|(_, v)| v)) {
                detect_cycle(interp, target, v, depth + 1)?;
            }
            Ok(())
        }
        Value::Term(tid) => {
            detect_cycle_term(interp, target, *tid, depth)
        }
        Value::Tuple { pos, named } => {
            for v in pos.iter().chain(named.iter().map(|(_, v)| v)) {
                detect_cycle(interp, target, v, depth + 1)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

fn detect_cycle_term(
    interp: &Interpreter,
    target: Symbol,
    tid: crate::kb::term::TermId,
    depth: usize,
) -> Result<(), EvalError> {
    const MAX_DEPTH: usize = 1024;
    if depth >= MAX_DEPTH {
        return Err(EvalError::CyclicReference);
    }
    use crate::kb::term::Term;
    match interp.kb().get_term(tid) {
        Term::Fn { functor, pos_args, named_args } => {
            if *functor == target {
                return Err(EvalError::CyclicReference);
            }
            let pos: Vec<_> = pos_args.iter().copied().collect();
            let named: Vec<_> = named_args.iter().map(|(_, t)| *t).collect();
            for t in pos.into_iter().chain(named.into_iter()) {
                detect_cycle_term(interp, target, t, depth + 1)?;
            }
            Ok(())
        }
        Term::Ref(sym) => {
            if *sym == target { Err(EvalError::CyclicReference) } else { Ok(()) }
        }
        _ => Ok(()),
    }
}

// ── Interpreter integration ────────────────────────────────────

/// The handler map. Stored behind an `Option` inside `Interpreter` so we
/// can `.take()` the handler out of the map, invoke it (which needs
/// `&mut Interpreter`), and put it back — without fighting the borrow
/// checker over a simultaneously-borrowed map entry.
pub(crate) struct EffectRegistry {
    handlers: HashMap<Symbol, Option<EffectHandler>>,
}

impl EffectRegistry {
    pub fn new() -> Self {
        Self { handlers: HashMap::new() }
    }

    pub fn insert(&mut self, effect_sym: Symbol, h: EffectHandler) -> Option<EffectHandler> {
        self.handlers.insert(effect_sym, Some(h)).and_then(|o| o)
    }

    pub fn remove(&mut self, effect_sym: Symbol) -> Option<EffectHandler> {
        self.handlers.remove(&effect_sym).and_then(|o| o)
    }

    #[allow(dead_code)]  // not active yet — kept for handler-presence queries
    pub fn has(&self, effect_sym: Symbol) -> bool {
        self.handlers.get(&effect_sym).map_or(false, |o| o.is_some())
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
            EvalError::UnknownOperation { name: effect_qname.to_string() }
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

    /// Invoke the handler for `effect_qname` with the given operation
    /// symbol and arguments. Used by builtins that represent effectful
    /// operations (e.g. `Console.print` routes through `ConsoleOutput`).
    pub fn invoke_effect_handler(
        &mut self,
        effect_qname: &str,
        op_sym: Symbol,
        args: &[Value],
    ) -> Result<Value, EvalError> {
        let effect_sym = self.kb.try_resolve_symbol(effect_qname).ok_or_else(|| {
            EvalError::UnknownOperation { name: effect_qname.to_string() }
        })?;
        let mut handler = self.effect_handlers.take_for_invoke(effect_sym).ok_or_else(|| {
            EvalError::Internal(format!("no handler registered for effect `{}`", effect_qname))
        })?;
        let result = handler(self, op_sym, args);
        self.effect_handlers.return_handler(effect_sym, handler);
        result
    }

    /// Register the standard effect handlers. Includes real-stdio
    /// Console handlers (call explicitly for programs that need terminal
    /// access; tests usually skip this and inject buffered handlers) and
    /// a fresh arena-backed Modify handler — the latter is always useful,
    /// even for tests, since Modify.get/set have no side effect beyond
    /// the handler's own state.
    pub fn register_standard_effect_handlers(&mut self) -> Result<(), EvalError> {
        let entries: [(&str, fn() -> EffectHandler); 4] = [
            ("anthill.prelude.Console.ConsoleOutput", stdio_console_output_handler),
            ("anthill.prelude.Console.ConsoleError", stdio_console_error_handler),
            ("anthill.prelude.Console.ConsoleInput", stdio_console_input_handler),
            ("Modify", default_modify_handler),
        ];
        for (qname, factory) in entries {
            match self.register_effect_handler(qname, factory()) {
                Ok(()) | Err(EvalError::UnknownOperation { .. }) => {}
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }
}

//! Shared bootstrap for anthill program binaries.
//!
//! The CLI `run` command (`anthill-cli`) and the bundle entry point
//! (`anthill-todo`) both: register the standard builtins + effect handlers on a
//! fresh interpreter, call the program's `main`, and map its result to a process
//! exit code. Those mechanics — and the exit-code conventions they share — live
//! here so the two binaries stay byte-identical in their error formatting and
//! exit codes. (The KB-build and `main`-invocation steps themselves differ: the
//! CLI discovers an entry sort and calls `main(args)`, while the todo bundle
//! threads a store/cell/requirements chain into `main(args, store, …)`; those
//! stay in each binary.)

use anthill_core::eval::{builtins, EvalError, Interpreter, Value};
use anthill_core::kb::KnowledgeBase;

/// Compilation failure — parse, load, or typecheck error, or no entry found.
pub const EXIT_COMPILE: i32 = 2;

/// Runtime failure — the evaluator errored during `main`.
pub const EXIT_RUNTIME: i32 = 1;

/// Substituted for a `main` return value outside 0..=255, so an out-of-range
/// exit can be distinguished from an evaluator error (EXIT_RUNTIME).
pub const EXIT_OUT_OF_RANGE: i32 = 255;

/// Runaway-loop backstop for the CLIs: bound total interpreter work so a
/// non-terminating program (a tail loop OR a dispatch/deliver value-cascade)
/// aborts with a named `StepsExhausted` instead of hanging. The library default
/// leaves `step_cap` `None` (uncapped batch eval); the CLIs opt in here. Sized
/// ~1000× above a real CLI workload (`anthill-todo status` is ~10^5 steps) yet
/// trips a runaway in seconds; a genuinely large batch program can raise it via
/// `config_mut()`.
pub const CLI_STEP_CAP: u64 = 100_000_000;

/// Prepare `interp` to run a program: install the CLI runaway backstop (unless
/// the embedder already set a `step_cap`), then register the standard builtins
/// and effect handlers. On failure prints an `error: …` line and returns
/// `Err(EXIT_RUNTIME)`; the caller forwards the code.
pub fn register_runtime(interp: &mut Interpreter) -> Result<(), i32> {
    if interp.config().step_cap.is_none() {
        interp.config_mut().step_cap = Some(CLI_STEP_CAP);
    }
    builtins::register_standard_builtins(interp).map_err(|e| {
        eprintln!("error: registering builtins: {e}");
        EXIT_RUNTIME
    })?;
    interp.register_standard_effect_handlers().map_err(|e| {
        eprintln!("error: registering effect handlers: {e}");
        EXIT_RUNTIME
    })?;
    Ok(())
}

/// Build the `args: List[String]` value both entry points pass to `main` from
/// their CLI argv. Returns the raw `Result` so each caller keeps its own
/// error-message / exit plumbing (the CLI uses `?`, the bundle a `match`).
pub fn build_args_value(interp: &mut Interpreter, args: &[String]) -> Result<Value, EvalError> {
    let elements: Vec<Value> = args.iter().map(|s| Value::Str(s.clone())).collect();
    interp.build_list_value(elements, &[])
}

/// Map the result of invoking a program's `main` to a process exit code, with
/// the error formatting both binaries share:
///   - `Int(n)` in 0..=255 → `n`; outside → a warning + `EXIT_OUT_OF_RANGE`.
///   - a non-Int return → `error: main returned non-Int64 value` + `EXIT_RUNTIME`.
///   - `Raised` — a top-level `Error` effect that propagated out of `main`
///     (WI-195) — → `error: <payload>` + `EXIT_RUNTIME`. (`Raised`'s own
///     `Display` drops the payload, so it is rendered here via [`render_payload`],
///     which needs `kb` to resolve functor/field symbols to names.)
///   - any other evaluator error → `error: <e>` + `EXIT_RUNTIME`.
pub fn exit_code_from_main(kb: &KnowledgeBase, result: Result<Value, EvalError>) -> i32 {
    match result {
        Ok(Value::Int(n)) => {
            if (0..=255).contains(&n) {
                n as i32
            } else {
                eprintln!("warning: main returned {n}, outside 0..=255 — clamped");
                EXIT_OUT_OF_RANGE
            }
        }
        Ok(other) => {
            eprintln!("error: main returned non-Int64 value: {other:?}");
            EXIT_RUNTIME
        }
        Err(EvalError::Raised { payload }) => {
            eprintln!("error: {}", render_payload(kb, &payload, 0));
            EXIT_RUNTIME
        }
        Err(e) => {
            eprintln!("error: {e}");
            EXIT_RUNTIME
        }
    }
}

/// Render a raised `Error` payload as a human-readable line. Store-I/O builtins
/// raise `Str` payloads (printed verbatim); WI-467 made div-by-zero raise the
/// structured `division_by_zero(op: "Int64.div")` entity, and user code can
/// `Error.raise` any `Value`. Renders an entity as `functor(pos…, field: val…)`
/// using `kb` to resolve the interned functor/field symbols to their short
/// names — so an unhandled `10 / 0` prints
/// `error: division_by_zero(op: "Int64.div")` rather than a `Symbol`-index
/// debug dump. `depth` bounds recursion against pathological nesting.
fn render_payload(kb: &KnowledgeBase, v: &Value, depth: usize) -> String {
    const MAX_DEPTH: usize = 6;
    match v {
        // A bare top-level Str (store-I/O raises these) prints verbatim, as it
        // did before; a Str nested in an entity field is quoted so the field
        // reads as a string literal (`op: "Int64.div"`).
        Value::Str(s) if depth == 0 => s.clone(),
        Value::Str(s) => format!("{s:?}"),
        Value::Int(n) => n.to_string(),
        Value::BigInt(n) => n.to_string(),
        Value::Float(x) => x.to_string(),
        Value::Bool(b) => b.to_string(),
        Value::Unit => "()".to_string(),
        Value::Entity { functor, pos, named, .. } => {
            let name = kb.resolve_sym(*functor);
            if (pos.is_empty() && named.is_empty()) || depth >= MAX_DEPTH {
                return name.to_string();
            }
            let mut parts: Vec<String> =
                pos.iter().map(|p| render_payload(kb, p, depth + 1)).collect();
            for (fname, fv) in named.iter() {
                parts.push(format!("{}: {}", kb.resolve_sym(*fname), render_payload(kb, fv, depth + 1)));
            }
            format!("{}({})", name, parts.join(", "))
        }
        // Handles / streams / substitutions have no readable surface form; name
        // the carrier kind rather than leaking a debug dump.
        other => other.type_name().to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::rc::Rc;

    /// WI-467: the `division_by_zero(op:)` entity payload an unhandled
    /// `10 / 0` carries renders as a readable line — `resolve_sym` turns the
    /// interned functor/field symbols into names — not the `Symbol`-index
    /// debug dump the old `format!("{payload:?}")` fallback produced.
    #[test]
    fn render_payload_renders_division_by_zero_entity_readably() {
        let mut kb = KnowledgeBase::new();
        let functor = kb.intern("division_by_zero");
        let op_field = kb.intern("op");
        let payload = Value::Entity {
            functor,
            pos: Rc::from([]),
            named: Rc::from([(op_field, Value::Str("Int64.div".to_string()))]),
            ty: None,
        };
        assert_eq!(
            render_payload(&kb, &payload, 0),
            r#"division_by_zero(op: "Int64.div")"#,
        );
    }

    /// A bare top-level `Str` payload (store-I/O builtins raise these) still
    /// prints verbatim — unquoted — as before WI-467's renderer landed.
    #[test]
    fn render_payload_prints_bare_string_verbatim() {
        let kb = KnowledgeBase::new();
        assert_eq!(
            render_payload(&kb, &Value::Str("persist failed: disk full".to_string()), 0),
            "persist failed: disk full",
        );
    }
}

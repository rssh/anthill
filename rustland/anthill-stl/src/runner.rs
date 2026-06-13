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
///     `Display` drops the payload, so it is rendered here.)
///   - any other evaluator error → `error: <e>` + `EXIT_RUNTIME`.
pub fn exit_code_from_main(result: Result<Value, EvalError>) -> i32 {
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
            let msg = match &payload {
                Value::Str(s) => s.clone(),
                // v1: builtins raise String payloads; a user-raised entity falls
                // back to a debug rendering until a Value printer lands.
                other => format!("{other:?}"),
            };
            eprintln!("error: {msg}");
            EXIT_RUNTIME
        }
        Err(e) => {
            eprintln!("error: {e}");
            EXIT_RUNTIME
        }
    }
}

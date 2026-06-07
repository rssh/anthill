//! WI-416 trip-wire (`#[ignore]`).
//!
//! Typechecking a sort operation that calls a CROSS-SORT `requires`-op typed
//! with the callee sort's own bare sort-parameter (`List.member(x: T, l: List)`,
//! `T = List.T`; member's body defers `eq` to `List requires Eq[T]`) currently
//! INFINITE-RECURSES in the typer, and the process dies by signal (stack
//! overflow → `SIGABRT`). Because that is an uncatchable process abort — not a
//! recoverable `panic!` — it cannot live as an in-process `#[test]` (it would
//! abort the whole test binary). So this is a SUBPROCESS test: it runs the
//! built `anthill check` on the repro fixture and asserts the child exits
//! cleanly (a clean typecheck OR a clean diagnostic), never via a crash signal.
//!
//! Narrowing (see WI-416): calling `List.length` (no deferred spec op) from a
//! sort op is fine; calling `member` from a FREE op with no enclosing sort is
//! fine (that is WI-415's passing case); `List.nth` (its own `[Elem]` param)
//! errors cleanly. The crash is specific to a cross-sort, bare-sort-param,
//! spec-op-deferring call made from WITHIN a sort's operation. Pre-existing
//! (overflows before WI-415). It blocks the WI-415 cross-sort-ABSTRACT
//! requirement-threading runtime gap (that scenario cannot even be
//! typechecked). Un-`#[ignore]` this test when WI-416 lands.

use std::path::PathBuf;
use std::process::Command;

const ANTHILL_BIN: &str = env!("CARGO_BIN_EXE_anthill");

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/check/wi416-cross-sort-member.anthill")
}

#[test]
#[ignore] // WI-416: typer stack overflow (SIGABRT) on this input. Un-ignore when fixed.
fn wi416_cross_sort_member_call_does_not_overflow_typer() {
    let out = Command::new(ANTHILL_BIN)
        .args(["check", fixture().to_str().unwrap()])
        .output()
        .expect("run anthill check");
    // The bug: the typer infinite-recurses, so the child is killed by a signal
    // and reports NO exit code (`code()` is `None`). Acceptance: the child
    // exits cleanly — it typechecks the program or emits a diagnostic, but
    // never crashes. (`code().is_some()` is true for any normal exit, 0 or not,
    // and false only when terminated by a signal.)
    assert!(
        out.status.code().is_some(),
        "`anthill check` crashed with no exit code — likely the WI-416 typer \
         stack overflow; status = {:?}\nstderr:\n{}",
        out.status,
        String::from_utf8_lossy(&out.stderr),
    );
}

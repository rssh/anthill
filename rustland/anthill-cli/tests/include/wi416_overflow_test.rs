//! WI-416 regression: the typer must not infinite-recurse on a cross-sort
//! `requires`-op call.
//!
//! Typechecking a sort operation that calls a CROSS-SORT `requires`-op typed
//! with the callee sort's own bare sort-parameter (`List.member(x: T, l: List)`,
//! `T = List.T`; member's body defers `eq` to `List requires Eq[T]`) used to
//! INFINITE-RECURSE in `walk_type`: two distinct `Var` instances of `Coll.T`
//! cross-bind into a cyclic substitution (`a -> Ref(Coll.T) -> a`), and the
//! recursive walker overflowed the stack (`SIGABRT`). Fixed by making
//! `walk_type` iterative with cycle detection (a cyclic subst means those vars
//! are unified, so it returns a representative).
//!
//! Because a stack overflow is an uncatchable process abort — not a recoverable
//! `panic!` — this cannot be an in-process `#[test]` (it would abort the whole
//! test binary even if it regressed). So it is a SUBPROCESS test: it runs the
//! built `anthill check` on the repro fixture and asserts the child exits
//! cleanly (typecheck or a clean diagnostic), never via a crash signal.
//!
//! Narrowing (see WI-416): calling `List.length` (no deferred spec op) from a
//! sort op was always fine; `member` from a FREE op with no enclosing sort is
//! WI-415's case; `List.nth` (its own `[Elem]` param) errors cleanly. The crash
//! was specific to a cross-sort, bare-sort-param, spec-op-deferring call made
//! from WITHIN a sort's operation. (Pre-existing — it predated WI-415.)

use std::path::PathBuf;
use std::process::Command;

const ANTHILL_BIN: &str = env!("CARGO_BIN_EXE_anthill");

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/check/wi416-cross-sort-member.anthill")
}

#[test]
fn wi416_cross_sort_member_call_does_not_overflow_typer() {
    let out = Command::new(ANTHILL_BIN)
        .args(["check", fixture().to_str().unwrap()])
        .output()
        .expect("run anthill check");
    // A typer infinite-recursion kills the child by signal, leaving NO exit code
    // (`code()` is `None`). The fix makes it terminate: the child exits cleanly —
    // it typechecks the program or emits a diagnostic, but never crashes.
    // (`code().is_some()` is true for any normal exit, 0 or not, and false only
    // when terminated by a signal.)
    assert!(
        out.status.code().is_some(),
        "`anthill check` crashed with no exit code — the WI-416 typer stack \
         overflow regressed; status = {:?}\nstderr:\n{}",
        out.status,
        String::from_utf8_lossy(&out.stderr),
    );
}

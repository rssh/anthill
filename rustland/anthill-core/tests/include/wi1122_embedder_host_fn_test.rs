//! WI-1122 — an EMBEDDER can bind its own carrier's operations to its own functions.
//!
//! THE PRE-FIX STATE. WI-876 gave `operation_map` two halves. The DATA half is open —
//! any `.anthill` file may write `operation_map { squish: "my_key" }`. The FUNCTION
//! half was closed: `eval::builtins::HOST_FNS` is a `const` slice compiled into
//! anthill-core, `host_fn_by_key` consulted only that, and an unknown key is a FATAL
//! `EvalError::Internal`. So a host embedding anthill and binding a carrier of its own
//! — anthill-todo naming `gh_create_entry`, or anyone else — could not name its own
//! functions at all. This is not a third registration tier; it is the missing half of
//! the second one.
//!
//! WHAT IS UNDER TEST, and what each test would catch:
//!   * the CAPABILITY — an embedder-registered function is reachable from an
//!     `operation_map` and its value comes back (`an_embedder_registered_function_…`);
//!   * a function may CLOSE OVER the embedder's own config, which is what the seam's
//!     first consumer needs (`…_may_close_over_its_own_state`);
//!   * the same ARITY CHECK applies to it (`an_embedder_entry_of_the_wrong_arity_…`),
//!     which is the reason `HostFn` is shared rather than duplicated per registry;
//!   * a COLLISION with either half is refused, not ordered (`…_shadow_a_builtin_key`,
//!     `…_registered_twice`);
//!   * the ORDERING is enforced, not merely documented — a late registration is refused
//!     (`a_host_fn_registered_after_load_is_refused`), because the unenforced failure is
//!     SILENT in a release build;
//!   * the registry stays CLOSED — an unregistered key is still fatal
//!     (`an_unregistered_key_is_still_fatal`);
//!   * and the PLACEMENT: the table is on the `KnowledgeBase`, so it survives the
//!     scratch interpreter `run_in_bridge_interp` builds per bridged evaluation
//!     (`an_embedder_function_survives_a_fresh_interpreter_over_the_same_kb`).
//!
//! WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT (per the repo's control rule).
//! MEASURED, all three backouts actually run — not asserted from the armchair. The
//! first draft's claim here was wrong twice over, and only the measurement caught it.
//! The change has THREE independent halves, and each controls a disjoint set:
//!
//!   * back out `host_fn_by_key`'s EMBEDDER LEG (return `None` instead of consulting
//!     the KB table) → 6 fail: `…_callable_from_an_operation_map`,
//!     `…_survives_a_fresh_interpreter_over_the_same_kb`, `…_may_close_over_its_own_state`,
//!     `an_embedder_entry_of_the_wrong_arity_is_refused`, and both arity/ordering
//!     controls (`the_control_a_matching_arity_runs`,
//!     `the_control_the_same_registration_before_load_is_accepted`);
//!   * back out the COLLISION REFUSALS in `HostFnRegistry::register` → 2 fail:
//!     `an_embedder_cannot_shadow_a_builtin_key`, `an_embedder_key_cannot_be_registered_twice`;
//!   * back out the SEAL (the `sealed` guard) → 1 fails:
//!     `a_host_fn_registered_after_load_is_refused`.
//!
//! Two pass under ALL THREE backouts, by design: `the_control_a_fresh_key_registers`
//! (the control against a `register_host_fn` that refuses everything) and
//! `an_unregistered_key_is_still_fatal` (the control against a fix that was "accept any
//! key" — WI-876's closed-registry refusal must survive).
//!
//! TWO THINGS THE MEASUREMENT CAUGHT, recorded because both would have shipped:
//!   * the arity test asserted `err.contains('1') && err.contains('2')` and passed with
//!     everything backed out — the namespace `wi1122.arity` supplies both digits to the
//!     unknown-key message. It now asserts the arity sentence itself.
//!   * the seal test asserted its message contained "before"; the message says "BEFORE".
//!     The refusal was working; the assertion was not.
//!
//! Reference: `kb/host_fns.rs` (the argument for the placement),
//! `eval/builtins.rs` (`HOST_FNS`, `host_fn_by_key`, `register_operation_mappings`).

use anthill_core::eval::{EvalError, Interpreter, Value};
use anthill_core::kb::host_fns::HostFnRegError;
use anthill_core::kb::KnowledgeBase;

// ── The embedder's own host functions ────────────────────────────────

/// An embedder function that is NOT in `HOST_FNS` and could not be: it answers
/// something only this "host" knows. Deliberately not a re-spelling of an arithmetic
/// builtin — a test whose embedder function duplicates a stdlib one cannot tell the
/// two registries apart if the lookup silently fell back to the wrong half.
fn embedder_answer(_interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    match args {
        [Value::Int(n)] => Ok(Value::Int(n * 100 + 7)),
        other => Err(EvalError::Internal(format!(
            "embedder_answer: expected one Int, got {other:?}"
        ))),
    }
}

/// A two-argument embedder function, for the arity-mismatch fixture.
fn embedder_pair(_interp: &mut Interpreter, args: &[Value]) -> Result<Value, EvalError> {
    match args {
        [Value::Int(a), Value::Int(b)] => Ok(Value::Int(a + b)),
        other => Err(EvalError::Internal(format!(
            "embedder_pair: expected two Ints, got {other:?}"
        ))),
    }
}

// ── Fixtures ─────────────────────────────────────────────────────────

/// A carrier declaring a ONE-argument `answer`, mapped to `entry`, plus a driver that
/// CALLS it. The driver matters: a fixture that only declares the mapping would keep
/// passing if the registration bound nothing, which is the defect class this ticket
/// is one level below.
fn program(ns: &str, entry: &str) -> String {
    format!(
        "\nnamespace {ns}\n  \
         sort Widget\n    import anthill.prelude.{{Int64}}\n    \
         entity widget(v: Int64)\n    \
         operation answer(v: Int64) -> Int64\n  end\n  \
         provides Widget language rust\n    artifact \"nowhere.rs\"\n    \
         operation_map {{ {entry} }}\n  end\n  \
         sort Driver\n    import anthill.prelude.{{Int64}}\n    \
         import {ns}.Widget\n    \
         operation ask(n: Int64) -> Int64 = Widget.answer(4)\n  end\nend\n"
    )
}

/// Load `src` with `key`/`arity`/`f` registered on the KB BEFORE `load_all`, then
/// build an interpreter over it. The ordering is the documented one (`kb/host_fns.rs`
/// §Ordering) — load itself builds interpreters, so registering after the load would
/// exercise a weaker claim than the seam makes.
fn interp_with_host_fn(
    src: &str,
    key: &'static str,
    arity: usize,
    f: fn(&mut Interpreter, &[Value]) -> Result<Value, EvalError>,
) -> Result<Interpreter, String> {
    let kb = crate::common::try_load_kb_prepared(src, |kb| {
        kb.register_host_fn(key, arity, f)
            .expect("the embedder registration itself must succeed");
    })
    .unwrap_or_else(|errs| panic!("expected a clean load; got: {errs:?}"));
    let mut interp = Interpreter::new(kb);
    match anthill_core::eval::builtins::register_standard_builtins(&mut interp) {
        Ok(()) => Ok(interp),
        Err(e) => Err(format!("{e:?}")),
    }
}

// ── The capability ───────────────────────────────────────────────────

/// THE ACCEPTANCE: an embedder registers a function, an `operation_map` names it, and
/// CALLING the operation returns that function's value.
///
/// Asserts the VALUE, not that the program loaded or that registration returned `Ok`:
/// `407` can only come from `embedder_answer` running on the argument `4`. A
/// registration that bound nothing, or bound some other function, cannot produce it.
#[test]
fn an_embedder_registered_function_is_callable_from_an_operation_map() {
    let src = program("wi1122.ok", "answer: \"embedder_answer\"");
    let mut interp = interp_with_host_fn(&src, "embedder_answer", 1, embedder_answer)
        .expect("a registered key must let the interpreter build");

    let v = interp
        .call("wi1122.ok.Driver.ask", &[Value::Int(0)])
        .expect("the mapped operation must run");
    assert_eq!(
        v.as_int(),
        Some(407),
        "the embedder's function must be what ran: 4 * 100 + 7"
    );
}

/// THE PLACEMENT TEST, and the one that isolates it. The registry is on the
/// `KnowledgeBase` because `run_in_bridge_interp` (`kb/resolve.rs`) `mem::take`s the
/// KB and builds a FRESH `Interpreter` from it per bridged evaluation — one per
/// `[simp]` fire, per bridged `eq` dispatch — then registers builtins on THAT. A table
/// held by the embedder's own interpreter is simply absent there, and since an unknown
/// key is FATAL the scratch interpreter would fail to BUILD: one `operation_map` entry
/// would break resolution program-wide, at call sites having nothing to do with it.
///
/// Modeled here by the round-trip that `run_in_bridge_interp` performs: take the KB
/// back out of one interpreter (`into_kb`) and build a second over it. That is not an
/// approximation of the production path — `mem::take` on a `&mut KnowledgeBase`
/// resolves through `Default`/`new`, so the scratch interpreter receives the KB by the
/// same move this does, and gets its builtins registered by the same call.
///
/// The second interpreter is what carries the assertions: it must BUILD (the fatal
/// unknown-key refusal is what fires otherwise) and must RUN the operation to the same
/// value. Every other test in this file uses only the interpreter the embedder itself
/// built, so all of them pass under an `Interpreter`-held table and this one does not
/// — which is what makes it worth its own fixture.
#[test]
fn an_embedder_function_survives_a_fresh_interpreter_over_the_same_kb() {
    let src = program("wi1122.fresh", "answer: \"embedder_answer\"");
    let first = interp_with_host_fn(&src, "embedder_answer", 1, embedder_answer)
        .expect("the embedder's own interpreter must build");

    // The move `run_in_bridge_interp` makes: the KB leaves the interpreter, and a new
    // interpreter is built over it and given its builtins.
    let kb = first.into_kb();
    let mut second = Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut second).unwrap_or_else(|e| {
        panic!(
            "the second interpreter must build: {e:?}\n\
             an EvalError::Internal naming the host_fn key here means the embedder \
             table did not ride the KB — i.e. it is held by the Interpreter, and every \
             bridged evaluation in the program would fail this way"
        )
    });

    assert_eq!(
        second
            .call("wi1122.fresh.Driver.ask", &[Value::Int(0)])
            .expect("the mapped operation must run on the second interpreter too")
            .as_int(),
        Some(407),
        "and it must reach the SAME embedder function, not merely register something",
    );
}

// ── The arity check, inherited unchanged ─────────────────────────────

/// The WI-876 arity check applies to an EMBEDDER entry, and it is the reason `HostFn`
/// is one shared type rather than one per registry.
///
/// The operation declares ONE argument; the entry declares TWO. WI-876 measured what
/// accepting this costs: the program loads clean, passes `anthill check`, and dies
/// `ArityMismatch` at the first call.
///
/// WHERE IT IS REFUSED: at INTERPRETER BUILD, not at `register_host_fn`. The seam
/// cannot check it — no mapping exists on the KB when the embedder registers, so
/// nothing there knows what the operation declares. `register_operation_mappings` is
/// the earliest point that knows both, which is exactly what WI-876 said when it put
/// the check there. (The fixture asserts the registration itself SUCCEEDS, via
/// `interp_with_host_fn`.) The message must name both numbers so the repair is obvious.
#[test]
fn an_embedder_entry_of_the_wrong_arity_is_refused() {
    let src = program("wi1122.arity", "answer: \"embedder_pair\"");
    let err = interp_with_host_fn(&src, "embedder_pair", 2, embedder_pair)
        .err()
        .expect("an arity disagreement must refuse the interpreter build");

    // On the ARITY message specifically, not on the digits 1 and 2 appearing
    // anywhere: an earlier draft asserted `err.contains('1') && err.contains('2')`
    // and passed with the whole fix backed out, because the namespace
    // `wi1122.arity` supplies both digits and the unknown-key refusal quotes it.
    // A control run is what caught it.
    assert!(
        err.contains("embedder_pair"),
        "names the host function: {err}"
    );
    assert!(
        err.contains("takes 1 argument(s)"),
        "says what the OPERATION takes: {err}"
    );
    assert!(
        err.contains("takes 2"),
        "says what the HOST FUNCTION takes: {err}"
    );
}

/// THE CONTROL for the test above: the same fixture at MATCHING arity runs. Without
/// this, a refusal that fired on every embedder entry — arity or no arity — would look
/// like a passing arity check.
#[test]
fn the_control_a_matching_arity_runs() {
    let src = program("wi1122.arityok", "answer: \"embedder_answer\"");
    let mut interp = interp_with_host_fn(&src, "embedder_answer", 1, embedder_answer)
        .expect("matching arity must build");
    assert_eq!(
        interp
            .call("wi1122.arityok.Driver.ask", &[Value::Int(0)])
            .expect("must run")
            .as_int(),
        Some(407),
    );
}

// ── Collisions are refused, not ordered ──────────────────────────────

/// An embedder may not take a key this runtime already ships. Refused rather than
/// resolved by precedence: whichever side won, a program's behavior would change
/// silently when the other side later added the same key, and the `operation_map`
/// site spells only the key, so nothing there would show it.
#[test]
fn an_embedder_cannot_shadow_a_builtin_key() {
    let mut kb = KnowledgeBase::new();
    let err = kb
        .register_host_fn("ordered_compare", 2, embedder_pair)
        .expect_err("a key HOST_FNS ships must be refused");

    assert_eq!(
        err,
        HostFnRegError::ShadowsBuiltin {
            key: "ordered_compare".to_string()
        },
    );
    assert!(
        err.to_string().contains("ordered_compare"),
        "the message names the key: {err}"
    );
}

/// The same key registered twice by the embedder is refused — a key names exactly one
/// function. Silently keeping the first (or the last) would make the binding depend on
/// registration order, which is invisible at the `operation_map` site.
#[test]
fn an_embedder_key_cannot_be_registered_twice() {
    let mut kb = KnowledgeBase::new();
    kb.register_host_fn("embedder_answer", 1, embedder_answer)
        .expect("the first registration must succeed");
    let err = kb
        .register_host_fn("embedder_answer", 1, embedder_answer)
        .expect_err("the second must be refused");

    assert_eq!(
        err,
        HostFnRegError::Duplicate {
            key: "embedder_answer".to_string()
        },
    );
}

/// THE CONTROL for both refusals: a fresh key registers. Without it, a
/// `register_host_fn` that refused everything would pass the two tests above.
#[test]
fn the_control_a_fresh_key_registers() {
    let mut kb = KnowledgeBase::new();
    kb.register_host_fn("embedder_answer", 1, embedder_answer)
        .expect("a key in neither registry must register");
}

// ── Ordering is ENFORCED, not merely documented ──────────────────────

/// A LATE registration is refused. The ordering rule ("register before load") was a doc
/// line in the first draft of this ticket; the /code-review pass showed why that is not
/// enough, and this is the test for the enforcement that replaced it.
///
/// WHAT GOES WRONG UNENFORCED, and why it is worse than it looks: load itself builds
/// interpreters (a `[simp]` macro fire crosses `run_in_bridge_interp`). A key registered
/// afterwards is missing from those, so the scratch build fails with an
/// `EvalError::Internal` — and BOTH bridge callers residualize it. `simp_rewrite.rs`'s
/// macro arm and `resolve.rs`'s `bridge_op_to_eval` each `debug_assert!` that the error
/// is not `Internal` and then answer "nothing". In a DEBUG build the assert fires; in a
/// RELEASE build the macro silently does not expand and the rule silently does not
/// answer, on a program that loaded clean. That is a silent wrong answer reachable
/// purely by embedder call ordering, so the refusal moves to the seam.
#[test]
fn a_host_fn_registered_after_load_is_refused() {
    let src = program("wi1122.late", "answer: \"embedder_answer\"");
    // Load with the key registered on time, so the program itself is well-formed and
    // the only thing under test is the SECOND, late registration.
    let mut kb = crate::common::try_load_kb_prepared(&src, |kb| {
        kb.register_host_fn("embedder_answer", 1, embedder_answer)
            .expect("the on-time registration must succeed");
    })
    .unwrap_or_else(|errs| panic!("expected a clean load; got: {errs:?}"));

    let err = kb
        .register_host_fn("another_key", 1, embedder_answer)
        .expect_err("a registration after load must be refused");
    assert_eq!(
        err,
        HostFnRegError::AfterLoad {
            key: "another_key".to_string()
        },
    );
    assert!(
        err.to_string().contains("BEFORE calling load_all"),
        "the message must say what to do instead: {err}"
    );
}

/// THE CONTROL for the seal: the SAME key, registered BEFORE load, is accepted and runs.
/// Without it, a seal that refused every registration would pass the test above.
#[test]
fn the_control_the_same_registration_before_load_is_accepted() {
    let src = program("wi1122.ontime", "answer: \"embedder_answer\"");
    let mut interp = interp_with_host_fn(&src, "embedder_answer", 1, embedder_answer)
        .expect("registering before load must be accepted");
    assert_eq!(
        interp
            .call("wi1122.ontime.Driver.ask", &[Value::Int(0)])
            .expect("must run")
            .as_int(),
        Some(407),
    );
}

// ── An embedder function may CLOSE OVER its own state ────────────────

/// A CLOSURE, not a bare `fn` — the shape the seam's first consumer actually needs.
/// WI-1117 binds `gh_create_entry`, which needs a repo handle and a token; a bare `fn`
/// pointer captures neither, and would force every embedder into a `static` or a
/// thread-local. `Interpreter::register_builtin_sym` already accepts any `Fn + 'static`,
/// so this costs only the `Arc`.
///
/// The captured value is what the assertion reads: `4 * 100 + 7 + 9000` can only come
/// from a function that both ran on the argument AND saw `offset`. A seam that silently
/// dropped the capture, or that only accepted `fn` pointers, cannot produce it.
#[test]
fn an_embedder_function_may_close_over_its_own_state() {
    let src = program("wi1122.closure", "answer: \"embedder_configured\"");
    let offset = 9000i64; // stands in for an embedder's config: a token, a repo, a client

    let kb = crate::common::try_load_kb_prepared(&src, move |kb| {
        kb.register_host_fn("embedder_configured", 1, move |_interp, args: &[Value]| {
            match args {
                [Value::Int(n)] => Ok(Value::Int(n * 100 + 7 + offset)),
                other => Err(EvalError::Internal(format!("got {other:?}"))),
            }
        })
        .expect("a closure must be registerable");
    })
    .unwrap_or_else(|errs| panic!("expected a clean load; got: {errs:?}"));

    let mut interp = Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("a closure entry must let the interpreter build");
    assert_eq!(
        interp
            .call("wi1122.closure.Driver.ask", &[Value::Int(0)])
            .expect("the closure must run")
            .as_int(),
        Some(9407),
        "the CAPTURED offset must have reached the call",
    );
}

// ── The registry stays CLOSED ────────────────────────────────────────

/// PASSES BOTH WITH AND WITHOUT THE CHANGE, BY DESIGN. WI-876's refusal is what keeps
/// `operation_map` from binding to nothing, and the fix must not have been "accept any
/// key": a mapping naming a function NEITHER registry has is still fatal, and still
/// says so.
///
/// The embedder here registers a real function under a DIFFERENT key, so the miss is
/// a POPULATED table not containing the key rather than an absent table — the two are
/// distinct paths through the lookup, and only this one exercises the second half.
#[test]
fn an_unregistered_key_is_still_fatal() {
    let src = program("wi1122.missing", "answer: \"no_such_host_function\"");
    let err = interp_with_host_fn(&src, "embedder_answer", 1, embedder_answer)
        .err()
        .expect("a key in neither registry must refuse the interpreter build");

    assert!(
        err.contains("no_such_host_function"),
        "names the key that is missing: {err}"
    );
}

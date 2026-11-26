//! WI-20261126-7BJGQ — a host can call an operation whose `requires` names its parameters:
//! `Interpreter::call_assuming_requires` (and `call_bracketed_assuming_requires`) types the
//! call as if its value preconditions were established, the host taking them on itself.
//!
//! `Interpreter::call` types `op(__host_argument_0, …)` as the body of an operation of the
//! host's, which requires nothing, so a value precondition over a parameter is to be proved
//! where no guard, no prior `ensures` and no fact names the arguments: refused whatever the
//! values (MEASURED, the ticket's probe: `small(__host_argument_0)` "provable at the call
//! site, got unsatisfied precondition"). A host that decides the `requires` itself — anthill-
//! traces' runner, which checks them on the values with its own contract evaluator — had no
//! way to call such an operation. The user's decision (2026-11-26): shape (a), an explicit
//! entry where the host vouches for the preconditions; `call` is unchanged.
//!
//! WHICH CALLS THE HOST VOUCHES FOR: the operation it names, and the defaults spliced into
//! that call — not a call a `@[simp]` equation rewrites it into, whose preconditions the host
//! never decided (found by `/code-review`; `TypingEnv::vouch_for_preconditions_of`).
//!
//! BACK-OUT, measured on a binary of this file alone, 11 rows (each change made by hand, the
//! file run, the change undone):
//!
//!  * The host's vouching not passed to the typer (`call_entry` never calls
//!    `vouch_for_preconditions_of`): 8 RED, every row that runs through the new entry —
//!    `the_tickets_probe…`, `the_host_takes_on_what_it_vouches_for…`, `a_providers_member…`,
//!    `a_spec_operations_body…`, `a_default_spliced…`, `the_bracketed_entry…`,
//!    `a_clause_mixing…` and `a_vouched_call_does_not_type_a_plain_one` (its vouched half).
//!    GREEN either way, BY DESIGN, the three that pin what the entry must not change:
//!    `a_plain_call_still_refuses_the_precondition`, `a_requirement_over_a_spec_is_still_owed`
//!    and `a_call_a_simp_equation_rewrites_it_into_is_still_proved`.
//!  * The typed-call cache keyed without the vouching (`HostCallKey` holding
//!    `Preconditions::Proved` whatever the entry): RED are the five rows that make a plain
//!    call after a vouched one at the same types — `a_vouched_call_does_not_type_a_plain_one`,
//!    `a_providers_member…`, `a_spec_operations_body…`, `a_default_spliced…`,
//!    `the_bracketed_entry…` — each plain call taking the vouched typing and running.
//!  * Every call of the host's typing vouched for, not the named operation's and its
//!    defaults' (the second cut): RED is `a_call_a_simp_equation_rewrites_it_into_is_still_
//!    proved` alone (`outer(7)` ran `inner(7)`, 107).
//!  * The named operation's alone, a spliced default's call proved (the first cut):
//!    RED is `a_default_spliced_into_the_call_is_vouched_for_too` alone (`tiny(__host_
//!    argument_0)` refused at the splice).

use anthill_core::eval::{EvalError, HostValue, Interpreter, Value};

use crate::common::interp_for;

const SRC: &str = r#"
namespace bjgq
  import anthill.prelude.{Int64, String, Additive}
  rule small(?n) :- ?n < 10
  rule tiny(?n) :- ?n < 5
  sort S
    operation guarded(n: Int64) -> Int64
      requires small(n)
      = n + 1
    operation free(n: Int64) -> Int64
      = n + 1
  end
  sort Spec
    sort T = ?
    operation f(s: T, n: Int64) -> Int64
      requires small(n)
    operation g(s: T, n: Int64) -> Int64
      requires small(n)
      = n + 2
  end
  sort Impl
    entity mk(id: Int64)
    provides Spec[T = Impl]
    operation f(s: Impl, n: Int64) -> Int64
      requires small(n)
      = n + 1
  end
  operation make() -> Impl = Impl.mk(id: 0)
  sort D
    operation h(n: Int64) -> Int64
      requires tiny(n)
      = n
    operation withdef(n: Int64, m: Int64 = h(n)) -> Int64
      requires tiny(n), small(n)
      = n + m
  end
  operation scaled[X](n: Int64) -> Int64
    requires small(n)
    requires Additive[T = X]
    = n + 1
  operation zeroOf[X]() -> X requires Additive[T = X] = Additive.zero[T = X]()
  operation mixed[X](n: Int64) -> Int64
    requires small(n), Additive[T = X]
    = n + 1
  operation inner(n: Int64) -> Int64
    requires tiny(n)
    = n + 100
  operation outer(n: Int64) -> Int64
    requires small(n)
  rule r: outer(?n) <=> inner(?n) @[simp]
end
"#;

fn op(name: &str) -> String {
    format!("bjgq.{name}")
}

fn int(n: i64) -> HostValue {
    HostValue::from(Value::Int(n))
}

/// The answer of `name` called through the entry for a host that vouches for its
/// preconditions; it must run.
fn vouched(interp: &mut Interpreter, name: &str, args: &[HostValue]) -> Value {
    interp
        .call_assuming_requires(&op(name), args)
        .map(|h| h.value)
        .unwrap_or_else(|e| panic!("`{name}` called by a host vouching for its `requires` must run; got {e:?}"))
}

/// The refusal of `name` called through the plain entry: its sentence, which must name an
/// unsatisfied precondition.
fn refused_plain(interp: &mut Interpreter, name: &str, args: &[HostValue]) -> String {
    match interp.call(&op(name), args) {
        Err(EvalError::HostCallRefused { detail, .. }) => {
            assert!(
                detail.contains("unsatisfied precondition"),
                "`{name}`: refused for its precondition, got: {detail}"
            );
            detail
        }
        other => panic!("`{name}` called plainly must be refused for its precondition; got {other:?}"),
    }
}

// ── (1) the ticket's probe ──────────────────────────────────────────────

#[test]
fn the_tickets_probe_runs_through_the_assume_entry() {
    let mut interp = interp_for(SRC);
    assert!(matches!(vouched(&mut interp, "S.guarded", &[int(3)]), Value::Int(4)));
    // An operation with no precondition answers through either entry.
    assert!(matches!(vouched(&mut interp, "S.free", &[int(3)]), Value::Int(4)));
    let plain = interp.call(&op("S.free"), &[int(3)]).map(|h| h.value);
    assert!(matches!(plain, Ok(Value::Int(4))), "`free` through `call`: {plain:?}");
}

#[test]
fn the_host_takes_on_what_it_vouches_for_nothing_checks_it_at_run_time() {
    // `small(12)` is false; the host vouched for it, and the body runs. What the entry is
    // FOR: the host decides, the call does not decide again.
    let mut interp = interp_for(SRC);
    assert!(matches!(vouched(&mut interp, "S.guarded", &[int(12)]), Value::Int(13)));
}

// ── (2) the control: the default entry still refuses ───────────────────

#[test]
fn a_plain_call_still_refuses_the_precondition() {
    let mut interp = interp_for(SRC);
    let detail = refused_plain(&mut interp, "S.guarded", &[int(3)]);
    assert!(detail.contains("small(__host_argument_0)"), "names the clause: {detail}");
}

#[test]
fn a_vouched_call_does_not_type_a_plain_one() {
    // The typed call is kept per operation and argument types. A plain call at the types a
    // vouched one was typed at must still be refused, and a vouched call after a refused
    // plain one still run.
    let mut interp = interp_for(SRC);
    assert!(matches!(vouched(&mut interp, "S.guarded", &[int(3)]), Value::Int(4)));
    refused_plain(&mut interp, "S.guarded", &[int(3)]);
    assert!(matches!(vouched(&mut interp, "S.guarded", &[int(5)]), Value::Int(6)));
}

// ── (3) a provider's member, and a spec operation's body ──────────────

#[test]
fn a_providers_member_restating_the_requires_runs() {
    let mut interp = interp_for(SRC);
    let mk = interp.call(&op("make"), &[]).expect("`make` answers an `Impl`");
    // Named directly, and through the spec it provides.
    assert!(matches!(vouched(&mut interp, "Impl.f", &[mk.clone(), int(3)]), Value::Int(4)));
    assert!(matches!(vouched(&mut interp, "Spec.f", &[mk.clone(), int(3)]), Value::Int(4)));
    refused_plain(&mut interp, "Impl.f", &[mk.clone(), int(3)]);
    refused_plain(&mut interp, "Spec.f", &[mk, int(3)]);
}

#[test]
fn a_spec_operations_body_carrying_one_runs() {
    let mut interp = interp_for(SRC);
    let mk = interp.call(&op("make"), &[]).expect("`make` answers an `Impl`");
    assert!(matches!(vouched(&mut interp, "Spec.g", &[mk.clone(), int(3)]), Value::Int(5)));
    refused_plain(&mut interp, "Spec.g", &[mk, int(3)]);
}

#[test]
fn a_default_spliced_into_the_call_is_vouched_for_too() {
    // `withdef(3)` leaves `m` out; its default `h(n)` is typed again where the call is, with
    // `h`'s own `tiny(n)`. It follows from `withdef`'s `requires tiny(n)`, which the host
    // vouches for — as a default only loads where its preconditions follow from its
    // operation's — so the call runs: 3 + h(3).
    let mut interp = interp_for(SRC);
    assert!(matches!(vouched(&mut interp, "D.withdef", &[int(3)]), Value::Int(6)));
    refused_plain(&mut interp, "D.withdef", &[int(3)]);
}

#[test]
fn the_bracketed_entry_vouches_the_same_way() {
    // `scaled[X = Int64](3)`: the value precondition is the host's, the requirement over
    // `Additive` is supplied at `Int64` as for any call.
    let mut interp = interp_for(SRC);
    let int64 = crate::common::sort_type(interp.kb_mut(), "anthill.prelude.Int64");
    let got = interp
        .call_bracketed_assuming_requires(&op("scaled"), &[(Some("X"), int64.clone())], &[int(3)])
        .map(|h| h.value);
    assert!(matches!(got, Ok(Value::Int(4))), "`scaled[X = Int64](3)`, vouched: {got:?}");
    let plain = interp.call_bracketed(&op("scaled"), &[(Some("X"), int64)], &[int(3)]);
    assert!(
        matches!(&plain, Err(EvalError::HostCallRefused { detail, .. }) if detail.contains("unsatisfied precondition")),
        "`scaled[X = Int64](3)`, plain: {plain:?}"
    );
}

#[test]
fn a_clause_mixing_a_value_goal_with_a_requirement_takes_the_value_half_only() {
    // `requires small(n), Additive[T = X]` is ONE clause (WI-862's comma list). The host
    // vouches for `small(n)`; `Additive` is supplied at `Int64` and owed at `String`.
    let mut interp = interp_for(SRC);
    let int64 = crate::common::sort_type(interp.kb_mut(), "anthill.prelude.Int64");
    let string = crate::common::sort_type(interp.kb_mut(), "anthill.prelude.String");
    let got = interp
        .call_bracketed_assuming_requires(&op("mixed"), &[(Some("X"), int64)], &[int(3)])
        .map(|h| h.value);
    assert!(matches!(got, Ok(Value::Int(4))), "`mixed[X = Int64](3)`, vouched: {got:?}");
    let owed = interp.call_bracketed_assuming_requires(&op("mixed"), &[(Some("X"), string)], &[int(3)]);
    assert!(
        matches!(&owed, Err(EvalError::HostCallRefused { detail, .. }) if detail.contains("Additive")),
        "`mixed[X = String](3)`, vouched, still owes `Additive`: {owed:?}"
    );
}

// ── what the host cannot vouch for ─────────────────────────────────────

#[test]
fn a_call_a_simp_equation_rewrites_it_into_is_still_proved() {
    // `outer` has no body: `@[simp] outer(?n) <=> inner(?n)` rewrites the host's call into
    // `inner(__host_argument_0)`, whose `tiny(n)` the host never vouched for — `small(7)`
    // holds and `tiny(7)` does not. Proved as in a body, it is refused; a body calling
    // `outer(x)` under `small(x)` alone is refused for `tiny(x)` the same way.
    let mut interp = interp_for(SRC);
    match interp.call_assuming_requires(&op("outer"), &[int(7)]) {
        Err(EvalError::HostCallRefused { detail, .. }) => assert!(
            detail.contains("tiny(__host_argument_0)") && detail.contains("unsatisfied precondition"),
            "refused for the rewritten callee's own precondition: {detail}"
        ),
        other => panic!("`outer(7)` vouched for `small` alone must not run `inner`; got {other:?}"),
    }
    let twin = SRC.replacen(
        "\nend\n",
        "\n  operation body(x: Int64) -> Int64\n    requires small(x)\n    = outer(x)\nend\n",
        1,
    );
    let errs = crate::common::load_errors_of(&twin);
    assert!(
        errs.iter().any(|e| e.contains("tiny(x)") && e.contains("unsatisfied precondition")),
        "the body twin is refused for `tiny(x)`: {errs:?}"
    );
}


#[test]
fn a_requirement_over_a_spec_is_still_owed() {
    // No provision of `Additive` at `String`: the dictionary is owed whoever calls, and the
    // vouched call is refused in the plain call's sentence.
    let mut interp = interp_for(SRC);
    let string = crate::common::sort_type(interp.kb_mut(), "anthill.prelude.String");
    let refusal = |r: Result<HostValue, EvalError>| match r {
        Err(EvalError::HostCallRefused { detail, .. }) => detail,
        other => panic!("`zeroOf[X = String]()` must be refused; got {other:?}"),
    };
    let vouched = refusal(interp.call_bracketed_assuming_requires(
        &op("zeroOf"),
        &[(Some("X"), string.clone())],
        &[],
    ));
    let plain = refusal(interp.call_bracketed(&op("zeroOf"), &[(Some("X"), string)], &[]));
    assert_eq!(vouched, plain, "the same refusal through either entry");
    assert!(vouched.contains("Additive"), "names the requirement: {vouched}");
}

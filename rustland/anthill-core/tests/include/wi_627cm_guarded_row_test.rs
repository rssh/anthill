//! WI-20261029-627CM — a body is held to the guarded elements of its own effect row
//! (kernel-language.md §5.5). `L :- g` in an operation's row says that after a call `L` is
//! possible only where `g` holds, so each call in the body that incurs `L` must show `g` from
//! what holds at the call — or the call's own guard for `L`, its arguments substituted, must.
//!
//! Each row drives the program: a refusal names the label and the guard, and its accepted
//! twin runs to the value it leaves. Which part each row needs is said at the row, as the
//! parts that fail it when backed out alone (measured with one switch per part, in one
//! build). Backing out the check itself (`hold`) fails every row with a refusal; an accepted
//! program passes it either way by design — before this ticket a guarded element admitted its
//! label wherever the body incurred it. Two parts fail every row, as the stdlib is refused
//! without them: the arm's `===` fact (`struct`) and a guarded law in a proof from Γ (`law`).
//! A guarded atom a call kept is charged as its label where a name's scope ends (`charge`):
//! without it a guarded write to a fresh cell was undeclared, which fails each accepted twin
//! that writes one. The call over a parameter not evaluated in a guarded law's clause search
//! is driven by `wi1122_embedder_host_fn_test`, `wi1075_absolute_path_test` and
//! `wi_brt4y_host_implemented_test`, whose host binding blocks no evaluation survives.

use crate::common::{assert_refused_naming, load_errors_of, run_int64, try_load_kb_with};
use anthill_core::eval::{self, EvalError, Interpreter, Value};

fn program(ns: &str, body: &str) -> String {
    format!(
        "namespace test.n627.{ns}\n  import anthill.prelude.{{Int64, Bool, Cell, List, Unit, Error, DivisionByZero, EmptyStream, Stream}}\n  import anthill.prelude.Int64.{{div}}\n  import anthill.prelude.PartialEq.{{eq}}\n  import anthill.prelude.Stream.{{isEmpty}}\n  import anthill.prelude.EmptyStream.{{empty_stream}}\n{body}\nend\n"
    )
}

fn refused_at(ns: &str, body: &str, op: &str, label: &str, guard: &str, why: &str) {
    assert_refused_naming(
        &load_errors_of(&program(ns, body)),
        &[
            &format!("{op}.effects"),
            &format!("`{label}` only where `{guard}` holds"),
        ],
        why,
    );
}

/// The ticket's program: a write the row declares under `eq(b, true)`, made for every `b`.
/// Fails with the check backed out (`hold`): it loaded, and `caller(c)` wrote the cell
/// declaring nothing.
#[test]
fn a_write_made_for_every_b_is_refused() {
    refused_at(
        "always",
        r#"
  operation always(s: Cell[V = Int64], b: Bool) -> Unit effects { Modify[s] :- eq(b, true) } =
    Cell.set(s, 7)
"#,
        "always",
        "Modify[T = s]",
        "eq(b, true)",
        "a write under no condition is not one only where `b` is true",
    );
}

/// The write made only where `b` is false. Fails with the check backed out (`hold`).
#[test]
fn a_write_in_the_else_branch_is_refused() {
    refused_at(
        "else_branch",
        r#"
  operation always(s: Cell[V = Int64], b: Bool) -> Unit effects { Modify[s] :- eq(b, true) } =
    if b then () else Cell.set(s, 9)
"#,
        "always",
        "Modify[T = s]",
        "eq(b, true)",
        "the else branch holds `not(b)`",
    );
}

/// The write made only where `b` holds: under `if b`, `b = true` holds. Fails with that fact
/// backed out (`cond`), and with `charge` (`written` writes a fresh cell).
#[test]
fn a_write_under_if_b_loads_and_runs() {
    let src = program(
        "then_branch",
        r#"
  operation onlyIf(s: Cell[V = Int64], b: Bool) -> Unit effects { Modify[s] :- eq(b, true) } =
    if b then Cell.set(s, 1) else ()
  operation skipped() -> Int64 =
    let c = Cell.new(5)
    let _ = onlyIf(c, false)
    Cell.get(c)
  operation written() -> Int64 =
    let c = Cell.new(5)
    let _ = onlyIf(c, true)
    Cell.get(c)
"#,
    );
    assert_eq!(run_int64(&src, "test.n627.then_branch.skipped"), Ok(5));
    assert_eq!(run_int64(&src, "test.n627.then_branch.written"), Ok(1));
}

/// The call's own guard, its argument substituted, is the row's guard. Fails with the
/// callee's guard not assumed (`hyp`).
#[test]
fn a_call_whose_own_guard_is_the_rows_loads() {
    let src = program(
        "safe_div",
        r#"
  operation safeDiv(a: Int64, b: Int64) -> Int64 effects { Error[DivisionByZero] :- eq(b, 0) } =
    div(a, b)
  operation go() -> Int64 = safeDiv(6, 3)
"#,
    );
    assert_eq!(run_int64(&src, "test.n627.safe_div.go"), Ok(2));
    // A guard over another operand shows nothing about `b`. Fails with the check backed out
    // (`hold`).
    refused_at(
        "safe_div_other",
        r#"
  operation divOther(a: Int64, b: Int64) -> Int64 effects { Error[DivisionByZero] :- eq(b, 0) } =
    div(b, a)
"#,
        "divOther",
        "Error[T = DivisionByZero]",
        "eq(b, 0)",
        "`div(b, a)` raises where `a` is 0",
    );
}

/// A call whose guard is refuted where it is written incurs nothing, so it owes nothing; and
/// a row that also admits the label unguarded admits it. Pass either way by design.
#[test]
fn a_refuted_call_and_an_unguarded_twin_owe_nothing() {
    let src = program(
        "owe_nothing",
        r#"
  operation half(a: Int64, b: Int64) -> Int64 effects { Error[DivisionByZero] :- eq(b, 0) } =
    div(a, 2)
  operation both(s: Cell[V = Int64], b: Bool) -> Unit effects { Modify[s], Modify[s] :- eq(b, true) } =
    Cell.set(s, 3)
  operation go() -> Int64 =
    let c = Cell.new(0)
    let _ = both(c, false)
    Cell.get(c) + half(8, 1)
"#,
    );
    assert_eq!(run_int64(&src, "test.n627.owe_nothing.go"), Ok(7));
}

/// `Stream.head` and `Stream.tail` raise in the `none()` arm of `match splitFirst(s)`: the arm
/// shows `splitFirst(s) === none`, and the law `isEmpty(?s) = true :- splitFirst(?s) === none`
/// shows their guard `isEmpty(s)` from it. `List.head` raises in the `nil()` arm of `match
/// xs`, through the law `isEmpty(?xs) = true :- ?xs === nil`. Each fails, with the stdlib
/// refused, with the arm's `===` fact backed out (`struct`) or the law kept from the proof
/// (`law`).
#[test]
fn the_stdlib_heads_raise_only_where_the_stream_is_empty() {
    let src = program(
        "heads",
        r#"
  operation viaStream() -> Int64 effects Error[EmptyStream] = Stream.head(Stream.tail([4, 5]))
  operation viaList() -> Int64 effects Error[EmptyStream] = List.head([6, 7])
  operation ofNil() -> Int64 effects Error[EmptyStream] =
    let e: List[T = Int64] = []
    List.head(e)
"#,
    );
    assert_eq!(run_int64(&src, "test.n627.heads.viaStream"), Ok(5));
    assert_eq!(run_int64(&src, "test.n627.heads.viaList"), Ok(6));
    let mut interp = Interpreter::new(crate::common::load_kb_with(&src));
    eval::builtins::register_standard_builtins(&mut interp).expect("register standard builtins");
    match interp.call("test.n627.heads.ofNil", &[]) {
        Err(EvalError::Raised {
            payload: Value::Entity { functor, .. },
            ..
        }) => assert_eq!(
            interp.kb().qualified_name_of(functor),
            "anthill.prelude.EmptyStream.empty_stream",
            "the head of an empty list raises `empty_stream`"
        ),
        other => panic!("the head of an empty list raises, got {other:?}"),
    }
}

/// A Γ fact that is the goal as written answers it: `if isEmpty(xs)` shows `isEmpty(xs)`, and
/// so does `List.head(xs)`'s own guard. Fails with the as-written match backed out
/// (`written`), and with `hyp`.
#[test]
fn a_bool_operation_that_holds_shows_its_guard() {
    let src = program(
        "as_written",
        r#"
  operation firstIf(xs: List[T = Int64]) -> Int64 effects { Error[EmptyStream] :- isEmpty(xs) } =
    if isEmpty(xs) then Error.raise(empty_stream) else 0
  operation viaList(xs: List[T = Int64]) -> Int64 effects { Error[EmptyStream] :- isEmpty(xs) } =
    List.head(xs)
  operation viaSpec(xs: List[T = Int64]) -> Int64 effects { Error[EmptyStream] :- isEmpty(xs) } =
    Stream.head(xs)
  operation go() -> Int64 effects Error[EmptyStream] = firstIf([1]) + viaList([20]) + viaSpec([300])
"#,
    );
    assert_eq!(run_int64(&src, "test.n627.as_written.go"), Ok(320));
    refused_at(
        "as_written_other",
        r#"
  operation viaSpec(xs: List[T = Int64], ys: List[T = Int64]) -> Int64
      effects { Error[EmptyStream] :- isEmpty(xs) } =
    Stream.head(ys)
"#,
        "viaSpec",
        "Error[T = EmptyStream]",
        "isEmpty(xs)",
        "the head of `ys` raises where `ys` is empty",
    );
}

/// A write through a `let`-bound or a pattern-bound name is the write to the memory the name
/// reaches at the call (§5.6). Fails with the name's memory not read at the call (`mem`):
/// the label named `x` / `c`, which no element admits, and the boundary charged it to `s`
/// with the guard admitting it. The accepted twins fail with `cond` and `charge`.
#[test]
fn a_write_through_a_bound_name_is_held_as_the_parameters() {
    refused_at(
        "let_alias",
        r#"
  operation viaLet(s: Cell[V = Int64], b: Bool) -> Unit effects { Modify[s] :- eq(b, true) } =
    let x = s
    Cell.set(x, 1)
"#,
        "viaLet",
        "Modify[T = s]",
        "eq(b, true)",
        "`x` is `s`",
    );
    refused_at(
        "pattern",
        r#"
  entity box(c: Cell[V = Int64])
  operation viaPattern(s: Cell[V = Int64], b: Bool) -> Unit effects { Modify[s] :- eq(b, true) } =
    match box(c: s)
      case box(c) -> Cell.set(c, 1)
"#,
        "viaPattern",
        "Modify[T = s]",
        "eq(b, true)",
        "`c` is a field of a box holding `s`",
    );
    let src = program(
        "bound_ok",
        r#"
  entity box(c: Cell[V = Int64])
  operation viaLet(s: Cell[V = Int64], b: Bool) -> Unit effects { Modify[s] :- eq(b, true) } =
    let x = s
    if b then Cell.set(x, 1) else ()
  operation viaPattern(s: Cell[V = Int64], b: Bool) -> Unit effects { Modify[s] :- eq(b, true) } =
    match box(c: s)
      case box(c) -> if b then Cell.set(c, 20) else ()
  operation go() -> Int64 =
    let c = Cell.new(0)
    let d = Cell.new(0)
    let _ = viaLet(c, true)
    let _ = viaPattern(d, true)
    Cell.get(c) + Cell.get(d)
"#,
    );
    assert_eq!(run_int64(&src, "test.n627.bound_ok.go"), Ok(21));
    // Proposal 050.1 stage 6's program: `y` is `p` under `b` and a fresh cell otherwise, and
    // the write is charged `Modify[p]` whatever `b` is until the join carries its condition.
    refused_at(
        "ptt6d",
        r#"
  operation touch(p: Cell[V = Int64], b: Bool) -> Unit effects { Modify[p] :- eq(b, true) } =
    let y = if b then p else Cell.new(0)
    Cell.set(y, 1)
"#,
        "touch",
        "Modify[T = p]",
        "eq(b, true)",
        "the join charges `p` for every `b`",
    );
}

/// A lambda's body is incurred where the function is applied, so the write is held at the
/// application. Fails with the lambda's body held where it is written (`lambda`): `lambdaIf`
/// is refused. Also with `cond` and `charge`.
#[test]
fn a_lambda_is_held_where_it_is_applied() {
    let src = program(
        "lambda_ok",
        r#"
  operation lambdaIf(s: Cell[V = Int64], b: Bool) -> Unit effects { Modify[s] :- eq(b, true) } =
    let f = lambda (n: Int64) -> Cell.set(s, n)
    if b then f(4) else ()
  operation go() -> Int64 =
    let c = Cell.new(0)
    let _ = lambdaIf(c, true)
    Cell.get(c)
"#,
    );
    assert_eq!(run_int64(&src, "test.n627.lambda_ok.go"), Ok(4));
    refused_at(
        "lambda_always",
        r#"
  operation lambdaAlways(s: Cell[V = Int64], b: Bool) -> Unit effects { Modify[s] :- eq(b, true) } =
    let f = lambda (n: Int64) -> Cell.set(s, n)
    f(4)
"#,
        "lambdaAlways",
        "Modify[T = s]",
        "eq(b, true)",
        "the application writes `s` for every `b`",
    );
}

/// A callback's row is its promise: `f` raises only where its argument is 0, so `f(y)`
/// raises only where `y` is. (An argument whose row holds the label is refused at the slot,
/// §5.5, so the promise is kept by a function that does not raise.) Fails with the callback's
/// guard not assumed (`callback`), and with `hyp`.
#[test]
fn a_callbacks_own_guard_is_its_arguments() {
    let src = program(
        "callback",
        r#"
  operation viaCallback(y: Int64, f: (x: Int64) -> Int64 @ {Error[DivisionByZero] :- eq(x, 0)}) -> Int64
      effects { Error[DivisionByZero] :- eq(y, 0) } =
    f(y)
  operation go() -> Int64 = viaCallback(4, lambda (x: Int64) -> x * 3)
"#,
    );
    assert_eq!(run_int64(&src, "test.n627.callback.go"), Ok(12));
    refused_at(
        "callback_other",
        r#"
  operation viaCallback(y: Int64, z: Int64, f: (x: Int64) -> Int64 @ {Error[DivisionByZero] :- eq(x, 0)}) -> Int64
      effects { Error[DivisionByZero] :- eq(y, 0) } =
    f(z)
"#,
        "viaCallback",
        "Error[T = DivisionByZero]",
        "eq(y, 0)",
        "`f(z)` raises where `z` is 0",
    );
}

/// A parameter default's calls are the operation's (proposal 069 §3). Fails with the check
/// backed out (`hold`).
#[test]
fn a_default_is_held_to_the_row() {
    let errs = load_errors_of(&program(
        "default",
        r#"
  operation withDefault(a: Int64, b: Int64, n: Int64 = div(10, 0)) -> Int64
      effects { Error[DivisionByZero] :- eq(b, 0) } =
    a
"#,
    ));
    assert_refused_naming(
        &errs,
        &[
            "withDefault",
            "`Error[T = DivisionByZero]` only where `eq(b, 0)` holds",
        ],
        "the default divides by zero for every `b`",
    );
    // The loader's own verdict on the accepted twin, so the row above is not passing on a
    // fixture that fails for another reason.
    assert!(try_load_kb_with(&program(
        "default_ok",
        r#"
  operation withDefault(a: Int64, b: Int64, n: Int64 = div(10, 2)) -> Int64
      effects { Error[DivisionByZero] :- eq(b, 0) } =
    a
"#,
    ))
    .is_ok());
}

/// A call pinned to an override incurs what the override declares, which the spec operation's
/// row variable does not name: `Box.peek(m)` writes `m` through `MutBox.peek`. Fails with the
/// override's effects not held (`dispatched`): `peekAlways` loaded. Also with `cond` and
/// `charge`.
#[test]
fn a_call_pinned_to_an_override_is_held_to_its_effects() {
    const BOXES: &str = r#"
  import anthill.prelude.{Modify, Modifiable}
  sort Box
    effects Effect = ?
    operation peek(b: Self) -> Int64 effects Effect
  end
  sort MutBox
    entity mb(fd: Int64)
    provides Box
    provides Modifiable[T = Self]
    operation peek(b: MutBox) -> Int64 effects Modify[b] =
      match b
        case mb(x) -> x
  end
"#;
    let src = program(
        "dispatched",
        &format!(
            r#"{BOXES}
  operation peekIf(m: MutBox, flag: Bool) -> Int64 effects {{ Modify[m] :- eq(flag, true) }} =
    if flag then Box.peek(m) else 0
  operation go() -> Int64 =
    let m = mb(fd: 3)
    peekIf(m, true)
"#
        ),
    );
    assert_eq!(run_int64(&src, "test.n627.dispatched.go"), Ok(3));
    refused_at(
        "dispatched_always",
        &format!(
            r#"{BOXES}
  operation peekAlways(m: MutBox, flag: Bool) -> Int64 effects {{ Modify[m] :- eq(flag, true) }} =
    Box.peek(m)
"#
        ),
        "peekAlways",
        "Modify[T = m]",
        "eq(flag, true)",
        "`MutBox.peek` writes `m` for every `flag`",
    );
}

/// A recursive call whose argument has no term to substitute keeps its parameter in its
/// guard, and that parameter is the caller's own: the guard is not assumed there. Fails with
/// every conjunct of the callee's guard assumed (`unbound`): `f` loaded, though its recursive
/// call raises where its argument is 0, at `n` = 3.
#[test]
fn a_recursive_calls_unbound_guard_is_not_assumed() {
    refused_at(
        "recursive",
        r#"
  import anthill.prelude.Int64.{gt}
  operation f(n: Int64) -> Int64 effects { Error[DivisionByZero] :- eq(n, 0) } =
    if gt(n, 5) then div(10, n) else f(if eq(n, 3) then 0 else 6)
"#,
        "f",
        "Error[T = DivisionByZero]",
        "eq(n, 0)",
        "the recursive call raises where its argument is 0",
    );
}

/// Under `if b`, the else branch shows `b = false`. Fails with that fact backed out (`cond`).
#[test]
fn a_write_in_the_else_branch_of_if_b_shows_b_false() {
    let src = program(
        "else_false",
        r#"
  operation onlyIfNot(s: Cell[V = Int64], b: Bool) -> Unit effects { Modify[s] :- eq(b, false) } =
    if b then () else Cell.set(s, 2)
  operation go() -> Int64 =
    let c = Cell.new(0)
    let _ = onlyIfNot(c, false)
    Cell.get(c)
"#,
    );
    assert_eq!(run_int64(&src, "test.n627.else_false.go"), Ok(2));
}

/// A callback applied with a label fills its slots by the call's ranking, as an operation's
/// call does. Fails with the positional arguments paired by index only in a call without
/// labels (`ranked`).
#[test]
fn a_mixed_application_binds_the_callbacks_guard() {
    let src = program(
        "mixed",
        r#"
  operation viaCallback(y: Int64, f: (x: Int64, z: Int64) -> Int64 @ {Error[DivisionByZero] :- eq(x, 0)}) -> Int64
      effects { Error[DivisionByZero] :- eq(y, 0) } =
    f(y, z: 1)
  operation go() -> Int64 = viaCallback(4, lambda (x: Int64, z: Int64) -> x + z)
"#,
    );
    assert_eq!(run_int64(&src, "test.n627.mixed.go"), Ok(5));
}

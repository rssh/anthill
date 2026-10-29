//! WI-20261003-P1PVT — A FIELD READ OFF A STABLE VALUE PATH NAMES ITS EXISTENTIALS BY THE PATH.
//!
//! `h.s` over `s: Strm[T = Int64, E = ?]` is a `Strm[T = Int64, E = h.s.E]`: a path read twice
//! denotes one value, so its existential is one, and the path's own projection names it. A read
//! off what no path names (`mk().s`) keeps the fresh rigid WI-1063 opens a call's result to.
//!
//! TWO PLACES COMPUTE THE TYPE OF A FIELD PATH, and both now name the slots so
//! (`typing/elaborate.rs` `open_existentials`):
//!
//! * the EXPRESSION read `h.s` — a `field_access` call (`typing/apply.rs`, `read_path`);
//! * the RECEIVER of a WRITTEN projection `h.s.E` (`typing/projection.rs`
//!   `field_type_at_path`): in a body as written, through the `let` aliases in scope; at a call
//!   re-keyed to the argument's path, and fresh where the argument is no path
//!   (`projection::Receivers`).
//!
//! Before, the read opened a fresh rigid per read, while the written projection grounded to the
//! DECLARATION's own flexible `?`, which every use bound. So the ticket's program was refused,
//! and [`a_written_projection_off_a_fields_wildcard_is_no_flexible_type`] loaded and ran `x + 1`
//! on a `String`.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! MEASURED on 2026-10-17, on the tree this file is committed with, each part present but
//! disabled, on a temporary binary of this file and the 37 projection and existential suites
//! beside it (768 rows):
//!
//! 1. THE READ (`read_path` passed as `None`: a fresh rigid per read, as before). 11 FAIL:
//!    [`the_tickets_program_runs_to_42`], [`two_reads_of_one_path_agree`],
//!    [`a_let_alias_reads_the_path_it_names`],
//!    [`a_let_alias_in_a_nested_annotation_reads_the_path`],
//!    [`a_parameters_path_projection_is_the_callers_argument`],
//!    [`another_holders_row_is_not_the_arguments`],
//!    [`a_named_variable_is_named_by_its_first_slot`] and
//!    `a_lambda_at_a_call_whose_argument_is_no_path_waits_for_a_name`, where a read meets a
//!    written projection;
//!    [`reads_of_two_paths_do_not_agree`] and [`a_bare_nullary_operation_is_no_path`] on their
//!    TEXT alone (still refused, printing two rigids); and `wi_80zv8_written_wildcard_test`'s
//!    `a_field_read_opens_a_named_variable_too`, likewise on its text (`?x`).
//! 2. THE WRITTEN RECEIVER (`field_type_at_path`'s result discarded: the declared field type, its
//!    flexible `?`). 7 FAIL: [`the_tickets_program_runs_to_42`],
//!    [`a_let_alias_reads_the_path_it_names`],
//!    [`a_parameters_path_projection_is_the_callers_argument`],
//!    [`another_holders_row_is_not_the_arguments`],
//!    [`a_written_projection_off_a_fields_wildcard_is_no_flexible_type`] and
//!    [`a_call_whose_argument_is_no_path_opens_fresh`] — the hole itself, twice — and
//!    `a_lambda_at_a_call_whose_argument_is_no_path_waits_for_a_name`, whose unnamed call loads.
//!    [`a_named_variable_is_named_by_its_first_slot`] passes: a flexible `t.a.B` takes anything.
//! 3. A NAMED VARIABLE TAKES ITS FIRST SLOT'S PROJECTION (the `if let Some(path)` block of
//!    `open_existentials` skipped: a fresh rigid per read for it). 2 FAIL:
//!    [`a_named_variable_is_named_by_its_first_slot`] and `wi_80zv8_written_wildcard_test`'s
//!    `a_field_read_opens_a_named_variable_too` (its text).
//! 4. A CALL'S ARGUMENT THAT IS NO PATH OPENS FRESH (`Receivers::Call` keeping the callee's own
//!    path). 3 FAIL: [`a_call_whose_argument_is_no_path_opens_fresh`] — it loads —,
//!    `a_lambda_at_a_call_whose_argument_is_no_path_waits_for_a_name` — its unnamed call loads,
//!    hinted and checked at one callee-keyed `h.s.T` — and
//!    [`a_written_projection_off_a_fields_wildcard_is_no_flexible_type`] (its text: `h.s.T`).
//! 5. A BARE NULLARY OPERATION IS NO PATH (`stable_receiver_path` reading it as one). 1 FAILS:
//!    [`a_bare_nullary_operation_is_no_path`] — it loads.
//! 6. A BODY'S PATH IS READ THROUGH ITS `let` ALIASES (`Receivers::Own`'s aliases ignored). 1
//!    FAILS: [`a_let_alias_in_a_nested_annotation_reads_the_path`].
//!
//! CONTROLS, passing under every part by design: [`a_read_off_a_calls_result_opens_a_fresh_rigid`]
//! (no path, a fresh rigid either way) and [`a_receivers_slot_is_the_receivers`] (nothing opened:
//! the slot is the receiver's `V`). `wi_0rp29_review9_regressions_test`'s
//! `a_declared_fields_written_wildcard_is_opened` is the ticket's other control —
//! `takes_pure(h.s)` stays refused, `h.s.E` being no `{}`.
//!
//! NOT NAMED BY THE PATH, on this ticket's tree — a slot nested inside a written binding (`s:
//! Strm[T = List[T = ?]]`), a pattern binder over a stable scrutinee (`match h case hold(s)`
//! named `s.E`), and each reading of a call whose argument is no path — opened apart, each
//! refusing a correct program. WI-20261017-HQH9K opens a path once per body and a non-path
//! argument once per call (`wi_hqh9k_one_opening_of_a_field_path_test`); the lambda row here
//! turned with it, and the measurements above name it by its name on this ticket's tree,
//! `a_lambda_at_a_call_whose_argument_is_no_path_waits_for_a_name`.

use crate::common::{assert_refused_naming, load_errors_of as load_errors, run_int64 as run_src};

/// The declarations every row shares: a stream sort with an element and a row, a holder whose
/// field leaves the row open, a call that makes a holder.
const DECLS: &str = r#"
  import anthill.prelude.{Int64, Bool, String, Error, List}
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(t: T)
    operation each[EffP](s: Strm, f: (x: Int64) -> Bool @ {EffP, -s.E}) -> Bool effects {EffP} = f(1)
  end
  sort Hold
    entity hold(s: Strm[T = Int64, E = ?])
  end
  operation pure1(x: Int64) -> Bool = true
  operation same(a: Strm, b: Strm[E = a.E]) -> Int64 = 1
  operation mk() -> Hold = hold(s: strm(t: 1))
"#;

/// The ticket's operation: it hands `Strm.each` the read `h.s` and a callback declaring it lacks
/// `h.s.E`. Only the rows about it declare it, so a refusal row is judged on its own program.
const USE: &str = r#"
  operation use(h: Hold, g: (x: Int64) -> Bool @ {Error[String], -h.s.E}) -> Bool
    effects {Error[String]} = Strm.each(h.s, g)
"#;

fn program(ns: &str, body: &str) -> String {
    format!("namespace wi_p1pvt.{ns}\n{DECLS}\n{body}\nend\n")
}

fn program_with_use(ns: &str, body: &str) -> String {
    program(ns, &format!("{USE}\n{body}"))
}

// ── one value, one existential ───────────────────────────────────────────────────────────────

/// THE TICKET'S PROGRAM RUNS TO 42. `use`'s call `Strm.each(h.s, g)` reads the callee's `-s.E`
/// off the read `h.s`, and `g` declares `-h.s.E`: one value's row, spelled once. Refused before,
/// "expected callback … to lack the row `?E` …, got the callback `g` declares `Error[T =
/// String]`" (MEASURED).
#[test]
fn the_tickets_program_runs_to_42() {
    let src = program_with_use(
        "ticket",
        "  operation go() -> Int64 effects {Error[String]} =\n    if use(hold(s: strm(t: 1)), pure1) then 42 else 0",
    );
    assert_eq!(run_src(&src, "wi_p1pvt.ticket.go"), Ok(42));
}

/// TWO READS OF ONE PATH AGREE: `same(h.s, h.s)` over `same(a: Strm, b: Strm[E = a.E])`. Each
/// read opened its own rigid before, and the second was refused against the first.
#[test]
fn two_reads_of_one_path_agree() {
    let src = program(
        "twice",
        "  operation f(h: Hold) -> Int64 = same(h.s, h.s) + 41\n  operation go() -> Int64 = f(mk())",
    );
    assert_eq!(run_src(&src, "wi_p1pvt.twice.go"), Ok(42));
}

/// … AND READS OF TWO PATHS DO NOT: `h.s.E` is no `k.s.E`. Refused before too, by two fresh
/// rigids; the text names the two paths.
#[test]
fn reads_of_two_paths_do_not_agree() {
    let src = program(
        "two_paths",
        "  operation f(h: Hold, k: Hold) -> Int64 = same(h.s, k.s)",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["same.b (op-arg): expected Strm[E = h.s.E], got Strm[T = Int64, E = k.s.E]"],
        "the reads of two holders' streams passed for one row",
    );
}

/// A READ OFF A CALL'S RESULT OPENS A FRESH RIGID: `mk()` names no value, and two calls may
/// hold two rows. Control: refused, and printed so, before as after.
#[test]
fn a_read_off_a_calls_result_opens_a_fresh_rigid() {
    let src = program(
        "call_result",
        "  operation f() -> Int64 = same(mk().s, mk().s)",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["same.b (op-arg): expected Strm[E = ?E], got Strm[T = Int64, E = ?E]"],
        "the reads off two calls' results passed for one row",
    );
}

/// A `let` ALIAS READS THE PATH IT NAMES: `let t = h` then `t.s` is `h.s`, whose row `g`
/// declares it lacks.
#[test]
fn a_let_alias_reads_the_path_it_names() {
    let src = program(
        "alias",
        "  operation use2(h: Hold, g: (x: Int64) -> Bool @ {Error[String], -h.s.E}) -> Bool\n    effects {Error[String]} =\n    let t = h\n    Strm.each(t.s, g)\n  operation go() -> Int64 effects {Error[String]} =\n    if use2(mk(), pure1) then 42 else 0",
    );
    assert_eq!(run_src(&src, "wi_p1pvt.alias.go"), Ok(42));
}

// ── the written spelling ─────────────────────────────────────────────────────────────────────

/// A WRITTEN PROJECTION OFF A FIELD'S WILDCARD IS NO FLEXIBLE TYPE. `x: h.s.T` over `s: Strm[T =
/// ?]` grounded to the declaration's own `?`, which the body bound to `Int64` and the caller to
/// `String`: the program loaded and died in `x + 1`, "expected Int64, got String and Int64"
/// (MEASURED). Now `h.s.T` is the path's neutral in the body, refused there, and at the call —
/// whose argument is no path — an unknown of the call's own, which no `String` is.
#[test]
fn a_written_projection_off_a_fields_wildcard_is_no_flexible_type() {
    let src = r#"
namespace wi_p1pvt.written
  import anthill.prelude.{Int64, String}
  sort Strm
    sort T = ?
    entity strm(t: T)
  end
  sort Hold2
    entity hold2(s: Strm[T = ?])
  end
  operation takes_int(x: Int64) -> Int64 = x + 1
  operation u1(h: Hold2, x: h.s.T) -> Int64 = takes_int(x)
  operation go() -> Int64 = u1(hold2(s: strm(t: "a")), "hello")
end
"#;
    let errs = load_errors(src);
    assert_refused_naming(
        &errs,
        &["takes_int.x (op-arg): expected Int64, got h.s.T"],
        "a field's wildcard read as Int64 in the body",
    );
    assert_refused_naming(
        &errs,
        &["u1.x (op-arg): expected ?T, got String"],
        "a String passed for a holder's unknown element",
    );
}

/// A PARAMETER'S PATH PROJECTION IS RE-KEYED TO THE CALLER'S ARGUMENT: `use(k, g2)` reads `use`'s
/// `-h.s.E` as `-k.s.E`, which the caller's `g2` declares.
#[test]
fn a_parameters_path_projection_is_the_callers_argument() {
    let src = program_with_use(
        "rekey",
        "  operation caller(k: Hold, g2: (x: Int64) -> Bool @ {Error[String], -k.s.E}) -> Bool\n    effects {Error[String]} = use(k, g2)\n  operation go() -> Int64 effects {Error[String]} =\n    if caller(mk(), pure1) then 42 else 0",
    );
    assert_eq!(run_src(&src, "wi_p1pvt.rekey.go"), Ok(42));
}

/// … AND ANOTHER HOLDER'S ROW IS NOT IT: `g2` lacking `j.s.E` does not lack `k.s.E`. The
/// refusal is the call's alone: `use` itself loads.
#[test]
fn another_holders_row_is_not_the_arguments() {
    let src = program_with_use(
        "rekey_wrong",
        "  operation caller(k: Hold, j: Hold, g2: (x: Int64) -> Bool @ {Error[String], -j.s.E}) -> Bool\n    effects {Error[String]} = use(k, g2)",
    );
    let errs = load_errors(&src);
    assert_refused_naming(
        &errs,
        &["use.g (op-arg)", "to lack the row `k.s.E`"],
        "a callback lacking another holder's row passed for the argument's",
    );
    assert_eq!(
        errs.len(),
        1,
        "only the call is refused, `use` loads: {errs:?}"
    );
}

/// AT A CALL WHOSE ARGUMENT IS NO PATH, THE PARAMETER'S PATH OPENS FRESH. Kept as the callee's
/// own `h.s.T`, the self-recursive `run2(mk_int(), v, n - 1)` passed the caller's `v` — read off
/// the caller's `h` — for `mk_int()`'s element, the callee's `h` being the caller's own: the
/// program loaded and `app` ran `inc` on `"abc"` (MEASURED: this ticket's review).
#[test]
fn a_call_whose_argument_is_no_path_opens_fresh() {
    let src = r#"
namespace wi_p1pvt.no_path
  import anthill.prelude.{Int64, String}
  sort Strm
    sort T = ?
    entity strm(t: T, fn: (x: T) -> Int64)
  end
  sort Hold2
    entity hold2(s: Strm[T = ?])
  end
  operation inc(x: Int64) -> Int64 = x + 1
  operation slen(x: String) -> Int64 = 3
  operation mk_int() -> Hold2 = hold2(s: strm(t: 1, fn: inc))
  operation app(s: Strm, v: s.T) -> Int64 =
    let g = s.fn
    g(v)
  operation run2(h: Hold2, v: h.s.T, n: Int64) -> Int64 =
    if n < 1 then app(h.s, v) else run2(mk_int(), v, n - 1)
  operation go() -> Int64 =
    let h = hold2(s: strm(t: "abc", fn: slen))
    run2(h, h.s.t, 1)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["run2.v (op-arg): expected ?T, got h.s.T"],
        "a holder's element passed for another holder's at a self-recursive call",
    );
}

/// … BUT ONE FOR EVERY READING OF THE CALL: an unannotated lambda for `f: (x: h.s.T) -> Int64`
/// is hinted and checked at the call's one `h.s.T` and runs; bound to a `let` first, the
/// argument is a path, and the call runs too. Each reading opened its own rigid before, and the
/// first spelling was refused "expected ?T -> Int64, got ?T -> Int64" (MEASURED) — the limit
/// WI-20261017-HQH9K lifted.
#[test]
fn a_lambda_at_a_call_whose_argument_is_no_path_is_hinted_at_the_calls_unknown() {
    let decls = r#"
  import anthill.prelude.{Int64, String}
  sort Strm
    sort T = ?
    entity strm(t: T)
  end
  sort Hold2
    entity hold2(s: Strm[T = ?])
  end
  operation pick(h: Hold2, f: (x: h.s.T) -> Int64) -> Int64 = f(h.s.t)
"#;
    let unnamed = format!(
        "namespace wi_p1pvt.lambda_unnamed\n{decls}\n  operation go() -> Int64 = pick(hold2(s: strm(t: \"a\")), lambda (x) -> 42)\nend\n"
    );
    assert_eq!(run_src(&unnamed, "wi_p1pvt.lambda_unnamed.go"), Ok(42));
    let named = format!(
        "namespace wi_p1pvt.lambda_named\n{decls}\n  operation go() -> Int64 =\n    let k = hold2(s: strm(t: \"a\"))\n    pick(k, lambda (x) -> 42)\nend\n"
    );
    assert_eq!(run_src(&named, "wi_p1pvt.lambda_named.go"), Ok(42));
}

/// A BARE NULLARY OPERATION IS A CALL, NOT A PATH: `let y = mk` and `let z = mk` are two calls,
/// so `y.s` and `z.s` are two streams. While `stable_receiver_path` read the bare name as a
/// value, both aliased `mk` and `same(y.s, z.s)` loaded (MEASURED: this ticket's review).
#[test]
fn a_bare_nullary_operation_is_no_path() {
    let src = program(
        "nullary",
        "  operation f() -> Int64 =\n    let y = mk\n    let z = mk\n    same(y.s, z.s)",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["same.b (op-arg): expected Strm[E = y.s.E], got Strm[T = Int64, E = z.s.E]"],
        "two calls' holders read as one",
    );
}

/// A `let` ALIAS IN A NESTED ANNOTATION READS THE PATH IT NAMES: `let t = h` then `Option[T =
/// t.s.T]` is `Option[T = h.s.T]`, the type of `some(t.s.t)`. The alias canonicalization of an
/// annotation reaches only a top-level projection; the field path is named through the aliases
/// itself, and without them this was refused, "expected Option[T = t.s.T], got Option[T =
/// h.s.T]" (MEASURED: this ticket's review).
#[test]
fn a_let_alias_in_a_nested_annotation_reads_the_path() {
    let src = r#"
namespace wi_p1pvt.nested_alias
  import anthill.prelude.{Int64, Option}
  sort Strm
    sort T = ?
    entity strm(t: T)
  end
  sort Hold2
    entity hold2(s: Strm[T = ?])
  end
  operation f(h: Hold2) -> Int64 =
    let t = h
    let v: Option[T = t.s.T] = Option.some(t.s.t)
    42
  operation go() -> Int64 = f(hold2(s: strm(t: "a")))
end
"#;
    assert_eq!(run_src(src, "wi_p1pvt.nested_alias.go"), Ok(42));
}

// ── which slots the path names ───────────────────────────────────────────────────────────────

/// A NAMED VARIABLE THE FIELD WRITES AS A TOP-LEVEL SLOT takes its first slot's projection, so
/// the tie holds and the path names it: over `a: Pr[A = ?x, B = ?x]`, the read `t.a` is a `Pr[A
/// = t.a.A, B = t.a.A]` and a written `t.a.B` is `t.a.A`. `go` passes `f` a value read off the
/// path its argument is: `y: t.a.B` at `f(t, …)` is the caller's `t.a.A`.
#[test]
fn a_named_variable_is_named_by_its_first_slot() {
    let src = r#"
namespace wi_p1pvt.tie
  import anthill.prelude.{Int64}
  sort Pr
    sort A = ?
    sort B = ?
    entity pr(a: A, b: B)
  end
  sort Two
    entity two(a: Pr[A = ?x, B = ?x])
  end
  operation takes(p: Pr, x: p.A) -> Int64 = 41
  operation f(t: Two, y: t.a.B) -> Int64 = takes(t.a, y)
  operation g(t: Two) -> Int64 = takes(t.a, t.a.b)
  operation go() -> Int64 =
    let t = two(a: pr(a: 1, b: 2))
    f(t, t.a.b) + g(t) - 40
end
"#;
    assert_eq!(run_src(src, "wi_p1pvt.tie.go"), Ok(42));
}

/// A SLOT THE RECEIVER'S TYPE FILLS IS THE RECEIVER'S: `b.s` over `b: Box[V = Int64]` and `s:
/// Strm[T = V, E = ?]` reads an `Int64` element; only the field's own `E` is the path's.
/// Control: nothing is opened there, before or after.
#[test]
fn a_receivers_slot_is_the_receivers() {
    let src = r#"
namespace wi_p1pvt.held
  import anthill.prelude.{Int64}
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(t: T)
  end
  sort Box
    sort V = ?
    entity box(s: Strm[T = V, E = ?])
  end
  operation takes_int(x: Int64) -> Int64 = x
  operation f(b: Box[V = Int64]) -> Int64 = takes_int(b.s.t)
  operation g(b: Box[V = Int64], x: b.s.T) -> Int64 = takes_int(x)
  operation go() -> Int64 = f(box(s: strm(t: 40))) + g(box(s: strm(t: 0)), 2)
end
"#;
    assert_eq!(run_src(src, "wi_p1pvt.held.go"), Ok(42));
}

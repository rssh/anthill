//! WI-20261014-6MPN2 — a callback slot naming a label beside its row parameter
//! (`f: (k: Int64) -> Int64 @ {Error[String], EffP}`) binds the row parameter to the rest of
//! what the callback raises, the caller's own row among it.
//!
//! `use[R](h: … @ {R})` calls `run(1, lambda (k: Int64) -> h(5))`: the callback raises `R`,
//! `use`'s own row, rigid there. Its row meets the slot's by unification, which asks the rigid
//! `R` to take `Error[String]` and refuses without binding; the discharge pass that runs after
//! the arguments (`infer_discharged_row_tails`) passed over every callback row with a tail. So
//! `EffP` was left unconstrained — "expected a type for 'EffP', got unconstrained" — where the
//! slot `@ {EffP}` gave `{R}` and the call ran (MEASURED, plain and under the node carrier).
//! The pass now takes a row whose every tail is rigid: the label in the slot takes the
//! callback's labels it names, a rigid row the slot holds takes itself, and `EffP` the rest,
//! `{R}` here. It reads the slot as the call reads it, and the callback as the slot reads it,
//! and binds no residual a slot naming the tail denies.
//!
//! EVERY ROW DRIVES WHAT IT CLAIMS: an admitted program RUNS to its value; a refusal is
//! asserted by the words that say where it stands.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ──────────────────────────────────
//!
//! FIVE PARTS, each backed out in place and RUN over this file's 9 rows and the suites of
//! WI-329, WI-440, WI-441, WI-20260929-0RP29, WI-20261013-450KA and WI-20261013-1TJQH:
//!
//! 1. A CALLBACK ROW WITH A RIGID TAIL (the pass passing over a row with any tail, as it
//!    stood). 6 FAIL: [`the_callers_own_row_beside_a_label_binds_the_row_parameter`],
//!    [`two_of_the_callers_rows_bind_their_union`],
//!    [`a_label_the_slot_does_not_name_joins_the_callers_row`],
//!    [`the_callers_row_the_slot_holds_covers_itself`],
//!    [`a_slot_read_off_a_receiver_takes_no_label_over_the_callbacks_parameter`] (its controls;
//!    each refused "unconstrained"), and
//!    [`a_row_the_caller_does_not_declare_is_refused_at_its_boundary`] (refused at the call,
//!    for `EffP`, and not at `use`'s effects).
//! 2. A RIGID ROW OF THE SLOT COVERS ITSELF (the slot's rigid rows counted as tails). 2 FAIL:
//!    [`the_callers_row_the_slot_holds_covers_itself`] and
//!    [`a_slot_read_off_a_receiver_takes_no_label_over_the_callbacks_parameter`] (its
//!    controls).
//! 3. THE SLOT AS THE CALL READS IT (the written type, `-s.E` unexpanded), and
//! 4. NO RESIDUAL A SLOT'S ABSENCES DENY. Either backed out, 2 rows of
//!    `wi_0rp29_nested_projection_value_in_type_test` FAIL —
//!    `an_absence_over_a_row_variable_denies_the_variable` and
//!    `a_field_callback_is_held_to_a_lacked_row_however_it_is_passed`: `EffP` is bound to the
//!    `R` the slot lacks, and the call is refused for a contradiction in the slot instead of
//!    for the callback's row.
//! 5. THE CALLBACK AS A SLOT READ OFF A RECEIVER READS IT (the pass given the callback as
//!    written there). 1 FAILS:
//!    [`a_slot_read_off_a_receiver_takes_no_label_over_the_callbacks_parameter`].
//!
//! PASS EITHER WAY, BY DESIGN: [`the_row_parameter_said_whole_binds_as_before`] — the control,
//! the slot `@ {EffP}` and the bracket `run[EffP = {R}]` —
//! and [`a_label_over_the_callbacks_own_parameter_is_not_taken`] — the residual never carries a
//! label the slot's row parameter lacks. [`a_row_two_slots_share_takes_both_callbacks_rows`]
//! is WI-20260820-RDNS4's, and fails under its back-out.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// `run` over `slot`, the callback's row, and `effects`, its own; `use[R, Q]` over two
/// callbacks at its own rows, declaring `{declares}`, whose body is `body`; `go()` runs it with
/// `h` answering `n + 40` and `i` answering `n`.
fn program(ns: &str, slot: &str, effects: &str, declares: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Error, Cell, Modify, Function}}
  operation zero() -> Int64 = 0
  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n
  operation run[EffP](p: Int64, f: (k: Int64) -> Int64 @ {{{slot}}}) -> Int64 effects {{{effects}}} = f(p)
  operation use[R, Q](h: (n: Int64) -> Int64 @ {{R}}, i: (n: Int64) -> Int64 @ {{Q}}) -> Int64 effects {{{declares}}} =
{body}
  operation go() -> Int64 effects {{Error[String], Error[Int64]}} =
    use(lambda (n: Int64) -> n + 40, lambda (n: Int64) -> n)
end
"#
    )
}

/// The callback raising `use`'s own `R` — `h(5)`, 45 — as each spelling hands it to `run`.
const RAISES_R: [(&str, &str); 6] = [
    ("lambda", "    run(1, lambda (k: Int64) -> h(5))"),
    ("untyped", "    run(1, lambda k -> h(k + 4))"),
    ("let", "    let g = lambda (k: Int64) -> h(5)\n    run(1, g)"),
    ("parameter", "    run(5, h)"),
    (
        "function",
        "    let g: Function[A = Int64, B = Int64, E = {R}] = lambda (k: Int64) -> h(5)\n    run(1, g)",
    ),
    ("named", "    run(p: 1, f: lambda (k: Int64) -> h(5))"),
];

/// THE TICKET'S PROGRAM, and five spellings of its callback: the slot `@ {Error[String], EffP}`,
/// the callback raising `R` — `EffP` is `{R}` and the call is 45. The `@ {Modify[k], EffP}` slot
/// (a cell the callback is handed) is the ticket's other measured spelling. Refused
/// "unconstrained" before, all twelve. FAILS when backed out.
#[test]
fn the_callers_own_row_beside_a_label_binds_the_row_parameter() {
    for (spelling, body) in RAISES_R {
        let ns = format!("wi6mpn2.label_{spelling}");
        let src = program(
            &ns,
            "Error[String], EffP",
            "Error[String], EffP",
            "Error[String], R",
            body,
        );
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(45), "{spelling}");
    }
    let src = r#"
namespace wi6mpn2.own
  import anthill.prelude.{Int64, Cell, Modify}
  operation run[EffP](p: Cell[V = Int64], f: (k: Cell[V = Int64]) -> Int64 @ {Modify[k], EffP}) -> Int64 effects {Modify[p], EffP} = f(p)
  operation use[R](q: Cell[V = Int64], h: (n: Int64) -> Int64 @ {R}) -> Int64 effects {Modify[q], R} =
    run(q, lambda (k: Cell[V = Int64]) -> h(5))
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    use(c, lambda (n: Int64) -> n + 40)
end
"#;
    assert_eq!(
        run_int64(src, "wi6mpn2.own.go"),
        Ok(45),
        "the slot naming the callback's cell"
    );
}

/// TWO OF THE CALLER'S ROWS: one callback raising `R` and `Q`, and two callbacks at slots
/// naming one `EffP`, each raising one of them — `EffP` is `{R, Q}`. 45 + 3 = 48 and 41 + 2 =
/// 43. FAILS when backed out.
#[test]
fn two_of_the_callers_rows_bind_their_union() {
    let ns = "wi6mpn2.one_callback_two_rows";
    let src = program(
        ns,
        "Error[String], EffP",
        "Error[String], EffP",
        "Error[String], R, Q",
        "    run(1, lambda (k: Int64) -> h(5) + i(3))",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(48));

    let src = r#"
namespace wi6mpn2.two_callbacks
  import anthill.prelude.{Int64, String, Error}
  operation run2[EffP](f: (k: Int64) -> Int64 @ {Error[String], EffP}, g: (k: Int64) -> Int64 @ {Error[String], EffP}) -> Int64 effects {Error[String], EffP} = f(1) + g(2)
  operation use[R, Q](h: (n: Int64) -> Int64 @ {R}, i: (n: Int64) -> Int64 @ {Q}) -> Int64 effects {Error[String], R, Q} =
    run2(lambda (k: Int64) -> h(k), lambda (k: Int64) -> i(k))
  operation go() -> Int64 effects {Error[String]} = use(lambda (n: Int64) -> n + 40, lambda (n: Int64) -> n)
end
"#;
    assert_eq!(run_int64(src, "wi6mpn2.two_callbacks.go"), Ok(43));
}

/// A LABEL THE SLOT DOES NOT NAME, beside the caller's row: the callback raises `Error[Int64]`
/// as well as `R`, and `EffP` is `{Error[Int64], R}`. 45. FAILS when backed out.
#[test]
fn a_label_the_slot_does_not_name_joins_the_callers_row() {
    let ns = "wi6mpn2.other_label";
    let src = program(
        ns,
        "Error[String], EffP",
        "Error[String], EffP",
        "Error[String], Error[Int64], R",
        "    run(1, lambda (k: Int64) -> if zero() < 0 then Error.raise(7) else h(5))",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(45));
}

/// `run[EffP](s: Src, …, f: … @ {s.E, EffP})` over `s: Src[E = {R}]` inside `use[R, Q]`
/// declaring `{declares}`, the callback `lambda (k: Int64) -> {does}`.
fn projected(ns: &str, declares: &str, does: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Error}}
  sort Src
    effects E = ?
    entity src(n: Int64)
  end
  operation zero() -> Int64 = 0
  operation run[EffP](s: Src, p: Int64, f: (k: Int64) -> Int64 @ {{s.E, EffP}}) -> Int64 effects {{s.E, EffP}} = f(p)
  operation use[R, Q](h: (n: Int64) -> Int64 @ {{R}}, i: (n: Int64) -> Int64 @ {{Q}}) -> Int64 effects {{{declares}}} =
    let s: Src[E = {{R}}] = src(n: 0)
    run(s, 1, lambda (k: Int64) -> {does})
  operation go() -> Int64 effects {{Error[String]}} =
    use(lambda (n: Int64) -> n + 40, lambda (n: Int64) -> n)
end
"#
    )
}

/// THE CALLER'S ROW HELD BY THE SLOT, read off a receiver (`@ {s.E, EffP}`, `s.E = {R}`): it
/// covers the callback's `R`, and `EffP` is the rest — `{}` for `h(5)` (45), `{Error[String]}`
/// beside it (45), `{Q}` for `h(5) + i(3)` (48); a `use` not declaring `Q` is refused at its
/// effects. Each was refused "unconstrained" before. FAILS when backed out, and when the slot's
/// rigid rows are not read as covering the callback's (the slot then has two tails). A callback
/// raising `Error[String]` alone, its row closed, is `EffP = {Error[String]}` (45) — it ran
/// before as well, the slot read as written.
#[test]
fn the_callers_row_the_slot_holds_covers_itself() {
    for (case, declares, does, answer) in [
        ("own", "R", "h(5)", 45),
        (
            "label",
            "Error[String], R",
            "if zero() < 0 then Error.raise(\"x\") else h(5)",
            45,
        ),
        ("other", "R, Q", "h(5) + i(3)", 48),
        (
            "closed",
            "Error[String], R",
            "if zero() < 0 then Error.raise(\"x\") else 45",
            45,
        ),
    ] {
        let ns = format!("wi6mpn2.held_{case}");
        assert_eq!(
            run_int64(&projected(&ns, declares, does), &format!("{ns}.go")),
            Ok(answer),
            "{case}"
        );
    }
    assert_refused_naming(
        &load_errors_of(&projected("wi6mpn2.held_undeclared", "R", "h(5) + i(3)")),
        &[
            "type mismatch in use.effects (op-effects)",
            "undeclared effect: ?Q",
        ],
        "a `use` not declaring the row the slot does not hold",
    );
}

/// THE ROW REACHES `use`: bound, `EffP` is charged at the call, and a `use` that does not
/// declare what its callback raises is refused at its own effects — `R`, `Q`, or a cell in
/// scope the callback writes (`Modify[r]`, whose control declares it and runs: 3 + 2 + 40 and
/// the cell, 48). Each was refused at the call, "unconstrained", before. FAILS when backed
/// out.
#[test]
fn a_row_the_caller_does_not_declare_is_refused_at_its_boundary() {
    for (case, declares, body, undeclared) in [
        (
            "r",
            "Error[String]",
            "    run(1, lambda (k: Int64) -> h(5))",
            "undeclared effect: ?R",
        ),
        (
            "q",
            "Error[String], R",
            "    run(1, lambda (k: Int64) -> h(5) + i(3))",
            "undeclared effect: ?Q",
        ),
    ] {
        let ns = format!("wi6mpn2.undeclared_{case}");
        let src = program(
            &ns,
            "Error[String], EffP",
            "Error[String], EffP",
            declares,
            body,
        );
        assert_refused_naming(
            &load_errors_of(&src),
            &["type mismatch in use.effects (op-effects)", undeclared],
            &format!("a `use` refused for its {undeclared}"),
        );
    }
    let cell = |ns: &str, declares: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Error, Cell, Modify}}
  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n
  operation run[EffP](p: Int64, f: (k: Int64) -> Int64 @ {{Error[String], EffP}}) -> Int64 effects {{Error[String], EffP}} = f(p)
  operation use[R](r: Cell[V = Int64], h: (n: Int64) -> Int64 @ {{R}}) -> Int64 effects {{{declares}}} =
    run(1, lambda (k: Int64) -> put(r, 3) + h(2))
  operation go() -> Int64 effects {{Error[String]}} =
    let c: Cell[V = Int64] = Cell.new(1)
    let n = use(c, lambda (n: Int64) -> n + 40)
    n + Cell.get(c)
end
"#
        )
    };
    assert_refused_naming(
        &load_errors_of(&cell("wi6mpn2.undeclared_cell", "Error[String], R")),
        &[
            "type mismatch in use.effects (op-effects)",
            "undeclared effect: Modify[T = r]",
        ],
        "a `use` not declaring the cell its callback writes",
    );
    let ns = "wi6mpn2.declared_cell";
    assert_eq!(
        run_int64(
            &cell(ns, "Error[String], Modify[r], R"),
            &format!("{ns}.go")
        ),
        Ok(48)
    );
}

/// THE CONTROL: the row parameter said whole — the slot `@ {EffP}`, and the bracket
/// `run[EffP = {R}]` at the ticket's slot. 45 each. Passes either way by design.
#[test]
fn the_row_parameter_said_whole_binds_as_before() {
    let ns = "wi6mpn2.whole_slot";
    let src = program(
        ns,
        "EffP",
        "Error[String], EffP",
        "Error[String], R",
        RAISES_R[0].1,
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(45));
    let ns = "wi6mpn2.whole_bracket";
    let body = "    run[EffP = {R}](1, lambda (k: Int64) -> h(5))";
    let src = program(
        ns,
        "Error[String], EffP",
        "Error[String], EffP",
        "Error[String], R",
        body,
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(45));
}

/// A LABEL OVER THE CALLBACK'S OWN PARAMETER IS NOT TAKEN: the callback writes the cell it is
/// handed and raises `R`, at a slot `@ {Error[String], EffP}` that does not say that write.
/// `EffP` lacks the label, so the residual `{Modify[k], R}` is not bound and the call is
/// refused, as it was. Passes either way by design: it holds the pass to the lacks check.
#[test]
fn a_label_over_the_callbacks_own_parameter_is_not_taken() {
    let src = r#"
namespace wi6mpn2.own_binder
  import anthill.prelude.{Int64, String, Error, Cell, Modify}
  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n
  operation run[EffP](p: Cell[V = Int64], f: (k: Cell[V = Int64]) -> Int64 @ {Error[String], EffP}) -> Int64 effects {Error[String], EffP} = f(p)
  operation use[R](q: Cell[V = Int64], h: (n: Int64) -> Int64 @ {R}) -> Int64 effects {Error[String], Modify[q], R} =
    run(q, lambda (k: Cell[V = Int64]) -> put(k, 3) + h(2))
  operation go() -> Int64 effects {Error[String]} =
    let c: Cell[V = Int64] = Cell.new(1)
    use(c, lambda (n: Int64) -> n + 40)
end
"#;
    assert_refused_naming(
        &load_errors_of(src),
        &["wi6mpn2.own_binder.run", "'EffP'"],
        "a callback writing its own parameter at a slot that does not say it",
    );
}

/// `run[EffP](s: Src, p, f: (k: Cell) -> Int64 @ {{{slot}}})` over `s: Src[E = {R}]` inside
/// `use[R]` declaring `{declares}`, the callback `lambda ({binder}: Cell[V = Int64]) -> {does}`;
/// `go` answers `n * 100 + c * 10 + d` over cells holding 1 and 2.
fn projected_cell(ns: &str, slot: &str, declares: &str, binder: &str, does: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Error, Cell, Modify}}
  sort Src
    effects E = ?
    entity src(n: Int64)
  end
  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n
  operation run[EffP](s: Src, p: Cell[V = Int64], f: (k: Cell[V = Int64]) -> Int64 @ {{{slot}}}) -> Int64 effects {{Modify[p], s.E, EffP}} = f(p)
  operation use[R](q: Cell[V = Int64], r: Cell[V = Int64], h: (n: Int64) -> Int64 @ {{R}}) -> Int64 effects {{{declares}}} =
    let s: Src[E = {{R}}] = src(n: 0)
    run(s, q, lambda ({binder}: Cell[V = Int64]) -> {does})
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    let d: Cell[V = Int64] = Cell.new(2)
    let n = use(c, d, lambda (n: Int64) -> n + 40)
    n * 100 + Cell.get(c) * 10 + Cell.get(d)
end
"#
    )
}

/// A SLOT READ OFF A RECEIVER IS MET BY THE CALLBACK IN ITS NAMES: `@ {s.E, EffP}` is typed
/// after the arguments, and the callback the pass read there was the one as written — its own
/// parameter `c`, not the slot's `k`, which `EffP` is made to lack. A callback writing the cell
/// it is handed took `EffP := {Modify[c], …}`, and was refused at `use`'s effects for
/// "undeclared effect: Modify[T = c]", a binder out of scope (MEASURED, its row closed before
/// this change as well). Refused at the call now, written `c` or `k`, alone or beside `R`.
/// FAILS when the pass reads the callback as written for such a slot.
///
/// ITS CONTROLS run: the slot saying that write, `@ {Modify[k], s.E, EffP}` (5 + 41 and `c`
/// written, 4652), and a cell in scope, `put(r, 5)` (`d` written, 4615).
#[test]
fn a_slot_read_off_a_receiver_takes_no_label_over_the_callbacks_parameter() {
    for (case, binder, does) in [
        ("closed", "c", "put(c, 5)"),
        ("beside_r", "c", "put(c, 5) + h(1)"),
        ("same_name", "k", "put(k, 5) + h(1)"),
    ] {
        let ns = format!("wi6mpn2.received_{case}");
        let src = projected_cell(&ns, "s.E, EffP", "Modify[q], R", binder, does);
        assert_refused_naming(
            &load_errors_of(&src),
            &[&format!("{ns}.run"), "'EffP'"],
            &format!("a callback writing its own parameter ({case})"),
        );
    }
    let ns = "wi6mpn2.received_says";
    let src = projected_cell(
        ns,
        "Modify[k], s.E, EffP",
        "Modify[q], R",
        "c",
        "put(c, 5) + h(1)",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(4652));
    let ns = "wi6mpn2.received_scope";
    let src = projected_cell(
        ns,
        "s.E, EffP",
        "Modify[q], Modify[r], R",
        "c",
        "put(r, 5) + h(1)",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(4615));
}

/// A ROW PARAMETER TWO SLOTS SHARE TAKES WHAT EACH CALLBACK RAISES BEYOND ITS SLOT'S LABELS: `f`
/// at `@ {Error[String], EffP}` raises `R`, `g` at `@ {EffP}` raises `Q`, and `EffP` is `{R, Q}`
/// — 41 + 2. `g` used to bind `EffP := {Q}` as the arguments were unified, and the pass after
/// them left a bound tail alone, so `f` was refused at its slot (WI-20260820-RDNS4). FAILS with
/// that ticket's argument loops relating the rows again.
#[test]
fn a_row_two_slots_share_takes_both_callbacks_rows() {
    let src = r#"
namespace wi6mpn2.bound_first
  import anthill.prelude.{Int64, String, Error}
  operation run2[EffP](f: (k: Int64) -> Int64 @ {Error[String], EffP}, g: (k: Int64) -> Int64 @ {EffP}) -> Int64 effects {Error[String], EffP} = f(1) + g(2)
  operation use[R, Q](h: (n: Int64) -> Int64 @ {R}, i: (n: Int64) -> Int64 @ {Q}) -> Int64 effects {Error[String], R, Q} =
    run2(lambda (k: Int64) -> h(k), lambda (k: Int64) -> i(k))
  operation go() -> Int64 effects {Error[String]} = use(lambda (n: Int64) -> n + 40, lambda (n: Int64) -> n)
end
"#;
    assert_eq!(run_int64(src, "wi6mpn2.bound_first.go"), Ok(43));
}

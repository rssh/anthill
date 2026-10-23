//! WI-20261014-EDPF6 — a function type records its own parameters, so a callback is read at
//! its slot by what its TYPE says, whatever expression the value came through.
//!
//! `run(p, f: (k: Cell[V = Int64]) -> Int64 @ {Modify[k]}) effects {Modify[p]} = f(p)` takes a
//! callback that writes the cell it is handed. `let g = lambda (k: …) -> put(k, 5)` then
//! `run(q, g)` ran; `let t = (lambda (k: …) -> put(k, 5), 1)` then `run(q, t._1)` — the same
//! lambda, the same arrow — was refused "`k` is a parameter of the callback itself, at a
//! position this expression does not say" (MEASURED). The positions of a callback's own
//! parameters were read off the argument's EXPRESSION — an operation, a lambda, a callback
//! parameter, a `let` holding one — and an arrow type held none.
//!
//! Now the arrow records them (`TypeNode::Arrow::binders`, the stdlib's `Arrow.binders`): a
//! lambda's binders and an operation's parameters. A row label naming one is read at its
//! position wherever the value goes — a tuple's component, a pattern's binder, a list's
//! element; a callback parameter's place says its position itself. A label naming a binder out
//! of scope that the type does not record — an enclosing lambda's, named by a lambda it
//! returned — is still refused where the declared row speaks of one of its binders.
//!
//! EVERY ROW DRIVES WHAT IT CLAIMS: an admitted program RUNS, and its value says which cell was
//! written; a refusal is asserted by the words that name it, beside the program that differs
//! in one thing and runs.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! EACH PART backed out in place and RUN over this file's rows and the suites beside it
//! (`wi_1tjqh`, the four `wi_0rp29_*` files, `wi440`, `wi441`, `wi469`, `wi698`, `wi_41yye`,
//! `wi_450ka`, `wi_xzmgc`, `wi347`, `wi_f3fyj`: 614 rows). Measured on a tree that also gave
//! a lambda of several binders the parameter list `(_1: A, _2: B)`, a part since taken out (it
//! is WI-20260904-34J8Z's); the gate and the families were run again without it.
//!
//! 1. A LAMBDA'S ARROW RECORDS ITS BINDERS (the `LambdaBody` frame, `lambda_binder_slots`) —
//!    records none. 20 FAIL: seven rows here — every one but the operation's — and 13 beside: five of `wi_0rp29_nested_projection_value_in_type_test`
//!    (the `let`- and pattern-bound lambdas with their twins, and the control of a `let` over
//!    a callback parameter), review 9's three, four of `wi_1tjqh`, and
//!    `wi698_row_param_refinement_test::lambda_modify_aligned_to_present_place_loads`.
//! 2. AN OPERATION'S ARROW RECORDS ITS PARAMETERS (`operation_as_function_value`) — records
//!    none. 9 FAIL: [`an_operation_with_type_parameters_taken_as_a_value_keeps_its_parameters`]
//!    and 8 beside (`wi440` 1, `wi441` 3, `wi_0rp29` 1, `wi_1tjqh` 2, `wi_41yye` 1).
//! 3. A TYPE THAT RECORDS NO PARAMETERS SAYS NONE (`arrow_own_binders`) — says an empty list,
//!    as a function of no parameters. 14 FAIL:
//!    [`a_callback_writing_its_own_parameter_is_refused_where_the_slot_denies_it`] at the
//!    callback parameter, whose written arrow records none and loads clean under
//!    `-Modify[x]`, and 13 beside.
//! 4. A BINDER OUT OF ITS SCOPE IS REFUSED (`unplaced_binder`) — not refused. 2 FAIL:
//!    [`a_returned_lambda_is_read_by_the_parameters_its_own_type_records`] and
//!    `wi_0rp29_nested_projection_value_in_type_test::
//!    a_binder_out_of_its_scope_is_refused_where_the_row_speaks_of_one`.
//! 5. THE BINDERS RIDE THE σ WALK (`rewrite_type_occ_deep`) — dropped. 1 FAILS:
//!    [`a_lambda_whose_binder_the_call_types_keeps_its_parameters`].
//! 6. … AND THE GENERIC MAP, which instantiates a ∀ (`map_type_node`) — dropped. 1 FAILS:
//!    [`an_operation_with_type_parameters_taken_as_a_value_keeps_its_parameters`].
//!
//! NOT DRIVEN: the binders' re-key with the labels that name them (`substitute_ref_syms_occ`),
//! their term lowering (`type_node_to_term`), and the rebuilds through the extractor
//! (`arrow_value`, `entity_type_on_builders`, `rigidify_unwritten_sort_params`, projection
//! elimination, `open_slots_said_by`). Each backed out alone, none of the 614 rows fails, nor
//! the probe programs written to reach them: those rewrites meet written arrows, which record
//! none. Kept: a rewrite that dropped them would lose a parameter's position, and the program
//! would then be refused for a position nobody says.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// `put`, `run`, and a `go` that hands `use` a fresh cell holding 1 and reads it back:
/// `use(c) * 10 + Cell.get(c)`.
fn program(ns: &str, above: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Unit, String, List, Cell, Modify, Error, Bool}}
  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n
  operation run(p: Cell[V = Int64], f: (k: Cell[V = Int64]) -> Int64 @ {{Modify[k]}}) -> Int64 effects {{Modify[p]}} = f(p)
{above}
  operation use(q: Cell[V = Int64]) -> Int64 effects {{Modify[q]}} =
{body}
  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    let n = use(c)
    n * 10 + Cell.get(c)
end
"#
    )
}

const LAMBDA: &str = "lambda (k: Cell[V = Int64]) -> put(k, 5)";

/// The spellings of one callback that writes the cell it is handed, each passed to `run`.
fn spellings() -> Vec<(&'static str, &'static str, String)> {
    vec![
        ("let", "", format!("    let g = {LAMBDA}\n    run(q, g)")),
        ("tuple", "", format!("    let t = ({LAMBDA}, 1)\n    run(q, t._1)")),
        ("named-tuple", "", format!("    let t = (f: {LAMBDA}, n: 1)\n    run(q, t.f)")),
        ("pattern", "", format!("    let (g, n) = ({LAMBDA}, 1)\n    run(q, g)")),
        (
            "list",
            "",
            format!("    match [{LAMBDA}]\n      case cons(g, _) -> run(q, g)\n      case nil() -> 0"),
        ),
        (
            "parameter",
            "  operation via(q: Cell[V = Int64], g: (y: Cell[V = Int64]) -> Int64 @ {Modify[y]}) -> Int64 effects {Modify[q]} =\n    let t = (g, 1)\n    run(q, t._1)",
            format!("    via(q, {LAMBDA})"),
        ),
    ]
}

/// A CALLBACK THAT WRITES THE CELL ITS SLOT HANDS IT RUNS HOWEVER IT REACHED THE SLOT: `run`
/// writes 5 into `use`'s cell, 5 * 10 + 5. The tuple, the named tuple, the pattern and the list
/// were refused for a position nobody said, and so was a callback parameter put into a tuple
/// (MEASURED); the `let` ran.
#[test]
fn a_callback_writing_its_own_parameter_runs_however_it_reached_the_slot() {
    for (spelling, above, body) in spellings() {
        let ns = format!("wi_edpf6.runs_{}", spelling.replace('-', "_"));
        let src = program(&ns, above, &body);
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(55), "{spelling}");
    }
}

/// … AND IS REFUSED WHERE THE SLOT DENIES THE WRITE, by the absence it violates, as the lambda
/// written at the call is: `appD[EffP](q, f: (x: …) -> Int64 @ {EffP, -Modify[x]})`. And at a
/// slot that says nothing of a write, `@ {}`, by the closed row. The twins are the rows above.
#[test]
fn a_callback_writing_its_own_parameter_is_refused_where_the_slot_denies_it() {
    let denies = "  operation appD[EffP](q: Cell[V = Int64], f: (x: Cell[V = Int64]) -> Int64 @ {EffP, -Modify[x]}) -> Int64 effects {EffP} = f(q)\n  operation pure1(q: Cell[V = Int64], f: (x: Cell[V = Int64]) -> Int64) -> Int64 = f(q)";
    for (spelling, above, body) in spellings() {
        for (slot, names) in [
            (
                "appD[EffP = {}]",
                &["appD.f (op-arg)", "to lack `Modify[T = f.x]` (its `-…` lacks-constraint)"][..],
            ),
            ("pure1", &["pure1.f (op-arg)", "which the closed row does not admit"][..]),
        ] {
            let at = |text: &str| text.replace("run(q,", &format!("{slot}(q,"));
            let (above, body) = (format!("{}\n{denies}", at(above)), at(&body));
            let ns = format!("wi_edpf6.denied_{}", spelling.replace('-', "_"));
            let src = program(&ns, &above, &body);
            assert_refused_naming(&load_errors_of(&src), names, &format!("{spelling} at {slot}"));
        }
    }
}

/// … AND THE WRITE IS THE CALLER'S TO DECLARE: `use` declaring nothing is refused for the
/// undeclared `Modify[q]` it made through `run`, in every spelling.
#[test]
fn the_write_through_the_slot_is_charged_to_the_cell_handed_on() {
    for (spelling, above, body) in spellings() {
        let ns = format!("wi_edpf6.undeclared_{}", spelling.replace('-', "_"));
        let src = program(&ns, above, &body).replace(
            "operation use(q: Cell[V = Int64]) -> Int64 effects {Modify[q]} =",
            "operation use(q: Cell[V = Int64]) -> Int64 =",
        );
        assert_refused_naming(
            &load_errors_of(&src),
            &["use.effects (op-effects)", "undeclared effect: Modify[T = q]"],
            spelling,
        );
    }
}

/// A LAMBDA OF TWO PARAMETERS OUT OF A TUPLE is read at its parameters' positions too:
/// `slot2(p, f: (x: Cell, m: Int64) -> Int64 @ {Modify[x]}) = f(p, 3)` writes 9 into the cell,
/// 9 * 10 + 9.
#[test]
fn a_lambda_of_two_parameters_out_of_a_tuple_is_read_at_their_positions() {
    let ns = "wi_edpf6.two";
    let src = program(
        ns,
        "  operation slot2(p: Cell[V = Int64], f: (x: Cell[V = Int64], m: Int64) -> Int64 @ {Modify[x]}) -> Int64 effects {Modify[p]} = f(p, 3)",
        "    let t = (lambda (a: Cell[V = Int64], b: Int64) -> put(a, b * 3), 1)\n    slot2(q, t._1)",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(99));
}

/// A RETURNED LAMBDA IS READ BY THE PARAMETERS ITS OWN TYPE RECORDS. `mk(d)` is the lambda `mk`
/// returns. Writing its own parameter `j` it runs, the write landing on the cell `run` hands it
/// (5 * 10 + 5). Writing `k` — `mk`'s binder, the cell `d` the application was given — it is
/// refused: `k` is no parameter of the returned lambda, and reading it at position 0 would
/// charge the write to `q` and leave `d`'s undeclared.
#[test]
fn a_returned_lambda_is_read_by_the_parameters_its_own_type_records() {
    let above = "  operation inner(q: Cell[V = Int64], d: Cell[V = Int64]) -> Int64 effects {Modify[q]} =";
    let make = |writes: &str| {
        format!(
            "{above}\n    let mk = lambda (k: Cell[V = Int64]) -> lambda (j: Cell[V = Int64]) -> put({writes}, 5)\n    run(q, mk(d))"
        )
    };
    let body = "    let d: Cell[V = Int64] = Cell.new(1)\n    inner(q, d)";
    let ns = "wi_edpf6.returned_own";
    assert_eq!(run_int64(&program(ns, &make("j"), body), &format!("{ns}.go")), Ok(55));
    let src = program("wi_edpf6.returned_enclosing", &make("k"), body);
    assert_refused_naming(
        &load_errors_of(&src),
        &[
            "run.f (op-arg)",
            "`k` is a binder out of scope here, which the callback's type does not record as a \
             parameter of its own",
        ],
        "a returned lambda writing its enclosing lambda's binder",
    );
}

/// A LAMBDA'S BINDERS ARE ITS PARAMETERS EVEN WHERE ITS ROW NAMES NONE OF THEM: `lambda (k) ->
/// g(d)` writes `g.y`, a callback parameter's place, and that is no write to the cell `app`
/// hands the lambda. Refused at `app`'s slot, which admits only that write; the lambda writing
/// its own `k` runs (1 * 10 + 5, `d` untouched).
#[test]
fn a_lambdas_binders_are_its_parameters_where_its_row_names_none() {
    let above = "  operation app(q: Cell[V = Int64], f: (x: Cell[V = Int64]) -> Int64 @ {Modify[x]}) -> Int64 effects {Modify[q]} = f(q)\n  operation hand(q: Cell[V = Int64], d: Cell[V = Int64], g: (y: Cell[V = Int64]) -> Int64 @ {Modify[y]}) -> Int64 effects {Modify[q]} =";
    let make = |call: &str| {
        format!("{above}\n    let t = (lambda (k: Cell[V = Int64]) -> {call}, 1)\n    app(q, t._1)")
    };
    let body = format!("    let d: Cell[V = Int64] = Cell.new(1)\n    hand(q, d, {LAMBDA}) + Cell.get(d) - 1");
    let ns = "wi_edpf6.own_row_names_none_ok";
    assert_eq!(run_int64(&program(ns, &make("put(k, 5)"), &body), &format!("{ns}.go")), Ok(55));
    let src = program("wi_edpf6.own_row_names_none", &make("g(d)"), &body);
    assert_refused_naming(
        &load_errors_of(&src),
        &["app.f (op-arg)", "declares `Modify[T = g.y]`"],
        "a lambda handing its callback another cell, out of a tuple",
    );
}

/// A LAMBDA WHOSE BINDER THE CALL TYPES keeps its parameters through the substitution that
/// types it: `(lambda (k: Cell[V = Int64], n) -> put(k, 6), 1)._1` leaves `n` open, the call
/// to `run2` solves it, and the arrow read at the slot is the solved one — 6 * 10 + 6.
#[test]
fn a_lambda_whose_binder_the_call_types_keeps_its_parameters() {
    let ns = "wi_edpf6.solved";
    let src = program(
        ns,
        "  operation run2(p: Cell[V = Int64], f: (k: Cell[V = Int64], n: Int64) -> Int64 @ {Modify[k]}) -> Int64 effects {Modify[p]} = f(p, 3)",
        "    let t = (lambda (k: Cell[V = Int64], n) -> put(k, 6), 1)\n    run2(q, t._1)",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(66));
}

/// AN OPERATION WITH TYPE PARAMETERS TAKEN AS A VALUE keeps its parameters through the
/// instantiation of its ∀: `putAny[T](c, x: T)` writes `c`, its first parameter, so at a slot
/// writing its own first parameter it runs (5 * 10 + 5), and at one denying that write it is
/// refused by the absence it violates.
#[test]
fn an_operation_with_type_parameters_taken_as_a_value_keeps_its_parameters() {
    let above = "  operation run2(p: Cell[V = Int64], f: (k: Cell[V = Int64], n: Int64) -> Int64 @ {Modify[k]}) -> Int64 effects {Modify[p]} = f(p, 3)\n  operation runD[EffP](p: Cell[V = Int64], f: (k: Cell[V = Int64], n: Int64) -> Int64 @ {EffP, -Modify[k]}) -> Int64 effects {EffP} = f(p, 3)\n  operation putAny[T](c: Cell[V = Int64], x: T) -> Int64 effects Modify[c] = put(c, 5)";
    let ns = "wi_edpf6.poly";
    let src = program(ns, above, "    run2(q, putAny)");
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(55));
    let src = program("wi_edpf6.poly_denied", above, "    runD[EffP = {}](q, putAny)");
    assert_refused_naming(
        &load_errors_of(&src),
        &["runD.f (op-arg)", "to lack `Modify[T = f.k]` (its `-…` lacks-constraint)"],
        "an operation with type parameters writing the parameter the slot denies",
    );
}

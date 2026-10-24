//! WI-20261013-1TJQH — a callee's row parameter is inferred from a callback's row by what the
//! row's labels NAME, not by what the callback's type rides.
//!
//! `run[EffP](p, f: (k: Cell[V = Int64]) -> Int64 @ {EffP}) effects {EffP} = f(p)`, called from
//! `use(q, r)` with a callback writing `r` — `lambda (k) -> put(r, 5)`, row `{Modify[r]}`. `r` is
//! a value in scope at the call, so `EffP` is `{Modify[r]}` and the call runs.
//!
//! IT WAS REFUSED, "expected a type for 'EffP', got unconstrained", for the lambda written at the
//! call, and ran for the same lambda under a written arrow type — refused again once an alias
//! stood in that annotation, or under `ANTHILL_TEST_NODE_CARRIER=1` (MEASURED). The reader:
//! `bind_row_tail` declined a label holding a value on every carrier but the term one. What that
//! refusal held up is about the callback's OWN parameter, and is said now by what a label
//! names:
//!
//!  * a row variable takes no label over a binder out of scope where the variable is read — it
//!    is the called operation's, standing outside the callback's arrow, where the binder names
//!    nothing. A callback parameter's place is such a binder wherever it is read
//!    (`bind_row_tail`); any other is one where a call knows what is in scope
//!    (`callback_at_slot`);
//!  * the callback's row is read in the slot's binder names, so a slot that names the binder
//!    (`@ {Modify[k], EffP}`) takes the write itself and `EffP` the rest.
//!
//! EVERY ROW DRIVES WHAT IT CLAIMS: an admitted program RUNS, and its value says which cell was
//! written (`n * 100 + c * 10 + d`, the cells starting at 1 and 2); a refusal is asserted by the
//! words that name it, and the program beside it that differs in one thing runs.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! SEVEN PARTS, each backed out in place and RUN over this file's 12 rows and the four suites
//! beside it (`wi440`, `wi441`, `wi_450ka`, `wi_41yye`: 47 rows):
//!
//! 1. A LABEL HOLDING A VALUE IS BOUND WHATEVER IT RIDES (`bind_row_tail`'s refusal of one off
//!    the term carrier restored). 8 FAIL — each admitted program is refused, a row parameter
//!    unconstrained or left open:
//!    [`a_callback_writing_a_cell_in_scope_gives_the_row_parameter_its_row`],
//!    [`a_local_and_a_pattern_bound_cell_are_values_in_scope`],
//!    [`a_slot_naming_the_callbacks_parameter_takes_the_write_and_the_row_parameter_the_rest`]
//!    (the callback writing `r` as well),
//!    [`a_dispatched_call_reads_the_callback_at_its_slot_too`],
//!    [`a_constructor_reads_the_callback_at_its_fields_slot`],
//!    [`a_function_value_reads_the_callback_at_its_slot`],
//!    [`a_callback_writing_the_cell_the_slot_denies_is_refused_however_written`] (its control,
//!    the other cell), and `wi_41yye_enclosing_place_type_test::let_local_cell_is_checked`.
//! 2. A LABEL OVER A CALLBACK PARAMETER'S PLACE IS BOUND INTO NO ROW VARIABLE (`bind_row_tail`
//!    not asking). 2 FAIL:
//!    [`a_member_whose_slot_is_its_row_parameter_alone_does_not_fit_a_slot_naming_the_binder`]
//!    loads clean, and
//!    [`the_override_a_call_dispatches_to_reads_the_callback_at_its_own_slot`] is charged the
//!    binder.
//! 3. THE SLOT'S ROW VARIABLE LACKS A LABEL OVER A BINDER OUT OF SCOPE AT THE CALL
//!    (`callback_at_slot` registering none). 2 FAIL, each where the slot names no parameter to
//!    rename to: [`a_constructor_reads_the_callback_at_its_fields_slot`] and
//!    [`a_function_value_reads_the_callback_at_its_slot`] are refused for an undeclared
//!    `Modify[k]` instead, the binder leaked into the caller's row. (Re-measured by
//!    WI-20261014-EDPF6, on the tree its test file's ledger describes: a lambda taken out of a
//!    tuple is renamed by part 4 now, its arrow
//!    recording its parameters, and the renamed label is a callback parameter's place, which
//!    part 2 refuses on its own.)
//! 4. THE CALLBACK'S ROW IN THE SLOT'S BINDER NAMES (`callback_at_slot` renaming nothing, the
//!    callback's own parameters lacked as they stand). 2 FAIL, "unconstrained":
//!    [`a_slot_naming_the_callbacks_parameter_takes_the_write_and_the_row_parameter_the_rest`]
//!    and [`a_dispatched_call_reads_the_callback_at_its_slot_too`].
//! 5. THE OVERRIDE A CALL DISPATCHES TO READS THE CALLBACK AT ITS OWN SLOT (`override_at_call`
//!    unifying the argument as passed). 1 FAILS:
//!    [`the_override_a_call_dispatches_to_reads_the_callback_at_its_own_slot`].
//! 6. A CONSTRUCTOR READS IT AT ITS FIELD'S SLOT (`check_constructor_iter` unifying the
//!    argument as passed). 1 FAILS: [`a_constructor_reads_the_callback_at_its_fields_slot`].
//! 7. A FUNCTION VALUE READS IT AT ITS SLOT (the application of an arrow value unifying the
//!    argument as passed). 1 FAILS: [`a_function_value_reads_the_callback_at_its_slot`].
//!
//! NOT DRIVEN: the same reading in the override fallback's own argument loop
//! (`concrete_override_threaded`). Backed out alone, none of these 47 rows fails, nor any of
//! 877 rows of the dispatch suites, nor any of 42 programs written to reach it — it runs on
//! the substitution `override_at_call` has just left, where part 5 has already read the same
//! arguments. Its site says so.
//!
//! PARTS 2, 3 AND 4 TOGETHER ARE THE OLD REFUSAL MERELY REMOVED: 12 rows fail, eight of this
//! file and four held before this ticket —
//! `wi440_callback_lacks_test::modifying_callback_rejected_against_open_lacks`, and
//! `wi441_iterable_arrow_pred_test`'s `modifying_pred_rejected_by_find`,
//! `modifying_pred_rejected_by_filter_and_map` and
//! `find_over_cell_list_rejects_mutating_pred_accepts_reader`. Those four fail with parts 3
//! and 4 both out and hold with either in: with the row renamed the tail's lacks check reads
//! the slot's own `-Modify[x]`, and with the binder lacked the tail takes nothing over it.
//! With parts 2 and 3 both out
//! [`a_callbacks_own_parameter_is_no_label_a_row_parameter_takes`] fails at the lambda
//! written at the call, which loads clean.
//!
//! PASSES EITHER WAY, BY DESIGN: [`the_bracket_says_the_row_in_every_spelling`] — the repair the
//! refusal advised, which ran before.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// What a row varies of the program: declarations above `run`, `run` itself, a parameter `use`
/// takes beside its two cells and what `go` passes for it, the row `use` declares, and its body.
struct Shape<'a> {
    above: &'a str,
    run: &'a str,
    parameter: &'a str,
    passes: &'a str,
    declares: &'a str,
    body: &'a str,
}

/// `run`, its callback's row its own parameter.
const RUN: &str = "  operation run[EffP](p: Cell[V = Int64], f: (k: Cell[V = Int64]) -> Int64 @ {EffP}) -> Int64 effects {EffP} = f(p)";
/// `run`, its callback's row naming the callback's parameter beside its own.
const RUN_OWN: &str = "  operation run[EffP](p: Cell[V = Int64], f: (k: Cell[V = Int64]) -> Int64 @ {Modify[k], EffP}) -> Int64 effects {Modify[p], EffP} = f(p)";
/// `run`, its callback's row its own parameter and no write to the cell `run` is handed.
const RUN_DENIES: &str = "  operation run[EffP](p: Cell[V = Int64], f: (k: Cell[V = Int64]) -> Int64 @ {EffP, -Modify[p]}) -> Int64 effects {EffP} = f(p)";
/// Everything `use` can incur, so that what is judged is the slot.
const EVERYTHING: &str = "{Modify[q], Modify[r], Error[String]}";

impl Default for Shape<'_> {
    fn default() -> Self {
        Shape {
            above: "",
            run: RUN,
            parameter: "",
            passes: "",
            declares: EVERYTHING,
            body: "",
        }
    }
}

/// `use(q, r)` over two cells, its body `shape.body`; `go()` runs it over cells holding 1 and 2
/// and answers `n * 100 + c * 10 + d`.
fn program(ns: &str, shape: &Shape<'_>) -> String {
    let Shape {
        above,
        run,
        parameter,
        passes,
        declares,
        body,
    } = shape;
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Unit, String, List, Cell, Modify, Error, Function}}
  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n
  sort Box
    effects EB = ?
    entity box(g: (k: Cell[V = Int64]) -> Int64 @ {{EB}})
  end
  sort IC = Cell[V = Int64]
  sort MyInt = Int64
{above}
{run}
  operation use(q: Cell[V = Int64], r: Cell[V = Int64]{parameter}) -> Int64 effects {declares} =
{body}
  operation go() -> Int64 effects {{Error[String]}} =
    let c: Cell[V = Int64] = Cell.new(1)
    let d: Cell[V = Int64] = Cell.new(2)
    let n = use(c, d{passes})
    n * 100 + Cell.get(c) * 10 + Cell.get(d)
end
"#
    )
}

/// `lambda (k) -> {does}` handed to `{call}` (which writes `{cb}` where the callback goes) by
/// the spellings whose own parameters the expression says: written at the call, held in a
/// `let`, an operation, and a parameter of `use` typed `@ {row}` — the lambda behind that one
/// written in `go`, where `use`'s `q` and `r` are the cells `c` and `d`.
fn placed(does: &str, row: &str, call: &str) -> Vec<(&'static str, Shape<'static>)> {
    let leak = |s: String| -> &'static str { Box::leak(s.into_boxed_str()) };
    let lambda = format!("lambda (k: Cell[V = Int64]) -> {does}");
    let in_go = lambda.replace("(q,", "(c,").replace("(r,", "(d,");
    vec![
        (
            "lambda",
            Shape {
                body: leak(format!("    {}", call.replace("{cb}", &lambda))),
                ..Shape::default()
            },
        ),
        (
            "let",
            Shape {
                body: leak(format!("    let g = {lambda}\n    {}", call.replace("{cb}", "g"))),
                ..Shape::default()
            },
        ),
        (
            "parameter",
            Shape {
                parameter: leak(format!(", g: (k: Cell[V = Int64]) -> Int64 @ {row}")),
                passes: leak(format!(", {in_go}")),
                body: leak(format!("    {}", call.replace("{cb}", "g"))),
                ..Shape::default()
            },
        ),
    ]
}

/// THE TICKET'S MEASUREMENTS (1) TO (6): the callback writes `r`, a cell in scope at the call,
/// and `EffP` is its row — 5 answered, the second cell written: 515. Written at the call, held
/// in a `let`, taken out of a tuple, a parameter of `use` typed by an arrow and by a `Function`,
/// under a written arrow type and a written `Function`, those with an alias in them, and a
/// field. The first three, the two parameters and the two aliases were refused "expected a type
/// for 'EffP', got unconstrained"; the two annotations with no alias and the field ran
/// (MEASURED). FAILS under part 1.
#[test]
fn a_callback_writing_a_cell_in_scope_gives_the_row_parameter_its_row() {
    let lambda = "lambda (k: Cell[V = Int64]) -> put(r, 5)";
    let held = |annotation: &str| format!("    let g{annotation} = {lambda}\n    run(q, g)");
    let in_go = ", lambda (k: Cell[V = Int64]) -> put(d, 5)";
    let bodies: Vec<(&str, &str, &str, String)> = vec![
        ("lambda", "", "", format!("    run(q, {lambda})")),
        ("let", "", "", held("")),
        ("tuple", "", "", format!("    let t = ({lambda}, 1)\n    run(q, t._1)")),
        (
            "function",
            "",
            "",
            held(": Function[A = Cell[V = Int64], B = Int64, E = {Modify[r]}]"),
        ),
        ("arrow", "", "", held(": (k: Cell[V = Int64]) -> Int64 @ {Modify[r]}")),
        (
            "alias_in_a",
            "",
            "",
            held(": Function[A = IC, B = Int64, E = {Modify[r]}]"),
        ),
        (
            "alias_in_b",
            "",
            "",
            held(": Function[A = Cell[V = Int64], B = MyInt, E = {Modify[r]}]"),
        ),
        (
            "field",
            "",
            "",
            format!("    let b: Box[EB = {{Modify[r]}}] = box(g: {lambda})\n    run(q, b.g)"),
        ),
        (
            "function_parameter",
            ", g: Function[A = Cell[V = Int64], B = Int64, E = {Modify[r]}]",
            in_go,
            "    run(q, g)".to_string(),
        ),
        (
            "arrow_parameter",
            ", g: (k: Cell[V = Int64]) -> Int64 @ {Modify[r]}",
            in_go,
            "    run(q, g)".to_string(),
        ),
    ];
    for (spelling, parameter, passes, body) in &bodies {
        let ns = format!("wi1tjqh.scope_{spelling}");
        let src = program(
            &ns,
            &Shape {
                parameter,
                passes,
                body,
                ..Shape::default()
            },
        );
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(515), "{spelling}");
    }
}

/// … AND A CELL BOUND IN `use`'S BODY IS A VALUE IN SCOPE AS ITS PARAMETER IS: one a `let`
/// holds — written 5 and read back, 10 answered, neither of `go`'s cells written: 1012 — and
/// one a pattern binds to `r`: 515. Both were refused as above (MEASURED). FAILS under part 1.
#[test]
fn a_local_and_a_pattern_bound_cell_are_values_in_scope() {
    for (tag, body, answer) in [
        (
            "let",
            "    let x: Cell[V = Int64] = Cell.new(7)\n    run(q, lambda (k: Cell[V = Int64]) -> put(x, 5)) + Cell.get(x)",
            1012,
        ),
        (
            "pattern",
            "    match (r, 1)\n      case (x, _) -> run(q, lambda (k: Cell[V = Int64]) -> put(x, 5))",
            515,
        ),
    ] {
        let ns = format!("wi1tjqh.local_{tag}");
        let src = program(&ns, &Shape { body, ..Shape::default() });
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(answer), "{tag}");
    }
}

/// THE REPAIR THE REFUSAL ADVISED, `run[EffP = {Modify[r]}](q, …)`, in every spelling: 515.
/// Passes either way by design.
#[test]
fn the_bracket_says_the_row_in_every_spelling() {
    for (spelling, shape) in placed("put(r, 5)", "{Modify[r]}", "run[EffP = {Modify[r]}](q, {cb})") {
        let ns = format!("wi1tjqh.bracket_{spelling}");
        let src = program(&ns, &shape);
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(515), "{spelling}");
    }
}

/// A CALLBACK WRITING ITS OWN PARAMETER, AT A SLOT WHOSE ROW IS THE ROW PARAMETER ALONE: `k`
/// names nothing where `EffP` is read, so `EffP` does not take the write and the call is
/// refused — in every spelling, an operation and a lambda out of a tuple among them.
///
/// The callback parameter is the one that matters: `use` here declares NO effect, and with the
/// label bound it loaded, the call charged `Modify[g.k]`, which `use`'s boundary drops — `go`
/// answered 552, the first cell written by an operation typed pure (MEASURED). FAILS with parts
/// 2 and 3 both out — a clean load. Under part 3 alone it holds since WI-20261014-EDPF6: the
/// tuple's label is renamed by part 4 to a place part 2 refuses.
#[test]
fn a_callbacks_own_parameter_is_no_label_a_row_parameter_takes() {
    let unconstrained = ["type mismatch in", "run.type_arg", "expected a type for 'EffP'"];
    let mut shapes = placed("put(k, 5)", "{Modify[k]}", "run(q, {cb})");
    shapes.push((
        "operation",
        Shape {
            above: "  operation cb(k: Cell[V = Int64]) -> Int64 effects Modify[k] = put(k, 5)",
            body: "    run(q, cb)",
            ..Shape::default()
        },
    ));
    shapes.push((
        "tuple",
        Shape {
            body: "    let t = (lambda (k: Cell[V = Int64]) -> put(k, 5), 1)\n    run(q, t._1)",
            ..Shape::default()
        },
    ));
    for (spelling, shape) in &shapes {
        let src = program(&format!("wi1tjqh.own_{spelling}"), shape);
        assert_refused_naming(
            &load_errors_of(&src),
            &unconstrained,
            &format!("a callback writing its own parameter at `@ {{EffP}}` ({spelling})"),
        );
    }
    // The same callback parameter, handed on by an operation that declares nothing.
    let src = program(
        "wi1tjqh.own_pure",
        &Shape {
            parameter: ", g: (k: Cell[V = Int64]) -> Int64 @ {Modify[k]}",
            passes: ", lambda (k: Cell[V = Int64]) -> put(k, 5)",
            declares: "{}",
            body: "    run(q, g)",
            ..Shape::default()
        },
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &unconstrained,
        "a callback parameter writing its own parameter, in an operation declaring no effect",
    );
}

/// … AND THE SLOT THAT NAMES THE CALLBACK'S PARAMETER TAKES THAT WRITE ITSELF: `f: (k) -> Int64
/// @ {Modify[k], EffP}`, `run` declaring `{Modify[p], EffP}`. A callback writing `k` alone
/// leaves `EffP` empty — 5 answered, the first cell written: 552 — and one writing `k` and `r`
/// gives it `{Modify[r]}`: 11 answered, both written, 1156.
///
/// Every one of them was refused "expected a type for 'EffP', got unconstrained" (MEASURED):
/// the callback's `Modify[k]` met no label of the slot, whose binder is another symbol, and
/// went to the tail. FAILS under part 4, and under part 1 for the callback writing `r` too.
///
/// A lambda taken out of a tuple is read at its parameters' positions as the lambda written at
/// the call is: its arrow records them (WI-20261014-EDPF6).
#[test]
fn a_slot_naming_the_callbacks_parameter_takes_the_write_and_the_row_parameter_the_rest() {
    for (does, row, answer) in [
        ("put(k, 5)", "{Modify[k]}", 552),
        ("put(k, 5) + put(r, 6)", "{Modify[k], Modify[r]}", 1156),
    ] {
        let mut shapes = placed(does, row, "run(q, {cb})");
        // An operation at the top level has no `r` to write: it is the one-write row only.
        if !does.contains("(r,") {
            shapes.push((
                "operation",
                Shape {
                    above: "  operation cb(k: Cell[V = Int64]) -> Int64 effects Modify[k] = put(k, 5)",
                    body: "    run(q, cb)",
                    ..Shape::default()
                },
            ));
        }
        for (spelling, shape) in shapes {
            let ns = format!("wi1tjqh.named_{spelling}_{answer}");
            let src = program(&ns, &Shape { run: RUN_OWN, ..shape });
            assert_eq!(
                run_int64(&src, &format!("{ns}.go")),
                Ok(answer),
                "`{does}` ({spelling})"
            );
        }
    }
    let ns = "wi1tjqh.named_tuple";
    let src = program(
        ns,
        &Shape {
            run: RUN_OWN,
            body: "    let t = (lambda (k: Cell[V = Int64]) -> put(k, 5) + put(r, 6), 1)\n    run(q, t._1)",
            ..Shape::default()
        },
    );
    assert_eq!(
        run_int64(&src, &format!("{ns}.go")),
        Ok(1156),
        "a lambda out of a tuple writing its own parameter at a slot naming one",
    );
}

/// A MODIFYING CALLBACK AGAINST AN OPEN ROW THAT LACKS THE WRITE (`f: (x) -> Unit @ {Eff,
/// -Modify[x]}`) IS REFUSED HOWEVER IT IS WRITTEN — an operation, a lambda, a `let`, a callback
/// parameter, a lambda out of a tuple, each by the absence it violates. With the label bound and
/// nothing said of the binder, the operation, the lambda, the `let` and the tuple all LOADED:
/// the label `Eff` took covered itself before the absence was read (MEASURED). FAILS under part
/// 3 at the operation, the lambda, the `let` and the tuple once part 4 is out with it.
#[test]
fn a_modifying_callback_is_refused_at_an_open_row_that_lacks_the_write_however_written() {
    let lambda = "lambda (c: Cell[V = Int64]) -> Cell.set(c, 1)";
    let program = |ns: &str, parameter: &str, body: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, Unit, Cell, Modify}}
  operation bad(c: Cell[V = Int64]) -> Unit effects Modify[c] = Cell.set(c, 1)
  operation taker[Eff](f: (x: Cell[V = Int64]) -> Unit @ {{Eff, -Modify[x]}}) -> Unit = ()
  operation boom({parameter}) -> Unit =
{body}
end
"#
        )
    };
    let lacks = ["type mismatch in taker.f (op-arg)", "to lack `Modify[T = f.x]`"];
    for (spelling, parameter, body, names) in [
        ("operation", "", "    taker(bad)".to_string(), &lacks[..]),
        ("lambda", "", format!("    taker({lambda})"), &lacks[..]),
        ("let", "", format!("    let g = {lambda}\n    taker(g)"), &lacks[..]),
        (
            "parameter",
            "g: (c: Cell[V = Int64]) -> Unit @ {Modify[c]}",
            "    taker(g)".to_string(),
            &lacks[..],
        ),
        (
            "tuple",
            "",
            format!("    let t = ({lambda}, 1)\n    taker(t._1)"),
            &lacks[..],
        ),
    ] {
        let src = program(&format!("wi1tjqh.lacks_{spelling}"), parameter, &body);
        assert_refused_naming(
            &load_errors_of(&src),
            names,
            &format!("a modifying callback at `@ {{Eff, -Modify[x]}}` ({spelling})"),
        );
    }
}

/// … AND SO IS A CALLBACK WRITING THE CELL THE SLOT DENIES BY NAME: `f: … @ {EffP, -Modify[p]}`
/// and `run(q, …)` over a callback writing `q`, which is in scope and which `EffP` now takes —
/// the row is then `{Modify[q], -Modify[q]}`, refused in every spelling. Refused before as well:
/// these pass either way by design, by one of two refusals before and by one now.
///
/// THE CONTROL: the callback writing the OTHER cell, `r`, which the row does not deny — 515.
/// That one was refused "unconstrained" (MEASURED) and FAILS under part 1.
#[test]
fn a_callback_writing_the_cell_the_slot_denies_is_refused_however_written() {
    let lambda = "lambda (k: Cell[V = Int64]) -> put(q, 5)";
    let mut shapes = placed("put(q, 5)", "{Modify[q]}", "run(q, {cb})");
    for (spelling, body) in [
        ("tuple", format!("    let t = ({lambda}, 1)\n    run(q, t._1)")),
        (
            "function",
            format!("    let g: Function[A = Cell[V = Int64], B = Int64, E = {{Modify[q]}}] = {lambda}\n    run(q, g)"),
        ),
        (
            "field",
            format!("    let b: Box[EB = {{Modify[q]}}] = box(g: {lambda})\n    run(q, b.g)"),
        ),
        ("bracket", format!("    run[EffP = {{Modify[q]}}](q, {lambda})")),
    ] {
        shapes.push((
            spelling,
            Shape {
                body: Box::leak(body.into_boxed_str()),
                ..Shape::default()
            },
        ));
    }
    for (spelling, shape) in shapes {
        let src = program(
            &format!("wi1tjqh.denied_{spelling}"),
            &Shape { run: RUN_DENIES, ..shape },
        );
        assert_refused_naming(
            &load_errors_of(&src),
            &["type mismatch in run.f (op-arg)", "lack", "Modify[T = q]"],
            &format!("a callback writing `q` at `@ {{EffP, -Modify[p]}}` over `run(q, …)` ({spelling})"),
        );
    }
    let ns = "wi1tjqh.denied_other";
    let src = program(
        ns,
        &Shape {
            run: RUN_DENIES,
            body: "    run(q, lambda (k: Cell[V = Int64]) -> put(r, 5))",
            ..Shape::default()
        },
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(515));
}

/// `sort Each` declaring `each` with its callback slot at `spec_row`, `Strm` providing it with a
/// member whose slot is at `member_row`, and `use(s, q, r)` — declaring everything — whose body
/// is `call`.
fn dispatched(ns: &str, spec_row: &str, member_row: &str, call: &str) -> String {
    let each = |receiver: &str, row: &str| {
        format!(
            "operation each[EffP](s: {receiver}, p: Cell[V = Int64], f: (k: Cell[V = Int64]) -> Int64 @ {row}) -> Int64 effects {{Modify[p], EffP}}"
        )
    };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Cell, Modify, Error}}
  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n
  sort Each
    {spec}
  end
  sort Strm
    entity strm(n: Int64)
    provides Each
    {member} = f(p)
  end
  operation use(s: Strm, q: Cell[V = Int64], r: Cell[V = Int64]) -> Int64 effects {EVERYTHING} =
    {call}
  operation go() -> Int64 effects {{Error[String]}} =
    let c: Cell[V = Int64] = Cell.new(1)
    let d: Cell[V = Int64] = Cell.new(2)
    let n = use(strm(n: 0), c, d)
    n * 100 + Cell.get(c) * 10 + Cell.get(d)
end
"#,
        spec = each("Self", spec_row),
        member = each("Strm", member_row),
    )
}

/// A DISPATCHED CALL READS ITS CALLBACK THE SAME WAY, qualified and by dot: the spec's slot and
/// its member's both `@ {Modify[k], EffP}`, the callback writing its own parameter and `r` —
/// 11 answered, both cells written, 1156. Both were refused "unconstrained" (MEASURED). FAILS
/// under part 1 and under part 4.
#[test]
fn a_dispatched_call_reads_the_callback_at_its_slot_too() {
    let named = "{Modify[k], EffP}";
    let lambda = "lambda (k: Cell[V = Int64]) -> put(k, 5) + put(r, 6)";
    for (form, call) in [
        ("qualified", format!("Each.each(s, q, {lambda})")),
        ("dot", format!("s.each(q, {lambda})")),
    ] {
        let ns = format!("wi1tjqh.dispatched_{form}");
        let src = dispatched(&ns, named, named, &call);
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(1156), "{form}");
    }
}

/// TWO DECLARED SIGNATURES MEET WITH NO CALL BETWEEN THEM where a member is fitted to its spec,
/// and the rule holds there by what the label names: a member whose slot is its own row
/// parameter alone, `@ {EffP}`, takes less than a spec slot reading `@ {Modify[k], EffP}` — no
/// row `EffP` stands for holds a write to the slot's own binder — and is refused as no member
/// of it. With every label holding a value bound, it fitted, and the call ran to 552
/// (MEASURED). FAILS under part 2.
///
/// The member that writes the spec's slot fits, and is the row above.
#[test]
fn a_member_whose_slot_is_its_row_parameter_alone_does_not_fit_a_slot_naming_the_binder() {
    let src = dispatched(
        "wi1tjqh.member_fit",
        "{Modify[k], EffP}",
        "{EffP}",
        "Each.each(s, q, lambda (k: Cell[V = Int64]) -> put(k, 5))",
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &["its own member 'each' does not fit", "takes less than the spec's"],
        "a member slot `@ {EffP}` under a spec slot `@ {Modify[k], EffP}`",
    );
}

/// THE OVERRIDE A CALL DISPATCHES TO IS TYPED AT THAT CALL TOO, its own type parameters bound
/// from the arguments, and it reads the callback as the qualified call does. The member here
/// does not fit — its slot is `@ {EffQ}` under a spec slot `@ {Modify[k], s.E}` — and `use`
/// declares nothing, so the program is refused twice over: the member, and the write to `q`
/// the spec charges. Nothing else: with the argument met as passed, the override's `EffQ` took
/// the lambda's own binder and the caller was charged an undeclared `Modify[T = k]` as well, a
/// label naming nothing it can declare (MEASURED). FAILS under part 5, and under part 2.
#[test]
fn the_override_a_call_dispatches_to_reads_the_callback_at_its_own_slot() {
    let src = r#"
namespace wi1tjqh.override_slot
  import anthill.prelude.{Int64, Cell, Modify}
  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n
  sort Sp
    sort T = ?
    effects E = ?
    operation each(s: Self, p: Cell[V = Int64], f: (k: Cell[V = Int64]) -> Int64 @ {Modify[k], s.E}) -> Int64 effects {Modify[p], s.E}
  end
  sort Car
    effects EC = ?
    entity car(n: Int64)
    provides Sp[T = Self, E = {EC}]
    operation each[EffQ](s: Self, p: Cell[V = Int64], f: (k: Cell[V = Int64]) -> Int64 @ {EffQ}) -> Int64 effects {EffQ} = f(p)
  end
  operation use(q: Cell[V = Int64]) -> Int64 =
    let a: Car[EC = {}] = car(n: 0)
    Sp.each(a, q, lambda (k: Cell[V = Int64]) -> put(k, 5))
end
"#;
    let errs = load_errors_of(src);
    assert_refused_naming(
        &errs,
        &["its own member 'each' does not fit", "undeclared effect: Modify[T = q]"],
        "a member slot `@ {EffQ}` under a spec slot `@ {Modify[k], s.E}`, called from a pure `use`",
    );
    assert!(
        !errs.iter().any(|e| e.contains("Modify[T = k]")),
        "the lambda's own binder reached the caller's row:\n{}",
        errs.join("\n")
    );
}

/// A CONSTRUCTOR READS A CALLBACK AT ITS FIELD'S SLOT AS A CALL READS ONE AT A PARAMETER'S:
/// `entity box(g: (k: Cell[V = Int64]) -> Int64 @ {EB})`, and the sort's row parameter `EB`
/// takes the callback's write to `r` — `consume[E](b: Box[EB = E], p) effects {E}` then runs it
/// over `q`: 515, the field named and by position. Both were refused, `E` unconstrained
/// (MEASURED). FAILS under part 1.
///
/// A callback writing its OWN parameter leaves `EB` open — the binder names nothing in the
/// box's type — and the call is refused for the `E` nothing fixed, a lambda and an operation
/// alike. With the field met as passed, the box was a `Box[EB = {Modify[k]}]` and the caller
/// was refused for an undeclared `Modify[T = k]` instead (MEASURED). FAILS under part 6, and
/// under part 3.
#[test]
fn a_constructor_reads_the_callback_at_its_fields_slot() {
    let consume = "  operation consume[E](b: Box[EB = E], p: Cell[V = Int64]) -> Int64 effects {E} = match b case box(g) -> g(p)";
    let writes_r = "lambda (k: Cell[V = Int64]) -> put(r, 5)";
    for (spelling, body) in [
        ("named", format!("    consume(box(g: {writes_r}), q)")),
        ("positional", format!("    consume(box({writes_r}), q)")),
        ("let", format!("    let b = box({writes_r})\n    consume(b, q)")),
    ] {
        let ns = format!("wi1tjqh.field_{spelling}");
        let src = program(
            &ns,
            &Shape {
                above: consume,
                body: &body,
                ..Shape::default()
            },
        );
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(515), "{spelling}");
    }
    let cb = format!(
        "{consume}\n  operation cb(k: Cell[V = Int64]) -> Int64 effects Modify[k] = put(k, 5)"
    );
    for (spelling, body) in [
        ("lambda", "    consume(box(g: lambda (k: Cell[V = Int64]) -> put(k, 5)), q)"),
        ("operation", "    consume(box(cb), q)"),
    ] {
        let src = program(
            &format!("wi1tjqh.field_own_{spelling}"),
            &Shape {
                above: &cb,
                body,
                ..Shape::default()
            },
        );
        let errs = load_errors_of(&src);
        assert_refused_naming(
            &errs,
            &["consume.type_arg", "expected a type for 'E'"],
            &format!("a field callback writing its own parameter ({spelling})"),
        );
        assert!(
            !errs.iter().any(|e| e.contains("Modify[T = k]")),
            "the callback's own binder reached the box's row ({spelling}):\n{}",
            errs.join("\n")
        );
    }
}

/// … AND SO DOES THE APPLICATION OF A FUNCTION VALUE: `let app = lambda (f: (k: Cell[V =
/// Int64]) -> Int64 @ {?}) -> f(q)`, applied to a callback writing `r` — 515. It was refused for
/// an undeclared `?_`, the slot's row left open (MEASURED). FAILS under part 1.
///
/// Applied to a callback writing its own parameter it is refused still, and not for a label
/// over that binder: with the argument met as passed the slot's row took `Modify[k]`, and
/// that is what the caller was charged (MEASURED). FAILS under part 7, and under part 3.
#[test]
fn a_function_value_reads_the_callback_at_its_slot() {
    let app = "    let app = lambda (f: (k: Cell[V = Int64]) -> Int64 @ {?}) -> f(q)";
    let ns = "wi1tjqh.fnvalue_scope";
    let src = program(
        ns,
        &Shape {
            body: &format!("{app}\n    app(lambda (k: Cell[V = Int64]) -> put(r, 5))"),
            ..Shape::default()
        },
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(515));
    let src = program(
        "wi1tjqh.fnvalue_own",
        &Shape {
            body: &format!("{app}\n    app(lambda (k: Cell[V = Int64]) -> put(k, 5))"),
            ..Shape::default()
        },
    );
    let errs = load_errors_of(&src);
    assert_refused_naming(
        &errs,
        &["type mismatch in use.effects (op-effects)"],
        "a function value applied to a callback writing its own parameter",
    );
    assert!(
        !errs.iter().any(|e| e.contains("Modify[T = k]")),
        "the callback's own binder reached the caller's row:\n{}",
        errs.join("\n")
    );
}

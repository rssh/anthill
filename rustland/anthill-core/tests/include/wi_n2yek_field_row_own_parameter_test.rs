//! WI-20261014-N2YEK — a row variable of a callback's slot takes no label over the callback's
//! own parameter, and a slot whose every row variable lacks a label does not admit it, whatever
//! the variable is bound to later.
//!
//! `entity box(g: (z: Cell[V = Int64]) -> Int64 @ {EB})` given `lambda (z) -> put(z, 5)`: the
//! lambda writes the cell it is handed, and the field's row parameter `EB` stands outside the
//! arrow, where `z` names nothing — so `EB` lacks `Modify[z]` (`callback_at_slot`). A
//! construction checks its fields before its expectation binds the sort's parameters, and the
//! field's row was still open there, so the callback check admitted the lambda; the annotation
//! then bound `EB = {}`, and applying `b.g` wrote `q` from a `use` declaring nothing — 55
//! (MEASURED, plain and under the node carrier). So did every later binding of `EB`: an
//! annotation, a result type, a pure slot the construction is handed to, a bracket on a call the
//! field is projected into. The callback check now refuses a label every open tail of the slot
//! lacks, at the construction.
//!
//! An operation's slot `@ {EffP}` refused the same lambda only because nothing else bound `EffP`
//! ("expected a type for 'EffP', got unconstrained — use `run[EffP = …](…)`", a repair no bracket
//! makes good); it is refused at the argument now, by the same rule.
//!
//! EVERY ROW DRIVES WHAT IT CLAIMS: an admitted program RUNS to its value; a refusal is asserted
//! by the words that say where it stands.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ──────────────────────────────
//!
//! Backed out (the check answering "no tail lacks it"), 5 of 6 FAIL:
//! [`the_tickets_construction_is_refused_at_the_field`] (the program runs to 55, the
//! construction alone loads), [`every_binding_of_the_row_parameter_refuses_it`] (five run or
//! load, the unannotated one is refused at `use`'s effects for `b.EB`),
//! [`every_spelling_of_the_callback_is_refused`] (each runs to 55),
//! [`an_operation_slot_refuses_it_by_the_same_rule`] and
//! [`a_binder_out_of_scope_is_refused_by_the_same_rule`] (refused "unconstrained").
//!
//! PASS EITHER WAY, BY DESIGN: [`what_the_row_variable_takes_still_runs`] — the controls: a
//! lambda writing a cell in scope, reading its parameter, raising, at a slot naming the parameter
//! beside its row parameter, and a write to a cell in scope refused at a pure annotation.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// `Box` over the field `g`, `{above}` beside it, and `use(q)` declaring `{declares}` with
/// `{body}`; `go()` runs `use` over a cell holding 1 and answers `use(c) * 10 + Cell.get(c)`.
fn program(ns: &str, above: &str, declares: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Error, Cell, Modify}}
  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n
  sort Box
    effects EB = ?
    entity box(g: (z: Cell[V = Int64]) -> Int64 @ {{EB}})
  end
{above}
  operation use(q: Cell[V = Int64]) -> Int64{declares} =
{body}
  operation go() -> Int64 effects {{Error[String]}} =
    let c: Cell[V = Int64] = Cell.new(1)
    use(c) * 10 + Cell.get(c)
end
"#
    )
}

/// The refusal at the field, naming the label and why the row variable cannot take it.
fn assert_refused_at_the_field(src: &str, why: &str) {
    assert_refused_naming(
        &load_errors_of(src),
        &[
            "box.g (entity-field)",
            "may not take `Modify[T = ",
            "over its own parameter",
        ],
        why,
    );
}

/// THE TICKET'S PROGRAM: `Box[EB = {}]` over a lambda writing its own parameter, applied to `q`
/// in a `use` declaring nothing; and the construction alone. FAILS when backed out.
#[test]
fn the_tickets_construction_is_refused_at_the_field() {
    let src = program(
        "win2yek.ticket",
        "",
        "",
        "    let b: Box[EB = {}] = box(g: lambda (z: Cell[V = Int64]) -> put(z, 5))\n    let w = b.g\n    w(q)",
    );
    assert_refused_at_the_field(&src, "the ticket's program");
    let src = program(
        "win2yek.alone",
        "",
        "",
        "    let b: Box[EB = {}] = box(g: lambda (z: Cell[V = Int64]) -> put(z, 5))\n    0",
    );
    assert_refused_at_the_field(&src, "the construction alone");
}

/// WHEREVER `EB` IS BOUND, and where nothing binds it: an annotation naming another cell, none,
/// a result type, a result at the operation's own row parameter, a pure slot the construction
/// is handed to, and a bracket on the call its field is projected into — refused at the field.
/// FAILS when backed out.
#[test]
fn every_binding_of_the_row_parameter_refuses_it() {
    let lambda = "lambda (z: Cell[V = Int64]) -> put(z, 5)";
    let cases: [(&str, String, String); 6] = [
        (
            "another_cell",
            String::new(),
            format!("    let b: Box[EB = {{Modify[q]}}] = box(g: {lambda})\n    0"),
        ),
        (
            "unannotated",
            String::new(),
            format!("    let b = box(g: {lambda})\n    let w = b.g\n    w(q)"),
        ),
        (
            "result",
            format!("  operation mk() -> Box[EB = {{}}] = box(g: {lambda})\n"),
            "    let w = mk().g\n    w(q)".to_string(),
        ),
        (
            "result_row_parameter",
            format!("  operation mk[E]() -> Box[EB = E] = box(g: {lambda})\n"),
            "    0".to_string(),
        ),
        (
            "pure_slot",
            "  operation consume(b: Box[EB = {}], c: Cell[V = Int64]) -> Int64 =\n    let w = b.g\n    w(c)\n"
                .to_string(),
            format!("    consume(box(g: {lambda}), q)"),
        ),
        (
            "bracketed_slot",
            "  operation apply[E](p: Cell[V = Int64], f: (k: Cell[V = Int64]) -> Int64 @ {E}) -> Int64 effects {E} = f(p)\n"
                .to_string(),
            format!("    apply[E = {{}}](q, box(g: {lambda}).g)"),
        ),
    ];
    for (name, above, body) in cases {
        let src = program(&format!("win2yek.bound_{name}"), &above, "", &body);
        assert_refused_at_the_field(&src, name);
    }
}

/// EVERY SPELLING OF THE CALLBACK at `Box[EB = {}]`: a `let`-held lambda, the qualified
/// constructor, the field by position, an operation taken as a value, and `use`'s own callback
/// parameter typed as writing its parameter. FAILS when backed out.
#[test]
fn every_spelling_of_the_callback_is_refused() {
    let applied = "\n    let w = b.g\n    w(q)";
    let set_five =
        "  operation setFive(y: Cell[V = Int64]) -> Int64 effects Modify[y] = put(y, 5)\n";
    let cases: [(&str, &str, String); 4] = [
        (
            "let",
            "",
            format!("    let f = lambda (z: Cell[V = Int64]) -> put(z, 5)\n    let b: Box[EB = {{}}] = box(g: f){applied}"),
        ),
        (
            "qualified",
            "",
            format!("    let b: Box[EB = {{}}] = Box.box(g: lambda (z: Cell[V = Int64]) -> put(z, 5)){applied}"),
        ),
        (
            "positional",
            "",
            format!("    let b: Box[EB = {{}}] = box(lambda (z: Cell[V = Int64]) -> put(z, 5)){applied}"),
        ),
        ("operation", set_five, format!("    let b: Box[EB = {{}}] = box(g: setFive){applied}")),
    ];
    for (name, above, body) in cases {
        let src = program(&format!("win2yek.spelt_{name}"), above, "", &body);
        assert_refused_at_the_field(&src, name);
    }
    let above = "  operation hold(q: Cell[V = Int64], h: (k: Cell[V = Int64]) -> Int64 @ {Modify[k]}) -> Int64 =\n    let b: Box[EB = {}] = box(g: h)\n    let w = b.g\n    w(q)\n";
    let src = program(
        "win2yek.spelt_parameter",
        above,
        "",
        "    hold(q, lambda (z: Cell[V = Int64]) -> put(z, 5))",
    );
    assert_refused_at_the_field(&src, "a callback parameter");
}

/// AN OPERATION'S SLOT `@ {EffP}` refuses the same lambda at the argument, by the same rule,
/// where it said "unconstrained" and advised a bracket; the bracket `run[EffP = {}]` is refused
/// at its closed row, as before. FAILS when backed out (the first).
#[test]
fn an_operation_slot_refuses_it_by_the_same_rule() {
    let above = "  operation run[EffP](p: Cell[V = Int64], f: (k: Cell[V = Int64]) -> Int64 @ {EffP}) -> Int64 effects {EffP} = f(p)\n";
    let src = program(
        "win2yek.slot",
        above,
        "",
        "    run(q, lambda (z: Cell[V = Int64]) -> put(z, 5))",
    );
    let errs = load_errors_of(&src);
    assert_refused_naming(
        &errs,
        &[
            "run.f (op-arg)",
            "may not take `Modify[T = z]`",
            "over its own parameter `z`",
        ],
        "the open slot",
    );
    assert!(
        !errs.join(" | ").contains("unconstrained"),
        "refused at the argument, not for the row parameter: {errs:?}"
    );
    let src = program(
        "win2yek.slot_bracket",
        above,
        "",
        "    run[EffP = {}](q, lambda (z: Cell[V = Int64]) -> put(z, 5))",
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &["run.f (op-arg)", "(a closed row)", "`Modify[T = z]`"],
        "the bracketed slot",
    );
}

/// A LABEL OVER A BINDER OUT OF SCOPE THAT IS NOT THE CALLBACK'S OWN, at the same slot: the
/// write to `y` a lambda returned by `lambda (y) -> …` carries. It was refused "unconstrained"
/// (MEASURED), and is refused at the argument, the row variable lacking the label — and is not
/// called the lambda's own parameter. FAILS when backed out. A lambda applying `inner`'s callback
/// parameter `g` to its own `k` writes `k` (the application reads `g`'s parameter at its
/// argument, WI-20261014-7EZS6), and is refused as a lambda writing its own parameter is; it
/// carried `g`'s place `Modify[g.y]` before, out of scope, and was refused by the first rule.
#[test]
fn a_binder_out_of_scope_is_refused_by_the_same_rule() {
    let above = "  operation run[EffP](p: Cell[V = Int64], f: (k: Cell[V = Int64]) -> Int64 @ {EffP}) -> Int64 effects {EffP} = f(p)\n";
    let cases = [
        (
            "returned",
            "  operation inner(q: Cell[V = Int64], r: Cell[V = Int64]) -> Int64 effects {Modify[q], Modify[r]} =\n    \
             let mk = lambda (y: Cell[V = Int64]) -> lambda (k: Cell[V = Int64]) -> put(y, 5)\n    \
             run(q, mk(r))\n",
            "Modify[T = y]",
            false,
        ),
        (
            "applied",
            "  operation inner(q: Cell[V = Int64], g: (y: Cell[V = Int64]) -> Int64 @ {Modify[y]}) -> Int64 effects {Modify[q]} =\n    \
             run(q, lambda (k: Cell[V = Int64]) -> g(k))\n",
            "Modify[T = k]",
            true,
        ),
    ];
    for (name, inner, label, own) in cases {
        let src = program(
            &format!("win2yek.out_of_scope_{name}"),
            &format!("{above}{inner}"),
            "",
            "    0",
        );
        let errs = load_errors_of(&src);
        if own {
            assert_refused_naming(
                &errs,
                &[
                    "run.f (op-arg)",
                    &format!("may not take `{label}`"),
                    "over its own parameter `k`",
                ],
                name,
            );
            continue;
        }
        assert_refused_naming(
            &errs,
            &[
                "run.f (op-arg)",
                &format!("may not take `{label}`"),
                "which the row variable lacks",
            ],
            name,
        );
        assert!(
            !errs.iter().any(|e| e.contains("own parameter")),
            "{name}: not the callback's own parameter: {errs:?}"
        );
    }
}

/// THE CONTROLS: what a row variable takes still binds it and runs — a lambda writing a cell in
/// scope (`EB = {Modify[q]}`, 55), one reading its parameter (411), one raising at `Box[EB =
/// {Error[String]}]` (411), and a slot naming the parameter beside its row parameter (55); a
/// write to a cell in scope at `Box[EB = {}]` is refused at the annotation. PASS either way.
#[test]
fn what_the_row_variable_takes_still_runs() {
    let applied = "\n    let w = b.g\n    w(q)";
    let runs: [(&str, &str, &str, String, i64); 4] = [
        (
            "writes_scope",
            "",
            " effects Modify[q]",
            format!("    let b = box(g: lambda (z: Cell[V = Int64]) -> put(q, 5)){applied}"),
            55,
        ),
        (
            "reads_own",
            "",
            "",
            format!("    let b = box(g: lambda (z: Cell[V = Int64]) -> Cell.get(z) + 40){applied}"),
            411,
        ),
        (
            "raises",
            "",
            " effects Error[String]",
            format!(
                "    let b: Box[EB = {{Error[String]}}] = box(g: lambda (z: Cell[V = Int64]) -> if Cell.get(z) < 0 then Error.raise(\"boom\") else 41){applied}"
            ),
            411,
        ),
        (
            "slot_names_own",
            "  operation runOwn[EffP](p: Cell[V = Int64], f: (k: Cell[V = Int64]) -> Int64 @ {Modify[k], EffP}) -> Int64 effects {Modify[p], EffP} = f(p)\n",
            " effects Modify[q]",
            "    runOwn(q, lambda (z: Cell[V = Int64]) -> put(z, 5))".to_string(),
            55,
        ),
    ];
    for (name, above, declares, body, value) in runs {
        let ns = format!("win2yek.control_{name}");
        let src = program(&ns, above, declares, &body);
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(value), "{name}");
    }
    let src = program(
        "win2yek.control_scope_at_pure",
        "",
        "",
        &format!(
            "    let b: Box[EB = {{}}] = box(g: lambda (z: Cell[V = Int64]) -> put(q, 5)){applied}"
        ),
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &["b.annotation (let-binding)", "Box[EB = Modify[T = q]]"],
        "a cell in scope at a pure annotation",
    );
}

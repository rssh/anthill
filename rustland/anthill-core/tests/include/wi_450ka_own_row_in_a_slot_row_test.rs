//! WI-20261013-450KA — a slot's row holding the enclosing operation's own row parameter admits
//! THAT parameter and nothing else through it, however the callback is written.
//!
//! `use[R](…) effects {…, R}` calls `run`, whose callback slot reads — off a receiver
//! (`f: … @ {s.E}` over `s: Src[E = {Modify[q], Error[String], R}]`), out of the call's bracket
//! (`run[EffP = {R}](…)`), or from an earlier argument — a row holding `R`. `R` is rigid there:
//! a row unknown where the check runs.
//!
//! TWO READERS JUDGED THAT ROW, AND DISAGREED BOTH WAYS:
//!
//!  * the whole-type relation (`relate_effect_rows`, directional), which runs where both types
//!    are determined, REFUSED a callback raising `R` itself as soon as a label or a second row
//!    stood beside `R` in the slot's row — the shared tail was asked to take the extra labels,
//!    and one tail against two were no equal sets;
//!  * the per-label check (`validate_callback_effect_row`), the only reader where a type is not
//!    determined — a callee with a row parameter of its own, a `let`-held lambda of two
//!    parameters (its parameter list is a variable) — read ANY tail as an open row, so under a
//!    rigid one it admitted every label and every other row.
//!
//! So the ticket's two-parameter `let` loaded where the lambda written at the call was refused,
//! and — the wider half — `run[EffP = {R}](q, lambda (k) -> Error.raise("boom"))` loaded inside a
//! `use` declaring `{R}`, and a `go` typed pure raised (MEASURED, on every spelling below marked
//! "raised" or "wrote").
//!
//! EVERY ROW DRIVES WHAT IT CLAIMS: an admitted program RUNS, and its value says which cell was
//! written (`n * 100 + c * 10 + d`, the cells starting at 1 and 2); a refusal is asserted by the
//! words that name the slot, and the program beside it that differs in one thing runs.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! TWO PARTS, each backed out in place and RUN over this file's 12 rows:
//!
//! 1. A RIGID TAIL OF THE ACTUAL THAT THE EXPECTED ROW HOLDS IS A SUBSET (`relate_effect_rows`'s
//!    shortcut held to a CLOSED actual, as it stood). 2 FAIL:
//!    [`a_callback_raising_the_callers_own_row_fits_a_projected_slot_holding_it`] and
//!    [`a_callback_raising_one_of_two_own_rows_fits_a_projected_slot_holding_both`].
//! 2. A RIGID TAIL OPENS NOTHING (`validate_callback_effect_row` reading the declared row as
//!    open wherever it has a tail, and judging a rigid row of the callback only under a row
//!    with none). 8 FAIL, each loading where a refusal is owed:
//!    [`a_callback_writing_its_own_parameter_is_refused_at_a_projected_slot`],
//!    [`a_label_is_refused_at_a_bracket_holding_only_the_callers_own_row`],
//!    [`another_own_row_is_refused_at_a_bracket_holding_one`],
//!    [`a_function_slot_at_the_callers_own_row_admits_that_row_alone`],
//!    `a_row_an_earlier_argument_bound_to_the_callers_own_admits_that_row_alone` (since
//!    WI-20260820-RDNS4 [`a_row_two_callbacks_share_holds_both_of_the_callers_own_rows`], whose
//!    row is the union and whose refusals are at `use`'s effects),
//!    [`a_sorts_own_row_in_a_member_body_admits_that_row_alone`],
//!    [`a_dispatched_call_at_the_receivers_own_row_admits_that_row_alone`] and
//!    [`the_refusal_names_the_row_and_what_it_admits`].
//!
//! PASS EITHER WAY, BY DESIGN: [`the_callers_own_row_fits_a_bracket_holding_it`] and
//! [`a_label_written_beside_the_callers_own_row_is_admitted`] — the controls of part 2's
//! refusals, the same programs with the row said whole.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// `use[R, Q](q, r, h @ {R}, i @ {Q})` over two cells, declaring `{declares}`, whose body is
/// `body`; `go()` is PURE but for `go_row`, runs it over cells holding 1 and 2 with two pure
/// callbacks, and answers `n * 100 + c * 10 + d`. `run` is `run_decl`.
fn program(ns: &str, run_decl: &str, declares: &str, body: &str, go_row: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Unit, String, List, Cell, Modify, Error, Function}}
  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n
  sort Src
    effects E = ?
    entity src(n: Int64)
  end
{run_decl}
  operation use[R, Q](q: Cell[V = Int64], r: Cell[V = Int64], h: (n: Int64) -> Int64 @ {{R}}, i: (n: Int64) -> Int64 @ {{Q}}) -> Int64 effects {{{declares}}} =
{body}
  operation go() -> Int64{go_row} =
    let c: Cell[V = Int64] = Cell.new(1)
    let d: Cell[V = Int64] = Cell.new(2)
    let n = use(c, d, lambda (n: Int64) -> n + 40, lambda (n: Int64) -> n + 70)
    n * 100 + Cell.get(c) * 10 + Cell.get(d)
end
"#
    )
}

/// The callback's parameters at each arity, and what `run` applies it to.
const ARITIES: [(&str, &str, &str); 2] = [
    ("one", "k: Cell[V = Int64]", "f(p)"),
    ("two", "k: Cell[V = Int64], u: Int64", "f(p, 5)"),
];

/// The callback `lambda ({takes}) -> {does}` passed to `call` (which writes `{cb}` where it
/// goes), written at the call and held in a `let`.
fn spellings(takes: &str, does: &str, call: &str) -> [(&'static str, String); 2] {
    let lambda = format!("lambda ({takes}) -> {does}");
    [
        ("lambda", format!("    {}", call.replace("{cb}", &lambda))),
        ("let", format!("    let g = {lambda}\n    {}", call.replace("{cb}", "g"))),
    ]
}

/// THE TICKET'S SLOT: `run`'s callback row is projected off the receiver, `{s.E}`, and `use`
/// says `s`'s row whole — `everything`, which holds its own `R` and `Q`.
fn projected(ns: &str, takes: &str, applies: &str, body: &str) -> String {
    let everything = "Modify[q], Modify[r], Error[String], R, Q";
    let run = format!(
        "  operation run(s: Src, p: Cell[V = Int64], f: ({takes}) -> Int64 @ {{s.E}}) -> Int64 effects {{s.E}} = {applies}"
    );
    let body = format!("    let s: Src[E = {{{everything}}}] = src(n: 0)\n{body}");
    program(ns, &run, everything, &body, " effects {Error[String]}")
}

/// `run[EffP]`, its callback row its own parameter: `{EffP}`, said by the call's bracket.
fn bracketed(ns: &str, takes: &str, applies: &str, declares: &str, body: &str, go_row: &str) -> String {
    let run = format!(
        "  operation run[EffP](p: Cell[V = Int64], f: ({takes}) -> Int64 @ {{EffP}}) -> Int64 effects {{EffP}} = {applies}"
    );
    program(ns, &run, declares, body, go_row)
}

/// THE TICKET'S MEASUREMENT (1), (2), (4): the callback is `h(5)`, whose row is `use`'s own
/// `R`, and the slot's row holds `R` beside two writes, a label and `Q`. A subset, at both
/// arities and in both spellings: `h` answers 45, no cell is written — 4512. Three of the four
/// were refused "expected … @ {Error[T = String], Modify[T = q], Modify[T = r], ?R, ?Q}, got …
/// @ {?R}"; the two-parameter `let` ran (MEASURED). FAILS under part 1.
#[test]
fn a_callback_raising_the_callers_own_row_fits_a_projected_slot_holding_it() {
    for (arity, takes, applies) in ARITIES {
        for (spelling, body) in spellings(takes, "h(5)", "run(s, q, {cb})") {
            let ns = format!("wi450ka.own_{arity}_{spelling}");
            let src = projected(&ns, takes, applies, &body);
            assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(4512), "{arity}, {spelling}");
        }
    }
}

/// … AND THE OTHER OF THE TWO ROWS THE SLOT HOLDS: `i(5)`, whose row is `Q`. 75, no cell
/// written — 7512. FAILS under part 1.
#[test]
fn a_callback_raising_one_of_two_own_rows_fits_a_projected_slot_holding_both() {
    for (arity, takes, applies) in ARITIES {
        for (spelling, body) in spellings(takes, "i(5)", "run(s, q, {cb})") {
            let ns = format!("wi450ka.other_{arity}_{spelling}");
            let src = projected(&ns, takes, applies, &body);
            assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(7512), "{arity}, {spelling}");
        }
    }
}

/// THE TICKET'S MEASUREMENT (3): the callback writes the cell it is handed, `put(k, 5)`, whose
/// row is `{Modify[k]}`. The slot's row names `q` and `r` and no parameter of the callback, so
/// it does not say that write: refused at both arities and in both spellings. The
/// two-parameter `let` loaded and wrote the cell (MEASURED: 552). FAILS under part 2.
///
/// ITS CONTROL is the same callback writing `r`, a cell the slot's row names: 5, and `d`
/// written — 515, in all four.
#[test]
fn a_callback_writing_its_own_parameter_is_refused_at_a_projected_slot() {
    for (arity, takes, applies) in ARITIES {
        for (spelling, body) in spellings(takes, "put(k, 5)", "run(s, q, {cb})") {
            let ns = format!("wi450ka.writes_own_{arity}_{spelling}");
            let src = projected(&ns, takes, applies, &body);
            assert_refused_naming(
                &load_errors_of(&src),
                &["type mismatch in run.f (op-arg)"],
                &format!("a callback writing its own parameter ({arity}, {spelling})"),
            );
        }
        for (spelling, body) in spellings(takes, "put(r, 5)", "run(s, q, {cb})") {
            let ns = format!("wi450ka.writes_named_{arity}_{spelling}");
            let src = projected(&ns, takes, applies, &body);
            assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(515), "{arity}, {spelling}");
        }
    }
}

/// THE BRACKET SAYS THE ROW: `run[EffP = {R}](q, …)` inside a `use` declaring `{R}` alone,
/// under a `go` typed PURE. A callback raising `Error[String]` is no part of `{R}`, nor is one
/// writing its own parameter: refused, at both arities and in both spellings. All eight
/// loaded; the first raised `boom` out of `go`, the second wrote the cell (MEASURED). FAILS
/// under part 2.
#[test]
fn a_label_is_refused_at_a_bracket_holding_only_the_callers_own_row() {
    for does in ["Error.raise(\"boom\")", "put(k, 5)"] {
        for (arity, takes, applies) in ARITIES {
            for (spelling, body) in spellings(takes, does, "run[EffP = {R}](q, {cb})") {
                let ns = format!("wi450ka.label_{arity}_{spelling}");
                let src = bracketed(&ns, takes, applies, "R", &body, "");
                assert_refused_naming(
                    &load_errors_of(&src),
                    &["type mismatch in run.f (op-arg)"],
                    &format!("`{does}` at a slot whose row is `{{R}}` ({arity}, {spelling})"),
                );
            }
        }
    }
}

/// … AND SO IS THE CALLER'S OTHER ROW: `i(5)`, row `Q`, at `[EffP = {R}]` — `Q` cannot be
/// shown inside `R`. All four ran (MEASURED), the call charged `{R}`. FAILS under part 2.
#[test]
fn another_own_row_is_refused_at_a_bracket_holding_one() {
    for (arity, takes, applies) in ARITIES {
        for (spelling, body) in spellings(takes, "i(5)", "run[EffP = {R}](q, {cb})") {
            let ns = format!("wi450ka.other_row_{arity}_{spelling}");
            let src = bracketed(&ns, takes, applies, "R, Q", &body, "");
            assert_refused_naming(
                &load_errors_of(&src),
                &["type mismatch in run.f (op-arg)", "raises the row `?Q`"],
                &format!("a callback raising `Q` at a slot whose row is `{{R}}` ({arity}, {spelling})"),
            );
        }
    }
}

/// THE CONTROL OF THE TWO ROWS ABOVE: `h(5)`, row `R`, at `[EffP = {R}]`, and a pure callback
/// there. 45 and 41, no cell written. Passes either way by design.
#[test]
fn the_callers_own_row_fits_a_bracket_holding_it() {
    for (does, answer) in [("h(5)", 4512), ("41", 4112)] {
        for (arity, takes, applies) in ARITIES {
            for (spelling, body) in spellings(takes, does, "run[EffP = {R}](q, {cb})") {
                let ns = format!("wi450ka.fits_{arity}_{spelling}");
                let src = bracketed(&ns, takes, applies, "R", &body, "");
                assert_eq!(
                    run_int64(&src, &format!("{ns}.go")),
                    Ok(answer),
                    "`{does}` ({arity}, {spelling})"
                );
            }
        }
    }
}

/// … AND THE ROW SAID WHOLE: the bracket writes the labels beside `R`, `use` declares them,
/// `go` declares what reaches it. One callback that may raise, writes `q` — the cell `use`
/// names, not its own parameter — and raises `R`: it does not raise here, answers `h(5)` and
/// leaves 5 in the first cell — 4552. Passes either way by design.
#[test]
fn a_label_written_beside_the_callers_own_row_is_admitted() {
    let does = "if Cell.get(k) < 0 then Error.raise(\"boom\") else h(put(q, 5))";
    for (arity, takes, applies) in ARITIES {
        for (spelling, body) in
            spellings(takes, does, "run[EffP = {R, Error[String], Modify[q]}](q, {cb})")
        {
            let ns = format!("wi450ka.whole_{arity}_{spelling}");
            let src = bracketed(
                &ns,
                takes,
                applies,
                "R, Error[String], Modify[q]",
                &body,
                " effects {Error[String]}",
            );
            assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(4552), "{arity}, {spelling}");
        }
    }
}

/// A `Function[…]` SLOT AT THE SAME ROW: `f: Function[A = Cell[V = Int64], B = Int64, E =
/// EffP]` under `[EffP = {R}]`. The raising callback is refused — it raised out of a pure `go`
/// (MEASURED) — and `h(5)` runs. FAILS under part 2.
#[test]
fn a_function_slot_at_the_callers_own_row_admits_that_row_alone() {
    let run = "  operation run[EffP](p: Cell[V = Int64], f: Function[A = Cell[V = Int64], B = Int64, E = EffP]) -> Int64 effects {EffP} = f(p)";
    let takes = "k: Cell[V = Int64]";
    for (spelling, body) in spellings(takes, "Error.raise(\"boom\")", "run[EffP = {R}](q, {cb})") {
        let src = program(&format!("wi450ka.fn_boom_{spelling}"), run, "R", &body, "");
        assert_refused_naming(
            &load_errors_of(&src),
            &["type mismatch in run.f (op-arg)", "Error[T = String]"],
            &format!("a raising callback at a `Function` slot whose row is `{{R}}` ({spelling})"),
        );
    }
    for (spelling, body) in spellings(takes, "h(5)", "run[EffP = {R}](q, {cb})") {
        let ns = format!("wi450ka.fn_own_{spelling}");
        let src = program(&ns, run, "R", &body, "");
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(4512), "{spelling}");
    }
}

/// TWO CALLBACKS SHARING ONE ROW PARAMETER GIVE IT BOTH THEIR ROWS: `two[Rho](a: … @ {Rho}, b:
/// … @ {Rho})` at `h` (row `R`) and `i` (row `Q`) is `Rho = {R, Q}`, in either order — 41 + 72
/// and 71 + 42, no cell written: 11312, as the bracket `two[Rho = {R, Q}]` gives. A raising
/// callback beside `h` makes it `{Error[String], R}`, which `use` does not declare: refused at
/// `use`'s own effects, in either order.
///
/// It was the first argument that said the row (WI-20260820-RDNS4): `h` bound `Rho` to `R`, and
/// `i` and the raising lambda were refused at `b` — while `two(h, lambda … raise)` loaded and
/// raised out of a pure `go` before this ticket, and the same two arguments the other way round
/// were refused (MEASURED: the verdict turned on the order).
#[test]
fn a_row_two_callbacks_share_holds_both_of_the_callers_own_rows() {
    let two = "  operation two[Rho](a: (n: Int64) -> Int64 @ {Rho}, b: (n: Int64) -> Int64 @ {Rho}) -> Int64 effects {Rho} = a(1) + b(2)";
    let boom = "lambda (n: Int64) -> Error.raise(\"boom\")";
    for (tag, call) in [("h_boom", format!("two(h, {boom})")), ("boom_h", format!("two({boom}, h)"))] {
        let src = program(&format!("wi450ka.two_{tag}"), two, "R, Q", &format!("    {call}"), "");
        assert_refused_naming(
            &load_errors_of(&src),
            &["type mismatch in use.effects (op-effects)", "undeclared effect: Error[T = String]"],
            &format!("`{call}`"),
        );
    }
    for (tag, call) in [
        ("h_i", "two(h, i)"),
        ("i_h", "two(i, h)"),
        ("whole_h_i", "two[Rho = {R, Q}](h, i)"),
        ("whole_i_h", "two[Rho = {R, Q}](i, h)"),
    ] {
        let ns = format!("wi450ka.two_{tag}");
        let src = program(&ns, two, "R, Q", &format!("    {call}"), "");
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(11312), "`{call}`");
    }
}

/// `sort Strm { effects E = ? … }`, a receiver holding 1, and `go()` running `body` over one
/// typed pure.
fn stream_program(ns: &str, members: &str, rest: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Error}}
  operation run[EffP](p: Int64, f: (k: Int64) -> Int64 @ {{EffP}}) -> Int64 effects {{EffP}} = f(p)
  sort Each
    effects E = ?
    operation each(s: Self, f: (k: Int64) -> Int64 @ {{E}}) -> Int64 effects {{E}}
  end
  sort Strm
    effects E = ?
    entity strm(n: Int64)
{members}
  end
{rest}
  operation go() -> Int64 =
    let s: Strm[E = {{}}] = strm(n: 1)
    {body}
end
"#
    )
}

/// THE ROW PARAMETER IS THE SORT'S OWN: inside a member of `Strm`, `E` is as unknown as an
/// operation's `R`. `run[EffP = {E}](s.n, lambda … raise)` in a member declaring `{E}` loaded
/// and raised out of a pure `go` over a stream typed `E = {}` (MEASURED). Refused; the member
/// handing its own callback on answers `f(1) + 1`. FAILS under part 2.
#[test]
fn a_sorts_own_row_in_a_member_body_admits_that_row_alone() {
    let member = |does: &str| {
        format!(
            "    operation each(s: Self, f: (k: Int64) -> Int64 @ {{E}}) -> Int64 effects {{E}} =\n      run[EffP = {{E}}](s.n, lambda (k: Int64) -> {does})"
        )
    };
    let call = "Strm.each(s, lambda (k: Int64) -> k + 40)";
    let src = stream_program("wi450ka.member_boom", &member("Error.raise(\"boom\")"), "", call);
    assert_refused_naming(
        &load_errors_of(&src),
        &["type mismatch in run.f (op-arg)", "Error[T = String]"],
        "a raising callback at a slot whose row is the sort's own `E`",
    );
    let src = stream_program("wi450ka.member_own", &member("f(k) + 1"), "", call);
    assert_eq!(run_int64(&src, "wi450ka.member_own.go"), Ok(42));
}

/// THE CALL IS DISPATCHED: `Strm` provides `Each`, `use[R](s: Strm[E = {R}], …) effects {R}`
/// calls `each` on it — by dot, through the spec and through the sort — and the slot's `{E}` is
/// `{R}` by the receiver. A raising callback loaded in all three and raised out of a pure `go`
/// (MEASURED); `h(k)` answers 1 + 41. FAILS under part 2.
#[test]
fn a_dispatched_call_at_the_receivers_own_row_admits_that_row_alone() {
    let members = "    provides Each[E = E]\n    operation each(s: Self, f: (k: Int64) -> Int64 @ {E}) -> Int64 effects {E} = f(s.n)";
    let user = |call: &str| {
        format!(
            "  operation use[R](s: Strm[E = {{R}}], h: (n: Int64) -> Int64 @ {{R}}) -> Int64 effects {{R}} =\n    {call}"
        )
    };
    let go = "use(s, lambda (n: Int64) -> n + 41)";
    for (tag, receiver) in [("dot", "s.each("), ("spec", "Each.each(s, "), ("sort", "Strm.each(s, ")] {
        let boom = format!("{receiver}lambda (k: Int64) -> Error.raise(\"boom\"))");
        let src = stream_program(&format!("wi450ka.dispatch_boom_{tag}"), members, &user(&boom), go);
        assert_refused_naming(
            &load_errors_of(&src),
            &["type mismatch in each.f (op-arg)", "Error[T = String]"],
            &format!("a raising callback through `{receiver}…)`"),
        );
        let own = format!("{receiver}lambda (k: Int64) -> h(k))");
        let ns = format!("wi450ka.dispatch_own_{tag}");
        let src = stream_program(&ns, members, &user(&own), go);
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(42), "{tag}");
    }
}

/// WHAT THE REFUSAL SAYS: the slot, the row parameters its row is closed but for, and the
/// label. Two parameters where the row holds two. FAILS under part 2 (nothing is refused).
#[test]
fn the_refusal_names_the_row_and_what_it_admits() {
    let takes = "k: Cell[V = Int64]";
    let [(_, body), _] = spellings(takes, "Error.raise(\"boom\")", "run[EffP = {R}](q, {cb})");
    let src = bracketed("wi450ka.says_one", takes, "f(p)", "R", &body, "");
    assert_refused_naming(
        &load_errors_of(&src),
        &[
            "callback effects admitted by parameter `f` of `wi450ka.says_one.run`",
            "a row closed but for `?R`, the enclosing operation's own row, which admits only itself",
            "the lambda argument declares `Error[T = String]`, which that row does not admit",
        ],
        "one row parameter",
    );
    let [(_, body), _] = spellings(takes, "Error.raise(\"boom\")", "run[EffP = {R, Q}](q, {cb})");
    let src = bracketed("wi450ka.says_two", takes, "f(p)", "R, Q", &body, "");
    assert_refused_naming(
        &load_errors_of(&src),
        &[
            "a row closed but for `?",
            "`?R`",
            "`?Q`",
            "the enclosing operation's own rows, which admit only themselves",
        ],
        "two row parameters",
    );
}

//! FAMILY (c) — A CALLBACK'S EFFECT ROW: what a callback does, judged against the row its
//! slot writes (`kernel-language.md` §4.4, §5.5), by how the callback reaches the call.
//!
//! `run(p, f)` applies `f` to its cell `p` — and to a `5`, where the callback takes two —
//! its `f` typed at the `slot` hole's row. `use(q, r, h, i)` — two cells, and two callbacks at its own rows `R` and
//! `Q` — calls `run(q, <the callback>)`, and declares everything the call can incur, so
//! that what is judged is the slot. `go()` runs it over two fresh cells and returns the
//! result and both cells, `n * 100 + c * 10 + d`: a program the typer admits runs, and
//! the value says which cell was written.
//!
//! NOT PROGRAMS, and skipped ([`skips`]): a callback declared at the top level — an
//! operation, or the result of one — has no `r` and no `h` to name.
//!
//! ONE PROGRAM, TWO SPELLINGS (P4): a row holding one entry, braced and bare; a lambda
//! written at the call and the same lambda held in a `let`.

use super::{opt, spelt, Exception, Family, Hole, Picks, Program};

pub static FAMILY: Family = Family {
    name: "c-callback-row",
    rule: "a callback's effects against its slot's row, by how the callback reaches the call",
    holes: &[
        // The row `run`'s `f` writes after its arrow.
        Hole {
            name: "slot",
            options: &[
                opt("closed", ""),
                spelt("label", " @ {Error[String]}", "label"),
                spelt("label-bare", " @ Error[String]", "label"),
                spelt("open", " @ {EffP}", "open"),
                spelt("open-bare", " @ EffP", "open"),
                opt("open-lacks", " @ {EffP, -Modify[p]}"),
                opt("projected", " @ {s.E}"),
                // The one row that says a write to the cell the callback is handed.
                opt("own", " @ {Modify[k]}"),
                // That write, and a row parameter for whatever else the callback does.
                opt("own-open", " @ {Modify[k], EffP}"),
                // The slot's `{EffP}`, with the call's bracket saying it: the caller's own
                // row, which is rigid there, and two of them.
                opt("tail", " @ {EffP}"),
                opt("two-tails", " @ {EffP}"),
            ],
        },
        // How the callback reaches `run(q, …)`.
        Hole {
            name: "passed",
            options: &[
                opt("operation", "cb"),
                spelt("lambda", "", "lambda"),
                spelt("let", "g", "lambda"),
                opt("parameter", "g"),
                opt("tuple", "t._1"),
                opt("field", "b.g"),
                opt("result", "mk()"),
                opt("function", "g"),
            ],
        },
        // The callback's parameters: the cell `run` hands it, or that and an `Int64`.
        Hole {
            name: "takes",
            options: &[
                opt("cell", "k: Cell[V = Int64]"),
                opt("cell-and-int64", "k: Cell[V = Int64], u: Int64"),
            ],
        },
        // The callback's body.
        Hole {
            name: "does",
            options: &[
                opt("nothing", "41"),
                opt("raises", "if zero() < 0 then Error.raise(\"boom\") else 41"),
                opt("writes-own", "put(k, 5)"),
                opt("writes-scope", "put(r, 5)"),
                opt("raises-callers", "h(5)"),
            ],
        },
    ],
    render,
    skips: Some(skips),
    judge: super::judge_program,
    exceptions: EXCEPTIONS,
};

const EXCEPTIONS: &[Exception] = &[];

/// A callback declared at the top level names nothing of `use`'s.
fn skips(picks: &Picks<'_>) -> bool {
    (picks.is("passed", "operation") || picks.is("passed", "result"))
        && (picks.is("does", "writes-scope") || picks.is("does", "raises-callers"))
}

fn render(picks: &Picks<'_>) -> Program {
    let body = picks.text("does");
    let takes = picks.text("takes");
    let two = picks.is("takes", "cell-and-int64");
    let callback_type = format!("({takes}) -> Int64");
    let lambda = format!("lambda ({takes}) -> {body}");
    // The callback's own row, as a type written inside `use` says it — and, in braces,
    // as a binding of a row parameter there.
    let (row, bound) = match picks.label("does") {
        "nothing" => ("", "{}"),
        "raises" => (" @ {Error[String]}", "{Error[String]}"),
        "writes-own" => (" @ {Modify[k]}", "{}"),
        "writes-scope" => (" @ {Modify[r]}", "{Modify[r]}"),
        "raises-callers" => (" @ {R}", "{R}"),
        other => panic!("no does `{other}`"),
    };
    let writes_own = picks.is("does", "writes-own");

    let (type_parameters, run_effects, bracket) = match picks.label("slot") {
        "closed" => ("", "", ""),
        "label" | "label-bare" => ("", " effects {Error[String]}", ""),
        "open" | "open-bare" | "open-lacks" => ("[EffP]", " effects {EffP}", ""),
        "projected" => ("", " effects {s.E}", ""),
        "own" => ("", " effects {Modify[p]}", ""),
        "own-open" => ("[EffP]", " effects {Modify[p], EffP}", ""),
        "tail" => ("[EffP]", " effects {EffP}", "[EffP = {R}]"),
        "two-tails" => ("[EffP]", " effects {EffP}", "[EffP = {R, Q}]"),
        other => panic!("no slot `{other}`"),
    };
    let projected = picks.is("slot", "projected");
    let run = format!(
        "  operation run{type_parameters}({}p: Cell[V = Int64], f: {callback_type}{}) -> Int64{run_effects} = f(p{})\n",
        if projected { "s: Src, " } else { "" },
        picks.text("slot"),
        if two { ", 5" } else { "" },
    );

    // What stands above `use`, the parameter `use` takes beside its three, what `go`
    // passes for it, and the lines of `use` above its call.
    let (above, parameter, passes, held) = match picks.label("passed") {
        "operation" => (
            format!(
                "  operation cb({takes}) -> Int64{} = {body}\n",
                row.replace(" @ ", " effects ")
            ),
            String::new(),
            String::new(),
            String::new(),
        ),
        "lambda" => Default::default(),
        "let" => (String::new(), String::new(), String::new(), format!("    let g = {lambda}\n")),
        // What `use` passes on is `g` AT THE ROW ITS TYPE DECLARES — `{Modify[r]}`, `{R}` —
        // and that is what the slot judges. The lambda behind it is written in `go`,
        // where `use`'s `r` is the cell `d` and nothing has the row `R`: there it writes
        // `d`, and for `{R}` does nothing, `R` being `{}` at that call.
        "parameter" => (
            String::new(),
            format!(", g: {callback_type}{row}"),
            format!(
                ", lambda ({takes}) -> {}",
                match picks.label("does") {
                    "writes-scope" => "put(d, 5)",
                    "raises-callers" => "41",
                    _ => body,
                }
            ),
            String::new(),
        ),
        "tuple" => (String::new(), String::new(), String::new(), format!("    let t = ({lambda}, 1)\n")),
        "field" => (
            format!(
                "  sort Box\n    effects EB = ?\n    entity box(g: {callback_type} @ {{{}EB}})\n  end\n",
                if writes_own { "Modify[k], " } else { "" }
            ),
            String::new(),
            String::new(),
            format!("    let b: Box[EB = {bound}] = box(g: {lambda})\n"),
        ),
        "result" => (
            format!("  operation mk() -> {callback_type}{row} = {lambda}\n"),
            String::new(),
            String::new(),
            String::new(),
        ),
        // A `Function` type has no binder to name, so a callback writing its own
        // parameter leaves the row unwritten.
        "function" => (
            String::new(),
            String::new(),
            String::new(),
            format!(
                "    let g: Function[A = {}, B = Int64{}] = {lambda}\n",
                if two { "(Cell[V = Int64], Int64)" } else { "Cell[V = Int64]" },
                if writes_own {
                    String::new()
                } else {
                    format!(", E = {bound}")
                }
            ),
        ),
        other => panic!("no passed `{other}`"),
    };
    let callback = if picks.is("passed", "lambda") {
        lambda.as_str()
    } else {
        picks.text("passed")
    };
    // The row a projected slot reads off `s`: everything `use` declares.
    let (source_sort, source, source_argument) = if projected {
        (
            "  sort Src\n    effects E = ?\n    entity src(n: Int64)\n  end\n",
            "    let s: Src[E = {Modify[q], Modify[r], Error[String], R, Q}] = src(n: 0)\n",
            "s, ",
        )
    } else {
        ("", "", "")
    };
    Program {
        source: format!(
            r#"namespace family.c
  import anthill.prelude.{{Int64, Unit, String, List, Cell, Modify, Error, Function}}
  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n
  operation zero() -> Int64 = 0
{source_sort}{above}{run}  operation use[R, Q](q: Cell[V = Int64], r: Cell[V = Int64], h: (n: Int64) -> Int64 @ {{R}}, i: (n: Int64) -> Int64 @ {{Q}}{parameter}) -> Int64 effects {{Modify[q], Modify[r], Error[String], R, Q}} =
{source}{held}    run{bracket}({source_argument}q, {callback})
  operation go() -> Int64 effects {{Error[String]}} =
    let c: Cell[V = Int64] = Cell.new(1)
    let d: Cell[V = Int64] = Cell.new(2)
    let n = use(c, d, lambda (n: Int64) -> n, lambda (n: Int64) -> n{passes})
    n * 100 + Cell.get(c) * 10 + Cell.get(d)
end
"#
        ),
        entry: Some("family.c.go"),
        subject: None,
        refused: false,
    }
}

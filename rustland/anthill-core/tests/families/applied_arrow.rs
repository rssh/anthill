//! FAMILY (e) — A FUNCTION VALUE APPLIED: what a value of arrow type does to the cell it is
//! applied to, judged by where its type is written and how it is applied
//! (`kernel-language.md` §4.4, §5.5).
//!
//! `use(q, r, h)` — two cells, and a callback at its own row `R` — holds a function `w` over
//! a cell and applies it to `q`. `w`'s arrow may name its own parameter (`(z: Cell[V =
//! Int64]) -> Int64 @ {Modify[z]}`): applied to `q`, that write is a write to `q`, as an
//! operation's parameter is read at a call. `use` declares everything the application can
//! incur, or nothing at all, so a program that does something and declares nothing is the
//! control that the row reached `use` at all. `go()` runs `use` over two fresh cells and
//! returns the result and both cells, `n * 100 + c * 10 + d`: a program the typer admits
//! runs, and the value says which cell was written.
//!
//! The family [`super::callback_row`] passes a callback to a slot; this one APPLIES a value,
//! and moves where its type is written — a `let`, a parameter, an entity field, an
//! operation's result, a `Function` — around it.
//!
//! SOUNDNESS (P3): where `use` declares nothing, the template marks refused every program
//! whose application of `w` incurs something ([`Program::refused`], `incurs` in [`render`]) —
//! a second statement of the effect rule, the template's and not the typer's, so a program
//! the typer admits there is `UNSOUND …` whether or not another spelling of it is refused.
//!
//! NOT PROGRAMS, and skipped ([`skips`]): a row parameter where no declaration can bind one
//! (a `let`'s annotation, an operation's result, a value with no written arrow); an
//! operation's result or an entity field naming what only `use` has (`r`, `R`).
//!
//! ONE PROGRAM, THREE SPELLINGS (P4): the function held in a `let` unannotated, annotated at
//! the row its body has, and taken out of a tuple; applied as `w(q)`, through a `let` alias,
//! and handed to an operation whose slot is `w`'s own arrow, its parameter renamed (`apply(q,
//! w)`). Handed instead to a slot naming its parameter beside a row parameter (`applyOwn(q,
//! w)`, `@ {Modify[k], EA}`) is a program of its own: that slot says a write to the cell
//! whatever `w` does.

use super::{opt, spelt, Exception, Family, Hole, Picks, Program, Property};

pub static FAMILY: Family = Family {
    name: "e-applied-arrow",
    rule: "a function value applied to a cell, by where its arrow type is written and how it is applied",
    holes: &[
        // Where `w`'s type is written.
        Hole {
            name: "typed",
            options: &[
                spelt("unannotated", "", "held"),
                spelt("annotated", "", "held"),
                spelt("tuple", "", "held"),
                opt("parameter", ""),
                opt("field", ""),
                opt("result", ""),
                opt("function", ""),
            ],
        },
        // How the written arrow says what the body does: exactly; through a row parameter;
        // naming its own parameter beside a row parameter.
        Hole {
            name: "row",
            options: &[opt("exact", ""), opt("open", ""), opt("own-open", "")],
        },
        // How `use` applies `w` to `q`.
        Hole {
            name: "applied",
            options: &[
                spelt("call", "    w(q)", "applied"),
                spelt("alias", "    let v = w\n    v(q)", "applied"),
                spelt("slot", "    apply(q, w)", "applied"),
                // A slot naming its parameter beside a row parameter, whatever `w` does.
                opt("slot-own", "    applyOwn(q, w)"),
            ],
        },
        // `w`'s body.
        Hole {
            name: "does",
            options: &[
                opt("nothing", "41"),
                opt("raises", "if zero() < 0 then Error.raise(\"boom\") else 41"),
                opt("writes-own", "put(z, 5)"),
                opt("writes-scope", "put(r, 5)"),
                opt("raises-callers", "h(5)"),
            ],
        },
        // What `use` declares.
        Hole {
            name: "declares",
            options: &[
                opt("all", "Modify[q], Modify[r], Error[String], R"),
                opt("none", ""),
            ],
        },
    ],
    render,
    skips: Some(skips),
    judge: super::judge_program,
    exceptions: EXCEPTIONS,
};

const TICKET_7EZS6: &str = "WI-20261014-7EZS6";
const TICKET_6T5C6: &str = "WI-20261014-6T5C6";
const TICKET_EDPF6: &str = "WI-20261014-EDPF6";
const TICKET_N2YEK: &str = "WI-20261014-N2YEK";

const EXCEPTIONS: &[Exception] = &[
    // Applying a function value does not rename its own parameter to the argument: the
    // label left over is undeclared where the parameter is a lambda's. (Where it is a
    // callback parameter's it used to be DROPPED — a write to `q` in a `use` declaring
    // none; the boundary classifier now keeps a label on a callback read as a value on
    // every modifiable input, so those rows are refused and their exceptions are gone.)
    Exception {
        property: Property::OneVerdict,
        when: &["typed=unannotated", "does=writes-own", "applied=call"],
        ticket: TICKET_7EZS6,
        why: "a let-held lambda applied as `w(q)` writes `Modify[z]`, undeclared, where handed to a slot it is renamed",
    },
    Exception {
        property: Property::OneVerdict,
        when: &["typed=unannotated", "does=writes-own", "applied=alias"],
        ticket: TICKET_7EZS6,
        why: "a let-held lambda applied through an alias writes `Modify[z]`, undeclared",
    },
    Exception {
        property: Property::OneVerdict,
        when: &["typed=tuple", "does=writes-own", "applied=call"],
        ticket: TICKET_7EZS6,
        why: "a lambda out of a tuple applied as `w(q)` writes `Modify[z]`, undeclared",
    },
    Exception {
        property: Property::OneVerdict,
        when: &["typed=tuple", "does=writes-own", "applied=alias"],
        ticket: TICKET_7EZS6,
        why: "a lambda out of a tuple applied through an alias writes `Modify[z]`, undeclared",
    },
    // An arrow names its own parameter in its row only in an operation's parameter list.
    Exception {
        property: Property::OneVerdict,
        when: &["typed=annotated", "does=writes-own"],
        ticket: TICKET_6T5C6,
        why: "a `let` annotation's arrow cannot name its own parameter",
    },
    Exception {
        property: Property::OneVerdict,
        when: &["typed=result", "does=writes-own"],
        ticket: TICKET_6T5C6,
        why: "an operation result's arrow cannot name its own parameter, and the refusal's company differs by spelling",
    },
    // A lambda taken out of a tuple is not renamed where it meets a slot.
    Exception {
        property: Property::OneVerdict,
        when: &["typed=tuple", "does=writes-own", "applied=slot"],
        ticket: TICKET_EDPF6,
        why: "a lambda out of a tuple is refused at a slot naming its parameter",
    },
    Exception {
        property: Property::OneVerdict,
        when: &["typed=tuple", "does=writes-own", "applied=slot-own"],
        ticket: TICKET_EDPF6,
        why: "a lambda out of a tuple is refused at a slot naming its parameter",
    },
    // A field's row parameter bound to nothing takes a lambda writing its own parameter.
    Exception {
        property: Property::Sound,
        when: &["typed=field", "row=open", "does=writes-own"],
        ticket: TICKET_N2YEK,
        why: "`Box[EB = {}]` admits a lambda writing its own parameter, and applying it writes `q`",
    },
];

fn skips(picks: &Picks<'_>) -> bool {
    let names_use = picks.is("does", "writes-scope") || picks.is("does", "raises-callers");
    // A row parameter needs a declaration to bind it: `use`'s own, or the field's sort.
    (!picks.is("row", "exact") && !(picks.is("typed", "parameter") || picks.is("typed", "field")))
        // A top-level operation names nothing of `use`'s, and neither does a field written
        // without a row parameter.
        || (picks.is("typed", "result") && names_use)
        || (picks.is("typed", "field") && picks.is("row", "exact") && names_use)
}

fn render(picks: &Picks<'_>) -> Program {
    let body = picks.text("does");
    let arrow = "(z: Cell[V = Int64]) -> Int64";
    let lambda = format!("lambda (z: Cell[V = Int64]) -> {body}");
    // The body's row as a type written inside `use` says it, and — in braces — as a binding
    // of a row parameter, which cannot name the function's own parameter.
    let (exact, bound) = match picks.label("does") {
        "nothing" => ("", "{}"),
        "raises" => (" @ {Error[String]}", "{Error[String]}"),
        "writes-own" => (" @ {Modify[z]}", "{}"),
        "writes-scope" => (" @ {Modify[r]}", "{Modify[r]}"),
        "raises-callers" => (" @ {R}", "{R}"),
        other => panic!("no does `{other}`"),
    };
    // The row the arrow writes, at a declaration with a row parameter named `tail`.
    let written = |tail: &str| match picks.label("row") {
        "exact" => exact.to_string(),
        "open" => format!(" @ {{{tail}}}"),
        "own-open" => format!(" @ {{Modify[z], {tail}}}"),
        other => panic!("no row `{other}`"),
    };
    let open = !picks.is("row", "exact");

    // What stands above `use`, `use`'s own row parameter and the parameter it takes beside
    // its three, what `go` passes for it, and the lines of `use` above the application.
    let mut above = String::new();
    let mut row_parameter = "";
    let mut parameter = String::new();
    let mut passes = String::new();
    let held = match picks.label("typed") {
        "unannotated" => format!("    let w = {lambda}\n"),
        "annotated" => format!("    let w: {arrow}{exact} = {lambda}\n"),
        "tuple" => format!("    let t = ({lambda}, 1)\n    let w = t._1\n"),
        // The lambda behind the parameter is written in `go`, where `use`'s `r` is the cell
        // `d` and nothing has the row `R`: there it writes `d`, and for `{R}` does nothing.
        "parameter" => {
            if open {
                row_parameter = ", EW";
            }
            parameter = format!(", w: {arrow}{}", written("EW"));
            passes = format!(
                ", lambda (z: Cell[V = Int64]) -> {}",
                match picks.label("does") {
                    "writes-scope" => "put(d, 5)",
                    "raises-callers" => "41",
                    _ => body,
                }
            );
            String::new()
        }
        "field" => {
            above = format!(
                "  sort Box\n{}    entity box(g: {arrow}{})\n  end\n",
                if open { "    effects EB = ?\n" } else { "" },
                written("EB"),
            );
            let annotation = if open { format!(": Box[EB = {bound}]") } else { String::new() };
            format!("    let b{annotation} = box(g: {lambda})\n    let w = b.g\n")
        }
        "result" => {
            above = format!("  operation mk() -> {arrow}{exact} = {lambda}\n");
            "    let w = mk()\n".to_string()
        }
        // A `Function` type has no parameter to name, so a function writing its own
        // parameter leaves the row unwritten.
        "function" => format!(
            "    let w: Function[A = Cell[V = Int64], B = Int64{}] = {lambda}\n",
            if picks.is("does", "writes-own") { String::new() } else { format!(", E = {bound}") }
        ),
        other => panic!("no typed `{other}`"),
    };
    // `apply`: a slot at `w`'s own arrow, its parameter renamed and what only `use` names
    // left to a row parameter, so that handing `w` to it is applying `w`.
    let (apply_parameters, apply_row, apply_effects) = match (picks.label("row"), picks.label("does")) {
        ("open", _) | ("exact", "writes-scope" | "raises-callers") => ("[EA]", " @ {EA}", " effects {EA}"),
        ("own-open", _) => ("[EA]", " @ {Modify[k], EA}", " effects {Modify[p], EA}"),
        ("exact", "nothing") => ("", "", ""),
        ("exact", "raises") => ("", " @ {Error[String]}", " effects {Error[String]}"),
        ("exact", "writes-own") => ("", " @ {Modify[k]}", " effects {Modify[p]}"),
        other => panic!("no apply for {other:?}"),
    };
    let apply = format!(
        "  operation apply{apply_parameters}(p: Cell[V = Int64], f: (k: Cell[V = Int64]) -> Int64{apply_row}) -> Int64{apply_effects} = f(p)\n"
    );
    let declares = [picks.text("declares"), if row_parameter.is_empty() { "" } else { "EW" }]
        .into_iter()
        .filter(|s| !s.is_empty())
        .collect::<Vec<_>>()
        .join(", ");
    let effects = if declares.is_empty() { String::new() } else { format!(" effects {{{declares}}}") };
    // Where `use` declares nothing, the rule refuses every program whose application of `w`
    // incurs something: a slot naming its parameter says a write to `q`, and so does an arrow
    // naming its own; an open row at `use`'s own parameter is `EW`, which `use` declares, and
    // at the field it is bound to what the body does; any other row says what the body does.
    let incurs = picks.is("applied", "slot-own")
        || picks.is("row", "own-open")
        || match picks.label("row") {
            "open" => picks.is("typed", "field") && !picks.is("does", "nothing"),
            _ => !picks.is("does", "nothing"),
        };
    let refused = picks.is("declares", "none") && incurs;
    Program {
        source: format!(
            r#"namespace family.e
  import anthill.prelude.{{Int64, Unit, String, List, Cell, Modify, Error, Function}}
  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n
  operation zero() -> Int64 = 0
  operation applyOwn[EA](p: Cell[V = Int64], f: (k: Cell[V = Int64]) -> Int64 @ {{Modify[k], EA}}) -> Int64 effects {{Modify[p], EA}} = f(p)
{apply}{above}  operation use[R{row_parameter}](q: Cell[V = Int64], r: Cell[V = Int64], h: (n: Int64) -> Int64 @ {{R}}{parameter}) -> Int64{effects} =
{held}{applied}
  operation go() -> Int64 effects {{Error[String]}} =
    let c: Cell[V = Int64] = Cell.new(1)
    let d: Cell[V = Int64] = Cell.new(2)
    let n = use(c, d, lambda (n: Int64) -> n{passes})
    n * 100 + Cell.get(c) * 10 + Cell.get(d)
end
"#,
            applied = picks.text("applied"),
        ),
        entry: Some("family.e.go"),
        subject: None,
        refused,
    }
}

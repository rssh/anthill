//! FAMILY (f) — WHO SUPPLIES A CALL: which implementation runs a call of a spec operation
//! at a carrier, by what supplies it and by the route the call takes (`kernel-language.md`
//! §8.7, *Operation override*, *Backing is executable*, *One carrier declaring one spec
//! twice*; the map is `docs/design/supplier-question-map.md`).
//!
//! `Desc` declares one operation — `describe(x: T)`, which hands the carrier a value, or
//! `name()`, where only a bracket names it — with a default body (`= 1`) or without. `Leaf`
//! is supplied by one of seven configurations: nothing but the default, its own member
//! (`= 2`), an instance binding (`= 3`) written in its body, in a `namespace Leaf` entry or
//! beside a bare provision in its body, a witness sort's member (`= 4`), or its own member
//! beside a binding. `go()` returns the call's value.
//!
//! ONE PROGRAM, FOUR SPELLINGS (P4): the call by name, the dot, through a `requires`
//! dictionary (`gen(leaf())`), and through a receiver typed by a spec `Leaf` provides
//! (`viaShape(leaf())`). Every program carries all of them as declarations and differs
//! only in `go`'s call, and the file without `go` is the [`Program::subject`]: a refusal of
//! the declarations is one verdict for every route, and a refusal of the call is the
//! route's own. The rule-body route is proposal 068's and is not here.
//!
//! NOT PROGRAMS, and skipped ([`skips`]): the dot and the receiver spellings of `name()`,
//! which takes no receiver.
//!
//! SOUNDNESS (P3): the rule refuses two suppliers for one carrier, and a body-less
//! operation nothing supplies ([`Program::refused`]). A refusal the rule does not make is
//! no property's to see, and the verdict file holds it: the body-less `binding-both` was
//! one until WI-20261025-7K84M, where §8.7 merges the two provisions and the backing check
//! read one.
//!
//! A TIE IS ONE VERDICT WHERE §8.7 LETS THE ROUTE CHOOSE WHEN ([`judge`]): two suppliers are
//! refused at load where the carrier is static and at the call where only a value names it.
//! The receiver spelling is the one route where only a value names it, so its refusal when
//! the call runs is read as the call refused; on every other route a tie that reaches the
//! run is a P3 violation, as any program that loads and does not run is. Through a
//! dictionary the carrier is static where the dictionary is built, `gen(leaf())`, and the
//! tie is refused there (the user, 2026-10-25).
//!
//! NO EXCEPTIONS since WI-20261025-7K84M (`resolve_op_target_at`, `resolve_at_goal`'s
//! projection, the backing check's merged view and the construction's tie, one answer for
//! both halves), which took off the nine it listed, moving thirteen verdicts. CONTROL, measured
//! there: run with [`judge`] as plain `judge_program`, the family names both `own+binding` rows
//! of the receiving shape and nothing else — their receiver spelling against P2 and P3, and the
//! row against P4. Each of 7K84M's four parts backed out alone moves verdicts of this family
//! (`wi_7k84m_one_supplier_answer_test`'s header). It saw WI-20261025-ZAWX9's delivery
//! (`3657c39d`) too, which landed while it was being written: five verdicts moved, and the
//! three exceptions listed for ZAWX9 excused nothing.

use super::{opt, spelt, Exception, Family, Hole, Picks, Program, Verdict};

pub static FAMILY: Family = Family {
    name: "f-supplier-routes",
    rule: "the implementation a spec-operation call runs, by what supplies it and the route the call takes",
    holes: &[
        Hole {
            name: "shape",
            options: &[opt("receiver", ""), opt("nullary", "")],
        },
        Hole {
            name: "default",
            options: &[opt("defaulted", " = 1"), opt("body-less", "")],
        },
        Hole {
            name: "supplied",
            options: &[
                opt("default-only", ""),
                opt("own", ""),
                opt("binding-in-body", ""),
                opt("binding-in-entry", ""),
                opt("binding-both", ""),
                opt("witness-only", ""),
                opt("own+binding", ""),
            ],
        },
        Hole {
            name: "route",
            options: &[
                spelt("by-name", "", "call"),
                spelt("dot", "", "call"),
                spelt("dictionary", "", "call"),
                spelt("receiver", "", "call"),
            ],
        },
    ],
    render,
    skips: Some(skips),
    judge,
    exceptions: EXCEPTIONS,
};

const EXCEPTIONS: &[Exception] = &[];

/// The receiver spelling's call: the one route where only the value names the carrier.
const RECEIVER_CALL: &str = "viaShape(leaf())";

/// [`super::judge_program`], with the receiver spelling's tie refused when the call runs read
/// as the call refused, as the other routes refuse it at load (§8.7).
fn judge(program: &Program) -> Verdict {
    const TIE: &str = "AmbiguousSpecOpDispatch";
    let receiver = program.source.contains(&format!("go() -> Int64 = {RECEIVER_CALL}\n"));
    match super::judge_program(program) {
        Verdict::DriveFails(class) if receiver && class == TIE => Verdict::DriveRefused(class),
        verdict => verdict,
    }
}

fn skips(picks: &Picks<'_>) -> bool {
    picks.is("shape", "nullary") && (picks.is("route", "dot") || picks.is("route", "receiver"))
}

fn render(picks: &Picks<'_>) -> Program {
    let nullary = picks.is("shape", "nullary");
    let (op, sig, own_sig) = if nullary { ("name", "()", "()") } else { ("describe", "(x: T)", "(x: Leaf)") };
    let default = picks.text("default");
    let own = format!("    operation {op}{own_sig} -> Int64 = 2\n");
    let other = format!("  operation other{own_sig} -> Int64 = 3\n");
    let entry_binding = format!("  namespace Leaf\n    provides Desc[T = Leaf, {op} = other]\n  end\n");
    let bare = "    provides Desc[T = Leaf]\n".to_string();
    let (in_leaf, after_leaf) = match picks.label("supplied") {
        "default-only" => (bare, String::new()),
        "own" => (format!("{bare}{own}"), String::new()),
        "binding-in-body" => (format!("    provides Desc[T = Leaf, {op} = other]\n"), other),
        "binding-in-entry" => (String::new(), format!("{other}{entry_binding}")),
        "binding-both" => (bare, format!("{other}{entry_binding}")),
        "witness-only" => (
            String::new(),
            format!("  sort W\n    provides Desc[T = Leaf]\n    operation {op}{own_sig} -> Int64 = 4\n  end\n"),
        ),
        "own+binding" => (format!("{bare}{own}"), format!("{other}{entry_binding}")),
        other => panic!("no supplied `{other}`"),
    };
    let routes = if nullary {
        "  operation gen[A]() -> Int64 requires Desc[T = A] = Desc.name[T = A]()\n".to_string()
    } else {
        "  operation gen[A](x: A) -> Int64 requires Desc[T = A] = Desc.describe(x)\n  \
         operation viaShape(s: Shape) -> Int64 = Desc.describe(s)\n"
            .to_string()
    };
    let call = match (nullary, picks.label("route")) {
        (true, "by-name") => "Desc.name[T = Leaf]()",
        (true, "dictionary") => "gen[A = Leaf]()",
        (false, "by-name") => "Desc.describe(leaf())",
        (false, "dot") => "leaf().describe()",
        (false, "dictionary") => "gen(leaf())",
        (false, "receiver") => RECEIVER_CALL,
        other => panic!("no route {other:?}"),
    };
    let declarations = format!(
        r#"namespace family.f
  import anthill.prelude.{{Int64}}
  sort Shape
    sort E = ?
  end
  sort Desc
    sort T = ?
    operation {op}{sig} -> Int64{default}
  end
  sort Leaf
    entity leaf
    provides Shape[E = Int64]
{in_leaf}  end
{after_leaf}{routes}"#
    );
    // Two suppliers are a tie, and a body-less operation nothing supplies backs nothing.
    let refused = picks.is("supplied", "own+binding")
        || (picks.is("default", "body-less") && picks.is("supplied", "default-only"));
    Program {
        source: format!("{declarations}  operation go() -> Int64 = {call}\nend\n"),
        entry: Some("family.f.go"),
        subject: Some(format!("{declarations}end\n")),
        refused,
    }
}

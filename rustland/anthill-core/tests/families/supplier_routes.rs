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
//! ONE PROGRAM, THREE SPELLINGS (P4): the call by name, the dot, and through a `requires`
//! dictionary (`gen(leaf())`). Every program carries all of them as declarations and differs
//! only in `go`'s call, and the file without `go` is the [`Program::subject`]: a refusal of
//! the declarations is one verdict for every route, and a refusal of the call is the
//! route's own. The rule-body route is proposal 068's and is not here.
//!
//! A RECEIVER TYPED BY A SPEC `Leaf` PROVIDES IS NO SPELLING (proposal 073 §2): in
//! `viaShape(s: Shape) -> Int64 = Desc.describe(s)` the value is an instance of `Shape`, and
//! the call is one at `Shape` — its default, or refused at load without one, whoever supplies
//! `Leaf`. It was the fourth spelling while the run time dispatched it on the value, and is
//! `wi1010_defaulted_op_instance_fact_test`'s and `wi1012_static_supplier_tie_test`'s now.
//!
//! NOT PROGRAMS, and skipped ([`skips`]): the dot spelling of `name()`, which takes no
//! receiver.
//!
//! SOUNDNESS (P3): the rule refuses two suppliers for one carrier, and a body-less
//! operation nothing supplies ([`Program::refused`]). A refusal the rule does not make is
//! no property's to see, and the verdict file holds it: the body-less `binding-both` was
//! one until WI-20261025-7K84M, where §8.7 merges the two provisions and the backing check
//! read one.
//!
//! A TIE IS REFUSED AT LOAD on every route: the carrier is static at each, and through a
//! dictionary where the dictionary is built, `gen(leaf())` (the user, 2026-10-25). A tie that
//! reaches the run is a P3 violation, as any program that loads and does not run is.
//!
//! NO EXCEPTIONS since WI-20261025-7K84M (`resolve_op_target_at`, `resolve_at_goal`'s
//! projection, the backing check's merged view and the construction's tie, one answer for
//! both halves), which took off the nine it listed, moving thirteen verdicts. Each of 7K84M's
//! four parts backed out alone moves verdicts of this family
//! (`wi_7k84m_one_supplier_answer_test`'s header). It saw WI-20261025-ZAWX9's delivery
//! (`3657c39d`) too, which landed while it was being written: five verdicts moved, and the
//! three exceptions listed for ZAWX9 excused nothing.

use super::{opt, spelt, Exception, Family, Hole, Picks, Program};

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
            ],
        },
    ],
    render,
    skips: Some(skips),
    judge: super::judge_program,
    exceptions: EXCEPTIONS,
};

const EXCEPTIONS: &[Exception] = &[];

fn skips(picks: &Picks<'_>) -> bool {
    picks.is("shape", "nullary") && picks.is("route", "dot")
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
        "  operation gen[A](x: A) -> Int64 requires Desc[T = A] = Desc.describe(x)\n".to_string()
    };
    let call = match (nullary, picks.label("route")) {
        (true, "by-name") => "Desc.name[T = Leaf]()",
        (true, "dictionary") => "gen[A = Leaf]()",
        (false, "by-name") => "Desc.describe(leaf())",
        (false, "dot") => "leaf().describe()",
        (false, "dictionary") => "gen(leaf())",
        other => panic!("no route {other:?}"),
    };
    let declarations = format!(
        r#"namespace family.f
  import anthill.prelude.{{Int64}}
  sort Desc
    sort T = ?
    operation {op}{sig} -> Int64{default}
  end
  sort Leaf
    entity leaf
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

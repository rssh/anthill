//! FAMILY (d) — TWO CALLBACKS TYPED BY EACH OTHER: `two[A, B](f: (x: A) -> B, g: (y: B)
//! -> A)`, where what one lambda returns is what the other takes.
//!
//! It is here for ONE program and the three around it. With each lambda returning a list
//! of its parameter the call binds `B` to a list of `A` and `A` to a list of `B`; the
//! unifier's occurs check reads a binding as written, the substitution holds a cycle, and
//! the loader overflows its stack (WI-20261003-KQ6DG). That is the family's listed
//! exception to P1 — and, on every run, the control that a program which kills its
//! process is named and the run goes on, driven by the typer and not by a planted fault.
//! The same lambdas held in a `let` load, and so does a cycle through one list that the
//! call refuses: the family's exceptions to P4, the same ticket's. When it lands the
//! exceptions excuse nothing, the run says so, and they go.

use super::{opt, spelt, Exception, Family, Hole, Picks, Program, Property};

pub static FAMILY: Family = Family {
    name: "d-mutual-callbacks",
    rule: "two callbacks each typed by what the other returns, at a call",
    holes: &[
        Hole {
            name: "first",
            options: &[opt("x", "x"), opt("list-x", "[x]")],
        },
        Hole {
            name: "second",
            options: &[opt("y", "y"), opt("list-y", "[y]")],
        },
        Hole {
            name: "passed",
            options: &[spelt("lambda", "", "lambda"), spelt("let", "", "lambda")],
        },
    ],
    render,
    skips: None,
    judge: super::judge_program,
    exceptions: EXCEPTIONS,
};

/// All three are WI-20261003-KQ6DG's, whose note of 2026-10-13 has the programs.
const EXCEPTIONS: &[Exception] = &[
    Exception {
        property: Property::NoCrash,
        when: &["first=list-x", "second=list-y", "passed=lambda"],
        ticket: "WI-20261003-KQ6DG",
        why: "the call binds each type parameter inside the other, and every deep reader of the substitution recurses through the cycle",
    },
    // The lambdas held in a `let`: the call that is refused, or dies, where they are
    // written at it loads and runs.
    Exception {
        property: Property::OneVerdict,
        when: &["first=list-x", "passed=let"],
        ticket: "WI-20261003-KQ6DG",
        why: "a cycle the call refuses is admitted from a `let`",
    },
    Exception {
        property: Property::OneVerdict,
        when: &["second=list-y", "passed=let"],
        ticket: "WI-20261003-KQ6DG",
        why: "a cycle the call refuses is admitted from a `let`",
    },
];

fn render(picks: &Picks<'_>) -> Program {
    let first = format!("lambda (x) -> {}", picks.text("first"));
    let second = format!("lambda (y) -> {}", picks.text("second"));
    let call = if picks.is("passed", "lambda") {
        format!("    two({first}, {second})")
    } else {
        format!("    let f = {first}\n    let g = {second}\n    two(f, g)")
    };
    Program {
        source: format!(
            "namespace family.d\n  import anthill.prelude.{{Int64, List}}\n  operation two[A, B](f: (x: A) -> B, g: (y: B) -> A) -> Int64 = 1\n  operation go() -> Int64 =\n{call}\nend\n"
        ),
        entry: Some("family.d.go"),
        subject: None,
    }
}

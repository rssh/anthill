//! FAMILY (d) — TWO CALLBACKS TYPED BY EACH OTHER: `two[A, B](f: (x: A) -> B, g: (y: B)
//! -> A)`, where what one lambda returns is what the other takes.
//!
//! It is here for ONE program and the three around it. With each lambda returning a list
//! of its parameter the call binds `B` to a list of `A` and `A` to a list of `B`: no finite
//! type solves it, and the unifier's occurs check, which reads a binding through σ, refuses
//! the binding at `g` that closes the cycle (WI-20261003-KQ6DG). Before it read a binding as
//! written, σ held the cycle and the loader overflowed its stack — the family's exception to
//! P1 then. A cycle through one list (`[x]` beside `y`, `x` beside `[y]`) is refused alike,
//! and so is each program with its lambdas held in `let`s, which loaded while the check read
//! as written: one verdict for the two spellings of each pair. The two identities leave `A`
//! unconstrained, in both spellings.

use super::{opt, spelt, Exception, Family, Hole, Picks, Program};

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

const EXCEPTIONS: &[Exception] = &[];

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
        refused: false,
    }
}

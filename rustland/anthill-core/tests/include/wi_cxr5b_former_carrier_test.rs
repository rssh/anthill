//! WI-20261122-CXR5B — A FUNCTION-TYPED CARRIER, BY DECISION 1 (`docs/design/spec-carrier-set.md`).
//!
//! `Ap[F, R] { run(f: F, r: R); only(f: F) }` with providers at `F = (Int64) -> Int64` (and, for
//! two, `(String) -> Int64`), `R = Foo`. The readers of what a call fixes read SORT carriers: a
//! lambda at `F` fixed nothing they could see. So which type-var is declared first decided the
//! verdict — measured over a grid of 32 programs (`sweep/gen_former.py`):
//!   * with `R` first, the provision the receiver classification read first bound `F` before the
//!     lambda argument was typed: `Ap.run(lambda x -> 1, foo)` beside two providers apart in `F`
//!     ran the first, and `Ap.run(lambda (x: String) -> 7, foo)` was refused against its `F`;
//!   * with no sort carrier at all (`F` first, or `only` taking no `R`), nothing read `R` off a
//!     provision: the goal left it out and no provision answered, so `Ap.only(lambda (x: Int64)
//!     -> x + 1)` beside its one provider was refused in both orders.
//! Now what the provisions at the carrier write apart is left for the arguments to fix
//! (`written_alike_at_carrier`), and a call holding no sort carrier with a tuple or an arrow at a
//! type-var reads what it leaves free off the provisions at what it fixes
//! (`read_provisions_at_former_call`), refused where they write it apart.
//!
//! WHAT FAILS IF THIS IS BACKED OUT, and what passes either way, is said at each row. MEASURED
//! 2026-11-23, with `src/` backed out: the three rows marked FAILS fail, the control passes. Each
//! half alone: without `written_alike_at_carrier` the typed-lambda and open rows fail; without
//! `read_provisions_at_former_call`, all three.

use crate::common::{interp_for, load_errors_of};

const ONE: &str = r#"  sort W
    provides Ap[F = (Int64) -> Int64, R = Foo]
    operation run(f: (Int64) -> Int64, r: Foo) -> Int64 = f(41)
    operation only(f: (Int64) -> Int64) -> Int64 = f(1)
  end"#;

const TWO: &str = r#"  sort W1
    provides Ap[F = (Int64) -> Int64, R = Foo]
    operation run(f: (Int64) -> Int64, r: Foo) -> Int64 = f(41)
    operation only(f: (Int64) -> Int64) -> Int64 = f(1)
  end
  sort W2
    provides Ap[F = (String) -> Int64, R = Foo]
    operation run(f: (String) -> Int64, r: Foo) -> Int64 = f("s") + 100
    operation only(f: (String) -> Int64) -> Int64 = f("t") + 100
  end"#;

/// `Ap[F, R]` (with `R` first where `r_first`), `Foo`, the providers `provs` and a driver `go`.
fn program(ns: &str, r_first: bool, provs: &str, body: &str) -> String {
    let (x, y) = if r_first { ("R", "F") } else { ("F", "R") };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Ap
    sort {x} = ?
    sort {y} = ?
    operation run(f: F, r: R) -> Int64
    operation only(f: F) -> Int64
  end
  sort Foo
    entity foo
  end
{provs}
  sort Driver
    operation go() -> Int64 = {body}
  end
end
"#
    )
}

fn orders() -> [(&'static str, bool); 2] {
    [("ffirst", false), ("rfirst", true)]
}

fn go(src: &str, ns: &str) -> Result<i64, String> {
    match interp_for(src).call(&format!("{ns}.Driver.go"), &anthill_core::eval::HostValue::all(&[])).map(|h| h.value) {
        Ok(anthill_core::eval::Value::Int(n)) => Ok(n),
        other => Err(format!("{other:?}")),
    }
}

/// Beside ONE provider a lambda reads what it leaves free off it, in either order: `R` for
/// `only`, the unstated parameter for `run`. FAILS backed out: `only` refused in both orders,
/// `run(lambda x -> 1, foo)` refused with `F` first.
#[test]
fn a_lambda_beside_one_provision_reads_the_rest_off_it() {
    for (order, r_first) in orders() {
        for (shape, body, want) in [
            ("only_typed", "Ap.only(lambda (x: Int64) -> x + 1)", 2),
            ("only_unsaid", "Ap.only(lambda x -> 5)", 5),
            ("run_unsaid", "Ap.run(lambda x -> 1, foo)", 1),
        ] {
            let ns = format!("wicxr5bfc.one.{shape}.{order}");
            assert_eq!(go(&program(&ns, r_first, ONE, body), &ns), Ok(want), "{ns}");
        }
    }
}

/// Beside two providers apart in `F`, a lambda stating its type reads the provision it fits, in
/// either order. FAILS backed out: with `R` first `run` was refused against `W1`'s `F`, and
/// `only` was refused in both orders.
#[test]
fn a_typed_lambda_reads_the_provision_it_fits() {
    for (order, r_first) in orders() {
        for (shape, body, want) in [
            ("run", "Ap.run(lambda (x: String) -> 7, foo)", 107),
            ("only", "Ap.only(lambda (x: Int64) -> x + 1)", 2),
        ] {
            let ns = format!("wicxr5bfc.two.{shape}.{order}");
            assert_eq!(go(&program(&ns, r_first, TWO, body), &ns), Ok(want), "{ns}");
        }
    }
}

/// Beside two providers apart in `F`, a lambda stating no type fits both, and the call leaves `F`
/// open: refused in either order, naming it. FAILS backed out: with `R` first `run` ANSWERED 1,
/// the first provider's — the first match decision 1 refuses.
#[test]
fn a_lambda_fitting_two_provisions_leaves_its_type_open() {
    for (order, r_first) in orders() {
        for (shape, body) in [("run", "Ap.run(lambda x -> 1, foo)"), ("only", "Ap.only(lambda x -> 5)")] {
            let ns = format!("wicxr5bfc.open.{shape}.{order}");
            let text = load_errors_of(&program(&ns, r_first, TWO, body)).join("\n");
            assert!(text.contains("it leaves `F` open"), "`{ns}`:\n{text}");
        }
    }
}

/// CONTROL: a lambda stating the one provision's type, and a bracket naming the instance, answer
/// in either order. Passes either way, by design.
#[test]
fn a_lambda_at_its_provision_and_a_bracket_answer_in_either_order() {
    for (order, r_first) in orders() {
        for (provs, shape, body, want) in [
            (ONE, "typed", "Ap.run(lambda (x: Int64) -> x + 1, foo)", 42),
            (TWO, "bracket", "Ap[F = (Int64) -> Int64].run(lambda x -> x + 1, foo)", 42),
        ] {
            let ns = format!("wicxr5bfc.ctl.{shape}.{order}");
            assert_eq!(go(&program(&ns, r_first, provs, body), &ns), Ok(want), "{ns}");
        }
    }
}

/// A GENERIC rival provision meets a lambda too: `G[X] provides Ap[F = (X) -> X, R = Bar]` beside
/// `W` at `R = Foo` meets `Ap.only(lambda (x: Int64) -> x + 1)` at `X = Int64`, so the call leaves
/// `R` open between them — refused naming both, in either order. FAILS backed out (two other
/// refusals by order), and with this step's first cut, which gave the reading up beside any
/// generic provision of the spec (found by /code-review).
#[test]
fn a_generic_provision_meeting_the_call_is_read_as_any_other() {
    let generic = format!(
        "{ONE}\n  sort Bar\n    entity bar\n  end\n  sort G\n    sort X = ?\n    entity g(x: X)\n    \
         provides Ap[F = (X) -> X, R = Bar]\n    operation run(f: (X) -> X, r: Bar) -> Int64 = 9\n    \
         operation only(f: (X) -> X) -> Int64 = 9\n  end"
    );
    for (order, r_first) in orders() {
        let ns = format!("wicxr5bfc.generic.{order}");
        let text = load_errors_of(&program(&ns, r_first, &generic, "Ap.only(lambda (x: Int64) -> x + 1)")).join("\n");
        assert!(text.contains("it leaves `R` open"), "`{ns}`:\n{text}");
        assert!(text.contains(&format!("`{ns}.W`")) && text.contains(&format!("`{ns}.G`")), "`{ns}`:\n{text}");
    }
}

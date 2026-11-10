//! WI-20260926-Y6ZCD — a call to a spec operation whose carriers stand at several of its
//! parameters is answered at all of them, in an operation body as in a rule body.
//!
//! `Conv[A, B]`'s `conv(a: A, b: B)` with one provision, `W provides Conv[A = Leaf, B =
//! Int64]`. Before, an operation body's `Conv.conv(leaf(v: 1), "s")` loaded and answered `W.conv`
//! with a `String` in its `Int64` parameter. The dispatch found no candidate at `(Leaf,
//! String)`, the refusal on that miss asked whether `Leaf` provides `Conv` by any route, which
//! `W`'s provision says it does, and the call was passed to the run time, which dispatched on
//! the value at `A` alone. The rule-body twin was refused since WI-20260925-PRVA2 (c): "no
//! provision of `Conv` binds `A = Leaf, B = String`". Now the operation body asks the same
//! question through the same core (`carriers_no_provision_binds`, `simp_guard_decision`).
//!
//! The DEFAULTED operation had the same hole by another path, in both bodies: its suppliers
//! are found by the carrier at `A` (`carrier_override_suppliers`), and a witness's member, or
//! the carrier's own member, answered a call at bindings its provision does not have. Now a
//! supplier answers only where its provision binds the call's carriers (`supplier_answers_at`),
//! asked by the typer and by the interpreter's carrier override.
//!
//! BACKED OUT, MEASURED one part at a time in one build: the operation-body refusal fails the
//! rows marked BODY-LESS; the typer's supplier filter fails the rows marked TYPER; the
//! interpreter's fails the rows marked EVAL. The rows marked CONTROL pass either way, by design.

use crate::common::{
    assert_refused_naming, load_errors_of, load_kb_with, one_definite_int, run_int64,
};

/// The spec — `conv` body-less, or with a body when `defaulted` — a constructor sort, and
/// `extra`, the program's own provisions and calls, in namespace `wiy6zcd.<ns>`.
fn program(ns: &str, defaulted: bool, extra: &str) -> String {
    let conv = if defaulted {
        "operation conv(a: A, b: B) -> Int64 = 0"
    } else {
        "operation conv(a: A, b: B) -> Int64"
    };
    format!(
        "namespace wiy6zcd.{ns}
  import anthill.prelude.{{Int64, String}}
  sort Conv
    sort A = ?
    sort B = ?
    {conv}
  end
  sort Leaf
    entity leaf(v: Int64)
  end
{extra}
end
"
    )
}

/// The one provision of the ticket, `Conv[A = Leaf, B = Int64]`, answering `9`.
const W: &str = "  sort W
    provides Conv[A = Leaf, B = Int64]
    operation conv(a: Leaf, b: Int64) -> Int64 = 9
  end
";

fn qn(ns: &str, name: &str) -> String {
    format!("wiy6zcd.{ns}.{name}")
}

/// The refusal of a call at `(Leaf, String)`, which no provision binds.
fn assert_no_provision_at_leaf_string(ns: &str, errs: &[String], declarer: &str, why: &str) {
    assert_refused_naming(
        errs,
        &[
            &format!(
                "no provision of `wiy6zcd.{ns}.Conv` binds `A = wiy6zcd.{ns}.Leaf, B = \
                 anthill.prelude.String`"
            ),
            declarer,
        ],
        why,
    );
}

/// BODY-LESS. The ticket's program: refused at load, as its rule-body twin is. It loaded and
/// answered `9`. Beside it the call at the binding `W` has still answers `9` (CONTROL).
#[test]
fn a_call_no_provision_binds_is_refused_in_an_operation_body() {
    let bad = program(
        "t1",
        false,
        &format!("{W}  operation bad() -> Int64 = Conv.conv(leaf(v: 1), \"s\")"),
    );
    assert_no_provision_at_leaf_string(
        "t1",
        &load_errors_of(&bad),
        "this operation declares",
        "the ticket's call",
    );

    let good = program(
        "t1",
        false,
        &format!("{W}  operation good() -> Int64 = Conv.conv(leaf(v: 1), 4)"),
    );
    assert_eq!(
        run_int64(&good, &qn("t1", "good")),
        Ok(9),
        "`W.conv` at its own binding"
    );

    // CONTROL — the ticket's second program, a provision binding both parameters to one type:
    // the provision at the carrier binds `B` to `Int64`, so the argument is a type mismatch
    // at `b`, before and after.
    let same = program(
        "t1",
        false,
        "  sort W
    provides Conv[A = Int64, B = Int64]
    operation conv(a: Int64, b: Int64) -> Int64 = 1
  end
  operation bad() -> Int64 = Conv.conv(3, \"km\")",
    );
    assert_refused_naming(
        &load_errors_of(&same),
        &["conv.b", "expected Int64, got String"],
        "`(Int64, String)`",
    );
}

/// BODY-LESS. Wherever an evaluated body holds the call: a constant's value, an `if`
/// condition, a `match` arm, a `let`, the caller's parameters, named arguments, a dot, a
/// member import, the spec's bracket, a lambda, and a lambda handed to an operation. Each
/// loaded and answered through `W.conv`.
#[test]
fn every_evaluated_site_asks_the_provision() {
    let sites: &[(&str, &str, &str)] = &[
        (
            "c1",
            "  const c: Int64 = Conv.conv(leaf(v: 1), \"s\")\n  operation bad() -> Int64 = c",
            "a constant's value declares",
        ),
        (
            "c2",
            "  import anthill.prelude.PartialOrd.{gt}\n  \
             operation bad() -> Int64 = if gt(Conv.conv(leaf(v: 1), \"s\"), 0) then 1 else 2",
            "this operation declares",
        ),
        (
            "c3",
            "  operation bad() -> Int64 = match leaf(v: 1)\n    case leaf(v) -> Conv.conv(leaf(v: v), \"s\")",
            "this operation declares",
        ),
        (
            "c4",
            "  operation bad() -> Int64 =\n    let x = leaf(v: 1)\n    let s = \"s\"\n    Conv.conv(x, s)",
            "this operation declares",
        ),
        (
            "c5",
            "  operation f(x: Leaf, s: String) -> Int64 = Conv.conv(x, s)",
            "this operation declares",
        ),
        (
            "c6",
            "  operation bad() -> Int64 = Conv.conv(b: \"s\", a: leaf(v: 1))",
            "this operation declares",
        ),
        ("c7", "  operation bad() -> Int64 = leaf(v: 1).conv(\"s\")", "this operation declares"),
        (
            "c8",
            "  import wiy6zcd.c8.Conv.{conv}\n  operation bad() -> Int64 = conv(leaf(v: 1), \"s\")",
            "this operation declares",
        ),
        (
            "c9",
            "  operation bad() -> Int64 = Conv[A = Leaf, B = String].conv(leaf(v: 1), \"s\")",
            "this operation declares",
        ),
        (
            "c10",
            "  operation bad() -> Int64 =\n    let f = lambda (x: Leaf) -> Conv.conv(x, \"s\")\n    f(leaf(v: 1))",
            "this operation declares",
        ),
        (
            "c11",
            "  operation app[X](f: (x: X) -> Int64, x: X) -> Int64 = f(x)\n  \
             operation bad() -> Int64 = app(lambda (x: Leaf) -> Conv.conv(x, \"s\"), leaf(v: 1))",
            "this operation declares",
        ),
    ];
    for &(ns, body, declarer) in sites {
        let src = program(ns, false, &format!("{W}{body}"));
        assert_no_provision_at_leaf_string(ns, &load_errors_of(&src), declarer, ns);
    }
    // An untyped lambda knows only `B` where the call is typed, and no provision binds
    // `B = String` at any `A`.
    let src = program(
        "c12",
        false,
        &format!("{W}  operation bad() -> Int64 =\n    let f = lambda x -> Conv.conv(x, \"s\")\n    f(leaf(v: 1))"),
    );
    assert_refused_naming(
        &load_errors_of(&src),
        &["no provision of `wiy6zcd.c12.Conv` binds `B = anthill.prelude.String`"],
        "an untyped lambda",
    );
}

/// CONTROL. The provision at the call's types answers: of two at `A = Leaf`, the one at each
/// call's `B`; the advised repair, a provision at `(Leaf, String)`; the caller's parameters at
/// `W`'s binding; and a generic caller declaring the requirement, at `W`'s binding.
#[test]
fn the_provision_at_the_calls_types_answers() {
    let two = "  sort W2
    provides Conv[A = Leaf, B = String]
    operation conv(a: Leaf, b: String) -> Int64 = 8
  end
  operation s() -> Int64 = Conv.conv(leaf(v: 1), \"s\")
  operation i() -> Int64 = Conv.conv(leaf(v: 1), 4)
  operation f(x: Leaf, n: Int64) -> Int64 = Conv.conv(x, n)
  operation p() -> Int64 = f(leaf(v: 1), 4)
  operation g[X, U](x: X, u: U) -> Int64 requires Conv[A = X, B = U] = Conv.conv(x, u)
  operation q() -> Int64 = g(leaf(v: 1), 4)
  operation r() -> Int64 = g(leaf(v: 1), \"t\")
";
    let src = program("k1", false, &format!("{W}{two}"));
    for (name, want) in [("s", 8), ("i", 9), ("p", 9), ("q", 9), ("r", 8)] {
        assert_eq!(run_int64(&src, &qn("k1", name)), Ok(want), "`{name}`");
    }
}

/// CONTROL. The rule-body twin, refused since WI-20260925-PRVA2 (c), with its own sentence.
#[test]
fn the_rule_body_twin_is_refused_as_before() {
    let src = program(
        "k2",
        false,
        &format!("{W}  rule r(?r) :- Conv.conv(leaf(v: 1), \"s\", ?r)"),
    );
    assert_no_provision_at_leaf_string(
        "k2",
        &load_errors_of(&src),
        "this clause declares",
        "the rule body",
    );
}

/// A defaulted `conv`, `= 0`, beside `W` and `WS provides Conv[A = Leaf, B = String]`, which
/// writes no member and takes the spec's body.
const WS: &str = "  sort WS
    provides Conv[A = Leaf, B = String]
  end
";

/// TYPER and EVAL. A witness's member answers only at its provision's carriers: at `(Leaf,
/// String)` the call is `WS`'s, the spec's body, where it answered `W.conv`'s `9`; at `(Leaf,
/// Int64)` it is `W.conv`'s. Either filter backed out, the operation body's call at `(Leaf,
/// String)` answers `9`: the typer pins `W.conv`, or the interpreter's carrier override
/// redirects the spec's body the typer pinned to it.
#[test]
fn a_witness_member_answers_only_at_its_provisions_carriers() {
    let calls = "  operation s() -> Int64 = Conv.conv(leaf(v: 1), \"s\")
  operation i() -> Int64 = Conv.conv(leaf(v: 1), 4)
  rule rs(?r) :- Conv.conv(leaf(v: 1), \"s\", ?r)
  rule ri(?r) :- Conv.conv(leaf(v: 1), 4, ?r)
";
    let src = program("d1", true, &format!("{W}{WS}{calls}"));
    assert_eq!(
        run_int64(&src, &qn("d1", "s")),
        Ok(0),
        "the operation body at `(Leaf, String)`"
    );
    assert_eq!(
        run_int64(&src, &qn("d1", "i")),
        Ok(9),
        "CONTROL: the operation body at `(Leaf, Int64)`"
    );
    let mut kb = load_kb_with(&src);
    assert_eq!(
        one_definite_int(&mut kb, &qn("d1", "rs")),
        Some(0),
        "the rule body at `(Leaf, String)`"
    );
    assert_eq!(
        one_definite_int(&mut kb, &qn("d1", "ri")),
        Some(9),
        "CONTROL: the rule body at `(Leaf, Int64)`"
    );
}

/// TYPER and EVAL. The carrier's own member, `Leaf2.conv(a: Leaf2, b: Int64)` answering `7`,
/// answers the carrier's provision and a witness's that writes none of its own — so its own
/// signature is what it admits. Beside `WS2` the call at `(Leaf2, String)` is the spec's body,
/// where it answered `7`; with `W3`'s provision alone, writing no member, it is refused at
/// load, as no provision binds `(Leaf2, String)`. The typer's filter backed out, the rule
/// body's call answers `7`; the interpreter's, the operation body's.
#[test]
fn a_carriers_own_member_answers_only_at_its_signatures_carriers() {
    let leaf_own = "  sort Leaf2
    entity leaf2(v: Int64)
    provides Conv[A = Leaf2, B = Int64]
    operation conv(a: Leaf2, b: Int64) -> Int64 = 7
  end
  sort WS2
    provides Conv[A = Leaf2, B = String]
  end
  operation s() -> Int64 = Conv.conv(leaf2(v: 1), \"s\")
  operation i() -> Int64 = Conv.conv(leaf2(v: 1), 4)
  rule rs(?r) :- Conv.conv(leaf2(v: 1), \"s\", ?r)
";
    let src = program("o1", true, leaf_own);
    assert_eq!(
        run_int64(&src, &qn("o1", "s")),
        Ok(0),
        "the operation body at `(Leaf2, String)`"
    );
    assert_eq!(
        run_int64(&src, &qn("o1", "i")),
        Ok(7),
        "CONTROL: `Leaf2.conv` at its own binding"
    );
    let mut kb = load_kb_with(&src);
    assert_eq!(
        one_definite_int(&mut kb, &qn("o1", "rs")),
        Some(0),
        "the rule body at `(Leaf2, String)`"
    );

    // `Leaf2`'s member answering through a witness's provision that writes no member.
    let riding = "  sort Leaf2
    entity leaf2(v: Int64)
    operation conv(a: Leaf2, b: Int64) -> Int64 = 7
  end
  sort W3
    provides Conv[A = Leaf2, B = Int64]
  end
";
    let i = program(
        "o2",
        true,
        &format!("{riding}  operation i() -> Int64 = Conv.conv(leaf2(v: 1), 4)"),
    );
    assert_eq!(
        run_int64(&i, &qn("o2", "i")),
        Ok(7),
        "CONTROL: through `W3`'s provision"
    );
    let s = program(
        "o2",
        true,
        &format!("{riding}  operation s() -> Int64 = Conv.conv(leaf2(v: 1), \"s\")"),
    );
    assert_refused_naming(
        &load_errors_of(&s),
        &[
            "no impl matches",
            "Conv[A = wiy6zcd.o2.Leaf2, B = anthill.prelude.String]",
        ],
        "no provision binds `(Leaf2, String)`",
    );
}

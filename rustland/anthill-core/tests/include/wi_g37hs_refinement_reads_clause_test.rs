//! WI-20261020-G37HS — the typer's subsumption of a sort that refines another through
//! `requires` reads the instances its clauses give it, the refining sort's own arguments put
//! for the parameters a clause names (`subtype::refinement_admits_applied`, over the reader
//! the run-time test `type_admits` uses, `type_pattern::instances_through_requires`). It
//! compared heads only: a `narrow()` was accepted where a `Wide[W = String]` is expected
//! under `sort Narrow requires Wide[W = Int64]`, and a `Narrow2[Q = String]` refused where a
//! `Wide[W = String]` is expected under `requires Wide[W = Q]`.
//!
//! ── WHICH ROWS FAIL WHEN EACH PART IS BACKED OUT ──────────────────────────────────
//!
//! MEASURED with a temporary switch per part, both in one build:
//!
//! * The bare actual's arm (`bare_nominal_admits_applied`, admitting by name again):
//!   `a_refining_sort_is_refused_where_its_clause_gives_another_instance` (loads, answers 21),
//!   `every_position_reads_the_clause` (each of its eight refused programs loads),
//!   `a_clause_two_down_is_read_through_the_middle` (its refusal loads), and
//!   `the_typer_agrees_with_type_admits` at `clauseNot`, `twoDownNot` and `sinkNot`.
//! * The applied actual's arm (the refinement block of `parameterized_compatible_view`):
//!   `a_parametric_clause_reads_the_refining_sorts_argument` (refused, `expected Wide[W =
//!   String], got Narrow2[Q = String]`), and `the_typer_agrees_with_type_admits` at `param`
//!   and `nested`.
//! * The path guard of `instances_below`, which enters no sort a path has passed through: the
//!   cycle rows of `the_typer_agrees_with_type_admits` — `type_admits` errs at `cycle` and
//!   `cycleNot` ("nest deeper than 512 levels"), and the typer refuses `cycle`. A run-time
//!   defect as much as the typer's: the reader is the one they share.
//!
//! Pass either way, by design: `a_refining_sort_is_admitted_at_the_instance_its_clause_gives`
//! and the refusals in `a_parametric_clause_reads_the_refining_sorts_argument` — what the
//! change must leave as it was.

use anthill_core::eval::value::Value;

use crate::common::{assert_refused_naming, interp_for, load_errors_of};

/// The sorts every row compares: `Wide` refined at a fixed argument (`Narrow`), at the
/// refining sort's own parameter (`Narrow2`), two clauses down (`Narrower`), inside an
/// argument (`NestedQ`), at a contravariant parameter (`AnimalSink`, `CatSink`), and through
/// a cycle of clauses (`CycA`, `CycB`). `WInt` and `WStr` supply the requirement a
/// construction owes.
fn program(body: &str) -> String {
    format!(
        r#"
namespace wig37hs
  import anthill.prelude.{{Int64, String, Bool, List, Option, Function}}
  import anthill.reflect.{{type_admits}}
  import anthill.reflect.typing.{{Contravariant}}
  sort Wide
    sort W = ?
  end
  sort Narrow
    requires Wide[W = Int64]
    entity narrow
  end
  sort Narrow2
    sort Q = ?
    requires Wide[W = Q]
    entity narrow2
  end
  sort Narrower
    requires Narrow2[Q = String]
  end
  sort NestedQ
    sort Q = ?
    requires Wide[W = Option[T = Q]]
  end
  sort Animal
    entity animal
  end
  sort Cat
    requires Animal
    entity cat
  end
  sort Sink
    sort T = ?
  end
  fact Contravariant(sort: Sink, param: T)
  sort AnimalSink
    requires Sink[T = Animal]
  end
  sort CatSink
    requires Sink[T = Cat]
  end
  sort CycA
    requires CycB
  end
  sort CycB
    requires CycA
    requires Wide[W = Int64]
  end
  sort WInt
    provides Wide[W = Int64]
  end
  sort WStr
    provides Wide[W = String]
  end
  operation takeInt(x: Wide[W = Int64]) -> Int64 = 1
  operation takeStr(x: Wide[W = String]) -> Int64 = 2
  operation takeAt[Y](x: Wide[W = Y]) -> Int64 = 4
  operation takeAny(x: Wide) -> Int64 = 8
{body}
end
"#
    )
}

/// `wig37hs.go()`'s answer.
fn go(body: &str) -> i64 {
    let mut interp = interp_for(&program(body));
    match interp.call("wig37hs.go", &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("expected an Int64, got {other:?}"),
    }
}

/// The program's one refusal, which names each of `tokens`.
fn refused(body: &str, tokens: &[&str], why: &str) {
    let errs = load_errors_of(&program(body));
    assert_refused_naming(&errs, tokens, why);
    assert_eq!(errs.len(), 1, "{why}: one refusal, got {errs:#?}");
}

/// The ticket's program: `narrow()` is the instance `Wide[W = Int64]` its clause gives it,
/// and no `Wide[W = String]`. BACK-OUT (the bare arm): loads, and answers 21.
#[test]
fn a_refining_sort_is_refused_where_its_clause_gives_another_instance() {
    refused(
        "  operation go() -> Int64 = takeInt(narrow()) + 10 * takeStr(narrow())",
        &["takeStr.x", "expected Wide[W = String], got Narrow"],
        "a Narrow at Wide[W = String]",
    );
}

/// At the instance its clause gives it, and where the target writes no argument, a refining
/// sort is admitted as it was. CONTROL: passes either way.
#[test]
fn a_refining_sort_is_admitted_at_the_instance_its_clause_gives() {
    assert_eq!(
        go("  operation go() -> Int64 = takeInt(narrow()) + 10 * takeAny(narrow())"),
        81
    );
}

/// `requires Wide[W = Q]` gives `Narrow2[Q = String]` the instance `Wide[W = String]`, by
/// the parameter the clause names — at a concrete argument, and at a caller's own type
/// parameter. BACK-OUT (the applied arm): refused, `expected Wide[W = String], got
/// Narrow2[Q = String]`. The refusals pass either way: the arm refused every expected
/// binding before.
#[test]
fn a_parametric_clause_reads_the_refining_sorts_argument() {
    assert_eq!(
        go(
            r#"  operation pass(n: Narrow2[Q = String]) -> Int64 = takeStr(n)
  operation passAt[X](n: Narrow2[Q = X]) -> Int64 = takeAt[X](n)
  operation go() -> Int64 = pass(narrow2[String]()) + 10 * passAt[String](narrow2[String]())"#
        ),
        42
    );
    refused(
        "  operation pass(n: Narrow2[Q = String]) -> Int64 = takeInt(n)",
        &[
            "takeInt.x",
            "expected Wide[W = Int64], got Narrow2[Q = String]",
        ],
        "a Narrow2[Q = String] at Wide[W = Int64]",
    );
    refused(
        "  operation passAt[X](n: Narrow2[Q = X]) -> Int64 = takeStr(n)",
        &["takeStr.x", "expected Wide[W = String]"],
        "a Narrow2[Q = X] at Wide[W = String]",
    );
}

/// Every position a value meets a type reads the clause, each beside its twin at the instance
/// the clause gives, which loads. BACK-OUT (the bare arm): every refused program loads.
#[test]
fn every_position_reads_the_clause() {
    let rows: &[(&str, &str, &str)] = &[
        (
            "return",
            "  operation r() -> Wide[W = {W}] = narrow()",
            "r.return",
        ),
        (
            "let",
            "  operation r() -> Int64 =\n    let w: Wide[W = {W}] = narrow()\n    3",
            "w.annotation",
        ),
        (
            "field",
            "  sort H\n    entity holder(w: Wide[W = {W}])\n  end\n  operation r() -> H = holder(w: narrow())",
            "holder.w",
        ),
        (
            "list element",
            "  operation r() -> List[T = Wide[W = {W}]] = [narrow()]",
            "list.element",
        ),
        (
            "const",
            "  const cw: Wide[W = {W}] = narrow()",
            "cw.value",
        ),
        (
            "rule body",
            "  operation tk(x: Wide[W = {W}]) -> Int64 = 1\n  rule rr(?r) :- ?r <=> tk(narrow())",
            "tk.x",
        ),
        (
            "callback parameter",
            "  operation ap(f: (n: Narrow) -> Int64) -> Int64 = f(narrow())\n  operation r() -> Int64 = ap(lambda (x: Wide[W = {W}]) -> 5)",
            "ap.f",
        ),
        (
            "inside an argument",
            "  operation r(xs: List[T = Narrow]) -> List[T = Wide[W = {W}]] = xs",
            "r.return",
        ),
    ];
    let mut wrong = Vec::new();
    for (position, body, site) in rows {
        let at = |w: &str| body.replace("{W}", w);
        let errs = load_errors_of(&program(&at("Int64")));
        if !errs.is_empty() {
            wrong.push(format!("{position}: at Wide[W = Int64] refused: {errs:?}"));
        }
        let errs = load_errors_of(&program(&at("String")));
        let names = |e: &String| e.contains(site) && e.contains("Wide[W = String]");
        if errs.len() != 1 || !names(&errs[0]) {
            wrong.push(format!(
                "{position}: at Wide[W = String], one refusal at {site}: {errs:?}"
            ));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}

/// `Narrower requires Narrow2[Q = String]`, and `Narrow2[Q] requires Wide[W = Q]`: the
/// instance is `Wide[W = String]`, read through the middle clause at the argument the first
/// one writes. BACK-OUT (the bare arm): the refusal loads; the admission passes either way.
#[test]
fn a_clause_two_down_is_read_through_the_middle() {
    assert!(load_errors_of(&program(
        "  operation pl(l: Narrower) -> Int64 = takeStr(l)"
    ))
    .is_empty());
    refused(
        "  operation pl(l: Narrower) -> Int64 = takeInt(l)",
        &["takeInt.x", "expected Wide[W = Int64], got Narrower"],
        "a Narrower at Wide[W = Int64]",
    );
}

/// THE TYPER AND THE RUN TIME ANSWER ALIKE: a value typed `T` returned where `P` is declared
/// loads exactly where `type_admits(P, T)` answers `true`, at each refinement the harness
/// declares — a fixed argument, the refining sort's own, two clauses down, inside an argument,
/// a contravariant parameter, a cycle of clauses, and a target that writes no argument. Every `T` writes its
/// arguments: a parameter typed by a bare parametric sort is the parameter's own instance
/// (`n.Q`), not the open slot `type_admits` reads a bare sort as. BACK-OUT: with the bare arm
/// out, the typer admits `clauseNot`, `twoDownNot` and `sinkNot`; with the applied arm out, it
/// refuses `param` and `nested`; with the path guard out, `type_admits` errs at `cycle` and
/// `cycleNot` and the typer refuses `cycle`.
#[test]
fn the_typer_agrees_with_type_admits() {
    let pairs: &[(&str, &str, &str, bool)] = &[
        ("clause", "Wide[W = Int64]", "Narrow", true),
        ("clauseNot", "Wide[W = String]", "Narrow", false),
        ("clauseOpen", "Wide", "Narrow", true),
        ("param", "Wide[W = String]", "Narrow2[Q = String]", true),
        ("paramNot", "Wide[W = Int64]", "Narrow2[Q = String]", false),
        ("twoDown", "Wide[W = String]", "Narrower", true),
        ("twoDownNot", "Wide[W = Int64]", "Narrower", false),
        (
            "nested",
            "Wide[W = Option[T = Animal]]",
            "NestedQ[Q = Animal]",
            true,
        ),
        (
            "nestedNot",
            "Wide[W = Option[T = Cat]]",
            "NestedQ[Q = Animal]",
            false,
        ),
        ("sink", "Sink[T = Cat]", "AnimalSink", true),
        ("sinkNot", "Sink[T = Animal]", "CatSink", false),
        ("cycle", "Wide[W = Int64]", "CycA", true),
        ("cycleNot", "Wide[W = String]", "CycA", false),
    ];
    let ops: String = pairs
        .iter()
        .map(|(op, p, t, _)| {
            format!("  operation {op}(n: Int64) -> Bool = type_admits({p}, {t})\n")
        })
        .collect();
    let mut interp = interp_for(&program(&ops));
    let mut wrong = Vec::new();
    for (op, p, t, want) in pairs {
        match interp.call(&format!("wig37hs.{op}"), &[Value::Int(0)]) {
            Ok(Value::Bool(got)) if got == *want => {}
            other => wrong.push(format!(
                "{op}: type_admits({p}, {t}) is {want}, got {other:?}"
            )),
        }
        let errs = load_errors_of(&program(&format!("  operation f(x: {t}) -> {p} = x")));
        if errs.is_empty() != *want {
            wrong.push(format!(
                "{op}: the typer at `f(x: {t}) -> {p}`, not {want}: {errs:?}"
            ));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}

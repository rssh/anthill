//! WI-20261101-C580V — a call's type argument is inferred through a `requires` clause. Under
//! `sort Narrow requires Wide[W = Int64]`, `takeAt[Y](x: Wide[W = Y])` called with a
//! `narrow()` is at `Y = Int64` (`unify::unify_through_refinement`, over the instances the
//! subtype relation reads, `subtype::refinement_unifiers`); it was refused, "expected a type
//! for 'Y', got unconstrained". And an argument the arguments leave open — a sort whose clauses
//! give it two instances of `Wide` — is checked again at what the rest of the call fills it with
//! (`apply::recheck_arguments_left_open`): the argument check reads only a ground pair, so
//! `Both` was admitted at whatever the expected result, or a default, said.
//!
//! ── WHICH ROWS FAIL WHEN EACH PART IS BACKED OUT ──────────────────────────────────
//!
//! MEASURED with a temporary switch per part, all in one build:
//!
//! * The bare arm (`unify_parameterized_with_sort_ref`: a bare actual, `narrow()`, at an
//!   application): `a_call_reads_its_type_argument_through_the_clause` ("expected a type for
//!   'Y'"), `an_argument_is_checked_at_what_the_expected_result_fills` (`-> Option[T = String]`
//!   over a `Narrow` loads) and `two_paths_to_one_instance_are_one_answer`.
//! * The application arm, refining side first (`unify_parameterized_view`):
//!   `a_call_reads_its_type_argument_through_the_clause` at its `Narrow2` calls,
//!   `the_clause_is_read_and_not_a_parameter_of_the_same_name` (`expected Wide[W = String], got
//!   Narrow3[W = String]`), `an_alias_of_a_refining_instance_infers` and
//!   `a_bare_parameter_is_read_at_its_own_instance` ("expected a type for 'Y'").
//! * The application arm, refined side first: `a_callback_parameter_reads_the_clause` (the
//!   refusal loads).
//! * The dedupe of answers in `refinement_unifiers`: `two_paths_to_one_instance_are_one_answer`
//!   ("expected a type for 'Y'").
//! * The second check (`recheck_arguments_left_open` refusing nothing):
//!   `an_argument_is_checked_at_what_the_expected_result_fills` at its two-instance rows, and
//!   `two_instances_are_decided_by_the_rest_of_the_call` at the default `Bool` — each loads.
//!
//! Pass either way, by design: `a_clause_naming_no_argument_leaves_it_unconstrained`, the
//! refusal in `a_bare_parameter_is_read_at_its_own_instance`, and the rows of
//! `two_instances_are_decided_by_the_rest_of_the_call` other than the default `Bool`.

use anthill_core::eval::value::Value;

use crate::common::{assert_refused_naming, interp_for, load_errors_of};

/// `Wide` refined at a fixed argument (`Narrow`), at the refining sort's own parameter
/// (`Narrow2`), at a parameter named as the refined sort's is (`Narrow3`), with no argument
/// (`Plain`), and at two (`Both`). `isInt`, `isStr` and `isListStr` read the call's `Y` at run
/// time. `WInt`, `WStr` and `WListStr` supply the requirement a construction owes.
fn program(body: &str) -> String {
    format!(
        r#"
namespace wic580v
  import anthill.prelude.{{Int64, String, Bool, List, Option, none}}
  import anthill.reflect.{{type_admits, TypeValue}}
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
  sort Narrow3
    sort W = ?
    requires Wide[W = List[T = W]]
    entity narrow3
  end
  sort Plain
    requires Wide
  end
  sort Both
    requires Wide[W = Int64]
    requires Wide[W = String]
  end
  sort WInt
    provides Wide[W = Int64]
  end
  sort WStr
    provides Wide[W = String]
  end
  sort WListStr
    provides Wide[W = List[T = String]]
  end
  operation takeAt[Y](x: Wide[W = Y]) -> Int64 = 4
  operation isInt[Y](x: Wide[W = Y]) -> Bool requires TypeValue[T = Y] = type_admits(Int64, Y)
  operation isStr[Y](x: Wide[W = Y]) -> Bool requires TypeValue[T = Y] = type_admits(String, Y)
  operation isListStr[Y](x: Wide[W = Y]) -> Bool requires TypeValue[T = Y] = type_admits(List[T = String], Y)
  operation optOf[Y](x: Wide[W = Y]) -> Option[T = Y] = none()
{body}
end
"#
    )
}

/// `wic580v.<op>()`'s answer, a `Bool`.
fn answer(body: &str, op: &str) -> bool {
    let mut interp = interp_for(&program(body));
    match interp.call(&format!("wic580v.{op}"), &[]) {
        Ok(Value::Bool(b)) => b,
        other => panic!("{op}: expected a Bool, got {other:?}"),
    }
}

/// The program's one refusal, which names each of `tokens`.
fn refused(body: &str, tokens: &[&str], why: &str) {
    let errs = load_errors_of(&program(body));
    assert_refused_naming(&errs, tokens, why);
    assert_eq!(errs.len(), 1, "{why}: one refusal, got {errs:#?}");
}

fn loads(body: &str, why: &str) {
    let errs = load_errors_of(&program(body));
    assert!(errs.is_empty(), "{why}: loads, got {errs:#?}");
}

/// The ticket's three calls: a `Narrow` is at `Y = Int64`, a `Narrow2[Q = String]` at
/// `String`, and a `Narrow2[Q = X]` at the caller's own `X` — each read at run time. BACK-OUT:
/// with the bare arm out the `Narrow` calls, with the application arm out the `Narrow2` ones,
/// are refused, "expected a type for 'Y', got unconstrained".
#[test]
fn a_call_reads_its_type_argument_through_the_clause() {
    let body = r#"  operation fixed() -> Int64 = takeAt(narrow())
  operation fixedInt() -> Bool = isInt(narrow())
  operation fixedStr() -> Bool = isStr(narrow())
  operation own(m: Narrow2[Q = String]) -> Bool = isStr(m)
  operation ownStr() -> Bool = own(narrow2[String]())
  operation ownInt() -> Bool = isInt(narrow2[String]())
  operation callers[X](n: Narrow2[Q = X]) -> Bool requires TypeValue[T = X] = isStr(n)
  operation callersStr() -> Bool = callers(narrow2[String]())
  operation callersInt() -> Bool = callers(narrow2[Int64]())"#;
    let mut interp = interp_for(&program(body));
    match interp.call("wic580v.fixed", &[]) {
        Ok(Value::Int(4)) => {}
        other => panic!("fixed: expected 4, got {other:?}"),
    }
    let answers: Vec<(&str, bool)> = ["fixedInt", "fixedStr", "ownStr", "ownInt", "callersStr", "callersInt"]
        .iter()
        .map(|op| (*op, answer(body, op)))
        .collect();
    assert_eq!(
        answers,
        vec![
            ("fixedInt", true),
            ("fixedStr", false),
            ("ownStr", true),
            ("ownInt", false),
            ("callersStr", true),
            ("callersInt", false),
        ]
    );
}

/// A clause that writes no argument gives the instance `Wide`, which fixes nothing: the refusal
/// stays. CONTROL: passes either way.
#[test]
fn a_clause_naming_no_argument_leaves_it_unconstrained() {
    refused(
        "  operation go(p: Plain) -> Int64 = takeAt(p)",
        &["takeAt", "expected a type for 'Y'"],
        "a Plain fixes no Y",
    );
}

/// A parameter typed by the bare `Narrow2` is its own instance, `Narrow2[Q = n.Q]`, which the
/// clause gives `Wide[W = n.Q]`: the call is at `Y = n.Q`, and not at a type that is not it.
/// BACK-OUT (the application arm): `bare` refused, "expected a type for 'Y'"; the refusal
/// passes either way.
#[test]
fn a_bare_parameter_is_read_at_its_own_instance() {
    let mut interp = interp_for(&program(
        "  operation bare(n: Narrow2) -> Int64 = takeAt(n)\n  operation go() -> Int64 = bare(narrow2[String]())",
    ));
    match interp.call("wic580v.go", &[]) {
        Ok(Value::Int(4)) => {}
        other => panic!("go: expected 4, got {other:?}"),
    }
    refused(
        "  operation go(n: Narrow2) -> Option[T = String] = optOf(n)",
        &["go.return", "expected Option[T = String]"],
        "n.Q is not String",
    );
}

/// `Narrow3[W = String]` is a `Wide[W = List[T = String]]`: `Y` is read through the clause, not
/// paired with the refining sort's own `W` by its name. BACK-OUT (the application arm):
/// refused, `expected Wide[W = String], got Narrow3[W = String]`.
#[test]
fn the_clause_is_read_and_not_a_parameter_of_the_same_name() {
    assert!(answer(
            "  operation go() -> Bool = isListStr(narrow3[String]())",
            "go"
    ));
}

/// `sort NS = Narrow2[Q = String]` is read as its shape. BACK-OUT (the application arm):
/// refused, "expected a type for 'Y'".
#[test]
fn an_alias_of_a_refining_instance_infers() {
    assert!(answer(
            "  sort NS = Narrow2[Q = String]\n  operation via(m: NS) -> Bool = isStr(m)\n  operation go() -> Bool = via(narrow2[String]())",
            "go"
    ));
}

/// A generic operation passed where a callback takes a `Narrow2[Q = String]` is at the instance
/// the clause gives it: `optOf` there returns an `Option[T = String]`. The callback's parameter
/// meets the declared one with the refined sort first. BACK-OUT (the application arm, refined
/// side first): the refusal loads, at `Z = Option[T = Int64]`.
#[test]
fn a_callback_parameter_reads_the_clause() {
    let decl = "  operation ap[Z](f: (n: Narrow2[Q = String]) -> Z) -> Z = f(narrow2[String]())\n";
    let mut interp = interp_for(&program(&format!(
        "{decl}  operation go() -> Option[T = String] = ap(optOf)"
    )));
    match interp.call("wic580v.go", &[]) {
        Ok(Value::Entity { .. }) => {}
        other => panic!("go: expected none(), got {other:?}"),
    }
    refused(
        &format!("{decl}  operation go() -> Option[T = Int64] = ap(optOf)"),
        &["go.return", "expected Option[T = Int64], got Option[T = String]"],
        "optOf at a Narrow2[Q = String] is at String",
    );
}

/// The arguments are read first and the expected result fills what they leave open; the
/// argument is then checked at it. One instance: `Y` is the clause's, and a result claiming
/// another is refused. Two: the result decides between them, and one that is neither is
/// refused at the argument. BACK-OUT: with the bare arm out, `-> Option[T = String]` over a
/// `Narrow` loads; with the second check out, `Both` at `Option[T = Bool]` loads (the return;
/// the `let`, run as a program of its own, loads too).
#[test]
fn an_argument_is_checked_at_what_the_expected_result_fills() {
    refused(
        "  operation go() -> Option[T = String] = optOf(narrow())",
        &["go.return", "expected Option[T = String], got Option[T = Int64]"],
        "a Narrow's Y is Int64",
    );
    loads(
        "  operation go() -> Option[T = Int64] = optOf(narrow())",
        "a Narrow at its own instance",
    );
    loads(
        "  operation go(b: Both) -> Option[T = Int64] = optOf(b)",
        "Both at its Int64 instance",
    );
    loads(
        "  operation go(b: Both) -> Option[T = String] = optOf(b)",
        "Both at its String instance",
    );
    refused(
        "  operation go(b: Both) -> Option[T = Bool] = optOf(b)",
        &["optOf.x", "expected Wide[W = Bool], got Both"],
        "Both is no Wide[W = Bool]",
    );
    refused(
        "  operation go(b: Both) -> Int64 =\n    let o: Option[T = Bool] = optOf(b)\n    3",
        &["optOf.x", "expected Wide[W = Bool], got Both"],
        "Both is no Wide[W = Bool], in a let",
    );
}

/// Two instances fit, and the arguments do not say which: another argument says, or the
/// declared default, or the call is refused as unconstrained. BACK-OUT (the second check): the
/// default `Bool` loads. The other rows pass either way: another argument is read before the
/// argument check, and nothing at all leaves `Y` unbound.
#[test]
fn two_instances_are_decided_by_the_rest_of_the_call() {
    let decl = "  operation two[Y](x: Wide[W = Y], y: Y) -> Int64 = 1\n  operation dflt[Y = Int64](x: Wide[W = Y]) -> Int64 = 2\n  operation dfltB[Y = Bool](x: Wide[W = Y]) -> Int64 = 2\n";
    loads(
        &format!("{decl}  operation go(b: Both) -> Int64 = two(b, \"s\") + two(b, 5) + dflt(b)"),
        "another argument, or a default at one instance",
    );
    refused(
        &format!("{decl}  operation go(b: Both) -> Int64 = two(b, true)"),
        &["two.x", "expected Wide[W = Bool], got Both"],
        "another argument at neither instance",
    );
    refused(
        &format!("{decl}  operation go(b: Both) -> Int64 = dfltB(b)"),
        &["dfltB.x", "expected Wide[W = Bool], got Both"],
        "a default at neither instance",
    );
    refused(
        "  operation go(b: Both) -> Int64 = takeAt(b)",
        &["takeAt", "expected a type for 'Y'"],
        "nothing says which",
    );
    loads(
        "  operation go(b: Both) -> Int64 = takeAt[String](b)",
        "the repair the refusal advises",
    );
}

/// `D requires L, R`, each `requires Wide[W = Int64]`: two paths of clauses, one instance, one
/// answer. BACK-OUT: with the dedupe out, refused as two answers ("expected a type for 'Y'");
/// with the bare arm out, refused too.
#[test]
fn two_paths_to_one_instance_are_one_answer() {
    assert!(answer(
            "  sort L\n    requires Wide[W = Int64]\n  end\n  sort R\n    requires Wide[W = Int64]\n  end\n  sort D\n    requires L\n    requires R\n    entity d\n  end\n  sort LP\n    provides L\n  end\n  sort RP\n    provides R\n  end\n  operation go() -> Bool = isInt(d())",
            "go"
    ));
}

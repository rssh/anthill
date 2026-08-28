//! Integration tests for the stdlib CLI argument parser
//! (`stdlib/anthill/cli/{spec,parse}.anthill`). Drives `parse_argv` on a
//! 3-subcommand sample program and asserts on the parsed result.

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;

use crate::common::interp_for;

const PROGRAM: &str = r#"
namespace test.cli_demo
  import anthill.prelude.{List, Option, String, Bool}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.List.{nil, cons}
  import anthill.cli.spec.{OperationSpec, ParamSpec, ParamKind}
  import anthill.cli.spec.ParamKind.{positional, flag, repeated}
  import anthill.cli.parse.{ParseResult, parse_argv}
  import anthill.cli.help.{format_help}

  -- 3 subcommands: list (no params), show (id positional),
  -- update (id positional + --description flag + --acceptance repeated).
  operation specs() -> List[T = OperationSpec] = [
    OperationSpec("list", "list items", [], none()),
    OperationSpec("show", "show one item", [
      ParamSpec("id", positional(), true, "work item id")
    ], none()),
    OperationSpec("update", "update an item", [
      ParamSpec("id", positional(), true, "work item id"),
      ParamSpec("description", flag(), false, "new description"),
      ParamSpec("acceptance", repeated(), false, "acceptance criteria")
    ], none())
  ]

  -- parse a sample argv
  operation parse_update() -> ParseResult =
    parse_argv(specs(), ["update", "WI-001", "--description", "x", "--acceptance", "cargo-test"])

  operation parse_unknown() -> ParseResult =
    parse_argv(specs(), ["nope"])

  operation parse_missing_required() -> ParseResult =
    parse_argv(specs(), ["show"])

  -- Help text for the `update` subcommand (3rd in the list).
  operation help_for_update() -> String =
    match specs()
      case cons(_, cons(_, cons(s, _))) -> format_help(s)
      case _ -> "<not found>"
end
"#;

fn name_of(interp: &anthill_core::eval::Interpreter, sym: Symbol) -> String {
    interp.kb().local_name_of(sym).to_string()
}

/// Carrier-neutral: `common::entity_functor` reads the head through `TermView`, so the
/// same entity answers whether it rides as `Value::Entity`, `Value::Term` or
/// `Value::Node` — and a NULLARY constructor, which reads as a bare `Ref`, answers too.
fn entity_short_name(interp: &anthill_core::eval::Interpreter, v: &Value) -> Option<String> {
    let sym = crate::common::entity_functor(interp.kb(), v)?;
    let qn = name_of(interp, sym);
    qn.rsplit('.').next().map(|s| s.to_string())
}

/// `common::entity_field` bound to this file's interpreter — the field BY NAME, whatever
/// carrier the entity rides on.
///
/// WI-20260827-T2470: this file used to read every payload as `pos[i]`, which worked
/// only because `finish_constructor` left a positional constructor application's
/// arguments in `pos` — the divergence that ticket removes. `parse_ok(x)` now evaluates
/// to the canonical `Entity{parse_ok, named:[parsed: x]}` every other producer builds,
/// so a positional read found an EMPTY `pos` and this file panicked. A local
/// `Value::Entity { pos, named }` match would fix that row and keep the deeper fault: an
/// entity also arrives as `Value::Term` or `Value::Node`, and matching the enum makes
/// its CARRIER decide whether its own field is reachable.
fn field(interp: &anthill_core::eval::Interpreter, v: &Value, name: &str, rank: usize) -> Value {
    crate::common::entity_field(interp.kb(), v, name, rank)
}

/// Likewise for the leaf `String`s: `Value::as_str` answers only the `Value::Str`
/// carrier, so the payload's carrier would decide whether it reads as a string.
///
/// PANICS rather than defaulting, which `scalar_str`'s own contract demands: it answers
/// `None` both for a non-literal head and for a literal of the WRONG TYPE, "so a
/// wrong-typed value must not read as absent-but-fine". An `unwrap_or_default()` here
/// turned a `Binding` whose leaf stopped being a `String` into an empty pair, and the
/// failure then surfaced as a confusing vector mismatch instead of naming the carrier —
/// the same "the assert compares against nothing" mode this file's repair was about.
fn text(interp: &anthill_core::eval::Interpreter, v: &Value) -> String {
    crate::common::scalar_str(interp.kb(), v)
        .unwrap_or_else(|| panic!("expected a String leaf, got {v:?}"))
}

#[test]
fn parses_update_subcommand_with_flag_and_repeated() {
    let mut interp = interp_for(PROGRAM);
    let result = interp
        .call("test.cli_demo.parse_update", &[])
        .expect("parse_update runs");

    // Expect: parse_ok(ParsedArgs("update", [Binding("acceptance","cargo-test"),
    //                                         Binding("description","x"),
    //                                         Binding("id","WI-001")]))
    // (bindings are accumulated by cons, so order is reverse of the argv pass.)
    assert_eq!(
        entity_short_name(&interp, &result).as_deref(),
        Some("parse_ok")
    );

    let parsed = field(&interp, &result, "parsed", 0);
    assert_eq!(
        entity_short_name(&interp, &parsed).as_deref(),
        Some("ParsedArgs")
    );

    let (spec_name, bindings) = (
        field(&interp, &parsed, "spec_name", 0),
        field(&interp, &parsed, "bindings", 1),
    );
    assert_eq!(text(&interp, &spec_name), "update");

    // Walk the bindings list cons spine, collect (name, value) pairs.
    let mut pairs: Vec<(String, String)> = Vec::new();
    let mut cur = bindings;
    loop {
        match cur {
            Value::Entity { functor, .. } => {
                let name = name_of(&interp, functor);
                if name.ends_with(".nil") || name == "nil" {
                    break;
                }
                if name.ends_with(".cons") || name == "cons" {
                    let h = field(&interp, &cur, "head", 0);
                    let t = field(&interp, &cur, "tail", 1);
                    let (n, v) = (
                        text(&interp, &field(&interp, &h, "name", 0)),
                        text(&interp, &field(&interp, &h, "value", 1)),
                    );
                    pairs.push((n, v));
                    cur = t;
                } else {
                    panic!("unexpected list functor {name}");
                }
            }
            _ => panic!("expected list entity, got {cur:?}"),
        }
    }

    pairs.sort();
    assert_eq!(
        pairs,
        vec![
            ("acceptance".to_string(), "cargo-test".to_string()),
            ("description".to_string(), "x".to_string()),
            ("id".to_string(), "WI-001".to_string()),
        ]
    );
}

#[test]
fn unknown_subcommand_returns_parse_err() {
    let mut interp = interp_for(PROGRAM);
    let result = interp
        .call("test.cli_demo.parse_unknown", &[])
        .expect("parse_unknown runs");
    assert_eq!(
        entity_short_name(&interp, &result).as_deref(),
        Some("parse_err")
    );
    let err = match &result {
        Value::Entity { .. } => field(&interp, &result, "error", 0),
        _ => panic!("expected parse_err entity"),
    };
    assert_eq!(
        entity_short_name(&interp, &err).as_deref(),
        Some("unknown_subcommand")
    );
}

// Golden help-text. Bindings are accumulated by cons, so flag/repeat order
// follows declaration order; positional appears before flags in our format.
const EXPECTED_HELP: &str = "update an item\n\nUSAGE: update <id> [--description VALUE] [--acceptance VALUE]...\n\nARGS:\n  id  work item id\n\nFLAGS:\n  --description  new description\n  --acceptance  acceptance criteria\n";

#[test]
fn help_renders_subcommand_spec() {
    let mut interp = interp_for(PROGRAM);
    let result = interp
        .call("test.cli_demo.help_for_update", &[])
        .expect("help_for_update runs");
    assert_eq!(text(&interp, &result), EXPECTED_HELP);
}

#[test]
fn missing_required_positional_returns_parse_err() {
    let mut interp = interp_for(PROGRAM);
    let result = interp
        .call("test.cli_demo.parse_missing_required", &[])
        .expect("parse_missing runs");
    assert_eq!(
        entity_short_name(&interp, &result).as_deref(),
        Some("parse_err")
    );
    let err = match &result {
        Value::Entity { .. } => field(&interp, &result, "error", 0),
        _ => panic!("expected parse_err entity"),
    };
    assert_eq!(
        entity_short_name(&interp, &err).as_deref(),
        Some("missing_required")
    );
}

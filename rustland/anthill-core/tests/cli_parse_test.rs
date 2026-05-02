//! Integration tests for the stdlib CLI argument parser
//! (`stdlib/anthill/cli/{spec,parse}.anthill`). Drives `parse_argv` on a
//! 3-subcommand sample program and asserts on the parsed result.

mod common;

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;

use common::interp_for;

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
    interp.kb().resolve_sym(sym).to_string()
}

fn entity_short_name(interp: &anthill_core::eval::Interpreter, v: &Value) -> Option<String> {
    match v {
        Value::Entity { functor, .. } => {
            let qn = name_of(interp, *functor);
            qn.rsplit('.').next().map(|s| s.to_string())
        }
        _ => None,
    }
}

#[test]
fn parses_update_subcommand_with_flag_and_repeated() {
    let mut interp = interp_for(PROGRAM);
    let result = interp.call("test.cli_demo.parse_update", &[]).expect("parse_update runs");

    // Expect: parse_ok(ParsedArgs("update", [Binding("acceptance","cargo-test"),
    //                                         Binding("description","x"),
    //                                         Binding("id","WI-001")]))
    // (bindings are accumulated by cons, so order is reverse of the argv pass.)
    assert_eq!(entity_short_name(&interp, &result).as_deref(), Some("parse_ok"));

    let parsed = match &result {
        Value::Entity { pos, .. } => pos.first().cloned().expect("parse_ok payload"),
        _ => panic!("expected parse_ok entity"),
    };
    assert_eq!(entity_short_name(&interp, &parsed).as_deref(), Some("ParsedArgs"));

    let (spec_name, bindings) = match &parsed {
        Value::Entity { pos, .. } => (pos[0].clone(), pos[1].clone()),
        _ => panic!("expected ParsedArgs entity"),
    };
    assert_eq!(spec_name.as_str(), Some("update"));

    // Walk the bindings list cons spine, collect (name, value) pairs.
    let mut pairs: Vec<(String, String)> = Vec::new();
    let mut cur = bindings;
    loop {
        match cur {
            Value::Entity { functor, pos, .. } => {
                let name = name_of(&interp, functor);
                if name.ends_with(".nil") || name == "nil" {
                    break;
                }
                if name.ends_with(".cons") || name == "cons" {
                    let h = pos[0].clone();
                    let t = pos[1].clone();
                    let (n, v) = match h {
                        Value::Entity { pos: bp, .. } => {
                            (bp[0].as_str().unwrap_or("").to_string(),
                             bp[1].as_str().unwrap_or("").to_string())
                        }
                        _ => panic!("expected Binding entity, got {h:?}"),
                    };
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
    assert_eq!(pairs, vec![
        ("acceptance".to_string(), "cargo-test".to_string()),
        ("description".to_string(), "x".to_string()),
        ("id".to_string(), "WI-001".to_string()),
    ]);
}

#[test]
fn unknown_subcommand_returns_parse_err() {
    let mut interp = interp_for(PROGRAM);
    let result = interp.call("test.cli_demo.parse_unknown", &[]).expect("parse_unknown runs");
    assert_eq!(entity_short_name(&interp, &result).as_deref(), Some("parse_err"));
    let err = match &result {
        Value::Entity { pos, .. } => pos.first().cloned().expect("parse_err payload"),
        _ => panic!("expected parse_err entity"),
    };
    assert_eq!(entity_short_name(&interp, &err).as_deref(), Some("unknown_subcommand"));
}

// Golden help-text. Bindings are accumulated by cons, so flag/repeat order
// follows declaration order; positional appears before flags in our format.
const EXPECTED_HELP: &str = "update an item\n\nUSAGE: update <id> [--description VALUE] [--acceptance VALUE]...\n\nARGS:\n  id  work item id\n\nFLAGS:\n  --description  new description\n  --acceptance  acceptance criteria\n";

#[test]
fn help_renders_subcommand_spec() {
    let mut interp = interp_for(PROGRAM);
    let result = interp.call("test.cli_demo.help_for_update", &[]).expect("help_for_update runs");
    assert_eq!(result.as_str(), Some(EXPECTED_HELP));
}

#[test]
fn missing_required_positional_returns_parse_err() {
    let mut interp = interp_for(PROGRAM);
    let result = interp.call("test.cli_demo.parse_missing_required", &[]).expect("parse_missing runs");
    assert_eq!(entity_short_name(&interp, &result).as_deref(), Some("parse_err"));
    let err = match &result {
        Value::Entity { pos, .. } => pos.first().cloned().expect("parse_err payload"),
        _ => panic!("expected parse_err entity"),
    };
    assert_eq!(entity_short_name(&interp, &err).as_deref(), Some("missing_required"));
}

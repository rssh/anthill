//! A type written through an alias keeps the name it was written by.
//!
//! THE RULE. A type alias written bare in an operation parameter's type is the type it
//! stands for to everything that reads the type — the checks, dispatch, the index, a rule —
//! and a mismatch message leads with the name as written: `expected IntBox (Box[V =
//! Int64]), got String`.
//!
//! HOW. The parameter's type is lowered to an occurrence that holds the alias beside the
//! type it stands for (`TypeNode::Aliased`); the carrier-neutral view reads the type, and
//! the name is read by `written_alias` alone.
//!
//! BEFORE. The alias was replaced by the type it stands for where it was lowered, and the
//! message said `expected Box[V = Int64], got String`.
//!
//! CONTROLS — measured, each piece backed out on its own:
//!
//!   the name in the message (`render_mismatch_pair` showing each side as the type it is,
//!   as it did) — FAIL:
//!     a_mismatch_names_the_alias_as_written
//!     a_mismatch_names_an_alias_inside_a_type
//!   the node itself (`Loader::alias_nodes` never set, so the alias lowers to its type's
//!   term) — FAIL: the two above, and
//!     the_node_carrier_control_is_what_the_environment_asked_for
//!   a row's tail bound to a label written through an alias (`bind_row_tail` refusing every
//!   label that is no term) — FAIL:
//!     a_row_variable_takes_a_label_written_through_an_alias
//!   a function slot's label read as the row holding it on any carrier
//!   (`canonical_effects_row` handing a non-term binding on as it stands) — FAIL:
//!     a_function_slot_at_a_label_written_through_an_alias_is_charged_that_label
//!   the slot's charge asked of the binding on any carrier
//!   (`callable_effect_present_values` reading a term alone) — FAIL: the same test.
//!
//!   PASS EITHER WAY, by design:
//!     an_alias_typed_parameter_is_the_type_it_stands_for — the fence: what the node must
//!       not change. `wi_zy11j_alias_typed_value_test` holds the rest of it.
//!     a_rule_reads_the_type_and_no_alias — the fence for a rule: the same answers with
//!       the alias lowered to its type's term.
//!     a_type_written_without_an_alias_is_shown_once — the other side of the message.

use std::io::Write;

use anthill_core::eval::Value;

use crate::common::{interp_for, load_errors_of, load_kb_with, query_unary};

fn source(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace test.{ns}
  import anthill.prelude.{{Int64, String, Bool, List, Function, Error, ErrorTag, Result}}
  sort Box
    sort V = ?
    entity mk(v: V)
  end
  sort IntBox = Box[V = Int64]
  sort Money = Int64
  sort Oops = String
{body}
end
"#
    )
}

/// Load, call `test.<ns>.go()`, and hand back the integer it answers.
fn run(ns: &str, body: &str) -> i64 {
    let mut interp = interp_for(&source(ns, body));
    match interp.call(&format!("test.{ns}.go"), &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{ns}: expected an Int64, got {other:?}"),
    }
}

/// The one refusal of a source that must not load.
fn refusal(ns: &str, body: &str) -> String {
    let errs = load_errors_of(&source(ns, body));
    assert_eq!(errs.len(), 1, "{ns}: one refusal: {errs:#?}");
    errs.into_iter().next().unwrap()
}

// ── the type it stands for ──────────────────────────────────────────────────

/// A parameter typed by an alias takes a value of the type, hands it to that type's
/// operations, and is told apart from another instance.
#[test]
fn an_alias_typed_parameter_is_the_type_it_stands_for() {
    assert_eq!(
        run(
            "awnfence",
            "  operation unbox(b: IntBox) -> Int64 = b.v\n  operation pay(m: Money) -> Int64 = m + 1\n  \
             operation go() -> Int64 = unbox(Box.mk(4)) + pay(2)"
        ),
        7
    );
}

/// A rule over the reflect relations reads the parameter's type, and no alias: the
/// `FieldInfo` of `pay(m: Money)` holds `Int64` to a goal that asks for it, and is no
/// answer to one that asks for `Money`. (What that goal does find is every operation whose
/// one parameter is a type variable, which takes any type.)
#[test]
fn a_rule_reads_the_type_and_no_alias() {
    let mut kb = load_kb_with(&source(
        "awnrule",
        "  import anthill.reflect.{OperationInfo, FieldInfo}\n  \
         operation pay(m: Money) -> Int64 = m + 1\n  \
         fact asks(Int64)\n  fact asks_by_alias(Money)\n  \
         rule takes_one_int(?op) :- asks(?t), OperationInfo(name: ?op, params: [FieldInfo(name: ?, type_name: ?t)])\n  \
         rule takes_one_money(?op) :- asks_by_alias(?t), OperationInfo(name: ?op, params: [FieldInfo(name: ?, type_name: ?t)])",
    ));
    let pay = kb.resolve_symbol("test.awnrule.pay");
    let answers = |kb: &mut anthill_core::kb::KnowledgeBase, rule: &str| -> Vec<anthill_core::intern::Symbol> {
        query_unary(kb, rule)
            .into_iter()
            .filter_map(|(v, _)| anthill_core::eval::value_functor(kb, &v))
            .collect()
    };
    assert!(answers(&mut kb, "test.awnrule.takes_one_int").contains(&pay), "`pay` takes an `Int64`");
    assert!(!answers(&mut kb, "test.awnrule.takes_one_money").contains(&pay), "its slot holds no alias");
}

// ── the name it was written by ──────────────────────────────────────────────

/// The side written through an alias leads with the alias, and keeps the type it is.
#[test]
fn a_mismatch_names_the_alias_as_written() {
    let refused = refusal(
        "awnname",
        "  operation unbox(b: IntBox) -> Int64 = b.v\n  operation go() -> Int64 = unbox(\"s\")",
    );
    assert!(
        refused.contains("unbox.b (op-arg): expected IntBox (Box[V = Int64]), got String"),
        "{refused}"
    );
    // … on the ACTUAL side too: a value of an alias-typed parameter, handed on.
    let refused = refusal(
        "awnactual",
        "  operation show(s: String) -> Int64 = 1\n  operation via(m: Money) -> Int64 = show(m)\n  \
         operation go() -> Int64 = via(1)",
    );
    assert!(
        refused.contains("show.s (op-arg): expected String, got Money (Int64)"),
        "{refused}"
    );
}

/// An alias written inside a type is shown where it was written, and the whole type it
/// is once.
#[test]
fn a_mismatch_names_an_alias_inside_a_type() {
    let refused = refusal(
        "awninside",
        "  operation total(bs: List[T = IntBox]) -> Int64 = 0\n  operation go() -> Int64 = total([\"s\"])",
    );
    assert!(
        refused.contains("expected List[T = IntBox] (List[T = Box[V = Int64]]), got List[T = String]"),
        "{refused}"
    );
}

/// A type no alias was written in is shown once, as it always was.
#[test]
fn a_type_written_without_an_alias_is_shown_once() {
    let refused = refusal(
        "awnplain",
        "  operation unbox(b: Box[V = Int64]) -> Int64 = b.v\n  operation go() -> Int64 = unbox(\"s\")",
    );
    assert!(
        refused.contains("unbox.b (op-arg): expected Box[V = Int64], got String"),
        "{refused}"
    );
}

// ── two readers only an alias-carried type reaches ──────────────────────────

/// A callee's row variable takes what is left of a callback's row, a label written
/// through an alias among it: over `body: () -> Int64 @ {Error[P], Error[Oth]}` handed to
/// `Error.reify`, whose row is `{Error[T1], Rho}`, `Rho` is `{Error[Oth]}`. Refused,
/// "expected a type for 'Rho', got unconstrained", while a label that is no term could
/// not be bound to a tail.
#[test]
fn a_row_variable_takes_a_label_written_through_an_alias() {
    let body = "  import anthill.prelude.Result.{ok, err}\n  \
        sort Boom\n    entity boom(why: String)\n  end\n  \
        sort Other\n    entity other(why: String)\n  end\n  \
        sort Oth = Other\n  \
        operation twoWays(n: Int64) -> Int64 effects {Error[Boom], Error[Other]} =\n    \
        if n < 0 then Error.raise(boom(\"negative\")) else if n > 100 then Error.raise(other(\"big\")) else n + 1\n  \
        operation guard[P](body: () -> Int64 @ {Error[P], Error[Oth]})\n      \
        -> Result[E = P, T = Int64] effects {Error[Other]}\n      \
        requires ErrorTag[T = P] =\n    Error.reify(body)\n  \
        operation go() -> Int64 effects {Error[Other]} =\n    \
        match guard(lambda () -> twoWays(7))\n      case ok(n) -> n\n      case err(_) -> 0";
    assert_eq!(run("awnrow", body), 8);
}

/// A function slot bound to a label written through an alias is the row holding that
/// label: applying it charges the label, and the slot admits a callback that raises it.
#[test]
fn a_function_slot_at_a_label_written_through_an_alias_is_charged_that_label() {
    let boom = "  operation boom(x: Int64) -> Int64 effects {Error[String]} = Error.raise(\"boom\")\n";
    let refused = refusal(
        "awnslot",
        &format!(
            "{boom}  operation apply(f: Function[A = Int64, B = Int64, E = Error[Oops]]) -> Int64 = f(1)\n  \
             operation go() -> Int64 = apply(boom)"
        ),
    );
    assert!(
        refused.contains("apply.effects (op-effects)") && refused.contains("undeclared effect: Error[T = String]"),
        "{refused}"
    );
    // Declared, the same program loads: the slot admits `boom`.
    let errs = load_errors_of(&source(
        "awnslotok",
        &format!(
            "{boom}  operation apply(f: Function[A = Int64, B = Int64, E = Error[Oops]]) -> Int64\n      \
             effects {{Error[String]}} = f(1)\n  \
             operation go() -> Int64 effects {{Error[String]}} = apply(boom)"
        ),
    ));
    assert!(errs.is_empty(), "{errs:#?}");
}

// ── the control ─────────────────────────────────────────────────────────────

/// THE NODE-CARRIER CONTROL, OBSERVED (`ANTHILL_TEST_NODE_CARRIER`, `scripts/test.sh`). A
/// parameter typed by an alias rides the occurrence carrier either way; a parameter typed
/// by a sort rides it exactly when the control is on. The carrier IS this test's subject —
/// it is what makes a control run mean something — and no other test asserts one.
#[test]
fn the_node_carrier_control_is_what_the_environment_asked_for() {
    let kb = load_kb_with(&source(
        "awncontrol",
        "  operation plain(x: Int64) -> Int64 = x\n  operation aliased(x: Money) -> Int64 = x",
    ));
    let on_a_node = |op: &str| {
        let sym = kb.resolve_symbol(&format!("test.awncontrol.{op}"));
        let info = anthill_core::kb::op_info::lookup_operation_info(&kb, sym).expect("operation");
        matches!(info.params[0].1, Value::Node(_))
    };
    let asked = std::env::var("ANTHILL_TEST_NODE_CARRIER").is_ok_and(|v| v == "1");
    let observed = on_a_node("plain");
    // Written to the handle directly, and in one write: libtest captures a passing test's
    // `eprintln!`, and this line is for the run's log.
    let line = format!(
        "node carrier OBSERVED by {}: {}\n",
        module_path!(),
        if observed { "A NODE for every sort" } else { "terms, a node where an alias is written" }
    );
    let _ = std::io::stderr().write_all(line.as_bytes());
    assert!(on_a_node("aliased"), "a parameter typed by an alias rides the node");
    assert_eq!(observed, asked, "the loader carried a sort as the environment did not ask");
}

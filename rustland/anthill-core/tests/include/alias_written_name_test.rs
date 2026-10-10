//! A type written through an alias keeps the name it was written by.
//!
//! THE RULE. A type alias written bare in an operation's parameter or result type, in a
//! const's, in the type arguments a call writes, or in the annotation of a `let` or of a
//! typed binder, is the type it stands for to everything that reads the type — the checks,
//! dispatch, the index, a rule — and a mismatch message leads with the name as written:
//! `expected IntBox (Box[V = Int64]), got String`. (`declared_field_type_readers_test`
//! holds an entity's field.)
//!
//! AN ANNOTATION'S NAME RIDES THE BINDER. A pattern's term has no place for the name, so
//! it holds the type the annotation stands for, and the binder's occurrence carries the
//! type as written beside it — one lowering, two renderings. One that holds a variable is
//! carried as the type alone: `let p: Pair[A = Money, B = ?a]` is told `expected Pair[A =
//! Int64, B = ?a]`.
//!
//! HOW. The declared type is lowered to an occurrence that holds the alias beside the
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
//!   a result type lowered without the node (`written_type_to_value` not used for it) —
//!   FAIL:
//!     a_result_type_keeps_the_alias_it_was_written_by
//!   with the node at a result type, each of these backed out — FAIL:
//!     the region check reading a term alone (`result_type_admits_region` answering no
//!     off the term carrier): a_fresh_cell_returned_through_an_alias_owes_its_effect,
//!     a_fresh_cell_inside_a_result_typed_through_an_alias_owes_its_effect
//!     the join's widening reading a term alone (`widen_value`):
//!     two_variants_named_through_aliases_join_at_their_sort
//!     the result-type lookup reading a term alone (`lookup_operation_return_type`):
//!     a_result_type_keeps_the_alias_it_was_written_by, its nullary half
//!
//!   a const's type lowered without the node (`load_const` calling
//!   `type_expr_to_value`) — FAIL:
//!     a_const_typed_by_an_alias_keeps_the_alias_it_was_written_by
//!   a call's bracket lowered without the node (`build_call_type_args`), or its written
//!   receiver (`build_recv_type`), each on its own — FAIL:
//!     a_type_argument_written_at_a_call_keeps_its_alias, at that half
//!
//!   an annotation lowered without the node (`lower_written_annotation` calling
//!   `type_expr_to_value`), or read back as a term alone (`pattern_annotation_value`
//!   without its carried-type arm) — FAIL:
//!     a_let_annotation_keeps_the_alias_it_was_written_by
//!     a_typed_binder_keeps_the_alias_it_was_written_by
//!   a `let`'s own annotation not placed on its pattern (the `let` frame handing
//!   `pattern_src` no annotation) — FAIL: the first of those.
//!   the search for an alias in the annotation stopping at an effect row
//!   (`value_holds_alias_node` answering no for an effect expression) — FAIL: the first,
//!   at its row.
//!   a typed binder's annotation not kept for its frame (`load_pattern_var` recording
//!   none) — FAIL: the second.
//!   a row printed in the order its carrier stores it (`row_display` joining the spine as
//!   it stands) — FAIL:
//!     a_row_in_an_annotation_written_through_an_alias_is_printed_in_the_rows_order
//!
//!   PASS EITHER WAY, by design:
//!     an_annotation_holding_a_variable_names_the_type_alone — the stated limit.
//!     an_alias_typed_parameter_is_the_type_it_stands_for — the fence: what the node must
//!       not change. `wi_zy11j_alias_typed_value_test` holds the rest of it.
//!     a_result_field_effect_is_checked_through_an_alias — the same fence at the result:
//!       the field path of `Modify[result.a]` is walked over the type the alias stands for.
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
/// one parameter is a type variable, which takes any type.) The result of `price() ->
/// Money` reads the same way.
#[test]
fn a_rule_reads_the_type_and_no_alias() {
    let mut kb = load_kb_with(&source(
        "awnrule",
        "  import anthill.reflect.{OperationInfo, FieldInfo}\n  \
         operation pay(m: Money) -> Int64 = m + 1\n  \
         operation price() -> Money = 5\n  \
         fact asks(Int64)\n  fact asks_by_alias(Money)\n  \
         rule takes_one_int(?op) :- asks(?t), OperationInfo(name: ?op, params: [FieldInfo(name: ?, type_name: ?t)])\n  \
         rule takes_one_money(?op) :- asks_by_alias(?t), OperationInfo(name: ?op, params: [FieldInfo(name: ?, type_name: ?t)])\n  \
         rule gives_int(?op) :- asks(?t), OperationInfo(name: ?op, return_type: ?t)\n  \
         rule gives_money(?op) :- asks_by_alias(?t), OperationInfo(name: ?op, return_type: ?t)",
    ));
    let pay = kb.resolve_symbol("test.awnrule.pay");
    let price = kb.resolve_symbol("test.awnrule.price");
    let answers = |kb: &mut anthill_core::kb::KnowledgeBase, rule: &str| -> Vec<anthill_core::intern::Symbol> {
        query_unary(kb, rule)
            .into_iter()
            .filter_map(|(v, _)| anthill_core::eval::value_functor(kb, &v))
            .collect()
    };
    assert!(answers(&mut kb, "test.awnrule.takes_one_int").contains(&pay), "`pay` takes an `Int64`");
    assert!(!answers(&mut kb, "test.awnrule.takes_one_money").contains(&pay), "its slot holds no alias");
    assert!(answers(&mut kb, "test.awnrule.gives_int").contains(&price), "`price` gives an `Int64`");
    assert!(!answers(&mut kb, "test.awnrule.gives_money").contains(&price), "its result holds no alias");
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

// ── a result type ───────────────────────────────────────────────────────────

/// An operation's result type keeps its alias as a parameter's does: the mismatch names
/// it, and a bare reference to a nullary operation is still its call.
#[test]
fn a_result_type_keeps_the_alias_it_was_written_by() {
    let refused = refusal(
        "awnresult",
        "  operation make() -> IntBox = \"s\"\n  operation go() -> Int64 = 1",
    );
    assert!(
        refused.contains("make.return (op-return): expected IntBox (Box[V = Int64]), got String"),
        "{refused}"
    );
    assert_eq!(
        run("awnnullary", "  operation unit() -> Money = 5\n  operation go() -> Int64 = unit + 1"),
        6
    );
}

/// An operation that returns a fresh cell owes `Modify[result]`, also when its result is
/// typed by an alias of the cell's sort.
#[test]
fn a_fresh_cell_returned_through_an_alias_owes_its_effect() {
    let refused = refusal(
        "awnregion",
        "  import anthill.prelude.{Cell}\n  sort Counter = Cell\n  \
         operation dup(n: Int64) -> Counter =\n    let c = Cell.new(n)\n    c\n  \
         operation go() -> Int64 = 1",
    );
    assert!(
        refused.contains("dup.effects (op-effects)") && refused.contains("Modify[T = result]"),
        "{refused}"
    );
}

/// … and when the cell sits inside the result's type: an element, a component, the result
/// of a function handed back.
#[test]
fn a_fresh_cell_inside_a_result_typed_through_an_alias_owes_its_effect() {
    for (ns, result, body) in [
        ("awnregionlist", "List[T = Counter]", "[c]"),
        ("awnregiontuple", "(Counter, Int64)", "(c, 1)"),
        ("awnregionarrow", "(x: Int64) -> Counter", "lambda x -> c"),
    ] {
        let refused = refusal(
            ns,
            &format!(
                "  import anthill.prelude.{{Cell}}\n  sort Counter = Cell[V = Int64]\n  \
                 operation mk(n: Int64) -> {result} =\n    let c = Cell.new(n)\n    {body}\n  \
                 operation go() -> Int64 = 1"
            ),
        );
        assert!(
            refused.contains("mk.effects (op-effects)") && refused.contains("Modify[T = result]"),
            "{ns}: {refused}"
        );
    }
}

/// An effect on a field of the result is checked against the result's type, read through
/// the alias: a field the type has is taken, one it has not is refused.
#[test]
fn a_result_field_effect_is_checked_through_an_alias() {
    let decls = "  import anthill.prelude.{Cell}\n  \
                 sort Two = (a: Cell[V = Int64], b: Cell[V = Int64])\n";
    let taken = load_errors_of(&source(
        "awnfield",
        &format!("{decls}  operation pair() -> Two\n    effects {{Modify[result.a], Modify[result.b]}}"),
    ));
    assert!(taken.is_empty(), "{taken:#?}");
    let refused = refusal(
        "awnfieldbad",
        &format!("{decls}  operation pair() -> Two\n    effects Modify[result.nonexistent]"),
    );
    assert!(
        refused.contains("field projection") && refused.contains("nonexistent"),
        "{refused}"
    );
}

/// Two branches typed by aliases of two variants of one sort join at that sort.
#[test]
fn two_variants_named_through_aliases_join_at_their_sort() {
    assert_eq!(
        run(
            "awnjoin",
            "  sort Animal\n    entity cat(n: Int64)\n    entity dog(n: Int64)\n  end\n  \
             sort Kitty = Animal.cat\n  sort Doggy = Animal.dog\n  \
             operation aCat() -> Kitty = cat(n: 1)\n  operation aDog() -> Doggy = dog(n: 2)\n  \
             operation go() -> Int64 =\n    let r = if false then aCat() else aDog()\n    \
             match r\n      case cat(n) -> n\n      case dog(n) -> n"
        ),
        2
    );
}

// ── a const ─────────────────────────────────────────────────────────────────

/// A const typed by an alias is a value of the type, and a mismatch names the alias on
/// whichever side the const stands: at its own value, and where it is handed on.
#[test]
fn a_const_typed_by_an_alias_keeps_the_alias_it_was_written_by() {
    assert_eq!(
        run("awnconst", "  const LIMIT: Money = 5\n  operation go() -> Int64 = LIMIT + 1"),
        6
    );
    let refused = refusal(
        "awnconstvalue",
        "  const LIMIT: Money = \"s\"\n  operation go() -> Int64 = 1",
    );
    assert!(
        refused.contains("LIMIT.value (const): expected Money (Int64), got String"),
        "{refused}"
    );
    let refused = refusal(
        "awnconstuse",
        "  const LIMIT: Money = 5\n  operation show(s: String) -> Int64 = 1\n  \
         operation go() -> Int64 = show(LIMIT)",
    );
    assert!(
        refused.contains("show.s (op-arg): expected String, got Money (Int64)"),
        "{refused}"
    );
}

// ── the type arguments a call writes ────────────────────────────────────────

/// A type argument written at a call, in its bracket or on its receiver, is the type it
/// stands for, and a mismatch against it names the alias.
#[test]
fn a_type_argument_written_at_a_call_keeps_its_alias() {
    let decls = "  sort Vault\n    sort V = ?\n    entity vault(v: V)\n    \
                 operation wrap(x: V) -> Vault[V = V] = vault(v: x)\n  end\n";
    assert_eq!(
        run(
            "awncall",
            &format!(
                "{decls}  operation go() -> Int64 =\n    \
                 Vault[V = Money].wrap(4).v + Vault.wrap[V = Money](5).v"
            )
        ),
        9
    );
    for (ns, call) in [
        ("awncallrecv", "Vault[V = Money].wrap(\"s\").v"),
        ("awncallbracket", "Vault.wrap[V = Money](\"s\").v"),
    ] {
        let refused = refusal(ns, &format!("{decls}  operation go() -> Int64 = {call}"));
        assert!(
            refused.contains("wrap.x (op-arg): expected Money (Int64), got String"),
            "{ns}: {refused}"
        );
    }
}

// ── an annotation ───────────────────────────────────────────────────────────

/// A `let` annotation written through an alias keeps the name: at its own value, inside
/// the type, on a pattern that is no single name, and where the name it binds is handed on.
#[test]
fn a_let_annotation_keeps_the_alias_it_was_written_by() {
    assert_eq!(
        run("awnlet", "  operation go() -> Int64 =\n    let x: Money = 4\n    x + 1"),
        5
    );
    for (ns, body, expected) in [
        (
            "awnletvalue",
            "    let x: Money = \"s\"\n    1",
            "x.annotation (let-binding): expected Money (Int64), got String",
        ),
        (
            "awnletbox",
            "    let b: IntBox = mk(v: \"s\")\n    1",
            "b.annotation (let-binding): expected IntBox (Box[V = Int64]), got Box[V = String]",
        ),
        (
            "awnletinside",
            "    let xs: List[T = Money] = [\"a\"]\n    1",
            "expected Money (Int64), got String",
        ),
        (
            "awnlettuple",
            "    let (a, b): (Money, String) = (1, 2)\n    a",
            "expected (_1: Money, _2: String) ((_1: Int64, _2: String)), got (_1: Int64, _2: Int64)",
        ),
        (
            "awnletuse",
            "    let x: Money = 4\n    show(x)",
            "show.s (op-arg): expected String, got Money (Int64)",
        ),
        (
            "awnletrow",
            "    let s: Lazy[E = {Error[Oops]}] = \"s\"\n    1",
            "expected Lazy[E = {Error[T = Oops]}] (Lazy[E = {Error[T = String]}]), got String",
        ),
    ] {
        let refused = refusal(
            ns,
            &format!(
                "  sort Lazy\n    sort E = ?\n    entity lazy(v: Int64)\n  end\n  \
                 operation show(s: String) -> Int64 = 1\n  operation go() -> Int64 =\n{body}"
            ),
        );
        assert!(refused.contains(expected), "{ns}: {refused}");
    }
}

/// A typed binder written through an alias keeps the name for the value it binds.
#[test]
fn a_typed_binder_keeps_the_alias_it_was_written_by() {
    let decls = "  operation show(s: String) -> Int64 = 1\n  \
                 operation ap(f: (Int64) -> Int64) -> Int64 = f(1)\n";
    assert_eq!(
        run(
            "awnbinder",
            &format!("{decls}  operation go() -> Int64 = ap(lambda (m: Money) -> m + 1)")
        ),
        2
    );
    let refused = refusal(
        "awnbinderuse",
        &format!("{decls}  operation go() -> Int64 = ap(lambda (m: Money) -> show(m))"),
    );
    assert!(
        refused.contains("show.s (op-arg): expected String, got Money (Int64)"),
        "{refused}"
    );
}

/// A row is printed in one order, whichever carrier its type rides: with a label written
/// through an alias, the row rides an occurrence, and reads as its twin without one does.
#[test]
fn a_row_in_an_annotation_written_through_an_alias_is_printed_in_the_rows_order() {
    for (ns, label) in [("awnrowplain", "Foo"), ("awnrowalias", "MyFoo")] {
        let refused = refusal(
            ns,
            &format!(
                "  sort Foo\n    entity foo\n  end\n  sort Bar\n    entity bar\n  end\n  \
                 sort Baz\n    entity baz\n  end\n  sort MyFoo = Foo\n  \
                 operation use(g: (x: Int64) -> Bool @ {{Error[Foo], Error[Bar], Error[Baz]}}) -> Bool effects {{Error[Foo], Error[Bar], Error[Baz]}} =\n    \
                 let h: (x: Int64) -> Bool @ {{Error[{label}], Error[Bar]}} = g\n    h(1)"
            ),
        );
        assert!(
            refused.contains("expected Int64 -> Bool @ {Error[T = Bar], Error[T = Foo]}, got"),
            "{ns}: {refused}"
        );
    }
}

/// An annotation that holds a variable is carried as the type it stands for alone.
#[test]
fn an_annotation_holding_a_variable_names_the_type_alone() {
    let refused = refusal(
        "awnopen",
        "  sort Pair\n    sort A = ?\n    sort B = ?\n    entity pair(a: A, b: B)\n  end\n  \
         operation pick(x: ?a) -> Int64 =\n    let p: Pair[A = Money, B = ?a] = \"s\"\n    1\n  \
         operation go() -> Int64 = 1",
    );
    assert!(
        refused.contains("p.annotation (let-binding): expected Pair[A = Int64, B = ?a], got String"),
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

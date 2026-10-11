//! WI-20261011-12VZB — a constructor written with every argument named, out of
//! declaration order, is the value its in-order spelling is.
//!
//! THE RULE. The canonical entity form is every argument named, in declaration order
//! (docs/design/entity-term-mapping.md §2). An operation body's node is stored as it is
//! written and read, as a term, in that form: by the `@[simp]` matcher through its view,
//! and by a call-site precondition through its term twin.
//!
//! BEFORE. `Pair.first(Pair.pair(b: 2, a: 7))` under `rule first(pair(a: ?a, b: ?b)) <=>
//! ?a @[simp]` loaded clean and died `OperationBodyMissing`: the discrimination tree
//! descends named keys in the order the view gives them, and the view gave them as
//! written. `need(Pair.pair(b: 2, a: 7))` under `requires Pair.big(p)` was a load error,
//! "expected precondition `big(pair(b: 2, a: 7))` provable at the call site". The
//! positional and mixed spellings were the same defect and went with WI-20261011-CR6GD.
//!
//! EVERY ROW HAS ITS OWN SOURCE: a row that shares a fixture with another measures the
//! fixture.
//!
//! CONTROLS — measured by having `KnowledgeBase::named_out_of_declared_order`, the gate
//! of the all-named reading, answer `false`, and running this file.
//!
//!   FAIL, each dying `OperationBodyMissing`:
//!     an_equation_fires_on_named_arguments_out_of_order
//!     an_equation_written_out_of_order_fires_on_both
//!     three_fields_fire_in_every_order
//!     a_constructor_under_another_is_read_in_order_too
//!     an_imported_constructor_name_is_read_too
//!     a_parametric_sorts_constructor_is_read_too
//!     the_call_is_read_wherever_an_operation_body_writes_it
//!   FAIL, refused at load for an unprovable precondition:
//!     a_precondition_is_proved_at_named_arguments_out_of_order
//!   FAIL, on the clause the refusal names — it was judged as written:
//!     a_precondition_that_does_not_hold_is_refused_for_the_fact
//!   With the VIEW's key order alone answering as written, the equation rows fail and
//!   the two precondition rows pass; with the TWIN alone, the reverse.
//!
//!   PASS either way, by design — what the change must not move:
//!     the_in_order_spelling_fires_as_it_did
//!     the_arguments_are_still_evaluated_in_the_order_written — the node is not
//!       reordered; this is the row a reordering where the body is built would fail
//!     a_named_tuple_keeps_its_written_order — its order is its identity
//!     the_value_is_one_value_in_either_order — the evaluator's half, which always held
//!     a_label_the_entity_does_not_declare_is_still_refused
//!
//!   WHAT ELSE IT MOVED: behind a seal, a later load's `@[simp]` rule headed by a
//!   constructor is refused where a sealed body writes that construction out of order —
//!   `wi_9bkz4_sealed_bodies_test::a_simp_rule_over_a_construction_written_out_of_order_-
//!   is_refused_behind_a_seal`. No operation body in the standard library, the examples
//!   or anthill-todo writes one (counted where the node is built: 0 of 15, of 27 in
//!   webots-modelling and of 75 in anthill-todo with two or more named arguments).
//!
//!   NOT COVERED, each measured with the change in place and failing the same way in
//!   every spelling: a constructor written with fewer arguments than it declares fields
//!   (`Tri.tri(c: 3, a: 1)`) matches no pattern (WI-20260827-XFB56); an equation does
//!   not see through a binding (`let p = Pair.pair(b: 2, a: 7)` then `Pair.first(p)`).
//!   And two sites `the_call_is_read_wherever_an_operation_body_writes_it` does not
//!   list, where an equation rewrote no call in any spelling. A match arm's GUARD: fixed
//!   beside this, `wi_12vzb_match_guard_stored_as_typed_test`. A `const`'s VALUE: `const
//!   c: Int64 = dbl(4)` under `rule dbl(?n) <=> ?n + ?n @[simp]` loads clean and dies
//!   `OperationBodyMissing` — the value is checked with no equation applied
//!   (`typing/sorts.rs`, `check_constant_bodies`), and is not this change's.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// `lib.<ns>` with a two-field `Pair`, an `Outer` that holds one, a three-field `Tri`
/// and a parametric `Gen`, each with an operation defined by an equation over its
/// constructor's pattern in declaration order; `outside` is written in `test.<ns>`.
fn shaped(ns: &str, outside: &str) -> String {
    format!(
        "namespace lib.{ns}\n  import anthill.prelude.{{Int64, Bool}}\n  sort Pair\n    entity pair(a: Int64, b: Int64)\n    operation first(p: Pair) -> Int64\n    rule first(pair(a: ?a, b: ?b)) <=> ?a @[simp]\n    rule big(pair(a: ?a, b: ?b)) :- ?a > 3\n  end\n  sort Outer\n    entity wrap(p: Pair, n: Int64)\n    operation inner(o: Outer) -> Int64\n    rule inner(wrap(p: pair(a: ?a, b: ?b), n: ?n)) <=> ?b @[simp]\n  end\n  sort Tri\n    entity tri(a: Int64, b: Int64, c: Int64)\n    operation mid(t: Tri) -> Int64\n    rule mid(tri(a: ?a, b: ?b, c: ?c)) <=> ?b @[simp]\n  end\n  sort Gen\n    sort V = ?\n    entity g(v: V, w: V)\n    operation un(x: Gen[V]) -> V\n    rule un(g(v: ?v, w: ?w)) <=> ?v @[simp]\n  end\nend\nnamespace test.{ns}\n  import anthill.prelude.{{Int64, Bool, String, Error}}\n  import lib.{ns}.{{Pair, Outer, Tri, Gen}}\n{outside}\nend\n"
    )
}

/// `need`, callable where `Pair.big` is provable of its argument.
const NEED: &str = "  operation need(p: Pair) -> Int64\n    requires Pair.big(p)\n  = p.a\n";

#[track_caller]
fn assert_runs(src: &str, entry: &str, expected: i64) {
    assert_eq!(run_int64(src, entry), Ok(expected), "{entry}");
}

// ── the view: an equation fires ─────────────────────────────────────────────

/// The ticket's first program.
#[test]
fn an_equation_fires_on_named_arguments_out_of_order() {
    assert_runs(
        &shaped(
            "vzbeq",
            "  operation go() -> Int64 = Pair.first(Pair.pair(b: 2, a: 7))",
        ),
        "test.vzbeq.go",
        7,
    );
}

/// The left-hand side written out of order is the same pattern: the load puts a rule's
/// text in declaration order. Before, it fired on the in-order call alone.
#[test]
fn an_equation_written_out_of_order_fires_on_both() {
    let src = "namespace test.vzblhs\n  import anthill.prelude.Int64\n  sort Pair\n    entity pair(a: Int64, b: Int64)\n    operation first(p: Pair) -> Int64\n    rule first(pair(b: ?b, a: ?a)) <=> ?a @[simp]\n  end\n  operation same() -> Int64 = Pair.first(Pair.pair(b: 2, a: 7))\n  operation other() -> Int64 = Pair.first(Pair.pair(a: 7, b: 2))\nend\n";
    assert_runs(src, "test.vzblhs.same", 7);
    assert_runs(src, "test.vzblhs.other", 7);
}

/// Every order of three fields that is not the declared one, and a positional argument
/// beside two named ones written out of order — which took the field no name took
/// before this change, and is here to stay so.
#[test]
fn three_fields_fire_in_every_order() {
    let src = shaped(
        "vzbtri",
        "  operation acb() -> Int64 = Tri.mid(Tri.tri(a: 1, c: 3, b: 2))\n  operation bac() -> Int64 = Tri.mid(Tri.tri(b: 2, a: 1, c: 3))\n  operation bca() -> Int64 = Tri.mid(Tri.tri(b: 2, c: 3, a: 1))\n  operation cab() -> Int64 = Tri.mid(Tri.tri(c: 3, a: 1, b: 2))\n  operation cba() -> Int64 = Tri.mid(Tri.tri(c: 3, b: 2, a: 1))\n  operation mixed() -> Int64 = Tri.mid(Tri.tri(2, c: 3, a: 1))",
    );
    for entry in ["acb", "bac", "bca", "cab", "cba", "mixed"] {
        assert_runs(&src, &format!("test.vzbtri.{entry}"), 2);
    }
}

/// One level down: the outer constructor out of order over a positional inner one, the
/// inner one out of order, and both.
#[test]
fn a_constructor_under_another_is_read_in_order_too() {
    let src = shaped(
        "vzbnest",
        "  operation outer() -> Int64 = Outer.inner(Outer.wrap(n: 9, p: Pair.pair(7, 2)))\n  operation inner() -> Int64 = Outer.inner(Outer.wrap(p: Pair.pair(b: 2, a: 7), n: 9))\n  operation both() -> Int64 = Outer.inner(Outer.wrap(n: 9, p: Pair.pair(b: 2, a: 7)))",
    );
    assert_runs(&src, "test.vzbnest.outer", 2);
    assert_runs(&src, "test.vzbnest.inner", 2);
    assert_runs(&src, "test.vzbnest.both", 2);
}

#[test]
fn an_imported_constructor_name_is_read_too() {
    assert_runs(
        &shaped(
            "vzbbare",
            "  import lib.vzbbare.Pair.{pair}\n  operation go() -> Int64 = Pair.first(pair(b: 2, a: 7))",
        ),
        "test.vzbbare.go",
        7,
    );
}

/// A sort with a parameter, at a literal and under a caller generic in the content.
#[test]
fn a_parametric_sorts_constructor_is_read_too() {
    let src = shaped(
        "vzbgen",
        "  operation own() -> Int64 = Gen.un(Gen.g(w: 1, v: 5))\n  operation at[X](x: X) -> X = Gen.un(Gen.g(w: x, v: x))\n  operation generic() -> Int64 = at(6)",
    );
    assert_runs(&src, "test.vzbgen.own", 5);
    assert_runs(&src, "test.vzbgen.generic", 6);
}

/// The places an operation body writes the call: under a lambda with a typed binder and
/// with none, as a dot on the construction, in a condition, as another call's argument
/// and in the arm of a `match`.
#[test]
fn the_call_is_read_wherever_an_operation_body_writes_it() {
    let src = shaped(
        "vzbsite",
        "  import lib.vzbsite.Pair.{pair}\n  operation typed() -> Int64 =\n    let f = lambda (x: Int64) -> Pair.first(Pair.pair(b: x, a: 7))\n    f(2)\n  operation untyped() -> Int64 =\n    let f = lambda x -> Pair.first(Pair.pair(b: x, a: 7))\n    f(2)\n  operation dot() -> Int64 = Pair.pair(b: 2, a: 7).first()\n  operation cond() -> Int64 = if Pair.first(Pair.pair(b: 2, a: 7)) > 3 then 1 else 0\n  operation twice(n: Int64) -> Int64 = n + n\n  operation arg() -> Int64 = twice(Pair.first(Pair.pair(b: 2, a: 7)))\n  operation arm(p: Pair) -> Int64 =\n    match p\n      case pair(a: x, b: y) -> Pair.first(Pair.pair(b: y, a: 7))\n  operation inArm() -> Int64 = arm(Pair.pair(1, 2))",
    );
    assert_runs(&src, "test.vzbsite.typed", 7);
    assert_runs(&src, "test.vzbsite.untyped", 7);
    assert_runs(&src, "test.vzbsite.dot", 7);
    assert_runs(&src, "test.vzbsite.cond", 1);
    assert_runs(&src, "test.vzbsite.arg", 14);
    assert_runs(&src, "test.vzbsite.inArm", 7);
}

// ── the twin: a precondition is proved ──────────────────────────────────────

/// The ticket's second program: the clause's head names the fields in declaration order,
/// the call does not.
#[test]
fn a_precondition_is_proved_at_named_arguments_out_of_order() {
    let src = shaped(
        "vzbpre",
        &format!("{NEED}  operation go() -> Int64 = need(Pair.pair(b: 2, a: 7))"),
    );
    assert_runs(&src, "test.vzbpre.go", 7);
}

/// …and where the fact does not hold the call is still refused — for the fact: the
/// clause is named as it was judged, in declaration order.
#[test]
fn a_precondition_that_does_not_hold_is_refused_for_the_fact() {
    let errs = load_errors_of(&shaped(
        "vzbpren",
        &format!("{NEED}  operation go() -> Int64 = need(Pair.pair(b: 2, a: 1))"),
    ));
    assert_refused_naming(
        &errs,
        &["need.requires", "`big(pair(a: 1, b: 2))`"],
        "a precondition that fails",
    );
}

// ── what the change must not move ───────────────────────────────────────────

/// The spelling that always matched.
#[test]
fn the_in_order_spelling_fires_as_it_did() {
    let src = shaped(
        "vzbnamed",
        &format!("{NEED}  operation eq() -> Int64 = Pair.first(Pair.pair(a: 7, b: 2))\n  operation pre() -> Int64 = need(Pair.pair(a: 7, b: 2))"),
    );
    assert_runs(&src, "test.vzbnamed.eq", 7);
    assert_runs(&src, "test.vzbnamed.pre", 7);
}

/// The node is read in declaration order and RUN in the order written: of two arguments
/// that each raise, the first written is the one that does.
#[test]
fn the_arguments_are_still_evaluated_in_the_order_written() {
    let src = shaped(
        "vzborder",
        "  operation boom(m: String) -> Int64 effects {Error[String]} = Error.raise(m)\n  operation go() -> Int64 effects {Error[String]} = Pair.pair(b: boom(\"b first\"), a: boom(\"a first\")).a",
    );
    let err = run_int64(&src, "test.vzborder.go").expect_err("an argument raises");
    // Raised where it ran, not refused where it was loaded.
    assert!(err.contains("did not run to an Int64"), "{err}");
    assert!(err.contains("b first"), "{err}");
    assert!(!err.contains("a first"), "{err}");
}

/// A named tuple's written order is its identity: each of two equations, over the two
/// orders of one pair of labels, fires on its own order and not on the other's.
#[test]
fn a_named_tuple_keeps_its_written_order() {
    let src = "namespace test.vzbtuple\n  import anthill.prelude.Int64\n  operation tg[A](t: A) -> Int64\n  rule tg((x: ?a, y: ?b)) <=> ?a @[simp]\n  rule tg((y: ?b, x: ?a)) <=> ?b @[simp]\n  operation xy() -> Int64 = tg((x: 7, y: 2))\n  operation yx() -> Int64 = tg((y: 2, x: 7))\nend\n";
    assert_runs(src, "test.vzbtuple.xy", 7);
    assert_runs(src, "test.vzbtuple.yx", 2);
}

/// The value built is one value in either order, and its fields are read by name.
#[test]
fn the_value_is_one_value_in_either_order() {
    let src = shaped(
        "vzbvalue",
        "  operation same() -> Int64 = if Pair.pair(b: 2, a: 7) = Pair.pair(a: 7, b: 2) then 1 else 0\n  operation fields() -> Int64 =\n    let p = Pair.pair(b: 2, a: 7)\n    p.a * 10 + p.b",
    );
    assert_runs(&src, "test.vzbvalue.same", 1);
    assert_runs(&src, "test.vzbvalue.fields", 72);
}

#[test]
fn a_label_the_entity_does_not_declare_is_still_refused() {
    let errs = load_errors_of(&shaped(
        "vzbunknown",
        "  operation go() -> Int64 = Pair.first(Pair.pair(b: 2, zzz: 7))",
    ));
    assert_refused_naming(&errs, &["'pair' has no field 'zzz'"], "an undeclared label");
}

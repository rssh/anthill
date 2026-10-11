//! WI-20261011-RM247 — a `@[simp]` equation defines a body-less operation of a data sort
//! whether or not the sort takes parameters (kernel-language.md §5.3).
//!
//! THE RULE. A sort with constructors is a data sort, and nothing provides one (§5.1). A
//! body-less operation it declares is the sort's own: no call of it is dispatched to a
//! provider, so its `@[simp]` equation is its definition and fires wherever the operation
//! is called — as it always did for a sort with no parameter. A parametric sort WITHOUT
//! constructors is a spec, and a law written in it still waits for a carrier that provides
//! it.
//!
//! BEFORE. A body-less operation of a sort with a parameter was read as a dispatched spec
//! operation whatever the sort was (`lookup_spec_op_dispatch`), and every reader of that
//! answer held the call to `Box` providing `Box`. The equation's guard never held: the
//! program loaded clean and the call died `OperationBodyMissing`. A caller generic in the
//! content was refused for a missing `requires Box[V = …]`, and a rule body for a missing
//! `provides Box[…]` — neither of which a program can write.
//!
//! EVERY ROW HAS ITS OWN SOURCE: a row that shares a fixture with another measures the
//! fixture.
//!
//! CONTROLS — measured with the data-sort test backed out of `lookup_spec_op_dispatch`.
//!
//!   FAIL, each loading clean and dying `OperationBodyMissing` at the call:
//!     the_equation_defines_the_operation
//!     the_bracket_spelling_of_the_parameter_is_the_same_sort
//!     a_dot_on_the_value_reaches_it
//!     an_imported_name_reaches_it
//!     a_call_inside_the_sort_reaches_it
//!     an_alias_of_the_sort_is_the_sort
//!     an_operation_with_no_parameter_of_the_sort_is_defined_too
//!     a_content_parameter_owes_the_sort_nothing
//!     two_values_of_the_sort_are_two_arguments
//!     a_sort_with_a_requirement_is_still_a_data_sort
//!     the_equation_fires_under_itself
//!   FAIL, refused at load for a `requires Box[V = …]`:
//!     a_caller_generic_in_the_content_reaches_it
//!     a_binder_with_no_written_type_reaches_it
//!   FAIL, refused at load for a `provides Box[…]`:
//!     a_rule_body_reaches_it
//!     a_goal_in_a_rule_body_reaches_it
//!     a_clause_backed_operation_is_reached_from_a_rule_body
//!   and `wi1043_bodyless_rule_body_test::the_walk_gate_is_the_two_halves_and_a_data_-
//!   sorts_body_less_operations`, on the list of the operations this is about.
//!
//!   PASS with the change backed out, by design — what it must not move:
//!     the_same_sort_without_a_parameter_runs
//!     a_host_backed_operation_runs — the host function answers before a provider is asked
//!     a_specs_law_still_waits_for_a_provider
//!     a_law_on_a_spec_that_is_its_own_carrier_still_waits
//!   The last two are the fence on the other side, measured with the test widened to
//!   every parametric sort: both FAIL, each loading clean with its law fired.
//!
//! A CONSTRUCTOR ON THE RIGHT-HAND SIDE — found while delivering the above, and the plain
//! sort's as much as the parametric one's. `rule wrap(?v) <=> mk(?v) @[simp]` leaves the
//! constructor's application where the call stood. A rule's text carries that as an
//! application node; the typer checks it as the construction it is, and eval had no
//! reading for it: the program loaded clean and died `unknown operation: …Box.mk`.
//!
//!   CONTROLS — measured with eval's constructor arm backed out. FAIL, each loading clean
//!   and dying `UnknownOperation` on the constructor:
//!     a_constructor_on_the_right_hand_side_constructs
//!     a_constructor_written_with_its_field_name_constructs
//!     a_plain_sorts_constructor_constructs_too
//!     a_constructor_under_a_constructor_constructs
//!     a_free_standing_entity_constructs
//!   PASS either way, by design: a_constructor_with_no_field_is_its_value — a name, not
//!   an application.
//!
//!   NOT COVERED, both measured with the arm in place. A constructor that shares its
//!   sort's name (`sort E { entity E(n: Int64) }`, `<=> E(n: ?v)`) is refused at load,
//!   read as `E` applied to type arguments. A tuple written on the right-hand side (`<=>
//!   (?a, ?a)`) loads clean and dies in eval, `unhandled Expr variant`: it arrives as the
//!   tuple node of a rule's text, which is another node eval has no reading for.

use anthill_core::eval::Value;

use crate::common::{
    assert_refused_naming, interp_for, load_errors_of, load_kb_with, query_unary, run_int64,
};

/// `lib.<ns>.Box[V]`, a data sort with one parameter, holding `members`; `outside` is
/// written in `test.<ns>`, which imports the sort.
fn boxed(ns: &str, members: &str, outside: &str) -> String {
    format!(
        "namespace lib.{ns}\n  import anthill.prelude.{{Int64, Bool}}\n  sort Box\n    sort V = ?\n    entity mk(v: V)\n    operation peek(b: Box[V]) -> V = b.v\n{members}\n  end\nend\nnamespace test.{ns}\n  import anthill.prelude.Int64\n  import lib.{ns}.Box\n{outside}\nend\n"
    )
}

/// The operation the ticket is about: no body, and an equation that is its definition.
const OPEN: &str = "    operation open(b: Box[V]) -> V\n    rule open(?b) <=> peek(?b) @[simp]";

#[track_caller]
fn assert_runs(src: &str, entry: &str, expected: i64) {
    assert_eq!(run_int64(src, entry), Ok(expected), "{entry}");
}

// ── the equation is the definition ──────────────────────────────────────────

#[test]
fn the_equation_defines_the_operation() {
    assert_runs(
        &boxed(
            "rm247def",
            OPEN,
            "  operation go() -> Int64 =\n    let b = Box.mk(4)\n    Box.open(b)",
        ),
        "test.rm247def.go",
        4,
    );
}

#[test]
fn the_bracket_spelling_of_the_parameter_is_the_same_sort() {
    assert_runs(
        "namespace lib.rm247br\n  sort Box[V]\n    entity mk(v: V)\n    operation peek(b: Box[V]) -> V = b.v\n    operation open(b: Box[V]) -> V\n    rule open(?b) <=> peek(?b) @[simp]\n  end\nend\nnamespace test.rm247br\n  import anthill.prelude.Int64\n  import lib.rm247br.Box\n  operation go() -> Int64 =\n    let b = Box.mk(4)\n    Box.open(b)\nend\n",
        "test.rm247br.go",
        4,
    );
}

/// The twin the ticket measured: one sort, no parameter. It ran before and runs now.
#[test]
fn the_same_sort_without_a_parameter_runs() {
    assert_runs(
        "namespace lib.rm247plain\n  import anthill.prelude.Int64\n  sort Box\n    entity mk(v: Int64)\n    operation peek(b: Box) -> Int64 = b.v\n    operation open(b: Box) -> Int64\n    rule open(?b) <=> peek(?b) @[simp]\n  end\nend\nnamespace test.rm247plain\n  import anthill.prelude.Int64\n  import lib.rm247plain.Box\n  operation go() -> Int64 =\n    let b = Box.mk(4)\n    Box.open(b)\nend\n",
        "test.rm247plain.go",
        4,
    );
}

// ── every spelling of the call ──────────────────────────────────────────────

#[test]
fn a_dot_on_the_value_reaches_it() {
    assert_runs(
        &boxed(
            "rm247dot",
            OPEN,
            "  operation go() -> Int64 =\n    let b = Box.mk(4)\n    b.open()",
        ),
        "test.rm247dot.go",
        4,
    );
}

#[test]
fn an_imported_name_reaches_it() {
    assert_runs(
        &boxed(
            "rm247imp",
            OPEN,
            "  import lib.rm247imp.Box.{open}\n  operation go() -> Int64 =\n    let b = Box.mk(4)\n    open(b)",
        ),
        "test.rm247imp.go",
        4,
    );
}

#[test]
fn a_call_inside_the_sort_reaches_it() {
    assert_runs(
        &boxed(
            "rm247in",
            &format!("{OPEN}\n    operation twice(b: Box[V]) -> V = open(b)"),
            "  operation go() -> Int64 = Box.twice(Box.mk(4))",
        ),
        "test.rm247in.go",
        4,
    );
}

#[test]
fn an_alias_of_the_sort_is_the_sort() {
    assert_runs(
        &boxed(
            "rm247alias",
            OPEN,
            "  sort IntBox = Box[V = Int64]\n  operation at(b: IntBox) -> Int64 = Box.open(b)\n  operation go() -> Int64 = at(Box.mk(4))",
        ),
        "test.rm247alias.go",
        4,
    );
}

// ── what the argument's type may be ─────────────────────────────────────────

/// The content is the caller's type parameter: the call names no provider and needs none.
/// It was refused at load, asking the caller for `requires Box[V = …]`.
#[test]
fn a_caller_generic_in_the_content_reaches_it() {
    assert_runs(
        &boxed(
            "rm247gen",
            OPEN,
            "  operation at[X](b: Box[V = X]) -> X = Box.open(b)\n  operation go() -> Int64 = at(Box.mk(4))",
        ),
        "test.rm247gen.go",
        4,
    );
}

/// The binder's type is not known when the call under it is read. The equation does not
/// depend on it: the operation is the sort's own, whatever the argument turns out to be.
#[test]
fn a_binder_with_no_written_type_reaches_it() {
    assert_runs(
        &boxed(
            "rm247lam",
            OPEN,
            "  operation go() -> Int64 =\n    let f = lambda b -> Box.open(b)\n    f(Box.mk(4))",
        ),
        "test.rm247lam.go",
        4,
    );
}

// ── which parameters the operation has ──────────────────────────────────────

#[test]
fn an_operation_with_no_parameter_of_the_sort_is_defined_too() {
    assert_runs(
        &boxed(
            "rm247zero",
            "    operation zero() -> Int64\n    rule zero() <=> 7 @[simp]",
            "  operation go() -> Int64 = Box.zero()",
        ),
        "test.rm247zero.go",
        7,
    );
}

/// `same` takes the sort's content and no value of the sort. Read as a spec operation its
/// argument was the carrier, and `Int64` was asked to provide `Box`.
#[test]
fn a_content_parameter_owes_the_sort_nothing() {
    assert_runs(
        &boxed(
            "rm247same",
            "    operation same(v: V) -> V\n    rule same(?v) <=> ?v @[simp]",
            "  operation go() -> Int64 = Box.same(4)",
        ),
        "test.rm247same.go",
        4,
    );
}

#[test]
fn two_values_of_the_sort_are_two_arguments() {
    assert_runs(
        &boxed(
            "rm247two",
            "    operation first(a: Box[V], b: Box[V]) -> V\n    rule first(?a, ?b) <=> peek(?a) @[simp]",
            "  operation go() -> Int64 = Box.first(Box.mk(4), Box.mk(5))",
        ),
        "test.rm247two.go",
        4,
    );
}

#[test]
fn a_sort_with_a_requirement_is_still_a_data_sort() {
    assert_runs(
        "namespace lib.rm247req\n  import anthill.prelude.{Int64, PartialEq}\n  sort Box\n    sort V = ?\n    requires PartialEq[T = V]\n    entity mk(v: V)\n    operation peek(b: Box[V]) -> V = b.v\n    operation open(b: Box[V]) -> V\n    rule open(?b) <=> peek(?b) @[simp]\n  end\nend\nnamespace test.rm247req\n  import anthill.prelude.Int64\n  import lib.rm247req.Box\n  operation go() -> Int64 =\n    let b = Box.mk(4)\n    Box.open(b)\nend\n",
        "test.rm247req.go",
        4,
    );
}

#[test]
fn the_equation_fires_under_itself() {
    assert_runs(
        &boxed(
            "rm247nest",
            OPEN,
            "  operation go() -> Int64 = Box.open(Box.open(Box.mk(Box.mk(4))))",
        ),
        "test.rm247nest.go",
        4,
    );
}

// ── a rule body ─────────────────────────────────────────────────────────────

/// The call in a rule body is the same call: its value is what the operand of `<=>` is.
#[test]
fn a_rule_body_reaches_it() {
    let mut kb = load_kb_with(&boxed(
        "rm247rule",
        OPEN,
        "  rule r(?x) :- ?x <=> Box.open(Box.mk(4))",
    ));
    let answers = query_unary(&mut kb, "test.rm247rule.r");
    assert!(
        matches!(answers.as_slice(), [(Value::Int(4), true)]),
        "the value the equation gives the call: {answers:?}"
    );
}

/// And under a test: the goal holds at the value the equation gives, and at no other.
#[test]
fn a_goal_in_a_rule_body_reaches_it() {
    let mut kb = load_kb_with(&boxed(
        "rm247goal",
        OPEN,
        "  rule held(?x) :- ?x <=> 1, Box.open(Box.mk(4)) = 4\n  rule other(?x) :- ?x <=> 1, Box.open(Box.mk(4)) = 5",
    ));
    let held = query_unary(&mut kb, "test.rm247goal.held");
    assert!(matches!(held.as_slice(), [(Value::Int(1), true)]), "{held:?}");
    let other = query_unary(&mut kb, "test.rm247goal.other");
    assert!(other.is_empty(), "{other:?}");
}

// ── the other ways such an operation is run ─────────────────────────────────

/// Clauses written under the operation back it as they back a plain sort's: the goal is
/// resolved through them. The rule body was refused at load, for a `provides Box[…]`.
#[test]
fn a_clause_backed_operation_is_reached_from_a_rule_body() {
    let mut kb = load_kb_with(&boxed(
        "rm247clause",
        "    operation open(b: Box[V]) -> V\n    rule open(mk(v: ?v), ?v) :- true\n    operation full(b: Box[V]) -> Bool\n    rule full(mk(v: ?v)) :- true",
        "  rule r(?x) :- Box.open(Box.mk(4), ?x)\n  rule held(?x) :- ?x <=> 1, Box.full(Box.mk(4))",
    ));
    let r = query_unary(&mut kb, "test.rm247clause.r");
    assert!(matches!(r.as_slice(), [(Value::Int(4), true)]), "{r:?}");
    let held = query_unary(&mut kb, "test.rm247clause.held");
    assert!(matches!(held.as_slice(), [(Value::Int(1), true)]), "{held:?}");
}

/// A host function registered for the operation runs it.
#[test]
fn a_host_backed_operation_runs() {
    let mut interp = interp_for(&boxed(
        "rm247host",
        "    operation tag(b: Box[V]) -> Int64",
        "  operation go() -> Int64 = Box.tag(Box.mk(4))",
    ));
    interp
        .register_builtin("lib.rm247host.Box.tag", |_, _| Ok(Value::Int(9)))
        .expect("the operation is declared");
    let answer = interp.call("test.rm247host.go", &[]);
    assert!(matches!(answer, Ok(Value::Int(9))), "{answer:?}");
}

// ── a constructor on the right-hand side ────────────────────────────────────

/// The equation that builds a value of the sort: its right-hand side is the constructor
/// applied, and the rewritten call constructs.
#[test]
fn a_constructor_on_the_right_hand_side_constructs() {
    assert_runs(
        &boxed(
            "rm247ctor",
            "    operation wrap(v: V) -> Box[V]\n    rule wrap(?v) <=> mk(?v) @[simp]",
            "  operation go() -> Int64 = Box.peek(Box.wrap(4))",
        ),
        "test.rm247ctor.go",
        4,
    );
}

#[test]
fn a_constructor_written_with_its_field_name_constructs() {
    assert_runs(
        &boxed(
            "rm247field",
            "    operation wrap(v: V) -> Box[V]\n    rule wrap(?v) <=> mk(v: ?v) @[simp]",
            "  operation go() -> Int64 = Box.peek(Box.wrap(4))",
        ),
        "test.rm247field.go",
        4,
    );
}

/// No parameter, and the operation and its equation written outside the sort: the same
/// death before, so it was never the parameter's.
#[test]
fn a_plain_sorts_constructor_constructs_too() {
    assert_runs(
        "namespace test.rm247plainctor\n  import anthill.prelude.Int64\n  sort Box\n    entity mk(v: Int64)\n    operation peek(b: Box) -> Int64 = b.v\n  end\n  operation wrap(v: Int64) -> Box\n  rule wrap(?v) <=> Box.mk(?v) @[simp]\n  operation go() -> Int64 = Box.peek(wrap(4))\nend\n",
        "test.rm247plainctor.go",
        4,
    );
}

/// A constructor of the library's, and one under it.
#[test]
fn a_constructor_under_a_constructor_constructs() {
    assert_runs(
        "namespace test.rm247nested\n  import anthill.prelude.{Int64, Option}\n  import anthill.prelude.Option.{some, none}\n  sort Box\n    sort V = ?\n    entity mk(v: V)\n    operation peek(b: Box[V]) -> V = b.v\n    operation deep(v: V) -> Option[T = Box[V]]\n    rule deep(?v) <=> some(mk(?v)) @[simp]\n  end\n  operation unwrap(o: Option[T = Box[V = Int64]]) -> Int64 =\n    match o\n      case some(b) -> Box.peek(b)\n      case none() -> 0\n  operation go() -> Int64 = unwrap(Box.deep(4))\nend\n",
        "test.rm247nested.go",
        4,
    );
}

#[test]
fn a_free_standing_entity_constructs() {
    assert_runs(
        "namespace test.rm247free\n  import anthill.prelude.Int64\n  entity Rec(n: Int64)\n  operation mkrec(v: Int64) -> Rec\n  rule mkrec(?v) <=> Rec(n: ?v) @[simp]\n  operation nof(r: Rec) -> Int64 = r.n\n  operation go() -> Int64 = nof(mkrec(4))\nend\n",
        "test.rm247free.go",
        4,
    );
}

/// A constructor with no field is a name on the right-hand side, not an application, and
/// was read as the value it is before.
#[test]
fn a_constructor_with_no_field_is_its_value() {
    assert_runs(
        "namespace test.rm247nullary\n  import anthill.prelude.Int64\n  sort Col\n    entity red\n    entity green\n    operation pick(n: Int64) -> Col\n    rule pick(?n) <=> red @[simp]\n    operation code(c: Col) -> Int64 =\n      match c\n        case red() -> 1\n        case green() -> 2\n  end\n  operation go() -> Int64 = Col.code(Col.pick(4))\nend\n",
        "test.rm247nullary.go",
        1,
    );
}

// ── a spec is still a spec ──────────────────────────────────────────────────

/// `Sp` has a parameter and no constructor: a spec. Its law holds of the carriers that
/// provide it, and `Int64` does not, so the call is not rewritten and is refused as the
/// call of a spec operation nothing supplies.
#[test]
fn a_specs_law_still_waits_for_a_provider() {
    assert_refused_naming(
        &load_errors_of(
            "namespace lib.rm247spec\n  import anthill.prelude.Int64\n  sort Sp\n    sort T = ?\n    operation f(x: T) -> Int64\n    rule f(?x) <=> 1 @[simp]\n  end\nend\nnamespace test.rm247spec\n  import anthill.prelude.Int64\n  import lib.rm247spec.Sp\n  operation go() -> Int64 = Sp.f(4)\nend\n",
        ),
        &["`anthill.prelude.Int64` provides no `lib.rm247spec.Sp`"],
        "a spec's law at a carrier that does not provide the spec",
    );
}

/// `W` receives on itself and has no constructor: a value typed `W` is some provider's,
/// and a law with a value on its right is not fired on it (WI-725's dual).
#[test]
fn a_law_on_a_spec_that_is_its_own_carrier_still_waits() {
    assert_refused_naming(
        &load_errors_of(
            "namespace lib.rm247self\n  import anthill.prelude.Int64\n  sort W\n    sort T = ?\n    operation flip(w: Self) -> Int64\n    rule flip(?w) <=> 7 @[simp]\n  end\nend\nnamespace test.rm247self\n  import anthill.prelude.Int64\n  import lib.rm247self.W\n  operation at(w: W) -> Int64 = W.flip(w)\nend\n",
        ),
        &["missing `requires W[T = …]`"],
        "a self-carried spec's law at an abstract value",
    );
}

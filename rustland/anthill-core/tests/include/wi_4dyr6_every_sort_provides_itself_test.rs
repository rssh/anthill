//! WI-20261003-4DYR6 — a call of a sort's operation is answered by its carrier's member,
//! whether or not the sort takes a type parameter (kernel-language.md §5.3).
//!
//! THE RULE. Every sort provides itself, by its own operations, and no sort is a spec more
//! than another. A call `S.op(…)` has a CARRIER — the sort of the argument standing at
//! `S`, or the type bound to the parameter of `S` the operation receives on, or `S` where
//! the operation has neither — and the carrier provides `S`: it is `S`, or it declares the
//! provision. Its member `op` answers, and `S`'s own where it declares none.
//!
//! BEFORE. Who answers was read off the DECLARATION: an operation was dispatched only
//! where its sort declared a type parameter (`spec_op_parent_sort`). So over a sort with
//! none — `sort Sp { operation size(s: Sp) -> Int64 }`, `Car provides Sp` with its own
//! `size` — `Sp.size(car(n: 1))` loaded clean and died `OperationBodyMissing`; with a
//! default body on `Sp.size` it answered the default, in silence. One unused `sort T = ?`
//! in `Sp` made both right. The same test read a sort with a parameter AND constructors
//! as one a provider answers for, and an operation that names no carrier at all as
//! waiting for one.
//!
//! EVERY ROW HAS ITS OWN SOURCE: a row that shares a fixture with another measures the
//! fixture.
//!
//! WHAT IS READ OFF THE DECLARING SORT. Nothing but that it may be provided — it has no
//! constructor (`spec_op_parent_sort`). Not a type parameter, and not whether a sort
//! provides it yet: the answer of a declaration does not move with what is loaded after
//! it. `sort_provides` answers that a sort provides itself, so where the carrier turns out
//! to be the sort the readers find its own operation. One gate asks more, the rule body's
//! (`spec_op_call_parent`: a type parameter or a provider), because a rule body is typed
//! and woven at load with its arguments unbound.
//!
//! CONTROLS — each list is measured with one piece backed out; the last says which rows
//! pass either way, by design.
//!
//! (1) the gates made to ask for a type parameter alone, as they did
//!     (`sort_may_be_provided`, `spec_op_call_parent`, and the owner test of
//!     `clause_defined_own_operation` back at "a data sort").
//!   FAIL, each loading clean and dying `OperationBodyMissing` on `Sp.…`:
//!     the_providers_member_answers
//!     an_abstract_receiver_is_answered_by_its_values_sort
//!     two_providers_each_answer_for_their_own_values
//!     a_dot_on_an_abstract_receiver_reaches_it
//!     an_imported_name_reaches_it
//!     a_constant_and_a_condition_reach_it
//!     a_binder_with_no_written_type_reaches_it
//!     an_alias_of_the_sort_is_the_sort
//!     a_provider_of_a_provider_answers
//!     a_member_that_returns_a_function_answers
//!     a_clause_defined_operation_of_a_provided_sort_is_dispatched
//!     an_operation_that_names_no_carrier_of_a_provided_sort_keeps_its_equation
//!     a_law_fires_at_a_value_typed_at_its_sort
//!     one_call_over_a_sort_and_its_provider_answers
//!     a_later_load_may_provide_an_unsealed_sort
//!     a_later_load_may_provide_a_sealed_sort
//!     a_clause_defined_operation_on_a_receiver_waits_for_a_later_provider
//!   FAIL, answering the default where the provider declares the member:
//!     a_providers_member_stands_before_the_default
//!   FAIL, answering nothing:
//!     a_rule_body_goal_is_answered_by_the_provider
//!   FAIL, loading clean where a refusal is due:
//!     a_clause_defined_operation_of_a_sort_nothing_provides_is_refused
//!   FAIL, on what the gates answer:
//!     the_gates_read_no_parameter_and_no_provider
//!   and `wi1043_bodyless_rule_body_test::the_walk_gate_is_the_two_halves_and_a_data_-
//!   sorts_operations`.
//!
//! (1b) the gates made to ask for a type parameter OR A PROVIDER — the answer following
//!     the knowledge base. Every program row passes: eval asks again when the call runs.
//!   FAIL, on what the gates answer:
//!     the_gates_read_no_parameter_and_no_provider
//!   and the `wi1043` row above, on `Float.pow`.
//!
//! (2) the constructor leg taken out of `clause_is_dispatchable` and `enclosing_is_spec`.
//!   FAIL, each refused at load:
//!     a_requirement_of_a_data_sort_with_a_parameter_is_a_refinement
//!     a_requirement_written_before_its_data_sort_is_a_refinement
//!     a_type_parameter_may_take_its_data_sorts_name
//!
//! (3) `signature_names_no_carrier` made to answer no.
//!   FAIL, loading clean and dying `OperationBodyMissing`:
//!     a_sort_nothing_provides_keeps_its_equation
//!     an_operation_that_names_no_carrier_is_the_sorts_own
//!     an_operation_that_names_no_carrier_of_a_provided_sort_keeps_its_equation
//!   FAIL, loading clean where a refusal is due:
//!     a_clause_defined_operation_of_a_sort_nothing_provides_is_refused
//!
//! (4) `sort_provides` made to answer no for a sort under itself, as the relation's rows
//!     alone do.
//!   FAIL, the provider's member answering where the law is due:
//!     a_law_fires_at_a_value_typed_at_its_sort
//!   and `wi939_contains_rename_test::set_contains_answers_over_the_symbolic_algebra`
//!   (undecided) and `wi_rm247_data_sort_equation_test::a_law_on_a_sort_that_is_its_own_-
//!   carrier_fires_at_the_sort` (9, the member).
//!
//! (5) the library's `Map` law for `contains` put back as `neq(get(?m, ?k), none)`.
//!   FAIL, refused at load for `PartialEq` at the VALUE type:
//!     map_contains_asks_nothing_of_the_values
//!   and `wi_brt4y_host_implemented_test::a_migrated_pure_operation_reduces_in_a_rule_body`.
//!
//! (6) the resolver's body-less arm made to take an operation the interpreter has a host
//!     function for (`reduce_op_value`).
//!   FAILS, the effectful host function running at a rule-body operand:
//!     `wi_vpewk_host_op_operand_test::a_host_op_runs_at_an_operand_behind_an_error_row_and_not_behind_a_clock_row`
//!     (its `Clock` row; until WI-20260827-NFXPZ the `Error` row was the effectful one).
//!
//! THE FENCES, each measured the other way.
//!   `signature_names_no_carrier` made to answer yes — FAIL, loading clean:
//!     an_operation_typed_at_the_parameter_still_waits_for_a_carrier
//!     a_clause_defined_operation_of_a_provided_sort_is_dispatched (refused instead)
//!     a_clause_defined_operation_on_a_receiver_waits_for_a_later_provider (refused)
//!     and `wi_rm247…::a_specs_law_still_waits_for_a_provider`.
//!   The equation guard firing for an operation that names no carrier whatever the sort,
//!   its parameter-or-provider legs dropped — FAILS, answering the equation's 1:
//!     a_requirement_directs_an_operation_that_names_no_carrier_to_its_provider
//!   The clause-defined refusal made to ask whether a provider is in sight — FAILS,
//!   refused at the library's load:
//!     a_clause_defined_operation_on_a_receiver_waits_for_a_later_provider
//!   The rule body's gate made to answer for every sort that may be provided: 35 rows of
//!   the workspace FAIL (wi_p7vp4, wi_nekr0, wi_9r5hn, wi_mhrn1, wi_prva2), a
//!   module-style sort's operations woven as dispatched and its goals typed as calls.
//!   The gates made to answer for a sort with constructors too: 13 rows of the workspace
//!   FAIL, six of them `wi_rm247`'s.
//!
//! PASS under all of them, by design — what the change must not move:
//!     the_one_parameter_twin_is_unchanged
//!     the_carriers_member_called_by_its_own_name_runs
//!     a_default_runs_by_the_sorts_name_and_through_a_dot
//!     a_sort_that_does_not_provide_is_refused_at_the_argument
//!     a_provider_that_backs_nothing_is_refused
//!     nothing_provides_a_sort_with_constructors
//!     a_type_parameter_may_not_take_the_name_of_a_sort_a_witness_answers_for
//!
//! NOT COVERED, each measured. In a RULE BODY that calls the operation on a head
//! variable (`rule r(?s, ?x) :- Sp.dflt(?s, ?x)`), a DEFAULTED operation of a sort that
//! also declares a body-less one answers the default where the provider declares the
//! member; the same rule over a sort with a type parameter gives no value, its
//! `find_dictionary` goal left as a residual, for the body-less operation too.
//!
//! PINNED TO RECIPES BY NAME, the rows about a later load: their subject is which load
//! the provider arrives in, so they may not follow the switch.

use anthill_core::eval::{self, Interpreter, Value};
use anthill_core::kb::load::{self, LoadOptions};
use anthill_core::kb::typing::{
    defaulted_spec_op_parent, lookup_spec_op_dispatch, spec_op_call_parent,
};
use anthill_core::kb::KnowledgeBase;

use crate::common::{
    assert_refused_naming, load_errors_of, load_in_a_later_call, load_kb_with, query_unary,
    recipe_load, rendered_load_errors, run_int64, LoadRecipe,
};

/// `test.<ns>`, holding `Sp` — no type parameter, no constructor — with `members`, then
/// `rest`: the sorts that provide it and the operations that call it.
fn program(ns: &str, members: &str, rest: &str) -> String {
    format!(
        "namespace test.{ns}\n  import anthill.prelude.{{Int64, Bool, List}}\n  sort Sp\n{members}\n  end\n{rest}\nend\n"
    )
}

/// The operation the ticket is about: declared by `Sp`, with nothing to run.
const SIZE: &str = "    operation size(s: Sp) -> Int64";

/// A sort with a constructor that provides `Sp` and declares the member.
fn carrier(sort: &str, ctor: &str, size: i64) -> String {
    format!(
        "  sort {sort}\n    entity {ctor}(n: Int64)\n    provides Sp\n    operation size(c: {sort}) -> Int64 = {size}\n  end\n"
    )
}

#[track_caller]
fn assert_runs(src: &str, entry: &str, expected: i64) {
    assert_eq!(run_int64(src, entry), Ok(expected), "{entry}");
}

// ── the ticket's two programs ───────────────────────────────────────────────

#[test]
fn the_providers_member_answers() {
    assert_runs(
        &program(
            "dyr6call",
            SIZE,
            &format!("{}  operation go() -> Int64 = Sp.size(car(n: 1))", carrier("Car", "car", 42)),
        ),
        "test.dyr6call.go",
        42,
    );
}

#[test]
fn an_abstract_receiver_is_answered_by_its_values_sort() {
    assert_runs(
        &program(
            "dyr6abs",
            SIZE,
            &format!(
                "{}  operation measure(s: Sp) -> Int64 = Sp.size(s)\n  operation go() -> Int64 = measure(car(n: 1))",
                carrier("Car", "car", 42)
            ),
        ),
        "test.dyr6abs.go",
        42,
    );
}

/// The twin the ticket measured: one unused parameter in `Sp`. It ran before and runs now.
#[test]
fn the_one_parameter_twin_is_unchanged() {
    let src = "namespace test.dyr6twin\n  import anthill.prelude.Int64\n  sort Sp\n    sort T = ?\n    operation size(s: Sp) -> Int64\n  end\n  sort Car\n    entity car(n: Int64)\n    provides Sp[T = Int64]\n    operation size(c: Car) -> Int64 = 42\n  end\n  operation measure(s: Sp) -> Int64 = Sp.size(s)\n  operation direct() -> Int64 = Sp.size(car(n: 1))\n  operation abstractly() -> Int64 = measure(car(n: 1))\nend\n";
    assert_runs(src, "test.dyr6twin.direct", 42);
    assert_runs(src, "test.dyr6twin.abstractly", 42);
}

#[test]
fn the_carriers_member_called_by_its_own_name_runs() {
    assert_runs(
        &program(
            "dyr6own",
            SIZE,
            &format!("{}  operation go() -> Int64 = car(n: 1).size()", carrier("Car", "car", 42)),
        ),
        "test.dyr6own.go",
        42,
    );
}

// ── a default, and the member that stands before it ─────────────────────────

/// `Sp.size` has a body. `Car` declares the member and `Van` does not: the default is
/// what fills the gap, and it shadows nothing. It answered 7 for both.
#[test]
fn a_providers_member_stands_before_the_default() {
    let src = program(
        "dyr6default",
        "    operation size(s: Sp) -> Int64 = 7",
        &format!(
            "{}  sort Van\n    entity van(n: Int64)\n    provides Sp\n  end\n  operation ofCar() -> Int64 = Sp.size(car(n: 1))\n  operation ofVan() -> Int64 = Sp.size(van(n: 1))",
            carrier("Car", "car", 42)
        ),
    );
    assert_runs(&src, "test.dyr6default.ofCar", 42);
    assert_runs(&src, "test.dyr6default.ofVan", 7);
}

/// A default that names no carrier is `Sp`'s own whoever provides `Sp`, and a provider
/// that declares no member reaches the default through a dot as through the sort's name.
#[test]
fn a_default_runs_by_the_sorts_name_and_through_a_dot() {
    let src = program(
        "dyr6helper",
        "    operation size(s: Sp) -> Int64 = 7\n    operation helper(x: Int64) -> Int64 = x + 1",
        "  sort Van\n    entity van(n: Int64)\n    provides Sp\n  end\n  operation byName() -> Int64 = Sp.helper(41)\n  operation byDot() -> Int64 = van(n: 1).size()",
    );
    assert_runs(&src, "test.dyr6helper.byName", 42);
    assert_runs(&src, "test.dyr6helper.byDot", 7);
}

#[test]
fn two_providers_each_answer_for_their_own_values() {
    let src = program(
        "dyr6two",
        SIZE,
        &format!(
            "{}{}  operation measure(s: Sp) -> Int64 = Sp.size(s)\n  operation ofCar() -> Int64 = measure(car(n: 1))\n  operation ofVan() -> Int64 = measure(van(n: 1))\n  operation both(a: Sp, b: Sp) -> List[T = Sp] = [a, b]\n  operation total() -> Int64 = List.foldLeft(both(car(n: 1), van(n: 1)), 0, lambda (acc, s) -> acc + Sp.size(s))",
            carrier("Car", "car", 40),
            carrier("Van", "van", 2)
        ),
    );
    assert_runs(&src, "test.dyr6two.ofCar", 40);
    assert_runs(&src, "test.dyr6two.ofVan", 2);
    assert_runs(&src, "test.dyr6two.total", 42);
}

// ── every spelling of the call ──────────────────────────────────────────────

#[test]
fn a_dot_on_an_abstract_receiver_reaches_it() {
    assert_runs(
        &program(
            "dyr6dot",
            SIZE,
            &format!(
                "{}  operation viaDot(s: Sp) -> Int64 = s.size()\n  operation go() -> Int64 = viaDot(car(n: 1))",
                carrier("Car", "car", 42)
            ),
        ),
        "test.dyr6dot.go",
        42,
    );
}

#[test]
fn an_imported_name_reaches_it() {
    assert_runs(
        &program(
            "dyr6import",
            SIZE,
            &format!(
                "{}  import test.dyr6import.Sp.{{size}}\n  operation go() -> Int64 = size(car(n: 1))",
                carrier("Car", "car", 42)
            ),
        ),
        "test.dyr6import.go",
        42,
    );
}

#[test]
fn a_constant_and_a_condition_reach_it() {
    let src = program(
        "dyr6const",
        SIZE,
        &format!(
            "{}  const c: Int64 = Sp.size(car(n: 1))\n  operation big(s: Sp) -> Int64 = if Sp.size(s) > 10 then 1 else 0\n  operation ofConst() -> Int64 = c\n  operation ofCondition() -> Int64 = big(car(n: 1))",
            carrier("Car", "car", 42)
        ),
    );
    assert_runs(&src, "test.dyr6const.ofConst", 42);
    assert_runs(&src, "test.dyr6const.ofCondition", 1);
}

#[test]
fn a_binder_with_no_written_type_reaches_it() {
    assert_runs(
        &program(
            "dyr6lambda",
            SIZE,
            &format!(
                "{}  operation go() -> Int64 = List.foldLeft([car(n: 1), car(n: 2)], 0, lambda (acc, c) -> acc + Sp.size(c))",
                carrier("Car", "car", 21)
            ),
        ),
        "test.dyr6lambda.go",
        42,
    );
}

#[test]
fn an_alias_of_the_sort_is_the_sort() {
    assert_runs(
        &program(
            "dyr6alias",
            SIZE,
            &format!(
                "{}  sort SpA = Sp\n  operation go() -> Int64 = SpA.size(car(n: 1))",
                carrier("Car", "car", 42)
            ),
        ),
        "test.dyr6alias.go",
        42,
    );
}

/// A rule body writes the goal: the result is one more column, and the provider's member
/// is what answers it.
#[test]
fn a_rule_body_goal_is_answered_by_the_provider() {
    let mut kb = load_kb_with(&program(
        "dyr6rule",
        SIZE,
        &format!("{}  rule r(?x) :- Sp.size(car(n: 1), ?x)", carrier("Car", "car", 42)),
    ));
    let answers = query_unary(&mut kb, "test.dyr6rule.r");
    assert!(
        matches!(answers.as_slice(), [(Value::Int(42), true)]),
        "the value the provider's member gives: {answers:?}"
    );
}

/// `Leaf` provides `Mid`, which provides `Sp`: a `Leaf` is an `Sp` through it, as a
/// `NonMonotonicStore` is a `Store` in the library.
#[test]
fn a_provider_of_a_provider_answers() {
    assert_runs(
        &program(
            "dyr6chain",
            SIZE,
            "  sort Mid\n    provides Sp\n    operation depth(m: Mid) -> Int64\n  end\n  sort Leaf\n    entity leaf(n: Int64)\n    provides Mid\n    operation size(c: Leaf) -> Int64 = 40\n    operation depth(c: Leaf) -> Int64 = 2\n  end\n  operation viaMid(m: Mid) -> Int64 = Mid.depth(m) + Sp.size(m)\n  operation go() -> Int64 = viaMid(leaf(n: 1))",
        ),
        "test.dyr6chain.go",
        42,
    );
}

/// The shape the ticket was found on: a member whose result is a function.
#[test]
fn a_member_that_returns_a_function_answers() {
    assert_runs(
        "namespace test.dyr6fn\n  import anthill.prelude.Int64\n  sort Sp\n    operation adder(s: Sp) -> (x: Int64) -> Int64\n  end\n  sort Car\n    entity car(n: Int64)\n    provides Sp\n    operation adder(c: Car) -> (x: Int64) -> Int64 = lambda x -> x + c.n\n  end\n  operation run(s: Sp) -> Int64 =\n    let f = Sp.adder(s)\n    f(2)\n  operation go() -> Int64 = run(car(n: 40))\nend\n",
        "test.dyr6fn.go",
        42,
    );
}

// ── what the carrier owes ───────────────────────────────────────────────────

/// `Car` declares the member and no provision: it is not an `Sp`, and the call is refused
/// where the argument is written.
#[test]
fn a_sort_that_does_not_provide_is_refused_at_the_argument() {
    assert_refused_naming(
        &load_errors_of(&program(
            "dyr6none",
            SIZE,
            "  sort Car\n    entity car(n: Int64)\n    operation size(c: Car) -> Int64 = 42\n  end\n  operation go() -> Int64 = Sp.size(car(n: 1))",
        )),
        &["size.s", "expected Sp, got Car"],
        "a carrier that is not the sort and does not provide it",
    );
}

#[test]
fn a_provider_that_backs_nothing_is_refused() {
    assert_refused_naming(
        &load_errors_of(&program(
            "dyr6unbacked",
            SIZE,
            "  sort Car\n    entity car(n: Int64)\n    provides Sp\n  end",
        )),
        &["provides 'test.dyr6unbacked.Sp' but backs no operation"],
        "a provision with no member and no default to fall to",
    );
}

#[test]
fn nothing_provides_a_sort_with_constructors() {
    assert_refused_naming(
        &load_errors_of(
            "namespace test.dyr6data\n  import anthill.prelude.Int64\n  sort Box\n    entity mk(n: Int64)\n    operation size(b: Box) -> Int64 = 1\n  end\n  sort Car\n    entity car(n: Int64)\n    provides Box\n  end\nend\n",
        ),
        &["declares constructors", "nothing is-a a data sort"],
        "a provision of a sort with constructors",
    );
}

// ── the sort's own operation ────────────────────────────────────────────────

/// Nothing provides `Util` and it takes no parameter, so `Util` is the only carrier a
/// call of its operation can have: the equation is the operation's definition.
#[test]
fn a_sort_nothing_provides_keeps_its_equation() {
    assert_runs(
        "namespace test.dyr6module\n  import anthill.prelude.Int64\n  sort Util\n    operation f(x: Int64) -> Int64\n    rule f(?x) <=> ?x + 1 @[simp]\n  end\n  operation go() -> Int64 = Util.f(41)\nend\n",
        "test.dyr6module.go",
        42,
    );
}

/// The same sort with a parameter it uses nowhere. `f` names neither `Util` nor `T`, so
/// no argument and no result can stand at another carrier: it is `Util`'s own as above.
#[test]
fn an_operation_that_names_no_carrier_is_the_sorts_own() {
    assert_runs(
        "namespace test.dyr6nocarrier\n  import anthill.prelude.Int64\n  sort Util\n    sort T = ?\n    operation f(x: Int64) -> Int64\n    rule f(?x) <=> ?x + 1 @[simp]\n  end\n  operation go() -> Int64 = Util.f(41)\nend\n",
        "test.dyr6nocarrier.go",
        42,
    );
}

/// `Sp` takes no parameter and `Car` provides it. `ver` names no carrier, and a sort with
/// no parameter has no witness a call could select: `ver` is `Sp`'s own whoever provides
/// `Sp`, and its equation is its definition. `Car`'s member answers 99 so that the two
/// can be told apart.
#[test]
fn an_operation_that_names_no_carrier_of_a_provided_sort_keeps_its_equation() {
    assert_runs(
        &program(
            "dyr6ver",
            "    operation size(s: Sp) -> Int64\n    operation ver() -> Int64\n    rule ver() <=> 3 @[simp]",
            "  sort Car\n    entity car(n: Int64)\n    provides Sp\n    operation size(c: Car) -> Int64 = 39\n    operation ver() -> Int64 = 99\n  end\n  operation go() -> Int64 = Sp.ver() + Sp.size(car(n: 1))",
        ),
        "test.dyr6ver.go",
        42,
    );
}

/// The fence: with a type parameter AND a provider, a requirement names the provider
/// through the parameter, and the call is the provider's — `name` names no carrier, and
/// its equation is not fired over `W`'s member.
#[test]
fn a_requirement_directs_an_operation_that_names_no_carrier_to_its_provider() {
    assert_runs(
        "namespace test.dyr6slot\n  import anthill.prelude.Int64\n  sort Sp\n    sort T = ?\n    operation name() -> Int64\n    operation tag(x: T) -> Int64\n    rule name() <=> 1 @[simp]\n  end\n  sort W\n    entity w(n: Int64)\n    provides Sp[T = W]\n    operation name() -> Int64 = 42\n    operation tag(x: W) -> Int64 = 5\n  end\n  operation g[A](x: A) -> Int64 requires Sp[T = A] = Sp.name[T = A]()\n  operation go() -> Int64 = g(w(n: 1))\nend\n",
        "test.dyr6slot.go",
        42,
    );
}

/// `f` receives on `T`: its carrier is the argument's sort, which must provide `Sp`, and
/// `Int64` does not. The equation is a law of the providers and is not fired here.
#[test]
fn an_operation_typed_at_the_parameter_still_waits_for_a_carrier() {
    assert_refused_naming(
        &load_errors_of(
            "namespace test.dyr6law\n  import anthill.prelude.Int64\n  sort Sp\n    sort T = ?\n    operation f(x: T) -> Int64\n    rule f(?x) <=> 1 @[simp]\n  end\n  operation go() -> Int64 = Sp.f(4)\nend\n",
        ),
        &["`anthill.prelude.Int64` provides no `test.dyr6law.Sp`"],
        "a law at a carrier that does not provide the sort",
    );
}

/// Clauses answer a goal, not a call. Where the sort is the only carrier, a call of an
/// operation that has clauses and nothing to run is refused where it is written — as it
/// is for a namespace's operation and a data sort's.
#[test]
fn a_clause_defined_operation_of_a_sort_nothing_provides_is_refused() {
    assert_refused_naming(
        &load_errors_of(
            "namespace test.dyr6clauses\n  import anthill.prelude.Int64\n  sort Util\n    operation open(b: Int64) -> Int64\n    rule open(?v, ?v) :- true\n  end\n  operation go() -> Int64 = Util.open(42)\nend\n",
        ),
        &["test.dyr6clauses.Util.open", "defined by clauses alone"],
        "a call of a clause-defined operation no provider can answer",
    );
}

/// Where a sort provides it, the call is the dispatch's: `Car`'s member runs.
#[test]
fn a_clause_defined_operation_of_a_provided_sort_is_dispatched() {
    assert_runs(
        &program(
            "dyr6dispatched",
            "    operation size(s: Sp) -> Int64\n    rule size(?s, 7) :- true",
            &format!("{}  operation go() -> Int64 = Sp.size(car(n: 1))", carrier("Car", "car", 42)),
        ),
        "test.dyr6dispatched.go",
        42,
    );
}

// ── what is read off the declaring sort ─────────────────────────────────────

/// Nothing but that it may be provided. `Lone` takes no type parameter and nothing
/// provides it, and its operations are answered for as `Wide`'s are, which takes one: the
/// answer of a declaration does not move with what is loaded after it. `Held` has a
/// constructor, and nothing provides a data sort. A rule body's gate is the one that
/// asks more — a parameter or a provider — and `Lone` has neither.
///
/// `Held.open` is defined by a `@[simp]` equation rather than a body: a data sort's
/// body-less member with no definition is refused at load (WI-20260909-M8QWJ), and a body
/// would answer `lookup_spec_op_dispatch` before the declaring sort is read.
#[test]
fn the_gates_read_no_parameter_and_no_provider() {
    let kb = load_kb_with(
        "namespace test.dyr6gate\n  import anthill.prelude.Int64\n  sort Lone\n    operation open(l: Lone) -> Int64\n    operation peek(l: Lone) -> Int64 = 1\n  end\n  sort Wide\n    sort T = ?\n    operation open(w: Wide) -> Int64\n    operation peek(w: Wide) -> Int64 = 1\n  end\n  sort Held\n    entity held(n: Int64)\n    operation open(h: Held) -> Int64\n    rule open(?h) <=> 0 @[simp]\n    operation peek(h: Held) -> Int64 = 1\n  end\nend\n",
    );
    let op = |name: &str| {
        kb.try_resolve_symbol(&format!("test.dyr6gate.{name}"))
            .unwrap_or_else(|| panic!("`{name}` is declared"))
    };
    for sort in ["Lone", "Wide"] {
        assert!(
            lookup_spec_op_dispatch(&kb, op(&format!("{sort}.open"))).is_some(),
            "`{sort}.open` has no body: it is dispatched to its carrier's member"
        );
        assert!(
            defaulted_spec_op_parent(&kb, op(&format!("{sort}.peek"))).is_some(),
            "`{sort}.peek` has a body: it is a default its carrier may override"
        );
    }
    assert!(
        lookup_spec_op_dispatch(&kb, op("Held.open")).is_none()
            && defaulted_spec_op_parent(&kb, op("Held.peek")).is_none(),
        "nothing provides a sort with constructors: `Held`'s operations are its own"
    );
    assert!(
        spec_op_call_parent(&kb, op("Wide.open")).is_some()
            && spec_op_call_parent(&kb, op("Lone.open")).is_none(),
        "a rule body's walk asks a type parameter or a provider"
    );
}

// ── a sort provides itself ──────────────────────────────────────────────────

/// A law written in `Sp` is the law of every carrier, and `Sp` is one: at `s: Sp` the
/// value is `Sp`'s own or a provider's, so the law fires. `Car`'s `twice` answers 0 so
/// that the two can be told apart: 42 is the law.
#[test]
fn a_law_fires_at_a_value_typed_at_its_sort() {
    assert_runs(
        &program(
            "dyr6self",
            "    operation size(s: Sp) -> Int64\n    operation twice(s: Sp) -> Int64\n    rule twice(?s) <=> size(?s) + size(?s) @[simp]",
            "  sort Car\n    entity car(n: Int64)\n    provides Sp\n    operation size(c: Car) -> Int64 = 21\n    operation twice(c: Car) -> Int64 = 0\n  end\n  operation viaAbstract(s: Sp) -> Int64 = Sp.twice(s)\n  operation go() -> Int64 = viaAbstract(car(n: 1))",
        ),
        "test.dyr6self.go",
        42,
    );
}

/// The library's `Map` laws fire at a `Map` now, so they are held to what `Map` requires:
/// equality of its keys. `contains` is stated by the `put` that made the map, as `get` is.
/// It was `contains(?m, ?k) <=> neq(get(?m, ?k), none)`, which asks equality of the
/// VALUES: over a map of functions that law is a load error once it fires.
#[test]
fn map_contains_asks_nothing_of_the_values() {
    let src = "namespace test.dyr6map\n  import anthill.prelude.{Int64, String, Map, Bool}\n  operation ofFunctions() -> Int64 =\n    if Map.contains(Map.put(Map.empty(), \"a\", lambda (x: Int64) -> x), \"a\") then 42 else 0\n  operation present() -> Int64 =\n    if Map.contains(Map.put(Map.put(Map.empty(), \"a\", 1), \"b\", 2), \"a\") then 42 else 0\n  operation absent() -> Int64 =\n    if Map.contains(Map.put(Map.empty(), \"a\", 1), \"z\") then 0 else 42\nend\n";
    assert_runs(src, "test.dyr6map.ofFunctions", 42);
    assert_runs(src, "test.dyr6map.present", 42);
    assert_runs(src, "test.dyr6map.absent", 42);
}

// ── the readers that asked for a parameter alone ────────────────────────────

/// A `requires` clause over a sort with constructors names no provider — nothing provides
/// one — so it is a refinement, with a parameter as without. It was read as a dictionary
/// slot and the construction refused for `no impl provides Box`.
#[test]
fn a_requirement_of_a_data_sort_with_a_parameter_is_a_refinement() {
    let src = "namespace test.dyr6refines\n  import anthill.prelude.Int64\n  sort Box\n    sort V = ?\n    entity mk(v: V)\n  end\n  sort Narrow\n    requires Box[V = Int64]\n    entity narrow(n: Int64)\n    operation get(x: Narrow) -> Int64 = 42\n  end\n  operation takes(b: Box[V = Int64]) -> Int64 = 40\n  operation own() -> Int64 = Narrow.get(narrow(n: 1))\n  operation asBox() -> Int64 = takes(narrow(n: 1))\nend\n";
    assert_runs(src, "test.dyr6refines.own", 42);
    assert_runs(src, "test.dyr6refines.asBox", 40);
}

/// The same with the requiring sort written FIRST: what a `requires` clause is does not
/// follow the order the two sorts are declared in.
#[test]
fn a_requirement_written_before_its_data_sort_is_a_refinement() {
    assert_runs(
        "namespace test.dyr6forward\n  import anthill.prelude.Int64\n  sort Narrow\n    requires Box[V = Int64]\n    entity narrow(n: Int64)\n    operation get(x: Narrow) -> Int64 = 42\n  end\n  sort Box\n    sort V = ?\n    entity mk(v: V)\n  end\n  operation go() -> Int64 = Narrow.get(narrow(n: 1))\nend\n",
        "test.dyr6forward.go",
        42,
    );
}

/// A call selects a provider by its sort's short name only where a witness for the sort
/// can exist, and none can for a data sort: the name is free for a type parameter.
#[test]
fn a_type_parameter_may_take_its_data_sorts_name() {
    assert_runs(
        "namespace test.dyr6shadow\n  import anthill.prelude.Int64\n  sort Box\n    sort V = ?\n    entity mk(v: V)\n    operation same[Box](b: Box) -> Box = b\n  end\n  operation go() -> Int64 = Box.same(42)\nend\n",
        "test.dyr6shadow.go",
        42,
    );
}

#[test]
fn a_type_parameter_may_not_take_the_name_of_a_sort_a_witness_answers_for() {
    assert_refused_naming(
        &load_errors_of(
            "namespace test.dyr6key\n  import anthill.prelude.Int64\n  sort Sp\n    sort T = ?\n    operation size[Sp](s: Sp) -> Int64\n  end\nend\n",
        ),
        &["type parameter `Sp` collides with its own spec"],
        "a type parameter named as the sort whose provider a call selects by that name",
    );
}

// ── a later load ────────────────────────────────────────────────────────────

const LIB: &str = "namespace lib.dyr6seal\n  import anthill.prelude.Int64\n  sort Sp\n    operation size(s: Sp) -> Int64\n  end\n  operation measure(s: Sp) -> Int64 = Sp.size(s)\nend\n";

const A_PROVIDER_OF_THE_LIBRARYS_SORT: &str = "namespace test.dyr6seal\n  import anthill.prelude.Int64\n  import lib.dyr6seal.{Sp, measure}\n  sort Car\n    entity car(n: Int64)\n    provides Sp\n    operation size(c: Car) -> Int64 = 42\n  end\n  operation go() -> Int64 = measure(car(n: 1))\nend\n";

fn value(kb: KnowledgeBase, entry: &str) -> i64 {
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp).expect("standard builtins");
    match interp.call(entry, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{entry}` did not run to an Int64: {other:?}"),
    }
}

/// `lib` alone, in the standard library's call; `seal` says whether that load is sealed
/// before `program` is loaded into it.
fn later(lib: &str, program: &str, seal: bool) -> Result<KnowledgeBase, Vec<String>> {
    let (mut kb, _) =
        recipe_load(&[lib], None, LoadOptions::default(), LoadRecipe::OneShot, |_| {})
            .unwrap_or_else(|e| panic!("the library loads: {:?}", rendered_load_errors(e)));
    if seal {
        load::seal_declarations(&mut kb);
    }
    load_in_a_later_call(&mut kb, program, LoadOptions::default())
        .map(|_| kb)
        .map_err(rendered_load_errors)
}

fn then_the_program(seal: bool) -> Result<KnowledgeBase, Vec<String>> {
    later(LIB, A_PROVIDER_OF_THE_LIBRARYS_SORT, seal)
}

/// One call over both: the library's `measure` is typed with the provider in sight.
#[test]
fn one_call_over_a_sort_and_its_provider_answers() {
    let (kb, _) = recipe_load(
        &[LIB, A_PROVIDER_OF_THE_LIBRARYS_SORT],
        None,
        LoadOptions::default(),
        LoadRecipe::OneShot,
        |_| {},
    )
    .unwrap_or_else(|e| panic!("both load: {:?}", rendered_load_errors(e)));
    assert_eq!(value(kb, "test.dyr6seal.go"), 42);
}

/// Nothing sealed: the later load types the library's bodies again, and they learn of the
/// provider.
#[test]
fn a_later_load_may_provide_an_unsealed_sort() {
    let kb = then_the_program(false).unwrap_or_else(|e| panic!("the program loads: {e:?}"));
    assert_eq!(value(kb, "test.dyr6seal.go"), 42);
}

/// A sealed load's bodies are typed once, and `measure`'s was typed when nothing provided
/// `Sp`. Its receiver is typed at `Sp`, so the typer pinned no member to the call: who
/// answers is asked of the value when the call runs, and the provider that arrived later
/// is found there. A library may declare the sort and a program provide it.
#[test]
fn a_later_load_may_provide_a_sealed_sort() {
    let kb = then_the_program(true).unwrap_or_else(|e| panic!("the program loads: {e:?}"));
    assert_eq!(value(kb, "test.dyr6seal.go"), 42);
}

/// A library whose operation is defined by clauses, called on a receiver typed at the
/// sort, with no provider of its own. The call is the dispatch's, not the library's to be
/// refused for: the load that provides the sort brings the member that answers. Refused
/// at the library's load — "defined by clauses alone" — if the refusal asks whether a
/// provider is in sight.
#[test]
fn a_clause_defined_operation_on_a_receiver_waits_for_a_later_provider() {
    let lib = "namespace lib.dyr6late\n  import anthill.prelude.Int64\n  sort Sp\n    operation size(s: Sp) -> Int64\n    rule size(?s, 7) :- true\n  end\n  operation measure(s: Sp) -> Int64 = Sp.size(s)\nend\n";
    let program = "namespace test.dyr6late\n  import anthill.prelude.Int64\n  import lib.dyr6late.{Sp, measure}\n  sort Car\n    entity car(n: Int64)\n    provides Sp\n    operation size(c: Car) -> Int64 = 42\n  end\n  operation go() -> Int64 = measure(car(n: 1))\nend\n";
    for seal in [false, true] {
        let kb = later(lib, program, seal)
            .unwrap_or_else(|e| panic!("sealed: {seal} — the program loads: {e:?}"));
        assert_eq!(value(kb, "test.dyr6late.go"), 42, "sealed: {seal}");
    }
}

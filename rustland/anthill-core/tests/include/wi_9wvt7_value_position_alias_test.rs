//! WI-20260908-9WVT7 — a type alias written as a VALUE is the type it stands for (§5.1), and a
//! type application in a clause's term is the one term its type is (§5.4) — user, 2026-10-17.
//!
//! A. In an operation body `IntOpt` over `sort IntOpt = Option[T = Int64]` is the value
//!    `Option[T = Int64]` is: bare, through a chain, a `let`, a nested bracket, a dotted path,
//!    a `@[simp]` right-hand side, applied further (`IntPair[B = String]`, `IntPair[String]`),
//!    a slot left open (`sort Some = Box[V = ?]` is `Box`), the sort's own parameter read
//!    through its `TypeValue` clause, a tuple read as a bracket's entry writes it. The value was
//!    the alias's own name, which no type equals, and an application of one was refused.
//! B. In a clause's data slot and in a query the alias is the type it stands for as well, so a
//!    fact holding the one is found by a goal or a query writing the other. An alias of a tuple
//!    stays its name there: a tuple written in a data slot is a tuple of values, not a type.
//! C. A type application in a clause's term and in a query takes its positional and named
//!    inputs, in any order, as one term — `Pair[Int64, String]`, `Pair[A = Int64, B = String]`
//!    and `Pair[B = String, A = Int64]` are the term an operation body's value of the type is.
//!    They were three terms, each found by itself alone (the part of WI-20260823-53W12's
//!    reading of a clause's types decided here).
//!
//! WHAT FAILS UNDER WHICH BACK-OUT — MEASURED, each switched off alone in one build, over this
//! file and the whole `wi_tests` binary, where each moves only the rows named:
//!
//!   * the bare alias read as its own name →
//!     [`a_bare_alias_is_the_type_it_stands_for`], [`a_slot_the_alias_leaves_open_is_unwritten`],
//!     [`an_alias_of_the_sorts_parameter_is_read_through_its_clause`],
//!     [`an_alias_of_a_tuple_is_the_type_a_bracket_entry_writes`],
//!     [`a_fact_holding_an_alias_is_found_by_the_type`], [`a_query_reads_the_alias_too`],
//!     `alias_written_name_test::a_rule_reads_the_type_and_no_alias` and the rows without the
//!     clause of `wi_hzvqa_alias_receiver_test::an_alias_that_names_the_enclosing_parameter_is_at_that_parameter`;
//!   * an alias's application read as its own name →
//!     [`an_alias_applied_further_takes_both_bindings`],
//!     [`binding_again_what_the_alias_fixes_is_refused_once`],
//!     [`a_fact_holding_an_alias_is_found_by_the_type`], [`a_query_reads_the_alias_too`], and the
//!     alias spellings of [`a_type_application_in_a_clause_is_one_term`] and
//!     [`a_query_writes_a_type_application_as_one_term`];
//!   * a clause's type application kept as written →
//!     [`a_type_application_in_a_clause_is_one_term`],
//!     [`a_query_writes_a_type_application_as_one_term`], the applied halves of
//!     [`a_fact_holding_an_alias_is_found_by_the_type`] and [`a_query_reads_the_alias_too`],
//!     and `wi_tcsgt_structural_bracket_entry_test::a_positional_entry_in_a_clauses_term_is_the_named_one`.
//!
//!   PASS EITHER WAY, by design: [`an_alias_naming_the_sorts_parameter_outside_it_is_its_name`]
//!   and [`an_alias_of_a_tuple_stays_its_name_in_a_clause`] — the alias is read as written there.

use anthill_core::eval::Value;
use anthill_core::kb::resolve::ResolveConfig;

use crate::common::{
    assert_refused_naming, load_errors_of, load_kb_with, query_pattern_term, query_unary,
    run_int64, supply_invocation_imports,
};

/// The aliases and sorts the rows are about.
const DECLS: &str = "  sort IntOpt = Option[T = Int64]\n  sort MyInt = Int64\n  sort IntPair = \
                     Pair[A = Int64]\n  sort A1 = A2\n  sort A2 = Option[T = Int64]\n  sort AnyOpt \
                     = Option\n  sort Box\n    sort V = ?\n    entity mk(v: V)\n  end\n  sort Some = \
                     Box[V = ?]\n  sort P2 = (Int64, String)\n  sort Host\n    sort HB = Option[T = \
                     String]\n  end\n  sort Hold\n    entity held(t: Type, n: Int64)\n  end\n";

/// A program in `probe.<ns>` with the rows' declarations, `decls`, and `main`.
fn program(ns: &str, decls: &str, main: &str) -> String {
    format!(
        "namespace probe.{ns}\n  import anthill.prelude.{{Int64, String, Bool, List, Type, Option, \
         Pair, PartialEq}}\n  import anthill.reflect.{{TypeValue}}\n{DECLS}{decls}  operation \
         bit(c: Bool) -> Int64 = if c then 1 else 0\n  operation main() -> Int64 =\n    {main}\nend\n"
    )
}

fn run(ns: &str, decls: &str, main: &str) -> Result<i64, String> {
    run_int64(&program(ns, decls, main), &format!("probe.{ns}.main"))
}

/// The answers of `probe.<ns>.r(?n)`, sorted.
fn rule_answers(ns: &str, decls: &str) -> Vec<i64> {
    let mut kb = load_kb_with(&program(ns, decls, "0"));
    let mut ns_of: Vec<i64> = query_unary(&mut kb, &format!("probe.{ns}.r"))
        .into_iter()
        .map(|(v, definite)| match v {
            Value::Int(n) if definite => n,
            other => panic!("{ns}: expected a definite Int64, got {other:?}"),
        })
        .collect();
    ns_of.sort_unstable();
    ns_of
}

/// How many stored facts the query `pattern` finds, its names read in `probe.<ns>` and the
/// prelude, as `anthill query -i` reads them.
fn query_count(ns: &str, decls: &str, pattern: &str) -> usize {
    let mut kb = load_kb_with(&program(ns, decls, "0"));
    supply_invocation_imports(&mut kb, &[&format!("probe.{ns}.*"), "anthill.prelude.*"]);
    let goal = query_pattern_term(&mut kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

// ── A. in an operation body ───────────────────────────────────────────────────────────────

/// A BARE ALIAS IS THE TYPE IT STANDS FOR: compared with the type, through a chain of
/// aliases, an alias of a bare sort, a `let`, an argument, a nested bracket, a dotted path and
/// a `@[simp]` rule's right-hand side.
///
/// FAILS with the bare alias read as its own name: every comparison is false.
#[test]
fn a_bare_alias_is_the_type_it_stands_for() {
    let decls = "  rule ty() <=> IntOpt @[simp]\n  operation isOpt(t: Type) -> Bool = PartialEq.eq(t, \
                 Option[T = Int64])\n  operation viaLet() -> Type =\n    let t = IntOpt\n    t\n";
    assert_eq!(
        run(
            "vabare",
            decls,
            "bit(PartialEq.eq(Option[T = Int64], IntOpt)) + 2 * bit(PartialEq.eq(Int64, MyInt)) + 4 \
             * bit(PartialEq.eq(Option[T = Int64], A1)) + 8 * bit(PartialEq.eq(Option, AnyOpt)) + \
             16 * bit(PartialEq.eq(viaLet(), Option[T = Int64])) + 32 * bit(isOpt(IntOpt)) + 64 * \
             bit(PartialEq.eq(List[T = IntOpt], List[T = Option[T = Int64]])) + 128 * \
             bit(PartialEq.eq(Host.HB, Option[T = String])) + 256 * bit(PartialEq.eq(ty(), \
             Option[T = Int64]))"
        ),
        Ok(511)
    );
}

/// AN ALIAS APPLIED FURTHER is the sort it stands for with the bindings it fixes and the ones
/// written, a positional taking the next parameter the alias leaves open — as in a type
/// position. It was refused: the alias declares no parameters.
///
/// FAILS with an alias's application read as its own name: refused.
#[test]
fn an_alias_applied_further_takes_both_bindings() {
    assert_eq!(
        run(
            "vaapplied",
            "",
            "bit(PartialEq.eq(Pair[A = Int64, B = String], IntPair[B = String])) + 2 * \
             bit(PartialEq.eq(Pair[A = Int64, B = String], IntPair[String]))"
        ),
        Ok(3)
    );
}

/// BINDING AGAIN WHAT THE ALIAS FIXES is two values for one parameter, refused naming both, as
/// in a type position — once, though an operation's body is read by two walks.
///
/// FAILS with an alias's application read as its own name: the refusal is another one.
#[test]
fn binding_again_what_the_alias_fixes_is_refused_once() {
    let errs = load_errors_of(&program(
        "varebind",
        "  operation rebind() -> Bool = PartialEq.eq(IntPair[A = Bool], Int64)\n",
        "0",
    ));
    assert_refused_naming(
        &errs,
        &["it already binds `A` to `Int64`, which the application binds again"],
        "a fixed parameter bound again",
    );
    assert_eq!(errs.len(), 1, "one report: {errs:#?}");
}

/// A SLOT THE ALIAS'S DEFINITION LEAVES OPEN is left unwritten in the value, as a type value
/// written without it leaves it: `Some` over `sort Some = Box[V = ?]` is `Box`.
///
/// FAILS with the bare alias read as its own name.
#[test]
fn a_slot_the_alias_leaves_open_is_unwritten() {
    assert_eq!(run("vaopen", "", "bit(PartialEq.eq(Box, Some))"), Ok(1));
}

/// AN ALIAS NAMING THE SORT'S OWN PARAMETER is read inside the sort as the parameter written
/// there is: through the `requires TypeValue[T = S]` the sort declares, at the caller's `S`.
///
/// FAILS with the bare alias read as its own name: both comparisons are false.
#[test]
fn an_alias_of_the_sorts_parameter_is_read_through_its_clause() {
    let decls = "  sort Outer\n    sort S = ?\n    requires TypeValue[T = S]\n    entity o(s: S)\n    \
                 sort OB = Box[V = S]\n    sort OS = S\n    operation ob(x: Outer[S = S]) -> Type = \
                 OB\n    operation os(x: Outer[S = S]) -> Type = OS\n  end\n";
    assert_eq!(
        run(
            "vaparam",
            decls,
            "bit(PartialEq.eq(Outer.ob(Outer.o(1)), Box[V = Int64])) + 2 * \
             bit(PartialEq.eq(Outer.os(Outer.o(\"s\")), String))"
        ),
        Ok(3)
    );
}

/// OUTSIDE THE SORT such an alias is its own name, as in a type position: the parameter it
/// names is nobody's there.
#[test]
fn an_alias_naming_the_sorts_parameter_outside_it_is_its_name() {
    let decls = "  sort Outer\n    sort S = ?\n    entity o(s: S)\n    sort OB = Box[V = S]\n  end\n  \
                 operation outside() -> Type = Outer.OB\n";
    assert_eq!(run("vaoutside", decls, "bit(PartialEq.eq(outside(), Box))"), Ok(0));
}

/// AN ALIAS OF A TUPLE is the type a bracket's entry writing it is.
///
/// FAILS with the bare alias read as its own name: the entry is the alias's name.
#[test]
fn an_alias_of_a_tuple_is_the_type_a_bracket_entry_writes() {
    assert_eq!(
        run(
            "vatuple",
            "",
            "bit(PartialEq.eq(Box[V = P2], Box[V = (Int64, String)])) + 2 * bit(PartialEq.eq(P2, P2))"
        ),
        Ok(3)
    );
}

// ── B. in a clause's term and a query ─────────────────────────────────────────────────────

const HELD: &str = "  fact held(t: IntOpt, n: 1)\n  fact held(t: Option[T = Int64], n: 2)\n  fact \
                    held(t: MyInt, n: 3)\n  fact held(t: Int64, n: 4)\n  fact held(t: IntPair[String], \
                    n: 5)\n  fact held(t: Pair[A = Int64, B = String], n: 6)\n  fact held(t: Some, n: \
                    7)\n  fact held(t: Box, n: 8)\n";

/// A FACT HOLDING AN ALIAS IS FOUND BY THE TYPE, and a fact holding the type by the alias: a
/// rule body writing either finds both, bare, applied further, and with a slot left open.
///
/// FAILS with the bare alias read as its own name, with an alias's application read so (its
/// applied half), and with a clause's type application kept as written (the applied half:
/// `IntPair[String]` binds its positional).
#[test]
fn a_fact_holding_an_alias_is_found_by_the_type() {
    for (tag, goal, found) in [
        ("alias", "IntOpt", vec![1, 2]),
        ("written", "Option[T = Int64]", vec![1, 2]),
        ("aliassort", "MyInt", vec![3, 4]),
        ("sort", "Int64", vec![3, 4]),
        ("applied", "IntPair[B = String]", vec![5, 6]),
        ("pair", "Pair[A = Int64, B = String]", vec![5, 6]),
        ("open", "Some", vec![7, 8]),
        ("box", "Box", vec![7, 8]),
    ] {
        let ns = format!("vaheld{tag}");
        let decls = format!("{HELD}  rule r(?n) :- held(t: {goal}, n: ?n)\n");
        assert_eq!(rule_answers(&ns, &decls), found, "{ns}");
    }
}

/// A QUERY READS THE ALIAS as the fact holding it was stored, bare, qualified and applied.
///
/// FAILS with the bare alias read as its own name, and with an alias's application read so.
#[test]
fn a_query_reads_the_alias_too() {
    for (tag, pattern) in [
        ("bare", "held(t: IntOpt, n: ?)"),
        ("qualified", "held(t: probe.vaqueryqualified.IntOpt, n: ?)"),
        ("applied", "held(t: IntPair[String], n: ?)"),
    ] {
        let ns = format!("vaquery{tag}");
        assert_eq!(query_count(&ns, HELD, pattern), 2, "{ns}: {pattern}");
    }
}

/// AN ALIAS OF A TUPLE STAYS ITS NAME IN A CLAUSE: a tuple written in a data slot is a tuple of
/// values, and no type, so the alias is read as written there and found by itself.
#[test]
fn an_alias_of_a_tuple_stays_its_name_in_a_clause() {
    let decls = "  fact held(t: P2, n: 9)\n  rule r(?n) :- held(t: P2, n: ?n)\n";
    assert_eq!(rule_answers("vaheldtuple", decls), vec![9]);
}

// ── C. one term per type ──────────────────────────────────────────────────────────────────

const SPELLINGS: &str = "  fact held(t: Pair[Int64, String], n: 1)\n  fact held(t: Pair[A = Int64, B = \
                         String], n: 2)\n  fact held(t: Pair[B = String, A = Int64], n: 3)\n  fact \
                         held(t: Pair[Int64, B = String], n: 4)\n  fact held(t: IntPair[String], n: \
                         5)\n  fact held(t: List[T = Pair[String, Int64]], n: 6)\n";

/// A TYPE APPLICATION IN A CLAUSE IS ONE TERM, however its inputs are written: positionally, by
/// name, in either order, mixed, through an alias — and one bracket down. A goal with a
/// variable in a positional slot binds it at every spelling.
///
/// FAILS with a clause's type application kept as written: each goal finds its own spelling.
#[test]
fn a_type_application_in_a_clause_is_one_term() {
    for (tag, goal) in [
        ("named", "Pair[A = Int64, B = String]"),
        ("positional", "Pair[Int64, String]"),
        ("swapped", "Pair[B = String, A = Int64]"),
        ("mixed", "Pair[Int64, B = String]"),
        ("alias", "IntPair[String]"),
        ("variable", "Pair[Int64, ?s]"),
    ] {
        let ns = format!("vaone{tag}");
        let decls = format!("{SPELLINGS}  rule r(?n) :- held(t: {goal}, n: ?n)\n");
        assert_eq!(rule_answers(&ns, &decls), vec![1, 2, 3, 4, 5], "{ns}");
    }
    let decls = format!("{SPELLINGS}  rule r(?n) :- held(t: List[T = Pair[B = Int64, A = String]], n: ?n)\n");
    assert_eq!(rule_answers("vaonenested", &decls), vec![6]);
}

/// A QUERY WRITES A TYPE APPLICATION AS ONE TERM, as the facts it searches were stored.
///
/// FAILS with a clause's type application kept as written.
#[test]
fn a_query_writes_a_type_application_as_one_term() {
    for (tag, pattern) in [
        ("named", "held(t: Pair[A = Int64, B = String], n: ?)"),
        ("positional", "held(t: Pair[Int64, String], n: ?)"),
        ("swapped", "held(t: Pair[B = String, A = Int64], n: ?)"),
    ] {
        let ns = format!("vaqueryone{tag}");
        assert_eq!(query_count(&ns, SPELLINGS, pattern), 5, "{ns}: {pattern}");
    }
}

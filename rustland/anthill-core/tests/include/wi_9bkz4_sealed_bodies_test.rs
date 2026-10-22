//! WI-20261010-9BKZ4 — A SEALED LOAD'S BODIES ARE TYPED ONCE, by the load that declared
//! them, and what a later load could have changed in them is refused.
//!
//! The typer's two whole-KB sweeps typed the standard library again at every later
//! load: 99 ms and 11 ms of a 267 ms load of a four-line file. Behind a seal
//! (WI-20261009-4ZRTG) they skip what the seal holds.
//!
//! THE FIXTURES are a small LIBRARY file, loaded in the standard library's call and
//! sealed with it, and a PROGRAM file — once in that same call, once as a later load.
//! The library is ours so that its bodies say exactly what each row needs; one row
//! uses the standard library itself.
//!
//! WHAT FAILS WHEN (each measured by making the change and running this file):
//!
//! THE SWEEPS
//! * the free-operation sweep made to type sealed operations again (`sorts.rs`, the
//!   `partition`): `a_later_load_types_its_own_bodies_and_no_sealed_one` FAILS, and six
//!   rows about `@[simp]` rules with it — the sweep applies the rule to the library's
//!   body first, as it did before this ticket, and the check that follows finds a body
//!   nothing rewrites any more.
//! * the rule sweep made to type sealed rules again, or to type NO rule
//!   (`sealed::rule_body_is_typed_once` answering `false`, `true`): the same first row
//!   FAILS, on its rule counts.
//! * the free-operation sweep made to skip EVERY body: twelve rows FAIL — a program's
//!   own bodies are not typed, and nothing of it runs.
//! * the sweep made to skip a sealed operation whose load never ran its typer
//!   (`holds_operation` for `holds_typed_operation`), or the seal made to call every
//!   load typed: `a_sealed_load_that_never_ran_its_typer_is_typed_by_the_next_run`
//!   FAILS.
//! * the typer made to keep its dispatch memo from one load to the next (`sorts.rs`,
//!   `invalidate_resolve_cache`): `nothing_sealed_a_later_loads_provision_answers_as_
//!   in_one_call` FAILS — 12, 12, 2.
//!
//! THE `@[simp]` CHECK
//! * made to find nothing: the five `a_simp_rule_…_is_refused…` rows, the dot-rule row,
//!   `a_refused_rule_and_…` and `a_typer_run_made_by_hand_…` FAIL — each file loads,
//!   and the library's body silently keeps its meaning. With `ANTHILL_TYPER_ORACLE=1`
//!   beside that back-out they fail the other way, by the oracle's panic: "the body of
//!   sealed operation 'test.liba.libCallsBase' was REWRITTEN".
//! * made to refuse wherever a sealed body calls or constructs the head, without
//!   typing it: `a_simp_rule_that_reaches_no_sealed_body_loads` FAILS. (`a_simp_rule_
//!   over_a_construction_…` failed with it while a rule headed by a constructor fired
//!   on no construction; it is refused either way since the rule fires.)
//! * made to read only "came back rewritten", not what typing reported:
//!   `a_simp_rule_that_breaks_a_sealed_body_is_refused` FAILS — `libAdds` loads.
//! * its dot-rule arm removed: `a_dot_rule_for_a_sealed_sort_is_refused` FAILS.
//!
//! THE PROVISION CHECK
//! * made to find nothing: `a_more_specific_provision_…` (both), `a_second_witness_…`,
//!   `an_overlapping_provision_…`, the two `…_written_into_a_sealed_sort_…` rows and
//!   `a_refused_rule_and_…` FAIL — each loads. With the oracle beside it: "a call in
//!   the body of sealed operation 'test.libc.libAtWrapLeaf' was classified
//!   differently".
//! * made to refuse wherever a sealed provision answers beside it: `a_named_rival_…`
//!   and `a_named_ordering_…` FAIL.
//! * without "every type its head mentions is a sealed load's": `a_provider_and_an_
//!   override_for_the_programs_own_type_…` FAILS — `Desc[T = Wrap[A = Mine]]` is
//!   refused.
//! * without "a receiver-dispatched spec's carrier is its provider": `a_second_
//!   implementation_of_a_receiver_dispatched_spec_loads` FAILS.
//! * its "put into a sealed sort beside its own" arm removed: `a_second_provision_
//!   written_into_a_sealed_sort_is_refused` FAILS — it loads. The arm made to take
//!   EVERY later row a sealed sort is the provider of is driven elsewhere: four rows of
//!   `wi_5g28a_sort_domain_test` and `wi_shed7_fillable_test` FAIL, a sort's domain
//!   being derived for a library sort by the first load that reads it.
//! * its overlap arm made to find nothing: `an_overlapping_provision_…` FAILS; made to
//!   read a CONVERSION as a provision: `a_named_ordering_…` FAILS under `TwoStep`.
//! * made to judge a CONVERSION of the later load: `a_spec_that_converts_to_a_sealed_
//!   spec_loads` FAILS in two calls.
//!
//! THE RELATION CHECK (WI-20261013-WF14Z, user 2026-10-22)
//! * made to find nothing (`sealed::clauses_that_change_a_sealed_relation`):
//!   `a_clause_that_changes_a_sealed_relations_columns_is_refused` FAILS in two calls —
//!   `fact tagged("a")` loads, and the library's `doubled` hands `ilen` the `String`.
//! * made to say it at the first clause the later load wrote rather than the one that
//!   changes the reading: the same row FAILS, at `3:8` (`tagged(2)`) for `4:8`.
//! * BY DESIGN, `a_clause_at_a_sealed_relations_column_types_loads` passes either way:
//!   it is the row that fails if the check refuses every later clause.
//!
//! THE SEAL
//! * made to keep no types by symbol: eight rows FAIL, `the_seal_holds_…` among them.
//! * made to keep no rule-slot mark, so that the library's own clauses are judged:
//!   fourteen rows FAIL.
//!
//! BY DESIGN
//! * the ONE-CALL halves pass either way: they are what the fixture means, and what a
//!   later load is held to. So does `an_operation_that_captures_a_sealed_name_is_
//!   refused_in_both`: proposal 059 R4 refused it before this ticket, in both orders,
//!   and the row is here because it was one of the three ways in.
//! * `a_more_specific_provision_written_through_an_alias_is_refused` passes with or
//!   without anything of this ticket's reading an alias: the loader stores the head with
//!   the alias on an occurrence whose view is what the alias stands for, and the checks
//!   read the head through the view. It is the row that fails if a head is ever read by
//!   its alias's name, and `sealed::type_heads` says so.
//! * NOT MEASURED AS A BACK-OUT: that the checks read the KB and not one load's range
//!   (`a_refused_rule_and_a_refused_provision_are_refused_again_by_the_next_load`).
//!   They no longer take a range to read.
//!
//! UNDER `ANTHILL_TYPER_ORACLE=1` the suite's later loads were all typed both ways, and
//! none changed a sealed body but the shapes refused here (the whole `anthill-core`
//! suite on the shared base).
//!
//! PINNED TO RECIPES BY NAME, every row: the subject is the difference between one
//! call and two, so no row may follow the switch.

use anthill_core::eval::{self, Interpreter, Value};
use anthill_core::kb::load::{self, LoadOptions};
use anthill_core::kb::typing::{bodies_typed_by_this_thread, type_check_sorts};
use anthill_core::kb::KnowledgeBase;

use crate::common::{load_in_a_later_call, recipe_load, rendered_load_errors, LoadRecipe};

/// The library and the program in ONE call.
fn one_call(lib: &str, program: &str) -> Result<KnowledgeBase, Vec<String>> {
    recipe_load(&[lib, program], None, LoadOptions::default(), LoadRecipe::OneShot, |_| {})
        .map(|(kb, _)| kb)
        .map_err(rendered_load_errors)
}

/// The library in the standard library's call, the two SEALED, and nothing else.
fn sealed_library(lib: &str) -> KnowledgeBase {
    let (mut kb, _) =
        recipe_load(&[lib], None, LoadOptions::default(), LoadRecipe::OneShot, |_| {})
            .unwrap_or_else(|e| panic!("the library loads: {:?}", rendered_load_errors(e)));
    load::seal_declarations(&mut kb);
    kb
}

/// The library sealed, then the program as a LATER load.
fn two_calls(lib: &str, program: &str) -> Result<KnowledgeBase, Vec<String>> {
    let mut kb = sealed_library(lib);
    load_in_a_later_call(&mut kb, program, LoadOptions::default())
        .map(|_| kb)
        .map_err(rendered_load_errors)
}

/// What each of `entries` evaluates to, in order.
fn values(kb: KnowledgeBase, entries: &[&str]) -> Vec<i64> {
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp).expect("standard builtins");
    entries
        .iter()
        .map(|entry| match interp.call(entry, &[]) {
            Ok(Value::Int(n)) => n,
            other => panic!("`{entry}` did not run to an Int64: {other:?}"),
        })
        .collect()
}

fn loaded(r: Result<KnowledgeBase, Vec<String>>, how: &str) -> KnowledgeBase {
    r.unwrap_or_else(|e| panic!("{how}: the files load; got {e:?}"))
}

fn refused(r: Result<KnowledgeBase, Vec<String>>, how: &str) -> Vec<String> {
    match r {
        Ok(_) => panic!("{how}: the load must be refused, and it loaded clean"),
        Err(e) => e,
    }
}

// ── The sweep ────────────────────────────────────────────────────────

const A_PROGRAM_OF_ONE_OPERATION: &str = r#"
namespace test.w9bkz4.small
  import anthill.prelude.{Int64}
  operation seven() -> Int64 = 7
  sort Item
    entity item(n: Int64)
  end
  fact item(n: 1)
  rule small_rule(?x) :- item(n: ?x)
end
"#;

/// [`A_PROGRAM_OF_ONE_OPERATION`] without its rule — the baseline its rule is counted
/// against: whatever else a later load types (the sealed load's derived clauses, the
/// program's own) it types for this file too.
const THE_SAME_WITHOUT_ITS_RULE: &str = r#"
namespace test.w9bkz4.small
  import anthill.prelude.{Int64}
  operation seven() -> Int64 = 7
  sort Item
    entity item(n: Int64)
  end
  fact item(n: 1)
end
"#;

/// How many operation bodies and rule bodies loading `program` into `kb` types.
fn typed_by_a_later_load(kb: &mut KnowledgeBase, program: &str) -> (usize, usize) {
    let (ops_before, rules_before) = bodies_typed_by_this_thread();
    load_in_a_later_call(kb, program, LoadOptions::default())
        .map_err(rendered_load_errors)
        .expect("the later load");
    let (ops_after, rules_after) = bodies_typed_by_this_thread();
    (ops_after - ops_before, rules_after - rules_before)
}

/// The capability, driven: a later load types the bodies it brought and none of the
/// sealed load's. Before this ticket it typed every body the KB held, which is what an
/// UNSEALED earlier load still gets — measured here beside it, as the control.
///
/// OPERATIONS, exactly. RULES, the written ones: a sealed load's rule is known by the
/// source its head was written in, and a clause no source wrote — the standard library
/// derives 132 of its 254, the induction axioms among them — has no site to be known
/// by. Those are typed at every load as before, which costs time and skips nothing.
#[test]
fn a_later_load_types_its_own_bodies_and_no_sealed_one() {
    let (ops_before, rules_before) = bodies_typed_by_this_thread();
    let mut sealed = sealed_library(LIB_DESC);
    let (ops_library, rules_library) = bodies_typed_by_this_thread();
    assert!(
        ops_library - ops_before > 100 && rules_library - rules_before > 200,
        "the control on the instrument: the library's own load typed its bodies on this \
         thread ({} operations, {} rules)",
        ops_library - ops_before,
        rules_library - rules_before
    );
    let (ops, rules) = typed_by_a_later_load(&mut sealed, A_PROGRAM_OF_ONE_OPERATION);
    // `ANTHILL_TYPER_ORACLE=1` types the sealed bodies as well, to compare — which is
    // the one thing this row counts. Under it the row says so and stops: the oracle's
    // run is not where the sweep is measured.
    if std::env::var("ANTHILL_TYPER_ORACLE").is_ok_and(|v| v == "1") {
        assert!(ops > 100, "the oracle types every sealed operation body; typed {ops}");
        return;
    }
    assert_eq!(ops, 1, "the later load declares ONE operation with a body, and types that one");

    let mut unsealed = crate::common::load_unsealed(&[LIB_DESC]);
    assert_eq!(unsealed.sealed_census(), (0, 0, 0), "the fixture: nothing is sealed");
    let (ops_unsealed, rules_unsealed) =
        typed_by_a_later_load(&mut unsealed, A_PROGRAM_OF_ONE_OPERATION);
    assert!(
        ops_unsealed > 100,
        "NOTHING SEALED, NOTHING SKIPPED: an unsealed KB's operation bodies are all typed \
         again by a later load; typed {ops_unsealed}"
    );
    assert!(
        rules + 100 <= rules_unsealed,
        "the sealed load's WRITTEN rule bodies are not typed again: {rules} typed behind \
         the seal, {rules_unsealed} with nothing sealed"
    );
    // …and the program's own rule IS: one more than the same file without it.
    let (_, rules_without) =
        typed_by_a_later_load(&mut sealed_library(LIB_DESC), THE_SAME_WITHOUT_ITS_RULE);
    assert_eq!(
        rules,
        rules_without + 1,
        "the later load writes ONE rule with a body, and types that one"
    );
    assert_eq!(values(sealed, &["test.w9bkz4.small.seven"]), [7]);
}

/// The seal reaches what the sweep and the checks ask it about.
#[test]
fn the_seal_holds_the_librarys_operations_sorts_and_sources() {
    let kb = sealed_library(LIB_DESC);
    let (ops, sorts, sources) = kb.sealed_census();
    assert!(ops > 300 && sorts > 100 && sources > 50, "({ops}, {sorts}, {sources})");
}

// ── (1) a `@[simp]` rule over a sealed operation ─────────────────────

const LIB_SIMP: &str = r#"
namespace test.liba
  import anthill.prelude.{Int64}
  import anthill.prelude.Additive.{add}

  operation base(x: Int64) -> Int64 = 1
  operation libCallsBase() -> Int64 = base(5)

  sort Kind
    entity k1
    entity k2
  end
  operation weight(k: Kind) -> Int64
  rule weight(k1()) <=> 1 @[simp]
  operation libWeighs(k: Kind) -> Int64 = weight(k)

  sort Tag
    entity tag(n: Int64)
  end
  operation tagNumber(t: Tag) -> Int64 =
    match t
      case tag(n) -> n
  operation libTags() -> Int64 = tagNumber(tag(1))
  operation libAdds() -> Int64 = add(base(5), 1)
end
"#;

const A_RULE_OVER_A_LIBRARY_CALL: &str = r#"
namespace test.proga
  import anthill.prelude.{Int64}
  import test.liba.{base, libCallsBase}
  rule base(?x) <=> 2 @[simp]
  operation entry() -> Int64 = libCallsBase()
end
"#;

#[test]
fn a_simp_rule_that_rewrites_a_sealed_body_is_refused() {
    // What the fixture means: in one call the program's rule rewrites the library's
    // body, and the library's operation answers by it.
    let kb = loaded(one_call(LIB_SIMP, A_RULE_OVER_A_LIBRARY_CALL), "one call");
    assert_eq!(values(kb, &["test.proga.entry"]), [2]);

    let errors = refused(two_calls(LIB_SIMP, A_RULE_OVER_A_LIBRARY_CALL), "two calls");
    assert!(
        errors.iter().any(|e| e.contains("`@[simp]` rule over 'test.liba.base'")
            && e.contains("rewrites the body of 'test.liba.libCallsBase'")),
        "the refusal names the rule's head and the sealed operation; got {errors:?}"
    );
}

const A_RULE_OVER_A_GENERIC_LIBRARY_CALL: &str = r#"
namespace test.proga
  import anthill.prelude.{Int64}
  import test.liba.{Kind, weight, libWeighs}
  import test.liba.Kind.{k1}
  rule weight(?k) <=> 2 @[simp]
  operation entry() -> Int64 = libWeighs(k1())
end
"#;

/// The same through a body-less operation: `libWeighs` calls `weight(k)` with its own
/// parameter, which no library rule matches and the program's `weight(?k)` does.
#[test]
fn a_simp_rule_that_matches_a_sealed_bodys_call_is_refused() {
    let kb = loaded(one_call(LIB_SIMP, A_RULE_OVER_A_GENERIC_LIBRARY_CALL), "one call");
    assert_eq!(values(kb, &["test.proga.entry"]), [2]);

    let errors = refused(two_calls(LIB_SIMP, A_RULE_OVER_A_GENERIC_LIBRARY_CALL), "two calls");
    assert!(
        errors.iter().any(|e| e.contains("rewrites the body of 'test.liba.libWeighs'")),
        "got {errors:?}"
    );
}

const A_RULE_FOR_AN_ARGUMENT_OF_ITS_OWN: &str = r#"
namespace test.proga
  import anthill.prelude.{Int64}
  import test.liba.{Kind, weight}
  import test.liba.Kind.{k2}
  rule weight(k2()) <=> 2 @[simp]
  operation entry() -> Int64 = weight(k2())
end
"#;

/// The refusal is EXACT: a rule over a sealed operation that a sealed body calls, for
/// an argument no sealed call is written with, rewrites no sealed body and loads. It is
/// the shape of `rule fact_monotonicity(Mine) <=> …`, which the library documents.
#[test]
fn a_simp_rule_that_reaches_no_sealed_body_loads() {
    for (how, kb) in [
        ("one call", one_call(LIB_SIMP, A_RULE_FOR_AN_ARGUMENT_OF_ITS_OWN)),
        ("two calls", two_calls(LIB_SIMP, A_RULE_FOR_AN_ARGUMENT_OF_ITS_OWN)),
    ] {
        assert_eq!(values(loaded(kb, how), &["test.proga.entry"]), [2], "{how}");
    }
}

const A_RULE_OVER_A_LIBRARY_CONSTRUCTION: &str = r#"
namespace test.proga
  import anthill.prelude.{Int64}
  import test.liba.{Tag, libTags}
  import test.liba.Tag.{tag}
  rule tag(1) <=> tag(2) @[simp]
  operation entry() -> Int64 = libTags()
end
"#;

/// A rule headed by a CONSTRUCTOR rewrites a construction where a body is typed, as a
/// rule over a call does: in one call the library's operation answers by it, and behind
/// a seal the later load is refused — the check reads a construction as it reads a call.
///
/// THE DAY THIS ROW WAS WRITTEN FOR. It held the two orders to one answer while such a
/// rule fired on no construction in an operation body: the library writes `tag(1)`, the
/// rule's head is the `tag(n: 1)` the load makes of it, and an operation body's node was
/// read as written. It is read in the canonical entity form now
/// (`canonical_ctor_args`, found with WI-20261011-CR6GD), so one call answers
/// 2 — and the refusal that was waiting takes the other order.
#[test]
fn a_simp_rule_over_a_construction_is_refused_behind_a_seal() {
    let one = loaded(one_call(LIB_SIMP, A_RULE_OVER_A_LIBRARY_CONSTRUCTION), "one call");
    assert_eq!(values(one, &["test.proga.entry"]), [2]);

    let errors = refused(two_calls(LIB_SIMP, A_RULE_OVER_A_LIBRARY_CONSTRUCTION), "two calls");
    assert!(
        errors.iter().any(|e| e.contains("`@[simp]` rule over 'test.liba.Tag.tag'")
            && e.contains("rewrites the body of 'test.liba.libTags'")),
        "the refusal names the rule's head and the sealed operation; got {errors:?}"
    );
}

const LIB_NAMED: &str = r#"
namespace test.libn
  import anthill.prelude.{Int64}
  sort Span
    entity span(lo: Int64, hi: Int64)
  end
  operation top(s: Span) -> Int64 = s.hi
  operation libSpans() -> Int64 = top(span(hi: 9, lo: 1))
end
"#;

const A_RULE_OVER_A_CONSTRUCTION_WRITTEN_OUT_OF_ORDER: &str = r#"
namespace test.progn
  import anthill.prelude.{Int64}
  import test.libn.{Span, libSpans}
  import test.libn.Span.{span}
  rule span(lo: 1, hi: 9) <=> span(lo: 1, hi: 3) @[simp]
  operation entry() -> Int64 = libSpans()
end
"#;

/// The same for a construction the library writes with its arguments named out of
/// declaration order, `span(hi: 9, lo: 1)`: the rule's head is in that order, and the
/// node is read in it (WI-20261011-12VZB).
///
/// With `KnowledgeBase::named_out_of_declared_order` answering `false` this FAILS on its
/// first assertion: the rule fires on no body, one call answers 9 and two load clean.
#[test]
fn a_simp_rule_over_a_construction_written_out_of_order_is_refused_behind_a_seal() {
    let one = loaded(
        one_call(LIB_NAMED, A_RULE_OVER_A_CONSTRUCTION_WRITTEN_OUT_OF_ORDER),
        "one call",
    );
    assert_eq!(values(one, &["test.progn.entry"]), [3]);

    let errors = refused(
        two_calls(LIB_NAMED, A_RULE_OVER_A_CONSTRUCTION_WRITTEN_OUT_OF_ORDER),
        "two calls",
    );
    assert!(
        errors.iter().any(|e| e.contains("`@[simp]` rule over 'test.libn.Span.span'")
            && e.contains("rewrites the body of 'test.libn.libSpans'")),
        "the refusal names the rule's head and the sealed operation; got {errors:?}"
    );
}

const LIB_GUARD: &str = r#"
namespace test.libg
  import anthill.prelude.{Int64}
  sort Tag
    entity tag(n: Int64)
  end
  import test.libg.Tag.{tag}
  operation base(x: Int64) -> Int64 = 1
  operation libGuards(t: Tag) -> Int64 =
    match t
      case tag(n) | base(n) > 1 -> 7
      case _ -> 0
  operation libGuard() -> Int64 = libGuards(tag(5))
end
"#;

const A_RULE_OVER_A_CALL_IN_A_LIBRARY_GUARD: &str = r#"
namespace test.progg
  import anthill.prelude.{Int64}
  import test.libg.{base, libGuard}
  rule base(?x) <=> 2 @[simp]
  operation entry() -> Int64 = libGuard()
end
"#;

/// A match arm's GUARD is part of the body a rule rewrites: in one call the library's
/// arm is taken by the program's rule, and behind a seal the later load is refused.
///
/// With the written guard put back where the body is typed (`typing/build.rs`) this
/// FAILS on its first assertion: nothing rewrote the guard that runs, one call answers
/// 0 and two load clean.
#[test]
fn a_simp_rule_over_a_call_in_a_sealed_guard_is_refused() {
    let one = loaded(one_call(LIB_GUARD, A_RULE_OVER_A_CALL_IN_A_LIBRARY_GUARD), "one call");
    assert_eq!(values(one, &["test.progg.entry"]), [7]);

    let errors = refused(
        two_calls(LIB_GUARD, A_RULE_OVER_A_CALL_IN_A_LIBRARY_GUARD),
        "two calls",
    );
    assert!(
        errors.iter().any(|e| e.contains("`@[simp]` rule over 'test.libg.base'")
            && e.contains("rewrites the body of 'test.libg.libGuards'")),
        "the refusal names the rule's head and the sealed operation; got {errors:?}"
    );
}

const LIB_GUARD_DOT: &str = r#"
namespace test.libh
  import anthill.prelude.{Int64, Bool}
  sort Tag
    entity tag(n: Int64)
    operation small(t: Tag) -> Bool = t.n < 3
  end
  import test.libh.Tag.{tag}
  operation base(x: Int64) -> Int64 = 1
  operation libGuards(t: Tag) -> Int64 =
    match t
      case tag(n) | t.small() -> base(n)
      case tag(n) | base(n) > 1 -> 7
      case _ -> 0
  operation libGuard() -> Int64 = libGuards(tag(5)) * 10 + libGuards(tag(1))
end
"#;

const A_RULE_FOR_AN_ARGUMENT_NO_LIBRARY_GUARD_WRITES: &str = r#"
namespace test.progh
  import anthill.prelude.{Int64}
  import test.libh.{base, libGuard}
  rule base(99) <=> 2 @[simp]
  operation entry() -> Int64 = libGuard()
end
"#;

/// …and a rule that matches no call a sealed guard writes loads, in both orders: a
/// guard the library's own load already resolved a dot in, or left alone, comes back
/// from a second typing as it is stored, and is not read as rewritten.
///
/// With the written guard put back where the body is typed this FAILS with the row
/// above, as `wi_12vzb_match_guard_stored_as_typed_test::a_dot_call_in_a_guard_loads_-
/// and_runs` does: the library writes a dot in a guard. What it is here for is the
/// other direction — a guard whose second typing gave a new node would be refused
/// behind the seal for a rule that never touched it.
#[test]
fn a_simp_rule_that_reaches_no_sealed_guard_loads() {
    for (how, kb) in [
        ("one call", one_call(LIB_GUARD_DOT, A_RULE_FOR_AN_ARGUMENT_NO_LIBRARY_GUARD_WRITES)),
        ("two calls", two_calls(LIB_GUARD_DOT, A_RULE_FOR_AN_ARGUMENT_NO_LIBRARY_GUARD_WRITES)),
    ] {
        assert_eq!(values(loaded(kb, how), &["test.progh.entry"]), [1], "{how}");
    }
}

const A_RULE_THAT_BREAKS_A_LIBRARY_BODY: &str = r#"
namespace test.proga
  import anthill.prelude.{Int64, String}
  import test.liba.{base}
  rule base(?x) <=> "two" @[simp]
end
"#;

/// A rule whose rewrite leaves the sealed body ILL-TYPED: the typer does not write such
/// a body back, so "it came back rewritten" would not see it — what typing it reports
/// does. One call reports the library's operation; two may not load clean over it.
#[test]
fn a_simp_rule_that_breaks_a_sealed_body_is_refused() {
    let one = refused(one_call(LIB_SIMP, A_RULE_THAT_BREAKS_A_LIBRARY_BODY), "one call");
    assert!(
        one.iter().any(|e| e.contains("type mismatch in add.b"))
            && one.iter().any(|e| e.contains("libCallsBase.return")),
        "one call reports the two library operations the rule broke; got {one:?}"
    );

    let two = refused(two_calls(LIB_SIMP, A_RULE_THAT_BREAKS_A_LIBRARY_BODY), "two calls");
    for (how, op) in [("breaks", "libAdds"), ("rewrites", "libCallsBase")] {
        assert!(
            two.iter().any(|e| e.contains("`@[simp]` rule over 'test.liba.base'")
                && e.contains(&format!("{how} the body of 'test.liba.{op}'"))),
            "the rule {how} `{op}`; got {two:?}"
        );
    }
}

/// THE REFUSAL IS OF THE KB, NOT OF ONE LOAD. A refused load does not unwind, so its
/// rule is still there when the next file is loaded — which is refused for it again,
/// and does not find it "earlier" and load clean over a KB whose sealed bodies and
/// later bodies disagree.
#[test]
fn a_refused_rule_and_a_refused_provision_are_refused_again_by_the_next_load() {
    for (lib, offending, names) in [
        (LIB_SIMP, A_RULE_OVER_A_LIBRARY_CALL, "rewrites the body of 'test.liba.libCallsBase'"),
        (LIB_DESC, A_MORE_SPECIFIC_PROVISION_OF_LIBRARY_ELEMENTS, "changes who answers"),
    ] {
        let mut kb = sealed_library(lib);
        load_in_a_later_call(&mut kb, offending, LoadOptions::default())
            .map(|_| ())
            .expect_err("the fixture: the first later load is refused");
        let again = load_in_a_later_call(&mut kb, A_PROGRAM_OF_ONE_OPERATION, LoadOptions::default())
            .map(|_| ())
            .map_err(rendered_load_errors)
            .expect_err("a harmless file loaded over the refused KB is refused too");
        assert!(again.iter().any(|e| e.contains(names)), "got {again:?}");
    }
}

/// A TYPER RUN MADE BY HAND RAISES IT TOO — the checks are the typer's, not the load
/// pipeline's, so `type_check_sorts(&mut kb, result.loaded())` over an untyped later
/// load says what the pipeline's own call says.
#[test]
fn a_typer_run_made_by_hand_refuses_what_the_pipeline_refuses() {
    let mut kb = sealed_library(LIB_SIMP);
    let result = load_in_a_later_call(
        &mut kb,
        A_RULE_OVER_A_LIBRARY_CALL,
        LoadOptions { run_typer: false },
    )
    .map_err(rendered_load_errors)
    .expect("the untyped load: nothing has typed anything yet");
    let errors = rendered_load_errors(type_check_sorts(&mut kb, result.loaded()));
    assert!(
        errors.iter().any(|e| e.contains("rewrites the body of 'test.liba.libCallsBase'")),
        "got {errors:?}"
    );
}

/// TYPED ONCE IS NOT NEVER. A load that did not run its typer can be sealed — its
/// DECLARATIONS are sealed like any other's — but its bodies have not been typed, and
/// the typer run that follows types every one of them: exactly as many as it types
/// with nothing sealed.
#[test]
fn a_sealed_load_that_never_ran_its_typer_is_typed_by_the_next_run() {
    let typed_by_the_run_after = |seal: bool| -> (usize, usize) {
        let files = crate::common::stdlib_parsed();
        let mut kb = KnowledgeBase::new();
        let result = load::load_all_with(
            &mut kb,
            &files,
            &load::NullResolver,
            LoadOptions { run_typer: false },
        )
        .unwrap_or_else(|e| panic!("the untyped load: {:?}", rendered_load_errors(e)));
        if seal {
            load::seal_declarations(&mut kb);
            assert!(kb.sealed_census().0 > 300, "the untyped load's declarations are sealed");
        }
        let before = bodies_typed_by_this_thread();
        let errors = rendered_load_errors(type_check_sorts(&mut kb, result.loaded()));
        assert!(errors.is_empty(), "the library types clean; got {errors:?}");
        let after = bodies_typed_by_this_thread();
        (after.0 - before.0, after.1 - before.1)
    };
    let (sealed, unsealed) = (typed_by_the_run_after(true), typed_by_the_run_after(false));
    assert!(unsealed.0 > 100 && unsealed.1 > 100, "the control: {unsealed:?}");
    assert_eq!(
        sealed, unsealed,
        "(operation bodies, rule bodies) typed by the first run over a sealed, never typed \
         load, against the same load not sealed"
    );
}

const A_DOT_RULE_FOR_A_LIBRARY_SORT: &str = r#"
namespace test.liba.Kind
  import anthill.prelude.{Int64}
  rule dr: dot_apply(?e, heaviness, ?x) <=> 0 @[simp]
end
"#;

/// A DOT RULE for a sealed sort's members. The sealed bodies' dot calls were resolved
/// when they were typed and are gone from the stored bodies, so no typer run can ask
/// whether this rule would have fired in one: it is refused on its domain.
#[test]
fn a_dot_rule_for_a_sealed_sort_is_refused() {
    let errors = refused(two_calls(LIB_SIMP, A_DOT_RULE_FOR_A_LIBRARY_SORT), "two calls");
    assert!(
        errors
            .iter()
            .any(|e| e.contains("dot rule is written for 'test.liba.Kind'")),
        "got {errors:?}"
    );
}

const A_RULE_OVER_THE_STANDARD_LIBRARY: &str = r#"
namespace test.proga
  import anthill.prelude.{Int64, Bool, Option}
  import anthill.prelude.Option.{isEmpty, nonEmpty, some}
  rule isEmpty(?o) <=> true @[simp]
  operation entry() -> Int64 = if nonEmpty(some(1)) then 1 else 0
end
"#;

/// The same against the standard library itself, under the recipe the product is to
/// use: `Option.nonEmpty` is `not(isEmpty(o))`, and a program's rule over `isEmpty`
/// rewrote it — `nonEmpty(some(1))` false for every caller.
#[test]
fn a_simp_rule_over_the_standard_library_is_refused_after_it() {
    let one = recipe_load(
        &[A_RULE_OVER_THE_STANDARD_LIBRARY],
        None,
        LoadOptions::default(),
        LoadRecipe::OneShot,
        |_| {},
    )
    .map(|(kb, _)| kb)
    .map_err(rendered_load_errors);
    assert_eq!(
        values(loaded(one, "one call"), &["test.proga.entry"]),
        [0],
        "what the fixture means: in one call the rule rewrites the library's `nonEmpty`"
    );

    let two = recipe_load(
        &[A_RULE_OVER_THE_STANDARD_LIBRARY],
        None,
        LoadOptions::default(),
        LoadRecipe::TwoStep,
        |_| {},
    )
    .map(|(kb, _)| kb)
    .map_err(rendered_load_errors);
    let errors = refused(two, "the standard library, then the file");
    assert!(
        errors
            .iter()
            .any(|e| e.contains("rewrites the body of 'anthill.prelude.Option.nonEmpty'")),
        "got {errors:?}"
    );
}

// ── (1b) a `@[simp]` rule over a sealed constant's value ─────────────
//
// WI-20261011-2QZ3F. A const's value is typed with the equations applied and kept as
// typed, so it is a body a later load's rule could reach, and a sealed one is typed
// once. WHAT FAILS WHEN (each measured by making the change and running this file):
//
// * equations off in the const sweep (`sorts.rs`, `check_constant_bodies`): the two
//   `…_sealed_consts_value_is_refused` rows FAIL on their one-call halves — the rule
//   reaches no const, 1 where 2 is expected and a clean load where a mismatch is — and
//   `a_programs_const_rewritten_by_a_sealed_equation_stays_the_programs` FAILS, the
//   const's first read dying `OperationBodyMissing`.
// * the const sweep made to type sealed values again (`constant_values_by_seal` sealing
//   nothing): `a_simp_rule_that_rewrites_a_sealed_consts_value_is_refused` and
//   `a_simp_rule_that_breaks_…` FAIL on two calls — the sweep applies the rule first and
//   the check that follows finds a value nothing rewrites any more, or the mismatch is
//   reported with no refusal naming the const.
// * the check made to ask no const: the same two rows FAIL, each loading clean.
// * the check made to refuse wherever a sealed const's value calls the head, without
//   typing it: `a_simp_rule_that_reaches_no_sealed_consts_value_loads` FAILS, and
//   `a_simp_rule_that_breaks_…` on its word, "rewrites" for "breaks". The first passes
//   with every other change here, by design.
// * a const's seal read off the stored root's own span, not where the value was written
//   (`written_site`): `a_programs_const_rewritten_by_a_sealed_equation_stays_the_-
//   programs` FAILS — the third load is refused, "rewrites the value of const
//   'test.progk.mine', which a sealed load declared".

const LIB_CONST: &str = r#"
namespace test.libk
  import anthill.prelude.{Int64}
  import anthill.prelude.Additive.{add}

  operation base(x: Int64) -> Int64 = 1
  const libConst: Int64 = base(5)
  operation libReads() -> Int64 = libConst
  const libSum: Int64 = add(base(5), 1)

  sort Kind
    entity k1
    entity k2
  end
  operation weight(k: Kind) -> Int64 = 1
  const libWeight: Int64 = weight(k1())
  operation libWeighs() -> Int64 = libWeight

  operation inner(n: Int64) -> Int64 = n
  operation outer(n: Int64) -> Int64
  rule outer(?n) <=> inner(?n) @[simp]
end
"#;

const A_RULE_OVER_A_CALL_IN_A_LIBRARY_CONST: &str = r#"
namespace test.progk
  import anthill.prelude.{Int64}
  import test.libk.{base, libReads}
  rule base(?x) <=> 2 @[simp]
  operation entry() -> Int64 = libReads()
end
"#;

/// In one call the program's rule rewrites the library const's value, and the library
/// reads 2 by it. Behind the seal that value was typed and is not typed again.
#[test]
fn a_simp_rule_that_rewrites_a_sealed_consts_value_is_refused() {
    let kb = loaded(one_call(LIB_CONST, A_RULE_OVER_A_CALL_IN_A_LIBRARY_CONST), "one call");
    assert_eq!(values(kb, &["test.progk.entry"]), [2]);

    let errors =
        refused(two_calls(LIB_CONST, A_RULE_OVER_A_CALL_IN_A_LIBRARY_CONST), "two calls");
    assert!(
        errors.iter().any(|e| e.contains("`@[simp]` rule over 'test.libk.base'")
            && e.contains("rewrites the value of const 'test.libk.libConst'")),
        "the refusal names the rule's head and the sealed const; got {errors:?}"
    );
}

const A_RULE_FOR_AN_ARGUMENT_NO_LIBRARY_CONST_WRITES: &str = r#"
namespace test.progk
  import anthill.prelude.{Int64}
  import test.libk.{Kind, weight, libWeighs}
  import test.libk.Kind.{k2}
  rule weight(k2()) <=> 2 @[simp]
  operation entry() -> Int64 = weight(k2())
  operation lib() -> Int64 = libWeighs()
end
"#;

/// Exact here too: `libWeight` still holds its call of `weight`, a bodied operation,
/// and a rule over `weight` for an argument that call does not write rewrites nothing
/// sealed and loads.
#[test]
fn a_simp_rule_that_reaches_no_sealed_consts_value_loads() {
    for (how, kb) in [
        ("one call", one_call(LIB_CONST, A_RULE_FOR_AN_ARGUMENT_NO_LIBRARY_CONST_WRITES)),
        ("two calls", two_calls(LIB_CONST, A_RULE_FOR_AN_ARGUMENT_NO_LIBRARY_CONST_WRITES)),
    ] {
        assert_eq!(
            values(loaded(kb, how), &["test.progk.entry", "test.progk.lib"]),
            [2, 1],
            "{how}"
        );
    }
}

const A_RULE_THAT_BREAKS_A_LIBRARY_CONST: &str = r#"
namespace test.progk
  import anthill.prelude.{Int64}
  import test.libk.{base}
  rule base(?x) <=> "two" @[simp]
end
"#;

/// A rewrite that leaves a sealed value ILL-TYPED inside — `add("two", 1)` — is not
/// written back, so only what typing it reports says the rule reached it. One that is
/// ill-typed against the const's declared type alone is written first and compared
/// after, as an operation body is with its return type.
#[test]
fn a_simp_rule_that_breaks_a_sealed_consts_value_is_refused() {
    let one = refused(one_call(LIB_CONST, A_RULE_THAT_BREAKS_A_LIBRARY_CONST), "one call");
    assert!(
        one.iter().any(|e| e.contains("type mismatch in add.b"))
            && one.iter().any(|e| e.contains("libConst.value")),
        "one call reports the two library consts the rule broke; got {one:?}"
    );

    let two = refused(two_calls(LIB_CONST, A_RULE_THAT_BREAKS_A_LIBRARY_CONST), "two calls");
    for (how, constant) in [("breaks", "libSum"), ("rewrites", "libConst")] {
        assert!(
            two.iter().any(|e| e.contains("`@[simp]` rule over 'test.libk.base'")
                && e.contains(&format!("{how} the value of const 'test.libk.{constant}'"))),
            "the rule {how} `{constant}`; got {two:?}"
        );
    }
}

const A_CONST_OVER_A_LIBRARY_EQUATION: &str = r#"
namespace test.progk
  import anthill.prelude.{Int64}
  import test.libk.{outer}
  const mine: Int64 = outer(4)
  operation entry() -> Int64 = mine
end
"#;

const A_RULE_OVER_WHAT_THAT_EQUATION_WROTE: &str = r#"
namespace test.progm
  import anthill.prelude.{Int64}
  import test.libk.{inner}
  import test.progk.{entry}
  rule inner(4) <=> 9 @[simp]
  operation again() -> Int64 = entry()
end
"#;

/// A const of the program's, rewritten at its top by a SEALED equation, holds that
/// equation's text: `inner(4)`, whose span is in the library's file. The const is still
/// the program's. A load after it is not held to it as to a sealed value, and types it
/// again, as it types every body no seal holds.
#[test]
fn a_programs_const_rewritten_by_a_sealed_equation_stays_the_programs() {
    let mut kb = loaded(two_calls(LIB_CONST, A_CONST_OVER_A_LIBRARY_EQUATION), "two calls");
    load_in_a_later_call(&mut kb, A_RULE_OVER_WHAT_THAT_EQUATION_WROTE, LoadOptions::default())
        .map(|_| ())
        .map_err(rendered_load_errors)
        .unwrap_or_else(|e| panic!("the third load is the program's own; got {e:?}"));
    assert_eq!(values(kb, &["test.progm.again"]), [9]);
}

// ── (2) an operation added to a sealed scope ─────────────────────────

const LIB_SCOPE: &str = r#"
namespace test.libb
  import anthill.prelude.{Int64}

  operation helper() -> Int64 = 1

  sort Box
    entity box(n: Int64)
    operation libCall(b: Box) -> Int64 = helper()
  end
end
"#;

const AN_OPERATION_UNDER_A_NAME_THE_LIBRARY_READS: &str = r#"
namespace test.libb.Box
  import anthill.prelude.{Int64}
  operation helper() -> Int64 = 2
end
"#;

#[test]
fn an_operation_that_captures_a_sealed_name_is_refused_in_both() {
    for (how, verdict) in [
        ("one call", one_call(LIB_SCOPE, AN_OPERATION_UNDER_A_NAME_THE_LIBRARY_READS)),
        ("two calls", two_calls(LIB_SCOPE, AN_OPERATION_UNDER_A_NAME_THE_LIBRARY_READS)),
    ] {
        let errors = refused(verdict, how);
        assert!(
            errors.iter().any(|e| e.contains("captures a name that already resolves")
                && e.contains("'test.libb.helper'")),
            "{how}: got {errors:?}"
        );
    }
}

// ── (3) providers and overrides ──────────────────────────────────────

/// A spec `Desc` with a defaulted `rank`; `Leaf` providing it itself (1); `Wrap[E]`
/// given `Desc[E]` (10·inner + 2); `Leaf2` providing nothing, with ONE witness `W1`
/// (3); `Pair2[Leaf, B]` by the witness `LeftLeaf` (5); and library bodies that ask at
/// concrete types and through a requirement.
const LIB_DESC: &str = r#"
namespace test.libc
  import anthill.prelude.{Int64}
  import anthill.prelude.Additive.{add}
  import anthill.prelude.Multiplicative.{mul}

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
    operation rank(x: T) -> Int64 = 0
  end

  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 1
  end

  sort Wrap
    sort A = ?
    entity wrap(inner: A)
  end

  sort WrapDesc
    sort E = ?
    requires Desc[T = E]
    provides Desc[T = Wrap[A = E]]
    operation describe(w: Wrap[A = E]) -> Int64 =
      add(mul(10, Desc.describe(w.inner)), 2)
  end

  sort Leaf2
    entity leaf2
  end

  sort W1
    provides Desc[T = Leaf2]
    operation describe(x: Leaf2) -> Int64 = 3
  end

  sort Pair2
    sort A = ?
    sort B = ?
    entity pair2(a: A, b: B)
  end

  sort LeftLeaf
    sort B = ?
    provides Desc[T = Pair2[A = Leaf, B = B]]
    operation describe(p: Pair2[A = Leaf, B = B]) -> Int64 = 5
  end

  -- A spec DISPATCHED BY ITS RECEIVER: its carrier is whoever provides it.
  sort Shape
    sort T = ?
    operation area(s: Self) -> T
  end

  sort Sq
    entity sq(n: Int64)
    provides Shape[T = Int64]
    operation area(s: Sq) -> Int64 = 4
  end

  operation libAtWrapLeaf() -> Int64 = Desc.describe(wrap(leaf()))
  operation libAtPairOfLeaves() -> Int64 = Desc.describe(pair2(leaf(), leaf()))
  operation libArea() -> Int64 = Shape.area(sq(2))
  operation libAtLeaf() -> Int64 = Desc.describe(leaf())
  operation libAtLeaf2() -> Int64 = Desc.describe(leaf2())
  operation libGeneric[X](x: X) -> Int64 requires Desc[T = X] = Desc.describe(x)
  operation libRank[X](x: X) -> Int64 requires Desc[T = X] = Desc.rank(x)
end
"#;

const A_MORE_SPECIFIC_PROVISION_OF_LIBRARY_ELEMENTS: &str = r#"
namespace test.progc
  import anthill.prelude.{Int64}
  import test.libc.{Desc, Wrap, Leaf, libAtWrapLeaf, libGeneric}
  import test.libc.Wrap.{wrap}
  import test.libc.Leaf.{leaf}

  sort WrapLeafDesc
    provides Desc[T = Wrap[A = Leaf]]
    operation describe(w: Wrap[A = Leaf]) -> Int64 = 2
  end

  operation atTheLibrarysCall() -> Int64 = libAtWrapLeaf()
  operation atItsOwnCall() -> Int64 = Desc.describe(wrap(leaf()))
  operation throughAGenericBody() -> Int64 = libGeneric(wrap(leaf()))
end
"#;

#[test]
fn a_more_specific_provision_of_sealed_elements_is_refused() {
    // One call: the strictly more specific provision answers everywhere, the library's
    // own call included.
    let kb = loaded(one_call(LIB_DESC, A_MORE_SPECIFIC_PROVISION_OF_LIBRARY_ELEMENTS), "one call");
    assert_eq!(
        values(
            kb,
            &[
                "test.progc.atTheLibrarysCall",
                "test.progc.atItsOwnCall",
                "test.progc.throughAGenericBody"
            ]
        ),
        [2, 2, 2]
    );

    let errors = refused(
        two_calls(LIB_DESC, A_MORE_SPECIFIC_PROVISION_OF_LIBRARY_ELEMENTS),
        "two calls",
    );
    assert!(
        errors.iter().any(|e| e.contains("changes who answers")
            && e.contains("test.libc.Desc[T = test.libc.Wrap[A = test.libc.Leaf]]")
            && e.contains("there it is 'test.libc.WrapDesc'")
            && e.contains("it would be 'test.progc.WrapLeafDesc'")),
        "the refusal names the goal, who answered and who would; got {errors:?}"
    );
}

/// NOTHING SEALED: the same file after an UNSEALED library answers as one call does —
/// the earlier load's bodies are typed again and follow the provision, and the later
/// load's own call is answered from the provisions as they stand. Before this ticket
/// the last was not so: the typer's dispatch memo was never dropped between loads, and
/// the file's own call got the earlier load's memoized choice (12, 12, 2).
#[test]
fn nothing_sealed_a_later_loads_provision_answers_as_in_one_call() {
    let mut kb = crate::common::load_unsealed(&[LIB_DESC]);
    load_in_a_later_call(
        &mut kb,
        A_MORE_SPECIFIC_PROVISION_OF_LIBRARY_ELEMENTS,
        LoadOptions::default(),
    )
    .map_err(rendered_load_errors)
    .expect("nothing is sealed, so nothing is refused");
    assert_eq!(
        values(
            kb,
            &[
                "test.progc.atTheLibrarysCall",
                "test.progc.atItsOwnCall",
                "test.progc.throughAGenericBody"
            ]
        ),
        [2, 2, 2]
    );
}

const AN_OVERLAPPING_PROVISION_NEITHER_MORE_SPECIFIC: &str = r#"
namespace test.progc
  import anthill.prelude.{Int64}
  import test.libc.{Desc, Pair2, Leaf, libAtPairOfLeaves}

  sort RightLeaf
    sort A = ?
    provides Desc[T = Pair2[A = A, B = Leaf]]
    operation describe(p: Pair2[A = A, B = Leaf]) -> Int64 = 6
  end

  operation atTheLibrarysCall() -> Int64 = libAtPairOfLeaves()
end
"#;

/// Two provisions that overlap with neither the more specific: `Pair2[Leaf, B]` is the
/// library's and `Pair2[A, Leaf]` the program's, and at `Pair2[Leaf, Leaf]` — where the
/// library's body asks — they tie. Neither is a candidate at the other's head, so the
/// answer at the provision's own head says nothing; the overlap is what is refused.
#[test]
fn an_overlapping_provision_with_neither_more_specific_is_refused() {
    let one = refused(one_call(LIB_DESC, AN_OVERLAPPING_PROVISION_NEITHER_MORE_SPECIFIC), "one call");
    assert!(
        one.iter().any(|e| e.contains("ambiguous dispatch of `test.libc.Desc.describe`")),
        "one call refuses the library's own call, which meets the tie; got {one:?}"
    );

    let two = refused(
        two_calls(LIB_DESC, AN_OVERLAPPING_PROVISION_NEITHER_MORE_SPECIFIC),
        "two calls",
    );
    assert!(
        two.iter().any(|e| e.contains("overlaps the one 'test.libc.LeftLeaf' makes")
            && e.contains("neither is the more specific")),
        "got {two:?}"
    );
}

const A_SECOND_IMPLEMENTATION_OF_A_RECEIVER_SPEC: &str = r#"
namespace test.progs
  import anthill.prelude.{Int64}
  import test.libc.{Shape, libArea}

  sort Circ
    entity circ(r: Int64)
    provides Shape[T = Int64]
    operation area(s: Circ) -> Int64 = 9
  end

  operation itsOwn() -> Int64 = Shape.area(circ(1))
  operation atTheLibrarysCall() -> Int64 = libArea()
end
"#;

/// A spec dispatched by its RECEIVER has its carrier in no binding — the carrier is the
/// provider. A program's second implementation of one is therefore a provision with an
/// element of the program's own, though its head mentions none, and loads: no sealed
/// call has a `Circ` to be answered about.
#[test]
fn a_second_implementation_of_a_receiver_dispatched_spec_loads() {
    for (how, kb) in [
        ("one call", one_call(LIB_DESC, A_SECOND_IMPLEMENTATION_OF_A_RECEIVER_SPEC)),
        ("two calls", two_calls(LIB_DESC, A_SECOND_IMPLEMENTATION_OF_A_RECEIVER_SPEC)),
    ] {
        assert_eq!(
            values(loaded(kb, how), &["test.progs.itsOwn", "test.progs.atTheLibrarysCall"]),
            [9, 4],
            "{how}"
        );
    }
}

const A_MORE_SPECIFIC_PROVISION_THROUGH_AN_ALIAS: &str = r#"
namespace test.progc
  import anthill.prelude.{Int64}
  import test.libc.{Desc, Wrap, Leaf}

  sort Blade = Leaf

  sort WrapBladeDesc
    provides Desc[T = Wrap[A = Blade]]
    operation describe(w: Wrap[A = Blade]) -> Int64 = 2
  end
end
"#;

/// An ALIAS in the head is the type it stands for: `Wrap[A = Blade]` is `Wrap[A = Leaf]`
/// to the dispatch, so this is the refused provision spelled through a name of the
/// program's own, and that name does not make it the program's.
#[test]
fn a_more_specific_provision_written_through_an_alias_is_refused() {
    let errors = refused(
        two_calls(LIB_DESC, A_MORE_SPECIFIC_PROVISION_THROUGH_AN_ALIAS),
        "two calls",
    );
    assert!(
        errors.iter().any(|e| e.contains("changes who answers")
            && e.contains("there it is 'test.libc.WrapDesc'")),
        "got {errors:?}"
    );
}

/// …and its refusal points at the binding that wrote the head: a type written through an
/// alias is held on an occurrence, which has its own place. (A head written out is a term,
/// which has none, and its refusal carries no place.)
///
/// FAILS with the place read off a term alone (`sealed::written_view_site` answering
/// nothing for an occurrence).
#[test]
fn the_refusal_of_a_provision_written_through_an_alias_points_at_its_binding() {
    let errors = refused(
        two_calls(LIB_DESC, A_MORE_SPECIFIC_PROVISION_THROUGH_AN_ALIAS),
        "two calls",
    );
    assert!(
        errors
            .iter()
            .any(|e| e.starts_with("9:23: this provision changes who answers")),
        "got {errors:?}"
    );
}

const A_SECOND_PROVISION_WRITTEN_INTO_A_LIBRARY_SORT: &str = r#"
namespace test.libc.Leaf
  import anthill.prelude.{Int64}
  import test.libc.{Desc}
  operation otherDescribe(x: Leaf) -> Int64 = 8
  provides Desc[T = Leaf, describe = otherDescribe]
end
"#;

/// A provision written INTO a sealed sort beside the one it already makes, binding
/// another member: the dispatcher reads the two as ONE candidate, so nothing about who
/// answers changes — while one load of both meets the tie between the two members at
/// the library's own call.
#[test]
fn a_second_provision_written_into_a_sealed_sort_is_refused() {
    let one = refused(
        one_call(LIB_DESC, A_SECOND_PROVISION_WRITTEN_INTO_A_LIBRARY_SORT),
        "one call",
    );
    assert!(
        one.iter().any(|e| e.contains("ambiguous dispatch of `test.libc.Desc.describe`")
            && e.contains("otherDescribe")),
        "one call refuses the library's own call, which meets the two members; got {one:?}"
    );

    let two = refused(
        two_calls(LIB_DESC, A_SECOND_PROVISION_WRITTEN_INTO_A_LIBRARY_SORT),
        "two calls",
    );
    assert!(
        two.iter().any(|e| e.contains("is written for 'test.libc.Leaf', which a sealed load")
            && e.contains("already provides it there")),
        "got {two:?}"
    );
}

const A_FIRST_PROVISION_WRITTEN_INTO_A_LIBRARY_SORT: &str = r#"
namespace test.libc.Leaf2
  import anthill.prelude.{Int64}
  import test.libc.{Desc}
  provides Desc[T = Leaf2]
  operation describe(x: Leaf2) -> Int64 = 8
end
"#;

/// …and one written into a sealed sort that provided NOTHING of the spec: it makes the
/// carrier its own default beside the one witness that answered, which is the changed
/// answer the comparison refuses.
#[test]
fn a_first_provision_written_into_a_sealed_sort_changes_who_answers() {
    let errors = refused(
        two_calls(LIB_DESC, A_FIRST_PROVISION_WRITTEN_INTO_A_LIBRARY_SORT),
        "two calls",
    );
    assert!(
        errors.iter().any(|e| e.contains("changes who answers")
            && e.contains("there it is 'test.libc.W1'")
            && e.contains("it would be 'test.libc.Leaf2'")),
        "got {errors:?}"
    );
}

const LIB_CLAUSES: &str = r#"
namespace test.libq
  import anthill.prelude.{Int64}
  sort Tag
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort Ready
    sort T = ?
  end
  sort Steady
    sort T = ?
  end
  sort Plain
    entity plain
    provides Ready[T = Plain]
  end
  sort Rough
    entity rough
    provides Steady[T = Rough]
  end
  sort Box
    sort V = ?
    entity box(v: V)
    provides Tag[T = Box[V = V]] :- Ready[T = V]
    operation tag(x: Box[V = V]) -> Int64 = 1
  end
  operation libTag() -> Int64 = Tag.tag(box(v: plain()))
end
"#;

/// A clause of `Box`'s provision of `Tag` with no condition, and the call it lets
/// through: `Tag` at a `Box` of a type that is not `Ready`.
const A_CLAUSE_WITH_NO_CONDITION: &str = r#"
namespace test.libq.Box
  import test.libq.{Tag}
  provides Tag[T = Box[V = V]]
end
namespace test.progq
  import anthill.prelude.{Int64}
  import test.libq.{Tag}
  import test.libq.Box.{box}
  import test.libq.Rough.{rough}
  operation progTag() -> Int64 = Tag.tag(box(v: rough()))
end
"#;

/// …and one with another condition, which `Rough` meets.
const A_CLAUSE_WITH_ANOTHER_CONDITION: &str = r#"
namespace test.libq.Box
  import test.libq.{Tag, Steady}
  provides Tag[T = Box[V = V]] :- Steady[T = V]
end
namespace test.progq
  import anthill.prelude.{Int64}
  import test.libq.{Tag}
  import test.libq.Box.{box}
  import test.libq.Rough.{rough}
  operation progTag() -> Int64 = Tag.tag(box(v: rough()))
end
"#;

/// A CLAUSE written into a sealed sort at the head of a provision it already makes, under
/// other conditions. In one call it is an alternative clause, and the call the library's
/// condition leaves out is answered. Behind the seal it writes the row the library's
/// clause wrote, which the walk over the rows asserted since never meets: the clause
/// records are what see it.
/// BACK-OUT: with the clause records not read, both programs load clean in two calls
/// (MEASURED).
#[test]
fn a_clause_written_into_a_sealed_provision_is_refused() {
    for program in [A_CLAUSE_WITH_NO_CONDITION, A_CLAUSE_WITH_ANOTHER_CONDITION] {
        let one = loaded(one_call(LIB_CLAUSES, program), "one call");
        assert_eq!(values(one, &["test.progq.progTag"]), vec![1]);
        let two = refused(two_calls(LIB_CLAUSES, program), "two calls");
        assert!(
            two.iter().any(|e| e.contains("is written for 'test.libq.Box', which a sealed load")
                && e.contains("under other conditions")),
            "got {two:?}"
        );
    }
}

const A_SECOND_WITNESS_WHERE_THE_LIBRARY_HAD_ONE: &str = r#"
namespace test.progc
  import anthill.prelude.{Int64}
  import test.libc.{Desc, Leaf2, libAtLeaf2}

  sort W2
    provides Desc[T = Leaf2]
    operation describe(x: Leaf2) -> Int64 = 4
  end

  operation atTheLibrarysCall() -> Int64 = libAtLeaf2()
end
"#;

/// A tie where the library had ONE answer and no default: in one call the library's
/// own unselected call is refused as ambiguous, so in two it may not load clean and
/// leave that call answering `W1`.
#[test]
fn a_second_witness_that_ties_a_sealed_answer_is_refused() {
    let one = refused(one_call(LIB_DESC, A_SECOND_WITNESS_WHERE_THE_LIBRARY_HAD_ONE), "one call");
    assert!(
        one.iter().any(|e| e.contains("ambiguous dispatch of `test.libc.Desc.describe`")),
        "one call refuses the library's own call; got {one:?}"
    );

    let two = refused(two_calls(LIB_DESC, A_SECOND_WITNESS_WHERE_THE_LIBRARY_HAD_ONE), "two calls");
    assert!(
        two.iter().any(|e| e.contains("changes who answers")
            && e.contains("there it is 'test.libc.W1'")
            && e.contains("no single provider answers")),
        "got {two:?}"
    );
}

const A_NAMED_RIVAL_BESIDE_THE_CARRIERS_OWN: &str = r#"
namespace test.progc
  import anthill.prelude.{Int64}
  import test.libc.{Desc, Leaf, libAtLeaf}
  import test.libc.Leaf.{leaf}

  sort Rival
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end

  operation atTheLibrarysCall() -> Int64 = libAtLeaf()
  operation unselected() -> Int64 = Desc.describe(leaf())
  operation selected() -> Int64 = Desc.describe[Desc = Rival](leaf())
end
"#;

/// The language's named-instance feature, over sealed elements throughout: a second
/// provider beside the carrier's own leaves every unselected call where it was, and is
/// reached by the call that names it. `ByLength provides Ord[T = String]` is this.
#[test]
fn a_named_rival_beside_a_sealed_default_loads() {
    for (how, kb) in [
        ("one call", one_call(LIB_DESC, A_NAMED_RIVAL_BESIDE_THE_CARRIERS_OWN)),
        ("two calls", two_calls(LIB_DESC, A_NAMED_RIVAL_BESIDE_THE_CARRIERS_OWN)),
    ] {
        assert_eq!(
            values(
                loaded(kb, how),
                &[
                    "test.progc.atTheLibrarysCall",
                    "test.progc.unselected",
                    "test.progc.selected"
                ]
            ),
            [1, 1, 7],
            "{how}"
        );
    }
}

const A_SPEC_THAT_CONVERTS_TO_A_LIBRARY_SPEC: &str = r#"
namespace test.progv
  import anthill.prelude.{Int64}
  import test.libc.{Desc, libAtLeaf}

  sort Rich
    sort T = ?
    provides Desc[T = T]
    operation extra(x: T) -> Int64
  end

  operation atTheLibrarysCall() -> Int64 = libAtLeaf()
end
"#;

/// A spec of the program's own that PROVIDES a library spec at its own parameter is a
/// conversion — hold a `Rich[T]` and a `Desc[T]` can be had — and provides at no type.
/// It answers no dispatch, so it changes none, and loads after a sealed library as
/// with it.
#[test]
fn a_spec_that_converts_to_a_sealed_spec_loads() {
    for (how, kb) in [
        ("one call", one_call(LIB_DESC, A_SPEC_THAT_CONVERTS_TO_A_LIBRARY_SPEC)),
        ("two calls", two_calls(LIB_DESC, A_SPEC_THAT_CONVERTS_TO_A_LIBRARY_SPEC)),
    ] {
        assert_eq!(values(loaded(kb, how), &["test.progv.atTheLibrarysCall"]), [1], "{how}");
    }
}

const A_NAMED_ORDERING_FOR_A_LIBRARY_TYPE: &str = r#"
namespace test.progo
  import anthill.prelude.{Int64, String, WeakOrd}

  sort ByLength
    import anthill.prelude.String.{length}
    import anthill.prelude.Numeric.{sub}
    provides WeakOrd[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(length(a), length(b))
  end

  operation selected() -> Int64 = WeakOrd.compare[WeakOrd = ByLength]("zz", "aa")
  operation unselected() -> Int64 = WeakOrd.compare("zz", "aa")
end
"#;

/// The same against the standard library itself: `ByLength provides WeakOrd[T = String]`
/// is a second ordering of a library type under a library spec, beside `String`'s own.
/// It loads after the sealed library as with it, the call that names it gets it (two
/// strings of one length compare equal) and the one that does not gets `String`'s.
///
/// The row the CONVERSION is for: `Ord provides WeakOrd[T = T]` says how to obtain one
/// spec from the other and provides at no type. Taken for a provision, its head — a
/// bare parameter — overlaps every provision of `WeakOrd` there is.
#[test]
fn a_named_ordering_for_a_standard_library_type_loads_after_it() {
    for recipe in [LoadRecipe::OneShot, LoadRecipe::TwoStep] {
        let kb = recipe_load(
            &[A_NAMED_ORDERING_FOR_A_LIBRARY_TYPE],
            None,
            LoadOptions::default(),
            recipe,
            |_| {},
        )
        .map(|(kb, _)| kb)
        .map_err(rendered_load_errors);
        let got = values(
            loaded(kb, &format!("{recipe:?}")),
            &["test.progo.selected", "test.progo.unselected"],
        );
        assert_eq!(got[0], 0, "{recipe:?}: `ByLength` calls \"zz\" and \"aa\" equal");
        assert!(got[1] > 0, "{recipe:?}: `String`'s own ordering puts \"zz\" after \"aa\"");
    }
}

const A_PROVIDER_AND_AN_OVERRIDE_FOR_ITS_OWN_TYPE: &str = r#"
namespace test.progc
  import anthill.prelude.{Int64}
  import test.libc.{Desc, Wrap, libGeneric, libRank}
  import test.libc.Wrap.{wrap}

  sort Mine
    entity mine
    provides Desc[T = Mine]
    operation describe(x: Mine) -> Int64 = 7
    operation rank(x: Mine) -> Int64 = 5
  end

  sort WrapMineDesc
    provides Desc[T = Wrap[A = Mine]]
    operation describe(w: Wrap[A = Mine]) -> Int64 = 9
  end

  operation throughAGenericBody() -> Int64 = libGeneric(mine())
  operation theOverride() -> Int64 = libRank(mine())
  operation moreSpecificAtItsOwnType() -> Int64 = libGeneric(wrap(mine()))
end
"#;

/// What must keep working, and does with no library body typed again (user,
/// 2026-10-10): a provider, an override of a spec's default, and a provision MORE
/// SPECIFIC than the library's at a type of the program's own — each reaches a generic
/// library body through the dictionary the program's call passes. The last is the one
/// the refusal must not take: its head mentions `Mine`, which no sealed body can name.
#[test]
fn a_provider_and_an_override_for_the_programs_own_type_reach_a_sealed_body() {
    for (how, kb) in [
        ("one call", one_call(LIB_DESC, A_PROVIDER_AND_AN_OVERRIDE_FOR_ITS_OWN_TYPE)),
        ("two calls", two_calls(LIB_DESC, A_PROVIDER_AND_AN_OVERRIDE_FOR_ITS_OWN_TYPE)),
    ] {
        assert_eq!(
            values(
                loaded(kb, how),
                &[
                    "test.progc.throughAGenericBody",
                    "test.progc.theOverride",
                    "test.progc.moreSpecificAtItsOwnType"
                ]
            ),
            [7, 5, 9],
            "{how}"
        );
    }
}

// ── The relation check ───────────────────────────────────────────────

const LIB_RELATION: &str = r#"
namespace test.libr
  import anthill.prelude.{Int64}
  sort U
    operation ilen(n: Int64) -> Int64 = n
  end
  fact isInt(1)
  rule tagged(?x) :- isInt(?x)
  rule doubled(?r) :- tagged(?v), ?r <=> U.ilen(?v)
end
"#;

/// A CLAUSE A LATER LOAD ADDS TO A SEALED RELATION, THAT CHANGES WHAT ITS COLUMNS READ, IS
/// REFUSED: `fact tagged("a")` beside the library's `tagged`, whose column is an `Int64`,
/// makes it of some type, and the library's `doubled` hands it to `ilen` as an `Int64`. In
/// one call the clause typing refuses `doubled` for it; behind the seal `doubled` is not
/// typed again, so the clause is refused where it is written.
#[test]
fn a_clause_that_changes_a_sealed_relations_columns_is_refused() {
    // `tagged(2)` first, at the column's own type: the refusal is said at `tagged("a")`,
    // line 4, the clause that changes the reading (found by /code-review).
    let program = "namespace test.progr\n  import test.libr.{tagged}\n  fact tagged(2)\n  \
                   fact tagged(\"a\")\nend\n";
    let errors = refused(one_call(LIB_RELATION, program), "one call");
    assert!(
        errors.iter().any(|e| e.contains("type mismatch in ilen.n (op-arg)")
            && e.contains("got a value of some type: `tagged._1`")),
        "one call refuses the library's reader; got {errors:?}"
    );
    let errors = refused(two_calls(LIB_RELATION, program), "two calls");
    assert!(
        errors.len() == 1
            && errors[0].starts_with("4:8:")
            && errors[0].contains(
                "a clause for 'test.libr.tagged', which a sealed load wrote, changes how its \
                 column `_1` reads — `anthill.prelude.Int64` over the sealed load's clauses, of \
                 some type with this one"
            ),
        "two calls refuse the clause; got {errors:?}"
    );
}

/// CONTROL, PASSES EITHER WAY: a clause at the column's own type adds rows and changes no
/// reading — `fact tagged(2)` loads in two calls, and the library's `doubled` answers it.
#[test]
fn a_clause_at_a_sealed_relations_column_types_loads() {
    let program = "namespace test.progr\n  import test.libr.{tagged}\n  fact tagged(2)\nend\n";
    let mut kb = loaded(two_calls(LIB_RELATION, program), "two calls");
    let mut answers: Vec<i64> = crate::common::query_unary(&mut kb, "test.libr.doubled")
        .into_iter()
        .map(|(v, _)| match v {
            Value::Int(n) => n,
            other => panic!("an Int64 answer, got {other:?}"),
        })
        .collect();
    answers.sort();
    assert_eq!(answers, [1, 2]);
}

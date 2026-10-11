//! WI-20261011-A3NND — A SEALED LOAD'S PROVISIONS ARE CHECKED ONCE.
//!
//! `check_provider_requires` resolved the contract of every provision of the KB at
//! every load: 27 ms of a 65 ms load of a one-operation file into a copy of the sealed
//! standard library (`docs/measurements/test-infrastructure/provider-requires-2026-10-11.txt`).
//! Behind a seal it reads the provisions asserted since, and every one when something
//! asserted since can change the verdict of a provision the seal holds
//! (`typing::checked_provisions`, whose module doc has the argument).
//!
//! The trap is a row skipped that should have been checked: it fails in silence. So the
//! rows here assert on what a load's verdict cannot show — HOW MANY provisions the
//! check read (`provisions_checked_by_this_thread`) — beside the verdicts, and there is
//! one for each way a later load can reach an earlier provision.
//!
//! WHAT FAILS WHEN THE CHANGE IS BACKED OUT — measured, each by making the change and
//! running this file (17 rows as it stands, 2026-10-11, the dev profile; re-measured
//! after /code-review's changes):
//!
//! * the check made to read every row whatever a seal holds (`rows_a_run_reads` taking
//!   no seal's word): 4 FAIL — `a_later_load_reads_the_provisions_it_brought`,
//!   `a_conversion_to_a_sealed_spec_is_read_with_the_programs_rows`,
//!   `a_seal_of_all_of_a_loads_files_holds_its_provisions`, and
//!   `a_refused_provision_is_refused_again_by_the_next_load` on its count. The other 13
//!   pass: they assert that every row IS read.
//! * the check made to skip the held rows whatever was asserted since
//!   (`later_fact_that_reaches_a_held_verdict` answering `None`): 8 FAIL — the five rows
//!   named `…_reads_every_provision` on their counts, and `a_second_answer_for_a_sealed_goal_is_refused_as_in_one_call`,
//!   `a_requires_written_into_a_sealed_sort_refuses_the_next_load_too` and
//!   `a_type_parameter_written_into_a_sealed_sort_refuses_the_next_load_too` on their
//!   VERDICTS as well: the tie, the unmet requirement and the refinement turned demand
//!   load clean in two calls. Under `ANTHILL_PROVISION_ORACLE=1` the same eight fail,
//!   and the ones whose full run refuses anything panic with the oracle's own report,
//!   which names the errors only the full run gives.
//! * each clause of that function alone: no type-parameter clause,
//!   `a_type_parameter_written_into_…` FAILS; no `requires` clause,
//!   `a_requires_written_into_…`; no "the provider was there before",
//!   `a_provision_written_into_a_sealed_sort_…`; no need for a binding of the later
//!   load's own, four — `a_second_answer_…`, `a_generic_provision_…`,
//!   `a_provision_at_an_alias_…`, `a_provision_at_a_spec_…`; `is_inert` without its
//!   provider clause, `a_provision_at_a_spec_…`; a conversion not exempt,
//!   `a_conversion_to_a_sealed_spec_…`.
//! * `check_provider_requires_since` made to read nothing (`load_phase_inner`): 2 FAIL —
//!   `a_derived_noneq_is_checked_by_the_load_that_derives_it`, nine rows short (407 of
//!   416: the library's eight derived `NonEq` and `Reading`'s), and
//!   `a_load_sealed_before_its_check_ran_is_checked_by_the_next`, eight short (417 of
//!   425): the library's eight, which a load that stopped before its typer never
//!   derived and the next load derives below its check.
//! * a load that stops before its typer made to record a check all the same
//!   (`LastLoad::provisions_checked` set at that exit):
//!   `a_load_sealed_before_its_check_ran_is_checked_by_the_next` FAILS.
//! * a seal made to hold the provisions whatever part of the load it is of
//!   (`seal_declarations_where` not asking `whole_load`):
//!   `a_seal_of_a_loads_first_files_holds_no_provision` FAILS. A seal of ALL of a load's
//!   files made to hold nothing: the four rows of the first back-out FAIL — and, under
//!   `ANTHILL_PROVISION_ORACLE=1`, `the_oracle_runs_when_it_is_asked_for` with them:
//!   asked for, and no narrowed run to compare. (The first cut held them only by the
//!   door named `seal_declarations`, the shared base is sealed by the other, and
//!   nothing in the suite then failed — `a_seal_of_all_of_…` did not exist, and the
//!   oracle's control counted runs that read every row. Measured on that cut: with the
//!   row added, it alone failed.)
//! * the variable misspelt in `typing::provision_oracle_on` (one letter) and
//!   `ANTHILL_PROVISION_ORACLE=1` set: `the_oracle_runs_when_it_is_asked_for` FAILS —
//!   asked for, no run compared — and the 16 others pass, judged by nothing.
//!
//! AND ONE UNIT ROW, beside the code (`typing::checked_provisions::a3nnd_seal_tests`): a
//! provision asserted between a load's check and its seal is read by the next load. It
//! FAILS with the seal taking its slot count where the seal is taken.
//!
//! NOT DRIVEN BY ANY ROW, each a clause that only makes the check read MORE, and said
//! at its site: the `ProvidesConditionInfo` clause (a written `provides … :-` files its
//! row beside the condition, and the provider clause answers for the row —
//! `a_condition_written_for_a_sealed_sort_…` passes without it); `is_inert`'s alias
//! clause (a head written through an alias is read through the view as the type it
//! stands for, so `a_provision_at_an_alias_…` passes without it); and the canonical
//! half of `is_later`. And one that makes it read LESS when it is wrong, the guard for
//! a goal with a binding left open: no fixture was found that puts one to the search
//! and loads clean (the module doc).
//!
//! BY DESIGN
//! * the ONE-CALL half of `a_second_answer_…` passes either way: it is what the fixture
//!   means.
//! * `nothing_sealed_nothing_skipped` passes with or without the change: a plain
//!   sequence of loads is what the check always was. It is the row that fails if the
//!   narrowing ever reaches a KB nothing sealed.
//!
//! PINNED TO RECIPES BY NAME, every row: the subject is what a LATER load reads, so no
//! row may follow the switch.

use anthill_core::kb::load::{self, LoadOptions};
use anthill_core::kb::typing::{provision_oracle_runs_by_this_thread, provisions_checked_by_this_thread};
use anthill_core::kb::KnowledgeBase;

use crate::common::{load_in_a_later_call, recipe_load, rendered_load_errors, LoadRecipe};

/// Two specs, the second requiring the first, a type, and a witness of each for it:
/// `HighW`'s contract — `Low[T = Leaf]` — is answered by `LowA`, through the search.
const LIB: &str = r#"
namespace test.a3lib
  import anthill.prelude.{Int64}

  sort Low
    sort T = ?
    operation low(x: T) -> Int64
  end

  sort High
    sort T = ?
    requires Low[T = T]
    operation high(x: T) -> Int64
  end

  sort Leaf
    entity leaf
  end

  sort LowA
    provides Low[T = Leaf]
    operation low(x: Leaf) -> Int64 = 1
  end

  sort HighW
    provides High[T = Leaf]
    operation high(x: Leaf) -> Int64 = 2
  end
end
"#;

/// The standard library and `lib` in one call — every provision of the KB checked by
/// that load, and nothing sealed by the test.
fn loaded(lib: &str, options: LoadOptions) -> KnowledgeBase {
    recipe_load(&[lib], None, options, LoadRecipe::OneShot, |_| {})
        .unwrap_or_else(|e| panic!("the library loads: {:?}", rendered_load_errors(e)))
        .0
}

/// [`loaded`], and that load SEALED whole.
fn sealed_library(lib: &str) -> KnowledgeBase {
    let mut kb = loaded(lib, LoadOptions::default());
    load::seal_declarations(&mut kb);
    kb
}

/// How many provision rows the KB holds.
fn provisions(kb: &KnowledgeBase) -> usize {
    let relation = kb
        .try_resolve_symbol("anthill.reflect.SortProvidesInfo")
        .expect("the provision relation is declared");
    kb.rules_by_functor(relation).len()
}

/// `program` as a later load into `kb`: its verdict, and how many provision rows the
/// check read for it.
fn later_load(kb: &mut KnowledgeBase, program: &str) -> (Result<(), Vec<String>>, usize) {
    let before = provisions_checked_by_this_thread();
    let verdict = load_in_a_later_call(kb, program, LoadOptions::default())
        .map(|_| ())
        .map_err(rendered_load_errors);
    (verdict, provisions_checked_by_this_thread() - before)
}

/// `program` loaded clean after the sealed library: `(rows the check read, rows the KB
/// held before the load, rows it holds after)`.
fn read_by_a_clean_later_load(program: &str) -> (usize, usize, usize) {
    let mut kb = sealed_library(LIB);
    let before = provisions(&kb);
    let (verdict, read) = later_load(&mut kb, program);
    if let Err(errors) = verdict {
        panic!("the program loads after the sealed library; got {errors:?}");
    }
    (read, before, provisions(&kb))
}

// ── What a later load reads ──────────────────────────────────────────

/// A type of the program's own, providing both library specs at itself, and an
/// operation.
const A_PROGRAM_OF_ITS_OWN_TYPE: &str = r#"
namespace test.a3prog
  import anthill.prelude.{Int64}
  import test.a3lib.{Low, High}

  sort Twig
    entity twig
    provides Low[T = Twig]
    operation low(x: Twig) -> Int64 = 5
    provides High[T = Twig]
    operation high(x: Twig) -> Int64 = 6
  end

  operation seven() -> Int64 = 7
end
"#;

/// THE CHANGE: a later load reads the provisions asserted since the seal — the
/// program's written two and the ones derived for its type — and none of the library's.
/// Each exactly once: the count is the rows the load added.
#[test]
fn a_later_load_reads_the_provisions_it_brought() {
    let (read, before, after) = read_by_a_clean_later_load(A_PROGRAM_OF_ITS_OWN_TYPE);
    assert!(before > 400, "the standard library's provisions are in the KB: {before}");
    assert!(after - before >= 2, "the program wrote two provisions: {before} -> {after}");
    assert_eq!(
        read,
        after - before,
        "the check reads the {} rows asserted since the seal, of {after}",
        after - before
    );
}

const A_SPEC_THAT_CONVERTS_TO_A_SEALED_ONE: &str = r#"
namespace test.a3prog
  import anthill.prelude.{Int64}
  import test.a3lib.{Low}

  sort Finer
    sort T = ?
    provides Low[T = T]
    operation fine(x: T) -> Int64
  end
end
"#;

/// A CONVERSION is no candidate at any goal — `Finer provides Low[T = T]` says a `Finer`
/// dictionary yields a `Low` one, at no type — and is a chain entry of its own spec
/// alone. So a spec of the program's that converts to a library one is read with the
/// program's rows, though its one binding is a parameter and names no type at all.
#[test]
fn a_conversion_to_a_sealed_spec_is_read_with_the_programs_rows() {
    let (read, before, after) = read_by_a_clean_later_load(A_SPEC_THAT_CONVERTS_TO_A_SEALED_ONE);
    assert!(after > before, "the conversion is a provision row: {before} -> {after}");
    assert_eq!(read, after - before, "the rows asserted since the seal, of {after}");
}

/// NOTHING SEALED, NOTHING SKIPPED: the same program after the same library, no seal
/// taken, is checked with every provision of the KB — a plain sequence of loads.
#[test]
fn nothing_sealed_nothing_skipped() {
    let mut kb = crate::common::load_unsealed(&[LIB]);
    assert_eq!(kb.sealed_census(), (0, 0, 0), "the fixture: nothing is sealed");
    let (verdict, read) = later_load(&mut kb, A_PROGRAM_OF_ITS_OWN_TYPE);
    assert_eq!(verdict, Ok(()));
    assert_eq!(read, provisions(&kb), "every provision of the KB, each once");
}

/// A seal of ALL of a load's files holds its provisions whichever door took it. The
/// one-call recipe seals "the first files of the load" (`seal_declarations_of`), and
/// given the standard library alone those are all of them — which is how the suites'
/// shared base is built, so this is the row for what every test on it reads.
#[test]
fn a_seal_of_all_of_a_loads_files_holds_its_provisions() {
    let mut kb = recipe_load(&[], None, LoadOptions::default(), LoadRecipe::OneShot, |_| {})
        .unwrap_or_else(|e| panic!("the standard library loads: {:?}", rendered_load_errors(e)))
        .0;
    let before = provisions(&kb);
    let (verdict, read) = later_load(&mut kb, A_PROGRAM_OF_ITS_OWN_TYPE_ELSEWHERE);
    assert_eq!(verdict, Ok(()));
    let after = provisions(&kb);
    assert!(after > before, "the program brought provisions: {before} -> {after}");
    assert_eq!(read, after - before, "the rows asserted since the seal, of {after}");
}

/// A seal of SOME of a load's files holds no provision: the rows of the files it does
/// not seal are below its slot count too, and their goals name types no seal holds. The
/// one-call recipe seals the standard library's part of a load that has a program in it
/// that way.
#[test]
fn a_seal_of_a_loads_first_files_holds_no_provision() {
    let mut kb = loaded(LIB, LoadOptions::default());
    assert!(
        kb.sealed_census().0 > 0,
        "the recipe sealed the standard library's declarations"
    );
    let (verdict, read) = later_load(&mut kb, A_PROGRAM_OF_ITS_OWN_TYPE);
    assert_eq!(verdict, Ok(()));
    assert_eq!(read, provisions(&kb));
}

/// A load that stops before its typer has checked no provision, and a seal of it tells
/// no later load that it has: the next one reads every row.
#[test]
fn a_load_sealed_before_its_check_ran_is_checked_by_the_next() {
    let mut kb = loaded(
        LIB,
        LoadOptions {
            run_typer: false,
            ..Default::default()
        },
    );
    load::seal_declarations(&mut kb);
    let (verdict, read) = later_load(&mut kb, A_PROGRAM_OF_ITS_OWN_TYPE);
    assert_eq!(verdict, Ok(()));
    assert_eq!(read, provisions(&kb), "every provision of the KB, each once");
}

const A_COMPOSITE_THAT_REACHES_A_FLOAT: &str = r#"
namespace test.a3prog
  import anthill.prelude.{Float}

  sort Reading
    entity reading(v: Float)
  end
end
"#;

/// The `NonEq` provision `eq_derive::run` derives for a composite that reaches a `Float`
/// is asserted BELOW the check. The load that derives it checks it now; before, the
/// first load to ask whether it holds was the next one, and none did when none came —
/// the standard library's own eight were checked by every test's load and by no
/// one-call load. In one call over everything each row of the KB is read once.
#[test]
fn a_derived_noneq_is_checked_by_the_load_that_derives_it() {
    let before = provisions_checked_by_this_thread();
    let kb = loaded(A_COMPOSITE_THAT_REACHES_A_FLOAT, LoadOptions::default());
    let read = provisions_checked_by_this_thread() - before;
    let noneq = kb.resolve_symbol("anthill.prelude.NonEq");
    let reading = kb.resolve_symbol("test.a3prog.Reading");
    assert!(kb.sort_provides(reading, noneq), "`Reading` has its derived `NonEq`");
    assert_eq!(read, provisions(&kb), "every provision of the KB, the derived ones too");
}

// ── What makes a later load read every provision ─────────────────────

/// Loads `program` after the sealed library and asserts the check read EVERY provision
/// the KB held when it ran — the held ones with the rest. Returns the load's verdict.
fn reads_every_provision(program: &str) -> Result<(), Vec<String>> {
    let mut kb = sealed_library(LIB);
    let before = provisions(&kb);
    let (verdict, read) = later_load(&mut kb, program);
    assert!(
        read >= before,
        "the check reads the {before} provisions the seal holds as well; it read {read} \
         (verdict: {verdict:?})"
    );
    verdict
}

const A_SECOND_WITNESS_OF_A_SEALED_SPEC_FOR_A_SEALED_TYPE: &str = r#"
namespace test.a3prog
  import anthill.prelude.{Int64}
  import test.a3lib.{Low, Leaf}

  sort LowB
    provides Low[T = Leaf]
    operation low(x: Leaf) -> Int64 = 9
  end
end
"#;

/// WHO ANSWERS A GOAL. `HighW`'s contract, `Low[T = Leaf]`, had one answer in the
/// library; a second witness makes it a tie, which is the LIBRARY provision's refusal.
/// One call refuses `HighW`; two calls refuse it too, because the later provision is at
/// a type the seal holds and the check reads every row.
#[test]
fn a_second_answer_for_a_sealed_goal_is_refused_as_in_one_call() {
    let tie = |errors: &[String]| {
        errors.iter().any(|e| {
            e.contains("'test.a3lib.HighW' provides 'test.a3lib.High'")
                && e.contains("test.a3lib.LowA")
                && e.contains("test.a3prog.LowB")
        })
    };
    let one = recipe_load(
        &[LIB, A_SECOND_WITNESS_OF_A_SEALED_SPEC_FOR_A_SEALED_TYPE],
        None,
        LoadOptions::default(),
        LoadRecipe::OneShot,
        |_| {},
    )
    .map(|_| ())
    .map_err(rendered_load_errors)
    .expect_err("one call refuses the tie");
    assert!(tie(&one), "one call names the provision whose contract ties; got {one:?}");

    let two = reads_every_provision(A_SECOND_WITNESS_OF_A_SEALED_SPEC_FOR_A_SEALED_TYPE)
        .expect_err("two calls refuse the tie");
    assert!(tie(&two), "two calls name it too; got {two:?}");
}

const A_REQUIRES_WRITTEN_INTO_A_SEALED_SPEC: &str = r#"
namespace test.a3prog
  import anthill.prelude.{Int64}

  sort Marker
    sort T = ?
    operation mark(x: T) -> Int64
  end
end

namespace test.a3lib.Low
  requires test.a3prog.Marker[T = T]
end
"#;

const AN_INNOCENT_PROGRAM: &str = r#"
namespace test.a3later
  import anthill.prelude.{Int64}
  operation eight() -> Int64 = 8
end
"#;

/// THE SPEC'S `requires`. A `requires` written into a sealed spec is refused where it is
/// written, and the fact is asserted all the same — so every provider of that spec now
/// breaks its contract, and a refused load does not unwind. The load AFTER it, of a file
/// that does nothing wrong, is refused by this check and by nothing else: it reads the
/// KB, finds the `requires`, and reads every row.
#[test]
fn a_requires_written_into_a_sealed_sort_refuses_the_next_load_too() {
    let unmet = |errors: &[String]| {
        errors.iter().any(|e| {
            e.contains("'test.a3lib.LowA' provides 'test.a3lib.Low'")
                && e.contains("test.a3prog.Marker")
        })
    };
    let mut kb = sealed_library(LIB);
    let before = provisions(&kb);
    let (first, read) = later_load(&mut kb, A_REQUIRES_WRITTEN_INTO_A_SEALED_SPEC);
    let first = first.expect_err("the load that writes the `requires` is refused");
    assert!(
        first.iter().any(|e| e.contains("`requires` is not allowed in a secondary entry")),
        "refused where it is written; got {first:?}"
    );
    assert!(read >= before, "and every provision is read: {read} of {before}");
    assert!(unmet(&first), "so the library's provider is refused too; got {first:?}");

    let (next, read) = later_load(&mut kb, AN_INNOCENT_PROGRAM);
    assert!(read >= before, "the next load reads every provision too: {read} of {before}");
    let next = next.expect_err("the KB a refused load left is refused again");
    assert!(unmet(&next), "by the provider's unmet contract; got {next:?}");
}

/// A sort with no type parameter, a sort that REFINES it, and a provision whose contract
/// reaches the refining sort's own provision: `HighN`'s `Low[T = Narrow]` is answered by
/// `Narrow`, whose `requires Boom` asks for no dictionary while `Boom` has no parameter.
const LIB_WITH_A_REFINEMENT: &str = r#"
namespace test.a3ref
  import anthill.prelude.{Int64}

  sort Low
    sort T = ?
    operation low(x: T) -> Int64
  end

  sort High
    sort T = ?
    requires Low[T = T]
    operation high(x: T) -> Int64
  end

  sort Boom
    entity boom
  end

  sort Narrow
    requires Boom
    entity narrow
    provides Low[T = Narrow]
    operation low(x: Narrow) -> Int64 = 1
  end

  sort HighN
    provides High[T = Narrow]
    operation high(x: Narrow) -> Int64 = 2
  end
end
"#;

const A_TYPE_PARAMETER_WRITTEN_INTO_A_SEALED_SORT: &str = r#"
namespace test.a3ref.Boom
  sort U = ?
end
"#;

/// A TYPE PARAMETER OF A REQUIRED SORT (found by /code-review). A `requires` naming a
/// sort with no type parameter is a refinement; give the sort one and the same clause is
/// a demand for a dictionary nothing provides. A binder in a secondary entry is refused
/// where it is written, and the parameter is registered all the same — so, as with the
/// `requires` above, the load AFTER it is refused by this check and by nothing else. It
/// writes to none of the three relations: the check finds it in the symbol table.
#[test]
fn a_type_parameter_written_into_a_sealed_sort_refuses_the_next_load_too() {
    let unmet = |errors: &[String]| {
        errors.iter().any(|e| {
            e.contains("'test.a3ref.HighN' provides 'test.a3ref.High'") && e.contains("test.a3ref.Boom")
        })
    };
    let mut kb = sealed_library(LIB_WITH_A_REFINEMENT);
    let before = provisions(&kb);
    let (first, read) = later_load(&mut kb, A_TYPE_PARAMETER_WRITTEN_INTO_A_SEALED_SORT);
    let first = first.expect_err("a binder in a secondary entry is refused");
    assert!(read >= before, "every provision is read: {read} of {before}");
    assert!(unmet(&first), "and the library's provision is refused too; got {first:?}");

    let (next, read) = later_load(&mut kb, AN_INNOCENT_PROGRAM);
    assert!(read >= before, "the next load reads every provision too: {read} of {before}");
    let next = next.expect_err("the KB a refused load left is refused again");
    assert!(unmet(&next), "by the provision whose contract no longer holds; got {next:?}");
}

const A_PROVISION_WRITTEN_INTO_A_SEALED_SORT: &str = r#"
namespace test.a3prog
  import anthill.prelude.{Int64}

  sort Mine
    sort T = ?
    operation mine(x: T) -> Int64
  end
end

namespace test.a3lib.Leaf
  import anthill.prelude.{Int64}
  import test.a3prog.{Mine}
  provides Mine[T = Leaf]
  operation mine(x: Leaf) -> Int64 = 4
end
"#;

/// AN EARLIER SORT'S NEW PROVISION — here of a spec of the program's own, which loads.
/// The provider was there before the seal: its provisions are what its own goals are
/// answered by first, and an edge a goal's type is matched through. Every row is read.
#[test]
fn a_provision_written_into_a_sealed_sort_reads_every_provision() {
    assert_eq!(reads_every_provision(A_PROVISION_WRITTEN_INTO_A_SEALED_SORT), Ok(()));
}

const A_GENERIC_PROVISION_OF_A_SEALED_SPEC: &str = r#"
namespace test.a3prog
  import anthill.prelude.{Int64}
  import test.a3lib.{Low}

  sort AnyLow
    sort E = ?
    provides Low[T = E]
    operation low(x: E) -> Int64 = 0
  end
end
"#;

/// A PROVISION AT A PARAMETER matches every goal of its spec, the library's among them.
/// It loads — `LowA`, at the type itself, stays the more specific answer for the
/// library's goal — and the check read every row to say so.
#[test]
fn a_generic_provision_of_a_sealed_spec_reads_every_provision() {
    assert_eq!(reads_every_provision(A_GENERIC_PROVISION_OF_A_SEALED_SPEC), Ok(()));
}

const A_PROVISION_AT_AN_ALIAS_OF_A_SEALED_TYPE: &str = r#"
namespace test.a3prog
  import anthill.prelude.{Int64}
  import test.a3lib.{Low, Leaf}

  sort Blade = Leaf

  sort LowC
    provides Low[T = Blade]
    operation low(x: Blade) -> Int64 = 3
  end
end
"#;

/// A NAME OF THE PROGRAM'S OWN FOR A SEALED TYPE is that type to the search, so a
/// provision at it is a second answer for the library's goal — read as one whichever
/// way the head is carried, and refused as the tie it is: `HighW`'s contract, between
/// `LowA` and `LowC`. (The typer's sealed-dispatch refusal names the same provision;
/// this row is about the check's.)
#[test]
fn a_provision_at_an_alias_of_a_sealed_type_reads_every_provision() {
    let errors = reads_every_provision(A_PROVISION_AT_AN_ALIAS_OF_A_SEALED_TYPE)
        .expect_err("a second answer for `Low[T = Leaf]`");
    assert!(
        errors.iter().any(|e| {
            e.contains("'test.a3lib.HighW' provides 'test.a3lib.High'")
                && e.contains("test.a3lib.LowA")
                && e.contains("test.a3prog.LowC")
        }),
        "the library provision whose contract ties is named; got {errors:?}"
    );
}

const A_PROVISION_AT_A_SPEC_A_SEALED_TYPE_PROVIDES: &str = r#"
namespace test.a3prog
  import anthill.prelude.{Int64}
  import test.a3lib.{Low}

  sort Shape
    sort T = ?
    operation area(x: T) -> Int64
  end

  sort Square
    entity square
    provides Shape[T = Square]
    operation area(x: Square) -> Int64 = 4
  end

  sort LowOfShapes
    provides Low[T = Shape]
    operation low(x: Shape) -> Int64 = 2
  end
end
"#;

/// A TYPE OF THE PROGRAM'S OWN THAT SOMETHING PROVIDES is not "nothing but itself": a
/// goal's type is matched against a head through the provisions of that head, so a
/// provision at a spec is a candidate wherever a provider of the spec is asked for.
/// Here nothing of the library's provides `Shape`, and the program loads.
#[test]
fn a_provision_at_a_spec_a_sealed_type_provides_reads_every_provision() {
    assert_eq!(reads_every_provision(A_PROVISION_AT_A_SPEC_A_SEALED_TYPE_PROVIDES), Ok(()));
}

const A_CONDITION_ON_A_SEALED_SORTS_PROVISION: &str = r#"
namespace test.a3prog
  import anthill.prelude.{Int64}

  sort Mine
    sort T = ?
    operation mine(x: T) -> Int64
  end

  sort Other
    sort T = ?
    operation other(x: T) -> Int64
  end
end

namespace test.a3lib.Leaf
  import anthill.prelude.{Int64}
  import test.a3prog.{Mine, Other}
  provides Mine[T = Leaf] :- Other[T = Leaf]
  operation mine(x: Leaf) -> Int64 = 4
end
"#;

/// A PROVISION'S CLAUSES. A condition written since the seal for a provider that was
/// there before it is a clause of that provider's provision. Every row is read, and the
/// program — a spec of its own, provided for a library sort under a condition — loads.
#[test]
fn a_condition_written_for_a_sealed_sort_reads_every_provision() {
    assert_eq!(reads_every_provision(A_CONDITION_ON_A_SEALED_SORTS_PROVISION), Ok(()));
}

// ── A refused provision ──────────────────────────────────────────────

const A_PROVISION_THAT_BREAKS_ITS_CONTRACT: &str = r#"
namespace test.a3prog
  import anthill.prelude.{Int64}
  import test.a3lib.{High}

  sort Twig
    entity twig
    provides High[T = Twig]
    operation high(x: Twig) -> Int64 = 6
  end
end
"#;

/// THE CHECK READS THE KB, NOT THE LOAD. A provision of the program's own that breaks
/// its contract is refused, and stays in the KB; the load after it reads it again —
/// with the rest asserted since the seal, and none of the library's — and is refused
/// by it. A check that read only what one load brought would load clean over it.
#[test]
fn a_refused_provision_is_refused_again_by_the_next_load() {
    let unmet = |errors: &[String]| {
        errors.iter().any(|e| {
            e.contains("'test.a3prog.Twig' provides 'test.a3lib.High'") && e.contains("test.a3lib.Low")
        })
    };
    let mut kb = sealed_library(LIB);
    let before = provisions(&kb);
    let (first, _) = later_load(&mut kb, A_PROVISION_THAT_BREAKS_ITS_CONTRACT);
    let first = first.expect_err("`Twig` provides `High` and no `Low`");
    assert!(unmet(&first), "got {first:?}");

    let after = provisions(&kb);
    let (next, read) = later_load(&mut kb, AN_INNOCENT_PROGRAM);
    let next = next.expect_err("the refused provision is still in the KB");
    assert!(unmet(&next), "got {next:?}");
    assert_eq!(
        read,
        provisions(&kb) - before,
        "the rows asserted since the seal ({before} held, {after} after the refused load), \
         and none the seal holds"
    );
}

// ── The oracle ───────────────────────────────────────────────────────

/// THE ORACLE RUNS WHEN IT IS ASKED FOR, AND ONLY THEN — the control of the instrument,
/// in every run. "The oracle run was clean" is evidence only if the switch took: a
/// variable misspelt in a command, or in the reader, leaves a run that judges nothing
/// and is green. So a load is made and the runs of the check the oracle judged on this
/// thread are counted: some under `ANTHILL_PROVISION_ORACLE=1`, none without it. What
/// was OBSERVED goes into the run's log, so a reader of a log sees which run it is.
///
/// The variable is read HERE and spelled out, not through the library's reader: the
/// row is a control on that reader.
///
/// A NARROWED run is what the oracle compares, and what is counted: a run that read
/// every row has nothing to be compared with. So the load is one that IS narrowed
/// whatever recipe the run is under — the standard library alone, sealed as the shared
/// base is, and then a program — and the row FAILS under the switch if narrowing has
/// stopped there, which an oracle run that compared nothing would otherwise pass over
/// (/code-review: the first cut counted every run, and said ON beside a recipe with no
/// later load).
#[test]
fn the_oracle_runs_when_it_is_asked_for() {
    use std::io::Write;
    let asked = std::env::var("ANTHILL_PROVISION_ORACLE").is_ok_and(|v| v == "1");
    let mut kb = recipe_load(&[], None, LoadOptions::default(), LoadRecipe::OneShot, |_| {})
        .unwrap_or_else(|e| panic!("the standard library loads: {:?}", rendered_load_errors(e)))
        .0;
    let before = provision_oracle_runs_by_this_thread();
    let (verdict, _) = later_load(&mut kb, A_PROGRAM_OF_ITS_OWN_TYPE_ELSEWHERE);
    assert_eq!(verdict, Ok(()));
    let judged = provision_oracle_runs_by_this_thread() - before;
    // To the handle directly and in one write: libtest captures `eprintln!` of a
    // passing test, and this line is for the run's log.
    let line = format!(
        "provision oracle OBSERVED by {}: {} ({judged} narrowed runs of the check compared \
         with a full one in one later load)\n",
        module_path!(),
        if judged > 0 { "ON" } else { "off" },
    );
    let _ = std::io::stderr().write_all(line.as_bytes());
    assert_eq!(
        judged > 0,
        asked,
        "ANTHILL_PROVISION_ORACLE asked for: {asked}; narrowed runs of the provision \
         check the oracle compared with a full one in a later load on this thread: {judged}"
    );
}

/// A program that needs no library but the standard one.
const A_PROGRAM_OF_ITS_OWN_TYPE_ELSEWHERE: &str = r#"
namespace test.a3own
  import anthill.prelude.{Int64}

  sort Spec
    sort T = ?
    operation one(x: T) -> Int64
  end

  sort Twig
    entity twig
    provides Spec[T = Twig]
    operation one(x: Twig) -> Int64 = 1
  end
end
"#;

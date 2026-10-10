//! WI-20261009-4ZRTG — THE LIBRARY IS SEALED: a file loaded after the standard library
//! may not declare again what the library declared, as it may not when the two go to
//! the loader in one call.
//!
//! The loader's declared-once ledgers are per load, on purpose (a source may be
//! presented again), so a LATER load's declaration of a library name was not seen as a
//! second one. Measured before this ticket, the stdlib and one user file under each
//! recipe by name: redeclaring `anthill.prelude.Option.isEmpty` and reopening
//! `enum Trust` were REFUSED in one call and LOADED CLEAN in two — the first replacing
//! the body every library caller reaches — and declaring `sort Option` again PANICKED
//! the loader in one call and loaded clean in two.
//!
//! WHAT FAILS WHEN (each measured by making the change and running this file):
//!
//! * `load::seal_declarations_where` made to seal nothing: ten rows FAIL — the three
//!   `*_is_refused_as_a_later_load`, `the_default_recipe_refuses_…`, `a_later_load_
//!   into_a_kb_of_any_recipe_…`, the two `…_presented_again_…` rows, `another_text_
//!   at_the_same_position_…`, `sealing_twice_…` and `a_type_declared_twice_by_the_
//!   later_load_…` — each file loads clean.
//!   The one-call halves of those rows pass either way BY DESIGN: they are the
//!   one-call rule the seal carries across, and the control that the fixture is what
//!   it says.
//! * the recipe's one-shot arm made not to seal: `a_later_load_into_a_kb_of_any_
//!   recipe_…` FAILS under `OneShot`, and `the_default_recipe_refuses_…` and `a_sealed_
//!   librarys_own_files_presented_again_…` with it — the shared base is built by that
//!   arm.
//! * the seal made to append a site it already holds: `sealing_twice_seals_once`
//!   FAILS — three declarations are counted.
//! * the scan made to keep both refusals of one type: `a_type_declared_twice_by_the_
//!   later_load_is_refused_once` FAILS under `TwoStep`.
//! * `derive_sort_domains` made to queue a job for each declaration of a sort again:
//!   both `…_does_not_panic` rows FAIL, by panicking.
//! * `register_specialization_witnesses` made to take derived provisions again:
//!   `a_later_load_registers_the_proof_records_one_call_registers` FAILS — 15 more.
//! * `an_unsealed_earlier_load_is_not_a_library`, `an_unsealed_kb_may_be_presented_
//!   its_files_again` and the two `*_loads_under_both` rows pass either way BY DESIGN:
//!   they say what the seal does NOT reach.
//!
//! BEHIND A SEAL THERE IS NO PRESENTING AGAIN (user, 2026-10-10). The first cut let the
//! same text at the same position through as "the same declaration". It is not: the
//! loader does not skip it, it loads it again, and a KB then holds two `OperationInfo`
//! rows for one operation. So the sealed source itself is refused like any other.

use anthill_core::kb::load::{self, LoadOptions, NullResolver};
use anthill_core::kb::KnowledgeBase;

use crate::common::rendered_load_errors as rendered;
use crate::common::{recipe_load, LoadRecipe};

/// A second declaration of an operation the library declares, with another body.
const AN_OPERATION_AGAIN: &str = "namespace anthill.prelude.Option\n  operation isEmpty(o: Self) -> Bool = true\nend\n";
/// A second declaration of a library enum, with a variant of its own.
const AN_ENUM_AGAIN: &str = "namespace anthill.prelude.Meta\n  enum Trust {\n    entity wild_guess\n  }\nend\n";
/// A second declaration of a library sort.
const A_SORT_AGAIN: &str = "namespace anthill.prelude\n  sort Option\n    entity nothing_at_all\n  end\nend\n";
/// NOT a second declaration: a new operation written into a library sort's scope.
const AN_OPERATION_ADDED: &str = "namespace anthill.prelude.Option\n  operation brandNew4zrtg(o: Self) -> Bool = true\nend\n";
/// NOT a second declaration: a sort of the program's own.
const A_SORT_OF_ITS_OWN: &str = "namespace test.w4zrtg\n  sort Fine\n    entity fine(n: Int64)\n  end\nend\n";

fn verdict(src: &str, recipe: LoadRecipe) -> Result<(), Vec<String>> {
    recipe_load(&[src], None, LoadOptions::default(), recipe, |_| {})
        .map(|_| ())
        .map_err(rendered)
}

fn refusal(src: &str, recipe: LoadRecipe) -> Vec<String> {
    verdict(src, recipe).expect_err("the file declares a library name again and must be refused")
}

#[test]
fn an_operation_declared_again_is_refused_as_a_later_load() {
    for recipe in [LoadRecipe::OneShot, LoadRecipe::TwoStep] {
        let errors = refusal(AN_OPERATION_AGAIN, recipe);
        assert!(
            errors.iter().any(|e| e.contains(
                "operation 'anthill.prelude.Option.isEmpty' is declared more than once"
            ) && e.contains("2 declarations")),
            "{recipe:?}: the refusal counts both declarations, the library's and the \
             file's; got {errors:?}"
        );
    }
}

#[test]
fn an_enum_declared_again_is_refused_as_a_later_load() {
    for recipe in [LoadRecipe::OneShot, LoadRecipe::TwoStep] {
        let errors = refusal(AN_ENUM_AGAIN, recipe);
        assert!(
            errors
                .iter()
                .any(|e| e.contains("type 'Trust' is declared more than once")
                    && e.contains("anthill.prelude.Meta")),
            "{recipe:?}: R1's refusal, naming the type and its scope; got {errors:?}"
        );
    }
}

#[test]
fn a_sort_declared_again_is_refused_as_a_later_load() {
    let errors = refusal(A_SORT_AGAIN, LoadRecipe::TwoStep);
    assert!(
        errors
            .iter()
            .any(|e| e.contains("type 'Option' is declared more than once")),
        "got {errors:?}"
    );
}

/// The same file in ONE call: refused by R1, where it used to take the loader down in
/// a later pass (`fill_derive`), which goes on after R1 to collect the other errors.
#[test]
fn a_sort_declared_again_is_refused_in_one_call_and_does_not_panic() {
    let errors = refusal(A_SORT_AGAIN, LoadRecipe::OneShot);
    assert!(
        errors
            .iter()
            .any(|e| e.contains("type 'Option' is declared more than once")),
        "got {errors:?}"
    );
}

/// The same panic by another road, within ONE file and with no library sort in it: a
/// parameterised sort declared twice, and a third sort holding it. The second
/// declaration's (empty) parameter list met conditions drawn over the first's.
#[test]
fn a_sort_declared_twice_and_held_by_another_is_refused_and_does_not_panic() {
    const TWICE_AND_HELD: &str = "namespace test.w4zrtg.twice
  sort Pair
    sort A = ?
    entity pair(a: A)
  end
  sort Pair
    entity unit2
  end
  sort Holder
    sort T = ?
    entity hold(p: Pair[A = T])
  end
end
";
    for recipe in [LoadRecipe::OneShot, LoadRecipe::TwoStep] {
        let errors = refusal(TWICE_AND_HELD, recipe);
        assert!(
            errors
                .iter()
                .any(|e| e.contains("type 'Pair' is declared more than once")),
            "{recipe:?}: got {errors:?}"
        );
    }
}

/// A sealed type the later load declares TWICE is one refusal naming all three sites,
/// as it is in one call — not R1's for the two and another across the seal.
#[test]
fn a_type_declared_twice_by_the_later_load_is_refused_once() {
    const TWICE: &str = "namespace anthill.prelude.Meta
  enum Trust {
    entity wild_guess
  }
  enum Trust {
    entity wilder_guess
  }
end
";
    for recipe in [LoadRecipe::OneShot, LoadRecipe::TwoStep] {
        let about_trust: Vec<String> = refusal(TWICE, recipe)
            .into_iter()
            .filter(|e| e.contains("type 'Trust' is declared more than once"))
            .collect();
        assert_eq!(about_trust.len(), 1, "{recipe:?}: got {about_trust:?}");
        assert_eq!(
            about_trust[0].matches("`enum` at").count(),
            3,
            "{recipe:?}: the library's declaration and the file's two; got {about_trust:?}"
        );
    }
}

#[test]
fn an_operation_added_to_a_library_scope_loads_under_both() {
    for recipe in [LoadRecipe::OneShot, LoadRecipe::TwoStep] {
        verdict(AN_OPERATION_ADDED, recipe)
            .unwrap_or_else(|e| panic!("{recipe:?}: a NEW name in a library scope is no redeclaration: {e:?}"));
    }
}

#[test]
fn a_sort_of_the_programs_own_loads_under_both() {
    for recipe in [LoadRecipe::OneShot, LoadRecipe::TwoStep] {
        verdict(A_SORT_OF_ITS_OWN, recipe).unwrap_or_else(|e| panic!("{recipe:?}: {e:?}"));
    }
}

/// BEHIND A SEAL, A SOURCE PRESENTED AGAIN IS A SECOND DECLARATION: the sealed
/// library's own files, handed to the loader again, are refused for what they declare.
#[test]
fn a_sealed_librarys_own_files_presented_again_are_refused() {
    let mut kb = crate::common::load_stdlib_kb();
    let errors = crate::common::present_all_again(&mut kb, &[])
        .map(|_| ())
        .map_err(rendered)
        .expect_err("the library is sealed, and these are its declarations again");
    assert!(
        errors.iter().any(|e| e.contains("is declared more than once")),
        "got {} errors, the first: {:?}",
        errors.len(),
        errors.first()
    );
}

/// A file of the test's own, sealed with the library by hand, for the two rows below.
const SEALED_BY_HAND: &str = "namespace test.w4zrtg.same\n  operation f(x: Int64) -> Int64 = 1\nend\n";

fn a_kb_with_that_file_sealed() -> KnowledgeBase {
    let mut kb = KnowledgeBase::new();
    let own = anthill_core::parse::parse(SEALED_BY_HAND).expect("parse");
    let mut files = crate::common::stdlib_parsed();
    files.push(&own);
    crate::common::expect_loaded(load::load_all(&mut kb, &files, &NullResolver));
    load::seal_declarations(&mut kb);
    kb
}

/// The same text, parsed again as a file re-read from disk is: refused. It is the same
/// SOURCE, and it would still be loaded a second time.
#[test]
fn the_same_source_presented_again_from_another_copy_is_refused() {
    let mut kb = a_kb_with_that_file_sealed();
    let again = String::from(SEALED_BY_HAND);
    let errors = crate::common::load_in_a_later_call(&mut kb, &again, LoadOptions::default())
        .map(|_| ())
        .map_err(rendered)
        .expect_err("the sealed file presented again");
    assert!(
        errors
            .iter()
            .any(|e| e.contains("operation 'test.w4zrtg.same.f' is declared more than once")),
        "got {errors:?}"
    );
}

/// And where nothing is sealed, a KB may be presented its files again, as it could
/// before: this is what the idempotent-across-loads suites do, on `load_unsealed`.
#[test]
fn an_unsealed_kb_may_be_presented_its_files_again() {
    let mut kb = crate::common::load_unsealed(&[SEALED_BY_HAND]);
    crate::common::expect_loaded(crate::common::present_all_again(&mut kb, &[SEALED_BY_HAND]));
}

/// ANOTHER text with its declaration at the same position is a second declaration:
/// the body differs by one character, so every span is the sealed file's.
#[test]
fn another_text_at_the_same_position_is_a_second_declaration() {
    let mut kb = a_kb_with_that_file_sealed();
    let other = SEALED_BY_HAND.replace("= 1", "= 2");
    assert_eq!(other.len(), SEALED_BY_HAND.len(), "the fixture keeps every position");
    let errors = crate::common::load_in_a_later_call(&mut kb, &other, LoadOptions::default())
        .map(|_| ())
        .map_err(rendered)
        .expect_err("another body for a sealed operation is a second declaration");
    assert!(
        errors
            .iter()
            .any(|e| e.contains("operation 'test.w4zrtg.same.f' is declared more than once")),
        "got {errors:?}"
    );
}

/// Sealing the same load twice seals it once: the refusal counts the library's
/// declaration and the file's, not the library's twice.
#[test]
fn sealing_twice_seals_once() {
    let mut kb = crate::common::load_stdlib_kb();
    load::seal_declarations(&mut kb);
    let errors = crate::common::load_in_a_later_call(&mut kb, AN_OPERATION_AGAIN, LoadOptions::default())
        .map(|_| ())
        .map_err(rendered)
        .expect_err("the library is sealed");
    assert!(
        errors.iter().any(|e| e.contains("(2 declarations)")),
        "got {errors:?}"
    );
}

/// THE LIBRARY IS SEALED UNDER EVERY RECIPE, AND ONLY THE LIBRARY: a later load into
/// the KB a recipe hands back may not declare a library operation again, and may
/// declare the test's own — the same whichever recipe built the KB, or a test with a
/// later load of its own would get one verdict from the gate and another from a
/// control run.
#[test]
fn a_later_load_into_a_kb_of_any_recipe_meets_the_sealed_library() {
    const OWN: &str = "namespace test.w4zrtg.own
  operation g(x: Int64) -> Int64 = 1
end
";
    const OWN_AGAIN: &str = "namespace test.w4zrtg.own
  operation g(x: Int64) -> Int64 = 22
end
";
    for recipe in [LoadRecipe::OneShot, LoadRecipe::TwoStep] {
        let (mut kb, _) = crate::common::expect_loaded(recipe_load(
            &[OWN],
            None,
            LoadOptions::default(),
            recipe,
            |_| {},
        ));
        let later = |kb: &mut KnowledgeBase, src: &str| {
            crate::common::load_in_a_later_call(kb, src, LoadOptions::default())
                .map(|_| ())
                .map_err(rendered)
        };
        later(&mut kb, OWN_AGAIN).unwrap_or_else(|e| {
            panic!("{recipe:?}: the test's own file is not sealed, so this is as it was: {e:?}")
        });
        let errors = later(&mut kb, AN_OPERATION_AGAIN)
            .expect_err("a library operation declared again by a later load");
        assert!(
            errors.iter().any(|e| e.contains("is declared more than once")),
            "{recipe:?}: got {errors:?}"
        );
    }
}

/// THE SEAL IS EXPLICIT (user, 2026-10-09): two plain `load_all` calls with no seal
/// between them behave as they did — the later one's operation is accepted. This is
/// the row that says what was NOT changed; the day a later load is refused whatever
/// came before it, it fails, and should.
#[test]
fn an_unsealed_earlier_load_is_not_a_library() {
    let mut kb = KnowledgeBase::new();
    let stdlib = crate::common::stdlib_parsed();
    crate::common::expect_loaded(load::load_all(&mut kb, &stdlib, &NullResolver));
    crate::common::expect_loaded(crate::common::load_in_a_later_call(
        &mut kb,
        AN_OPERATION_AGAIN,
        LoadOptions::default(),
    ));
}

/// And the default recipe — a copy of the shared base — is sealed too: a test's file
/// is judged as a user's is.
#[test]
fn the_default_recipe_refuses_a_library_operation_declared_again() {
    let errors = crate::common::load_errors_of(AN_OPERATION_AGAIN);
    assert!(
        errors
            .iter()
            .any(|e| e.contains("is declared more than once")),
        "got {errors:?}"
    );
}

/// The same cause, another pass: one that sweeps the WHOLE knowledge base in a later
/// load. A file loaded after the library leaves the proof records one call leaves —
/// none for the library's derived provisions, which only the later load could see, and
/// the file's OWN: its provider of a spec that carries a requirement gets its
/// specialization record under both, so an exclusion that dropped everything fails
/// here too.
#[test]
fn a_later_load_registers_the_proof_records_one_call_registers() {
    const A_PROVIDER: &str = r#"
namespace test.w4zrtg.records
  import anthill.prelude.{Eq, PartialEq}
  sort A
    sort T = ?
    requires anthill.prelude.Eq[T = T]
  end
  sort B
    provides PartialEq[T = B]
    provides Eq[T = B]
    provides A[T = B]
  end
end
"#;
    let records = |src: &str, recipe: LoadRecipe| {
        let (kb, _) = crate::common::expect_loaded(recipe_load(
            &[src],
            None,
            LoadOptions::default(),
            recipe,
            |_| {},
        ));
        let record = kb
            .try_resolve_symbol("anthill.realization.ProofRecord")
            .expect("the library declares ProofRecord");
        kb.rules_by_functor(record)
            .into_iter()
            .filter(|rid| kb.is_fact(*rid))
            .count()
    };
    let library_alone = records(A_SORT_OF_ITS_OWN, LoadRecipe::OneShot);
    assert!(library_alone > 0, "the library registers proof records of its own");
    assert_eq!(records(A_SORT_OF_ITS_OWN, LoadRecipe::TwoStep), library_alone);

    let with_a_provider = records(A_PROVIDER, LoadRecipe::OneShot);
    assert!(
        with_a_provider > library_alone,
        "the fixture has to register records of its own for this to read any: \
         {with_a_provider} against {library_alone}"
    );
    assert_eq!(records(A_PROVIDER, LoadRecipe::TwoStep), with_a_provider);
}

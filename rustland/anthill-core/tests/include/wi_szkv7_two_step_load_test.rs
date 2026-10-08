//! WI-20261006-SZKV7 — the two-step load recipe, and the CONTROL that a run under
//! `ANTHILL_TEST_TWO_STEP_LOAD=1` measured what its log says it measured.
//!
//! `common::recipe_load` hands the stdlib and a test's own files to the loader either in
//! one `load_all` or in two (`common::LoadRecipe`). A suite run under the switch that
//! reports "green" is only evidence if the switch took effect, so the recipe has to be
//! OBSERVABLE: a load reports the sorts IT defined (`LoadResult::defined_sorts`), and the
//! user's call under the two-step recipe defined the user's sorts and no stdlib one.
//!
//! WHAT FAILS WHEN (each measured by making the change and running this file):
//!
//! * `the_recipes_differ_in_which_call_defines_the_stdlib` and
//!   `a_two_step_kb_runs_a_program_over_the_stdlib` name the recipe EXPLICITLY, so they
//!   drive the two-step path in every gate. Both arms of `recipe_load` made the one-shot
//!   call: the first FAILS. The second passes either way BY DESIGN — it says the two-step
//!   KB is a working one, not which recipe built it.
//! * `the_switch_selects_the_recipe_the_helpers_run` is the control for a SWITCHED run.
//!   `try_load_kb_named_prepared_with` made to pass `LoadRecipe::OneShot` instead of
//!   reading the switch: it FAILS under `ANTHILL_TEST_TWO_STEP_LOAD=1`, and passes without
//!   the variable BY DESIGN — an ordinary gate has no switch to ignore. The name in
//!   `common`'s constant changed by one letter: it FAILS under the switch the same way,
//!   which is why the row spells the name out instead of importing it.
//!
//! WHAT NO ROW HERE CAN FAIL ON: the variable renamed in `scripts/test.sh` alone. Then
//! nothing sets the name this binary reads, every helper runs one-shot, and the control —
//! which sees no switch either — agrees. For that the control writes the recipe it
//! OBSERVED into the run's log, under the script's own `load:` line: the two are written
//! by different programs and a reader of the log sees them disagree.

use std::collections::BTreeSet;

use anthill_core::eval::{self, Interpreter};
use anthill_core::kb::load::{LoadOptions, LoadResult};
use anthill_core::kb::KnowledgeBase;

use crate::common::{recipe_control_load, recipe_load, LoadRecipe};

const USER_SORT: &str = "test.szkv7.Probe";
/// A sort the stdlib defines, and so one that only a load of the stdlib reports.
const STDLIB_SORT: &str = "anthill.prelude.List";

/// One sort, and an operation whose body runs stdlib code over a stdlib value.
const USER: &str = r#"
namespace test.szkv7
  import anthill.prelude.{Int64, List}

  sort Probe
    entity probe(n: Int64)
  end

  operation main() -> Int64 = List.length([10, 20, 30]) + 39
end
"#;

fn defined_sort_names(kb: &KnowledgeBase, result: &LoadResult) -> BTreeSet<String> {
    result
        .defined_sorts
        .iter()
        .map(|s| kb.qualified_name_of(*s).to_string())
        .collect()
}

fn load(recipe: LoadRecipe) -> (KnowledgeBase, LoadResult) {
    crate::common::expect_loaded(recipe_load(
        &[USER],
        None,
        LoadOptions::default(),
        recipe,
        |_| {},
    ))
}

fn assert_one_shot(names: &BTreeSet<String>) {
    assert!(
        names.contains(USER_SORT) && names.contains(STDLIB_SORT),
        "a one-shot load defines the user's sorts AND the stdlib's in its one call; \
         it reported {} sorts, `{USER_SORT}`: {}, `{STDLIB_SORT}`: {}",
        names.len(),
        names.contains(USER_SORT),
        names.contains(STDLIB_SORT),
    );
}

fn assert_two_step(names: &BTreeSet<String>) {
    assert_eq!(
        names,
        &BTreeSet::from([USER_SORT.to_string()]),
        "the user's call of a two-step load defines the user's sorts and nothing else"
    );
}

#[test]
fn the_recipes_differ_in_which_call_defines_the_stdlib() {
    let (kb, result) = load(LoadRecipe::OneShot);
    assert_one_shot(&defined_sort_names(&kb, &result));

    let (kb, result) = load(LoadRecipe::TwoStep);
    assert_two_step(&defined_sort_names(&kb, &result));
}

#[test]
fn a_two_step_kb_runs_a_program_over_the_stdlib() {
    for recipe in [LoadRecipe::OneShot, LoadRecipe::TwoStep] {
        let (kb, _) = load(recipe);
        let mut interp = Interpreter::new(kb);
        eval::builtins::register_standard_builtins(&mut interp)
            .expect("register standard eval builtins");
        match interp.call("test.szkv7.main", &[]) {
            Ok(eval::Value::Int(42)) => {}
            other => panic!("{recipe:?}: `main` did not run to 42: {other:?}"),
        }
    }
}

#[test]
fn the_switch_selects_the_recipe_the_helpers_run() {
    use std::io::Write;

    // Read HERE and spelled out, not through `LoadRecipe::from_env` or the constant it
    // reads: the row is a control on both, so it cannot take either's word — a renamed
    // constant leaves this name set and the helpers one-shot, and the row fails.
    let switched = std::env::var("ANTHILL_TEST_TWO_STEP_LOAD").is_ok_and(|v| v == "1");

    let (kb, result) = crate::common::expect_loaded(recipe_control_load(USER));
    let names = defined_sort_names(&kb, &result);

    // What the helpers RAN, read off the load and not off any variable. Written to the
    // handle directly because libtest captures `eprintln!` of a passing test and this
    // line is for the run's log (see the module doc).
    let observed = if names.contains(STDLIB_SORT) { "one shot" } else { "TWO-STEP" };
    let _ = writeln!(
        std::io::stderr(),
        "load recipe OBSERVED by {}: {observed}",
        module_path!()
    );

    if switched {
        assert_two_step(&names);
    } else {
        assert_one_shot(&names);
    }
}

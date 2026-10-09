//! WI-20261006-SZKV7 — the two-step load recipe, and the CONTROL that a run measured the
//! recipe its log says it measured. Since WI-059 there are three: the SHARED BASE (the
//! default — a copy of the stdlib loaded once per test binary), one shot
//! (`ANTHILL_TEST_FRESH_LOAD=1`) and two steps (`ANTHILL_TEST_TWO_STEP_LOAD=1`).
//!
//! `common::recipe_load` hands the stdlib and a test's own files to the loader either in
//! one `load_all` or in two (`common::LoadRecipe`). A suite run that reports "green" is
//! only evidence if the recipe it names took effect, so the recipe has to be OBSERVABLE,
//! by two readings: a load reports the sorts IT defined (`LoadResult::defined_sorts`) —
//! the user's call defined the stdlib's sorts too only in one shot — and the helpers
//! count the stdlib loads made on the calling thread, which is none on the shared base.
//!
//! WHAT FAILS WHEN (each measured by making the change and running this file):
//!
//! * `the_recipes_differ_in_which_call_defines_the_stdlib` and
//!   `a_two_step_kb_runs_a_program_over_the_stdlib` name the recipe EXPLICITLY, so they
//!   drive the two-step path in every gate. Both arms of `recipe_load` made the one-shot
//!   call: the first FAILS. The second passes either way BY DESIGN — it says the two-step
//!   KB is a working one, not which recipe built it.
//! * `the_switch_selects_the_recipe_the_helpers_run` is the control for EVERY run, the
//!   ordinary gate included — the default is a recipe to be observed like the others.
//!   Measured on the default (WI-059), each alone: `common::run_switched_recipe` made
//!   never to choose the shared base — it FAILS, observing one shot; `load_stdlib_kb`
//!   made to load for itself — it FAILS on the stdlib-alone reading; the base made
//!   per-thread (`SHARED_BASE` a `thread_local!`) — it FAILS on the second thread's
//!   reading, which the first two back-outs pass. Measured under
//!   `ANTHILL_TEST_TWO_STEP_LOAD=1` (WI-20261006-SZKV7): `run_switched_recipe` made to
//!   pass `LoadRecipe::OneShot` — it FAILS; the name in `common`'s constant changed by
//!   one letter — it FAILS the same way, which is why the row spells the names out
//!   instead of importing them.
//!
//! WHAT NO ROW HERE CAN FAIL ON: a variable renamed in `scripts/test.sh` alone. Then
//! nothing sets the name this binary reads, every helper runs the default, and the
//! control — which sees no switch either — agrees. For that the control writes the recipe it
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
    // Read HERE and spelled out, not through `common`'s read or the constants it reads:
    // the row is a control on both, so it cannot take either's word — a renamed
    // constant leaves these names set and the helpers on another recipe, and the row
    // fails.
    let set = |name: &str| std::env::var(name).is_ok_and(|v| v == "1");
    let asked = match (set("ANTHILL_TEST_FRESH_LOAD"), set("ANTHILL_TEST_TWO_STEP_LOAD")) {
        (false, false) => "SHARED BASE",
        (true, false) => "one shot",
        (false, true) => "TWO-STEP",
        (true, true) => panic!("both switches are set; `common` refuses that"),
    };
    // Have the shared base built before the count is read: whichever thread asks first
    // loads the stdlib for everybody, and that one load is not this row's.
    drop(crate::common::load_stdlib_kb());
    let loads_before = crate::common::stdlib_loads_by_this_thread();
    let (kb, result) = crate::common::expect_loaded(recipe_control_load(USER));
    let stdlib_loads = crate::common::stdlib_loads_by_this_thread() - loads_before;
    let names = defined_sort_names(&kb, &result);
    // What the helpers RAN, read off the load and not off any variable. Three recipes,
    // told apart by two readings: which call defined the stdlib's sorts separates one
    // shot from the other two; whether this thread loaded the stdlib AT ALL for the
    // load separates a fresh two-step from the shared base.
    let observed = match (names.contains(STDLIB_SORT), stdlib_loads) {
        (true, 1) => "one shot",
        (false, 1) => "TWO-STEP",
        (false, 0) => "SHARED BASE",
        other => panic!(
            "no recipe loads like this: (the stdlib's sorts in the call, stdlib loads on \
             this thread) = {other:?}"
        ),
    };
    // Written to the handle directly because libtest captures `eprintln!` of a passing
    // test and this line is for the run's log (see the module doc) — and in ONE write:
    // formatted piece by piece, another thread's `test … ok` landed in the middle of it.
    let line = format!("load recipe OBSERVED by {}: {observed}\n", module_path!());
    let _ = std::io::stderr().write_all(line.as_bytes());
    if observed == "one shot" {
        assert_one_shot(&names);
    } else {
        assert_two_step(&names);
    }
    assert_eq!(observed, asked, "the helpers ran a recipe the environment did not ask for");

    // And the stdlib ALONE: a copy of the base, or a load of its own.
    let loads_before = crate::common::stdlib_loads_by_this_thread();
    drop(crate::common::load_stdlib_kb());
    assert_eq!(
        crate::common::stdlib_loads_by_this_thread() - loads_before,
        usize::from(asked != "SHARED BASE"),
        "`load_stdlib_kb` under {asked}: a copy of the shared base loads nothing, and a \
         fresh recipe loads the stdlib once"
    );

    // ONE base for the binary, not one a thread: libtest runs each test on a thread of
    // its own, so a per-thread base would be a full load a test, plus a copy. A thread
    // that has loaded nothing yet takes a KB and still has loaded nothing.
    let on_another_thread = std::thread::spawn(|| {
        let (kb, result) = crate::common::expect_loaded(recipe_control_load(USER));
        let defined_the_stdlib = defined_sort_names(&kb, &result).contains(STDLIB_SORT);
        (crate::common::stdlib_loads_by_this_thread(), defined_the_stdlib)
    })
    .join()
    .expect("the second thread's load");
    if asked == "SHARED BASE" {
        assert_eq!(on_another_thread, (0, false), "a second thread built a base of its own");
        assert_eq!(crate::common::shared_base_builds(), 1, "the base is built once a process");
    } else {
        assert_eq!(on_another_thread.0, 1, "a fresh recipe loads the stdlib on every thread");
    }
}

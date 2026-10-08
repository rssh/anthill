//! WI-20261006-SZKV7, the first finding of the two-step run — a load checks the clauses
//! IT asserted, whichever load defined the sort they are written under.
//!
//! The typer's sort loop reaches a fact through its constructor's SORT and a rule through
//! its domain SORT, and a load hands it the sorts that load defined. One call over
//! everything, that is every clause. A LATER call's clause under an EARLIER call's sort
//! was under no sort in the list and was never checked: `fact box(n: "seven")` over a base
//! `box(n: Int64)` loaded clean, and so did a rule with contradictory variable types
//! written into the base's sort. The loader now hands the typer the clauses it asserted
//! beside the sorts it defined (`typing::Loaded`), and the typer takes nothing else.
//!
//! EVERY ROW HERE MAKES ITS SECOND CALL BY NAME, so the file measures the same thing
//! whatever `ANTHILL_TEST_TWO_STEP_LOAD` says — the subject is the second call, and a
//! helper that made one call or two by the switch would test it only on switched runs.
//!
//! WHAT FAILS WHEN (measured by making the change and running this file):
//!
//! * the loader handing the typer no clauses (`rules: 0..0`): the SIX rows that load a
//!   bad clause in a later call fail — the three `a_later_calls_…_is_…`,
//!   `a_fact_spelled_…`, `the_two_recipes_agree_…`, `kb_loaded_refuses_…`.
//!   `the_clauses_are_what_…` passes: it calls the typer itself.
//! * `check_late_clauses` returning at once: those six and the hand-driven row FAIL.
//! * its fact arm alone skipped: the four FACT rows and the hand-driven row fail; its
//!   rule arm alone skipped: the two RULE rows fail; the rule arm without its
//!   pattern-fragment call: `…_is_held_to_the_pattern_fragment` FAILS, and it alone.
//! * the fact arm not leaving the call's own constructors to the sort loop:
//!   `one_call_reports_the_fact_once` FAILS, and `a_refused_files_…` with it; the rule
//!   arm not leaving the call's own sorts to it: `one_call_reports_the_rule_once` FAILS.
//! * the rule arm taking a rule whose domain is no sort: TEN rows fail,
//!   `a_later_calls_namespace_level_rule_…` among them and in its ONE-call half — the
//!   stdlib itself stops loading, because in one call the pass then takes every
//!   namespace-level rule there is. That guard keeps one call's verdict what it was.
//! * the sorts of a file that failed to load left out of "the call's own":
//!   `a_refused_files_own_clauses_are_left_alone` FAILS.
//! * the two `…_loads` rows pass through all of these BY DESIGN: they are the control
//!   that the refusals are about the clause, not about writing one in a second call.

use anthill_core::eval::value::Value;
use anthill_core::eval::EvalError;
use anthill_core::kb::load::{self, LoadError, LoadOptions, NullResolver};
use anthill_core::kb::typing::type_check_sorts;
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

use crate::common::{expect_loaded, interp_for, load_kb_with, recipe_load, LoadRecipe};

/// The earlier load: one entity with a typed field, and a well-typed fact of it.
const BASE: &str = r#"
namespace test.ff.base
  sort Box
    entity box(n: Int64)
  end
  fact box(n: 1)
end
"#;

/// The later load: a fact of the BASE's entity whose field is not an `Int64`.
const ILL: &str = r#"
namespace test.ff.cand
  import test.ff.base.Box.{box}
  fact box(n: "seven")
end
"#;

/// Its control: the same fact, well typed.
const WELL: &str = r#"
namespace test.ff.cand
  import test.ff.base.Box.{box}
  fact box(n: 7)
end
"#;

/// The refusal, as every row below must see it: the field, what it declares, what it got.
fn assert_names_the_field(errors: &[String], why: &str) {
    assert!(
        errors
            .iter()
            .any(|e| e.contains("box.n") && e.contains("expected Int64") && e.contains("String")),
        "{why}: the refusal names the field, the declared type and the offender; got {errors:?}"
    );
}

fn rendered(errors: Vec<LoadError>) -> Vec<String> {
    errors.iter().map(|e| e.to_string()).collect()
}

/// `source` loaded into `kb` in a call of its own — the second call, by name.
fn load_in_a_later_call(
    kb: &mut KnowledgeBase,
    source: &str,
    options: LoadOptions,
) -> Result<load::LoadResult, Vec<LoadError>> {
    let parsed = parse::parse(source).expect("parse the later call's source");
    load::load_all_with(kb, &[&parsed], &NullResolver, options)
}

#[test]
fn a_later_calls_fact_over_an_earlier_calls_entity_is_field_checked() {
    let mut kb = load_kb_with(BASE);
    let errors = match load_in_a_later_call(&mut kb, ILL, LoadOptions::default()) {
        Err(errors) => rendered(errors),
        Ok(_) => panic!("`fact box(n: \"seven\")` over `box(n: Int64)` must not load"),
    };
    assert_names_the_field(&errors, "a second `load_all`");
}

#[test]
fn a_well_typed_fact_over_an_earlier_calls_entity_loads() {
    let mut kb = load_kb_with(BASE);
    expect_loaded(load_in_a_later_call(&mut kb, WELL, LoadOptions::default()));
    let box_sym = kb
        .try_resolve_symbol("test.ff.base.Box.box")
        .expect("the base's constructor");
    let facts = kb
        .rules_by_functor(box_sym)
        .into_iter()
        .filter(|rid| kb.is_fact(*rid))
        .count();
    assert_eq!(facts, 2, "the base's fact and the later call's are both there");
}

/// The same question through the recipe's two arms, over an entity the STDLIB declares —
/// the shape of `wi830_extent_binding_test::a_role_that_is_not_a_role_is_refused_at_load`,
/// which is what found this. Both recipes are named: the row's subject is that they agree.
#[test]
fn the_two_recipes_agree_on_a_fact_over_a_stdlib_entity() {
    const SRC: &str = r#"
namespace test.ff.std
  import anthill.persistence.{FileStore}
  fact FileStore(root: 7, convention: flat())
end
"#;
    let verdict = |recipe| match recipe_load(&[SRC], None, LoadOptions::default(), recipe, |_| {}) {
        Err(errors) => rendered(errors),
        Ok(_) => panic!("{recipe:?}: `root: 7` over `FileStore(root: String, ..)` must not load"),
    };
    let one_shot = verdict(LoadRecipe::OneShot);
    assert!(
        one_shot
            .iter()
            .any(|e| e.contains("FileStore.root") && e.contains("expected String")),
        "the one-shot refusal names the field and its declared type; got {one_shot:?}"
    );
    assert_eq!(
        verdict(LoadRecipe::TwoStep),
        one_shot,
        "loaded after the stdlib, the file gets the diagnostics it gets loaded with it"
    );
}

/// `KB.loaded` IS a later call — `load_all` on the live KB — and "does this candidate
/// load" is the whole of what a checker asks it.
#[test]
fn kb_loaded_refuses_an_ill_typed_fact_over_a_base_entity() {
    let mut interp = interp_for(BASE);
    let mut loaded = |source: &str| {
        let list = interp
            .build_list_value(vec![Value::Str(source.to_string())], &[])
            .expect("build List[String]");
        interp.call("anthill.reflect.KB.loaded", &[list])
    };

    let payload = match loaded(ILL) {
        Err(EvalError::Raised { payload }) => format!("{payload:?}"),
        other => panic!("a candidate that does not load is RAISED, as `load_failed`; got {other:?}"),
    };
    assert!(
        payload.contains("box.n") && payload.contains("expected Int64"),
        "the raised diagnostics are the field refusal, not some other one; got {payload}"
    );
    let accepted = loaded(WELL);
    assert!(
        accepted.is_ok(),
        "the well-typed candidate loads, so the refusal above was about the value: {accepted:?}"
    );
}

/// The typer's entry, driven by hand over a second call that stopped before it: the
/// call's CLAUSES are what reach the field, and its sorts alone do not.
#[test]
fn the_clauses_are_what_the_hand_driven_form_of_a_load_hands_the_typer() {
    let mut kb = load_kb_with(BASE);
    let untyped = LoadOptions {
        run_typer: false,
        ..Default::default()
    };
    let result = expect_loaded(load_in_a_later_call(&mut kb, ILL, untyped));
    assert!(
        !result.loaded_rules.is_empty(),
        "the later call asserted a clause, and its `LoadResult` says where"
    );

    // A `Loaded` comes from a `LoadResult` and from nowhere else, so "the sorts and no
    // clauses" has to be written out as the result it would have come from.
    let sorts_alone = load::LoadResult {
        defined_sorts: result.defined_sorts.clone(),
        ..Default::default()
    };
    let sorts_alone = rendered(type_check_sorts(&mut kb, sorts_alone.loaded()));
    assert!(
        !sorts_alone.iter().any(|e| e.contains("box.n")),
        "CONTROL: without the call's clauses nothing reaches `box.n` — which is the \
         defect, and why they are half of the work list; got {sorts_alone:?}"
    );
    let with_facts = rendered(type_check_sorts(&mut kb, result.loaded()));
    assert_names_the_field(&with_facts, "`type_check_sorts` over what the call added");
}

/// In ONE call the fact's constructor is declared by that call, so the sort loop already
/// checks it; the pass over the call's facts must not report it a second time. Read off
/// the typer and not off `load_all`, whose exit collapses identical diagnostics and would
/// hide a double report.
#[test]
fn one_call_reports_the_fact_once() {
    let untyped = LoadOptions {
        run_typer: false,
        ..Default::default()
    };
    let (mut kb, result) = expect_loaded(recipe_load(
        &[BASE, ILL],
        None,
        untyped,
        LoadRecipe::OneShot,
        |_| {},
    ));
    let errors = rendered(type_check_sorts(&mut kb, result.loaded()));
    let about_the_field: Vec<&String> = errors.iter().filter(|e| e.contains("box.n")).collect();
    assert_eq!(
        about_the_field.len(),
        1,
        "one ill-typed fact, one report; got {about_the_field:?}"
    );
}

/// `rule H :- true` is the other spelling of `fact H`, and the same bodyless clause. It is
/// not in `LoadResult::fact_rule_ids` — `load_fact` alone writes that list — which is why
/// the typer is handed the call's rule SLOTS and not that list (/code-review).
#[test]
fn a_fact_spelled_as_a_bodyless_rule_is_field_checked_too() {
    const RULE_SPELLED: &str = r#"
namespace test.ff.cand
  import test.ff.base.Box.{box}
  rule box(n: "seven") :- true
end
"#;
    let mut kb = load_kb_with(BASE);
    let errors = match load_in_a_later_call(&mut kb, RULE_SPELLED, LoadOptions::default()) {
        Err(errors) => rendered(errors),
        Ok(_) => panic!("`rule box(n: \"seven\") :- true` over `box(n: Int64)` must not load"),
    };
    assert_names_the_field(&errors, "a bodyless rule in a second `load_all`");
}

/// The earlier load for the RULE rows: a sort with two differently typed fields.
const SORT: &str = r#"
namespace test.ff.rules
  sort Rec
    entity box(n: Int64)
    entity tag(s: String)
  end
  fact box(n: 1)
end
"#;

/// A rule written INTO that sort by a later load, through a second `namespace` entry —
/// its domain is `Rec`, which the later call did not define.
fn into_the_sort(rule: &str) -> String {
    format!(
        "namespace test.ff.rules.Rec\n  import anthill.reflect.Expr.{{ho_apply}}\n  {rule}\nend\n"
    )
}

#[test]
fn a_later_calls_rule_in_an_earlier_calls_sort_is_typed() {
    let mut kb = load_kb_with(SORT);
    let later = into_the_sort("rule bad(?x) :- box(n: ?x), tag(s: ?x)");
    let errors = match load_in_a_later_call(&mut kb, &later, LoadOptions::default()) {
        Err(errors) => rendered(errors),
        Ok(_) => panic!("`?x` is an `Int64` in `box` and a `String` in `tag`: must not load"),
    };
    assert!(
        errors
            .iter()
            .any(|e| e.contains("bad") && e.contains("contradictory variable types")),
        "the rule's own contradiction is reported; got {errors:?}"
    );
}

#[test]
fn a_later_calls_rule_in_an_earlier_calls_sort_is_held_to_the_pattern_fragment() {
    let mut kb = load_kb_with(SORT);
    let later = into_the_sort("rule nested(?x) :- box(n: ?x), ho_apply(ho_apply(?P, ?x), ?x)");
    let errors = match load_in_a_later_call(&mut kb, &later, LoadOptions::default()) {
        Err(errors) => rendered(errors),
        Ok(_) => panic!("a predicate applied to a predicate is outside the fragment: must not load"),
    };
    assert!(
        errors
            .iter()
            .any(|e| e.contains("nested") && e.contains("nested ho_apply")),
        "the pattern-fragment refusal is reported; got {errors:?}"
    );
}

/// The control for the two rows above, driven: a well-typed rule written into the earlier
/// sort loads, and ANSWERS over the earlier load's fact.
#[test]
fn a_well_typed_rule_in_an_earlier_calls_sort_loads() {
    let mut kb = load_kb_with(SORT);
    let later = into_the_sort("rule held(?x) :- box(n: ?x)");
    expect_loaded(load_in_a_later_call(&mut kb, &later, LoadOptions::default()));
    assert_eq!(
        crate::common::one_definite_int(&mut kb, "test.ff.rules.Rec.held"),
        Some(1),
        "the later call's rule reads the earlier call's `fact box(n: 1)`"
    );
}

/// The rule arm's twin of `one_call_reports_the_fact_once`: a rule in a sort THIS call
/// defined is the sort loop's, and the pass over the call's clauses must leave it there.
/// Counted off the typer for the same reason — `load_all`'s exit would hide a double.
#[test]
fn one_call_reports_the_rule_once() {
    const IN_ITS_OWN_SORT: &str = r#"
namespace test.ff.own
  import anthill.reflect.Expr.{ho_apply}
  sort Rec
    entity box(n: Int64)
    rule nested(?x) :- box(n: ?x), ho_apply(ho_apply(?P, ?x), ?x)
  end
end
"#;
    let untyped = LoadOptions {
        run_typer: false,
        ..Default::default()
    };
    let (mut kb, result) = expect_loaded(recipe_load(
        &[IN_ITS_OWN_SORT],
        None,
        untyped,
        LoadRecipe::OneShot,
        |_| {},
    ));
    let errors = rendered(type_check_sorts(&mut kb, result.loaded()));
    let about_the_rule: Vec<&String> = errors
        .iter()
        .filter(|e| e.contains("nested ho_apply"))
        .collect();
    assert_eq!(
        about_the_rule.len(),
        1,
        "one rule outside the fragment, one report; got {about_the_rule:?}"
    );
}

/// A rule written at NAMESPACE level has a namespace for its domain, and the sort loop
/// visits sorts: in one call its contradiction is not reported, and never was. The row
/// does not say that is right. It says the pass over the call's clauses takes only rules
/// in a SORT, so it changes neither what one call says about such a rule nor — the same
/// thing — what a later call does.
#[test]
fn a_later_calls_namespace_level_rule_gets_the_verdict_one_call_gives_it() {
    const AT_NAMESPACE_LEVEL: &str = r#"
namespace test.ff.free
  import test.ff.rules.Rec.{box, tag}
  rule bad(?x) :- box(n: ?x), tag(s: ?x)
end
"#;
    let one_call = recipe_load(
        &[SORT, AT_NAMESPACE_LEVEL],
        None,
        LoadOptions::default(),
        LoadRecipe::OneShot,
        |_| {},
    )
    .map(|_| ())
    .map_err(rendered);

    let mut kb = load_kb_with(SORT);
    let later_call = load_in_a_later_call(&mut kb, AT_NAMESPACE_LEVEL, LoadOptions::default())
        .map(|_| ())
        .map_err(rendered);
    assert_eq!(
        one_call,
        Ok(()),
        "one call loads it, as it did before the pass over the call's clauses existed"
    );
    assert_eq!(later_call, one_call);
}

/// A file that fails to load defined its sorts in THIS call, so its clauses are not
/// "under a sort an earlier call defined" — and the typer does not visit a file that did
/// not load. One mistake, one diagnostic: nothing cascades from the refused file.
///
/// The mistake has to be one the file's own ITEM WALK reports (`fact e(n: 1) = 2`, a
/// fact that is no definition): that is what drops the file's sorts from the typer's
/// list. A name that resolves nowhere is reported by the declaration pass instead, the
/// file's items load, and its sorts are typed as any other's.
#[test]
fn a_refused_files_own_clauses_are_left_alone() {
    const REFUSED: &str = r#"
namespace test.ff.refused
  sort S
    entity e(n: Int64)
  end
  fact e(n: "seven")
  fact e(n: 1) = 2
end
"#;
    let errors = match recipe_load(
        &[REFUSED],
        None,
        LoadOptions::default(),
        LoadRecipe::OneShot,
        |_| {},
    ) {
        Err(errors) => rendered(errors),
        Ok(_) => panic!("a `fact` with a non-defining connective must not load"),
    };
    assert!(
        !errors.is_empty(),
        "the refusal is the file's own; got {errors:?}"
    );
    assert!(
        !errors.iter().any(|e| e.contains("e.n")),
        "the refused file's fact is not typed on top of it; got {errors:?}"
    );
}

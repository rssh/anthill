//! WI-20261006-SZKV7, the second finding of the two-step run — a composite's equality is
//! closed by the load that defines it.
//!
//! What decides a composite's equality is who supplies its `eq` and which provisions of
//! `PartialEq`, `Eq` and `NonEq` name it. A load that finds no `eq` supplied DERIVES the
//! equality from the fields — `Eq` if every field is, `NonEq` if one reaches a `Float` —
//! and it reads the provisions through a negation too (it derives nothing for a sort
//! something already speaks for). Sound within a load; across loads, a later one that
//! added to an earlier sort's equality left the derived rows standing beside its own,
//! with every dependent row and every resolved call resting on them. For a sort with a
//! `Float` field the derived comparison then DECIDED: `eq(reading(1.5), reading(2.5))`
//! answered `false` where one load of the same two sources answers `true`.
//!
//! The later load is now refused (`eq_derive::later_equality_refusals`,
//! `LoadError::EqualityOfEarlierSort`). Each composite's equality SIGNATURE — its `eq`
//! suppliers and the provisions naming it — is recorded when a load succeeds, and a load
//! under which an existing composite's signature has changed is a load error. One load
//! of both sources is untouched.
//!
//! EVERY ROW NAMES ITS CALLS, as `wi_szkv7_clause_frontier_test` does and for its reason.
//!
//! WHAT FAILS WHEN (measured by making the change and running this file):
//!
//! * the check reporting nothing: SEVENTEEN rows fail — every row that expects a
//!   refusal.
//! * who supplies the `eq` left out of the signature: the rows whose later load changes
//!   only that — `…_eq_member_of_the_sort_…`, `…_eq_member_of_an_earlier_witness_…`,
//!   `…_redeclaration_of_the_sort_…` — and `…_provision_binding_an_eq_…`, which names it.
//! * the provisions left out: `…_witness_that_supplies_no_eq_…`,
//!   `…_witness_writing_eq_alone_…`, `…_condition_on_an_earlier_provision_…`,
//!   `…_provision_for_another_instantiation_…`, `…_provision_binding_an_eq_…`.
//! * a provision's conditions and clause count left out of its entry:
//!   `…_condition_on_an_earlier_provision_…` and `…_provision_binding_an_eq_…`.
//! * a provision's ROW left out of its entry: `…_provision_for_another_instantiation_…`
//!   and `…_witness_writing_eq_alone_…`.
//! * `Eq` / `NonEq` provisions read by the carrier parameter a DISPATCH reads (the one an
//!   operation receives on, which they do not have): `a_later_witness_writing_eq_alone_
//!   is_refused`, and it alone — the witness's `Eq` is then filed under the witness.
//! * the carriers a load was refused over recorded as they now are:
//!   `a_knowledge_base_left_by_a_refused_load_is_refused_again`, and it alone.
//! * the record written only by a load that SUCCEEDED:
//!   `a_sort_a_failed_load_defined_is_held_too` and
//!   `a_failed_loads_derived_rows_do_not_refuse_its_corrected_retry` — one in each
//!   direction, which is why the record is written at every exit.
//! * the PARTIAL exit not recording: `a_partial_load_records_…`, and it alone.
//! * the record not restored by a layer's discard:
//!   `a_discarded_layer_leaves_the_record_as_the_base_had_it`, and it alone.
//! * the record taken where the check is made instead of at the END of the load — so
//!   without what the load's own later passes derive: nine rows, among them every one
//!   that makes a later load and expects it accepted (the two `…_its_own_sort` rows,
//!   `an_accepted_source_presented_again_…`, `an_earlier_sorts_own_eq_…`,
//!   `an_eq_for_a_sort_that_is_no_composite_…`), the stdlib's composites reading as
//!   changed. That is what those rows are for: the check refusing too much.
//!
//! `one_load_of_both_…` passes through all of these BY DESIGN — one load has no earlier
//! record to be held to. It is the control that the refused sources are valid together.

use anthill_core::eval::value::Value;
use anthill_core::eval::{self, EvalError, Interpreter};
use anthill_core::kb::load::{LoadError, LoadOptions, LoadResult};
use anthill_core::kb::KnowledgeBase;

use crate::common::{
    assert_refused_naming, expect_loaded, load_in_a_later_call, load_kb_with, recipe_load,
    rendered_load_errors, LoadRecipe,
};

/// The earlier load: a sort that reaches a `Float`, so its derived equality is the
/// partial, field-wise one.
const READING: &str = r#"
namespace test.le.base
  import anthill.prelude.{Float}
  sort Reading
    entity reading(v: Float)
  end
end
"#;

/// A later load's `eq` for it, from a witness sort — and a call, to read it back.
const READING_EQ: &str = r#"
namespace test.le.later
  import anthill.prelude.{Eq, PartialEq, Bool}
  import test.le.base.{Reading}
  import test.le.base.Reading.{reading}
  sort ReadingEq
    provides PartialEq[T = Reading]
    provides Eq[T = Reading]
    operation eq(a: Reading, b: Reading) -> Bool = true
  end
  sort Probe
    import anthill.prelude.PartialEq.{eq}
    operation direct() -> Bool = eq(reading(v: 1.5), reading(v: 2.5))
  end
end
"#;

/// An earlier load whose sort has only `Eq` fields: its derived equality is the total one.
const POINT: &str = r#"
namespace test.le.total
  import anthill.prelude.{Int64}
  sort Point
    entity point(x: Int64, y: Int64)
  end
end
"#;

fn later(kb: &mut KnowledgeBase, source: &str) -> Result<LoadResult, Vec<LoadError>> {
    load_in_a_later_call(kb, source, LoadOptions::default())
}

/// `earlier`, then `later_source` in a call of its own, which must be refused naming
/// `carrier` and each of `added`.
fn assert_later_load_refused(earlier: &str, later_source: &str, carrier: &str, added: &[&str]) {
    let mut kb = load_kb_with(earlier);
    let errors = match later(&mut kb, later_source) {
        Err(errors) => rendered_load_errors(errors),
        Ok(_) => panic!("a later load adding to the equality of '{carrier}' must not load"),
    };
    let closed = format!("the equality of '{carrier}' is closed");
    let mut tokens: Vec<&str> = vec![&closed];
    tokens.extend(added);
    assert_refused_naming(
        &errors,
        &tokens,
        "the refusal names the earlier sort and what this load added to its equality",
    );
}

fn bool_of(kb: KnowledgeBase, op: &str) -> bool {
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp).expect("standard builtins");
    match interp.call(op, &[]) {
        Ok(Value::Bool(b)) => b,
        other => panic!("`{op}` did not run to a Bool: {other:?}"),
    }
}

// ── an `eq`, through each of its three routes ──────────────────

#[test]
fn a_later_witness_eq_for_a_derived_partial_equality_is_refused() {
    assert_later_load_refused(
        READING,
        READING_EQ,
        "test.le.base.Reading",
        &["test.le.later.ReadingEq"],
    );
}

/// A witness that writes `Eq` ALONE — the spelling the prelude advertises, `PartialEq`
/// then being forwarded. `Eq` declares no operation, so the reading that asks which
/// parameter an operation receives on files this provision under the WITNESS; the check
/// reads the sort it is about off the spec's sole parameter instead.
#[test]
fn a_later_witness_writing_eq_alone_is_refused() {
    assert_later_load_refused(
        READING,
        r#"
namespace test.le.eqonly
  import anthill.prelude.{Eq, Bool}
  import test.le.base.{Reading}
  sort ReadingEqOnly
    provides Eq[T = Reading]
    operation eq(a: Reading, b: Reading) -> Bool = true
  end
end
"#,
        "test.le.base.Reading",
        &["`test.le.eqonly.ReadingEqOnly`'s provision of `Eq` for it is new"],
    );
}

/// The CONTROL, driven: the same two sources in ONE load are accepted, and the supplied
/// `eq` is the one that decides — the answer the later load used to contradict.
#[test]
fn one_load_of_both_accepts_it_and_the_supplied_eq_decides() {
    let (kb, _) = expect_loaded(recipe_load(
        &[READING, READING_EQ],
        None,
        LoadOptions::default(),
        LoadRecipe::OneShot,
        |_| {},
    ));
    assert!(
        bool_of(kb, "test.le.later.Probe.direct"),
        "`ReadingEq.eq` is `true`; the field-wise comparison would say `false`"
    );
}

#[test]
fn a_later_witness_eq_for_a_derived_total_equality_is_refused() {
    assert_later_load_refused(
        POINT,
        r#"
namespace test.le.total.later
  import anthill.prelude.{Eq, PartialEq, Bool}
  import test.le.total.{Point}
  sort PointAlwaysEq
    provides PartialEq[T = Point]
    provides Eq[T = Point]
    operation eq(a: Point, b: Point) -> Bool = true
  end
end
"#,
        "test.le.total.Point",
        &["test.le.total.later.PointAlwaysEq"],
    );
}

/// The BINDING route: no witness sort, a provision of the sort's own that binds its `eq`
/// to an operation — written in a later entry of the sort.
#[test]
fn a_later_provision_binding_an_eq_is_refused() {
    assert_later_load_refused(
        POINT,
        r#"
namespace test.le.total.Point
  import anthill.prelude.{PartialEq, Bool}
  operation peq(a: Point, b: Point) -> Bool = true
  provides PartialEq[T = Point, eq = peq]
end
"#,
        "test.le.total.Point",
        &[
            "its own provision of `PartialEq` for it has changed",
            "`test.le.total.Point.peq` now supplies its `eq`",
        ],
    );
}

/// The MEMBER route, which writes no provision at all: a later entry of the sort itself
/// declaring `eq`.
#[test]
fn a_later_eq_member_of_the_sort_is_refused() {
    assert_later_load_refused(
        POINT,
        r#"
namespace test.le.total.Point
  import anthill.prelude.{Bool}
  operation eq(a: Point, b: Point) -> Bool = true
end
"#,
        "test.le.total.Point",
        &["`test.le.total.Point.eq` now supplies its `eq`"],
    );
}

/// An `eq` added to a WITNESS the earlier load declared without one. No provision is
/// written and the composite gains no member of its own — only who supplies its `eq`
/// changes, which is why the check compares that and not what the load wrote.
#[test]
fn a_later_eq_member_of_an_earlier_witness_is_refused() {
    let (mut kb, _) = expect_loaded(recipe_load(
        &[
            POINT,
            r#"
namespace test.le.total.speaks
  import anthill.prelude.{PartialEq}
  import test.le.total.{Point}
  sort PointSpeaks
    provides PartialEq[T = Point]
  end
end
"#,
        ],
        None,
        LoadOptions::default(),
        LoadRecipe::OneShot,
        |_| {},
    ));
    let errors = match later(
        &mut kb,
        r#"
namespace test.le.total.speaks.PointSpeaks
  import anthill.prelude.{Bool}
  import test.le.total.{Point}
  operation eq(a: Point, b: Point) -> Bool = true
end
"#,
    ) {
        Err(errors) => rendered_load_errors(errors),
        Ok(_) => panic!("an `eq` on the witness that speaks for `Point` must not load later"),
    };
    assert_refused_naming(
        &errors,
        &[
            "the equality of 'test.le.total.Point' is closed",
            "`test.le.total.speaks.PointSpeaks.eq` now supplies its `eq`",
        ],
        "the witness is an earlier load's, and so is the sort it speaks for",
    );
}

/// The sort DECLARED AGAIN by the later load, with an `eq` in it. Declaring a sort again
/// across loads is accepted, so "a sort this load declares" is not "a sort new to the
/// KB" — and it is the second the rule is about.
#[test]
fn a_later_redeclaration_of_the_sort_with_an_eq_is_refused() {
    assert_later_load_refused(
        POINT,
        r#"
namespace test.le.total
  import anthill.prelude.{Int64, Bool}
  sort Point
    entity point(x: Int64, y: Int64)
    operation eq(a: Point, b: Point) -> Bool = true
  end
end
"#,
        "test.le.total.Point",
        &["`test.le.total.Point.eq` now supplies its `eq`"],
    );
}

// ── and what adds to the equality without supplying an `eq` ────

/// A witness that only SPEAKS for the sort. The derivation derives nothing for a sort a
/// provision already names, so loaded together `Point` gets no derived `Eq`; loaded
/// after, the derived `Eq` stood beside the witness.
#[test]
fn a_later_witness_that_supplies_no_eq_is_refused_too() {
    assert_later_load_refused(
        POINT,
        r#"
namespace test.le.total.speaks
  import anthill.prelude.{PartialEq}
  import test.le.total.{Point}
  sort PointSpeaks
    provides PartialEq[T = Point]
  end
end
"#,
        "test.le.total.Point",
        &["test.le.total.speaks.PointSpeaks", "`PartialEq`"],
    );
}

/// A later entry that restates one of the sort's provisions UNDER A CONDITION. The
/// provision row is the earlier load's, unchanged; what changes is that it is now
/// conditional, and written by two clauses.
#[test]
fn a_later_condition_on_an_earlier_provision_is_refused() {
    assert_later_load_refused(
        r#"
namespace test.le.cond
  import anthill.prelude.{Eq, PartialEq}
  sort Colour
    entity red
    entity green
    provides PartialEq[T = Colour]
    provides Eq[T = Colour]
  end
end
"#,
        r#"
namespace test.le.cond.Colour
  import anthill.prelude.{Eq, Int64}
  provides Eq[T = Colour] :- Eq[T = Int64]
end
"#,
        "test.le.cond.Colour",
        &["its own provision of `Eq` for it has changed"],
    );
}

/// A witness the earlier load declared speaks for ONE instantiation of a parametric
/// composite; a later entry of it speaks for ANOTHER. Same provider, same spec — a new
/// provision row, which is what a provision in the signature is identified by.
#[test]
fn a_later_provision_for_another_instantiation_is_refused() {
    let (mut kb, _) = expect_loaded(recipe_load(
        &[r#"
namespace test.le.inst
  import anthill.prelude.{PartialEq, Int64}
  sort Crate
    sort A = ?
    entity crate(v: A)
  end
  sort CrateSpeaks
    provides PartialEq[T = Crate[A = Int64]]
  end
end
"#],
        None,
        LoadOptions::default(),
        LoadRecipe::OneShot,
        |_| {},
    ));
    let errors = match later(
        &mut kb,
        r#"
namespace test.le.inst.CrateSpeaks
  import anthill.prelude.{PartialEq, String}
  import test.le.inst.{Crate}
  provides PartialEq[T = Crate[A = String]]
end
"#,
    ) {
        Err(errors) => rendered_load_errors(errors),
        Ok(_) => panic!("a second provision naming `Crate` must not load later"),
    };
    assert_refused_naming(
        &errors,
        &[
            "the equality of 'test.le.inst.Crate' is closed",
            "`test.le.inst.CrateSpeaks`'s provision of `PartialEq` for it is new",
        ],
        "the provider and the spec are the earlier load's; the provision is not",
    );
}

// ── whatever the earlier load did about the sort's equality ────

/// The earlier load WROTE the structural equality instead of having it derived — the
/// same provision, by the derivation's own account, and the same replacement.
#[test]
fn a_later_eq_for_a_structural_equality_the_earlier_load_wrote_is_refused() {
    assert_later_load_refused(
        r#"
namespace test.le.written
  import anthill.prelude.{Eq, PartialEq}
  sort Colour
    entity red
    entity green
    provides PartialEq[T = Colour]
    provides Eq[T = Colour]
  end
end
"#,
        r#"
namespace test.le.written.later
  import anthill.prelude.{Eq, PartialEq, Bool}
  import test.le.written.{Colour}
  sort ColourEq
    provides PartialEq[T = Colour]
    provides Eq[T = Colour]
    operation eq(a: Colour, b: Colour) -> Bool = true
  end
end
"#,
        "test.le.written.Colour",
        &["test.le.written.later.ColourEq"],
    );
}

/// The earlier load derived NOTHING for the sort: its field is of an abstract sort, which
/// has no equality to propagate. `=` over its values was structural all the same, and a
/// late `eq` changes that for every rule already loaded — so this is refused too, and the
/// rule needs no record of what an earlier load derived.
#[test]
fn a_later_eq_for_a_sort_nothing_was_derived_for_is_refused() {
    const HOLDER: &str = r#"
namespace test.le.none
  import anthill.prelude.{Int64}
  sort Handle
  end
  sort Holder
    entity holder(n: Int64, h: Handle)
  end
end
"#;
    let derived: Vec<(String, String)> = crate::common::sort_provisions_all(&load_kb_with(HOLDER))
        .into_iter()
        .filter(|(sort, spec)| {
            sort == "test.le.none.Holder"
                && ["Eq", "PartialEq", "NonEq"]
                    .iter()
                    .any(|s| *spec == format!("anthill.prelude.{s}"))
        })
        .collect();
    assert!(
        derived.is_empty(),
        "CONTROL: the earlier load derived no equality for `Holder` — else this row is one \
         of the derived ones above; got {derived:?}"
    );
    assert_later_load_refused(
        HOLDER,
        r#"
namespace test.le.none.later
  import anthill.prelude.{Eq, PartialEq, Bool}
  import test.le.none.{Holder}
  sort HolderEq
    provides PartialEq[T = Holder]
    provides Eq[T = Holder]
    operation eq(a: Holder, b: Holder) -> Bool = true
  end
end
"#,
        "test.le.none.Holder",
        &["test.le.none.later.HolderEq"],
    );
}

/// A PARAMETRIC sort's derived equality is conditional on its arguments', and the sort
/// here is the stdlib's `List`, so the two recipes of the test helpers are the two loads.
/// This is the fixture of
/// `wi228_tree_threaded_dispatch_test::pin_now_threads_conditional_tree_into_nested_dictionary_nodes`,
/// the one test that differed under the two-step recipe; both recipes are named, the
/// row's subject being that they now differ LOUDLY.
#[test]
fn a_later_eq_for_a_parametric_stdlib_sort_is_refused() {
    const EQ_LIST: &str = r#"
namespace test.le.list
  import anthill.prelude.{Eq, PartialEq, List, Int64, Bool}
  sort EqList
    sort A = ?
    requires Eq[T = A]
    provides PartialEq[T = List[T = A]]
    provides Eq[T = List[T = A]]
    operation eq(x: List[T = A], y: List[T = A]) -> Bool = true
  end
  sort Driver
    import anthill.prelude.PartialEq.{eq}
    operation drive() -> Bool = eq([1], [2])
  end
end
"#;
    let load = |recipe| recipe_load(&[EQ_LIST], None, LoadOptions::default(), recipe, |_| {});

    let (kb, _) = expect_loaded(load(LoadRecipe::OneShot));
    assert!(
        bool_of(kb, "test.le.list.Driver.drive"),
        "loaded WITH the stdlib, `EqList.eq` is `List`'s equality"
    );

    let errors = match load(LoadRecipe::TwoStep) {
        Err(errors) => rendered_load_errors(errors),
        Ok(_) => panic!("loaded AFTER the stdlib, an `eq` for `List` must not load"),
    };
    assert_refused_naming(
        &errors,
        &[
            "the equality of 'anthill.prelude.List' is closed",
            "test.le.list.EqList",
        ],
        "the stdlib's `List` is an earlier load's sort",
    );
}

/// `KB.loaded` is a later load: the candidate is refused, RAISED as the diagnostics.
#[test]
fn a_kb_loaded_candidate_adding_to_a_base_sorts_equality_is_refused() {
    let mut interp = crate::common::interp_for(READING);
    let list = interp
        .build_list_value(vec![Value::Str(READING_EQ.to_string())], &[])
        .expect("build List[String]");
    let payload = match interp.call("anthill.reflect.KB.loaded", &[list]) {
        Err(EvalError::Raised { payload }) => format!("{payload:?}"),
        other => panic!("the candidate is RAISED, as `load_failed`; got {other:?}"),
    };
    assert!(
        payload.contains("the equality of 'test.le.base.Reading' is closed"),
        "the raised diagnostics are this refusal; got {payload}"
    );
}

// ── what the refusal must not touch ────────────────────────────

/// A later load defines equality for ITS OWN sort — a `Float` field and an `eq`, the very
/// shape refused above when the sort is someone else's — and the `eq` decides.
#[test]
fn a_later_load_may_supply_the_equality_of_its_own_sort() {
    let mut kb = load_kb_with(READING);
    expect_loaded(later(
        &mut kb,
        r#"
namespace test.le.own
  import anthill.prelude.{Float, Eq, PartialEq, Bool}
  sort Gauge
    entity gauge(v: Float)
    provides PartialEq[T = Gauge]
    provides Eq[T = Gauge]
    operation eq(a: Gauge, b: Gauge) -> Bool = true
  end
  sort Probe
    import anthill.prelude.PartialEq.{eq}
    operation direct() -> Bool = eq(gauge(v: 1.5), gauge(v: 2.5))
  end
end
"#,
    ));
    assert!(
        bool_of(kb, "test.le.own.Probe.direct"),
        "`Gauge.eq` is `true`, and `Gauge` is this load's own"
    );
}

/// And a witness for its own sort, the other spelling of the same thing.
#[test]
fn a_later_load_may_witness_the_equality_of_its_own_sort() {
    let mut kb = load_kb_with(POINT);
    expect_loaded(later(
        &mut kb,
        r#"
namespace test.le.own2
  import anthill.prelude.{Int64, Eq, PartialEq, Bool}
  sort Tick
    entity tick(n: Int64)
  end
  sort TickEq
    provides PartialEq[T = Tick]
    provides Eq[T = Tick]
    operation eq(a: Tick, b: Tick) -> Bool = true
  end
  sort Probe
    import anthill.prelude.PartialEq.{eq}
    operation direct() -> Bool = eq(tick(n: 1), tick(n: 2))
  end
end
"#,
    ));
    assert!(
        bool_of(kb, "test.le.own2.Probe.direct"),
        "`TickEq.eq` is `true`, and `Tick` is this load's own"
    );
}

/// An earlier load's sort that had its OWN `eq` from the start is a boundary and, with a
/// `Float` field, one the derivation's partial half also reaches. Nothing a later load
/// adds is about it, so a later load of an unrelated source is not refused.
#[test]
fn an_earlier_sorts_own_eq_does_not_refuse_a_later_load() {
    let mut kb = load_kb_with(
        r#"
namespace test.le.fixed
  import anthill.prelude.{Float, Eq, PartialEq, Bool}
  sort Approx
    entity approx(v: Float)
    provides PartialEq[T = Approx]
    provides Eq[T = Approx]
    operation eq(a: Approx, b: Approx) -> Bool = true
  end
end
"#,
    );
    expect_loaded(later(&mut kb, POINT));
}

/// The check is about COMPOSITES — the sorts whose equality a load derives or compares
/// structurally. An `eq` for an earlier load's ABSTRACT sort adds to no derivation: it is
/// what a host's bindings do for the primitives, in whatever load they arrive.
#[test]
fn an_eq_for_a_sort_that_is_no_composite_is_accepted() {
    let mut kb = load_kb_with(
        r#"
namespace test.le.abs
  sort Handle
  end
end
"#,
    );
    expect_loaded(later(
        &mut kb,
        r#"
namespace test.le.abs.later
  import anthill.prelude.{Eq, PartialEq, Bool}
  import test.le.abs.{Handle}
  sort HandleEq
    provides PartialEq[T = Handle]
    provides Eq[T = Handle]
    operation eq(a: Handle, b: Handle) -> Bool = true
  end
end
"#,
    ));
}

/// A source an earlier load already ACCEPTED, presented again on its own, adds nothing:
/// the sort's `eq` was supplied in the load that defined it, and still is. (Read off what
/// the load declared, this was refused — the member is declared again.)
#[test]
fn an_accepted_source_presented_again_is_accepted() {
    const MEMBER: &str = r#"
namespace test.le.total.Point
  import anthill.prelude.{Bool}
  operation eq(a: Point, b: Point) -> Bool = true
end
"#;
    let (mut kb, _) = expect_loaded(recipe_load(
        &[POINT, MEMBER],
        None,
        LoadOptions::default(),
        LoadRecipe::OneShot,
        |_| {},
    ));
    expect_loaded(later(&mut kb, MEMBER));
}

/// A REFUSED source presented again is refused again, and so is any other source: a
/// plain load does not unwind, so the knowledge base a refused load leaves behind holds
/// what was refused, and it is held to the last state that LOADED until it is repaired
/// or discarded. (Read off the rows a load wrote, the second attempt was accepted — its
/// rows land on the slots the refused attempt filled.)
#[test]
fn a_knowledge_base_left_by_a_refused_load_is_refused_again() {
    let mut kb = load_kb_with(READING);
    let refused = |kb: &mut KnowledgeBase, source: &str, why: &str| {
        let errors = match later(kb, source) {
            Err(errors) => rendered_load_errors(errors),
            Ok(_) => panic!("{why}"),
        };
        assert_refused_naming(
            &errors,
            &["the equality of 'test.le.base.Reading' is closed", "test.le.later.ReadingEq"],
            why,
        );
    };
    refused(&mut kb, READING_EQ, "the first attempt is refused");
    refused(&mut kb, READING_EQ, "the same source again is refused again");
    refused(&mut kb, POINT, "and so is an unrelated source, the base being as the refused load left it");
}

/// A layer's discard takes its part of the record with it. The first candidate gives the
/// base's ABSTRACT sort an equality — allowed, it is no composite — and the base's
/// composite holding it thereby gets a DERIVED equality, inside the layer. Discarded, the
/// derived rows are gone; the record must be back at the base's too, or the next
/// candidate, which touches nothing, is refused for the composite's equality having
/// "changed".
#[test]
fn a_discarded_layer_leaves_the_record_as_the_base_had_it() {
    let mut interp = crate::common::interp_for(
        r#"
namespace test.le.layer
  import anthill.prelude.{Int64}
  sort Handle
  end
  sort Holder
    entity holder(n: Int64, h: Handle)
  end
end
"#,
    );
    let mut loaded = |interp: &mut Interpreter, source: &str| {
        let list = interp
            .build_list_value(vec![Value::Str(source.to_string())], &[])
            .expect("build List[String]");
        interp.call("anthill.reflect.KB.loaded", &[list])
    };
    let derived_for = |interp: &Interpreter| -> Vec<(String, String)> {
        crate::common::sort_provisions_all(interp.kb())
            .into_iter()
            .filter(|(sort, spec)| {
                sort == "test.le.layer.Holder" && spec == "anthill.prelude.Eq"
            })
            .collect()
    };

    let layer = loaded(
        &mut interp,
        r#"
namespace test.le.layer.Handle
  import anthill.prelude.{Eq, PartialEq}
  provides PartialEq[T = Handle]
  provides Eq[T = Handle]
end
"#,
    )
    .expect("an equality for the abstract `Handle` loads");
    assert_eq!(
        derived_for(&interp).len(),
        1,
        "CONTROL: inside the layer `Holder` has a derived `Eq` — the row the record must \
         not keep"
    );
    drop(layer);
    interp.sweep_layers();
    assert!(derived_for(&interp).is_empty(), "the discard took the derived row");

    let next = loaded(
        &mut interp,
        "namespace test.le.layer.next\n  entity unrelated\nend\n",
    );
    assert!(
        next.is_ok(),
        "the next candidate adds to nothing; `Holder`'s equality is the base's again: {next:?}"
    );
}

// ── the record, at every exit ──────────────────────────────────

/// A PARTIAL load records too. Here it is the first load into the KB, so without its
/// record there is no earlier sort at all and the later load is held to nothing.
#[test]
fn a_partial_load_records_what_the_next_load_is_held_to() {
    let untyped = LoadOptions {
        run_typer: false,
        ..Default::default()
    };
    let (mut kb, _) = expect_loaded(recipe_load(
        &[READING],
        None,
        untyped,
        LoadRecipe::OneShot,
        |_| {},
    ));
    let errors = match later(&mut kb, READING_EQ) {
        Err(errors) => rendered_load_errors(errors),
        Ok(_) => panic!("`Reading` is the partial load's sort, and its equality is closed"),
    };
    assert_refused_naming(
        &errors,
        &["the equality of 'test.le.base.Reading' is closed", "test.le.later.ReadingEq"],
        "a load that stopped before the typer still defined the sort",
    );
}

/// A sort defined by a load that FAILED for an unrelated reason is held like any other:
/// the failed load's passes derived its equality all the same, and the next load must
/// not get to add to it unseen.
#[test]
fn a_sort_a_failed_load_defined_is_held_too() {
    let mut kb = load_kb_with(POINT);
    let failed = later(
        &mut kb,
        &format!("{READING}\nnamespace test.le.base.bad\n  import test.le.base.Reading.{{reading}}\n  fact reading(v: \"x\")\nend\n"),
    );
    let errors = rendered_load_errors(failed.err().expect("the ill-typed fact fails the load"));
    assert!(
        !errors.iter().any(|e| e.contains("is closed")),
        "CONTROL: the load fails for a reason that has nothing to do with equality; got {errors:?}"
    );
    let errors = match later(&mut kb, READING_EQ) {
        Err(errors) => rendered_load_errors(errors),
        Ok(_) => panic!("`Reading`'s equality was derived by the failed load and is closed"),
    };
    assert_refused_naming(
        &errors,
        &["the equality of 'test.le.base.Reading' is closed", "test.le.later.ReadingEq"],
        "the failed load defined the sort",
    );
}

/// And the other half: what a failed load's passes DERIVED for an earlier composite is
/// recorded as well, so its corrected retry is not refused over a row no source wrote.
/// The load gives the base's abstract `Handle` an equality (allowed), which derives an
/// `Eq` for the base's `Holder`, and fails on an unrelated ill-typed fact.
#[test]
fn a_failed_loads_derived_rows_do_not_refuse_its_corrected_retry() {
    const HANDLE_EQ: &str = r#"
namespace test.le.retry.Handle
  import anthill.prelude.{Eq, PartialEq}
  provides PartialEq[T = Handle]
  provides Eq[T = Handle]
end
"#;
    let mut kb = load_kb_with(
        r#"
namespace test.le.retry
  import anthill.prelude.{Int64}
  sort Handle
  end
  sort Holder
    entity holder(n: Int64, h: Handle)
  end
end
"#,
    );
    let failed = later(
        &mut kb,
        &format!("{HANDLE_EQ}\nnamespace test.le.retry.bad\n  import test.le.retry.Holder.{{holder}}\n  fact holder(n: \"x\")\nend\n"),
    );
    let errors = rendered_load_errors(failed.err().expect("the ill-typed fact fails the load"));
    assert!(
        errors.iter().any(|e| e.contains("holder.n")) && !errors.iter().any(|e| e.contains("is closed")),
        "CONTROL: it fails on the fact, and not on equality; got {errors:?}"
    );
    expect_loaded(later(&mut kb, HANDLE_EQ));
}

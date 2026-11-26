//! WI-20261010-ANK4X — THE PROVIDER INDEX TAKES A ROW WHERE ONE IS ASSERTED, and a pass
//! that asserts provisions reads its own rows back through it.
//!
//! The index over `SortProvidesInfo` and `ProvidesConditionInfo` was built once per
//! frozen state and DROPPED around every pass that asserted a provision, so that pass's
//! reads scanned the relation: 39 % of a later load, in the pre-typer half of equality
//! derivation alone. It is filed now where a clause is stored
//! (`KnowledgeBase::push_value_head_entry`), and nothing drops it.
//!
//! THE TRAP of an index that takes rows as they come is a read that MISSES one asserted
//! a moment before. The fixture is the shape that needs such a row: `Holder`'s field is
//! a parametric sort at `Colour`, and `Colour`'s `Eq` and `Holder`'s are asserted by
//! `derive_conditional_eq` in the same load, a moment before what reads them — the
//! derived members, `Hash`, the forwarded rows and the typer, which resolves
//! `contains`'s `requires Eq[T = Holder]` through `Option[T = Colour]` to `Colour`.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ───────────────────────────────
//!
//! MEASURED 2026-10-11 on the tree as delivered, three ways, each by making the change in
//! `load::load_phase_inner` and running this file with `wi_ckd4j`, `wi1098` and `wi664`
//! (37 tests; 37 pass as it stands). `before` is the index as it was above the
//! derivation (`kb.provides_index.borrow().clone()`). There were TWO passes then:
//! `derive_total_eq` asserted `Colour`'s rows one pass before `derive_conditional_eq`
//! read them, to leave `Colour` out of its own candidates and to decide `Holder`'s
//! field. WI-20261102-YX17K folded them into one; the first row below is measured again
//! on the fold, and the third no longer has a pass to stand between.
//!
//! * THE INDEX LEFT AS IT STOOD BEFORE THE DERIVATION'S ROWS (put back to `before`
//!   below the call) — an index that took no row while the pass asserted: 37 of 37
//!   FAIL, and not on a row; the stdlib's own load panics, so the shared base is never
//!   built. On the two passes (`before` above `derive_total_eq`) the panic was the load's
//!   check of the index against the relation, naming the 94 buckets short of rows — the
//!   providers of `Eq` and of `PartialEq`, and the provisions and the edges of 46
//!   carriers. On the fold, MEASURED 2026-11-26, it is the forwarding of the derived rows
//!   that stops first (`provides_index.rs`, WI-20261121-TV0PA's debug assertion:
//!   "`anthill.prelude.Result`'s provision of `anthill.prelude.Eq` is conditioned and no
//!   clause is filed at its view"), which runs before that check is reached.
//! * THE SAME, WITH THAT CHECK TAKEN OUT (two passes): 37 of 37 FAIL again, the stdlib
//!   REFUSED, one error a carrier: "'anthill.reflect.MemberKind' provides
//!   'anthill.prelude.Eq', which requires 'anthill.prelude.PartialEq', but … does not
//!   provide" it. Nothing files the rows later, so the typer's checks read an index
//!   without them. Loud both ways.
//! * THE INDEX SHORT OF `derive_total_eq`'S ROWS THROUGH `derive_conditional_eq` ONLY
//!   (two passes), put right after it (`ProvidesIndex::from_scan(kb)`) — what a read that
//!   misses a row asserted a pass before is, with everything downstream served: 2 of 37
//!   FAILED. `a_total_composite_is_derived_once`, under each of the three recipes —
//!   `Colour` was not seen to provide `Eq`, was taken for a candidate of the conditional
//!   pass too, and was derived a second time, filing a clause the total pass's row did
//!   not have; and `wi1098_derive_eq_total_test::a_parametric_sort_derives_a_conditional_row`,
//!   on the same count. `a_holder_of_a_total_composite_answers` and the 34 others PASSED:
//!   the second derivation of `Colour` answered for `Holder`'s field, the value of the
//!   call right through a wrong derivation — the green suite over a stale index that the
//!   ticket names. Which is why this change is held by the load's own check and by the
//!   agreement run (`ANTHILL_PROVIDES_INDEX_AGREEMENT=1`, `rustland/CLAUDE.md`), and a
//!   value is asserted here only to say that the derivation still does its work.
//!   Since the fold there is no such row to miss: `Holder`'s field reads `Colour`'s
//!   verdict inside the one pass's fixpoint, and `Colour` has one owner.
//!
//! NOT THE RECIPE, BY NAME: each row runs on the shared base — a later load, into a
//! copy — and under both fresh recipes by name, because where the passes assert between
//! their reads differs between them: in one call `Option`'s conditional rows are
//! derived by the same pass that derives `Holder`'s, as a later load they are an
//! earlier load's.

use anthill_core::eval::value::Value;
use anthill_core::eval::Interpreter;
use anthill_core::kb::load::LoadOptions;
use anthill_core::kb::typing::provider_index_agreement_reads_by_this_thread;
use anthill_core::kb::KnowledgeBase;

use crate::common::{expect_loaded, load_kb_with, recipe_load, LoadRecipe};

const PROGRAM: &str = r#"
namespace wiank4x.derive
  import anthill.prelude.{Bool, Int64, List, Option}
  import anthill.prelude.List.{cons, nil, contains}
  import anthill.prelude.Option.{some, none}
  sort Colour
    entity red
    entity green
  end
  sort Holder
    entity holder(o: Option[T = Colour])
  end
  sort D
    operation same(n: Int64) -> Int64 =
      if contains(cons(head: holder(o: some(red)), tail: nil), holder(o: some(red))) then 1 else 0
    operation other(n: Int64) -> Int64 =
      if contains(cons(head: holder(o: some(red)), tail: nil), holder(o: some(green))) then 1 else 0
    operation absent(n: Int64) -> Int64 =
      if contains(cons(head: holder(o: some(red)), tail: nil), holder(o: none)) then 1 else 0
  end
end
"#;

/// The program loaded each way a test can load it: on the shared base, and under the
/// two fresh recipes by name.
fn loaded_each_way() -> Vec<(&'static str, KnowledgeBase)> {
    let mut out = vec![("the shared base", load_kb_with(PROGRAM))];
    for recipe in [LoadRecipe::OneShot, LoadRecipe::TwoStep] {
        let (kb, _) = expect_loaded(recipe_load(
            &[PROGRAM],
            None,
            LoadOptions::default(),
            recipe,
            |_| {},
        ));
        out.push((
            match recipe {
                LoadRecipe::OneShot => "one call",
                LoadRecipe::TwoStep => "two calls",
            },
            kb,
        ));
    }
    out
}

fn call(interp: &mut Interpreter, op: &str) -> i64 {
    match interp.call(&format!("wiank4x.derive.D.{op}"), &anthill_core::eval::HostValue::all(&[Value::Int(0)])).map(|h| h.value) {
        Ok(Value::Int(n)) => n,
        other => panic!("{op}: expected an Int, got {other:?}"),
    }
}

/// THE VALUE of a call that requires `Eq[Holder]` — `List.contains` — beside two
/// negative twins: a `contains` that answered `true` for anything would pass the first
/// and fail the others. `Eq[Holder]` holds only through `Eq[Option[T = Colour]]`, and
/// that only through the `Eq[Colour]` the same load derived.
#[test]
fn a_holder_of_a_total_composite_answers() {
    for (how, kb) in loaded_each_way() {
        let mut interp = Interpreter::new(kb);
        anthill_core::eval::builtins::register_standard_builtins(&mut interp);
        assert_eq!(call(&mut interp, "same"), 1, "{how}");
        assert_eq!(call(&mut interp, "other"), 0, "{how}");
        assert_eq!(call(&mut interp, "absent"), 0, "{how}");
    }
}

/// `Colour` and `Holder` are derived by ONE pass (WI-20261102-YX17K): each provides both
/// specs in one clause with no condition — `Colour` resting on nothing, `Holder`'s field
/// on nothing but `Colour` — filed as a written unconditional provision is. FAILS on the
/// tree before the fold, MEASURED, under each of the three recipes: there the TOTAL pass
/// derived `Colour` and filed no clause (count 0), and this row pinned that 0 as the sign
/// that the conditional pass had not derived it a second time. The record cannot show a
/// second derivation now — it keeps one entry per distinct condition list — and the
/// fold leaves none to show: no earlier pass asserts a row this one could miss.
#[test]
fn a_total_composite_is_derived_once() {
    // Every recipe is asked before any is judged, so a run says which of them differ.
    let mut wrong: Vec<String> = Vec::new();
    for (how, kb) in loaded_each_way() {
        for carrier in ["Colour", "Holder"] {
            let sym = kb
                .try_resolve_symbol(&format!("wiank4x.derive.{carrier}"))
                .expect(carrier);
            for spec in ["anthill.prelude.PartialEq", "anthill.prelude.Eq"] {
                let spec_sym = kb.try_resolve_symbol(spec).expect(spec);
                let clauses = kb.provides_clause_count(sym, spec_sym);
                if clauses != 1 {
                    wrong.push(format!(
                        "{how}: `{carrier}` provides {spec} by the derivation, in one clause, \
                         and has {clauses}"
                    ));
                }
                if kb.provision_has_conditions(sym, spec_sym) {
                    wrong.push(format!(
                        "{how}: `{carrier}` provides {spec} under a condition, where its \
                         fields' {spec} holds outright"
                    ));
                }
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// THE AGREEMENT CONTROL RUNS WHEN IT IS ASKED FOR, AND ONLY THEN — the control of the
/// instrument, in every run. "The agreement run was clean" is evidence only if the
/// switch took: a variable misspelt in a command, or in the reader, leaves a run that
/// checks nothing and is green. So a load is made and the reads the control made both
/// ways on this thread are counted (`provider_index_agreement_reads_by_this_thread`):
/// some under `ANTHILL_PROVIDES_INDEX_AGREEMENT=1`, none without it. What was OBSERVED
/// goes into the run's log, as the recipe's control does it, so a reader of a log sees
/// which run it is.
///
/// The variable is read HERE and spelled out, not through the library's reader: the
/// row is a control on that reader. MEASURED (2026-10-11): with the name in
/// `typing::agreement_on` changed by one letter and the switch set, this row FAILS —
/// asked for, none made — and the 13 others run with it (this file's and
/// `wi_ckd4j`'s) pass, checking nothing.
#[test]
fn the_agreement_control_runs_when_it_is_asked_for() {
    use std::io::Write;
    let asked = std::env::var("ANTHILL_PROVIDES_INDEX_AGREEMENT").is_ok_and(|v| v == "1");
    let before = provider_index_agreement_reads_by_this_thread();
    drop(load_kb_with(PROGRAM));
    let reads = provider_index_agreement_reads_by_this_thread() - before;
    // To the handle directly and in one write: libtest captures `eprintln!` of a
    // passing test, and this line is for the run's log.
    let line = format!(
        "provider index agreement OBSERVED by {}: {} ({reads} reads of one load made both ways)\n",
        module_path!(),
        if reads > 0 { "ON" } else { "off" },
    );
    let _ = std::io::stderr().write_all(line.as_bytes());
    assert_eq!(
        reads > 0,
        asked,
        "ANTHILL_PROVIDES_INDEX_AGREEMENT asked for: {asked}; reads of the provider index \
         made both ways by a load on this thread: {reads}"
    );
}

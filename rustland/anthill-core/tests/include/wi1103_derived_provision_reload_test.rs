//! WI-1103 — a DERIVED provision must survive the NEXT load phase.
//!
//! `eq_derive::run` asserts a Partial composite's `NonEq` + `PartialEq` and stands
//! AFTER `check_provider_operations`, so a derived `NonEq`'s unbacked `nonEqRefl`
//! witness (a propagated classification, not a hand-declared primitive) is not held
//! to op-backing. That placement protects the row being CREATED and not the row that
//! already EXISTS: the fact persists in the KB, and the next `load_phase_inner` walks
//! it BEFORE `eq_derive` re-runs. MEASURED at 51d17d22 — `load_stdlib` then
//! `load_incremental` over the full stdlib + host closure refused five carriers
//! (`anthill.reflect.Expr`, `TermRepr`, `LiteralRepr`, `anthill.geometry.EulerAngles`,
//! `Vec3`), i.e. a KB that had just loaded clean could not be loaded into again.
//!
//! The fix makes the exemption a property of the ROW
//! (`KnowledgeBase::mark_unbacked_derived_provision`, read by the op-backing walk in
//! `check_provider_operations`) instead of a property of the pass ORDER.
//!
//! WHY THE SUITE WAS GREEN: nearly every test builds its KB with ONE `load_all`, and
//! the two-phase path's own fixtures (`incremental_load_test`) loaded `stdlib_dir()`
//! ALONE — without `anthill-stl/`, so `fact Eq[Int64]` and friends are absent, almost
//! nothing classifies, and these five carriers are never reached. Same
//! "corpus cannot reach the bug" shape as WI-979. Those fixtures now load the FULL
//! closure, and are a second CONTROL for this file.
//!
//! CONTROL — MEASURED by backing the change out (the `is_unbacked_derived_provision`
//! skip in `check_provider_operations`) and running the whole `anthill-core` suite:
//! FOUR tests fail and no others. Two here —
//! `two_phase_load_drives_a_derived_noneq_carrier` and
//! `derived_noneq_rows_survive_the_next_phase_unchanged`, both at their phase-2
//! load, with the five `UnbackedProviderOperation` errors above — and two in
//! `incremental_load_test` (`load_incremental_does_not_touch_stdlib_facts`,
//! `load_incremental_equivalent_to_load_all`), which only reach the defect now that
//! their fixtures load the full closure.
//! `hand_written_unbacked_provision_is_refused_in_both_phases` passes either way BY
//! DESIGN: it is the guard that the mark did not turn the check off, so it must be
//! green before and after.

use anthill_core::eval::Interpreter;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use anthill_core::persistence::print::TermPrinter;

/// The phase-2 file. It USES a carrier whose `NonEq` was derived in PHASE 1
/// (`anthill.geometry.Vec3`) — so the classification under test is not vacuous — and
/// declares a Float-reaching composite of its OWN (`reading`), so this phase's
/// derivation runs too and its rows are marked as they are created.
const USER: &str = r#"
namespace test.wi1103
  import anthill.prelude.{Bool, Int64, Float}
  import anthill.prelude.Float.{nan}
  import anthill.prelude.PartialEq.{eq, neq}
  import anthill.geometry.{Vec3}

  sort Reading
    entity reading(v: Vec3, tag: Int64)
  end

  -- A phase-1-derived NonEq carrier, compared FIELD-WISE: IEEE nan != nan.
  operation vec3_nan_eq()  -> Bool =
    eq(Vec3(x: nan, y: 0.0, z: 0.0), Vec3(x: nan, y: 0.0, z: 0.0))
  operation vec3_nan_neq() -> Bool =
    neq(Vec3(x: nan, y: 0.0, z: 0.0), Vec3(x: nan, y: 0.0, z: 0.0))
  -- ... and still discriminating without a NaN.
  operation vec3_eq() -> Bool =
    eq(Vec3(x: 1.0, y: 2.0, z: 3.0), Vec3(x: 1.0, y: 2.0, z: 3.0))
  operation vec3_ne() -> Bool =
    eq(Vec3(x: 1.0, y: 2.0, z: 3.0), Vec3(x: 1.0, y: 2.0, z: 9.0))

  -- A PHASE-2 composite reaching the same Float leaf one level deeper.
  operation reading_nan_eq() -> Bool =
    eq(reading(v: Vec3(x: nan, y: 0.0, z: 0.0), tag: 1),
       reading(v: Vec3(x: nan, y: 0.0, z: 0.0), tag: 1))
  operation reading_eq() -> Bool =
    eq(reading(v: Vec3(x: 1.0, y: 2.0, z: 3.0), tag: 1),
       reading(v: Vec3(x: 1.0, y: 2.0, z: 3.0), tag: 1))
end
"#;

fn parse_files(paths: &[std::path::PathBuf]) -> Vec<anthill_core::parse::ir::ParsedFile> {
    paths
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p).expect("read");
            parse::parse(&src).expect("parse")
        })
        .collect()
}

/// Phase 1 over the FULL closure — `stdlib/anthill/` **plus** `anthill-stl/anthill/`.
/// The host bindings are what make this reach the defect: `fact Eq[Int64]` /
/// `fact NonEq[Float]` live there, and without them the classifier has no lawful-`Eq`
/// leaves to propagate from and no partial leaf to propagate (see the module header).
fn phase_one_full_closure() -> KnowledgeBase {
    let files = crate::common::collect_stdlib_and_rust_bindings();
    let parsed = parse_files(&files);
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::load_stdlib(&mut kb, &refs, &NullResolver).expect("phase 1: full-closure stdlib load");
    kb
}

fn load_phase_two(kb: &mut KnowledgeBase, src: &str) -> Result<(), Vec<String>> {
    let user = parse::parse(src).expect("parse user source");
    load::load_incremental(kb, &[&user], &NullResolver)
        .map(|_| ())
        .map_err(|errs| errs.iter().map(|e| e.to_string()).collect())
}

fn call_bool(i: &mut Interpreter, op: &str) -> bool {
    i.call(op, &[])
        .unwrap_or_else(|e| panic!("call {op}: {e:?}"))
        .as_bool()
        .unwrap_or_else(|| panic!("call {op}: not a Bool"))
}

/// Every `SortProvidesInfo` fact, rendered. `TermPrinter` prints SHORT names, so a
/// row reads `SortProvidesInfo(sort_ref: Vec3, spec: SortView(NonEq, T: Vec3))`.
fn provides_rows(kb: &KnowledgeBase) -> Vec<String> {
    let sym = kb
        .try_resolve_symbol("anthill.reflect.SortProvidesInfo")
        .expect("SortProvidesInfo");
    let printer = TermPrinter::new(kb);
    kb.rules_by_functor(sym)
        .iter()
        .map(|rid| printer.print_term(kb.rule_head(*rid)))
        .collect()
}

/// The rendered `NonEq` row for one carrier — a whole-string match, so a substring
/// that also appears in a neighbouring carrier's row cannot stand in for it.
const VEC3_NONEQ: &str = "SortProvidesInfo(sort_ref: Vec3, spec: SortView(NonEq, T: Vec3))";

/// THE HEADLINE. Two phases over the full closure, and the second phase is DRIVEN:
/// the derived-`NonEq` carrier's field-wise equality actually runs and answers IEEE.
///
/// CONTROL — FAILS without the change, at the `load_phase_two` line, with the five
/// `UnbackedProviderOperation` errors named in the module header. The `eq` assertions
/// below are not reachable at all until the load succeeds, which is why the load and
/// the behaviour are one test: "it loads clean" would not show that the row still
/// MEANS anything, and the `eq` calls alone cannot run.
#[test]
fn two_phase_load_drives_a_derived_noneq_carrier() {
    let mut kb = phase_one_full_closure();
    load_phase_two(&mut kb, USER).expect("phase 2 must load into an already-loaded KB");

    let mut i = Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut i)
        .expect("register standard eval builtins");

    // The PHASE-1-derived carrier, compared field-wise across the phase boundary.
    assert!(
        !call_bool(&mut i, "test.wi1103.vec3_nan_eq"),
        "eq(Vec3(nan,0,0), Vec3(nan,0,0)) must be FALSE — Vec3's NonEq was derived in \
         phase 1 and its field-wise comparison must still be in force in phase 2"
    );
    assert!(
        call_bool(&mut i, "test.wi1103.vec3_nan_neq"),
        "neq(Vec3(nan,0,0), Vec3(nan,0,0)) must be true"
    );
    assert!(
        call_bool(&mut i, "test.wi1103.vec3_eq"),
        "eq(Vec3(1,2,3), Vec3(1,2,3)) must be true — field-wise, not merely non-reflexive"
    );
    assert!(
        !call_bool(&mut i, "test.wi1103.vec3_ne"),
        "eq(Vec3(1,2,3), Vec3(1,2,9)) must be false"
    );

    // A PHASE-2 composite reaching the same leaf: this phase's own derivation runs
    // and is marked as it is created, exactly as phase 1's was.
    assert!(
        !call_bool(&mut i, "test.wi1103.reading_nan_eq"),
        "eq(reading(Vec3(nan,..),1), reading(Vec3(nan,..),1)) must be FALSE — a phase-2 \
         composite over a phase-1 partial carrier is itself Partial"
    );
    assert!(
        call_bool(&mut i, "test.wi1103.reading_eq"),
        "eq(reading(Vec3(1,2,3),1), reading(Vec3(1,2,3),1)) must be true"
    );
}

/// The rows themselves: phase 2 neither drops one, nor re-derives a duplicate, nor
/// RECLASSIFIES a carrier.
///
/// Two questions, and the second is the one that only becomes ASKABLE now. (1) Does
/// the row survive? `eq_derive::run` guards each assertion with `sort_provides`, so
/// the second phase must find the phase-1 row and assert nothing — a duplicate would
/// be a second candidate for one `(NonEq, Vec3)` dictionary (058 §4.9). (2) Does the
/// CLASSIFICATION agree across the boundary? Phase 2 recomputes it with phase 1's
/// derived `PartialEq` rows already in the relation, so `build_sort_ops_table` runs
/// ABOVE the classifier having inherited `PartialEq.eq` onto every derived carrier —
/// input the phase-1 classifier did not have. Were that to read as an own `eq`, the
/// carrier would become a lawful-`Eq` BOUNDARY, lose its `NonEq`, and silently launder
/// `eq(Vec3(nan,..), Vec3(nan,..))` back to true. It does not (the eq-dispatch index's
/// own-member route filters the spec op itself), and this pins it. WI-1103's ticket
/// names this suspicion as unreachable BECAUSE THE LOAD FAILED FIRST; it is reachable
/// now, so it is measured rather than left inherited.
///
/// CONTROL — FAILS without the change: phase 2 does not complete, so `expect` panics
/// before any row is compared.
#[test]
fn derived_noneq_rows_survive_the_next_phase_unchanged() {
    let mut kb = phase_one_full_closure();

    let noneq_rows = |kb: &KnowledgeBase| -> Vec<String> {
        let mut v: Vec<String> = provides_rows(kb)
            .into_iter()
            .filter(|s| s.contains("SortView(NonEq,"))
            .collect();
        v.sort();
        v
    };

    let after_one = noneq_rows(&kb);
    assert_eq!(
        after_one.iter().filter(|s| *s == VEC3_NONEQ).count(),
        1,
        "phase 1 must derive exactly one `{VEC3_NONEQ}` row; got {after_one:#?}"
    );

    load_phase_two(&mut kb, USER).expect("phase 2 must load into an already-loaded KB");

    let after_two = noneq_rows(&kb);

    // Nothing phase 1 classified may vanish or double.
    for row in &after_one {
        assert_eq!(
            after_two.iter().filter(|s| *s == row).count(),
            after_one.iter().filter(|s| *s == row).count(),
            "phase 2 changed the multiplicity of `{row}`\nbefore: {after_one:#?}\nafter: {after_two:#?}"
        );
    }
    // ... and the ONLY new row is phase 2's own composite, which reaches the same
    // Float leaf through the phase-1 carrier it wraps. An empty diff here would mean
    // the fixture stopped exercising this phase's derivation.
    let fresh: Vec<&String> = after_two.iter().filter(|s| !after_one.contains(s)).collect();
    assert_eq!(
        fresh,
        vec![&"SortProvidesInfo(sort_ref: Reading, spec: SortView(NonEq, T: Reading))".to_string()],
        "phase 2 must derive exactly its own new composite's NonEq"
    );
}

/// THE CONTROL FOR THE CHANGE ITSELF: the check is not off. A HAND-WRITTEN
/// `fact NonEq[T = Opaque]` over a carrier that backs no `nonEqRefl` — and that the
/// derivation would never classify Partial, since it reaches no `Float` — is refused
/// in phase 2 with the SAME message it gets in phase 1.
///
/// Passes BOTH with and without the change, BY DESIGN — that is what it is for. What
/// it would catch is a fix that exempted provisions wholesale (e.g. "only check rows
/// asserted by THIS phase's source files", which also stops checking every earlier
/// phase's written provisions).
#[test]
fn hand_written_unbacked_provision_is_refused_in_both_phases() {
    const BAD: &str = r#"
namespace test.wi1103bad
  import anthill.prelude.{Int64, NonEq}

  sort Opaque
    entity opaque(n: Int64)
  end

  fact NonEq[T = Opaque]
end
"#;
    let needle = "'test.wi1103bad.Opaque' provides 'anthill.prelude.NonEq' but backs no \
                  operation 'anthill.prelude.NonEq.nonEqRefl'";

    // Phase 1 (one-shot): the reference wording.
    let one_shot = crate::common::try_load_kb_with(BAD)
        .err()
        .expect("a hand-written unbacked NonEq provision must be a load error, one-shot");
    assert!(
        one_shot.iter().any(|e| e.contains(needle)),
        "one-shot load must report the unbacked provision; got {one_shot:#?}"
    );

    // Phase 2: same refusal, same wording.
    let mut kb = phase_one_full_closure();
    let two_phase = load_phase_two(&mut kb, BAD)
        .err()
        .expect("a hand-written unbacked NonEq provision must be a load error in phase 2 too");
    assert!(
        two_phase.iter().any(|e| e.contains(needle)),
        "phase-2 load must report the SAME unbacked provision; got {two_phase:#?}"
    );
}

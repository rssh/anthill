//! WI-M460D — ADDING AN `entity` TO A SPEC MUST NOT HIDE ITS OPERATIONS FROM A
//! `requires` CALLER.
//!
//! §8.6's `exposed` set is the VARIANT-EXPOSURE link's filter: a sort that declares
//! entity constructors leaks *those names and no others* to its enclosing scope. It
//! was applied to every non-enclosing parent instead — and `requires`, `provides` and
//! a wildcard import are all non-enclosing too, so whether a bare member name crossed
//! a `requires` edge depended on whether the target happened to declare a variant.
//! One line apart, measured:
//!
//!   sort Spec { operation f(x: Int64) -> Int64 = x }                    -> reached
//!   sort Spec { entity marker(n: Int64)  operation f(…) = x }           -> REFUSED
//!     "`f` is a member of sort Spec, not in scope as a bare name here"
//!
//! The spec said both things in two paragraphs of one section: step 3(c) filtered
//! every non-enclosing parent by `exposed`, while *Variant exposure* said a sort's
//! operations "are reached via `Sort.op`, `requires`, or wildcard". Only the edge
//! KIND tells them apart, and `is_enclosing` cannot say it — hence
//! `SymbolTable::add_exposure_parent` and `parent_edge_is_exposure_only`.
//!
//! WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT. The fix re-keys TWO arms that
//! share one `exposure_edge` binding, so each is backed out ALONE — widening the
//! binding instead of the arm moves both, and hands this ticket a failure that
//! belongs to the other arm's measurement.
//!
//! ARM 1, the inward reach — restore `!parent.exposed.is_empty() &&
//! !parent.exposed.contains(name)` on every non-enclosing edge. FOUR rows fail, all
//! of them here:
//!         [`a_requires_caller_reaches_a_variant_bearing_specs_operation`]
//!         [`a_wildcard_import_reaches_the_sorts_operations_too`]
//!         [`an_importing_file_reaches_the_sorts_operations_at_its_own_address`]
//!         [`the_two_programs_agree`]
//!   and FIVE pass either way, BY DESIGN — the controls:
//!         [`control_a_requires_caller_reaches_a_variant_less_specs_operation`]
//!           the ticket's OTHER program, one `entity` line apart from the subject.
//!           It is the whole acceptance: the two must AGREE, so a fix that broke
//!           this one would satisfy the subject and still be wrong.
//!         [`control_exposure_still_leaks_a_constructor_to_the_enclosing_scope`]
//!         [`control_exposure_still_does_not_leak_an_operation_to_the_enclosing_scope`]
//!         [`control_a_sibling_sorts_member_may_share_an_exposed_constructors_name`]
//!         [`a_sibling_files_wildcard_import_does_not_lift_the_filter_for_another_file`]
//!           — both its arms expect a refusal, and the blanket filter refuses
//!           everything, so it is green for the WRONG reason under this back-out.
//!           ARM 3 is the back-out that can move it.
//!   Nothing else moves. The whole workspace — 36 test binaries — was run under the
//!   coupled back-out and `wi_tests` was the only binary with a failure in it, so
//!   the strictly-weaker isolated one cannot reach further. The defect is invisible
//!   on the corpus, which is why it went unnoticed until a spec grew a constructor.
//!
//! ARM 2, the WI-999 capture skip — key it on `exposed.contains(name)` alone. In
//! `anthill-core` exactly one row fails, `wi999_name_capture_test::wildcard_import_
//! of_a_variant_bearing_sort_is_a_capture` — the same single row WI-999's own doc
//! names for the `parent_edge_is_imported` conjunct this predicate replaces.
//!
//! ARM 3, the WI-995 file-locality of the new predicate — answer
//! `parent_edge_is_exposure_only` over the RAW origin list rather than the visible
//! ones. In `anthill-core`'s `wi_tests` exactly one row fails,
//! [`a_sibling_files_wildcard_import_does_not_lift_the_filter_for_another_file`], and
//! its "importer present" arm is the one that moves: the file that wrote no import
//! loads clean because a SIBLING file wrote one. Found by `/code-review`, not by the
//! nine rows here — the wildcard row above puts its import in a DIFFERENT namespace,
//! which is the one arrangement where the pair carries no exposure origin at all.
//!
//! DELETING the `exposed` test rather than re-keying it is NOT attributable to
//! [`control_exposure_still_does_not_leak_an_operation_to_the_enclosing_scope`], and
//! saying it were would credit that control with a measurement it cannot make.
//! Measured: 2251 rows of the `wi_tests` binary fail — two thirds of it, and the
//! count moves with the binary — because the STDLIB stops loading
//! ("ambiguous symbol 'eq' in scope 'anthill.prelude.Eq': candidates [PartialEq.eq,
//! Pair.eq, TotalFloat.eq]") — every sort's members leak into its namespace at once.
//! The control fails among them; what it adds is saying WHY in one line, not in 2251.
//!
//! WHAT NOTHING HERE COVERS: the `provides` edge (`wire_provides_scope_parent`) is
//! the same non-enclosing shape and carried the same defect, and it is UNREACHABLE
//! by construction — a `provides` whose target declares constructors is already
//! refused ("declares constructors, which makes it a DATA sort, and nothing is-a a
//! data sort"), so no program can reach that edge with a non-empty `exposed`. It is
//! fixed by the same re-keying and driven by nothing.

use anthill_core::eval::Value;

/// Load, then DRIVE. "It loads clean" is not evidence that the name reached the
/// operation — the whole subject here is which declaration a bare name found.
fn eval_int(src: &str, op: &str, arg: i64) -> i64 {
    let mut interp = crate::common::interp_for(src);
    match interp.call(op, &[Value::Int(arg)]) {
        Ok(Value::Int(n)) => n,
        Ok(other) => panic!("expected Int from {op}, got {}", other.type_name()),
        Err(e) => panic!("{op} failed to evaluate: {e}"),
    }
}

fn eval_int_files(srcs: &[&str], op: &str, arg: i64) -> i64 {
    let mut interp = crate::common::interp_for_files(srcs);
    match interp.call(op, &[Value::Int(arg)]) {
        Ok(Value::Int(n)) => n,
        Ok(other) => panic!("expected Int from {op}, got {}", other.type_name()),
        Err(e) => panic!("{op} failed to evaluate: {e}"),
    }
}

/// One namespace per fixture, and each row in its own: a load error in the subject
/// must not take a control down with it, or 2/2 red proves nothing.
fn spec_and_caller(ns: &str, spec_body: &str) -> String {
    format!(
        r#"
namespace {ns}
  sort Spec
{spec_body}    operation f(x: Int64) -> Int64 = x
  end
  sort User
    requires {ns}.Spec
    entity u(n: Int64)
    operation g(y: Int64) -> Int64 = f(y)
  end
end
"#
    )
}

// ── the ticket's two programs, which must agree ─────────────────────────────

/// CONTROL, and the ticket's first program: a variant-LESS spec's `exposed` set is
/// empty, so the filter never fired and `requires` always reached `f`. This is the
/// arm that made the defect invisible — every stdlib spec (`PartialEq`, `Ord`,
/// `Numeric`, …) declares no variants.
#[test]
fn control_a_requires_caller_reaches_a_variant_less_specs_operation() {
    let src = spec_and_caller("m460d.plain", "");
    assert_eq!(eval_int(&src, "m460d.plain.User.g", 5), 5);
}

/// THE SUBJECT. One `entity` line more than the control, and nothing else changed.
/// Backed out, this fails at LOAD: "`f` is a member of sort Spec, not in scope as a
/// bare name here".
#[test]
fn a_requires_caller_reaches_a_variant_bearing_specs_operation() {
    let src = spec_and_caller("m460d.variant", "    entity marker(n: Int64)\n");
    assert_eq!(
        eval_int(&src, "m460d.variant.User.g", 5),
        5,
        "an unrelated `entity` on the spec must not change what `requires` reaches"
    );
}

/// The acceptance stated as one assertion rather than inferred from two green rows:
/// the two programs must AGREE. Kept because "both pass" is a property of the pair,
/// and a future change that made both wrong in the same way would still be caught by
/// the value.
#[test]
fn the_two_programs_agree() {
    let plain = eval_int(&spec_and_caller("m460d.agree_a", ""), "m460d.agree_a.User.g", 9);
    let variant = eval_int(
        &spec_and_caller("m460d.agree_b", "    entity marker(n: Int64)\n"),
        "m460d.agree_b.User.g",
        9,
    );
    assert_eq!((plain, variant), (9, 9), "adding an `entity` changed the answer");
}

// ── the wildcard form, the other half of §8.6's own sentence ────────────────

/// §8.6: a sort's operations "are reached via `Sort.op`, `requires`, or **wildcard**".
/// The wildcard edge is non-enclosing too, so it was filtered by `exposed` exactly as
/// the `requires` edge was: importing a variant-bearing sort reached its constructors
/// and hid its operations. Backed out, this fails at load on a bare `shade`.
#[test]
fn a_wildcard_import_reaches_the_sorts_operations_too() {
    let src = r#"
namespace m460d.wildlib
  sort Colour
    entity Red(x: Int64)
    operation shade(n: Int64) -> Int64 = n
  end
end
namespace m460d.wild
  import m460d.wildlib.Colour.*
  operation drive(n: Int64) -> Int64 = shade(n)
end
"#;
    assert_eq!(eval_int(src, "m460d.wild.drive", 4), 4);
}

// ── the controls that keep the exposure link itself narrow ──────────────────

/// CONTROL — passes either way. §8.6's leak still happens: a bare constructor name
/// resolves in the ENCLOSING namespace. Without this row, a change that severed the
/// exposure link entirely would satisfy every subject above.
#[test]
fn control_exposure_still_leaks_a_constructor_to_the_enclosing_scope() {
    let src = r#"
namespace m460d.leak
  sort Colour
    entity Red(x: Int64)
    operation shade(n: Int64) -> Int64 = n
  end
  operation drive(n: Int64) -> Int64 =
    match Red(x: n)
      case Red(v) -> v
end
"#;
    assert_eq!(eval_int(src, "m460d.leak.drive", 6), 6);
}

/// CONTROL — passes either way. The exposure link leaks constructor names and
/// nothing else, so a bare `shade` in the enclosing namespace stays refused: this is
/// the row that says in ONE line what deleting the `exposed` test costs. It is not
/// the row that ATTRIBUTES that cost — measured, the deletion takes 2251 rows with
/// it by making the stdlib itself ambiguous (see the file header).
#[test]
fn control_exposure_still_does_not_leak_an_operation_to_the_enclosing_scope() {
    let errs = crate::common::try_load_kb_with(
        r#"
namespace m460d.noleak
  sort Colour
    entity Red(x: Int64)
    operation shade(n: Int64) -> Int64 = n
  end
  operation drive(n: Int64) -> Int64 = shade(n)
end
"#,
    )
    .err()
    .expect("a sort's operation must not leak as a bare name to its enclosing scope");
    assert!(
        errs.iter().any(|e| e.contains("`shade` is a member of sort Colour")),
        "expected the member-not-bare refusal; got {errs:#?}"
    );
}

/// CONTROL — passes either way. §8.7: members and constructors are named per TYPE,
/// so a sibling sort may declare an operation whose name an exposed constructor also
/// carries, and 059 R4's capture rule still stops at the exposure link. This is the
/// row the capture arm's re-keying could have broken — it now asks whether the edge
/// IS the exposure link instead of whether the name happens to be in `exposed`.
#[test]
fn control_a_sibling_sorts_member_may_share_an_exposed_constructors_name() {
    let src = r#"
namespace m460d.sib
  sort Colour
    entity Red(x: Int64)
  end
  sort Box
    entity b(k: Int64)
    operation Red(n: Int64) -> Int64 = 3
  end
  operation drive(n: Int64) -> Int64 = Box.Red(n)
end
"#;
    assert_eq!(eval_int(src, "m460d.sib.drive", 1), 3);
}

// ── WI-995: the widening is the IMPORTING FILE'S, not the address's ─────────
//
// `add_parent_raw` dedups on the whole `ScopeInclusion`, so a wildcard import written
// IN the namespace that declares the variant-bearing sort lands on the SAME
// `(scope, parent)` pair as the exposure link — one entry, two origins. Asking "are
// all this edge's origins `Exposure`" over the RAW list then answers `false` for every
// asking file, and one file's import lifts the `exposed` filter for all of them.
//
// Found by `/code-review` on the first cut of this ticket, with the flip driven: the
// reader below loaded CLEAN, and was refused again the moment the importing file was
// dropped from the load. A foreign import GRANTING a name is the WI-995 rule
// inverted — the direction `import_parent_visible` already guards going the other way.

/// `sort Colour` with a constructor and a member, and two files that read it at the
/// same address — one that writes the wildcard import, one that writes nothing.
const WI995_LIB: &str = r#"
namespace m460d.filelocal
  sort Colour
    entity Red(x: Int64)
    operation shade(n: Int64) -> Int64 = n
  end
end
"#;
const WI995_IMPORTER: &str = r#"
namespace m460d.filelocal
  import m460d.filelocal.Colour.*
  operation viaimport(n: Int64) -> Int64 = shade(n)
end
"#;
const WI995_READER: &str = r#"
namespace m460d.filelocal
  operation reader(n: Int64) -> Int64 = shade(n)
end
"#;

/// CONTROL for the row below, and what keeps that row from being satisfied by any
/// change that simply re-refuses everything: the file that WROTE the import still
/// reaches the member, at the same address, in the same load.
#[test]
fn an_importing_file_reaches_the_sorts_operations_at_its_own_address() {
    assert_eq!(
        eval_int_files(&[WI995_LIB, WI995_IMPORTER], "m460d.filelocal.viaimport", 4),
        4
    );
}

/// THE SUBJECT: a file that wrote no import is refused, and stays refused whether or
/// not a SIBLING file at the same address wrote one — its answer must not depend on
/// somebody else's text. Backed out (answer `parent_edge_is_exposure_only` over the
/// raw origin list rather than the visible ones): the "importer present" arm fails and
/// the fixture loads clean, while the "importer absent" arm passes — which is why both
/// arms are here, and why the pair is what says the answer stopped moving.
#[test]
fn a_sibling_files_wildcard_import_does_not_lift_the_filter_for_another_file() {
    for (label, files) in [
        (
            "importer present",
            vec![WI995_LIB, WI995_IMPORTER, WI995_READER],
        ),
        ("importer absent", vec![WI995_LIB, WI995_READER]),
    ] {
        let errs = crate::common::try_load_kb_with_files(&files)
            .err()
            .unwrap_or_else(|| {
                panic!("{label}: a file that wrote no import must not reach `shade`")
            });
        assert!(
            errs.iter()
                .any(|e| e.contains("`shade` is a member of sort Colour")),
            "{label}: expected the member-not-bare refusal; got {errs:#?}"
        );
    }
}

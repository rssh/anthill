//! WI-20260903-W9D4Z — ONE AUTHORED MISTAKE IS DIAGNOSED ONCE.
//!
//! A load error the reader cannot tell apart from one already reported — same file, same
//! `line:col`, same sentence — is now reported once. The rule belongs to the DIAGNOSTIC
//! CHANNEL, not to any producer, and it is applied at the load phase's two exits
//! (`dedup_rendered_load_errors`).
//!
//! ── WHY IT SURFACED NOW ──────────────────────────────────────────────────────
//!
//! WI-20260903-FCZ3N made a fired `[simp]` rule's RHS keep the span its AUTHOR wrote.
//! That is the whole point of that ticket — before it, N firings of one rule carried
//! their N REDEXES' distinct spans, so the copies were distinguishable and every one of
//! them pointed at a line where the mistake is not written. Moving the location to the
//! right place left the COUNT as the residue:
//!
//! ```text
//!   rule bad(?x) <=> sink("nope") [simp]
//!   operation c(n: Int64) -> Int64 = bad(n) + bad(n)
//!
//!   4:20: type mismatch in sink.r (op-arg): expected Int64, got String
//!   4:20: type mismatch in sink.r (op-arg): expected Int64, got String     <- byte-identical
//! ```
//!
//! ── THE CLAIM IS INDISTINGUISHABILITY, NOT IMPOSSIBILITY ────────────────────
//!
//! The two errors above ARE two findings — two redexes, each independently type-checked.
//! What is asserted is not that such a pair cannot arise (it plainly can, and this is
//! how) but that PRINTING THE SECOND ONE TELLS THE READER NOTHING: same sentence, same
//! `path:line:col`, nothing to separate the copies. What must NOT collapse is a pair the
//! reader COULD separate — hence [`two_written_copies_are_two_diagnoses`] and
//! [`two_files_reporting_at_the_same_offset_stay_two`], which are this file's controls
//! and are green under every back-out below by design.
//!
//! ── THE CENSUS THE TICKET ASKED FOR, RUN BEFORE THE CHANGE LANDED ───────────
//!
//! The whole workspace suite (36 binaries, 6 358 tests) was run with a probe at both
//! exits of `load_phase_inner` recording every batch containing two errors with the same
//! `(file, rendering)`. **SEVEN GROUPS, ALL n = 2, IN FOUR TEST FILES** — and every one
//! of them is a second instance of this same shape, not a suite measuring the duplicate:
//!
//! | groups | diagnostic | the two copies come from | pinned here by |
//! |---|---|---|---|
//! | 5 | `invalid type argument: 'anthill.prelude.Cell' has no type parameter named 'W'` / `… is over-applied` on `is_modifiable(Cell[…])` — `wi709_type_arg_validation_test`, `wi710_rule_body_type_arg_test`, `wi839_call_bracket_channel_test` | the per-file LOADER **and** `type_check_sorts` | [`one_written_type_argument_read_by_two_passes_is_one_diagnosis`] |
//! | 2 | `type mismatch in div.effects (op-effects): expected declared: [], got undeclared effect: …` — `wi_vt8cf_division_tower_test` | `type_check_sorts`, TWICE | [`a_span_less_diagnostic_raised_twice_by_one_pass_is_one`] |
//!
//! NONE of the four asserts a COUNT: `wi709`/`wi710`/`wi839` use `errs.iter().any(…)` and
//! `wi_vt8cf` uses `!errs.is_empty()`, so no row was measuring the duplication. That is
//! what the full-suite run after the change confirms — 0 failures.
//!
//! The two families are why this is the CHANNEL's rule and not a producer's. The
//! `Cell[W]` pair crosses the per-file/whole-KB boundary, so `dedup_load_errors` — which
//! runs per file, before the typer exists — cannot see both copies; the `div.effects`
//! pair is raised twice inside ONE pass, which no cross-pass key would catch either.
//! Producers that had noticed their own duplicates collapsed them by hand for exactly
//! this reason (`check_rule_body_goals`, `check_use_site_requires_eq`, whose comments
//! said the producer was the only place that could). Those keys stay — they are
//! `SourceSpan`-based and so hold regardless of how a message renders — with this as the
//! backstop under all of them.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ───────────────────────────
//!
//! **AXIS 1 — THE DEDUP ITSELF.** `dedup_rendered_load_errors` returning `errors`
//! unchanged. **EXACTLY 3 ROWS FAIL** of the 4 072 in `wi_tests`, all in this file, and
//! each for a different producer pairing:
//!
//! * [`one_simp_mistake_fired_at_two_sites_is_one_diagnosis`] — 2 errors, then 3 at three
//!   firing sites. The ticket's own repro.
//! * [`one_written_type_argument_read_by_two_passes_is_one_diagnosis`] — 2 errors: the
//!   LOADER's and the TYPER's, which no per-file dedup can pair.
//! * [`a_span_less_diagnostic_raised_twice_by_one_pass_is_one`] — 2 errors from one pass,
//!   and span-LESS, so it also measures the arm of the key that renders a bare message.
//!
//! Nothing outside `wi_tests` can fail under this back-out, and that is an argument
//! rather than a second measurement: backing the dedup out restores the tree the census
//! was taken on, and that tree's full 36-binary run was green. The census is the complete
//! population of what the change touches, and none of the four files it names asserts a
//! count. What IS measured over all 36 binaries is the FORWARD direction — the change
//! itself, run green below.
//!
//! **AXIS 2 — FILE IDENTITY IN THE KEY.** Keying on the rendering ALONE (dropping the
//! source address). **EXACTLY 2 ROWS FAIL** over `wi_tests` (4 072), and only one of them
//! is this file's:
//!
//! * [`two_files_reporting_at_the_same_offset_stay_two`] — two PATHLESS files whose
//!   errors render byte-for-byte alike collapse to one, losing a diagnostic outright.
//! * `wi835_use_site_requires_scope_test::one_refusal_per_site_including_across_files_at_equal_offsets`
//!   — the same hazard, found and fixed at a PRODUCER key in WI-835 ("a site key that
//!   carried only the offsets, and not the `SourceId`, collapsed these two into one and
//!   silently dropped the second file's diagnostic"). That an existing row written
//!   against a producer catches this back-out is the evidence that the file half of the
//!   key is load-bearing and not decoration.
//!
//! It is NOT a limit the per-file `dedup_load_errors` had: that one is reached only
//! through `stamped_file_errors`, which is handed one file's errors at a time, so it
//! never saw a cross-file pair to collapse — MEASURED at 2, with and without this
//! change, on two unlabeled `TypedPatternNotEnforced` rules at equal offsets. (That
//! measurement corrected the claim to the contrary in that variant's own doc.) The
//! hazard is NEW with a batch-wide key, and answered where it arises.
//!
//! **AXIS 3 — THE RENDERING IN THE KEY.** Keying on `(file, span)` and dropping the
//! message. **12 ROWS FAIL** over `wi_tests`, and TEN of them are pre-existing rows in
//! EIGHT files this change never touches — which is the measurement that says the message
//! half is load-bearing, not a preference:
//!
//! ```text
//!   wi347_override_refinement_test::one_misspelling_in_both_clause_lists_is_reported_twice
//!   wi792_function_value_args_test::{positional,named}_argument_types_are_checked_at_a_…
//!   wi1100_call_arity_test::a_named_argument_naming_no_parameter_leaves_a_slot_unfilled
//!   wi994_variant_exposure_test::one_variant_name_exposed_by_two_namespaces_is_ambiguous
//!   wi749_rule_ref_zero_arg_member_test::wi749_unresolvable_receiver_stays_loud
//!   wi_7x7nk_projection_names_no_column_test::x7nk_a_mixed_projection_answers_each_field_…
//!   wi_w6jh0_companion_receiver_bracket_test  (3 rows)
//! ```
//!
//! …plus this file's [`two_findings_at_one_span_are_two_diagnoses`] and
//! [`a_span_less_diagnostic_raised_twice_by_one_pass_is_one`] (every span-LESS error keys
//! alike under a span-only key, so `div`, `mod` and `rem` merge into one). §8.5's rule
//! that "a diagnostic list is never silently truncated" (WI-20260830-JM7A8) is the same
//! promise stated in the spec.
//!
//! GREEN UNDER ALL THREE BACK-OUTS, BY DESIGN — the controls:
//! [`two_written_copies_are_two_diagnoses`] (two spans, so nothing to collapse — the row
//! that a dedup collapsing on the MESSAGE alone would fail) and
//! [`distinct_mistakes_are_all_still_reported`] (three offsets, three errors).

use crate::common::{try_load_kb_with, try_load_kb_with_files};

/// `line:col` of `needle`'s first occurrence, in the 1-based form the loader prefixes its
/// error strings with. Computed from the fixture so an edit to the skeleton moves the
/// expectation with it instead of silently asserting about a line that is now something
/// else. (Same helper, same reason, as `wi_fcz3n_simp_rhs_occurrence_test`.)
fn line_col(src: &str, needle: &str) -> String {
    let idx = src
        .find(needle)
        .unwrap_or_else(|| panic!("fixture does not contain {needle:?}"));
    let line = src[..idx].matches('\n').count() + 1;
    let col = idx - src[..idx].rfind('\n').map_or(0, |p| p + 1) + 1;
    format!("{line}:{col}")
}

/// [`line_col`] of the `n`-th (0-based) occurrence — [`line_col`] itself always finds the
/// first, which for a fixture that writes one mistake TWICE would name the same place
/// twice and quietly assert nothing about the second.
fn nth_line_col(src: &str, needle: &str, n: usize) -> String {
    let idx = src
        .match_indices(needle)
        .nth(n)
        .unwrap_or_else(|| panic!("fixture has no occurrence {n} of {needle:?}"))
        .0;
    line_col(src, &src[idx..])
}

fn errs(src: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_default()
}

/// The ticket's program: ONE written `sink("nope")`, reached through a `[simp]` rule that
/// the consumer fires N times.
fn fired_n_times(calls: &str) -> String {
    format!(
        "namespace zzw9\n  import anthill.prelude.Int64\n  \
         operation sink(r: Int64) -> Int64 = r\n  \
         rule bad(?x) <=> sink(\"nope\") [simp]\n  \
         operation c(n: Int64) -> Int64 = {calls}\nend\n"
    )
}

/// **A — THE HEADLINE.** One authored mistake, N firing sites, ONE diagnosis — and it is
/// at the place the author wrote it, which is what WI-20260903-FCZ3N established and what
/// makes the copies indistinguishable in the first place.
///
/// N is varied (1, 2, 3) rather than fixed at 2: a repair that merely dropped the LAST
/// error, or kept a fixed number, passes the two-site row and fails here.
///
/// RED UNDER AXIS 1 at `n = 2` (2 errors) and `n = 3` (3).
#[test]
fn one_simp_mistake_fired_at_two_sites_is_one_diagnosis() {
    let at_rhs = line_col(&fired_n_times("bad(n)"), "sink(\"nope\")");
    for (sites, calls) in [
        (1, "bad(n)"),
        (2, "bad(n) + bad(n)"),
        (3, "bad(n) + bad(n) + bad(n)"),
    ] {
        let src = fired_n_times(calls);
        let e = errs(&src);
        assert_eq!(
            e.len(),
            1,
            "one written `sink(\"nope\")` fired at {sites} site(s) is ONE diagnosis, and \
             the copies carry nothing to tell them apart: {e:#?}"
        );
        assert!(
            e[0].starts_with(&format!("{at_rhs}: ")),
            "…reported where the author wrote it ({at_rhs}), not at a redex: {:?}",
            e[0]
        );
    }
}

/// **B — THE CONTROL, AND THE POINT.** Two mistakes the author actually wrote TWICE stay
/// two diagnoses, because the reader can separate them: two different `line:col`.
///
/// This is the row that fails for a dedup keyed on the MESSAGE alone, which is the shape
/// this change would otherwise be indistinguishable from. GREEN UNDER ALL THREE BACK-OUTS by
/// design — with no dedup at all there are still exactly two.
#[test]
fn two_written_copies_are_two_diagnoses() {
    const SRC: &str = "namespace zzw9b\n  import anthill.prelude.Int64\n  \
                       operation sink(r: Int64) -> Int64 = r\n  \
                       operation c2(n: Int64) -> Int64 = sink(\"nope\") + sink(\"nope\")\nend\n";
    let e = errs(SRC);
    assert_eq!(
        e.len(),
        2,
        "the author wrote the mistake twice, at two places — both must be reported: {e:#?}"
    );
    let first = line_col(SRC, "sink(\"nope\")");
    let second = nth_line_col(SRC, "sink(\"nope\")", 1);
    assert_ne!(
        first, second,
        "the fixture must put the two copies at two places, or it controls for nothing"
    );
    for at in [&first, &second] {
        assert!(
            e.iter().any(|x| x.starts_with(&format!("{at}: "))),
            "expected a diagnostic at {at}, got {e:#?}"
        );
    }
}

/// **C — THE CROSS-PASS INSTANCE**, and the reason the per-file [`dedup_load_errors`]
/// could not own this. ONE written `Cell[W = Int64]` is read by the LOADER and again by
/// `type_check_sorts`; the loader's dedup runs per file, before the typer exists, so it
/// never sees the pair. Five of the census's seven groups are this shape.
///
/// RED UNDER AXIS 1: 2 errors, byte-identical.
#[test]
fn one_written_type_argument_read_by_two_passes_is_one_diagnosis() {
    const SRC: &str = "namespace zzw9c\n  import anthill.prelude.{Cell, Int64, Bool}\n  \
                       import anthill.reflect.{is_modifiable}\n  \
                       operation ask() -> Bool = is_modifiable(Cell[W = Int64])\nend\n";
    let e = errs(SRC);
    assert_eq!(
        e.len(),
        1,
        "`Cell[W = Int64]` is written ONCE — the loader and the typer each read it: {e:#?}"
    );
    let at = line_col(SRC, "Cell[W = Int64]");
    assert!(
        e[0].contains("no type parameter named 'W'") && e[0].starts_with(&format!("{at}: ")),
        "…and the surviving one is the diagnostic, at the written type: {:?}",
        e[0]
    );
}

/// **D — THE INTRA-PASS INSTANCE, AND THE SPAN-LESS ARM.** `type_check_sorts` raises the
/// undeclared-effect mismatch for one operation TWICE in a single pass, so no cross-pass
/// key would catch it either. It also carries NO span, so it exercises the branch of the
/// key that renders a bare message with no `line:col` — where two copies have only the
/// sentence and the file to be told apart by.
///
/// RED UNDER AXIS 1: 2 errors per operation.
#[test]
fn a_span_less_diagnostic_raised_twice_by_one_pass_is_one() {
    const SRC: &str = "\
namespace zzw9d
  import anthill.prelude.{Int64, Numeric, PartialOrd, EuclideanDomain}
  sort Money
    entity Money(cents: Int64)
    operation add(a: Money, b: Money) -> Money = Money(cents: a.cents + b.cents)
    operation sub(a: Money, b: Money) -> Money = Money(cents: a.cents - b.cents)
    operation mul(a: Money, b: Money) -> Money = Money(cents: a.cents * b.cents)
    operation zero() -> Money = Money(cents: 0)
    operation div(a: Money, b: Money) -> Money = Money(cents: a.cents / b.cents)
    operation mod(a: Money, b: Money) -> Money = Money(cents: a.cents % b.cents)
  end
  fact PartialOrd[T = Money]
  fact Numeric[T = Money]
  fact EuclideanDomain[T = Money]
end
";
    let e = errs(SRC);
    for op in ["div", "mod"] {
        let hits: Vec<&String> = e
            .iter()
            .filter(|x| x.contains(&format!("type mismatch in {op}.effects (op-effects)")))
            .collect();
        assert_eq!(
            hits.len(),
            1,
            "`{op}` declares no effects and its body raises one — ONE undeclared-effect \
             diagnosis, raised twice by one pass: {e:#?}"
        );
        assert!(
            !hits[0].starts_with(|c: char| c.is_ascii_digit()),
            "the fixture must keep this diagnostic SPAN-LESS — a located one is prefixed \
             `line:col: ` — or it stops measuring the bare-message arm of the key: {:?}",
            hits[0]
        );
    }
}

/// **E — THE CONTROL FOR FILE IDENTITY**, and the only row in this file that measures it
/// (`wi835`'s own cross-file row measures the same hazard from the producer side). Two PATHLESS
/// files (a CLI string, a test fixture) whose mistakes sit at the SAME byte offset and
/// whose messages name the same SHORT operation name render byte-for-byte alike. They are
/// two diagnostics about two files and must both survive — a key that used the rendering
/// alone would silently drop one.
///
/// The identical rendering is ASSERTED rather than assumed: qualify that `sink.r` and the
/// two stop colliding, and this row would go on passing while measuring nothing.
///
/// RED UNDER AXIS 2 (1 error). Green under axes 1 and 3 — with no dedup at all there are
/// two, and a span-only key still tells the two FILES apart by their addresses.
#[test]
fn two_files_reporting_at_the_same_offset_stay_two() {
    // Byte-for-byte the same length, the same short op name, the mistake at the same
    // offset — everything but the namespace, which never reaches the message.
    const A: &str = "namespace zza\n  import anthill.prelude.Int64\n  \
                     operation sink(r: Int64) -> Int64 = r\n  \
                     operation c() -> Int64 = sink(\"nope\")\nend\n";
    const B: &str = "namespace zzb\n  import anthill.prelude.Int64\n  \
                     operation sink(r: Int64) -> Int64 = r\n  \
                     operation c() -> Int64 = sink(\"nope\")\nend\n";
    assert_eq!(A.len(), B.len(), "the two files must align byte-for-byte");
    let e = try_load_kb_with_files(&[A, B]).err().unwrap_or_default();
    assert_eq!(
        e.len(),
        2,
        "two files, two mistakes — neither may be dropped for looking like the other: \
         {e:#?}"
    );
    assert_eq!(
        e[0], e[1],
        "THE FIXTURE'S OWN PREMISE: the two renderings must be byte-identical, or this \
         row controls for nothing"
    );
}

/// **F — THE OTHER CONTROL.** Distinct mistakes are all still reported. A dedup that
/// over-reached — collapsing on the message, or on the operation — would report one.
/// GREEN UNDER ALL THREE BACK-OUTS by design: there is nothing here to collapse.
#[test]
fn distinct_mistakes_are_all_still_reported() {
    const SRC: &str = "namespace zzw9f\n  import anthill.prelude.Int64\n  \
                       operation sink(r: Int64) -> Int64 = r\n  \
                       operation c1() -> Int64 = sink(\"a\")\n  \
                       operation c2() -> Int64 = sink(\"bb\")\n  \
                       operation c3() -> Int64 = sink(\"ccc\")\nend\n";
    let e = errs(SRC);
    assert_eq!(
        e.len(),
        3,
        "three separately written mistakes are three diagnoses: {e:#?}"
    );
    for needle in ["sink(\"a\")", "sink(\"bb\")", "sink(\"ccc\")"] {
        let at = line_col(SRC, needle);
        assert!(
            e.iter().any(|x| x.starts_with(&format!("{at}: "))),
            "expected a diagnostic at {at} for {needle}, got {e:#?}"
        );
    }
}

/// **G — THE CONTROL FOR THE MESSAGE HALF OF THE KEY.** Two DIFFERENT findings can share
/// one span: `two("x", "y")` mistypes both arguments, and both diagnostics are reported
/// at the CALL — same `line:col`, different sentences (`two.a` and `two.b`). The reader
/// can separate them, so both are owed, and §8.5's standing rule that "a diagnostic list
/// is never silently truncated" (WI-20260830-JM7A8) says so for the same population.
///
/// RED UNDER AXIS 3 — keying on `(file, span)` and dropping the rendering, which reports
/// ONE and silently drops the other. No other row in this file catches that: every
/// duplicate the change collapses shares its message too, so a span-only key passes A, C
/// and D and loses a diagnostic in silence.
#[test]
fn two_findings_at_one_span_are_two_diagnoses() {
    const SRC: &str = "namespace zzw9g\n  import anthill.prelude.{Int64, String}\n  \
                       operation two(a: Int64, b: Int64) -> Int64 = a + b\n  \
                       operation c() -> Int64 = two(\"x\", \"y\")\nend\n";
    let e = errs(SRC);
    assert_eq!(
        e.len(),
        2,
        "both arguments are mistyped — two findings, and they happen to share the call's \
         span: {e:#?}"
    );
    let at = line_col(SRC, "two(\"x\", \"y\")");
    for (i, param) in ["two.a", "two.b"].iter().enumerate() {
        assert!(
            e.iter().any(|x| x.contains(param)),
            "expected the finding for {param}, got {e:#?}"
        );
        assert!(
            e[i].starts_with(&format!("{at}: ")),
            "THE FIXTURE'S OWN PREMISE: both findings must be AT THE SAME PLACE ({at}), \
             or this row stops separating the message half of the key from the span \
             half: {:?}",
            e[i]
        );
    }
}

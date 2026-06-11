//! WI-440: the `-Modify[binder]` CHECKING direction — the slice WI-353 left
//! out. A call site passing an eta'd operation into a callback parameter
//! validates the op's declared effect row against the parameter's arrow row,
//! with the two binder spaces aligned POSITIONALLY (the declared row's labels
//! name the callback's `CallbackParam` places `<op>.f.x`; the argument op's
//! row names its OWN param places `<pred>.c` — param i ↔ param i).
//!
//! Row-openness decision (recorded in the WI): an absence-only annotation
//! (`@ -Modify[x]`) is a CLOSED row carrying the lacks atom; openness is
//! written EXPLICITLY with a row variable (`@ {Eff, -Modify[x]}`). An
//! implicit fresh tail was tried and reverted — the minted var is unnameable,
//! so a HOF APPLYING the callback surfaced an undeclared-effect `?ρ` it had
//! no syntax to declare.

fn load_errors(extras: &[&str]) -> Vec<String> {
    crate::wi424_iterable_members_test::load_errors(extras)
}

/// Shared fixture: a Beep effect, a violating / a noisy / a pure callback.
const FIXTURE: &str = r#"
  import anthill.prelude.{Effect, Unit, Int64, Cell, Modify}
  sort Beep end
  fact Effect[T = Beep]
  operation bad(c: Cell[V = Int64]) -> Unit effects Modify[c] = Cell.set(c, 1)
  operation noisy(c: Cell[V = Int64]) -> Unit effects Beep = ()
  operation pure_cb(c: Cell[V = Int64]) -> Unit = ()
"#;

/// THE violation: a pred that writes through its argument is REJECTED against
/// a `-Modify[x]` callback param (closed absence-only form).
#[test]
fn modifying_callback_rejected_against_lacks() {
    let src = format!(
        r#"
namespace wi440.lacks
{FIXTURE}
  operation taker(f: (x: Cell[V = Int64]) -> Unit @ -Modify[x]) -> Unit = ()
  operation boom() -> Unit = taker(bad)
end
"#
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("lack") && e.contains("Modify")),
        "Modify[c] callback vs -Modify[x] param must be rejected with the \
         lacks-constraint message; got: {errs:?}",
    );
}

/// The violation under the EXPLICIT open form `{{Eff, -Modify[x]}}` — the
/// absent label is checked before tail absorption.
#[test]
fn modifying_callback_rejected_against_open_lacks() {
    let src = format!(
        r#"
namespace wi440.openlacks
{FIXTURE}
  operation taker[Eff](f: (x: Cell[V = Int64]) -> Unit @ {{Eff, -Modify[x]}}) -> Unit = ()
  operation boom() -> Unit = taker(bad)
end
"#
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().any(|e| e.contains("lack") && e.contains("Modify")),
        "Modify[c] vs {{Eff, -Modify[x]}} must be rejected via the absent \
         label, not absorbed by the tail; got: {errs:?}",
    );
}

/// The open-row reading: an UNRELATED effect (Beep) is absorbed by the
/// explicit row-var tail — accepted; a pure callback is accepted everywhere.
#[test]
fn unrelated_effect_accepted_under_open_row() {
    let src = format!(
        r#"
namespace wi440.open
{FIXTURE}
  operation taker[Eff](f: (x: Cell[V = Int64]) -> Unit @ {{Eff, -Modify[x]}}) -> Unit = ()
  operation ok_noisy() -> Unit = taker(noisy)
  operation ok_pure() -> Unit = taker(pure_cb)
end
"#
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "a Beep callback must be absorbed by the {{Eff | …}} tail and a pure \
         callback accepted; got: {errs:?}",
    );
}

/// A CLOSED row (absence-only or `{{}}`) admits no unrelated effect: the
/// callback's Beep would escape the WI-352/353 boundary propagation (which
/// derives from the DECLARED callback row), so it is rejected loudly.
#[test]
fn unrelated_effect_rejected_against_closed_row() {
    let src = format!(
        r#"
namespace wi440.closed
{FIXTURE}
  operation taker(f: (x: Cell[V = Int64]) -> Unit @ -Modify[x]) -> Unit = ()
  operation taker2(f: (x: Cell[V = Int64]) -> Unit @ {{}}) -> Unit = ()
  operation boom() -> Unit = taker(noisy)
  operation boom2() -> Unit = taker2(noisy)
end
"#
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.iter().filter(|e| e.contains("closed row") && e.contains("Beep")).count() >= 2,
        "a Beep callback must be rejected against BOTH closed forms \
         (-Modify[x] and {{}}); got: {errs:?}",
    );
}

/// Binder ALIGNMENT accepts the each-style positive case: the declared row
/// PRESENTS `Modify[a]` (the callback may modify its element), and an op
/// declaring `Modify[c]` on its own param is covered (param 0 ↔ param 0).
/// An uncovered unrelated effect on the same closed row stays rejected.
#[test]
fn aligned_modify_covered_by_declared_present() {
    let src = format!(
        r#"
namespace wi440.aligned
{FIXTURE}
  operation taker(f: (a: Cell[V = Int64]) -> Unit @ Modify[a]) -> Unit = ()
  operation ok_aligned() -> Unit = taker(bad)
end
"#
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "Modify[c] must align to the declared Modify[a] (param 0 ↔ param 0) \
         and be accepted; got: {errs:?}",
    );
}

/// Loud-error: a typo'd place in an absence label is load-BLOCKING (the
/// constraint would be vacuous), not the advisory unresolved-name warning.
#[test]
fn unresolved_place_in_absence_is_load_blocking() {
    let src = r#"
namespace wi440.typo
  import anthill.prelude.{Unit, Int64, Cell, Modify}
  operation taker(f: (x: Cell[V = Int64]) -> Unit @ -Modify[zzz_no_such]) -> Unit = ()
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.iter().any(|e| e.contains("unresolved place") && e.contains("zzz_no_such")
            && e.contains("vacuous")),
        "a typo'd place in -Modify[…] must be the load-blocking \
         UnresolvedEffectPlace error; got: {errs:?}",
    );
}

/// The `@ {{}}` surface form parses (WI-440 grammar fix: `commaSep`, so the
/// explicit closed-empty row no longer error-recovers into a zero-width
/// `simple_type`) and a pure callback conforms to it.
#[test]
fn empty_braced_row_parses_and_accepts_pure() {
    let src = format!(
        r#"
namespace wi440.emptyrow
{FIXTURE}
  operation taker(f: (x: Cell[V = Int64]) -> Unit @ {{}}) -> Unit = ()
  operation ok() -> Unit = taker(pure_cb)
end
"#
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "`@ {{}}` must parse as the closed-empty row and accept a pure \
         callback; got: {errs:?}",
    );
}

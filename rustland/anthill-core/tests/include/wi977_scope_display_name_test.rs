//! WI-977 — WHAT WE CALL A SCOPE IN A DIAGNOSTIC: its QUALIFIED name (spec §8.6,
//! "How a diagnostic names a scope").
//!
//! Rustland had THREE derivations of that name and they did not agree. `load.rs`
//! answered the LOCAL name at `Loader::scope_display_name` and again in an
//! open-coded copy inside `forbid_internal_import`, while `scope_qualified_name`
//! answered the qualified one — so `wi997_declaration_ledger_test` pinned both
//! spellings eleven lines apart, `in scope 'wi997.sib'` on the duplicate-declaration
//! row and a bare `in scope 'peek'` on the unresolved-name rows. A fourth site, the
//! typer's `TypeError::ForbiddenInternalField` → `LoadError` conversion, filled the
//! scope slot with the literal string `"another scope"`, which rendered as
//! `cannot be referenced from scope 'another scope'` — prose in a name slot, reading
//! as a scope actually so named. All four now ask `KnowledgeBase::scope_display_name`.
//!
//! WHAT FAILS WHEN THE CHANGE IS BACKED OUT — MEASURED, by restoring each of the four
//! sites to the answer it gave before and re-running, not predicted:
//!
//! * Full back-out (all four sites): 5 fail, 2 pass. The five are
//!   `two_sibling_scopes_are_told_apart`, `an_unresolved_name_names_the_scope_qualified`,
//!   `a_forbidden_internal_import_names_the_importing_scope`,
//!   `a_hidden_field_projection_names_the_referencing_scope` and
//!   `no_diagnostic_invents_a_scope_named_another_scope`.
//! * Typer half alone (`"another scope"` restored, the two `load.rs` sites left
//!   qualified): exactly 2 fail — the last two of that list. The WI-369 suite that
//!   OWNS this diagnostic passes 8/8 through it, because it asserts
//!   `contains("internal") && contains("v")`, which the fabricated name satisfies.
//!
//! THE ROWS THAT PASS EITHER WAY, and why they are not evidence for the SPELLING:
//!
//! * `a_duplicate_declaration_row_was_already_qualified` — the stated CONTROL. That
//!   row read `scope_qualified_name`, the one derivation of the three that was
//!   already right, so it is unaffected by design.
//! * `the_global_scope_renders_its_reserved_spelling` — passes under back-out only
//!   because the back-out was simulated by restoring the four ANSWERS while leaving
//!   `KnowledgeBase::scope_display_name` in place. A true revert deletes that method
//!   and this test would not compile. It measures the helper's global-scope arm.
//! * `control_a_top_level_projection_of_a_public_field_still_loads` — the control for
//!   the encapsulation repair below, not for the spelling.
//!
//! `two_sibling_scopes_are_told_apart` is the sharpest of the five: it does not depend
//! on any particular path spelling, only on the two rows DIFFERING, and under the
//! local-name spelling both render `in scope 'Holder'` byte-for-byte.
//!
//! A SECOND DEFECT, FOUND BY `/code-review` ON THIS TICKET'S OWN DIFF and repaired
//! here rather than filed: carrying the scope out of `hidden_field_owner` first made
//! its absence a silent skip (`let scope = scope?`), which documented as an invariant
//! what was really a measured hole in WI-369 — a projection of an `internal` field
//! written at a file's TOP LEVEL was never refused, because
//! `internal_field_hidden_from`'s `None` arm answered "not hidden". Top-level code is
//! written in the GLOBAL scope and §8.6 puts that outside the declaring scope, so the
//! `None` now resolves there instead of skipping.
//! `a_top_level_projection_of_an_internal_field_is_refused` fails against the old
//! permissive arm; its control fails against the over-broad "no enclosing sort ⇒
//! always hidden" repair.
//!
//! A THIRD DEFECT, from the same review, same repair-in-place: naming the scope made
//! the typer's answer COMPARABLE to the loader's for the first time, and they
//! disagreed — the typer read `TypingEnv::enclosing_sort` (the SORT) while the loader
//! reads `current_scope` (the OPERATION), so one file reported two scopes for one
//! body. `TypingEnv::referencing_scope` prefers the enclosing OPERATION, which the env
//! already carried as `enclosing_op`. Pinned by
//! `the_typer_and_the_loader_name_the_same_scope_for_the_same_code`; its control,
//! `control_an_operation_still_sees_its_own_sorts_internal_field`, is what rejects a
//! narrowing that broke visibility rather than just renaming it.
//!
//! AND A REGRESSION THIS TICKET ITSELF CAUSED, caught by the third review pass, which
//! is the reason two of the rows below are about RULES. "The scope this code is
//! written in" has THREE answers, not two: an operation body, a rule body, and
//! neither. `set_enclosing_sort` has one caller (the operation-body loop), so every
//! RULE body answered `None` — and once `None` meant the global scope, a rule inside
//! the declaring sort projecting its own `internal` field became a hard load error.
//! The workspace stayed green at 4947 tests through it, because nothing projected an
//! internal field from a rule body. `TypingEnv::rule_scope` (the rule's `domain`)
//! is the third answer; `a_rule_inside_the_declaring_sort_sees_its_internal_field`
//! and `a_rule_outside_the_declaring_sort_is_refused_naming_the_rules_scope` are the
//! rows that would have caught it.

use crate::common::try_load_kb_with_files;

/// A sort with an `internal` carrier constructor, plus a public way to build it.
/// Mirrors WI-369's `BOX_SRC` — the diagnostics under test are that ticket's.
const BOX: &str = r#"
sort wi977.box.Box
  import anthill.prelude.Int64
  internal entity mk(v: Int64)
  operation make(x: Int64) -> Box
  =
    mk(v: x)
end
"#;

/// The same shape with a PUBLIC carrier, for the control on the top-level row:
/// `internal` is what must be refused there, not projection-from-top-level.
const OPEN: &str = r#"
sort wi977.open.Open
  import anthill.prelude.Int64
  entity omk(w: Int64)
end
"#;

fn errors_of(sources: &[&str]) -> Vec<String> {
    match try_load_kb_with_files(sources) {
        Ok(_) => Vec::new(),
        Err(errs) => errs,
    }
}

/// Every `in scope '…'` / `from scope '…'` name the given sources' diagnostics render,
/// in order. The tests assert on THESE rather than on "an error came back": a load
/// that fails for the right reason with the wrong scope name is the defect.
fn scope_names_in(sources: &[&str]) -> Vec<String> {
    errors_of(sources)
        .iter()
        .filter_map(|e| {
            let at = e.find("in scope '").map(|i| i + "in scope '".len()).or_else(|| {
                e.find("from scope '").map(|i| i + "from scope '".len())
            })?;
            let rest = &e[at..];
            rest.find('\'').map(|end| rest[..end].to_string())
        })
        .collect()
}

/// THE ARGUMENT FOR QUALIFIED, driven: two `sort Holder`s in sibling namespaces, the
/// same unresolved name in each. The two refusals must be TELLABLE APART.
///
/// Under the local-name spelling both rendered `unresolved name 'Missing' in scope
/// 'Holder'` — identical strings for two different scopes, so the message did not
/// locate the error. This test fails when the change is backed out without depending
/// on any particular path spelling.
#[test]
fn two_sibling_scopes_are_told_apart() {
    let names = scope_names_in(&[r#"
namespace wi977.left
  sort Holder
    entity h(n: Missing)
  end
end
"#, r#"
namespace wi977.right
  sort Holder
    entity h(n: Missing)
  end
end
"#]);
    assert_eq!(
        names,
        vec!["wi977.left.Holder", "wi977.right.Holder"],
        "two sibling `Holder` scopes must render distinctly; a local name makes \
         both rows `Holder` and the reader cannot tell which one refused",
    );
}

/// `UnresolvedName` in a nested scope names the whole path, not the last segment.
#[test]
fn an_unresolved_name_names_the_scope_qualified() {
    let names = scope_names_in(&[r#"
namespace wi977.un
  sort Holder
    entity h(n: Missing)
  end
end
"#]);
    assert_eq!(names, vec!["wi977.un.Holder"]);
}

/// The `internal` SELECTIVE-IMPORT refusal — `forbid_internal_import`, which held the
/// open-coded copy of the local-name unwrap. Asserts the full rendering, so the
/// `declared_in` half is pinned alongside the scope half.
#[test]
fn a_forbidden_internal_import_names_the_importing_scope() {
    let errs = errors_of(&[BOX, r#"
namespace wi977.badimp
  import anthill.prelude.Int64
  import wi977.box.Box.{mk}
  operation sneak(x: Int64) -> Box
  =
    mk(v: x)
end
"#]);
    assert!(
        errs.iter().any(|e| e.contains(
            "'mk' is internal to 'wi977.box.Box' and cannot be referenced from scope \
             'wi977.badimp'"
        )),
        "the import refusal must name the importing scope in full; got: {errs:#?}",
    );
}

/// The `internal` FIELD-PROJECTION refusal — the typer path whose scope slot was the
/// literal `"another scope"`. This is the arm no fixture reached: WI-369's own test
/// asserts only that some error mentions `internal` and `v`, which the fabricated
/// name satisfied.
#[test]
fn a_hidden_field_projection_names_the_referencing_scope() {
    let errs = errors_of(&[BOX, r#"
sort wi977.peek.Peeker
  import anthill.prelude.Int64
  import wi977.box.Box
  operation peek(b: Box) -> Int64
  =
    b.v
end
"#]);
    assert!(
        errs.iter().any(|e| e.contains(
            "'v' is internal to 'wi977.box.Box' and cannot be referenced from scope \
             'wi977.peek.Peeker.peek'"
        )),
        "the projection refusal must name the scope the projection was WRITTEN in — \
         the OPERATION, not its sort; got: {errs:#?}",
    );
}

/// THE TYPER AND THE LOADER MUST NAME THE SAME SCOPE FOR THE SAME CODE. One fixture,
/// two diagnostics from two subsystems, both about code written in an operation body.
///
/// Found by `/code-review` on this ticket's own diff and repaired here. The typer read
/// `TypingEnv::enclosing_sort`, one scope OUT from where the code is, while the loader
/// reads `current_scope`, the operation's — so this file produced
/// `in scope 'wi977.two.Peeker.other'` beside `from scope 'wi977.two.Peeker'`. Making
/// the scope name qualified is what turned that from invisible into obvious: before
/// this ticket the typer's row said `'another scope'` and there was nothing to compare.
#[test]
fn the_typer_and_the_loader_name_the_same_scope_for_the_same_code() {
    let names = scope_names_in(&[BOX, r#"
sort wi977.two.Peeker
  import anthill.prelude.Int64
  import wi977.box.Box
  operation peek(b: Box) -> Int64
  =
    b.v
  operation other(x: Nope) -> Int64
  =
    1
end
"#]);
    assert!(
        names.contains(&"wi977.two.Peeker.peek".to_string()),
        "the typer's row must name the operation scope; got: {names:?}",
    );
    assert!(
        names.contains(&"wi977.two.Peeker.other".to_string()),
        "the loader's row must name the operation scope; got: {names:?}",
    );
    assert!(
        !names.contains(&"wi977.two.Peeker".to_string()),
        "neither row may name the SORT — that is the granularity split this test \
         exists to close; got: {names:?}",
    );
}

/// A RULE BODY IS A THIRD CONTEXT, and the one that caught a regression this ticket
/// introduced. `TypingEnv::set_enclosing_sort` has ONE caller — the operation-body
/// loop — so every rule body answered `None` for "what scope is this written in".
/// Once `hidden_field_owner` read `None` as the global scope (the top-level repair
/// above), a rule written INSIDE the declaring sort, projecting its own `internal`
/// field, became a hard load error naming `<global>`.
///
/// MEASURED both ways: against `rule_scope`-less code this fixture fails with
/// `'x' is internal to 'wi977.rin.Point' and cannot be referenced from scope
/// '<global>'`; against the permissive pre-ticket arm it passes, as it does now. The
/// whole workspace — 4947 tests — stayed green through the regression, because no
/// fixture projected an internal field from a rule body. That is why this row exists
/// rather than a note.
#[test]
fn a_rule_inside_the_declaring_sort_sees_its_internal_field() {
    let errs = errors_of(&[r#"
namespace wi977.rin
  sort Point
    import anthill.prelude.Int64
  import anthill.prelude.PartialEq.{eq}
    internal entity point(x: Int64, y: Int64)
    entity wrap(p: Point, v: Int64)
    rule holds(?p, ?v)
      :- wrap(p: ?p, v: ?v), eq(?v, ?p.x)
  end
end
"#]);
    assert!(
        errs.is_empty(),
        "a rule written INSIDE the declaring sort must see its own internal field; \
         got: {errs:#?}",
    );
}

/// The other half: a rule OUTSIDE the declaring sort is still refused, and names the
/// scope the rule was written in — its `domain` — not `<global>`. Without the
/// `rule_scope` arm this row still refuses, but names `<global>`, which is the §8.6
/// naming rule broken in the one context that had no answer.
#[test]
fn a_rule_outside_the_declaring_sort_is_refused_naming_the_rules_scope() {
    let errs = errors_of(&[r#"
namespace wi977.rout
  sort Point
    import anthill.prelude.Int64
    internal entity point(x: Int64, y: Int64)
    entity wrap(p: Point, v: Int64)
  end
  import anthill.prelude.Int64
  import wi977.rout.Point
  import anthill.prelude.PartialEq.{eq}
  rule holds(?p, ?v)
    :- Point.wrap(p: ?p, v: ?v), eq(?v, ?p.x)
end
"#]);
    assert!(
        errs.iter().any(|e| e.contains(
            "'x' is internal to 'wi977.rout.Point' and cannot be referenced from scope \
             'wi977.rout'"
        )),
        "the rule-body refusal must name the rule's own scope; got: {errs:#?}",
    );
}

/// CONTROL for the row above, and the one that rejects the over-narrow repair.
/// Asking the visibility question at the OPERATION's scope rather than its sort must
/// not turn a visible name hidden: an operation INSIDE the declaring sort still
/// reaches its own `internal` constructor, through the enclosing-parent chain
/// `internal_visible_from` walks. Loads clean before and after; fails if the
/// operation's scope were ever treated as unparented.
#[test]
fn control_an_operation_still_sees_its_own_sorts_internal_field() {
    let errs = errors_of(&[r#"
sort wi977.own.Box
  import anthill.prelude.Int64
  internal entity mk(v: Int64)
  operation make(x: Int64) -> Box
  =
    mk(v: x)
  operation peek_own(b: Box) -> Int64
  =
    b.v
end
"#]);
    assert!(
        errs.is_empty(),
        "an operation must still see its OWN sort's internal field; got: {errs:#?}",
    );
}

/// The fabricated name has no producer left. Sweeps the two `internal` refusals that
/// reach the typer conversion, since that is where the string lived.
#[test]
fn no_diagnostic_invents_a_scope_named_another_scope() {
    let errs = errors_of(&[BOX, r#"
sort wi977.peek2.Peeker
  import anthill.prelude.Int64
  import wi977.box.Box
  operation peek(b: Box) -> Int64
  =
    b.v
end
"#]);
    assert!(
        !errs.is_empty(),
        "the fixture must still refuse — an empty error list would make the \
         assertion below vacuous",
    );
    assert!(
        !errs.iter().any(|e| e.contains("another scope")),
        "no diagnostic may name a scope 'another scope'; got: {errs:#?}",
    );
}

/// CONTROL — PASSES EITHER WAY BY DESIGN. The duplicate-declaration row read
/// `scope_qualified_name`, the one derivation of the three that already answered
/// qualified, so this assertion held before the change and holds after. It is here to
/// say which half of the file measures the change and which half measures that the
/// change left the already-correct site alone.
#[test]
fn a_duplicate_declaration_row_was_already_qualified() {
    let errs = errors_of(&[r#"
namespace wi977.dup
  entity Rec(a: anthill.prelude.Int64)
  sort Rec
  end
end
"#]);
    assert!(
        errs.iter()
            .any(|e| e.contains("is declared more than once in scope 'wi977.dup'")),
        "the ledger row names its scope qualified, before and after WI-977; \
         got: {errs:#?}",
    );
}

/// The global scope is the one scope that is not a declaration and has no qualified
/// name. It answers the reserved spelling, which no declaration can collide with
/// (WI-987). Pinned at the helper itself, beside the source-level witness below.
#[test]
fn the_global_scope_renders_its_reserved_spelling() {
    let mut kb = anthill_core::kb::KnowledgeBase::new();
    let g = kb.global_scope();
    assert_eq!(
        kb.scope_display_name(g),
        anthill_core::intern::GLOBAL_SCOPE_NAME,
    );
    assert_eq!(kb.scope_display_name(g), "<global>");
}

/// TOP-LEVEL CODE IS OUTSIDE EVERY DECLARING SCOPE BUT THE GLOBAL ONE (§8.6), so this
/// must be REFUSED — the assertion this row exists for.
///
/// Found by `/code-review` on this ticket's own diff, and MEASURED before repairing:
/// against the previous `internal_field_hidden_from`, whose `None` arm answered
/// `false` and whose doc said "there is no lexical scope to test against, so
/// enforcement is skipped (permissive)", this exact source loaded CLEAN
/// (`loaded: 2651 facts, 179 rules`) while the identical body inside a `sort` or
/// `namespace` was refused. WI-369 encapsulation was unenforced for precisely the
/// code with no scope to be inside.
///
/// THE SCOPE NAMED IS THE OPERATION, NOT `<global>`, and the distinction is the point
/// of `TypingEnv::referencing_scope`: the projection is written inside `top_peek`, and
/// a top-level operation's qualified name IS its short name, the global scope
/// contributing no prefix. Measured, the loader names the same fixture's unresolved
/// type `in scope 'top_other'` — the two agree here as they do inside a sort. The bare
/// `<global>` is what a projection outside ANY operation would name; it is pinned at
/// the helper by `the_global_scope_renders_its_reserved_spelling` above.
#[test]
fn a_top_level_projection_of_an_internal_field_is_refused() {
    let errs = errors_of(&[BOX, r#"
import anthill.prelude.Int64
import wi977.box.Box
operation top_peek(b: Box) -> Int64
=
  b.v
"#]);
    assert!(
        errs.iter().any(|e| e.contains(
            "'v' is internal to 'wi977.box.Box' and cannot be referenced from scope \
             'top_peek'"
        )),
        "a top-level projection of an internal field must be refused, naming the \
         operation it was written in; got: {errs:#?}",
    );
}

/// CONTROL for the row above — and the one that rejects the over-broad fix. What
/// makes the top-level projection illegal is `internal`, NOT being at top level: a
/// PUBLIC field projected from the very same place must still load clean. Backing the
/// repair out to "always hidden when there is no enclosing sort" passes the row above
/// and fails this one.
#[test]
fn control_a_top_level_projection_of_a_public_field_still_loads() {
    let errs = errors_of(&[OPEN, r#"
import anthill.prelude.Int64
import wi977.open.Open
operation top_read(o: Open) -> Int64
=
  o.w
"#]);
    assert!(
        errs.is_empty(),
        "a PUBLIC field must stay projectable from top level; got: {errs:#?}",
    );
}

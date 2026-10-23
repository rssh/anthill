//! WI-20261022-JBHQC — AN IMPORT OF A PREDICATE A RULE HEAD OF THE SAME LOAD INTRODUCES
//! IS WIRED BEFORE THE HEADS ARE DECIDED, and reads as an import of an existing name.
//!
//! THE PLAIN FORM. `import a.b.p` binds the name `a.b.p` (§8.6), and a predicate a rule
//! head introduces has that name only after scan sub-pass 3 (§5.3 "Naming one from
//! elsewhere" lists both import forms). WI-295 deferred the selective form's names for
//! that reason; the plain form was refused at sub-pass 2, so it could name such a
//! predicate only when an EARLIER load had minted it. Measured before the change:
//! `import anthill.reflect.feed.reaches` resolved after the stdlib's sealed load and was
//! `UnresolvedImport` in one call over both (the fresh recipe failed
//! `wi_6wvjb…::a_clause_against_an_earlier_loads_clauses_is_refused` on it), and two
//! namespaces of ONE program — one file or two — could not import each other's
//! predicates this way at all, while the `{p}` spelling of the same program loaded.
//!
//! THE WIRING. A deferred import used to be wired after the mint, and phase 2 learned of
//! it through a side list the mint guard alone read, for the head's own scope alone. Each
//! reader it did not reach read the same text differently from the same text with the
//! import wired at sub-pass 2 (here: `r` DECLARED in `jq.lib`, the `…_declared` control of
//! each set) — three `/code-review` rounds, each finding the next. Now the head census
//! says which qualified names the scan's heads will mint, a deferred import is wired to
//! the symbol reserved for its target before phase 2, and every reader reads the ladder:
//! a clause in a sort nested in the importing namespace joins the import; an equation
//! the import reaches is refused (D0EXD); 059 R3 names where a joining clause lands; a
//! head is not taken by the import of the predicate it DEFINES, whichever import reaches
//! it; an import whose target no head mints is refused before any head reads it; and a
//! one-segment import the prelude answered is the program's name when a head of the load
//! mints it. Two more readers the review found ride along: a local minted in a scope that
//! ENCLOSES a head denoting through an import captures it as one at its own address does
//! (JR7BB), and `{p}` under a base that names nothing is one error. And a fourth round
//! (also `/code-review`): a capture is told by the frozen answer against the answer after
//! the mint, not by an overlay walk that refused programs that load; reservations are
//! withdrawn only once nothing they read is withdrawn too; a deferred import keeps its
//! place among the writes of its name; and a prelude fallback, or a name one scope below,
//! is wired by which heads introduce on their own, after phase 2. And a fifth: a deferred
//! import HOLDS ITS PLACE among the writes of its name from sub-pass 2 (a placeholder no
//! resolution reads, `ImportOrigin::Deferred`) and the wiring takes that place, rather
//! than placing it by counting positions, which a late wiring or a repeat misplaced; and
//! a selective import whose target is withdrawn lands one scope below, at its place.
//!
//! COST, measured: `report_post_mint_captures` asks a head again only where the scan
//! minted its name somewhere; on the stdlib in one call (231 census heads) and on
//! `examples/github-todo` it asked none.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ─────────────────────────────
//!
//! Each part on its own, measured:
//!
//! | part backed out | rows that fail |
//! |---|---|
//! | `process_one_import`'s `Plain` arm refusing a miss at once, as before | every row with a plain import of a predicate of the load: `a_plain_import_…`, `across_two_files_…`, `a_clause_at_the_imported_name_…`, `a_one_segment_plain_import_of_a_top_level_…`, the `_plain` nested, equation, R3 and definer rows, `the_definer_under_a_file_level_import_…`, `a_reservation_no_head_mints_…`, `a_reservation_whose_definer_reads_…`, `a_local_in_an_enclosing_scope_captures_…` (not its `_declared` control), `a_head_denoting_the_reservation_…`, `a_deferred_import_keeps_its_place_…`, `…_one_scope_below_that_a_head_introduces`, `a_late_import_keeps_its_place_…`, `deferred_and_resolved_imports_…`, `a_selective_import_whose_target_is_withdrawn_…`; under the fresh recipe also `wi_6wvjb…::a_clause_against_an_earlier_loads_clauses_is_refused` |
//! | the wiring done after the mint instead (the import added once its definer minted) | `a_clause_at_the_imported_name_…`, the `_plain` and `_selective` nested, equation and R3 rows, `a_reservation_no_head_mints_…`, `a_reservation_whose_definer_reads_…`, `a_local_in_an_enclosing_scope_captures_…`, `a_head_denoting_the_reservation_…`, `a_deferred_import_keeps_its_place_…`, `…_one_scope_below_that_a_head_introduces`, `a_late_import_keeps_its_place_…`, `deferred_and_resolved_imports_…`, `a_selective_import_whose_target_is_withdrawn_…` |
//! | `DeferredWiring::is_own_reservation` answering `false` | the four definer rows, `a_head_denoting_the_reservation_…` |
//! | `DeferredWiring::settle` doing nothing | `a_reservation_no_head_mints_is_withdrawn` (on `report_unminted`), `a_reservation_whose_definer_reads_…`, `a_selective_import_whose_target_is_withdrawn_…` |
//! | `settle` withdrawing every idle reservation at once | `a_reservation_whose_definer_reads_a_withdrawn_one_is_kept` |
//! | `report_post_mint_captures` | `a_local_in_an_enclosing_scope_captures_…` both |
//! | the nested-scope rung (no selective import left for `wire_late`) | `a_selective_import_reaches_a_name_one_scope_below`, `…_one_scope_below_that_a_head_introduces`, `a_late_import_keeps_its_place_…` |
//! | `one_scope_below` counting every head one scope below, not those that introduce | `a_selective_import_reaches_the_one_name_one_scope_below_that_a_head_introduces` |
//! | the selective arm deferring the names of a base that names nothing | `a_selective_import_of_a_base_that_names_nothing_is_one_error` |
//! | the prelude fallback not deferred | `a_one_segment_import_the_prelude_answered_is_the_programs_name` |
//! | the prelude fallback wired before phase 2, not by the heads that introduce on their own | `a_head_under_a_prelude_fallback_does_not_mint_its_name` |
//! | `DeferredWiring::wire` appending the wired write instead of taking the import's place | `a_deferred_import_keeps_its_place_…`, `a_late_import_keeps_its_place_…`, `deferred_and_resolved_imports_…` |
//! | `take_back` refusing a selective import instead of re-pointing it one scope below | `a_selective_import_whose_target_is_withdrawn_lands_one_scope_below` |
//!
//! `SymbolTable::withdraw_reserved` has no row: a withdrawn reservation comes with a refused
//! load (its import names nothing) or with a prelude fallback, which `wire_late` reserves
//! only for a head introducing on its own — and nothing a test can reach lists the table's
//! symbols after a refused load. It is kept so that nothing does.
//!
//! The controls pass either way BY DESIGN: `a_head_denoting_its_own_scopes_declaration_…`
//! and `a_head_denoting_the_reservation_its_enclosing_scope_mints_…` are the programs the
//! overlay walk refused, which the capture check passes either way (the second needs the
//! plain form and the definer, as the table says); the `…_declared` rows wire the import at
//! sub-pass 2, which is the reading every deferred import must agree with;
//! `the_selective_form_of_the_same_program_loads` is the spelling WI-295 already
//! deferred; and the rows of an import that names nothing are what no deferral may
//! swallow — refused once, at the import, with no head of its name taken by it. Those
//! last FAILED before this design (a second, "loader invariant" error, or a sibling
//! file's head refused as captured ahead of the import's own error — found by
//! `/code-review`); no single part of it can be backed out to fail them again, an import
//! no head mints having nothing to be wired to.

use crate::common::{
    load_errors_of, load_kb_with, load_kb_with_user_files, load_outcome, load_outcome_files,
    pattern_hits, unrendered_load_errors_of, UserFile,
};
use anthill_core::kb::load::LoadError;

const LIB: &str = "namespace jq.lib\n  fact s(1, 2)\n  rule r(?x, ?y) :- s(?x, ?y)\nend\n";

/// [`LIB`] with `r` DECLARED (proposal 061), so an import of it resolves at sub-pass 2.
const DECLARED_LIB: &str =
    "namespace jq.lib\n  fact s(1, 2)\n  rule r(?x, ?y)\n  rule r(?x, ?y) :- s(?x, ?y)\nend\n";

const PLAIN: &str = "jq.lib.r";
const SELECTIVE: &str = "jq.lib.{r}";

fn app(import: &str) -> String {
    format!("namespace jq.app\n  import {import}\n  rule q(?a, ?b) :- r(?a, ?b)\nend\n")
}

/// `q` answers exactly `(1, 2)`, through the imported `r`.
fn assert_q_reads_r(kb: &mut anthill_core::kb::KnowledgeBase) {
    assert_eq!(
        pattern_hits(kb, "jq.app.q(?a, ?b)"),
        1,
        "one answer through `r`"
    );
    assert_eq!(pattern_hits(kb, "jq.app.q(1, 2)"), 1, "and it is `s`'s row");
}

fn peeled(errors: &[LoadError]) -> Vec<&LoadError> {
    errors.iter().map(LoadError::peel).collect()
}

/// The one error `errors` holds, which must be `UnresolvedImport` at `path`.
fn only_unresolved_import(errors: &[LoadError], path: &str) {
    match peeled(errors).as_slice() {
        [LoadError::UnresolvedImport { path: got, .. }] => assert_eq!(got, path),
        other => panic!("expected exactly `UnresolvedImport` at {path}, got {other:#?}"),
    }
}

fn unresolved_import(src: &str, path: &str) {
    only_unresolved_import(&unrendered_load_errors_of(src), path);
}

/// No head was refused as captured by a local — the noise an import that names nothing
/// made when it took heads of its name.
fn no_capture_refusal(errors: &[LoadError]) {
    assert!(
        !peeled(errors)
            .iter()
            .any(|e| matches!(e, LoadError::RuleHeadImportCapturedByLocal { .. })),
        "no head captured by an import that names nothing: {errors:#?}"
    );
}

// ── the plain form, in one load ─────────────────────────────────────────

#[test]
fn a_plain_import_of_a_predicate_of_the_same_load_resolves() {
    let mut kb = load_kb_with(&format!("{LIB}{}", app(PLAIN)));
    assert_q_reads_r(&mut kb);
}

/// The deferred import carries the file it was written in (imports are file-local,
/// WI-995): the importer and the predicate in two files of one load.
#[test]
fn across_two_files_of_one_load() {
    let importer = app(PLAIN);
    let mut kb = load_kb_with_user_files(&[UserFile::Text(LIB), UserFile::Text(&importer)]);
    assert_q_reads_r(&mut kb);
}

/// A head of the imported name REFERENCES what was imported, as under the selective form
/// (`wi_rdgqc_deferred_import_mint_test`): the clause is `jq.lib.r`'s, and `jq.app`
/// declares no `r` of its own.
#[test]
fn a_clause_at_the_imported_name_joins_the_imported_predicate() {
    let src = format!("{LIB}namespace jq.app\n  import jq.lib.r\n  fact r(3, 4)\nend\n");
    let mut kb = load_kb_with(&src);
    assert_eq!(pattern_hits(&mut kb, "jq.lib.r(3, 4)"), 1);
    assert!(kb.try_resolve_symbol("jq.app.r").is_none());
}

/// `import p` of a predicate a namespace-less file's rule introduces: the path's base is
/// `<global>`.
#[test]
fn a_one_segment_plain_import_of_a_top_level_predicate_resolves() {
    let top = "rule p(1) :- true\n";
    let importer = "namespace jq.app\n  import p\n  rule q(?x) :- p(?x)\nend\n";
    let mut kb = load_kb_with_user_files(&[UserFile::Text(top), UserFile::Text(importer)]);
    assert_eq!(pattern_hits(&mut kb, "jq.app.q(1)"), 1);
}

/// `import Option` when a namespace-less file's rule mints `Option`: sub-pass 2 bound the
/// prelude's, for want of a top-level `Option` it could not see yet; an earlier load
/// would have shown it, and the import reads the program's name.
#[test]
fn a_one_segment_import_the_prelude_answered_is_the_programs_name() {
    let top = "rule Option(1) :- true\n";
    let importer = "namespace jq.app\n  import Option\n  rule q(?x) :- Option(?x)\nend\n";
    let mut kb = load_kb_with_user_files(&[UserFile::Text(top), UserFile::Text(importer)]);
    assert_eq!(pattern_hits(&mut kb, "jq.app.q(1)"), 1);
}

/// CONTROL: the selective spelling, deferred since WI-295.
#[test]
fn the_selective_form_of_the_same_program_loads() {
    let mut kb = load_kb_with(&format!("{LIB}{}", app(SELECTIVE)));
    assert_q_reads_r(&mut kb);
}

/// `import nsq.{p}` of a `p` a rule introduces in `nsq.Rec`, one scope below the base:
/// sub-pass 2's nested-scope rung, for a name the load mints.
#[test]
fn a_selective_import_reaches_a_name_one_scope_below() {
    let src = "namespace nsq\n  sort Rec\n    entity rec\n    rule p(1) :- true\n  end\nend\n\
               namespace otherq\n  import nsq.{p}\n  rule q(?x) :- p(?x)\nend\n";
    let mut kb = load_kb_with(src);
    assert_eq!(pattern_hits(&mut kb, "otherq.q(1)"), 1);
}

// ── an import that names nothing ────────────────────────────────────────

/// CONTROL: the base names a namespace, the leaf nothing the load mints.
#[test]
fn a_leaf_that_names_nothing_is_still_unresolved() {
    unresolved_import(
        &format!("{LIB}namespace jq.app\n  import jq.lib.nope\nend\n"),
        "jq.lib.nope",
    );
}

/// CONTROL: an import naming nothing beside a head of its name — one error, the import's,
/// and the head is the program's own.
fn import_naming_nothing_beside_a_head_is_one_error(import: &str) {
    unresolved_import(
        &format!("{LIB}namespace jq.app\n  import {import}\n  fact nope(1)\nend\n"),
        "jq.lib.nope",
    );
}

#[test]
fn an_import_naming_nothing_beside_a_head_of_its_name_is_one_error_plain() {
    import_naming_nothing_beside_a_head_is_one_error("jq.lib.nope");
}

#[test]
fn an_import_naming_nothing_beside_a_head_of_its_name_is_one_error_selective() {
    import_naming_nothing_beside_a_head_is_one_error("jq.lib.{nope}");
}

/// CONTROL: an import naming nothing, beside a head of its name in another file at the
/// same scope. The two heads introduce `rr` in two files, which is 061's own refusal;
/// what must NOT be here is the sibling's head refused as capturing the import.
fn import_naming_nothing_beside_a_sibling_file(import: &str, path: &str) {
    let importer = format!("namespace jq.app\n  import {import}\n  fact rr(1)\nend\n");
    let sibling = "namespace jq.app\n  fact rr(2)\nend\n";
    let errors = load_outcome_files(&[
        UserFile::Text(LIB),
        UserFile::Text(&importer),
        UserFile::Text(sibling),
    ])
    .errors();
    no_capture_refusal(&errors);
    assert!(
        peeled(&errors)
            .iter()
            .any(|e| matches!(e, LoadError::UnresolvedImport { path: p, .. } if p == path)),
        "{errors:#?}"
    );
}

#[test]
fn a_leaf_that_names_nothing_takes_no_sibling_files_head() {
    import_naming_nothing_beside_a_sibling_file("jq.lib.rr", "jq.lib.rr");
}

#[test]
fn a_base_that_names_nothing_takes_no_sibling_files_head() {
    import_naming_nothing_beside_a_sibling_file("jq.nowhere.rr", "jq.nowhere.rr");
}

/// `import jq.nowhere.{r}` beside a head `r`: ONE error, the base's — its names are not
/// deferred, a base that names nothing holding no name any head mints.
#[test]
fn a_selective_import_of_a_base_that_names_nothing_is_one_error() {
    unresolved_import(
        "namespace jq.app\n  import jq.nowhere.{r}\n  fact r(1)\nend\n",
        "jq.nowhere",
    );
}

/// A reservation no head mints: `Lib`'s `r` reads `other.r` through the nearer
/// `import other.r` of its namespace, so it mints no `app.Lib.r`, and the import of
/// `app.Lib.r` in `user` names nothing — one error, the import's.
#[test]
fn a_reservation_no_head_mints_is_withdrawn() {
    let src = "namespace other\n  fact r(9)\nend\n\
               namespace app\n  import other.r\n  sort Lib\n    entity l\n    fact s(1)\n    \
               rule r(?x) :- s(?x)\n  end\nend\n\
               namespace user\n  import app.Lib.r\nend\n";
    unresolved_import(src, "app.Lib.r");
}

// ── a head under a deferred import reads as under a wired one ───────────

/// `fact r(5, 6)` in `sort S` of the importing namespace lands on `jq.lib.r` — the
/// ladder walks from `S` to the namespace that holds the import — and `S` declares no
/// `r`.
fn nested_clause_joins(lib: &str, import: &str) {
    let src = format!(
        "{lib}namespace jq.app\n  import {import}\n  sort S\n    entity s0\n    \
         fact r(5, 6)\n  end\nend\n"
    );
    let mut kb = load_kb_with(&src);
    assert_eq!(pattern_hits(&mut kb, "jq.lib.r(5, 6)"), 1, "{import}");
    assert!(kb.try_resolve_symbol("jq.app.S.r").is_none(), "{import}");
}

#[test]
fn a_clause_in_a_sort_nested_in_the_importing_namespace_joins_plain() {
    nested_clause_joins(LIB, PLAIN);
}

#[test]
fn a_clause_in_a_sort_nested_in_the_importing_namespace_joins_selective() {
    nested_clause_joins(LIB, SELECTIVE);
}

/// CONTROL: the import wired at sub-pass 2.
#[test]
fn a_clause_in_a_sort_nested_in_the_importing_namespace_joins_declared() {
    nested_clause_joins(DECLARED_LIB, PLAIN);
}

/// An equation whose subject the import brings in names another scope's PREDICATE, and
/// is refused (WI-20260821-D0EXD) — the one error the load has.
fn equation_at_the_import_is_refused(lib: &str, import: &str) {
    let src =
        format!("{lib}namespace jq.app\n  import {import}\n  rule r(1, 2) <=> 5 @[simp]\nend\n");
    let errors = unrendered_load_errors_of(&src);
    match peeled(&errors).as_slice() {
        [LoadError::EquationSubjectNamesAPredicate {
            name,
            predicate_scopes,
            ..
        }] => {
            assert_eq!(name, "r", "{import}");
            assert_eq!(predicate_scopes, &["jq.lib".to_string()], "{import}");
        }
        other => panic!("{import}: expected the D0EXD refusal alone, got {other:#?}"),
    }
}

#[test]
fn an_equation_at_an_imported_predicate_is_refused_plain() {
    equation_at_the_import_is_refused(LIB, PLAIN);
}

#[test]
fn an_equation_at_an_imported_predicate_is_refused_selective() {
    equation_at_the_import_is_refused(LIB, SELECTIVE);
}

/// CONTROL: the import wired at sub-pass 2.
#[test]
fn an_equation_at_an_imported_predicate_is_refused_declared() {
    equation_at_the_import_is_refused(DECLARED_LIB, PLAIN);
}

/// 059 R3 refuses a `rule` in a secondary entry whose head joins an existing predicate,
/// naming where it lands — `jq.lib.r`, not "a name that resolves elsewhere".
fn r3_names_where_the_clause_lands(lib: &str, import: &str) {
    let src = format!(
        "{}  sort Rec\n    entity rec\n  end\nend\nnamespace jq.lib.Rec\n  import {import}\n  \
         rule r(7, 8) :- true\nend\n",
        lib.strip_suffix("end\n")
            .expect("the lib ends its namespace")
    );
    let errors = load_errors_of(&src);
    assert_eq!(errors.len(), 1, "{import}: {errors:#?}");
    assert!(
        errors[0].contains("it resolves to 'jq.lib.r'"),
        "{import}: {}",
        errors[0]
    );
}

#[test]
fn r3_names_where_the_clause_lands_plain() {
    r3_names_where_the_clause_lands(LIB, PLAIN);
}

#[test]
fn r3_names_where_the_clause_lands_selective() {
    r3_names_where_the_clause_lands(LIB, SELECTIVE);
}

/// CONTROL: the import wired at sub-pass 2.
#[test]
fn r3_names_where_the_clause_lands_declared() {
    r3_names_where_the_clause_lands(DECLARED_LIB, PLAIN);
}

// ── the definer of what an import waits for ─────────────────────────────

/// The import's DEFINER under the importing scope is not taken by the import: `Lib`'s
/// rule mints `app.Lib.r`, which is what the import waits for.
fn definer_under_the_import(import: &str) {
    let src = format!(
        "namespace app\n  import {import}\n  sort Lib\n    entity l\n    fact s(1)\n    \
         rule r(?x) :- s(?x)\n  end\n  rule q(?x) :- r(?x)\nend\n"
    );
    let mut kb = load_kb_with(&src);
    assert_eq!(pattern_hits(&mut kb, "app.q(1)"), 1, "{import}");
}

#[test]
fn the_definer_under_an_enclosing_import_is_not_taken_by_it_plain() {
    definer_under_the_import("app.Lib.r");
}

#[test]
fn the_definer_under_an_enclosing_import_is_not_taken_by_it_selective() {
    definer_under_the_import("app.Lib.{r}");
}

/// A file's top-level import encloses every namespace of the file, the definer's too.
#[test]
fn the_definer_under_a_file_level_import_is_not_taken_by_it() {
    let app_without_import = app(PLAIN).replace("  import jq.lib.r\n", "");
    let mut kb = load_kb_with(&format!("import jq.lib.r\n{LIB}{app_without_import}"));
    assert_q_reads_r(&mut kb);
}

/// Two deferred imports of one short name reach the definer: the file's `import a.{r}`
/// and its namespace's `import app.Lib.{r}`. The nearer is the one of the predicate it
/// defines, so it defines it — `q` reads `Lib`'s row, not `a`'s.
#[test]
fn the_definer_under_two_imports_of_its_name_defines_it() {
    let src = "namespace a\n  fact s(1)\n  rule r(?x) :- s(?x)\nend\n\
               import a.{r}\n\
               namespace app\n  import app.Lib.{r}\n  sort Lib\n    entity l\n    fact t(2)\n    \
               rule r(?x) :- t(?x)\n  end\n  rule q(?x) :- r(?x)\nend\n";
    let mut kb = load_kb_with(src);
    assert_eq!(pattern_hits(&mut kb, "app.q(2)"), 1);
    assert_eq!(pattern_hits(&mut kb, "app.q(?x)"), 1);
}

// ── a local that captures a head denoting through an import ─────────────

/// `fact r(5, 6)` in `jq.app.S` denotes `jq.lib.r` through `jq.app`'s import, in one
/// file; another file writes `fact r(7, 8)` at `jq.app`, whose local the first head's
/// ladder would meet before the import. Refused (WI-20260821-JR7BB), not loaded clean
/// with the first fact moved under `jq.app.r`.
fn enclosing_local_captures(lib: &str) {
    let importer = format!(
        "{lib}namespace jq.app\n  import jq.lib.r\n  sort S\n    entity s0\n    \
         fact r(5, 6)\n  end\nend\n"
    );
    let sibling = "namespace jq.app\n  fact r(7, 8)\nend\n";
    let errors = load_outcome_files(&[UserFile::Text(&importer), UserFile::Text(sibling)]).errors();
    match peeled(&errors).as_slice() {
        [LoadError::RuleHeadImportCapturedByLocal { name, scope, .. }] => {
            assert_eq!((name.as_str(), scope.as_str()), ("r", "jq.app"));
        }
        other => panic!("expected the capture refusal alone, got {other:#?}"),
    }
}

#[test]
fn a_local_in_an_enclosing_scope_captures_a_head_denoting_through_an_import() {
    enclosing_local_captures(LIB);
}

/// The same with the import wired at sub-pass 2: the capture is the wired import's too.
#[test]
fn a_local_in_an_enclosing_scope_captures_a_head_denoting_through_an_import_declared() {
    enclosing_local_captures(DECLARED_LIB);
}

/// CONTROL: a head denoting its OWN scope's declaration, beside a head introducing the
/// name in the scope enclosing it — no capture: its answer is the same after the mint.
#[test]
fn a_head_denoting_its_own_scopes_declaration_is_not_captured() {
    let src = "namespace e\n  rule p(1) :- true\n  namespace s\n    rule p(?x)\n    \
               rule p(2) :- true\n  end\nend\n";
    let mut kb = load_kb_with(src);
    assert_eq!(pattern_hits(&mut kb, "e.s.p(2)"), 1);
    assert_eq!(pattern_hits(&mut kb, "e.p(1)"), 1);
}

/// CONTROL: `Inner`'s `fact r(5)` denotes the reservation of `app.Lib.r` through `app`'s
/// import, and `Lib`, which its ladder meets first, mints exactly that symbol — no capture.
#[test]
fn a_head_denoting_the_reservation_its_enclosing_scope_mints_is_not_captured() {
    let src = "namespace app\n  import app.Lib.r\n  namespace Lib\n    fact s(1)\n    \
               rule r(?x) :- s(?x)\n    namespace Inner\n      fact r(5)\n    end\n  end\nend\n";
    let mut kb = load_kb_with(src);
    assert_eq!(pattern_hits(&mut kb, "app.Lib.r(?x)"), 2);
}

/// `y`'s `p` reads `z.p` through `import z.p`, so `y.p` is never minted; `x.Rec`'s `p`
/// reads `y.p`'s reservation, idle only because of THAT one — withdrawn, `x.Rec`'s head
/// reads nothing and mints `x.Rec.p`, which `user` imports. One error: `import y.p`.
#[test]
fn a_reservation_whose_definer_reads_a_withdrawn_one_is_kept() {
    let src = "namespace z\n  fact p(0)\nend\n\
               namespace y\n  import z.p\n  fact p(9)\nend\n\
               namespace x\n  import y.p\n  sort Rec\n    entity e\n    fact p(1)\n  end\nend\n\
               namespace user\n  import x.Rec.p\nend\n";
    unresolved_import(src, "y.p");
}

/// `import lib.r` then `import other.r`: the LATER write is what `r` means, though
/// `lib.r` is a predicate of the load, wired after `other.r` was. The reverse order is
/// the control.
#[test]
fn a_deferred_import_keeps_its_place_among_the_writes_of_its_name() {
    let src = |imports: &str| {
        format!(
            "namespace lib\n  fact s(1)\n  rule r(?x) :- s(?x)\nend\n\
             namespace other\n  rule r(?x)\n  fact r(2)\nend\n\
             namespace app\n{imports}  rule q(?x) :- r(?x)\nend\n"
        )
    };
    let mut kb = load_kb_with(&src("  import lib.r\n  import other.r\n"));
    assert_eq!(
        pattern_hits(&mut kb, "app.q(2)"),
        1,
        "the later import, `other.r`"
    );
    assert_eq!(pattern_hits(&mut kb, "app.q(?x)"), 1);
    let mut kb = load_kb_with(&src("  import other.r\n  import lib.r\n"));
    assert_eq!(
        pattern_hits(&mut kb, "app.q(1)"),
        1,
        "the later import, `lib.r`"
    );
    assert_eq!(pattern_hits(&mut kb, "app.q(?x)"), 1);
}

/// `import todo` falls back to the prelude's `todo`, and the head `todo(1)` written under
/// it reads that: a clause of the prelude's operation, refused as such — not the minter of
/// a top-level `todo` the rewired import would then name.
#[test]
fn a_head_under_a_prelude_fallback_does_not_mint_its_name() {
    let (kb, errors) = load_outcome("import todo\nrule todo(1) :- true\n").kb_and_errors();
    assert!(
        kb.try_resolve_symbol("todo").is_none(),
        "no top-level `todo` minted"
    );
    assert!(
        errors
            .iter()
            .any(|e| e.to_string().contains("anthill.prelude.todo")),
        "the head is a clause of the prelude's `todo`: {errors:#?}"
    );
}

/// `import base.{p}` where `base.A`'s head `p` reads `other.p` (it mints nothing) and
/// `base.B`'s introduces: the one name a head introduces one scope below is `base.B.p`.
#[test]
fn a_selective_import_reaches_the_one_name_one_scope_below_that_a_head_introduces() {
    let src = "namespace other\n  fact p(7)\nend\n\
               namespace base\n  sort A\n    entity a\n    import other.p\n    fact p(1)\n  end\n  \
               sort B\n    entity b\n    fact p(2)\n  end\nend\n\
               namespace user\n  import base.{p}\n  rule q(?x) :- p(?x)\nend\n";
    let mut kb = load_kb_with(src);
    assert_eq!(pattern_hits(&mut kb, "user.q(2)"), 1);
    assert_eq!(pattern_hits(&mut kb, "user.q(?x)"), 1);
}

// ── the fifth round: a deferred import keeps the place the text gave it ─

/// `import base.{p}` (wired after phase 2, one scope below) before `import other.p`
/// (wired before it): the text's LAST import is what `p` means, whichever was wired
/// last. The reverse order is the control.
#[test]
fn a_late_import_keeps_its_place_before_a_later_direct_one() {
    let src = |imports: &str| {
        format!(
            "namespace other\n  fact p(7)\nend\n\
             namespace base\n  sort B\n    entity b\n    fact p(2)\n  end\nend\n\
             namespace user\n{imports}  rule q(?x) :- p(?x)\nend\n"
        )
    };
    let mut kb = load_kb_with(&src("  import base.{p}\n  import other.p\n"));
    assert_eq!(
        pattern_hits(&mut kb, "user.q(7)"),
        1,
        "the later import, `other.p`"
    );
    assert_eq!(pattern_hits(&mut kb, "user.q(?x)"), 1);
    let mut kb = load_kb_with(&src("  import other.p\n  import base.{p}\n"));
    assert_eq!(
        pattern_hits(&mut kb, "user.q(2)"),
        1,
        "the later import, `base.B.p`"
    );
    assert_eq!(pattern_hits(&mut kb, "user.q(?x)"), 1);
}

/// Deferred and resolved imports of one name interleaved, one deferred twice: the text's
/// last import, `last.p`, is what `p` means.
#[test]
fn deferred_and_resolved_imports_of_one_name_keep_the_texts_order() {
    let src = "namespace lib\n  fact p(1)\nend\nnamespace lib2\n  fact p(3)\nend\n\
               namespace other\n  rule p(?x)\n  fact p(2)\nend\n\
               namespace last\n  rule p(?x)\n  fact p(4)\nend\n\
               namespace user\n  import lib.p\n  import lib.p\n  import other.p\n  \
               import lib2.p\n  import last.p\n  rule q(?x) :- p(?x)\nend\n";
    let mut kb = load_kb_with(src);
    assert_eq!(pattern_hits(&mut kb, "user.q(4)"), 1);
    assert_eq!(pattern_hits(&mut kb, "user.q(?x)"), 1);
}

/// `import base.{p}` waits for `base.p`, which one file's head would mint — but that head
/// reads `other.p` through its own file's import, so `base.p` is withdrawn. The import is
/// then the one name a head introduces one scope below, `base.B.p`, as a load in two
/// steps reads it — not refused.
#[test]
fn a_selective_import_whose_target_is_withdrawn_lands_one_scope_below() {
    let first = "namespace other\n  fact p(0)\nend\n\
                 namespace base\n  import other.p\n  fact p(1)\nend\n";
    let second = "namespace base\n  sort B\n    entity b\n    fact p(2)\n  end\nend\n\
                  namespace user\n  import base.{p}\n  rule q(?x) :- p(?x)\nend\n";
    let mut kb = load_kb_with_user_files(&[UserFile::Text(first), UserFile::Text(second)]);
    assert_eq!(pattern_hits(&mut kb, "user.q(2)"), 1);
    assert_eq!(pattern_hits(&mut kb, "user.q(?x)"), 1);
    assert_eq!(
        pattern_hits(&mut kb, "other.p(1)"),
        1,
        "`base`'s head is `other.p`'s"
    );
}

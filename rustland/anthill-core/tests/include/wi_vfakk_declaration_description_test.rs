//! WI-20260830-VFAKK — A BODY-LESS RULE DECLARATION HAS A DESCRIPTION TARGET OF ITS
//! OWN: THE PREDICATE SYMBOL IT DECLARES.
//!
//! §4.1 admits a `{< … >}` block on a declaration and refuses one that has no stable
//! `DescriptionInfo.target`. Proposal 061 made `rule p(?x)` a DECLARATION — it brings a
//! predicate symbol into existence in scan pass 1 and stores no clause — and the two
//! rules were written for different constructs, so it fell between them: unlabeled, the
//! converter refused the block ("no stable target", §4.1); labeled, 061 refused the
//! LABEL ("nothing to cite"). Each refusal sent the author to the other one.
//!
//! WHAT THE SPLIT NOW IS. A rule has a description target when it is LABELED (the
//! citation handle) or when it DECLARES (the predicate symbol). An unlabeled rule that
//! stores a CLAUSE has neither, and both halves of that refusal share one sentence
//! (`parse::error::description_without_target`).
//!
//! WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT — THREE AXES, each measured on its
//! own (present-but-neutralized, not deleted). The distinction matters because the
//! three fail in three different WAYS, and a row that is red for the wrong reason
//! measures nothing:
//!
//!   * the CONVERTER's admission of a body-less block (`|| body.is_none()`) — 5 red,
//!     3914 green. Every fixture here becomes a PARSE error, and `try_load_kb_with`
//!     PANICS on those by design (`tests/common/mod.rs`), so no assertion in any of
//!     the five is reached at all. It is the loudest back-out and the least
//!     informative — outside this file it also reds all 47 rows of `guardians_test`,
//!     because the example stops parsing.
//!   * the LOADER's emission on the declared symbol — 3 red, 3916 green:
//!     `a_declarations_block_names_the_predicate_it_declares`,
//!     `two_blocks_on_one_declaration_are_indexed` and
//!     `a_declaration_shares_its_target_with_standalone_describe`, each on its own
//!     assertion (`[]` where a fact was expected). THIS is the axis that measures what
//!     the ticket added; `guardians_test` loses exactly one row to it.
//!   * the LOADER's §4.1 refusal (the `Clause` arm) — 1 red, 3918 green:
//!     `a_bodyless_equation_head_is_refused_at_load` alone, and it fails by LOADING
//!     CLEAN, i.e. with the block SILENTLY DROPPED. That is the hole admitting
//!     body-less rules at the converter would otherwise have opened.
//!
//! (The first version of this note claimed the equation row failed on its LOCATION
//! assertion under the converter back-out. It does not — it panics before reaching
//! one. /code-review measured it.)
//!
//! WHICH ROWS PASS EITHER WAY BY DESIGN — the CONTROLS, each guarding a refusal this
//! must NOT relax (the ticket names the first three):
//!   * `a_labeled_declaration_is_still_refused_by_061`
//!   * `a_bodied_unlabeled_rules_block_is_still_refused_at_parse`
//!   * `an_asserting_bodyless_rule_is_still_a_clause` (`:- true`, 061's assertion
//!     spelling — body-less in intent, a CLAUSE to `rule_reading`, and the remedy 061's
//!     own diagnostic offers)
//!   * `a_bodyless_rule_that_declares_nothing_is_still_refused`
//!
//! THE POPULATION IS `rule_reading`'s THREE ARMS, not the two the ticket named:
//! `Declaration` (the three emission rows), `Clause` (the equation row), and
//! `DeclaresNothing` (the last control). Every body-less rule the converter now
//! carries a block for lands in exactly one of them, and none of the three drops it
//! in silence.

use crate::common::{load_kb_with, parse_errs, try_load_kb_with};
use crate::wi1070_operation_description_test::descriptions_of;

/// The load errors of a source that must NOT load. Panics if it loads clean, since a
/// fixture that no longer trips the rule is a test-authoring bug.
fn load_errs(src: &str) -> Vec<String> {
    match try_load_kb_with(src) {
        Ok(_) => panic!("fixture loaded CLEAN, but this call site declares it must fail"),
        Err(errs) => errs,
    }
}

/// THE TICKET'S SHAPE, in miniature: `guardians.in_org`. A relation the library
/// DECLARES and a deployment asserts rows for — the one declaration whose intent a
/// reader most wants, and the one that could not carry it.
#[test]
fn a_declarations_block_names_the_predicate_it_declares() {
    const SRC: &str = r#"
namespace vfakk.decl
  {< Which addresses belong to the organisation. >}
  rule in_org(?a)
end
"#;
    let kb = load_kb_with(SRC);
    assert_eq!(
        descriptions_of(&kb, "vfakk.decl.in_org"),
        vec![(
            0,
            "Which addresses belong to the organisation.".to_string()
        )],
        "a body-less rule's block must reach the KB as a DescriptionInfo naming the \
         predicate that rule DECLARES",
    );
}

/// The per-target index is the declaration's own, exactly as it is for a sort or an
/// operation — not a global enumeration over every `DescriptionInfo` (WI-438).
#[test]
fn two_blocks_on_one_declaration_are_indexed() {
    const SRC: &str = r#"
namespace vfakk.two
  {< first >} {< second >}
  rule membership(?a)
end
"#;
    let kb = load_kb_with(SRC);
    assert_eq!(
        descriptions_of(&kb, "vfakk.two.membership"),
        vec![(0, "first".to_string()), (1, "second".to_string())],
        "each block is its own fact, indexed 0-based per target and in source order",
    );
}

/// ONE TARGET TERM, both spellings — the property `emit_own_descriptions` exists for.
/// A separate key would print the same and answer differently.
#[test]
fn a_declaration_shares_its_target_with_standalone_describe() {
    const SRC: &str = r#"
namespace vfakk.share
  {< inline on the declaration >}
  rule releasable(?t)
  describe releasable {< standalone companion >}
end
"#;
    let kb = load_kb_with(SRC);
    assert_eq!(
        descriptions_of(&kb, "vfakk.share.releasable"),
        vec![
            (0, "inline on the declaration".to_string()),
            (1, "standalone companion".to_string()),
        ],
        "the inline block and `describe` must land on ONE target and share its index \
         counter, the way they already do for an operation",
    );
}

/// THE OTHER HALF OF §4.1, and the row that says admitting body-less rules at the
/// converter did not open a silent drop. A body-less `<=>` head is body-less to the eye
/// and a CLAUSE to `rule_reading`: its clauses index under the CONNECTIVE, so its
/// subject declares no predicate and there is no symbol to name. The refusal is the
/// LOADER's, because only `rule_reading` can tell this shape from a declaration — which
/// is why the assertion is on the loader's own construct wording, not merely on "it was
/// refused" (that much was true before, from the other pass).
#[test]
fn a_bodyless_equation_head_is_refused_at_load() {
    const SRC: &str = r#"
namespace vfakk.eqn
  import anthill.prelude.Int64
  {< has no target >}
  rule twice(?x) <=> ?x
end
"#;
    let errs = load_errs(SRC);
    assert!(
        errs.iter().any(|e| {
            e.contains("description block on an unlabeled rule that stores a clause")
                && e.contains("no stable target")
        }),
        "the loader must refuse it with §4.1's own sentence, naming the construct; \
         got: {errs:#?}",
    );
    // ... and the LABELED spelling of the same rule is the escape that sentence names.
    const LABELED: &str = r#"
namespace vfakk.eqn_labeled
  import anthill.prelude.Int64
  {< the equation's own intent >}
  rule law: twice(?x) <=> ?x
end
"#;
    let kb = load_kb_with(LABELED);
    assert_eq!(
        descriptions_of(&kb, "vfakk.eqn_labeled.law"),
        vec![(0, "the equation's own intent".to_string())],
        "a LABEL is the citation handle §4.1 sends the author to, and it must work",
    );
}

// ── controls ────────────────────────────────────────────────────

/// PASSES EITHER WAY BY DESIGN. 061 refuses a citation LABEL on a declaration — there
/// is no clause to cite — and this change gives the BLOCK a target without giving the
/// label one. Backing the change out leaves this refusal exactly where it is.
#[test]
fn a_labeled_declaration_is_still_refused_by_061() {
    const SRC: &str = r#"
namespace vfakk.labeled_decl
  {< Which addresses belong to the organisation. >}
  rule org_membership: in_org(?a)
end
"#;
    let errs = load_errs(SRC);
    assert!(
        errs.iter()
            .any(|e| e.contains("A citation label on it has nothing to cite")),
        "061's label refusal must still fire, with the block now admitted by the \
         converter; got: {errs:#?}",
    );
}

/// PASSES EITHER WAY BY DESIGN. The shape WI-1072 refuses at the BLOCK's own span, and
/// the one the converter still decides alone: a body ⇒ a clause, which is
/// `rule_reading`'s first line, so the two passes cannot part ways on it.
#[test]
fn a_bodied_unlabeled_rules_block_is_still_refused_at_parse() {
    const SRC: &str = r#"namespace vfakk.bodied
                           {< has no target >}
                           rule adult(?x) :- person(?x)
                         end"#;
    let errs = parse_errs(SRC);
    assert_eq!(errs.len(), 1, "one block, one refusal: {errs:?}");
    assert!(
        errs[0].contains("description block on unlabeled rule")
            && errs[0].contains("no stable target"),
        "the converter must still name the construct and the missing target; got {:?}",
        errs[0],
    );
}

/// PASSES EITHER WAY BY DESIGN, and it is the row that pins the split point. `:- true`
/// is 061's spelling of a body-less ASSERTION — the desugaring `fact` takes, and the
/// remedy 061's own diagnostic offers — so it reads as a CLAUSE, not a declaration, and
/// its block has no target. It looks like the admitted shape and must not behave like
/// one.
#[test]
fn an_asserting_bodyless_rule_is_still_a_clause() {
    const SRC: &str = r#"namespace vfakk.assert_true
                           {< has no target >}
                           rule p(1) :- true
                         end"#;
    let errs = parse_errs(SRC);
    assert_eq!(
        errs.len(),
        1,
        "`:- true` is an assertion, so its unlabeled block still has no target: {errs:?}",
    );
    assert!(
        errs[0].contains("description block on unlabeled rule"),
        "and it is refused as the CLAUSE it is, by the converter; got {:?}",
        errs[0],
    );
}

/// PASSES EITHER WAY BY DESIGN, and it closes `rule_reading`'s third arm. A QUALIFIED
/// body-less head references rather than introduces, so it declares nothing and asserts
/// nothing — already a located refusal (061). The block rides on a rule that is refused
/// whole, which is why admitting it at the converter cannot turn this into an
/// acceptance: what changes is only which pass says so.
#[test]
fn a_bodyless_rule_that_declares_nothing_is_still_refused() {
    const SRC: &str = r#"
namespace vfakk.nothing
  {< has nothing to attach to >}
  rule vfakk.nothing.qualified(?a)
end
"#;
    let errs = load_errs(SRC);
    assert!(
        errs.iter()
            .any(|e| e.contains("a rule with no body DECLARES a predicate")),
        "a body-less rule that declares nothing must keep its own 061 refusal, not \
         acquire a description one; got: {errs:#?}",
    );
}

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
//! WHAT THE SPLIT WAS. A rule had a description target when it was LABELED (the
//! citation handle) or when it DECLARED (the predicate symbol). An unlabeled rule that
//! stored a CLAUSE had neither, and was refused. Since WI-20261121-MVQP8 it has the label
//! the converter generates for it, its head's name and a content hash
//! (`wi_mvqp8_generated_label_test`), so the refusal
//! rows below now read that label back; the rows were refusals until then, measured.
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
//!   * the LOADER's §4.1 refusal (the `Clause` arm) — 1 red, 3918 green: the equation
//!     row alone, by LOADING CLEAN with the block SILENTLY DROPPED. That arm now emits
//!     the block on the equation's generated label (WI-20261121-MVQP8).
//!
//! (The first version of this note claimed the equation row failed on its LOCATION
//! assertion under the converter back-out. It does not — it panics before reaching
//! one. /code-review measured it.)
//!
//! WHICH ROWS PASS EITHER WAY BY DESIGN — the CONTROLS, each guarding a refusal this
//! must NOT relax:
//!   * `a_labeled_declaration_is_still_refused_by_061`
//!   * `a_bodyless_rule_that_declares_nothing_is_still_refused`
//! Two more were controls until WI-20261121-MVQP8 and read its generated label now:
//!   * `a_bodied_unlabeled_rules_block_names_its_generated_label`
//!   * `an_asserting_bodyless_rule_is_still_a_clause` (`:- true`, 061's assertion
//!     spelling — body-less in intent, a CLAUSE to `rule_reading`, so its block names its
//!     clause's label and not a declared predicate)
//!
//! THE POPULATION IS `rule_reading`'s THREE ARMS, not the two the ticket named:
//! `Declaration` (the three emission rows), `Clause` (the equation row, on its generated
//! label), and `DeclaresNothing` (the last control). Every body-less rule the converter
//! carries a block for lands in exactly one of them, and none of the three drops it in
//! silence.

use crate::common::{load_kb_with, try_load_kb_with};
use crate::wi1070_operation_description_test::descriptions_of;
use crate::wi_mvqp8_generated_label_test::{is_generated, target_of};

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

/// A body-less EQUATION head stores a clause headed by the connective, so its subject
/// declares no predicate and the declaration's target is not there. Until
/// WI-20261121-MVQP8 the loader refused its block; it now names the label generated
/// from the equation's text.
#[test]
fn a_bodyless_equation_head_names_its_generated_label() {
    const SRC: &str = r#"
namespace vfakk.eqn
  import anthill.prelude.Int64
  {< the equation's own intent >}
  rule twice(?x) <=> ?x
end
"#;
    let kb = load_kb_with(SRC);
    let target = target_of(&kb, "the equation's own intent");
    assert!(is_generated(&target, "vfakk.eqn.twice"), "{target}");
    assert!(
        descriptions_of(&kb, "vfakk.eqn.twice").is_empty(),
        "and not the subject, which the equation does not declare",
    );
    // ... and the LABELED spelling of the same rule still names its label.
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

/// The shape WI-1072 refused at the BLOCK's own span — a body ⇒ a clause — names its
/// generated label since WI-20261121-MVQP8.
#[test]
fn a_bodied_unlabeled_rules_block_names_its_generated_label() {
    let kb = load_kb_with(
        r#"namespace vfakk.bodied
             fact person(1)
             {< who is an adult >}
             rule adult(?x) :- person(?x)
           end"#,
    );
    let target = target_of(&kb, "who is an adult");
    assert!(is_generated(&target, "vfakk.bodied.adult"), "{target}");
}

/// The row that pins the split point. `:- true` is 061's spelling of a body-less
/// ASSERTION — the desugaring `fact` takes — so it reads as a CLAUSE, not a declaration:
/// its block names the clause's generated label, and the predicate `p` gets none.
#[test]
fn an_asserting_bodyless_rule_is_still_a_clause() {
    let kb = load_kb_with(
        r#"namespace vfakk.assert_true
             {< one row >}
             rule p(1) :- true
           end"#,
    );
    let target = target_of(&kb, "one row");
    assert!(is_generated(&target, "vfakk.assert_true.p"), "{target}");
    assert!(
        descriptions_of(&kb, "vfakk.assert_true.p").is_empty(),
        "an assertion declares nothing, so its block is not the predicate's",
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

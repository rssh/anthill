//! WI-1072 — EVERY ADMITTED DECLARATION DESCRIPTION HAS A STABLE, QUERYABLE TARGET.
//!
//! WI-1070 closed the drop for `operation` and `const`; the grammar already accepts
//! the same leading `description` field on `entity`, `rule`, `constraint`, `fact`, and
//! `namespace`. The converter dropped all five. This suite makes the target policy
//! explicit rather than treating "it loads" as evidence:
//!
//! * a named declaration (`entity`, labeled `rule`, labeled `constraint`, namespace)
//!   emits `DescriptionInfo` whose `target` is that declaration's qualified name;
//! * a description on an anonymous declaration (fact, unlabeled rule/constraint) was
//!   refused during conversion because no stable citation/name target existed;
//!   WI-20260830-VFAKK narrowed the RULE half of that — a body-less rule is proposal
//!   061's DECLARATION and names a predicate — and WI-20261121-MVQP8 closed the rest:
//!   each names the label the converter generates for it (`wi_mvqp8_generated_label_test`);
//! * the four pre-existing stdlib entity blocks are recovered; and
//! * sort/enum/operation/const are controls, unchanged by this extension.
//!
//! BACK-OUT MATRIX. Removing the WI-1072 implementation makes every positive named
//! row return `[]` and the stdlib row lose all four descriptions; removing
//! WI-20261121-MVQP8's makes the anonymous row a parse refusal again. The control row
//! passes either way by design; it proves the extension did not move the four
//! already-working declaration kinds.

use crate::common::load_kb_with;
use crate::wi1070_operation_description_test::descriptions_of;
use crate::wi_mvqp8_generated_label_test::{is_generated, target_of};

#[test]
fn entity_descriptions_name_free_standing_and_nested_constructors() {
    const SRC: &str = r#"
namespace wi1072.entity
  import anthill.prelude.Int64

  {< free-standing entity >}
  entity Rec(n: Int64)

  sort Wrap
    {< nested constructor >}
    entity W(n: Int64)
  end
end
"#;
    let kb = load_kb_with(SRC);
    assert_eq!(
        descriptions_of(&kb, "wi1072.entity.Rec"),
        vec![(0, "free-standing entity".to_string())],
        "a free-standing entity's own block must name that entity",
    );
    assert_eq!(
        descriptions_of(&kb, "wi1072.entity.Wrap.W"),
        vec![(0, "nested constructor".to_string())],
        "a sort-body entity's own block must name the constructor, not its sort",
    );
}

#[test]
fn labeled_multi_head_rule_description_emits_once_on_the_citation_handle() {
    const SRC: &str = r#"
namespace wi1072.rule
  {< one description for one citation handle >}
  rule law: p(1), q(1) :- true
  describe law {< standalone companion >}
end
"#;
    let kb = load_kb_with(SRC);
    assert_eq!(
        descriptions_of(&kb, "wi1072.rule.law"),
        vec![
            (0, "one description for one citation handle".to_string()),
            (1, "standalone companion".to_string()),
        ],
        "a multi-head rule has one label target: emit once, outside the per-head loop, \
         and share that exact target with standalone `describe`",
    );
}

#[test]
fn labeled_constraint_description_names_the_constraint() {
    const SRC: &str = r#"
namespace wi1072.constraint
  fact p(1)
  {< labeled denial >}
  constraint distinct: p(?x), p(?x)
end
"#;
    let kb = load_kb_with(SRC);
    assert_eq!(
        descriptions_of(&kb, "wi1072.constraint.distinct"),
        vec![(0, "labeled denial".to_string())],
        "a constraint label is its stable description target and must be qualified in \
         the declaring scope",
    );
}

#[test]
fn top_level_and_nested_namespace_descriptions_name_the_namespace() {
    const SRC: &str = r#"
{< outer namespace >}
namespace wi1072.space
  {< nested namespace >}
  namespace inner
  end
end
"#;
    let kb = load_kb_with(SRC);
    assert_eq!(
        descriptions_of(&kb, "wi1072.space"),
        vec![(0, "outer namespace".to_string())],
        "a description before a top-level namespace must attach to that namespace",
    );
    assert_eq!(
        descriptions_of(&kb, "wi1072.space.inner"),
        vec![(0, "nested namespace".to_string())],
        "the identical surface before a nested namespace must attach to the child",
    );
}

/// The three shapes this suite refused as anonymous — a fact, an unlabeled rule that stores
/// a clause, an unlabeled constraint — have a target since WI-20261121-MVQP8: the label
/// the converter generates for each, its head's name and a hash of its content. Measured
/// before it: each was refused at parse with "description block on … has no stable
/// target".
#[test]
fn anonymous_declaration_descriptions_name_their_generated_label() {
    const CASES: [(&str, &str); 3] = [
        (
            "wi1072.anon_fact.p",
            r#"namespace wi1072.anon_fact
                 {< its own >}
                 fact p(1)
               end"#,
        ),
        // `:- true` is the explicit empty body — an ASSERTION under 061 — so it stores a
        // clause, and takes a label.
        (
            "wi1072.anon_rule.p",
            r#"namespace wi1072.anon_rule
                 {< its own >}
                 rule p(1) :- true
               end"#,
        ),
        (
            "wi1072.anon_constraint.p",
            r#"namespace wi1072.anon_constraint
                 fact p(1)
                 {< its own >}
                 constraint p(?x), p(?x)
               end"#,
        ),
    ];
    for (name, src) in CASES {
        let kb = load_kb_with(src);
        let target = target_of(&kb, "its own");
        assert!(is_generated(&target, name), "{name}: the block names the generated label, got {target}");
        assert_eq!(descriptions_of(&kb, &target), vec![(0, "its own".to_string())]);
    }
}

#[test]
fn the_four_stdlib_entity_blocks_are_no_longer_silent() {
    let kb = load_kb_with("");
    const EXPECTED: [(&str, &str); 4] = [
        ("anthill.prelude.TypeExtractor.Arrow", "WI-20261104-6HVXM"),
        ("anthill.prelude.TypeExtractor.ExprCarried", "WI-376"),
        (
            "anthill.prelude.TypeExtractor.RigidTypeProjection",
            "WI-428",
        ),
        (
            "anthill.prelude.TypeExtractor.Error",
            "not a well-formed type",
        ),
    ];
    for (target, sentinel) in EXPECTED {
        let rows = descriptions_of(&kb, target);
        assert_eq!(
            rows.len(),
            1,
            "{target} must recover its one written block: {rows:?}"
        );
        assert!(
            rows[0].1.contains(sentinel),
            "{target}'s recovered text must be the block written at that entity: {rows:?}",
        );
    }
}

/// PASSES EITHER WAY BY DESIGN. These four kinds already emitted before WI-1072;
/// keeping the control in the new suite makes an accidental double-emission or target
/// drift visible at the same site as the extension.
#[test]
fn sort_enum_operation_and_const_descriptions_are_unchanged() {
    const SRC: &str = r#"
namespace wi1072.control
  import anthill.prelude.Int64

  {< existing sort >}
  sort Plain
  end

  {< existing enum >}
  enum Colour
    entity Red
  end

  {< existing operation >}
  operation id(x: Int64) -> Int64 = x

  {< existing const >}
  const answer: Int64 = 42
end
"#;
    let kb = load_kb_with(SRC);
    for (target, text) in [
        ("wi1072.control.Plain", "existing sort"),
        ("wi1072.control.Colour", "existing enum"),
        ("wi1072.control.id", "existing operation"),
        ("wi1072.control.answer", "existing const"),
    ] {
        assert_eq!(
            descriptions_of(&kb, target),
            vec![(0, text.to_string())],
            "{target}: the existing declaration-description path must stay exactly one fact",
        );
    }
}

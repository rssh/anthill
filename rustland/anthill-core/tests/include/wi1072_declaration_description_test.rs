//! WI-1072 — EVERY ADMITTED DECLARATION DESCRIPTION HAS A STABLE, QUERYABLE TARGET.
//!
//! WI-1070 closed the drop for `operation` and `const`; the grammar already accepts
//! the same leading `description` field on `entity`, `rule`, `constraint`, `fact`, and
//! `namespace`. The converter dropped all five. This suite makes the target policy
//! explicit rather than treating "it loads" as evidence:
//!
//! * a named declaration (`entity`, labeled `rule`, labeled `constraint`, namespace)
//!   emits `DescriptionInfo` whose `target` is that declaration's qualified name;
//! * a description on an anonymous declaration (fact, unlabeled rule/constraint) is
//!   refused during conversion because no stable citation/name target exists;
//! * the four pre-existing stdlib entity blocks are recovered; and
//! * sort/enum/operation/const are controls, unchanged by this extension.
//!
//! BACK-OUT MATRIX. Removing the WI-1072 implementation makes every positive named
//! row return `[]`, the stdlib row lose all four descriptions, and every anonymous
//! row parse clean (the old silent drop). The control row passes either way by design;
//! it proves the extension did not move the four already-working declaration kinds.

use crate::common::{load_kb_with, parse_errs};
use crate::wi1070_operation_description_test::descriptions_of;

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

#[test]
fn anonymous_declaration_descriptions_are_refused_not_dropped() {
    const CASES: [(&str, &str); 3] = [
        (
            "fact",
            r#"namespace wi1072.anon_fact
                 {< has no target >}
                 fact p(1)
               end"#,
        ),
        (
            "unlabeled rule",
            r#"namespace wi1072.anon_rule
                 {< has no target >}
                 rule p(1) :- true
               end"#,
        ),
        (
            "unlabeled constraint",
            r#"namespace wi1072.anon_constraint
                 {< has no target >}
                 constraint p(?x), p(?x)
               end"#,
        ),
    ];

    for (kind, src) in CASES {
        let errors = parse_errs(src);
        assert_eq!(
            errors.len(),
            1,
            "{kind}: one unsupported description must produce one precise refusal: {errors:?}",
        );
        assert!(
            errors[0].contains("description block")
                && errors[0].contains(kind)
                && errors[0].contains("no stable target"),
            "{kind}: refusal must name both the written construct and the missing \
             target, got {:?}",
            errors[0],
        );
    }
}

#[test]
fn the_four_stdlib_entity_blocks_are_no_longer_silent() {
    let kb = load_kb_with("");
    const EXPECTED: [(&str, &str); 4] = [
        ("anthill.prelude.TypeExtractor.Arrow", "WI-791"),
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

//! DV7DP: metadata must be readable through an Anthill rule and SLD resolution.
//! Removing declaration fact emission breaks the tagged AND empty-block queries,
//! shared-name queries, and scope checks. The rule-metadata and unlabeled-constraint
//! tests are controls: they pass without declaration metadata by design. What a
//! bracket right after a type means is WI-20260915-G9EA9's, in its own test file.
//!
//! `kind` is driven from Anthill too: every declaration is also read through a rule
//! that names its `MemberKind` (`kind: Sort`), and `shared_names_keep_each_declarations_block`
//! reads both kinds back for one name — in its equal-block iteration the two heads
//! differ ONLY in `kind`.

use std::collections::HashSet;

use anthill_core::kb::load::{meta_has_flag, meta_value};
use anthill_core::kb::op_info;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::KnowledgeBase;

const TAGGED: &str = r#"
namespace test.dv7dp
  import anthill.prelude.{Int64}

  sort Tagged
    entity tagged(n: Int64) @[Marker, Key: 7]
    entity plain(n: Int64)
  end @[Marker, Key: 7]

  sort Id = ? @[Marker, Key: 7]

  enum Colour
    entity red
    entity green
  end @[Marker, Key: 7]

  entity loose(n: Int64) @[Marker, Key: 7]

  const LIMIT: Int64 = 7 @[Marker, Key: 7]

  rule small(?n) :- tagged(n: ?n)
  rule named: small(?n) :- plain(n: ?n) @[Marker, Key: 7]

  constraint bounded: small(?n) :- ?n > 100 @[Marker, Key: 7]

  operation twice(n: Int64) -> Int64
    = n + n @[Marker, Key: 7]
end
"#;

const UNTAGGED: &str = r#"
namespace test.dv7dp
  import anthill.prelude.{Int64}

  sort Tagged
    entity tagged(n: Int64)
    entity plain(n: Int64)
  end

  sort Id = ?

  enum Colour
    entity red
    entity green
  end

  entity loose(n: Int64)

  const LIMIT: Int64 = 7

  constraint bounded: tagged(n: ?n) :- ?n > 100

  operation twice(n: Int64) -> Int64 = n + n
end
"#;

/// Each declaration with the `MemberKind` its row must carry.
const DECLARED: &[(&str, &str)] = &[
    ("test.dv7dp.Tagged", "Sort"),
    ("test.dv7dp.Tagged.tagged", "Constructor"),
    ("test.dv7dp.Id", "Sort"),
    ("test.dv7dp.Colour", "Enum"),
    ("test.dv7dp.loose", "Constructor"),
    ("test.dv7dp.LIMIT", "Const"),
    ("test.dv7dp.bounded", "Constraint"),
    ("test.dv7dp.twice", "Operation"),
];

// The reader is written in Anthill, so this tests declared field layout, name
// resolution and query execution together, rather than walking host-side storage.
//
// Each name reaches the join through a `Term`-typed FACT, never written in the rule
// body: a rule-body value slot has no reading for a sort, operation or constraint label
// (`SortInfo(name: Tagged)` is refused the same way — WI-206 gates the sort rung on a
// `Type` slot, WI-40KSW is its message), while a fact argument is data. The same
// join is how any reader reaches the row: from `SortInfo(name: ?s)` and its kin.
//
// Per subject `i`: `read{i}` answers every row for the name, `own{i}` only the row
// whose `kind` is the one written beside the name.
fn load_readers(src: &str, names: &[(&str, &str)]) -> KnowledgeBase {
    let mut src = src.to_owned();
    src.push_str(
        "\nnamespace test.dv7dp.readers\n import anthill.prelude.{Int64}\n \
         import anthill.reflect.{DeclarationMeta, Term}\n \
         import anthill.reflect.MemberKind.{Sort, Enum, Constructor, Const, Constraint, Operation, Rule, Namespace}\n \
         entity Subject(key: Int64, name: Term)\n",
    );
    let mut imported = HashSet::new();
    for (i, (name, kind)) in names.iter().enumerate() {
        let local = match name.rsplit_once('.') {
            Some((parent, local)) => {
                if imported.insert(*name) {
                    src.push_str(&format!(" import {parent}.{{{local}}}\n"));
                }
                local
            }
            None => name,
        };
        src.push_str(&format!(
            " fact Subject(key: {i}, name: {local})\n \
             rule subject{i}(?s) :- Subject(key: {i}, name: ?s)\n \
             rule read{i}(?m) :- Subject(key: {i}, name: ?s), DeclarationMeta(name: ?s, kind: ?, meta: ?m)\n \
             rule own{i}(?m) :- Subject(key: {i}, name: ?s), DeclarationMeta(name: ?s, kind: {kind}, meta: ?m)\n \
             rule kinds{i}(?k) :- Subject(key: {i}, name: ?s), DeclarationMeta(name: ?s, kind: ?k, meta: ?)\n"
        ));
    }
    src.push_str("end\n");
    crate::common::load_kb_with(&src)
}

/// The `MemberKind` variant names `kinds{i}` answers, sorted. Rows are counted by
/// kind, not by `read{i}`'s answers: two rows with equal blocks give `read{i}` one
/// answer, since its head projects only the block.
fn kinds(kb: &mut KnowledgeBase, i: usize) -> Vec<String> {
    let mut kinds: Vec<String> = crate::common::query_unary(kb, &format!("test.dv7dp.readers.kinds{i}"))
        .into_iter()
        .map(|(value, _)| match kb.get_term(value.expect_term()) {
            Term::Ref(s) => kb.qualified_name_of(*s).to_owned(),
            Term::Fn { functor, .. } => kb.qualified_name_of(*functor).to_owned(),
            term => panic!("kind must name a MemberKind variant, got {term:?}"),
        })
        .collect();
    kinds.sort();
    kinds
}

/// The blocks `reader{i}` answers (`reader` is `read` or `own`).
fn blocks(kb: &mut KnowledgeBase, reader: &str, i: usize) -> Vec<TermId> {
    // The subject row is the control on an EMPTY answer: without it, a fact naming
    // nothing would read as "no metadata" and pass the negative cases.
    let subjects = crate::common::query_unary(kb, &format!("test.dv7dp.readers.subject{i}"));
    assert_eq!(subjects.len(), 1, "subject {i} must name its declaration");
    crate::common::query_unary(kb, &format!("test.dv7dp.readers.{reader}{i}"))
        .into_iter()
        .map(|(value, definite)| {
            assert!(definite, "metadata query must be definite");
            value.expect_term()
        })
        .collect()
}

fn assert_tagged(kb: &KnowledgeBase, meta: TermId) {
    assert!(meta_has_flag(kb, Some(meta), "Marker"));
    let key = meta_value(kb, Some(meta), "Key").expect("Key present");
    assert!(matches!(kb.get_term(key), Term::Const(Literal::Int(7))));
    assert!(!meta_has_flag(kb, Some(meta), "Absent"));
}

// An answer reads the empty `meta()` back as the bare `Ref(meta)`: a nullary
// application and its name are one discrimination key (WI-719), and the meta readers
// see no attributes in either.
fn assert_empty(kb: &KnowledgeBase, meta: TermId) {
    let functor = match kb.get_term(meta) {
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } if pos_args.is_empty() && named_args.is_empty() => *functor,
        Term::Ref(functor) => *functor,
        term => panic!("expected empty meta(), got {term:?}"),
    };
    assert_eq!(kb.qualified_name_of(functor), "meta");
}

#[test]
fn every_declaration_kind_is_queryable() {
    let mut kb = load_readers(TAGGED, DECLARED);
    for (i, (name, kind)) in DECLARED.iter().enumerate() {
        assert_eq!(
            kinds(&mut kb, i),
            [format!("anthill.reflect.MemberKind.{kind}")],
            "{name}"
        );
        for reader in ["read", "own"] {
            let rows = blocks(&mut kb, reader, i);
            assert_eq!(rows.len(), 1, "{reader} {name} ({kind})");
            assert_tagged(&kb, rows[0]);
        }
    }
}

#[test]
fn declarations_without_blocks_query_as_empty_meta() {
    let mut kb = load_readers(UNTAGGED, DECLARED);
    for (i, (name, kind)) in DECLARED.iter().enumerate() {
        for reader in ["read", "own"] {
            let rows = blocks(&mut kb, reader, i);
            assert_eq!(rows.len(), 1, "{reader} {name} ({kind})");
            assert_empty(&kb, rows[0]);
        }
    }
}

#[test]
fn operation_relation_uses_operation_info_term() {
    let mut kb = load_readers(TAGGED, &[("test.dv7dp.twice", "Operation")]);
    let rows = blocks(&mut kb, "own", 0);
    let twice = kb.try_resolve_symbol("test.dv7dp.twice").unwrap();
    let info = op_info::lookup_operation_info(&kb, twice).unwrap();
    assert_eq!(rows, vec![info.meta.unwrap()]);
}

#[test]
fn sort_block_resolves_its_own_members() {
    let mut kb = load_readers(
        r#"
namespace test.dv7dp
 import anthill.prelude.{Int64}
 sort Box
   sort T = ?
   const SIZE: Int64 = 3
   entity box(v: T)
 end @[Elem: T, Size: SIZE]
end
"#,
        &[("test.dv7dp.Box", "Sort")],
    );
    let rows = blocks(&mut kb, "own", 0);
    assert_eq!(rows.len(), 1);
    for (key, name) in [
        ("Elem", "test.dv7dp.Box.T"),
        ("Size", "test.dv7dp.Box.SIZE"),
    ] {
        let value = meta_value(&kb, Some(rows[0]), key).unwrap();
        assert_eq!(
            kb.get_term(value),
            &Term::Ref(kb.try_resolve_symbol(name).unwrap())
        );
    }
}

#[test]
fn shared_names_keep_each_declarations_block() {
    // An eponymous constructor IS its sort (§6.3, one symbol), so both rows carry one
    // name; `kind` is what keeps them two. The EQUAL-block iteration is the one that
    // needs it: the two heads then differ only in `kind`.
    for sort_block in ["@[Marker, Key: 7]", "@[Other]", ""] {
        let source = format!(
            "namespace test.dv7dp\n sort Point\n entity Point @[Marker, Key: 7]\n end {sort_block}\nend\n"
        );
        let mut kb = load_readers(
            &source,
            &[("test.dv7dp.Point", "Sort"), ("test.dv7dp.Point", "Constructor")],
        );
        assert_eq!(
            kinds(&mut kb, 0),
            ["anthill.reflect.MemberKind.Constructor", "anthill.reflect.MemberKind.Sort"],
            "sort block `{sort_block}`"
        );

        let ctor = blocks(&mut kb, "own", 1);
        assert_eq!(ctor.len(), 1);
        assert_tagged(&kb, ctor[0]);

        let sort = blocks(&mut kb, "own", 0);
        assert_eq!(sort.len(), 1);
        match sort_block {
            "@[Other]" => {
                assert!(meta_has_flag(&kb, Some(sort[0]), "Other"));
                assert!(!meta_has_flag(&kb, Some(sort[0]), "Marker"));
            }
            "" => assert_empty(&kb, sort[0]),
            _ => assert_tagged(&kb, sort[0]),
        }
    }
}

#[test]
fn redeclared_parameter_keeps_only_its_written_block() {
    // A header parameter and its written redeclaration are one parameter reaching the
    // loader twice (a desugared `sort T = ?` / HK `sort F … end` beside the written one):
    // ONE row, the written block — never an empty `meta()` beside it. The unredeclared
    // `Plain.U` is the control that a parameter without a block still reads as empty.
    let mut kb = load_readers(
        "namespace test.dv7dp\n \
         sort Box[T]\n sort T = ? @[Marker, Key: 7]\n entity box(v: T)\n end\n \
         sort Spec[F[E]]\n sort F\n end @[Marker, Key: 7]\n end\n \
         sort Plain[U]\n entity plain(v: U)\n end\n\
         end\n",
        &[
            ("test.dv7dp.Box.T", "Sort"),
            ("test.dv7dp.Spec.F", "Sort"),
            ("test.dv7dp.Plain.U", "Sort"),
        ],
    );
    for i in 0..2 {
        let rows = blocks(&mut kb, "read", i);
        assert_eq!(rows.len(), 1, "parameter {i}");
        assert_tagged(&kb, rows[0]);
        assert_eq!(kinds(&mut kb, i), ["anthill.reflect.MemberKind.Sort"]);
    }
    let rows = blocks(&mut kb, "read", 2);
    assert_eq!(rows.len(), 1);
    assert_empty(&kb, rows[0]);
}

#[test]
fn documented_joins_reach_each_members_own_row() {
    // The spec's two joins, run: `SortInfo` binds the name a rule cannot write, and
    // `MemberInfo`'s `kind` selects the member's own row out of the name's two.
    let mut kb = crate::common::load_kb_with(
        r#"
namespace test.dv7dp
  import anthill.reflect.{SortInfo, MemberInfo, DeclarationMeta}
  import anthill.reflect.MemberKind.{Sort}

  sort Point
    entity Point @[OnConstructor]
  end @[OnSort]

  enum Colour
    entity red
  end @[OnEnum]

  rule sort_attributes(?m) :- SortInfo(name: ?s), DeclarationMeta(name: ?s, kind: Sort, meta: ?m)
  rule member_attributes(?m) :- MemberInfo(name: ?s, kind: ?k), DeclarationMeta(name: ?s, kind: ?k, meta: ?m)
end
"#,
    );
    let flags = |kb: &mut KnowledgeBase, rule: &str| -> Vec<&'static str> {
        let answers = crate::common::query_unary(kb, &format!("test.dv7dp.{rule}"));
        let mut flags: Vec<&'static str> = ["OnSort", "OnConstructor", "OnEnum"]
            .into_iter()
            .filter(|flag| {
                answers
                    .iter()
                    .any(|(value, _)| meta_has_flag(kb, Some(value.expect_term()), flag))
            })
            .collect();
        flags.sort();
        flags
    };
    // `kind: Sort` is a `sort … end`'s row only: the enum's is `Enum`, the eponymous
    // constructor's `Constructor`.
    assert_eq!(flags(&mut kb, "sort_attributes"), ["OnSort"]);
    // MemberInfo lists `Point` once, as `Sort` (§6.3: not a member of itself), and
    // `Colour` as `Enum` — each joins its own row.
    assert_eq!(flags(&mut kb, "member_attributes"), ["OnEnum", "OnSort"]);
}

#[test]
fn top_level_declarations_are_queryable() {
    let mut kb = load_readers(
        "sort Loose\n entity loose\nend @[Marker, Key: 7]\nentity Free @[Marker, Key: 7]\n",
        &[("Loose", "Sort"), ("Free", "Constructor")],
    );
    for i in 0..2 {
        let rows = blocks(&mut kb, "own", i);
        assert_eq!(rows.len(), 1);
        assert_tagged(&kb, rows[0]);
    }
}

#[test]
fn rules_keep_clause_metadata() {
    let mut kb = load_readers(
        TAGGED,
        &[
            ("test.dv7dp.named", "Rule"),
            ("test.dv7dp.small", "Rule"),
            ("test.dv7dp", "Namespace"),
        ],
    );
    for i in 0..3 {
        assert!(blocks(&mut kb, "read", i).is_empty());
    }
    let label = kb.try_resolve_symbol("test.dv7dp.named").unwrap();
    let functor = kb.try_resolve_symbol("test.dv7dp.small").unwrap();
    let rid = kb
        .rules_by_functor(functor)
        .into_iter()
        .find(|&rid| kb.rule_label(rid) == Some(label))
        .unwrap();
    assert!(meta_has_flag(&kb, kb.rule_meta(rid), "Marker"));
}

#[test]
fn unlabeled_constraint_block_is_refused() {
    let errs = crate::common::parse_errs(
        "namespace test.dv7dp\n import anthill.prelude.{Int64}\n entity tagged(n: Int64)\n constraint tagged(n: ?n) :- ?n > 100 @[Marker]\nend\n",
    );
    crate::common::assert_refused_naming(
        &errs,
        &["unlabeled constraint", "label"],
        "constraint block",
    );
}

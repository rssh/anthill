//! WI-20260915-G9EA9 — a meta block opens with the single token `@[`, in every position.
//!
//! A bare `[` competed with type arguments (`sort Ids = List [M]` loaded as `List[M]`),
//! with the next rule entry's collection-literal head (WI-893) and with a dot-callee
//! bracket (BAD3V). The block is now `@[…]`, trailing the declaration or clause it
//! belongs to, and the retired spellings are refused with a message naming the new one.
//!
//! CONTROLS. On the pre-G9EA9 grammar every `@[` fixture here fails to load — as a
//! syntax error, or, where `@` could read as the arrow-effect infix (`7 @ [simp]`), as a
//! Pratt desugaring error — so each capability test fails there;
//! `the_retired_spellings_are_refused_naming_the_block` fails there too, because all but
//! the `@ [` row parsed clean as blocks. The `[Int64]`
//! rows of `a_block_after_a_type_is_the_declarations` and the over-application refusal
//! pass on both grammars by design: they pin that a bare bracket after a type is, and
//! stays, type arguments.

use anthill_core::eval::Value;
use anthill_core::kb::load::meta_has_flag;
use anthill_core::kb::op_info;
use anthill_core::kb::term::{Term, TermId};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use anthill_core::parse::ir::{Item, ProofBody};

/// `DeclarationMeta` rows for each qualified name, read by an Anthill rule joined through
/// a `Term`-typed fact (a rule body cannot spell a sort or operation in that slot).
fn declaration_blocks(src: &str, names: &[&str]) -> (KnowledgeBase, Vec<Vec<TermId>>) {
    let mut src = src.to_owned();
    src.push_str(
        "\nnamespace test.g9ea9.readers\n import anthill.prelude.{Int64}\n \
         import anthill.reflect.{DeclarationMeta, Term}\n \
         entity Subject(key: Int64, name: Term)\n",
    );
    for (i, name) in names.iter().enumerate() {
        let (parent, local) = name.rsplit_once('.').expect("qualified name");
        src.push_str(&format!(
            " import {parent}.{{{local}}}\n fact Subject(key: {i}, name: {local})\n \
             rule read{i}(?m) :- Subject(key: {i}, name: ?s), DeclarationMeta(name: ?s, kind: ?, meta: ?m)\n"
        ));
    }
    src.push_str("end\n");
    let mut kb = crate::common::load_kb_with(&src);
    let rows = (0..names.len())
        .map(|i| {
            crate::common::query_unary(&mut kb, &format!("test.g9ea9.readers.read{i}"))
                .into_iter()
                .map(|(v, _)| v.expect_term())
                .collect()
        })
        .collect();
    (kb, rows)
}

/// The empty block reads back as `meta()` or its bare name (WI-719); neither has keys.
fn is_empty_meta(kb: &KnowledgeBase, m: TermId) -> bool {
    match kb.get_term(m) {
        Term::Fn { pos_args, named_args, .. } => pos_args.is_empty() && named_args.is_empty(),
        Term::Ref(_) => true,
        _ => false,
    }
}

#[test]
fn a_rule_and_a_rule_entry_block_fire() {
    // `@[simp]` is the enablement (§5.3): the tagged law replaces the body's answer, and
    // the untagged sibling — same shape, no block — leaves its operation's body standing.
    const SRC: &str = r#"
namespace test.g9ea9.rules
  import anthill.prelude.Int64
  operation tau() -> Int64 = 1
  operation sigma() -> Int64 = 1
  operation rho() -> Int64 = 1
  rule tau() <=> 7 @[simp]
  rule {
    sigma() <=> 8 @[simp]
  }
  rule rho() <=> 9
  operation drive_tau() -> Int64 = tau()
  operation drive_sigma() -> Int64 = sigma()
  operation drive_rho() -> Int64 = rho()
end
"#;
    let mut interp = crate::common::interp_for(SRC);
    for (path, want) in [
        ("test.g9ea9.rules.drive_tau", 7),
        ("test.g9ea9.rules.drive_sigma", 8),
        ("test.g9ea9.rules.drive_rho", 1),
    ] {
        match interp.call(path, &[]) {
            Ok(Value::Int(n)) if n == want => {}
            other => panic!("{path} must answer {want}; got {other:?}"),
        }
    }
}

#[test]
fn a_bare_name_before_the_block_is_not_an_instantiation() {
    // §5.3's retired trap: `<=> constant [simp]` read as `constant[simp]`, so a nullary
    // RHS needed its parentheses. `@[` begins no instantiation bracket, so the bare RHS
    // and the parenthesised one are the same law — CONTROL: `pick(2)`, written `()`,
    // answers the value `pick(1)` must equal.
    const SRC: &str = r#"
namespace test.g9ea9.trap
  import anthill.prelude.Int64
  enum Mono
    entity constant
    entity monotone
  end
  operation pick(n: Int64) -> Mono
  rule pick(1) <=> constant @[simp]
  rule pick(2) <=> constant() @[simp]
  operation bare() -> Mono = pick(1)
  operation paren() -> Mono = pick(2)
end
"#;
    let mut interp = crate::common::interp_for(SRC);
    let bare = interp.call("test.g9ea9.trap.bare", &[]).expect("bare RHS fires");
    let paren = interp.call("test.g9ea9.trap.paren", &[]).expect("parenthesised RHS fires");
    assert_eq!(format!("{bare:?}"), format!("{paren:?}"));
}

#[test]
fn a_fact_block_is_its_clause_metadata() {
    let kb = crate::common::load_kb_with(
        "namespace test.g9ea9.facts\n import anthill.prelude.Int64\n entity point(n: Int64)\n \
         fact point(n: 1) @[trust: axiom]\n fact point(n: 2)\nend\n",
    );
    let point = kb.try_resolve_symbol("test.g9ea9.facts.point").unwrap();
    let flagged: Vec<bool> = kb
        .rules_by_functor(point)
        .into_iter()
        .map(|rid| meta_has_flag(&kb, kb.rule_meta(rid), "trust"))
        .collect();
    assert_eq!(flagged.len(), 2);
    assert_eq!(flagged.iter().filter(|&&f| f).count(), 1, "exactly the tagged fact");
}

#[test]
fn operation_declaration_and_entry_blocks_reach_operation_info() {
    let kb = crate::common::load_kb_with(
        r#"
namespace test.g9ea9.ops
  import anthill.prelude.Int64
  sort S
    entity s
    operation single() -> Int64
      = 1 @[Marker]
    operation {
      entry() -> Int64 @[Marker]
    }
  end
end
"#,
    );
    for name in ["test.g9ea9.ops.S.single", "test.g9ea9.ops.S.entry"] {
        let sym = kb.try_resolve_symbol(name).unwrap();
        let info = op_info::lookup_operation_info(&kb, sym).unwrap();
        assert!(meta_has_flag(&kb, info.meta, "Marker"), "{name}");
    }
}

#[test]
fn a_proof_step_block_is_the_steps_rule_metadata() {
    let parsed = parse::parse(
        "namespace test.g9ea9.proof\n rule target(1)\n proof target\n   rule s1: target(1) @[Marker] by derivation\n end\nend\n",
    )
    .expect("parse");
    let Item::Namespace(ns) = &parsed.items[0] else { panic!("namespace") };
    let steps = ns
        .items
        .iter()
        .find_map(|item| match item {
            Item::Proof(p) => match &p.body {
                Some(ProofBody::Structured { steps, .. }) => Some(steps),
                _ => None,
            },
            _ => None,
        })
        .expect("structured proof");
    let meta = steps[0].rule.meta.as_ref().expect("the step's block");
    let key = meta.entries[0].key.segments.last().copied().unwrap();
    assert_eq!(parsed.symbols.local_name(key), "Marker");
}

#[test]
fn a_block_after_a_type_is_the_declarations() {
    // The four productions that end `type [block]`: each takes `@[…]` as its own block.
    // CONTROL rows: the bracket spelling after the same kind of type is the TYPE's
    // arguments and records no block — by design, not by accident of typing.
    let (kb, rows) = declaration_blocks(
        r#"
namespace test.g9ea9.decls
  import anthill.prelude.{Int64, List}
  sort Id = Int64 @[Serializable]
  sort Carrier
    entity carrier
    effects E = ? @[Serializable]
  end
  operation f() -> Int64 @[Serializable]
  const K: Int64 @[Serializable]

  sort Xs = List [Int64]
  operation g() -> List [Int64]
  const Ks: List [Int64]
end
"#,
        &[
            "test.g9ea9.decls.Id",
            "test.g9ea9.decls.Carrier.E",
            "test.g9ea9.decls.f",
            "test.g9ea9.decls.K",
            "test.g9ea9.decls.Xs",
            "test.g9ea9.decls.g",
            "test.g9ea9.decls.Ks",
        ],
    );
    for (i, row) in rows.iter().enumerate() {
        assert_eq!(row.len(), 1, "one row for declaration {i}");
        let tagged = meta_has_flag(&kb, Some(row[0]), "Serializable");
        if i < 4 {
            assert!(tagged, "declaration {i} records its `@[Serializable]`");
        } else {
            assert!(is_empty_meta(&kb, row[0]), "`[Int64]` in declaration {i} is no block");
        }
    }
    let g = kb.try_resolve_symbol("test.g9ea9.decls.g").unwrap();
    assert!(op_info::lookup_operation_info(&kb, g).unwrap().meta.is_none());
}

#[test]
fn a_bracket_that_over_applies_its_type_is_refused() {
    let errs = crate::common::try_load_kb_with(
        "namespace test.g9ea9.over\n import anthill.prelude.{Int64}\n sort Id = Int64 [Marker]\nend\n",
    )
    .err()
    .expect("over-applied Int64");
    crate::common::assert_refused_naming(&errs, &["over-applied"], "sort bracket");
}

#[test]
fn the_retired_spellings_are_refused_naming_the_block() {
    for (src, token) in [
        (
            "namespace t1\n import anthill.prelude.Int64\n entity a(n: Int64)\n rule r(?x) :- a(n: ?x) [simp]\nend\n",
            "write `@[simp]`",
        ),
        (
            "namespace t2\n rule {\n  q(?a) [simp]\n  r(?b)\n }\nend\n",
            "write `@[simp]`",
        ),
        (
            "namespace t3\n import anthill.prelude.Int64\n entity f(n: Int64)\n fact f(n: 1) [trust: axiom]\nend\n",
            "write `@[trust: axiom]`",
        ),
        (
            "namespace t4\n import anthill.prelude.Int64\n entity e(n: Int64) [Marker]\nend\n",
            "write `@[Marker]`",
        ),
        ("namespace t5\n sort S\n  entity s\n end [Marker]\nend\n", "write `@[Marker]`"),
        (
            "namespace t6\n import anthill.prelude.Int64\n entity e(n: Int64) @ [Marker]\nend\n",
            "the single token `@[`",
        ),
    ] {
        let errs = crate::common::parse_errs(src);
        crate::common::assert_refused_naming(&errs, &[token], src);
    }
}

#[test]
fn a_bracket_after_a_bodyless_consts_type_is_refused_as_a_retired_block() {
    // The fourth type-ending production: `[Marker, Key: 7]` cannot be type arguments
    // (`Key: 7` is no binding), so it is a syntax error — and the refusal says what the
    // author meant to write.
    let errs = crate::common::parse_errs(
        "namespace t8\n import anthill.prelude.{Int64}\n const K: Int64 [Marker, Key: 7]\nend\n",
    );
    crate::common::assert_refused_naming(&errs, &["syntax error", "write `@[Marker, Key: 7]`"], "const");
}

#[test]
fn an_arrow_effect_that_is_a_list_is_refused_once() {
    // `@ [simp]` after an arrow TERM parses clean — `@` is the arrow-effect infix — so no
    // syntax error would ever carry a hint. No effect is a list, so it is refused on every
    // parse, with ONE message (the retired-block hint defers to it). CONTROL: without the
    // refusal this source parses clean and the tag is silently an effect.
    let errs = crate::common::parse_errs("namespace t9\n rule r(?f) <=> ?a -> ?b @ [simp]\nend\n");
    assert_eq!(
        errs.iter().filter(|e| e.contains("`@[`")).count(),
        1,
        "one message naming `@[`: {errs:?}"
    );
    crate::common::assert_refused_naming(&errs, &["never a list"], "arrow effect list");
}

#[test]
fn retired_blocks_with_dotted_keys_and_string_punctuation_are_still_named() {
    for (src, token) in [
        (
            "namespace t10\n import anthill.prelude.Int64\n entity p(n: Int64)\n fact p(n: 1) [a.b: c]\nend\n",
            "write `@[a.b: c]`",
        ),
        (
            "namespace t11\n import anthill.prelude.Int64\n operation f() -> Int64\n  meta [CppBody: \"g());\"]\nend\n",
            "clause was removed",
        ),
    ] {
        let errs = crate::common::parse_errs(src);
        crate::common::assert_refused_naming(&errs, &[token], src);
    }
}

#[test]
fn brackets_that_are_not_blocks_draw_no_hint_beside_an_unrelated_error() {
    // Each source fails for an unrelated reason (`end [Marker]` makes the whole file one
    // ERROR, so every byte is "near" it); only that retired block may be named. A legal
    // type application, a bracket in description prose, and a list after a keyword are
    // not blocks.
    for (src, not_named) in [
        (
            "namespace t12\n import anthill.prelude.{Int64, List}\n sort Xs = List [Int64]\n sort S\n  entity s\n end [Marker]\nend\n",
            "`[Int64]`",
        ),
        (
            "namespace t13\n {< a sorted list [ascending] of keys >}\n sort S\n  entity s\n end [Marker]\nend\n",
            "`[ascending]`",
        ),
        (
            "namespace t14\n rule r(?x) :- member(?x) in [a, b] )\nend\n",
            "`[a, b]`",
        ),
    ] {
        let errs = crate::common::parse_errs(src);
        assert!(
            !errs.iter().any(|e| e.contains(not_named) && e.contains("retired spelling")),
            "{not_named} is not a block: {errs:?}"
        );
    }
}

#[test]
fn a_type_application_on_a_broken_line_draws_no_block_hint() {
    // The hint wants whitespace before the bracket: `Eq[T]` on a line that fails for an
    // unrelated reason is a type application, and naming it a retired block would send
    // the author after the wrong fix.
    let errs = crate::common::parse_errs(
        "namespace t7\n import anthill.prelude.{Int64, Eq}\n operation f(x: Eq[T]) -> \nend\n",
    );
    assert!(
        !errs.iter().any(|e| e.contains("retired spelling")),
        "no block hint for `Eq[T]`: {errs:?}"
    );
}

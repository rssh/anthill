//! WI-1070 — AN OPERATION'S (AND A `const`'S) OWN DESCRIPTION BLOCK REACHES THE KB.
//!
//! §4.1 makes a description block "free-form text, preserved as KB facts", and the
//! reflect layer is what a tool reads to document an API. Before this change the
//! grammar accepted `{< … >}` on an `operation` / `const`, `parse::ir::Operation` and
//! `parse::ir::Const` had nowhere to put it, and the text was gone before the loader —
//! no `DescriptionInfo`, no warning. WI-1000 measured it: the standalone `describe`
//! spelling scored 1 hit against a sentinel, the operation's own block 0.
//!
//! WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT:
//!   * `operation_own_description_emits_fact`            — 0 facts instead of 1
//!   * `operation_entry_own_description_emits_fact`      — PARSE ERROR (the block form's
//!     `description` field did not exist at all), so the load panics before counting.
//!     Its `twice` row is the exception: an ABSENCE assertion, which passes either way
//!     when backed out — it guards the between-entries block from binding BACKWARD, and
//!     only the `thrice` row beside it makes that guard non-vacuous
//!   * `operation_multiple_descriptions_emit_indexed_facts` — 0 facts instead of 2
//!   * `const_own_description_emits_fact`                — 0 facts instead of 1
//!   * `both_spellings_emit_one_fact_each`               — 1 fact instead of 2
//!
//! WHICH ROWS PASS EITHER WAY BY DESIGN — the CONTROL for the `describe` spelling,
//! which this change must leave exactly as it was:
//!   * `standalone_describe_emits_exactly_one_fact`
//!
//! `both_spellings_emit_one_fact_each` is the pair's real content: it is the row that
//! fails if the fix double-emits (2 spellings → 3 or 4 facts) as well as the row that
//! fails if the inline spelling stays inert (→ 1 fact). Backing the change out and
//! double-emitting move it in opposite directions, so one number decides both.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::{Literal, Term, TermId};

use crate::common::load_kb_with;

/// Named arg `field` of a `Term::Fn`, by LOCAL name.
fn named_arg(kb: &KnowledgeBase, term_id: TermId, field: &str) -> Option<TermId> {
    match kb.get_term(term_id) {
        Term::Fn { named_args, .. } => named_args
            .iter()
            .find(|(sym, _)| kb.local_name_of(*sym) == field)
            .map(|&(_, tid)| tid),
        _ => None,
    }
}

/// Every `DescriptionInfo` whose `target` is the nullary name term for
/// `target_qname`, as `(index, content)` pairs sorted by index.
///
/// Reading BACK through the fact's own `target` field is the point: the stdlib
/// contributes plenty of `DescriptionInfo` facts, so a global count would pass while
/// naming nothing, and asserting "the program loads" would pass with the text dropped.
pub(crate) fn descriptions_of(kb: &KnowledgeBase, target_qname: &str) -> Vec<(i64, String)> {
    let desc_sym = kb.resolve_symbol("anthill.reflect.DescriptionInfo");
    let mut out: Vec<(i64, String)> = Vec::new();
    for fid in kb.rules_by_functor(desc_sym) {
        let head = kb.fact_term(fid);
        let target = named_arg(kb, head, "target").expect("DescriptionInfo.target");
        let target_sym = match kb.get_term(target) {
            Term::Fn { functor, .. } => *functor,
            Term::Ref(s) | Term::Ident(s) => *s,
            other => panic!("unexpected DescriptionInfo.target carrier: {other:?}"),
        };
        if kb.qualified_name_of(target_sym) != target_qname {
            continue;
        }
        let content = match kb.get_term(named_arg(kb, head, "content").expect("content")) {
            Term::Const(Literal::String(s)) => s.clone(),
            other => panic!("expected String content, got {other:?}"),
        };
        let index = match kb.get_term(named_arg(kb, head, "index").expect("index")) {
            Term::Const(Literal::Int(n)) => *n,
            other => panic!("expected Int index, got {other:?}"),
        };
        out.push((index, content));
    }
    out.sort();
    out
}

// ── The gap WI-1000 measured ────────────────────────────────────

#[test]
fn operation_own_description_emits_fact() {
    const SRC: &str = r#"
namespace wi1070.own
  import anthill.prelude.Int64
  {< the operation's own block >}
  operation show(x: Int64) -> Int64 = x
end
"#;
    let kb = load_kb_with(SRC);
    assert_eq!(
        descriptions_of(&kb, "wi1070.own.show"),
        vec![(0, "the operation's own block".to_string())],
        "an operation's inline description block must reach the KB as a \
         DescriptionInfo naming that operation",
    );
}

/// The `operation { … }` entry (block) form — a SEPARATE grammar production that did
/// not carry a `description` field at all, so this source did not even parse before.
///
/// THREE POSITIONS in one block, because they are not the same risk. `show`'s block is
/// the SAFE one: the token before it is the block's own `{`. `thrice`'s is the RISKY
/// one — it sits directly after the preceding entry's brace-less `= x` body, and
/// `description_block` is a single `{<`-initial token, so an `_expr_body` that grew
/// greedier (or a change to the entry's trailing `optional($.meta_block)`) could
/// re-associate it onto `twice`. `twice`'s empty row is what would catch that, and it
/// is only meaningful beside `thrice`'s positive one: an assertion that a description
/// is ABSENT passes trivially when no description was written near it at all.
#[test]
fn operation_entry_own_description_emits_fact() {
    const SRC: &str = r#"
namespace wi1070.entry
  import anthill.prelude.Int64
  operation {
    {< the entry form's own block >}
    show(x: Int64) -> Int64 = x
    twice(x: Int64) -> Int64 = x
    {< written between two entries >}
    thrice(x: Int64) -> Int64 = x
  }
end
"#;
    let kb = load_kb_with(SRC);
    assert_eq!(
        descriptions_of(&kb, "wi1070.entry.show"),
        vec![(0, "the entry form's own block".to_string())],
        "an `operation {{ … }}` entry's inline description must reach the KB",
    );
    assert_eq!(
        descriptions_of(&kb, "wi1070.entry.thrice"),
        vec![(0, "written between two entries".to_string())],
        "a block written BETWEEN two entries belongs to the one it precedes — the \
         position where the preceding entry's brace-less body abuts the `{{<` token",
    );
    assert!(
        descriptions_of(&kb, "wi1070.entry.twice").is_empty(),
        "…and must not spill BACKWARD onto the entry whose body precedes it",
    );
}

/// Multiple blocks on one operation, and the per-target index they carry (WI-438).
#[test]
fn operation_multiple_descriptions_emit_indexed_facts() {
    const SRC: &str = r#"
namespace wi1070.multi
  import anthill.prelude.Int64
  {< first line >}
  {< second line >}
  operation show(x: Int64) -> Int64 = x
end
"#;
    let kb = load_kb_with(SRC);
    assert_eq!(
        descriptions_of(&kb, "wi1070.multi.show"),
        vec![(0, "first line".to_string()), (1, "second line".to_string())],
        "repeated blocks must all reach the KB, indexed per target in source order",
    );
}

/// The `const` peer of the same hole — `const_declaration` accepts the block in the
/// grammar, `parse::ir::Const` had nowhere to put it.
#[test]
fn const_own_description_emits_fact() {
    const SRC: &str = r#"
namespace wi1070.konst
  import anthill.prelude.Int64
  {< the const's own block >}
  const answer: Int64 = 42
end
"#;
    let kb = load_kb_with(SRC);
    assert_eq!(
        descriptions_of(&kb, "wi1070.konst.answer"),
        vec![(0, "the const's own block".to_string())],
        "a const's inline description block must reach the KB too",
    );
}

// ── Controls ────────────────────────────────────────────────────

/// PASSES EITHER WAY BY DESIGN. The standalone `describe` spelling is what WI-1000
/// measured at 1 hit and what 059 R3 admits in a secondary entry; this change must not
/// move it. It is the control for the SPELLING, not a measure of the fix.
#[test]
fn standalone_describe_emits_exactly_one_fact() {
    const SRC: &str = r#"
namespace wi1070.standalone
  import anthill.prelude.Int64
  operation show(x: Int64) -> Int64 = x
  describe show {< the standalone describe >}
end
"#;
    let kb = load_kb_with(SRC);
    assert_eq!(
        descriptions_of(&kb, "wi1070.standalone.show"),
        vec![(0, "the standalone describe".to_string())],
        "the standalone `describe` spelling must still emit exactly one fact",
    );
}

/// Both spellings on one operation: exactly one fact each, indices 0 and 1, targets
/// identical. A double-emit at either end shows up here as a third row.
#[test]
fn both_spellings_emit_one_fact_each() {
    const SRC: &str = r#"
namespace wi1070.both
  import anthill.prelude.Int64
  {< inline block >}
  operation show(x: Int64) -> Int64 = x
  describe show {< standalone describe >}
end
"#;
    let kb = load_kb_with(SRC);
    assert_eq!(
        descriptions_of(&kb, "wi1070.both.show"),
        vec![(0, "inline block".to_string()), (1, "standalone describe".to_string())],
        "the two spellings must contribute one fact each — neither dropped nor doubled",
    );
}

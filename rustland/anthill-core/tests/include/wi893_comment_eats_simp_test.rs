//! WI-893 — a comment line immediately above a `[simp]`-tagged `rule { }` entry
//! SILENTLY ATE the attribute. This suite exists because the tree-sitter corpus case is
//! not enough: nothing in the repo runs `npx tree-sitter test` under `cargo test`, and
//! the defect is invisible to a green suite. It produced a WRONG PROGRAM, not an error
//! — the tag re-parsed as a separate junk rule headed by the list `[simp]`, so the
//! equation went INERT (WI-881: `[simp]` is the ENABLEMENT, so a dropped tag is a
//! dropped definition) and a junk entry was asserted beside it.
//!
//! THE CAUSE is a GLR tie in the `[$.rule_entry]` conflict, broken by `prec.dynamic`;
//! `tree-sitter-anthill/grammar.js` (`rule_entry`) carries it, and the four parses are
//! pinned in `tree-sitter-anthill/test/corpus/rule_entry_meta.txt` — whose cases share
//! one body, so each differs from the control by exactly one comment line (that is why
//! two of them carry an entry they do not need). This file pins what a LOAD and an EVAL
//! see.
//!
//! THE DAMAGE IT ALREADY DID: driving WI-887, `bool.anthill`'s two `ite` case laws were
//! tagged with a `-- if-then-else` line immediately above the FIRST. `ite_true`'s tag
//! was eaten and `ite_false`'s survived, and the probe taken was exactly the branch
//! whose tag was gone — so "tagging buys nothing" was recorded, and it was an artifact.
//! Half-eaten looks backed. [`a_comment_above_a_tagged_law_leaves_it_firing`] drives
//! both orders of that asymmetry, because asserting one branch per operation would have
//! passed against the defect half the time.
//!
//! STDLIB LOADS: THREE. One interpreter for the firing test and two KBs for the
//! differential — the price of keeping two distinct claims in two named tests, which is
//! the discipline `wi884_sibling_backing_test` records. The two convert-time tests load
//! nothing: `common::parse_errs` / `parses_clean` reach that layer without the stdlib.
//!
//! Reference: WI-448 (the same tie in another production pair), WI-881 (`[simp]` is the
//! enablement), WI-887 (the ticket whose central measurement this invalidated), spec
//! §"A head is an atom".

use anthill_core::eval::Value;

/// Two independent law pairs, each with a comment in a position that used to eat a tag:
/// above the FIRST of the pair (`pick893`, the historical `bool.anthill` shape) and
/// above the SECOND (`flip893`, the other order). The block opens with an untagged
/// entry because the trigger needs a PRECEDING entry — a comment above a block's first
/// entry never tripped it.
///
/// Both operations are DECLARED body-less: their `[simp]` laws are their whole
/// definition, which is what makes an eaten tag observable as `OperationBodyMissing`
/// rather than as a silently missed rewrite.
const TAGGED_WITH_COMMENTS: &str = r#"
namespace wi893.commentEatsTag
  import anthill.prelude.{Int64, Bool}

  sort C
    import anthill.prelude.{Int64, Bool}

    operation pick893(cond: Bool, then: Int64, else: Int64) -> Int64
    operation flip893(cond: Bool, then: Int64, else: Int64) -> Int64

    rule {
      seed:      seed893(?x) = ?x
      -- comment above the FIRST tagged entry of the pair
      pickTrue:  pick893(true, ?t, ?_) = ?t [simp]
      pickFalse: pick893(false, ?_, ?e) = ?e [simp]
      flipTrue:  flip893(true, ?t, ?_) = ?t [simp]
      -- comment above the SECOND tagged entry of the pair
      flipFalse: flip893(false, ?_, ?e) = ?e [simp]
    }

    operation drivePickThen(n: Int64) -> Int64 = pick893(true, 10, 20)
    operation drivePickElse(n: Int64) -> Int64 = pick893(false, 10, 20)
    operation driveFlipThen(n: Int64) -> Int64 = flip893(true, 30, 40)
    operation driveFlipElse(n: Int64) -> Int64 = flip893(false, 30, 40)
  end
end
"#;

/// The control half of the differential: the same program with every comment line
/// removed. DERIVED rather than copied, because the comparison below is only meaningful
/// while the two differ by exactly the comments — a hand-kept twin would state that
/// invariant in prose and let an edit to one side break it silently.
fn without_comments(src: &str) -> String {
    src.lines()
        .filter(|l| !l.trim_start().starts_with("--"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// THE ACCEPTANCE, and the one a green suite could not have given: a tagged law whose
/// entry is preceded by a comment is indexed as a `[simp]` equation and FIRES.
///
/// All four branches are driven on ONE interpreter. Pre-fix, exactly two of them died
/// `OperationBodyMissing` — `pick893`'s THEN branch and `flip893`'s ELSE branch, the
/// entries the two comments sat above — while their siblings answered.
#[test]
fn a_comment_above_a_tagged_law_leaves_it_firing() {
    let mut interp = crate::common::interp_for(TAGGED_WITH_COMMENTS);
    for (op, expected) in [
        ("drivePickThen", 10),
        ("drivePickElse", 20),
        ("driveFlipThen", 30),
        ("driveFlipElse", 40),
    ] {
        let path = format!("wi893.commentEatsTag.C.{op}");
        match interp.call(&path, &[Value::Int(0)]) {
            Ok(Value::Int(n)) if n == expected => {}
            other => panic!(
                "{path} must reduce to {expected} — its `[simp]` law is its whole \
                 definition, so anything else means the tag was eaten; got {other:?}"
            ),
        }
    }
}

/// THE JUNK ENTRY IS GONE. The dropped attribute did not merely vanish — it was
/// asserted as a rule of its own, headed by the list `[simp]`, so the commented program
/// carried one MORE entry than the identical uncommented one. Counting catches that
/// without depending on how the junk entry happens to be shaped.
///
/// The junk entry has an empty body, so `fact_count` is where it landed; `rule_count`
/// is the control saying the comment moved nothing else either.
#[test]
fn a_comment_changes_nothing_the_kb_can_see() {
    let with = crate::common::load_kb_with(TAGGED_WITH_COMMENTS);
    let without = crate::common::load_kb_with(&without_comments(TAGGED_WITH_COMMENTS));
    assert_eq!(
        with.fact_count(),
        without.fact_count(),
        "a comment above a tagged entry must assert no extra entry \
         (pre-fix the tag became a junk rule headed by the list `[simp]`)",
    );
    assert_eq!(
        with.rule_count(),
        without.rule_count(),
        "a comment above a tagged entry must change no bodied rule either",
    );
}

/// A CONCLUSION IS NEVER A BARE LITERAL — the ticket asked for this to be answered
/// explicitly, and the answer is what makes the grammar's `prec.dynamic` bias exact
/// rather than arbitrary: the reading the bias discards is one the language refuses.
///
/// `rule { [simp] }` — the shape a dropped attribute re-parsed as — LOADED CLEAN before
/// this change (measured), which is what kept the defect silent end to end. Both
/// producers of a conclusion are driven, because a fact IS a rule with an empty body
/// and `fact 42` reached `assert_fact` unguarded: `fact` is the surface a user is
/// likelier to hand-write. Both a `collection_literal` and a scalar appear, because the
/// check is deliberately the whole literal family. One source carries all four, since
/// `Converter::err` accumulates; no stdlib load is involved.
#[test]
fn a_bare_literal_conclusion_is_refused() {
    const SRC: &str = r#"
namespace wi893.literalHead
  sort P
    rule { [simp] }
    rule { 42 }
    fact [simp]
    fact "s"
  end
end
"#;
    let errs = crate::common::parse_errs(SRC);
    let heads = errs
        .iter()
        .filter(|e| e.contains("rule head must be an atom"))
        .count();
    let facts = errs
        .iter()
        .filter(|e| e.contains("fact must be an atom"))
        .count();
    assert_eq!(
        heads, 2,
        "both literal rule heads must be refused; got {errs:?}"
    );
    assert_eq!(facts, 2, "both literal facts must be refused; got {errs:?}");
}

/// THE CONTROL for [`a_bare_literal_conclusion_is_refused`]: the conclusion shapes that
/// ARE atoms still parse. Without this, a refusal that swallowed ordinary heads would
/// look like a pass — and the check sits in the path every rule in the stdlib takes.
///
/// A literal in ARGUMENT position (`p(42)`) and on the right of an equational head
/// (`f(?x) = 42`) are where a literal legitimately appears in a conclusion, and both are
/// covered: the check reads the conclusion's OWN kind, not the kinds within it.
#[test]
fn atom_conclusions_still_parse() {
    crate::common::parses_clean(
        r#"
namespace wi893.atomHeads
  sort P
    rule { plain: p893(?x) :- q893(?x) }
    rule { withLiteralArg: r893(42) }
    rule { equational: f893(?x) = 42 [simp] }
    rule { denial: ⊥ :- s893(?x) }
    fact t893(42)
  end
end
"#,
    );
}

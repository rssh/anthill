//! WI-20260904-B8ESG — A CONSTRUCTOR IN A RULE- OR FACT-HEAD ARGUMENT NAMED NOTHING,
//! SILENTLY, and a head pattern built on it simply stopped matching.
//!
//! WI-1034 refuses a rule-body GOAL whose functor names nothing and WI-1058 a rule-body
//! DATA slot. A head ARGUMENT had neither check — the third position in the same family,
//! and the one where the failure is quietest, because a head is not proved and not
//! rewritten. What it does is MATCH, and a term whose functor denotes nothing matches
//! only another undenoting term of the same spelling.
//!
//! DRIVEN, and this is the ticket's own measurement retaken:
//!
//! ```text
//!   fact stored(cons(head: 1, tail: nil))     -- only the List SORT imported
//!   rule drive(1) :- stored([1])
//!
//!   without the `cons` import:  loaded: 2883 facts, 308 rules   drive -> no solutions
//!   with it:                    loaded: 2883 facts, 308 rules   drive -> 1 solution(s)
//! ```
//!
//! Identical counts. Importing a SORT does not bring its members into scope
//! (kernel-language.md §8.6), so the fact's `cons` interned bare while the body's list
//! literal lowered to the declared one. The stdlib shipped exactly this shape through
//! WI-909 (`reflect/typing.anthill`'s `list_contains`), and the ticket records that the
//! loud channel covered 2 of 8 affected files in that migration — every other site had to
//! be found by reading, and three successive audits each looked complete and were not.
//!
//! ## THE EXEMPTION CENSUS, WHICH THE TICKET CALLS THE WORK
//!
//! Measured by running the check over the corpus and reading every report. A first cut
//! walked the stored head TERM and reported **434** sites on
//! `examples/classic-mini/ancestor` alone. Three gates take it to zero, and each is a
//! position rather than a spelling:
//!
//! | gate | what it removes | measured |
//! |---|---|---|
//! | `term_depth > 1` | the head's OWN functor — a head INTRODUCES its name (WI-896) | every rule and fact |
//! | `!is_minted` | desugar markers: `pattern_constructor`, `match_branch`, `pattern_var`, `lambda_expr`, … | **404 of 434** (141 / 132 / 131) |
//! | `!in_quoted_term` | the interior of a reflect `Term`-typed field, which holds a QUOTED PATTERN (§4.2) | the 4 `Quoted("sql", …)` in `examples/sql-store` |
//!
//! The marker gate is PROVENANCE and not spelling (WI-1009's rule), which matters because
//! in TERM form a `match`/`lambda` and its patterns are marker-encoded and nothing about
//! the term distinguishes them from a user's own call. It is also why the check records
//! its sites in the LOADER and takes the verdict after every file has loaded: only the
//! loader knows the position and the provenance, and only the post-load KB knows whether
//! a name declares anything (a predicate defined purely by FACTS keeps an `Unresolved`
//! functor until its clauses land).
//!
//! Walking the term had a second defect the parse-node span fixes: all 434 of its reports
//! rendered at `0..0`, because the term-span table is keyed on the hash-consed `TermId`
//! and two identical subterms written in two files share one entry.
//!
//! ## WHAT THE CENSUS FOUND IN THE CORPUS
//!
//! Two names survived the gates, and they split the way the ticket predicted:
//!
//!   * **`Quoted` ×4, `examples/sql-store`** — a §4.2 kernel TERM FORM with no declaration
//!     anywhere in the implementation. NOT a defect and not an exemption for `Quoted`
//!     either: every one is written into a field declared `anthill.reflect.Term`, and that
//!     position says "do not resolve this". The quoted-field gate covers it. Worth knowing
//!     that WI-1058's rule-body check ALREADY refuses a `Quoted(…)` written in a body data
//!     slot — so the language's existing position is that the name denotes nothing, and
//!     this check agrees with it rather than inventing a rule.
//!   * **`untrusted` ×10, `examples/guardians/fixtures/mailbox.anthill`** — a REAL instance,
//!     fixed at its source in this commit. `untrusted` is a member of `enum guardians.Text`
//!     and the fixture imported only the sort. Latent, because `lib/classify.anthill`
//!     matches `subject` and `body` with wildcards — which is precisely the ticket's point:
//!     "a name-resolution change cannot be verified by 'the corpus loads clean' while this
//!     position is unchecked".
//!
//! ## WHICH ROWS MOVE
//!
//! `a_head_argument_that_names_nothing_is_refused` fails with the check backed out — it is
//! the only row that measures it. `the_same_fact_matches_once_the_name_is_imported` is the
//! CONTROL that says the refusal is about the NAME and not about the shape, and
//! `head_functors_and_desugar_markers_are_not_judged` is the exemption census as an
//! assertion; both pass either way, by design, in fixtures of their own.

use anthill_core::kb::KnowledgeBase;

/// THE DEFECT. Only the `List` SORT is imported, so `cons` and `nil` name nothing here.
const SRC_UNIMPORTED: &str = r#"
namespace test.b8esg.unimported
  import anthill.prelude.{Int64, List}
  fact stored(cons(head: 1, tail: nil))
  rule drive(1) :- stored([1])
end
"#;

/// THE CONTROL — the same program with the one import that makes the name denote.
const SRC_IMPORTED: &str = r#"
namespace test.b8esg.imported
  import anthill.prelude.{Int64, List}
  import anthill.prelude.List.{cons, nil}
  fact stored(cons(head: 1, tail: nil))
  rule drive(1) :- stored([1])
end
"#;

/// THE EXEMPTIONS, as a program: a head functor nothing has declared yet (it is being
/// introduced here), and a desugar marker in an argument.
const SRC_EXEMPT: &str = r#"
namespace test.b8esg.exempt
  import anthill.prelude.{Int64}
  fact brandNewPredicate(lambda v -> v + 1)
  rule alsoBrandNew(?x) :- brandNewPredicate(?x)
end
"#;

/// Definite answers of `<qn>(?r)`.
fn answers(kb: &mut KnowledgeBase, qn: &str) -> usize {
    crate::common::definite_unary(kb, qn).len()
}

/// THE ROW THAT MEASURES THE CHECK: a head argument whose functor names nothing is
/// refused at load, naming the functor, in the family's own census-and-repair vocabulary,
/// at a real `line:col`.
///
/// Backed out, this fixture LOADS — with a fact count identical to the control's — and the
/// defect is then only visible as `drive` answering nothing.
#[test]
fn a_head_argument_that_names_nothing_is_refused() {
    let errs = crate::common::try_load_kb_with(SRC_UNIMPORTED)
        .err()
        .unwrap_or_default();
    crate::common::assert_refused_naming(
        &errs,
        &[
            // The offending name, and that it is the HEAD-ARGUMENT position rather than
            // one of its two siblings. BARE, not `anthill.prelude.List.cons`: the whole
            // defect is that the name resolved to nothing, so the symbol it interned as
            // has no qualification to render — which is itself worth pinning, since a
            // message that printed a qualified name here would be naming a declaration
            // the author does not have.
            "head argument term `cons`",
            // WI-1034/WI-1058's shared census…
            "no rule, fact, operation, entity, const or builtin is declared under that name",
            // …and their shared repair, which for this defect is the whole story: one
            // import. §8.6 — importing a SORT does not bring its members into scope.
            "import the namespace that declares",
        ],
        "a fact-head argument built on an unimported constructor",
    );
    // `line:col`, which the ticket's acceptance asks for by name. `4:15` is the `cons`
    // in `  fact stored(cons(head: 1, tail: nil))` — the line the author edits and the
    // column of the name they must import, not the enclosing fact's start and not the
    // `0..0` a walk over the hash-consed head term produced for all 434 of its reports.
    assert!(
        errs.iter().any(|e| e.contains("4:15")),
        "the refusal must point at the `cons` itself. Got:\n{errs:#?}"
    );
}

/// THE CONTROL, and what makes the row above a statement about the NAME.
///
/// Same fact, same body goal, one extra import — it loads and ANSWERS. Without this, the
/// refusal above is satisfied by any change that broke `cons(head:, tail:)` generally.
///
/// Passes either way, by design.
#[test]
fn the_same_fact_matches_once_the_name_is_imported() {
    let mut kb = crate::common::load_kb_with(SRC_IMPORTED);
    assert_eq!(
        answers(&mut kb, "test.b8esg.imported.drive"),
        1,
        "`stored([1])` finds `stored(cons(head: 1, tail: nil))` — the list literal and the \
         fact head now spell ONE `cons`. This is the answer the unimported twin loses, \
         silently, with an identical fact count"
    );
}

/// THE EXEMPTION CENSUS, AS AN ASSERTION — the three gates, driven rather than described.
///
///   * `brandNewPredicate` and `alsoBrandNew` are head FUNCTORS that nothing declares:
///     a head INTRODUCES its name (WI-896), which is what `term_depth > 1` protects.
///   * the `lambda` argument lowers to marker-encoded `lambda_expr(pattern_var(v), …)`,
///     and the KB declares nothing under any of those — 404 of the first cut's 434 reports.
///
/// Passes either way, by design: nothing here was ever refused. It is the row that would
/// catch a gate being dropped, which is the failure mode that turns this check from a
/// diagnostic into a wall — measured at 434 refusals on one example.
#[test]
fn head_functors_and_desugar_markers_are_not_judged() {
    let mut kb = crate::common::load_kb_with(SRC_EXEMPT);
    assert_eq!(
        answers(&mut kb, "test.b8esg.exempt.alsoBrandNew"),
        1,
        "the fixture loads and the introduced predicate answers, so neither the head \
         functors nor the lambda's desugar markers were judged"
    );
}

// ── Rows from `/code-review` of the first cut ─────────────────────────────────────────

/// A CONNECTIVE HEAD'S SUBJECT IS EXEMPT, ITS ARGUMENTS ARE NOT: they MATCH. The first
/// cut exempted everything below `<=>`, so this equation — whose rewrite can never fire,
/// because its LHS pattern names nothing — loaded clean. That is the ticket's silent
/// defect in the place constructor patterns are most often written.
///
/// FAILS WHEN BACKED OUT (exempting the whole connective subtree): the fixture loads.
#[test]
fn a_connective_subjects_arguments_are_judged() {
    let errs = crate::common::try_load_kb_with(
        r#"
namespace test.b8esg.equation
  import anthill.prelude.{Int64, List}
  operation len(xs: List[T = Int64]) -> Int64
  rule len(cons(head: ?h, tail: ?t)) <=> 1 [simp]
end
"#,
    )
    .err()
    .unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("head argument term `cons` names nothing")),
        "the LHS pattern's `cons` is judged. Got:\n{errs:#?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("head argument term `len`")),
        "the SUBJECT introduces the name the equation defines and is not judged. \
         Got:\n{errs:#?}"
    );
}

/// THE SIGIL-FREE PARAMETER HEAD judges its arguments too. `convert_rule_head_with_params`
/// converts them without passing the head through `convert_term`, so the first cut's
/// absolute `term_depth > 1` gate skipped them — the head node's own gate is by parse id
/// now. FAILS WHEN BACKED OUT (the depth gate): the fixture loads.
#[test]
fn a_parameter_form_heads_arguments_are_judged() {
    let errs = crate::common::try_load_kb_with(
        r#"
namespace test.b8esg.params
  import anthill.prelude.{Int64, List}
  rule tagged(cons(head: ?x, tail: ?), p: Int64) :- true
end
"#,
    )
    .err()
    .unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("head argument term `cons` names nothing")),
        "a positional argument of a parameter-form head is a head argument. Got:\n{errs:#?}"
    );
}

/// NOT JUDGED, each for a stated reason, and each a false refusal the first cut made or
/// could have made. Passes with the respective gate in place; FAILS with it backed out:
///
///   * `twice` — a call through a LAMBDA-BOUND name remaps to the binder's unique symbol,
///     which declares nothing by construction and denotes the binding all the same.
///   * `listed` / `optional` — a `Quoted` term written into a container of `Term`
///     (`List[T = Term]`, `Option[T = Term]`) is as quoted as one written into a bare
///     `Term` field: the list literal's elements and the `some` payload convert under the
///     element type.
#[test]
fn a_local_binder_and_a_quoted_container_are_not_judged() {
    let errs = crate::common::try_load_kb_with(
        r#"
namespace test.b8esg.notjudged
  import anthill.prelude.{Int64, List, Option}
  import anthill.prelude.Option.{some}
  import anthill.reflect.{Term}
  fact twice(lambda f -> lambda x -> f(f(x)))
  entity Listed(patterns: List[T = Term])
  entity Optional(pattern: Option[T = Term])
  fact listed(Listed(patterns: [Quoted("sql", "SELECT 1")]))
  fact optional(Optional(pattern: some(Quoted("sql", "SELECT 1"))))
end
"#,
    )
    .err()
    .unwrap_or_default();
    assert!(
        !errs.iter().any(|e| e.contains("head argument term")),
        "none of these is a head argument that names nothing. Got:\n{errs:#?}"
    );
}

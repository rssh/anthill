//! WI-20261115-JY1XE — a negated quantifier is DECIDED: the NAF groundness gate reads a
//! quantifier's binder as bound inside its quantifier (`SearchStream::negand_is_ground`),
//! and the loader refuses a binder written in the clause outside its own quantifier
//! (`Converter::note_variable_occurrence`), which is what makes that reading sound.
//!
//! Before, `!(forall ?p in [1, 2]: ?p > 5)` delayed as floundering: the negand holds its
//! binder `?p`, unbound, and the gate delayed on any unbound variable, although no caller
//! can bind a binder: the quantifier binds it to each element in turn, and a
//! hereditary-Harrop discharge skolemises its binders. The same quantifier behind a
//! predicate was decided, since there the negand is the ground call.
//!
//! BACK-OUT, measured on the selected binary (19 rows):
//! - the gate as before (`negand_is_ground` answering `value_is_ground` alone): the 7 rows
//!   of `decided` fail, each answer conditional;
//! - the refusal backed out (`note_variable_occurrence` and the checks of
//!   `open_quantifier_binders` doing nothing): the 7 rows of `refused` that assert a
//!   refusal fail;
//! - the 3 rows of `controls` and the two rows of `refused` that must NOT refuse pass
//!   either way, BY DESIGN: what still delays, the predicate spelling that was decided all
//!   along, and what the refusal must not refuse — but
//!   `a_later_proof_step_may_reuse_the_name` fails with the reset at a proof step backed
//!   out.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

use crate::common::{load_errors_of, load_kb_with, parse_errs, parses_clean, query_pattern_term};

const FIXTURE: &str = r#"
namespace test.jy1xe
  import anthill.prelude.{Int64, List}

  rule forall_none_big :- !(forall ?p in [1, 2]: ?p > 5)
  rule some_none_big   :- !(some ?p in [1, 2]: ?p > 5)
  rule forall_all_big  :- !(forall ?p in [6, 7]: ?p > 5)
  rule not_all_big(?xs) :- !(forall ?p in ?xs: ?p > 5)

  rule all_big(?xs) :- (forall ?p in ?xs: ?p > 5)
  rule not_all_big_by_predicate :- !all_big([1, 2])

  rule not_all_above(?y) :- !(forall ?p in [1, 2]: ?p > ?y)
  rule not_all_above_unbound :- !(forall ?p in [1, 2]: ?p > ?y)
  rule not_all_big_unbound :- !(forall ?p in ?xs: ?p > 5)

  entity Product(price: Int64)
  entity Shop(products: List[T = Product])
  rule unpriced(Shop(products: ?ps)) :- !(forall ?p in ?ps: ?p.price > 0)

  rule not_all_rows_positive(?xss) :- !(forall ?xs in ?xss: (forall ?x in ?xs: ?x > 0))

  rule not_and(?y) :- !(?y > 0, (forall ?p in [1, 2]: ?p > 5))
  rule not_or(?y)  :- !(?y > 0 | (forall ?p in [1, 2]: ?p > 5))
  rule not_and_not(?y) :- !(?y > 0 & !(forall ?p in [1, 2]: ?p > 5))

  sort N
    entity z
    entity s(n: N)
  end
  fact nat(z)
  rule nat(s(?n)) :- nat(?n)
  fact even(z)
  rule not_succ_closed :- !(forall(?x), nat(?x) -: nat(s(?x)))
  rule not_all_even    :- !(forall(?x), nat(?x) -: even(?x))
  rule not_one_binder_twice :- !(forall(?x, ?x), nat(?x) -: even(?x))

  rule siblings :- !((forall ?x in [1, 2]: ?x > 5), (some ?x in [3]: ?x > 5))
end
"#;

/// The answers `pattern` gets over `kb`: (definite, conditional).
fn answers(kb: &mut KnowledgeBase, pattern: &str) -> (usize, usize) {
    let goal = query_pattern_term(kb, pattern);
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    let definite = sols.iter().filter(|s| s.residual.is_empty()).count();
    (definite, sols.len() - definite)
}

fn assert_answers(kb: &mut KnowledgeBase, pattern: &str, want: (usize, usize), why: &str) {
    assert_eq!(
        answers(kb, pattern),
        want,
        "`{pattern}`: (definite, conditional) — {why}"
    );
}

mod decided {
    use super::*;

    /// The ticket's rows 1-4: the quantifier decides, and now the negation does.
    #[test]
    fn the_measured_rows_answer() {
        let mut kb = load_kb_with(FIXTURE);
        assert_answers(&mut kb, "test.jy1xe.forall_none_big", (1, 0), "row 1: no element is > 5");
        assert_answers(&mut kb, "test.jy1xe.some_none_big", (1, 0), "row 2: no element is > 5");
        assert_answers(&mut kb, "test.jy1xe.forall_all_big", (0, 0), "row 3: both are > 5");
        assert_answers(&mut kb, "test.jy1xe.not_all_big([1, 2])", (1, 0), "row 4");
        assert_answers(&mut kb, "test.jy1xe.not_all_big([6, 7])", (0, 0), "row 4, refuted");
    }

    /// The ticket's own case: an invariant written in place, through a field projection.
    #[test]
    fn a_projected_field_in_the_body() {
        let mut kb = load_kb_with(FIXTURE);
        assert_answers(
            &mut kb,
            "test.jy1xe.unpriced(test.jy1xe.Shop(products: [test.jy1xe.Product(price: 1), test.jy1xe.Product(price: 0)]))",
            (1, 0),
            "one price is not positive",
        );
        assert_answers(
            &mut kb,
            "test.jy1xe.unpriced(test.jy1xe.Shop(products: [test.jy1xe.Product(price: 1), test.jy1xe.Product(price: 2)]))",
            (0, 0),
            "every price is positive",
        );
    }

    /// An inner quantifier's collection is the outer binder: bound inside the outer body.
    #[test]
    fn a_nested_quantifier_over_the_outer_binder() {
        let mut kb = load_kb_with(FIXTURE);
        assert_answers(&mut kb, "test.jy1xe.not_all_rows_positive([[1], [0, 3]])", (1, 0), "a 0");
        assert_answers(&mut kb, "test.jy1xe.not_all_rows_positive([[1], [2, 3]])", (0, 0), "none");
    }

    /// The gate reaches a quantifier under `,` / `&`, `|` and a nested `!`.
    #[test]
    fn a_quantifier_under_a_connective() {
        let mut kb = load_kb_with(FIXTURE);
        // !(T ∧ F), !(F ∧ F)
        assert_answers(&mut kb, "test.jy1xe.not_and(3)", (1, 0), "!(true, false)");
        assert_answers(&mut kb, "test.jy1xe.not_and(-3)", (1, 0), "!(false, false)");
        // !(T ∨ F), !(F ∨ F)
        assert_answers(&mut kb, "test.jy1xe.not_or(3)", (0, 0), "!(true | false)");
        assert_answers(&mut kb, "test.jy1xe.not_or(-3)", (1, 0), "!(false | false)");
        // !(T ∧ ¬F), !(F ∧ ¬F)
        assert_answers(&mut kb, "test.jy1xe.not_and_not(3)", (0, 0), "!(true & !false)");
        assert_answers(&mut kb, "test.jy1xe.not_and_not(-3)", (1, 0), "!(false & !false)");
    }

    /// The hereditary-Harrop discharge's skolemised binders read the same way (decided
    /// with the user 2026-11-21): the negation decides by whether the discharge is provable.
    #[test]
    fn a_discharge_s_binders_are_bound() {
        let mut kb = load_kb_with(FIXTURE);
        assert_answers(&mut kb, "test.jy1xe.not_succ_closed", (0, 0), "nat(c) proves nat(s(c))");
        assert_answers(&mut kb, "test.jy1xe.not_all_even", (1, 0), "nat(c) does not prove even(c)");
        assert_answers(
            &mut kb,
            "test.jy1xe.not_one_binder_twice",
            (1, 0),
            "`forall(?x, ?x)` binds one variable",
        );
    }

    /// The rule `controls::a_free_body_variable_still_delays` asks with `?y` unbound,
    /// asked with it bound: it decides, so the delay there is the variable's.
    #[test]
    fn a_bound_body_variable_decides() {
        let mut kb = load_kb_with(FIXTURE);
        assert_answers(&mut kb, "test.jy1xe.not_all_above(0)", (0, 0), "1 > 0, 2 > 0");
        assert_answers(&mut kb, "test.jy1xe.not_all_above(1)", (1, 0), "1 > 1 fails");
    }

    /// Two sibling quantifiers may share a binder name: each binds it over its own body.
    #[test]
    fn sibling_quantifiers_share_a_binder_name() {
        let mut kb = load_kb_with(FIXTURE);
        assert_answers(&mut kb, "test.jy1xe.siblings", (1, 0), "!(false, false)");
    }
}

mod controls {
    use super::*;

    /// Row 5: behind a predicate the negand is the ground call, decided before the change.
    #[test]
    fn the_predicate_spelling_is_unchanged() {
        let mut kb = load_kb_with(FIXTURE);
        assert_answers(&mut kb, "test.jy1xe.not_all_big_by_predicate", (1, 0), "row 5");
    }

    /// A free variable of the body other than the binder still delays: a caller may bind it.
    #[test]
    fn a_free_body_variable_still_delays() {
        let mut kb = load_kb_with(FIXTURE);
        assert_answers(&mut kb, "test.jy1xe.not_all_above(?y)", (0, 1), "?y unbound");
        assert_answers(&mut kb, "test.jy1xe.not_all_above_unbound", (0, 1), "?y never bound");
    }

    /// A collection that is not yet ground still delays: the binder does not scope it.
    #[test]
    fn an_open_collection_still_delays() {
        let mut kb = load_kb_with(FIXTURE);
        assert_answers(&mut kb, "test.jy1xe.not_all_big(?xs)", (0, 1), "?xs unbound");
        assert_answers(&mut kb, "test.jy1xe.not_all_big_unbound", (0, 1), "?xs never bound");
    }
}

mod refused {
    use super::*;

    /// `clause` as line 4 of a file, so a refusal's positions read `4:col`.
    fn source_of(clause: &str) -> String {
        format!(
            "namespace test.jy1xe_refused\n  import anthill.prelude.{{Int64, List}}\n  fact nat(1)\n  {clause}\nend\n"
        )
    }

    /// What converting `clause` refuses: the refusal is the converter's, where the
    /// clause's variables are scoped. Panics if it converts clean.
    fn refusals(clause: &str) -> Vec<String> {
        parse_errs(&source_of(clause))
    }

    fn assert_refused(clause: &str, needle: &str) {
        let errs = refusals(clause);
        assert!(
            errs.len() == 1 && errs[0].contains(needle),
            "`{clause}` must be refused once, saying `{needle}`; got {errs:#?}"
        );
    }

    #[test]
    fn a_binder_the_head_writes() {
        assert_refused(
            "rule n(?p) :- !(forall ?p in [1, 2]: ?p > 5)",
            "the binder `?p` is already a variable of this clause (written at 4:10)",
        );
    }

    #[test]
    fn a_binder_an_earlier_goal_writes() {
        assert_refused(
            "rule e(?q) :- ?q <=> ?p, (some ?p in [1]: ?p > 0)",
            "the binder `?p` is already a variable of this clause",
        );
    }

    #[test]
    fn a_binder_a_later_goal_writes() {
        assert_refused(
            "rule l(?q) :- !(forall ?p in [1, 2]: ?p > 5), ?q <=> ?p",
            "`?p` is the binder of the quantifier at 4:18 and is written here, outside it",
        );
    }

    #[test]
    fn a_binder_in_its_own_collection() {
        assert_refused(
            "rule c :- (forall ?p in ?p: ?p > 0)",
            "`?p` is written in the collection of the quantifier that binds it",
        );
    }

    #[test]
    fn a_binder_an_enclosing_quantifier_binds() {
        assert_refused(
            "rule r(?xss) :- (forall ?x in ?xss: (forall ?x in ?x: ?x > 0))",
            "`?x` is already the binder of the enclosing quantifier at 4:19",
        );
    }

    #[test]
    fn a_discharge_binder_the_clause_writes() {
        assert_refused(
            "rule h(?x) :- (forall(?x), nat(?x) -: nat(?x))",
            "the binder `?x` is already a variable of this clause",
        );
        assert_refused(
            "rule h(?y) :- (forall(?x), nat(?x) -: nat(?x)), ?y <=> ?x",
            "`?x` is the binder of the quantifier at 4:17 and is written here, outside it",
        );
    }

    /// What the refusal is for. With the reuse loaded, the gate's reading would decide
    /// `n(?z)` for every `?z` while `n(6)` is refuted: one rule, two answers by the order
    /// the caller binds. MEASURED with the refusal backed out: `n(?z)` answered 1 definite.
    #[test]
    fn a_reused_binder_cannot_answer_two_ways() {
        assert!(
            !refusals("rule n(?p) :- !(forall ?p in [1, 2]: ?p > 5)").is_empty(),
            "a reused binder must not load"
        );
    }

    /// Not refused: a name a structured proof's earlier step bound in a quantifier, written
    /// plainly in a later step. The steps share their variables with each other and with
    /// the parent rule, by design (`convert_proof_step`), but each is a clause of its own,
    /// so each has its own quantifier scope. Back-out: without the reset at the step, this
    /// row is refused ("`?x` is the binder of the quantifier at …").
    #[test]
    fn a_later_proof_step_may_reuse_the_name() {
        parses_clean(
            "namespace test.jy1xe_proof\n  import anthill.prelude.{Int64, List}\n  \
             rule lemma: ok :- (forall ?x in [1]: ?x > 0)\n  \
             proof lemma\n    \
             rule s1: one :- (forall ?x in [1]: ?x > 0) by z3\n    \
             rule s2: two(?x) :- ?x > 0 by z3\n  \
             end\nend\n",
        );
    }

    /// Not refused: a name reused by the NEXT item. A `fact` keeps the variable scope of
    /// what came before it, and the binder state must not.
    #[test]
    fn the_next_item_may_reuse_the_name() {
        let errs = load_errors_of(&source_of(
            "rule q :- (forall ?x in [1]: ?x > 0)\n  fact uses(?x)\n  rule again(?x) :- nat(?x)",
        ));
        assert!(errs.is_empty(), "nothing to refuse: {errs:#?}");
    }
}

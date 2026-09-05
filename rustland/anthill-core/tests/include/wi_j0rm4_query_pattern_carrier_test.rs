//! **WI-20260904-J0RM4 — A QUERY PATTERN IS TRANSIENT, SO IT DOES NOT ENTER THE
//! HASH-CONSED STORE.**
//!
//! `convert_query_term` used to build the pattern with `kb.alloc`, minting
//! `kb.fresh_var` + `kb.alloc(Term::Var(..))` for every field the query did not write
//! (§8.3's all-fields-fresh completion). A fresh `VarId` makes each var term NEW, so
//! hash-consing could not dedup it — nor the `Fn` node above it, whose identity depends
//! on it — and the store grew by a fixed amount per query, forever: the `TermStore` is
//! monotone under a scoped-KB layer by design (WI-SPGBP suspends freeing for the layer's
//! whole lifetime, because a re-entering id would resurrect a retracted fact's slot), so
//! a release afterwards is not available where it would matter most. The CLI exits after
//! one query, which is why nothing showed.
//!
//! # What each row measures, and what fails when the change is backed out
//!
//!  * [`repeated_conversion_of_one_pattern_does_not_grow_the_term_store`] — THE
//!    HEADLINE. FAILS on the baseline: MEASURED +3 slots per conversion of
//!    `Top(a: 1)` (two omitted fields' fresh vars, plus the enclosing `Fn`).
//!  * [`a_repeated_fact_matching_query_run_is_flat`] — the same over the FULL
//!    `anthill query` shape, conversion AND resolution, for the query kind whose
//!    resolution opens no clause. FAILS on the baseline (+3 per query).
//!  * [`resolution_of_a_rule_goal_still_grows_the_store_by_one`] — the SEPARATE SITE
//!    this ticket does not close, measured rather than left to be discovered. See the
//!    section below.
//!  * [`distinct_patterns_of_one_functor_do_not_share_fill_variables`] — the SOUNDNESS
//!    control on the cheaper repair this rejects. A fill var reused per (functor, field)
//!    would make the store constant too, and would silently force two independent
//!    positions to be equal. PASSES EITHER WAY by design: it fails only for a
//!    hypothetical var-pooling implementation, and says so rather than being deleted.
//!  * [`a_query_pattern_label_prints_both_list_surfaces_as_brackets`] — the PRINTER
//!    PARITY row. `anthill query --query-file`'s label moved printers with the carrier,
//!    and `/code-review` reproduced a real regression there; see the row.
//!  * The four AGREEMENT rows — [`a_completed_pattern_matches_the_facts_it_used_to`],
//!    [`the_all_fields_fresh_expansion_still_answers`],
//!    [`a_list_literal_pattern_still_matches_its_stored_twin`],
//!    [`an_unresolvable_name_still_heads_no_clause`] — PASS EITHER WAY by design. They
//!    are the ticket's "matching results are identical before and after": the carrier
//!    may not change a single answer, so a row that went red on the baseline would be
//!    measuring a behaviour change this ticket promises not to make.
//!
//! # Two things the ticket's acceptance asked for that are NOT this ticket's
//!
//! **THE VarId COUNTER CANNOT BE FIXED, AND MUST NOT BE.** The ticket asks that "the
//! term-store length and the VarId counter are UNCHANGED after the first". The second
//! half is not available: a var id is the KB's global numbering, and a query pattern's
//! variables must be distinct from every variable the resolver opens for a clause, or
//! two unrelated positions bind together. A `u32` counter also retains nothing — it is
//! not the leak. [`the_var_counter_still_moves_and_that_is_correct`] records the
//! measurement instead of asserting a property the system cannot have.
//!
//! **THE RESOLVER HAS ITS OWN, SMALLER LEAK**, and it is a different site with a
//! different mechanism. MEASURED: converting AND resolving `two(?x)` (a rule goal) grows
//! the store by exactly 1 per query, all of it after the conversion; `Top(a: ?x)` (facts
//! only, no clause opened) grows it by 0. The one slot is `with_fresh_vars`' De Bruijn
//! opening — `term_from_debruijn` allocates a `Term::Var(Global(fresh))` for the head
//! slot a query var linked to, and `Substitution` is `TermId`-keyed throughout, so it
//! cannot take a transient carrier without moving the substitution layer with it. That
//! is a bigger change than this whole ticket and belongs to its own.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term_view::{TermView, ViewHead};
use anthill_core::kb::KnowledgeBase;

use crate::common::{load_kb_bare, load_kb_with, query_pattern_term};

/// Three fields, two facts, and one rule over it — enough that a query both COMPLETES
/// slots (the leak's source) and RESOLVES against real clauses.
const SRC: &str = r#"
namespace j0rm4
  entity Top(a: Int64, b: Int64, c: Int64)
  fact Top(a: 1, b: 2, c: 3)
  fact Top(a: 4, b: 5, c: 6)
  rule two(?a) :- Top(a: ?a, b: ?, c: ?)
end
"#;

/// THE HEADLINE. Converting one pattern N times must leave the hash-consed store the
/// size it was.
///
/// FAILS WHEN THE CHANGE IS BACKED OUT: MEASURED on the baseline, `term_store_len` went
/// 58 → 61 → 64 → 67 over four conversions of this pattern — three slots each, one per
/// omitted field's fresh var plus the `Fn` node whose identity depends on them.
#[test]
fn repeated_conversion_of_one_pattern_does_not_grow_the_term_store() {
    let mut kb = load_kb_bare(&[SRC]);
    // The FIRST conversion is allowed to grow it: a pattern naming symbols or literals
    // the program never wrote (there are none here, but a query may) interns those, and
    // that is the shared vocabulary, not the pattern.
    let _ = query_pattern_term(&mut kb, "j0rm4.Top(a: 1)");
    let after_first = kb.term_store_len();

    for i in 0..8 {
        let _ = query_pattern_term(&mut kb, "j0rm4.Top(a: 1)");
        assert_eq!(
            kb.term_store_len(),
            after_first,
            "conversion #{i} grew the hash-consed store; a query pattern is transient \
             and must not enter it",
        );
    }
}

/// The FULL `anthill query` shape — convert, then resolve — for a query answered by
/// FACTS. No clause is opened, so the resolver's own De Bruijn allocation (the separate
/// site in this file's header) does not arise and the whole run is flat.
///
/// FAILS WHEN THE CHANGE IS BACKED OUT, at the conversion's own growth. It also pins the
/// resolver half, which was ALREADY clean for this query kind: MEASURED, four
/// convert-and-resolve rounds of `Top(a: ?x)` all read `(60, 60)` for
/// (before-resolve, after-resolve).
#[test]
fn a_repeated_fact_matching_query_run_is_flat() {
    let mut kb = load_kb_bare(&[SRC]);
    let cfg = ResolveConfig::default();

    let first = query_pattern_term(&mut kb, "j0rm4.Top(a: ?x)");
    assert_eq!(
        kb.resolve(&[first], &cfg).len(),
        2,
        "the fixture must actually answer, or this measures nothing",
    );
    let after_first = kb.term_store_len();

    for i in 0..8 {
        let goal = query_pattern_term(&mut kb, "j0rm4.Top(a: ?x)");
        assert_eq!(
            kb.resolve(&[goal], &cfg).len(),
            2,
            "query #{i} must keep answering the same two rows",
        );
        assert_eq!(
            kb.term_store_len(),
            after_first,
            "query #{i} grew the hash-consed store",
        );
    }
}

/// THE SEPARATE SITE, MEASURED rather than left to be found later — see this file's
/// header for what it is and why it is not this ticket's.
///
/// The row asserts BOTH halves so it stays honest in both directions: the conversion
/// contributes exactly 0 (this ticket), and the resolution contributes exactly 1 per
/// rule-goal query (the site that remains). If the remaining leak is ever closed this
/// row goes red, which is the intended signal to delete it — an unasserted "known leak"
/// is how one survives its own fix.
#[test]
fn resolution_of_a_rule_goal_still_grows_the_store_by_one() {
    let mut kb = load_kb_bare(&[SRC]);
    let cfg = ResolveConfig::default();
    // Warm up: the first run interns whatever shared vocabulary the query names.
    let warm = query_pattern_term(&mut kb, "j0rm4.two(?x)");
    assert_eq!(kb.resolve(&[warm], &cfg).len(), 2);

    for i in 0..4 {
        let before = kb.term_store_len();
        let goal = query_pattern_term(&mut kb, "j0rm4.two(?x)");
        assert_eq!(
            kb.term_store_len(),
            before,
            "round #{i}: the CONVERSION must contribute nothing — that is this ticket",
        );
        assert_eq!(kb.resolve(&[goal], &cfg).len(), 2);
        assert_eq!(
            kb.term_store_len(),
            before + 1,
            "round #{i}: `with_fresh_vars`' De Bruijn opening still interns one var \
             term per clause opened. If this is now 0, the remaining site has been \
             closed and this row should be deleted rather than relaxed",
        );
    }
}

/// THE NOTE ROW — green on both sides, and here because the ticket's acceptance asked
/// for something the system cannot give. See this file's header.
///
/// It asserts the DIRECTION (the counter moves) rather than a fixed delta, so it does
/// not go red when an unrelated change alters how many variables a clause opens.
#[test]
fn the_var_counter_still_moves_and_that_is_correct() {
    let mut kb = load_kb_bare(&[SRC]);
    let before_convert = kb.var_counter();
    let _ = query_pattern_term(&mut kb, "j0rm4.Top(a: 1)");
    let after_convert = kb.var_counter();
    assert!(
        after_convert > before_convert,
        "the two omitted fields still need variables of their own; a pattern that \
         minted none would share ids with the resolver's opened clause vars",
    );

    // A RULE goal for the resolution half: matching a fact opens no clause, so it is
    // the clause opening — not resolution as such — that mints more.
    let rule_goal = query_pattern_term(&mut kb, "j0rm4.two(?x)");
    let before_resolve = kb.var_counter();
    let _ = kb.resolve(&[rule_goal], &ResolveConfig::default());
    assert!(
        kb.var_counter() > before_resolve,
        "and opening a clause moves it further, which is why 'unchanged across N \
         queries' was never available",
    );
}

/// THE SOUNDNESS CONTROL on the repair this ticket does NOT take. Reusing one fill var
/// per (functor, field) would also make the store constant — and would make these two
/// independent `Top` slots share a variable, so a solution would have to agree on `b`
/// across them. PASSES EITHER WAY today; it is a guard on a future "optimization".
#[test]
fn distinct_patterns_of_one_functor_do_not_share_fill_variables() {
    let mut kb = load_kb_bare(&[SRC]);
    let one = query_pattern_term(&mut kb, "j0rm4.Top(a: 1)");
    let two = query_pattern_term(&mut kb, "j0rm4.Top(a: 4)");

    let b = kb.intern("b");
    let read_b = |kb: &KnowledgeBase, p: &anthill_core::kb::load::QueryPattern| {
        match TermView::head(&TermView::named_arg(p, kb, b).expect("b slot completed"), kb) {
            ViewHead::Var(v) => v,
            other => panic!("the omitted field `b` must be filled with a var, got {other:?}"),
        }
    };
    assert_ne!(
        read_b(&kb, &one),
        read_b(&kb, &two),
        "two patterns' fills must be independent variables — sharing them would force \
         two unrelated facts to agree on `b`",
    );
}

// ── Agreement: the answers are identical to the baseline's ──────────────────
//
// Every row below PASSES EITHER WAY by design. A carrier change that altered one
// answer would be a behaviour change this ticket promises not to make, so these
// are the promise, not the measurement.

/// A partially-written pattern still reaches the facts its completed slots match, and
/// still discriminates on the field it DID write.
#[test]
fn a_completed_pattern_matches_the_facts_it_used_to() {
    let mut kb = load_kb_bare(&[SRC]);
    let cfg = ResolveConfig::default();

    let all = query_pattern_term(&mut kb, "j0rm4.Top(a: ?x)");
    assert_eq!(
        kb.resolve(&[all], &cfg).len(),
        2,
        "an unwritten field matches anything",
    );

    let one = query_pattern_term(&mut kb, "j0rm4.Top(a: 1)");
    assert_eq!(
        kb.resolve(&[one], &cfg).len(),
        1,
        "a written field still discriminates",
    );

    let none = query_pattern_term(&mut kb, "j0rm4.Top(a: 99)");
    assert!(
        kb.resolve(&[none], &cfg).is_empty(),
        "and a field no fact carries still matches nothing",
    );
}

/// §8.3 (WI-20260902-CZJ2N): a BARE entity name is the all-fields-fresh pattern, so
/// `Top` finds exactly what `Top()` finds. The expansion now runs on the transient
/// carrier; it must expand to the same thing.
#[test]
fn the_all_fields_fresh_expansion_still_answers() {
    let mut kb = load_kb_bare(&[SRC]);
    let cfg = ResolveConfig::default();

    let bare = query_pattern_term(&mut kb, "j0rm4.Top");
    let applied = query_pattern_term(&mut kb, "j0rm4.Top()");
    assert_eq!(
        kb.resolve(&[bare], &cfg).len(),
        2,
        "a bare entity name searches for the all-fields-fresh pattern",
    );
    assert_eq!(
        kb.resolve(&[applied], &cfg).len(),
        2,
        "and the applied spelling is the same query",
    );
}

/// WI-1096: a `[…]` in a query pattern lowers to the `cons`/`nil` spine the LOADER
/// stored, or the query cannot match the fact it is looking for. The transient carrier
/// builds that spine itself (`load::build_query_list`), so this pins the shape
/// agreement — the named-arg `cons(head:, tail:)` order included, since a differently
/// ordered pair keys differently in the discrimination tree.
#[test]
fn a_list_literal_pattern_still_matches_its_stored_twin() {
    let mut kb = load_kb_with(
        "namespace j0rm4l\n  import anthill.prelude.{List, Int64}\n  \
         entity Box(items: List[T = Int64])\n  fact Box(items: [1, 2, 3])\nend\n",
    );
    // The namespace in query scope the way `anthill query -i j0rm4l.*` puts it there —
    // a program file's own imports are file-local and do not reach a query (WI-995).
    crate::common::supply_invocation_imports(&mut kb, &["j0rm4l.*"]);
    let cfg = ResolveConfig::default();

    let exact = query_pattern_term(&mut kb, "Box(items: [1, 2, 3])");
    assert_eq!(
        kb.resolve(&[exact], &cfg).len(),
        1,
        "the written literal must take the same shape the fact stored",
    );

    let wrong = query_pattern_term(&mut kb, "Box(items: [1, 2])");
    assert!(
        kb.resolve(&[wrong], &cfg).is_empty(),
        "and a different list must still not match it",
    );
}

/// **THE PRINTER PARITY ROW**, and the one thing `/code-review` found broken: moving the
/// pattern to the occurrence carrier moved `anthill query --query-file`'s LABEL from
/// `TermPrinter::print_term` to `print_occurrence`, and the two printers did not restore
/// the same list surfaces.
///
/// Two rows, and the pair is the point — a `List`-declared slot LOWERS its `[…]` to a
/// cons/nil spine, while a slot whose declared type names a RIVAL collection keeps the
/// flat `ListLiteral(…)` (spec §4.6, WI-1096). The term printer collapsed BOTH to `[…]`;
/// the occurrence printer collapsed neither, and the first fix restored only the spine —
/// so the `Set` row is what caught the remaining half, with the `List` row as its
/// control. FAILS on the intermediate state (`ListLiteral(1, 2)`), and would fail on the
/// baseline too if the labels had not been term-printed there.
#[test]
fn a_query_pattern_label_prints_both_list_surfaces_as_brackets() {
    use anthill_core::persistence::print::TermPrinter;
    let mut kb = load_kb_with(
        "namespace j0rm4p\n  import anthill.prelude.{List, Set, Int64}\n  \
         entity Listed(xs: List[T = Int64])\n  entity Tagged(tags: Set[T = Int64])\n\
         end\n",
    );
    crate::common::supply_invocation_imports(&mut kb, &["j0rm4p.*"]);

    for pattern in ["Listed(xs: [1, 2])", "Tagged(tags: [1, 2])"] {
        let pat = query_pattern_term(&mut kb, pattern);
        let label = TermPrinter::new(&kb).print_occurrence(&pat);
        assert!(
            label.contains("[1, 2]"),
            "`{pattern}` must label with its bracket surface, not with the constructor \
             it lowered (or did not lower) to; got `{label}`",
        );
    }
}

/// WI-476: a name that resolves to no single symbol is a bare intern that heads no
/// clause. `Value` has no `Ident` carrier by design ("minting an unresolved identifier
/// as a runtime value would be a bug"), which is why the pattern rides the OCCURRENCE
/// carrier — so this row is also the reason for that carrier choice.
#[test]
fn an_unresolvable_name_still_heads_no_clause() {
    let mut kb = load_kb_bare(&[SRC]);
    let qt = query_pattern_term(&mut kb, "no_such_thing_j0rm4(?x)");

    assert!(
        kb.undefined_functor(&qt).is_some(),
        "the undefined-functor reporter must still see the bare intern through the \
         transient carrier",
    );
    assert!(
        kb.browse_program_clauses_matching(&qt).is_empty(),
        "and it must head no clause",
    );
}

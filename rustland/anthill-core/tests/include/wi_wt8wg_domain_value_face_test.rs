//! WI-20260911-WT8WG (proposal 060 §2.2) — the VALUE face of a sort's domain:
//! `<Sort>.domain`, cited as an ordinary `Relation`.
//!
//! WI-743 delivered the GOAL face — a typed relational head reads the derived
//! `anthill.kernel.domain_member` relation as an appended body goal. This ticket adds
//! the NAME that reads the same clauses from a value position:
//!
//! ```text
//! Colour.domain(?x)  ==  anthill.kernel.domain_member(?x, Colour)
//! ```
//!
//! THE AUTHOR WRITES NO DOMAIN EXPRESSION. They write a sort; the loader derives the
//! 1-ary projection beside the kernel clause, installs the bound `x: Colour` on it, and
//! from there NOTHING IS NEW — the typer's sweep prepends the conformance goal and
//! appends the member goal exactly as it does for a hand-written typed head, and
//! proposal 052's citation arm already resolves `Sort.rule` to a `Relation` value. So
//! the three readers — mode (in), mode (out), and the citation — cannot disagree: there
//! is ONE set of clauses under all of them.
//!
//! NOT DELIVERED HERE: the PARAMETERISED value face. `List[T = Letter].domain` needs the
//! citation's type argument to reach a clause, and a rule citation's query is built from
//! the clause head alone — **WI-20260911-5G28A** owns that. This ticket turns the silent
//! acceptance loud (see `a_parameterised_sorts_citation_names_its_owner`).
//!
//! WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT — nine axes, each RUN over this file AND
//! `wi743_finite_domain_test` together (39 rows), never predicted. Each back-out MUTATES
//! its site rather than deleting it, so what is measured is the BEHAVIOUR and not the
//! tree's loadability.
//!
//!  * **[a] the derived clause** (`emit_domain_value_face` returns before asserting) —
//!    8 fail: every row here that cites a DERIVED `<Sort>.domain`. Not the two
//!    hand-written rows, not the two kernel-goal rows, not `String.domain` — those three
//!    groups are what separate "the derivation" from "the name", "the written override"
//!    and "the goal face".
//!  * **[b] the BOUND on that clause** (`install_rule_type_bounds` skipped) — 7 fail:
//!    [a]'s eight minus `a_parameterised_sorts_citation_names_its_owner`, which never had
//!    a clause to bound. The count MOVES, not just the column type: measured,
//!    `Colour.domain.takeN(5)` answers 1 and not 3, because with no bound the sweep
//!    appends no member goal and the body-less clause answers one unconstrained row.
//!  * **[b2] the SPAN on that clause** (`set_rule_head_span` skipped) — the BINARY ABORTS:
//!    0 passed, 39 failed. The sweep anchors a body-less clause's generated goals on
//!    `rule_head_span` and hits its own `debug_assert!(false, "a type bound on a body-less
//!    clause with no source head span")`. The strongest control in the file, and the
//!    reason the span is a field of `DomainMemberJob` rather than an afterthought.
//!  * **[c] the 1-ARY hand-written hook** (its arity filter no longer matches) — exactly
//!    2, one per file: `a_written_domain_is_both_the_value_face_and_the_generator` and
//!    wi743's `a_hand_written_domain_narrows_the_sort`. The written relation stops
//!    suppressing the derivation, so both answer the sort's three rows instead of two.
//!  * **[d] the typer's SWEEP EXCLUSION** (`sort_domain_is_written` no longer consulted) —
//!    exactly 1: `a_written_domain_annotated_with_its_own_sort_does_not_loop`. That row
//!    exists because nothing else measures it — every OTHER hand-written fixture leaves
//!    its head unannotated, and the loop needs the annotation to close.
//!  * **[e] the SOURCE declaration in `kernel.anthill`** — **0 fail; all 39 pass.** Stated
//!    rather than hidden. The declaration is the documented surface; what REGISTERS
//!    `anthill.kernel.domain_member` is the bootstrap (`load::register_prelude`), beside
//!    `push_choice` / `and` / `or` / `cut`. So
//!    `the_kernel_domain_relation_is_writable_from_a_rule_body` credits the bootstrap, not
//!    the source line. Backing out the BOOTSTRAP instead is not a behaviour measurement:
//!    36 tests across the suite build a bare `KnowledgeBase::new()` + `register_prelude`
//!    KB with a user sort in it, and every one fails to LOAD — measured, and the reason
//!    that channel has to exist.
//!  * **[f] the PASS-1 MINT of `<Sort>.domain`** (minted at the drain only) — 8 fail, the
//!    SAME rows as [a] by a DIFFERENT mechanism: the clause is built, but a citation is
//!    lowered during the item walk, so `Colour.domain.takeN(5)` is an *unknown functor*
//!    before the name exists. Two axes over one row set — [a] withholds the clause, [f]
//!    the name — and neither is redundant.
//!  * **[g] the CARRIER-NEUTRAL read** in `resolve::builtin_type_domain` — exactly 1:
//!    `a_written_conformance_goal_reads_its_type_through_the_view`. Under the back-out it
//!    is not a wrong answer but an ABORT (`debug_assert!(false, "the bound operand is not
//!    a type term")`), which is what a source-written `domain(?x, Colour)` in mode (in)
//!    did before this ticket.
//!  * **[h] the citation DIAGNOSTIC** (`domain_value_face_refusal` returns `None`) —
//!    exactly 2: `a_parameterised_sorts_citation_names_its_owner` and
//!    `a_declined_sorts_citation_says_why_the_domain_is_missing`. Both citations are
//!    still REFUSED under the back-out; what is lost is the message — the one naming
//!    5G28A, and the one naming the loader's own decline reason. That is why both rows
//!    assert TOKENS and not merely that a load error happened, and why they assert
//!    DIFFERENT tokens: a sort with a domain and no name to cite it by, and a sort with
//!    no derived domain at all, are two facts and get two sentences.
//!
//!  * `a_constructorless_sort_has_no_value_face` fails under NO axis but the [b2] abort,
//!    BY DESIGN: it is the gate's other side — a sort with no constructors never enters
//!    this machinery — and it is here so a future widening of the mint has something to
//!    break.
//!
//! THREE ROWS CAME FROM `/code-review` ON THIS TICKET'S OWN FIRST CUT, and each one is a
//! control for a repair rather than for the feature. Their axis is the repair itself,
//! measured by reverting it:
//!
//!  * `the_minted_name_does_not_shadow_the_kernel_goal` — with `define` in place of
//!    `define_qualified_only`, the fixture is a LOAD ERROR ("expected a term a clause of
//!    `Colour.domain` can match (1 positional), got 2 positional"). A short name in the
//!    sort's `locals` sits in front of `anthill.kernel.domain` for every body written
//!    inside that sort, which is the opposite of declaring the kernel goals writable.
//!  * `a_written_bound_carrying_a_type_variable_suspends` — without
//!    `resolve::view_has_type_variable`, `varBound` answers 0 (REFUTED) where it must
//!    answer one conditional row; its two controls stay at 1-definite and 0 either way,
//!    which is what makes the middle number readable.
//!  * `a_domain_at_an_unrecognised_arity_declines_readably` — with the silent `return`,
//!    the fixture still loads and the goal face still answers 3, and BOTH decline records
//!    are `None`. That row fails on the reason alone, which is the whole point: the
//!    defect was invisible in every count.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

use crate::common::{interp_for, try_load_kb_with};

fn definite_answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .filter(|s| s.is_definite())
        .count()
}

fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

/// The op returns an `Int64`, so the row is a COUNT and any carrier confusion in the
/// harness shows up as a load error rather than as a silently-passing assertion.
fn int_op(src: &str, qn: &str) -> i64 {
    let mut interp = interp_for(src);
    let v = interp
        .call(qn, &[])
        .unwrap_or_else(|e| panic!("`{qn}` must run: {e:?}"));
    crate::common::scalar_int(interp.kb(), &v)
        .unwrap_or_else(|| panic!("`{qn}` must answer an Int64"))
}

const COLOUR_SRC: &str = r#"
namespace test.wt8wg.colour
  import anthill.prelude.{Int64, String, List, Relation, Error, EmptyStream}
  import anthill.prelude.PartialEq.{eq}

  -- The author writes THIS, and nothing else. No `palette` facts, no wrapper sort,
  -- no `domain` of their own.
  sort Colour
    entity red
    entity green
    entity blue
  end

  -- 26 of the 37 all-nullary corpus sorts are this shape.
  sort Unit
    entity only
  end

  operation colours() -> Int64 effects Error = Colour.domain.takeN(5).length()
  operation units()   -> Int64 effects Error = Unit.domain.takeN(5).length()
  operation firstColour() -> Colour effects {Error, Error[T = EmptyStream]} =
    Colour.domain.head.x
  operation reds() -> Int64 effects Error =
    Colour.domain.where(lambda c -> eq(c.x, red())).takeN(5).length()
end
"#;

/// ACCEPTANCE, first half: the citation answers the sort's inhabitants and no more.
#[test]
fn the_derived_value_face_answers_the_sorts_inhabitants() {
    assert_eq!(
        int_op(COLOUR_SRC, "test.wt8wg.colour.colours"),
        3,
        "`Colour.domain` is the three constructors the author declared"
    );
    assert_eq!(
        int_op(COLOUR_SRC, "test.wt8wg.colour.units"),
        1,
        "a one-constructor sort answers exactly once — the row that separates \
         'the citation resolves' from 'it resolves to the RIGHT relation'"
    );
}

/// ACCEPTANCE, second half: the column is TYPED at the sort, which is what the bound on
/// the derived clause is for. A count alone passes with an untyped `Term` column.
#[test]
fn the_derived_column_is_typed_at_the_sort() {
    let mut interp = interp_for(COLOUR_SRC);
    let v = interp
        .call("test.wt8wg.colour.firstColour", &[])
        .expect("`Colour.domain.head.x` runs");
    let ctor = crate::common::entity_functor(interp.kb(), &v)
        .map(|s| interp.kb().qualified_name_of(s).to_string());
    assert_eq!(ctor.as_deref(), Some("test.wt8wg.colour.Colour.red"));

    // THE REFUSAL is the half that measures the TYPE rather than the value: the same
    // expression in an `Int64` slot must not load.
    let wrong = COLOUR_SRC.replace(
        "operation firstColour() -> Colour effects {Error, Error[T = EmptyStream]} =",
        "operation firstColour() -> Int64 effects {Error, Error[T = EmptyStream]} =",
    );
    let errs = try_load_kb_with(&wrong)
        .err()
        .expect("`Colour.domain.head.x` must not satisfy an `Int64` return");
    crate::common::assert_refused_naming(
        &errs,
        &["Int64"],
        "the derived column is `Colour`, so an `Int64` return is a type error",
    );
}

/// 052's algebra over the derived face — it is a REAL `Relation`, not a special case.
#[test]
fn the_value_face_is_an_ordinary_relation() {
    assert_eq!(
        int_op(COLOUR_SRC, "test.wt8wg.colour.reds"),
        1,
        "`Colour.domain.where(c -> eq(c.x, red()))` keeps one of the three rows"
    );
}

const NAT_SRC: &str = r#"
namespace test.wt8wg.nat
  import anthill.prelude.{Int64, String, List, Relation, Error}

  sort Nat
    entity z
    entity s(p: Nat)
  end

  operation firstFour() -> List[T = (x: Nat)] effects Error = Nat.domain.takeN(4)
end
"#;

/// The value face inherits WI-743's FAIRNESS, and the order is what says so. A count
/// alone passes with the rows reversed, or with the recursive constructor first.
#[test]
fn a_recursive_sorts_value_face_enumerates_by_depth() {
    let mut interp = interp_for(NAT_SRC);
    let rows = interp
        .call("test.wt8wg.nat.firstFour", &[])
        .expect("`Nat.domain.takeN(4)` runs");
    let kb = interp.kb();
    let depths: Vec<usize> = crate::common::list_heads(&rows)
        .iter()
        .map(|row| {
            let mut v = crate::common::sole_column(row);
            let mut d = 0;
            // `s(p: …)` down to `z`. `entity_field` PANICS on a missing field, which is
            // what makes a shape change here a failure rather than a depth of 0.
            while crate::common::entity_functor(kb, &v)
                .map(|f| kb.local_name_of(f).to_string())
                .as_deref()
                == Some("s")
            {
                v = crate::common::entity_field(kb, &v, "p", 0);
                d += 1;
            }
            d
        })
        .collect();
    assert_eq!(
        depths,
        vec![0, 1, 2, 3],
        "`z`, `s(z)`, `s(s(z))`, `s(s(s(z)))` — base constructor first, then by depth"
    );
}

const HAND_SRC: &str = r#"
namespace test.wt8wg.hand
  import anthill.prelude.{Int64, String, List, Relation, Error}

  sort Palette
    entity red
    entity green
    entity blue
    -- 1-ARY since this ticket: the same relation the citation reads.
    rule domain(?x) :- ?x <=> red() | ?x <=> green()
  end

  rule pick(?x: Palette) :- true
  rule is_blue(?x: Palette) :- ?x <=> blue()

  operation written() -> Int64 effects Error = Palette.domain.takeN(5).length()
end
"#;

/// A HAND-WRITTEN `domain` is the value face AND the generator, and the two are the same
/// relation — which is the whole point of the 1-ary spelling.
#[test]
fn a_written_domain_is_both_the_value_face_and_the_generator() {
    assert_eq!(
        int_op(HAND_SRC, "test.wt8wg.hand.written"),
        2,
        "the citation reads the WRITTEN clauses — two rows, not the sort's three"
    );
    let mut kb = try_load_kb_with(HAND_SRC).expect("loads");
    assert_eq!(
        definite_answers(&mut kb, "test.wt8wg.hand.pick(?x)"),
        2,
        "and so does the typed head, through the loader's forwarding clause"
    );
    assert_eq!(
        answers(&mut kb, "test.wt8wg.hand.is_blue(?x)"),
        0,
        "domain-defining in BOTH modes: `blue()` conforms to `Palette` and is not a \
         member of its domain"
    );
}

const HAND_TYPED_SRC: &str = r#"
namespace test.wt8wg.handt
  import anthill.prelude.{Int64, String, List, Relation, Error}

  sort Palette
    entity red
    entity green
    entity blue
    -- ANNOTATED WITH ITS OWN SORT: the natural 1-ary spelling, and the one that would
    -- loop through the forwarding clause without the typer's exclusion.
    rule domain(?x: Palette) :- ?x <=> red() | ?x <=> green()
  end

  operation written() -> Int64 effects Error = Palette.domain.takeN(5).length()
end
"#;

/// THE SELF-CALL TRAP. WI-743 refused this clause at the loader, which cost nothing while
/// the written spelling was 2-ary and the annotation was redundant. At the 1-ARY spelling
/// the annotation is the natural thing to write, so the loop is cut at the typer instead:
/// a clause of a WRITTEN `S.domain` gets the conformance goal and not the member goal.
#[test]
fn a_written_domain_annotated_with_its_own_sort_does_not_loop() {
    assert_eq!(
        int_op(HAND_TYPED_SRC, "test.wt8wg.handt.written"),
        2,
        "the annotated clause answers its own two rows and does not re-enter itself"
    );
}

const KERNEL_SRC: &str = r#"
namespace test.wt8wg.kernel
  import anthill.prelude.{Int64}
  import anthill.kernel.*

  sort Colour
    entity red
    entity green
    entity blue
  end

  rule members(?x) :- domain_member(?x, Colour)
  rule redConforms() :- ?x <=> red(), domain(?x, Colour)
  rule redIsNotAnInt(?y) :- ?y <=> red(), domain(?y, Int64)
end
"#;

/// `anthill.kernel.domain_member` IS WRITABLE — it is declared in `kernel.anthill`
/// (061's body-less form) rather than minted at the derivation's drain, which is after
/// every body in the batch has resolved. MEASURED before this ticket: under
/// `import anthill.kernel.*`, `domain`, `domain_leaf`, `find_dictionary` and `push_and`
/// all resolved and `domain_member` alone "named nothing".
#[test]
fn the_kernel_domain_relation_is_writable_from_a_rule_body() {
    let mut kb = try_load_kb_with(KERNEL_SRC).expect("`domain_member` must resolve");
    assert_eq!(
        definite_answers(&mut kb, "test.wt8wg.kernel.members(?x)"),
        3,
        "a written `domain_member(?x, Colour)` generates the sort's three inhabitants"
    );
}

/// …and the CONFORMANCE goal beside it no longer aborts on a source-written type operand.
/// Before this ticket `domain(?x, Colour)` with `?x` bound hit
/// `debug_assert!(false, "the bound operand is not a type term")` at resolve.rs — an
/// abort in a debug build and a resolver `Error` in release — because the reader demanded
/// the `Value::Term` carrier the TYPER's splice produces. A written goal's operand rides
/// whatever the body lowering produced, so it is read through the VIEW.
#[test]
fn a_written_conformance_goal_reads_its_type_through_the_view() {
    let mut kb = try_load_kb_with(KERNEL_SRC).expect("loads");
    assert_eq!(
        definite_answers(&mut kb, "test.wt8wg.kernel.redConforms()"),
        1,
        "`red()` conforms to `Colour`"
    );
    // THE CONTROL: the same goal at a type the value does not conform to must REFUTE,
    // not succeed — so the row above is a verdict and not a vacuous pass.
    assert_eq!(
        answers(&mut kb, "test.wt8wg.kernel.redIsNotAnInt(?y)"),
        0,
        "`red()` does not conform to `Int64`"
    );
}

const PARAM_BRACED: &str = r#"
namespace test.wt8wg.braced
  import anthill.prelude.{Int64, String, List, Relation, Error}
  sort Letter
    entity a
    entity b
  end
  operation n() -> Int64 effects Error = List[T = Letter].domain.takeN(5).length()
end
"#;

const PARAM_BARE: &str = r#"
namespace test.wt8wg.bare
  import anthill.prelude.{Int64, String, List, Relation, Error}
  operation n() -> Int64 effects Error = List.domain.takeN(5).length()
end
"#;

/// DECISION C — no value face for a parameterised sort, and the citation says WHOSE
/// ticket that is. MEASURED before this change, on a hand-written twin inside a
/// parameterised sort: `Wrap[T = Colour].dom.takeN(5)` AND bare `Wrap.dom.takeN(5)` BOTH
/// LOAD CLEAN — the bracket is validated and dropped, the bound is a type variable so the
/// sweep skips the member goal, and the citation can only flounder at the drain.
#[test]
fn a_parameterised_sorts_citation_names_its_owner() {
    for (what, src) in [("braced", PARAM_BRACED), ("bare", PARAM_BARE)] {
        let errs = try_load_kb_with(src)
            .err()
            .unwrap_or_else(|| panic!("the {what} parameterised citation must be refused"));
        crate::common::assert_refused_naming(
            &errs,
            &["has a domain but no `.domain` to cite it by", "5G28A"],
            "a parameterised sort's citation names the ticket that owns it",
        );
    }
    // THE GOAL FACE IS UNTOUCHED — `List` keeps its derived member clause. Without this
    // the refusal above would pass just as well if the derivation had been switched off
    // for parameterised sorts entirely.
    let kb = try_load_kb_with(
        r#"
namespace test.wt8wg.goalface
  import anthill.prelude.{Int64, List}
end
"#,
    )
    .expect("loads");
    let list = kb.try_resolve_symbol("anthill.prelude.List").expect("List");
    assert!(
        kb.has_domain_member(list),
        "`List` still has its derived `domain_member` clause — only the NAME is withheld"
    );
}

const FIELD_SRC: &str = r#"
namespace test.wt8wg.field
  import anthill.prelude.{Int64, String, List, Relation, Error}

  sort Colour
    entity red
    entity green
    entity blue
  end

  -- §6.3: the eponymous constructor IS the sort, so this field and the derived relation
  -- want the same written name.
  sort Thing
    entity Thing(domain: Colour)
  end

  operation things() -> Int64 effects Error = Thing.domain.takeN(9).length()
  operation theField() -> Colour = Thing(domain: red()).domain
end
"#;

/// kernel-language.md §5.3 says a `domain` in a sort's scope that is NOT the member
/// relation is not the sort's domain. Its FIELD case turns out not to be a collision at
/// all — MEASURED, and the reason the corpus's three `domain` fields (`guardians.Address`,
/// github-todo's `FactRef` and `FactHolds`) all keep a derived value face: a field is
/// reached through the entity's field table, never through this symbol.
#[test]
fn a_field_named_domain_and_the_derived_relation_coexist() {
    assert_eq!(
        int_op(FIELD_SRC, "test.wt8wg.field.things"),
        3,
        "`Thing.domain` is the sort's three inhabitants (one per `Colour`)"
    );
    let mut interp = interp_for(FIELD_SRC);
    let v = interp
        .call("test.wt8wg.field.theField", &[])
        .expect("the FIELD still reads");
    let ctor = crate::common::entity_functor(interp.kb(), &v)
        .map(|s| interp.kb().qualified_name_of(s).to_string());
    assert_eq!(ctor.as_deref(), Some("test.wt8wg.field.Colour.red"));
}

/// THE THREE READERS READ ONE SET OF CLAUSES — the design claim, asserted rather than
/// argued. The citation, mode (out) through a typed head, and an explicit kernel goal must
/// agree on the SAME sort in the SAME KB; a derivation that answered the citation from a
/// second clause set would pass every count row above and fail this one.
#[test]
fn the_citation_and_the_goal_face_answer_the_same_rows() {
    const SRC: &str = r#"
namespace test.wt8wg.agree
  import anthill.prelude.{Int64, String, List, Relation, Error}
  import anthill.kernel.*

  sort Colour
    entity red
    entity green
    entity blue
  end

  rule viaHead(?x: Colour) :- true
  rule viaKernel(?x) :- domain_member(?x, Colour)

  operation viaCitation() -> Int64 effects Error = Colour.domain.takeN(9).length()
end
"#;
    let cited = int_op(SRC, "test.wt8wg.agree.viaCitation");
    let mut kb = try_load_kb_with(SRC).expect("loads");
    let head = definite_answers(&mut kb, "test.wt8wg.agree.viaHead(?x)");
    let kernel = definite_answers(&mut kb, "test.wt8wg.agree.viaKernel(?x)");
    assert_eq!(
        (cited as usize, head, kernel),
        (3, 3, 3),
        "the citation, the typed head and the explicit kernel goal are one relation"
    );
}

/// A SECOND LOAD OF THE SAME FILE MUST NOT DOUBLE THE ANSWERS. Two channels could each
/// produce a duplicate — the pass-1 mint (a second `define` under one name) and the drain
/// (a second clause) — and a doubled domain is the kind of defect a `takeN` row reads as
/// success. The guards are `mint_domain_value_face_name`'s name check and pass 1's
/// `has_domain_member` skip; this drives both at once.
#[test]
fn a_second_load_does_not_duplicate_the_value_face() {
    use anthill_core::kb::load::{self, NullResolver};

    let src = r#"
namespace test.wt8wg.reload
  import anthill.prelude.{Int64, String, List, Relation, Error}
  sort Colour
    entity red
    entity green
    entity blue
  end
end
"#;
    let mut kb = try_load_kb_with(src).expect("first load");
    let parsed = anthill_core::parse::parse(src).expect("parse");
    load::load_all(&mut kb, &[&parsed], &NullResolver).expect("second load of the same file");

    let dom = kb
        .try_resolve_symbol("test.wt8wg.reload.Colour.domain")
        .expect("`Colour.domain` still resolves to one name after two loads");
    assert_eq!(
        kb.clause_ids_of(dom).len(),
        1,
        "one derived clause, not one per load"
    );
    assert_eq!(
        definite_answers(&mut kb, "test.wt8wg.reload.Colour.domain(?x)"),
        3,
        "and three rows, not six"
    );
}

/// `/code-review` FINDING — THE MINTED NAME MUST NOT SHADOW THE KERNEL GOAL.
///
/// `SymbolTable::define` inserts the SHORT name into the scope's `locals`, and
/// `resolve_in_scope` reads locals before imports. Minting a local `domain` in every
/// constructor-bearing sort therefore put one in front of `anthill.kernel.domain` for
/// every rule body written INSIDE that sort. MEASURED before the repair: this fixture was
/// a LOAD ERROR — *expected a term a clause of `Colour.domain` can match (1 positional),
/// got 2 positional*. The mint is `define_qualified_only` now (WI-422's API, for exactly
/// this leak), and the value face loses nothing: it is cited as `Colour.domain`.
#[test]
fn the_minted_name_does_not_shadow_the_kernel_goal() {
    const SRC: &str = r#"
namespace test.wt8wg.shadow
  import anthill.prelude.{Int64, String, List, Relation, Error}
  import anthill.kernel.*

  sort Colour
    entity red
    entity green
    entity blue
    -- written INSIDE the sort, where the minted `domain` would shadow the kernel's
    rule mine(?x) :- domain(?x, Colour)
  end

  operation cited() -> Int64 effects Error = Colour.domain.takeN(9).length()
end
"#;
    let mut kb = try_load_kb_with(SRC)
        .expect("a 2-ary kernel `domain` goal inside a sort body must still load");
    assert_eq!(
        answers(&mut kb, "test.wt8wg.shadow.Colour.mine(?x)"),
        1,
        "and it is the CONFORMANCE goal, which delays on an unbound `?x` — WI-742's \
         ladder, unchanged"
    );
    // THE OTHER HALF: the qualified-only mint must still serve the citation.
    assert_eq!(int_op(SRC, "test.wt8wg.shadow.cited"), 3);
}

/// `/code-review` FINDING — A SOURCE-WRITTEN BOUND CARRYING A TYPE VARIABLE SUSPENDS.
///
/// `type_is_undetermined` walks for type variables only on the `Value::Term` carrier;
/// every other carrier is called DETERMINED as soon as its head is decidable. So the new
/// source-written arm reached `types_compatible` with a free `?e` in the bound and came
/// back REFUTED — a verdict, where WI-067's rule is that an open variable never gets one.
/// Before this ticket the same shape was a loud abort, so the arm turned a loud error into
/// a silently wrong answer until `view_has_type_variable` was added beside it.
///
/// THE TWO CONTROLS ARE THE POINT: without them "0 rows" and "1 conditional row" are hard
/// to tell from a fixture that simply cannot reach a verdict.
#[test]
fn a_written_bound_carrying_a_type_variable_suspends() {
    const SRC: &str = r#"
namespace test.wt8wg.openbound
  import anthill.prelude.{Int64, String, List}
  import anthill.kernel.*

  sort Letter
    entity a
    entity b
  end

  -- `?x` is BOUND first, so the unbound-value delay cannot stand in for the verdict.
  rule varBound(?x)    :- ?x <=> [a()], domain(?x, List[T = ?e])
  rule groundBound(?x) :- ?x <=> [a()], domain(?x, List[T = Letter])
  rule wrongBound(?x)  :- ?x <=> [a()], domain(?x, Int64)
end
"#;
    let mut kb = try_load_kb_with(SRC).expect("loads");
    assert_eq!(
        (
            answers(&mut kb, "test.wt8wg.openbound.varBound(?x)"),
            definite_answers(&mut kb, "test.wt8wg.openbound.varBound(?x)")
        ),
        (1, 0),
        "a free `?e` in the bound leaves the row CONDITIONAL — not refuted, not definite"
    );
    assert_eq!(
        definite_answers(&mut kb, "test.wt8wg.openbound.groundBound(?x)"),
        1,
        "CONTROL: the same shape with a closed bound reaches a verdict and HOLDS"
    );
    assert_eq!(
        answers(&mut kb, "test.wt8wg.openbound.wrongBound(?x)"),
        0,
        "CONTROL: and a closed bound the value does not satisfy REFUTES — so the row \
         above is a withheld verdict, not a guard that never decides anything"
    );
}

/// `/code-review` FINDING — A `domain` AT AN ARITY THE HOOK DOES NOT RECOGNISE DECLINES
/// READABLY, instead of returning in silence.
///
/// The ladder knows 1-ary (forward to it) and 2-ary (refuse, naming the 1-ary spelling).
/// A bare nullary or 3-ary `domain` is neither, so the author's own relation keeps the
/// name and the structural derivation runs beside it. MEASURED before the repair: the
/// fixture loaded clean, the goal face answered the sort's 3 rows, and BOTH decline
/// records were `None` — so `Sort.domain` cited an unrelated relation with nothing
/// anywhere saying why.
#[test]
fn a_domain_at_an_unrecognised_arity_declines_readably() {
    const SRC: &str = r#"
namespace test.wt8wg.arity
  import anthill.prelude.{Int64, String, List, Relation, Error}

  sort S
    entity one
    entity two
    entity three
    rule domain(?a, ?b, ?c) :- ?a <=> one(), ?b <=> two(), ?c <=> three()
  end

  rule pick(?x: S) :- true
end
"#;
    let mut kb = try_load_kb_with(SRC).expect("an unrelated `domain` relation is the \
                                               author's own and does not fail the load");
    assert_eq!(
        definite_answers(&mut kb, "test.wt8wg.arity.pick(?x)"),
        3,
        "the GOAL face is untouched — the derivation ran"
    );
    let s = kb.try_resolve_symbol("test.wt8wg.arity.S").expect("S");
    let reason = kb
        .domain_value_face_decline_reason(s)
        .expect("the value face declined, and says so");
    assert!(
        reason.contains("arity 3") && reason.contains("domain(?x)"),
        "the reason names the arity found and the spelling expected, got: {reason}"
    );
}

/// A DECLINED sort — one whose derivation found a field type it cannot name — has a
/// minted `<Sort>.domain` with no clause behind it, exactly as a parameterised sort does.
/// Its citation must say WHY, from `domain_member_decline_reason`; without that second
/// arm the author is told the name is unresolved, which is true and useless.
#[test]
fn a_declined_sorts_citation_says_why_the_domain_is_missing() {
    let errs = try_load_kb_with(
        r#"
namespace test.wt8wg.declined
  import anthill.prelude.{Int64, String, List, Relation, Error}
  sort Holder
    entity hold(xs: List)
  end
  operation n() -> Int64 effects Error = Holder.domain.takeN(5).length()
end
"#,
    )
    .err()
    .expect("a declined sort has no value face to cite");
    crate::common::assert_refused_naming(
        &errs,
        &["has no derived domain", "no type arguments"],
        "a DECLINED sort's citation says it has no domain — not that it has one with no \
         name, which is the parameterised sort's case and a different sentence",
    );
}

/// A sort with NO constructors has no domain to derive and no name to cite, so the
/// citation is the ordinary unknown-member error — LOUD AT LOAD, where a
/// derived-but-floundering member would have been loud only at the drain.
#[test]
fn a_constructorless_sort_has_no_value_face() {
    let errs = try_load_kb_with(
        r#"
namespace test.wt8wg.leaf
  import anthill.prelude.{Int64, String, List, Relation, Error}
  operation n() -> Int64 effects Error = String.domain.takeN(5).length()
end
"#,
    )
    .err()
    .expect("`String.domain` names nothing");
    crate::common::assert_refused_naming(
        &errs,
        &["String.domain.takeN"],
        "a sort with no constructors has no `.domain` member at all",
    );
}

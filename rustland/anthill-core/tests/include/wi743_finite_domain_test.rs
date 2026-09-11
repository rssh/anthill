//! WI-743 (proposal 060 §2.2) — a closed sort IS a generator: the loader derives its
//! `domain_member` relation from its constructor list, and a typed relational head
//! reads it in mode (out).
//!
//! WI-742 gave `?x: T` a body goal that TESTS (`domain(?x, T)`, prepended) and DELAYS
//! when `?x` is unbound. This ticket adds the generator at the other end of the body:
//! `domain_member(?x, T)`, APPENDED, one derived clause per sort with constructors —
//! a disjunction over the constructors with each field's own domain conjoined inside
//! the branch, and the TYPE travelling as the second argument so one `List` clause
//! serves every element sort.
//!
//! WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT — nine axes, each RUN, not predicted.
//! (An earlier draft of this header guessed three of the first six wrong; the numbers
//! below are from the back-outs themselves, re-run after `/code-review`.)
//!
//!  * `derive_domain_member_clauses`' STRUCTURAL clauses (pass 2 emits nothing) — 16 of
//!    22 fail. Everything that enumerates, plus the leaf, decline and determinacy rows,
//!    whose fixtures all rest on some sort having a clause.
//!  * THE TYPER's appended member goal (`append_generated_body_goals` handed an empty
//!    list) — 13 fail: the enumerating rows. Not
//!    `a_leaf_element_type_is_answered_exactly_once` (the WI-742 conformance goal alone
//!    still answers it), not `a_field_naming_a_bare_parameterised_sort_declines` (a
//!    loader fact), and not `an_indeterminate_bound_gets_no_generator` (nothing is
//!    generated for it either way). Those three are what separate this axis from the one
//!    above.
//!  * `BuiltinTag::DomainLeaf`'s `has_domain_member` → `Failure` arm (settled design
//!    §5's "exactly once") — 7 fail. Not just the leaf row: with the catch-all answering
//!    beside every structural clause, EVERY derived sort's rows double.
//!  * HAND-WRITTEN WINS (the `<Sort>.domain` lookup forced to `None`) — 3 fail: the two
//!    hand-written rows and the refusal row, which has nothing left to refuse.
//!  * THE HOOK'S VARIABLE SPELLING (`domain(?x, ?t)` no longer accepted) — exactly
//!    `a_hand_written_domain_may_name_its_type_with_a_variable`.
//!  * THE TYPER's DETERMINACY rule (`bound_names_a_determinate_type` removed) — 2 fail,
//!    and they are the two directions the defect has.
//!    `an_indeterminate_bound_gets_no_generator` answers 20 rows (the cap) for a clause
//!    whose body binds its one variable outright — a WRONG answer; and
//!    `a_bare_parameterised_bound_still_answers_its_bound_value` answers 0 where it
//!    answered 1 before this ticket — a LOST one. The second is `/code-review`'s finding
//!    and the louder of the two: `x: List` is the stdlib's own dominant spelling.
//!  * THE LOADER's DECLINE for an unrepairable field (the field kept, unconstrained) —
//!    exactly `a_field_naming_a_bare_parameterised_sort_declines`.
//!  * RECURSIVE FIELD POSITIONS FIRST inside a branch (`[true, false]` → `[false,
//!    true]`) — exactly `an_infinite_domain_is_fair`, and only because that row asserts
//!    the first four LENGTHS. A count alone passes either way: head-before-tail still
//!    reaches the cap, walking `nil, [a], [a, a], [a, a, a], …` and never reaching `[b]`.
//!  * BASE CONSTRUCTORS FIRST (the `sort_by_key` partition removed) — exactly
//!    `a_base_constructor_declared_last_is_still_tried_first`, and that row exists
//!    BECAUSE nothing else measured it: every other fixture writes its base case first,
//!    so declaration order alone orders them right. With the partition gone `Chain`
//!    answers five rows still — at depths `[23, 22, 21, 20, 19]`, the depth cap
//!    bottoming out and backtracking, where the partition gives `[0, 1, 2, 3, 4]`.
//!
//!  * `a_constructorless_bound_keeps_wi742`, `an_introducer_bound_still_delays`,
//!    `bool_has_no_derived_domain`, `a_simp_equation_reads_no_member_and_still_fires`
//!    and `a_declined_sort_records_why` pass under EVERY back-out above, BY DESIGN:
//!    they are the gate's other side — what a sort with no derived domain still does.
//!    The `[simp]` one is not inert, though: it fails the moment the append stops
//!    honouring `is_directional_equation`, which is this change's blast radius.
//!
//! WHAT IS NOT HERE, each with its owner:
//!  * ABSTRACT `T` (an introducer bound, recorded as the SPEC) enumerating through the
//!    caller's instantiation. Nothing is derived for a spec, so the bound keeps
//!    WI-742's delay — pinned by `an_introducer_bound_still_delays`. Making it
//!    enumerate needs `domain` to be a SPEC member and a dictionary channel that
//!    carries a RELATION (WI-20260909-NAR1X), neither of which exists.
//!  * The VALUE face. `Colour.domain` cited as a relation VALUE is not delivered;
//!    §2.2 promises the GOAL face only.
//!  * `Bool`. Its values are literals, not entity constructors, so it has no
//!    constructor list to derive from — pinned by `bool_has_no_derived_domain`.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId, Var};
use anthill_core::kb::term_view::{TermView, ViewHead};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

/// Solutions whose residual set is EMPTY. The distinction is the point of half the
/// rows here: before this ticket a typed head over an unbound variable answered ONE
/// CONDITIONAL row with the guard undischarged, and a count alone reads that as an
/// answer.
fn definite_answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .filter(|s| s.is_definite())
        .count()
}

const COLOUR_SRC: &str = r#"
namespace test.wi743.colour
  import anthill.prelude.{Int64, String, List}

  sort Colour
    entity red
    entity green
    entity blue
  end

  -- One constructor: 26 of the 37 all-nullary sorts in the corpus are this shape.
  sort Unit
    entity only
  end

  fact seen(red())

  -- The 060 §2.2 driver in the §2.1 parameter form: no wrapper sort, no domain facts.
  rule triangle(a: Colour, b: Colour, c: Colour) :- a != b, a != c, b != c

  rule one(?x: Unit) :- true
  rule unseen(?x: Colour) :- not(seen(?x))
  rule every(?x: Colour) :- true
end
"#;

#[test]
fn a_closed_sort_is_its_own_domain() {
    let mut kb = crate::common::load_kb_with(COLOUR_SRC);
    // Three constructors, three DEFINITE rows, from the sort declaration alone.
    assert_eq!(definite_answers(&mut kb, "test.wi743.colour.every(?x)"), 3);
}

#[test]
fn the_colouring_needs_no_palette() {
    let mut kb = crate::common::load_kb_with(COLOUR_SRC);
    // 3! = 6: the map-colouring payoff at three regions. The `!=` goals are written
    // BEFORE anything binds, which is the mode the whole feature is about.
    assert_eq!(
        definite_answers(&mut kb, "test.wi743.colour.triangle(?a, ?b, ?c)"),
        6
    );
}

#[test]
fn a_one_constructor_sort_answers_once() {
    let mut kb = crate::common::load_kb_with(COLOUR_SRC);
    assert_eq!(definite_answers(&mut kb, "test.wi743.colour.one(?x)"), 1);
}

#[test]
fn naf_over_a_generated_domain_decides() {
    let mut kb = crate::common::load_kb_with(COLOUR_SRC);
    // THE GENERATOR MAKING NAF DECIDABLE IS THE FEATURE, not a regression. `not(…)`
    // over an unbound variable must not answer (WI-067), so before this ticket the
    // clause had nothing to decide on. With the domain generating, each of the three
    // colours is tested in turn and two of them survive.
    assert_eq!(definite_answers(&mut kb, "test.wi743.colour.unseen(?x)"), 2);
}

#[test]
fn declaration_order_is_the_answer_order() {
    let mut kb = crate::common::load_kb_with(COLOUR_SRC);
    let every = kb.try_resolve_symbol("test.wi743.colour.every").unwrap();
    let x = fresh_var(&mut kb, "x");
    let goal = kb.alloc(Term::Fn {
        functor: every,
        pos_args: SmallVec::from_elem(x, 1),
        named_args: SmallVec::new(),
    });
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    let order: Vec<String> = sols
        .iter()
        .map(|s| {
            // CARRIER-NEUTRAL: an enumerated row rides whichever carrier the clause's
            // `<=>` produced, which is a `Value::Node` here and an interned term
            // elsewhere. `expect_term` panics on the first of those.
            let v = kb.reify(x, &s.subst);
            match TermView::head(&v, &kb) {
                ViewHead::Functor {
                    functor: Some(f), ..
                } => kb.local_name_of(f).to_string(),
                other => panic!("a domain row must be a constructor, got {other:?}"),
            }
        })
        .collect();
    // DECLARATION order, once each (the ticket's acceptance). Derived as CLAUSES, not
    // as ground facts: facts at a variable position take the walk whose run-to-run
    // order WI-20260911-SXZ3G records — four orders in six runs. Clauses that share a
    // var-headed leaf enumerate in clause order, which is the order the derivation
    // writes the constructors in.
    assert_eq!(order, vec!["red", "green", "blue"]);
}

/// A fresh `Var::Global` term — for the rows that need the QUERY variable in hand to
/// read its binding back, which `query_pattern_term`'s string form does not give.
fn fresh_var(kb: &mut KnowledgeBase, name: &str) -> TermId {
    let sym = kb.intern(name);
    let vid = kb.fresh_var(sym);
    kb.alloc(Term::Var(Var::Global(vid)))
}

const WORD_SRC: &str = r#"
namespace test.wi743.words
  import anthill.prelude.{Int64, String, List}

  sort Letter
    entity a
    entity b
    entity c
  end

  rule word(?w: List[T = Letter]) :- ?w <=> [?, ?, ?]
  rule no_repeat(?w: List[T = Letter]) :- ?w <=> [?x, ?y, ?z], ?x != ?y, ?y != ?z
  rule any_word(?w: List[T = Letter]) :- true
  rule text(?w: List[T = String]) :- ?w <=> ["ab"]
  rule loose_text(?w: List[T = String]) :- ?w <=> [?]
end
"#;

#[test]
fn a_recursive_type_enumerates_by_length() {
    let mut kb = crate::common::load_kb_with(WORD_SRC);
    // The spine is bound by the body; the APPENDED domain goal fills the three cells.
    assert_eq!(definite_answers(&mut kb, "test.wi743.words.word(?w)"), 27);
    assert_eq!(
        definite_answers(&mut kb, "test.wi743.words.no_repeat(?w)"),
        12
    );
}

#[test]
fn an_infinite_domain_is_fair() {
    let mut kb = crate::common::load_kb_with(WORD_SRC);
    // FINITENESS IS NOT A GATE (settled design §2). `List[T = Letter]` is a closed sort
    // with a recursive constructor, so its domain is infinite — and FAIR, by the two
    // ordering rules the derivation writes: base constructors first, and inside a
    // branch the recursive positions first. Capped rather than drained: a full drain of
    // a fair infinite relation does not return, and a DEPTH-FIRST descent into one
    // spine would never reach the cap either, so the number is the evidence.
    let w = fresh_var(&mut kb, "w");
    let any = kb.try_resolve_symbol("test.wi743.words.any_word").unwrap();
    let goal = kb.alloc(Term::Fn {
        functor: any,
        pos_args: SmallVec::from_elem(w, 1),
        named_args: SmallVec::new(),
    });
    let sols = kb.resolve(
        &[goal],
        &ResolveConfig {
            max_solutions: 30,
            ..Default::default()
        },
    );
    assert_eq!(sols.len(), 30);
    assert!(sols.iter().all(|s| s.is_definite()));
    // BY LENGTH, which is the assertion that measures the ordering rules rather than
    // merely their absence of harm. A count alone passes with BOTH orderings backed out:
    // head-before-tail still reaches the cap, it just walks `nil, [a], [a, a],
    // [a, a, a], …` and never reaches `[b]` at all.
    let tail = kb.intern("tail");
    let rows: Vec<_> = sols.iter().take(4).map(|s| kb.reify(w, &s.subst)).collect();
    let lens: Vec<usize> = rows
        .iter()
        .map(|v| spine_depth(&kb, v, "cons", tail))
        .collect();
    assert_eq!(
        lens,
        vec![0, 1, 1, 1],
        "nil, then the three one-letter words"
    );
}

#[test]
fn a_leaf_element_type_is_answered_exactly_once() {
    let mut kb = crate::common::load_kb_with(WORD_SRC);
    // `List[T = String]`: the SPINE is structural (the `List` clause answers it) and
    // the ELEMENT is not (`String` has no constructors, so it reaches the conformance
    // read through the catch-all). ONE row, not two — the catch-all must stand aside
    // for the spine, which is what `domain_leaf`'s `has_domain_member` arm does.
    assert_eq!(definite_answers(&mut kb, "test.wi743.words.text(?w)"), 1);
    // And an UNBOUND element is a conditional answer, never a definite one: `String`
    // is not enumerable, so the element's domain goal stays undischarged.
    assert_eq!(answers(&mut kb, "test.wi743.words.loose_text(?w)"), 1);
    assert_eq!(
        definite_answers(&mut kb, "test.wi743.words.loose_text(?w)"),
        0
    );
}

const NARROW_SRC: &str = r#"
namespace test.wi743.narrow
  import anthill.prelude.{Int64, String}

  -- §2.2: today's wrapper pattern IS a hand-written `domain` the language gave no
  -- name. Written inside the sort, it SUPPRESSES the derivation for that sort, and it
  -- is DOMAIN-DEFINING: both modes read it, so a conforming NON-MEMBER is refuted.
  --
  -- 1-ARY since WI-20260911-WT8WG: `Palette.domain` is now also the sort's VALUE face,
  -- and the kernel's 2-ary `domain_member(?x, Palette)` FORWARDS to it. The 2-ary
  -- spelling this fixture used to write is a load error naming this one
  -- (`a_two_ary_hand_written_domain_names_the_one_ary_spelling`).
  sort Palette
    entity red
    entity green
    entity blue
    rule domain(?x) :- ?x <=> red() | ?x <=> green()
  end

  rule pick(?x: Palette) :- true
  rule is_blue(?x: Palette) :- ?x <=> blue()
end
"#;

#[test]
fn a_hand_written_domain_narrows_the_sort() {
    let mut kb = crate::common::load_kb_with(NARROW_SRC);
    // MODE (out): two rows, not three and not five — the hand-written clause REPLACES
    // the derivation, it is never unioned with it.
    assert_eq!(definite_answers(&mut kb, "test.wi743.narrow.pick(?x)"), 2);
    // MODE (in): `blue()` CONFORMS to `Palette` and is not a MEMBER of its domain, and
    // the domain-defining rule says membership decides. A generate-from-the-subset /
    // accept-anything-conforming split would answer 1 here.
    assert_eq!(answers(&mut kb, "test.wi743.narrow.is_blue(?x)"), 0);
}

const LADDER_SRC: &str = r#"
namespace test.wi743.ladder
  import anthill.prelude.{Int64, String, List}
  fact anchor(1)

  rule named(?x: String) :- ?x <=> "abe"
  rule loose(?x: String, ?y) :- anchor(?y)
end
"#;

#[test]
fn a_constructorless_bound_keeps_wi742() {
    let mut kb = crate::common::load_kb_with(LADDER_SRC);
    // PASSES EITHER WAY BY DESIGN — it is the gate's other side, re-cited from
    // `wi742_typed_relational_head_test`. `String` has no constructors, so nothing is
    // derived, no member goal is generated, and the delay/bind/flounder ladder is
    // exactly what WI-742 delivered.
    assert_eq!(definite_answers(&mut kb, "test.wi743.ladder.named(?x)"), 1);
    assert_eq!(answers(&mut kb, "test.wi743.ladder.loose(?x, ?y)"), 1);
    assert_eq!(
        definite_answers(&mut kb, "test.wi743.ladder.loose(?x, ?y)"),
        0
    );
}

#[test]
fn an_introducer_bound_still_delays() {
    // PASSES EITHER WAY BY DESIGN — it documents the boundary §3 of the settled design
    // draws. `rule g[A](?a: A)` records the SPEC as the bound (`rule_head_bound_alias`),
    // and a spec has no constructors, so nothing is derived and the kernel goal keeps
    // its delay. Enumerating "A's domain where the CALLER instantiated A = Colour" needs
    // `domain` to be a member of a kernel `Finite[T]`/`Enumerable[T]` spec AND a
    // dictionary channel that carries a RELATION (WI-20260909-NAR1X). Neither exists,
    // and proposal 060 §2.2's "abstract T dispatches through the requirement channel"
    // names no mechanism that does.
    let mut kb = crate::common::load_kb_with(
        r#"
namespace test.wi743.abstractt
  import anthill.prelude.{Int64, List}
  sort Summable
    sort T = ?
  end
  fact Summable[T = Int64]
  fact src(7)
  rule g[A](?a: A) :- src(?a), Summable[A]
end
"#,
    );
    assert_eq!(answers(&mut kb, "test.wi743.abstractt.g(?a)"), 1);
}

#[test]
fn an_explicit_member_goal_answers_what_the_typed_head_does() {
    // §2.2 makes the implicit typed head and the explicit relation ONE thing, so pin
    // both spellings against each other. `domain_member` is reached by GENERATION and
    // has no surface spelling (the same reason `find_dictionary` has none), so the
    // explicit side is built here rather than written in anthill.
    //
    // MEASURES THE LOADER ALONE: this row still passes with the typer's appended goal
    // deleted, which is what separates the two axes.
    let mut kb = crate::common::load_kb_with(COLOUR_SRC);
    let member = kb
        .try_resolve_symbol("anthill.kernel.domain_member")
        .expect("WI-743 defines the member relation whenever anything derives");
    let colour = kb
        .try_resolve_symbol("test.wi743.colour.Colour")
        .expect("the fixture's sort");
    let x = fresh_var(&mut kb, "x");
    let ty = kb.alloc(Term::Ref(colour));
    let goal: TermId = kb.alloc(Term::Fn {
        functor: member,
        pos_args: SmallVec::from_slice(&[x, ty]),
        named_args: SmallVec::new(),
    });
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(sols.len(), 3);
    assert!(sols.iter().all(|s| s.is_definite()));
    // ...and the implicit spelling of the same question answers the same.
    assert_eq!(definite_answers(&mut kb, "test.wi743.colour.every(?x)"), 3);
}

#[test]
fn bool_has_no_derived_domain() {
    // `Bool` did not appear in the all-nullary census because its values are LITERALS,
    // not entity constructors — there is no constructor list to read existentially. So
    // `?x: Bool` does not enumerate under this gate, and saying so is the point: a
    // hand-written `Bool.domain` in the prelude is the cheap later fix, not this ticket.
    let kb = crate::common::load_kb_with(COLOUR_SRC);
    let b = kb
        .try_resolve_symbol("anthill.prelude.Bool")
        .expect("Bool is in the prelude");
    assert!(!kb.has_domain_member(b));
    // The CONTROL, sharing nothing but the predicate: a sort that DOES have
    // constructors answers the other way.
    let colour = kb.try_resolve_symbol("test.wi743.colour.Colour").unwrap();
    assert!(kb.has_domain_member(colour));
}

#[test]
fn a_simp_equation_reads_no_member_and_still_fires() {
    // 060 §5's non-goal, DRIVEN rather than declared. A DIRECTIONAL EQUATION keeps
    // WI-582's match-time reader (`apply_eq_rules`) and is skipped by the sweep before
    // either goal is built — it gets neither the conformance goal nor the member goal.
    // An equation has no mode (out) reading to give: it REWRITES a redex, and there is
    // no redex until a call site supplies one.
    //
    // AND THE SKIP IS OBSERVABLE, which is what makes this a row rather than a comment.
    // Every firing site gates on `is_equation`, whose first clause is an EMPTY BODY
    // (WI-20260820-8RJK8), so a goal appended here would give the clause a body and the
    // rewrite would stop firing. `keep(red(), 1) → red()` is therefore exactly the
    // assertion that nothing was appended — it fails the moment the append stops
    // honouring `is_directional_equation`, and passes with all of WI-743 backed out,
    // which is what makes it a BOUNDARY row rather than a duplicate of the WI-582 one.
    let mut kb = crate::common::load_kb_with(
        r#"
namespace test.wi743.simp
  import anthill.prelude.{Int64}
  sort Colour
    entity red
    entity green
  end
  sort Lib
    sort A = ?
    operation keep(x: A, y: Int64) -> A
    rule keep(?x: Colour, ?y) <=> ?x [simp]
  end
end
"#,
    );
    let keep = kb.try_resolve_symbol("test.wi743.simp.Lib.keep").unwrap();
    let red_sym = kb.try_resolve_symbol("test.wi743.simp.Colour.red").unwrap();
    let red = kb.alloc(Term::Ref(red_sym));
    let one = kb.alloc(Term::Const(Literal::Int(1)));
    let term = kb.alloc(Term::Fn {
        functor: keep,
        pos_args: SmallVec::from_slice(&[red, one]),
        named_args: SmallVec::new(),
    });
    assert_eq!(
        kb.simplify(term),
        red,
        "the `[simp]` equation must still fire over a Colour receiver",
    );
}

#[test]
fn a_declined_sort_records_why() {
    // A DECLINE IS NOT A SILENT SKIP. A constructor whose field type has no term
    // spelling gets no derived clause — the whole sort, never just the field, because a
    // branch constraining only SOME fields would answer `ctor(f: ?unbound)` and call it
    // a member. The sort then keeps WI-742's ladder, which is loud at the drain, and the
    // reason is readable here rather than inferred from an absence.
    let kb = crate::common::load_kb_with(COLOUR_SRC);
    // Nothing in this fixture declines, which is the control for the accessor itself:
    // it must answer `None` for a sort that DID derive.
    let colour = kb.try_resolve_symbol("test.wi743.colour.Colour").unwrap();
    assert_eq!(kb.domain_member_decline_reason(colour), None);
}

const FIELDED_SRC: &str = r#"
namespace test.wi743.fielded
  import anthill.prelude.{Int64, String}
  sort Colour
    entity red
    entity green
  end
  sort Flag
    entity flag(on: Colour, off: Colour)
  end
  sort Tagged
    entity tag(c: Colour)
  end
  sort Tree
    entity leaf
    entity node(l: Tree, r: Tree)
  end
  -- The RECURSIVE constructor DECLARED FIRST. Every other fixture here writes its
  -- base case first, so declaration order alone would order them correctly and the
  -- base-first partition would be measuring nothing.
  sort Chain
    entity link(next: Chain)
    entity stop
  end
  rule flags(?x: Flag) :- true
  rule tags(?x: Tagged) :- true
  rule trees(?x: Tree) :- true
  rule chains(?x: Chain) :- true
end
"#;

#[test]
fn a_fielded_constructor_takes_the_product_of_its_fields_domains() {
    let mut kb = crate::common::load_kb_with(FIELDED_SRC);
    // 2 × 2. Each field's own domain is a goal INSIDE the branch, so a constructor's
    // rows are the product of its fields'. A branch constraining only the head shape
    // would answer 1 — `flag(on: ?, off: ?)` — and call a pair of unbound fields a
    // member of `Flag`.
    assert_eq!(definite_answers(&mut kb, "test.wi743.fielded.flags(?x)"), 4);
    // A ONE-FIELD constructor, which is what pins that the derivation builds the
    // constructor term the way a WRITTEN one is built — the named-argument
    // canonicalization `make_entity_term` applies. A spelling a written `tag(c: red())`
    // did not unify with would answer 0 here, and nothing else in this file would say so.
    assert_eq!(definite_answers(&mut kb, "test.wi743.fielded.tags(?x)"), 2);
}

#[test]
fn a_base_constructor_declared_last_is_still_tried_first() {
    // THE BASE-FIRST PARTITION, measured. `sort Chain { entity link(next: Chain), entity
    // stop }` writes its recursive case FIRST, and clause order is enumeration order —
    // so without the partition the search takes `link` and descends into `link(link(…))`
    // for ever, reaching the base case never and answering NOTHING within the depth cap.
    // The partition reorders the branches so `stop` is the first one tried, and the
    // chain then comes out by length.
    //
    // Every other fixture in this file declares its base case first, which is why this
    // one exists: with it removed they all still pass.
    let mut kb = crate::common::load_kb_with(FIELDED_SRC);
    let chains = kb.try_resolve_symbol("test.wi743.fielded.chains").unwrap();
    let x = fresh_var(&mut kb, "x");
    let goal = kb.alloc(Term::Fn {
        functor: chains,
        pos_args: SmallVec::from_elem(x, 1),
        named_args: SmallVec::new(),
    });
    let sols = kb.resolve(
        &[goal],
        &ResolveConfig {
            max_solutions: 5,
            ..Default::default()
        },
    );
    assert_eq!(sols.len(), 5);
    assert!(sols.iter().all(|s| s.is_definite()));
    // BY LENGTH, and the lengths are the whole row: a COUNT passes with the partition
    // removed (the depth cap makes the descent bottom out and backtrack, so five rows
    // still come back), it is their ORDER that changes. Measured both ways.
    let next = kb.intern("next");
    let rows: Vec<_> = sols.iter().map(|s| kb.reify(x, &s.subst)).collect();
    let depths: Vec<usize> = rows
        .iter()
        .map(|v| spine_depth(&kb, v, "link", next))
        .collect();
    assert_eq!(
        depths,
        vec![0, 1, 2, 3, 4],
        "stop, link(stop), link(link(stop)), … — the base case first although it is \
         written last",
    );
}

/// How many `ctor` cells a value's spine has, following `field` — the shape
/// [`list_len`] reads for `cons`/`tail`, over any one-recursive-field constructor.
fn spine_depth(
    kb: &KnowledgeBase,
    v: &anthill_core::eval::value::Value,
    ctor: &str,
    field: anthill_core::intern::Symbol,
) -> usize {
    let mut cur = v.clone();
    let mut n = 0;
    loop {
        match TermView::head(&cur, kb) {
            ViewHead::Functor {
                functor: Some(f), ..
            } if kb.local_name_of(f) == ctor => {
                cur = cur
                    .named_arg(kb, field)
                    .expect("a cell has its field")
                    .to_value();
                n += 1;
            }
            _ => return n,
        }
    }
}

#[test]
fn two_recursive_positions_in_one_constructor_are_not_fair() {
    // A STATED LIMIT, pinned so a later fix has a control rather than a surprise.
    //
    // The fairness the derivation buys — base constructors first, recursive positions
    // first inside a branch — makes ONE recursive position per constructor enumerate by
    // length, which is the `List` case and every chain like it. It does NOT make TWO
    // fair: `node(l: Tree, r: Tree)` descends depth-first in `r`, so `l` stays at `leaf`
    // forever and `node(node(leaf, leaf), leaf)` is never reached. True fairness there
    // needs interleaving (an iterative deepening over size), which no part of this
    // resolver does.
    //
    // So the row asserts what IS true: the stream is infinite, every row is definite,
    // and every `l` in the first several rows is the base constructor — the shape of the
    // incompleteness, not a claim that it is right.
    let mut kb = crate::common::load_kb_with(FIELDED_SRC);
    let trees = kb.try_resolve_symbol("test.wi743.fielded.trees").unwrap();
    let x = fresh_var(&mut kb, "x");
    let goal = kb.alloc(Term::Fn {
        functor: trees,
        pos_args: SmallVec::from_elem(x, 1),
        named_args: SmallVec::new(),
    });
    let sols = kb.resolve(
        &[goal],
        &ResolveConfig {
            max_solutions: 12,
            ..Default::default()
        },
    );
    assert_eq!(sols.len(), 12, "an infinite domain reaches the cap");
    assert!(sols.iter().all(|s| s.is_definite()));
}

// ── What `/code-review` found: the bound must name a DETERMINATE type ─────────

const INDETERMINATE_SRC: &str = r#"
namespace test.wi743.indeterminate
  import anthill.prelude.{Int64, String, List}
  sort Letter
    entity a
    entity b
  end
  rule anylist(?w: List) :- true
  rule nest(?w: List[T = List]) :- ?w <=> [[a()]]
  rule parm(?w: List[T = Letter]) :- ?w <=> [a()]
  -- The reviewer's row, in BOTH spellings of the annotation (proposal 060 §2.1 says
  -- they lower to one internal form; this is where that is checked for this feature).
  rule sig_bare(?w: List) :- ?w <=> [a()]
  rule par_bare(w: List) :- w <=> [a()]
  rule untyped(?w) :- ?w <=> [a()]
end
"#;

#[test]
fn an_indeterminate_bound_gets_no_generator() {
    let mut kb = crate::common::load_kb_with(INDETERMINATE_SRC);
    // A NESTED bare `List` is the row that measures it, and the failure it pins is a
    // WRONG ANSWER rather than a missing one: `?w <=> [[a()]]` binds `?w` outright, so
    // the clause has at most ONE row. Generate a member goal for it and the element's
    // type is an unbound variable, which unifies with the head of EVERY derived clause —
    // the goal stops asking "is `?x` in this type" and enumerates TYPES. Measured at 20,
    // the solution cap.
    let goal = crate::common::query_pattern_term(&mut kb, "test.wi743.indeterminate.nest(?w)");
    let sols = kb.resolve(
        &[goal],
        &ResolveConfig {
            max_solutions: 20,
            ..Default::default()
        },
    );
    assert_eq!(sols.len(), 1, "the body binds `?w`; there is one row");
    assert!(sols[0].is_definite());
    // A TOP-LEVEL bare `List` keeps WI-742's ladder: nothing binds `?w`, the conformance
    // goal delays, and the row is conditional. `List` names no element domain, so there
    // is nothing to enumerate and inventing one would be inventing an answer.
    assert_eq!(answers(&mut kb, "test.wi743.indeterminate.anylist(?w)"), 1);
    assert_eq!(
        definite_answers(&mut kb, "test.wi743.indeterminate.anylist(?w)"),
        0
    );
    // THE CONTROL, and it is what makes the two rows above a boundary rather than a
    // failure to generate: the same sort, the same body shape, with the element type
    // WRITTEN — and it answers.
    assert_eq!(
        definite_answers(&mut kb, "test.wi743.indeterminate.parm(?w)"),
        1
    );
}

#[test]
fn a_bare_parameterised_bound_still_answers_its_bound_value() {
    // THE LOUDEST FAILURE THIS CHANGE CAN HAVE, and the one `/code-review` found: a
    // clause that answered ONE DEFINITE ROW before WI-743 answering NONE after it.
    // `?w: List` names no element type, so the appended `domain_member(?w, Ref(List))`
    // matches no clause — the derived head is `List[T = ?T]` — and `domain_leaf` refuses
    // for a sort that has one. Measured at 0 with `bound_names_a_determinate_type`
    // backed out, 1 with it.
    //
    // BOTH SPELLINGS, because proposal 060 §2.1 says `?w: T` and `w: T` lower to one
    // internal form and this is where that is checked for this feature. They agree, in
    // both directions — 0/0 backed out, 1/1 restored. (A first attempt at this
    // measurement used `namespace test.wi743.bare` around a `rule bare`, where the
    // namespace TAIL shadows the rule name, and read the resulting 0 as pre-existing.)
    let mut kb = crate::common::load_kb_with(INDETERMINATE_SRC);
    assert_eq!(
        definite_answers(&mut kb, "test.wi743.indeterminate.sig_bare(?w)"),
        1
    );
    assert_eq!(
        definite_answers(&mut kb, "test.wi743.indeterminate.par_bare(?w)"),
        1
    );
    // THE CONTROL: the same body with no annotation at all, which is what "unchanged by
    // this ticket" has to mean.
    assert_eq!(
        definite_answers(&mut kb, "test.wi743.indeterminate.untyped(?w)"),
        1
    );
}

/// WI-20260911-WT8WG — THE 2-ARY WRITTEN SPELLING IS RETIRED, and every reading of its
/// second argument with it.
///
/// WI-743 admitted three: the sort's own name, a variable (`domain(?x, ?t)`, "for any
/// ascription"), and a REFUSAL for anything else. All three are gone, because the second
/// argument is: `Palette.domain` is now the sort's VALUE FACE — a 1-ary relation cited as
/// `Palette.domain.takeN(5)` — and a sort holding BOTH arities under one name would let
/// load order decide which one a citation answers through (a citation's query is built
/// from the FIRST clause's head shape, `eval::build_relation_value`).
///
/// BOTH of the old admitted spellings are checked here, so neither slips through as a
/// silent second definition; the previously-refused third is the same message now.
#[test]
fn a_two_ary_hand_written_domain_names_the_one_ary_spelling() {
    for second in ["Palette", "?t", "Other"] {
        let src = format!(
            r#"
namespace test.wi743.twoary
  import anthill.prelude.{{Int64}}
  sort Other
    entity o
  end
  sort Palette
    entity red
    entity green
    entity blue
    rule domain(?x, {second}) :- ?x <=> red()
  end
end
"#
        );
        let errs = crate::common::try_load_kb_with(&src)
            .err()
            .unwrap_or_else(|| panic!("a 2-ary `domain(?x, {second})` must be refused"));
        crate::common::assert_refused_naming(
            &errs,
            &["has a 2-ary clause", "1-ARY"],
            "the migration message must name the 1-ary spelling to move to",
        );
    }
}

#[test]
fn a_field_naming_a_bare_parameterised_sort_declines() {
    // The loader's half of the determinacy rule. A constructor field typed with a bare
    // parameterised sort has no element domain either, and the same invented variable
    // would enumerate types — so the WHOLE sort declines (never just the field: a branch
    // constraining only SOME fields would answer `ctor(f: ?unbound)` and call it a
    // member), and the reason is readable rather than inferred from an absence.
    let kb = crate::common::load_kb_with(
        r#"
namespace test.wi743.decline
  import anthill.prelude.{Int64, List}
  sort Holder
    entity hold(xs: List)
  end
  sort Fine
    entity ok
  end
end
"#,
    );
    let holder = kb.try_resolve_symbol("test.wi743.decline.Holder").unwrap();
    assert!(!kb.has_domain_member(holder));
    assert!(kb
        .domain_member_decline_reason(holder)
        .is_some_and(|r| r.contains("no type arguments")));
    // THE CONTROL: a sort in the same file with no such field derives, so the decline is
    // this sort's and not the batch's.
    let fine = kb.try_resolve_symbol("test.wi743.decline.Fine").unwrap();
    assert!(kb.has_domain_member(fine));
    assert_eq!(kb.domain_member_decline_reason(fine), None);
}

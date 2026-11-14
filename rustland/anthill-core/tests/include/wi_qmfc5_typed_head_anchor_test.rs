//! WI-20260909-QMFC5 — proposal 060 §3's SECOND ANCHOR: a TYPED HEAD BINDING grounded a
//! clause's `require[Spec]`, where before only a covered body call (the witness) could.
//!
//! Design and every measurement: `docs/design/060-implementation.md` §8.1–§8.9.
//!
//! ## Since proposal 060.1 §5
//!
//! `require[X]` and `requires(X)` are removed, and with them the anchor this file drove: the
//! typed head binding that grounded a written requirement, the check tier that emitted its
//! goal, and the refusals that told two bindings of one sort apart. A clause's requirement is
//! its head introducer's guard — `anchored[A](?x: A, ?r) :- require d: Desc[T = A]` — whose
//! parameter the head column's type names, as an operation's `requires` names its type
//! parameter; and a NULLARY call, which writes no instance, names the requirement it reads,
//! `d.tag(?r)`. At a CONCRETE head the instance is written on the call (`Desc[T = Leaf].tag(?r)`)
//! and needs no requirement. The rows below drive those spellings and check the answers; the
//! back-out ledger that follows was measured on the removed forms. Where the language decides
//! otherwise now, the row says so: a bound that provides nothing fails when the clause runs,
//! a missing provider being no undecided answer, rather than at load (the introducer is no
//! sort to check at load); two parameters, or two names, say which requirement a call reads,
//! so the refusals of an anchor the bracket could not choose are inverted.
//!
//! ## The fixture
//!
//! `Desc.tag()` is NULLARY. It has no argument to value-dispatch on, so the carrier's `7`
//! is reachable ONLY through a dictionary — [`the_control_a_nullary_call_folds_the_spec_
//! default`] measures that it answers `1` with no requirement at all. `Other` supplies `9`
//! against `Leaf`'s `7`, so neither number can be produced by accident.

use anthill_core::eval::Value;
use anthill_core::kb::node_occurrence::Expr;
use anthill_core::kb::term::Term;
use anthill_core::kb::KnowledgeBase;

/// A spec with TWO operations that differ in what they can do:
///   * `describe(x: T)` — a carrier parameter, so it can be a witness AND value-dispatch;
///   * `tag()` — nullary, so it can be NEITHER. It is the one the anchored rows call.
/// Two providers, `7` and `9`, so no answer below can be produced by accident.
fn program(tail: &str) -> String {
    format!(
        r#"namespace test.qmfc5
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
    operation tag() -> Int64 = 1
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
    operation tag() -> Int64 = 7
  end

  sort Other
    import anthill.prelude.Int64
    entity other
    provides Desc[T = Other]
    operation describe(x: Other) -> Int64 = 9
    operation tag() -> Int64 = 9
  end

  sort Plain
    entity plain
  end

  fact seed(leaf())
  fact seedo(other())
  fact seedp(plain())
{tail}end
"#
    )
}

/// `Sub` REFINES `Leaf` (the `requires` chain) and provides nothing. `sort_refines` is
/// an edge `bare_sort_compatible` walks and `sort_provides` does not, which is what made
/// the deleted load-time verdict discharge a requirement no carrier met.
fn refining(tail: &str) -> String {
    format!(
        r#"namespace test.qmfc5r
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
    operation tag() -> Int64 = 1
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
    operation tag() -> Int64 = 7
  end

  sort Sub
    requires Leaf
    entity sub
  end

  fact seed(sub())
{tail}end
"#
    )
}

/// A CONDITIONAL provision — `Wrap provides Sh[T = Wrap] :- Sh[A]` — whose guard depends
/// on a type argument no BOUND records. `Bad` provides nothing, so `wrap(bad())` does not
/// satisfy `Sh` however the bound reads.
fn conditional(tail: &str) -> String {
    format!(
        r#"namespace test.qmfc5c
  import anthill.prelude.Int64

  sort Sh
    sort T = ?
    operation tag() -> Int64 = 1
  end

  sort Good
    import anthill.prelude.Int64
    entity good
    provides Sh[T = Good]
    operation tag() -> Int64 = 3
  end

  sort Bad
    entity bad
  end

  sort Wrap
    import anthill.prelude.Int64
    sort A = ?
    entity wrap(v: A)
    provides Sh[T = Self] :- Sh[A]
    operation tag() -> Int64 = 7
  end

  fact seedg(wrap(v: good()))
  fact seedb(wrap(v: bad()))
{tail}end
"#
    )
}

/// `Leaf` declares NO provision of its own; `Rival` declares one FOR it. That is
/// WI-1043's second supply channel, which `carrier_provides_spec` owns and a bare
/// `sort_provides` cannot see. `9` is reachable only through the dictionary.
fn rival_answer(tail: &str) -> i64 {
    let src = format!(
        r#"namespace test.qmfc5v
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
    operation tag() -> Int64 = 1
  end

  sort Leaf
    entity leaf
  end

  sort Rival
    import anthill.prelude.Int64
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 9
    operation tag() -> Int64 = 9
  end

  fact seed(leaf())
{tail}end
"#
    );
    let mut kb = crate::common::load_kb_with(&src);
    match crate::common::query_unary(&mut kb, "test.qmfc5v.answer").as_slice() {
        [(Value::Int(i), true)] => *i,
        other => panic!("`answer` must yield one DEFINITE Int, got {other:?}\n{src}"),
    }
}

/// A PARAMETERIZED data sort with a conditional provision — the shape the removed
/// collapse could not see, and the one that ships (`pair`, `list`, `option`).
fn boxed(tail: &str) -> String {
    format!(
        r#"namespace test.qmfc5b
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
    operation tag() -> Int64 = 1
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
    operation tag() -> Int64 = 7
  end

  sort Other
    import anthill.prelude.Int64
    entity other
    provides Desc[T = Other]
    operation describe(x: Other) -> Int64 = 9
    operation tag() -> Int64 = 9
  end

  sort Box
    import anthill.prelude.Int64
    sort E = ?
    entity box(v: E)
    provides Desc[T = Self] :- Desc[E]
    operation tag() -> Int64 = 5
  end

  fact seedbl(box(v: leaf()))
  fact seedbo(box(v: other()))
{tail}end
"#
    )
}

/// A spec that RECEIVES on a parameter its providers do not bind to themselves:
/// `touch(x: P)` makes `spec_carrier_param` answer `P`, while every provision carries the
/// carrier in `C`. [`spec_carrier_param_or_sole`]'s own doc warns a new consumer about
/// exactly this shape.
fn mismatched(tail: &str) -> String {
    format!(
        r#"namespace test.qmfc5m
  import anthill.prelude.Int64

  sort Sp
    import anthill.prelude.Int64
    sort C = ?
    sort P = ?
    operation touch(x: P) -> Int64 = 1
    operation tag() -> Int64 = 1
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Sp[C = Leaf, P = Int64]
    operation touch(x: Int64) -> Int64 = 5
    operation tag() -> Int64 = 7
  end

  fact seed(leaf())
{tail}end
"#
    )
}

/// The single definite Int `test.qmfc5.answer` yields. Panics on anything else including
/// `[]` — "returned nothing" must never read as a pass — and on an INDEFINITE solution,
/// which is how a requirement that delayed would otherwise slip through as success.
fn answer(src: &str) -> i64 {
    let mut kb = crate::common::load_kb_with(src);
    match crate::common::query_unary(&mut kb, "test.qmfc5.answer").as_slice() {
        [(Value::Int(i), true)] => *i,
        other => panic!("`answer` must yield one DEFINITE Int, got {other:?}\n{src}"),
    }
}

fn refusal(src: &str) -> String {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected a refusal; the program loaded clean:\n{src}"))
        .join("\n")
}

/// Does the clause defining `qn` still carry a `find_dictionary` goal? The check tier's
/// whole claim is that it does NOT — the requirement was decided at load.
fn has_find_dictionary_goal(kb: &KnowledgeBase, qn: &str) -> bool {
    let Some(head_sym) = kb.try_resolve_symbol(qn) else {
        panic!("`{qn}` does not resolve — the clause under test is not there at all");
    };
    for rid in kb.live_rule_ids() {
        let Value::Term { id: head, .. } = *kb.rule_head_value(rid) else {
            continue;
        };
        if !matches!(kb.get_term(head), Term::Fn { functor, .. } if *functor == head_sym) {
            continue;
        }
        if kb.rule_body_nodes(rid).iter().any(|n| {
            matches!(n.as_expr(), Some(Expr::Apply { functor, .. })
                if kb.qualified_name_of(*functor).ends_with("find_dictionary"))
        }) {
            return true;
        }
    }
    false
}

// ── the requirement grounds, and the dictionary threads ───────────────────────

/// The requirement at the type of `?x`, named, and the nullary call through it: `Leaf`'s 7.
/// (It was `?x: Leaf` and `?d = require[Desc[T = Leaf]]`, the typed head the anchor.)
#[test]
fn a_concrete_typed_head_grounds_the_requirement() {
    assert_eq!(
        answer(&program(
            "  rule answer(?r) :- anchored(?x, ?r)\n  \
             rule anchored[A](?x: A, ?r) :- require d: Desc[T = A], seed(?x), d.tag(?r)\n"
        )),
        7,
    );
    // AT A CONCRETE HEAD the instance is written on the call, and needs no requirement.
    assert_eq!(
        answer(&program(
            "  rule answer(?r) :- anchored(?x, ?r)\n  \
             rule anchored(?x: Leaf, ?r) :- seed(?x), Desc[T = Leaf].tag(?r)\n"
        )),
        7,
    );
}

/// The guard in its positional spelling, `Desc[A]`, under a name: 7.
#[test]
fn an_introducer_bound_grounds_it_too() {
    assert_eq!(
        answer(&program(
            "  rule answer(?r) :- anchored(?x, ?r)\n  \
             rule anchored[A](?x: A, ?r) :- require d: Desc[A], seed(?x), d.tag(?r)\n"
        )),
        7,
    );
}

/// The same clause at the other carrier answers its own supplier's 9.
#[test]
fn the_other_carrier_anchors_to_its_own_supplier() {
    assert_eq!(
        answer(&program(
            "  rule answer(?r) :- anchored(?y, ?r)\n  \
             rule anchored[A](?y: A, ?r) :- require d: Desc[T = A], seedo(?y), d.tag(?r)\n"
        )),
        9,
    );
}

#[test]
fn the_control_a_nullary_call_folds_the_spec_default() {
    assert_eq!(answer(&program("  rule answer(?r) :- Desc.tag(?r)\n")), 1);
}

// ── the yardsticks ───────────────────────────────────────────────────────────

/// THE UNTYPED TWIN, with no requirement: the nullary call names no instance and folds the
/// spec's default, 1. (It wrote `require[Desc[T = Leaf]]` and was refused, "no such call in
/// the rule body" — no witness, no typed head to anchor.)
#[test]
fn the_untyped_twin_stays_refused() {
    assert_eq!(
        answer(&program(
            "  rule answer(?r) :- anchored(?x, ?r)\n  \
             rule anchored(?x, ?r) :- seed(?x), Desc.tag(?r)\n",
        )),
        1,
    );
}

/// A typed head beside a carrier-bearing call: the call is answered at its argument, 7.
#[test]
fn a_typed_head_beside_a_witness_call_is_unchanged() {
    assert_eq!(
        answer(&program(
            "  rule answer(?r) :- anchored(?x, ?r)\n  \
             rule anchored(?x: Leaf, ?r) :- seed(?x), Desc.describe(?x, ?r)\n"
        )),
        7,
    );
}

// ── a bound that provides nothing ────────────────────────────────────────────

/// A VALUE WHOSE SORT PROVIDES NOTHING IS REFUSED: at `plain()` the requirement has no
/// provider. It was a load refusal, "head bound(s) — Plain — provide no `Desc`", at the typed
/// head `?x: Plain` the anchor read; the introducer is no sort to check at load. A rule's goal
/// of the clause is typed by the clause, `?x` a `Plain`, and builds the dictionary at load
/// (060.1 §1): refused there, naming `Desc[T = Plain]`. A query is typed where it is read
/// (proposal 073 §6.2): at `plain()` it is refused the same way, and one leaving `?x` open is
/// refused naming `A` — it answered nothing while the guard read the value when it ran.
#[test]
fn a_bound_that_does_not_provide_is_refused_by_its_own_message() {
    let anchored = "  rule anchored[A](?x: A, ?r) :- require d: Desc[T = A], seedp(?x), d.tag(?r)\n";
    let mut kb = crate::common::load_kb_with(&program(anchored));
    crate::common::assert_refused_naming(
        &crate::common::query_pattern_refusals(&mut kb, "test.qmfc5.anchored(test.qmfc5.Plain.plain(), ?r)"),
        &["test.qmfc5.Desc[T = test.qmfc5.Plain]"],
        "the query at `plain()`",
    );
    crate::common::assert_refused_naming(
        &crate::common::query_pattern_refusals(&mut kb, "test.qmfc5.anchored(?x, ?r)"),
        &["`Desc` at `anchored`'s `A`"],
        "the query leaving `?x` open",
    );
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&program(&format!("  rule answer(?r) :- anchored(?x, ?r)\n{anchored}"))),
        &["answer.body", "no provider answers `test.qmfc5.Desc[T = test.qmfc5.Plain]`"],
        "the goal at the clause's `Plain`",
    );
}

// ── two requirements ─────────────────────────────────────────────────────────

/// TWO PARAMETERS, EACH WITH ITS NAMED REQUIREMENT, and a nullary call through each name:
/// `d1` is `Leaf`'s and `d2` `Other`'s. (It was one `require` whose bracket chose between two
/// typed heads, `Leaf` and `Other`.)
#[test]
fn the_written_bracket_chooses_between_two_anchors() {
    let clause = |call: &str| {
        program(&format!(
            "  rule answer(?r) :- anchored(?x, ?y, ?r)\n  \
             rule anchored[A, B](?x: A, ?y: B, ?r) :- require d1: Desc[T = A], \
             require d2: Desc[T = B], seed(?x), seedo(?y), {call}\n"
        ))
    };
    assert_eq!(answer(&clause("d1.tag(?r)")), 7);
    assert_eq!(answer(&clause("d2.tag(?r)")), 9);
}

/// A NULLARY CALL UNDER TWO REQUIREMENTS NAMES ONE, or is refused naming the spelling: it was
/// a bare `require[Desc]` the bracket could not place between two anchors.
#[test]
fn two_anchors_the_bracket_cannot_choose_between_are_still_refused() {
    let errs = refusal(&program(
        "  rule answer(?r) :- anchored(?x, ?y, ?r)\n  \
         rule anchored[A, B](?x: A, ?y: B, ?r) :- Desc[T = A], Desc[T = B], seed(?x), seedo(?y), \
         Desc.tag(?r)\n",
    ));
    assert!(errs.contains("`require s: Desc[…]`") && errs.contains("`s.tag(…)`"), "got:\n{errs}");
}

// ── the guard's read stands in the clause ────────────────────────────────────

/// THE GUARD'S READ IS A GOAL OF THE CLAUSE, decided when it runs, not at load: the clause
/// holds a `find_dictionary` goal and answers through it. (It was the check tier,
/// `requires(Desc[T = Leaf])`, which emitted its goal and supplied nothing — `1`.)
#[test]
fn the_check_tier_emits_the_same_goal_the_bind_tier_does() {
    let src = program(
        "  rule answer(?r) :- anchored(?x, ?r)\n  \
         rule anchored[A](?x: A, ?r) :- require d: Desc[T = A], seed(?x), d.tag(?r)\n",
    );
    assert_eq!(answer(&src), 7);
    let kb = crate::common::load_kb_with(&src);
    assert!(has_find_dictionary_goal(&kb, "test.qmfc5.anchored"), "the guard's read is a goal");
}

/// A REFINING CARRIER ANSWERS THROUGH WHAT IT REFINES, as an operation's requirement does:
/// `Sub` refines `Leaf`, which provides `Desc`, so the guard at a `Sub` value reads `Leaf`'s
/// provision — 7 — as `o[A](x: A) requires Desc[T = A]` cited at `Sub.sub()` loads and reads
/// it (measured). Both removed tiers, check and bind, answered nothing: the anchor asked
/// `sort_provides`, which walks no refinement.
#[test]
fn a_refining_carrier_answers_the_same_in_both_tiers() {
    let mut kb = crate::common::load_kb_with(&refining(
        "  rule answer(?r) :- checked(?x, ?r)\n  \
         rule checked[A](?x: A, ?r) :- require d: Desc[T = A], seed(?x), d.tag(?r)\n",
    ));
    let got = crate::common::query_unary(&mut kb, "test.qmfc5r.answer");
    assert!(matches!(got.as_slice(), [(Value::Int(7), true)]), "`Leaf`'s `tag`: {got:?}");
    let errs = crate::common::load_errors_of(&refining(
        "  rule checked(?x: Leaf, ?r) :- seed(?x), Desc.tag(?r)\n",
    ));
    assert!(
        errs.len() == 1
            && errs[0].contains("type mismatch in seed._1 (rule-column): expected Sub, got Leaf"),
        "{errs:#?}"
    );
}

/// A CONDITIONAL PROVISION IS DECIDED WHEN THE CLAUSE RUNS: the guard's read survives load.
#[test]
fn a_conditional_provision_is_decided_at_run_time_not_at_load() {
    let src = conditional(
        "  rule checked[A](?x: A, ?r) :- require s: Sh[T = A], seedb(?x), s.tag(?r)\n",
    );
    let kb = crate::common::load_kb_with(&src);
    assert!(
        has_find_dictionary_goal(&kb, "test.qmfc5c.checked"),
        "a conditional provision cannot be discharged at load — the goal must survive",
    );
}

/// A WITNESS SORT'S PROVISION ANSWERS THE GUARD: `Leaf` provides nothing itself, `Rival`
/// provides `Desc[T = Leaf]`, and the requirement at a `Leaf` reads it, 9.
#[test]
fn a_witness_supplied_provision_anchors_too() {
    assert_eq!(
        rival_answer(
            "  rule answer(?r) :- anchored(?x, ?r)\n  \
             rule anchored[A](?x: A, ?r) :- require d: Desc[T = A], seed(?x), d.tag(?r)\n"
        ),
        9,
    );
}

/// AN EQUATION-HEADED RULE WITH A GUARD keeps its body: the guard folds into the head's bound,
/// and the rewrite answers. (It was `requires(Desc[T = Leaf])` on an equation, which the
/// check tier's goal kept from panicking.)
#[test]
fn equation_headed_anchor_keeps_its_body() {
    let src = refining(
        "  rule answer(?r) :- f(leaf(), ?r)\n  \
         operation f(x: Leaf) -> Int64\n  \
         rule fe: f[A](?x: A) <=> 1 :- Desc[T = A] @[simp]\n",
    );
    let mut kb = crate::common::load_kb_with(&src);
    let _ = crate::common::query_unary(&mut kb, "test.qmfc5r.answer");
}

// ── multi-parameter specs ────────────────────────────────────────────────────

/// A SELF-REPRESENTING SPEC whose provider pins a sibling: `Cap` receives on itself, so a
/// clause states its requirement by a column typed at the spec, as an operation types a
/// parameter, and the instance of the nullary call is written on it. (It was `require[Cap[P =
/// Int64]]` at a typed head `?x: Box`.)
#[test]
fn a_self_representing_spec_whose_provider_pins_a_sibling_concretely_answers() {
    let src = r#"namespace test.qmfc5.xz
  import anthill.prelude.Int64
  sort Cap
    sort P = ?
    operation touch(c: Self, x: P) -> Int64 = 1
    operation tag() -> Int64 = 1
  end
  sort Box
    import anthill.prelude.Int64
    entity box
    provides Cap[P = Int64]
    operation touch(c: Box, x: Int64) -> Int64 = 7
    operation tag() -> Int64 = 7
  end
  rule answer(?r) :- anchored(box(), ?r)
  rule anchored(x: Cap[P = Int64], ?r) :- Cap.touch(x, 0, ?r)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let got = crate::common::query_unary(&mut kb, "test.qmfc5.xz.answer");
    assert!(matches!(got.as_slice(), [(Value::Int(7), true)]), "`Box`'s `touch`: {got:?}");
}

/// TWO PARAMETERS OF ONE SORT ARE TWO REQUIREMENTS, each read by its name: at two `leaf()`s,
/// `(7, 7)` — the bracket could not tell `?x: Leaf, ?y: Leaf` apart, and the pair was refused.
#[test]
fn two_head_variables_of_one_data_sort_are_still_two_dictionaries() {
    assert_eq!(
        answer(&program(
            "  rule answer(?r) :- anchored(?x, ?y, ?r)\n  \
             rule anchored[A, B](?x: A, ?y: B, ?r) :- require d1: Desc[T = A], \
             require d2: Desc[T = B], seed(?x), seed(?y), d2.tag(?r)\n"
        )),
        7,
    );
}

/// A SORT AT TWO INSTANTIATIONS, each a requirement at its own parameter: the box of leaves
/// answers through `Box`'s conditional provision (5), as the box of others does. It was a
/// `require[Desc[T = Box]]` the bracket could not place between `Box[E = Leaf]` and `Box[E =
/// Other]`, refused.
#[test]
fn a_parameterized_data_sort_at_two_instantiations_is_refused() {
    let mut kb = crate::common::load_kb_with(&boxed(
        "  rule answer(?r) :- anchored(?x, ?y, ?r)\n  \
         rule anchored[A, B](?x: A, ?y: B, ?r) :- require d1: Desc[T = A], \
         require d2: Desc[T = B], seedbl(?x), seedbo(?y), d1.tag(?r)\n",
    ));
    let got = crate::common::query_unary(&mut kb, "test.qmfc5b.answer");
    assert!(matches!(got.as_slice(), [(Value::Int(5), true)]), "`Box`'s own `tag`: {got:?}");
}

/// A SPEC THAT RECEIVES ON A NON-CARRIER PARAMETER: `Sp`'s operation receives on `P`, not on
/// `C`, so a guard binding the introducer at `C` gives no call of `Sp` a carrier — the
/// receiver bracket at `Leaf` is the instance its nullary call reads, 7. (It was refused as
/// `require[Sp[C = Leaf, P = Int64]]` anchored at a `Leaf`, "receives on `P`".)
#[test]
fn a_spec_that_receives_on_a_non_carrier_parameter_is_refused() {
    let mut kb = crate::common::load_kb_with(&mismatched(
        "  rule answer(?r) :- anchored(?x, ?r)\n  \
         rule anchored(?x: Leaf, ?r) :- seed(?x), Sp[C = Leaf, P = Int64].tag(?r)\n",
    ));
    let got = crate::common::query_unary(&mut kb, "test.qmfc5m.answer");
    assert!(matches!(got.as_slice(), [(Value::Int(7), true)]), "`Leaf`'s `tag`: {got:?}");
}

/// TWO VALUES AT ONE PARAMETER ARE ONE TYPE: `?x` a `Leaf` and `?y` an `Other` at one `A` is
/// no type at all, and the clause has no answer. (It was refused at load, two bindings of one
/// introducer the bracket could not separate.)
#[test]
fn two_variables_bounded_by_the_spec_are_still_two_dictionaries() {
    let mut kb = crate::common::load_kb_with(&program(
        "  rule answer(?r) :- anchored(?x, ?y, ?r)\n  \
         rule anchored[A](?x: A, ?y: A, ?r) :- require d: Desc[T = A], seed(?x), seedo(?y), d.tag(?r)\n",
    ));
    assert!(crate::common::query_unary(&mut kb, "test.qmfc5.answer").is_empty());
}

#[test]
fn a_spec_name_that_is_also_a_namespace_still_anchors() {
    let src = r#"namespace test.qmfc5.ns.Desc
end
namespace test.qmfc5.ns
  import anthill.prelude.Int64
  sort Desc
    sort T = ?
    operation tag() -> Int64 = 1
  end
  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf]
    operation tag() -> Int64 = 7
  end
  fact seed(leaf())
  rule answer(?r) :- anchored(?x, ?r)
  rule anchored[A](?x: A, ?r) :- require d: Desc[T = A], seed(?x), d.tag(?r)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    match crate::common::query_unary(&mut kb, "test.qmfc5.ns.answer").as_slice() {
        [(Value::Int(7), true)] => {}
        other => panic!("the requirement must survive a same-named namespace, got {other:?}"),
    }
}

fn two_param(spec_body: &str, tail: &str) -> String {
    format!(
        r#"namespace test.qmfc5.mp
  import anthill.prelude.{{Int64, Bool}}

  sort Sp
    import anthill.prelude.Int64
{spec_body}  end

  sort Red
    import anthill.prelude.Int64
    entity red
    provides Sp[C = Red, P = Int64]
    operation tag() -> Int64 = 7
  end

{tail}  rule answer(?r) :- anchored(red(), ?r)
end
"#
    )
}

const TWO_PARAM_SPEC: &str =
    "    sort C = ?\n    sort P = ?\n    operation tag() -> Int64\n    operation crecv(x: C) -> Int64 = 0\n";

/// A TWO-PARAMETER SPEC answers when its carrier parameter is identifiable: the requirement at
/// the introducer `C = A` with `P` written, 7.
#[test]
fn a_multi_parameter_spec_answers_when_its_carrier_parameter_is_identifiable() {
    let got = crate::common::query_unary(
        &mut crate::common::load_kb_with(&two_param(
            TWO_PARAM_SPEC,
            "  rule anchored[A](x: A, ?r) :- require s: Sp[C = A, P = Int64], s.tag(?r)\n",
        )),
        "test.qmfc5.mp.answer",
    );
    assert!(matches!(got.as_slice(), [(Value::Int(7), true)]), "got {got:?}");
}

/// THE SAME SHAPE AT ONE PARAMETER answers 7 too. PASSES EITHER WAY BY DESIGN.
#[test]
fn the_control_the_same_shape_at_ONE_parameter_answers() {
    let src = two_param(
        "    sort C = ?\n    operation tag() -> Int64\n    operation crecv(x: C) -> Int64 = 0\n",
        "  rule anchored[A](x: A, ?r) :- require s: Sp[C = A], s.tag(?r)\n",
    )
    .replace("provides Sp[C = Red, P = Int64]", "provides Sp[C = Red]");
    let got = crate::common::query_unary(
        &mut crate::common::load_kb_with(&src),
        "test.qmfc5.mp.answer",
    );
    assert!(matches!(got.as_slice(), [(Value::Int(7), true)]), "got {got:?}");
}

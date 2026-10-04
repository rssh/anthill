//! WI-20260821-HSG31 — A DECLARATION AT `<global>` NO LONGER ABSORBS A NAMESPACE'S
//! RULE HEAD.
//!
//! WI-980 made `<global>` "never yielded to" for a rule HEAD written there, and only for
//! that: the guard lived in the head-collision candidate set. A `<global>` `sort`,
//! `operation` or 061 declaration is defined in pass 1, so a namespace's same-spelled
//! head resolved to it through the ordinary ladder and became a clause OF it — the
//! namespace's predicate never existed, on a program that loads clean. Measured before
//! the change: one namespace-less `operation type_compatible(…)` left
//! `anthill.reflect.typing.type_compatible` absent with its five stdlib clauses on the
//! user's operation; a top-level `rule` of the same name left it intact.
//!
//! The rule now holds over the SCOPE (kernel-language.md §5.3, "`<global>` is not a party
//! to any of it"): a head written inside a namespace does not resolve to a name whose only
//! home is `<global>`. It declares at its own scope instead.
//!
//! ── THE BACK-OUT, applied and run ───────────────────────────────────────────
//!
//! In `load.rs`'s `rule_head_ladder_answer`, make the `Found(sym) if … <global> …` arm
//! return `ResolveResult::Found(sym)` instead of re-asking
//! `resolve_rule_head_inside_namespace`. **6 rows fail**: the two stdlib rows, the
//! `sort` and `operation` rows, the staged row and the equation row. **4 pass either way
//! by design** and are the controls: the top-level `rule` spelling (WI-980's own case),
//! the documented top-level form joining at `<global>`, a namespace REFERENCE to a
//! top-level name, and the ambiguity that stays refused.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::{load, KnowledgeBase};
use anthill_core::parse;

/// Clauses stored under `qn`, or `None` when nothing is named `qn` — the absent-versus-
/// empty distinction the defect lives in: the absorbed predicate is ABSENT, not empty.
fn clauses(kb: &KnowledgeBase, qn: &str) -> Option<usize> {
    let sym = kb.try_resolve_symbol(qn)?;
    Some(kb.rules_by_functor(sym).len())
}

fn answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

/// The stdlib predicate a namespace-less user file declares the name of. Five clauses,
/// all bodied, so it is decided by the head pass and was exposed to the ladder.
const STDLIB_PRED: &str = "anthill.reflect.typing.type_compatible";

fn assert_stdlib_intact(user: &str) {
    let kb = crate::common::load_kb_with(user);
    assert_eq!(
        clauses(&kb, STDLIB_PRED),
        Some(5),
        "the stdlib predicate must keep its clauses whatever a namespace-less file declares"
    );
    assert_eq!(
        clauses(&kb, "type_compatible"),
        Some(0),
        "and the user's top-level name exists, carrying none of them"
    );
}

#[test]
fn a_global_operation_does_not_absorb_a_stdlib_predicate() {
    // Measured before: `STDLIB_PRED` = None, `type_compatible` = Some(5).
    assert_stdlib_intact("operation type_compatible(a: Int64, b: Int64) -> Int64 = 1\n");
}

#[test]
fn a_global_sort_does_not_absorb_a_stdlib_predicate() {
    assert_stdlib_intact("sort type_compatible\n  entity tcq(n: Int64)\nend\n");
}

/// One namespace-less declaration of `zqop` beside a namespace that writes a `zqop` rule,
/// as two files and as one — the file boundary is not what the rule is about.
fn assert_namespace_keeps_its_predicate(global_decl: &str) {
    let ns = "namespace zdemo\n  rule zqop(2, 7) :- true\nend\n";
    let joined = format!("{global_decl}{ns}");
    for files in [vec![global_decl, ns], vec![joined.as_str()]] {
        let mut kb = crate::common::try_load_kb_with_files(&files).expect("loads");
        assert_eq!(clauses(&kb, "zdemo.zqop"), Some(1), "{files:?}");
        assert_eq!(clauses(&kb, "zqop"), Some(0), "{files:?}");
        assert_eq!(answers(&mut kb, "zdemo.zqop(2, ?x)"), 1, "{files:?}");
    }
}

#[test]
fn a_global_operation_does_not_absorb_a_namespace_head() {
    // Measured before: `zdemo.zqop` = None, `zqop` = Some(1).
    assert_namespace_keeps_its_predicate("operation zqop(a: Int64, b: Int64) -> Int64 = 1\n");
}

#[test]
fn a_global_sort_does_not_absorb_a_namespace_head() {
    assert_namespace_keeps_its_predicate("sort zqop\n  entity zq(n: Int64)\nend\n");
}

#[test]
fn a_global_rule_head_never_absorbed_one_control() {
    // CONTROL — WI-980's own case, passing before and after: two predicates.
    let mut kb = crate::common::try_load_kb_with_files(&[
        "rule zqop(1, 1) :- true\n",
        "namespace zdemo\n  rule zqop(2, 7) :- true\nend\n",
    ])
    .expect("loads");
    assert_eq!(clauses(&kb, "zdemo.zqop"), Some(1));
    assert_eq!(clauses(&kb, "zqop"), Some(1));
    assert_eq!(answers(&mut kb, "zdemo.zqop(2, ?x)"), 1);
}

#[test]
fn a_staged_load_does_not_yield_to_an_earlier_global_head() {
    // The ticket's second channel: batch 1 mints `<global>.zq`, and batch 2's namespace
    // head used to find it through the ordinary ladder. Measured before: `zq1.zq` = None,
    // `zq` = Some(2) — where one `load_all` over the same pair keeps them apart.
    let mut kb = crate::common::load_kb_with("rule zq(0) :- true\n");
    let second = parse::parse("namespace zq1\n  rule zq(1) :- true\nend\n").expect("parses");
    load::load_all(&mut kb, &[&second], &load::NullResolver).expect("the second batch loads");
    assert_eq!(clauses(&kb, "zq1.zq"), Some(1));
    assert_eq!(clauses(&kb, "zq"), Some(1));
    assert_eq!(answers(&mut kb, "zq1.zq(?x)"), 1);
    assert_eq!(answers(&mut kb, "zq(?x)"), 1);
}

#[test]
fn a_namespace_equation_defines_its_own_operation_beside_a_global_predicate() {
    // §5.3's equation refusal used to record "a `<global>` predicate does absorb a
    // namespace's equation subject, and nothing says so". It no longer does: `pg.f` is the
    // equation-defined operation the namespace wrote, citable by its qualified name from a
    // scope that never saw the top-level file.
    //
    // THE QUALIFIED CALL IS THE DISCRIMINATION. A caller INSIDE `pg` writing `f(true)`
    // answers 7 either way — absorbed, the equation still rewrites its LHS, which then
    // names `<global>.f` — so what the absorption deletes is `pg.f` as a name.
    let src = "rule f(?x)\nnamespace pg\n  rule f(true) <=> 7 @[simp]\nend\n\
               namespace pgc\n  operation g() -> Int64 = pg.f(true)\nend\n";
    let kb = crate::common::load_kb_with(src);
    assert!(kb.try_resolve_symbol("pg.f").is_some(), "`pg.f` must exist");
    let mut interp = crate::common::interp_for(src);
    match interp.call("pgc.g", &[]).expect("the namespace's operation answers by its name") {
        anthill_core::eval::Value::Int(i) => assert_eq!(i, 7),
        other => panic!("expected an Int, got {other:?}"),
    }
}

#[test]
fn the_documented_top_level_form_still_joins_at_global_control() {
    // CONTROL — a namespace-less file's own sort is not "inside a namespace", so its head
    // joins the top-level declaration exactly as `demo { rule p(?x) … sort Rec { … } }`
    // joins inside a namespace. Passes before and after.
    let mut kb = crate::common::load_kb_with(
        "rule p(?x)\nrule p(1) :- true\nsort Rec\n  entity r(n: Int64)\n  rule p(2) :- true\nend\n",
    );
    assert_eq!(clauses(&kb, "p"), Some(2));
    assert_eq!(clauses(&kb, "Rec.p"), None);
    assert_eq!(answers(&mut kb, "p(?x)"), 2);
}

#[test]
fn a_namespace_reference_still_reaches_a_top_level_name_control() {
    // CONTROL — the rule is about HEADS. A body goal is a reference and reads the full
    // ladder, so top-level code stays usable from inside a namespace. Passes either way.
    let mut kb = crate::common::load_kb_with(
        "rule gq(1) :- true\nnamespace zr\n  rule uses(?x) :- gq(?x)\nend\n",
    );
    assert_eq!(answers(&mut kb, "zr.uses(?x)"), 1);
}

#[test]
fn an_ambiguity_with_a_global_name_is_still_reported_control() {
    // CONTROL — `nb` reaches `p` both at `<global>` and through `import nd.*`, so its own
    // references to `p` are ambiguous; the head does not quietly pick `nd.p` (WI-900
    // reports ambiguity at the reference). Refused before and after.
    let r = crate::common::try_load_kb_with_files(&[
        "operation p(a: Int64) -> Int64 = 1\n",
        "namespace nd\n  rule p(?x)\nend\n",
        "namespace nb\n  import nd.*\n  rule p(1) :- true\nend\n",
    ]);
    crate::common::expect_load_errors(
        r,
        &["ambiguous symbol 'p' in scope 'nb': candidates [\"p\", \"nd.p\"]"],
    );
}

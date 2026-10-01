//! WI-20261001-KDMQS — A `const` IN A CLAUSE'S DATA SLOT IS ITS VALUE (spec §5.9), folded
//! when the clause converts. So a persisted IEEE special, which can only be written as its
//! const's name (`Float.infinity`), reloads as the Float it was.
//!
//! MEASURED BEFORE THE CHANGE, on the CLI. No const folded in any data slot: `fact f(v:
//! D_MIN)` answered `?x = D_MIN`, `f(v: 1.5)` matched nothing, and `:- f(v: ?x), ?x = 1.5`
//! answered 0. A DOTTED const was not even resolved: `fact f(v: Float.infinity)` stored
//! `field_access(Float, infinity)`, so a persisted `+∞` came back as structure and the
//! join `f(v: ?x), ?r <=> 1.0 / 0.0, ?x = ?r` answered 0. The same dotted const in a rule
//! body was a LOAD ERROR ("type mismatch in Float.name").
//!
//! ── WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT ─────────────────────────────────
//!
//! Back out the FOLD (`Loader::data_slot_const_value` / `data_slot_dotted_const` and the
//! query twin `query_data_slot_const` answering `None`), MEASURED — SIX FAIL:
//! [`persisted_ieee_specials_reload_as_the_float_they_were`] (the three special rows),
//! [`a_literal_bodied_const_in_a_fact_is_its_value`],
//! [`a_const_in_a_rule_body_value_slot_is_its_value`] (`gt` / `flag = true` / `<=> nn`),
//! [`a_dotted_const_in_a_rule_body_data_slot_matches_the_fact`] (back to the load error),
//! [`a_query_pattern_folds_like_the_fact_it_searches_for`], and
//! [`a_computed_const_in_a_data_slot_is_refused_loudly`] (it loads clean, holding the
//! symbol).
//!
//! The two `/code-review` fixes, each MEASURED against its own back-out:
//! [`a_query_evaluates_a_computed_const`] fails without the evaluator in
//! `query_data_slot_const` (0 ≠ 1), and
//! [`a_compound_expression_in_a_fact_keeps_the_const_for_eval`] fails without the term
//! walk's compound-marker rule (the load refuses `D_MAX`).
//!
//! Back out the PRINTER's dotted-chain rendering (`TermPrinter::dotted_chain_name`),
//! MEASURED — ONE FAILS, [`the_store_retracts_a_persisted_ieee_special`], on "must be
//! dropped"; it passes under the fold back-out, where the KB holds the chain itself. The KB keys the folded `+∞` as
//! `Float.infinity`, the parse of the same on-disk text keys as `field_access(Float,
//! infinity)`, and the fact stays on disk without a word.
//!
//! PASS EITHER WAY, BY DESIGN — controls that say what the change does NOT touch:
//! the FINITE row of the round trip (a `3.0` was always a literal);
//! [`the_symbolic_spelling_still_matches_its_fact`] (before: symbol against symbol;
//! after: value against value. It guards the regression a facts-only fold would have
//! caused, where the goal kept the symbol and the fact held the value);
//! the GOAL-position row `:- flag`, which is WI-20260822-NDG34's and stays 0;
//! [`a_quoted_term_field_keeps_the_const_as_written`] (which DID fail, 0 ≠ 1, before
//! `Loader::entity_field_is_quoted`: the occurrence walk folded what the quoted term
//! kept); and the operation-body row of
//! [`a_computed_const_in_a_data_slot_is_refused_loudly`], which folds at eval.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term};
use anthill_core::kb::{ClauseKind, KnowledgeBase};
use anthill_core::persistence::file_store::{FileConvention, FileStore};
use anthill_core::persistence::Store;
use ordered_float::OrderedFloat;
use smallvec::SmallVec;

/// The DEFINITE answers of the unary relation `qn`.
fn definite(kb: &mut KnowledgeBase, qn: &str) -> usize {
    crate::common::query_unary(kb, qn)
        .iter()
        .filter(|(_, definite)| *definite)
        .count()
}

/// The one definite answer of the unary relation `qn`, as the Float it denotes.
fn one_float(kb: &mut KnowledgeBase, qn: &str) -> f64 {
    let rows = crate::common::query_unary(kb, qn);
    match rows.as_slice() {
        [(v, true)] => {
            use anthill_core::kb::term_view::TermView;
            v.literal_f64(kb)
                .unwrap_or_else(|| panic!("{qn}: the answer is not a Float: {v:?}"))
        }
        _ => panic!("{qn}: expected one definite row, got {rows:?}"),
    }
}

/// How many solutions `pattern` has, through the shipped query-pattern path.
fn pattern_answers(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    let goal = crate::common::query_pattern_term(kb, pattern);
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

/// The four entities the round trip persists, one per value so a row is attributable.
const RT_DECLS: &str = "  import anthill.prelude.{Float}\n  \
     sort Rec\n    \
       entity pinf(v: Float)\n    \
       entity ninf(v: Float)\n    \
       entity nan(v: Float)\n    \
       entity fin(v: Float)\n  \
     end\n";

/// THE ACCEPTANCE. A fact holding each of `1.0/0.0`, `-1.0/0.0`, `0.0/0.0` (and a finite
/// control) is persisted through the file store, reloaded from the text it wrote, and
/// joined against the value COMPUTED in a rule body: one row each.
///
/// THE JOIN IS A MATCH. The computed value is bound first and the fact is looked up by
/// it (`?r <=> 1.0 / 0.0, pinf(v: ?r)`), so the discrimination tree must index the
/// stored value. That is the claim the fold makes.
///
/// WHICH NaN EQUALITY HOLDS, and why both are right. `Literal::Float` is an
/// `OrderedFloat`, under which EVERY NaN is equal to every other, whatever its sign bit
/// or payload. So the stored `Float.nan` (the host's canonical quiet NaN) and a computed
/// `0.0 / 0.0` (whose sign bit is the platform's choice) are ONE term, and the match and
/// `<=>` both succeed: structurally they are the same value. The written test `=` is
/// `Float`'s IEEE `eq`, under which NaN equals nothing, itself included. So the
/// `=`-spelled join answers 0 for NaN, by design, while its ±∞ rows answer 1.
#[test]
fn persisted_ieee_specials_reload_as_the_float_they_were() {
    let dir = tempfile::tempdir().expect("create temp dir");
    let mut store = FileStore::new(dir.path().to_path_buf(), FileConvention::Flat);
    let mut kb = crate::common::load_kb_with(&format!("namespace kdmqs.rt\n{RT_DECLS}end\n"));
    let v = kb.intern("v");
    let sort = ClauseKind::Fact;
    let domain = kb.intern("kdmqs");
    for (entity, value) in [
        ("pinf", 1.0_f64 / 0.0),
        ("ninf", -1.0_f64 / 0.0),
        ("nan", 0.0_f64 / 0.0),
        ("fin", 3.0),
    ] {
        let functor = kb.resolve_symbol(&format!("kdmqs.rt.Rec.{entity}"));
        let lit = kb.alloc(Term::Const(Literal::Float(OrderedFloat(value))));
        let head = kb.alloc(Term::Fn {
            functor,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_elem((v, lit), 1),
        });
        store.persist(&kb, head, sort, domain, None).unwrap();
    }
    store.flush(&kb).unwrap();
    let written = std::fs::read_to_string(dir.path().join("facts.anthill")).unwrap();
    for line in [
        "fact pinf(v: Float.infinity)",
        "fact ninf(v: Float.negativeInfinity)",
        "fact nan(v: Float.nan)",
        "fact fin(v: 3.0)",
    ] {
        assert!(written.contains(line), "the store writes `{line}`: {written}");
    }

    // A store writes bare `fact …` lines; the scope they reload into supplies the names
    // they use, `Float` among them (WI-20260825-5W3RJ).
    let mut kb2 = crate::common::load_kb_with(&format!(
        "namespace kdmqs.rt\n{RT_DECLS}{written}  \
         rule m_pinf(1) :- ?r <=> 1.0 / 0.0, pinf(v: ?r)\n  \
         rule m_ninf(1) :- ?r <=> -1.0 / 0.0, ninf(v: ?r)\n  \
         rule m_nan(1) :- ?r <=> 0.0 / 0.0, nan(v: ?r)\n  \
         rule m_fin(1) :- ?r <=> 6.0 / 2.0, fin(v: ?r)\n  \
         rule e_pinf(1) :- pinf(v: ?x), ?r <=> 1.0 / 0.0, ?x = ?r\n  \
         rule e_ninf(1) :- ninf(v: ?x), ?r <=> -1.0 / 0.0, ?x = ?r\n  \
         rule e_nan(1) :- nan(v: ?x), ?r <=> 0.0 / 0.0, ?x = ?r\n  \
         rule u_nan(1) :- nan(v: ?x), ?r <=> 0.0 / 0.0, ?x <=> ?r\n\
         end\n"
    ));
    for rel in ["m_pinf", "m_ninf", "m_nan"] {
        assert_eq!(
            definite(&mut kb2, &format!("kdmqs.rt.{rel}")),
            1,
            "{rel}: the reloaded fact holds the Float, so the computed value finds it. \
             Before the fold it held `field_access(Float, …)` and this answered 0",
        );
    }
    assert_eq!(
        definite(&mut kb2, "kdmqs.rt.m_fin"),
        1,
        "CONTROL: a finite Float round-trips as a literal, before and after",
    );
    assert_eq!(definite(&mut kb2, "kdmqs.rt.e_pinf"), 1, "IEEE: +inf = +inf");
    assert_eq!(definite(&mut kb2, "kdmqs.rt.e_ninf"), 1, "IEEE: -inf = -inf");
    assert_eq!(
        definite(&mut kb2, "kdmqs.rt.e_nan"),
        0,
        "IEEE `=`: NaN equals nothing, itself included. The fact IS the NaN (see `u_nan`)",
    );
    assert_eq!(
        definite(&mut kb2, "kdmqs.rt.u_nan"),
        1,
        "`<=>` is structural, and under `OrderedFloat` every NaN is the same term",
    );
}

/// The file store finds a persisted IEEE special by its content key and drops it.
#[test]
fn the_store_retracts_a_persisted_ieee_special() {
    let dir = tempfile::tempdir().expect("create temp dir");
    let mut store = FileStore::new(dir.path().to_path_buf(), FileConvention::Flat);
    let mut kb = crate::common::load_kb_with(&format!(
        "namespace kdmqs.rt\n{RT_DECLS}  \
         fact pinf(v: Float.infinity)\n  \
         fact fin(v: 3.0)\n\
         end\n"
    ));
    let rid = |kb: &KnowledgeBase, qn: &str| {
        let sym = kb.resolve_symbol(qn);
        let rids = kb.rules_by_functor(sym);
        assert_eq!(rids.len(), 1, "{qn}: one fact");
        rids[0]
    };
    let (pinf, fin) = (rid(&kb, "kdmqs.rt.Rec.pinf"), rid(&kb, "kdmqs.rt.Rec.fin"));
    let sort = ClauseKind::Fact;
    let domain = kb.intern("kdmqs");
    for id in [pinf, fin] {
        store.persist(&kb, kb.rule_head(id), sort, domain, None).unwrap();
    }
    store.flush(&kb).unwrap();
    let path = dir.path().join("facts.anthill");
    let written = std::fs::read_to_string(&path).unwrap();
    assert!(written.contains("fact pinf(v: Float.infinity)"), "{written}");

    for id in [pinf, fin] {
        assert!(store.retract(&kb, id).unwrap(), "retract is buffered");
        kb.retract(id);
    }
    store.flush(&kb).unwrap();
    let after = std::fs::read_to_string(&path).unwrap();
    assert!(
        !after.contains("pinf"),
        "the persisted `+∞` must be found by its content key and dropped. The KB keys \
         the folded Float as `Float.infinity`, and the parse of the same text must key \
         the same, or the fact stays on disk silently: {after}",
    );
    assert!(!after.contains("fin"), "CONTROL, the finite fact: {after}");
}

const CONST_SRC: &str = "namespace kdmqs.c\n  \
     import anthill.prelude.{Float, Int64, Bool}\n  \
     import anthill.prelude.Float.{infinity}\n  \
     const D_MIN: Float = 1.5\n  \
     const D_ALIAS: Float = D_MIN\n  \
     const BROADCAST: Int64 = -1\n  \
     const nn: Int64 = 5\n  \
     const flag: Bool = true\n  \
     sort Rec\n    \
       entity f(v: Float)\n    \
       entity g(n: Int64)\n  \
     end\n  \
     fact f(v: D_MIN)\n  \
     fact f(v: infinity)\n  \
     fact g(n: BROADCAST)\n  \
     rule by_value(1) :- f(v: 1.5)\n  \
     rule by_alias(1) :- f(v: D_ALIAS)\n  \
     rule by_name(1) :- f(v: D_MIN)\n  \
     rule by_test(?x) :- f(v: ?x), ?x = 1.5\n  \
     rule g_value(?n) :- g(n: ?n)\n  \
     rule gt(1) :- Int64.gt(nn, 3)\n  \
     rule flag_eq(1) :- flag = true\n  \
     rule flag_goal(1) :- flag\n  \
     rule bound(?x) :- ?x <=> nn\n\
     end\n";

/// A literal-bodied const in a fact IS its value: matched by the value, found by a test on
/// the value, and an alias of it (`const D_ALIAS: Float = D_MIN`) is the same value.
#[test]
fn a_literal_bodied_const_in_a_fact_is_its_value() {
    let mut kb = crate::common::load_kb_with(CONST_SRC);
    assert_eq!(definite(&mut kb, "kdmqs.c.by_value"), 1, "the fact is matched by 1.5");
    assert_eq!(definite(&mut kb, "kdmqs.c.by_alias"), 1, "an alias const has its value");
    assert_eq!(one_float(&mut kb, "kdmqs.c.by_test"), 1.5, "the test `?x = 1.5` holds");
    assert_eq!(
        crate::common::one_definite_int(&mut kb, "kdmqs.c.g_value"),
        Some(-1),
        "a negative literal body (`-1`, the webots BROADCAST spelling) is a literal too",
    );
}

/// CONTROL: the symbolic spelling of a goal still finds the fact written with the same
/// symbol, because BOTH sides fold. Passes either way by design.
#[test]
fn the_symbolic_spelling_still_matches_its_fact() {
    let mut kb = crate::common::load_kb_with(CONST_SRC);
    assert_eq!(definite(&mut kb, "kdmqs.c.by_name"), 1);
}

/// The value-slot rows of WI-20260822-NDG34: a const read by a rule-body goal's argument
/// is its value. The GOAL-position row `:- flag` is that ticket's own question and is not
/// moved here: it stays 0.
#[test]
fn a_const_in_a_rule_body_value_slot_is_its_value() {
    let mut kb = crate::common::load_kb_with(CONST_SRC);
    assert_eq!(definite(&mut kb, "kdmqs.c.gt"), 1, "`Int64.gt(nn, 3)` reads nn = 5");
    assert_eq!(definite(&mut kb, "kdmqs.c.flag_eq"), 1, "`flag = true` reads flag = true");
    assert_eq!(
        crate::common::one_definite_int(&mut kb, "kdmqs.c.bound"),
        Some(5),
        "`?x <=> nn` binds the value",
    );
    assert_eq!(
        definite(&mut kb, "kdmqs.c.flag_goal"),
        0,
        "CONTROL: a bare const in GOAL position is not folded (WI-20260822-NDG34)",
    );
}

/// A DOTTED const in a rule-body data slot loads (it was a load error) and builds the same
/// term the fact spelling it with the imported short name built.
///
/// Its own fixture, so that the load error it gives without the fold does not take
/// [`CONST_SRC`]'s controls down with it.
#[test]
fn a_dotted_const_in_a_rule_body_data_slot_matches_the_fact() {
    let mut kb = crate::common::load_kb_with(
        "namespace kdmqs.d\n  \
         import anthill.prelude.{Float}\n  \
         import anthill.prelude.Float.{infinity}\n  \
         sort Rec\n    entity f(v: Float)\n  end\n  \
         fact f(v: infinity)\n  \
         rule dotted(1) :- f(v: Float.infinity)\n\
         end\n",
    );
    assert_eq!(definite(&mut kb, "kdmqs.d.dotted"), 1);
}

/// A query pattern folds like the fact it searches for, in both spellings: the qualified
/// dotted name and the imported short one.
#[test]
fn a_query_pattern_folds_like_the_fact_it_searches_for() {
    let mut kb = crate::common::load_kb_with(CONST_SRC);
    assert_eq!(pattern_answers(&mut kb, "kdmqs.c.Rec.f(v: kdmqs.c.D_MIN)"), 1);
    assert_eq!(pattern_answers(&mut kb, "kdmqs.c.Rec.f(v: 1.5)"), 1);
    assert_eq!(
        pattern_answers(&mut kb, "kdmqs.c.Rec.f(v: anthill.prelude.Float.infinity)"),
        1
    );
    crate::common::supply_invocation_imports(&mut kb, &["kdmqs.c.*"]);
    assert_eq!(pattern_answers(&mut kb, "f(v: D_ALIAS)"), 1);
}

/// A const whose body COMPUTES its value has no value when a clause loads, so a data slot
/// naming it is refused, loudly and at the slot, instead of storing the symbol, which
/// matches nothing the const denotes. The same const in an operation body folds at eval,
/// as it always did.
#[test]
fn a_computed_const_in_a_data_slot_is_refused_loudly() {
    let decls = "  import anthill.prelude.{Float}\n  \
                 const D_MIN: Float = 1.5\n  \
                 const D_MAX: Float = 2.0 * D_MIN\n  \
                 sort Rec\n    entity f(v: Float)\n  end\n  \
                 operation dmax() -> Float = D_MAX\n";
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(&format!(
            "namespace kdmqs.cx\n{decls}  fact f(v: D_MAX)\nend\n"
        )),
        &["the const `kdmqs.cx.D_MAX` is written in a data slot"],
    );
    let mut kb = crate::common::load_kb_with(&format!(
        "namespace kdmqs.cx\n{decls}  rule via_op(?x) :- ?x <=> dmax()\nend\n"
    ));
    assert_eq!(
        one_float(&mut kb, "kdmqs.cx.via_op"),
        3.0,
        "CONTROL: the operation body evaluates the computed const",
    );
}

/// A QUERY may name a computed const: it converts against a loaded program, so the
/// evaluator gives the value. A fact can hold that value without naming the const, here as
/// a store reload writes it, so a query by the const's name must find it. Without the
/// evaluator the pattern kept the symbol and answered 0 (`/code-review`'s finding).
#[test]
fn a_query_evaluates_a_computed_const() {
    let mut kb = crate::common::load_kb_with(
        "namespace kdmqs.qe\n  \
         import anthill.prelude.{Float}\n  \
         const D_MIN: Float = 1.5\n  \
         const D_MAX: Float = 2.0 * D_MIN\n  \
         sort Rec\n    entity f(v: Float)\n  end\n  \
         fact f(v: 3.0)\n\
         end\n",
    );
    assert_eq!(pattern_answers(&mut kb, "kdmqs.qe.Rec.f(v: kdmqs.qe.D_MAX)"), 1);
    assert_eq!(
        pattern_answers(&mut kb, "kdmqs.qe.Rec.f(v: kdmqs.qe.D_MIN)"),
        0,
        "CONTROL: the value is compared, not just any Float",
    );
}

/// A compound expression (`if` / `let` / `lambda`) is EVALUATED, so a const inside one is
/// not a data slot even when the expression is written in a fact. The rule-body walk left
/// it alone from the start; the term walk folded it, so a computed const there was refused
/// in a fact and accepted in a rule body (`/code-review`'s finding).
#[test]
fn a_compound_expression_in_a_fact_keeps_the_const_for_eval() {
    let mut kb = crate::common::load_kb_with(
        "namespace kdmqs.ce\n  \
         import anthill.prelude.{Float}\n  \
         const D_MIN: Float = 1.5\n  \
         const D_MAX: Float = 2.0 * D_MIN\n  \
         fact held(if true then D_MAX else 0.0)\n  \
         rule any(1) :- held(?)\n\
         end\n",
    );
    assert_eq!(definite(&mut kb, "kdmqs.ce.any"), 1);
}

/// CONTROL: a field declared `anthill.reflect.Term` holds a QUOTED pattern, and a const in
/// it is what its author wrote, not a value. Matched by the symbol, not by the value.
#[test]
fn a_quoted_term_field_keeps_the_const_as_written() {
    let mut kb = crate::common::load_kb_with(
        "namespace kdmqs.q\n  \
         import anthill.prelude.{Float}\n  \
         import anthill.reflect.{Term}\n  \
         const D_MIN: Float = 1.5\n  \
         sort Rec\n    entity f(v: Float)\n    entity holds(pattern: Term)\n  end\n  \
         fact holds(pattern: f(v: D_MIN))\n  \
         rule by_name(1) :- holds(pattern: f(v: D_MIN))\n  \
         rule by_value(1) :- holds(pattern: f(v: 1.5))\n\
         end\n",
    );
    assert_eq!(definite(&mut kb, "kdmqs.q.by_name"), 1);
    assert_eq!(definite(&mut kb, "kdmqs.q.by_value"), 0);
}

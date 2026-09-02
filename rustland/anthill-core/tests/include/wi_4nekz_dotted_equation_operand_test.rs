//! WI-20260902-4NEKZ — A DOTTED PAREN-LESS CITATION OF A RULE IS THAT RELATION IN A
//! RULE-BODY VALUE SLOT, AS IT ALREADY IS IN AN OPERATION BODY.
//!
//! WI-20260901-719FJ collapses a dotted paren-less citation to the name it spells in a
//! LOGICAL position only: a DATA slot holds a term whose spelling is its identity, so
//! `fact holds(ns.rel)` and the goal `holds(ns.rel)` must build ONE term and the chain
//! stands. That is right, and it left the chain to be TYPED — leaf by leaf.
//!
//! ── IT WAS NOT A BAD MESSAGE, IT WAS A REFUSAL ───────────────────────────────
//!
//! The ticket described a diagnostic defect. Measured, it also REFUSED WELL-TYPED
//! PROGRAMS, which is why this file's headline is a load and not a string:
//!
//! | program (one file, `rule rel(1) :- base(1)` one namespace up) | before | after |
//! |---|---|---|
//! | `rule r(1) :- ns.rel = ns.rel`   | **6 load errors** | loads |
//! | `rule r(1) :- ns.rel = local_rel` | **3 load errors** | loads |
//! | `rule r(1) :- ns.rel = 7`        | **3** per-segment errors | **1**, the true one |
//!
//! The three per operand were one per SEGMENT of a name that RESOLVES —
//! `zzf2.name`, `inner.name`, `rel.name`, all "expected resolved name, got unresolved" —
//! because the typer reached [`check_bare_ref`] once per leaf of the `field_access` chain
//! and a namespace has no value reading. The ONE-SEGMENT spelling of the same program
//! says the true thing (`eq.b (op-arg): expected Relation[…], got Int64`) and so does the
//! OPERATION-BODY spelling of the dotted one, because `Loader::try_qualified_rule_ref`
//! collapses the chain there. The rule body was the one position with neither.
//!
//! ── THE POPULATION, MEASURED RATHER THAN ASSUMED ─────────────────────────────
//!
//! Six name kinds were compared in BOTH positions, and exactly ONE row differed:
//!
//! | the chain names | operation body | rule body, before | rule body, after |
//! |---|---|---|---|
//! | a **RULE**   | 1 error | **3** | 1 |
//! | a constructor | 3 | 3 | 3 |
//! | a sort        | 2 | 2 | 2 |
//! | a namespace   | 2 | 2 | 2 |
//! | an entity     | 2 | 2 | 2 |
//! | nothing       | 3 | 3 | 3 |
//!
//! So the other five are not this spelling's defect: they are `check_bare_ref`'s
//! fall-through saying "unresolved" about a name that resolved, once per segment, and
//! they are identical in both positions. **WI-20260902-40KSW** owns them, and
//! [`the_five_other_name_kinds_still_agree_with_the_operation_body`] is its fixture.
//!
//! ── WHY THE REPAIR IS THE TYPER'S AND NOT THE LOADER'S ───────────────────────
//!
//! Collapsing the chain in a rule-body value slot is the obvious repair and it is WRONG:
//! it would fell
//! `wi_719fj_dotted_paren_less_citation_test::a_data_slot_still_stores_the_chain_on_both_sides_of_a_match`.
//! A `fact`'s argument is a TERM built by `convert_term`, which keeps the chain; a rule
//! body is an OCCURRENCE. Rewriting one side alone stops them matching — WI-756's rule,
//! and the whole reason 719FJ gated its own collapse on a logical position. Reading the
//! chain in the typer changes no term, which
//! [`the_chain_is_unchanged_as_a_term_and_at_run_time`] asserts directly.
//!
//! AND IT IS NOT A LIE ABOUT THE VALUE, checked: `?t <=> ns.rel` and the one-segment
//! `?t <=> rel` BOTH bind the NAME (`Ref(rel)`) at run time — neither builds a `Relation`
//! value in a rule body. So typing the chain as `Relation[T]` says exactly what the
//! one-segment spelling already says in the same position, which is the parity this
//! ticket is about, rather than inventing a reading for one spelling.
//!
//! NO SCALAND MIRROR: the diagnosis is the typer's, and scaland has none (WI-1007).
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! TWO AXES, each backed out PRESENT-BUT-WRONG and run over the whole `wi_tests` binary.
//!
//! **1 — THE READING.** `dotted_citation_relation`'s rung at the head of `visit_type`'s
//! `Expr::Apply` arm, made to answer `None`. **EXACTLY 4 ROWS FAIL** of 4 047:
//! [`a_dotted_rule_citation_types_as_the_relation_it_names`],
//! [`the_mismatch_diagnosis_is_the_one_the_other_two_spellings_give`],
//! [`every_citation_form_reaches_the_same_reading`], and
//! [`a_hand_written_field_access_call_is_not_a_citation`] — the last on its PAIR half
//! ("the desugared dot still loads"), which is what makes that test a measurement of
//! PROVENANCE rather than of the recognizer being switched off.
//!
//! **2 — THE PROVENANCE GATE.** Drop `occ.is_dot_chain() &&` from
//! `loader_chain_dotted_name`'s guard, so the recognizer works by SHAPE as this ticket's
//! first cut did. **EXACTLY 1 ROW FAILS:**
//! [`a_hand_written_field_access_call_is_not_a_citation`], on both its receiver shapes.
//! Every other row passes with it out, which is what says the gate is a second decision
//! and not a restatement of the first — and the two axes meet in that one test, on its
//! two halves.
//!
//! TWO MORE ROWS PASS UNDER BOTH, BY DESIGN, and each guards a different way of getting
//! this wrong: [`the_five_other_name_kinds_still_agree_with_the_operation_body`] fails if
//! the rung is widened past `cites_a_relation` to "the chain resolves", and
//! [`the_chain_is_unchanged_as_a_term_and_at_run_time`] fails if the repair is moved to
//! the loader.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

/// The fixture every test here varies: `zz4n.inner.rel` is a real one-clause relation,
/// `zz4n.two.rel2` its one-segment twin, and `body` is written in `zz4n.two`'s rule body.
fn rule_body(body: &str) -> Vec<String> {
    let src = format!(
        "namespace zz4n.inner\n  fact base4n(1)\n  rule rel(1) :- base4n(1)\nend\n\
         namespace zz4n.two\n  fact base4n2(1)\n  rule rel2(1) :- base4n2(1)\n  \
         rule r(1) :- {body}\nend\n"
    );
    crate::common::try_load_kb_with(&src).err().unwrap_or_default()
}

/// The same `body` written in an OPERATION body instead — the position that already had
/// the reading, and the yardstick every row below is read against.
fn op_body(body: &str) -> Vec<String> {
    let src = format!(
        "namespace zz4n.inner\n  fact base4n(1)\n  rule rel(1) :- base4n(1)\nend\n\
         namespace zz4n.op\n  import anthill.prelude.Bool\n  \
         operation viaOp() -> Bool = {body}\nend\n"
    );
    crate::common::try_load_kb_with(&src).err().unwrap_or_default()
}

/// **A — THE HEADLINE, AND IT IS A LOAD.** Two WELL-TYPED programs that did not load.
///
/// Asserted as a LOAD rather than as an error string because the defect was a refusal:
/// `ns.rel = ns.rel` reported SIX errors (three per operand) and `ns.rel = local_rel`
/// three. Both are comparisons of two `Relation[T = Unit]` values, which is what the
/// one-segment spelling has always been allowed to write.
#[test]
fn a_dotted_rule_citation_types_as_the_relation_it_names() {
    for (label, body, before) in [
        (
            "both operands dotted",
            "zz4n.inner.rel = zz4n.inner.rel",
            6,
        ),
        ("dotted against its one-segment twin", "zz4n.inner.rel = rel2", 3),
    ] {
        let errs = rule_body(body);
        assert!(
            errs.is_empty(),
            "{label}: `{body}` compares two relations and must LOAD — it reported \
             {before} per-segment 'unresolved name' errors before this ticket; now: {errs:#?}"
        );
    }
    // THE CONTROL that says the two really are relations and not two things that failed
    // to type: the ONE-SEGMENT comparison, which has always loaded.
    assert!(
        rule_body("rel2 = rel2").is_empty(),
        "the one-segment comparison is the control and has always loaded"
    );
}

/// **B — AND WHEN IT IS A REAL MISMATCH, ONE TRUE DIAGNOSIS.** `ns.rel = 7` compares a
/// relation with an integer; that is an error and must be reported as one.
///
/// THE TEXT IS ASSERTED, not the count alone: a repair that merely stopped the cascade
/// would leave one error still saying a resolved name is unresolved, which is the half of
/// this ticket that would have gone unmeasured.
#[test]
fn the_mismatch_diagnosis_is_the_one_the_other_two_spellings_give() {
    let dotted = rule_body("zz4n.inner.rel = 7");
    assert_eq!(
        dotted.len(),
        1,
        "one written name, one diagnosis — it was THREE, one per segment: {dotted:#?}"
    );
    assert!(
        dotted[0].contains("eq.b (op-arg)") && dotted[0].contains("Relation"),
        "…and it names the COMPARISON and the relation type, not a segment: {:?}",
        dotted[0]
    );
    assert!(
        !dotted[0].contains("unresolved"),
        "…and it does not call a name that resolves unresolved: {:?}",
        dotted[0]
    );

    // THE TWO YARDSTICKS, both green before and after: the one-segment spelling in the
    // same position, and the dotted spelling in an OPERATION body. The claim of this
    // ticket is that all three agree, so all three are read.
    let one_segment = rule_body("rel2 = 7");
    let in_op_body = op_body("zz4n.inner.rel = 7");
    assert_eq!(
        one_segment.len(),
        1,
        "the one-segment yardstick: {one_segment:#?}"
    );
    assert_eq!(
        in_op_body.len(),
        1,
        "the operation-body yardstick — where `try_qualified_rule_ref` already \
         collapsed the chain: {in_op_body:#?}"
    );
    for (label, other) in [("one-segment", &one_segment), ("op-body", &in_op_body)] {
        assert!(
            other[0].contains("eq.b (op-arg)") && other[0].contains("Relation"),
            "{label} must say the same thing: {:?}",
            other[0]
        );
    }
}

/// **C — EVERY CITATION FORM, because the reading consults NO SCOPE.** The recognizer
/// joins the receiver's already-QUALIFIED symbol with the field's short name, which is
/// only sound if the loader really has re-routed each level. It has: measured, the
/// receiver leaf carries `zz4nc.inner` in all three forms.
///
/// A relative citation is the row that would fail if the recognizer resolved the WRITTEN
/// text instead — `inner.rel` names nothing at global scope.
#[test]
fn every_citation_form_reaches_the_same_reading() {
    for (label, decl, body) in [
        (
            "absolute",
            "namespace zz4nc.inner\n  fact b(1)\n  rule rel(1) :- b(1)\nend\n\
             namespace zz4nc.two\n",
            "zz4nc.inner.rel = 7",
        ),
        (
            "relative",
            "namespace zz4nd\n  namespace inner\n    fact b(1)\n    rule rel(1) :- b(1)\n  end\n",
            "inner.rel = 7",
        ),
        (
            "marked absolute",
            "namespace zz4ne.inner\n  fact b(1)\n  rule rel(1) :- b(1)\nend\n\
             namespace zz4ne.two\n",
            "..zz4ne.inner.rel = 7",
        ),
    ] {
        let src = format!("{decl}  rule r(1) :- {body}\nend\n");
        let errs = crate::common::try_load_kb_with(&src).err().unwrap_or_default();
        assert_eq!(
            errs.len(),
            1,
            "{label} (`{body}`): one written name, one diagnosis — each was THREE (two \
             for the relative form, which has one segment fewer): {errs:#?}"
        );
        assert!(
            errs[0].contains("eq.b (op-arg)"),
            "{label}: …and it is the comparison: {:?}",
            errs[0]
        );
    }
}

/// **THE BOUND — GREEN BEFORE AND AFTER, AND THE ROW A TOO-WIDE RUNG FAILS.**
///
/// The rung fires only when the joined name `cites_a_relation`. Keyed instead on "the
/// chain resolves to something", it would swallow these five and change their
/// diagnostics; keyed on the RULE, they are untouched. Asserted as a PAIR against the
/// OPERATION body rather than as absolute counts, because those counts belong to
/// WI-20260902-40KSW and will move when it lands — what must not move is the two
/// positions agreeing.
#[test]
fn the_five_other_name_kinds_still_agree_with_the_operation_body() {
    const DECL: &str = "\
namespace zz4nf
  import anthill.prelude.Int64
  sort Color
    entity red
  end
  entity acct(n: Int64)
end
namespace zz4nf.inner
  fact b(1)
  rule rel(1) :- b(1)
end
";
    for (label, body) in [
        ("constructor", "zz4nf.Color.red = 7"),
        ("sort", "zz4nf.Color = 7"),
        ("namespace", "zz4nf.inner = 7"),
        ("entity", "zz4nf.acct = 7"),
        ("nothing", "zz4nf.nosuch.x = 7"),
    ] {
        let rule = crate::common::try_load_kb_with(&format!(
            "{DECL}namespace zz4nfr\n  rule r(1) :- {body}\nend\n"
        ))
        .err()
        .unwrap_or_default();
        let op = crate::common::try_load_kb_with(&format!(
            "{DECL}namespace zz4nfo\n  import anthill.prelude.Bool\n  \
             operation viaOp() -> Bool = {body}\nend\n"
        ))
        .err()
        .unwrap_or_default();
        assert_eq!(
            rule.len(),
            op.len(),
            "{label} (`{body}`): a chain naming no rule is NOT this ticket's — the two \
             positions report it identically, and must keep doing so \
             (WI-20260902-40KSW owns the message itself).\nrule body: {rule:#?}\nop body: {op:#?}"
        );
        assert!(
            !rule.is_empty(),
            "{label}: …and it is still refused — this row must not become a silent \
             acceptance"
        );
    }
    // AND THE VAR-ROOTED PROJECTION, which is a genuine dot on a VALUE and never a name:
    // the loader re-routes it to `DotApply`, so the recognizer must never see it.
    //
    // THE NON-EMPTY ASSERTION IS THE POINT, not decoration: `iter().all(…)` is TRUE of an
    // empty list, so without it this row would go vacuous — still reading as a guard —
    // the day the fixture started loading clean. (`/code-review` caught it written that
    // way; measured, it reports one error today.)
    let projection = crate::common::try_load_kb_with(
        "namespace zz4ng\n  entity boxed(f: anthill.prelude.Int64)\n  \
         fact boxed(f: 1)\n  rule r(1) :- boxed(f: ?x), ?x.f = 7\nend\n",
    )
    .err()
    .unwrap_or_default();
    assert!(
        !projection.is_empty(),
        "the projection fixture must still be REFUSED — an empty list would make the \
         assertion below vacuous while it still read as a guard"
    );
    assert!(
        projection.iter().all(|e| !e.contains("Relation")),
        "a projection on a VALUE is not a citation and must not be read as a relation; \
         got {projection:#?}"
    );
}

/// **THE PROVENANCE BOUND — the row `/code-review` had to find, because the first cut of
/// this ticket got it wrong.** A HAND-WRITTEN call to a functor spelled `field_access` is
/// a call to whatever that name denotes, NOT the desugaring of a dot
/// (WI-20260901-92VA4). The loader gates its own recognizer on the parse term's
/// `is_minted` bit for exactly this; the typer's had no such bit and read the written
/// call as a name, typed it `Relation[T]`, and let the program LOAD CLEAN — a SILENT
/// ACCEPTANCE, strictly worse than the noisy refusal this ticket replaced.
///
/// SHAPE CANNOT TELL THEM APART, which is why `NodeOccurrence` grew a `dot_chain` bit
/// rather than the recognizer growing a cleverer pattern. MEASURED: with a ONE-SEGMENT
/// receiver the two forms reach the typer as identical `Expr::Apply` nodes — same
/// functor, a resolved `Ref` receiver, a bare `Ident` selector. A first repair that
/// required every receiver segment to be a resolved `Ref` closed the two-segment case and
/// left this one wide open.
///
/// EACH WRITTEN FORM IS PAIRED WITH THE DOT IT MIMICS, so the row measures the
/// PROVENANCE and not the spelling: the dotted form of the same program loads.
#[test]
fn a_hand_written_field_access_call_is_not_a_citation() {
    for (label, receiver) in [
        ("two-segment receiver", "zz4n.inner"),
        // The one-segment receiver is the shape a resolved-segments test would MISS.
        ("one-segment receiver", "zz4n"),
    ] {
        let written = rule_body(&format!(
            "anthill.reflect.field_access({receiver}, rel) = 7"
        ));
        assert!(
            !written.is_empty(),
            "{label}: a WRITTEN `field_access` call is a call, not the name \
             `{receiver}.rel` — it must stay refused. It loaded clean on this ticket's \
             first cut."
        );
        assert!(
            written.iter().all(|e| !e.contains("Relation")),
            "{label}: …and nothing about it is typed as a relation: {written:#?}"
        );
    }
    // THE PAIR: the DOT that spells the same chain does load, so this is the provenance
    // being read and not the recognizer being switched off.
    assert!(
        rule_body("zz4n.inner.rel = zz4n.inner.rel").is_empty(),
        "the desugared dot still loads — the row above is about PROVENANCE, not shape"
    );
}

/// **THE OTHER BOUND — GREEN BEFORE AND AFTER, AND THE ROW A LOADER REPAIR FAILS.**
///
/// The change is a typer READ. The chain is still the term it was, so the two sides of a
/// match still spell it the same way (719FJ's rule), and the value a data slot binds is
/// unmoved. A repair that collapsed the chain in the rule-body walk instead would break
/// the first assertion here and 719FJ's own data-slot row with it.
#[test]
fn the_chain_is_unchanged_as_a_term_and_at_run_time() {
    const SRC: &str = "\
namespace zz4nh.inner
  fact b(1)
  rule rel(1) :- b(1)
end
fact holds4nh(zz4nh.inner.rel)
rule via4nh(1) :- holds4nh(zz4nh.inner.rel)
rule slot4nh(?t) :- ?t <=> zz4nh.inner.rel
";
    let mut kb = crate::common::load_kb_with(SRC);
    let goal = crate::common::query_pattern_term(&mut kb, "via4nh(?x)");
    let answered = kb
        .resolve(&[goal], &ResolveConfig::default())
        .iter()
        .filter(|s| s.is_definite())
        .count();
    assert_eq!(
        answered, 1,
        "the fact's data slot and the rule body's still spell ONE term — the row a \
         loader-side collapse would fell"
    );

    // AND THE VALUE IS THE NAME, not a `Relation` — the same thing the one-segment
    // spelling binds in this position, which is what makes the TYPE this ticket gives
    // the chain a statement about parity rather than an invented reading.
    let mut bound = crate::common::definite_unary(&mut kb, "slot4nh");
    assert_eq!(bound.len(), 1, "`slot4nh` binds exactly once; got {bound:?}");
    let bound = bound.pop().expect("checked above");
    assert!(
        kb.value_symbol(&bound).is_some(),
        "a dotted citation in a data slot still binds the NAME at run time; got {bound:?}"
    );
}

//! WI-20261030-BXMPK — A GOAL HOLDING A VALUE WITH NO TERM FORM IS CARRIED, NOT LOWERED.
//! A closure an operation returned, or a lambda written where an argument goes, reaches the
//! goal it stands in: the resolver's `ho_apply` builds the applied goal over its arguments
//! as they are, and the query lowerer keeps a leaf on the carrier it came on and makes an
//! `or` and a multi-goal branch goals over their parts (`or(…)`, `push_and(…)`). Each
//! lowered to a term before, and a part with no term form lost the goal: `?p(?f, ?r)` with
//! `?f` a closure answered nothing, as if `?p` were unbound; an operation querying a rule
//! with a function it was handed raised `malformed_query`, one undecided row.
//!
//! The contract proof's conjuncts are carried as well, and its body found an older defect
//! on the way: a body with no term form (an `if`, a lambda) asserted in a debug build and
//! read `result` as `⊥` in release; the proof now says it cannot run it (`Deferred`).
//!
//! ## Back-out
//!
//! Each part put back as it was — its lowering through `value_to_term`, a part with no term
//! form refusing the goal — under a switch of its own, one build (measured 2026-10-30):
//!
//! | put back | fails |
//! |---|---|
//! | `ho_apply`'s arguments lowered | `a_closure_reaches_the_applied_predicate`, `a_lambda_reaches_the_applied_predicate`, `a_forall_antecedent_applies_its_predicate_to_a_lambda` |
//! | a query leaf lowered (`lower_leaf`) | every `a_query_`/`a_negated_`/`a_disjunctive_` row here; `wi_prva2_pre_existing_defects_test::a_bridged_control_form_operand_reaches_the_rule` |
//! | a query leaf carried but not put in the stored form (`canonical_spine` skipped) | `a_positional_entity_leaf_meets_its_named_fact` |
//! | an `or`'s branches lowered | `a_query_or_carries_a_function`, `a_disjunctive_conjunction_carries_a_function` |
//! | a multi-goal branch's goals lowered (the synthesized rule's body) | `a_negated_conjunction_carries_a_function`, `a_disjunctive_conjunction_carries_a_function` |
//! | the contract body lowered by the asserting `occurrence_to_term` | `a_contract_over_a_body_with_no_term_form_is_deferred` (a debug-build panic) |
//!
//! The controls — [`the_applied_predicate_over_a_number_answers_either_way`],
//! [`the_queries_over_a_number_answer_either_way`] and
//! [`a_contract_requires_holding_a_lambda_is_assumed_either_way`] — pass under every one
//! of them by design. The last is the contract half of the ticket's acceptance, and is a
//! control because no program reaches the lowering it names: the loader carries every
//! contract conjunct as a term, a lambda there as its reflect term (see `contract_goal`).

use crate::common::{interp_for, load_kb_with, one_definite_int, query_unary};
use anthill_core::eval::Value;
use anthill_core::kb::proof_verify::{verify_proofs, ProofVerdict};

/// Every answer of `qn(?r)`, each asserted definite, as a string or an integer's digits.
fn answers(src: &str, qn: &str) -> Vec<String> {
    let mut kb = load_kb_with(src);
    query_unary(&mut kb, qn)
        .into_iter()
        .map(|(v, definite)| match (v, definite) {
            (Value::Str(s), true) => s,
            (Value::Int(n), true) => n.to_string(),
            (other, definite) => panic!("`{qn}` answered {other:?} (definite: {definite})"),
        })
        .collect()
}

// ── `ho_apply`: `?p(args…)` with `?p` bound to a relation ──────────────────────────────────

const HO: &str = r#"
namespace test.bxmpk.ho
  import anthill.prelude.{String, Int64}
  import anthill.prelude.PartialEq.{eq}

  operation applyThunk[Rho](f: () -> String @ {Rho}) -> String effects {Rho} = f()
  operation pureThunk() -> () -> String = lambda () -> "x"

  rule cc(?f, ?r) :- applyThunk(?f, ?r)
  rule same(?n, ?r) :- ?r <=> ?n
  rule apply2(?p, ?f, ?r) :- ?p(?f, ?r)

  rule viaClosure(?r) :- pureThunk(?f), apply2(cc, ?f, ?r)
  rule viaLambda(?r) :- apply2(cc, lambda () -> "y", ?r)
  rule viaNumber(?r) :- apply2(same, 3, ?r)
  rule notClosure(1) :- not(viaClosure("x"))
  rule notClosureY(1) :- not(viaClosure("y"))

  rule hyp(?x, ?f) :- eq(1, 2)
  rule holdsFor(?p, ?f) :- (forall(?x), ?p(?x, ?f) -: hyp(?x, ?g))
  rule forallLambda(1) :- holdsFor(hyp, lambda () -> "x")
  rule forallNumber(1) :- holdsFor(hyp, 5)

  rule ok :- true
  rule call0(?p) :- ?p()
  rule viaNullary(1) :- call0(ok)
end
"#;

#[test]
fn a_closure_reaches_the_applied_predicate() {
    assert_eq!(answers(HO, "test.bxmpk.ho.viaClosure"), ["x"]);
    assert!(
        answers(HO, "test.bxmpk.ho.notClosure").is_empty(),
        "`not(viaClosure(\"x\"))` must fail, decided"
    );
}

#[test]
fn a_lambda_reaches_the_applied_predicate() {
    assert_eq!(answers(HO, "test.bxmpk.ho.viaLambda"), ["y"]);
}

/// A `forall` antecedent `?p(?x, ?f)` is assumed as the applied goal `hyp(?x, <lambda>)`,
/// so the consequent `hyp(?x, ?g)` reads it; it stayed `ho_apply(hyp, ?x, <lambda>)`, which
/// matched nothing, and the consequent fell to `hyp`'s clause, which fails.
#[test]
fn a_forall_antecedent_applies_its_predicate_to_a_lambda() {
    assert_eq!(answers(HO, "test.bxmpk.ho.forallLambda"), ["1"]);
}

/// CONTROL: the same applications over a number, a nullary `?p()` (an entity with no
/// arguments, where the lowering made the nullary canon's `Ref`), and a negation over a
/// value the closure does not give, which holds whether the goal is reached or lost.
#[test]
fn the_applied_predicate_over_a_number_answers_either_way() {
    assert_eq!(answers(HO, "test.bxmpk.ho.viaNumber"), ["3"]);
    assert_eq!(answers(HO, "test.bxmpk.ho.forallNumber"), ["1"]);
    assert_eq!(answers(HO, "test.bxmpk.ho.viaNullary"), ["1"]);
    assert_eq!(answers(HO, "test.bxmpk.ho.notClosureY"), ["1"]);
}

// ── the query lowerer: an operation that queries with a function it was handed ───────────

const QUERY: &str = r#"
namespace test.bxmpk.query
  import anthill.prelude.{Stream, Option, Error, Int64, String, EmptyStream}
  import anthill.prelude.Stream.{splitFirst}
  import anthill.prelude.Option.{some, none}
  import anthill.reflect.{as_term, ResolveStreamFailure}
  import anthill.reflect.KB.{kb, execute}
  import anthill.reflect.LogicalQuery.{pattern_query, negation, disjunction, conjunction}

  entity Holder(f: () -> String, tag: String)
  fact Holder(tag: "t")
  entity Counted(n: Int64, tag: String)
  fact Counted(tag: "t")

  rule keep(?f, ?c) :- ?c <=> 1

  sort Driver
    operation viaRule(f: () -> String) -> Int64 effects {Error, Error[EmptyStream]} =
      keep(f).head.c
    operation leaf(f: () -> String) -> Int64 effects Error[ResolveStreamFailure] =
      match splitFirst(execute(kb(), pattern_query(term: as_term(Holder(f: f, tag: "t")))))
        case none() -> 0
        case some(_) -> 1
    operation orOne(f: () -> String) -> Int64 effects Error[ResolveStreamFailure] =
      match splitFirst(execute(kb(), disjunction(left: pattern_query(term: as_term(Holder(f: f, tag: "u"))),
                                                  right: pattern_query(term: as_term(Holder(f: f, tag: "t"))))))
        case none() -> 0
        case some(_) -> 1
    operation notBoth(f: () -> String) -> Int64 effects Error[ResolveStreamFailure] =
      match splitFirst(execute(kb(), negation(query: conjunction(left: pattern_query(term: as_term(Holder(f: f, tag: "t"))),
                                                                  right: pattern_query(term: as_term(Holder(f: f, tag: "t")))))))
        case none() -> 0
        case some(_) -> 1
    operation eitherBoth(f: () -> String) -> Int64 effects Error[ResolveStreamFailure] =
      match splitFirst(execute(kb(), disjunction(left: conjunction(left: pattern_query(term: as_term(Holder(f: f, tag: "t"))),
                                                                    right: pattern_query(term: as_term(Holder(f: f, tag: "u")))),
                                                  right: conjunction(left: pattern_query(term: as_term(Holder(f: f, tag: "t"))),
                                                                     right: pattern_query(term: as_term(Holder(f: f, tag: "t")))))))
        case none() -> 0
        case some(_) -> 1

    -- The same queries handed a number.
    operation viaRuleN(n: Int64) -> Int64 effects {Error, Error[EmptyStream]} = keep(n).head.c
    operation notBothN(n: Int64) -> Int64 effects Error[ResolveStreamFailure] =
      match splitFirst(execute(kb(), negation(query: conjunction(left: pattern_query(term: as_term(Counted(n: n, tag: "t"))),
                                                                  right: pattern_query(term: as_term(Counted(n: n, tag: "t")))))))
        case none() -> 0
        case some(_) -> 1
    operation eitherBothN(n: Int64) -> Int64 effects Error[ResolveStreamFailure] =
      match splitFirst(execute(kb(), disjunction(left: conjunction(left: pattern_query(term: as_term(Counted(n: n, tag: "t"))),
                                                                    right: pattern_query(term: as_term(Counted(n: n, tag: "u")))),
                                                  right: pattern_query(term: as_term(Counted(n: n, tag: "t"))))))
        case none() -> 0
        case some(_) -> 1

    -- Called from the interpreter, each hands the query a CLOSURE.
    operation viaRuleC() -> Int64 effects {Error, Error[EmptyStream]} = viaRule(lambda () -> "x")
    operation leafC() -> Int64 effects Error[ResolveStreamFailure] = leaf(lambda () -> "x")
    operation orOneC() -> Int64 effects Error[ResolveStreamFailure] = orOne(lambda () -> "x")
    operation notBothC() -> Int64 effects Error[ResolveStreamFailure] = notBoth(lambda () -> "x")
    operation eitherBothC() -> Int64 effects Error[ResolveStreamFailure] = eitherBoth(lambda () -> "x")
  end

  -- Called from a rule body, each hands the query the LAMBDA OCCURRENCE (the bridge passes
  -- an operand on the carrier the resolver proved it on).
  rule rViaRule(?r) :- ?r <=> Driver.viaRule(lambda () -> "x")
  rule rLeaf(?r) :- ?r <=> Driver.leaf(lambda () -> "x")
  rule rOrOne(?r) :- ?r <=> Driver.orOne(lambda () -> "x")
  rule rNotBoth(?r) :- ?r <=> Driver.notBoth(lambda () -> "x")
  rule rEitherBoth(?r) :- ?r <=> Driver.eitherBoth(lambda () -> "x")
  rule rViaRuleN(?r) :- ?r <=> Driver.viaRuleN(5)
  rule rNotBothN(?r) :- ?r <=> Driver.notBothN(5)
  rule rEitherBothN(?r) :- ?r <=> Driver.eitherBothN(5)
end
"#;

/// `Driver.<op>()` called from the interpreter, as an integer.
fn interp_int(op: &str) -> i64 {
    let mut interp = interp_for(QUERY);
    match interp.call(&format!("test.bxmpk.query.Driver.{op}"), &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{op}` returned {other:?}"),
    }
}

fn rule_int(name: &str) -> Option<i64> {
    let mut kb = load_kb_with(QUERY);
    one_definite_int(&mut kb, &format!("test.bxmpk.query.{name}"))
}

/// `keep(f).head.c` queries the rule with the function: `keep(<f>, ?c)`.
#[test]
fn a_query_leaf_carries_a_function() {
    assert_eq!(rule_int("rViaRule"), Some(1), "a lambda, through the bridge");
    assert_eq!(interp_int("viaRuleC"), 1, "a closure, from the interpreter");
    assert_eq!(rule_int("rLeaf"), Some(1), "an entity holding a lambda");
    assert_eq!(interp_int("leafC"), 1, "an entity holding a closure");
}

/// `Holder(f, "u") | Holder(f, "t")`: the second branch matches the fact.
#[test]
fn a_query_or_carries_a_function() {
    assert_eq!(rule_int("rOrOne"), Some(1));
    assert_eq!(interp_int("orOneC"), 1);
}

/// `not(Holder(f, "t"), Holder(f, "t"))`: the conjunction holds, so the negation fails.
#[test]
fn a_negated_conjunction_carries_a_function() {
    assert_eq!(rule_int("rNotBoth"), Some(0));
    assert_eq!(interp_int("notBothC"), 0);
}

/// `(Holder(f, "t"), Holder(f, "u")) | (Holder(f, "t"), Holder(f, "t"))`: the second holds.
#[test]
fn a_disjunctive_conjunction_carries_a_function() {
    assert_eq!(rule_int("rEitherBoth"), Some(1));
    assert_eq!(interp_int("eitherBothC"), 1);
}

/// A leaf a host builtin or a bridge built POSITIONALLY is put in the form the fact is
/// stored in, as `value_to_term` did while it lowered: `Counted(5, "t")` meets
/// `fact Counted(tag: "t")`, and a positional entity nested in a tuple too.
#[test]
fn a_positional_entity_leaf_meets_its_named_fact() {
    let mut kb = load_kb_with(QUERY);
    let counted = kb.try_resolve_symbol("test.bxmpk.query.Counted").expect("Counted");
    let pq = kb
        .try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query")
        .expect("pattern_query");
    let term = kb.intern("term");
    let positional = Value::Entity {
        functor: counted,
        pos: vec![Value::Int(5), Value::Str("t".into())].into(),
        named: Vec::new().into(),
    };
    let query = Value::Entity {
        functor: pq,
        pos: Vec::new().into(),
        named: vec![(term, positional)].into(),
    };
    let mut stream = kb.execute_logical_query(&query).expect("the leaf lowers");
    let mut rows = 0;
    while let Some((_, rest)) = stream.split_first(&mut kb).expect("no fault") {
        rows += 1;
        stream = rest;
    }
    assert_eq!(rows, 1, "`Counted(5, \"t\")` is `Counted(n: 5, tag: \"t\")`");
}

/// CONTROL: the same query shapes over a number, which lowers.
#[test]
fn the_queries_over_a_number_answer_either_way() {
    assert_eq!(rule_int("rViaRuleN"), Some(1));
    assert_eq!(rule_int("rNotBothN"), Some(0));
    assert_eq!(rule_int("rEitherBothN"), Some(1));
}

// ── the contract proof ───────────────────────────────────────────────────────────────────

/// Two programs, so a proof that panics under a back-out takes no other row with it.
const CONTRACT_BODY: &str = r#"
namespace test.bxmpk.ct
  import anthill.prelude.{String, Int64}
  import anthill.prelude.PartialEq.{eq}

  sort Colour
    entity red
    entity green
  end

  rule known1(?x) :- eq(?x, 0)
  rule anything(?f) :- eq(1, 1)

  operation lamBody(x: Int64) -> () -> String
    ensures anything(result)
    = lambda () -> "x"
  operation ifBody(x: Int64) -> Int64
    ensures known1(result)
    = if eq(x, 1) then 0 else 0
  operation matchBody(c: Colour) -> Int64
    ensures known1(result)
    = match c case red -> 0 case green -> 0
  operation letBody(x: Int64) -> Int64
    ensures known1(result)
    =
      let y = x
      0
  proof lamBody.ensures by derivation end
  proof ifBody.ensures by derivation end
  proof matchBody.ensures by derivation end
  proof letBody.ensures by derivation end
end
"#;

const CONTRACT_REQUIRES: &str = r#"
namespace test.bxmpk.ct
  import anthill.prelude.{String, Int64}
  import anthill.prelude.PartialEq.{eq}

  rule known(?x, ?f) :- eq(?x, 0)
  rule known1(?x) :- eq(?x, 0)

  operation needsLam(x: Int64) -> Int64
    requires known(x, lambda () -> "x")
    ensures known(result, lambda () -> "x")
    = x
  operation besideLam(x: Int64) -> Int64
    requires known1(x), known(x, lambda () -> "x")
    ensures known1(result)
    = x
  proof needsLam.ensures by derivation end
  proof besideLam.ensures by derivation end
end
"#;

fn contract_verdicts(src: &str) -> Vec<(String, ProofVerdict)> {
    let mut kb = load_kb_with(src);
    verify_proofs(&mut kb)
        .into_iter()
        .filter(|r| r.rule_qn.starts_with("test.bxmpk.ct."))
        .map(|r| (r.rule_qn, r.verdict))
        .collect()
}

fn verdict(all: &[(String, ProofVerdict)], op: &str) -> ProofVerdict {
    let qn = format!("test.bxmpk.ct.{op}.ensures");
    all.iter()
        .find(|(q, _)| *q == qn)
        .unwrap_or_else(|| panic!("no verdict for `{qn}` in {all:?}"))
        .1
        .clone()
}

/// The proof reads `result` as the body's term; a body with none is not run.
#[test]
fn a_contract_over_a_body_with_no_term_form_is_deferred() {
    let all = contract_verdicts(CONTRACT_BODY);
    for op in ["lamBody", "ifBody", "matchBody", "letBody"] {
        match verdict(&all, op) {
            ProofVerdict::Deferred { reason } => {
                assert!(reason.contains("no term form"), "`{op}`: {reason}")
            }
            other => panic!("`{op}` is not deferred: {other:?}"),
        }
    }
}

/// CONTROL: a `requires` holding a lambda is assumed, alone and beside another conjunct.
#[test]
fn a_contract_requires_holding_a_lambda_is_assumed_either_way() {
    let all = contract_verdicts(CONTRACT_REQUIRES);
    assert_eq!(verdict(&all, "needsLam"), ProofVerdict::Discharged);
    assert_eq!(verdict(&all, "besideLam"), ProofVerdict::Discharged);
}

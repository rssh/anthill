//! WI-20261109-JEE0E (proposal 051 Phase 2, 4 of 4) — `neq` is a body in `PartialEq`,
//! `Bool.not(eq(a, b))`.
//!
//! Before, `PartialEq.neq` was `@[host_implemented]` beside an inert law `rule neq(?a, ?b)
//! <=> not(eq(?a, ?b))`: the interpreter's `builtin_neq` was `!semantic_equal(a, b)` and the
//! resolver's `SemNeq` its `sem_eq_core` negated, so `neq` found `eq` from the value through
//! the equality index at every call. Measured by running this file on 3933f7a7: every typed
//! `neq` call is unclassified, and `ensures not(neq(x, x))` over `x: Float` is discharged,
//! though `x` may be `nan`.
//!
//! Now (1) `PartialEq` declares `operation neq(a: T, b: T) -> Bool = Bool.not(eq(a, b))`, in
//! place of the host operation, its binding and the law; `SemNeq` and `builtin_neq` are gone.
//! A typed call is the body entered with the dictionary of the carrier its types resolve, and
//! the body's `eq(a, b)` is that dictionary's member (the interpreter's step 2b, as for a
//! receiver-less sibling): traced on 2026-11-10 at `sem_eq_dispatch_target`, the carrier and
//! generic rows read the equality index nowhere, where they read it 10 and 4 times with the
//! member taken from the value. (2) A `neq` goal no type reached is read as `not(eq(a, b))`
//! (`KnowledgeBase::untyped_neq_as_not_eq`), with `eq`'s verdicts. (3) A contract proof's
//! eigenvariable carries whether its parameter is equal to itself by `Eq`'s law — its declared
//! type provides `Eq`, or the operation or its sort requires `Eq` at it
//! (`OpaqueSkolems::not_self_equal`); an `eq` success resting on one that is not is undecided,
//! as its failure already was. And a comparison written with its result column answers what
//! its two operands' comparison answers there (`comparison_of_result_column`): `eq(x, 1,
//! false)` was discharged, the folded `Success` read as forced. (4) In a proof from Γ, an `eq` test whose left
//! operand is an unbound variable takes no guarded `=` law as a premise
//! (`SearchStream::guarded_laws_answer`). (5) `Relation.guarded_of` admits `PartialEq.neq` as
//! a condition atom. Outside this file: the SMT lowering reads `neq` as the negation of `eq`
//! (anthill-smt-gen `uninterpreted_call`), and `BRIDGE_REENTRY_CAP` is 8, its canary moved to
//! a circle through an `eq` written as clauses (wi625).
//!
//! ## Back-out
//!
//! Measured 2026-11-10, one part at a time by a temporary switch, over the whole
//! `anthill-core` crate (10 774 rows):
//!
//! - the parent tree, this file run there: `neq_at_a_carrier_answers_through_its_eq` and
//!   `neq_at_each_primitive_negates_its_eq` (each call unclassified), and
//!   `a_contract_reads_neq_through_eq_at_the_parameters_type` (`Float`);
//! - (2) out: the contract row (`ensures neq(x, 1)` discharged), the three skolem rows of
//!   `gamma_verdict_three_valued_test`, and `kb::resolve`'s `untyped_neq_succeeds_on_different`;
//! - (3) out: the contract row (`eq(x, x)` and `not(neq(x, x))` discharged at `Float`); the
//!   requirement half out, or the result-column half:
//!   `a_contract_reads_the_law_at_the_parameters_requirements`;
//! - (4) out: `a_bool_operation_over_an_unbound_argument_is_no_premise_search` hangs (measured
//!   to 120 s; on the parent tree the same program loads in 1.6 s, its laws' `neq(?k, ?k2)`
//!   guards then a builtin that waited);
//! - (5) out: the seven `wi730_boolean_condition_test` rows that filter with `!=`;
//! - the SMT lowering out (`anthill-cli`): four `wi_zz7ph_law_lowering_test` rows, the verdict
//!   row among them — `neq(?a, ?a)` under `requires Eq[T = T]` is `sat`.
//!
//! PASS EITHER WAY, BY DESIGN: (1)'s dictionary member in step 2b moves no answer — with the
//! member taken from the value the same `eq` answers; the trace above is what tells them
//! apart. The untyped and generic rows pass on the parent tree as well, answering by value.

use anthill_core::eval::{Interpreter, Value};
use anthill_core::kb::node_occurrence::{for_each_child, ApplyDispatch, Expr, NodeOccurrence};
use anthill_core::kb::KnowledgeBase;
use std::rc::Rc;

use crate::common::{interp_for, query_unary};

const NEQ: &str = "anthill.prelude.PartialEq.neq";

/// `Pt`'s `eq` compares `x` alone, so `pt(1, 2)` equals `pt(1, 9)` and only a `neq` that
/// reads `Pt.eq` says they are not apart.
const PT: &str = r#"
  sort Pt
    entity pt(x: Int64, y: Int64)
    operation eq(a: Self, b: Self) -> Bool =
      match a
        case pt(ax, _) ->
          match b
            case pt(bx, _) -> PartialEq.eq(ax, bx)
    provides PartialEq[Self]
    provides Eq[Self]
  end
"#;

fn program(ns: &str, body: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.{{Int64, Bool, Float, String, BigInt, PartialEq, Eq}}
  import anthill.prelude.Float.{{nan, neg}}
  import anthill.prelude.BigInt.{{to_bigint}}
{PT}
{body}
end
"#
    )
}

fn call_bool(interp: &mut Interpreter, op: &str) -> bool {
    match interp.call(op, &[]) {
        Ok(Value::Bool(b)) => b,
        other => panic!("`{op}`: expected a Bool, got {other:?}"),
    }
}

/// The one definite `Bool` the unary relation `qn` answers.
fn rule_bool(interp: &mut Interpreter, qn: &str) -> bool {
    match query_unary(interp.kb_mut(), qn).as_slice() {
        [(Value::Bool(b), true)] => *b,
        other => panic!("`{qn}`: expected one definite Bool, got {other:?}"),
    }
}

/// Is `pattern` proved: `Some(true)` for one definite solution, `Some(false)` for none,
/// `None` while undecided.
fn holds(kb: &mut KnowledgeBase, pattern: &str) -> Option<bool> {
    let goal = crate::common::query_pattern_term(kb, pattern);
    let got = kb.resolve(&[goal], &anthill_core::kb::resolve::ResolveConfig::default());
    match got.as_slice() {
        [] => Some(false),
        [one] if one.is_definite() => Some(true),
        [_] => None,
        _ => panic!("`{pattern}`: {} rows", got.len()),
    }
}

/// What the typer decided for each call of `PartialEq.neq` under `roots`.
fn decided(kb: &KnowledgeBase, roots: &[Rc<NodeOccurrence>]) -> Vec<String> {
    let mut out = Vec::new();
    let mut stack: Vec<Rc<NodeOccurrence>> = roots.to_vec();
    while let Some(o) = stack.pop() {
        let Some(expr) = o.as_expr() else { continue };
        if let Expr::Apply { functor, .. } = expr {
            if kb.qualified_name_of(*functor) == NEQ {
                out.push(match o.apply_dispatch() {
                    ApplyDispatch::Pin(t) => format!("pin {}", kb.qualified_name_of(t)),
                    ApplyDispatch::NeedsDict(t) => format!("dict {}", kb.qualified_name_of(t)),
                    ApplyDispatch::Unclassified => "unclassified".to_string(),
                });
            }
        }
        for_each_child(expr, |c| stack.push(Rc::clone(c)));
    }
    out
}

/// A typed call of `neq`: the body in the spec, entered with the dictionary of the carrier
/// the call's types resolve.
fn the_body() -> Vec<String> {
    vec![format!("dict {NEQ}")]
}

fn decided_in_op(kb: &KnowledgeBase, op: &str) -> Vec<String> {
    let sym = kb.try_resolve_symbol(op).unwrap_or_else(|| panic!("`{op}` resolves"));
    let body = kb.op_body_node(sym).unwrap_or_else(|| panic!("`{op}` has a body"));
    decided(kb, &[Rc::clone(body)])
}

fn decided_in_rule(kb: &KnowledgeBase, qn: &str) -> Vec<String> {
    let roots: Vec<Rc<NodeOccurrence>> = kb
        .rule_ids_by_qn(qn)
        .into_iter()
        .flat_map(|rid| kb.rule_body_nodes(rid).to_vec())
        .collect();
    decided(kb, &roots)
}

const NS_PT: &str = "test.jee0e.carrier";

/// `neq` at `Pt` answers through `Pt.eq`: `pt(1, 2)` and `pt(1, 9)` are not apart, `pt(1, 2)`
/// and `pt(2, 2)` are — in an operation body, as `!=`, as a rule goal with its result
/// column, as `!=` in a rule body, and at a head that types its variables.
#[test]
fn neq_at_a_carrier_answers_through_its_eq() {
    let src = program(
        NS_PT,
        r#"
  operation same() -> Bool = PartialEq.neq(pt(1, 2), pt(1, 9))
  operation apart() -> Bool = PartialEq.neq(pt(1, 2), pt(2, 2))
  operation sameBang() -> Bool = pt(1, 2) != pt(1, 9)
  operation apartBang() -> Bool = pt(1, 2) != pt(2, 2)
  rule sameGoal(?r) :- PartialEq.neq(pt(1, 2), pt(1, 9), ?r)
  rule apartGoal(?r) :- PartialEq.neq(pt(1, 2), pt(2, 2), ?r)
  rule sameBangGoal() :- pt(1, 2) != pt(1, 9)
  rule apartBangGoal() :- pt(1, 2) != pt(2, 2)
  rule typedApart(?a: Pt, ?b: Pt) :- ?a != ?b
  rule typedSame() :- typedApart(pt(1, 2), pt(1, 9))
  rule typedDiffer() :- typedApart(pt(1, 2), pt(2, 9))
"#,
    );
    let mut interp = interp_for(&src);
    for op in ["same", "apart", "sameBang", "apartBang"] {
        assert_eq!(decided_in_op(interp.kb(), &format!("{NS_PT}.{op}")), the_body(), "{op}");
    }
    for rule in ["sameGoal", "apartGoal", "sameBangGoal", "apartBangGoal", "typedApart"] {
        assert_eq!(decided_in_rule(interp.kb(), &format!("{NS_PT}.{rule}")), the_body(), "{rule}");
    }
    let mut op = |name: &str| call_bool(&mut interp, &format!("{NS_PT}.{name}"));
    assert!(!op("same"), "`Pt.eq` compares `x`: not apart");
    assert!(op("apart"));
    assert!(!op("sameBang"));
    assert!(op("apartBang"));
    assert!(!rule_bool(&mut interp, &format!("{NS_PT}.sameGoal")));
    assert!(rule_bool(&mut interp, &format!("{NS_PT}.apartGoal")));
    let kb = interp.kb_mut();
    assert_eq!(holds(kb, &format!("{NS_PT}.sameBangGoal()")), Some(false));
    assert_eq!(holds(kb, &format!("{NS_PT}.apartBangGoal()")), Some(true));
    assert_eq!(holds(kb, &format!("{NS_PT}.typedSame()")), Some(false));
    assert_eq!(holds(kb, &format!("{NS_PT}.typedDiffer()")), Some(true));
}

const NS_PRIM: &str = "test.jee0e.prim";

/// `neq` at each primitive carrier is the negation of that carrier's `eq`: `Float`'s IEEE
/// (`nan` apart from itself, the two zeros not apart), the literal compare of `Int64`,
/// `String`, `Bool` and `BigInt` — in both bodies.
#[test]
fn neq_at_each_primitive_negates_its_eq() {
    let src = program(
        NS_PRIM,
        r#"
  operation intApart() -> Bool = PartialEq.neq(1, 2)
  operation intSame() -> Bool = PartialEq.neq(3, 3)
  operation floatNan() -> Bool = PartialEq.neq(nan, nan)
  operation floatZeros() -> Bool = PartialEq.neq(neg(0.0), 0.0)
  operation stringSame() -> Bool = "a" != "a"
  operation boolApart() -> Bool = true != false
  operation bigSame() -> Bool = PartialEq.neq(to_bigint(7), to_bigint(7))
  rule intApartGoal(?r) :- PartialEq.neq(1, 2, ?r)
  rule intSameGoal(?r) :- PartialEq.neq(3, 3, ?r)
  rule floatNanGoal(?r) :- PartialEq.neq(nan, nan, ?r)
  rule floatZerosGoal(?r) :- PartialEq.neq(neg(0.0), 0.0, ?r)
  rule stringSameGoal(?r) :- PartialEq.neq("a", "a", ?r)
  rule boolApartGoal(?r) :- PartialEq.neq(true, false, ?r)
  rule bigSameGoal(?r) :- PartialEq.neq(to_bigint(7), to_bigint(7), ?r)
  rule nanBang() :- nan != nan
"#,
    );
    let mut interp = interp_for(&src);
    for op in ["intApart", "floatNan", "stringSame"] {
        assert_eq!(decided_in_op(interp.kb(), &format!("{NS_PRIM}.{op}")), the_body(), "{op}");
    }
    for rule in ["intApartGoal", "floatNanGoal", "nanBang"] {
        assert_eq!(decided_in_rule(interp.kb(), &format!("{NS_PRIM}.{rule}")), the_body(), "{rule}");
    }
    for (name, want) in [
        ("intApart", true),
        ("intSame", false),
        ("floatNan", true),
        ("floatZeros", false),
        ("stringSame", false),
        ("boolApart", true),
        ("bigSame", false),
    ] {
        assert_eq!(call_bool(&mut interp, &format!("{NS_PRIM}.{name}")), want, "{name}");
        let goal = format!("{NS_PRIM}.{name}Goal");
        if interp.kb().try_resolve_symbol(&goal).is_some() {
            assert_eq!(rule_bool(&mut interp, &goal), want, "{name}Goal");
        }
    }
    assert_eq!(holds(interp.kb_mut(), &format!("{NS_PRIM}.nanBang()")), Some(true));
}

const NS_GEN: &str = "test.jee0e.gen";

/// A generic caller holding `PartialEq[T = A]` hands `neq` its dictionary: at `Pt` the body
/// reads `Pt.eq`, at `Int64` the literal compare — from an operation and from a rule that
/// declares the requirement.
#[test]
fn a_generic_caller_hands_neq_its_dictionary() {
    let src = program(
        NS_GEN,
        r#"
  operation apartBy[A](a: A, b: A) -> Bool requires PartialEq[T = A] = PartialEq.neq(a, b)
  operation ptSame() -> Bool = apartBy(pt(1, 2), pt(1, 9))
  operation ptApart() -> Bool = apartBy(pt(1, 2), pt(2, 9))
  operation intApart() -> Bool = apartBy(1, 2)
  rule apartR[A](?a: A, ?b: A, ?r) :- PartialEq[T = A], PartialEq.neq(?a, ?b, ?r)
  rule ptSameGoal(?r) :- apartR(pt(1, 2), pt(1, 9), ?r)
  rule ptApartGoal(?r) :- apartR(pt(1, 2), pt(2, 9), ?r)
  rule intApartGoal(?r) :- apartR(1, 2, ?r)
"#,
    );
    let mut interp = interp_for(&src);
    for (name, want) in [("ptSame", false), ("ptApart", true), ("intApart", true)] {
        assert_eq!(call_bool(&mut interp, &format!("{NS_GEN}.{name}")), want, "{name}");
        assert_eq!(rule_bool(&mut interp, &format!("{NS_GEN}.{name}Goal")), want, "{name}Goal");
    }
}

const NS_UNTYPED: &str = "test.jee0e.untyped";

/// A `neq` goal no type reaches — at a variable the clause leaves open, with no dictionary
/// of `PartialEq` declared — is read at the type its values carry when it runs (073 §6.2,
/// no typed caller): `Pt`'s `eq`, IEEE for two floats, the literal compare; a delay while an
/// operand is unbound.
#[test]
fn an_untyped_neq_goal_runs_at_the_type_its_values_carry() {
    let src = program(
        NS_UNTYPED,
        r#"
  import anthill.prelude.PartialEq.{neq}
  rule differ(?a, ?b) :- neq(?a, ?b)
  rule bang(?a, ?b) :- ?a != ?b
  rule nans() :- differ(nan, nan)
  rule ints() :- differ(1, 5)
  rule intsSame() :- bang(5, 5)
  rule strs() :- bang("a", "a")
  rule pts() :- differ(pt(1, 2), pt(1, 9))
  rule ptsApart() :- bang(pt(1, 2), pt(2, 9))
"#,
    );
    let mut kb = crate::common::load_kb_with(&src);
    for (pattern, want) in [
        ("nans()", Some(true)),
        ("ints()", Some(true)),
        ("intsSame()", Some(false)),
        ("strs()", Some(false)),
        ("pts()", Some(false)),
        ("ptsApart()", Some(true)),
        ("differ(?x, 3)", None),
    ] {
        let pattern = format!("{NS_UNTYPED}.{pattern}");
        assert_eq!(holds(&mut kb, &pattern), want, "`{pattern}`");
    }
}

/// A contract over a parameter is proved for every input, so an `ensures` that compares the
/// parameter is undecided unless the comparison is forced. `neq(x, 1)` is not (`x` might be
/// `1`); `neq(x, x)` is false wherever `Eq`'s law holds, so `not(neq(x, x))` is proved at
/// `Int64` and undecided at `Float`, whose `nan` is not equal to itself — as `eq(x, x)` is.
#[test]
fn a_contract_reads_neq_through_eq_at_the_parameters_type() {
    use anthill_core::kb::proof_verify::{verify_proofs, ProofVerdict};
    fn verdict(ns: &str, ty: &str, ensures: &str) -> ProofVerdict {
        let src = format!(
            r#"namespace {ns}
  import anthill.prelude.{{Int64, Float, Bool, PartialEq}}
  import anthill.prelude.PartialEq.{{eq, neq}}
  sort Box
    entity box(value: {ty})
    operation wrap(x: {ty}) -> Box
      ensures {ensures}
      = box(value: x)
    proof wrap.ensures by derivation end
  end
end
"#
        );
        let mut kb = crate::common::load_kb_with(&src);
        verify_proofs(&mut kb)
            .into_iter()
            .find(|r| r.rule_qn.ends_with("wrap.ensures"))
            .expect("the proof is reported")
            .verdict
    }
    let undecided = |v: &ProofVerdict| {
        matches!(v, ProofVerdict::Failed { reason } if reason.contains("could not be DECIDED"))
    };
    let refuted = |v: &ProofVerdict| {
        matches!(v, ProofVerdict::Failed { reason } if reason.contains("is not derivable"))
    };
    let mut n = 0;
    let mut at = |ty: &str, ensures: &str| {
        n += 1;
        verdict(&format!("test.jee0e.contract{n}"), ty, ensures)
    };
    for ty in ["Int64", "Float"] {
        let v = at(ty, "neq(x, 1)");
        assert!(undecided(&v), "{ty}: `neq(x, 1)` rests on `x`; got {v:?}");
        let v = at(ty, "x != 1");
        assert!(undecided(&v), "{ty}: `x != 1`; got {v:?}");
    }
    let v = at("Int64", "neq(x, x)");
    assert!(refuted(&v), "`Eq`'s law: `x` is equal to itself; got {v:?}");
    let v = at("Float", "neq(x, x)");
    assert!(undecided(&v), "`x` might be `nan`, apart from itself; got {v:?}");
    let v = at("Int64", "not(neq(x, x))");
    assert!(matches!(v, ProofVerdict::Discharged), "Int64 provides `Eq`; got {v:?}");
    let v = at("Int64", "eq(x, x)");
    assert!(matches!(v, ProofVerdict::Discharged), "Int64 provides `Eq`; got {v:?}");
    let v = at("Float", "not(neq(x, x))");
    assert!(undecided(&v), "`x` might be `nan`; got {v:?}");
    let v = at("Float", "eq(x, x)");
    assert!(undecided(&v), "`x` might be `nan`; got {v:?}");
}


/// A precondition over an argument nothing has bound is not provable at the call, and the
/// call is refused — for a Bool operation with a body as for any goal (`nonZero(?n)`'s Bool
/// view is `eq(nonZero(?n), true)`, and the call cannot run). In a proof from Γ an `eq` test
/// whose left operand is unbound takes no guarded `=` law as a premise: the call's placeholder
/// would be bound to each law's left side, and `Map`'s laws, whose guards read `neq(?k, ?k2)`
/// as `not(eq(?k, ?k2))`, would be met again without end.
#[test]
fn a_bool_operation_over_an_unbound_argument_is_no_premise_search() {
    let src = r#"
namespace test.jee0e.unbound
  import anthill.prelude.{Int64, Bool, PartialEq}
  operation nonZero(n: Int64) -> Bool = Bool.not(PartialEq.eq(n, 0))
  sort Box
    entity box(value: Int64)
    operation guarded(b: Box, n: Int64) -> Int64
      requires nonZero(n)
      = n
  end
  operation caller(b: Box, n: Int64) -> Int64 =
    ?b.guarded(?n)
end
"#;
    let errs = crate::common::load_errors_of(src);
    assert!(
        errs.iter().any(|e| e.contains("expected precondition `nonZero(?n)` provable at the call site")),
        "{errs:?}"
    );
}

/// The law at a contract's parameter is read off its declared type and off what the operation
/// and its sort require of it: under `requires Eq[T = T]` an abstract `x: T` is equal to itself
/// and `eq(result.value, x)` is proved; under `requires PartialEq[T = T]` alone it is not. A
/// comparison written with its result column answers what its comparison answers:
/// `neq(x, 1, true)` and `eq(x, 1, false)` rest on `x`, and are undecided.
#[test]
fn a_contract_reads_the_law_at_the_parameters_requirements() {
    use anthill_core::kb::proof_verify::{verify_proofs, ProofVerdict};
    fn verdict(ns: &str, scope: &str, ty: &str, ensures: &str) -> ProofVerdict {
        let src = format!(
            r#"namespace {ns}
  import anthill.prelude.{{Int64, Bool, PartialEq}}
  import anthill.prelude.PartialEq.{{eq, neq}}
  sort Box
    {scope}
    entity box(value: {ty})
    operation wrap(x: {ty}) -> Box
      ensures {ensures}
      = box(value: x)
    proof wrap.ensures by derivation end
  end
end
"#
        );
        let mut kb = crate::common::load_kb_with(&src);
        verify_proofs(&mut kb)
            .into_iter()
            .find(|r| r.rule_qn.ends_with("wrap.ensures"))
            .expect("the proof is reported")
            .verdict
    }
    let undecided = |v: &ProofVerdict| {
        matches!(v, ProofVerdict::Failed { reason } if reason.contains("could not be DECIDED"))
    };
    let lawful = "sort T = ?\n    requires anthill.prelude.Eq[T = T]";
    let partial = "sort T = ?\n    requires anthill.prelude.PartialEq[T = T]";
    let v = verdict("test.jee0e.law1", lawful, "T", "eq(result.value, x)");
    assert!(matches!(v, ProofVerdict::Discharged), "`Eq[T]` is required; got {v:?}");
    let v = verdict("test.jee0e.law2", partial, "T", "eq(result.value, x)");
    assert!(undecided(&v), "`PartialEq[T]` alone gives no law; got {v:?}");
    for (n, ensures) in [(3, "neq(x, 1, true)"), (4, "eq(x, 1, false)")] {
        let v = verdict(&format!("test.jee0e.law{n}"), "", "Int64", ensures);
        assert!(undecided(&v), "`{ensures}` rests on `x`; got {v:?}");
    }
}

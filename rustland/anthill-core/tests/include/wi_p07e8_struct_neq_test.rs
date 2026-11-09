//! Proposal 051 phase 2 (1 of 4), WI-20261109-P07E8 — `!==`, the structural inequality
//! test: `anthill.kernel.struct_neq`, the negation of `===` (`struct_eq`) where `===`
//! decides, and undecided where `===` is.
//!
//! Before this ticket a `!==` was a syntax error (`syntax error near `= ?``, measured on
//! the parent's CLI): the lexer read `!=` and then a stray `=`. Each row's doc names the
//! parts whose back-out fails it, measured one at a time by temporary switches, now gone.
//!
//! With the resolver's `StructNeq` tag not registered, the ground-pair, value-slot,
//! unbound-operand, head and capture rows still pass, by design: a `struct_neq` goal is then an application of a `@[host_implemented]`
//! operation, which the interpreter's function answers, and delays while an argument is
//! unbound. What the tag adds is the verdict over a parameter: without it `x !== 1`
//! discharges as a contract.

use anthill_core::eval::Value;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::KnowledgeBase;

const SRC: &str = r#"
namespace p07e8
  import anthill.prelude.{Int64, Float, Bool}
  sort Tag
    entity tag(n: Int64)
  end
  rule apart(?x, ?y) :- ?x !== ?y
  rule nanApart() :- Float.nan !== Float.nan
  rule nanUnequal() :- Float.nan != Float.nan
  operation opApart(a: Int64, b: Int64) -> Bool = a !== b
  operation opTagApart(a: Int64, b: Int64) -> Bool = tag(n: a) !== tag(n: b)
  operation opNanApart() -> Bool = Float.nan !== Float.nan
  operation opNanUnequal() -> Bool = Float.nan != Float.nan
  rule asValue(?b) :- ?b <=> (1 !== 2)
  rule asValueSame(?b) :- ?b <=> (1 !== 1)
  rule unbound() :- ?x !== 1
  rule boundLater() :- ?x !== 1, ?x <=> 2
  rule boundLaterSame() :- ?x !== 1, ?x <=> 1
  rule neqColumn(?r) :- anthill.kernel.struct_neq(1, 2, ?r)
  rule neqColumnSame(?r) :- anthill.kernel.struct_neq(1, 1, ?r)
  rule eqColumn(?r) :- anthill.kernel.struct_eq(1, 2, ?r)
end
"#;

/// Is `pattern` proved: `Some(true)` for one definite solution, `Some(false)` for none,
/// `None` while undecided (a conditional answer).
fn holds(kb: &mut KnowledgeBase, pattern: &str) -> Option<bool> {
    let goal = crate::common::query_pattern_term(kb, pattern);
    let got = kb.resolve(&[goal], &ResolveConfig::default());
    match got.as_slice() {
        [] => Some(false),
        [one] if one.is_definite() => Some(true),
        _ => None,
    }
}

fn call_bool(interp: &mut anthill_core::eval::Interpreter, op: &str, args: &[Value]) -> bool {
    use anthill_core::kb::term_view::TermView;
    let v = interp
        .call(op, args)
        .unwrap_or_else(|e| panic!("{op} must evaluate: {e:?}"));
    v.literal_bool(interp.kb())
        .unwrap_or_else(|| panic!("{op} must answer a Bool, got {v:?}"))
}

/// `!==` answers the negation of `===` on a ground pair, written in a rule body, an
/// operation body and a query: equal Int64s, unequal ones, entities, and `nan` — which
/// `===` reads structurally, so `nan !== nan` is false while the semantic `nan != nan` is
/// true. Fails with the interpreter's `kernel_struct_neq` answering as `===`.
#[test]
fn a_ground_pair_answers_the_negation_in_every_body() {
    let mut kb = crate::common::load_kb_with(SRC);
    for (pattern, want) in [
        ("p07e8.apart(1, 2)", true),
        ("p07e8.apart(3, 3)", false),
        ("p07e8.apart(p07e8.Tag.tag(n: 1), p07e8.Tag.tag(n: 2))", true),
        ("p07e8.apart(p07e8.Tag.tag(n: 1), p07e8.Tag.tag(n: 1))", false),
        ("p07e8.nanApart()", false),
        ("p07e8.nanUnequal()", true),
        ("1 !== 2", true),
        ("3 !== 3", false),
    ] {
        assert_eq!(holds(&mut kb, pattern), Some(want), "`{pattern}`");
    }

    let mut interp = crate::common::interp_for(SRC);
    for (op, args, want) in [
        ("p07e8.opApart", vec![Value::Int(1), Value::Int(2)], true),
        ("p07e8.opApart", vec![Value::Int(3), Value::Int(3)], false),
        ("p07e8.opTagApart", vec![Value::Int(1), Value::Int(2)], true),
        ("p07e8.opTagApart", vec![Value::Int(1), Value::Int(1)], false),
        ("p07e8.opNanApart", vec![], false),
        ("p07e8.opNanUnequal", vec![], true),
    ] {
        assert_eq!(call_bool(&mut interp, op, &args), want, "{op}{args:?}");
    }
}

/// A `!==` written where a value goes is its `Bool`, as a `===` is: `?b <=> (1 !== 2)`
/// binds `?b` to `true`. Fails with `StructNeq` taken out of the tests `evaluate.rs` reads
/// as values: the comparison is then a goal held as data, and the answer is not a `Bool`.
#[test]
fn a_comparison_in_a_value_slot_is_its_bool() {
    let mut kb = crate::common::load_kb_with(SRC);
    for (relation, want) in [("p07e8.asValue", true), ("p07e8.asValueSame", false)] {
        let rows = crate::common::query_unary(&mut kb, relation);
        assert_eq!(rows.len(), 1, "{relation}: one answer, got {rows:?}");
        let (value, definite) = &rows[0];
        assert!(*definite, "{relation}: a definite answer, got {rows:?}");
        assert!(
            matches!(value, Value::Bool(b) if *b == want),
            "{relation}: `{want}`, got {value:?}"
        );
    }
}

/// At three arguments the third is the result column, bound to the `Bool` the test decided,
/// as `PartialEq.eq`/`neq` read theirs. Fails without the column read in the resolver: the
/// `struct_neq` rows then succeed with `?r` unbound and the `struct_eq` row has no answer.
#[test]
fn a_third_argument_is_the_result_column() {
    let mut kb = crate::common::load_kb_with(SRC);
    for (relation, want) in [
        ("p07e8.neqColumn", true),
        ("p07e8.neqColumnSame", false),
        ("p07e8.eqColumn", false),
    ] {
        let rows = crate::common::query_unary(&mut kb, relation);
        assert_eq!(rows.len(), 1, "{relation}: one answer, got {rows:?}");
        assert!(
            rows[0].1 && matches!(rows[0].0, Value::Bool(b) if b == want),
            "{relation}: a definite `{want}`, got {rows:?}"
        );
    }
}

/// `?x !== 1` with `?x` unbound never succeeds on a test that did not finish: it delays,
/// and is a conditional answer if nothing binds `?x`; bound later, it answers. Fails with
/// the resolver's `StructNeq` negating every verdict of `===`, the delay included.
#[test]
fn an_unbound_operand_is_undecided_not_true() {
    let mut kb = crate::common::load_kb_with(SRC);
    for (pattern, want) in [
        ("p07e8.unbound()", None),
        ("?x !== 1", None),
        ("p07e8.boundLater()", Some(true)),
        ("p07e8.boundLaterSame()", Some(false)),
    ] {
        assert_eq!(holds(&mut kb, pattern), want, "`{pattern}`");
    }
}

/// A contract `x !== 1` over an operation's parameter succeeds structurally — the
/// parameter is not the literal `1` — but the parameter might be 1, so it is undecided, as
/// `neq(x, 1)` is (`gamma_verdict_three_valued_test`). Fails with `StructNeq` out of the
/// skolem verdict table, and with the tag not registered: the contract then discharges.
#[test]
fn a_contract_over_a_parameter_is_undecided() {
    use anthill_core::kb::proof_verify::{verify_proofs, ProofVerdict};
    let src = r#"
namespace p07e8.ct
  import anthill.prelude.{Int64}
  sort Box
    entity box(value: Int64)
    operation wrap(x: Int64) -> Box
      ensures x !== 1
      = box(value: x)
    proof wrap.ensures by derivation end
  end
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    let report = verify_proofs(&mut kb);
    let verdict = &report
        .iter()
        .find(|r| r.rule_qn.ends_with("wrap.ensures"))
        .expect("a proof-report entry for `wrap.ensures`")
        .verdict;
    match verdict {
        ProofVerdict::Failed { reason } => assert!(
            reason.contains("could not be DECIDED"),
            "`x !== 1` over a parameter is undecided; got: {reason}"
        ),
        other => panic!("`x !== 1` over a parameter must not discharge; got {other:?}"),
    }
}

/// A bodyless `!==` head is refused at load naming `<=>`, as a `===` one is (WI-1090): a
/// rule, a fact, and one whose left operand names nothing. Fails with `struct_neq` out of
/// the equality family: the head then reads as declaring the desugaring's functor.
#[test]
fn a_bodyless_head_is_refused_naming_unify() {
    for (label, clause) in [
        ("rule", "rule tau(?x) !== ?x"),
        ("fact", "fact 1 !== 2"),
        ("var", "rule ?x !== ?x"),
    ] {
        let src = format!(
            "namespace p07e8.head.{label}\n  import anthill.prelude.{{Int64}}\n  {clause}\nend\n"
        );
        let errs = crate::common::load_errors_of(&src);
        assert_eq!(errs.len(), 1, "{label}: one refusal, got {errs:#?}");
        crate::common::assert_refused_naming(
            &errs,
            &["`!==` is the structural inequality TEST", "Write `<=>`"],
            label,
        );
    }
}

/// A `@[simp]` tag on a bodied `!==` head is refused as one on a `===` head is, and the
/// refusal names the connective written. Fails with the two structural tests read as one
/// wording: the `!==` head is then called an identity test.
#[test]
fn a_rewrite_tag_on_a_bodied_head_names_the_connective() {
    for (op, wording) in [
        ("!==", "a structural inequality test (`!==`)"),
        ("===", "a structural identity test (`===`)"),
    ] {
        let src = format!(
            "namespace p07e8.tag\n  import anthill.prelude.{{Int64}}\n  \
             rule tau(?x) {op} ?x :- ?x === 1 @[simp]\nend\n"
        );
        let errs = crate::common::load_errors_of(&src);
        assert_eq!(errs.len(), 1, "{op}: one refusal, got {errs:#?}");
        crate::common::assert_refused_naming(&errs, &[wording], op);
    }
}

/// A namespace declaring its own `struct_neq` does not capture the operator: `1 !== 2`
/// written there is the kernel's test in both bodies, and only a written `struct_neq(1, 2)`
/// call reaches the namespace's own. Fails with the operator minting the short name
/// `struct_neq`: the rule-body row then answers the namespace's `false`.
#[test]
fn a_namespace_struct_neq_does_not_capture_the_operator() {
    let src = r#"
namespace p07e8.own
  import anthill.prelude.{Int64, Bool}
  operation struct_neq(a: Int64, b: Int64) -> Bool = false
  rule viaOperator() :- 1 !== 2
  operation opViaOperator() -> Bool = 1 !== 2
  operation opWritten() -> Bool = struct_neq(1, 2)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(holds(&mut kb, "p07e8.own.viaOperator()"), Some(true));
    let mut interp = crate::common::interp_for(src);
    assert!(call_bool(&mut interp, "p07e8.own.opViaOperator", &[]));
    assert!(!call_bool(&mut interp, "p07e8.own.opWritten", &[]));
}

//! WI-738 — an unevaluated CALL in OPERAND position must DELAY, never be decided
//! by a STRUCTURAL comparison.
//!
//! THE BUG. `reduce_op_value` returns a builtin call unchanged ("a builtin is
//! reduced by its own path, not folded") — but that path only exists when the
//! builtin is the goal's OWN functor. Nested as an operand there is no such path,
//! so the call reached the comparison still an `Apply`, and `is_unreduced_op_call`
//! answered NO for it (it tested `builtins.get(f).is_none()`, false for `sub`), so
//! no delay fired and the comparison fell through to a structural verdict. The
//! TERM `sub(2,1)` differs structurally from the term `1` — hence:
//!
//!   * `neq(sub(?x,?y), 1)` was silently, unconditionally TRUE   (false positive)
//!   * `eq(?y, add(?x,?x))` was silently FALSE                   (false negative)
//!
//! One root cause, opposite lies. This contradicted what WI-483 documented as the
//! design — "a COMPLEX op-call … is LEFT uninterpreted, treated as un-ground (it
//! residualizes / delays), NOT a loud error". It did not residualize; it DECIDED.
//! Residualizing is honest; deciding an uninterpreted call is a wrong answer.
//!
//! WHAT THIS FIXES, AND WHAT IT DOES NOT. The floor makes such an operand DELAY.
//! It does NOT make it compute: `eq(?z, add(?x,?y))` still does not bind `?z`
//! (`=` never binds — kernel-language.md §8.3). Making it evaluate means
//! FLATTENING to the graph form `add(?x,?y,?z)`, which the 3-arg arithmetic
//! builtin already binds (pinned below) — additive, and separate.
//!
//! WHY THESE TESTS ARE RESOLVER-LEVEL. The floor's contract is about DEFINITENESS,
//! which `isEmpty` cannot see: a delayed goal rotates, flounders, and yields a
//! RESIDUAL solution, and the Relation drain currently materializes that residual
//! as though it were a definite row (WI-737 — the raise that fixes it is separate).
//! So an eval-level `isEmpty` reads `false` both before and after this fix, for
//! different reasons. `ResolveConfig.definite_only` is the honest lens: it is
//! exactly "a decision boundary that asks *is there a solution?*" (WI-519), and it
//! separates "refuted / undecided" from "proved". Before the fix `not_diag(2,1)`
//! produced a DEFINITE solution (the structural lie); after, it produces none.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::{ResolveConfig, Solution};
use anthill_core::kb::term::{Term, TermId, Literal};
use anthill_core::parse;
use smallvec::SmallVec;

const SRC: &str = r#"
namespace wi738.operand
  import anthill.prelude.{Int64, Bool}
  import anthill.prelude.Numeric.{add, sub}

  sort N
    entity num(v: Int64)
  end
  fact num(v: 1)
  fact num(v: 2)
  fact num(v: 3)

  -- THE FALSE POSITIVE: sub(?x,?y) nested under neq.
  rule not_diag(?x, ?y) :- num(v: ?x), num(v: ?y), neq(sub(?x, ?y), 1)

  -- THE FALSE NEGATIVE: add(?x,?x) nested under eq.
  rule doubled(?x, ?y) :- num(v: ?x), eq(?y, add(?x, ?x))

  -- The line the fix must not cross: a DATA constructor is not a call.
  rule ctor_same(?x) :- eq(some(?x), some(?x))

  -- A plain comparison on BOUND vars: no call in operand position.
  rule distinct(?x, ?y) :- num(v: ?x), num(v: ?y), neq(?x, ?y)

  -- The GRAPH form, which a future flattening macro would lower onto.
  rule sum3(?x, ?y, ?z) :- num(v: ?x), num(v: ?y), add(?x, ?y, ?z)
end
"#;

fn load_kb() -> KnowledgeBase {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    parsed.push(parse::parse(SRC).unwrap_or_else(|e| panic!("parse extra: {e:?}")));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).unwrap_or_else(|e| panic!("load: {e:?}"));
    kb
}

fn int(kb: &mut KnowledgeBase, n: i64) -> TermId {
    kb.alloc(Term::Const(Literal::Int(n)))
}

fn goal(kb: &mut KnowledgeBase, qn: &str, args: &[TermId]) -> TermId {
    let f = kb.resolve_symbol(qn);
    kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::from_slice(args),
        named_args: SmallVec::new(),
    })
}

/// Resolve with `definite_only` — the WI-519 decision boundary: a floundered
/// residual is skipped, so a solution here means the goal was actually PROVED.
fn definite_solutions(kb: &mut KnowledgeBase, qn: &str, args: &[i64]) -> Vec<Solution> {
    let ts: Vec<TermId> = args.iter().map(|&n| int(kb, n)).collect();
    let g = goal(kb, qn, &ts);
    let cfg = ResolveConfig { max_solutions: 10, definite_only: true, ..Default::default() };
    kb.resolve(&[g], &cfg)
}

/// THE FALSE POSITIVE — the unsound direction, and the reason this ticket exists.
/// `neq(sub(2,1), 1)` must not PROVE: 2-1 = 1, so the guard is false. Before the
/// fix the structural verdict (`sub(2,1)` ≠ `1` as terms) made it unconditionally
/// true and `not_diag(2,1)` came back as a definite solution.
///
/// This is the N-queens diagonal guard (WI-740): admitting a pair the guard must
/// exclude is exactly how an eight-queens written today would "run" and print
/// garbage instead of failing loudly.
#[test]
fn wi738_nested_builtin_under_neq_is_not_silently_proved() {
    let mut kb = load_kb();
    let sols = definite_solutions(&mut kb, "wi738.operand.not_diag", &[2, 1]);
    assert!(
        sols.is_empty(),
        "neq(sub(2,1), 1) must NOT be proved — 2-1=1, so the guard is false. A \
         structural verdict over the unevaluated term sub(2,1) made it silently, \
         unconditionally true; it must delay instead. Got {} definite solution(s).",
        sols.len(),
    );
}

/// The same root cause, opposite direction. `eq(2, add(1,1))` must not be proved
/// either — not because 1+1 ≠ 2, but because `eq` cannot decide an unevaluated
/// call and `=` never binds. Before the fix this was a definite REFUTATION (it
/// compared 2 against the term `add(1,1)`); now it delays.
///
/// Pinned as "not proved" rather than "proved": the floor's contract is that the
/// goal stops DECIDING, and computing it is the separate flattening step.
#[test]
fn wi738_nested_builtin_under_eq_is_not_silently_decided() {
    let mut kb = load_kb();
    let sols = definite_solutions(&mut kb, "wi738.operand.doubled", &[1, 2]);
    assert!(
        sols.is_empty(),
        "eq(?y, add(?x,?x)) cannot be decided by comparing against the unevaluated \
         term add(1,1) — it must delay. Got {} definite solution(s).",
        sols.len(),
    );
}

/// THE LINE THE FIX MUST NOT CROSS. A data constructor is NOT a call: `some(?x)`
/// vs `some(?x)` must still be decided EQUAL structurally, not delayed. If the fix
/// had keyed on "is an Apply" instead of "is a builtin/bodied CALL", this would
/// flounder and yield nothing.
///
/// Anthill can draw this line because `operation` and `entity` are distinct
/// declarations — unlike Prolog, where `1+2` is legitimately a term.
#[test]
fn wi738_data_constructors_still_compare_structurally() {
    let mut kb = load_kb();
    let sols = definite_solutions(&mut kb, "wi738.operand.ctor_same", &[7]);
    assert_eq!(
        sols.len(),
        1,
        "eq(some(7), some(7)) must still be PROVED structurally — a constructor is \
         data, not a call, so it must not delay",
    );
}

/// A comparison with no call in operand position is untouched: `neq` still decides
/// on bound vars, in both directions.
#[test]
fn wi738_plain_comparison_on_bound_vars_unaffected() {
    let mut kb = load_kb();
    assert_eq!(
        definite_solutions(&mut kb, "wi738.operand.distinct", &[1, 2]).len(),
        1,
        "neq(1,2) holds",
    );
    assert!(
        definite_solutions(&mut kb, "wi738.operand.distinct", &[1, 1]).is_empty(),
        "neq(1,1) is refuted",
    );
}

/// The GRAPH form still binds. `add(?x,?y,?z)` computes `?z` via the 3-arg
/// arithmetic builtin ("If 3 positional args: binds the 3rd arg to the computed
/// result", resolve.rs) — the route a flattening macro would lower `eq(?z,
/// add(?x,?y))` onto. The floor must not break the path that makes evaluation
/// reachable, so pin it here.
#[test]
fn wi738_three_arg_graph_form_still_binds() {
    let mut kb = load_kb();
    assert_eq!(
        definite_solutions(&mut kb, "wi738.operand.sum3", &[1, 2, 3]).len(),
        1,
        "add(1,2,?z) binds ?z=3, so sum3(1,2,3) is proved",
    );
    assert!(
        definite_solutions(&mut kb, "wi738.operand.sum3", &[1, 2, 9]).is_empty(),
        "add(1,2,?z) binds ?z=3, so sum3(1,2,9) is refuted",
    );
}

/// CARRIER NEUTRALITY. The operand must delay in BOTH carriers. A rule-body
/// operand arrives as a `Value::Node` occurrence (the tests above), but a
/// DIRECTLY-BUILT term goal — `resolve(&[neq(1, sub(2,1))])`, the shape a
/// resolver-level query or an `or`/`push_choice` branch body presents — arrives as
/// a `Value::Term`, since `walk_view` yields `Value::term` for any `Term::Fn`.
///
/// Without the `Term` arm of `is_unreduced_builtin_call` this goal keeps the old
/// silent lie: `sub(2,1)` and `1` differ as TERMS, so `neq` is structurally true
/// and the goal is PROVED — even though 2-1 = 1 and the guard is false. That is
/// the same carrier asymmetry `op_call_as_occ` already avoids by handling both.
#[test]
fn wi738_term_carried_operand_also_delays() {
    let mut kb = load_kb();
    let one = int(&mut kb, 1);
    let two = int(&mut kb, 2);
    let sub_call = goal(&mut kb, "anthill.prelude.Numeric.sub", &[two, one]);
    let g = goal(&mut kb, "anthill.prelude.PartialEq.neq", &[one, sub_call]);
    let cfg = ResolveConfig { max_solutions: 10, definite_only: true, ..Default::default() };
    let sols = kb.resolve(&[g], &cfg);
    assert!(
        sols.is_empty(),
        "neq(1, sub(2,1)) must NOT be proved — 2-1=1, so the guard is false. A \
         Term-carried builtin operand must delay exactly like a Node-carried one; \
         got {} definite solution(s).",
        sols.len(),
    );
}

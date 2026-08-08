//! WI-1042 — ONE OWNER for the defaulted-spec-op gate, driven rather than argued.
//!
//! Three sites decide what to do with a call on a spec operation that HAS a default
//! body: `check_apply_iter`'s WI-444 block (pin the carrier's supplied impl, or refuse a
//! tie), `dot_member_dispatch_decision`'s defaulted leg (the same decision reached by the
//! dot spelling, WI-1035), and `call_dispatch_shape` (the WI-1026 rule-body walk
//! trigger). They spelled the gate two different ways, and the equivalence was held by a
//! doc comment 30 000 lines away.
//!
//! WHY A COMMENT WAS NOT ENOUGH, and it is not a style point: when this file was written
//! the third spelling carried a `!is_builtin` clause the other two did not, and its
//! call-site population was ZERO across the whole corpus — so a clause added to the
//! WI-444 block would have moved the PIN/REFUSE population and left the rule-body FIRE
//! population behind, silently, with the full suite green both ways. (WI-1036 has since
//! deleted that clause, on evidence this sharing is what made cheap to gather: the walk
//! trigger now asks the gate and nothing else.) That is the drift this file measures.
//!
//! WHAT THIS FILE ACTUALLY LOADS, since the two scopes are easy to conflate: `corpus_kb`
//! is `load_kb_with`, i.e. **stdlib + the Rust host bindings** and nothing else. A drift
//! visible only in `examples/` or `anthill-todo` is not covered here.
//!
//! AND THE ORACLE'S OWN BLIND SPOT, stated so it is not mistaken for coverage: both sides
//! of the agreement test bottom out in [`sort_is_parametric`], so a clause added THERE
//! moves both and this file stays green. That is by design — `sort_is_parametric` is the
//! shared reading of "what makes a sort a spec", and a change to it is meant to reach
//! every reader. What the test catches is a clause added to ONE of the two gates.
//!
//! WHAT FAILS WHEN THE CHANGE IS BACKED OUT — stated per test at its site. The headline:
//! `the_shared_gate_agrees_with_the_wi444_spelling` fails the moment a clause is added to
//! [`defaulted_spec_op_parent`] alone, and the corpus population is large enough
//! (`the_gate_population_is_not_vacuous`) that it cannot pass by having nothing to check.
//! Restoring the `!is_builtin` clause INTO the shared gate — the WI-1036 blast radius,
//! which WI-1036 has since deleted from its one reader — is exactly such a clause,
//! and it is the case `a_builtin_backed_defaulted_spec_op_is_in_the_shared_gate` pins.

use anthill_core::kb::op_info::all_operation_params;
use anthill_core::kb::typing::{defaulted_spec_op_parent, lookup_spec_op_dispatch, spec_op_parent_sort};
use anthill_core::kb::KnowledgeBase;
use anthill_core::intern::Symbol;

/// The WI-444 gate as `check_apply_iter` spelled it before this ticket, kept here as the
/// ORACLE — an independent construction out of the two named readers, so the assertion
/// below compares two spellings rather than a function with itself.
fn wi444_gate_spelling(kb: &KnowledgeBase, op: Symbol) -> Option<Symbol> {
    if lookup_spec_op_dispatch(kb, op).is_some() {
        return None;
    }
    spec_op_parent_sort(kb, op)
}

fn corpus_kb() -> KnowledgeBase {
    crate::common::load_kb_with("namespace wi1042.probe\nend\n")
}

/// Every operation the corpus declares, both spellings, one assertion.
///
/// CONTROL — the case that fails when the change is backed out: add any clause to
/// [`defaulted_spec_op_parent`] that the oracle does not have (`!kb.is_builtin(f)` is the
/// live candidate, WI-1036) and this fails on the `PartialOrd` family. Backing out the
/// SHARING alone cannot be observed here, which is why this test's subject is the gate and
/// not a program: the shared-ness is what makes a future clause reach all three sites, and
/// this is the assertion that notices when it does not.
///
/// It also drives the one difference the two spellings genuinely have. The oracle's body
/// test is `!operation_has_no_body`, true also of a symbol with NO `OperationInfo`; the
/// gate reads `op_has_runnable_body`, which requires one. The walk trigger's old doc
/// asserted they coincide under a parametric parent and called that "a coupling, not a
/// licence"; this measures it instead of asserting it.
#[test]
fn the_shared_gate_agrees_with_the_wi444_spelling() {
    let kb = corpus_kb();
    let mut checked = 0usize;
    for (op, _) in all_operation_params(&kb) {
        assert_eq!(
            defaulted_spec_op_parent(&kb, op),
            wi444_gate_spelling(&kb, op),
            "the shared defaulted-spec-op gate and the WI-444 spelling disagree on `{}` \
             — a clause was added to one of them alone",
            kb.qualified_name_of(op),
        );
        checked += 1;
    }
    assert!(
        checked > 300,
        "expected the corpus to declare hundreds of operations, walked {checked} — the \
         agreement above would be vacuous over an empty domain",
    );
}

/// The gate is not vacuously `None` everywhere: the corpus really does declare defaulted
/// spec ops, so the agreement test above has a subject on both sides of its answer.
///
/// CONTROL: with the corpus's defaulted spec ops gone this reports 0 and fails; it also
/// fails if the gate is narrowed until it admits nobody. The exact count is deliberately
/// NOT pinned — it moves with the stdlib — but the named member is.
#[test]
fn the_gate_population_is_not_vacuous() {
    let kb = corpus_kb();
    let admitted: Vec<Symbol> = all_operation_params(&kb)
        .into_iter()
        .map(|(op, _)| op)
        .filter(|&op| defaulted_spec_op_parent(&kb, op).is_some())
        .collect();
    assert!(
        admitted.len() >= 10,
        "the shared gate admits only {} of the corpus's operations — too few for the \
         agreement test to be measuring anything",
        admitted.len(),
    );
    let gt = kb
        .try_resolve_symbol("anthill.prelude.PartialOrd.gt")
        .expect("the stdlib declares PartialOrd.gt");
    assert_eq!(
        defaulted_spec_op_parent(&kb, gt),
        kb.try_resolve_symbol("anthill.prelude.PartialOrd"),
        "`PartialOrd.gt` is a defaulted member of a parametric sort — the shape this gate \
         exists to name",
    );
}

/// A BUILTIN-MAPPED DEFAULTED SPEC OP IS ONE, and the gate says so by what it IS.
/// `PartialOrd.gt` is defaulted AND builtin-mapped; every reader of the gate admits it.
/// When this was written one reader — the rule-body walk trigger — excluded it through a
/// `!is_builtin` clause of its own, and this test's subject was that the clause was
/// SITE-LOCAL and could not become a claim about the shape. WI-1036 then deleted the
/// clause outright, so today no reader excludes it and the assertion pins the shared
/// answer the deletion rests on.
///
/// CONTROL: put a `!is_builtin` clause into [`defaulted_spec_op_parent`] and this fails,
/// as does `the_shared_gate_agrees_with_the_wi444_spelling` — a per-site dispatch policy
/// must not be spelled as a change to what a defaulted spec op IS.
#[test]
fn a_builtin_backed_defaulted_spec_op_is_in_the_shared_gate() {
    let kb = corpus_kb();
    let gt = kb
        .try_resolve_symbol("anthill.prelude.PartialOrd.gt")
        .expect("the stdlib declares PartialOrd.gt");
    assert!(kb.is_builtin(gt), "`PartialOrd.gt` is builtin-mapped");
    assert!(
        defaulted_spec_op_parent(&kb, gt).is_some(),
        "the shared gate must classify a builtin-backed defaulted spec op by what it IS; \
         a dispatch policy that wants to skip it belongs at a reader (WI-1036)",
    );
}

/// NON-OPERATION FUNCTORS — and the ONE case where the new gate genuinely answers
/// differently from the spelling it replaced. The gate is asked once per `Expr::Apply`
/// functor, and the majority of those are not operations at all — a relational atom head,
/// an entity constructor, a namespace-parented name. Most leave at
/// `impl_parent_sort_of_op`'s name split, before `op_has_runnable_body` can fall through
/// `lookup_operation_info`'s record miss into its O(N_ops) fact scan.
///
/// `anthill.prelude.Option.some` is the exception and the reason this test exists.
/// It is an entity constructor declared INSIDE a parametric sort, so the name split and
/// the parametric leg both pass and only the body leg can answer — and the two body tests
/// disagree about it: the old `!operation_has_no_body` is TRUE for a symbol with no
/// `OperationInfo`, so the pre-change WI-444 spelling calls `Option.some` a defaulted spec
/// op, while the gate does not. The agreement test above cannot see this, because
/// `all_operation_params` enumerates `OperationInfo` facts and `Option.some` has none.
///
/// CONTROL, MEASURED — and the first version of this sentence was WRONG, which is why the
/// number is here. Give the gate the old body test and 15 tests across 5 suites fail, not
/// one: 14 of them through the rule-body walk trigger, which then type-checks
/// entity-constructor calls (driven — re-conjoining `op_has_runnable_body` at that site
/// alone restores exactly those 14; re-measured after WI-1036, unchanged), and THIS one,
/// which is the only test in the workspace
/// that sees the gate's own answer rather than one site's use of it. That is what it is
/// for: the other three call sites are safe by a precondition each (see
/// [`defaulted_spec_op_parent`]'s doc), and a site that later loses its precondition
/// inherits an answer this test has pinned.
#[test]
fn a_non_operation_functor_is_not_a_defaulted_spec_op() {
    let kb = corpus_kb();
    for qn in [
        // The one that is NOT rejected by the name split: `some` is declared INSIDE
        // `Option`, whose parent probe passes AND which is parametric, so only the body
        // leg can answer for it. An entity constructor is not an operation, and
        // `op_has_runnable_body`'s `OperationInfo`-existence gate is what says so.
        "anthill.prelude.Option.some",
        "anthill.prelude.Option", // a sort — parented by a NAMESPACE
        "anthill.prelude",        // a namespace
        "anthill.reflect.OperationInfo",
    ] {
        let sym = kb
            .try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("the corpus declares `{qn}`"));
        assert_eq!(
            defaulted_spec_op_parent(&kb, sym),
            None,
            "`{qn}` is not an operation, so it is not a defaulted spec op",
        );
    }
}

/// ITEM (3) — WHAT A `spec_op_parent_sort` MISS MEANS AT THE DOT SITE, driven rather
/// than argued. `dot_member_dispatch_decision` reaches that miss only after
/// `find_spec_op_for_provided_sort` answered `Some`, so the member DOES back something
/// the carrier `provides`; the ticket read the miss as an unexpected shape and asked for
/// a loud error or a recorded impossibility argument. IT IS NEITHER — the shape is
/// reachable by a legal program, and this is it:
///
/// `Plain` declares no `sort X = ?`, so it is not a SPEC (058: a spec sort is one with a
/// type parameter). `Leaf provides Plain` loads clean, the dot resolves `describe` to
/// `Leaf`'s own member, and `Plain.describe` has no parametric parent. There is no
/// spec-op dispatch to decide and no supplier set keyed on a carrier, so `Take` is the
/// ANSWER and not a fallback — and a loud error here would refuse this program.
///
/// CONTROL: turn that early return into an error and this fails. MEASURED, as a `panic!`
/// there: it fired on this fixture and on nothing else in the workspace's 4321 tests, which
/// is what says the shape is reachable AND rare — the two halves of "record the argument,
/// do not raise".
///
/// WHAT THIS TEST CANNOT SEE, so it is not read as more than it is: deleting the
/// `provides Plain` line leaves the answer at 7, because `find_spec_op_for_provided_sort`
/// then misses one line earlier and returns `Take` for a different reason. The test pins
/// the ANSWER at a shape that reaches the miss, not which early-out produced it.
#[test]
fn a_non_parametric_provided_sort_takes_the_member() {
    let ns = "wi1042.nonparametric";
    let src = format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  -- NOT a spec: no `sort X = ?`, so `spec_op_parent_sort` misses on its members.
  sort Plain
    operation describe(x: Int64) -> Int64 = 1
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Plain
    operation describe(x: Leaf) -> Int64 = 7
  end

  rule answer(?r) :- leaf().describe(?r)
end
"#
    );
    assert_eq!(
        crate::wi1026_rule_body_spec_op_dispatch_test::answer(ns, &src),
        7,
        "a member backing a NON-parametric provided sort is taken, not routed through a \
         dispatch that does not exist",
    );
}


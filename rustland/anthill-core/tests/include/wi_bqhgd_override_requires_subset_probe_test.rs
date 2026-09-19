//! WI-20260919-BQHGD (2) — WHAT THE OVERRIDE-REFINEMENT LEG DOES TODAY WITH AN
//! OPERATION-LEVEL `requires`, measured for proposal 065 §3 before step 3 builds on it.
//!
//! 065 §3: an implementation's OPERATION-level requirements must be a SUBSET of its spec
//! operation's, while a requirement over the provider's OWN sort parameters rides on the
//! instance and is allowed. The guess was that `check_override_refinement`'s
//! precondition leg already enforces the first half. MEASURED — half right:
//!
//!  * an ADDED clause is refused ("strengthens the precondition") — the rule 065 wants;
//!  * a clause RESTATED from the spec is refused TOO when it names the operation's own
//!    TYPE parameter (`requires Eq[T = B]` on both sides). The leg compares clauses
//!    structurally and does not align the two operations' type parameters
//!    (`Desc.f.B` vs `Leaf.f.B`), so it reads the restatement as an addition. The same
//!    restatement over a GROUND type (`Eq[T = Int64]`) loads. Under 065 an implementation
//!    must restate `TypeValue[T = B]` to read `B`, so this over-refusal BLOCKS step 3
//!    (WI-20260919-N31XX), which aligns the type parameters and FLIPS
//!    [`restating_the_specs_type_param_clause_is_refused_today`].
//!
//! Every row here pins CURRENT behaviour. Which ones step 3 changes is said at each row;
//! the others are the rule 065 keeps and pass either way by design.

use anthill_core::eval::Value;

use crate::common::{interp_for, try_load_kb_with};

/// `SPEC_REQ` / `IMPL_REQ` are the spec's and the override's operation-level clauses;
/// `BOX_REQ` is a clause on a PARAMETRIC provider sort, over its own parameter.
const BASE: &str = r#"
namespace test.bqhgd
  import anthill.prelude.{Int64, Eq}

  sort Desc
    import anthill.prelude.Int64
    sort T = ?
    operation f[B](self: T, x: B) -> Int64 SPEC_REQ
  end

  sort Leaf
    import anthill.prelude.{Int64, Eq}
    entity leaf
    provides Desc[T = Leaf]
    operation f[B](self: Leaf, x: B) -> Int64 IMPL_REQ = 1
  end

  sort Box
    import anthill.prelude.{Int64, Eq}
    sort V = ?
    entity box(v: V)
    BOX_REQ
    provides Desc[T = Box[V = V]]
    operation f[B](self: Box, x: B) -> Int64 = 2
  end

  operation viaLeaf() -> Int64 = Desc.f(leaf(), 5)
  operation viaGeneric[Q](y: Q) -> Int64 = Desc.f(leaf(), y)
  operation viaGenericCall() -> Int64 = viaGeneric(5)
  operation viaBox() -> Int64 = Desc.f(box(7), 5)
end
"#;

fn src(spec: &str, imp: &str, bx: &str) -> String {
    BASE.replace("SPEC_REQ", spec)
        .replace("IMPL_REQ", imp)
        .replace("BOX_REQ", bx)
}

const STRENGTHENS: &str = "'test.bqhgd.Leaf' overrides 'test.bqhgd.Desc.f' but does not refine it: \
     it strengthens the precondition";

fn refusal(spec: &str, imp: &str, bx: &str) -> Vec<String> {
    match try_load_kb_with(&src(spec, imp, bx)) {
        Ok(_) => Vec::new(),
        Err(es) => es.to_vec(),
    }
}

/// Loads, and every route answers — so a clean load is not vacuous.
fn loads_and_answers(spec: &str, imp: &str, bx: &str) {
    let mut interp = interp_for(&src(spec, imp, bx));
    for (op, want) in [
        ("viaLeaf", 1),
        ("viaGenericCall", 1),
        ("viaBox", 2),
    ] {
        match interp.call(&format!("test.bqhgd.{op}"), &[]) {
            Ok(Value::Int(n)) => assert_eq!(n, want, "{op}"),
            other => panic!("{op}: {other:?}"),
        }
    }
}

/// THE RULE 065 §3 WANTS, already enforced: an override adding an operation-level clause
/// the spec does not declare is refused. Step 3 keeps this — green either way by design.
#[test]
fn an_override_adding_an_op_level_clause_is_refused() {
    let errs = refusal("", "requires Eq[T = B]", "");
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert!(errs[0].contains(STRENGTHENS), "{errs:#?}");
}

/// THE OVER-REFUSAL. The spec declares `requires Eq[T = B]` and the override restates it
/// verbatim; the leg does not align the two operations' type parameters, so the
/// restatement reads as an addition. PINS TODAY'S BEHAVIOUR: WI-20260919-N31XX aligns the
/// type parameters and turns this row into "loads and answers".
#[test]
fn restating_the_specs_type_param_clause_is_refused_today() {
    let errs = refusal("requires Eq[T = B]", "requires Eq[T = B]", "");
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert!(errs[0].contains(STRENGTHENS), "{errs:#?}");
}

/// CONTROL for the row above: the same restatement over a GROUND type loads and runs —
/// which is what isolates the type-PARAMETER alignment as the cause. Green either way.
#[test]
fn restating_a_ground_clause_loads() {
    loads_and_answers("requires Eq[T = Int64]", "requires Eq[T = Int64]", "");
}

/// CONTROL: a subset (the spec declares, the override omits) loads and runs. Green either
/// way.
#[test]
fn a_spec_only_clause_loads() {
    loads_and_answers("requires Eq[T = B]", "", "");
}

/// 065 §3's permitted half: a requirement over the PROVIDER's own sort parameter is not
/// an operation-level addition, and loads and runs. Green either way.
#[test]
fn a_provider_sort_clause_over_its_own_param_loads() {
    loads_and_answers("", "", "requires Eq[T = V]");
}

/// CONTROL: no clauses anywhere.
#[test]
fn no_clauses_loads() {
    loads_and_answers("", "", "");
}

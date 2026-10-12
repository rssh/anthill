//! WI-20261012-ZZ7PH — what the core gives a reader that lowers a spec's law: the CHAIN
//! of a `requires` clause with its bindings composed (`load::requirement_chain`), and
//! what a clause keeps of a TYPED HEAD VARIABLE (`ProgramClause::type_bounds`,
//! `frame_type_params`; `typing::is_typed_head_domain_goal`).
//!
//! The SMT emitter is the reader (`anthill-smt-gen`'s `sort.rs`); what a proof's
//! document is for them is driven through the binary
//! (`anthill-cli/tests/include/wi_zz7ph_law_lowering_test.rs`).
//!
//! What fails when a part is backed out:
//! `docs/measurements/test-infrastructure/law-lowering-2026-10-12.txt` §5.

use crate::common::load_kb_with;
use anthill_core::eval::Value;
use anthill_core::kb::load::{requirement_chain, requires_clauses_of, RequirementInstance};
use anthill_core::kb::term::{Term, Var};
use anthill_core::kb::typing::{is_typed_head_domain_goal, sort_functor_of_view};
use anthill_core::kb::KnowledgeBase;

/// The chain of the ONE `requires` clause of `scope`.
fn chain_of(kb: &mut KnowledgeBase, scope: &str) -> RequirementInstance {
    let clauses = requires_clauses_of(kb, &[scope]).expect("the clauses are read");
    assert_eq!(clauses.len(), 1, "`{scope}` has one clause: {clauses:?}");
    requirement_chain(kb, &clauses[0]).expect("the clause has a chain")
}

/// An instance as `<spec text> {<parameter> = <the sort its binding is>, …}`, and its
/// own chain indented under it.
fn shape(kb: &KnowledgeBase, instance: &RequirementInstance, depth: usize, out: &mut Vec<String>) {
    let bindings: Vec<String> = instance
        .bindings
        .iter()
        .map(|(param, ty)| {
            format!(
                "{} = {}",
                kb.qualified_name_of(*param),
                sort_functor_of_view(kb, ty).map_or("?", |sort| kb.qualified_name_of(sort))
            )
        })
        .collect();
    out.push(format!(
        "{}{} {{{}}}",
        "  ".repeat(depth),
        instance.spec_text,
        bindings.join(", ")
    ));
    for in_turn in &instance.in_turn {
        shape(kb, in_turn, depth + 1, out);
    }
}

/// THE CHAIN OF `requires Ord[T = T]`: `Ord`, the `WeakOrd` it PROVIDES — a spec's
/// `provides` is a conversion and stands in the chain where a `requires` does — and
/// under that `Eq` with the `PartialEq` it provides, and `PartialOrd` with the
/// `PartialEq` it requires. Every binding is the SCOPE'S parameter: `Eq.T` is bound to
/// `WeakOrd.T` where it is written, and to `Scope.T` here. A binding whose value is an
/// operation (`compare = compare`, completed by the loader) is not a type parameter's.
#[test]
fn the_chain_of_a_clause_is_composed_into_the_scopes_terms() {
    let mut kb = load_kb_with(
        r#"
namespace test.zz7ph.chain
  sort Scope
    sort T = ?
    requires anthill.prelude.Ord[T = T]
  end
end
"#,
    );
    let chain = chain_of(&mut kb, "test.zz7ph.chain.Scope");
    let mut shown = Vec::new();
    shape(&kb, &chain, 0, &mut shown);
    let t = "test.zz7ph.chain.Scope.T";
    let at =
        |spec: &str| format!("anthill.prelude.{spec}[T = {t}] {{anthill.prelude.{spec}.T = {t}}}");
    assert_eq!(
        shown,
        vec![
            at("Ord"),
            format!("  {}", at("WeakOrd")),
            format!("    {}", at("Eq")),
            format!("      {}", at("PartialEq")),
            format!("    {}", at("PartialOrd")),
            format!("      {}", at("PartialEq")),
        ]
    );
}

/// A binding is composed through EVERY step, a rename and a concrete type alike:
/// `Mid.B` is bound to the scope's `T`, and `Leaf.A` to `Mid.B` where `Mid` writes its
/// requirement — so `Leaf.A` is `Scope.T` here, and `Int64` under the other scope.
#[test]
fn a_binding_is_composed_through_a_rename_and_to_a_concrete_type() {
    let mut kb = load_kb_with(
        r#"
namespace test.zz7ph.compose
  import anthill.prelude.{Int64}

  sort Leaf
    sort A = ?
  end
  sort Mid
    sort B = ?
    requires Leaf[A = B]
  end
  sort Scope
    sort T = ?
    requires Mid[B = T]
  end
  sort Concrete
    requires Mid[B = Int64]
  end
end
"#,
    );
    let ns = "test.zz7ph.compose";
    for (scope, bound_to, text) in [
        ("Scope", format!("{ns}.Scope.T"), format!("{ns}.Scope.T")),
        (
            "Concrete",
            "anthill.prelude.Int64".to_owned(),
            "anthill.prelude.Int64".to_owned(),
        ),
    ] {
        let chain = chain_of(&mut kb, &format!("{ns}.{scope}"));
        let mut shown = Vec::new();
        shape(&kb, &chain, 0, &mut shown);
        assert_eq!(
            shown,
            vec![
                format!("{ns}.Mid[B = {text}] {{{ns}.Mid.B = {bound_to}}}"),
                format!("  {ns}.Leaf[A = {text}] {{{ns}.Leaf.A = {bound_to}}}"),
            ],
            "`{scope}`"
        );
    }
}

const TYPED_HEADS: &str = r#"
namespace test.zz7ph.bounds
  import anthill.prelude.PartialEq.{eq, neq}
  import anthill.prelude.{Int64}

  sort Scope
    sort T = ?
    sort U = ?
    rule carrier(?a: T, ?b) :- neq(?a, ?b)
    rule both(?a: T, ?u: U) :- eq(?a, ?a), eq(?u, ?u)
    rule scalar(?n: Int64) :- eq(?n, 3)
    rule plain(?a, ?b) :- neq(?a, ?b)
  end
end
"#;

/// The one clause of `test.zz7ph.bounds.Scope.<rule>`.
fn clause_of(kb: &KnowledgeBase, rule: &str) -> anthill_core::kb::ProgramClause {
    let mut clauses = kb.program_clauses_by_qn(&format!("test.zz7ph.bounds.Scope.{rule}"));
    assert_eq!(clauses.len(), 1, "`{rule}`");
    clauses.remove(0)
}

/// The frame slot a bound is, when it is the clause's own variable.
fn bound_slot(kb: &KnowledgeBase, bound: &Value) -> Option<u32> {
    match bound {
        Value::Term { id, .. } => match kb.get_term(*id) {
            Term::Var(Var::DeBruijn(slot)) => Some(*slot),
            _ => None,
        },
        _ => None,
    }
}

/// WHAT A CLAUSE KEEPS OF A BOUND. `?a: T` names the enclosing sort's parameter, and a
/// relational clause admits that parameter to its frame: the stored bound is a VARIABLE
/// of the clause, and `frame_type_params` is what says the variable is `Scope.T`. Two
/// parameters are two slots. A scalar bound is the type, and no slot of the frame is a
/// parameter. A clause that wrote no bound has neither.
#[test]
fn a_clause_keeps_the_bounds_of_its_head_variables_and_which_parameter_each_names() {
    let kb = load_kb_with(TYPED_HEADS);
    let params_of = |clause: &anthill_core::kb::ProgramClause| -> Vec<(u32, String)> {
        let mut params: Vec<(u32, String)> = clause
            .frame_type_params
            .iter()
            .map(|(slot, param)| (*slot, kb.qualified_name_of(*param).to_owned()))
            .collect();
        params.sort();
        params
    };
    let named = |clause: &anthill_core::kb::ProgramClause| -> Vec<String> {
        clause
            .type_bounds
            .iter()
            .map(|(_, bound)| {
                let slot =
                    bound_slot(&kb, bound).expect("a bound that names a parameter is a slot");
                params_of(clause)
                    .into_iter()
                    .find(|(at, _)| *at == slot)
                    .map(|(_, param)| param)
                    .expect("the slot is a declared parameter's")
            })
            .collect()
    };

    let carrier = clause_of(&kb, "carrier");
    assert_eq!(
        carrier.type_bounds.len(),
        1,
        "`?a` has a bound and `?b` has none"
    );
    assert_eq!(named(&carrier), ["test.zz7ph.bounds.Scope.T"]);

    let mut both = named(&clause_of(&kb, "both"));
    both.sort();
    assert_eq!(
        both,
        ["test.zz7ph.bounds.Scope.T", "test.zz7ph.bounds.Scope.U"]
    );

    let scalar = clause_of(&kb, "scalar");
    assert_eq!(scalar.type_bounds.len(), 1);
    assert_eq!(
        bound_slot(&kb, &scalar.type_bounds[0].1),
        None,
        "a type, not a slot"
    );
    assert_eq!(
        sort_functor_of_view(&kb, &scalar.type_bounds[0].1).map(|sort| kb.qualified_name_of(sort)),
        Some("anthill.prelude.Int64")
    );
    assert_eq!(params_of(&scalar), Vec::<(u32, String)>::new());

    let plain = clause_of(&kb, "plain");
    assert!(plain.type_bounds.is_empty() && plain.frame_type_params.is_empty());
}

/// THE GOALS THE LOADER GENERATES FOR A TYPED HEAD ARE TOLD FROM THE ONES WRITTEN, by
/// provenance: a reader that takes the bound for what it says skips exactly these. The
/// written body of `carrier` is one goal, and the rest of its stored body is the type
/// test in front and the fill behind; a clause with no bound has none generated.
#[test]
fn the_goals_generated_for_a_typed_head_are_told_from_the_written() {
    let kb = load_kb_with(TYPED_HEADS);
    let generated = |rule: &str| -> (usize, usize) {
        let clause = clause_of(&kb, rule);
        let generated = clause
            .body_nodes
            .iter()
            .filter(|goal| is_typed_head_domain_goal(&kb, goal))
            .count();
        (generated, clause.body_nodes.len() - generated)
    };
    let (made, written) = generated("carrier");
    assert!(made >= 1, "a bound has a generated type test");
    assert_eq!(written, 1, "`neq(?a, ?b)`");
    let (made, written) = generated("both");
    assert!(made >= 2, "one for each bound");
    assert_eq!(written, 2);
    assert_eq!(generated("scalar").1, 1);
    assert_eq!(generated("plain"), (0, 1));
}

//! WI-899 — a resolver builtin and written clauses are answer sources for ONE
//! predicate. Native backing is an implementation detail: it must not turn the
//! clause index off at the builtin's arity.
//!
//! BACK-OUT MEASUREMENT: removing `Candidate::Builtin` and the combined choice
//! point in `resolve.rs` makes the two exact-arity capability tests fail. The
//! controls still pass: the native `push_choice` answers remain 1/2, and the
//! clause-free fixture never manufactures 3. The off-arity control passes either
//! way and protects WI-896's resolved-name behaviour.

use anthill_core::eval::Value;
use anthill_core::kb::resolve::{ResolveConfig, Solution};
use anthill_core::kb::term::{Literal, Term, Var};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

fn int_answers(kb: &mut KnowledgeBase, qn: &str) -> Vec<i64> {
    let functor = kb.resolve_symbol(qn);
    let name = kb.intern("wi899_answer");
    let vid = kb.fresh_var(name);
    let var = kb.alloc(Term::Var(Var::Global(vid)));
    let goal = kb.alloc(Term::Fn {
        functor,
        pos_args: SmallVec::from_slice(&[var]),
        named_args: SmallVec::new(),
    });
    let mut answers: Vec<i64> = kb
        .resolve(&[goal], &ResolveConfig::default())
        .into_iter()
        .filter(Solution::is_definite)
        .filter_map(|solution| match kb.reify(var, &solution.subst) {
            Value::Int(i) => Some(i),
            Value::Term { id, .. } => match kb.get_term(id) {
                Term::Const(Literal::Int(i)) => Some(*i),
                _ => None,
            },
            _ => None,
        })
        .collect();
    answers.sort_unstable();
    answers
}

const PUSH_CHOICE_BASE: &str = r#"
namespace wi899.choice
  import anthill.prelude.{Int64}
  import anthill.kernel.{push_choice}

  fact nativeLeft899(1)
  fact nativeRight899(2)
  rule answer899(?n) :- push_choice(nativeLeft899(?n), nativeRight899(?n))
end
"#;

const PUSH_CHOICE_WITH_CLAUSE: &str = r#"
namespace wi899.choice
  import anthill.prelude.{Int64}
  import anthill.kernel.{push_choice}

  fact nativeLeft899(1)
  fact nativeRight899(2)
  rule push_choice(nativeLeft899(3), nativeRight899(3)) :- true
  rule answer899(?n) :- push_choice(nativeLeft899(?n), nativeRight899(?n))
end
"#;

#[test]
fn native_control_answers_and_written_clause_answers_coexist() {
    let mut control = crate::common::load_kb_with(PUSH_CHOICE_BASE);
    assert_eq!(
        int_answers(&mut control, "wi899.choice.answer899"),
        vec![1, 2],
        "CONTROL: without the written push_choice clause, only its two native branches answer",
    );

    let mut combined = crate::common::load_kb_with(PUSH_CHOICE_WITH_CLAUSE);
    assert_eq!(
        int_answers(&mut combined, "wi899.choice.answer899"),
        vec![1, 2, 3],
        "the native branches must remain, and the same-predicate written clause must add 3",
    );
}

#[test]
fn off_native_arity_clause_keeps_the_existing_symbol_and_answers() {
    const SRC: &str = r#"
namespace wi899.offarity
  import anthill.prelude.{Int64}
  import anthill.kernel.{or}

  fact source899(4)
  rule or(?n) :- source899(?n)
  rule answer899(?n) :- or(?n)
end
"#;
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(
        int_answers(&mut kb, "wi899.offarity.answer899"),
        vec![4],
        "off the native handler's arity, the resolved-symbol clause must remain the only answer source",
    );
}

#[test]
fn a_written_clause_on_native_gte_is_reached_by_sld() {
    const SRC: &str = r#"
namespace wi899.gte
  import anthill.prelude.{Float}
  import anthill.prelude.PartialOrd.{gte}

  fact seed899(5.0)
  rule gte(?x, 3.0) :- seed899(?x)
end
"#;
    let mut kb = crate::common::load_kb_with(SRC);
    let gte = kb.resolve_symbol("anthill.prelude.PartialOrd.gte");
    let name = kb.intern("wi899_x");
    let vid = kb.fresh_var(name);
    let var = kb.alloc(Term::Var(Var::Global(vid)));
    let add = kb.resolve_symbol("anthill.prelude.Additive.add");
    let one = kb.alloc(Term::Const(Literal::Float(1.0.into())));
    let two = kb.alloc(Term::Const(Literal::Float(2.0.into())));
    let computed_three = kb.alloc(Term::Fn {
        functor: add,
        pos_args: SmallVec::from_slice(&[one, two]),
        named_args: SmallVec::new(),
    });
    let goal = kb.alloc(Term::Fn {
        functor: gte,
        pos_args: SmallVec::from_slice(&[var, computed_three]),
        named_args: SmallVec::new(),
    });

    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    let definite_fives = solutions
        .iter()
        .filter(|solution| solution.is_definite())
        .filter(|solution| match kb.reify(var, &solution.subst) {
            Value::Float(f) => f == 5.0,
            Value::Term { id, .. } => matches!(
                kb.get_term(id),
                Term::Const(Literal::Float(f)) if f.into_inner() == 5.0
            ),
            _ => false,
        })
        .count();
    assert_eq!(
        definite_fives, 1,
        "after add(1.0, 2.0) is evaluated for candidate selection, the native comparison may \
         residualize on ?x but the written gte(?x, 3.0) clause must prove ?x = 5.0",
    );
}

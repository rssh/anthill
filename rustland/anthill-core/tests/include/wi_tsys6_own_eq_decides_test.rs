//! WI-20261025-TSYS6 — A TYPE'S OWN `eq` DECIDES `=`, written as its member or as a provision's
//! binding alike, identical operands included: reflexivity is `Eq`'s law (`eq_refl`), not
//! `PartialEq`'s (the user, 2026-10-25; kernel-language.md §8.3). A type that provides `Eq`
//! keeps the reflexivity answer.
//!
//! MEASURED before, for a `Loop` that provides only `PartialEq`: its own member `eq = false`
//! answered `PartialEq.eq(lp(v: 1), lp(v: 1))` with 0 — the call by name is pinned to the
//! member — while the same `false` written as `eq = neverEq` answered 1, the semantic-equality
//! builtin answering reflexivity before it asked the binding; and a circular binding answered 1
//! on identical operands, the cap that refuses it never reached.
//!
//! The builtin's reflexivity step, and the WI-664 field-wise compare before it, stand aside for
//! an operand headed by such a type (`KnowledgeBase::eq_dispatch_is_partial`, set where the
//! equality index is built), in eval (`semantic_equal`) and in the resolver (`sem_eq_values`).
//! The routes stay as they were (the user's choice): the member is pinned and runs, the binding
//! is reached through the builtin, so a circular member still runs to the step budget where a
//! circular binding is refused at the bridge's re-entry cap.
//!
//! BACK-OUTS, MEASURED: with the gate on `eq_dispatch_is_partial` removed from both halves, the
//! five rows that name the binding or an open operand fail; the member's two rows and the
//! controls pass either way by design (the dictionary spelling passes too: it already entered
//! the binding). With eval's refusal of an open operand removed, its row alone fails.
//!
//! NOT COVERED, and a gap of its own: an operand of such a type BURIED in one with no `eq` of
//! its own (`some(lp(v: 1))` against itself) is answered by reflexivity at the top, as a buried
//! override is answered structurally (WI-625's documented gap).

use crate::common::{query_unary, run_int64};

/// `Loop` with `supply` written beside it, and `go()` comparing two identical values by name.
fn program(ns: &str, in_loop: &str, supply: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.{{Int64, Bool, PartialEq, Eq}}
  sort Loop
    entity lp(v: Int64)
{in_loop}  end
{supply}
  operation go() -> Int64 = if PartialEq.eq(lp(v: 1), lp(v: 1)) then 1 else 0
  rule rq(?r) :- PartialEq.eq(lp(v: 1), lp(v: 1)), ?r <=> 1
end
"#
    )
}

/// `neverEq`, bound as `Loop`'s `eq` by a `namespace Loop` entry providing `specs`.
fn never_binding(specs: &[&str]) -> String {
    let provisions: String = specs
        .iter()
        .map(|spec| format!("    provides {spec}[T = Loop, eq = neverEq]\n"))
        .collect();
    format!(
        "  operation neverEq(x: Loop, y: Loop) -> Bool = false\n  namespace Loop\n{provisions}  end\n"
    )
}

/// The BINDING decides identical operands, by name: 0. It answered 1.
#[test]
fn a_binding_decides_identical_operands() {
    let ns = "test.tsys6.binding";
    let src = program(ns, "", &never_binding(&["PartialEq"]));
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(0));
}

/// … and in a rule body, the resolver's half: `rq` has no answer. It had one.
#[test]
fn a_binding_decides_identical_operands_in_a_rule_body() {
    let ns = "test.tsys6.rule";
    let src = program(ns, "", &never_binding(&["PartialEq"]));
    let mut kb = crate::common::load_kb_with(&src);
    assert!(query_unary(&mut kb, &format!("{ns}.rq")).is_empty());
}

/// A CIRCULAR binding is refused on identical operands too, at the bridge's re-entry cap. It
/// answered 1.
#[test]
fn a_circular_binding_is_refused_on_identical_operands() {
    let ns = "test.tsys6.circular";
    let supply = "  operation loopEq(x: Loop, y: Loop) -> Bool = PartialEq.eq(x, y)\n  \
                  namespace Loop\n    provides PartialEq[T = Loop, eq = loopEq]\n  end\n";
    let src = program(ns, "", supply);
    let answer = run_int64(&src, &format!("{ns}.go"));
    assert!(
        answer
            .as_ref()
            .is_err_and(|e| e.contains("could not be decided")),
        "refused at the cap: {answer:?}"
    );
}

/// … THROUGH EVERY SPELLING: the infix `=`, the dot, and a `requires PartialEq[T = T]`
/// dictionary. `=` and the dot answered 1 by reflexivity, as the call by name did; the
/// dictionary already entered the binding, and passes either way.
#[test]
fn a_binding_decides_identical_operands_through_every_spelling() {
    let ns = "test.tsys6.spellings";
    let supply = format!(
        "{}  operation same[T](a: T, b: T) -> Bool requires PartialEq[T = T] = PartialEq.eq(a, b)\n  \
         operation infix() -> Int64 = if lp(v: 1) = lp(v: 1) then 1 else 0\n  \
         operation dot() -> Int64 = if lp(v: 1).eq(lp(v: 1)) then 1 else 0\n  \
         operation dict() -> Int64 = if same(lp(v: 1), lp(v: 1)) then 1 else 0\n",
        never_binding(&["PartialEq"])
    );
    let src = program(ns, "", &supply);
    for entry in ["infix", "dot", "dict"] {
        assert_eq!(run_int64(&src, &format!("{ns}.{entry}")), Ok(0), "{entry}");
    }
}

/// A NON-GROUND operand of such a type is undecided, and refused: its `eq` cannot be asked of a
/// value with a variable in it (`=` never binds), and reflexivity is not its answer. It answered
/// `true` by reflexivity; with reflexivity gone and nothing else said, eval's last step would
/// have answered `false` (found by /code-review).
#[test]
fn a_non_ground_operand_is_undecided() {
    use anthill_core::eval::Value;
    use anthill_core::kb::term::{Term, Var};
    use smallvec::SmallVec;
    let ns = "test.tsys6.open";
    let src = program(ns, "", &never_binding(&["PartialEq"]));
    let mut interp = crate::common::interp_for(&src);
    let lp = interp
        .kb()
        .try_resolve_symbol(&format!("{ns}.Loop.lp"))
        .expect("lp");
    let v = interp.kb_mut().intern("v");
    let x = interp.kb_mut().intern("x");
    let vid = interp.kb_mut().fresh_var(x);
    let var = interp.kb_mut().alloc(Term::Var(Var::Global(vid)));
    let open = Value::term(interp.kb_mut().alloc(Term::Fn {
        functor: lp,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(v, var)]),
    }));
    let answer = interp.call("anthill.prelude.PartialEq.eq", &[open.clone(), open]);
    assert!(
        answer
            .as_ref()
            .is_err_and(|e| format!("{e:?}").contains("could not be decided")),
        "undecided, not an answer: {answer:?}"
    );
}

/// A CIRCULAR MEMBER runs, as the routes were left (the member is pinned at load and the
/// binding reached through the builtin, the user's choice): it stops at a step budget where one
/// is set, and not at the bridge's cap. Passes either way by design; it pins the route.
#[test]
fn a_circular_member_runs_to_the_step_budget() {
    let ns = "test.tsys6.member_loop";
    let member = "    operation eq(x: Loop, y: Loop) -> Bool = PartialEq.eq(x, y)\n    \
                  provides PartialEq[T = Loop]\n";
    let src = program(ns, member, "");
    let mut interp = crate::common::interp_for(&src);
    interp.config_mut().step_cap = Some(1_000_000);
    let answer = interp.call(&format!("{ns}.go"), &[]);
    assert!(
        matches!(
            answer,
            Err(anthill_core::eval::EvalError::StepsExhausted { .. })
        ),
        "the step budget: {answer:?}"
    );
}

/// THE MEMBER decides as it always did, and now as the binding does. Passes either way by
/// design: the call by name is pinned to it.
#[test]
fn the_member_decides_identical_operands() {
    let ns = "test.tsys6.member";
    let member =
        "    operation eq(x: Loop, y: Loop) -> Bool = false\n    provides PartialEq[T = Loop]\n";
    let src = program(ns, member, "");
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(0));
}

/// CONTROLS, which pass either way by design: a type that provides `Eq` keeps the reflexivity
/// answer, licensed by `eq_refl` — the binding `neverEq` is not asked, by name or in a rule body;
/// and IEEE `Float` stays `nan != nan`.
#[test]
fn a_type_providing_eq_keeps_reflexivity() {
    let ns = "test.tsys6.lawful";
    let src = program(ns, "", &never_binding(&["PartialEq", "Eq"]));
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(1));
    let mut kb = crate::common::load_kb_with(&src);
    assert_eq!(query_unary(&mut kb, &format!("{ns}.rq")).len(), 1);

    let ns = "test.tsys6.float";
    let src = format!(
        r#"namespace {ns}
  import anthill.prelude.{{Int64, Float, PartialEq}}
  operation go() -> Int64 = if PartialEq.eq(Float.div(0.0, 0.0), Float.div(0.0, 0.0)) then 1 else 0
end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(0));
}

//! WI-529: position-directed resolution of the boolean operators `not`/`or`/`and`
//! plus prefix `-` (`neg`).
//!
//! The decided design (docs/design/kernel-vocab-provenance.md §C.1) splits each
//! boolean operator by syntactic position:
//!
//!   * an **operation body** is value/eval context — `not`/`or`/`and` mean the
//!     dispatched Bool VALUE ops (`Bool.not`/`Bool.or`/`Bool.and`, which have eval
//!     builtins). This is the NEW capability: op-body `not(x)` was broken before
//!     (it resolved to `reflect.not`, the NAF primitive, which has no eval builtin).
//!   * a **rule body goal** is resolver context — `not(goal)` stays
//!     negation-as-failure (`anthill.reflect.not`) and `or(g1,g2)` stays disjunction
//!     (`anthill.kernel.or`), unchanged.
//!
//! `neg` (a new spec op, defaulted to `sub(zero-val, a)`) routes to `Numeric.neg`
//! everywhere (not position-directed). Prefix `-x` SUGAR on non-literals is deferred —
//! it collides with negative-literal lexing (`/-?[0-9]+/`) — so `neg(x)` is the form;
//! negative literals (`-1`, `-0.45`) lex directly and are unaffected.
//!
//! The eval tests below are the load-routing proof: if op-body `not(true)` still
//! resolved to `reflect.not`, eval would error (no eval builtin) rather than yield
//! `false`. The resolver side (rule-body `not` = NAF, `or` = disjunction) is also
//! covered by `push_choice_test` and the typing tests; one NAF test is repeated
//! here to nail the position-direction contrast.

use anthill_core::eval::Value;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, Var};
use smallvec::SmallVec;
use crate::common::{self, interp_for};

fn expect_bool(v: Value) -> bool {
    match v {
        Value::Bool(b) => b,
        other => panic!("expected Bool, got {other:?}"),
    }
}

fn expect_int(v: Value) -> i64 {
    v.as_int().unwrap_or_else(|| panic!("expected Int64, got {v:?}"))
}

const EVAL_SRC: &str = r#"
namespace test.wi529.eval
  import anthill.prelude.{Bool, Int64}
  -- op bodies are evaluated: not/or/and are the dispatched Bool VALUE ops
  operation t_not() -> Bool = not(true)
  operation t_bang() -> Bool = !false
  operation t_and_tt() -> Bool = and(true, true)
  operation t_and_tf() -> Bool = and(true, false)
  operation t_or_ff() -> Bool = or(false, false)
  operation t_or_tf() -> Bool = or(true, false)
  -- `neg` → Numeric.neg. Prefix `-x` SUGAR on non-literals is deferred (collides with
  -- negative-literal lexing); `neg(x)` is the form, negative literals (`-7`) lex directly.
  operation t_neg() -> Int64 = neg(7)
  operation t_negvar(x: Int64) -> Int64 = neg(x)
end
"#;

/// Op-body `not`/`!`/`and`/`or` resolve to the dispatched `Bool` value ops and
/// evaluate. Reaching a Bool result at all proves the routing: `reflect.not` /
/// `kernel.or` have no eval builtin, so a mis-route would error here.
#[test]
fn op_body_boolean_ops_eval_as_bool_values() {
    let mut interp = interp_for(EVAL_SRC);
    let call = |interp: &mut anthill_core::eval::Interpreter, name: &str| {
        interp
            .call(name, &[])
            .unwrap_or_else(|e| panic!("call {name}: {e:?}"))
    };

    assert!(!expect_bool(call(&mut interp, "test.wi529.eval.t_not")), "not(true) = false");
    assert!(expect_bool(call(&mut interp, "test.wi529.eval.t_bang")), "!false = true");
    assert!(expect_bool(call(&mut interp, "test.wi529.eval.t_and_tt")), "and(true, true) = true");
    assert!(!expect_bool(call(&mut interp, "test.wi529.eval.t_and_tf")), "and(true, false) = false");
    assert!(!expect_bool(call(&mut interp, "test.wi529.eval.t_or_ff")), "or(false, false) = false");
    assert!(expect_bool(call(&mut interp, "test.wi529.eval.t_or_tf")), "or(true, false) = true");
}

/// `neg(...)` routes to `Numeric.neg` and evaluates (the new `numeric_neg` builtin
/// handles every Numeric carrier). Prefix `-x` SUGAR on non-literals is deferred — it
/// collides with negative-literal lexing — so `neg(x)` is the form here; negative
/// literals (`-7`) lex directly and are unaffected.
#[test]
fn neg_evals_via_numeric_neg() {
    let mut interp = interp_for(EVAL_SRC);
    let neg = interp
        .call("test.wi529.eval.t_neg", &[])
        .expect("call t_neg");
    assert_eq!(expect_int(neg), -7, "neg(7) = -7");

    let negvar = interp
        .call("test.wi529.eval.t_negvar", &[Value::Int(7)])
        .expect("call t_negvar");
    assert_eq!(expect_int(negvar), -7, "neg(x) with x=7 is -7");
}

/// Contrast: in a RULE BODY, `not(goal)` is still negation-as-failure
/// (`anthill.reflect.not`), unaffected by the op-body Bool routing. `allowed(?x)`
/// holds for the `num` that is not `blocked` — pure NAF semantics.
#[test]
fn rule_body_not_stays_negation_as_failure() {
    let src = r#"
namespace test.wi529.naf
  sort N
    entity n1
    entity n2
  end
  fact num(n1)
  fact num(n2)
  fact blocked(n1)
  rule allowed(?x) :- num(?x), not(blocked(?x))
end
"#;
    let mut kb = common::load_kb_with(src);
    let allowed_sym = kb
        .try_resolve_symbol("test.wi529.naf.allowed")
        .expect("allowed symbol");
    let n2_sym = kb
        .try_resolve_symbol("test.wi529.naf.N.n2")
        .expect("n2 symbol");

    let x_sym = kb.intern("_x");
    let x_vid = kb.fresh_var(x_sym);
    let x_term = kb.alloc(Term::Var(Var::Global(x_vid)));
    let goal = kb.alloc(Term::Fn {
        functor: allowed_sym,
        pos_args: SmallVec::from_slice(&[x_term]),
        named_args: SmallVec::new(),
    });

    let cfg = ResolveConfig::default();
    let solutions = kb.resolve(&[goal], &cfg);
    assert_eq!(solutions.len(), 1, "exactly n2 is allowed (n1 is blocked → NAF fails)");
    let bound = kb.reify(x_term, &solutions[0].subst).expect_term();
    assert_eq!(bound, kb.alloc(Term::Ref(n2_sym)), "allowed binds ?x = n2");
}

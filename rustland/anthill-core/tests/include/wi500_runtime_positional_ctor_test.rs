//! WI-500: RUNTIME-built positional constructors canonicalize to NAMED — the
//! WI-433 never-match bug class on the NON-loader (value→term) path.
//!
//! WI-433 desugared only SOURCE-written terms (the loader). At runtime,
//! `finish_constructor` builds a `Value::Entity` keeping a positional ctor
//! positional, and `alloc_from_value` (the `Value`→`Term` lowering the `persist`
//! builtin uses) used to build `Term::Fn` with `pos_args` VERBATIM. `assert_fact`
//! then stored+indexed that term positionally, so a runtime-built positional
//! entity persisted and queried WITHIN THE SAME PROCESS never unified with the
//! canonical named pattern (`Verified(at: ?)`) — the heimdall WI-005 symptom on
//! the runtime path.
//!
//! Fix: a shared `positional_to_named_plan` (the loader's rank-among-not-named
//! rule) applied at the value→term boundary (`alloc_from_value` + the Node-aware
//! `value_to_term`), so a runtime positional entity lowers to the SAME named
//! shape the loader produces.

use anthill_core::eval::value::Value;
use anthill_core::eval::Interpreter;
use anthill_core::kb::term::{Literal, Term};
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::resolve::ResolveConfig;
use smallvec::SmallVec;
use std::rc::Rc;

fn config() -> ResolveConfig {
    ResolveConfig { max_solutions: 10, ..ResolveConfig::default() }
}

/// Resolve the CANONICAL named query `Verified(at: <at>)` and count solutions.
/// A concrete-literal pattern matches only a stored `Verified(at: "now")` fact,
/// so this is a clean 0→1 signal for the runtime fact. (WI-515: the loader's
/// entity-schema fact the literal also used to exclude is no longer asserted.)
fn resolve_verified_at(kb: &mut KnowledgeBase, at: &str) -> usize {
    let f = kb.resolve_symbol("test.wi500.Status.Verified");
    let at_sym = kb.intern("at");
    let val = kb.alloc(Term::Const(Literal::String(at.to_string())));
    let q = kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_elem((at_sym, val), 1),
    });
    kb.resolve(&[q], &config()).len()
}

/// Build the positional `Value::Entity { Verified, pos: ["now"], named: [] }`
/// that an op-body `Verified("now")` evaluates to (`finish_constructor` keeps it
/// positional).
fn positional_verified(kb: &KnowledgeBase, at: &str) -> Value {
    Value::Entity {
        functor: kb.resolve_symbol("test.wi500.Status.Verified"),
        pos: Rc::from(vec![Value::Str(at.to_string())]),
        named: Rc::from(Vec::<(_, _)>::new()),
    }
}

const SRC: &str = r#"
namespace test.wi500
  import anthill.prelude.String
  sort Status
    import anthill.prelude.String
    entity Verified(at: String)
  end
  operation mk() -> Status
    = Verified("now")
end
"#;

/// `alloc_from_value` lowers a positional entity to the canonical NAMED term:
/// empty `pos_args`, `named_args = [(at, "now")]`.
#[test]
fn alloc_from_value_desugars_positional_to_named() {
    let mut kb = crate::common::load_kb_with(SRC);
    let v = positional_verified(&kb, "now");
    let t = kb.alloc_from_value(&v).expect("lower positional entity");
    match kb.get_term(t) {
        Term::Fn { pos_args, named_args, .. } => {
            assert!(pos_args.is_empty(), "positional args must be desugared away, got {pos_args:?}");
            assert_eq!(named_args.len(), 1, "exactly the one declared field");
            let (field, _) = named_args[0];
            assert_eq!(kb.resolve_sym(field), "at", "positional arg fills the declared `at` field");
        }
        other => panic!("expected Term::Fn, got {other:?}"),
    }
}

/// The acceptance: a runtime positional `Verified("now")` persisted
/// (`alloc_from_value` → `assert_fact`) then matched against the named
/// `Verified(at: ?)` pattern in ONE process succeeds.
#[test]
fn persisted_positional_entity_matches_named_pattern() {
    let mut kb = crate::common::load_kb_with(SRC);
    let v = positional_verified(&kb, "now");
    // Exactly the persist builtin's lowering: value → term → assert_fact.
    let t = kb.alloc_from_value(&v).expect("lower positional entity");
    let sort = kb.make_name_term("Fact");
    let domain = kb.make_name_term("test.wi500");
    kb.assert_fact(t, sort, domain, None);
    assert_eq!(
        resolve_verified_at(&mut kb, "now"),
        1,
        "runtime positional Verified(\"now\") must match the named Verified(at: \"now\") pattern",
    );
}

/// End-to-end: evaluate the op-body `Verified("now")` to a runtime `Value`, then
/// persist+match it — faithful to the work item's "runtime op-body" wording.
#[test]
fn op_body_positional_ctor_persisted_matches() {
    let kb = crate::common::load_kb_with(SRC);
    let mut interp = Interpreter::new(kb);
    let v = interp.call("test.wi500.mk", &[]).expect("call mk");
    let t = interp.kb_mut().alloc_from_value(&v).expect("lower op result");
    let sort = interp.kb_mut().make_name_term("Fact");
    let domain = interp.kb_mut().make_name_term("test.wi500");
    interp.kb_mut().assert_fact(t, sort, domain, None);
    assert_eq!(
        resolve_verified_at(interp.kb_mut(), "now"),
        1,
        "op-body Verified(\"now\") result must match the named Verified(at: \"now\") pattern",
    );
}

/// LOUD at the runtime boundary too: a positional entity with more positional
/// args than the entity's fields is a hard lowering error (never a silent
/// never-match), mirroring the loader's over-arity load error.
#[test]
fn over_arity_runtime_ctor_is_loud() {
    let mut kb = crate::common::load_kb_with(SRC);
    let v = Value::Entity {
        functor: kb.resolve_symbol("test.wi500.Status.Verified"),
        pos: Rc::from(vec![Value::Str("now".into()), Value::Str("extra".into())]),
        named: Rc::from(Vec::<(_, _)>::new()),
    };
    match kb.alloc_from_value(&v) {
        Ok(_) => panic!("Verified(\"now\", \"extra\") (2 args, 1 field) must fail to lower"),
        Err(e) => {
            let msg = e.to_string();
            assert!(
                msg.contains("Verified") && msg.contains("at"),
                "the arity error must name the constructor and its declared field; got: {msg}",
            );
        }
    }
}

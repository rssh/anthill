//! WI-919 — A STORE'S DECLARED POLICY IS RESOLVED AT REGISTRATION, LIKE A MOUNT'S NAME.
//!
//! A `Store` declares its intrinsic per-functor write policy as `(qualified functor
//! name, policy)` pairs (`Store::owned_monotonicity`), and that is the right boundary: a
//! backend can only speak names. What was wrong is where the name was READ. The table
//! stayed String-keyed, so the guard rendered an already-resolved `Symbol` back to text
//! on every ask — `qualified_name_of(functor)` — and any spelling the two sides did not
//! share simply missed. A miss is `.unwrap_or(Monotonicity::Monotone)`, precedence rung
//! 3, which the proposal-053 retract guard refuses.
//!
//! DRIVEN before the fix, with a store declaring the SHORT name `Ghost` for a KB whose
//! functor is `test.syn.Ghost`:
//!
//!     registration = accepted, silently
//!     monotonicity = anthill.reflect.Monotonicity.monotone   <- rung 3, i.e. a miss
//!     retract      = Err(Raised("retract refused: functor `test.syn.Ghost` is not
//!                                non_monotone (proposal 053)"))
//!
//! The author declared exactly that policy and is told their functor does not have it.
//! Nothing in the message mentions a store, a declaration, or a spelling — a policy
//! VERDICT for a policy that was declared, one spelling away. The control run (same
//! store, qualified spelling) retracts `Ok(true)`.
//!
//! THE FIX MOVES THE READ, NOT THE BOUNDARY. `register_mirror` resolves each declared
//! name once — the rule `register_extent_owner` already followed for a mount's `owned()`
//! names, in the same `ExtentRegError` vocabulary — and keys the table on `Symbol`. So
//! the guard asks with the symbol it already holds, and rung 3's `monotone` now means
//! only what rung 3 says: no store spoke for this functor.
//!
//! WHY THE REFUSAL IS A REFUSAL and not a dropped entry: the reader cannot tell a
//! dropped entry from a functor no store declared, so a silent drop IS the defect above,
//! deferred to the next retract. The cost is that declaring a policy for a functor this
//! KB does not have is no longer expressible; no in-tree backend does it (the filesystem
//! stores declare none at all), and the field's old comment — "a backend may name a
//! functor that is only interned after bootstrap" — describes no live caller: the one
//! production registration (anthill-todo) happens after the project is loaded.
//!
//! WHAT EACH TEST IS FOR. The first two pin the two refusals. The third is the CONTROL,
//! green on BOTH sides: the same store under the spelling that matches still registers
//! AND still reaches the guard, so the refusals above are about the name and not about
//! the policy path having stopped working. `wi667_store_monotonicity_test` is the wider
//! both-sides control — every one of its cases registers a mirror.
//!
//! STDLIB LOADS: three, one per `#[test]`.

use anthill_core::eval::{Interpreter, Value};
use anthill_core::intern::Symbol;
use anthill_core::kb::extent::ExtentRegError;
use anthill_core::kb::term::TermId;
use anthill_core::kb::{KnowledgeBase, RuleId};
use anthill_core::persistence::{Monotonicity, PersistenceError, Store};

use crate::common::interp_for;

/// A store that is the authority for its own functor, declaring the policy intrinsically
/// rather than through the project's reflect rules — the WI-667 `PolicyStore` shape,
/// reduced to what this suite needs (its retract always succeeds, so a refusal here can
/// only come from the guard).
struct PolicyStore {
    /// The spelling this backend uses for the functor it owns. THE variable under test.
    functor: String,
    policy: Monotonicity,
}

impl Store for PolicyStore {
    fn persist(&mut self, _kb: &KnowledgeBase, _f: TermId, _s: Symbol, _d: Symbol, _m: Option<TermId>)
        -> Result<(), PersistenceError> { Ok(()) }
    fn retract(&mut self, _kb: &KnowledgeBase, _id: RuleId) -> Result<bool, PersistenceError> {
        Ok(true)
    }
    fn flush(&mut self, _kb: &KnowledgeBase) -> Result<(), PersistenceError> { Ok(()) }
    fn owned_monotonicity(&self) -> Vec<(String, Monotonicity)> {
        vec![(self.functor.clone(), self.policy)]
    }
}

/// Register a `PolicyStore` declaring `functor` as `non_monotone`, returning the store
/// value and the registration's verdict.
fn register_declaring(
    interp: &mut Interpreter,
    functor: &str,
) -> (Value, Result<(), ExtentRegError>) {
    let store_functor = interp.kb_mut().intern("PolicyStore");
    let store_val = Value::Entity { functor: store_functor, pos: vec![].into(), named: vec![].into() };
    let key = interp.store_canonical_key(&store_val).expect("canonical key");
    let outcome = interp.register_mirror(key, Box::new(PolicyStore {
        functor: functor.to_owned(),
        policy: Monotonicity::NonMonotone,
    }));
    (store_val, outcome)
}

/// A nullary carrier headed by the declared entity `qname` — the fact to persist.
fn functor_value(interp: &mut Interpreter, qname: &str) -> Value {
    let sym = interp.kb_mut().try_resolve_symbol(qname)
        .unwrap_or_else(|| panic!("resolve `{qname}`"));
    Value::Entity { functor: sym, pos: vec![].into(), named: vec![].into() }
}

/// Persist `fact` through `store`, then retract it through the reference that came back.
fn persist_then_retract(interp: &mut Interpreter, store: &Value, fact: Value) -> Value {
    let stored = interp
        .call("anthill.persistence.Store.persist", &[store.clone(), fact, Value::Unit])
        .expect("persist ok");
    let reference_field = interp.kb_mut().intern("reference");
    let reference = match &stored {
        Value::Entity { named, .. } => named.iter()
            .find(|(name, _)| *name == reference_field)
            .map(|(_, value)| value.clone())
            .expect("StoredRef carries reference"),
        other => panic!("persist must return StoredRef, got {other:?}"),
    };
    interp
        .call("anthill.persistence.NonMonotonicStore.retract", &[store.clone(), reference])
        .expect("the store declared non_monotone, so the guard passes")
}

const GHOST: &str = "namespace test.syn\n  entity Ghost\nend\n";

/// THE DEFECT. `Ghost` is what the backend calls it; `test.syn.Ghost` is what the KB
/// does, and nothing brings the short name into scope at `_global`. Pre-fix that
/// disagreement was invisible until a retract reported it as a policy verdict.
#[test]
fn a_store_policy_named_by_an_unmatched_spelling_is_refused_at_registration() {
    let mut interp = interp_for(GHOST);

    let (_store, outcome) = register_declaring(&mut interp, "Ghost");

    let err = outcome.expect_err(
        "the declared name denotes no functor here, so the policy would reach nothing \
         — pre-fix this registered silently and surfaced at the retract as \
         'functor `test.syn.Ghost` is not non_monotone'",
    );
    match err {
        ExtentRegError::UnresolvableName(name) => assert_eq!(
            name, "Ghost",
            "and the refusal must name the spelling nobody resolved — that string is \
             the only thing the author can fix",
        ),
        other => panic!("expected UnresolvableName naming the declaration; got {other:?}"),
    }
}

/// The other half of the name question, at this registration site as at every other
/// (WI-907/916/917): a name that denotes SEVERAL things is a different fault from one
/// that denotes none, and reporting it as absent sends the author to declare a third.
/// Pre-fix this registration was likewise accepted in silence (measured).
#[test]
fn a_store_policy_naming_a_contested_functor_is_refused_as_ambiguous() {
    let mut interp = interp_for(
        "namespace wi919.alpha\n  entity Widget919\nend\n\
         namespace wi919.beta\n  entity Widget919\nend\n\
         import wi919.alpha.*\nimport wi919.beta.*\n",
    );

    let (_store, outcome) = register_declaring(&mut interp, "Widget919");

    let err = outcome.expect_err("a contested name denotes no single functor to key on");
    match err {
        ExtentRegError::AmbiguousName { candidates, .. } => assert_eq!(
            candidates,
            vec!["wi919.alpha.Widget919".to_owned(), "wi919.beta.Widget919".to_owned()],
            "and it must name what it could not choose between",
        ),
        other => panic!("expected AmbiguousName; got {other:?}"),
    }
}

/// CONTROL, green on BOTH sides of the fix: the SAME store under the spelling the KB
/// shares registers, and its declared policy still carries the retract past the
/// proposal-053 guard (which would refuse under the `monotone` default). This is what
/// makes the two refusals above findings about the NAME rather than about the policy
/// path — and it is the end-to-end assertion that a `Symbol`-keyed table still answers.
#[test]
fn the_matching_declaration_registers_and_still_reaches_the_retract_guard() {
    let mut interp = interp_for(GHOST);

    let (store, outcome) = register_declaring(&mut interp, "test.syn.Ghost");
    outcome.expect("the declared name is exactly the functor's qualified name");

    let fact = functor_value(&mut interp, "test.syn.Ghost");
    assert!(
        matches!(persist_then_retract(&mut interp, &store, fact), Value::Bool(true)),
        "the store's declared non_monotone must still reach the guard",
    );
}

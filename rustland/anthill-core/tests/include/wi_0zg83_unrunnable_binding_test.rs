//! WI-20260828-0ZG83 — a `language rust` binding this runtime cannot run is reported at
//! the call it backs, and the rest of the program runs.
//!
//! Before: building an interpreter validated every `operation_map` / `const_map` entry,
//! and one key the runtime lacked — an embedder's (WI-1122), in a runtime that embedder
//! did not build — refused the build with an `EvalError::Internal`. A rule body builds an
//! interpreter per bridged evaluation, so `?r <=> plain(1)` over a program that also
//! maps `squish` to an embedder's key panicked (`bridged_value`'s `debug_assert!` on
//! `Internal`), and so did a bodied `eq` dispatch (`bridge_eq_op_to_eval`); `anthill run`
//! refused every entry. Now an unrunnable mapping registers an entry that raises
//! `EvalError::UnrunnableHostBinding` when called (kernel-language.md §10.2).
//!
//! WHICH ROWS FAIL WITH THE CHANGE BACKED OUT, measured with a temporary switch that
//! restores the refusal at interpreter build (a panic, as a debug build's bridge gave),
//! and with the pre-change binary on the same programs:
//!   * the four rows that build an interpreter over `PROGRAM` —
//!     `an_unrunnable_binding_does_not_stop_an_unrelated_goal`,
//!     `a_goal_that_reaches_the_binding_is_reported_at_it`,
//!     `a_goal_that_forces_the_const_is_reported_at_it` and
//!     `an_operation_body_runs_beside_the_binding`;
//!   * with `force_const`'s host branch keeping its `Forcing` mark on an error,
//!     `an_operation_body_runs_beside_the_binding` alone, at the second force of `seed`
//!     (`ConstCycle`).
//! `the_stdlib_writes_no_binding_this_runtime_cannot_run` and
//! `unrunnable_bindings_names_each_reason` read `builtins::unrunnable_bindings`, which
//! this change adds. `the_same_program_runs_once_the_embedder_registers_its_keys` is
//! the control: with the keys registered it passes under both, so the other rows
//! measure the keys and not the program's shape (it fails with WI-1122's embedder leg
//! backed out, which is what it registers through).

use anthill_core::eval::{Interpreter, UnrunnableHostBindingWhy, Value};
use anthill_core::kb::resolve::ResolveConfig;

/// An operation and a const bound to keys no registry has, beside code that reaches
/// neither and code that reaches each.
const PROGRAM: &str = r#"
namespace test.zg83
  import anthill.prelude.{Int64, Bool, Eq, PartialEq}
  import anthill.prelude.PartialEq.{eq}
  sort W
    entity w(n: Int64)
    operation squish(x: W) -> Int64 @[host_implemented]
    const seed: Int64
  end
  provides W language rust
    artifact "nowhere.rs"
    operation_map { squish: "zg83_squish" }
    const_map { seed: "zg83_seed" }
  end
  -- A bodied `eq`: comparing two `Tagged` builds an interpreter to run it.
  sort Tagged
    entity tagged(key: Int64, note: Int64)
  end
  operation taggedEq(x: Tagged, y: Tagged) -> Bool =
    match x
      case tagged(k1, n1) ->
        match y
          case tagged(k2, n2) -> eq(k1, k2)
  namespace Tagged
    provides PartialEq[T = Tagged, eq = taggedEq]
    provides Eq[T = Tagged, eq = taggedEq]
  end
  operation plain(x: Int64) -> Int64 = x + 1
  operation viaSquish(x: Int64) -> Int64 = W.squish(w(n: x))
  operation viaSeed(x: Int64) -> Int64 = W.seed + x
  rule other(?r) :- ?r <=> plain(1)
  rule sameTag() :- tagged(key: 1, note: 9) = tagged(key: 1, note: 8)
  rule uses(?r) :- ?r <=> W.squish(w(n: 3))
  rule seeded(?r) :- ?r <=> viaSeed(1)
  rule never() :- not(W.squish(w(n: 3)) = 4)
end
"#;

fn int(interp: &Interpreter, v: &Value) -> i64 {
    crate::common::scalar_int(interp.kb(), v).unwrap_or_else(|| panic!("an Int64, got {v:?}"))
}

/// The goals that reach no binding are decided as they would be without it: a bodied
/// operation bridged from a rule body, and a bodied `eq` the comparison dispatches to.
#[test]
fn an_unrunnable_binding_does_not_stop_an_unrelated_goal() {
    let (sols, faults) = crate::common::resolve_with_messages(PROGRAM, "test.zg83.other(?r)");
    assert_eq!(sols.len(), 1, "one answer: {faults:?}");
    assert!(
        sols[0].residual.is_empty(),
        "decided, not residual: {:?}",
        sols[0].residual
    );
    assert!(faults.is_empty(), "nothing reported: {faults:?}");

    let (sols, faults) = crate::common::resolve_with_messages(PROGRAM, "test.zg83.sameTag()");
    assert_eq!(
        (sols.len(), faults.len()),
        (1, 0),
        "`taggedEq` compares the keys only, so the two are equal: {faults:?}"
    );
}

/// A goal that reaches the operation's binding has no value there, and is told why,
/// naming the operation and the key; a negation over it proves nothing.
#[test]
fn a_goal_that_reaches_the_binding_is_reported_at_it() {
    let (sols, faults) = crate::common::resolve_with_messages(PROGRAM, "test.zg83.uses(?r)");
    assert!(
        sols.iter().all(|s| !s.residual.is_empty()),
        "no decided answer: {} answers",
        sols.len()
    );
    assert!(
        faults.iter().any(|m| m.contains(
            "`test.zg83.W.squish` could not be evaluated by the resolver: its `language \
             rust` binding (`operation_map`) names host function \"zg83_squish\", which \
             this runtime does not provide"
        )),
        "the fault names the operation and the key: {faults:?}"
    );

    let (sols, faults) = crate::common::resolve_with_messages(PROGRAM, "test.zg83.never()");
    assert!(
        sols.iter().all(|s| !s.residual.is_empty()),
        "`not(…)` over a call with no value is undecided, not proved: {} answers",
        sols.len()
    );
    assert!(!faults.is_empty(), "and the search says why");
}

/// The const peer: a goal whose evaluation forces the const is told the const and its key.
#[test]
fn a_goal_that_forces_the_const_is_reported_at_it() {
    let faults = crate::common::fault_messages(PROGRAM, "test.zg83.seeded(?r)");
    assert!(
        faults.iter().any(|m| m.contains(
            "`test.zg83.viaSeed` could not be evaluated by the resolver: `test.zg83.W.seed` \
             has no value here: its `language rust` binding (`const_map`) names host value \
             \"zg83_seed\", which this runtime does not provide"
        )),
        "the fault names the const and the key: {faults:?}"
    );
}

/// From an operation body: the interpreter is built, an operation that reaches no binding
/// runs, and each that reaches one raises `UnrunnableHostBinding` at the call — at every
/// call. A const's value source that raised once used to leave the const marked as being
/// forced, so its second force was reported as a cycle (`ConstCycle`).
#[test]
fn an_operation_body_runs_beside_the_binding() {
    let mut interp = crate::common::interp_for(PROGRAM);
    let v = interp
        .call("test.zg83.plain", &[Value::Int(1)])
        .expect("an operation that reaches no binding runs");
    assert_eq!(int(&interp, &v), 2);

    // Each twice: the second call meets the binding again, not a state the first left.
    for (entry, mapped, key) in [
        ("test.zg83.viaSquish", "test.zg83.W.squish", "zg83_squish"),
        ("test.zg83.viaSquish", "test.zg83.W.squish", "zg83_squish"),
        ("test.zg83.viaSeed", "test.zg83.W.seed", "zg83_seed"),
        ("test.zg83.viaSeed", "test.zg83.W.seed", "zg83_seed"),
    ] {
        let b = crate::common::unrunnable_at_call(&mut interp, entry, &[Value::Int(3)]);
        assert_eq!(
            (b.mapped.as_str(), b.key.as_str()),
            (mapped, key),
            "{entry}"
        );
    }
}

/// The list an embedder asks for before any call: both bindings, each with its reason.
#[test]
fn unrunnable_bindings_names_each_reason() {
    let kb = crate::common::load_kb_with(PROGRAM);
    let found: Vec<(String, String, String)> =
        anthill_core::eval::builtins::unrunnable_bindings(&kb)
            .into_iter()
            .map(|b| (b.mapped, b.key, format!("{:?}", b.why)))
            .collect();
    assert_eq!(
        found,
        vec![
            (
                "test.zg83.W.squish".to_string(),
                "zg83_squish".to_string(),
                format!("{:?}", UnrunnableHostBindingWhy::UnknownFunction),
            ),
            (
                "test.zg83.W.seed".to_string(),
                "zg83_seed".to_string(),
                format!("{:?}", UnrunnableHostBindingWhy::UnknownValue),
            ),
        ]
    );

    // The two disagreements with a key this runtime does have: `ordered_compare` takes
    // two arguments, where `squish` takes one and a const's value source none.
    let kb = crate::common::load_kb_with(
        &PROGRAM
            .replace("\"zg83_squish\"", "\"ordered_compare\"")
            .replace("\"zg83_seed\"", "\"ordered_compare\""),
    );
    let whys: Vec<String> = anthill_core::eval::builtins::unrunnable_bindings(&kb)
        .into_iter()
        .map(|b| format!("{:?}", b.why))
        .collect();
    assert_eq!(
        whys,
        vec![
            format!(
                "{:?}",
                UnrunnableHostBindingWhy::ArityDisagrees {
                    declared: 1,
                    host: 2
                }
            ),
            format!("{:?}", UnrunnableHostBindingWhy::NotNullary { host: 2 }),
        ]
    );
}

/// The library this runtime ships writes no key it lacks: the check a build used to make
/// for every program, kept for the one whose keys this runtime owns.
#[test]
fn the_stdlib_writes_no_binding_this_runtime_cannot_run() {
    let kb = crate::common::load_stdlib_kb();
    let unrunnable = anthill_core::eval::builtins::unrunnable_bindings(&kb);
    assert!(unrunnable.is_empty(), "{unrunnable:?}");
}

/// THE CONTROL: the same program, its two keys registered by the embedder before the load,
/// runs every call and lists no unrunnable binding. NOT THE RECIPE, BY NAME: an embedder
/// registers before the load (WI-1122), so this load is a fresh one, off the shared base.
#[test]
fn the_same_program_runs_once_the_embedder_registers_its_keys() {
    let kb = crate::common::try_load_kb_prepared(PROGRAM, |kb| {
        kb.register_host_fn("zg83_squish", 1, |_i, _a| Ok(Value::Int(40)))
            .expect("a fresh key registers");
        kb.register_host_fn("zg83_seed", 0, |_i, _a| Ok(Value::Int(7)))
            .expect("a fresh key registers");
    })
    .unwrap_or_else(|errs| panic!("a clean load: {errs:?}"));
    assert!(anthill_core::eval::builtins::unrunnable_bindings(&kb).is_empty());

    let mut kb = kb;
    let goal = crate::common::query_pattern_term(&mut kb, "test.zg83.uses(40)");
    assert_eq!(kb.resolve(&[goal], &ResolveConfig::default()).len(), 1);

    let mut interp = Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp);
    for (entry, want) in [("test.zg83.viaSquish", 40), ("test.zg83.viaSeed", 10)] {
        let v = interp
            .call(entry, &[Value::Int(3)])
            .unwrap_or_else(|e| panic!("`{entry}` runs: {e}"));
        assert_eq!(int(&interp, &v), want, "{entry}");
    }
}

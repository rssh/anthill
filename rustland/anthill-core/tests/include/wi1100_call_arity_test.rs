//! WI-1100 — an operation call's ARGUMENT COUNT is checked at LOAD.
//!
//! THE DEFECT. Nothing compared a call's argument count against the callee's
//! declaration. `check_apply_iter`'s Path 1 reads `written_params.get(i)` per positional
//! argument, so a SURPLUS argument matched no parameter and was skipped; a MISSING one
//! left a parameter with nothing to check against. MEASURED against the built CLI, both
//! directions, host-backed and anthill-defined:
//!
//! ```anthill
//! operation four_args() -> String = concat("a", "b", "c", "d")   -- concat is BINARY
//! operation one_arg()   -> String = concat("a")
//! ```
//!
//! `anthill load` answered `loaded: 2602 facts, 176 rules` and `anthill check` answered
//! `128 pass, 0 failed`. Both answers that followed were wrong in a different way:
//!
//!   * **The evaluator caught it, LATE.** `EvalError::ArityMismatch` fires when the call
//!     actually runs — so the error existed, deferred to whichever execution first
//!     reached that expression.
//!   * **The resolver swallowed it.** `anthill query 'probe.arity.Probe.four_args()'`
//!     answered `no solutions` — a wrong-arity call on the resolution path was
//!     indistinguishable from a goal that legitimately has no answer.
//!
//! WHY IT IS NOT ACADEMIC. WI-1097's duplicate-id store gate built its refusal message
//! with a four-argument `concat`. The bundle loaded, the binary built, and the whole
//! `anthill-todo` suite stayed green — because no test drove a store that actually HAD a
//! duplicate. The error path of an error-detection gate was itself broken, and only a
//! test that drove the refusal found it. Any diagnostic branch carries that exposure.
//!
//! THE RULE, and it is the spec's own: "the argument **count** must equal the declared
//! arity" (kernel §"Applying a function value checks its arguments", which states it of
//! an arrow application by saying such a call "is checked exactly as calling a named
//! operation is" — the thing that was not true). Named arguments make it a coverage
//! question rather than an integer compare: every declared slot filled exactly once, and
//! no argument occupying a slot that does not exist. It is decided off the binding
//! `bind_call_arguments` already computed for the WI-426 label checks
//! ([`call_arity_error`], kb/typing.rs), so one pairing of arguments to slots answers
//! both.
//!
//! THE ONE TOLERANCE, and it is a reading rather than a hole: a rule body's goal may be
//! written at the operation's arity + 1 — the FUNCTIONAL-RELATION view (§5.3, WI-938),
//! where the last positional column receives the result. That is the shape WI-1043's
//! rule-body spec-op dispatch is written in, and `a_rule_body_relational_goal_still_loads`
//! below is its control here. Everything else, in a rule body and an operation body alike,
//! is refused.
//!
//! WI-1100 scoped that tolerance by a PER-RULE flag rather than by position, so it also
//! admitted a VALUE-position rule-body call over-applied by exactly one — one position of
//! this very defect. **WI-1104 CLOSED IT**: the gate is now `NodePos`, which rides the
//! typer's work-stack frame and so answers per node, and the same ticket type-checks the
//! admitted column against the callee's declared RETURN. The two controls below are
//! unchanged by it and are its regression net — this file's relational goal must still
//! load in BOTH spellings, the dotted one being the path whose position must survive the
//! `DotApply` → synthesized-`Apply` lowering. See `wi1104_relational_column_test`.
//!
//! WHAT FAILS IF THIS IS BACKED OUT — MEASURED, two reverts, two runs:
//!
//! | test | the arity check | the rule-body tolerance |
//! |---|---|---|
//! | `a_host_backed_binary_call_with_four_arguments_is_refused` | **FAILS** (loads clean) | ok |
//! | `a_host_backed_binary_call_with_one_argument_is_refused` | **FAILS** (loads clean) | ok |
//! | `an_anthill_defined_operation_is_refused_in_both_directions` | **FAILS** (loads clean) | ok |
//! | `a_named_argument_naming_no_parameter_leaves_a_slot_unfilled` | **FAILS** (label half alone) | ok |
//! | `a_wrong_arity_dot_call_is_refused` | **FAILS** (loads clean) | ok |
//! | `a_wrong_arity_goal_never_reaches_the_resolver` | **FAILS** (loads clean) | ok |
//! | `a_rule_body_goal_two_over_the_arity_is_still_refused` | **FAILS** (loads clean) | ok |
//! | `a_capture_op_counts_only_what_the_author_writes` | **FAILS** (loads clean) | ok |
//! | `a_rule_body_relational_goal_still_loads` | ok | **FAILS** (refused) |
//! | `wi1043…::one_supplier_answers_the_supplied_impl_in_a_rule_body` | ok | **FAILS** |
//! | `wi1035…::one_supplier_through_a_dot_still_reaches_the_own_member` | ok | **FAILS** |
//! | the three remaining CONTROLS below | ok | ok |
//!
//! The second column is 17 failures across five files: this one, plus every rule-body
//! answer in `wi1026` / `wi1035` / `wi1043` / `wi1044` — the relational goal is what
//! those tickets' whole subject is written in. Two of their refusal tests pass either
//! way and are NOT columns here, because without the tolerance they are refused for the
//! wrong reason (arity, not a supplier tie).
//!
//! The controls pass either way BY DESIGN — they are the false-positive half, and the
//! `...`-capture one is the shape most likely to break: a variadic capture parameter is
//! a declared slot that no argument names (`r.fix()`), filled by the WI-727 rewrite
//! rather than by the caller.
//!
//! THE PREDICTED OFFENDERS DID NOT MATERIALIZE. The ticket expected the check to refuse
//! files that load today ("finding some is the point"). MEASURED twice: the full
//! workspace suite (4767 tests, every crate's fixtures) and a direct `anthill load`
//! sweep over all fourteen `.anthill` projects in the repo — stdlib, `anthill-testcases`,
//! both `examples/classic-mini`, `examples/github-todo`, `examples/sql-store`,
//! `examples/webots-modelling/lf1`, `anthill-todo`, and the three crate bundles.
//! **Zero**. The one offender that motivated the ticket, WI-1097's four-argument
//! `concat`, was fixed when WI-1097 was delivered.

use crate::common::try_load_kb_with;

fn refusal(src: &str) -> String {
    match try_load_kb_with(src) {
        Ok(_) => panic!("expected a load refusal, but the program loaded clean"),
        Err(errs) => errs.join(" | "),
    }
}

fn loads(src: &str) {
    if let Err(errs) = try_load_kb_with(src) {
        panic!("expected a clean load, got: {}", errs.join(" | "));
    }
}

// ── the refusals: the count is checked, both directions ─────────────────────

/// THE HEADLINE, and the exact program the ticket measured loading clean. `concat` is
/// declared `(a: String, b: String)` and host-backed, so this also pins that the check
/// reads the DECLARATION and not the host mapping.
#[test]
fn a_host_backed_binary_call_with_four_arguments_is_refused() {
    let msg = refusal(
        r#"
namespace test.wi1100.many
  import anthill.prelude.String.{concat}
  operation four_args() -> String = concat("a", "b", "c", "d")
end
"#,
    );
    assert!(
        msg.contains("expected 2 arguments") && msg.contains("got 4 arguments"),
        "the diagnostic must state the declared arity AND the count given; got: {msg}",
    );
    assert!(
        msg.contains("anthill.prelude.String.concat"),
        "and name the operation; got: {msg}",
    );
}

/// TOO FEW, not just too many — the direction that produced no evaluator trap either
/// until the call ran, and the one a "surplus arguments" check alone would miss. The
/// unfilled parameter is named, because with named arguments in play the count alone
/// does not say which slot is empty.
#[test]
fn a_host_backed_binary_call_with_one_argument_is_refused() {
    let msg = refusal(
        r#"
namespace test.wi1100.few
  import anthill.prelude.String.{concat}
  operation one_arg() -> String = concat("a")
end
"#,
    );
    assert!(
        msg.contains("expected 2 arguments") && msg.contains("got 1 argument"),
        "got: {msg}",
    );
    assert!(
        msg.contains("no argument fills parameter `b`"),
        "the unfilled parameter must be named; got: {msg}",
    );
}

/// An anthill-DEFINED operation, both directions in one program — this is what pins the
/// rule to DECLARATIONS rather than to host mappings. Both calls are reported: the
/// refusal is per call site, not the first one found.
#[test]
fn an_anthill_defined_operation_is_refused_in_both_directions() {
    let msg = refusal(
        r#"
namespace test.wi1100.own
  import anthill.prelude.{Int64}
  operation pair(a: Int64, b: Int64) -> Int64 = a
  operation too_many() -> Int64 = pair(1, 2, 3)
  operation too_few() -> Int64 = pair(1)
end
"#,
    );
    assert!(
        msg.contains("got 3 arguments"),
        "the over-applied call; got: {msg}",
    );
    assert!(
        msg.contains("got 1 argument; no argument fills parameter `b`"),
        "the under-applied call; got: {msg}",
    );
    assert!(
        msg.contains("test.wi1100.own.pair"),
        "both naming the callee; got: {msg}",
    );
}

/// A LABEL cannot smuggle a slot past the check either: the count is right and a
/// parameter is still empty, because one label named a parameter that does not exist.
/// Both facts are reported — they say different true things about the call.
#[test]
fn a_named_argument_naming_no_parameter_leaves_a_slot_unfilled() {
    let msg = refusal(
        r#"
namespace test.wi1100.label
  import anthill.prelude.{Int64}
  operation pair(a: Int64, b: Int64) -> Int64 = a
  operation drive() -> Int64 = pair(a: 1, bogus: 2)
end
"#,
    );
    assert!(
        msg.contains("named argument 'bogus' names no parameter"),
        "the label half; got: {msg}",
    );
    assert!(
        msg.contains("no argument fills parameter `b`"),
        "the arity half — the count is 2 and a slot is still empty; got: {msg}",
    );
}

/// The DOT spelling reaches the same check: the receiver is the first slot, so
/// `x.describe(1)` on a one-parameter member is two arguments against one declaration.
#[test]
fn a_wrong_arity_dot_call_is_refused() {
    let msg = refusal(
        r#"
namespace test.wi1100.dot
  import anthill.prelude.{Int64}
  sort Box
    entity box(v: Int64)
    operation get(b: Box) -> Int64 = b.v
  end
  operation drive() -> Int64 = box(v: 1).get(2)
end
"#,
    );
    assert!(
        msg.contains("expected 1 argument") && msg.contains("got 2 arguments"),
        "got: {msg}",
    );
}

/// THE RESOLVER BULLET. The ticket's `anthill query …` answered `no solutions` for a
/// wrong-arity goal — silence indistinguishable from a goal with no answer. There is
/// nothing to re-drive after the fix and that is the point: the file carrying the call
/// never loads, so no query over it can be asked. Asserted as the refusal.
#[test]
fn a_wrong_arity_goal_never_reaches_the_resolver() {
    let src = r#"
namespace test.wi1100.query
  import anthill.prelude.String.{concat}
  sort Probe
    operation four_args() -> String = concat("a", "b", "c", "d")
  end
end
"#;
    assert!(
        try_load_kb_with(src).is_err(),
        "the KB the query would run against is never built",
    );
}

// ── the controls: what must still load ──────────────────────────────────────

/// The exact-count call, positional. Passes either way by design.
#[test]
fn a_correct_arity_call_still_loads() {
    loads(
        r#"
namespace test.wi1100.ok
  import anthill.prelude.String.{concat}
  import anthill.prelude.{Int64}
  operation pair(a: Int64, b: Int64) -> Int64 = a
  operation drive() -> String = concat("a", "b")
  operation drive2() -> Int64 = pair(1, 2)
end
"#,
    );
}

/// NAMED arguments, including a PERMUTED list — the slots are filled by label, so the
/// coverage and not the position is what the check reads. Passes either way by design.
#[test]
fn a_named_and_permuted_call_still_loads() {
    loads(
        r#"
namespace test.wi1100.named
  import anthill.prelude.{Int64}
  operation pair(a: Int64, b: Int64) -> Int64 = a
  operation all_named() -> Int64 = pair(a: 1, b: 2)
  operation permuted() -> Int64 = pair(b: 2, a: 1)
  operation mixed() -> Int64 = pair(1, b: 2)
end
"#,
    );
}

/// THE SLOT NO CALLER FILLS: a variadic capture parameter (`...args: R`, WI-727) is a
/// declared parameter that an ordinary call never names — `r.fix()` supplies one
/// argument against a two-parameter declaration, and the WI-727 rewrite fills the
/// capture slot with the empty record before this check runs. The most likely
/// false-positive shape in the language; passes either way by design.
#[test]
fn an_empty_variadic_capture_still_loads() {
    loads(
        r#"
namespace test.wi1100.capture
  import anthill.prelude.{Int64}
  operation cap[R](x: Int64, ...rest: R) -> Int64 = x
  operation empty_capture() -> Int64 = cap(1)
  operation with_capture() -> Int64 = cap(1, a: 2, b: 3)
end
"#,
    );
}

/// …and a capture op's FIXED parameters are still required. The counts here are the
/// ones the AUTHOR can write: the `...rest` slot is filled by the WI-727 rewrite from
/// named arguments, so it is neither an argument to be counted nor a parameter to be
/// demanded — reporting it on either side would state a count the source cannot have.
/// (Review-found: with the rewritten argument list this said "got 1 argument" about a
/// call with none in it, against an "expected 2" no caller could write.)
#[test]
fn a_capture_op_counts_only_what_the_author_writes() {
    let msg = refusal(
        r#"
namespace test.wi1100.capbad
  import anthill.prelude.{Int64}
  operation cap[R](x: Int64, ...rest: R) -> Int64 = x
  operation drive() -> Int64 = cap()
end
"#,
    );
    assert!(
        msg.contains("expected 1 argument") && msg.contains("got 0 arguments"),
        "both counts in the source's currency; got: {msg}",
    );
    assert!(
        msg.contains("`...rest` capture") && msg.contains("no argument fills parameter `x`"),
        "the capture is described rather than counted, and the empty slot is named; \
         got: {msg}",
    );
}

/// THE TOLERANCE'S control: a rule body's goal at the operation's arity + 1 is the
/// FUNCTIONAL-RELATION view (§5.3, WI-938) — `describe` takes ONE parameter and the goal
/// writes two, the second receiving the result. This is the shape WI-1043's rule-body
/// spec-op dispatch is written in; refusing it would refuse a delivered feature.
///
/// Both spellings, because they arrive at the check differently — the qualified one as a
/// direct call on a body-less spec op, the dot one through WI-282's dispatch with the
/// receiver prepended — and both are arity + 1.
#[test]
fn a_rule_body_relational_goal_still_loads() {
    loads(
        r#"
namespace test.wi1100.relview
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    operation describe(x: Leaf) -> Int64 = 7
    provides Desc[T = Leaf]
  end

  rule qualified(?r) :- Desc.describe(leaf(), ?r)
  rule dotted(?r) :- leaf().describe(?r)
end
"#,
    );
}

/// …and the tolerance is EXACTLY one column: a rule-body goal two over the declared
/// arity is still refused, so "in a rule body anything goes" is not what was traded for
/// the relational view.
#[test]
fn a_rule_body_goal_two_over_the_arity_is_still_refused() {
    let msg = refusal(
        r#"
namespace test.wi1100.relbad
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    operation describe(x: Leaf) -> Int64 = 7
    provides Desc[T = Leaf]
  end

  rule qualified(?r) :- Desc.describe(leaf(), 1, ?r)
end
"#,
    );
    assert!(
        msg.contains("expected 1 argument") && msg.contains("got 3 arguments"),
        "got: {msg}",
    );
}

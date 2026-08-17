//! WI-824 — an ABSTRACT per-call element must not be PINNED to a STRUCTURED
//! provider head.
//!
//! THE DEFECT (found while building the WI-817 witness; it refuted that
//! ticket's first-cut positive control). Dispatch candidate matching
//! (`match_candidate_against_goal` arm (2), kb/typing.rs) accepted ANY
//! type-param per-call element against a parameterized candidate head — a
//! var-against-structure match, i.e. UNIFICATION where dispatch does MATCHING.
//! So an UNCONDITIONED parametric provider
//!
//! ```anthill
//! sort WrapDesc
//!   sort E = ?
//!   fact Desc[T = Wrap[A = E]]        -- free E, NO requires
//!   operation describe(w: Wrap[A = E]) -> Int64 = …
//! end
//! ```
//!
//! matched a goal `Desc[T = <abstract>]` and, being the only match, resolved
//! `Unique` — the one outcome WI-325's abstract-call protection does not guard
//! (it guards `NoCandidates` / `NoMatch`). The caller never chose that impl.
//!
//! THE ASYMMETRY the ticket asked to establish, measured: the CONDITIONAL twin
//! of the same provider (identical head, plus `requires Desc[T = E]`) never
//! mis-pinned — the head matched exactly the same way, but the impl's own
//! sub-goal is unresolvable at the abstract element, so the walk ended in a
//! refusal. The two diverged only AFTER the bad head match; the head match is
//! the defect, and refusing it makes them agree.
//!
//! CHOSEN SEMANTICS — the ticket's option (i), goal type params are RIGID in
//! candidate matching, NOT (ii) "match survives, classifies Deferred".
//! Reasons: (a) a rigid skolem is a definite per-body type that is not
//! provably `Wrap[A = E]` for any `E`, so there is nothing to defer TO — the
//! sound reading is "this candidate does not apply"; (b) `Deferred` means "a
//! dictionary arrives at runtime", and when nothing supplies one the program
//! loads clean and dies at eval on an unbound `__req_*` — the failure mode
//! WI-828 exists to convert INTO a load error; (c) refusing routes the call
//! into the ladder that already handles abstract calls
//! (`MissingRequiresForSpecOp` when uncovered, WI-562 licensing when covered),
//! adding no new outcome.
//!
//! Option (i) is taken at its word — with a call-site σ in hand, EVERY bare
//! type-param element is treated as rigid, not just those a σ-class walk can
//! prove rigid. The narrower form was written and measured first (identical on
//! this corpus), and it claims something that does not hold up: the leniency it
//! preserved exists for WI-507's unpinned sibling, which meets an impl-param
//! REF and is therefore decided by a different arm. Keying on σ-presence also
//! keeps the rule independent of what the classifier can see — it cannot see an
//! OPERATION's own type param, and returns "unknown" on chase-bound exhaustion.
//!
//! The two witnesses below cover BOTH ways the mis-pin was silent — an eval
//! crash (the WI-817 pin, now flipped there) and a WRONG VALUE — and the
//! controls pin the WATCH clause: a parametric provider at a CONCRETE binding
//! must keep resolving, conditional and unconditioned alike.

use anthill_core::eval::Value;

/// Spec + a base impl + `Wrap`, shared by every program here. `describe`
/// values are distinct per impl so a mis-pin is READABLE off the result.
const BASE: &str = r#"
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Leaf
    entity leaf
    fact Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 1
  end
  sort Wrap
    sort A = ?
    entity wrap(inner: A)
  end
"#;

/// The UNCONDITIONED parametric provider: free `E`, no `requires`. Its
/// `describe` returns 99 — a value no correct resolution of these programs can
/// produce, so "loads clean and returns 99" is exactly the mis-pin.
const UNCONDITIONED_PROVIDER: &str = r#"
  sort WrapDesc
    sort E = ?
    fact Desc[T = Wrap[A = E]]
    operation describe(w: Wrap[A = E]) -> Int64 = 99
  end
"#;

/// The CONDITIONAL twin — same head, plus the `requires` that makes it a real
/// conditional instance. `describe(wrapⁿ(leaf))` = 1, 12, 122, … (depth-coded).
const CONDITIONAL_PROVIDER: &str = r#"
  sort WrapDesc
    sort E = ?
    requires Desc[T = E]
    fact Desc[T = Wrap[A = E]]
    operation describe(w: Wrap[A = E]) -> Int64 =
      add(mul(10, Desc.describe(w.inner)), 2)
  end
"#;

/// A caller whose enclosing `requires` is at `Wrap[A = AT]` calling a callee
/// requiring `Desc[BT]` at `BT := AT`: the entry σ-DISAGREES with the goal
/// (WI-821), so the dictionary must be CONSTRUCTED, and construction meets the
/// abstract element `AT`. Nothing in scope supplies `Desc` at a bare `AT`.
const CROSS_SORT_CALLERS: &str = r#"
  sort Callee
    sort BT = ?
    requires Desc[BT]
    operation b(y: BT) -> Int64 = Desc.describe(y)
  end
  sort Caller
    sort AT = ?
    requires Desc[T = Wrap[A = AT]]
    operation a(x: AT) -> Int64 = Callee.b(x)
  end
"#;

/// The entry point every evaluated program here needs: `Driver.drive(n)` runs
/// `call` and returns its value. One spelling, so the depth-coded results below
/// are all read off the same shape.
fn driver(call: &str) -> String {
    format!("\n  sort Driver\n    operation drive(n: Int64) -> Int64 = {call}\n  end\n")
}

fn program(ns: &str, parts: &[&str]) -> String {
    format!(
        "\nnamespace {ns}\n  import anthill.prelude.{{Int64, Bool}}\n{BASE}{}\nend\n",
        parts.concat()
    )
}

/// The WI-325 ladder's suggestion for this spec. One owner beside
/// `DESC_INSTANCES`, which this file also shares; see
/// `common::MISSING_DESC_REQUIRES`.
const MISSING_REQUIRES: &str = crate::common::MISSING_DESC_REQUIRES;

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but the source loaded clean"))
}

/// The ONE load error whose text names `site`, or a panic listing what was
/// reported instead. Every refusal pin below asserts its clauses against a
/// SINGLE diagnostic, never the concatenation of all of them: a joined haystack
/// stays green when the clauses drift apart into two errors, or when an
/// unrelated second error happens to carry one of them.
fn sole_error_at(src: &str, site: &str) -> String {
    let errs = load_errs(src);
    let mut hits = errs.iter().filter(|e| e.contains(site));
    let found = hits
        .next()
        .unwrap_or_else(|| {
            panic!(
                "no load error names `{site}`; got:\n  {}",
                errs.join("\n  ")
            )
        })
        .clone();
    assert!(
        hits.next().is_none(),
        "expected ONE error naming `{site}`; got:\n  {}",
        errs.join("\n  ")
    );
    found
}

/// Evaluate on a FRESH interpreter (a trapped call poisons later calls on the
/// same one); the load doubles as the clean-load gate — `interp_for` panics on
/// a dirty load.
fn eval_fresh(src: &str, entry: &str) -> Result<Value, anthill_core::eval::EvalError> {
    let mut interp = crate::common::interp_for(src);
    interp.call(entry, &[Value::Int(0)])
}

// ── Positive controls ────────────────────────────────────────────────

/// The harness must actually report a load error, so the "loads clean" half of
/// the value pins below (enforced by `interp_for`'s panic) is not vacuous.
#[test]
fn positive_control_load_error_is_reported() {
    let src = program(
        "wi824.posload",
        &["  sort Bad\n    operation bad(x: NoSuchSort) -> Int64 = 0\n  end\n"],
    );
    assert!(!load_errs(&src).is_empty());
}

// ── Witness 1: the WRONG-VALUE mis-pin (dictionary construction) ──────

/// FIXED BY WI-824 (was: loads clean, `drive` = **99**). The dictionary for
/// `Callee.b` at `BT := AT` is CONSTRUCTED (the caller's `Desc[Wrap[A = AT]]`
/// entry σ-disagrees, so it is not forwarded), and construction resolved the
/// abstract `AT` against the unconditioned provider's structured head — the
/// mis-pin, in its silent form: no crash, a WRONG VALUE. `Caller.a(leaf())`
/// ran `WrapDesc.describe` on a `leaf`, which reads no field and so cannot
/// even fail loudly. SOUND: nothing supplies `Desc` at the bare `AT`, so the
/// call is refused at LOAD — the WI-828 diagnostic, naming the requirement,
/// the enclosing entry that only coarsely covers it, and (now) that no impl
/// provides the spec at this instantiation.
#[test]
fn cross_sort_construction_refuses_unconditioned_provider() {
    let src = program(
        "wi824.xsort",
        &[
            UNCONDITIONED_PROVIDER,
            CROSS_SORT_CALLERS,
            &driver("Caller.a(leaf())"),
        ],
    );
    let text = sole_error_at(&src, "wi824.xsort.Callee.b.requires");
    assert!(
        text.contains("cannot be supplied") && text.contains("no impl provides wi824.xsort.Desc"),
        "expected a load refusal naming the unsuppliable requirement (pre-WI-824 this \
         loaded clean and computed 99 from a mis-pinned dictionary); got:\n{text}"
    );
}

/// THE ASYMMETRY CONTROL for the witness above: the CONDITIONAL twin of the
/// same provider was already refused here before WI-824 (its own `requires`
/// sub-goal is unresolvable at the abstract element), and still is. The two
/// providers now agree — which is the point of the fix; only the tail of the
/// message changes (the walk no longer reports a cycle through `WrapDesc.E`,
/// because the bad head match that created that cycle is gone).
#[test]
fn cross_sort_construction_refuses_conditional_provider_too() {
    let src = program(
        "wi824.xsortc",
        &[
            CONDITIONAL_PROVIDER,
            CROSS_SORT_CALLERS,
            &driver("Caller.a(leaf())"),
        ],
    );
    let text = sole_error_at(&src, "wi824.xsortc.Callee.b.requires");
    assert!(
        text.contains("cannot be supplied"),
        "expected the same refusal as the unconditioned twin; got:\n{text}"
    );
}

// ── Witness 2: the abstract in-body call (WI-817's pin, restated) ─────

/// FIXED BY WI-824. An abstract `Desc.describe(x)` in a body whose enclosing
/// SORT declares no covering `requires` must be rejected at load naming the
/// clause that would license it. Before the fix the unconditioned provider
/// answered the abstract goal `Unique` and the program loaded clean, to die at
/// eval reading `w.inner` off a `leaf`. (The full polymorphic-recursion
/// spelling of this witness is `unconditioned_parametric_fact_refused_at_
/// abstract_call`, wi817.)
#[test]
fn abstract_body_call_refused_when_uncovered() {
    let src = program(
        "wi824.body",
        &[
            UNCONDITIONED_PROVIDER,
            r#"
  sort Holder
    sort HT = ?
    operation probe(x: HT) -> Int64 = Desc.describe(x)
  end
"#,
        ],
    );
    let text = sole_error_at(&src, "wi824.body.Desc.describe.requires");
    assert!(
        text.contains(MISSING_REQUIRES),
        "expected the WI-325 ladder to name the spec op and the missing requires; \
         got:\n{text}"
    );
}

/// The other half of the ladder — WI-562 licensing: the SAME body with the
/// covering `requires Desc[T = HT]` on the enclosing sort loads clean and
/// evaluates through the runtime dictionary. Proves the refusal did not
/// swallow the legitimate abstract call: `probe(wrap(leaf()))` = 99 via the
/// provider the CALLER's instantiation actually selects.
#[test]
fn abstract_body_call_still_licensed_when_covered() {
    let src = program(
        "wi824.covered",
        &[
            UNCONDITIONED_PROVIDER,
            r#"
  sort Holder
    sort HT = ?
    requires Desc[T = HT]
    operation probe(x: HT) -> Int64 = Desc.describe(x)
  end
"#,
            &driver("Holder.probe(wrap(leaf()))"),
        ],
    );
    let got = eval_fresh(&src, "wi824.covered.Driver.drive");
    assert!(
        matches!(got, Ok(Value::Int(99))),
        "a COVERED abstract call must still resolve through the caller's dictionary \
         (WrapDesc at the concrete Wrap[A = Leaf]); got {got:?}"
    );
}

// ── WATCH clause: parametric providers at CONCRETE bindings ──────────

/// The fix must not break a parametric provider where the call PINS the
/// element — the goal is `Desc[T = Wrap[A = Leaf]]`, structure against
/// structure, no wildcard involved. Conditional provider: 10·1 + 2 = 12
/// (its own `requires Desc[T = E]` resolves at `E := Leaf`).
#[test]
fn conditional_parametric_provider_resolves_at_concrete_binding() {
    let src = program(
        "wi824.conc",
        &[CONDITIONAL_PROVIDER, &driver("Desc.describe(wrap(leaf()))")],
    );
    let got = eval_fresh(&src, "wi824.conc.Driver.drive");
    assert!(
        matches!(got, Ok(Value::Int(12))),
        "expected Ok(Int(12)); got {got:?}"
    );
}

/// Same control for the UNCONDITIONED provider — the one WI-824 refuses at an
/// abstract element must stay fully usable at a concrete one (99), and one
/// level deeper (`wrap(wrap(leaf()))`) too, so the refusal is about the
/// ELEMENT'S ABSTRACTNESS and not about the provider's shape.
#[test]
fn unconditioned_parametric_provider_resolves_at_concrete_binding() {
    for (depth, expr) in [(1, "wrap(leaf())"), (2, "wrap(wrap(leaf()))")] {
        let src = program(
            "wi824.uconc",
            &[
                UNCONDITIONED_PROVIDER,
                &driver(&format!("Desc.describe({expr})")),
            ],
        );
        let got = eval_fresh(&src, "wi824.uconc.Driver.drive");
        assert!(
            matches!(got, Ok(Value::Int(99))),
            "depth {depth}: expected Ok(Int(99)); got {got:?}"
        );
    }
}

/// The base impl must keep winning at its own concrete binding with the
/// parametric provider in scope (`Desc[T = Leaf]` → 1) — i.e. the refusal did
/// not make the parametric head match MORE goals by dropping out of the
/// specificity comparison.
#[test]
fn base_impl_still_wins_at_its_own_binding() {
    let src = program(
        "wi824.base",
        &[UNCONDITIONED_PROVIDER, &driver("Desc.describe(leaf())")],
    );
    let got = eval_fresh(&src, "wi824.base.Driver.drive");
    assert!(
        matches!(got, Ok(Value::Int(1))),
        "expected Ok(Int(1)); got {got:?}"
    );
}

//! WI-828 — a GENUINELY-UNCONSTRAINED requirement element at a call-site
//! dict build is a LOAD-TIME diagnostic, not a silent `dispatch_dict: None`
//! that loads clean and dies at eval.
//!
//! Background (WI-821): σ-class agreement gates requirement forwarding — a
//! caller entry whose element the call-site σ maps to a different class is
//! no cover. For a NULLARY / return-only callee element (`make() -> MT` —
//! no argument pins `MT`), the σ-class of the unbound element can never
//! equal the caller's rigid, so the pre-WI-821 loose forward (`MT := CT`)
//! is correctly refused — but the refusal used to land as `require_complete
//! → None → ConcreteApplyWithin { dispatch_dict: None } → plain apply`:
//! a clean load followed by `Err(Internal(DeferToRequirement: __req_desc
//! not bound))` at eval — the repo's named anti-pattern. The DECIDED rule:
//! such a program is REJECTED at load (`TypeError::UnsatisfiableRequirement`)
//! with a located diagnostic naming the dep, the unconstrained element, the
//! σ-refused covering entry, and the construction outcome (the Ambiguous
//! provider set when there is one; measured on these fixtures: `NoMatch`);
//! no fallback semantics (any pick would resurrect a blind guess).
//!
//! The fixtures reconstruct the two /code-review drives (findings 4 and 6,
//! both CONFIRMED HEAD-vs-HEAD~1 at WI-821 time):
//!   (a) direct call — HEAD~1 Ok(Int(11)) via the loose forward; post-gate
//!       HEAD loaded clean then died Internal at eval. Now: load diagnostic.
//!   (b) eta — HEAD~1 Ok(Int(4)); post-gate HEAD raised the bare WI-420
//!       "unsatisfiable requirement" naming neither the σ refusal nor the
//!       element. Now: the same refusal diagnostic, eta-flavored.
//!
//! The σ-refusal gate is deliberately NARROW: bare `NoMatch` (a cross-sort
//! abstract call with no covering entry and no provider — the pre-existing
//! WI-415/418 gap) and `Cyclic` (WI-827's sphere) keep their silent no-dict
//! behavior, and op-scoped `requires` chains never reach this build at all
//! (`ConcreteApplyWithin` gates on the callee's PARENT-SORT chain), so the
//! wi817 (c)-row pins are untouched by construction.

use anthill_core::eval::Value;

/// Spec `Desc` with a nullary producer + describer, and TWO ground
/// instances. The ticket predicted Strategy 3 would resolve `Ambiguous(2)`
/// for the unconstrained element; MEASURED on HEAD the σ-gated candidate
/// match refuses an unbound element against ground heads outright, so
/// construction terminates `NoMatch` ("no provider constructs …") — the
/// second instance stays to pin that the diagnostic fires WITH providers
/// present (no blind pick of one of them).
const INSTANCES: &str = r#"
  sort Desc
    sort T = ?
    operation fresh() -> T
    operation describe(x: T) -> Int64
  end

  sort Leaf
    entity leaf
    fact Desc[T = Leaf]
    operation fresh() -> Leaf = leaf()
    operation describe(x: Leaf) -> Int64 = 1
  end

  sort Pebble
    entity pebble
    fact Desc[T = Pebble]
    operation fresh() -> Pebble = pebble()
    operation describe(x: Pebble) -> Int64 = 5
  end
"#;

fn with_instances(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
{INSTANCES}
{body}
end
"#
    )
}

fn load_errs(sources: &[&str]) -> Vec<String> {
    crate::common::try_load_kb_with_files(sources)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but the sources loaded clean"))
}

/// Assert `errs` contains ONE refusal diagnostic carrying every piece the
/// ticket names: the dep (`Desc[`…), the unconstrained element (`MT`), the
/// σ-refused covering entry (WI-821 + the caller element `CT`), the
/// construction outcome (measured: `NoMatch`, rendered via the resolver's
/// own hint — "no impl provides"), and a source location.
fn assert_refusal_diagnostic(errs: &[String], usage_marker: &str) {
    let text = errs.join("\n");
    let refusal = errs
        .iter()
        .find(|e| e.contains("cannot be supplied"))
        .unwrap_or_else(|| panic!("no refusal diagnostic among load errors:\n{text}"));
    for piece in [
        "Desc[",
        "MT",
        "unconstrained",
        "WI-821",
        "CT",
        "no impl provides",
        usage_marker,
    ] {
        assert!(
            refusal.contains(piece),
            "refusal diagnostic must name `{piece}`; got:\n{refusal}"
        );
    }
    assert!(
        refusal.chars().next().is_some_and(|c| c.is_ascii_digit()),
        "refusal diagnostic must be located (line:col prefix); got:\n{refusal}"
    );
}

/// (a) The direct-call drive: `make() -> MT` pins nothing, `Box`'s
/// `requires Desc[T = CT]` σ-disagrees (unbound vs rigid), and Strategy-3
/// construction finds no provider for the unbound element (measured
/// `NoMatch`; the ticket predicted `Ambiguous(2)`). Pre-fix: loaded clean,
/// then `Err(Internal("DeferToRequirement: requirement param `__req_desc`
/// not bound in caller frame"))` at eval. Now: located load diagnostic.
#[test]
fn direct_call_unconstrained_element_is_a_load_diagnostic() {
    let src = with_instances(
        "wi828.a",
        r#"  sort Maker
    sort MT = ?
    requires Desc[T = MT]
    operation make() -> MT = Desc.fresh()
  end
  sort Box
    sort CT = ?
    requires Desc[T = CT]
    operation use(x: CT) -> Int64 = add(mul(10, Desc.describe(Maker.make())), 1)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Box.use(leaf())
  end"#,
    );
    assert_refusal_diagnostic(&load_errs(&[&src]), "call to");
}

/// (b) The eta drive: `bump` sits on requires-carrying `Maker` (element
/// never mentioned in bump's signature, so the expected `Int64 -> Int64`
/// arrow pins nothing) and is passed as a function value from a sort whose
/// own `requires Desc[T = CT]` covers only as a σ-refused wildcard. Pre-fix:
/// the bare WI-420 error named neither the refusal nor the element. Now: the
/// refusal diagnostic, marked as the function-value usage.
#[test]
fn eta_unconstrained_element_diagnostic_names_the_refusal() {
    let maker_ns = with_instances(
        "wi828.m",
        r#"  sort Maker
    sort MT = ?
    requires Desc[T = MT]
    operation bump(n: Int64) -> Int64 = add(n, 1)
  end"#,
    );
    let caller_ns = r#"
namespace wi828.b
  import anthill.prelude.{Int64, Function}
  import wi828.m.{Desc}
  import wi828.m.Maker.{bump}
  sort Applier
    operation apply1(f: Function[A = Int64, B = Int64]) -> Int64 = f(3)
  end
  sort Caller
    sort CT = ?
    requires Desc[T = CT]
    operation run(x: CT) -> Int64 = Applier.apply1(bump)
  end
end
"#;
    assert_refusal_diagnostic(&load_errs(&[&maker_ns, caller_ns]), "function value");
}

/// The NESTED spelling of (a): the caller's only cover for `Desc` sits in a
/// slot's sub-chain (`requires Outer[OT = CT]` with `Outer requires
/// Desc[T = OT]`), so Strategy 1 never sees it — Strategy 2 matches it
/// COMPOSED into caller scope (`Desc[T = CT]`) and the σ-gate refuses it
/// there. The refusal scan mirrors that composition; before it did, this
/// spelling was the one place the silent load-clean-die-at-eval mode
/// survived.
#[test]
fn nested_cover_refusal_is_also_a_load_diagnostic() {
    let src = with_instances(
        "wi828.n",
        r#"  sort Maker
    sort MT = ?
    requires Desc[T = MT]
    operation make() -> MT = Desc.fresh()
  end
  sort Outer
    sort OT = ?
    requires Desc[T = OT]
    operation touch(o: OT) -> Int64 = 7
  end
  sort Box2
    sort CT = ?
    requires Outer[OT = CT]
    operation use(x: CT) -> Int64 = add(mul(10, Desc.describe(Maker.make())), 1)
  end"#,
    );
    assert_refusal_diagnostic(&load_errs(&[&src]), "call to");
}

/// Positive control 1 — the σ-AGREEING twin of (a): `make(seed: MT)` pins
/// `MT := CT` (the caller's own rigid) at the call, so the caller's
/// `requires Desc[T = CT]` forwards by name (WI-418, the dominant correct
/// case) and the program loads AND runs: describe(make(leaf)) = 1 → 11.
/// Proves the diagnostic does not over-fire on same-class forwarding.
#[test]
fn constrained_twin_forwards_and_evals() {
    let src = with_instances(
        "wi828.ok",
        r#"  sort Maker
    sort MT = ?
    requires Desc[T = MT]
    operation make(seed: MT) -> MT = seed
  end
  sort Box
    sort CT = ?
    requires Desc[T = CT]
    operation use(x: CT) -> Int64 = add(mul(10, Desc.describe(Maker.make(x))), 1)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Box.use(leaf())
  end"#,
    );
    let mut interp = crate::common::interp_for(&src);
    let got = interp.call("wi828.ok.Driver.drive", &[Value::Int(0)]);
    assert!(matches!(got, Ok(Value::Int(11))), "expected Ok(Int(11)); got {got:?}");
}

/// Positive control 2 — the CONCRETE twin of (a): the call pins `MT := Leaf`
/// with a value from a requires-FREE caller, so the dep substitutes to
/// `Desc[T = Leaf]` and Strategy 3 constructs from the unique fact (WI-415).
/// Proves the diagnostic does not over-fire on concrete construction.
#[test]
fn concrete_twin_constructs_and_evals() {
    let src = with_instances(
        "wi828.conc",
        r#"  sort Maker
    sort MT = ?
    requires Desc[T = MT]
    operation make(seed: MT) -> MT = seed
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Desc.describe(Maker.make(leaf()))
  end"#,
    );
    let mut interp = crate::common::interp_for(&src);
    let got = interp.call("wi828.conc.Driver.drive", &[Value::Int(0)]);
    assert!(matches!(got, Ok(Value::Int(1))), "expected Ok(Int(1)); got {got:?}");
}

//! WI-20261122-CXR5B, eighth step — A PROVIDER WITH CONSTRUCTORS MAY BE NAMED WHERE NO VALUE AT
//! THE CALL DECIDES (c3 and g4 of `docs/design/spec-carrier-set.md`, folded into the ticket by the
//! user 2026-11-22).
//!
//! §4.4's check 3 refused every bracket naming a CONCRETE provider (a sort with constructors),
//! because "the value decides" (`validate_instance_selection`, `TieRepair::ValueDirected`). Where
//! the called operation takes no value the dispatch reads its provider off — `Dflt.dflt()`,
//! `Src.make()`, no `Self` parameter and none at the carrier parameter
//! (`op_has_spec_carrier_param`) — nothing at the call can name the provider but the bracket,
//! and two concrete providers left the call with no repair: c3 refused "none can be named here",
//! g4's bracket refused "no explicit selection of a concrete provider". Now, for an operation OF
//! the spec the bracket names, the bracket is admitted there and the tie offers it; a value that
//! decides keeps the refusal, and so does a named requirement slot of another sort
//! (WI-20260911-TX0G6's rule, `wi_tx0g6_selection_validation_test`).
//!
//! For a self-representing spec the bracket also fixes the provision's carrier, the provider
//! (§5.4's second amendment), and a goal naming its carrier that leaves out a type-var the
//! provider's row binds to its own parameter is at one of its values: `Src.make[Src = Ones]()`
//! fixing no `T` was refused "the call selected `Ones` …, which provides no instance at these
//! bindings".
//!
//! WHAT FAILS IF THIS IS BACKED OUT, and what passes either way, is said at each row. MEASURED
//! 2026-11-22, these rows kept: with `src/` at `3fd813422`, the first two fail and the control
//! passes; `wi843_coexisting_instances_test`'s moved row fails too. The open-`T` half of g4 alone
//! (the candidate match, `candidates.rs`) was measured by probe: `Src.make[Src = Ones]()` refused,
//! `Src.make[Src = Ones, T = Int64]()` answering.

use crate::common::{interp_for, load_errors_of};

/// What `{ns}.Driver.go()` answers.
fn go(src: &str, ns: &str) -> i64 {
    match interp_for(src)
        .call(&format!("{ns}.Driver.go"), &anthill_core::eval::HostValue::all(&[]))
        .map(|h| h.value)
        .unwrap_or_else(|e| panic!("`{ns}.Driver.go`: {e:?}"))
    {
        anthill_core::eval::Value::Int(n) => n,
        other => panic!("`{ns}.Driver.go` answered no Int64: {other:?}"),
    }
}

/// c3: two data sorts each providing `Dflt[T = Int64]`, and a driver whose `go` is `body`.
fn dflt(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Dflt
    sort T = ?
    operation dflt() -> T
  end
  sort C1
    entity c1
    provides Dflt[T = Int64]
    operation dflt() -> Int64 = 1
  end
  sort C2
    entity c2
    provides Dflt[T = Int64]
    operation dflt() -> Int64 = 2
  end
  sort Driver
    operation go() -> Int64 = {body}
  end
end
"#
    )
}

/// g2–g6's self-representing `Src`, provided by `Ones` and `Twos`, and a driver whose `go` is
/// `body`.
fn src(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Src
    sort T = ?
    operation next(s: Self) -> Int64
    operation make() -> Self
  end
  sort Ones
    sort T = ?
    entity ones
    provides Src[T = T]
    operation next(s: Ones) -> Int64 = 1
    operation make() -> Self = ones
  end
  sort Twos
    sort T = ?
    entity twos
    provides Src[T = T]
    operation next(s: Twos) -> Int64 = 2
    operation make() -> Self = twos
  end
  sort Driver
    operation go() -> Int64 = {body}
  end
end
"#
    )
}

/// c3: the call naming neither is refused, OFFERING the bracket; each bracket answers. FAILS
/// backed out: the refusal said "none can be named here", and the bracket was refused "no
/// explicit selection of a concrete provider".
#[test]
fn two_concrete_providers_are_told_apart_by_the_bracket_where_no_value_decides() {
    let text = load_errors_of(&dflt("wicxr5bcb.dflt.none", "Dflt.dflt[T = Int64]()")).join("\n");
    assert!(text.contains("[Dflt = "), "the bracket is offered:\n{text}");
    for (ns, named, answer) in [("wicxr5bcb.dflt.c1", "C1", 1), ("wicxr5bcb.dflt.c2", "C2", 2)] {
        let src = dflt(ns, &format!("Dflt.dflt[T = Int64, Dflt = {named}]()"));
        assert_eq!(go(&src, ns), answer, "{ns}");
    }
}

/// g4 and g3: naming the provider of a self-representing spec's call with no `Self` value fixes
/// it, whether the call fixes `T` or not; the call naming neither is refused offering the
/// bracket. FAILS backed out: the bracket was refused as naming a concrete provider, and g3's
/// refusal offered none.
#[test]
fn a_self_representing_calls_bracket_fixes_its_provider() {
    for (ns, call, answer) in [
        ("wicxr5bcb.src.ones", "Src.make[Src = Ones]()", 1),
        ("wicxr5bcb.src.twos", "Src.make[Src = Twos]()", 2),
        ("wicxr5bcb.src.onest", "Src.make[Src = Ones, T = Int64]()", 1),
    ] {
        assert_eq!(go(&src(ns, &format!("Src.next({call})")), ns), answer, "{ns}");
    }
    let text = load_errors_of(&src("wicxr5bcb.src.none", "Src.next(Src.make())")).join("\n");
    assert!(text.contains("[Src = "), "the bracket is offered:\n{text}");
}

/// CONTROL: where a value decides — `next(s: Self)` on a `Ones` — a bracket naming a concrete
/// provider stays refused. Passes either way, by design.
#[test]
fn a_bracket_where_a_value_decides_stays_refused() {
    let text = load_errors_of(&src("wicxr5bcb.src.value", "Src.next[Src = Ones](ones)")).join("\n");
    assert!(text.contains("CONCRETE provider"), "{text}");
}

/// The value a bracketed `Self` result is, is the provider at what the call fixed: `let o =
/// Src.make[Src = Ones, T = Int64]()` is a `Ones[T = Int64]`, which a use at `Ones[T = Int64]`
/// takes and one at `Ones[T = String]` refuses, naming the `T = Int64` the call fixed. Bound by a
/// `let`, so no type is expected at the call and the bracket alone types it. FOUND BY /code-review:
/// a first cut typed it the bare provider, and the agreeing use was refused "got `Ones[T = o.T]`"
/// — this row FAILS with that typing restored. The agreeing use FAILS backed out too (the bracket
/// refused as naming a concrete provider); the refusal passes either way, by design.
#[test]
fn a_bracketed_self_result_is_the_provider_at_what_the_call_fixed() {
    let with_use = |ns: &str, at: &str| {
        src(ns, "\n      let o = Src.make[Src = Ones, T = Int64]()\n      useAt(o)")
            .replace("  sort Driver", &format!("  operation useAt(o: Ones[T = {at}]) -> Int64 = 3\n  sort Driver"))
            .replace("import anthill.prelude.{Int64}", "import anthill.prelude.{Int64, String}")
    };
    assert_eq!(go(&with_use("wicxr5bcb.typed.agree", "Int64"), "wicxr5bcb.typed.agree"), 3);
    let text = load_errors_of(&with_use("wicxr5bcb.typed.apart", "String")).join("\n");
    for want in ["expected Ones[T = String]", "T = Int64]"] {
        assert!(text.contains(want), "the refusal names what the call fixed (`{want}` missing):\n{text}");
    }
}

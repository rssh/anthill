//! A PROOF AT A CALL READS EACH ARGUMENT AS ITS VALUE (WI-20261105-CBRD2). A guard or a
//! precondition is proved at a call with each parameter replaced by its argument's term.
//!
//! * The term of `scored[A = Int64, Score = ByOne](5)` is `scored(5)`: the dictionary the call
//!   selects is not in it. The resolver ran `scored` with `Score`'s provider derived from the
//!   value, which at `Int64` is two, `ByOne` and `ByZero`, so the proof was undecided, a guarded
//!   effect kept and a precondition unproved. The substitution keeps each argument beside its
//!   term (`typing::CallSigma`), and the goal a proof builds takes, at each call inside an
//!   argument, what the typer decided there (`typing::clause_goal`).
//! * The term of a dotted argument, `listOf(4).head` or `mkn(4).c`, is the reflect datum
//!   `dot_apply(…)`, of `four()` the bare name `four`, and of a function parameter's `g(4)` a
//!   call no clause answers; the resolver compares each as a datum unequal to every number, so
//!   `eq(n, 4)` was refuted and the effect it guards dropped at a call that incurs it, and
//!   `neq(n, 0)` proved over `zero()`. Such an argument is not substituted
//!   (`typing::guard_arg_term`): the guard is undecided and the effect kept.
//!
//! The rows of the first part measure the reading (`resolve::bridge_derivations_by_this_thread`)
//! beside the verdicts.
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches, then removed. The control is each switch unset: every row
//! passes.
//!
//! * No stamps carried onto the goal:
//!   [`a_guard_over_a_selected_call_is_refuted_at_its_dictionary`] and
//!   [`a_precondition_over_a_selected_call_is_proved_at_its_dictionary`] fail at `ByOne`, on the
//!   count. Measured one by one, the labelled call `risky(n: …)` and the override's guard
//!   (`Halver.slice`) each derive their dictionaries and keep `Boom`, the caller refused.
//! * Every argument substituted:
//!   [`a_guard_over_an_argument_whose_term_is_not_its_value_is_undecided`] fails at each such
//!   argument, the program loading clean, and
//!   [`a_precondition_over_an_argument_whose_term_is_not_its_value_is_unproved`] at each, the
//!   precondition proved. Every call of a name substituted, `g(4)` and `h()` load clean.
//!
//! The `ByZero` cases and the `id(…)` controls pass either way by design.

use anthill_core::kb::resolve::bridge_derivations_by_this_thread;

use crate::common::{load_errors_of, load_stdlib_kb};

fn src(ns: &str, decls: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Effect, List}}
  import anthill.prelude.PartialEq.{{eq, neq}}
  sort Score
    sort T = ?
    operation score(x: T) -> Int64
  end
  sort ByOne
    provides Score[T = Int64]
    operation score(x: Int64) -> Int64 = 1
  end
  sort ByZero
    provides Score[T = Int64]
    operation score(x: Int64) -> Int64 = 0
  end
  sort Boom
    entity Bang
    provides Effect[T = Boom]
  end
  operation scored[A](x: A) -> Int64 requires Score[T = A] = Score.score(x)
  operation small(n: Int64) -> Bool = n < 1
  operation risky(n: Int64) -> Int64 effects {{ Boom :- eq(n, 0) }} = n
  operation riskyIf(n: Int64) -> Int64 effects {{ Boom :- small(n) }} = n
  operation safe(n: Int64) -> Int64 requires neq(n, 0) = n
  operation risky4(n: Int64) -> Int64 effects {{ Boom :- eq(n, 4) }} = n
  operation four() -> Int64 = 4
  operation zero() -> Int64 = 0
  operation id(x: Int64) -> Int64 = x
  operation mkn(x: Int64) -> (c: Int64) = (c: x)
  operation listOf(x: Int64) -> List[T = Int64] = [x]
  sort Halver
    sort T = ?
    operation slice(a: T, b: Int64) -> T effects {{ Boom :- eq(b, 0) }}
  end
  sort Box
    entity box(v: Int64)
    operation slice(x: Box, y: Int64) -> Box effects {{ Boom :- eq(y, 0) }} = box(v: 1)
  end
  namespace Box
    provides Halver[T = Box]
  end
{decls}
end
"#
    )
}

/// The load's errors and the dictionaries it derived from values, the shared base loaded first.
fn errors_and_derived(src: &str) -> (Vec<String>, usize) {
    drop(load_stdlib_kb());
    let before = bridge_derivations_by_this_thread();
    let errs = load_errors_of(src);
    (errs, bridge_derivations_by_this_thread() - before)
}

/// `risky(scored[…, Score = ByOne](5))` owes nothing, the guard `eq(n, 0)` refuted at `1`; so
/// for `riskyIf`, whose guard is a call, `small(n)`, for the argument passed by its label, and
/// for `Halver.slice`, whose guard is its override's, `Box.slice`'s. At `ByZero` each owes `Boom`.
#[test]
fn a_guard_over_a_selected_call_is_refuted_at_its_dictionary() {
    let mut n = 0;
    for (ret, call) in [
        ("Int64", "risky(SEL)"),
        ("Int64", "riskyIf(SEL)"),
        ("Int64", "risky(n: SEL)"),
        ("Box", "Halver.slice(a: box(v: 7), b: SEL)"),
    ] {
        for (provider, owes) in [("ByOne", false), ("ByZero", true)] {
            n += 1;
            let call = call.replace("SEL", &format!("scored[A = Int64, Score = {provider}](5)"));
            let decls = format!("  operation c() -> {ret} = {call}");
            let (errs, derived) = errors_and_derived(&src(&format!("test.cbrd2.ga.g{n}"), &decls));
            assert_eq!(derived, 0, "{call}: a dictionary derived from the values");
            assert_eq!(errs.iter().any(|e| e.contains("undeclared effect: Boom")), owes, "{call}: {errs:?}");
            assert!(errs.iter().all(|e| e.contains("undeclared effect: Boom")), "{call}: {errs:?}");
        }
    }
}

/// `safe(scored[…, Score = ByOne](5))` proves `neq(n, 0)` at `1`; at `ByZero` it is refused.
#[test]
fn a_precondition_over_a_selected_call_is_proved_at_its_dictionary() {
    for (n, (provider, refused)) in [("ByOne", false), ("ByZero", true)].into_iter().enumerate() {
        let decls = format!("  operation c() -> Int64 = safe(scored[A = Int64, Score = {provider}](5))");
        let (errs, derived) = errors_and_derived(&src(&format!("test.cbrd2.ga.p{n}"), &decls));
        assert_eq!(derived, 0, "safe at {provider}: a dictionary derived from the values");
        assert_eq!(errs.len(), usize::from(refused), "safe at {provider}: {errs:?}");
        assert!(
            errs.iter().all(|e| e.contains("safe.requires") && e.contains("precondition")),
            "safe at {provider}: {errs:?}"
        );
    }
}

/// `risky4(n)` incurs `Boom` where `n` is `4`. Over `four()`, `mkn(4).c`, `listOf(4).head`,
/// `(c: 4).c` and a function parameter's `g(4)` and `g()` the guard is undecided and the effect
/// kept; over `id(4)` it holds, and over `id(3)` it is refuted.
#[test]
fn a_guard_over_an_argument_whose_term_is_not_its_value_is_undecided() {
    for (n, (arg, owes)) in [
        ("four()", true),
        ("mkn(4).c", true),
        ("listOf(4).head", true),
        ("(c: 4).c", true),
        ("g(4)", true),
        ("h()", true),
        ("id(4)", true),
        ("id(3)", false),
    ]
    .into_iter()
    .enumerate()
    {
        let decls = format!("  operation c(g: (Int64) -> Int64, h: () -> Int64) -> Int64 = risky4({arg})");
        let errs = load_errors_of(&src(&format!("test.cbrd2.ga.v{n}"), &decls));
        assert_eq!(errs.len(), usize::from(owes), "risky4({arg}): {errs:?}");
        assert!(errs.iter().all(|e| e.contains("undeclared effect: Boom")), "risky4({arg}): {errs:?}");
    }
}

/// `safe(n)` requires `neq(n, 0)`: unproved over `zero()` and `mkn(0).c`, so the call is
/// refused; proved over `id(5)`.
#[test]
fn a_precondition_over_an_argument_whose_term_is_not_its_value_is_unproved() {
    for (n, (arg, refused)) in [("zero()", true), ("mkn(0).c", true), ("id(5)", false)].into_iter().enumerate() {
        let decls = format!("  operation c() -> Int64 = safe({arg})");
        let errs = load_errors_of(&src(&format!("test.cbrd2.ga.u{n}"), &decls));
        assert_eq!(errs.len(), usize::from(refused), "safe({arg}): {errs:?}");
        assert!(
            errs.iter().all(|e| e.contains("safe.requires") && e.contains("precondition")),
            "safe({arg}): {errs:?}"
        );
    }
}

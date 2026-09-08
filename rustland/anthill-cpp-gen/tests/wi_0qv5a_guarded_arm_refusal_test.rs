//! WI-20260907-0QV5A — A `match` ARM GUARD IS REFUSED BY THE cpp17-stl PROFILE RATHER
//! THAN LOWERED WITHOUT ITS GUARD, AS A DEGRADABLE CAPABILITY GAP.
//!
//! `lower_match_branches_node` folds the arms into a `<tag-check> ? <body> : <next>`
//! chain and never read `branch.guard`. That AGREED with the program until this ticket:
//! the interpreter ignored the guard too, so a guarded arm really was taken on its tag
//! alone. `eval/eval.rs::scan_match_arms` now evaluates the guard and falls through when
//! it is false, so the same source evaluated and compiled would answer differently — the
//! generated C++ taking an arm the interpreter declines, silently.
//!
//! A REFUSAL RATHER THAN A LOWERING, and the reason is structural: the chain's LAST branch
//! is the unconditional catch-all, so a match whose final arm is guarded has nowhere to
//! fall out to — it needs the `MatchFailed` escape this backend has no form for. Nor can
//! the exhaustiveness check supply the missing coverage, since it only diagnoses ENUM
//! scrutinees. `(tag && guard) ? …` for the non-final arms alone would be half a feature
//! that still emits wrong code for the other half.
//!
//! AND A **CAPABILITY GAP** RATHER THAN A BARE ERROR (WI-891, found by `/code-review`):
//! "this profile has not implemented that shape yet" is what `CodegenContext::
//! capability_gap` exists for, and it degrades the ONE method to a build-breaking
//! `static_assert` while the rest of the header still emits. A bare `CppCodegenError` is
//! FATAL — one guarded arm anywhere in a KB would have meant no C++ for any other
//! operation or sort in it. That blast radius is what
//! [`a_guarded_arm_degrades_only_its_own_method`] pins.

use super::common;

use anthill_cpp_gen::emit_traits_struct;
use common::{load_kb_with, load_kb_with_lenient};

/// The guarded fixture and its guard-free control. The second arm is an unguarded
/// catch-all so the fixture survives the LOAD — a guarded arm covers nothing for
/// exhaustiveness since this same ticket (`anthill-core`'s
/// `wi_0qv5a_match_arm_guard_test::a_guarded_arm_does_not_cover_its_constructor_for_-
/// exhaustiveness`), so a two-constructor `enum` guarded on one of them is refused before
/// codegen ever sees it.
fn program(guard: &str, ns: &str) -> String {
    format!(
        r#"
        namespace test.qv5acpp{ns}
          import anthill.prelude.{{Bool, Int64}}
          enum Hue
            entity warm(heat: Int64)
            entity cool(chill: Int64)
          end
          sort Ops
            operation never() -> Bool = false
            operation rank(h: Hue) -> Int64 =
              match h
                case warm(a){guard} -> a
                case _ -> 0
          end
        end
    "#
    )
}

/// FAILS ON THE BACK-OUT of the refusal (`if false && branch.guard.is_some()`), and the
/// emitted body is the finding verbatim:
///
/// ```text
/// return (std::holds_alternative<warm>(h) ? [&]() { auto a = std::get<warm>(h).heat; return a; }() : 0);
/// ```
///
/// `never()` appears nowhere in it — the arm is taken on its tag alone, on a value for
/// which the interpreter falls through to the catch-all.
///
/// FAILS DIFFERENTLY IF THE GAP IS DOWNGRADED to a bare `CppCodegenError`: `emit_traits_-
/// struct` then returns `Err` and there is no struct to assert on at all — which is the
/// half of this row that measures the WI-891 channel rather than the refusal. The three
/// assertions are therefore not redundant: the first says the guard is refused, the second
/// says the wrong code is not emitted, the third says the refusal costs one method and not
/// the header.
#[test]
fn a_guarded_arm_degrades_only_its_own_method() {
    let mut kb = load_kb_with(&program(" | never()", "g"));
    let cpp = emit_traits_struct(&mut kb, "test.qv5acppg.Ops")
        .expect("a capability gap degrades the method, it does not abort the header");
    assert!(
        cpp.contains("static_assert") && cpp.contains("arm GUARD"),
        "the guarded method must degrade to a `static_assert` naming what it refuses:\n{cpp}"
    );
    assert!(
        !cpp.contains("holds_alternative"),
        "the tag check must NOT be emitted for a guarded arm — that is the wrong code \
         this refusal exists to prevent:\n{cpp}"
    );
    assert!(
        cpp.contains("never") && cpp.contains("return false"),
        "the SIBLING operation must still emit — a capability gap costs one method, not \
         the header:\n{cpp}"
    );

    // CONTROL — unguarded, same shape, lowers for real. Passes either way by design: it
    // is what says this refuses the GUARD and not the constructor arm around it.
    let mut kb2 = load_kb_with(&program("", "p"));
    let cpp2 = emit_traits_struct(&mut kb2, "test.qv5acppp.Ops")
        .expect("the same arms without a guard still lower");
    assert!(
        cpp2.contains("holds_alternative") && !cpp2.contains("static_assert"),
        "the control must emit the real tag-check chain:\n{cpp2}"
    );
}

/// THE SECOND `/code-review` FINDING — `node_references_name` walked a match arm's
/// scrutinee and body but not its GUARD, so `check_recursive_lambda_node` was blind to a
/// binder referenced only from a guard. That check runs BEFORE the arm is lowered, so the
/// two refusals are distinguishable by message: with the guard scanned the lambda is named
/// as self-recursive, without it the walk says "no reference" and the lowering's guard
/// refusal answers instead.
///
/// FAILS ON THE BACK-OUT of the added guard scan: the `static_assert` carries "arm GUARD"
/// rather than "recursive anonymous lambda", so the author is told the profile lacks
/// guards when the actual obstacle is the self-recursion — and the moment the guard
/// refusal is replaced by a real lowering, that same blindness stops being a wrong message
/// and becomes a miscompile.
///
/// LOADED LENIENTLY, exactly as `unsupported_test::recursive_anonymous_lambda_rejected`
/// loads its own: a lambda naming its own binder does not TYPE (`unknown functor \`f\``),
/// so the only way to put one in front of codegen is the deliberate-dirty helper. That is
/// the shape the check exists for, and the reason it is a codegen-side check at all.
#[test]
fn a_binder_referenced_only_from_a_guard_is_seen_as_self_recursive() {
    let src = r#"
        namespace test.qv5acpprec
          import anthill.prelude.{Bool, Int64}
          sort Ops
            operation go(n: Int64) -> Int64 =
              let f = lambda (x: Int64) -> match x
                case y | f(y) -> 1
                case _ -> 0
              f(n)
          end
        end
    "#;
    let mut kb = load_kb_with_lenient(src);
    let cpp = emit_traits_struct(&mut kb, "test.qv5acpprec.Ops")
        .expect("both refusals are capability gaps, so the method degrades either way");
    assert!(
        cpp.contains("recursive anonymous lambda"),
        "a binder referenced from an arm GUARD is self-recursion as much as one \
         referenced from an arm body; the guard-blind walk reported the arm-guard \
         refusal instead:\n{cpp}"
    );
}

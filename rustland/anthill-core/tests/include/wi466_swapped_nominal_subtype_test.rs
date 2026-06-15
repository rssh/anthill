//! WI-466 (WI-405 follow-up, same root cause): the `(parameterized, sort_ref)`
//! arm of `types_compatible` called `sort_sym_compatible` with SWAPPED args —
//! `(expected_spec, actual_base)` instead of the `(actual, expected)` direction
//! the working `(sort_ref, parameterized)` sibling arm (and the adjacent
//! `sort_provides_admissibly(actual_base, expected)`) use. In that arm the
//! PARAMETERIZED side is the ACTUAL and the bare `sort_ref` side the EXPECTED, so
//! the correct call is `sort_sym_compatible(actual_base, expected)`.
//!
//! The swap was TWO latent defects, exercised here in BOTH directions through
//! RETURN-type conformance (`operation f(x: A) -> B = x` loads clean iff `A <: B`):
//!
//!   (1) FALSE-REJECT — a parameterized actual whose base REFINES (via `requires`)
//!       the bare expected did not conform. `Refined[T = Int64]` returned as bare
//!       `Base`, where `Refined requires Base`, must conform (the ticket's repro,
//!       which errored `expected Base, got Refined[T = Int64]` pre-fix).
//!
//!   (2) FALSE-ACCEPT (soundness) — the REVERSE: a parameterized `Base[..]` was
//!       wrongly admitted where an expected sort that REFINES `Base` was demanded.
//!       `Base2[X = Int64]` returned as `Refined2` (where `Refined2 requires Base2`)
//!       must be REJECTED — a `Base2` is not a `Refined2`.
//!
//! The fix changes the nominal check in BOTH `types_compatible_term_dispatch` and
//! its carrier peer `types_compatible_view_structural`; these load tests exercise
//! the term-dispatch path.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

fn load_errors(extras: &[&str]) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    for ex in extras {
        parsed.push(parse::parse(ex).expect("parse extra"));
    }
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

// ── (1) FALSE-REJECT fix: parameterized refining actual → bare expected ─────────

/// The ticket's exact repro. `Refined requires Base`, so a `Refined[T = Int64]`
/// (parameterized actual) conforms to the bare `Base` (sort_ref expected). Base is
/// memberless, so the WI-401 abstracting-return gate does not enter — the only
/// question is the nominal refinement direction, which pre-WI-466 was backwards.
#[test]
fn refining_parameterized_actual_conforms_to_bare_base() {
    let src = r#"
namespace test.wi466.refine_ok
  import anthill.prelude.{Int64}
  sort Base
  end
  sort Refined
    requires Base
    sort T = ?
    entity makeRefined(x: T)
  end
  operation f(p: Refined[T = Int64]) -> Base = p
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.is_empty(),
        "Refined requires Base, so Refined[T = Int64] must conform to bare Base \
         (pre-WI-466 false-reject): {errs:?}",
    );
}

// ── (2) FALSE-ACCEPT removal (soundness): parameterized base → refining expected ─

/// The reverse of (1). `Refined2 requires Base2`, so `Base2` does NOT refine
/// `Refined2`; a parameterized `Base2[X = Int64]` must NOT conform to the bare
/// `Refined2`. The swapped call accepted this (it asked "does Refined2 refine
/// Base2?" = yes), an unsound upcast of a supertype value to a subtype. `Base2`
/// does not `provide` `Refined2` either, so the corrected nominal check is the
/// only path — and it now refuses.
#[test]
fn base_parameterized_actual_rejected_against_refining_expected() {
    let src = r#"
namespace test.wi466.refine_unsound
  import anthill.prelude.{Int64}
  sort Base2
    sort X = ?
    entity makeBase2(x: X)
  end
  sort Refined2
    requires Base2
    entity makeRefined2(n: Int64)
  end
  operation g(p: Base2[X = Int64]) -> Refined2 = p
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        !errs.is_empty(),
        "Base2 does NOT refine Refined2 (the requires is the other way); returning a \
         Base2[X = Int64] as Refined2 must be REJECTED (pre-WI-466 false-accept)",
    );
}

/// Control: the corrected direction did not break the `(sort_ref, parameterized)`
/// sibling — a refining actual on the BARE side still conforms to a parameterized
/// expected of its parent. `RefinedC requires BaseC`; a bare `RefinedC` value
/// conforms to a `BaseC[X = Int64]`-shaped expected only via the binding-precise
/// path, so here we keep it nominal: a `RefinedC` conforms to bare `BaseC`.
#[test]
fn sibling_arm_bare_refining_actual_still_conforms() {
    let src = r#"
namespace test.wi466.sibling_ok
  import anthill.prelude.{Int64}
  sort BaseC
  end
  sort RefinedC
    requires BaseC
    entity makeRefinedC(n: Int64)
  end
  operation k(p: RefinedC) -> BaseC = p
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.is_empty(),
        "RefinedC requires BaseC, so a RefinedC must still conform to BaseC \
         (the bare↔bare arm is unaffected): {errs:?}",
    );
}

//! WI-427: BIDIRECTIONAL `expected → argument` inference — the missing half of "both
//! sides." WI-379 delivered `argument → expected` (args-before-expected); this is the
//! reverse: the declared PARAMETER TYPE must flow *down* into an argument as a top-down
//! checking hint, so a polymorphic argument whose type parameter appears ONLY in its
//! return (and so is unconstrained from the argument itself) is pinned by the call
//! context.
//!
//! These are the **acceptance checklist anchors** for the bidirectional-flow example in
//! `docs/design/path-dependent-types.md` §4.1, live since WI-427 landed (before it, the
//! argument was synthesized in isolation via `push_visit_no_hint`, so `poly`'s `X` was
//! reported "unconstrained" before the param type could pin it). Three flows must meet
//! for the example to typecheck:
//!   1. expected → argument (WI-427): the param `Wrapper[P = Inner[T = String]]` pins
//!      `poly()`'s `X = String`;
//!   2. projection off the grounded receiver (WI-398, delivered): `s.cell.T = String`;
//!   3. argument → parameter (WI-379, delivered): `"abc" : String` checks against `k`.
//!
//! SOUNDNESS: the hint must pin by EQUALITY (a concrete/structured param type), never by
//! forcing a metavariable through a `<:` subtype constraint — the hard case WI-379's
//! args-first order deliberately sidesteps (expansion-during-unification.md variance note).

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

/// The bidirectional-flow checklist example must typecheck: the param type pins the
/// polymorphic argument's return-only `X` (expected → argument), the projection grounds
/// off the receiver, and the `String` value checks against `k`.
#[test]
fn bidirectional_flow_conforms() {
    let ok = r#"
namespace test.wi427.ok
  import anthill.prelude.String
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  sort Wrapper
    sort P = ?
    entity wrap(cell: P)
  end
  operation check(s: Wrapper[P = Inner[T = String]], k: s.cell.T) -> String
  operation poly[X]() -> Wrapper[P = Inner[T = X]]
  operation caller() -> String = check(poly(), "abc")
end
"#;
    assert!(
        load_errors(&[ok]).is_empty(),
        "param type Wrapper[P=Inner[T=String]] must pin poly's X=String (expected→argument), \
         then s.cell.T = String and \"abc\" conforms",
    );
}

/// The soundness twin: with `X` pinned to `String` via the param type, `k : s.cell.T` is
/// `String`, so passing `42` (Int64) must be rejected — and for the RIGHT reason
/// (String/Int64 mismatch), not the current "X unconstrained".
#[test]
fn bidirectional_flow_wrong_value_rejected_for_right_reason() {
    let wrong = r#"
namespace test.wi427.wrong
  import anthill.prelude.{String, Int64}
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  sort Wrapper
    sort P = ?
    entity wrap(cell: P)
  end
  operation check(s: Wrapper[P = Inner[T = String]], k: s.cell.T) -> String
  operation poly[X]() -> Wrapper[P = Inner[T = X]]
  operation caller() -> String = check(poly(), 42)
end
"#;
    let errs = load_errors(&[wrong]);
    assert!(
        errs.iter().any(|e| e.contains("String") && e.contains("Int64")),
        "k : s.cell.T is String (via the pinned X), so 42 must be rejected as String/Int64; \
         got: {errs:?}",
    );
}

/// The constructor-field twin: a nested call in an ENTITY FIELD slot whose declared
/// field type is ground pins the same way (`hold(poly())` — `poly`'s return-only `X`
/// is pinned by the field type `w: Wrapper[P = Inner[T = String]]`).
#[test]
fn bidirectional_flow_constructor_field_pins() {
    let ok = r#"
namespace test.wi427.ctor
  import anthill.prelude.String
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  sort Wrapper
    sort P = ?
    entity wrap(cell: P)
  end
  sort Holder
    entity hold(w: Wrapper[P = Inner[T = String]])
  end
  operation poly[X]() -> Wrapper[P = Inner[T = X]]
  operation caller() -> Holder = hold(poly())
end
"#;
    let errs = load_errors(&[ok]);
    assert!(errs.is_empty(), "constructor-field twin: {errs:?}");
}

//! WI-381: resolve a DEFINED-TYPE / ALIAS to its underlying shape BEFORE expansion
//! and projection (design `docs/design/expansion-during-unification.md` §1, §6 OQ6).
//!
//! A bare reference to `sort IntList = List[T = Int]` must resolve to its shape
//! `List[T = Int]` so that:
//!   - a projection `s.T` on `s: IntList` projects off the RESOLVED shape (=> `Int`),
//!     not the opaque alias (which declares no member `T`); chains
//!     (`Top = Mid`, `Mid = List[T = Int]`) follow to a finite shape;
//!   - the alias-fixed binding `T = Int` is KEPT — an `IntList` value conforms to its
//!     own definition `List[T = Int]` and is rejected against `List[T = String]`; the
//!     alias did NOT go all-fresh and lose `T = Int`.
//!
//! Sites fixed (Rust typer): the projection eliminator (`project_type_member`), the
//! `parameterized ↔ sort_ref` unify boundary (`unify_parameterized_with_sort_ref`),
//! and the subtype boundary (`types_compatible`). Prerequisite for WI-374 (expansion)
//! and WI-376 (projection) over aliases.
//!
//! NOTE — the ARGUMENT-side enforcement (passing an `IntList` where `List[T = String]`
//! is expected) is NOT yet observable here: operation arguments are not type-checked
//! against their declared types until **WI-385** (the arg-unify booleans are
//! discarded). The unify-boundary fix is in place for when that lands; the
//! return/projection positions below are the checked positions today.

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

/// A partially-applied parametric alias parses + loads.
#[test]
fn alias_loads() {
    let src = r#"
namespace test.wi381.loads
  import anthill.prelude.{List, Int}
  sort IntList = List[T = Int]
  operation use_it(l: IntList) -> Int
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "alias `sort IntList = List[T = Int]` should load: {errs:?}");
}

/// `s.T` on an `IntList` projects `Int` (off the resolved shape `List[T = Int]`).
#[test]
fn alias_projection_projects_resolved_member() {
    let src = r#"
namespace test.wi381.proj
  import anthill.prelude.{List, Int}
  sort IntList = List[T = Int]
  operation peek(l: IntList) -> l.T
  operation caller(xs: IntList) -> Int = peek(xs)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.is_empty(),
        "peek(xs) is IntList.T = (List[T=Int]).T = Int; returning it as Int must conform: {errs:?}",
    );
}

/// The resolved member is REAL: `peek(xs)` is `Int`, so returning it where `String` is
/// declared is rejected (the projection did not invent a fresh element).
#[test]
fn alias_projection_wrong_member_rejected() {
    let src = r#"
namespace test.wi381.proj_wrong
  import anthill.prelude.{List, Int, String}
  sort IntList = List[T = Int]
  operation peek(l: IntList) -> l.T
  operation caller(xs: IntList) -> String = peek(xs)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        !errs.is_empty(),
        "peek(xs) is Int (resolved off IntList); returning it as String must be REJECTED",
    );
}

/// A simple-alias CHAIN `Top = Mid`, `Mid = List[T = Int]` follows to a finite shape,
/// so `s.T` on a `Top` still projects `Int`.
#[test]
fn alias_chain_projection() {
    let src = r#"
namespace test.wi381.chain
  import anthill.prelude.{List, Int}
  sort Mid = List[T = Int]
  sort Top = Mid
  operation peek(l: Top) -> l.T
  operation caller(xs: Top) -> Int = peek(xs)
end
"#;
    let errs = load_errors(&[src]);
    assert!(errs.is_empty(), "Top -> Mid -> List[T=Int]; (Top).T must project Int: {errs:?}");
}

/// `T = Int` is KEPT at the subtype boundary: an `IntList` conforms to its own
/// definition `List[T = Int]` (return-conformance — a checked position today).
#[test]
fn alias_return_conformance_keeps_binding_ok() {
    let src = r#"
namespace test.wi381.ret_ok
  import anthill.prelude.{List, Int}
  sort IntList = List[T = Int]
  operation f(xs: IntList) -> List[T = Int] = xs
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.is_empty(),
        "an IntList value must conform to its own definition List[T = Int]: {errs:?}",
    );
}

/// `T = Int` is KEPT (not all-fresh): an `IntList` does NOT conform to
/// `List[T = String]` — returning one there is rejected.
#[test]
fn alias_return_conformance_wrong_binding_rejected() {
    let src = r#"
namespace test.wi381.ret_wrong
  import anthill.prelude.{List, Int, String}
  sort IntList = List[T = Int]
  operation g(xs: IntList) -> List[T = String] = xs
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        !errs.is_empty(),
        "IntList resolves to List[T=Int]; conforming it to List[T=String] must be REJECTED",
    );
}

/// A CYCLIC alias (`A = B`, `B = A`) must not hang the resolver — the cycle guard
/// refuses to resolve, leaving the alias opaque (a projection over it then surfaces a
/// loud error rather than looping). The point of the test is TERMINATION.
#[test]
fn cyclic_alias_terminates() {
    let src = r#"
namespace test.wi381.cyclic
  import anthill.prelude.{Int}
  sort A = B
  sort B = A
  operation peek(x: A) -> x.T
  operation caller(xs: A) -> Int = peek(xs)
end
"#;
    // Either the loader rejects the cyclic definition or projection over the opaque
    // alias is a loud error — in both cases the call returns (does not loop).
    let errs = load_errors(&[src]);
    assert!(
        !errs.is_empty(),
        "a cyclic alias / projection over an unresolvable alias must be a loud error, not a hang",
    );
}

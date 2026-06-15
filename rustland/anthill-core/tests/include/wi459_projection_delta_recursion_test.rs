//! WI-459 (Gap A — DOMINANT WI-447 blocker): projection neutrals must compare by
//! DEFINITIONAL (δ) equality, not syntactic identity. A recursive / consuming body's
//! projected member off a LOCAL whose type BINDS that member must δ-reduce to the bound
//! value, rather than survive as a fresh neutral that then fails an identity check.
//!
//! MINIMAL REPRO (the historical `/tmp/probeD`):
//! ```text
//! operation sfd(xs: List) -> Option[Pair[A=xs.T, B=List[T=xs.T]]]
//!   = match xs case nil->none case cons(h,t)->some(pair(h,t))
//! operation collectd(xs: List) -> List[T=xs.T]
//!   = match sfd(xs) case none->nil case some(pair(h,rest))->cons(head:h, tail:collectd(rest))
//! ```
//! `collectd(rest)` is `List[rest.T]`; `rest : List[T = xs.T]`, so `rest.T` is
//! DEFINITIONALLY EQUAL to `xs.T` (δ: project `T` off `rest`'s type binding) but NOT
//! syntactically identical. Before this fix it leaked to the ζ arm as a fresh neutral and
//! failed `match.rule: expected List[T=xs.T], got List[T=xs.T]` (same print, distinct
//! identity).
//!
//! Design: `docs/design/path-dependent-types.md` (the WI-400 non-injective ζ core stays
//! non-decomposing; the δ-reduction lives at the ELIMINATION site, which has the receiver's
//! type in hand).

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

/// The DOMINANT repro: a recursive consumer whose recursion variable carries a
/// projection-bound element type-checks — `collectd(rest) : List[T = rest.T]` δ-reduces to
/// the enclosing `List[T = xs.T]` because `rest : List[T = xs.T]`.
#[test]
fn recursive_projection_consumer_delta_reduces() {
    let ok = r#"
namespace test.wi459.collectd
  import anthill.prelude.{List, Option, Pair}
  import anthill.prelude.Pair.{pair}
  operation sfd(xs: List) -> Option[Pair[A = xs.T, B = List[T = xs.T]]]
    = match xs
        case nil -> none
        case cons(h, t) -> some(pair(h, t))
  operation collectd(xs: List) -> List[T = xs.T]
    = match sfd(xs)
        case none -> nil
        case some(pair(h, rest)) -> cons(head: h, tail: collectd(rest))
end
"#;
    let errs = load_errors(&[ok]);
    assert!(
        errs.is_empty(),
        "collectd(rest) : List[rest.T] must δ-reduce to List[xs.T] (rest : List[T = xs.T]); \
         got: {errs:?}",
    );
}

/// The EFFECT DUAL: a recursive consumer that declares the receiver's access effect
/// (`effects s.E`) and recurses on a tail whose type binds that effect must type-check —
/// the recursive call's `effects s.E` δ-reduces to the enclosing `s.E` because
/// `rest : Src[T = s.T, E = s.E]`. Before this fix the blanket effect `Ref`-substitution
/// re-keyed the δ-reduced `s.E` to `rest.E`, surfacing the ticket's
/// "undeclared effect: s.E, body's s.E = rest.E".
#[test]
fn recursive_projection_consumer_effect_dual_delta_reduces() {
    let ok = r#"
namespace test.wi459.counte
  import anthill.prelude.{Option, Pair, Int64, EffectsRuntime}
  import anthill.prelude.Pair.{pair}
  import anthill.prelude.Numeric.{add}
  sort Src
    import anthill.prelude.EffectsRuntime
    sort T = ?
    effects E = ?
  end
  operation sfdE(s: Src) -> Option[Pair[A = s.T, B = Src[T = s.T, E = s.E]]] effects s.E
  operation countE(s: Src) -> Int64 effects s.E
    = match sfdE(s)
        case none -> 0
        case some(pair(h, rest)) -> add(1, countE(rest))
end
"#;
    let errs = load_errors(&[ok]);
    assert!(
        errs.is_empty(),
        "countE(rest) : effects rest.E must δ-reduce to s.E (rest : Src[E = s.E]); \
         got: {errs:?}",
    );
}

/// SOUNDNESS (WI-400 non-injectivity preserved): the re-keying does NOT let a neutral
/// absorb a concrete demand. `h : xs.T` is the re-keyed abstract neutral (the `A` field of
/// `sfd`'s `Pair[A = xs.T, …]` result); returning it under a CONCRETE declared return
/// (`-> Int64`) must be REJECTED at the branch/return conformance — a neutral never equals
/// `Int64`. The fix re-keys a neutral's RECEIVER (formal → argument); it never decomposes
/// or grounds a neutral against a concrete type. (The `none -> 0` branch pins the match's
/// expected to `Int64`, so the `h` branch is checked against it directly — the return gate,
/// not an incidental constructor-arg clash.)
#[test]
fn neutral_element_under_concrete_return_rejected() {
    let wrong = r#"
namespace test.wi459.first_wrong
  import anthill.prelude.{List, Option, Pair, Int64}
  import anthill.prelude.Pair.{pair}
  operation sfd(xs: List) -> Option[Pair[A = xs.T, B = List[T = xs.T]]]
    = match xs
        case nil -> none
        case cons(h, t) -> some(pair(h, t))
  operation firstOrZero(xs: List) -> Int64
    = match sfd(xs)
        case none -> 0
        case some(pair(h, rest)) -> h
end
"#;
    let errs = load_errors(&[wrong]);
    assert!(
        errs.iter().any(|e| e.contains("xs.T") && e.contains("Int64")),
        "h : xs.T (neutral) cannot satisfy a concrete `-> Int64` — a neutral never absorbs a \
         concrete demand; expected a mismatch naming xs.T vs Int64, got: {errs:?}",
    );
}

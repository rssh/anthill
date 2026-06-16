//! WI-404 — a DENOTED / value-in-type parameter binding must round-trip through
//! the SUBTYPE check, so a denoted-bearing parameterized type conforms to ITSELF.
//!
//! THE ORIGINAL BUG (surfaced 2026-06-06): a binding like `N = 3` in
//! `Vec[T = Int64, N = 3]` (a value-in-type / denoted parameter) was dropped to a
//! wildcard `N = ?` on the way into `parameterized_compatible_view` /
//! `check_binding_by_variance`, so returning a `Vec[T=Int64,N=3]` value where
//! `Vec[T=Int64,N=3]` was declared was SPURIOUSLY REJECTED (a type not compatible
//! with itself) — and, the latent soundness smell, a real mismatch `N=3` vs `N=4`
//! could have been MASKED by both sides collapsing to `?`.
//!
//! RESOLUTION (two halves — "compares" and "renders"):
//!   - COMPARES: the comparison half was resolved by the cumulative value-in-type
//!     denoted work — decisively by WI-481 ("re-key value-in-type denoted param
//!     refs in a call's return type"), which makes the denoted SURVIVE into a
//!     synthesized call-return type instead of being dropped to a fresh inference
//!     var, plus the `(denoted, denoted)` subtype arm (WI-342) that compares two
//!     denoteds structurally via `unify_denoted_view`. These tests LOCK IN that
//!     resolution across the vehicles the ticket names (plain literal, value-place,
//!     alias, member-op) and pin the soundness direction (a differing denoted is
//!     still rejected).
//!   - RENDERS: the rendering half is fixed in this change — `denoted_value_display`
//!     dropped a LITERAL denoted (`N = 3`) to `?`, so the mismatch error read
//!     `expected N = ?, got N = ?` (illegible, the exact "renders as N = ?" symptom).
//!     It now renders the literal, asserted by `differing_denoted_literal_rejected`.
//!
//! Why the accept+reject pairs are a real guard (not an identity short-circuit):
//! if the denoted `N` had collapsed to a wildcard, the body type would conform to
//! BOTH `N=3` AND `N=4` — but the `N=4` / mismatched-place cases are REJECTED while
//! the matching cases are ACCEPTED, so the synthesized body type provably carries
//! the concrete denoted value, not a wildcard.

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

// A sort `Vec` with a type param `T` and a value-in-type param `N` (a denoted
// literal fills it), plus a producer op whose return carries the denoted `N = 3`.
const VEC: &str = r#"
namespace test.wi404.vec
  import anthill.prelude.{Int64}
  export Vec, mk
  sort Vec
    sort T = ?
    sort N = ?
  end
  operation mk() -> Vec[T = Int64, N = 3]
end
"#;

/// THE CORE CASE: a consumer whose declared return is exactly the producer's
/// denoted-bearing return type must LOAD CLEAN — `Vec[T=Int64,N=3]` conforms to
/// itself (the denoted literal `N = 3` round-trips through the subtype check).
#[test]
fn denoted_literal_parameterized_conforms_to_itself() {
    let consumer = r#"
namespace test.wi404.use
  import anthill.prelude.{Int64}
  import test.wi404.vec.{Vec, mk}
  operation usevec() -> Vec[T = Int64, N = 3] = mk()
end
"#;
    let errs = load_errors(&[VEC, consumer]);
    assert!(
        errs.is_empty(),
        "a denoted-bearing parameterized type must conform to itself (WI-404); got: {errs:?}",
    );
}

/// MUST STILL REJECT — a consumer declaring `N = 4` while the body produces
/// `N = 3` is a genuine mismatch. With the accepting case above, this pins that the
/// denoted value is preserved in the comparison (not collapsed to a wildcard that
/// would conform to any `N`).
#[test]
fn differing_denoted_literal_rejected() {
    let consumer = r#"
namespace test.wi404.bad
  import anthill.prelude.{Int64}
  import test.wi404.vec.{Vec, mk}
  operation badvec() -> Vec[T = Int64, N = 4] = mk()
end
"#;
    let errs = load_errors(&[VEC, consumer]);
    assert!(
        !errs.is_empty(),
        "a consumer declaring N = 4 over a body producing N = 3 must be REJECTED (WI-404 \
         must not mask a real mismatch by collapsing the denoted to a wildcard); got no errors",
    );
    // WI-404 rendering half: the literal denoted must RENDER as its value (`N = 3` /
    // `N = 4`), not the `?` fallthrough that hid which binding clashed.
    let joined = errs.join(" | ");
    assert!(
        joined.contains("N = 3") && joined.contains("N = 4"),
        "the mismatch error must name the actual literals (`N = 3` vs `N = 4`), not `N = ?` \
         (WI-404 rendering); got: {errs:?}",
    );
}

/// Value-PLACE denoted (`N = c`, `c` a param) rather than a literal — the WI-481
/// re-keying vehicle. The body `mk(c)` re-keys its declared `N = mk.c` to the
/// caller's `c`, which must conform to the declared `N = c`.
#[test]
fn denoted_value_place_conforms_to_itself() {
    let vec = r#"
namespace test.wi404.vpvec
  import anthill.prelude.{Int64}
  export Vec, Producer, mk
  sort Vec
    sort T = ?
    sort N = ?
  end
  sort Producer
  end
  operation mk(c: Producer) -> Vec[T = Int64, N = c]
end
"#;
    let consumer = r#"
namespace test.wi404.vpuse
  import anthill.prelude.{Int64}
  import test.wi404.vpvec.{Vec, Producer, mk}
  operation usevec(c: Producer) -> Vec[T = Int64, N = c] = mk(c)
end
"#;
    let errs = load_errors(&[vec, consumer]);
    assert!(errs.is_empty(), "value-place denoted self-conformance (WI-404); got: {errs:?}");
}

/// Value-place SOUNDNESS control: the body produces `N = c` but the declared return
/// is `N = d` (a DIFFERENT param). Must REJECT — the denoted place must not collapse
/// to a wildcard that masks the mismatch.
#[test]
fn differing_denoted_value_place_rejected() {
    let vec = r#"
namespace test.wi404.vpmvec
  import anthill.prelude.{Int64}
  export Vec, Producer, mk
  sort Vec
    sort T = ?
    sort N = ?
  end
  sort Producer
  end
  operation mk(c: Producer) -> Vec[T = Int64, N = c]
end
"#;
    let consumer = r#"
namespace test.wi404.vpmuse
  import anthill.prelude.{Int64}
  import test.wi404.vpmvec.{Vec, Producer, mk}
  operation usevec(c: Producer, d: Producer) -> Vec[T = Int64, N = d] = mk(c)
end
"#;
    let errs = load_errors(&[vec, consumer]);
    assert!(
        !errs.is_empty(),
        "a body producing N = c against a declared N = d (different place) must be REJECTED \
         (WI-404 value-place soundness); got no errors",
    );
}

/// The ORIGINAL surfacing vehicle (WI-381 alias resolution): a denoted-bearing alias
/// `Vec3i = Vec[T = Int64, N = 3]` must conform to its own definition, so a value of
/// `Vec[T=Int64,N=3]` is returnable where `Vec3i` is declared.
#[test]
fn denoted_bearing_alias_conforms_to_definition() {
    let vec = r#"
namespace test.wi404.alvec
  import anthill.prelude.{Int64}
  export Vec, Vec3i, mk
  sort Vec
    sort T = ?
    sort N = ?
  end
  sort Vec3i = Vec[T = Int64, N = 3]
  operation mk() -> Vec[T = Int64, N = 3]
end
"#;
    let consumer = r#"
namespace test.wi404.aluse
  import anthill.prelude.{Int64}
  import test.wi404.alvec.{Vec, Vec3i, mk}
  operation usevec() -> Vec3i = mk()
end
"#;
    let errs = load_errors(&[vec, consumer]);
    assert!(errs.is_empty(), "denoted-bearing alias self-conformance (WI-404); got: {errs:?}");
}

/// A sort-MEMBER op (the abstract-member path) whose return carries the denoted —
/// the body call `mk(c)` and the declared return both carry `N = 3` and must conform.
#[test]
fn denoted_member_op_return_conforms() {
    let vec = r#"
namespace test.wi404.mvec
  import anthill.prelude.{Int64}
  export Vec
  sort Vec
    sort T = ?
    sort N = ?
    operation mk(c: Vec) -> Vec[T = Int64, N = 3]
    operation usevec(c: Vec) -> Vec[T = Int64, N = 3] = mk(c)
  end
end
"#;
    let errs = load_errors(&[vec]);
    assert!(errs.is_empty(), "member-op denoted return self-conformance (WI-404); got: {errs:?}");
}

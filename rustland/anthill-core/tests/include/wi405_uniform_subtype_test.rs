//! WI-405: the subtype relation (`types_compatible`) must apply its helpers
//! UNIFORMLY across dispatch arms. Two latent false-rejects — surfaced by the
//! WI-381 and WI-384 code-reviews, both off the critical path but real — are
//! closed by threading the relevant helper through the arms it was missing from.
//!
//! FACET A (provider admissibility). WI-344's `sort_provides_admissibly` was
//! confined to the bare↔bare `(sort_ref, sort_ref)` arm. A value whose type is a
//! PARAMETERIZED form `S[bindings]` — including a PARTIAL form such as a
//! constructor result `S[A = ?_]` (B left unbound) after WI-384 — compared
//! against a BARE provider spec `Spec` it provides (`S provides Spec`) lost
//! provider admissibility: the `(parameterized, sort_ref)` arm did nominal
//! base-sort compat ONLY. Now provider admissibility runs in that arm too (and
//! its carrier-agnostic peer in `types_compatible_view_structural`). Sound: a
//! bare spec carries no bindings to drop, the same reasoning that confines the
//! base-only check to the bare↔bare arm.
//!
//! FACET B (alias resolution). WI-381 wired `resolve_alias_shape` into the
//! bare↔parameterized arms but NOT the bare↔bare arm, so two aliases of the SAME
//! shape (`sort IntList = List[T = Int64]; sort IntList2 = List[T = Int64]`)
//! compared bare↔bare did a nominal NAME compare only → false-reject. Now the
//! `(sort_ref, sort_ref)` arm resolves a (ground) alias on either side and
//! re-dispatches.
//!
//! All checked through RETURN-type conformance (`check_operation_bodies`), which
//! is enforced today: `operation f(x: A) -> B = x` loads clean iff `A <: B`.

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

// ── FACET A: parameterized carrier vs bare provider spec ────────────────────

// A multi-param carrier `S` that PROVIDES a bare (param-less) spec `Spec`, with a
// constructor `makeS` that binds only `A` (so its result is the PARTIAL form
// `S[A = …]`, `B` unbound). `NonProv` is a same-shaped carrier that does NOT
// provide `Spec` — the negative control.
const FACET_A_PRELUDE: &str = r#"
  import anthill.prelude.{String, Int64}
  sort Spec
  end
  sort S
    sort A = ?
    sort B = ?
    provides Spec
    entity makeS(a: A)
  end
  sort NonProv
    sort A = ?
    sort B = ?
    entity makeNonProv(a: A)
  end
"#;

/// A PARTIAL parameterized type `S[A = String]` (B unbound) conforms to the bare
/// provider spec `Spec` it provides — the ticket's headline accept.
#[test]
fn partial_parameterized_conforms_to_bare_provider_spec() {
    let src = format!(
        "namespace test.wi405.partial\n{FACET_A_PRELUDE}\n  operation f(p: S[A = String]) -> Spec = p\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "S[A = String] (partial) provides Spec; returning it as bare Spec must conform: {errs:?}",
    );
}

/// The exact ticket repro: a CONSTRUCTOR result `makeS(\"hi\")` infers `S[A = String]`
/// (B unbound) and is returned where bare `Spec` is expected.
#[test]
fn constructor_result_conforms_to_bare_provider_spec() {
    let src = format!(
        "namespace test.wi405.ctor\n{FACET_A_PRELUDE}\n  operation g() -> Spec = makeS(\"hi\")\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "makeS(\"hi\") : S[A = String] provides Spec; returning it as bare Spec must conform: {errs:?}",
    );
}

/// A fully-bound parameterized carrier `S[A = String, B = Int64]` also conforms to
/// the bare provider spec — provider admissibility is binding-agnostic on a bare
/// spec (there are no bindings to check).
#[test]
fn full_parameterized_conforms_to_bare_provider_spec() {
    let src = format!(
        "namespace test.wi405.full\n{FACET_A_PRELUDE}\n  operation h(p: S[A = String, B = Int64]) -> Spec = p\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        errs.is_empty(),
        "S[A = String, B = Int64] provides Spec; returning it as bare Spec must conform: {errs:?}",
    );
}

/// The accept is GATED on the provider fact: a same-shaped carrier that does NOT
/// provide `Spec` stays rejected (the relation widened along `provides`, not for
/// every parameterized type).
#[test]
fn parameterized_non_provider_rejected_against_bare_spec() {
    let src = format!(
        "namespace test.wi405.nonprov\n{FACET_A_PRELUDE}\n  operation bad(p: NonProv[A = String]) -> Spec = p\nend\n"
    );
    let errs = load_errors(&[&src]);
    assert!(
        !errs.is_empty(),
        "NonProv does not provide Spec; a NonProv[A = String] must NOT conform to bare Spec",
    );
}

// ── FACET B: alias vs same-shape alias ──────────────────────────────────────

/// Two DISTINCT aliases of the SAME shape conform bare↔bare: an `IntList` value is
/// usable where an `IntList2` is expected, because both resolve to `List[T = Int64]`.
#[test]
fn alias_conforms_to_same_shape_alias() {
    let src = r#"
namespace test.wi405.alias_ok
  import anthill.prelude.{List, Int64}
  sort IntList = List[T = Int64]
  sort IntList2 = List[T = Int64]
  operation f(xs: IntList) -> IntList2 = xs
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.is_empty(),
        "IntList and IntList2 both resolve to List[T = Int64]; an IntList must conform to IntList2: {errs:?}",
    );
}

/// The alias resolution is binding-PRECISE: aliases of DIFFERENT shape do NOT
/// conform (the resolution keeps the fixed bindings, it does not erase them).
#[test]
fn alias_to_different_shape_alias_rejected() {
    let src = r#"
namespace test.wi405.alias_wrong
  import anthill.prelude.{List, Int64, String}
  sort IntList = List[T = Int64]
  sort StrList = List[T = String]
  operation g(xs: IntList) -> StrList = xs
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        !errs.is_empty(),
        "IntList resolves to List[T=Int64], StrList to List[T=String]; the conversion must be REJECTED",
    );
}

/// TERMINATION guard for FACET B. A NON-WELL-FOUNDED alias — one whose ground shape
/// transitively references itself through a binding — has no finite expansion.
/// Resolving it to a one-step shape and re-dispatching through `types_compatible`
/// would recurse forever (a stack overflow on load). The well-foundedness guard in
/// `resolve_alias_shape` leaves such an alias OPAQUE, so the subtype check
/// terminates with a (sound, conservative) nominal false-reject. The point of the
/// test is that it RETURNS at all — like WI-381's `cyclic_alias_terminates`, but for
/// a DEEP structural cycle that the bare-ref chain guard does not catch.
#[test]
fn recursive_parameterized_alias_terminates() {
    let src = r#"
namespace test.wi405.rec_alias
  import anthill.prelude.{List}
  sort A = List[T = B]
  sort B = List[T = A]
  sort C = List[T = D]
  sort D = List[T = C]
  operation f(x: A) -> C = x
end
"#;
    // If FACET B did not bound the recursion this overflows the stack; reaching the
    // assert at all proves termination. The recursive aliases stay opaque, so the
    // cross-alias return does not conform → a loud error (never a hang).
    let errs = load_errors(&[src]);
    assert!(
        !errs.is_empty(),
        "non-well-founded recursive aliases stay opaque; A does not conform to C, and the \
         check must TERMINATE with an error rather than hang",
    );
}

/// FACET A reaches the WI-401 abstracting-return gate for a PARAMETERIZED body too:
/// `S[A = String]` provides the bare spec `MemberSpec`, so the conformance check now
/// ACCEPTS the upcast — but `MemberSpec` has a member `K` left wholly unbound by the
/// bare return, so the body mints a hidden-local abstraction that escapes (the
/// avoidance problem). The gate must still fire (it ran only for a bare body before
/// FACET A widened this arm).
#[test]
fn parameterized_body_abstracting_return_still_rejected() {
    let src = r#"
namespace test.wi405.escape
  import anthill.prelude.{String}
  sort MemberSpec
    sort K = ?
  end
  sort S
    sort A = ?
    sort B = ?
    provides MemberSpec
    entity makeS(a: A)
  end
  operation seal(p: S[A = String]) -> MemberSpec = p
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.iter().any(|e| e.contains("abstracting return") || e.contains("escape")),
        "S[A = String] upcast to bare MemberSpec leaves member K unbound; the WI-401 gate must \
         still reject the abstracting return, got: {errs:?}",
    );
}

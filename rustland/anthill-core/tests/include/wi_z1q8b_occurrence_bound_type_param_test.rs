//! An operation's TYPE PARAMETER bound to an OCCURRENCE-CARRIED type is substituted into
//! the types built over it, instead of being left a wildcard.
//!
//! FOUND by WI-20260923-Z1Q8B's driven controls and fixed inline, with no ticket of its own:
//! reading `.v` off a value typed `Foo[T = Int64, N = 3]` did not type, while the same read
//! off `Foo[T = Int64]` did.
//!
//! THE MECHANISM. A type rides the occurrence carrier (`Value::Node`) whenever it carries a
//! denoted — the literal `3` in `Foo[T = Int64, N = 3]`. The typer resolves a call's return
//! type with `walk_type_deep_value`, whose hash-consed arm is `walk_type_deep_g`: `TermId`
//! in and out, so a variable bound to a non-`Term` carrier comes back as the bare variable
//! (WI-394: `walk_type` "deliberately STOPS" there). A bare variable in a resolved type is a
//! WILDCARD, so the binding was not just unread — it stopped constraining anything.
//! `rewrite_type_occ_deep` had the same drop in its interned-child arm, one carrier over.
//!
//! MEASURED at 5ec10808 — every program below loaded clean, or was refused, the wrong way
//! round, while its hash-consed twin was right:
//!   * `idf[A](x: A) -> A` laundered `Foo[T = Int64, N = 3]` into a declared
//!     `Foo[T = String, N = 3]` — a WRONG ACCEPT through the identity function;
//!   * `wrap[A](x: A) -> Option[T = A]`, the same one level down;
//!   * `pairUp[A](x: A) -> Two[L = A, R = Foo[T = Int64, N = 3]]`, the same with the RETURN
//!     type itself on the occurrence carrier (the `rewrite_type_occ_deep` twin);
//!   * `mk(1).v`, `idf(mk(1)).v`, and `.v` on a `match`-bound payload REFUSED — `field_access`
//!     declares `-> FieldOf[T = R, Name = Name]`, `R` stayed a variable, and `FieldOf`
//!     reduced over an abstract operand to a residual (or the dot saw no receiver at all).
//!
//! THE FIX splices each such binding in, walked on its own carrier, and rebuilds only the
//! spine above it — through `KnowledgeBase::fn_value` for a `Value` (a `Value::Entity` when
//! a child is not a leaf, never interned). Inside an occurrence, an occurrence-carried
//! binding is placed as the child it is, and an application rebuilt around one is LOWERED
//! to its type term, the answer that walk's own `TypeNode::Var` arm already gives.
//!
//! THREE BACK-OUTS, each MEASURED over all 6541 `anthill-core` tests; each list is the
//! whole of what failed:
//!   T  the `Value::Term` arm's splice removed → 11: every row here that reads `.v` or
//!      checks a hash-consed return — all but the two occurrence REFUSALS and the nested
//!      control, whose payload comes back LOWERED to a term and so needs no splice to be
//!      read — and the five Z1Q8B controls in `wi1magr_member_signature_test` /
//!      `wi347_override_refinement_test` / `wi431_instance_fact_coverage_test` that read a
//!      field off a denoted-bearing value.
//!   O  the occurrence-child splice removed → 4: the two occurrence-return refusals and
//!      their controls.
//!   L  the lowering of a rebuilt application removed → 2: the nested-application refusal
//!      and its control (the debug build's guard at the splice site panics, as designed).

use anthill_core::eval::Value;

use crate::common;

/// `Foo` carries a phantom `N`, so `Foo[T = Int64, N = 3]` rides the occurrence carrier;
/// `Two` is a second parameterized sort for an occurrence-carried RETURN type. The generic
/// operations bind their `A` to whatever the caller passes. `body` adds the probe.
fn src(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace wi_z1q8b.{ns}
  import anthill.prelude.{{Int64, String, Option}}
  import anthill.prelude.Option.{{some, none}}

  sort Foo
    sort T = ?
    sort N = ?
    entity foo(v: T)
  end

  sort Two
    sort L = ?
    sort R = ?
    entity two(l: L, r: R)
  end

  operation mk(x: Int64) -> Foo[T = Int64, N = 3] = foo(v: x)
  operation mkPlain(x: Int64) -> Foo[T = Int64] = foo(v: x)
  operation idf[A](x: A) -> A = x
  operation wrap[A](x: A) -> Option[T = A] = some(x)
  operation pairUp[A](x: A) -> Two[L = A, R = Foo[T = Int64, N = 3]] = two(l: x, r: mk(1))
  operation pairOpt[A](x: A) -> Two[L = Option[T = A], R = Foo[T = Int64, N = 3]] =
    two(l: some(x), r: mk(1))
{body}
end
"#
    )
}

fn load_errors(src: &str) -> Vec<String> {
    common::try_load_kb_with(src).err().unwrap_or_default()
}

/// Load `src`, call its zero-argument `probe`, and return the `Int64` it answers.
fn probe(ns: &str, body: &str) -> i64 {
    let mut interp = common::interp_for(&src(ns, body));
    match interp.call(&format!("wi_z1q8b.{ns}.probe"), &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("`probe` must load and answer an Int64; got {other:?}"),
    }
}

/// The one refusal every wrong-type row expects: the return check naming both types.
fn assert_return_refused(errs: &[String], expected: &str, got: &str) {
    assert!(
        errs.iter().any(|e| e.contains("probe.return")
            && e.contains(&format!("expected {expected}, got {got}"))),
        "the return type must be checked against what the call really returns, naming both; \
         got: {errs:#?}"
    );
}

// ── the field read that surfaced it ─────────────────────────────────────────────

#[test]
fn a_field_of_a_denoted_bearing_value_types_and_runs() {
    // BACK-OUT T takes it: `FieldOf[T = ?R, Name = "v"]` is the return type.
    let n = probe("field_direct", "  operation probe() -> Int64 = mk(7).v");
    assert_eq!(n, 7);
}

#[test]
fn a_field_through_the_identity_function_types_and_runs() {
    // BACK-OUT T takes it: `idf`'s `A` stays a variable, so the dot has no receiver type.
    let n = probe("field_idf", "  operation probe() -> Int64 = idf(mk(8)).v");
    assert_eq!(n, 8);
}

#[test]
fn a_field_of_a_matched_option_payload_types_and_runs() {
    // BACK-OUT T takes it: the scrutinee's `Option[T = ?A]` gives the pattern binder no
    // type to project from.
    let n = probe(
        "field_match",
        "  operation probe() -> Int64 =
    match wrap(mk(9))
      case some(f) -> f.v
      case none() -> 0",
    );
    assert_eq!(n, 9);
}

// ── the wrong accepts ───────────────────────────────────────────────────────────

#[test]
fn the_identity_function_does_not_launder_a_denoted_bearing_type() {
    // THE WRONG ACCEPT. BACK-OUT T takes it: `idf(mk(1))` typed as the bare `?A`, which
    // unifies with the declared `Foo[T = String, N = 3]`.
    let errs = load_errors(&src(
        "idf_wrong",
        "  operation probe() -> Foo[T = String, N = 3] = idf(mk(1))",
    ));
    assert_return_refused(&errs, "Foo[T = String, N = 3]", "Foo[T = Int64, N = 3]");

    // THE HASH-CONSED TWIN, and the reason the row above is a defect rather than a policy:
    // the same program over `Foo[T = Int64]` is refused. Passes either way by design.
    let errs = load_errors(&src(
        "idf_wrong_plain",
        "  operation probe() -> Foo[T = String] = idf(mkPlain(1))",
    ));
    assert!(
        errs.iter().any(|e| e.contains("probe.return")),
        "the hash-consed twin has always been refused; got: {errs:#?}"
    );
}

#[test]
fn a_parameter_under_a_hash_consed_constructor_is_substituted() {
    // `Option[T = A]` is hash-consed and `A` sits inside it — the spine above the splice
    // is rebuilt. BACK-OUT T takes it.
    let errs = load_errors(&src(
        "wrap_wrong",
        "  operation probe() -> Option[T = Foo[T = String, N = 3]] = wrap(mk(1))",
    ));
    assert_return_refused(
        &errs,
        "Option[T = Foo[T = String, N = 3]]",
        "Option[T = Foo[T = Int64, N = 3]]",
    );
}

// ── the occurrence-carrier twin ─────────────────────────────────────────────────

#[test]
fn a_parameter_inside_an_occurrence_carried_return_type_is_substituted() {
    // `pairUp`'s return type carries a denoted, so IT is an occurrence, and `A` is one of
    // its interned children — `rewrite_type_occ_deep`'s arm, not the term walk's. BACK-OUT
    // O takes it; BACK-OUT T does not.
    let errs = load_errors(&src(
        "pair_wrong",
        "  operation probe() -> Two[L = Foo[T = String, N = 3], R = Foo[T = Int64, N = 3]] = \
         pairUp(mk(2))",
    ));
    assert_return_refused(
        &errs,
        "Two[L = Foo[T = String, N = 3], R = Foo[T = Int64, N = 3]]",
        "Two[L = Foo[T = Int64, N = 3], R = Foo[T = Int64, N = 3]]",
    );
}

#[test]
fn a_parameter_inside_an_occurrence_carried_return_type_runs() {
    // THE CONTROL, driven. BACK-OUTS O and T both take it: O leaves `l`'s type the
    // unsubstituted `?A`, and T leaves the field read over it a `FieldOf` residual.
    let n = probe(
        "pair_ok",
        "  operation probe() -> Int64 =
    match pairUp(mk(5))
      case two(l, r) -> l.v",
    );
    assert_eq!(n, 5);
}

#[test]
fn a_nested_application_inside_an_occurrence_carried_return_type_is_substituted() {
    // `Option[T = A]` is itself an interned child of the occurrence, so the splice
    // rebuilds an APPLICATION there, which has no occurrence-child form and is lowered to
    // its type term. BACK-OUTS O and L take it.
    let errs = load_errors(&src(
        "pairopt_wrong",
        "  operation probe() -> Two[L = Option[T = Foo[T = String, N = 3]], R = Foo[T = Int64, \
         N = 3]] = pairOpt(mk(2))",
    ));
    assert_return_refused(
        &errs,
        "Two[L = Option[T = Foo[T = String, N = 3]], R = Foo[T = Int64, N = 3]]",
        "Two[L = Option[T = Foo[T = Int64, N = 3]], R = Foo[T = Int64, N = 3]]",
    );
}

#[test]
fn a_nested_application_inside_an_occurrence_carried_return_type_runs() {
    // THE CONTROL, driven. BACK-OUTS O and L take it; T does not — the lowered payload is a
    // term, so the field read over it needs no splice.
    let n = probe(
        "pairopt_ok",
        "  operation probe() -> Int64 =
    match pairOpt(mk(6))
      case two(l, r) -> match l
        case some(f) -> f.v
        case none() -> 0",
    );
    assert_eq!(n, 6);
}

//! WI-491 — covariant / projection return types rooted at the receiver.
//!
//! An operation may declare its return as the WHOLE type of one of its own
//! parameters — `operation iterator(m: MappedStream) -> m.Sort = m` — meaning
//! "returns a value of the receiver's type". This is the wide-type sibling of
//! the receiver-type-member projections (WI-376 `x.A` / `X.L`; WI-430
//! carrier-precise): `m.Sort` projects the whole sort of `m`, not one member.
//!
//! The typer eliminates a TOP-LEVEL expression-carried projection RETURN type
//! against the op's own parameter types before the conformance + WI-401 escape
//! checks, so:
//!   * the identity body `= m` (type `Box`) conforms to `b.Sort` (= `Box`);
//!   * the avoidance gate sees the input-rooted concrete type (`b.Sort` ⟹ `Box`,
//!     same sort as the body ⟹ admitted), unlike a bare `-> Spec` whose abstract
//!     members would escape;
//!   * the returned value is admissible wherever the receiver's type — and the
//!     spec it provides — is expected.

use anthill_core::eval::Value;

fn expect_int(v: Value) -> i64 {
    v.as_int().unwrap_or_else(|| panic!("expected Int64, got {v:?}"))
}

// A plain (effect-free) carrier so the feature is exercised end-to-end without
// the stream effect-row grounding (WI-495). `Box` provides the `Holder` spec.
const SRC: &str = r#"
namespace wi491.covariant
  import anthill.prelude.Int64

  sort Holder
    sort T = ?
    operation get(h: Holder) -> Int64
  end

  sort Box
    import wi491.covariant.Holder
    entity box(v: Int64)
    provides Holder[T = Int64]
    operation get(b: Box) -> Int64 = match b case box(n) -> n
  end

  -- WI-491 headline: a covariant return rooted at the receiver. `b.Sort` is the
  -- whole type of `b` (= Box), input-rooted, so the avoidance gate admits `= b`.
  operation identity(b: Box) -> b.Sort = b

  operation mk() -> Box = box(7)

  -- The result has the receiver's OWN type (Box): a `box(..)` pattern match on
  -- `identity(b)` succeeds (the result is statically — and dynamically — a Box).
  operation roundtrip(b: Box) -> Int64 =
    match identity(b)
      case box(n) -> n

  -- The result is admissible where the receiver's PROVIDED SPEC is expected:
  -- `use_holder` wants a `Holder`; `identity(b)` is a `Box`, which provides Holder.
  -- `h.get()` dispatches Holder's op on the concrete Box value.
  operation use_holder(h: Holder) -> Int64 = h.get()
  operation via_spec(b: Box) -> Int64 = use_holder(identity(b))
end
"#;

/// The covariant identity returns a value of the receiver's own type, so a
/// member of that type (`Box.get`) applies to the result.
#[test]
fn covariant_return_yields_receiver_type() {
    let mut interp = crate::common::interp_for(SRC);
    let b = interp.call("wi491.covariant.mk", &[]).expect("build box");
    let got = interp
        .call("wi491.covariant.roundtrip", &[b])
        .unwrap_or_else(|e| panic!("call roundtrip: {e:?}"));
    assert_eq!(expect_int(got), 7);
}

/// The result is admissible wherever the receiver's PROVIDED SPEC (Holder) is
/// expected — provider admissibility flows through the covariant return.
#[test]
fn covariant_return_admissible_where_provided_spec_expected() {
    let mut interp = crate::common::interp_for(SRC);
    let b = interp.call("wi491.covariant.mk", &[]).expect("build box");
    let got = interp
        .call("wi491.covariant.via_spec", &[b])
        .unwrap_or_else(|e| panic!("call via_spec: {e:?}"));
    assert_eq!(expect_int(got), 7);
}

/// THE ticket's headline form against the real lazy carrier: `operation
/// iterator(m: MappedStream) -> m.Sort = m` TYPE-CHECKS at load (the def-site
/// elimination of `m.Sort` ⟹ MappedStream, so the identity body conforms and the
/// avoidance gate admits the input-rooted return). Pure load-clean assertion —
/// consuming a constructed lazy stream is the effect-row grounding of WI-495.
#[test]
fn mappedstream_covariant_iterator_typechecks() {
    let src = r#"
namespace wi491.headline
  import anthill.prelude.{MappedStream, Stream}
  operation iterator(m: MappedStream) -> m.Sort = m
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.is_empty(),
        "`iterator(m: MappedStream) -> m.Sort = m` must type-check (covariant \
         receiver-rooted return); got: {errs:?}",
    );
}

/// WI-491 surfaces a PRECISE error (not a vague conformance mismatch, and never a
/// silent accept) when the projection return names a member the receiver's type
/// does not have: `-> m.Nonexistent` reports "no member 'Nonexistent'" — the
/// elimination error itself, loud and early (project principle: no fallback).
#[test]
fn bogus_member_projection_return_reports_precise_error() {
    let src = r#"
namespace wi491.bogusmember
  import anthill.prelude.{MappedStream, Stream}
  operation bad(m: MappedStream) -> m.Nonexistent = m
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("Nonexistent") && e.contains("no member")),
        "a bogus projection-return member must report the precise elimination error \
         ('no member ...'), not a vague conformance mismatch; got: {errs:?}",
    );
}

/// WI-491 must NOT open an escape hole: a BARE abstract-spec return (`-> Stream`,
/// whose members T,E are left unbound) is still REJECTED by the WI-401 avoidance
/// gate — only the input-rooted `m.Sort` projection is admitted.
#[test]
fn bare_abstract_spec_return_still_rejected() {
    let src = r#"
namespace wi491.hole
  import anthill.prelude.{MappedStream, Stream}
  operation bad(m: MappedStream) -> Stream = m
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.iter().any(|e| e.contains("abstracting return") || e.contains("escape")),
        "a bare `-> Stream` return must stay rejected (abstract members escape); \
         got: {errs:?}",
    );
}

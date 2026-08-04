//! WI-979 — a `sort X … end` that REUSES an existing symbol must record its
//! CATEGORIES from the declaration, not from which arm of `scan_items_pass1`
//! happened to produce the symbol.
//!
//! The two declarations are identical in every fixture; only their ORDER differs.
//! That is the whole experiment.
//!
//! WHICH ROWS FAIL WHEN THE FIX IS BACKED OUT: every `ns-first` row below.
//! `sort`-first passes either way, BY DESIGN — it is the control, and it is what
//! makes the ns-first failures attributable to the reuse arm rather than to the
//! fixture.
//!
//! SCOPE, STATED SO IT IS NOT READ WIDER THAN IT IS. This ticket fixes the
//! CATEGORY. It does NOT make the reuse arm wire the sort's scope the way the
//! fresh arm does — two `is_new`-gated links remain, each pinned by a test here:
//! the enclosing link (`entity X` then `sort X`, left refused pending 059 R1) and
//! the variant-exposure link (WI-994, open, with a measured reason for not taking
//! the obvious fix). Nor does it reach a pass-1 reader that runs BEFORE the
//! `sort X` item: `is_sort_scope` is consulted during the same pass, so a reader
//! reached earlier still sees the pre-fix answer.

mod common;

use anthill_core::eval::Value;
use anthill_core::intern::SymbolKind;

/// `sort` first, then the secondary entry. The control.
const SORT_FIRST: &str = r#"
namespace wi979.sf
  import anthill.prelude.Int64
  sort Rec
    entity Rec(n: Int64)
  end
  namespace Rec
    operation twice(r: Rec) -> Int64 = r.n
  end
  operation drive() -> Int64 = Rec(n: 5).twice()
end
"#;

/// The secondary entry first. Same two declarations, swapped.
const NS_FIRST: &str = r#"
namespace wi979.nf
  import anthill.prelude.Int64
  namespace Rec
    operation twice(r: Rec) -> Int64 = r.n
  end
  sort Rec
    entity Rec(n: Int64)
  end
  operation drive() -> Int64 = Rec(n: 5).twice()
end
"#;

fn cases() -> [(&'static str, &'static str, &'static str); 2] {
    [
        ("sort-first (CONTROL)", SORT_FIRST, "wi979.sf"),
        ("ns-first", NS_FIRST, "wi979.nf"),
    ]
}

#[test]
fn both_orders_record_the_same_categories() {
    for (label, src, ns) in cases() {
        let kb = common::load_kb_with(src);
        let sym = kb
            .try_resolve_symbol(&format!("{ns}.Rec"))
            .unwrap_or_else(|| panic!("{label}: {ns}.Rec has no symbol"));
        assert!(
            kb.has_kind(sym, SymbolKind::Sort),
            "{label}: `sort Rec … end` was written, so Rec must carry Sort",
        );
        assert!(
            kb.has_kind(sym, SymbolKind::Entity),
            "{label}: the eponymous `entity Rec(…)` collapses onto the sort (§6.3 / \
             WI-926), so Rec must carry Entity",
        );
        assert!(
            kb.has_kind(sym, SymbolKind::Namespace),
            "{label}: `namespace Rec` was written too",
        );
    }
}

#[test]
fn neither_order_defines_a_phantom_nested_constructor() {
    // §6.3: the eponymous constructor IS the sort, one symbol. It only collapses
    // when the enclosing scope is known to be a sort — so losing the Sort category
    // leaves `Rec.Rec` standing as a separate nested symbol, and a receiver then
    // reports its sort as `<ns>.Rec.Rec` and dot dispatch misses.
    for (label, src, ns) in cases() {
        let kb = common::load_kb_with(src);
        assert!(
            kb.try_resolve_symbol(&format!("{ns}.Rec.Rec")).is_none(),
            "{label}: `{ns}.Rec.Rec` exists — the eponymous constructor did not collapse",
        );
    }
}

/// THE SAME DEFECT ONE GATE OVER, STILL OPEN — pinned in both directions so the
/// asymmetry is a stated invariant rather than a silence. Whether a sort's variants
/// are visible to its enclosing scope is ALSO gated on `is_new`, so `namespace
/// Colour … end` written before `sort Colour { entity Red }` leaves bare `Red`
/// unresolvable, while the same two declarations swapped resolve it.
///
/// WHY IT IS NOT FIXED HERE, measured. Un-gating it is the obvious sibling of the
/// `add_kind` fix, and it was tried and reverted: `is_new` is false for the whole
/// PRE-REGISTERED population too, so un-gating hands 7 bootstrap sorts an exposure
/// link they never had — driven, bare `guarded` under a wildcard import goes from
/// resolving uniquely to `LogicalQuery.guarded` to AMBIGUOUS against
/// `EffectExpression.guarded`. Nothing in the tree has a wildcard import, so the
/// suite stayed green through it; the green suite was not evidence. A correct fix
/// must tell declaration-reuse from bootstrap-reuse, which `is_new` cannot. WI-994.
///
/// A NON-eponymous sort is what exposes this at all: with `entity Rec` inside
/// `sort Rec` the bare name resolves as the sort itself, so the exposure link is
/// never consulted and the eponymous fixtures above cannot see it either way.
#[test]
fn variant_exposure_is_still_order_dependent_wi994() {
    const V_SORT_FIRST: &str = r#"
namespace wi979.vsf
  import anthill.prelude.Int64
  sort Colour
    entity Red(v: Int64)
  end
  namespace Colour
    operation twice(c: Colour) -> Int64 = 2
  end
  operation drive() -> Int64 = Red(v: 5).twice()
end
"#;
    const V_NS_FIRST: &str = r#"
namespace wi979.vnf
  import anthill.prelude.Int64
  namespace Colour
    operation twice(c: Colour) -> Int64 = 2
  end
  sort Colour
    entity Red(v: Int64)
  end
  operation drive() -> Int64 = Red(v: 5).twice()
end
"#;
    // sort-first WORKS — and passes with or without the `add_kind` fix, so it is
    // the control for the pinned row below rather than a measure of this ticket.
    let mut interp = common::interp_for(V_SORT_FIRST);
    assert!(
        matches!(interp.call("wi979.vsf.drive", &[]), Ok(Value::Int(2))),
        "sort-first: bare `Red(…)` must resolve through the variant-exposure link",
    );
    // ns-first is the OPEN defect. When WI-994 lands this call starts succeeding
    // and `expect_load_errors` fails — which is the point: the fix has to come
    // here and flip it, not land silently.
    common::expect_load_errors(
        common::try_load_kb_with(V_NS_FIRST),
        &["type mismatch in Red.apply: expected known operation or arrow-typed variable"],
    );
}

/// THE HALF DELIBERATELY NOT FIXED, pinned so the decision is visible and a silent
/// change is caught. `entity X(…)` then `sort X … end` also takes the reuse arm, and
/// there the skipped link is the ENCLOSING one — the sort body resolves nothing from
/// outside itself. It is left alone: proposal 059 R1 refuses two type declarations at
/// one address outright, so making this shape work would build a capability R1
/// removes. It fails LOUDLY today, which is the right behaviour to hold pending R1 —
/// un-gating the link would instead make it silently succeed.
///
/// THE FIXTURE CARRIES A VARIANT ON PURPOSE. Without one, `has_variant` is false and
/// this test cannot see the variant-exposure gate at all — it passed unchanged while
/// an earlier attempt at WI-994 un-gated that link and made bare `Inner` resolve out
/// of this very shape, half-wiring the scope (variants leaking out while the body
/// still could not see in). A pinning test blind to the change it pins is not a pin.
#[test]
fn entity_then_sort_body_still_fails_loudly_pending_059_r1() {
    common::expect_load_errors(
        common::try_load_kb_with(r#"
namespace wi979.es
  import anthill.prelude.Int64
  entity Rec(n: Int64)
  sort Rec
    entity Inner
    operation twice(r: Rec) -> Int64 = r.n
  end
end
"#),
        &[
            "unresolved name 'Int64' in scope 'twice'",
            "unresolved name 'Rec' in scope 'twice'",
            // …and the knock-on: with the param type unresolved, `r.n` has no
            // receiver sort to dispatch the field on.
            "type mismatch in Rec.n: expected operation declared on the receiver's sort",
        ],
    );
}

#[test]
fn both_orders_dispatch_the_secondary_entrys_member() {
    // The capability, DRIVEN: a member declared in the secondary entry, called on
    // a receiver built from the main entry's constructor. Asserting the VALUE, not
    // that the file loaded — a `twice` that resolved to nothing would fail here.
    for (label, src, _ns) in cases() {
        let mut interp = common::interp_for(src);
        let got = interp
            .call(&format!("{_ns}.drive"), &[])
            .unwrap_or_else(|e| panic!("{label}: drive() failed: {e:?}"));
        assert!(
            matches!(got, Value::Int(5)),
            "{label}: Rec(n: 5).twice() must dispatch to the secondary entry's \
             member and read the field, got {got:?}",
        );
    }
}

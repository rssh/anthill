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
//! CATEGORY. It did NOT make the reuse arm wire the sort's scope the way the fresh
//! arm does; of the two `is_new`-gated links it left behind, the variant-exposure
//! one has since been un-gated (WI-994, flipped below) and the ENCLOSING one is
//! still gated — `entity X` then `sort X`, refused outright by 059 R1 / WI-997,
//! and pinned here. Nor does it reach a pass-1 reader that runs BEFORE the
//! `sort X` item: `is_sort_scope` is consulted during the same pass, so a reader
//! reached earlier still sees the pre-fix answer.

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
        let kb = crate::common::load_kb_with(src);
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
        let kb = crate::common::load_kb_with(src);
        assert!(
            kb.try_resolve_symbol(&format!("{ns}.Rec.Rec")).is_none(),
            "{label}: `{ns}.Rec.Rec` exists — the eponymous constructor did not collapse",
        );
    }
}

/// THE SAME DEFECT ONE GATE OVER, NOW CLOSED (WI-994). Whether a sort's variants
/// are visible to its enclosing scope was ALSO gated on `is_new`, so `namespace
/// Colour … end` written before `sort Colour { entity Red }` left bare `Red`
/// unresolvable, while the same two declarations swapped resolved it. Both orders
/// now resolve it — 059's "main and secondary name roles, not order", and §8.6's
/// exposure read off the declaration.
///
/// The fix is a plain un-gate after all. This file used to record a reason not to
/// take it — `is_new` is false for the PRE-REGISTERED stdlib sorts too, so
/// un-gating "hands 7 bootstrap sorts an exposure link they never had". That
/// population is the same defect, not a second one, and `wi994_variant_exposure_test`
/// drives both it and the `guarded` row cited as the regression.
///
/// A NON-eponymous sort is what exposes this at all: with `entity Rec` inside
/// `sort Rec` the bare name resolves as the sort itself, so the exposure link is
/// never consulted and the eponymous fixtures above cannot see it either way.
#[test]
fn variant_exposure_is_order_independent_wi994() {
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
    // Same two rows as `cases()` above, over the non-eponymous fixtures: the
    // sort-first CONTROL passes either way, and ns-first is the row WI-994 fixed —
    // back the un-gate out and it fails at LOAD, `type mismatch in Red.apply: …
    // got unknown functor`.
    for (label, src, ns) in [
        ("sort-first (CONTROL)", V_SORT_FIRST, "wi979.vsf"),
        ("ns-first", V_NS_FIRST, "wi979.vnf"),
    ] {
        let mut interp = crate::common::interp_for(src);
        assert!(
            matches!(interp.call(&format!("{ns}.drive"), &[]), Ok(Value::Int(2))),
            "{label}: bare `Red(…)` must resolve through the variant-exposure link",
        );
    }
}

/// THE HALF DELIBERATELY NOT FIXED — and WI-997 is why it stays that way. `entity
/// X(…)` then `sort X … end` also takes the reuse arm, and there the skipped link is
/// the ENCLOSING one, so the sort body resolves nothing from outside itself. Supplying
/// that link would have built exactly the capability 059 R1 removes; R1 has now landed
/// (WI-997), and this shape is REFUSED as two declarations of one type.
///
/// SO THIS TEST NOW PINS BOTH ENDS AT ONCE: the R1 refusal names the pair, and the
/// three pre-existing errors below it are still present and unchanged — the missing
/// link was never repaired, which is what keeps the decision visible. If a later
/// change un-gates it, those three disappear and this fails.
///
/// THE FIXTURE CARRIES A VARIANT ON PURPOSE. Without one `has_variant` is false
/// and this test cannot see the exposure gate at all — the pre-WI-994 version had
/// none and passed unchanged through a change to it. With WI-994 landed, bare
/// `Inner` now DOES resolve out of this shape while the body still cannot see in;
/// that is not a half-fix left lying around, because R1 refuses the pair outright
/// and no program reaches a KB built from it.
#[test]
fn entity_then_sort_body_is_refused_by_059_r1_and_still_unwired() {
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(
            r#"
namespace wi979.es
  import anthill.prelude.Int64
  entity Rec(n: Int64)
  sort Rec
    entity Inner
    operation twice(r: Rec) -> Int64 = r.n
  end
end
"#,
        ),
        &[
            // WI-997 / 059 R1 — the pair itself, named with both keywords and lines.
            "type 'Rec' is declared more than once in scope 'wi979.es': \
             `entity` at 4:3, `sort` at 5:3",
            // …and the shape is STILL unwired, which R1 does not repair and must not.
            // WI-977: qualified, matching the R1 row above.
            "unresolved name 'Int64' in scope 'wi979.es.Rec.twice'",
            "unresolved name 'Rec' in scope 'wi979.es.Rec.twice'",
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
        let mut interp = crate::common::interp_for(src);
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

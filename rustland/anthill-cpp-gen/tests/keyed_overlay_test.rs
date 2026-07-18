//! WI-089(a): active-key priority for keyed `TypeMapping` overlays.
//!
//! A type mapping is selected by an ordered active-key list, most-specific
//! first: `[binding?, profile?, none]`. A binding overlay (in scope only at a
//! carrier-dispatch boundary) shadows a profile overlay, which shadows the
//! language base. This is the one place "binding shadows profile shadows base"
//! is decided; declared-signature lowering and the marshalling boundary both
//! route through it (`resolve_type_mapping`), differing only by which keys are
//! active.

use super::common;

use anthill_cpp_gen::{cpp_host_type, emit_namespace_header_with_profile};
use common::load_kb_with;

#[test]
fn priority_ladder_binding_shadows_profile_shadows_base() {
    // One synthetic anthill type with all three overlays asserted as ordinary
    // facts (anthill_type is a plain String — no sort declaration needed). The
    // resolver picks by the active-key list; this exercises every rung of the
    // ladder, including the "base wins when no overlay is active" case that is
    // the declared-signature (no-binding) position.
    let source = r#"
        namespace test.ladder
          import anthill.realization.TypeMapping
          import anthill.prelude.Option.{some, none}

          fact TypeMapping(lang: some("cpp"), key: none,
                           anthill_type: "Widget", host_type: "Base",
                           lift: none, lower: none)
          fact TypeMapping(lang: some("cpp"), key: some("cpp20-stl"),
                           anthill_type: "Widget", host_type: "Profile",
                           lift: none, lower: none)
          fact TypeMapping(lang: some("cpp"), key: some("gadget"),
                           anthill_type: "Widget", host_type: "Bound",
                           lift: none, lower: none)
        end
    "#;
    let mut kb = load_kb_with(source);

    // No profile, no binding (declared-signature position) → language base.
    assert_eq!(cpp_host_type(&mut kb, "Widget", None, None).as_deref(), Some("Base"));

    // Profile active, no binding → the profile overlay shadows the base.
    assert_eq!(
        cpp_host_type(&mut kb, "Widget", Some("cpp20-stl"), None).as_deref(),
        Some("Profile")
    );

    // Binding active (carrier-dispatch boundary) → the binding overlay shadows
    // both the profile overlay and the base.
    assert_eq!(
        cpp_host_type(&mut kb, "Widget", Some("cpp20-stl"), Some("gadget")).as_deref(),
        Some("Bound")
    );

    // Binding active with no profile → binding still shadows the base.
    assert_eq!(
        cpp_host_type(&mut kb, "Widget", None, Some("gadget")).as_deref(),
        Some("Bound")
    );

    // A profile with no matching overlay falls through to the base — an
    // unrelated profile must not accidentally pick another profile's entry.
    assert_eq!(
        cpp_host_type(&mut kb, "Widget", Some("cpp17-stl"), None).as_deref(),
        Some("Base")
    );

    // A binding with no matching overlay falls through (no profile here) to the
    // base — the base sentinel is always last in the active-key list.
    assert_eq!(
        cpp_host_type(&mut kb, "Widget", None, Some("no-such-binding")).as_deref(),
        Some("Base")
    );
}

#[test]
fn profile_threads_into_declared_signature_lowering() {
    // A profile-keyed overlay on a real primitive: the cpp base maps Float ->
    // double; a cpp20-stl overlay remaps it to float. An entity field of type
    // Float must lower to the overlay under the active profile and to the base
    // without it — proving the CLI-facing `emit_*_with_profile` threading
    // actually reaches type lowering.
    let source = r#"
        namespace test.pf
          import anthill.prelude.Float
          import anthill.realization.TypeMapping
          import anthill.prelude.Option.{some, none}

          entity Holder(x: Float)

          fact TypeMapping(lang: some("cpp"), key: some("cpp20-stl"),
                           anthill_type: "Float", host_type: "float",
                           lift: none, lower: none)
        end
    "#;
    let mut kb = load_kb_with(source);

    let base = emit_namespace_header_with_profile(&mut kb, "test.pf", None)
        .expect("emit test.pf (base)");
    assert!(
        base.contains("double x;") && !base.contains("float x;"),
        "without a profile, Holder.x should lower to the base double:\n{base}"
    );

    let overlay = emit_namespace_header_with_profile(&mut kb, "test.pf", Some("cpp20-stl".to_string()))
        .expect("emit test.pf (cpp20-stl)");
    assert!(
        overlay.contains("float x;"),
        "under cpp20-stl, Holder.x should lower to the profile overlay float:\n{overlay}"
    );
}

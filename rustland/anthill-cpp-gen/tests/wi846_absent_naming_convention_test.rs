//! WI-846: a ZERO-result cpp `NamingConvention` read must NOT silently fall
//! through to identity casing.
//!
//! `cpp_method_name` is reached only at a CARRIER-DISPATCH boundary (an
//! operation on a sort bound to a foreign host type), where the emitted
//! `self->method(...)` call must spell the HOST method name. When no cpp
//! `NamingConvention` resolves, WI-833 returned identity casing with NO
//! diagnostic, so a project that binds a carrier but never loads a cpp naming
//! profile emitted non-compilable C++ silently.
//!
//! MEASUREMENT (WI-846 acceptance 1) — what cpp-gen emitted BEFORE this fix,
//! for `get_reading(self: Sensor) -> Unit` bound to `::vendor::Sensor *` with
//! zero cpp `NamingConvention` loaded:
//!
//! ```text
//! Ok("struct Sensor {
//!     static void get_reading(::vendor::Sensor * self) {
//!         self->get_reading();          // <- IDENTITY, silently: no diagnostic
//!     }
//! };")
//! ```
//!
//! `self->get_reading()` compiles against a vendor header only if it declares
//! `get_reading()`; a `getReading()` header gets a silent build break. Per the
//! repo rule ("prefer a loud error over a silent skip"), and because this branch
//! is reachable ONLY in a misconfigured/partial-load state (the bundled stdlib
//! always ships one cpp `NamingConvention`, and a KB with no realization profile
//! at all would already have failed lowering its first primitive type), the
//! decided policy is a LOUD `CppCodegenError` naming the absent profile — the
//! zero-half twin of the `>1` ambiguity error `cpp_method_name` already raises.
//!
//! The zero branch is UNREACHABLE with the default harness, which always loads
//! `realization/cpp_std.anthill`. This suite uses
//! `common::load_kb_without_cpp_profile` — the harness's "no cpp realization
//! profile" load path (stdlib minus `cpp_std`) — to reach it.

use super::common;

use anthill_cpp_gen::emit_traits_struct;
use common::load_kb_without_cpp_profile;

/// Emit `test.wi846.naming.Sensor`'s traits struct with a carrier binding but
/// (crucially) NO cpp `NamingConvention` loaded. `get_reading(self: Sensor)`
/// reaches carrier-dispatch body synthesis, which reads the cpp
/// `NamingConvention` via `cpp_method_name`. The project supplies its OWN
/// `Unit -> void` `TypeMapping` (so the signature lowers) but no naming
/// convention — the exact misconfiguration WI-846 is about.
fn emit_sensor_without_naming_profile() -> Result<String, String> {
    let source = r#"
        namespace test.wi846.naming
          import anthill.prelude.{Unit, String, Option, Bool}
          import anthill.realization.{Implementation, CarrierBinding, NamingConvention, TypeMapping}
          import anthill.prelude.Option.{some, none}

          sort Sensor
            operation get_reading(self: Sensor) -> Unit
          end

          fact Implementation(
            target:        "test.wi846.naming.Sensor",
            artifact:      "sensor.hpp",
            language:      "cpp",
            profile:       none,
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Sensor", host_type: "::vendor::Sensor *")],
            namespace_map: [],
            binding:       none)

          -- The project has its OWN type mappings (so the signature lowers) but
          -- ships NO cpp NamingConvention. cpp_std (which normally supplies the
          -- one snake_case -> camelCase convention) is NOT loaded here.
          fact TypeMapping(lang: some("cpp"), key: none, anthill_type: "Unit",
                           host_type: "void", lift: none, lower: none)
        end
    "#;
    let mut kb = load_kb_without_cpp_profile(source);
    emit_traits_struct(&mut kb, "test.wi846.naming.Sensor").map_err(|e| e.message)
}

/// The decided policy: a zero-result cpp `NamingConvention` at a carrier-dispatch
/// boundary is a LOUD `CppCodegenError`, never silent identity casing.
#[test]
fn absent_naming_convention_is_a_loud_error_not_silent_identity() {
    let err = emit_sensor_without_naming_profile()
        .expect_err("zero cpp NamingConvention at a carrier boundary must fail loudly");
    // Names WHAT resolved to nothing and WHERE it bit...
    assert!(err.contains("NamingConvention"), "names the absent convention: {err}");
    assert!(
        err.contains("get_reading"),
        "names the carrier-dispatch method it bit on: {err}"
    );
    // ...and names the absent profile so the fix is obvious. (The silent
    // identity is guarded by `expect_err` above — a regression returns
    // `Ok("...self->get_reading();...")`, on which `expect_err` panics; the
    // error is raised before any dispatch string is built, so asserting the
    // message lacks it would be vacuous.)
    assert!(
        err.contains("anthill.realization.cpp_std"),
        "names the absent realization profile: {err}"
    );
}

/// The escape hatch the error message advertises actually works: a project that
/// WANTS identity casing declares it (`source_case == method_case`) rather than
/// relying on the removed silent fallback. With such a convention present (and
/// still no cpp_std), emission succeeds and `get_reading` stays `get_reading` —
/// no error, identity by an EXPLICIT opt-in. Closes the loop on the remediation
/// the loud error names.
#[test]
fn declared_identity_casing_emits_identity_without_error() {
    let source = r#"
        namespace test.wi846.identity
          import anthill.prelude.{Unit, String, Option, Bool}
          import anthill.realization.{Implementation, CarrierBinding, NamingConvention, TypeMapping}
          import anthill.prelude.Option.{some, none}

          sort Sensor
            operation get_reading(self: Sensor) -> Unit
          end

          fact Implementation(
            target:        "test.wi846.identity.Sensor",
            artifact:      "sensor.hpp",
            language:      "cpp",
            profile:       none,
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Sensor", host_type: "::vendor::Sensor *")],
            namespace_map: [],
            binding:       none)

          fact TypeMapping(lang: some("cpp"), key: none, anthill_type: "Unit",
                           host_type: "void", lift: none, lower: none)
          -- Identity casing, declared intentionally (the error's advised remedy).
          fact NamingConvention(language: "cpp", method_case: "snake_case", source_case: "snake_case")
        end
    "#;
    let mut kb = load_kb_without_cpp_profile(source);
    let traits = emit_traits_struct(&mut kb, "test.wi846.identity.Sensor")
        .expect("a declared identity convention emits, never errors");
    assert!(
        traits.contains("self->get_reading()"),
        "declared snake_case -> snake_case keeps the method name identity:\n{traits}"
    );
}

/// The fix does NOT over-fire: with the stdlib cpp `NamingConvention` present
/// (the default harness, which loads `cpp_std`), the SAME carrier-dispatch
/// emission succeeds and applies the convention — `get_reading` -> `getReading`
/// under snake_case -> camelCase. Guards the loud error to the genuinely-absent
/// case, so a normal build is unaffected.
#[test]
fn naming_convention_present_still_emits_the_dispatch() {
    let source = r#"
        namespace test.wi846.present
          import anthill.prelude.{Unit, String, Option, Bool}
          import anthill.realization.{Implementation, CarrierBinding, NamingConvention}
          import anthill.prelude.Option.{some, none}

          sort Sensor
            operation get_reading(self: Sensor) -> Unit
          end

          fact Implementation(
            target:        "test.wi846.present.Sensor",
            artifact:      "sensor.hpp",
            language:      "cpp",
            profile:       none,
            description:   none,
            carrier:       [CarrierBinding(sort_name: "Sensor", host_type: "::vendor::Sensor *")],
            namespace_map: [],
            binding:       none)
        end
    "#;
    let mut kb = common::load_kb_with(source);
    let traits = emit_traits_struct(&mut kb, "test.wi846.present.Sensor")
        .expect("with the stdlib cpp NamingConvention present, emission succeeds");
    assert!(
        traits.contains("self->getReading()"),
        "snake_case -> camelCase applied at the boundary:\n{traits}"
    );
}

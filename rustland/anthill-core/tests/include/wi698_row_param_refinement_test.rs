//! WI-698 / proposal 054 §"Mechanism": the Faking story's static half rides
//! DELIVERED machinery — a carrier-tied effect-row parameter (`effects EM = ?`,
//! the WI-320 EffectsRuntime anchor), instantiated per carrier in `provides`
//! and substituted into the spec op's row at concrete call sites
//! (`substituted_op_effects`). These tests pin that substrate from the
//! 2026-07-12 design-session smoke, BEFORE `External` itself exists:
//! `Outside` below is a stand-in effect declared the Clock way.
//!
//! Pinned invariants:
//!   1. a consumer holding the "fake" carrier (EM = {}) typechecks at the
//!      INSTANTIATED row — `effects {}` loads (refinement-by-instantiation);
//!   2. the "real" carrier's row ({Outside}) reaches the same consumer shape
//!      and is REJECTED loudly — instantiation is enforced, not dropped;
//!   3. param-to-param threading (a wrapper's own row param bound in its
//!      `provides` — the `CoordState[M]` shape of WI-437 §8.3) refines and
//!      enforces identically;
//!   4. dot dispatch on an ABSTRACT carrier fails loudly — no silent `{}`;
//!   5. the stdlib precedent itself: `Iterable.isEmpty` (row = spec param E)
//!      over `List` (E = {}) under a consumer declaring `effects {}`;
//!   6. the pre-WI-700 GAP, pinned to flip — TWO independent probes:
//!      (a) `shield[EffP = {Outside}](poke)` loads although the callback row
//!          declares `-Outside` (lacks unenforced at explicit instantiation);
//!      (b) `shield[EffP = {}](poke3)` loads although `poke3` declares
//!          `{Outside}` (callback-row conformance unchecked entirely).
//!      Declared rows are what the row checker consumes — `poke`/`poke3`
//!      have pure bodies and OVER-declare deliberately. WI-700 wires the
//!      checks; as each lands, flip the corresponding `*_today` test from
//!      `expect_load` to `expect_reject`.
//!
//! One row param (`EM`) stands in for 054 §Mechanism's read/write pair
//! (`ER`/`EW`, the WI-441 decoupled split): multiple params ride the same
//! type-arg substitution (MappedStream's `ES`/`EF` ships it today).

/// The 054 §Faking mini-model: user effect + spec with row param + the two
/// carriers. NOTE `import anthill.prelude.EffectsRuntime`: the `effects EM = ?`
/// desugar emits `requires EffectsRuntime[Effects = EM]`, and without the
/// import the provider-requires exemption misses (symbol identity) — see the
/// WI-698 memory/proposal by-catch.
const MECH_SRC: &str = r#"
namespace smoke.b_mech
  import anthill.prelude.{Int64, Effect, EffectsRuntime}

  sort Outside
  end
  fact Effect[T = Outside]

  sort Mir
    sort C = ?
    effects EM = ?
    operation ping(m: C) -> Int64 effects EM
  end

  sort Gh
    entity MkGh
    provides Mir[C = Gh, EM = {Outside}]
    operation ping(m: Gh) -> Int64 effects {Outside} = 41
  end

  sort Fake
    entity MkFake
    provides Mir[C = Fake, EM = {}]
    operation ping(m: Fake) -> Int64 effects {} = 42
  end

  operation t_fake(f: Fake) -> Int64
    effects {}
  = f.ping()

  operation t_gh_ok(g: Gh) -> Int64
    effects {Outside}
  = g.ping()
end
"#;

/// Negative twin: the real carrier under a pure consumer row must be rejected.
const NEG_SRC: &str = r#"
namespace smoke.b_neg
  import anthill.prelude.{Int64}
  import smoke.b_mech.{Gh}

  operation t_gh_wrong(g: Gh) -> Int64
    effects {}
  = g.ping()
end
"#;

/// Param-to-param threading: Wrap2's OWN row param bound into its `provides`
/// (the MappedStream `provides Stream[T = T, E = {ES, EF}]` idiom, C-style).
const WRAP_SRC: &str = r#"
namespace smoke.c_wrap
  import anthill.prelude.{Int64, EffectsRuntime}
  import smoke.b_mech.{Mir}

  sort Wrap2
    effects EW = ?
    entity mkWrap2
    provides Mir[C = Wrap2[EW], EM = EW]
    operation ping(m: Wrap2) -> Int64 effects EW = 7
  end

  operation t_wrap_pure(w: Wrap2[EW = {}]) -> Int64
    effects {}
  = w.ping()
end
"#;

const WRAP_NEG_SRC: &str = r#"
namespace smoke.c_wrap_neg
  import anthill.prelude.{Int64}
  import smoke.b_mech.{Outside}
  import smoke.c_wrap.{Wrap2}

  operation t_wrap_wrong(w: Wrap2[EW = {Outside}]) -> Int64
    effects {}
  = w.ping()
end
"#;

/// Abstract-carrier probe: dispatch on a bare type param must not silently
/// grant a refined row (today it fails as unresolved dot dispatch — loud).
/// `Mir` is imported DELIBERATELY: the spec is in scope, so the pinned
/// failure is receiver-side (abstract `M`), not name resolution.
const GENERIC_SRC: &str = r#"
namespace smoke.d_gen
  import anthill.prelude.{Int64}
  import smoke.b_mech.{Mir}

  operation t_gen[M](m: M) -> Int64
    effects {}
  = m.ping()
end
"#;

/// The stdlib precedent: Iterable's op row is the spec's E param; List
/// instantiates E = {}; a pure consumer row must typecheck.
const STDLIB_PRECEDENT_SRC: &str = r#"
namespace smoke.a_inst
  import anthill.prelude.{List, Bool, Int64}

  operation probe(xs: List[T = Int64]) -> Bool
    effects {}
  = xs.isEmpty()
end
"#;

/// Gap probe (a): `shield` demands `-Outside` on its callback, yet an
/// explicitly-instantiated `EffP = {Outside}` LOADS — the lacks-constraint
/// is unenforced at this call shape today. WI-700 flips this.
const LACKS_SRC: &str = r#"
namespace smoke.e_lacks
  import anthill.prelude.{Int64}
  import smoke.b_mech.{Outside}

  operation shield[EffP](f: () -> Int64 @ {EffP, -Outside}) -> Int64
    effects {EffP}
  = f()

  operation t_shield_ok() -> Int64
    effects {}
  = shield(lambda () -> 5)
end
"#;

const LACKS_GAP_SRC: &str = r#"
namespace smoke.e2_lacks_named
  import anthill.prelude.{Int64}
  import smoke.b_mech.{Outside}
  import smoke.e_lacks.{shield}

  operation poke() -> Int64
    effects {Outside}
  = 41

  operation t_shield_named() -> Int64
    effects {Outside}
  = shield[EffP = {Outside}](poke)
end
"#;

/// Gap probe (b): even a plain row MISMATCH loads — `poke3` declares
/// `{Outside}` where the explicit instantiation says `EffP = {}`. Callback-row
/// conformance at this shape is unchecked entirely; unlike probe (a) there is
/// no self-contradictory `{Outside, -Outside}` row here, so when WI-698 (c)
/// lands, the reject must come from actual-vs-declared conformance itself.
const LACKS_GAP2_SRC: &str = r#"
namespace smoke.e3_row_mismatch
  import anthill.prelude.{Int64}
  import smoke.b_mech.{Outside}
  import smoke.e_lacks.{shield}

  operation poke3() -> Int64
    effects {Outside}
  = 41

  operation t_row_mismatch() -> Int64
    effects {}
  = shield[EffP = {}](poke3)
end
"#;

fn expect_load(sources: &[&str], what: &str) {
    crate::common::try_load_kb_with_files(sources)
        .unwrap_or_else(|errs| panic!("{what} must load; got: {errs:?}"));
}

/// All `needles` must co-occur in ONE error string — tying the assertion to
/// the offending op AND the mechanism, so an unrelated diagnostic that merely
/// mentions a token (every source names `Outside`/`ping` somewhere) cannot
/// satisfy it.
fn expect_reject(sources: &[&str], needles: &[&str], what: &str) {
    match crate::common::try_load_kb_with_files(sources) {
        Ok(_) => panic!("{what} must be rejected (expected an error mentioning {needles:?})"),
        Err(errs) => assert!(
            errs.iter().any(|e| needles.iter().all(|n| e.contains(n))),
            "{what}: expected one error mentioning all of {needles:?}, got: {errs:?}",
        ),
    }
}

#[test]
fn row_param_instantiation_refines_at_concrete_call_site() {
    expect_load(&[MECH_SRC], "fake at EM = {} under a consumer row {}");
}

#[test]
fn row_param_instantiation_is_enforced_not_dropped() {
    expect_reject(
        &[MECH_SRC, NEG_SRC],
        &["t_gh_wrong", "Outside"],
        "the real carrier's {Outside} under a consumer row {}",
    );
}

#[test]
fn row_param_threads_param_to_param() {
    expect_load(&[MECH_SRC, WRAP_SRC], "Wrap2[EW = {}] threading (CoordState shape)");
}

#[test]
fn threaded_row_param_is_enforced() {
    expect_reject(
        &[MECH_SRC, WRAP_SRC, WRAP_NEG_SRC],
        &["t_wrap_wrong", "Outside"],
        "Wrap2[EW = {Outside}] under a consumer row {}",
    );
}

#[test]
fn abstract_carrier_leaks_no_refined_row() {
    expect_reject(
        &[MECH_SRC, GENERIC_SRC],
        &["ping", "no such member"],
        "dot dispatch on an abstract carrier type param",
    );
}

#[test]
fn stdlib_iterable_list_instantiation_precedent() {
    expect_load(&[STDLIB_PRECEDENT_SRC], "Iterable.isEmpty over List (E = {})");
}

/// PINS GAP (a) — flip to `expect_reject` when WI-700 wires the lacks
/// check at explicit instantiation sites.
#[test]
fn lacks_unenforced_at_explicit_instantiation_today() {
    expect_load(
        &[MECH_SRC, LACKS_SRC, LACKS_GAP_SRC],
        "pre-WI-698 status quo (a): EffP = {Outside} against a declared -Outside",
    );
}

/// PINS GAP (b) — flip to `expect_reject` when WI-700 wires callback-row
/// conformance at explicit instantiation sites.
#[test]
fn row_conformance_unchecked_at_explicit_instantiation_today() {
    expect_load(
        &[MECH_SRC, LACKS_SRC, LACKS_GAP2_SRC],
        "pre-WI-698 status quo (b): {Outside}-rowed op where EffP = {}",
    );
}

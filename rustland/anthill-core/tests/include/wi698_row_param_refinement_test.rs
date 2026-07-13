//! WI-698 / proposal 054 §"Mechanism": the Faking story's static half rides
//! DELIVERED machinery — a carrier-tied effect-row parameter (`effects EM = ?`,
//! the WI-320 EffectsRuntime anchor), instantiated per carrier in `provides`
//! and substituted into the spec op's row at concrete call sites
//! (`substituted_op_effects`). These tests pin that substrate.
//!
//! WI-699 retargets the substrate probes from the design-session stand-in
//! effect `Outside` onto the REAL `anthill.prelude.External` (proposal 054,
//! declared the Clock way in `stdlib/anthill/prelude/external.anthill`): the
//! retargeted carrier probes (invariants 1–3, 6) now bind `External`, while
//! invariants 4–5 are effect-agnostic (abstract-dispatch failure; the stdlib
//! `List` precedent). The two GAP pins (invariant 7) DELIBERATELY keep the
//! generic `Outside` stand-in — the hole they pin is NOT External-specific (it
//! exists for Modify / Error / Clock alike), and keeping them off `External`
//! isolates them from External's extra gates (the Branch × External
//! co-occurrence check, WI-701). WI-700 DELIVERED closed both (they were
//! `*_today` `expect_load` pins, now `expect_reject`).
//!
//! Pinned invariants:
//!   1. a consumer holding the "fake" carrier (EM = {}) typechecks at the
//!      INSTANTIATED row — `effects {}` loads (refinement-by-instantiation);
//!   2. the "real" carrier's row ({External}) reaches the same consumer shape
//!      and is REJECTED loudly — instantiation is enforced, not dropped;
//!   3. param-to-param threading (a wrapper's own row param bound in its
//!      `provides` — the `CoordState[M]` shape of WI-437 §8.3) refines and
//!      enforces identically;
//!   4. dot dispatch on an ABSTRACT carrier fails loudly — no silent `{}`;
//!   5. the stdlib precedent itself: `Iterable.isEmpty` (row = spec param E)
//!      over `List` (E = {}) under a consumer declaring `effects {}`;
//!   6. the 054 §Mechanism READ/WRITE SPLIT: a spec `Mir2` with TWO decoupled
//!      row params (`ER`/`EW`, the WI-441 pair shipped as MappedStream
//!      `ES`/`EF`) threads and refines INDEPENDENTLY. The GENUINE pin is the
//!      param-to-param `Wrap2RW` (WRAP_SRC's idiom — typer-enforced both ways —
//!      extended to two params): it threads its own `WR`/`WW` into
//!      `Mir2[ER = WR, EW = WW]`, and a consumer instantiating
//!      `Wrap2RW[WR = {External}, WW = {Modify[Reg]}]` refines ER and EW to
//!      DIFFERENT rows at the call site, each declared tightly — so a swap or a
//!      dropped param fails to load (the `*_wrong` negatives). `StoreRW` pins
//!      the UNION `{ER, EW}` at a NON-empty instantiation (a dropped component
//!      is caught by `store_union_drops`). `FakeRW`/`GhRW` only ILLUSTRATE the
//!      §Faking concrete shape (read pure vs tracked write; real both-External):
//!      their `provides Mir2` effect-binding is fail-open today
//!      (`check_override_refinement` defers denoted/parametric rows), so it is
//!      `Wrap2RW`, not they, that pins the mechanism. Expected FREE — the same
//!      type-arg substitution carries a second row param with no new typer work;
//!   7. WI-700 DELIVERED — effect-row enforcement at an EXPLICIT instantiation
//!      site, TWO independent probes over the generic `Outside` stand-in:
//!      (a) `shield[EffP = {Outside}](poke)` is REJECTED: the instantiation makes
//!          the callback row `{Outside, -Outside}` (present AND absent `Outside`),
//!          violating its own `-Outside` — the self-contradiction reject (hoisted by
//!          WI-705 to the signature-altitude `check_signature_self_contradiction`,
//!          which reads the DECLARED row RAW so the clash is not swallowed as a `None`);
//!      (b) `shield[EffP = {}](poke3)` is REJECTED: the closed callback row
//!          `{-Outside}` forbids the `{Outside}` that `poke3` declares
//!          (actual-vs-declared conformance, no self-contradiction).
//!      Declared rows are what the row checker consumes — `poke`/`poke3` have pure
//!      bodies and OVER-declare deliberately. Both probes are NULLARY ops passed by
//!      name: WI-700 eta-lifts a nullary op ref in a callback slot to
//!      `() -> ret @ row` (pre-WI-700 it collapsed to its return type, dropping the
//!      row and bypassing the check).

/// The 054 §Faking mini-model over the REAL `External`: spec with a row param +
/// the two carriers. NOTE: no `import anthill.prelude.EffectsRuntime` is needed —
/// the `effects EM = ?` desugar emits its `requires` anchor by CANONICAL name
/// (`anthill.prelude.EffectsRuntime`), so it resolves import-independent (WI-703).
/// Before WI-703 this source had to import the anchor as a workaround, else the
/// bare `EffectsRuntime` landed unresolved and the provider-requires exemption
/// (keyed on the canonical symbol) missed, misreporting it as a missing provision.
const MECH_SRC: &str = r#"
namespace smoke.b_mech
  import anthill.prelude.{Int64, External}

  sort Mir
    sort C = ?
    effects EM = ?
    operation ping(m: C) -> Int64 effects EM
  end

  sort Gh
    entity MkGh
    provides Mir[C = Gh, EM = {External}]
    operation ping(m: Gh) -> Int64 effects {External} = 41
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
    effects {External}
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
  import anthill.prelude.{Int64}
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
  import anthill.prelude.{Int64, External}
  import smoke.c_wrap.{Wrap2}

  operation t_wrap_wrong(w: Wrap2[EW = {External}]) -> Int64
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

/// 054 §Mechanism READ/WRITE SPLIT: a spec `Mir2` with TWO decoupled row params
/// (`ER`/`EW`), the WI-441 pair shipped as MappedStream `ES`/`EF`.
///
/// The GENUINE two-param pin is `Wrap2RW` — WRAP_SRC's param-to-param idiom
/// (which the typer enforces both ways) extended to TWO params: it threads its
/// own `WR`/`WW` into `Mir2[ER = WR, EW = WW]`, so a consumer instantiating
/// `Wrap2RW[WR = {External}, WW = {Modify[Reg]}]` refines ER and EW to DIFFERENT
/// rows through call-site type-arg substitution into `peek`/`stir`. Because the
/// two rows are DISTINCT and each consumer declares its row TIGHTLY, a swap or a
/// dropped param under-declares and fails to load (pinned negatively by
/// WRAP2RW_NEG_SRC). `StoreRW` pins the UNION `{ER, EW}` at a NON-empty
/// instantiation (a dropped component is caught by STORE_UNION_NEG_SRC).
///
/// `FakeRW`/`GhRW` only ILLUSTRATE the §Faking concrete shape (read pure vs
/// tracked write; real both-External) and are checked at their CONCRETE ops by
/// `obs_fake_*`/`obs_gh_read`. NOTE: their `provides Mir2[...]` effect-binding is
/// NOT enforced today — `check_override_refinement` defers denoted/parametric
/// effect rows (fail-open), so those bindings could be swapped without any test
/// noticing; `Wrap2RW` is what actually pins the mechanism. Expected FREE: the
/// same type-arg substitution carries a second row param with no new typer work.
const RW_SRC: &str = r#"
namespace smoke.f_rw
  import anthill.prelude.{Int64, Unit, Modify, Modifiable, External}
  import smoke.b_mech.{Mir}

  sort Reg
    entity mkReg
  end
  fact Modifiable[T = Reg]

  sort Mir2
    sort C = ?
    effects ER = ?
    effects EW = ?
    operation peek(m: C) -> Int64 effects ER
    operation stir(m: C, x: Int64) -> Unit effects EW
  end

  sort Wrap2RW
    effects WR = ?
    effects WW = ?
    entity mkWrap2RW
    provides Mir2[C = Wrap2RW[WR, WW], ER = WR, EW = WW]
    operation peek(m: Wrap2RW) -> Int64 effects WR = 0
    operation stir(m: Wrap2RW, x: Int64) -> Unit effects WW = ()
  end

  sort GhRW
    entity mkGhRW
    provides Mir2[C = GhRW, ER = {External}, EW = {External}]
    operation peek(m: GhRW) -> Int64 effects {External} = 1
    operation stir(m: GhRW, x: Int64) -> Unit effects {External} = ()
  end

  sort FakeRW
    entity mkFakeRW
    provides Mir2[C = FakeRW, ER = {}, EW = {Modify[Reg]}]
    operation peek(m: FakeRW) -> Int64 effects {} = 2
    operation stir(m: FakeRW, x: Int64) -> Unit effects {Modify[Reg]} = ()
  end

  sort StoreRW
    effects ER = ?
    effects EW = ?
    entity mkStoreRW
    provides Mir[C = StoreRW[ER, EW], EM = {ER, EW}]
    operation ping(m: StoreRW) -> Int64 effects {ER, EW} = 0
  end

  -- GENUINE two-param substitution: ER and EW refined to DIFFERENT non-empty
  -- rows at the call site, each declared TIGHTLY — a swap/conflation of the two
  -- params under-declares one of these and fails to load.
  operation wrap_read_ext(w: Wrap2RW[WR = {External}, WW = {Modify[Reg]}]) -> Int64
    effects {External}
  = w.peek()

  operation wrap_write_mod(w: Wrap2RW[WR = {External}, WW = {Modify[Reg]}]) -> Unit
    effects {Modify[Reg]}
  = w.stir(0)

  -- Union threads BOTH components at a NON-empty instantiation.
  operation store_union(s: StoreRW[ER = {External}, EW = {Modify[Reg]}]) -> Int64
    effects {External, Modify[Reg]}
  = s.ping()

  -- Concrete-carrier consumers (§Faking shape): read pure / write tracked / real
  -- read External. These check the CONCRETE ops, not the Mir2 provides binding.
  operation obs_fake_read(f: FakeRW) -> Int64
    effects {}
  = f.peek()

  operation obs_fake_write(f: FakeRW) -> Unit
    effects {Modify[Reg]}
  = f.stir(0)

  operation obs_gh_read(g: GhRW) -> Int64
    effects {External}
  = g.peek()
end
"#;

/// Negative twin for the concrete write: the fake's WRITE refines to
/// {Modify[Reg]}, so a consumer declaring `{}` for `f.stir(...)` must be rejected
/// — the tracked write escapes a pure row.
const RW_NEG_SRC: &str = r#"
namespace smoke.f_rw_neg
  import anthill.prelude.{Int64, Unit}
  import smoke.f_rw.{FakeRW}

  operation obs_fake_write_wrong(f: FakeRW) -> Unit
    effects {}
  = f.stir(0)
end
"#;

/// Negative twin for the GENUINE two-param substitution: `w.peek()` refines to
/// WR = {External} at the call site, so declaring `{}` must be rejected — the
/// External read escapes a pure row. This pins that the read row substitutes and
/// is ENFORCED (not dropped to {}, and not conflated with the write row WW).
const WRAP2RW_NEG_SRC: &str = r#"
namespace smoke.f_rw_wrap_neg
  import anthill.prelude.{Int64, Modify, External}
  import smoke.f_rw.{Wrap2RW, Reg}

  operation wrap_read_wrong(w: Wrap2RW[WR = {External}, WW = {Modify[Reg]}]) -> Int64
    effects {}
  = w.peek()
end
"#;

/// Negative twin for the store UNION: `s.ping()` threads `{ER, EW}`, so at
/// ER = {External}, EW = {Modify[Reg]} a consumer declaring only `{External}`
/// must be rejected — the write component escapes. Pins that the union carries
/// BOTH components (not just one), the non-degenerate half of the union claim.
const STORE_UNION_NEG_SRC: &str = r#"
namespace smoke.f_rw_store_neg
  import anthill.prelude.{Int64, Modify, External}
  import smoke.f_rw.{StoreRW, Reg}

  operation store_union_drops(s: StoreRW[ER = {External}, EW = {Modify[Reg]}]) -> Int64
    effects {External}
  = s.ping()
end
"#;

/// Gap probe (a): `shield` demands `-Outside` on its callback, yet an
/// explicitly-instantiated `EffP = {Outside}` LOADS — the lacks-constraint
/// is unenforced at this call shape today. WI-700 flips this. Kept on the
/// generic `Outside` stand-in (declared here): the hole is not
/// External-specific, and `Outside` carries none of External's extra gates.
const LACKS_SRC: &str = r#"
namespace smoke.e_lacks
  import anthill.prelude.{Int64, Effect}

  sort Outside
  end
  fact Effect[T = Outside]

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
  import smoke.e_lacks.{Outside, shield}

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
/// no self-contradictory `{Outside, -Outside}` row here, so when WI-700 lands,
/// the reject must come from actual-vs-declared conformance itself.
const LACKS_GAP2_SRC: &str = r#"
namespace smoke.e3_row_mismatch
  import anthill.prelude.{Int64}
  import smoke.e_lacks.{Outside, shield}

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
/// mentions a token (every source names `External`/`ping` somewhere) cannot
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
        &["t_gh_wrong", "External"],
        "the real carrier's {External} under a consumer row {}",
    );
}

/// WI-703 regression: an `effects E = ?` row param on a spec that a carrier
/// `provides` must load with NO `import anthill.prelude.EffectsRuntime`. The
/// `effects EM = ?` desugar emits its `requires` anchor by CANONICAL name
/// (`anthill.prelude.EffectsRuntime`), so the bare anchor no longer lands
/// unresolved and the provider-requires exemption (keyed on the canonical
/// symbol) fires. Before the fix this exact source failed to load with
/// `'…Gh3' provides '…Mir3', which requires 'EffectsRuntime', but '…Gh3' does
/// not provide 'EffectsRuntime'` — the confusing wart WI-703 removes.
const NO_ER_IMPORT_SRC: &str = r#"
namespace smoke.wi703_no_import
  import anthill.prelude.{Int64, External}

  sort Mir3
    sort C = ?
    effects EM = ?
    operation ping(m: C) -> Int64 effects EM
  end

  sort Gh3
    entity mkGh3
    provides Mir3[C = Gh3, EM = {External}]
    operation ping(m: Gh3) -> Int64 effects {External} = 41
  end
end
"#;

#[test]
fn effects_row_param_provider_needs_no_effectsruntime_import() {
    expect_load(
        &[NO_ER_IMPORT_SRC],
        "an `effects E = ?` provider loading without importing EffectsRuntime (WI-703)",
    );
}

/// WI-703 regression (WI-422 phantom-rival class): emitting the anchor by its
/// canonical name makes it RESOLVE, so `scan_items_pass2` must NOT wire it as a
/// scope parent — otherwise the whole `anthill.prelude` namespace becomes a
/// resolution parent of every `effects E = ?` sort, and a user sort sharing a
/// prelude short name resurfaces as a phantom rival (ambiguous-symbol load
/// error). Here `Option` is a USER sort referenced by bare name INSIDE the
/// `effects E = ?` sort `Cache`; it must resolve to `…wi703_no_parent.Option`,
/// not collide with `anthill.prelude.Option`. Break the load.rs anchor-skip and
/// this reddens with `ambiguous symbol 'Option' … [anthill.prelude.Option,
/// …wi703_no_parent.Option]`.
const NO_PRELUDE_PARENT_SRC: &str = r#"
namespace smoke.wi703_no_parent
  import anthill.prelude.{Int64}

  sort Option
    entity myNone
  end

  sort Cache
    effects E = ?
    operation lookup(c: Cache) -> Option effects E
  end
end
"#;

#[test]
fn effects_row_param_anchor_is_not_wired_as_scope_parent() {
    expect_load(
        &[NO_PRELUDE_PARENT_SRC],
        "a user sort sharing a prelude short name, referenced inside an `effects E = ?` sort (WI-703 / WI-422 class)",
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
        &["t_wrap_wrong", "External"],
        "Wrap2[EW = {External}] under a consumer row {}",
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

/// 054 §Mechanism read/write split: TWO decoupled row params (ER/EW) thread and
/// refine independently — the genuine pin is `Wrap2RW`, which refines WR↦ER and
/// WW↦EW to DIFFERENT rows through call-site substitution (a swap would break
/// the tight `wrap_read_ext`/`wrap_write_mod` declarations). Expected FREE
/// (WI-441 substitution carries the second param with no new typer work).
#[test]
fn rw_split_threads_two_decoupled_row_params() {
    expect_load(
        &[MECH_SRC, RW_SRC],
        "read/write split: Wrap2RW refines WR={External}/WW={Modify[Reg]} independently + store union non-empty",
    );
}

/// The write row's refinement is enforced independently of the read row: the
/// fake's tracked {Modify[Reg]} write must not escape a pure `{}` consumer row.
#[test]
fn rw_split_write_refinement_is_enforced() {
    expect_reject(
        &[MECH_SRC, RW_SRC, RW_NEG_SRC],
        &["obs_fake_write_wrong", "Modify"],
        "the fake write's {Modify[Reg]} under a consumer row {}",
    );
}

/// The GENUINE two-param substitution is enforced: `w.peek()` refines to
/// WR = {External}, so declaring `{}` must be rejected (the External read
/// escapes). This is what actually pins that the second row param threads —
/// a swap/conflation of WR/WW, or a dropped read row, would not reject here.
#[test]
fn rw_split_read_row_substitution_is_enforced() {
    expect_reject(
        &[MECH_SRC, RW_SRC, WRAP2RW_NEG_SRC],
        &["wrap_read_wrong", "External"],
        "Wrap2RW[WR = {External}] read under a consumer row {}",
    );
}

/// The store threads the UNION of BOTH row params: at ER = {External},
/// EW = {Modify[Reg]} a consumer declaring only `{External}` must be rejected —
/// the write component of the union escapes. Pins the union is non-degenerate.
#[test]
fn rw_split_store_union_threads_both_components() {
    expect_reject(
        &[MECH_SRC, RW_SRC, STORE_UNION_NEG_SRC],
        &["store_union_drops", "Modify"],
        "StoreRW union {External, Modify[Reg]} under a consumer row {External}",
    );
}

/// GAP (a) — WI-700 DELIVERED: the lacks-constraint is ENFORCED at an explicit
/// instantiation site. `shield[EffP = {Outside}]` makes the callback param row
/// `{Outside, -Outside}` (present AND absent `Outside`), so the instantiation
/// violates its own `-Outside` — the param is uninhabitable and the load is
/// rejected. WI-705 SUBSUMED the original per-arg reject: the clash is now caught
/// at signature altitude (`check_signature_self_contradiction`, param-row branch),
/// which reads the DECLARED row RAW so it is not swallowed. Independent of `poke`:
/// any argument fails an uninhabitable param.
#[test]
fn lacks_enforced_at_explicit_instantiation() {
    expect_reject(
        &[LACKS_SRC, LACKS_GAP_SRC],
        &["shield", "Outside", "lack"],
        "EffP = {Outside} against a declared -Outside (self-contradictory instantiation)",
    );
}

/// GAP (b) — WI-700 DELIVERED: callback-row conformance is CHECKED at an explicit
/// instantiation site. `shield[EffP = {}]` closes the callback param row to
/// `{-Outside}`; `poke3` declares `{Outside}`, which the closed row forbids, so the
/// load is rejected. Unlike (a) there is no self-contradictory row — the reject
/// comes from actual-vs-declared conformance itself, reached because WI-700
/// eta-lifts the NULLARY `poke3` to a `() -> Int64 @ {Outside}` arrow (pre-WI-700
/// it collapsed to `Int64`, dropping its row, so the check was bypassed).
#[test]
fn row_conformance_checked_at_explicit_instantiation() {
    expect_reject(
        &[LACKS_SRC, LACKS_GAP2_SRC],
        &["shield", "poke3", "Outside"],
        "{Outside}-rowed op passed where EffP = {} (row conformance)",
    );
}

/// WI-700 nullary eta-lift round-trips through EVAL. The probes above reject at
/// LOAD, so they never exercise the eval half of the fix — the typer now ACCEPTS a
/// nullary op in a callback slot, so eval must MINT an `OpRef` for it (not eagerly
/// call it) and APPLY that arity-0 `OpRef` at `f()`. This pins the typer⊆eval
/// invariant: `five` is passed by name into a `() -> Int64` slot, `call_thunk`
/// invokes it, and the result is `5` (the deferred call ran once, at `f()`).
const ETA_NULLARY_SRC: &str = r#"
namespace smoke.eta_nullary
  import anthill.prelude.{Int64}

  operation five() -> Int64 = 5

  operation call_thunk(f: () -> Int64) -> Int64
    effects {}
  = f()

  operation use_it() -> Int64
    effects {}
  = call_thunk(five)
end
"#;

#[test]
fn nullary_eta_lift_round_trips_through_eval() {
    let mut interp = crate::common::interp_for(ETA_NULLARY_SRC);
    let r = interp
        .call("smoke.eta_nullary.use_it", &[])
        .expect("use_it evaluates");
    assert_eq!(
        r.as_int(),
        Some(5),
        "nullary `five` eta'd to an OpRef, then called as a thunk at `f()`, yields 5",
    );
}

/// WI-700 regression guard (surfaced in review): a NULLARY op whose RETURN type is
/// itself a function, passed BY NAME into a slot of that function type, must still
/// load and eval. The nullary eta-lift must NOT shadow the zero-arg-call/return-type
/// reading when `ret` already conforms to the expected arrow (`make_inc() ->
/// Function[..]` into a `Function[..]` slot) — else the arg types as `() ->
/// Function[..]` and mismatches. Pre-fix this rejected with `expected Function[..],
/// got () -> Function[..]`. `go` evals to `0`: `make_inc` is zero-arg-called to yield
/// the identity lambda, which `apply_it` then applies to `0`.
const NULLARY_RETURNS_FN_SRC: &str = r#"
namespace smoke.nullary_ret_fn
  import anthill.prelude.{Int64, Function}

  operation make_inc() -> Function[A = Int64, B = Int64]
  = lambda (x: Int64) -> x

  operation apply_it(f: Function[A = Int64, B = Int64]) -> Int64
  = f(0)

  operation go() -> Int64
  = apply_it(make_inc)
end
"#;

#[test]
fn nullary_returning_function_prefers_return_type_reading() {
    let mut interp = crate::common::interp_for(NULLARY_RETURNS_FN_SRC);
    let r = interp
        .call("smoke.nullary_ret_fn.go", &[])
        .expect("go evaluates");
    assert_eq!(
        r.as_int(),
        Some(0),
        "make_inc reads as its returned Function (not eta'd to `() -> Function`); apply_it(make_inc) applies it to 0",
    );
}

// ── WI-705: effect-row self-contradiction at SIGNATURE altitude ────────────────
//
// WI-700 rejects a self-contradictory instantiated CALLBACK-PARAM row, but only
// for an eta'd OP-REF callback arg (inside the per-arg `validate_callback_effect_
// row`, which bails at the `arg_op_sym` extraction for non-var-ref args). Three
// shapes of the SAME uninhabitable-row bug are involved: (a) an op's OWN
// instantiated row (no callback param at all) and (b) a LAMBDA callback with a
// self-contradictory instantiated declared row — both verified LOADING on HEAD,
// the two WI-700 missed; plus (c) an INFERENCE-bound (non-explicit) row param,
// which WI-700 DID catch (its per-arg check ran after unification) and which the
// subsumption must not regress. WI-705 replaces the per-arg reject with ONE per-call
// SIGNATURE validation, decomposing the op's own row AND each arrow-typed param's
// row (after subst). It runs AFTER the argument-unification loops (not merely after
// `seed_op_type_args`) precisely so `subst` carries the FULL instantiation — explicit
// AND inferred — covering all three shapes and SUBSUMING WI-700's eta-scoped reject.

/// WI-705 probe (a): an op's OWN instantiated effect row is self-contradictory.
/// `g[E]() effects {E, -Outside}` instantiated `g[E = {Outside}]()` makes the
/// signature row `{Outside, -Outside}` — present AND absent `Outside`, hence
/// uninhabitable. There is no callback param, so WI-700's per-arg
/// `validate_callback_effect_row` never inspects it. `g` OVER-declares on a pure
/// body (the `poke` idiom); the row checker consumes the DECLARED row.
const OWN_ROW_SELFCONTRA_SRC: &str = r#"
namespace smoke.e4_own_row
  import anthill.prelude.{Int64}
  import smoke.e_lacks.{Outside}

  operation g[E]() -> Int64
    effects {E, -Outside}
  = 41

  operation t_own_row() -> Int64
    effects {Outside}
  = g[E = {Outside}]()
end
"#;

/// WI-705 probe (b): a LAMBDA callback with a self-contradictory instantiated
/// declared row. `shield[EffP = {Outside}]` makes the callback param row
/// `{Outside, -Outside}`; the arg is a pure lambda (not a var-ref op), so
/// WI-700's `validate_callback_effect_row` bails at `arg_op_sym` and never checks
/// it. The signature-level check is actual-agnostic, so it rejects the
/// uninhabitable param regardless of the callback shape.
const LAMBDA_SELFCONTRA_SRC: &str = r#"
namespace smoke.e5_lambda_selfcontra
  import anthill.prelude.{Int64}
  import smoke.e_lacks.{Outside, shield}

  operation t_lambda_selfcontra() -> Int64
    effects {Outside}
  = shield[EffP = {Outside}](lambda () -> 5)
end
"#;

/// WI-705 probe (a) — REJECTED: the op's OWN instantiated row `{Outside, -Outside}`
/// is uninhabitable. WI-700's per-arg callback check never inspects it (no callback
/// param); the signature-level `check_signature_self_contradiction` (run over the op's
/// own row after unification) rejects it, naming the op and the clashing `Outside`.
#[test]
fn own_row_self_contradiction_rejected_at_signature() {
    expect_reject(
        &[LACKS_SRC, OWN_ROW_SELFCONTRA_SRC],
        &["e4_own_row.g", "Outside", "lack"],
        "g[E = {Outside}]() own row {Outside, -Outside} (self-contradictory instantiation)",
    );
}

/// WI-705 probe (b) — REJECTED: a LAMBDA callback whose instantiated declared param
/// row `{Outside, -Outside}` is uninhabitable. WI-700's per-arg check bails at the
/// var-ref extraction for a lambda arg; the signature-level check is actual-agnostic,
/// so it rejects the uninhabitable param regardless of the callback's shape. Shares
/// the diagnostic wording with the (now-removed) WI-700 eta-scoped reject, so the
/// `shield`/`Outside`/`lack` assertion is stable across the subsumption.
#[test]
fn lambda_callback_self_contradiction_rejected_at_signature() {
    expect_reject(
        &[LACKS_SRC, LAMBDA_SELFCONTRA_SRC],
        &["shield", "Outside", "lack"],
        "shield[EffP = {Outside}](lambda) callback row {Outside, -Outside} (self-contradictory instantiation)",
    );
}

/// WI-705 probe (c) — REGRESSION GUARD for the WI-700 coverage this WI subsumes: an
/// INFERENCE-bound (no explicit `[EffP=…]`) row param that makes a callback declared
/// row self-contradictory. `f[EffP](a: () -> Int64 @ {EffP}, cb: () -> Int64 @ {EffP,
/// -Outside})` called `f(src, src)` with `src` rowed {Outside}: arg `a` infers
/// EffP={Outside}, so `cb`'s row becomes {Outside, -Outside}. WI-700's per-arg check
/// rejected this because it ran AFTER argument unification; WI-705 must too, which is
/// exactly why `check_signature_self_contradiction` runs after the arg-unify loops
/// (not merely after `seed_op_type_args`, which would see only explicit args and
/// silently re-open this hole). Verified LOADING with the check placed pre-unification
/// and REJECTED with it placed post-unification.
const INFER_SELFCONTRA_SRC: &str = r#"
namespace smoke.e6_infer_selfcontra
  import anthill.prelude.{Int64}
  import smoke.e_lacks.{Outside}

  operation src() -> Int64
    effects {Outside}
  = 1

  operation f[EffP](a: () -> Int64 @ {EffP}, cb: () -> Int64 @ {EffP, -Outside}) -> Int64
    effects {EffP}
  = cb()

  operation caller() -> Int64
    effects {Outside}
  = f(src, src)
end
"#;

#[test]
fn inference_bound_self_contradiction_rejected() {
    expect_reject(
        &[LACKS_SRC, INFER_SELFCONTRA_SRC],
        &["e6_infer_selfcontra.f", "Outside", "lack"],
        "EffP inferred to {Outside} making cb's row {Outside, -Outside} (no explicit instantiation)",
    );
}

/// WI-705 guarded-exclusion guard: a GUARDED (dischargeable) present label must NOT
/// count as an unconditional contradiction against a `-X` lacks in the same row.
/// `g[E]() effects { Outside :- eq(1,0), -Outside, E }` decomposes (pre-discharge)
/// to present `[Outside]` (the guarded atom is conservatively present, WI-478) and
/// absent `[Outside]` (the literal `-Outside`), so a naive `row_self_contradiction`
/// fires — but WI-067 discharge would refute `eq(1,0)` and drop `Outside`, leaving an
/// inhabitable `{-Outside}`. `check_signature_self_contradiction` must therefore DEFER
/// (load), not hard-reject, when the only clashing label is guarded. `E = {}`
/// satisfies the "some type param bound" gate so the check actually runs.
const GUARDED_SELFCONTRA_SRC: &str = r#"
namespace smoke.e7_guarded
  import anthill.prelude.{Int64}
  import smoke.e_lacks.{Outside}

  operation g[E]() -> Int64
    effects { Outside :- eq(1, 0), -Outside, E }
  = 1

  operation caller() -> Int64
    effects {}
  = g[E = {}]()
end
"#;

#[test]
fn guarded_present_vs_lacks_defers_not_rejects() {
    expect_load(
        &[LACKS_SRC, GUARDED_SELFCONTRA_SRC],
        "a guarded (dischargeable) present label vs a -X lacks must defer to discharge, not reject",
    );
}

// ── WI-701: the `Branch` × `External` co-occurrence gate ───────────────────────
//
// Proposal 054 §"`Branch` and `External`": a `Branch` region may not perform
// `External`. Neither branch-interaction contract (snapshot-above / survive-below,
// 027/037/047 §8) is available for state the runtime cannot mediate, and the hazard
// is permanent (no `register_undo` for the world; a solver re-runs the continuation
// once per solution). WI-701 is the BLUNT load-time co-occurrence reject: any
// operation whose DECLARED effect row presents both labels is rejected. WI-329's
// row-discharge typing later makes it compositional (a solver's reify discharges
// `Branch`); this is the un-discharged floor, "acceptable and intended" per the ticket.

/// A `Branch` region performing `External` — the primary hazard shape (a body that
/// searches AND mints an issue). `search_and_create` OVER-declares on a pure body
/// (the `poke`/`poke3` idiom: over-declaration is not itself an error), so ONLY the
/// co-occurrence gate fires, isolating the mechanism under test.
const BRANCH_EXTERNAL_SRC: &str = r#"
namespace smoke.g_branch_external
  import anthill.prelude.{Int64, Branch, External}

  operation search_and_create() -> Int64
    effects {Branch, External}
  = 41
end
"#;

/// Order-independence + the body-less SPEC-op shape: the same reject when the row is
/// written `External`-first and declared on a body-less spec operation (walked per
/// `OperationInfo` fact, so a spec op with no body is covered like the signature check).
const BRANCH_EXTERNAL_SPEC_SRC: &str = r#"
namespace smoke.g2_branch_external_spec
  import anthill.prelude.{Int64, Branch, External}

  sort Region
    sort C = ?
    operation region_probe(m: C) -> Int64 effects {External, Branch}
  end
end
"#;

/// Negative: `Branch` ALONE loads — the gate rejects only the CO-occurrence, never
/// `Branch` on its own (a pure search region is fine).
const BRANCH_ALONE_SRC: &str = r#"
namespace smoke.g3_branch_alone
  import anthill.prelude.{Int64, Branch}

  operation only_branch() -> Int64
    effects {Branch}
  = 41
end
"#;

/// Negative twin: `External` ALONE loads — an `External`-rowed op with no `Branch`
/// is exactly what every WI-437 backend op is; it must stay loadable.
const EXTERNAL_ALONE_SRC: &str = r#"
namespace smoke.g4_external_alone
  import anthill.prelude.{Int64, External}

  operation only_external() -> Int64
    effects {External}
  = 41
end
"#;

/// WI-701 present-vs-absent: `effects {Branch, -External}` LOADS — an ABSENT External
/// is not co-occurrence (the op explicitly LACKS External inside a Branch region,
/// which is exactly fine). Locks the gate to PRESENCE, so a future refactor keying on
/// "mentions External" instead of "presents External" would be caught here.
const BRANCH_LACKS_EXTERNAL_SRC: &str = r#"
namespace smoke.g5_branch_lacks_external
  import anthill.prelude.{Int64, Branch, External}

  operation branch_lacks_external() -> Int64
    effects {Branch, -External}
  = 41
end
"#;

/// WI-701 guarded co-occurrence: a GUARDED External (`External :- g`) is
/// CONSERVATIVELY PRESENT — the same stance `decompose_effect_row_raw` takes — so
/// `{Branch, External :- g}` is REJECTED: the gate peeks past the `:- guard` to the
/// External sort. Without the guarded-unwrap this slips through (the `guarded(...)`
/// atom classifies as `Parameterized{base: guarded}`, not `External`). Over-declared
/// on a pure body (WI-478: a guarded effect is a declaration, not a performance).
const BRANCH_GUARDED_EXTERNAL_SRC: &str = r#"
namespace smoke.g6_branch_guarded_external
  import anthill.prelude.{Int64, Branch, External}

  operation guarded_region(b: Int64) -> Int64
    effects {Branch, External :- eq(b, 0)}
  = 41
end
"#;

/// WI-701: an op declaring `effects {Branch, External}` is REJECTED at load — a
/// Branch region may not perform External. Needles tie the error to THIS op AND both
/// effects, so an unrelated diagnostic mentioning a token cannot satisfy it.
#[test]
fn branch_external_co_occurrence_rejected() {
    expect_reject(
        &[BRANCH_EXTERNAL_SRC],
        &["search_and_create", "Branch", "External"],
        "an op declaring effects {Branch, External}",
    );
}

/// WI-701: the reject is order-independent and covers body-less SPEC ops — the row
/// is walked per `OperationInfo` fact, not off a body.
#[test]
fn branch_external_co_occurrence_rejected_spec_op_order_independent() {
    expect_reject(
        &[BRANCH_EXTERNAL_SPEC_SRC],
        &["region_probe", "Branch", "External"],
        "a body-less spec op declaring effects {External, Branch}",
    );
}

/// WI-701 negative: `Branch` alone loads — the gate is a CO-occurrence reject, not a
/// ban on `Branch`.
#[test]
fn branch_alone_still_loads() {
    expect_load(&[BRANCH_ALONE_SRC], "effects {Branch} alone");
}

/// WI-701 negative: `External` alone loads — the gate does not touch ordinary
/// External-rowed ops (every WI-437 backend op).
#[test]
fn external_alone_still_loads() {
    expect_load(&[EXTERNAL_ALONE_SRC], "effects {External} alone");
}

/// WI-701 present-vs-absent: `{Branch, -External}` loads — an absent External is not
/// co-occurrence. Guards against the gate keying on mere mention of the label.
#[test]
fn branch_with_absent_external_loads() {
    expect_load(&[BRANCH_LACKS_EXTERNAL_SRC], "effects {Branch, -External}");
}

/// WI-701: a GUARDED External is conservatively present, so `{Branch, External :- g}`
/// is rejected — the gate peeks past the guard to the External sort (loud over silent,
/// consistent with `decompose_effect_row_raw`).
#[test]
fn branch_guarded_external_co_occurrence_rejected() {
    expect_reject(
        &[BRANCH_GUARDED_EXTERNAL_SRC],
        &["guarded_region", "Branch", "External"],
        "guarded External co-occurring with Branch",
    );
}

// ── WI-702: the `[simp]`/`[unfold]` formation gate (proposal 054 §"Consumers") ──
//
// A `[simp]`/`[unfold]` equation is a DIRECTIONAL rewrite — `fire_simp` /
// `fire_simp_equation` fire it LHS→RHS, so firing DUPLICATES / REORDERS / DROPS the
// matched redex. That is sound today only because effectful ops never *become* simp
// equations (the defining-equation family declines them — the part-1 gate). The one
// hole left is a USER-WRITTEN `[simp]`/`[unfold]` rule whose sides MENTION an effectful
// operation symbol: rewriting its call is unsound (an External `create_issue` rewritten
// twice mints two issues). WI-702 rejects such a rule at LOAD; the firing sites stay
// effect-blind. The gate keys on the EFFECT ROW (any effect — function-hood), NOT
// `requires` (Set/Map carry `requires Eq[T]` into member/insert/get, and the stdlib's
// own `member(?x, insert(?s,?x)) <=> true [simp]` laws mention them — so a
// requires-inclusive gate would reject the standard library; the whole-stdlib load in
// github_todo_test is the standing positive control for that).

/// A `[simp]` rewrite whose LHS mentions an `External`-rowed op — firing it would
/// re-run / drop the external call. REJECTED at load, naming the op AND its row.
const SIMP_EXTERNAL_SRC: &str = r#"
namespace smoke.h1_simp_external
  import anthill.prelude.{Int64, External}

  operation poke_ext(x: Int64) -> Int64
    effects {External}
  = x

  rule poke_ext(?x) <=> ?x [simp]
end
"#;

/// The `[unfold]` tag is a directional rewrite too, so it is gated identically.
const UNFOLD_EXTERNAL_SRC: &str = r#"
namespace smoke.h2_unfold_external
  import anthill.prelude.{Int64, External}

  operation poke_unf(x: Int64) -> Int64
    effects {External}
  = x

  rule poke_unf(?x) <=> ?x [unfold]
end
"#;

/// EFFECT-GENERAL, not External-only: a `[simp]` rule mentioning an op carrying a
/// USER-declared effect (`Outside`, the Clock convention) is rejected too — a
/// non-empty effect row is not equational regardless of WHICH effect (the
/// function-hood predicate, shared with the part-1 gate). Locks the "any effect"
/// scope decision against a future narrowing to a single named effect.
const SIMP_USER_EFFECT_SRC: &str = r#"
namespace smoke.h3_simp_user_effect
  import anthill.prelude.{Int64, Effect}

  sort Outside
  end
  fact Effect[T = Outside]

  operation poke_out(x: Int64) -> Int64
    effects {Outside}
  = x

  rule poke_out(?x) <=> ?x [simp]
end
"#;

/// Negative control: a `[simp]` rewrite over PURE ops (`dbl` / `add`) LOADS — the
/// gate rejects only effectful mentions, never `[simp]` itself. (`dbl <=> add(x,x)`
/// would loop if fired, but LOADING is what is under test.)
const SIMP_PURE_SRC: &str = r#"
namespace smoke.h4_simp_pure
  import anthill.prelude.{Int64}
  import anthill.prelude.Numeric.{add}

  operation dbl(x: Int64) -> Int64 = add(x, x)

  rule dbl(?x) <=> add(?x, ?x) [simp]
end
"#;

/// Scope control: an UNTAGGED equation mentioning the SAME `External`-rowed op LOADS.
/// The hazard is FIRING (only `[simp]`/`[unfold]` rewrites fire); an untagged equation
/// is an inert cite-required LAW (`unindex_functor`'d, WI-139) that never rewrites, so
/// it is out of scope — this locks the gate to the tagged rewrites, not all equations.
const UNTAGGED_EXTERNAL_SRC: &str = r#"
namespace smoke.h5_untagged_external
  import anthill.prelude.{Int64, External}

  operation poke_law(x: Int64) -> Int64
    effects {External}
  = x

  rule poke_law(?x) <=> ?x
end
"#;

/// WI-702: a `[simp]` rewrite mentioning an `External`-rowed op is rejected at load.
/// Needles tie the error to THIS op AND its effect, so an unrelated diagnostic that
/// merely names a token cannot satisfy it.
#[test]
fn simp_rule_mentioning_external_op_rejected() {
    expect_reject(
        &[SIMP_EXTERNAL_SRC],
        &["poke_ext", "External"],
        "a `[simp]` rewrite mentioning an External-rowed op",
    );
}

/// WI-702: the `[unfold]` tag is gated identically (both are directional rewrites).
#[test]
fn unfold_rule_mentioning_external_op_rejected() {
    expect_reject(
        &[UNFOLD_EXTERNAL_SRC],
        &["poke_unf", "External"],
        "an `[unfold]` rewrite mentioning an External-rowed op",
    );
}

/// WI-702: the gate is effect-GENERAL — a user-declared effect (`Outside`) trips it
/// too, so the decision is "any non-empty effect row", not "External only".
#[test]
fn simp_rule_mentioning_user_effect_op_rejected() {
    expect_reject(
        &[SIMP_USER_EFFECT_SRC],
        &["poke_out", "Outside"],
        "a `[simp]` rewrite mentioning a user-effect-rowed op",
    );
}

/// WI-702 negative: a `[simp]` rewrite over PURE ops loads — the gate does not ban
/// `[simp]`, only effectful mentions.
#[test]
fn simp_rule_over_pure_ops_still_loads() {
    expect_load(&[SIMP_PURE_SRC], "a `[simp]` rewrite over pure ops");
}

/// WI-702 scope control: an UNTAGGED equation mentioning an effectful op loads — only
/// FIRING rewrites (`[simp]`/`[unfold]`) are the hazard, not every equational law.
#[test]
fn untagged_equation_mentioning_external_op_still_loads() {
    expect_load(&[UNTAGGED_EXTERNAL_SRC], "an untagged equation over an External-rowed op");
}

/// A `[simp]` rule whose GUARD calls an `External`-rowed op in METHOD syntax
/// (`?m.peek()`). The gate runs AFTER `type_rule_bodies` dispatches the `DotApply`
/// to `Apply(peek, ?m)`, so the effectful call is caught. Locks the ordering: a
/// gate placed BEFORE dot-dispatch would see an un-dispatched `DotApply` and miss
/// `peek` entirely (a code-review coverage-hole regression guard).
const SIMP_DOT_EXTERNAL_SRC: &str = r#"
namespace smoke.h6_simp_dot_external
  import anthill.prelude.{Int64, External}
  import anthill.prelude.Ordered.{gt}

  sort Reg
    operation peek(m: Reg) -> Int64
      effects {External}
  end

  operation gate(m: Reg) -> Int64 = 0

  rule gate(?m) <=> 0 :- gt(?m.peek(), 0) [simp]
end
"#;

/// WI-702: an effectful op reached via METHOD syntax in a `[simp]` guard is caught
/// (the gate runs after dot-dispatch). Regression guard for the code-review finding.
#[test]
fn simp_rule_with_dot_syntax_effectful_guard_rejected() {
    expect_reject(
        &[SIMP_DOT_EXTERNAL_SRC],
        &["peek", "External"],
        "a `[simp]` guard calling an External-rowed op via method syntax",
    );
}

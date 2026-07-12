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
//!          violating its own `-Outside` — the self-contradiction reject, which
//!          reads the DECLARED row RAW so the clash is not swallowed as a `None`;
//!      (b) `shield[EffP = {}](poke3)` is REJECTED: the closed callback row
//!          `{-Outside}` forbids the `{Outside}` that `poke3` declares
//!          (actual-vs-declared conformance, no self-contradiction).
//!      Declared rows are what the row checker consumes — `poke`/`poke3` have pure
//!      bodies and OVER-declare deliberately. Both probes are NULLARY ops passed by
//!      name: WI-700 eta-lifts a nullary op ref in a callback slot to
//!      `() -> ret @ row` (pre-WI-700 it collapsed to its return type, dropping the
//!      row and bypassing the check).

/// The 054 §Faking mini-model over the REAL `External`: spec with a row param +
/// the two carriers. NOTE `import anthill.prelude.EffectsRuntime`: the
/// `effects EM = ?` desugar emits `requires EffectsRuntime[Effects = EM]`, and
/// without the import the provider-requires exemption misses (symbol identity)
/// — see the WI-698 memory/proposal by-catch (WI-703).
const MECH_SRC: &str = r#"
namespace smoke.b_mech
  import anthill.prelude.{Int64, EffectsRuntime, External}

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
  import anthill.prelude.{Int64, Unit, EffectsRuntime, Modify, Modifiable, External}
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
/// rejected (the self-contradiction reject in `validate_callback_effect_row`,
/// reading the DECLARED row RAW so the clash is not swallowed). Independent of
/// `poke`: any argument fails an uninhabitable param.
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

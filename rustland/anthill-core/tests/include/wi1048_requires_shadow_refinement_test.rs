//! WI-1048 — the requires-shadow lint (WI-346) does not fire on a deliberate
//! REFINEMENT.
//!
//! WI-346 compared SHORT NAMES ONLY, so it could not tell an accidental
//! collision (the author believed `requires` overrides) from a deliberate
//! refinement (a distinct operation by construction). It therefore fired on the
//! stdlib's `FiniteCollection.map`/`filter` — proposal library/003 + WI-599's
//! THIN design, whose whole point is that the finite versions return a
//! `FiniteCollection` so `xs.map(f).size()` keeps type-checking — and advised a
//! rename that would have destroyed it.
//!
//! The narrowing (`typing::requires_shadow_is_confusable`): warn unless the two
//! operations are CONFIDENTLY distinguishable at a call site — different arity,
//! a different parameter type, or a different return type, each compared after
//! the `requires Spec[…]` clause's σ, and with a type PARAMETER on either side
//! read as a wildcard rather than a difference. Every leg that cannot be decided
//! falls open to warning, so the lint can only get quieter where a difference is
//! proven — it can never silently retire itself.
//!
//! WHAT FAILS WHEN THE CHANGE IS BACKED OUT is stated per test below. The
//! stdlib's own zero-warning pin lives with the channel it belongs to, in
//! `wi345_warnings_channel_test::clean_stdlib_load_carries_no_warnings`.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Load the stdlib and `extra` TOGETHER, returning either the warning strings
/// (clean load) or the load errors.
///
/// ONE `load_all` over stdlib + extra, deliberately: `load::load` of `extra` on
/// top of an already-loaded stdlib KB reports NO error for the row-A probe
/// below (measured). The whole-KB passes — op-body type checking and this very
/// lint among them — belong to `load_all`, so an incremental second `load` is
/// not the loader's verdict on this source, and a test reading it would assert
/// over checks that never ran.
fn load_stdlib_with(extra: &str) -> Result<Vec<String>, Vec<String>> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(result) => Ok(result.warnings.iter().map(|w| w.to_string()).collect()),
        Err(errs) => Err(errs.iter().map(|e| e.to_string()).collect()),
    }
}

/// The warning strings of a load that must be clean — a shadow is advisory, so
/// a load error here is a fixture bug, not the thing under test.
fn load_warnings(extra: &str) -> Vec<String> {
    load_stdlib_with(extra).unwrap_or_else(|errs| panic!(
        "expected a clean load (a shadow is advisory, not fatal); got errors:\n{}",
        errs.join("\n")))
}

// ── a refined RETURN type is a distinct operation → silent ──────────────

#[test]
fn refined_return_type_shadow_is_silent() {
    // The on-the-nose analogue of `FiniteCollection.map` vs `Iterable.map`:
    // same name, same arity, same parameter type (after σ maps `RSpec.C` to
    // `RCarrier`), DIFFERENT return type. The two can never be confused at a
    // call site — annotating the expected type makes the choice observable as a
    // loud type error (driven below in `finite_map_refuses_a_stream_return`).
    //
    // BACKED OUT: this test FAILS — the short-name-only predicate warns here.
    let src = r#"
        namespace wi1048.refine
          sort Broad
            entity broad(id: Int64)
          end
          sort Narrow
            entity narrow(id: Int64)
          end
          sort RSpec
            sort C = ?
            operation r_op(c: C) -> Broad
          end
          sort RCarrier
            entity rc(id: Int64)
          end
          sort RReq
            requires RSpec[C = RCarrier]
            operation r_op(c: RCarrier) -> Narrow = narrow(id: 1)
          end
        end
    "#;
    let warnings = load_warnings(src);
    assert!(
        !warnings.iter().any(|w| w.contains("wi1048.refine")),
        "a shadow that REFINES the return type is a distinct operation by \
         construction, not an accidental collision; got: {warnings:?}");
}

// ── a same-signature shadow STILL warns, even parametrically ────────────

#[test]
fn parametric_same_signature_shadow_still_warns() {
    // The case the lint is KEPT for, in the form that is easiest to lose: the
    // signature mentions an operation-level type parameter `U`. Each operation
    // mints its OWN logical variable for its own `U` (`VarId` compares by id,
    // not name), so a comparison by hash-cons identity would call these two
    // signatures DIFFERENT and stay silent — silently retiring the lint for
    // exactly the generic operations it most needs to cover. In
    // `types_definitely_differ` a type parameter is a WILDCARD, so no
    // disagreement between two of them is ever a proof of difference.
    //
    // BACKED OUT (whole change): this test still passes — it is the control
    // that the narrowing did not retire the lint. It FAILS if
    // `types_definitely_differ` drops its type-parameter wildcard for
    // `Term::Var`, which is the narrowing's own failure mode.
    let src = r#"
        namespace wi1048.parametric
          sort PSpec
            sort T = ?
            operation p_op[U](x: T, y: U) -> U
          end
          sort PCarrier
            entity pc(id: Int64)
          end
          sort PReq
            requires PSpec[T = PCarrier]
            operation p_op[U](x: PCarrier, y: U) -> U = y
          end
        end
    "#;
    let warnings = load_warnings(src);
    assert!(
        warnings.iter().any(|w|
            w.contains("wi1048.parametric.PReq")
                && w.contains("p_op")
                && w.contains("wi1048.parametric.PSpec")),
        "a same-signature shadow must still warn — the whole point of WI-346 — \
         and a signature over an op type parameter is no exception; got: {warnings:?}");
}

#[test]
fn unbound_spec_parameter_shadow_still_warns() {
    // `requires Pingable` binds NOTHING, so σ is empty and the spec op keeps its
    // `x: Pingable.T` / `-> Pingable.T`. Against the shadow's `Int64` that is
    // not a DIFFERENT type — it is an UNKNOWN one, which `Int64` instantiates.
    // Reading an unbound parameter as a difference would silence the plainest
    // accidental collision there is, which is what WI-346 exists for.
    //
    // This is the shape of `anthill-cli`'s `advisory-warning.anthill` fixture
    // (`run_cmd_test::advisory_warnings_print_but_do_not_block`), and that
    // fixture is what caught the first cut of this predicate treating the
    // unbound parameter as concrete. Pinned here too so the rule is tested
    // where it lives, not only where a CLI fixture happens to exercise it.
    //
    // BACKED OUT (whole change): this test still passes — another control that
    // the narrowing did not retire the lint. It FAILS if
    // `types_definitely_differ` drops its type-parameter wildcard for a
    // sort-parameter reference.
    let src = r#"
        namespace wi1048.unbound
          import anthill.prelude.Int64
          sort Pingable
            sort T = ?
            operation ping(x: T) -> T
          end
          sort Shadower
            requires Pingable
            operation ping(x: Int64) -> Int64 = x
          end
        end
    "#;
    let warnings = load_warnings(src);
    assert!(
        warnings.iter().any(|w|
            w.contains("wi1048.unbound.Shadower")
                && w.contains("ping")
                && w.contains("wi1048.unbound.Pingable")),
        "an UNBOUND spec type parameter is a wildcard, not a proven difference; \
         this shadow must still warn; got: {warnings:?}");
}

#[test]
fn elided_type_argument_shadow_still_warns() {
    // ELISION IS NOT DIFFERENCE. `Stream[T = Int64]` and `Stream[T = Int64,
    // E = {}]` name the same constructor; the first leaves `E` unstated, and an
    // unstated argument instantiates to whatever stands opposite it. A call site
    // cannot tell the two apart, so this is the collision WI-346 exists for.
    //
    // Found by the WI-1048 REVIEW, driven through `anthill check`: the first cut
    // of `types_definitely_differ` returned "different" on a differing named-arg
    // COUNT, so this loaded silent while the same file with `E = {}` written out
    // warned — a verdict that turned on how much the author bothered to spell.
    //
    // BACKED OUT (whole change): this test still passes. It FAILS if
    // `types_definitely_differ` decides on argument COUNT instead of comparing
    // only the positions both sides state.
    let src = r#"
        namespace wi1048.elided
          import anthill.prelude.{Int64, Stream}
          sort ECar
            entity ec(id: Int64)
          end
          sort ESpec
            sort T = ?
            operation e_op(x: T) -> Stream[T = Int64, E = {}]
          end
          sort EReq
            requires ESpec[T = ECar]
            operation e_op(x: ECar) -> Stream[T = Int64]
          end
        end
    "#;
    let warnings = load_warnings(src);
    assert!(
        warnings.iter().any(|w|
            w.contains("wi1048.elided.EReq") && w.contains("e_op")),
        "an ELIDED type argument is unstated, not different; this shadow must \
         still warn; got: {warnings:?}");
}

#[test]
fn bare_constructor_shadow_still_warns() {
    // The same rule reached from the other side: a bare name reference IS the
    // nullary spelling of its own constructor, so `List` against `List[T =
    // Int64]` is one elided argument, not a different type. Before the review
    // this pair fell to a hash-cons-identity catch-all and read as "definitely
    // different" — a `Ref` and an applied `Fn` are never the same TermId.
    //
    // BACKED OUT (whole change): this test still passes. It FAILS, with
    // `elided_type_argument_shadow_still_warns`, if `types_definitely_differ`
    // decides on argument COUNT. Measured: dropping `type_ctor_view`'s bare-name
    // arm does NOT fail this one — it fails the two `*_is_silent` tests instead,
    // because `Broad`/`Narrow` and `Int64`/`Bool` are bare `Ref`s and would go
    // undecided. Both halves of the arm's job are covered, by different tests.
    let src = r#"
        namespace wi1048.bare
          import anthill.prelude.{Int64, List}
          sort BCar2
            entity bc2(id: Int64)
          end
          sort GSpec
            sort T = ?
            operation g_op(x: T) -> List
          end
          sort GReq
            requires GSpec[T = BCar2]
            operation g_op(x: BCar2) -> List[T = Int64]
          end
        end
    "#;
    let warnings = load_warnings(src);
    assert!(
        warnings.iter().any(|w|
            w.contains("wi1048.bare.GReq") && w.contains("g_op")),
        "a bare constructor is its own nullary application, not a different \
         type; this shadow must still warn; got: {warnings:?}");
}

// ── a different ARITY is distinguishable → silent ───────────────────────

#[test]
fn differing_arity_shadow_is_silent() {
    // A call site passes a fixed number of arguments, so it cannot confuse a
    // 1-ary op with a 2-ary one.
    //
    // BACKED OUT: this test FAILS — the short-name-only predicate warns here.
    let src = r#"
        namespace wi1048.arity
          sort ASpec
            sort T = ?
            operation a_op(x: T) -> T
          end
          sort ACarrier
            entity ac(id: Int64)
          end
          sort AReq
            requires ASpec[T = ACarrier]
            operation a_op(x: ACarrier, y: ACarrier) -> ACarrier = x
          end
        end
    "#;
    let warnings = load_warnings(src);
    assert!(
        !warnings.iter().any(|w| w.contains("wi1048.arity")),
        "operations of different arity are not confusable at a call site; \
         got: {warnings:?}");
}

// ── a different PARAM type is distinguishable → silent ──────────────────

#[test]
fn differing_param_type_shadow_is_silent() {
    // Same arity and same return type, but the second parameter differs
    // (`Int64` vs `Bool`), so an argument that fits one does not fit the other.
    //
    // BACKED OUT: this test FAILS — the short-name-only predicate warns here.
    let src = r#"
        namespace wi1048.param
          import anthill.prelude.{Int64, Bool}
          sort BSpec
            sort T = ?
            operation b_op(x: T, tag: Int64) -> T
          end
          sort BCarrier
            entity bc(id: Int64)
          end
          sort BReq
            requires BSpec[T = BCarrier]
            operation b_op(x: BCarrier, tag: Bool) -> BCarrier = x
          end
        end
    "#;
    let warnings = load_warnings(src);
    assert!(
        !warnings.iter().any(|w| w.contains("wi1048.param")),
        "operations whose parameter types differ are not confusable at a call \
         site; got: {warnings:?}");
}

// ── the stdlib's behaviour is already right (the premise, re-measured) ──
//
// These two drive the shape the lint was firing on. They are the evidence that
// silencing the warning silences a FALSE POSITIVE rather than hiding a real
// problem — and they pass BOTH with and without the change, by design: the
// point is that dispatch and the typer were never wrong here.

/// The load errors of a load that may legitimately be refused — empty on a
/// clean load. Refusal is what one of the two rows is asserting.
fn stdlib_plus_source_errors(extra: &str) -> Vec<String> {
    load_stdlib_with(extra).err().unwrap_or_default()
}

#[test]
fn finite_map_refuses_a_stream_return() {
    // `List` provides BOTH `FiniteCollection` (explicitly) and `Iterable`
    // (transitively via `Stream`, WI-495), so `xs.map(f)` is genuinely
    // contested. Dispatch picks the MORE SPECIFIC `FiniteCollection.map`,
    // deterministically — and annotating the return type makes that choice
    // observable as a LOUD type error naming BOTH types. There is no silent
    // wrong answer behind the warning WI-346 was printing.
    let errs = stdlib_plus_source_errors(r#"
        namespace wi1048.row_a
          import anthill.prelude.{List, Int64, Stream}
          operation probe(xs: List[T = Int64]) -> Stream[T = Int64, E = {}] =
            xs.map(lambda x -> x)
        end
    "#);
    assert!(
        errs.iter().any(|e|
            e.contains("type mismatch")
                && e.contains("Stream[")
                && e.contains("FiniteCollection[")),
        "expected a type mismatch naming both the expected Stream and the \
         FiniteCollection dispatch actually produced; got: {errs:?}");
}

#[test]
fn finite_map_keeps_a_pipeline_consumable() {
    // The other side of WI-599's THIN design: because `FiniteCollection.map`
    // returns a `FiniteCollection`, the eager consumer downstream still
    // type-checks. This is what a rename — the warning's own advice — would
    // have broken.
    let errs = stdlib_plus_source_errors(r#"
        namespace wi1048.row_b
          import anthill.prelude.{List, Int64}
          operation probe(xs: List[T = Int64]) -> Int64 = xs.map(lambda x -> x).size()
        end
    "#);
    assert!(errs.is_empty(),
        "`xs.map(f).size()` over a finite source must stay consumable; \
         got: {errs:?}");
}

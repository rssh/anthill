//! WI-516 — graded-effect-row representation bug.
//!
//! An effect-set carried as a type parameter is represented inconsistently
//! between a braced row LITERAL position (`E = {E1, E2}` reads its vars as a
//! merge of OPEN TAILS) and forced/`effects` position (a performed captured
//! effect reads as a PRESENT LABEL). The two do not unify, so the graded
//! `DelayMonad` instance's `flatMap` body cannot conform to its declared
//! `E = {E1, E2}` return.
//!
//! These tests reconstruct the blocked `Delay` instance (stdlib
//! `anthill.prelude.delay`, proposal 047 §8) as a user source loaded over the
//! full stdlib. Nullary thunks use `lambda () -> body` (the typed-binder form
//! the spec used to show, `lambda (u: Unit) -> …`, does not parse — WI-517).

/// PRIMARY: with the secondary nested-arg effect-drop worked around by a `let`,
/// the only remaining failure is the present-label-vs-open-tail mismatch in the
/// `{E1, E2}` merge. This is the core acceptance criterion.
#[test]
fn delay_flatmap_let_workaround_conforms() {
    const SRC: &str = r#"
enum wi516.delay.Delay
  import anthill.prelude.{DelayMonad, Unit}

  sort T = ?
  sort E = ?
  entity delayed(thunk: () -> T @ E)

  operation delayPure[A](a: A) -> Delay[T = A, E = {}] =
    delayed(lambda () -> a)

  operation delayDelay[A, EffP](thunk: () -> A @ EffP) -> Delay[T = A, E = EffP] =
    delayed(thunk)

  operation delayForce[A, Eff](m: Delay[T = A, E = Eff]) -> A effects Eff =
    match m
      case delayed(t) -> t()

  operation delayFlatMap[A, B, E1, E2](m: Delay[T = A, E = E1], f: (A) -> Delay[T = B, E = E2]) -> Delay[T = B, E = {E1, E2}] =
    delayed(lambda () ->
      let a = delayForce(m)
      delayForce(f(a)))

  fact DelayMonad[M = Delay, pure = delayPure, delay = delayDelay, flatMap = delayFlatMap, force = delayForce]
end
"#;
    if let Err(errs) = crate::common::try_load_kb_with(SRC) {
        for e in &errs {
            eprintln!("{e}");
        }
        panic!("delay instance (let workaround) failed to load: {} errors", errs.len());
    }
}

/// SECONDARY: the nested argument-position call `delayForce(f(delayForce(m)))`
/// must accumulate `{E1, E2}` without the `let`. Today the inner `delayForce(m)`
/// argument-evaluation effect is dropped.
#[test]
fn delay_flatmap_nested_arg_accumulates_effects() {
    const SRC: &str = r#"
enum wi516.delaynest.Delay
  import anthill.prelude.{DelayMonad, Unit}

  sort T = ?
  sort E = ?
  entity delayed(thunk: () -> T @ E)

  operation delayPure[A](a: A) -> Delay[T = A, E = {}] =
    delayed(lambda () -> a)

  operation delayDelay[A, EffP](thunk: () -> A @ EffP) -> Delay[T = A, E = EffP] =
    delayed(thunk)

  operation delayForce[A, Eff](m: Delay[T = A, E = Eff]) -> A effects Eff =
    match m
      case delayed(t) -> t()

  operation delayFlatMap[A, B, E1, E2](m: Delay[T = A, E = E1], f: (A) -> Delay[T = B, E = E2]) -> Delay[T = B, E = {E1, E2}] =
    delayed(lambda () -> delayForce(f(delayForce(m))))

  fact DelayMonad[M = Delay, pure = delayPure, delay = delayDelay, flatMap = delayFlatMap, force = delayForce]
end
"#;
    if let Err(errs) = crate::common::try_load_kb_with(SRC) {
        for e in &errs {
            eprintln!("{e}");
        }
        panic!("delay instance (nested arg) failed to load: {} errors", errs.len());
    }
}

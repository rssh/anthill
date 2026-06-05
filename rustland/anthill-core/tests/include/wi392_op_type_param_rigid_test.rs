//! WI-392 — an operation's OWN declared type parameters are RIGID (Skolem)
//! while checking its body, so a call inside the body whose type parameter
//! resolves (through unification with an argument) to one of them is NOT a
//! false "unconstrained" leak.
//!
//! Before WI-392, `rewrap[A](b: Box[T = A]) -> Box[T = A] = idbox(b)` failed to
//! load: `idbox`'s flexible `A` resolved to `rewrap`'s own `A`, an unbound
//! `Var::Global`, which `check_unconstrained_type_params` reported as
//! "unconstrained — use `idbox[A = …](…)`". Skolemizing `rewrap`'s `A` to a
//! `Var::Rigid` while checking its body makes that resolution land on a rigid
//! (which the check passes, since it flags only bare `Global`s), while keeping
//! the body sound — it may USE `A` but never CONSTRAIN it.
//!
//! This is the typer prerequisite for WI-380 (rewriting the abstract `Stream`
//! ops `collect`/`takeN`/… to explicit `[Elem, Eff]` parameters): their default
//! bodies call `splitFirst` and recurse on themselves at the enclosing element
//! and effect parameters — exactly this pattern.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

fn load_errors(src: &str) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let s = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&s).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    parsed.push(parse::parse(src).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

/// A body calling ANOTHER type-parameterized op, with the callee's type param
/// resolving to the enclosing op's own declared `A`.
#[test]
fn cross_op_call_threads_enclosing_type_param() {
    let src = r#"
namespace test.wi392.cross
  sort Box
    sort T = ?
    operation idbox[A](b: Box[T = A]) -> Box[T = A] = b
    operation rewrap[A](b: Box[T = A]) -> Box[T = A] = idbox(b)
  end
end
"#;
    let errs = load_errors(src);
    assert!(
        errs.is_empty(),
        "rewrap[A](b) = idbox(b): idbox's A resolves to rewrap's own (rigid) A — \
         that is constrained-by-quantification, not an unconstrained leak; got: {errs:?}",
    );
}

/// A SELF-recursive body: the callee IS the enclosing op, so the recursive
/// call's type param resolves to the enclosing (rigid) `A`.
#[test]
fn self_recursive_call_threads_enclosing_type_param() {
    let src = r#"
namespace test.wi392.selfrec
  sort Box
    sort T = ?
    operation drain[A](b: Box[T = A]) -> Box[T = A] = drain(b)
  end
end
"#;
    let errs = load_errors(src);
    assert!(
        errs.is_empty(),
        "drain[A](b) = drain(b): the recursive call's A resolves to drain's own \
         (rigid) A — not an unconstrained leak; got: {errs:?}",
    );
}

/// The EFFECT type parameter threads too — `collect`'s actual shape carries
/// `Eff` in the *parameterized carrier type* (`Strm[E = Eff]`), so a recursive
/// call pins the callee's `Eff` from the argument's `E =` binding (not from an
/// `effects` clause alone). This is the WI-380 `collect[Elem, Eff]` pattern, and
/// it exercises the rigidified *effect-row* parameter (`declared_effects`).
#[test]
fn effect_type_param_threads_via_carrier_param_type() {
    let src = r#"
namespace test.wi392.eff
  sort Strm
    import anthill.prelude.EffectsRuntime
    sort T = ?
    effects E = ?
    operation peel[Elem, Eff](s: Strm[T = Elem, E = Eff]) -> Strm[T = Elem, E = Eff]
      effects Eff = peel(s)
  end
end
"#;
    let errs = load_errors(src);
    assert!(
        errs.is_empty(),
        "peel[Elem, Eff](s: Strm[T=Elem, E=Eff]) -> Strm[T=Elem, E=Eff] effects Eff \
         = peel(s): the recursive call pins Eff from s's `E =` binding to the \
         enclosing rigid Eff; the rigid effect row is checked, not bound; got: {errs:?}",
    );
}

/// Regression GUARD (not a rigid-vs-flexible discriminator): returning
/// `b : Box[T = A]` where `Box[T = Int]` is declared must stay REJECTED.
/// The operation-return check (`types_compatible`) is invariant in `Box.T`, so
/// it rejects `Box[T = A]` vs `Box[T = Int]` whether `A` is rigid or flexible —
/// this does not isolate the fix (the three cases above do that). Its job is to
/// pin that rigidifying the return type did not accidentally make an ill-typed
/// return pass (e.g. if rigid comparison were too loose).
#[test]
fn ill_typed_return_stays_rejected_with_rigid_param() {
    let src = r#"
namespace test.wi392.sound
  import anthill.prelude.Int
  sort Box
    sort T = ?
    operation widen[A](b: Box[T = A]) -> Box[T = Int] = b
  end
end
"#;
    let errs = load_errors(src);
    assert!(
        !errs.is_empty(),
        "widen[A](b: Box[T = A]) -> Box[T = Int] = b must be rejected: Box[T = A] \
         is not Box[T = Int] (invariant in Box.T); loaded clean instead",
    );
}

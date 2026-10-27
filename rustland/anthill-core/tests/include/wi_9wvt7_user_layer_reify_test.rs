//! WI-20260908-9WVT7 — A USER EFFECT LAYER'S `reify` WITH NOTHING TO RUN IS REFUSED AT THE
//! CALL. The runtime's boundary is `Error.reify`'s; a sort of the program declaring its own
//! body-less `reify[Rho, X, T1](body: () -> X @ {Err2[T1], Rho})` loaded, and a call of it died
//! "operation has no body: Err2.reify" when it ran — with no provider of `Err2`, and beside one
//! that supplies `reify`, since a call naming no instance is not dispatched to a provider.
//!
//! WI-20260909-M8QWJ's call check refuses a call of a member nothing can run, and let a
//! signature with type parameters through: a parameter written as an application of a
//! higher-kinded parameter (`m: M[A]` in `sort Monad[M[T]]`) lets a value direct the call to
//! a provider. Now only such a signature, of a sort something provides, is let through.
//!
//! ── WHICH ROWS FAIL WHEN EACH PART IS BACKED OUT ── measured 2026-10-27, each alone ──
//!
//! * The escape narrowed to a signature applying a higher-kinded parameter of a provided sort
//!   (`unselectable_spec_operation_call`): `with_no_provider_the_call_is_refused` and
//!   `beside_a_provider_the_call_is_refused_naming_the_bracket`, which load. Narrowed further,
//!   to a parameter alone, `wi453_hk_concrete_fill_test`'s result-applied `unit(42)` is
//!   refused.
//! * The refusal's account of a sort nothing provides (`provided`): the text of
//!   `with_no_provider_the_call_is_refused`.
//!
//! * The higher-kinded parameter found anywhere in a parameter's type, not at its head alone:
//!   `a_value_inside_a_higher_kinded_application_still_directs_the_call`, refused.
//!
//! PASS EITHER WAY BY DESIGN: `the_bracket_reaches_the_providers_reify`, the repair the
//! refusal advises, and `the_preludes_error_reify_still_runs`.

use anthill_core::eval::Value;

fn program(provider: &str, call: &str) -> String {
    format!(
        r#"
namespace test.userreify
  import anthill.prelude.{{Int64, String, Nothing, Effect, todo}}

  enum Result
    sort E = ?
    sort T = ?
    entity ok(value: T)
    entity err(error: E)
  end

  sort Boom
    entity boom(why: String)
  end

  sort Err2
    import anthill.prelude.{{Nothing, Effect}}
    import test.userreify.{{Result}}
    sort T = ?
    operation raise(error: T) -> Nothing effects Err2[T]
    operation reify[Rho, X, T1](body: () -> X @ {{Err2[T1], Rho}}) -> Result[E = T1, T = X]
      effects {{Rho}}
    provides Effect[T = Self]
  end
{provider}
  operation mayFail(n: Int64) -> Int64 effects {{Err2[Boom]}} = 41

  operation c(n: Int64) -> Result[E = Boom, T = Int64] = {call}
end
"#
    )
}

const PROVIDER: &str = r#"
  sort Impl
    import test.userreify.{Result, Err2}
    provides Err2[T = Boom]
    operation raise(error: Boom) -> Nothing effects Err2[Boom] = raise(error)
    operation reify[Rho, X, T1](body: () -> X @ {Err2[T1], Rho}) -> Result[E = T1, T = X]
      effects {Rho} = todo()
  end
"#;

const CALL: &str = "Err2.reify(lambda () -> mayFail(n))";

/// No sort provides `Err2`: the call reaches `Err2.reify` itself, and the refusal says that
/// nothing provides it, advising no bracket. The declaration alone loads.
#[test]
fn with_no_provider_the_call_is_refused() {
    let errs = crate::common::load_errors_of(&program("", CALL));
    assert_eq!(errs.len(), 1, "one refusal, the call's; got {errs:#?}");
    crate::common::assert_refused_naming(
        &errs,
        &[
            "a call of `test.userreify.Err2.reify` that nothing can run",
            "nothing provides `test.userreify.Err2`",
        ],
        "a user layer's reify with no provider",
    );
    assert!(!errs[0].contains("bracket"), "no bracket can name an instance: {errs:#?}");
    let declared_only = crate::common::load_errors_of(&program("", "ok(value: n)"));
    assert!(declared_only.is_empty(), "the declaration alone loads: {declared_only:#?}");
}

/// A provider that supplies `reify` does not make the call run: it names no instance, so it
/// still reaches `Err2.reify`. The refusal names the bracket.
#[test]
fn beside_a_provider_the_call_is_refused_naming_the_bracket() {
    let errs = crate::common::load_errors_of(&program(PROVIDER, CALL));
    crate::common::assert_refused_naming(
        &errs,
        &[
            "a call of `test.userreify.Err2.reify` that nothing can run",
            "Name the instance in the call's bracket",
        ],
        "a user layer's reify beside a provider",
    );
}

/// The advised repair: the bracket names `Impl`'s instance, and the call runs `Impl.reify`,
/// whose body is the hole.
#[test]
fn the_bracket_reaches_the_providers_reify() {
    let mut interp = crate::common::interp_for(&program(
        PROVIDER,
        "Err2.reify[T = Boom](lambda () -> mayFail(n))",
    ));
    match interp.call("test.userreify.c", &[Value::Int(1)]) {
        Err(e) => assert!(
            format!("{e}").contains("test.userreify.Impl.reify"),
            "the run reaches Impl's reify: {e}"
        ),
        Ok(v) => panic!("Impl's reify is the hole; got {v:?}"),
    }
}

/// CONTROL: the runtime's own boundary loads and catches.
#[test]
fn the_preludes_error_reify_still_runs() {
    let mut interp = crate::common::interp_for(
        r#"
namespace test.preludereify
  import anthill.prelude.{Int64, String, Error, Result}
  import anthill.prelude.Result.{ok, err}
  sort Boom
    entity boom(why: String)
  end
  operation mayFail(n: Int64) -> Int64 effects {Error[Boom]} = Error.raise(boom(why: "x"))
  operation c(n: Int64) -> Int64 =
    match Error.reify(lambda () -> mayFail(n))
      case ok(_) -> 1
      case err(_) -> 2
end
"#,
    );
    let v = interp.call("test.preludereify.c", &[Value::Int(1)]).expect("runs");
    assert!(matches!(v, Value::Int(2)), "caught; got {v:?}");
}

/// A call through a higher-kinded parameter keeps its dispatch: `ms: List[T = M[A]]` holds an
/// application of `M`, and the value of `ms` directs the call to `Option`'s provision (5);
/// `m: M[A]` beside it (6).
#[test]
fn a_value_inside_a_higher_kinded_application_still_directs_the_call() {
    let mut interp = crate::common::interp_for(
        r#"
namespace test.hknest
  import anthill.prelude.{Int64, List, Option}
  import anthill.prelude.Option.{some}
  sort Cnt[M[T]]
    operation count[A](ms: List[T = M[A]]) -> Int64
    operation one[A](m: M[A]) -> Int64
  end
  operation optCount[A](ms: List[T = Option[T = A]]) -> Int64 = 5
  operation optOne[A](m: Option[T = A]) -> Int64 = 6
  operation r() -> Int64 = Cnt.count([some(1)]) * 10 + Cnt.one(some(1))
end

namespace anthill.prelude.Option
  import test.hknest.Cnt
  provides Cnt[M = Self, count = test.hknest.optCount, one = test.hknest.optOne]
end
"#,
    );
    let v = interp.call("test.hknest.r", &[]).expect("runs");
    assert!(matches!(v, Value::Int(56)), "both calls reach Option's members; got {v:?}");
}

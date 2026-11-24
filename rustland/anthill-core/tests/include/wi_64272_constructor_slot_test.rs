//! WI-20261113-64272 — proposal 074 stage 8, PART 1: A CONSTRUCTOR AT A HIGHER-KINDED SLOT
//! (`docs/proposals/074-typeclass-instance-is-a-dictionary.md` §6, H4's rule; kernel-language
//! §5.4).
//!
//! A sort written at a higher-kinded parameter's slot (`M` of `sort Mon[M[T]]`) is a CONSTRUCTOR:
//! the sort with the parameters it writes, over the ones it leaves open, which take the slot's
//! arguments in declaration order, their count the same. `M[T = A]` with `M = Box` (`sort V = ?`)
//! is `Box[V = A]`, and with `M = Pair[A = Int64]` is `Pair[A = Int64, B = A]`. Before the stage:
//! the slot's keys were matched by name, so `provides Mon[M = Box]` was refused ("the member
//! returns `Box[V = ?A]`, which is not a subtype of the spec's `M[T = ?A]`"); a call's bracket
//! `[M = Option]` was expanded to the type `Option[T = ?]` and filled nothing (`Mon.pure[M =
//! Option](7)` typed `M[T = Int64]`); and `Pair[A = Int64]` at the slot was expanded too.
//!
//! Decided with the user 2026-11-24, writing the part: a provider at its own parameters
//! (`provides Monad[M = Self]`, `Option[T = T]`, `Result[E = E, T = T]`) writes a type, not a
//! constructor, and is refused naming the constructor (`Option`, `Result[E = E]`) — the
//! standard library's three such provisions and the fixtures were rewritten; and where an
//! argument fits two constructors (`Result[E = Boom, T = Int64]` is `Result[E = Boom]` over `T`
//! and `Result[T = Int64]` over `E`), a spec's own parameter is fixed by the constructors its
//! provisions write.
//!
//! CONTROLS — the back-out ledger at the end of this file.

use anthill_core::eval::Interpreter;

use crate::common::{interp_for, load_errors_of, show_value};

fn call(interp: &mut Interpreter, op: &str) -> String {
    match interp
        .call(op, &anthill_core::eval::HostValue::all(&[]))
        .map(|h| h.value)
    {
        Ok(v) => show_value(interp.kb(), &v),
        Err(e) => panic!("`{op}`: {e:?}"),
    }
}

/// A spec over a constructor, and its providers at `Option` and `List`.
const MON: &str = "
  sort Mon[M[T]]
    operation pure[A](a: A) -> M[T = A]
  end
  sort OptionMon
    provides Mon[M = Option]
    operation pure[A](a: A) -> Option[T = A] = some(a)
  end
  sort ListMon
    provides Mon[M = List]
    operation pure[A](a: A) -> List[T = A] = [a]
  end
";

/// `Box`, whose one parameter is `V`, and its provider.
const BOX: &str = "
  sort Box
    sort V = ?
    entity box(v: V)
  end
  sort BoxMon
    provides Mon[M = Box]
    operation pure[A](a: A) -> Box[V = A] = box(v: a)
  end
";

fn program(ns: &str, decls: &str, body: &str) -> String {
    format!(
        "namespace p074s8.{ns}\n  import anthill.prelude.{{Int64, String, Option, List, Pair}}\n  import anthill.prelude.Option.{{some, none}}\n{MON}{decls}{body}\nend\n"
    )
}

fn answers(ns: &str, decls: &str, body: &str, ops: &[(&str, &str)]) {
    let mut interp = interp_for(&program(ns, decls, body));
    for (op, want) in ops {
        assert_eq!(
            call(&mut interp, &format!("p074s8.{ns}.{op}")),
            *want,
            "{op}"
        );
    }
}

fn refusal(ns: &str, decls: &str, body: &str) -> String {
    let errors = load_errors_of(&program(ns, decls, body));
    assert!(!errors.is_empty(), "{ns}: expected a refusal");
    errors.join("\n")
}

// ── The constructor a bracket and an expected type fix ───────────────────────────────────

/// A call's bracket fixes the constructor: `Mon.pure[M = Option](7)` is `Option[T = Int64]`.
/// MEASURED before: typed `M[T = Int64]`, and refused at the result.
#[test]
fn a_bracket_fixes_the_constructor() {
    let body = "  operation viaOption() -> Option[T = Int64] = Mon.pure[M = Option](7)
  operation viaList() -> List[T = Int64] = Mon.pure[M = List](7)
  operation both() -> (Option[T = Int64], List[T = Int64]) = (Mon.pure[M = Option](7), Mon.pure[M = List](7))";
    answers(
        "bracket",
        "",
        body,
        &[
            ("viaOption", "some(value: 7)"),
            ("viaList", "[7]"),
            ("both", "(some(value: 7), [7])"),
        ],
    );
}

/// CONTROL, passes either way by design: the expected type fixed `Option` and `List` before the
/// stage too, their parameter being named `T` as the slot's is.
#[test]
fn an_expected_type_fixes_a_constructor_named_alike() {
    let body = "  operation go() -> (Option[T = Int64], List[T = Int64]) =
    let o: Option[T = Int64] = Mon.pure(7)
    let l: List[T = Int64] = Mon.pure(7)
    (o, l)";
    answers("expected", "", body, &[("go", "(some(value: 7), [7])")]);
}

// ── By order, not by name ─────────────────────────────────────────────────────────────────

/// `Box`'s parameter is `V`, the slot's `T`: by order, `provides Mon[M = Box]` loads and its
/// member answers through the bracket and through the expected type, a lambda typed from it.
/// MEASURED before: the provision was refused, "the member returns `Box[V = ?A]`, which is not
/// a subtype of the spec's `M[T = ?A]`".
#[test]
fn a_constructor_fills_by_order_not_by_name() {
    let body = "  operation viaBracket() -> Box[V = Int64] = Mon.pure[M = Box](7)
  operation viaExpected() -> Box[V = Int64] =
    let b: Box[V = Int64] = Mon.pure(7)
    b
  operation viaLambda() -> Int64 =
    let b: Box[V = (x: Int64) -> Int64] = Mon.pure(lambda (x) -> x + 1)
    match b
      case box(f) -> f(41)";
    answers(
        "byorder",
        BOX,
        body,
        &[
            ("viaBracket", "box(v: 7)"),
            ("viaExpected", "box(v: 7)"),
            ("viaLambda", "42"),
        ],
    );
}

/// A partial constructor: `Pair[A = Int64]` is `Pair` over `B`. Through the bracket, and
/// through the expected type `Pair[A = Int64, B = Int64]` — which fits `Pair[A = Int64]` and
/// `Pair[B = Int64]`, and the provision's constructor chooses. MEASURED before: the provision was
/// refused, its binding expanded to `Pair[A = Int64, B = ?]`.
#[test]
fn a_partial_constructor_is_the_sort_over_what_it_leaves_open() {
    let decls = "
  sort PairMon
    provides Mon[M = Pair[A = Int64]]
    operation pure[X](a: X) -> Pair[A = Int64, B = X] = Pair.pair(fst: 0, snd: a)
  end
";
    let body =
        "  operation viaBracket() -> Pair[A = Int64, B = Int64] = Mon.pure[M = Pair[A = Int64]](7)
  operation viaExpected() -> Pair[A = Int64, B = Int64] =
    let p: Pair[A = Int64, B = Int64] = Mon.pure(7)
    p";
    answers(
        "partial",
        decls,
        body,
        &[
            ("viaBracket", "pair(fst: 0, snd: 7)"),
            ("viaExpected", "pair(fst: 0, snd: 7)"),
        ],
    );
}

/// The standard library's `Result`: `provides Monad[M = Result[E = E]]` leaves the success type
/// open. A `Result[E = Boom, T = Int64]` fits two constructors, and the provision chooses, so
/// `Monad.map` maps the success.
#[test]
fn a_spec_call_whose_argument_fits_two_constructors_takes_the_provisions() {
    let src = "namespace p074s8.result
  import anthill.prelude.{Int64, String, Monad, Result}
  import anthill.prelude.Result.{ok}
  sort Boom
    entity boom(why: String)
  end
  operation go() -> Result[E = Boom, T = Int64] =
    let r: Result[E = Boom, T = Int64] = ok(value: 41)
    Monad.map(r, lambda (x: Int64) -> x * 2)
end
";
    let mut interp = interp_for(src);
    assert_eq!(call(&mut interp, "p074s8.result.go"), "ok(value: 82)");
}

// ── Refused where it is written ───────────────────────────────────────────────────────────

/// A constructor whose open parameters are not as many as the slot's is refused at the
/// provision: `Pair` leaves two, `Option[T = Int64]` none. MEASURED before: refused only where
/// the member was compared, naming the member and not the clause.
#[test]
fn a_constructor_of_another_arity_is_refused_at_the_provision() {
    let text = refusal(
        "twoopen",
        "
  sort PM
    provides Mon[M = Pair]
    operation pure[X](a: X) -> Pair[A = X, B = X] = Pair.pair(fst: a, snd: a)
  end
",
        "",
    );
    assert!(
        text.contains("`provides Mon[M = Pair]` in 'p074s8.twoopen.PM': `M` is a constructor of 1 parameter (`M[T]`)")
            && text.contains("`Pair` leaves `A`, `B`")
            && text.contains("`provides Mon[M = Pair[A = …]]`"),
        "{text}"
    );
    let text = refusal(
        "noneopen",
        "
  sort OM
    provides Mon[M = Option[T = Int64]]
    operation pure[X](a: X) -> Option[T = Int64] = some(1)
  end
",
        "",
    );
    assert!(text.contains("`Option[T = Int64]` leaves none"), "{text}");
}

/// A provider at its own parameters writes a type, and is refused naming the constructor it
/// meant (decided with the user 2026-11-24): `Self` in `Box2` is `Box2[V = V]`, meant `Box2`;
/// `R2[E = E, T = T]` meant `R2[E = E]`, and `R3[T = T, E = E]` meant `R3[E = E]`.
#[test]
fn a_provider_at_its_own_parameters_is_refused_naming_the_constructor() {
    let decls = "
  sort Box2
    sort V = ?
    entity b2(v: V)
    provides Mon[M = Self]
    operation pure[A](a: A) -> Box2[V = A] = b2(v: a)
  end
  sort R2
    sort E = ?
    sort T = ?
    entity r2(t: T)
    provides Mon[M = R2[E = E, T = T]]
    operation pure[A](a: A) -> R2[E = E, T = A] = r2(t: a)
  end
  sort R3
    sort T = ?
    sort E = ?
    entity r3(t: T)
    provides Mon[M = R3[T = T, E = E]]
    operation pure[A](a: A) -> R3[T = A, E = E] = r3(t: a)
  end
";
    let text = refusal("own", decls, "");
    assert!(
        text.contains("`Box2[V = V]` is 'p074s8.own.Box2' at its own parameters and leaves none — write the constructor, `provides Mon[M = Box2]`")
            && text.contains("write the constructor, `provides Mon[M = R2[E = E]]`")
            // The parameter named as the slot's is the one meant open, wherever it is declared
            // (found by /code-review: `R3[T = T]` was suggested, leaving `E` open).
            && text.contains("write the constructor, `provides Mon[M = R3[E = E]]`"),
        "{text}"
    );
}

/// A bracket's constructor of another arity is refused at the call, as at a provision.
/// MEASURED before: refused at the dispatch, "no impl matches".
#[test]
fn a_bracket_constructor_of_another_arity_is_refused_at_the_call() {
    let text = refusal(
        "bracketarity",
        "",
        "  operation go() -> Int64 =
    let p = Mon.pure[M = Pair](7)
    0",
    );
    assert!(
        text.contains("expected a constructor of 1 parameter at `M` (`M[T]`)")
            && text.contains("got `Pair`, which leaves `A`, `B`"),
        "{text}"
    );
    // The receiver's bracket, too (found by /code-review: refused only at the dispatch).
    let text = refusal(
        "recvarity",
        "",
        "  operation go() -> Int64 =
    let p = Mon[M = Pair].pure(7)
    0",
    );
    assert!(
        text.contains("expected a constructor of 1 parameter at `M` (`M[T]`)")
            && text.contains("got `Pair`, which leaves `A`, `B`"),
        "{text}"
    );
}

/// A result the constructor does not make is refused. Not a control: with the fill by name
/// (back-out p1b) `Mon.pure[M = Box](7)` read `Box[T = Int64]`, and the refusal named that.
#[test]
fn a_result_the_constructor_does_not_make_is_refused() {
    let text = refusal(
        "wrong",
        BOX,
        "  operation go() -> Box[V = String] = Mon.pure[M = Box](7)",
    );
    assert!(text.contains("expected Box[V = String]"), "{text}");
}

// ── Back-out ledger ───────────────────────────────────────────────────────────────────────
//
// MEASURED 2026-11-24: each piece backed out by a temporary switch, every row of anthill-core
// run (control 11653 passed, 0 failed). The standard library's rewritten provisions
// (`Monad[M = Option]`, `Monad[M = Result[E = E]]`, `DelayMonad[M = Delay]`) stay in every run,
// so a piece they need fails the rows that read them.
//
// p1a, a bracket's constructor bound as written (`bracket_value_to_bind`): 4 rows —
// `a_bracket_fixes_the_constructor`, `a_constructor_fills_by_order_not_by_name`,
// `a_partial_constructor_is_the_sort_over_what_it_leaves_open`,
// `a_bracket_constructor_of_another_arity_is_refused_at_the_call`.
//
// p1b, the fill by order (`apply_constructor`): 24 rows — `a_constructor_fills_by_order_not_by_name`,
// `a_partial_constructor_is_the_sort_over_what_it_leaves_open`,
// `a_result_the_constructor_does_not_make_is_refused`,
// `a_spec_call_whose_argument_fits_two_constructors_takes_the_provisions`, and the 20 rows of
// `wi_9wvt7_error_reify_test` (`Result`'s monad, at `Result[E = E]`).
//
// p1d, unification by order (`unify_constructor_application`): 22 rows —
// `a_partial_constructor_is_the_sort_over_what_it_leaves_open`,
// `a_spec_call_whose_argument_fits_two_constructors_takes_the_provisions`, and the 20 rows of
// `wi_9wvt7_error_reify_test`.
//
// p1e, the arity refusals at a provision and a bracket (`check_provision_constructors`,
// `seed_bracket_bindings`): 4 rows — `a_constructor_of_another_arity_is_refused_at_the_provision`,
// `a_provider_at_its_own_parameters_is_refused_naming_the_constructor`,
// `a_bracket_constructor_of_another_arity_is_refused_at_the_call`, and wi_xgrkz's
// `a_binding_of_another_kind_is_not_applied`.
//
// A fifth piece, a constructor left unexpanded by `expand_application` and the member check's
// template, failed no row backed out, unification by order covering what it was written for;
// it was removed.
//
// Passes under every piece by design: `an_expected_type_fixes_a_constructor_named_alike`.

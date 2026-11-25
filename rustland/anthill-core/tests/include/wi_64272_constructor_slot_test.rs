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
        "namespace p074s8.{ns}\n  import anthill.prelude.{{Int64, String, Option, List, Pair, Additive, Type, Bool, Map, PartialEq}}\n  import anthill.prelude.Option.{{some, none}}\n  import anthill.reflect.{{TypeValue}}\n  import anthill.realization.runtime.Dictionary\n{MON}{decls}{body}\nend\n"
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

// ── Part 2: a requirement's constructor, read through it ─────────────────────────────────

/// A sort over a constructor that requires the spec at it: inside `UseM`, `Mon.pure(x)` is at
/// `M = F`, so `M[Int64]` reads `F[Int64]`, and a call at `F = Option` answers through
/// `OptionMon`. MEASURED before part 2: refused, "expected F[T = Int64], got M[T = Int64]".
#[test]
fn a_requirement_at_a_constructor_parameter_is_read_through_it() {
    let decls = "
  sort UseM[F[T]]
    requires Mon[M = F]
    operation lift(x: Int64) -> F[Int64] = Mon.pure(x)
  end
";
    let body = "  operation viaOption() -> Option[Int64] = UseM[F = Option].lift(7)
  operation viaList() -> List[Int64] = UseM[F = List].lift(7)
  operation positional() -> Option[Int64] = UseM[Option].lift(7)";
    answers(
        "usem",
        decls,
        body,
        &[
            ("viaOption", "some(value: 7)"),
            ("viaList", "[7]"),
            ("positional", "some(value: 7)"),
        ],
    );
}

/// H4: a provider over a constructor, whose provision's constructor writes its own parameter
/// (`OptionT[F = F]`, over `T`) and whose member calls the spec at `F` — through the bracket,
/// and unbracketed, `M` fixed by the expected type `F[Option[A]]`. `F = List` and `F = Option`
/// each answer through their own provider. MEASURED before the stage: `pure`'s body refused,
/// "`Mon[M = OptionTMonad.F[T = ?]]` cannot be supplied" (the bracketed spelling, answered by
/// part 1); the unbracketed one was refused as `UseM` was.
#[test]
fn h4_a_provider_over_a_constructor_reads_the_constructors_provider() {
    let decls = "
  sort OptionT[F[T]]
    sort T = ?
    entity optT(run: F[Option[T]])
  end
  sort OptionTMon[F[T]]
    requires Mon[M = F]
    provides Mon[M = OptionT[F = F]]
    operation pure[A](a: A) -> OptionT[F = F, T = A] = optT(run: Mon.pure[M = F](some(a)))
  end
  sort OptionT2[F[T]]
    sort T = ?
    entity optT2(run: F[Option[T]])
  end
  sort OptionT2Mon[F[T]]
    requires Mon[M = F]
    provides Mon[M = OptionT2[F = F]]
    operation pure[A](a: A) -> OptionT2[F = F, T = A] = optT2(run: Mon.pure(some(a)))
  end
";
    let body = "  operation overList() -> OptionT[F = List, T = Int64] = Mon.pure[M = OptionT[F = List]](7)
  operation overOption() -> OptionT[F = Option, T = Int64] = Mon.pure[M = OptionT[F = Option]](7)
  operation unbracketed() -> OptionT2[F = List, T = Int64] = Mon.pure[M = OptionT2[F = List]](7)";
    answers(
        "optiont",
        decls,
        body,
        &[
            ("overList", "optT(run: [some(value: 7)])"),
            ("overOption", "optT(run: some(value: some(value: 7)))"),
            ("unbracketed", "optT2(run: [some(value: 7)])"),
        ],
    );
}

/// A call of a spec's own operation in its own body, placed at ANOTHER instance than the
/// body's, is refused at load (decided with the user 2026-11-25): the body is handed the provider
/// of its own instance alone. MEASURED before: both ran the caller's provider at the wrong types,
/// `Box.confused[F = Option, G = List](7)` answering `[7]` where `Option` is declared, and the
/// plain twin `"s"` where `Int64` is (WI-80ZV8's known issue (a)); part 2 had made the
/// higher-kinded one load where it was refused by luck.
#[test]
fn a_sibling_call_at_another_instance_is_refused() {
    let text = refusal(
        "sibhk",
        "
  sort Box[F[T], G[T]]
    operation wrapG[A](a: A) -> G[A]
    operation confused[A](a: A) -> F[A] = wrapG(a)
  end
",
        "",
    );
    assert!(
        text.contains("`wrapG` at `Box[G = F]`, another instance")
            && text.contains("nothing hands one at that"),
        "{text}"
    );
    let text = refusal(
        "sibplain",
        "
  sort Box2
    sort F = ?
    sort G = ?
    operation wrapG(a: Int64) -> G
    operation confused(a: Int64) -> F = wrapG(a)
  end
",
        "",
    );
    assert!(
        text.contains("`wrapG` at `Box2[G = F]`, another instance"),
        "{text}"
    );
}

/// CONTROL, passes either way by design: a sibling call at the body's own instance answers
/// through the body's provider, and one at another instance that a requirement hands answers
/// through that provider.
#[test]
fn a_sibling_call_at_the_bodys_instance_or_a_required_one_answers() {
    let decls = "
  sort Box2
    sort F = ?
    sort G = ?
    operation wrapG(a: Int64) -> G
    operation again(a: Int64) -> G = wrapG(a)
    operation viaReq(a: Int64) -> F requires Box2[F = F, G = F] = wrapG(a)
  end
  sort IS
    provides Box2[F = Int64, G = String]
    operation wrapG(a: Int64) -> String = \"s\"
  end
  sort II
    provides Box2[F = Int64, G = Int64]
    operation wrapG(a: Int64) -> Int64 = a + 1
  end
";
    let body = "  operation goAgain() -> String = Box2.again[F = Int64, G = String](7)
  operation goReq() -> Int64 = Box2.viaReq[F = Int64, G = String](7)";
    answers(
        "sibok",
        decls,
        body,
        &[("goAgain", "\"s\""), ("goReq", "8")],
    );
}

// ── Part 3: an operation's higher-kinded parameter ───────────────────────────────────────

/// H2: an operation declares a higher-kinded parameter with the sort's spelling, and a call
/// fixes it as any type parameter — by its bracket, by position, by the type its result is
/// expected at; `Box`'s `V` takes `F`'s `T` by order. MEASURED before: `[F[T]]` in an
/// operation's bracket was a syntax error.
#[test]
fn h2_an_operations_higher_kinded_parameter_is_fixed_as_any_parameter() {
    let body = "  operation lift[F[T]](x: Int64) -> F[Int64] requires Mon[M = F] = Mon.pure(x)
  operation viaBracket() -> Option[Int64] = lift[F = Option](7)
  operation viaPositional() -> List[Int64] = lift[List](7)
  operation viaExpected() -> Option[Int64] =
    let o: Option[Int64] = lift(7)
    o
  operation viaBox() -> Box[Int64] =
    let b: Box[Int64] = lift(7)
    b";
    answers(
        "h2",
        BOX,
        body,
        &[
            ("viaBracket", "some(value: 7)"),
            ("viaPositional", "[7]"),
            ("viaExpected", "some(value: 7)"),
            ("viaBox", "box(v: 7)"),
        ],
    );
}

/// H2, decided with the user 2026-11-13: where a call's types fit two constructors the call is
/// refused, naming both and the bracket that picks one — `Pair[Int64, Int64]` is `F = Pair[A =
/// Int64]` over `B` and `F = Pair[B = Int64]` over `A`; neither the last parameters nor the
/// providers of the clause choose. The bracket loads. Kinds count: `Eff[E = {}, T = Int64]`
/// fits one, `F = Eff[E = {}]`, `E` being a row where `F`'s parameter takes a type. MEASURED
/// before part 3: refused "expected a type for 'F', got unconstrained", naming neither.
#[test]
fn h2_a_call_fitting_two_constructors_is_refused_and_kinds_count() {
    let decls = "
  sort PairMon
    provides Mon[M = Pair[Int64]]
    operation pure[X](a: X) -> Pair[Int64, X] = Pair.pair(fst: 0, snd: a)
  end
  sort Eff
    effects E = ?
    sort T = ?
    entity eff(v: T)
  end
  sort EffMon
    provides Mon[M = Eff[E = {}]]
    operation pure[A](a: A) -> Eff[E = {}, T = A] = eff(v: a)
  end
  operation lift[F[T]](x: Int64) -> F[Int64] requires Mon[M = F] = Mon.pure(x)
";
    let text = refusal(
        "twofit",
        decls,
        "  operation go() -> Pair[Int64, Int64] =
    let p: Pair[Int64, Int64] = lift(7)
    p",
    );
    assert!(
        text.contains(
            "`Pair[A = Int64, B = Int64]` fits `F = Pair[A = Int64]` and `F = Pair[B = Int64]`"
        ) && text.contains("`lift[F = Pair[A = Int64]](…)`"),
        "{text}"
    );
    // An ARGUMENT that fits two, too (found by /code-review). MEASURED on part 3's first code:
    // refused "expected a type for 'F', got unconstrained", naming neither.
    let text = refusal(
        "twofitarg",
        decls,
        "  operation size[F[T]](m: F[Int64]) -> Int64 = 0
  operation go() -> Int64 = size(m: Pair.pair(fst: 1, snd: 2))",
    );
    assert!(
        text.contains(
            "`Pair[A = Int64, B = Int64]` fits `F = Pair[A = Int64]` and `F = Pair[B = Int64]`"
        ) && text.contains("`size[F = Pair[A = Int64]](…)`"),
        "{text}"
    );
    let body = "  operation named() -> Pair[Int64, Int64] = lift[F = Pair[Int64]](7)
  operation byKind() -> Eff[E = {}, T = Int64] =
    let e: Eff[E = {}, T = Int64] = lift(7)
    e";
    answers(
        "onefit",
        decls,
        body,
        &[("named", "pair(fst: 0, snd: 7)"), ("byKind", "eff(v: 7)")],
    );
}

/// H3: §5.4's member spelling at a higher-kinded member — H2 with the parameter unnamed. The
/// member sugar's parameter is a constructor slot, `requires Mon[M = P]` its clause. MEASURED
/// before part 3: loaded, and `let o: Option[Int64] = lift(7)` answered `?_`, the application
/// resolving to the spec's own `M`, which nothing at a call binds.
#[test]
fn h3_the_member_spelling_at_a_higher_kinded_member() {
    let body = "  operation lift(x: Int64) -> Mon.M[Int64] = Mon.pure(x)
  operation viaOption() -> Option[Int64] =
    let o: Option[Int64] = lift(7)
    o
  operation viaList() -> List[Int64] =
    let l: List[Int64] = lift(7)
    l";
    answers(
        "h3",
        "",
        body,
        &[("viaOption", "some(value: 7)"), ("viaList", "[7]")],
    );
}

/// H3, the member sugar's other readings at the applied spelling (found by /code-review):
/// inside the spec's own declaration `Mon2.M[Int64]` is its own `M`, and in an operation's body
/// the one its signature spelled (WI-20261005-KSSA4). MEASURED on part 3's first code: both
/// refused, "expected M[T = Int64], got M[T = Int64] (these render alike …)" — the first minting
/// a parameter of its own, the second reading the spec's `M` where the signature read the
/// sugar's.
#[test]
fn h3_the_member_spelling_in_the_specs_own_body_and_an_operations_body() {
    let decls = "
  sort Mon2[M[T]]
    operation pure[A](a: A) -> M[A]
    operation twice(x: Int64) -> Mon2.M[Int64] = pure(x)
  end
  sort OptionMon2
    provides Mon2[M = Option]
    operation pure[A](a: A) -> Option[A] = some(a)
  end
";
    let body = "  operation viaOwn() -> Option[Int64] = Mon2[M = Option].twice(7)
  operation liftLet(x: Int64) -> Mon.M[Int64] =
    let m: Mon.M[Int64] = Mon.pure(x)
    m
  operation viaBody() -> Option[Int64] =
    let o: Option[Int64] = liftLet(7)
    o";
    answers(
        "h3own",
        decls,
        body,
        &[("viaOwn", "some(value: 7)"), ("viaBody", "some(value: 7)")],
    );
}

/// H3 in a carrier block that provides the spec at one constructor: the member IS that
/// constructor (WI-201's narrowing), applied — `Box`, `R2[E = E]` over `T` (the block's `E` the
/// call's), `Pair[Int64]` over `B` (found by /code-review). MEASURED on part 3's first code:
/// refused, "expected M[T = Int64], got Box[V = Int64]", the narrowing recorded and dropped.
#[test]
fn h3_the_member_spelling_in_a_carrier_block_is_its_constructor() {
    let decls = "
  sort Box
    sort V = ?
    entity box(v: V)
  end
  sort BoxMon
    provides Mon[M = Box]
    operation pure[A](a: A) -> Box[V = A] = box(v: a)
    operation lift(x: Int64) -> Mon.M[Int64] = box(v: x)
  end
  sort R2
    sort E = ?
    sort T = ?
    entity r2(t: T)
  end
  sort R2Mon[E]
    provides Mon[M = R2[E = E]]
    operation pure[A](a: A) -> R2[E = E, T = A] = r2(t: a)
    operation lift(x: Int64) -> Mon.M[Int64] = r2(t: x)
  end
  sort PairMon
    provides Mon[M = Pair[Int64]]
    operation pure[X](a: X) -> Pair[Int64, X] = Pair.pair(fst: 0, snd: a)
    operation lift(x: Int64) -> Mon.M[Int64] = Pair.pair(fst: 1, snd: x)
  end
";
    let body = "  operation viaBox() -> Box[Int64] = BoxMon.lift(7)
  operation viaR2() -> R2[E = String, T = Int64] = R2Mon[E = String].lift(7)
  operation viaPair() -> Pair[Int64, Int64] = PairMon.lift(7)";
    answers(
        "h3block",
        decls,
        body,
        &[
            ("viaBox", "box(v: 7)"),
            ("viaR2", "r2(t: 7)"),
            ("viaPair", "pair(fst: 1, snd: 7)"),
        ],
    );
}

/// A parameter of an operation's higher-kinded parameter is a type: one of its own kind
/// (`F[G[T]]`) and a default (`F[T = Int64]`) are refused where they are written — and so is a
/// default of the parameter itself (`F[T] = Option`; found by /code-review, MEASURED on part 3's
/// first code: refused at the load as "leaves a slot open", which a constructor does).
#[test]
fn an_operations_higher_kinded_parameter_takes_types_and_no_default() {
    let text = crate::common::parse_errs(&program(
        "nested",
        "",
        "  operation lift[F[G[T]]](x: Int64) -> Int64 = x",
    ))
    .join("\n");
    assert!(
        text.contains("a parameter of a higher-kinded parameter is a type"),
        "{text}"
    );
    let text = crate::common::parse_errs(&program(
        "member_default",
        "",
        "  operation lift[F[T = Int64]](x: Int64) -> Int64 = x",
    ))
    .join("\n");
    assert!(
        text.contains("a parameter of a higher-kinded parameter declares no default"),
        "{text}"
    );
    let text = crate::common::parse_errs(&program(
        "param_default",
        "",
        "  operation lift[F[T] = Option](x: Int64) -> F[Int64] requires Mon[M = F] = Mon.pure(x)",
    ))
    .join("\n");
    assert!(
        text.contains(
            "operation type parameter `F`: a higher-kinded parameter declares no default"
        ),
        "{text}"
    );
}

// ── Part 4: a dictionary of a spec over a constructor, and `m.M[Int64]` off it ─────────────

/// H1: a parameter typed at a spec over a constructor is its dictionary, and its member
/// applied, `m.M[Int64]`, is the constructor the dictionary is at — `lift(m: Mon, x: Int64) ->
/// m.M[Int64]` is `lift[P[T]](m: Mon[M = P], x: Int64) -> P[Int64]`, the call fixing `P` by
/// the dictionary it hands. In the body too, in another parameter's type, and with the result
/// unannotated. MEASURED before part 4: refused, "unresolved type name 'm.M'", and each
/// `Dictionary.instance[Mon[M = Option]]()` "leaves `M` with a slot open".
#[test]
fn h1_a_dictionary_parameters_applied_member_is_its_constructor() {
    let body = "  operation lift(m: Mon, x: Int64) -> m.M[Int64] = Mon.pure(x)
  operation inBody(m: Mon, x: Int64) -> m.M[Int64] =
    let y: m.M[Int64] = Mon.pure(x)
    y
  operation same(m: Mon, v: m.M[Int64]) -> m.M[Int64] = v
  operation viaOption() -> Option[Int64] = lift(Dictionary.instance[Mon[M = Option]](), 7)
  operation viaList() -> List[Int64] = lift(Dictionary.instance[Mon[M = List]](), 7)
  operation viaBody() -> List[Int64] = inBody(Dictionary.instance[Mon[M = List]](), 7)
  operation viaParam() -> Option[Int64] = same(Dictionary.instance[Mon[M = Option]](), some(3))
  operation viaLet() -> List[Int64] =
    let y = lift(Dictionary.instance[Mon[M = List]](), 7)
    y";
    answers(
        "h1",
        "",
        body,
        &[
            ("viaOption", "some(value: 7)"),
            ("viaList", "[7]"),
            ("viaBody", "[7]"),
            ("viaParam", "some(value: 3)"),
            ("viaLet", "[7]"),
        ],
    );
    // The dictionary decides: at `List`'s, the result is no `Option`.
    let text = refusal(
        "h1wrong",
        "",
        "  operation lift(m: Mon, x: Int64) -> m.M[Int64] = Mon.pure(x)
  operation go() -> Option[Int64] = lift(Dictionary.instance[Mon[M = List]](), 7)",
    );
    assert!(
        text.contains("expected Option[T = Int64], got List[T = Int64]"),
        "{text}"
    );
}

/// H1 where the parameter's type writes the member: `m.M[Int64]` is the constructor written
/// there, applied — `Option[Int64]`, and `Pair[Int64, Int64]` for `Pair[Int64]`. MEASURED
/// before part 4: refused, "unresolved type name 'm.M'".
#[test]
fn h1_a_member_the_parameters_type_writes_is_that_constructor() {
    let decls = "
  sort PairMon
    provides Mon[M = Pair[Int64]]
    operation pure[X](a: X) -> Pair[Int64, X] = Pair.pair(fst: 0, snd: a)
  end
";
    let body = "  operation written(m: Mon[M = Option], x: Int64) -> m.M[Int64] = Mon.pure(x)
  operation writtenPair(m: Mon[M = Pair[Int64]], x: Int64) -> m.M[Int64] = Mon.pure(x)
  operation viaOption() -> Option[Int64] = written(Dictionary.instance[Mon[M = Option]](), 7)
  operation viaPair() -> Pair[Int64, Int64] =
    writtenPair(Dictionary.instance[Mon[M = Pair[Int64]]](), 7)";
    answers(
        "h1written",
        decls,
        body,
        &[
            ("viaOption", "some(value: 7)"),
            ("viaPair", "pair(fst: 0, snd: 7)"),
        ],
    );
}

/// A dictionary or a constructor passed on: the callee's constructor is the caller's own, its
/// skolem in the caller's body — through the dictionary (`lift(d, x)` in `outer(d: Mon, …)`),
/// through the expected type (`lift2(x)` under `requires Mon[M = G]`, an operation's or its
/// sort's), and at a dictionary written there (`Dictionary.instance[Mon[M = F]]()`). Found by
/// /code-review of part 4; MEASURED before, each refused: "expected d.M[T = Int64], got m.M[T =
/// Int64]", "expected a type for 'F', got unconstrained", and "`Mon[M = ?F]` binds `M` to `?F`,
/// which leaves none open" (the plain `Dictionary.instance[Additive[T = U]]()` answering).
#[test]
fn a_constructor_passed_on_is_the_callers_own() {
    let decls = "
  operation lift(m: Mon, x: Int64) -> m.M[Int64] = Mon.pure(x)
  operation lift2[F[T]](x: Int64) -> F[Int64] requires Mon[M = F] = Mon.pure(x)
  operation take(m: Mon) -> Int64 = 1
  sort UseM[G[T]]
    requires Mon[M = G]
    operation viaLift(x: Int64) -> G[Int64] = lift2(x)
  end
";
    let body = "  operation outer(d: Mon, x: Int64) -> d.M[Int64] = lift(d, x)
  operation outer2[G[T]](x: Int64) -> G[Int64] requires Mon[M = G] = lift2(x)
  operation hk[F[T]](x: Int64) -> Int64 requires Mon[M = F] = take(Dictionary.instance[Mon[M = F]]())
  operation viaDict() -> Option[Int64] = outer(Dictionary.instance[Mon[M = Option]](), 7)
  operation viaOp() -> List[Int64] = outer2[List](7)
  operation viaSort() -> Option[Int64] = UseM[G = Option].viaLift(7)
  operation viaInstance() -> Int64 = hk[Option](7)";
    answers(
        "passedOn",
        decls,
        body,
        &[
            ("viaDict", "some(value: 7)"),
            ("viaOp", "[7]"),
            ("viaSort", "some(value: 7)"),
            ("viaInstance", "1"),
        ],
    );
}

/// The member a parameter's type writes is found as the type's own lowering keys its
/// arguments: a positional after a named one binds the next parameter it leaves —
/// `Mon2[K = Int64, Option]` writes `M`. And a written constructor holding a variable of its own
/// occurrence (`Pair[?]`) is refused, being read again at each `m.M[…]`. Found by /code-review
/// of part 4; MEASURED before: the first refused, "expected m.M[T = Int64], got Option[T =
/// Int64]" (`M` taken as unwritten, and bound twice).
#[test]
fn the_member_a_parameters_type_writes_is_found_as_its_lowering_keys_it() {
    let decls = "
  sort Mon2[K, M[T]]
    operation pure2[A](k: K, a: A) -> M[A]
  end
  sort OptionMon2
    provides Mon2[K = Int64, M = Option]
    operation pure2[A](k: Int64, a: A) -> Option[A] = some(a)
  end
";
    answers(
        "mixed",
        decls,
        "  operation lift(m: Mon2[K = Int64, Option], x: Int64) -> m.M[Int64] = Mon2.pure2(0, x)
  operation go() -> Option[Int64] = lift(Dictionary.instance[Mon2[K = Int64, M = Option]](), 7)",
        &[("go", "some(value: 7)")],
    );
    let text = refusal(
        "fresh",
        "",
        "  operation lift(m: Mon[M = Pair[?]], x: Int64) -> m.M[Int64] = Mon.pure(x)",
    );
    assert!(
        text.contains(
            "which holds a variable of its own occurrence (`?`), another at every reading"
        ),
        "{text}"
    );
}

/// A dictionary of a spec over a constructor is written at the constructor, which leaves the
/// slot's count of parameters open (H4's rule): `Dictionary.instance[Mon[M = Option]]()`, and
/// refused where the constructor leaves another count — `Pair` two, `Option[Int64]` none.
/// MEASURED before part 4: refused, "`Mon[M = Option]` leaves `M` with a slot open".
#[test]
fn a_dictionary_at_a_constructor_slot_is_written_at_the_constructor() {
    answers(
        "dict",
        "",
        "  operation take(m: Mon) -> Int64 = 1
  operation go() -> Int64 = take(Dictionary.instance[Mon[M = Option]]())",
        &[("go", "1")],
    );
    for (ns, at, left) in [
        ("dictpair", "Pair", "which leaves `A`, `B` open"),
        ("dictnone", "Option[Int64]", "which leaves none open"),
    ] {
        let text = refusal(
            ns,
            "",
            &format!(
                "  operation take(m: Mon) -> Int64 = 1
  operation go() -> Int64 = take(Dictionary.instance[Mon[M = {at}]]())"
            ),
        );
        assert!(
            text.contains("expected a constructor of 1 parameter at `M` (`M[T]`)")
                && text.contains(left),
            "{text}"
        );
    }
}

/// The two entries one dictionary parameter lends — at its members and at the types its type
/// writes (stage 9) — are one dictionary, so a call nothing else fixes reads it: under `d:
/// Additive[T = U]`, `Additive.zero()` is `d`'s. Found writing part 4, with G2's twin: MEASURED
/// before, refused, "two requirements of the enclosing declaration with no name both cover,
/// `Additive[T = d.T]` and `Additive[T = U]`".
#[test]
fn a_dictionary_parameters_two_entries_are_one_dictionary() {
    answers(
        "oneDict",
        "",
        "  operation zero[U](d: Additive[T = U]) -> U =
    let z = Additive.zero()
    z
  operation go() -> Int64 = zero(Dictionary.instance[Additive[T = Int64]]())",
        &[("go", "0")],
    );
}

// ── Part 5: `TypeValue` at a parameter a type leaves unwritten ───────────────────────────

/// H5, decided with the user 2026-11-13: `TypeValue` at a sort with unwritten parameters is
/// derived as at any sort, each unwritten parameter's sub-dictionary one whose `type_value()`
/// leaves it unwritten — so a constructor read as a value is the bare sort, the value `t() ->
/// Type = Option` already is. A bracket and a requirement alike, nested, and past a sort's own
/// `requires` (`Map requires Eq[T = K]`). MEASURED before part 5: refused, "unresolved:
/// TypeValue[T = Option.T]", and through `tv`, "`TypeValue[T = Option[T = ?]]` … no row of
/// `anthill.reflect.TypeValue` answers here".
#[test]
fn h5_typevalue_at_a_constructor_is_the_bare_sort() {
    let body = "  operation t() -> Type = Option
  operation tv[X]() -> Type requires TypeValue[T = X] = X
  operation direct() -> Type = TypeValue.type_value[T = Option]()
  operation viaTv() -> Type = tv[X = Option]()
  operation same() -> Bool =
    let a = TypeValue.type_value[T = Option]()
    let b = t()
    PartialEq.eq(a, b)
  operation nested() -> Type = TypeValue.type_value[T = List[T = Option]]()
  operation mapK() -> Type = TypeValue.type_value[T = Map[K = Int64]]()
  operation pairA() -> Type = TypeValue.type_value[T = Pair[A = Int64]]()
  operation pairB() -> Type = TypeValue.type_value[T = Pair[B = Int64]]()";
    answers(
        "h5",
        "",
        body,
        &[
            ("direct", "Option"),
            ("viaTv", "Option"),
            ("same", "true"),
            ("nested", "List[T = Option]"),
            ("mapK", "Map[K = Int64]"),
            ("pairA", "Pair[A = Int64]"),
            ("pairB", "Pair[B = Int64]"),
        ],
    );
}

/// H5: the dictionary keeps its shape, one sub-dictionary per declared parameter, an unwritten
/// one's `impl` the open slot's — `Dictionary.instance[TypeValue[T = Option]]()` is
/// `Dictionary(Dictionary(impl: Unwritten), impl: Option)`. MEASURED before part 5: refused,
/// "`TypeValue[T = Option]` leaves `T` with a slot open".
#[test]
fn h5_an_unwritten_parameters_dictionary_keeps_the_shape() {
    answers(
        "h5dict",
        "",
        "  operation d() -> TypeValue[T = Option] = Dictionary.instance[TypeValue[T = Option]]()",
        &[("d", "Dictionary(Dictionary(impl: Unwritten), impl: Option)")],
    );
}

/// H5: a parameter inference leaves free is one left unwritten (the user: an inferred type and a
/// written one behave the same) — `tyOf(none)` is `Option`, as `tv[X = Option]()` is; and the
/// constructor a dictionary is at, read as a value, `m.M`, is `Option` at `Option`'s. MEASURED
/// before part 5: each refused at the call, "`TypeValue[T = Option]` cannot be supplied".
#[test]
fn h5_an_inferred_free_parameter_and_a_dictionarys_constructor() {
    let body = "  operation tyOf[B](x: B) -> Type requires TypeValue[T = B] = B
  operation tOf(m: Mon) -> Type requires TypeValue[m.M] = m.M
  operation viaNone() -> Type = tyOf(none)
  operation viaDict() -> Type = tOf(Dictionary.instance[Mon[M = Option]]())";
    answers(
        "h5free",
        "",
        body,
        &[("viaNone", "Option"), ("viaDict", "Option")],
    );
}

/// No other spec has an answer at an open slot: `PartialEq` at `Option`'s unwritten `T` stays
/// refused, its written twin loading; and `TypeValue` of a type nothing fixes is no open slot of a
/// sort, and stays refused. Passes before and after part 5 by design.
#[test]
fn h5_no_other_spec_answers_at_an_open_slot() {
    let text = refusal(
        "h5eq",
        "",
        "  operation eqOf[X]() -> Int64 requires PartialEq[T = X] = 0
  operation un() -> Int64 = eqOf[X = Option]()
  operation ok() -> Int64 = eqOf[X = Option[Int64]]()",
    );
    // `un` alone: the written twin `ok` loads.
    assert!(
        text.contains(
            "`anthill.prelude.PartialEq[T = anthill.prelude.Option[T = ?]]` cannot be supplied"
        ) && text.matches("cannot be supplied").count() == 1,
        "{text}"
    );
    let text = refusal(
        "h5top",
        "",
        "  operation top() -> Type = TypeValue.type_value()",
    );
    assert!(
        text.contains("that names no instance of `anthill.reflect.TypeValue`"),
        "{text}"
    );
}

// ── Part 6: a parameter of a higher-kinded parameter is a row by use ─────────────────────

/// `Eff`, whose `E` is a row, a graded monad over a constructor of two parameters, and `Eff`'s
/// provider of it — §6's G1–G3 as the proposal writes them.
const GRADED: &str = "
  sort Eff
    effects E = ?
    sort T = ?
    entity eff(run: () -> T @ E)
  end
  operation force[R, A](m: Eff[E = R, T = A]) -> A effects R =
    match m
      case eff(run) -> run()
  sort GradedMonad[M[E, T]]
    operation pure[A](a: A) -> M[E = {}, T = A]
    operation bind[R1, R2, A, B](m: M[E = R1, T = A], f: (a: A) -> M[E = R2, T = B]) -> M[E = {R1, R2}, T = B]
    operation lift[R, A](body: () -> A @ R) -> M[E = R, T = A]
  end
  sort EffMonad
    provides GradedMonad[M = Eff]
    operation pure[A](a: A) -> Eff[E = {}, T = A] = eff(run: lambda () -> a)
    operation bind[R1, R2, A, B](m: Eff[E = R1, T = A], f: (a: A) -> Eff[E = R2, T = B]) -> Eff[E = {R1, R2}, T = B] =
      eff(run: lambda () -> force(f(force(m))))
    operation lift[R, A](body: () -> A @ R) -> Eff[E = R, T = A] = eff(run: body)
  end
";

/// `greet`'s body, G1's: one `println`, captured, then `1`.
const GREET_BODY: &str =
    "GradedMonad.bind(GradedMonad.lift(lambda () -> println(console(), name)), lambda (u) -> GradedMonad.pure(1))";

fn graded(ns: &str, body: &str) -> String {
    format!(
        "namespace p074s8.{ns}\n  import anthill.prelude.{{Int64, String, Unit}}\n  import anthill.prelude.Console.{{console, println, ConsoleOutput}}\n  import anthill.realization.runtime.Dictionary\n{GRADED}{body}\nend\n"
    )
}

/// Load a graded program and call each `(op, value, printed)` in turn: `printed` is everything
/// the console holds after the call — so an operation that only BUILDS a computation leaves it
/// as it was, and one that forces it adds its line.
fn graded_runs(ns: &str, body: &str, steps: &[(&str, &str, &str)]) {
    let mut interp = interp_for(&graded(ns, body));
    let (buf, handler) = crate::common::buffered_console();
    interp
        .register_effect_handler("anthill.prelude.Console.ConsoleOutput", handler)
        .expect("register output handler");
    for (op, want, printed) in steps {
        let got = call(&mut interp, &format!("p074s8.{ns}.{op}"));
        if !want.is_empty() {
            assert_eq!(got, *want, "{op}");
        }
        assert_eq!(buf.borrow().as_str(), *printed, "printed after {op}");
    }
}

fn graded_refusal(ns: &str, body: &str) -> String {
    let errors = load_errors_of(&graded(ns, body));
    assert!(!errors.is_empty(), "{ns}: expected a refusal");
    errors.join("\n")
}

/// G1, decided with the user 2026-11-13: a parameter of a higher-kinded parameter is a row by
/// use. `greet`'s `M` is bound by its clause to `GradedMonad`'s `M`, whose `E` the spec writes
/// rows at (`{}`, `R` of `@ R`, `{R1, R2}`), so `greet`'s `E` is a row too, and the body's
/// grade, `{{}, ConsoleOutput}`, is the declared `ConsoleOutput`. Building prints nothing;
/// forcing prints `x` and answers 1. MEASURED before part 6: refused, "expected M[E =
/// ConsoleOutput, T = Int64], got M[E = {{}, ConsoleOutput}, T = Int64]", `E` read as a type.
#[test]
fn g1_a_parameter_a_spec_writes_rows_at_is_a_row() {
    let body = format!(
        "  operation greet[M[E, T]](name: String) -> M[E = ConsoleOutput, T = Int64] requires GradedMonad[M = M] =
    {GREET_BODY}
  operation build() -> Eff[E = ConsoleOutput, T = Int64] =
    let b: Eff[E = ConsoleOutput, T = Int64] = greet(\"x\")
    b
  operation go() -> Int64 effects ConsoleOutput = force(build())"
    );
    graded_runs("g1", &body, &[("build", "", ""), ("go", "1", "x\n"), ("go", "1", "x\nx\n")]);
}

/// G1 at a sort's own higher-kinded parameter: `UseG[F[E, T]] requires GradedMonad[M = F]`
/// makes `F`'s `E` a row, as an operation's clause does. Found writing the row: the reader took
/// the sort's `requires` for a type and found no slot there (refused, "expected F[E =
/// ConsoleOutput, T = Int64], got F[E = {{}, ConsoleOutput}, T = Int64]").
#[test]
fn g1_a_sorts_constructor_parameter_bound_by_its_requires() {
    let body = format!(
        "  sort UseG[F[E, T]]
    requires GradedMonad[M = F]
    operation greetG(name: String) -> F[E = ConsoleOutput, T = Int64] =
      {GREET_BODY}
  end
  operation go() -> Int64 effects ConsoleOutput =
    let b: Eff[E = ConsoleOutput, T = Int64] = UseG[F = Eff].greetG(\"x\")
    force(b)"
    );
    graded_runs("g1sort", &body, &[("go", "1", "x\n")]);
}

/// G1 with no clause: a row written at a member of the operation's own higher-kinded parameter
/// makes it a row — `keep`'s `{ConsoleOutput}` is the row `ConsoleOutput`, as at `Eff`, and
/// `x` is its declared result.
#[test]
fn g1_a_row_written_at_a_member_makes_it_a_row() {
    let body = "  operation keep[M[E, T]](x: M[E = {ConsoleOutput}, T = Int64]) -> M[E = ConsoleOutput, T = Int64] = x
  operation mk() -> Eff[E = ConsoleOutput, T = Int64] =
    eff(run: lambda () ->
      let u = println(console(), \"y\")
      2)
  operation go() -> Int64 effects ConsoleOutput = force(keep(mk()))";
    graded_runs("g1written", body, &[("go", "2", "y\n")]);
}

/// G1 at an entity's field: `Wrap`'s field writes the row `{ConsoleOutput}` at `F`'s `E`, so
/// `F`'s `E` is a row, and `unwrap`'s too, whose `F` its parameter's type binds to `Wrap`'s.
/// Found by part 6's /code-review: the fields were not read, and `unwrap` was refused, "expected
/// F[E = ConsoleOutput, T = Int64], got F[E = {ConsoleOutput}, T = Int64]".
#[test]
fn g1_a_row_an_entitys_field_writes() {
    let body = "  sort Wrap[F[E, T]]
    entity w(x: F[E = {ConsoleOutput}, T = Int64])
  end
  operation unwrap[F[E, T]](v: Wrap[F = F]) -> F[E = ConsoleOutput, T = Int64] =
    match v
      case w(x) -> x
  operation mk() -> Wrap[F = Eff] =
    w(x: eff(run: lambda () ->
      let u = println(console(), \"z\")
      3))
  operation go() -> Int64 effects ConsoleOutput = force(unwrap(mk()))";
    graded_runs("g1field", body, &[("go", "3", "z\n")]);
}

/// G2: G1's body over a dictionary parameter, `m.M[ConsoleOutput, Int64]` (part 4's H1), at
/// `Eff`'s dictionary. MEASURED before part 6: refused as G1, "expected m.M[E = ConsoleOutput,
/// T = Int64], got m.M[E = {{}, ConsoleOutput}, T = Int64]".
#[test]
fn g2_a_dictionary_parameters_constructor_at_a_row() {
    let body = format!(
        "  operation greetWith(m: GradedMonad, name: String) -> m.M[ConsoleOutput, Int64] =
    {GREET_BODY}
  operation build() -> Eff[E = ConsoleOutput, T = Int64] =
    let b: Eff[E = ConsoleOutput, T = Int64] = greetWith(Dictionary.instance[GradedMonad[M = Eff]](), \"x\")
    b
  operation go() -> Int64 effects ConsoleOutput = force(build())"
    );
    graded_runs("g2", &body, &[("build", "", ""), ("go", "1", "x\n")]);
}

/// G3: the grade is checked. `greet` declared `M[E = {}, …]` over the body that prints is
/// refused, its row holding `ConsoleOutput`; and `force(b)` in an operation whose row lacks
/// `ConsoleOutput` is refused naming it. Both refused before part 6 too — the first by the
/// reading that refused G1's correct grade as well, so it is G1's row that tells the two apart;
/// the second by `Eff`'s own row, which G1 does not touch.
#[test]
fn g3_a_grade_the_body_does_not_have_is_refused() {
    let text = graded_refusal(
        "g3a",
        &format!(
            "  operation greet[M[E, T]](name: String) -> M[E = {{}}, T = Int64] requires GradedMonad[M = M] =
    {GREET_BODY}"
        ),
    );
    assert!(
        text.contains(
            "type mismatch in greet.return (op-return): expected M[E = {}, T = Int64], got M[E = {{}, ConsoleOutput}, T = Int64]"
        ),
        "{text}"
    );
    let text = graded_refusal(
        "g3b",
        &format!(
            "  operation greet[M[E, T]](name: String) -> M[E = ConsoleOutput, T = Int64] requires GradedMonad[M = M] =
    {GREET_BODY}
  operation quiet() -> Int64 =
    let b: Eff[E = ConsoleOutput, T = Int64] = greet(\"x\")
    force(b)"
        ),
    );
    assert!(
        text.contains("quiet.effects (op-effects): expected declared: [], got undeclared effect: ConsoleOutput")
            && !text.contains("greet.return"),
        "{text}"
    );
}

/// G1's provision rule: a provider's constructor agrees in kind with the slot it fills, by
/// order. A type parameter where the spec writes a row is refused at the provision — `Delay`
/// with `sort E = ?` providing the standard library's `DelayMonad`, which the standard library's
/// own `Delay` wrote before part 6 and now declares `effects E = ?` — and the row-declared twin
/// loads and runs. MEASURED before part 6: the type form loaded.
#[test]
fn a_type_parameter_where_the_spec_writes_a_row_is_refused_at_the_provision() {
    let delay = |e: &str| {
        format!(
            "namespace p074s8.delay{e}
  import anthill.prelude.{{DelayMonad, Unit, Int64}}
  sort Delay
    sort T = ?
    {e} E = ?
    entity delayed(thunk: () -> T @ E)
    operation delayPure[A](a: A) -> Delay[T = A, E = {{}}] =
      delayed(lambda () -> a)
    operation delayDelay[A, EffP](thunk: () -> A @ EffP) -> Delay[T = A, E = EffP] =
      delayed(thunk)
    operation delayForce[A, Eff](m: Delay[T = A, E = Eff]) -> A effects Eff =
      match m
        case delayed(t) -> t()
    operation delayFlatMap[A, B, E1, E2](m: Delay[T = A, E = E1], f: (A) -> Delay[T = B, E = E2]) -> Delay[T = B, E = {{E1, E2}}] =
      delayed(lambda () ->
        let a = delayForce(m)
        delayForce(f(a)))
    provides DelayMonad[M = Delay, pure = delayPure, delay = delayDelay, flatMap = delayFlatMap, force = delayForce]
  end
  operation run() -> Int64 = Delay.delayForce(Delay.delayFlatMap(Delay.delayPure(6), lambda (a) -> Delay.delayPure(a + 1)))
end
"
        )
    };
    let errors = load_errors_of(&delay("sort"));
    assert_eq!(
        errors,
        vec![
            "`provides DelayMonad[M = Delay]` in 'p074s8.delaysort.Delay': `M`'s `E` is a row, and `Delay`'s `E`, which takes it, is a type — a constructor's open parameters take `M`'s in order, each of the same kind at 18:5"
                .to_string()
        ],
    );
    let mut interp = interp_for(&delay("effects"));
    assert_eq!(call(&mut interp, "p074s8.delayeffects.run"), "7");
}

/// The other direction: a row parameter where the spec uses a type is refused at the provision —
/// `Mon`'s `T` is no row anywhere, and `RowBox`'s one open parameter is. MEASURED before part 6:
/// loaded.
#[test]
fn a_row_parameter_where_the_spec_uses_a_type_is_refused_at_the_provision() {
    let text = refusal(
        "rowbox",
        "  sort RowBox
    effects E = ?
    entity rb(n: Int64)
  end
  sort RowBoxMon
    provides Mon[M = RowBox]
    operation pure[A](a: A) -> RowBox[E = A] = rb(n: 0)
  end",
        "",
    );
    assert!(
        text.contains(
            "`provides Mon[M = RowBox]` in 'p074s8.rowbox.RowBoxMon': `M`'s `T` is a type, and `RowBox`'s `E`, which takes it, is a row"
        ),
        "{text}"
    );
}

/// A later load may not make a sealed spec's member a row: the standard library's `Monad` read
/// `M`'s `T` as a type, in its bodies and at its provisions (`Monad[M = Option]`), so an
/// operation a program adds to it writing `M[T = {}]` is refused (kernel-language §8.3). Writing
/// a row where the sealed spec already has one changes nothing and loads: `DelayMonad`'s `E`.
/// Found by part 6's /code-review; MEASURED before the fix: `weird` loaded, `Monad`'s `T` a row
/// for every later reading.
#[test]
fn a_later_load_may_not_make_a_sealed_specs_member_a_row() {
    let errors = load_errors_of(
        "namespace anthill.prelude.Monad
  import anthill.prelude.{Int64}
  operation weird[A](m: M[T = {}]) -> Int64 = 0
end
",
    );
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(
        errors[0].contains(
            "this load writes a row at `M`'s `T`, which 'anthill.prelude.Monad' declared in a sealed load and reads as a type"
        ),
        "{errors:?}"
    );
    let mut interp = interp_for(
        "namespace anthill.prelude.DelayMonad
  import anthill.prelude.{Int64}
  operation weird2[A](m: M[T = A, E = {}]) -> Int64 = 3
end
namespace p074s8.sealedrow
  import anthill.prelude.{Int64, Delay, DelayMonad}
  operation k() -> Int64 = DelayMonad.weird2(Delay.delayPure(1))
end
",
    );
    assert_eq!(call(&mut interp, "p074s8.sealedrow.k"), "3");
}

/// A match reads a field that applies its sort's higher-kinded parameter at the constructor the
/// scrutinee's type fills it with: `case optT(run)` over `OptionT[F = List, T = Int64]` binds
/// `run: List[Option[Int64]]`, and over an operation's own `OptionT[F = G, T = A]`, `run:
/// G[Option[A]]`. Found by part 6's /code-review, both refused on the stage's parent commit: "expected
/// List[T = Option[T = Int64]], got F[T = Option[T = Int64]]" — the signature's `F = List` opened
/// `List`'s `T` as a slot it leaves out, which is no constructor — and "expected G[T = Option[T =
/// ?A]], got F[T = Option[T = ?A]]", the pattern's walk leaving the application's head.
#[test]
fn a_match_reads_a_field_at_the_scrutinees_constructor() {
    let body = "  sort OptionT[F[T]]
    sort T = ?
    entity optT(run: F[Option[T]])
  end
  operation runOf[G[T], A](o: OptionT[F = G, T = A]) -> G[Option[A]] =
    match o
      case optT(run) -> run
  operation atList(o: OptionT[F = List, T = Int64]) -> List[Option[Int64]] =
    match o
      case optT(run) -> run
  operation viaRunOf() -> List[Option[Int64]] = runOf(OptionT.optT(run: [some(7)]))
  operation viaAtList() -> List[Option[Int64]] = atList(OptionT.optT(run: [some(7)]))";
    answers(
        "matchctor",
        "",
        body,
        &[("viaRunOf", "[some(value: 7)]"), ("viaAtList", "[some(value: 7)]")],
    );
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

// PART 2, MEASURED 2026-11-25 the same way, on the part's final code (control 11658 passed, 0
// failed). Before the sibling refusal, its control failed one row, wi383's
// `rigid_functor_application_rejects_wrong_functor`, which the part moves and which is rewritten
// on what it is about, two rigid functors of one body.
//
// p2a, a higher-kinded parameter's own variable read as its constructor (`constructor_of`, with
// the guard that a carrier still at its own variable is unfilled — without it the load
// overflowed its stack, `F[T = X]` filling to itself): 1 row,
// `a_requirement_at_a_constructor_parameter_is_read_through_it`.
//
// p2c, a sibling call at another instance refused (`sibling_at_another_instance`, decided with
// the user 2026-11-25), on both routes that read the body's provider — the self-recursive
// `UnresolvedSpecOp` and the own-carrier `call_at_own_instance`, which compared the carrier
// alone (found by /code-review): 2 rows, `a_sibling_call_at_another_instance_is_refused` and
// wi383's `a_sibling_call_at_another_functor_is_refused`; control 11658 / 0 on the final code.
// Its census, each route's refusal run over all of anthill-core before a row was written for
// it, failed one row in all: the one the part had added asserting the call loads.
//
// p2d, on the node carrier (ANTHILL_TEST_NODE_CARRIER=1): a higher-kinded parameter's
// application keeps its head in the occurrence walk and is filled by order there, as its term
// twin is (`rewrite_occ_deep`). Before it, measured on that carrier over all of anthill-core:
// `a_requirement_at_a_constructor_parameter_is_read_through_it` failed ("expected ?F[T = Int64],
// got M[T = Int64]"), with the four wi_xgrkz rows that failed there on the stage's parent commit
// too; with it, only the four wi_cxr5b two-application rows fail, as on the parent commit.
//
// A piece binding a carrier explicitly to another higher-kinded parameter's variable in
// `unify_constructor_application` failed no row backed out — the unification of two carriers'
// variables already leaves `M` at `F`'s — and was removed.
//
// Passes under every piece of part 2 by design: `h4_a_provider_over_a_constructor_reads_the_
// constructors_provider`, answered by part 1 (MEASURED after part 1: `optT(run: [some(value:
// 7)])`, refused before the stage), and `a_sibling_call_at_the_bodys_instance_or_a_required_one_
// answers`.
//
// PART 3, MEASURED 2026-11-25 the same way (control 11662 passed, 0 failed). The grammar, which
// no switch backs out, was measured at the stage's start: `[F[T]]` in an operation's bracket was
// a syntax error.
//
// p3a, an operation's `F[T]` a marked carrier — its members type parameters of its scope, its
// variable its `SortAlias` (load.rs, `scan_operation_params` and the operation's load): 2 rows,
// `h2_an_operations_higher_kinded_parameter_is_fixed_as_any_parameter` and
// `h2_a_call_fitting_two_constructors_is_refused_and_kinds_count`.
//
// p3b, the refusal naming the two constructors a call fits (`constructors_the_call_fits`): 1 row,
// `h2_a_call_fitting_two_constructors_is_refused_and_kinds_count`.
//
// p3c, the member sugar's parameter a constructor slot where the member is higher-kinded
// (`applied_higher_kinded_member`): 1 row, `h3_the_member_spelling_at_a_higher_kinded_member`.
//
// p3d, the converter's refusals of a member of its own kind and a member's default: 1 row,
// `an_operations_higher_kinded_parameter_takes_types_and_no_default`.
//
// The fixes of part 3's /code-review, MEASURED 2026-11-25 the same way (control 11664 passed, 0
// failed):
//
// p3e, `Mon2.M` inside `Mon2`'s own declaration its own `M` (`applied_higher_kinded_member`): 1
// row, `h3_the_member_spelling_in_the_specs_own_body_and_an_operations_body`.
//
// p3f, an operation's body reading the parameter its signature spelled: the same row.
//
// p3g, a carrier block's narrowed constructor applied: 1 row,
// `h3_the_member_spelling_in_a_carrier_block_is_its_constructor` ("expected M[T = Int64], got
// Box[V = Int64]" with it out). The constructor's bindings are kept as the clause writes them,
// a parameter of the block its `Ref`: lowered to the parameter's variable, by the clause canon or
// by the signature's own reader, `R2Mon[E = String].lift(7)` was typed `R2[E = ?E, T = Int64]`
// (MEASURED both ways).
//
// p3h, an argument that fits two constructors named in the refusal (`constructor_args`): 1 row,
// `h2_a_call_fitting_two_constructors_is_refused_and_kinds_count`.
//
// p3i, a higher-kinded parameter's default refused at the converter: 1 row,
// `an_operations_higher_kinded_parameter_takes_types_and_no_default`.
//
// The domain the member's carrier is backed under — the operation, as an operation's own `F[T]`
// is, where it was the spec's (the sealed `anthill.prelude.Monad` for a program) — changes no
// row's verdict: nothing a row drives reads that domain.
//
// PART 4, MEASURED 2026-11-25 the same way (control 11668 passed, 0 failed):
//
// p4a, a dictionary at a constructor slot (`dictionary_instance_call`): 3 rows,
// `a_dictionary_at_a_constructor_slot_is_written_at_the_constructor`,
// `h1_a_dictionary_parameters_applied_member_is_its_constructor`,
// `h1_a_member_the_parameters_type_writes_is_that_constructor`.
//
// p4b, `m.M[args]` read off the operation's parameter (`mint_dictionary_members`): 2 rows, the
// two `h1_` rows.
//
// p4c, the parameter's type written `Mon[M = P]` (`with_dictionary_member_carriers`): 1 row,
// `h1_a_dictionary_parameters_applied_member_is_its_constructor`.
//
// p4d, one parameter's two entries one dictionary (`read_requirement_by_name`): 1 row,
// `a_dictionary_parameters_two_entries_are_one_dictionary`.
//
// p4e, the member the parameter's type writes read as that constructor: 1 row,
// `h1_a_member_the_parameters_type_writes_is_that_constructor`.
//
// The fixes of part 4's /code-review, MEASURED the same way (control 11670 passed, 0 failed):
//
// p4f, a call handed the enclosing operation's constructor skolems (`check_apply_call`): 1 row,
// `a_constructor_passed_on_is_the_callers_own`. p4g, a skolem read back as its parameter
// (`constructor_of`, `KnowledgeBase::rigid_carrier`), backed out alone: 7 rows — that row,
// `h1_a_dictionary_parameters_applied_member_is_its_constructor`, and five of parts 2 and 3
// (`a_requirement_at_a_constructor_parameter_is_read_through_it`, both `h2_` rows, and the two
// `h3_` rows other than the carrier block's), since the skolems handed with no reader of them
// leave each body's constructor unread. p4fg, the two backed out together, the code before the fix: 1
// row, `a_constructor_passed_on_is_the_callers_own`.
//
// p4h, the member a parameter's type writes found by `fit_type_args`: 1 row,
// `the_member_a_parameters_type_writes_is_found_as_its_lowering_keys_it`. p4j, a written
// constructor holding a fresh variable refused: the same row.
//
// The review also found the pre-scan reading an arrow's binder `m` in `f: (m: Mon) ->
// m.M[Int64]` as the operation's `m`; a walker skipping an arrow's binders was written and
// removed, no loading program being able to tell — an arrow binder's applied member is
// unread (refused, "unresolved type name 'm.M'") either way.
//
// PART 5, MEASURED 2026-11-25 the same way (control 11674 passed, 0 failed). H5 lifts a refusal
// eight rows of earlier tickets pinned; its census, the part's code run over all of
// anthill-core before a row was rewritten, failed those eight and no other. Seven are
// rewritten to H5's answers: `wi_89j6k`'s and `wi_wgjfn`'s empty list (a host's reading),
// `wi_9wvt7_reify_rule_body`'s collection whose element is open (refused now by the boundary's
// two labels), `wi_n31xx`'s `tyOf(none())`, `wi_rs2g4`'s `[U = List]`, and `wi_sqzpq`'s two
// calls at `Boom`. The eighth, `wi_9wvt7_review5`'s `variant[C](w: Wrap.wrap[V = C])`, found the
// first rule too broad — a caller's own parameter read as an unwritten one — and passes as it
// was once the rule reads only the asking sort's own parameter.
//
// p5a, `TypeValue` answered at an unwritten parameter (`unwritten_parameter_of_a_type`): 10
// rows, part 5's three answering rows and the seven rewritten.
//
// p5b, the reader leaving the parameter unwritten (`type_of_type_value_dictionary`): 6 rows,
// the ones that read the type.
//
// p5c, a `TypeValue` dictionary written with a slot open (`dictionary_instance_call`): 3 rows,
// `h5_an_unwritten_parameters_dictionary_keeps_the_shape` and the two host readings, which go
// through that call.
//
// p5d, the open slot read only at the asking sort's own parameter, backed out to any parameter:
// 1 row, `wi_9wvt7_review5_test::a_part_with_no_instance_is_said_and_a_variant_is_its_sort`.
//
// Passes before and after by design: `h5_no_other_spec_answers_at_an_open_slot`.
//
// PART 6, MEASURED 2026-11-25 the same way (control 11681 passed, 0 failed; 11684 with the
// review's rows). The standard library's `Delay` declares `effects E = ?` in every run, and the
// two wi516 fixtures with it; the type form is refused at the provision.
//
// p6a, the rows a signature writes (`record_hk_row_members`): the standard library's own
// `provides DelayMonad[M = Delay]` is refused, `DelayMonad`'s `E` then a type, so every row that
// loads it fails (10527). Backed out with p6f, the kind check: 8 rows — the four G1/G2 rows read
// by a clause or written (`g1_a_parameter_a_spec_writes_rows_at_is_a_row`,
// `g1_a_sorts_constructor_parameter_bound_by_its_requires`,
// `g1_a_row_written_at_a_member_makes_it_a_row`, `g2_a_dictionary_parameters_constructor_at_a_row`),
// `g3_a_grade_the_body_does_not_have_is_refused`, the two provision rows and
// `a_later_load_may_not_make_a_sealed_specs_member_a_row`.
//
// p6b, the rows a clause gives by order (`clause_slots_binding`): 4 rows — the two `g1_` rows
// read by a clause, `g2_`, and `g3_`.
//
// p6c, a sort's own `requires` read as such a clause: 1 row,
// `g1_a_sorts_constructor_parameter_bound_by_its_requires`.
//
// p6d, the reader (`effects_param_head_is`): 5 rows — the four G1/G2 rows and `g3_`.
//
// p6f, the kind agreement at a provision (`check_provision_constructors`): 2 rows,
// `a_type_parameter_where_the_spec_writes_a_row_is_refused_at_the_provision` and
// `a_row_parameter_where_the_spec_uses_a_type_is_refused_at_the_provision`.
//
// A sixth piece, the same rows read by `effect_row_params_of_spec` and
// `declared_effect_row_params`, failed no row backed out; it was removed.
//
// The fixes of part 6's /code-review, MEASURED the same way:
//
// p6g, a later load's row at a sealed spec's member refused: 1 row,
// `a_later_load_may_not_make_a_sealed_specs_member_a_row`.
//
// p6h, the rows an entity's field writes: 1 row, `g1_a_row_an_entitys_field_writes`.
//
// p6i, a pattern's field read at the scrutinee's constructor (`pattern_field_type_through`):
// 2 rows, `a_match_reads_a_field_at_the_scrutinees_constructor` and
// `g1_a_row_an_entitys_field_writes`, whose `unwrap` matches.
//
// p6j, no unwritten slot opened inside a higher-kinded slot (`rigidify_unwritten_sort_params`): 1
// row, `a_match_reads_a_field_at_the_scrutinees_constructor` (its `atList`).
//
// A layer's rows go with it: `kb::layer`'s `s8_a_layers_row_at_an_earlier_member_goes_with_the_layer`
// fails with `hk_row_members` out of `kb_scoped_fields!`.
//
// Passes before and after by design: G3's first refusal (`g3_`'s `greet` declared `M[E = {}]`),
// refused before part 6 too, by the reading that refused G1's correct grade as well.

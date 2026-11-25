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

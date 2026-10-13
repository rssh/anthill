//! WI-20260930-JPSDH — a call-site bracket on a spec operation whose call is typed against the
//! override it runs (the WI-606 fallback, `typing/build.rs` `concrete_override_threaded`):
//! `Sp.pick2[W = Int64](a, b)` and `Car.pick2[W = Int64](a, b)` are one call in two spellings,
//! and are answered and refused alike.
//!
//! The spec operation's return and effects hold `s.E`, which does not eliminate over a `Car`
//! that provides `Sp[E = {EC}]` — so the call is typed against `Car.pick2`, whose own `W` only
//! the bracket binds:
//!
//! ```text
//! sort Sp   operation pick2[W](x: T, s: Self) -> Option[T = Pair[A = s.T, B = W]] effects s.E
//! sort Car  provides Sp[T = Self, E = {EC}]
//!           operation pick2[W, U, R](x: Car[V = U, EC = R], s: Self)
//!             -> Option[T = Pair[A = Car[V = V, EC = EC], B = W]] effects {EC} = none
//! ```
//!
//! AS FILED the program wrote `s: Sp` and `s: Car` beside a bare `T` and `V`, which is refused
//! where it is declared since a bare sort names any instance; the rows write `s: Self`.
//!
//! WHAT THE TICKET FOUND WAS ALREADY BUILT when it was taken up: WI-20260929-0RP29's later
//! passes gave the fallback the bracket and the arguments' join (`override_at_call`), with two
//! rows (`wi_0rp29_nested_projection_value_in_type_test::a_call_site_bracket_reaches_the_fallback`
//! and `…_contradicted`). Run at the sites below, three things were left, and are this file's:
//!
//! * a bracket an argument contradicts ONLY THROUGH THE OVERRIDE loaded through the spec
//!   (`Sp.pick2[W = String](a, b, 5)` beside `Car.pick2[W, …](…, k: W)`), the bracket reaching
//!   nothing: the declarations were related in one unification, and a position where the spec
//!   writes a type bound the override's parameter before the position that relates it to the
//!   spec's was read;
//! * an UNWRITTEN bracket was refused "Car has no member E", where the carrier spelling and
//!   the spec's own path say which parameter is unconstrained and how to write it;
//! * and, made reachable by the first: a parameter the bracket fixes was not judged against
//!   its arguments where the override's EFFECTS are read (a defaulted spec operation, no
//!   fallback), so `Sp.op[U = String](x, 5, "s")` charged `Error[String]` and raised the `5`.
//!
//! MEASURED, each part backed out alone over this file (17 rows; the last row of the
//! contradiction section was added after, and its own measurement is at its site):
//!
//! 1. THE BRACKET STEP (`override_at_call`, step 1) — seeding nothing. 7 FAIL:
//!    [`a_bracket_is_related_by_position_never_by_name`],
//!    [`a_bracket_holds_a_nested_type_an_alias_and_a_type_holding_a_value`],
//!    [`the_bracket_decides_the_type_the_override_answers_at`],
//!    [`a_bracket_wider_than_its_arguments_is_what_the_override_charges`] and the three rows
//!    of part 2. THE PLAIN CALL DOES NOT, and rests on two readers: unseeded, the override's
//!    `W` is still free after the arguments and takes the spec's return as the call bound it
//!    (step 5). With step 5 backed out as well, 10 FAIL — those seven, both
//!    `a_bracket_reaches_the_override_…` rows and
//!    [`an_unwritten_bracket_is_refused_naming_the_spec_operations_parameter`] (its advised
//!    repair); step 5 backed out alone fails none here, the bracket seeding first.
//! 2. ONE RELATION PER POSITION (`DeclarationsRelated`) — one unification over every
//!    position. 3 FAIL: [`a_bracket_an_argument_contradicts_through_the_override_is_refused`],
//!    [`a_bracket_beside_an_argument_decides_what_the_override_answers_at`] and
//!    [`a_bracket_an_argument_contradicts_is_refused_where_the_override_charges_an_effect`]
//!    (refused, but as the join's "no common type").
//! 3. A PARAMETER THE BRACKET FIXED JUDGES ITS ARGUMENTS (`override_at_call`) — not. 1 FAILS:
//!    [`a_bracket_an_argument_contradicts_is_refused_where_the_override_charges_an_effect`]
//!    (it LOADS). The fallback's rows pass: its own validation refuses there, in the same
//!    words. With only a parameter WRITTEN WITH A PROJECTION left unjudged, that row's second
//!    half fails the same way (`k: Pair[A = c.V, B = W]` LOADS).
//! 4. THE UNWRITTEN BRACKET NAMED (`concrete_override_threaded`) — declined. 1 FAILS:
//!    [`an_unwritten_bracket_is_refused_naming_the_spec_operations_parameter`].
//!
//! PASS EITHER WAY, BY DESIGN — the controls that a part above refuses or names nothing it
//! should not: [`a_bracket_agreeing_with_its_arguments_through_the_override_runs`],
//! [`a_bracket_agreeing_with_its_arguments_charges_what_it_says`],
//! [`an_unwritten_bracket_on_the_other_two_routes_is_refused_alike`],
//! [`an_unwritten_parameter_the_expected_type_fixes_loads`],
//! [`an_override_parameter_standing_at_no_spec_parameter_still_declines`],
//! [`an_argument_alone_binds_the_overrides_parameter`] and
//! [`a_parameter_the_bracket_fixes_is_read_through_the_calls_rekey`] (which fails on a
//! judgement that reads the parameter as written).
//!
//! NOT REACHED, and not this ticket's: beside a spec DEFAULT body a member that declares no
//! effect is not read at the call at all, so `Sp.op[U = String](x, 5)` over a pure
//! `Car.op[W](c, k: W) -> Option[T = W] = some(k)` loads and fails at run time, with or without
//! the bracket's type coming from an annotation instead — WI-20260930-FB53M's question (is a
//! member that does not fit the spec operation its supplier).

use crate::common::{assert_refused_naming, load_errors_of as load_errors, run_int64 as run_src};

const PICK2: &str =
    "operation pick2[W](x: T, s: Self) -> Option[T = Pair[A = s.T, B = W]] effects s.E";
const CAR_PICK2: &str = "operation pick2[W, U, R](x: Car[V = U, EC = R], s: Self) -> Option[T = \
                         Pair[A = Car[V = V, EC = EC], B = W]] effects {EC} = none";

/// The none arm answers 7.
const ARMS: &str = "      case some(p) -> 1\n      case none() -> 7";

/// `Animal` over `cat` and `dog`; `Sp[T, E]` with `spec_op`; `Car[V, EC]` providing `Sp[T =
/// Self, E = {EC}]` with `member`; then `rest`.
fn program(ns: &str, spec_op: &str, member: &str, rest: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option, Pair, String, List, Error}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Pair.{{pair}}
  import anthill.prelude.List.{{cons, nil}}
  sort Animal
    entity cat(n: Int64)
    entity dog(m: String)
  end
  sort Buf
    sort T = ?
    sort N = ?
    entity buf(items: List[T])
  end
  sort MyInt = Int64
  sort Sp
    sort T = ?
    effects E = ?
    {spec_op}
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = Self, E = {{EC}}]
    {member}
  end
{rest}
end
"#
    )
}

/// `use[R]` over two `Car`s at `EC = R` with `body` (a `cat` `c1` in scope), and `go` calling
/// it on one pure `Car`.
fn caller(body: &str) -> String {
    format!(
        "  operation use[R](a: Car[V = Int64, EC = R], b: Car[V = Int64, EC = R]) -> Int64 \
         effects {{R}} =\n    let c1: cat = cat(n: 5)\n{body}\n  operation go() -> Int64 =\n    \
         let a: Car[V = Int64, EC = {{}}] = car(v: 1)\n    use(a, a)\n"
    )
}

/// `go` of [`program`] with [`caller`]'s `body`.
fn run(ns: &str, spec_op: &str, member: &str, body: &str) -> Result<i64, String> {
    run_src(&program(ns, spec_op, member, &caller(body)), &format!("{ns}.go"))
}

/// The refusals of [`program`] with [`caller`]'s `body`.
fn refusals(ns: &str, spec_op: &str, member: &str, body: &str) -> Vec<String> {
    load_errors(&program(ns, spec_op, member, &caller(body)))
}

// ── the bracket reaches the override ──────────────────────────────────────────

/// THE TICKET'S CALL, AT EACH SITE A CALL IS WRITTEN: arguments by name and out of order, a
/// lambda's body, an `if` condition, a match guard, and a carrier with no row parameter of
/// the caller's. Each answers the override's `none` arm.
#[test]
fn a_bracket_reaches_the_override_wherever_the_call_is_written() {
    let isnone = "  operation isnone[X](o: Option[T = X]) -> Bool = match o\n      case some(_) \
                  -> false\n      case none() -> true\n";
    let sites = [
        ("plain", format!("    match Sp.pick2[W = Int64](a, b)\n{ARMS}")),
        ("named", format!("    match Sp.pick2[W = Int64](s: b, x: a)\n{ARMS}")),
        (
            "lambda",
            "    let f = lambda (z: Int64) -> match Sp.pick2[W = Int64](a, b)\n      case \
             some(p) -> 1\n      case none() -> z\n    f(7)"
                .to_string(),
        ),
        (
            "cond",
            "    if isnone(Sp.pick2[W = Int64](a, b)) then 7 else 1".to_string(),
        ),
        (
            "guard",
            "    let n: Int64 = 3\n    match n\n      case k | isnone(Sp.pick2[W = Int64](a, \
             b)) -> 7\n      case _ -> 1"
                .to_string(),
        ),
    ];
    for (tag, body) in sites {
        let ns = format!("wijpsdh.site_{tag}");
        let src = program(&ns, PICK2, CAR_PICK2, &format!("{isnone}{}", caller(&body)));
        assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(7), "{tag}");
    }
    let ns = "wijpsdh.site_concrete";
    let concrete = format!(
        "  operation go() -> Int64 =\n    let a: Car[V = Int64, EC = {{}}] = car(v: 1)\n    \
         match Sp.pick2[W = Int64](a, a)\n{ARMS}\n"
    );
    assert_eq!(
        run_src(&program(ns, PICK2, CAR_PICK2, &concrete), &format!("{ns}.go")),
        Ok(7)
    );
}

/// … AND UNQUALIFIED, IMPORTED INTO ANOTHER NAMESPACE: `pick2[W = Int64](a, b)`.
#[test]
fn a_bracket_reaches_the_override_through_an_imported_name() {
    let src = format!(
        r#"
namespace wijpsdh.imp
  import anthill.prelude.{{Int64, Bool, Option, Pair}}
  import anthill.prelude.Option.{{some, none}}
  sort Sp
    sort T = ?
    effects E = ?
    {PICK2}
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = Self, E = {{EC}}]
    {CAR_PICK2}
  end
end
namespace wijpsdh.imp.user
  import anthill.prelude.{{Int64, Bool, Option, Pair}}
  import anthill.prelude.Option.{{some, none}}
  import wijpsdh.imp.{{Sp, Car}}
  import wijpsdh.imp.Car.{{car}}
  import wijpsdh.imp.Sp.{{pick2}}
  operation use[R](a: Car[V = Int64, EC = R], b: Car[V = Int64, EC = R]) -> Int64 effects {{R}} =
    match pick2[W = Int64](a, b)
{ARMS}
  operation go() -> Int64 =
    let a: Car[V = Int64, EC = {{}}] = car(v: 1)
    use(a, a)
end
"#
    );
    assert_eq!(run_src(&src, "wijpsdh.imp.user.go"), Ok(7));
}

/// THE BRACKET IS RELATED BY POSITION, NEVER BY NAME. The override's parameter that stands
/// where the spec writes `W` is called `Z` and declared last; then the two names are SWAPPED
/// — the override's `X` stands at the spec's `W` and its `W` at the spec's `X` — and a result
/// annotated the way the names read is refused through the spec as through the carrier, the
/// way the positions read loading on both. Last, the CARRIER's own parameter is called `W`,
/// and the bracket leaves it alone.
#[test]
fn a_bracket_is_related_by_position_never_by_name() {
    let moved = "operation pick2[U, R, Z](x: Car[V = U, EC = R], s: Self) -> Option[T = Pair[A \
                 = Car[V = V, EC = EC], B = Z]] effects {EC} = none";
    for (q, call) in [("sp", "Sp.pick2[W = Int64]"), ("car", "Car.pick2[Z = Int64]")] {
        let body = format!(
            "    let r: Option[T = Pair[A = Car, B = Int64]] = {call}(a, b)\n    7"
        );
        assert_eq!(
            run(&format!("wijpsdh.moved_{q}"), PICK2, moved, &body),
            Ok(7),
            "{q}"
        );
    }

    let spec2 = "operation pick2[W, X](x: T, s: Self) -> Option[T = Pair[A = W, B = Pair[A = \
                 s.T, B = X]]] effects s.E";
    let swapped = "operation pick2[X, W](x: Car[V = ?, EC = ?], s: Self) -> Option[T = Pair[A = \
                   X, B = Pair[A = Car[V = V, EC = EC], B = W]]] effects {EC} = none";
    for (q, call) in [
        ("sp", "Sp.pick2[W = Int64, X = String]"),
        ("car", "Car.pick2[X = Int64, W = String]"),
    ] {
        let annotated = |a: &str, b: &str| {
            format!(
                "    let r: Option[T = Pair[A = {a}, B = Pair[A = Car, B = {b}]]] = {call}(a, \
                 b)\n    7"
            )
        };
        assert_eq!(
            run(
                &format!("wijpsdh.swapped_{q}"),
                spec2,
                swapped,
                &annotated("Int64", "String")
            ),
            Ok(7),
            "{q}"
        );
        assert_refused_naming(
            &refusals(
                &format!("wijpsdh.swapped_bad_{q}"),
                spec2,
                swapped,
                &annotated("String", "Int64"),
            ),
            &["in r.annotation", "got Option[T = Pair[A = Int64"],
            q,
        );
    }

    let src = r#"
namespace wijpsdh.sortw
  import anthill.prelude.{Int64, Bool, Option, Pair, String}
  import anthill.prelude.Option.{some, none}
  sort Sp
    sort T = ?
    effects E = ?
    operation pick2[W](x: T, s: Self) -> Option[T = Pair[A = s.T, B = W]] effects s.E
  end
  sort Car
    sort W = ?
    effects EC = ?
    entity car(v: W)
    provides Sp[T = Self, E = {EC}]
    operation pick2[Z, U, R](x: Car[W = U, EC = R], s: Self) -> Option[T = Pair[A = Car[W = W, EC = EC], B = Z]] effects {EC} = none
  end
  operation use[R](a: Car[W = Int64, EC = R], b: Car[W = Int64, EC = R]) -> Int64 effects {R} =
    let r: Option[T = Pair[A = Car[W = Int64, EC = R], B = String]] = Sp.pick2[W = String](a, b)
    7
  operation go() -> Int64 =
    let a: Car[W = Int64, EC = {}] = car(v: 1)
    use(a, a)
end
"#;
    assert_eq!(run_src(src, "wijpsdh.sortw.go"), Ok(7));
}

/// THE BRACKET HOLDS ANY TYPE: one applied to another, an alias, one holding a value — and a
/// result annotated at another value is refused on both spellings.
#[test]
fn a_bracket_holds_a_nested_type_an_alias_and_a_type_holding_a_value() {
    let body = "    let r1: Option[T = Pair[A = Car[V = Int64, EC = R], B = Option[T = Int64]]] \
                = Sp.pick2[W = Option[T = Int64]](a, b)\n    let r2: Option[T = Pair[A = Car[V \
                = Int64, EC = R], B = Int64]] = Sp.pick2[W = MyInt](a, b)\n    let r3: Option[T \
                = Pair[A = Car[V = Int64, EC = R], B = Buf[T = Int64, N = 3]]] = Sp.pick2[W = \
                Buf[T = Int64, N = 3]](a, b)\n    7";
    assert_eq!(run("wijpsdh.held", PICK2, CAR_PICK2, body), Ok(7));
    for q in ["Sp", "Car"] {
        let body = format!(
            "    let r: Option[T = Pair[A = Car[V = Int64, EC = R], B = Buf[T = Int64, N = \
             4]]] = {q}.pick2[W = Buf[T = Int64, N = 3]](a, b)\n    7"
        );
        assert_refused_naming(
            &refusals(&format!("wijpsdh.held_bad_{q}"), PICK2, CAR_PICK2, &body),
            &["in r.annotation", "B = Buf[T = Int64, N = 3]"],
            q,
        );
    }
}

const PICK_MK: &str = "operation pick2[W](x: T, s: Self, mk: (n: Int64) -> W) -> Option[T = \
                       Pair[A = s.T, B = List[T = W]]] effects s.E";
const CAR_PICK_MK: &str = "operation pick2[W, U, R](x: Car[V = U, EC = R], s: Self, mk: (n: \
                           Int64) -> W) -> Option[T = Pair[A = Car[V = V, EC = EC], B = List[T \
                           = W]]] effects {EC} = some(pair(s, [mk(41)]))";

/// `q.pick2{call}` over [`PICK_MK`], its first answer `v` bound and `arm` answered.
fn mk_body(q: &str, call: &str, arm: &str) -> String {
    format!(
        "    match {q}.pick2{call}\n      case some(pair(_, cons(v, _))) ->\n        {arm}\n      \
         case _ -> 0"
    )
}

/// THE BRACKET DECIDES THE TYPE THE OVERRIDE ANSWERS AT, a fitting member and no default
/// body: `[W = Animal]` over a callback answering a `cat` answers a list of `Animal`, so `let
/// z: cat = v` is refused on both spellings and `let z: Animal = v` runs on both. From the
/// argument alone the override's `W` is `cat`, and the spec spelling loaded the first.
#[test]
fn the_bracket_decides_the_type_the_override_answers_at() {
    let call = "[W = Animal](a, b, lambda n -> c1)";
    for q in ["Sp", "Car"] {
        assert_refused_naming(
            &refusals(
                &format!("wijpsdh.decides_bad_{q}"),
                PICK_MK,
                CAR_PICK_MK,
                &mk_body(q, call, "let z: cat = v\n        2"),
            ),
            &["z.annotation", "expected cat, got Animal"],
            q,
        );
        assert_eq!(
            run(
                &format!("wijpsdh.decides_{q}"),
                PICK_MK,
                CAR_PICK_MK,
                &mk_body(q, call, "let z: Animal = v\n        2"),
            ),
            Ok(2),
            "{q}"
        );
    }
}

/// … AND ITS CONTROL: with no bracket the argument alone binds `W` — a `cat` — on both
/// spellings, and what the override answers is read back (`41 + 1`). Passes with every part
/// of the ledger backed out.
#[test]
fn an_argument_alone_binds_the_overrides_parameter() {
    for q in ["Sp", "Car"] {
        assert_eq!(
            run(
                &format!("wijpsdh.alone_{q}"),
                PICK_MK,
                CAR_PICK_MK,
                &mk_body(q, "(a, b, lambda n -> c1)", "let z: cat = v\n        2"),
            ),
            Ok(2),
            "{q}"
        );
        assert_eq!(
            run(
                &format!("wijpsdh.alone_v_{q}"),
                PICK_MK,
                CAR_PICK_MK,
                &mk_body(q, "[W = Int64](a, b, lambda n -> n + 1)", "v"),
            ),
            Ok(42),
            "{q}"
        );
    }
}

// ── a bracket an argument contradicts ─────────────────────────────────────────

/// `pick2[W](x: T, s: Self, k: {spec_k}) … = none` — a DEFAULT body, so the member beside it
/// is not compared with it where it is declared (WI-20260930-FB53M) and the call is its only
/// judge — and `Car.pick2[W, U, R](…, k: W)`, answering `some(pair(s, k))`.
fn default_spec(spec_k: &str) -> String {
    format!(
        "operation pick2[W](x: T, s: Self, k: {spec_k}) -> Option[T = Pair[A = s.T, B = W]] \
         effects s.E = none"
    )
}
const CAR_PICK_K: &str = "operation pick2[W, U, R](x: Car[V = U, EC = R], s: Self, k: W) -> \
                          Option[T = Pair[A = Car[V = V, EC = EC], B = W]] effects {EC} = \
                          some(pair(s, k))";

/// `q.pick2{call}`, the override's second component `w` bound and `arm` answered.
fn k_body(q: &str, call: &str, arm: &str) -> String {
    format!(
        "    match {q}.pick2{call}\n      case some(pair(_, w)) ->\n        {arm}\n      case \
         none() -> 7"
    )
}

/// A BRACKET AN ARGUMENT CONTRADICTS ONLY THROUGH THE OVERRIDE IS REFUSED ON BOTH SPELLINGS,
/// in the same words. The spec takes `k: Int64` whatever `W` is, so its own argument check
/// passes `Sp.pick2[W = String](a, b, 5)`; the override takes `k: W`. The spec spelling
/// LOADED, the bracket reaching nothing and the override answering at the argument's `Int64`.
/// Likewise `[W = dog]` beside a `cat`, the spec taking any `Animal`.
#[test]
fn a_bracket_an_argument_contradicts_through_the_override_is_refused() {
    for q in ["Sp", "Car"] {
        assert_refused_naming(
            &refusals(
                &format!("wijpsdh.contra_{q}"),
                &default_spec("Int64"),
                CAR_PICK_K,
                &k_body(q, "[W = String](a, b, 5)", "1"),
            ),
            &["pick2.k (op-arg): expected String, got Int64"],
            q,
        );
        assert_refused_naming(
            &refusals(
                &format!("wijpsdh.contra_sub_{q}"),
                &default_spec("Animal"),
                CAR_PICK_K,
                &k_body(q, "[W = dog](a, b, c1)", "1"),
            ),
            &["pick2.k (op-arg): expected dog, got cat"],
            q,
        );
    }
}

/// … AND THE BRACKET, WIDER THAN THE ARGUMENT, DECIDES WHAT THE OVERRIDE ANSWERS AT: after
/// `[W = Animal](a, b, c1)` the answer is an `Animal` on both spellings. The spec spelling
/// read it as the argument's `cat`.
#[test]
fn a_bracket_beside_an_argument_decides_what_the_override_answers_at() {
    for q in ["Sp", "Car"] {
        assert_refused_naming(
            &refusals(
                &format!("wijpsdh.wider_{q}"),
                &default_spec("Animal"),
                CAR_PICK_K,
                &k_body(q, "[W = Animal](a, b, c1)", "let z: cat = w\n        2"),
            ),
            &["z.annotation", "expected cat, got Animal"],
            q,
        );
    }
}

/// … AND THE CONTROLS: a bracket its argument agrees with runs the override on both spellings
/// — at the argument's own type (`5 + 1`), at a wider one, and with no bracket at all. Passes
/// with every part of the ledger backed out.
#[test]
fn a_bracket_agreeing_with_its_arguments_through_the_override_runs() {
    for q in ["Sp", "Car"] {
        for (tag, spec_k, call, arm, want) in [
            ("same", "Int64", "[W = Int64](a, b, 5)", "w + 1", 6),
            ("none", "Int64", "(a, b, 5)", "w + 1", 6),
            ("wider", "Animal", "[W = Animal](a, b, c1)", "1", 1),
            ("exact", "Animal", "[W = cat](a, b, c1)", "1", 1),
        ] {
            assert_eq!(
                run(
                    &format!("wijpsdh.agree_{tag}_{q}"),
                    &default_spec(spec_k),
                    CAR_PICK_K,
                    &k_body(q, call, arm),
                ),
                Ok(want),
                "{tag} {q}"
            );
        }
    }
}

// ── …where the override's effects are read, and no fallback ───────────────────

/// `Sp` over `spec_op`, `Car` providing it with `member`, and `via` — declaring
/// `Error[declared]` — answering `call` over a cat `c1` and a dog `d1`. No projection: the
/// spec operation's own types stand, and the override is read for what it charges.
fn effects_program(ns: &str, spec_op: &str, member: &str, declared: &str, call: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option, String, Error, List, Pair}}
  import anthill.prelude.Pair.{{pair}}
  sort Animal
    entity cat(n: Int64)
    entity dog(m: String)
  end
  sort Sp
    sort T = ?
    {spec_op}
  end
  sort Car
    sort V = ?
    entity car(v: V)
    provides Sp[T = V]
    {member}
  end
  operation via(x: Car[V = Int64]) -> Int64 effects {{Error[{declared}]}} =
    let c1: cat = cat(n: 1)
    let d1: dog = dog(m: "woof")
    {call}
end
"#
    )
}

const DEFAULTED_OP: &str = "operation op[U](s: Self, k: Int64, u: U) -> Int64 = 0";
const CAR_OP_KU: &str =
    "operation op[W](c: Self, k: W, u: W) -> Int64 effects {Error[W]} = Error.raise(k)";

/// A BRACKET AN ARGUMENT CONTRADICTS IS REFUSED WHERE THE OVERRIDE CHARGES AN EFFECT, in the
/// carrier spelling's words: `Sp.op[U = String](x, 5, "s")` over `Car.op[W](c, k: W, u: W)
/// effects {Error[W]} = Error.raise(k)` beside a default. The spec takes `k: Int64`, so only
/// the override's `k: W` contradicts. With the bracket reaching `W` and nothing judging the
/// arguments against it, `via` declaring `Error[String]` LOADED and raised the `5`; with the
/// bracket reaching nothing it was refused, as the join's "no common type for `W`".
#[test]
fn a_bracket_an_argument_contradicts_is_refused_where_the_override_charges_an_effect() {
    for (q, call) in [
        ("sp", "Sp.op[U = String](x, 5, \"s\")"),
        ("car", "Car.op[W = String](x, 5, \"s\")"),
    ] {
        let src = effects_program(
            &format!("wijpsdh.eff_contra_{q}"),
            DEFAULTED_OP,
            CAR_OP_KU,
            "String",
            call,
        );
        assert_refused_naming(
            &load_errors(&src),
            &["op.k (op-arg): expected String, got Int64"],
            q,
        );
    }
    // … and where the override writes that parameter with a projection of its own (`c.V`),
    // eliminated against the arguments before the argument is judged.
    let spec_op = "operation op[U](s: Self, k: Pair[A = Int64, B = Int64], u: U) -> Int64 = 0";
    let member = "operation op[W](c: Self, k: Pair[A = c.V, B = W], u: W) -> Int64 effects \
                  {Error[W]} = Error.raise(u)";
    for (q, call) in [
        ("sp", "Sp.op[U = String](x, pair(1, 5), \"s\")"),
        ("car", "Car.op[W = String](x, pair(1, 5), \"s\")"),
    ] {
        let src = effects_program(
            &format!("wijpsdh.eff_contra_proj_{q}"),
            spec_op,
            member,
            "String",
            call,
        );
        assert_refused_naming(
            &load_errors(&src),
            &["op.k (op-arg): expected Pair[A = Int64, B = String], got Pair[A = Int64, B = Int64]"],
            q,
        );
    }
}

/// … AND ITS CONTROLS: a bracket the arguments agree with loads, and so does the call with no
/// bracket; arguments that disagree with each other and no bracket are refused as the join
/// refuses them. Passes with every part of the ledger backed out.
#[test]
fn a_bracket_agreeing_with_its_arguments_charges_what_it_says() {
    for (tag, call) in [("same", "Sp.op[U = Int64](x, 5, 6)"), ("none", "Sp.op(x, 5, 6)")] {
        let src = effects_program(
            &format!("wijpsdh.eff_agree_{tag}"),
            DEFAULTED_OP,
            CAR_OP_KU,
            "Int64",
            call,
        );
        assert_eq!(crate::common::try_load_kb_with(&src).err(), None, "{tag}");
    }
    let src = effects_program(
        "wijpsdh.eff_nojoin",
        DEFAULTED_OP,
        CAR_OP_KU,
        "String",
        "Sp.op(x, 5, \"s\")",
    );
    assert_refused_naming(
        &load_errors(&src),
        &["no common type for type parameter `W` of `op`: Int64 (k), String (u)"],
        "no bracket, two arguments",
    );
}

/// A BRACKET WIDER THAN ITS ARGUMENTS IS WHAT THE OVERRIDE CHARGES, a fitting member and no
/// default body: `Sp.op[U = Animal](x, c1, c1)` over `Car.op[W](c, a: W, b: W) effects
/// {Error[W]}` charges `Error[Animal]` on both spellings — `via` declaring `Error[cat]` is
/// refused and declaring `Error[Animal]` loads. From the arguments alone it is `Error[cat]`.
#[test]
fn a_bracket_wider_than_its_arguments_is_what_the_override_charges() {
    let spec_op = "operation op[U](s: Self, a: U, b: U) -> Int64";
    let member =
        "operation op[W](c: Self, a: W, b: W) -> Int64 effects {Error[W]} = Error.raise(b)";
    for (q, call) in [
        ("sp", "Sp.op[U = Animal](x, c1, c1)"),
        ("car", "Car.op[W = Animal](x, c1, c1)"),
    ] {
        let src = |tag: &str, declared: &str| {
            effects_program(
                &format!("wijpsdh.eff_wider_{tag}_{q}"),
                spec_op,
                member,
                declared,
                call,
            )
        };
        assert_refused_naming(
            &load_errors(&src("bad", "cat")),
            &["expected declared: [Error[T = cat]], got undeclared effect: Error[T = Animal]"],
            q,
        );
        assert_eq!(
            crate::common::try_load_kb_with(&src("ok", "Animal")).err(),
            None,
            "{q}"
        );
    }
}

/// A PARAMETER THE BRACKET FIXES IS READ THROUGH THE CALL'S RE-KEY WHERE ITS ARGUMENT IS
/// JUDGED: `st: Strm[T = W2, E = {Modify[hh]}]` holds a value-in-type naming the override's
/// own `hh`, for which the call passes `k`, so a stream writing `k` is that parameter's
/// argument — through the spec as through the carrier, where the spec's return holds `s.E`
/// (the fallback) and where it holds no projection (the override read for its effects). Read
/// as written, both spec spellings were refused "expected Strm[T = Int64, E = {Modify[T =
/// hh]}], got Strm[T = Int64, E = {Modify[T = k]}]" (MEASURED, on the tree before this row;
/// the workspace suite was green on it). Passes with every part of the ledger backed out —
/// the judgement backed out judges nothing.
#[test]
fn a_parameter_the_bracket_fixes_is_read_through_the_calls_rekey() {
    let program = |ns: &str, spec_ret: &str, member_ret: &str, call: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Option, Pair, Cell, Modify}}
  import anthill.prelude.Option.{{some, none}}
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(x: T)
  end
  sort Sp
    sort T = ?
    effects E = ?
    operation feed[W](s: Self, h: Cell[V = Int64], st: Strm[T = W, E = {{Modify[h]}}], w: W) -> {spec_ret}
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = Self, E = {{EC}}]
    operation feed[W2](c: Self, hh: Cell[V = Int64], st: Strm[T = W2, E = {{Modify[hh]}}], w: W2) -> {member_ret}
  end
  operation use[R](a: Car[V = Int64, EC = R], k: Cell[V = Int64], st: Strm[T = Int64, E = {{Modify[k]}}]) -> Int64 effects {{R, Modify[k]}} =
    match {call}(a, k, st, 5)
      case some(p) -> 1
      case none() -> 7
end
"#
        )
    };
    let paths = [
        (
            "fallback",
            "Option[T = Pair[A = s.T, B = W]] effects {s.E, Modify[h]}",
            "Option[T = Pair[A = Car[V = V, EC = EC], B = W2]] effects {EC, Modify[hh]} = none",
        ),
        (
            "effects",
            "Option[T = W] effects {Modify[h]}",
            "Option[T = W2] effects {Modify[hh]} = none",
        ),
    ];
    for (path, spec_ret, member_ret) in paths {
        for (q, call) in [("sp", "Sp.feed[W = Int64]"), ("car", "Car.feed[W2 = Int64]")] {
            let src = program(&format!("wijpsdh.rekey_{path}_{q}"), spec_ret, member_ret, call);
            assert_eq!(
                crate::common::try_load_kb_with(&src).err(),
                None,
                "{path} {q}"
            );
        }
    }
}

// ── the bracket left unwritten ────────────────────────────────────────────────

/// AN UNWRITTEN BRACKET IS REFUSED NAMING THE SPEC OPERATION'S PARAMETER: nothing fixes `W`
/// in `Sp.pick2(a, b)`, and the refusal says so and how to write it — the spec operation's
/// own name for it, which is what this call's bracket can bind: with two parameters and one
/// written, the other is named `X`, where the override calls its own `Q`. It was "type Car
/// has no member E". THE ADVISED REPAIR RUNS: the bracket written, the call answers 7.
#[test]
fn an_unwritten_bracket_is_refused_naming_the_spec_operations_parameter() {
    let errs = refusals(
        "wijpsdh.unwritten",
        PICK2,
        CAR_PICK2,
        &format!("    match Sp.pick2(a, b)\n{ARMS}"),
    );
    assert_refused_naming(
        &errs,
        &[
            "wijpsdh.unwritten.Sp.pick2.type_arg",
            "expected a type for 'W', got unconstrained — use `pick2[W = …](…)`",
        ],
        "the spec operation's parameter",
    );
    assert!(
        !errs.iter().any(|e| e.contains("has no member")),
        "one refusal, the parameter's: {errs:#?}"
    );
    assert_eq!(
        run(
            "wijpsdh.unwritten_repaired",
            PICK2,
            CAR_PICK2,
            &format!("    match Sp.pick2[W = Int64](a, b)\n{ARMS}"),
        ),
        Ok(7)
    );

    let spec2 = "operation pick2[W, X](x: T, s: Self) -> Option[T = Pair[A = W, B = Pair[A = \
                 s.T, B = X]]] effects s.E";
    let member2 = "operation pick2[P, Q](x: Car[V = ?, EC = ?], s: Self) -> Option[T = Pair[A = \
                   P, B = Pair[A = Car[V = V, EC = EC], B = Q]]] effects {EC} = none";
    let errs = refusals(
        "wijpsdh.unwritten_two",
        spec2,
        member2,
        &format!("    match Sp.pick2[W = Int64](a, b)\n{ARMS}"),
    );
    assert_refused_naming(
        &errs,
        &[
            "wijpsdh.unwritten_two.Sp.pick2.type_arg",
            "expected a type for 'X', got unconstrained — use `pick2[X = …](…)`",
        ],
        "the second parameter, by the spec's name",
    );
    assert_eq!(
        run(
            "wijpsdh.unwritten_two_repaired",
            spec2,
            member2,
            &format!("    match Sp.pick2[W = Int64, X = String](a, b)\n{ARMS}"),
        ),
        Ok(7)
    );
}

/// … AS THE OTHER TWO ROUTES REFUSE IT: the carrier spelling names the override's parameter,
/// and the spec spelling over a receiver typed by the spec itself — whose `s.E` eliminates,
/// so no override is read — names the spec's. Passes with every part of the ledger backed
/// out.
#[test]
fn an_unwritten_bracket_on_the_other_two_routes_is_refused_alike() {
    assert_refused_naming(
        &refusals(
            "wijpsdh.unwritten_car",
            PICK2,
            CAR_PICK2,
            &format!("    match Car.pick2(a, b)\n{ARMS}"),
        ),
        &[
            "wijpsdh.unwritten_car.Car.pick2.type_arg",
            "expected a type for 'W', got unconstrained — use `pick2[W = …](…)`",
        ],
        "the carrier spelling",
    );
    let abstract_receiver = format!(
        "  operation use[R](a: Sp[T = Int64, E = R]) -> Int64 effects {{R}} =\n    match \
         Sp.pick2(1, a)\n{ARMS}\n"
    );
    assert_refused_naming(
        &load_errors(&program(
            "wijpsdh.unwritten_abs",
            PICK2,
            CAR_PICK2,
            &abstract_receiver,
        )),
        &[
            "wijpsdh.unwritten_abs.Sp.pick2.type_arg",
            "expected a type for 'W', got unconstrained — use `pick2[W = …](…)`",
        ],
        "a receiver typed by the spec",
    );
}

/// … AND NOT WHERE THE EXPECTED TYPE FIXES IT: the result annotated, `Sp.pick2(a, b)` loads
/// with no bracket on both spellings. Passes with every part of the ledger backed out.
#[test]
fn an_unwritten_parameter_the_expected_type_fixes_loads() {
    for q in ["Sp", "Car"] {
        let body = format!(
            "    let r: Option[T = Pair[A = Car[V = Int64, EC = R], B = Int64]] = {q}.pick2(a, \
             b)\n    7"
        );
        assert_eq!(
            run(&format!("wijpsdh.expected_{q}"), PICK2, CAR_PICK2, &body),
            Ok(7),
            "{q}"
        );
    }
}

/// … NOR FOR AN OVERRIDE PARAMETER THAT STANDS AT NO PARAMETER OF THE SPEC'S: `Car.pick`'s
/// `X` stands where the spec writes `s.T`, so no bracket of `Sp.pick` could bind it and the
/// call keeps the refusal it had. Passes with every part of the ledger backed out.
#[test]
fn an_override_parameter_standing_at_no_spec_parameter_still_declines() {
    let spec_op = "operation pick(x: T, s: Self) -> Option[T = Pair[A = s.T, B = Sp[T = s.T, E \
                   = s.E]]] effects s.E = none";
    let member = "operation pick[W, R, X](x: Car[V = W, EC = R], s: Self) -> Option[T = Pair[A \
                  = X, B = Car[V = V, EC = EC]]] effects {EC} = none";
    let errs = refusals(
        "wijpsdh.own",
        spec_op,
        member,
        &format!("    match Sp.pick(a, b)\n{ARMS}"),
    );
    assert_refused_naming(
        &errs,
        &["pick.return", "has no member 'E'"],
        "the spec's own refusal",
    );
    assert!(
        !errs.iter().any(|e| e.contains("unconstrained")),
        "no bracket is advised: {errs:#?}"
    );
}

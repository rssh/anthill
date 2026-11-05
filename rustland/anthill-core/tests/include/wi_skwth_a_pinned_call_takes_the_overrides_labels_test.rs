//! WI-20260825-SKWTH (user decision 2026-11-05) — A CALL PINNED TO AN OVERRIDE IS CHARGED THE
//! OVERRIDE'S ROW, LABELS INCLUDED, AND IS REFUSED ONLY FOR WHAT THAT ROW REFUSES.
//!
//! WI-20260930-GJW9Z made a pinned call take what the override declares, read at the call, in
//! place of the spec operation's row VARIABLES, and kept the spec's LABELS beside it
//! (`typing::effects_of_pinned_call`). A label an override narrows away was therefore still
//! charged through the spec spelling and not through the carrier's: a bare `a / b` over `Float`
//! paid `Divisible.div`'s guarded `Error[DivisionByZero]`, which `Float.div` does not declare
//! (`wi_vt8cf_division_tower_test::a_bare_float_division_is_charged_float_divs_row`). The spec's
//! row is the widest an override may declare, so the override's narrowing is what the call
//! incurs, and the spec spelling is now charged what the qualified one is (kernel-language §8.7).
//!
//! THE SPEC'S ROW WAS ALSO JUDGED before the pin, and two of its verdicts refused the call
//! outright: a guarded atom held to the caller's guarded row (`hold_call_to_guarded_row`) and a
//! `Modify` over an argument that names no place. Both are now held until the call is known to
//! be charged that row (`typing::SpecRowVerdict`); the override's atoms are held to the same two
//! checks where its row is read.
//!
//! THE CENSUS, MEASURED before the change over every load of the workspace with the labels
//! dropped: two populations changed and no other. `Float.div`, and a receiver's row the spec
//! reads (`Stream.splitFirst … effects s.E`) at a carrier whose override declares none — charged
//! where the receiver's row was ground, NOT where it was a row variable, and never through the
//! carrier's own `splitFirst` (`a_receivers_row_the_override_does_not_declare_is_not_charged`).
//!
//! WHICH PINS ARE DRIVEN. Every pin decides in `effects_of_pinned_call`; the rows reach it from
//! the body-less dispatch (most rows), from a defaulted spec operation's supplier, and from an
//! instance's operation binding. The two pins that reach a defaulted operation through another
//! sort's provision, and the WI-606 no-candidate pin, go through the same function and are not
//! driven here with a label.
//!
//! BACKED OUT, MEASURED, each `…_not_charged` / `…_not_held` / `…_not_refused` row fails, and the
//! rest pass either way BY DESIGN — a label the override declares is charged, a call no override
//! is pinned to is charged and judged by the spec's row, a default body that runs is charged its
//! own — so the fix narrows only what the override narrows:
//!
//!  * labels kept (`effects_of_pinned_call` keeping the spec op's non-variable effects beside the
//!    override's, as GJW9Z left it): all of them, each refused "undeclared effect: …" or by the
//!    guarded-row / placeless check;
//!  * the labels dropped but the two checks immediate (`SpecRowVerdict::new(false)` in
//!    `check_apply_iter`): `a_narrowed_label_is_not_held_to_the_callers_guarded_row` and
//!    `a_narrowed_modify_is_not_refused_as_placeless` alone.
//!
//! A row the override leaves OPEN at the call keeps the spec's row beside it, as before
//! (`wi_gjw9z_spec_call_charges_the_callers_row_test::an_override_row_left_open_keeps_the_spec_row`).

use crate::common::{load_errors_of, run_int64};

/// Assert that ONE refusal carries every token — the call's own, not a sentence assembled from
/// two errors.
fn assert_one_refusal_naming(errs: &[String], tokens: &[&str], why: &str) {
    assert!(
        errs.iter().any(|e| tokens.iter().all(|t| e.contains(t))),
        "{why}: expected one refusal naming {tokens:?}, got {errs:#?}"
    );
}

/// `Sp.op` declares an UNGUARDED `Error[Oops]`, with `spec_body` (`""` for none); `Car.op` is the
/// carrier's member, `member` (`""` for none).
fn label_program(ns: &str, spec_body: &str, member: &str, extra: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Error}}
  sort Oops
    entity oops
  end
  sort Sp
    sort T = ?
    operation op(x: T) -> Int64 effects Error[Oops]{spec_body}
  end
  sort Car
    entity car(v: Int64)
    provides Sp[T = Car]
    {member}
  end
{extra}
end
"#
    )
}

const PURE_OP: &str = "operation op(x: Car) -> Int64 = x.v";
const RAISING_OP: &str = "operation op(x: Car) -> Int64 effects Error[Oops] = x.v";
const CALLS: &str = "  operation viaSpec() -> Int64 = Sp.op(car(v: 3))\n  \
                     operation viaCar() -> Int64 = Car.op(car(v: 4))";

/// THE LABEL THE OVERRIDE NARROWS AWAY: `Car.op` declares nothing, so `Sp.op(car(…))` — pinned
/// to it, the carrier being static — is pure, as `Car.op(car(…))` is, and both run.
#[test]
fn a_label_the_override_narrows_away_is_not_charged() {
    let ns = "wi_skwth.narrow";
    let src = label_program(ns, "", PURE_OP, CALLS);
    assert_eq!(run_int64(&src, &format!("{ns}.viaSpec")), Ok(3));
    assert_eq!(run_int64(&src, &format!("{ns}.viaCar")), Ok(4));
}

/// CONTROL — the label the override DECLARES is charged, through either spelling. Passes with the
/// change backed out.
#[test]
fn a_label_the_override_declares_is_charged_both_ways() {
    let errs = load_errors_of(&label_program("wi_skwth.kept", "", RAISING_OP, CALLS));
    for op in ["viaSpec", "viaCar"] {
        assert_one_refusal_naming(
            &errs,
            &[&format!("{op}.effects"), "undeclared effect: Error[T = Oops]"],
            &format!("`{op}` incurs the override's declared label"),
        );
    }
}

/// A DEFAULTED SPEC OPERATION'S SUPPLIER: `Sp.op` has a default body raising `Error[Oops]`, and
/// `Car.op` supplies the carrier's own, pure — the call is pinned to it, and runs pure. The
/// CONTROL is the same call where `Car` supplies none: the default body runs, and is charged.
#[test]
fn a_label_the_supplier_of_a_defaulted_operation_narrows_away_is_not_charged() {
    let ns = "wi_skwth.dflt";
    let src = label_program(ns, " = Error.raise(oops)", PURE_OP, CALLS);
    assert_eq!(run_int64(&src, &format!("{ns}.viaSpec")), Ok(3));

    let errs = load_errors_of(&label_program(
        "wi_skwth.dflt_runs",
        " = Error.raise(oops)",
        "",
        "  operation viaSpec() -> Int64 = Sp.op(car(v: 3))",
    ));
    assert_one_refusal_naming(
        &errs,
        &["viaSpec.effects", "undeclared effect: Error[T = Oops]"],
        "the default body runs, and its row is charged",
    );
}

/// CONTROL — a call nothing pins to an override, over a type parameter its caller requires `Sp`
/// at, is charged the SPEC's row: no implementation is known there, and the spec's row is what
/// any of them may incur. Declared, it runs. Passes with the change backed out.
#[test]
fn an_unpinned_call_is_charged_the_specs_label() {
    let errs = load_errors_of(&label_program(
        "wi_skwth.unpinned",
        "",
        PURE_OP,
        "  operation viaReq[A](x: A) -> Int64 requires Sp[T = A] = Sp.op(x)",
    ));
    assert_one_refusal_naming(
        &errs,
        &["viaReq.effects", "undeclared effect: Error[T = Oops]"],
        "an unpinned spec call is charged the spec's label",
    );

    let ns = "wi_skwth.unpinned_declared";
    let src = label_program(
        ns,
        "",
        PURE_OP,
        "  operation viaReq[A](x: A) -> Int64 requires Sp[T = A] effects Error[Oops] = Sp.op(x)\n  \
         operation go() -> Int64 effects Error[Oops] = viaReq(car(v: 5))",
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(5));
}

/// AN INSTANCE'S OPERATION BINDING: `CpsM.unit` declares `Error[Oops]`, and `Option`'s instance
/// binds it to `optionUnit`, `impl_effects`. `go` reads `unit(42)` at an `Option`.
fn instance_program(ns: &str, impl_effects: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.{{Option, Int64, Error}}
  import {ns}.CpsM.{{unit}}
  sort Oops
    entity oops
  end
  sort CpsM[F[T]]
    operation unit[A](a: A) -> F[T = A] effects Error[Oops]
  end
  operation optionUnit[A](a: A) -> Option[T = A]{impl_effects} = some(a)
  operation go() -> Int64 =
    let o: Option[T = Int64] = unit(42)
    match o
      case some(v) -> v
      case none() -> 0
end

namespace anthill.prelude.Option
  import {ns}.CpsM
  provides CpsM[F = Self, unit = {ns}.optionUnit]
end
"#
    )
}

/// …PINNED TO THE BOUND OPERATION, which is pure: `unit(42)` runs pure. The CONTROL binds one
/// declaring the label, and the same call is charged it — passes with the change backed out.
#[test]
fn a_label_the_bound_operation_narrows_away_is_not_charged() {
    let ns = "wi_skwth.inst";
    assert_eq!(
        run_int64(&instance_program(ns, ""), &format!("{ns}.go")),
        Ok(42)
    );
    assert_one_refusal_naming(
        &load_errors_of(&instance_program("wi_skwth.inst_err", " effects Error[Oops]")),
        &["go.effects", "undeclared effect: Error[T = Oops]"],
        "the bound operation's label is charged",
    );
}

/// THE SPEC'S GUARDED ATOM IS NOT HELD TO THE CALLER'S GUARDED ROW where the call is pinned to an
/// override that does not incur it. `f` admits `Error[DivisionByZero]` only where `eq(d, 0)`;
/// `a / b` is pinned to `Float.div`, so `Divisible.div`'s `eq(b, 0)` — which nothing shows — is
/// nothing `f` must answer for, as `Float.div(a, b)` is not. Refused, the guarded-row check named
/// `div` at the bare `a / b` (MEASURED). `go` calls `f` with `d = 2`, refuting the guard.
#[test]
fn a_narrowed_label_is_not_held_to_the_callers_guarded_row() {
    let ns = "wi_skwth.guarded";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Float, Bool, Error, DivisionByZero}}
  import anthill.prelude.PartialEq.{{eq}}
  operation f(a: Float, b: Float, n: Int64, d: Int64) -> Int64
    effects {{ Error[DivisionByZero] :- eq(d, 0) }} =
    if Float.isInfinite(a / b) then n / d else 0
  operation go() -> Int64 = f(1.0, 0.0, 7, 2)
end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(3));
}

/// CONTROL — the guarded-row check still refuses what the charged row incurs: the override's own
/// atom (`Int64.div`'s, at `n / d` under a guard on another operand), and the spec's at a call no
/// override is pinned to. Passes with the change backed out.
#[test]
fn a_guarded_atom_the_charged_row_incurs_is_still_held() {
    for (tag, sig, body) in [
        (
            "pinned",
            "(n: Int64, d: Int64, e: Int64) -> Int64 effects { Error[DivisionByZero] :- eq(e, 0) }",
            "n / d",
        ),
        (
            "unpinned",
            "[A](x: A, y: A) -> A requires Divisible[T = A] \
             effects { Error[DivisionByZero] :- eq(x, 0) }",
            "x / y",
        ),
    ] {
        let src = format!(
            "namespace wi_skwth.held_{tag}\n  \
             import anthill.prelude.{{Int64, Error, DivisionByZero, Divisible}}\n  \
             import anthill.prelude.PartialEq.{{eq}}\n  \
             operation f{sig} = {body}\nend\n"
        );
        assert_one_refusal_naming(
            &load_errors_of(&src),
            &["f.effects", "the call of `div` incurs `Error[T = DivisionByZero]`"],
            &format!("`{body}` ({tag}) incurs the guarded atom its row holds"),
        );
    }
}

/// THE SPEC'S `Modify[x]` IS NOT REFUSED AS PLACELESS where the call is pinned to an override that
/// does not incur it: `Sp.touch(car(…))` passes a constructor, which names no place, and
/// `Car.touch` modifies nothing — the call runs, as `Car.touch(car(…))` does. Refused, it was
/// "expected an argument naming a PLACE, because `….Sp.touch` declares `Modify[x]`" (MEASURED).
/// The CONTROL is the same call at a type parameter, where no override is pinned and the spec's
/// `Modify[x]` is the row: still refused, and passes with the change backed out.
#[test]
fn a_narrowed_modify_is_not_refused_as_placeless() {
    let spec = "  sort Sp\n    sort T = ?\n    \
                operation touch(x: T) -> Int64 effects Modify[x]\n    \
                operation make() -> T\n  end\n";
    let ns = "wi_skwth.placeless";
    let src = format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64, Modify}}\n{spec}  \
         sort Car\n    entity car(v: Int64)\n    provides Sp[T = Car]\n    \
         operation touch(x: Car) -> Int64 = x.v\n    \
         operation make() -> Car = car(v: 0)\n  end\n  \
         operation viaSpec() -> Int64 = Sp.touch(car(v: 3))\n  \
         operation viaCar() -> Int64 = Car.touch(car(v: 4))\nend\n"
    );
    assert_eq!(run_int64(&src, &format!("{ns}.viaSpec")), Ok(3));
    assert_eq!(run_int64(&src, &format!("{ns}.viaCar")), Ok(4));

    let unpinned = format!(
        "namespace wi_skwth.placeless_unpinned\n  import anthill.prelude.{{Int64, Modify}}\n{spec}  \
         operation viaReq[A](x: A) -> Int64 requires Sp[T = A] effects Modify[x] =\n    \
         Sp.touch(Sp.make[T = A]())\nend\n"
    );
    assert_one_refusal_naming(
        &load_errors_of(&unpinned),
        &["touch.x", "expected an argument naming a PLACE"],
        "an unpinned call is judged by the spec's row",
    );
}

/// A RECEIVER'S ROW THE OVERRIDE DOES NOT DECLARE: `Stream.splitFirst` declares `effects s.E`,
/// `Cnt` provides `Stream` at its own `E`, and `Cnt.splitFirst` declares nothing. The four
/// spellings — the spec's and the carrier's, at a ground `E` and at a row variable — are charged
/// one row, the override's; backed out, the spec spelling at the ground row alone was refused
/// "undeclared effect: Error[T = EmptyStream]" (MEASURED), the one of the four where the spec's
/// `s.E` resolved to labels rather than to a variable.
#[test]
fn a_receivers_row_the_override_does_not_declare_is_not_charged() {
    let ns = "wi_skwth.receiver";
    let src = format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, List, Option, Pair, Stream, Error, EmptyStream}}
  import anthill.prelude.List.{{cons, nil}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Pair.{{pair}}
  sort Cnt
    sort T = ?
    effects E = ?
    entity cnt(items: List[T])
    provides Stream[T = T, E = E]
    operation splitFirst(c: Self) -> Option[Pair[A = T, B = Cnt[T = T, E = E]]] =
      match List.splitFirst(c.items)
        case none() -> none
        case some(pair(h, t)) -> some(pair(h, cnt(t)))
  end
  operation ground(x: Cnt[T = Int64, E = {{Error[EmptyStream]}}]) -> Int64 =
    match Stream.splitFirst(x)
      case some(pair(h, _)) -> h
      case none() -> 0
  operation groundCar(x: Cnt[T = Int64, E = {{Error[EmptyStream]}}]) -> Int64 =
    match Cnt.splitFirst(x)
      case some(pair(h, _)) -> h
      case none() -> 0
  operation open[R](x: Cnt[T = Int64, E = R]) -> Int64 =
    match Stream.splitFirst(x)
      case some(pair(h, _)) -> h
      case none() -> 0
  operation openCar[R](x: Cnt[T = Int64, E = R]) -> Int64 =
    match Cnt.splitFirst(x)
      case some(pair(h, _)) -> h
      case none() -> 0
  operation go() -> Int64 =
    let c: Cnt[T = Int64, E = {{Error[EmptyStream]}}] = cnt(items: cons(7, nil))
    ground(c) + groundCar(c) + open(c) + openCar(c)
end
"#
    );
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(28));
}

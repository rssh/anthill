//! WI-20261122-CXR5B, fourth step — A WITNESS OF A HIGHER-KINDED SPEC (c1 of
//! `docs/design/spec-carrier-set.md`): `BoxM provides Monad[M = Box]` answers
//! `Monad.flatMap(box(v: 41), …)`.
//!
//! The cause, named as §7 asks, is two readers:
//! - which type-var an operation takes (`spec_carrier_param`) counted a parameter typed at a
//!   bare type-var only (`declared_type_param_vid`'s arity pin), so `Monad`, whose operations take
//!   `m: M[A]`, took none, and no provision of it was a witness at another sort; it now counts a
//!   type-var heading an application (`declared_type_param_head_vid`);
//! - the higher-kinded branch of `check_apply_call` (WI-453), with `M` filled to `Box` by the
//!   argument, asked only `Box`'s own provision of `Monad`, and refused "no impl matches"; a call
//!   a witness at `Box` answers, or whose bracket names a provider other than `Box`, now goes to
//!   the resolution after it, which weighs the witnesses, reads the bracket and discharges a
//!   provision's conditions.
//!
//! WHAT FAILS IF THIS IS BACKED OUT, and what passes either way, is said at each row. MEASURED
//! 2026-11-22, these rows kept: with `src/` at `4467ab69f`, 4 of the first 5 fail and the
//! control passes (the sixth row, added after, fails at its refusal); with the branch alone backed out, the same 4; with the operation carrier's reader
//! alone, 3 (the bracket row passes: it needs only the branch to read the bracket).

use crate::common::{interp_for, load_errors_of};

/// `Box`, the witnesses `names` of `Monad[M = Box]` (each with the members a `Monad` has), and
/// a driver whose `go` is `call`.
fn program(ns: &str, names: &[&str], own: bool, call: &str) -> String {
    let members = "    operation pure[A](a: A) -> Box[T = A] = box(v: a)\n    \
                   operation flatMap[A, B, EffP](m: Box[T = A], f: (A) -> Box[T = B] @ {EffP}) -> Box[T = B] effects {EffP} =\n      \
                   match m\n        case box(x) -> f(x)\n    \
                   operation map[A, B, EffP](m: Box[T = A], f: (A) -> B @ {EffP}) -> Box[T = B] effects {EffP} =\n      \
                   match m\n        case box(x) -> box(v: f(x))\n  end\n";
    let witnesses: String =
        names.iter().map(|w| format!("  sort {w}\n    provides Monad[M = Box]\n{members}")).collect();
    let box_own = if own { format!("    provides Monad[M = Self]\n{members}") } else { "  end\n".into() };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Monad}}
  sort Box
    sort T = ?
    entity box(v: T)
{box_own}{witnesses}  operation unbox(b: Box[T = Int64]) -> Int64 =
    match b
      case box(x) -> x
  sort Driver
    operation go() -> Int64 = unbox({call}(box(v: 41), lambda (x: Int64) -> box(v: x + 1)))
  end
end
"#
    )
}

/// What `{ns}.Driver.go()` answers.
fn go(src: &str, ns: &str) -> i64 {
    match interp_for(src)
        .call(&format!("{ns}.Driver.go"), &anthill_core::eval::HostValue::all(&[]))
        .map(|h| h.value)
        .unwrap_or_else(|e| panic!("`{ns}.Driver.go`: {e:?}"))
    {
        anthill_core::eval::Value::Int(n) => n,
        other => panic!("`{ns}.Driver.go` answered no Int64: {other:?}"),
    }
}

/// c1: the one witness at `Box` answers. FAILS backed out: refused at load, "`Monad.flatMap`
/// … no impl matches" — with either reader alone backed out too.
#[test]
fn a_witness_of_a_higher_kinded_spec_answers_its_call() {
    let ns = "wicxr5bhk.one";
    assert_eq!(go(&program(ns, &["BoxM"], false, "Monad.flatMap"), ns), 42);
}

/// Two witnesses at `Box` and no bracket: refused at the call, naming both and the bracket that
/// selects one; the bracket naming either answers. The refusal FAILS backed out, where the call
/// was refused "no impl matches", naming neither.
#[test]
fn two_witnesses_at_one_carrier_are_named_at_the_call() {
    let ns = "wicxr5bhk.two";
    let text = load_errors_of(&program(ns, &["BoxM", "BoxM2"], false, "Monad.flatMap")).join("\n");
    for want in ["2 instances provide", "BoxM", "BoxM2", "[Monad = "] {
        assert!(text.contains(want), "`{want}` missing:\n{text}");
    }
    for named in ["BoxM", "BoxM2"] {
        let ns = format!("wicxr5bhk.named{named}");
        let call = format!("Monad.flatMap[Monad = {named}]");
        assert_eq!(go(&program(&ns, &["BoxM", "BoxM2"], false, &call), &ns), 42, "{ns}");
    }
}

/// CONTROL, c2: `Box` providing `Monad` for itself answers, as it did. Passes either way, by
/// design.
#[test]
fn the_carriers_own_provision_still_answers() {
    let ns = "wicxr5bhk.own";
    assert_eq!(go(&program(ns, &[], true, "Monad.flatMap"), ns), 42);
}

/// A bracket naming the witness beside the carrier's OWN provision runs the witness (whose
/// `flatMap` answers `empty`, 0), and with no bracket the carrier's own answers (42), its
/// inferred default. FOUND BY /code-review: the branch read no bracket, and ran `Box`'s own
/// under `[Monad = BoxM]` — which it did before this step too, so the bracket half FAILS backed
/// out and the unbracketed half passes either way, by design.
#[test]
fn a_bracket_naming_the_witness_beside_the_carriers_own_runs_the_witness() {
    let program = |ns: &str, call: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, Monad}}
  sort Box
    sort T = ?
    entity box(v: T)
    entity empty
    provides Monad[M = Self]
    operation pure[A](a: A) -> Box[T = A] = box(v: a)
    operation flatMap[A, B, EffP](m: Box[T = A], f: (A) -> Box[T = B] @ {{EffP}}) -> Box[T = B] effects {{EffP}} =
      match m
        case box(x) -> f(x)
        case empty -> empty
    operation map[A, B, EffP](m: Box[T = A], f: (A) -> B @ {{EffP}}) -> Box[T = B] effects {{EffP}} =
      match m
        case box(x) -> box(v: f(x))
        case empty -> empty
  end
  sort BoxM
    provides Monad[M = Box]
    operation pure[A](a: A) -> Box[T = A] = box(v: a)
    operation flatMap[A, B, EffP](m: Box[T = A], f: (A) -> Box[T = B] @ {{EffP}}) -> Box[T = B] effects {{EffP}} = empty
    operation map[A, B, EffP](m: Box[T = A], f: (A) -> B @ {{EffP}}) -> Box[T = B] effects {{EffP}} = empty
  end
  operation unbox(b: Box[T = Int64]) -> Int64 =
    match b
      case box(x) -> x
      case empty -> 0
  sort Driver
    operation go() -> Int64 = unbox({call}(box(v: 41), lambda (x: Int64) -> box(v: x + 1)))
  end
end
"#
        )
    };
    let ns = "wicxr5bhk.ownnamed";
    assert_eq!(go(&program(ns, "Monad.flatMap[Monad = BoxM]"), ns), 0, "the bracket names BoxM");
    let ns = "wicxr5bhk.ownunnamed";
    assert_eq!(go(&program(ns, "Monad.flatMap"), ns), 42, "the carrier's own");
}

/// A witness whose provision's CONDITION nothing meets answers no call: refused, naming the
/// condition. FOUND BY /code-review: a first cut took the witness in the higher-kinded branch
/// and ran it (7). Refused either way, by design (before, as no impl at all); the unmet condition
/// named FAILS backed out.
#[test]
fn a_conditional_witness_answers_only_where_its_condition_holds() {
    let src = r#"
namespace wicxr5bhk.cond
  import anthill.prelude.{Int64}
  sort Gate
    sort T = ?
    operation ok(x: T) -> Int64
  end
  sort Wrap[W[T]]
    operation unwrap[A](w: W[A]) -> Int64
  end
  sort Box
    sort T = ?
    entity box(v: T)
  end
  sort WBox
    sort T = ?
    provides Wrap[W = Box] :- Gate[T = Int64]
    operation unwrap[A](w: Box[T = A]) -> Int64 = 7
  end
  sort Driver
    operation go() -> Int64 = Wrap.unwrap(box(v: 1))
  end
end
"#;
    let text = load_errors_of(src).join("\n");
    for want in ["no impl matches", "unresolved", "Gate[T"] {
        assert!(text.contains(want), "`{want}` missing:\n{text}");
    }
}

/// MOVED, decided with the user 2026-11-22: a bare provision of a higher-kinded spec whose
/// operation takes `W[A]` leaves the type-var the operation takes unbound, and is refused as a
/// bare provision of a spec whose operation takes its type-var directly is (decision 3's
/// direction); the binding written, it answers. It loaded and answered 7 before this step, so the
/// refusal FAILS backed out; the repaired spelling passes either way, by design.
#[test]
fn a_bare_provision_of_a_higher_kinded_spec_names_its_carrier() {
    let program = |ns: &str, provides: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Wrap[W[T]]
    operation unwrap[A](w: W[A]) -> Int64
  end
  sort Box
    sort T = ?
    entity box(v: T)
    {provides}
    operation unwrap[A](w: Box[T = A]) -> Int64 = 7
  end
  sort Driver
    operation go() -> Int64 = Wrap.unwrap(box(v: 1))
  end
end
"#
        )
    };
    let text = load_errors_of(&program("wicxr5bhk.bare", "provides Wrap")).join("\n");
    for want in ["binds nothing at", "carrier parameter `W`"] {
        assert!(text.contains(want), "`{want}` missing:\n{text}");
    }
    let ns = "wicxr5bhk.bound";
    assert_eq!(go(&program(ns, "provides Wrap[W = Self]"), ns), 7);
}

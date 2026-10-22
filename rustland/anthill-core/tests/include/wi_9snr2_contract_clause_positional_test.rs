//! WI-20260929-9SNR2 — a positional type argument nested in an operation's `requires` or
//! `ensures` binds its parameter, as in a clause's data slot.
//!
//! `operation needs(x: Int64) -> Int64 requires Store[State = Buf[Int64]]` is
//! `requires Store[State = Buf[T = Int64]]` (kernel-language §5.1: a positional binds the
//! next declared parameter no name took). The loader's term walk normalized a nested
//! bracket to its named form only in a clause's DATA slot; a contract clause converts with
//! const folding off, so `Buf[Int64]` kept its positional, and every reader of a nested
//! binding reads named arguments alone. MEASURED before the fix: the requirement was
//! `Store[State = Buf[]]` — a body call through it loaded and died at run time ("the
//! argument types pin `Store[State = Buf[]]`, and no provider answers it"), and a
//! requirement at `Buf[String]`, which no provision covers, loaded clean where
//! `Buf[T = String]` is refused. The ticket's literal program (the requirement unused) ran
//! either way. A named slot (`requires s: Store[…]`) is the same clause list, and `ensures`
//! the same walk: `ensures KVStore[C, K = String, V = Buf[Int64]]` was refused against a
//! provider at `V = Buf[T = Int64]`, the expected type printed `V = Buf(Int64)`.
//!
//! A sort's `requires`, a call's bracket and a rule body's `require[…]` read the positional
//! before the fix as after; they take other lowerings.
//!
//! ── WHICH ROWS FAIL WHEN THE FIX IS BACKED OUT ───────────────────────────────
//!
//! The fix: `convert_term_inner` normalizes a nested bracket outside a data slot too.
//! Backed out (normalization in a data slot only) and run, 9 FAIL:
//! [`a_requirement_runs_through_the_positional_binding`],
//! [`a_requirement_positional_at_both_levels_runs`] and
//! [`a_named_slot_runs_through_the_positional_binding`] at run time;
//! [`a_requirement_at_an_uncovered_positional_binding_is_refused`] and
//! [`a_named_slot_at_an_uncovered_positional_binding_is_refused`], a clean load;
//! [`a_positional_beside_a_named_argument_binds_the_parameter_left`] and
//! [`a_positional_on_an_alias_binds_the_parameter_it_leaves`], refused at a requirement
//! missing the positional's parameter; [`an_existential_return_takes_the_positional_binding`],
//! refused; and [`an_existential_return_at_an_uncovered_positional_binding_is_refused`] at its
//! message (`V = Buf(String)`).
//!
//! PASSES EITHER WAY, by design: [`the_tickets_program_runs`], the ticket's program, whose
//! body never reads the requirement; [`the_named_spelling_is_the_baseline`]; and
//! [`an_operation_body_and_an_equation_read_the_positional_alike`], measured with the CLI on
//! the parent build and on this one.

use crate::common::{assert_refused_naming, interp_for, load_errors_of};
use anthill_core::eval::Value;

/// `Buf[T]`, `P2[A, B]` with the alias `PA = P2[A = Int64]`, the spec `Store` and two
/// carriers: one at `Buf[T = Int64]`, one at `P2[A = Int64, B = String]`. `body` follows.
fn program(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Bool}}

  sort Buf
    sort T = ?
    entity buf(v: T)
  end

  sort P2
    sort A = ?
    sort B = ?
    entity p2(a: A, b: B)
  end
  sort PA = P2[A = Int64]

  sort Store
    sort State = ?
    operation peek(s: State) -> Int64
  end

  sort BufCarrier
    provides Store[State = Buf[T = Int64]]
    operation peek(s: Buf[T = Int64]) -> Int64 = s.v
  end

  sort PairCarrier
    provides Store[State = P2[A = Int64, B = String]]
    operation peek(s: P2[A = Int64, B = String]) -> Int64 = s.a
  end
{body}
end
"#
    )
}

/// Load `program(ns, body)`, call `ns.go()`, return its `Int64`.
fn answers(ns: &str, body: &str) -> i64 {
    let mut interp = interp_for(&program(ns, body));
    let entry = format!("{ns}.go");
    match interp.call(&entry, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{entry}` must run to an Int64: {other:?}"),
    }
}

fn refused(ns: &str, body: &str) -> Vec<String> {
    load_errors_of(&program(ns, body))
}

// ── an anonymous requirement ──────────────────────────────────────────────────────────

/// THE TICKET'S PROGRAM: the requirement is not read by the body.
#[test]
fn the_tickets_program_runs() {
    let body = "
  operation needs(x: Int64) -> Int64 requires Store[State = Buf[Int64]] = x + 41
  operation go() -> Int64 = needs(1)";
    assert_eq!(answers("wi9snr2.ticket", body), 42);
}

/// The body calls through the requirement, which `Buf[Int64]` must pin at `Buf[T = Int64]`.
#[test]
fn a_requirement_runs_through_the_positional_binding() {
    let body = "
  operation needs(x: Int64) -> Int64 requires Store[State = Buf[Int64]] =
    Store.peek(buf(v: x)) + 41
  operation go() -> Int64 = needs(1)";
    assert_eq!(answers("wi9snr2.through", body), 42);
}

/// Positional at both levels: the spec's `State` by position, and `Buf`'s `T` inside it.
#[test]
fn a_requirement_positional_at_both_levels_runs() {
    let body = "
  operation needs(x: Int64) -> Int64 requires Store[Buf[Int64]] =
    Store.peek(buf(v: x)) + 41
  operation go() -> Int64 = needs(1)";
    assert_eq!(answers("wi9snr2.both", body), 42);
}

/// THE CONTROL: no provision covers `Buf[String]`, so the call cannot be supplied — refused
/// naming the binding, as `Buf[T = String]` is.
#[test]
fn a_requirement_at_an_uncovered_positional_binding_is_refused() {
    let body = "
  operation needs(x: Int64) -> Int64 requires Store[State = Buf[String]] = x + 41
  operation go() -> Int64 = needs(1)";
    let errs = refused("wi9snr2.uncovered", body);
    assert_refused_naming(
        &errs,
        &[
            "cannot be supplied",
            "Store[State = wi9snr2.uncovered.Buf[T = anthill.prelude.String]]",
        ],
        "a requirement at a positional binding no provision covers",
    );
}

/// A positional beside a named argument binds the parameter the name left; written in
/// either order, the requirement is the provider's.
#[test]
fn a_positional_beside_a_named_argument_binds_the_parameter_left() {
    for (ns, binding) in [
        ("wi9snr2.mixed_first", "P2[Int64, B = String]"),
        ("wi9snr2.mixed_second", "P2[String, A = Int64]"),
    ] {
        let body = format!(
            "
  operation needs(x: Int64) -> Int64 requires Store[State = {binding}] =
    Store.peek(p2(a: x, b: \"s\")) + 41
  operation go() -> Int64 = needs(1)"
        );
        assert_eq!(answers(ns, &body), 42, "`{binding}`");
    }
}

/// Through an alias that fixes `A`, the positional binds `B`.
#[test]
fn a_positional_on_an_alias_binds_the_parameter_it_leaves() {
    let body = "
  operation needs(x: Int64) -> Int64 requires Store[State = PA[String]] =
    Store.peek(p2(a: x, b: \"s\")) + 41
  operation go() -> Int64 = needs(1)";
    assert_eq!(answers("wi9snr2.alias", body), 42);
}

/// THE BASELINE the positional rows are read against.
#[test]
fn the_named_spelling_is_the_baseline() {
    let body = "
  operation needs(x: Int64) -> Int64 requires Store[State = Buf[T = Int64]] =
    Store.peek(buf(v: x)) + 41
  operation go() -> Int64 = needs(1)";
    assert_eq!(answers("wi9snr2.named", body), 42);
}

// ── a named requirement slot ──────────────────────────────────────────────────────────

/// `requires s: Store[…]` is the same clause list; the witness is selected at the call.
#[test]
fn a_named_slot_runs_through_the_positional_binding() {
    let body = "
  operation needs(x: Int64) -> Int64 requires s: Store[State = Buf[Int64]] =
    s.peek(buf(v: x)) + 41
  operation go() -> Int64 = needs[s = BufCarrier](1)";
    assert_eq!(answers("wi9snr2.slot", body), 42);
}

/// THE CONTROL: the slot's binding is `Buf[T = String]`, which the body's call at
/// `Buf[T = Int64]` is not.
#[test]
fn a_named_slot_at_an_uncovered_positional_binding_is_refused() {
    let body = "
  operation needs(x: Int64) -> Int64 requires s: Store[State = Buf[String]] =
    s.peek(buf(v: x)) + 41
  operation go() -> Int64 = needs[s = BufCarrier](1)";
    let errs = refused("wi9snr2.slot_uncovered", body);
    assert_refused_naming(
        &errs,
        &["requires s: wi9snr2.slot_uncovered.Store[State = wi9snr2.slot_uncovered.Buf[T = anthill.prelude.String]]"],
        "a named slot at a positional binding the call is not at",
    );
}

// ── an existential return ─────────────────────────────────────────────────────────────

fn existential(ns: &str, value_binding: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Bool}}

  sort Buf
    sort T = ?
    entity buf(v: T)
  end

  sort KVStore
    sort K = ?
    sort V = ?
    operation describe(s: Self) -> Int64
  end

  sort MemStore
    provides KVStore[K = String, V = Buf[T = Int64]]
    entity memStore
    operation describe(s: MemStore) -> Int64 = 42
  end

  operation openStore(p: Bool) -> C ensures KVStore[C, K = String, V = {value_binding}] =
    memStore
  operation go() -> Int64 = openStore(true).describe()
end
"#
    )
}

/// `ensures KVStore[C, …, V = Buf[Int64]]` is met by the provider at `V = Buf[T = Int64]`,
/// and the call runs through the returned carrier.
#[test]
fn an_existential_return_takes_the_positional_binding() {
    let ns = "wi9snr2.ensures";
    let mut interp = interp_for(&existential(ns, "Buf[Int64]"));
    match interp.call(&format!("{ns}.go"), &[]) {
        Ok(Value::Int(n)) => assert_eq!(n, 42),
        other => panic!("`{ns}.go` must run to an Int64: {other:?}"),
    }
}

/// THE CONTROL: the provider does not meet `V = Buf[String]`; refused naming the binding as
/// the named spelling's is.
#[test]
fn an_existential_return_at_an_uncovered_positional_binding_is_refused() {
    let errs = load_errors_of(&existential("wi9snr2.ensures_bad", "Buf[String]"));
    assert_refused_naming(
        &errs,
        &["expected KVStore[K = String, V = Buf[T = String]], got MemStore"],
        "an existential return at a positional binding no provision meets",
    );
}

// ── what the fix also reaches ─────────────────────────────────────────────────────────

/// An operation body and a `@[simp]` equation's right-hand side are converted by the same
/// walk, so the fix normalizes their nested brackets too. Each reads the type through its
/// own lowering as well, which already took the positional: the row passes either way, and
/// holds the two spellings to one type there. The swapped `Pair[Bool, String]` is its
/// control.
#[test]
fn an_operation_body_and_an_equation_read_the_positional_alike() {
    let ns = "wi9snr2.body";
    let src = |inner: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Bool, Type, PartialEq}}

  sort Pair
    sort A = ?
    sort B = ?
    entity pair(a: A, b: B)
  end

  operation named() -> Type = Pair[A = Int64, B = Pair[B = Bool, A = String]]
  operation viaBody() -> Type = Pair[Int64, {inner}]
  operation viaEquation() -> Type
  rule viaEquation() <=> Pair[Int64, {inner}] @[simp]

  operation go() -> Int64 =
    (if PartialEq.eq(viaBody(), named()) then 10 else 0)
      + (if PartialEq.eq(viaEquation(), named()) then 1 else 0)
end
"#
        )
    };
    for (inner, expected) in [("Pair[String, Bool]", 11), ("Pair[Bool, String]", 0)] {
        let mut interp = interp_for(&src(inner));
        match interp.call(&format!("{ns}.go"), &[]) {
            Ok(Value::Int(n)) => assert_eq!(n, expected, "`Pair[Int64, {inner}]`"),
            other => panic!("`{ns}.go` must run to an Int64: {other:?}"),
        }
    }
}

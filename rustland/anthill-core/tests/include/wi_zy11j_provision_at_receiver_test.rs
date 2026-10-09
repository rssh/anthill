//! What a receiver's provision binds a spec parameter to is read where a lambda is hinted,
//! and after the arguments where nothing else says it. Found while closing
//! WI-20261009-ZY11J; it has no ticket of its own.
//!
//! THE RULE. A spec operation's receiver names a carrier, and the carrier's provision of
//! the spec says what each spec parameter is: the carrier's own parameter (`Wrap[A]
//! provides Sp[T = A]`), the carrier itself (`T = Self`), or a type of its own (`Cg
//! provides Sp[T = Rec]`). A callback parameter typed by the spec parameter is hinted
//! with that type, and a result typed by it is that type — for an operation received on
//! the spec (`each(s: Self, …)`) as for one received on a carrier parameter
//! (`visit(c: C, …)`).
//!
//! BEFORE.
//!
//!   - The hint of a self-receiver call read only the parameters the provision binds to
//!     THIS instance. Over `Wrap[A] provides Sp[T = A]`, `Sp.each(w, lambda q -> q.n)` was
//!     refused, "Sp.T.n: … no such member"; and a wider sibling narrowed the lambda where
//!     the carrier takes parameters.
//!   - Neither hint read a plain type. Over `Cg provides Sp[T = Rec]` the same call was
//!     refused the same way, and over `Bag provides Holder[C = Bag, Element = Rec]`,
//!     `Holder.visit(bag, lambda q -> q.n)` was refused at "<unresolved receiver>.n".
//!   - A self-receiver call never bound a plain type at all. `Feed.next(f: Self) -> T` at
//!     `GF provides Feed[T = Int64]` left `T` to the caller's expected type: `operation
//!     go() -> String = Feed.next(gf)` loaded, and answered 5. The carrier-parameter
//!     shape has bound it after the arguments since WI-383; a self receiver now reads it
//!     with the rest of the provision, before them, so a wrong argument is refused where
//!     it is passed.
//!   - A self-receiver call at a carrier that takes no parameters did not read the
//!     provision's compound types before its arguments either, so an argument fixed the
//!     spec parameter and the receiver was refused for it.
//!
//! EVERY ROW HAS ITS OWN SOURCE.
//!
//! CONTROLS — measured, each piece backed out on its own:
//!
//!   the hint of a self-receiver call reading THIS-instance bindings alone
//!   (`bind_self_receiver_params_for_hint` calling `bind_this_instance_params`) — FAIL:
//!     a_lambda_at_a_self_receiver_is_hinted_with_what_the_provision_binds
//!     a_wider_sibling_does_not_narrow_the_lambda_at_a_carrier_with_parameters
//!   a plain type of the provision's own skipped by the shared reading
//!   (`bind_spec_params_from_provision` taking a ground leaf for no value) — FAIL:
//!     a_lambda_at_a_self_receiver_is_hinted_with_what_the_provision_binds
//!     a_lambda_at_another_type_is_refused_where_it_is_passed
//!     a_self_receivers_result_is_what_the_provision_binds
//!   the provision left unread at a receiver whose type writes no argument
//!   (`bind_spec_params_from_provision` returning on an empty `recv_bindings`) — FAIL:
//!     those three, and a_carrier_without_parameters_reads_its_provision_as_one_with_them_does
//!   the carrier-parameter hint without the provision's plain types
//!   (`bind_spec_params_for_hint`'s `bind_ground_value_params_from_provider`) — FAIL:
//!     a_lambda_at_a_carrier_parameter_is_hinted_with_what_the_provision_binds
//!
//!   PASS UNDER EVERY BACK-OUT, by design:
//!     a_lambda_that_needs_no_hint_is_as_it_was
//!     a_carrier_parameters_result_is_what_the_provision_binds

use anthill_core::eval::Value;

use crate::common::{interp_for, try_load_kb_with};

/// The specs and carriers the rows are about, indented for a namespace body.
const DECLS: &str = r#"
  sort Rec
    entity rec(n: Int64)
  end

  sort Sp[T]
    operation each(s: Self, f: (q: T) -> Int64) -> Int64
  end
  sort Cg
    entity cg(n: Int64)
    provides Sp[T = Rec]
    operation each(s: Cg, f: (q: Rec) -> Int64) -> Int64 = f(rec(n: 4))
  end
  sort Car[A]
    entity car(a: A)
    provides Sp[T = Rec]
    operation each(s: Car[A], f: (q: Rec) -> Int64) -> Int64 = f(rec(n: 4))
  end
  sort Wrap[A]
    entity wrap(a: A)
    provides Sp[T = A]
    operation each(s: Wrap[A], f: (q: A) -> Int64) -> Int64 = f(s.a)
  end

  sort Feed[T]
    operation next(f: Self) -> T
    operation twice(f: Self) -> T = next(f)
  end
  sort GF
    entity gf
    provides Feed[T = Int64]
    operation next(f: GF) -> Int64 = 5
  end

  sort Holder[C, Element]
    operation visit(c: C, f: (q: Element) -> Int64) -> Int64
    operation peek(c: C) -> Element
  end
  sort Bag
    entity bag(n: Int64)
    provides Holder[C = Bag, Element = Rec]
    operation visit(c: Bag, f: (q: Rec) -> Int64) -> Int64 = f(rec(n: 4))
    operation peek(c: Bag) -> Rec = rec(n: 9)
  end

  sort Sq[T]
    operation each(s: Self, f: (q: T) -> Int64, z: T) -> Int64
    operation one(s: Self, z: T) -> Int64
  end
  sort Cq[V]
    entity cq(v: V)
    provides Sq[T = (c: Int64, a: Int64)]
    operation each(c: Self, f: (q: (c: Int64, a: Int64)) -> Int64, z: (c: Int64, a: Int64)) -> Int64 = f(z)
    operation one(c: Self, z: (c: Int64, a: Int64)) -> Int64 = z.a
  end
  sort C0
    entity c0
    provides Sq[T = (c: Int64, a: Int64)]
    operation each(c: C0, f: (q: (c: Int64, a: Int64)) -> Int64, z: (c: Int64, a: Int64)) -> Int64 = f(z)
    operation one(c: C0, z: (c: Int64, a: Int64)) -> Int64 = z.a
  end
"#;

fn source(ns: &str, go: &str) -> String {
    format!(
        "namespace test.{ns}\n  import anthill.prelude.{{Int64, String, Bool}}\n{DECLS}\n  operation go() -> {go}\nend\n"
    )
}

/// Load, call `test.<ns>.go()`, and hand back the integer it answers.
fn run(ns: &str, go: &str) -> i64 {
    let mut interp = interp_for(&source(ns, go));
    match interp.call(&format!("test.{ns}.go"), &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{ns}: expected an Int64, got {other:?}"),
    }
}

/// The refusals of a source that must not load, rendered.
fn refusal(ns: &str, go: &str) -> String {
    let errs = try_load_kb_with(&source(ns, go))
        .err()
        .unwrap_or_else(|| panic!("{ns}: must be refused, and loaded clean"));
    format!("{errs:?}")
}

// ── a lambda's hint ─────────────────────────────────────────────────────────

/// A callback parameter typed by the spec's parameter is hinted with what the receiver's
/// provision binds it to: a type of the provision's own, at a carrier with parameters and
/// at one without, and the carrier's own parameter. Each was refused, "Sp.T.n: … no such
/// member".
#[test]
fn a_lambda_at_a_self_receiver_is_hinted_with_what_the_provision_binds() {
    for (name, go, answer) in [
        ("ground", "Int64 =\n    let b: Cg = cg(n: 1)\n    Sp.each(b, lambda q -> q.n)", 4),
        (
            "parametric",
            "Int64 =\n    let b: Car[A = Int64] = Car.car(1)\n    Sp.each(b, lambda q -> q.n)",
            4,
        ),
        ("direct", "Int64 = Sp.each(Car.car(1), lambda q -> q.n)", 4),
        (
            "own",
            "Int64 =\n    let b: Wrap[A = Rec] = Wrap.wrap(rec(n: 6))\n    Sp.each(b, lambda q -> q.n)",
            6,
        ),
    ] {
        let ns = format!("provhint{name}");
        assert_eq!(run(&ns, go), answer, "{ns}");
    }
    // The member the lambda reads is looked for on that type, and named by it.
    let rendered = refusal(
        "provhintmember",
        "Int64 =\n    let b: Cg = cg(n: 1)\n    Sp.each(b, lambda q -> q.zz)",
    );
    assert!(rendered.contains("Rec.zz"), "{rendered}");
}

/// What needed no hint ran before and runs now: the lambda that writes its parameter's
/// type, the dot spelling (which calls the carrier's own operation), and a parameter the
/// body does not read a member of.
#[test]
fn a_lambda_that_needs_no_hint_is_as_it_was() {
    for (name, go, answer) in [
        (
            "annotated",
            "Int64 =\n    let b: Cg = cg(n: 1)\n    Sp.each(b, lambda (q: Rec) -> q.n)",
            4,
        ),
        ("dot", "Int64 =\n    let b: Cg = cg(n: 1)\n    b.each(lambda q -> q.n)", 4),
        (
            "plain",
            "Int64 =\n    let b: Wrap[A = Int64] = Wrap.wrap(6)\n    Sp.each(b, lambda q -> q + 1)",
            7,
        ),
    ] {
        let ns = format!("provnohint{name}");
        assert_eq!(run(&ns, go), answer, "{ns}");
    }
}

/// The receiver's provision is read before a sibling argument pins the parameter, at a
/// carrier that takes parameters too: a wider tuple passed for `T` does not narrow the
/// lambda. Before: "each.f (op-arg): expected ((c: Int64, a: Int64)) -> Int64, got
/// ((c: Int64, a: Int64, extra: Int64)) -> Int64". The sibling at exactly the bound tuple
/// ran before and runs now.
#[test]
fn a_wider_sibling_does_not_narrow_the_lambda_at_a_carrier_with_parameters() {
    let call = |sibling: &str| {
        format!(
            "Int64 =\n    let k: Cq[V = Int64] = cq(v: 1)\n    let p: {sibling}\n    Sq.each(k, lambda (q) -> q.a + 41, p)"
        )
    };
    assert_eq!(
        run(
            "provwide",
            &call("(c: Int64, a: Int64, extra: Int64) = (c: 1, a: 1, extra: 2)")
        ),
        42
    );
    assert_eq!(run("provexact", &call("(c: Int64, a: Int64) = (c: 1, a: 1)")), 42);
}

/// The carrier-parameter shape: `Holder.visit(c: C, f: (q: Element) -> Int64)` at `Bag
/// provides Holder[C = Bag, Element = Rec]`. Before: "<unresolved receiver>.n". The dot
/// spelling ran before and runs now.
#[test]
fn a_lambda_at_a_carrier_parameter_is_hinted_with_what_the_provision_binds() {
    assert_eq!(run("provvisit", "Int64 = Holder.visit(bag(n: 1), lambda q -> q.n)"), 4);
    assert_eq!(run("provvisitdot", "Int64 = bag(n: 1).visit(lambda q -> q.n)"), 4);
}

// ── an argument ─────────────────────────────────────────────────────────────

/// A lambda that writes another type than the provision's is refused where it is passed.
/// Before, its annotation fixed the spec parameter and the receiver was refused for it:
/// "each.s (op-arg): expected Sp[T = Int64], got Cg".
#[test]
fn a_lambda_at_another_type_is_refused_where_it_is_passed() {
    let rendered = refusal(
        "provargannotated",
        "Int64 =\n    let b: Cg = cg(n: 1)\n    Sp.each(b, lambda (q: Int64) -> q)",
    );
    assert!(
        rendered.contains("each.f (op-arg): expected Rec -> Int64, got Int64 -> Int64"),
        "{rendered}"
    );
}

/// A carrier that takes no parameters reads its provision as one that takes them does:
/// an argument typed by the spec's parameter is held to what the provision binds, so a
/// wrong one is refused where it is passed and a wider tuple is taken. Before, the
/// carrier without parameters left `T` to the argument: the wrong one was blamed on the
/// receiver, "one.s (op-arg): expected Sq[T = Int64], got C0", and the wider tuple was
/// refused the same way where `cq(v: 1)` took it.
#[test]
fn a_carrier_without_parameters_reads_its_provision_as_one_with_them_does() {
    for (carrier, recv) in [("with", "cq(v: 1)"), ("without", "c0")] {
        let ns = format!("provargwrong{carrier}");
        let rendered = refusal(&ns, &format!("Int64 = Sq.one({recv}, 5)"));
        assert!(
            rendered.contains("one.z (op-arg): expected (c: Int64, a: Int64), got Int64"),
            "{ns}: {rendered}"
        );
        let ns = format!("provargwide{carrier}");
        assert_eq!(run(&ns, &format!("Int64 = Sq.one({recv}, (c: 1, a: 2, extra: 3))")), 2, "{ns}");
        let ns = format!("provargexact{carrier}");
        assert_eq!(run(&ns, &format!("Int64 = Sq.one({recv}, (c: 1, a: 2))")), 2, "{ns}");
    }
}

// ── a result ────────────────────────────────────────────────────────────────

/// A result typed by the spec's parameter is what the receiver's provision binds it to,
/// and not what the caller expects. Before, `go() -> String = Feed.next(gf)` loaded and
/// answered 5, and the defaulted `Feed.twice(gf)` was refused for a provider of
/// `Feed[T = String]`.
#[test]
fn a_self_receivers_result_is_what_the_provision_binds() {
    for (name, call) in [("next", "Feed.next(gf)"), ("twice", "Feed.twice(gf)")] {
        let ns = format!("provresult{name}");
        assert_eq!(run(&ns, &format!("Int64 = {call}")), 5, "{ns}");
        let ns = format!("provresultbad{name}");
        let rendered = refusal(&ns, &format!("String = {call}"));
        assert!(
            rendered.contains("go.return (op-return): expected String, got Int64"),
            "{ns}: {rendered}"
        );
    }
}

/// The carrier-parameter shape has held its result to the provision since WI-383; it does
/// not move.
#[test]
fn a_carrier_parameters_result_is_what_the_provision_binds() {
    assert_eq!(run("provpeek", "Int64 = Holder.peek(bag(n: 1)).n"), 9);
    let rendered = refusal("provpeekbad", "String = Holder.peek(bag(n: 1))");
    assert!(
        rendered.contains("go.return (op-return): expected String, got Rec"),
        "{rendered}"
    );
}

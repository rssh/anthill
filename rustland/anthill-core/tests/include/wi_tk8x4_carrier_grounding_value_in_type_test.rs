//! WI-20260929-TK8X4 — a spec operation called on a receiver whose type argument HOLDS A
//! VALUE has the type its provision gives it there, as it has at the argument's type twin.
//!
//! `Holder[T = Buf[T = Int64, N = 3]]` provides `Peek[T]`, so `Peek.peek(h)` is a `Buf[T =
//! Int64, N = 3]`. The argument holds a value, so it rides an occurrence and not a
//! hash-consed term, and the reader of a receiver's arguments kept terms only: the spec's
//! `T` stayed open and took whatever the context expected. MEASURED when the ticket was
//! filed, over `operation peek(p: Peek) -> T`: `f(h: Holder[T = Buf[T = Int64, N = 3]]) ->
//! Int64 = Peek.peek(h)` LOADED and `anthill run` died "main returned non-Int64 value", and
//! `Peek.peek(h).v` was refused "<unresolved receiver>.v … no such member" — while at `N =
//! Bool` the first was refused and the second ran.
//!
//! THE TICKET'S PROGRAM IS WRITTEN OTHERWISE NOW. A receiver typed by the spec's bare name
//! beside a result typed `T` is refused at the declaration (proposal 070: a bare sort is any
//! instance); the two spellings that say what it meant are `peek(p: Self) -> T` and
//! `peek(p: Peek) -> p.T`. Both are rows here.
//!
//! TWO READERS ANSWER IT, and a row's back-out says which it rests on:
//!
//! * (A) THE RECEIVER'S ARGUMENTS, read for what the provision binds the spec's parameters
//!   to (`typing::parameterized_vid_bindings`) — the reader the ticket names, each argument
//!   on the carrier it rides since WI-20260829-2NMXA. The one binder of a spec that receives
//!   on a parameter of its own (`Look.look(c: C)`), and of a callback's hint.
//! * (B) THE PROVISION READ AT THE ARGUMENT'S INSTANCE (`typing::provider_view_at_instance`),
//!   by unification and by the subtype relation: a receiver typed `Self` is the spec at its
//!   own parameters, so unifying the argument with it binds them too, and a holder passed
//!   where `Peek[T = …]` is declared is compared through it.
//!
//! EVERY ROW ASSERTS A VERDICT THAT NAMES THE TYPE OR A VALUE THAT WAS COMPUTED: a refusal
//! names `Buf[T = Int64, N = 3]` as what the call is — under a back-out several are refused
//! for another reason ("missing `requires Look[Elem = …]`"), which is not this — and a run
//! answers the 7 the holder was built with. Each helper asserts the `N = Bool` twin FIRST,
//! so a row that fails at `N = 3` has passed its twin.
//!
//! ── WHICH ROWS FAIL WHEN A READER IS BACKED OUT ──────────────────────────────
//!
//! Each back-out is PRESENT AND WRONG — the reader keeps an argument only where it is a
//! term, as it did when the ticket was filed — APPLIED AND RUN over this file's 14 rows.
//! Every failure is at `N = 3`.
//!
//! * (A) alone — 7 FAIL: [`a_spec_that_receives_on_its_own_parameter`] (the wrongly typed
//!   `f` LOADS, and runs to a `Buf`), [`its_default_the_provider_does_not_override`],
//!   [`a_callbacks_parameter_is_the_type_at_the_receiver`] (`q.v`: no member `v`),
//!   [`a_receivers_own_argument_that_is_the_value`] (`Look.look(h)` at `N = 4` loads),
//!   [`under_a_requires_clause_of_a_generic_caller`],
//!   [`wherever_the_call_is_written_on_a_carrier_parameter_spec`] and
//!   [`a_second_holder_inside_the_first`]'s carrier-parameter half. RUN OVER THE WHOLE OF
//!   `anthill-core` AS WELL (8523 rows): these seven and twelve older rows are all that
//!   fail — the ten effect-row rows named below, the unit row
//!   `wi470_parameterized_vid_bindings_reads_both_carriers` and
//!   `n01py…::a_row_that_names_a_cell_is_read_like_a_ground_one`. The eleven of those that
//!   are programs hold an effect row; a type that holds a value in a receiver's argument is
//!   driven through this reader by this file alone.
//! * (B) alone — 1 FAILS: [`a_holder_where_the_spec_at_a_type_is_declared`] (a holder at
//!   `N = 3` passed, and returned, where the spec at `N = 4` is declared LOADS; a correct
//!   annotation is refused).
//! * (A) AND (B) — all but [`the_projection_spelling_of_the_ticket`] FAIL: the eight above,
//!   and the five a `Self` receiver binds either way — [`the_tickets_call`] (loads, runs to
//!   a `Buf`; `.v` refused "<unresolved receiver>.v"), which is the ticket's measurement
//!   again, [`a_default_the_provider_does_not_override`],
//!   [`a_binding_that_wraps_the_receivers_argument`],
//!   [`a_provision_reached_through_another_spec`] and
//!   [`wherever_the_call_is_written_on_a_self_receiving_spec`].
//! * THE SELF-RECEIVER BINDER keeping a binding only where it is a term
//!   (`bind_spec_params_from_provision`, what the reader's answer is bound through) — 1
//!   FAILS: [`a_callbacks_parameter_is_the_type_at_the_receiver`]. A hint is read before
//!   the argument is unified, so nothing else has bound `T` yet.
//!
//! PASSES UNDER EVERY BACK-OUT, by design: [`the_projection_spelling_of_the_ticket`] — `p.T`
//! is read off the argument's own type and asks no provision; it is the other spelling of
//! the ticket's program, and says the acceptance holds for both.
//!
//! ALSO RUN, at the same verdicts: under `ANTHILL_TEST_NODE_CARRIER=1`, where the `N = Bool`
//! twins ride an occurrence too, and under the two other load recipes.
//!
//! NOT HERE, and where it is: an EFFECT ROW in the receiver's argument. A row the receiver
//! writes that names a cell is read by the same two readers and driven in
//! `wi_2nmxa_denoted_provision_binding_test` — MEASURED beside these rows: ten of its 21
//! fail under (A), one under (B), twelve under both. A row the receiver leaves unwritten is
//! the receiver's own projection, `wi612_abstract_stream_consumer_effect_test`, whose two
//! rows pass under each back-out: the reader was never what answered them.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// The argument that holds a value, and its type twin.
const VAL: &str = "Buf[T = Int64, N = 3]";
const TYP: &str = "Buf[T = Int64, N = Bool]";

/// A spec that receives on ITSELF: an operation each provider writes, a default over it, and
/// one that hands the element to a callback.
const PEEK: &str = r#"
  sort Peek
    sort T = ?
    operation peek(p: Self) -> T
    operation again(p: Self) -> T = peek(p)
    operation each(p: Self, f: (x: T) -> Int64) -> Int64 = f(peek(p))
  end
"#;

/// `Holder[T]` provides `Peek[T]`.
const HOLDER: &str = r#"
  sort Holder
    sort T = ?
    entity holder(x: T)
    provides Peek[T]
    operation peek(h: Self) -> T = match h case holder(x) -> x
  end
"#;

/// A spec that receives on a PARAMETER OF ITS OWN, with a default, and `Holder` providing it.
const LOOK: &str = r#"
  sort Look
    sort C = ?
    sort Elem = ?
    operation look(c: C) -> Elem
    operation look2(c: C) -> Elem = look(c)
  end

  sort Holder
    sort T = ?
    entity holder(x: T)
    provides Look[C = Self, Elem = T]
    operation look(h: Self) -> T = match h case holder(x) -> x
  end
"#;

fn program(ns: &str, decls: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool}}

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end

  sort Two
    sort A = ?
    sort B = ?
    entity two(a: A, b: B)
  end
{decls}
{body}
end
"#
    )
}

/// `body` — which declares `go() -> Int64` — is refused, and the refusal names `tokens`.
fn refused(ns: &str, decls: &str, body: &str, tokens: &[&str]) {
    assert_refused_naming(&load_errors_of(&program(ns, decls, body)), tokens, body);
}

/// `body` — which declares `go() -> Int64` — loads, and `go()` runs to 7.
fn answers_7(ns: &str, decls: &str, body: &str) {
    assert_eq!(
        run_int64(&program(ns, decls, body), &format!("{ns}.go")),
        Ok(7),
        "{body}"
    );
}

/// `call` is a `Buf` on a `h: Holder[T = Buf…]`, at the type twin and then at the value:
/// returned where an `Int64` is declared it is refused naming the `Buf`, and its `.v` runs
/// to the 7 the holder was built with.
fn the_call_is_a_buf(ns: &str, decls: &str, call: &str) {
    the_call_is_a_buf_on(ns, decls, "Holder[T = {buf}]", "holder(buf(7))", call);
}

/// [`the_call_is_a_buf`] on a receiver typed `recv` — `{buf}` in it is the argument that
/// holds the value — and built by `arg`.
fn the_call_is_a_buf_on(ns: &str, decls: &str, recv: &str, arg: &str, call: &str) {
    for (twin, buf) in [("typ", TYP), ("val", VAL)] {
        let recv = recv.replace("{buf}", buf);
        refused(
            &format!("{ns}.{twin}.wrong"),
            decls,
            &format!(
                "  operation f(h: {recv}) -> Int64 = {call}\n  \
                 operation go() -> Int64 = f({arg})"
            ),
            &["f.return", &format!("expected Int64, got {buf}")],
        );
        answers_7(
            &format!("{ns}.{twin}.right"),
            decls,
            &format!(
                "  operation f(h: {recv}) -> Int64 = {call}.v\n  \
                 operation go() -> Int64 = f({arg})"
            ),
        );
    }
}

// ── the ticket's program, in the two spellings it has now ──────────────────────────────────

/// THE TICKET'S CALL, the receiver typed `Self`: `Peek.peek(h)` is the `Buf` the holder
/// holds. Refused where an `Int64` is declared, and `Peek.peek(h).v` runs.
#[test]
fn the_tickets_call() {
    the_call_is_a_buf("witk8x4.ticket", &format!("{PEEK}{HOLDER}"), "Peek.peek(h)");
}

/// THE OTHER SPELLING, `peek(p: Peek) -> p.T`. CONTROL — passes under every back-out, by
/// design: the result is the argument's own `T`, read off its type, and no provision is
/// asked.
#[test]
fn the_projection_spelling_of_the_ticket() {
    let decls = r#"
  sort Peek
    sort T = ?
    operation peek(p: Peek) -> p.T
  end

  sort Holder
    sort T = ?
    entity holder(x: T)
    provides Peek[T]
    operation peek(h: Holder) -> h.T = match h case holder(x) -> x
  end
"#;
    the_call_is_a_buf("witk8x4.projection", decls, "Peek.peek(h)");
}

/// A DEFAULT THE PROVIDER DOES NOT OVERRIDE has no signature of the provider's to read the
/// element from: the spec's `T` at this receiver is all there is. By the spec's name and by
/// dot.
#[test]
fn a_default_the_provider_does_not_override() {
    let decls = format!("{PEEK}{HOLDER}");
    the_call_is_a_buf("witk8x4.default", &decls, "Peek.again(h)");
    the_call_is_a_buf("witk8x4.default_dot", &decls, "h.again()");
}

// ── a spec that receives on a parameter of its own ─────────────────────────────────────────

/// `Look.look(c: C) -> Elem` under `Holder provides Look[C = Self, Elem = T]`: the argument
/// binds `C`, and `Elem` is what the provision says it is at that `C` — read off the
/// receiver's arguments by (A) and by nothing else. Backed out, this is the ticket's
/// measurement on today's tree: the wrongly typed `f` loads and runs to a `Buf`.
#[test]
fn a_spec_that_receives_on_its_own_parameter() {
    the_call_is_a_buf("witk8x4.own_param", LOOK, "Look.look(h)");
}

/// Its default, by the spec's name and by dot.
#[test]
fn its_default_the_provider_does_not_override() {
    the_call_is_a_buf("witk8x4.own_param_default", LOOK, "Look.look2(h)");
    the_call_is_a_buf("witk8x4.own_param_default_dot", LOOK, "h.look2()");
}

/// UNDER A `requires` CLAUSE: a caller generic in the carrier and the element, called at the
/// holder. The clause's `R` is what the provision binds `Elem` to at that receiver.
#[test]
fn under_a_requires_clause_of_a_generic_caller() {
    for (default, op) in [("abstract", "look"), ("default", "look2")] {
        let decls = format!(
            "{LOOK}\n  operation g[P, R](c: P) -> R requires Look[C = P, Elem = R] = Look.{op}(c)"
        );
        the_call_is_a_buf(&format!("witk8x4.clause.{default}"), &decls, "g(h)");
    }
}

// ── what the provision binds, other than the receiver's argument as it stands ──────────────

/// A CALLBACK'S PARAMETER is hinted with the spec's `T` at the receiver: `q.v` reads the
/// `Buf`'s field, and a callback that hands the `Buf` back where an `Int64` is declared is
/// refused naming both arrows.
#[test]
fn a_callbacks_parameter_is_the_type_at_the_receiver() {
    let decls = format!("{PEEK}{HOLDER}");
    for (twin, buf) in [("typ", TYP), ("val", VAL)] {
        answers_7(
            &format!("witk8x4.hint.{twin}.right"),
            &decls,
            &format!(
                "  operation f(h: Holder[T = {buf}]) -> Int64 = Peek.each(h, lambda q -> q.v)\n  \
                 operation go() -> Int64 = f(holder(buf(7)))"
            ),
        );
        refused(
            &format!("witk8x4.hint.{twin}.wrong"),
            &decls,
            &format!(
                "  operation f(h: Holder[T = {buf}]) -> Int64 = Peek.each(h, lambda q -> q)\n  \
                 operation go() -> Int64 = f(holder(buf(7)))"
            ),
            &["each.f", &format!("expected {buf} -> Int64, got {buf} -> {buf}")],
        );
    }
}

/// A BINDING THAT WRAPS the receiver's argument, `provides Peek[T = Two[A = T, B = Int64]]`:
/// the argument is spliced into the binding where its parameter stood. Through the default
/// and through the provider's own operation.
#[test]
fn a_binding_that_wraps_the_receivers_argument() {
    let decls = format!(
        r#"{PEEK}
  sort Holder
    sort T = ?
    entity holder(x: T)
    provides Peek[T = Two[A = T, B = Int64]]
    operation peek(h: Self) -> Two[A = T, B = Int64] = match h case holder(x) -> two(x, 1)
  end
"#
    );
    the_call_is_a_buf("witk8x4.wrapped", &decls, "Peek.again(h).a");
    the_call_is_a_buf("witk8x4.wrapped_own", &decls, "Peek.peek(h).a");
}

/// A PROVISION REACHED THROUGH ANOTHER SPEC: `Holder provides Mid[T]`, `Mid provides
/// Peek[T]`, and no `Holder provides Peek`. The receiver's argument goes through both.
#[test]
fn a_provision_reached_through_another_spec() {
    let decls = format!(
        r#"{PEEK}
  sort Mid
    sort T = ?
    provides Peek[T]
    operation mid(m: Self) -> T
    operation peek(m: Self) -> T = mid(m)
  end

  sort Holder
    sort T = ?
    entity holder(x: T)
    provides Mid[T]
    operation mid(h: Self) -> T = match h case holder(x) -> x
  end
"#
    );
    the_call_is_a_buf("witk8x4.through.default", &decls, "Peek.again(h)");
    the_call_is_a_buf("witk8x4.through.own", &decls, "Peek.peek(h)");
}

/// A SECOND HOLDER INSIDE THE FIRST: the outer call's type is a holder of the `Buf`, and the
/// inner call reads that. On the spec that receives on itself and on the one that receives
/// on its own parameter.
#[test]
fn a_second_holder_inside_the_first() {
    for (kind, decls, call) in [
        ("self", format!("{PEEK}{HOLDER}"), "Peek.again(Peek.again(h))"),
        ("own_param", LOOK.to_string(), "Look.look(Look.look(h))"),
    ] {
        the_call_is_a_buf_on(
            &format!("witk8x4.nested.{kind}"),
            &decls,
            "Holder[T = Holder[T = {buf}]]",
            "holder(holder(buf(7)))",
            call,
        );
    }
}

/// THE RECEIVER'S OWN ARGUMENT IS THE VALUE, and the result's type names it: `H2[N = 3]`
/// gives a `Buf[T = Int64, N = 3]`. Returned where `N = 4` is declared it is refused naming
/// both — backed out, it LOADS and answers 7 — and where `N = 3` is declared it runs. The
/// type twin is `N = Bool` against `N = Int64`.
#[test]
fn a_receivers_own_argument_that_is_the_value() {
    let sized = r#"
  sort Sized
    sort N = ?
    operation same(p: Self) -> Buf[T = Int64, N = N]
    operation again(p: Self) -> Buf[T = Int64, N = N] = same(p)
  end

  sort H2
    sort N = ?
    entity h2(x: Int64)
    provides Sized[N]
    operation same(h: Self) -> Buf[T = Int64, N = N] = match h case h2(x) -> buf(x)
  end
"#;
    let look_sized = r#"
  sort Look
    sort C = ?
    sort Elem = ?
    operation look(c: C) -> Elem
  end

  sort H2
    sort N = ?
    entity h2(x: Int64)
    provides Look[C = Self, Elem = Buf[T = Int64, N = N]]
    operation look(h: Self) -> Buf[T = Int64, N = N] = match h case h2(x) -> buf(x)
  end
"#;
    for (kind, decls, call) in [
        ("default", sized, "Sized.again(h)"),
        ("own", sized, "Sized.same(h)"),
        ("own_param", look_sized, "Look.look(h)"),
    ] {
        for (twin, n, other) in [("typ", "Bool", "Int64"), ("val", "3", "4")] {
            let body = |declared: &str| {
                format!(
                    "  operation g(h: H2[N = {n}]) -> Buf[T = Int64, N = {declared}] = {call}\n  \
                     operation go() -> Int64 = g(h2(7)).v"
                )
            };
            refused(
                &format!("witk8x4.own_arg.{kind}.{twin}.wrong"),
                decls,
                &body(other),
                &[
                    "g.return",
                    &format!("expected Buf[T = Int64, N = {other}], got Buf[T = Int64, N = {n}]"),
                ],
            );
            answers_7(&format!("witk8x4.own_arg.{kind}.{twin}.right"), decls, &body(n));
        }
    }
}

// ── the holder where the spec at a type is declared ────────────────────────────────────────

/// A HOLDER WHERE `Peek[T = Buf…]` IS DECLARED — a spec that receives on itself is its own
/// carrier, so the holder is a value of it at what the provision binds `T` to there. The
/// subtype relation reads the provision at the holder's instance, which is (B) and nothing
/// else. As an argument, as a returned value and under a `let` annotation: declared at
/// another value it is refused naming both types — backed out, the first two LOAD — and
/// declared at the holder's own it runs — backed out, the annotation is refused. The type
/// twin is `N = Bool` against `N = Int64`.
#[test]
fn a_holder_where_the_spec_at_a_type_is_declared() {
    let decls = format!("{PEEK}{HOLDER}");
    // `(what, where the refusal is, the body)`; `{at}` is the type the spec is declared at.
    let places = [
        (
            "argument",
            "takes.p",
            "  operation takes(p: Peek[T = {at}]) -> Int64 = Peek.peek(p).v\n  \
             operation f(h: Holder[T = {buf}]) -> Int64 = takes(h)",
        ),
        (
            "returned",
            "up.return",
            "  operation up(h: Holder[T = {buf}]) -> Peek[T = {at}] = h\n  \
             operation f(h: Holder[T = {buf}]) -> Int64 = Peek.peek(up(h)).v",
        ),
        (
            "annotation",
            "p.annotation",
            "  operation f(h: Holder[T = {buf}]) -> Int64 =\n    \
             let p: Peek[T = {at}] = h\n    Peek.peek(p).v",
        ),
    ];
    for (what, site, template) in places {
        for (twin, n, other) in [("typ", "Bool", "Int64"), ("val", "3", "4")] {
            let buf = format!("Buf[T = Int64, N = {n}]");
            let body = |at: &str| {
                format!(
                    "{}\n  operation go() -> Int64 = f(holder(buf(7)))",
                    template.replace("{at}", at).replace("{buf}", &buf)
                )
            };
            let elsewhere = format!("Buf[T = Int64, N = {other}]");
            refused(
                &format!("witk8x4.declared.{what}.{twin}.wrong"),
                &decls,
                &body(&elsewhere),
                &[
                    site,
                    &format!("expected Peek[T = {elsewhere}], got Holder[T = {buf}]"),
                ],
            );
            answers_7(&format!("witk8x4.declared.{what}.{twin}.right"), &decls, &body(&buf));
        }
    }
}

// ── wherever the call is written ────────────────────────────────────────────────────────

/// The places a call's type is read from: `(what, a body that misuses the `Buf`, where its
/// refusal is, the type declared there, a body that uses the `Buf`)`. `{c}` is the call,
/// `{n}` the same call with its receiver passed by name, `{buf}` the argument's type.
const SITES: [(&str, &str, &str, &str, &str); 5] = [
    (
        "argument",
        "  operation inc(n: Int64) -> Int64 = n\n  \
         operation f(h: Holder[T = {buf}]) -> Int64 = inc({c})",
        "inc.n",
        "Int64",
        "  operation inc(n: Int64) -> Int64 = n\n  \
         operation f(h: Holder[T = {buf}]) -> Int64 = inc({c}.v)",
    ),
    (
        "named_receiver",
        "  operation f(h: Holder[T = {buf}]) -> Int64 = {n}",
        "f.return",
        "Int64",
        "  operation f(h: Holder[T = {buf}]) -> Int64 = {n}.v",
    ),
    (
        "annotation",
        "  operation f(h: Holder[T = {buf}]) -> Int64 =\n    let x: Int64 = {c}\n    x",
        "x.annotation",
        "Int64",
        "  operation f(h: Holder[T = {buf}]) -> Int64 =\n    let x: {buf} = {c}\n    x.v",
    ),
    (
        "lambda_body",
        "  operation f(h: Holder[T = {buf}]) -> Int64 =\n    \
         let k = lambda (z: Int64) -> {c}\n    k(1)",
        "f.return",
        "Int64",
        "  operation f(h: Holder[T = {buf}]) -> Int64 =\n    \
         let k = lambda (z: Int64) -> {c}.v\n    k(1)",
    ),
    (
        "condition",
        "  operation f(h: Holder[T = {buf}]) -> Int64 = if {c} then 1 else 2",
        "if.condition",
        "Bool",
        "  operation f(h: Holder[T = {buf}]) -> Int64 = if {c}.v > 0 then {c}.v else 2",
    ),
];

/// Every site of [`SITES`], at the type twin and then at the value.
fn at_every_site(ns: &str, decls: &str, call: &str, named: &str) {
    for (what, wrong, site, declared, right) in SITES {
        for (twin, buf) in [("typ", TYP), ("val", VAL)] {
            let body = |template: &str| {
                format!(
                    "{}\n  operation go() -> Int64 = f(holder(buf(7)))",
                    template.replace("{c}", call).replace("{n}", named).replace("{buf}", buf)
                )
            };
            refused(
                &format!("{ns}.{what}.{twin}.wrong"),
                decls,
                &body(wrong),
                &[site, &format!("expected {declared}, got {buf}")],
            );
            answers_7(&format!("{ns}.{what}.{twin}.right"), decls, &body(right));
        }
    }
}

/// As another call's argument, with the receiver passed by name, under a `let` annotation,
/// in a lambda's body and as an `if`'s condition — a default of a spec that receives on
/// itself.
#[test]
fn wherever_the_call_is_written_on_a_self_receiving_spec() {
    at_every_site(
        "witk8x4.sites.self",
        &format!("{PEEK}{HOLDER}"),
        "Peek.again(h)",
        "Peek.again(p: h)",
    );
}

/// The same five sites, on a spec that receives on its own parameter.
#[test]
fn wherever_the_call_is_written_on_a_carrier_parameter_spec() {
    at_every_site("witk8x4.sites.own_param", LOOK, "Look.look(h)", "Look.look(c: h)");
}

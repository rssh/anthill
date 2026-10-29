//! WI-20261017-HQH9K — ONE OPENING OF A FIELD PATH PER BODY, AND OF A NON-PATH ARGUMENT PER CALL.
//!
//! WI-20261003-P1PVT names a field path's TOP-LEVEL open slots by the path (`h.s` over `s:
//! Strm[T = Int64, E = ?]` is `Strm[T = Int64, E = h.s.E]`), and three spellings of one value
//! still opened apart, each refusing a correct program. A holder at a stable path is now opened
//! ONCE — `PathOpenings` (`typing/elaborate.rs`): the body's, in its `TypingEnv`; a call's,
//! carried by its `Apply` / `ApplyHints` frames — and every reading takes that opening:
//!
//! * a slot NESTED in a written binding (`s: Strm[T = List[T = ?]]`) is one rigid per path, for
//!   the read `h.s`, a written `h.s.T` and a pattern binder alike (§1);
//! * a PATTERN BINDER over a stable scrutinee is read at the path (`case hold(s)` over `h` is the
//!   field `h.s`) and aliases it, as a `let` of it does — and a named variable two fields share
//!   is the holder's one unknown, for the binders and the reads (§2);
//! * at a call whose argument is NO PATH, the hint, the parameter, the return and the effects
//!   read one unknown of the call's own (§3).
//!
//! What stays apart, by design: two paths (`h.s`, `k.s`), two calls' results, two calls, and a
//! field the holder's constructors type differently (no path type: its binder keeps its name).
//!
//! Found beside it and closed with it (§4): an argument at a parameter a field-path projection
//! types was not checked at all — `swap(t.a, u.a)` loaded and ran `inc` on a `String`.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! MEASURED on 2026-10-29, on the tree this file is committed with, each part disabled alone by
//! a temporary switch, on a binary of this file and the three suites beside it
//! (`wi_p1pvt_field_path_existential_test`, `wi_80zv8_written_wildcard_test`,
//! `wi_0rp29_call_binding_test`; 114 rows, 119 with §4 and the review's rows; parts 8 and 9 are
//! the review's):
//!
//! 1. THE READ KEPT (`apply.rs`, the field read's `Recorded` passed as `None`). 4 FAIL:
//!    [`a_nested_slot_is_one_unknown_for_two_parameters`],
//!    [`a_nested_slot_is_one_unknown_for_every_reading_of_the_path`],
//!    [`a_nested_slot_is_one_unknown_for_a_binder_over_the_path`] and
//!    [`a_variable_two_fields_share_is_one_unknown_for_the_holder`].
//! 2. A WRITTEN RECEIVER KEPT, in the body's record or at a call in the caller's
//!    (`field_type_at_path`'s record dropped there). 3 FAIL: the first two of 1 and
//!    [`a_variable_two_fields_share_is_one_unknown_for_the_holder`].
//! 3. THE CALL'S RECORD (`field_type_at_path`'s record dropped for a callee's path off an
//!    argument that is no path). 2 FAIL: [`a_calls_readings_of_an_argument_that_is_no_path_are_one`]
//!    and P1PVT's `a_lambda_at_a_call_whose_argument_is_no_path_is_hinted_at_the_calls_unknown`.
//! 4. A HOLDER'S NAMED VARIABLES SHARED BY ITS FIELDS (`RecordSlot::seed` skipped). 1 FAILS:
//!    [`a_variable_two_fields_share_is_one_unknown_for_the_holder`].
//! 5. A PATTERN FIELD READ AT THE PATH (`bind_and_label_pattern`'s path branch skipped). 8 FAIL:
//!    [`a_binder_over_a_path_is_the_paths_field`], [`a_binder_and_the_read_of_its_path_agree`],
//!    [`a_nested_slot_is_one_unknown_for_a_binder_over_the_path`],
//!    [`a_variable_two_fields_share_is_one_unknown_for_the_holder`], and on their TEXT alone (the
//!    binder's name where the path is printed): [`a_binder_over_no_path_or_another_path_is_not_the_path`],
//!    80ZV8's `a_binder_over_a_field_left_open_is_an_instance_of_its_own` and
//!    `a_variable_two_fields_share_is_one_for_both_binders`, 0RP29's
//!    `a_mixed_calls_receiver_row_is_the_bound_arguments`.
//! 6. A BINDER OVER A PATH ALIASES IT (the `Pattern::Var` arm's `bind_receiver_alias` skipped —
//!    a `let`'s alias too, which is recorded there now). 3 FAIL:
//!    [`a_binder_over_a_path_is_the_paths_field`],
//!    [`a_nested_slot_is_one_unknown_for_every_reading_of_the_path`] (its `let` alias) and P1PVT's
//!    `a_let_alias_reads_the_path_it_names`.
//! 7. ONLY A FIELD THE CONSTRUCTORS TYPE ALIKE IS READ AT THE PATH (the pattern's own field type
//!    taken where `resolve_field_type` refuses). 2 FAIL:
//!    [`a_field_the_constructors_type_apart_is_read_by_its_binder`] and 80ZV8's
//!    `a_binder_over_a_field_left_open_is_an_instance_of_its_own` (its `case same(m)` arm).
//!
//! 8. A PATTERN READS AT THE PATH ONLY WHEN EVERY FIELD IT TAKES OUT HAS A TYPE THERE (a field
//!    with one read at the path beside one without). 1 FAILS:
//!    [`a_variable_a_constructor_typed_field_shares_is_one_for_the_pattern`].
//! 9. A BARE NULLARY OPERATION ARGUMENT IS NO PATH (`field_type_at_path` keeping a re-key to one).
//!    1 FAILS: [`a_bare_nullary_operation_argument_is_a_call`].
//! 10. §4, A FIELD-PATH NEUTRAL'S RECEIVER IS NO CALLABLE (`node_contains_callable` descending
//!    into an `ExprCarried`'s receiver again). 1 FAILS:
//!    [`a_parameter_a_field_path_projection_types_checks_its_argument`]; none of §1–§3 reads it.
//!
//! NOT DRIVEN: the record speaks for a holder at the type it was opened at. A call that wraps an
//! argument in `some(…)` reads one at another ([`an_argument_the_call_wraps_reads_its_holder_afresh`]),
//! and is refused with the check backed out too; no other program of the suites reaches it.
//!
//! CONTROLS, passing under every part by design: [`a_nested_slot_stays_apart_where_the_value_does`],
//! [`a_holders_shared_variable_is_its_own`], [`two_calls_read_two_unknowns`],
//! [`an_argument_the_call_wraps_reads_its_holder_afresh`] and
//! [`a_field_path_projection_agrees_with_itself`] — the same verdict before the ticket and after,
//! with every part present or backed out.

use crate::common::{assert_refused_naming, load_errors_of as load_errors, run_int64 as run_src};

// ── §1 a nested slot is one rigid per path ───────────────────────────────────────────────────

const NESTED: &str = r#"
  import anthill.prelude.{Int64, List}
  sort Strm
    sort T = ?
    entity strm(t: T)
  end
  sort Hold3
    entity hold3(s: Strm[T = List[T = ?]])
  end
  operation same_list[A](x: A, y: A) -> Int64 = 42
  operation takes_ints(l: List[T = Int64]) -> Int64 = 0
  operation mk3() -> Hold3 = hold3(s: strm(t: [1]))
"#;

fn nested(ns: &str, body: &str) -> String {
    format!("namespace wi_hqh9k.{ns}\n{NESTED}\n{body}\nend\n")
}

/// THE TICKET'S FIRST PROGRAM RUNS TO 42: `x: h.s.T` and `y: h.s.T` over `s: Strm[T = List[T =
/// ?]]` are one `List` of one unknown, so `same_list(x, y)` finds one `A`; and the caller's
/// `f(h, h.s.t, h.s.t)` passes reads of its `h.s` for the parameters' `h.s.T`. Refused before in
/// the body, "no common type for type parameter `A` …: List[T = ?T] (x), List[T = ?T] (y)", and
/// at the call, "expected List[T = ?T], got List[T = ?T]" (MEASURED).
#[test]
fn a_nested_slot_is_one_unknown_for_two_parameters() {
    let src = nested(
        "params",
        "  operation f(h: Hold3, x: h.s.T, y: h.s.T) -> Int64 = same_list(x, y)\n  operation go() -> Int64 =\n    let h = mk3()\n    f(h, h.s.t, h.s.t)",
    );
    assert_eq!(run_src(&src, "wi_hqh9k.params.go"), Ok(42));
}

/// … AND FOR EVERY READING IN ONE BODY: the read twice, a written `h.s.T` beside the read, and a
/// `let` alias's read beside the path's.
#[test]
fn a_nested_slot_is_one_unknown_for_every_reading_of_the_path() {
    let src = nested(
        "readings",
        "  operation g(h: Hold3) -> Int64 = same_list(h.s.t, h.s.t)\n  operation k(h: Hold3, x: h.s.T) -> Int64 = same_list(x, h.s.t)\n  operation a(h: Hold3) -> Int64 =\n    let t = h\n    same_list(t.s.t, h.s.t)\n  operation go() -> Int64 =\n    let h = mk3()\n    g(h) + k(h, h.s.t) + a(h) - 84",
    );
    assert_eq!(run_src(&src, "wi_hqh9k.readings.go"), Ok(42));
}

/// … AND FOR A PATTERN BINDER over the path, one level down (`case hold3(s)`) or two (`case
/// hold3(strm(t))`).
#[test]
fn a_nested_slot_is_one_unknown_for_a_binder_over_the_path() {
    let src = nested(
        "binder",
        "  operation p(h: Hold3) -> Int64 = match h\n    case hold3(s) -> same_list(s.t, h.s.t)\n  operation q(h: Hold3) -> Int64 = match h\n    case hold3(strm(t)) -> same_list(t, h.s.t)\n  operation go() -> Int64 = p(mk3()) + q(mk3()) - 42",
    );
    assert_eq!(run_src(&src, "wi_hqh9k.binder.go"), Ok(42));
}

/// CONTROLS — refused before and after: two holders' nested slots are two unknowns; so are two
/// calls' results'; and a nested slot is no `Int64`.
#[test]
fn a_nested_slot_stays_apart_where_the_value_does() {
    assert_refused_naming(
        &load_errors(&nested(
            "two_holders",
            "  operation f(h: Hold3, k: Hold3) -> Int64 = same_list(h.s.t, k.s.t)",
        )),
        &["no common type for type parameter `A` of `same_list`: List[T = ?T] (x), List[T = ?T] (y)"],
        "two holders' nested slots taken for one",
    );
    assert_refused_naming(
        &load_errors(&nested(
            "two_calls",
            "  operation f() -> Int64 = same_list(mk3().s.t, mk3().s.t)",
        )),
        &["no common type for type parameter `A` of `same_list`: List[T = ?T] (x), List[T = ?T] (y)"],
        "two calls' results' nested slots taken for one",
    );
    assert_refused_naming(
        &load_errors(&nested(
            "not_int",
            "  operation f(h: Hold3) -> Int64 = takes_ints(h.s.t)",
        )),
        &["takes_ints.l (op-arg): expected List[T = Int64], got List[T = ?T]"],
        "a holder's nested slot taken for an Int64",
    );
}

// ── §2 a pattern binder over a path is the path's field ──────────────────────────────────────

const HOLD: &str = r#"
  import anthill.prelude.{Int64, Bool, String, Error}
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(t: T)
    operation each[EffP](s: Strm, f: (x: Int64) -> Bool @ {EffP, -s.E}) -> Bool effects {EffP} = f(1)
  end
  sort Hold
    entity hold(s: Strm[T = Int64, E = ?])
  end
  operation pure1(x: Int64) -> Bool = true
  operation same(a: Strm, b: Strm[E = a.E]) -> Int64 = 1
  operation mk() -> Hold = hold(s: strm(t: 1))
"#;

fn hold(ns: &str, body: &str) -> String {
    format!("namespace wi_hqh9k.{ns}\n{HOLD}\n{body}\nend\n")
}

/// THE TICKET'S SECOND PROGRAM RUNS TO 42: the binder `s` of `case hold(s)` over `h` is `h.s`,
/// so `Strm.each(s, g)` reads the callee's `-s.E` as `-h.s.E`, which `g` declares. Refused
/// before, `-s.E` against `-h.s.E`, where `Strm.each(h.s, g)` loaded (MEASURED). Driven through
/// a `match`, a destructuring `let`, and a `match` on a `let` alias of `h`.
#[test]
fn a_binder_over_a_path_is_the_paths_field() {
    for (ns, body) in [
        ("match", "match h\n      case hold(s) -> Strm.each(s, g)"),
        ("let", "let hold(s) = h\n    Strm.each(s, g)"),
        ("alias", "let t = h\n    match t\n      case hold(s) -> Strm.each(s, g)"),
    ] {
        let src = hold(
            ns,
            &format!(
                "  operation use(h: Hold, g: (x: Int64) -> Bool @ {{Error[String], -h.s.E}}) -> Bool\n    effects {{Error[String]}} =\n    {body}\n  operation go() -> Int64 effects {{Error[String]}} =\n    if use(hold(s: strm(t: 1)), pure1) then 42 else 0"
            ),
        );
        assert_eq!(run_src(&src, &format!("wi_hqh9k.{ns}.go")), Ok(42), "{ns}");
    }
}

/// … AND THE BINDER AND THE READ ARE ONE TYPE, either way round: `same(s, h.s)` and `same(h.s,
/// s)` over `same(a: Strm, b: Strm[E = a.E])`. Both refused before, `s.E` against `h.s.E`.
#[test]
fn a_binder_and_the_read_of_its_path_agree() {
    let src = hold(
        "agree",
        "  operation f(h: Hold) -> Int64 = match h\n    case hold(s) -> same(s, h.s) + same(h.s, s) + 40\n  operation go() -> Int64 = f(mk())",
    );
    assert_eq!(run_src(&src, "wi_hqh9k.agree.go"), Ok(42));
}

/// CONTROLS — a binder over what no path names is its own: over `mk()` the binder's `s.E` is
/// no `h.s.E`; and a binder over another holder is that holder's field, `k.s`.
#[test]
fn a_binder_over_no_path_or_another_path_is_not_the_path() {
    assert_refused_naming(
        &load_errors(&hold(
            "call_scrutinee",
            "  operation use(h: Hold, g: (x: Int64) -> Bool @ {Error[String], -h.s.E}) -> Bool\n    effects {Error[String]} = match mk()\n      case hold(s) -> Strm.each(s, g)",
        )),
        &["each.f (op-arg)", "to lack the row `s.E`"],
        "a binder over a call's result read as a parameter's field",
    );
    assert_refused_naming(
        &load_errors(&hold(
            "other_holder",
            "  operation f(h: Hold, k: Hold) -> Int64 = match k\n    case hold(s) -> same(s, h.s)",
        )),
        &["same.b (op-arg): expected Strm[E = k.s.E], got Strm[T = Int64, E = h.s.E]"],
        "a binder over one holder taken for another's field",
    );
}

const TWO: &str = r#"
  import anthill.prelude.{Int64, String}
  sort Box
    sort T = ?
    entity leaf(v: T)
    entity node(next: Box[T = ?])
    entity same(next: Self)
  end
  sort Two
    entity two(a: Box[T = ?x], b: Box[T = ?x])
  end
  operation same_t[A](x: A, y: A) -> Int64 = 14
  operation takes_int(b: Box[T = Int64]) -> Int64 = 41
  operation takes_any[A](b: Box[T = A]) -> Int64 = 41
"#;

fn two(ns: &str, body: &str) -> String {
    format!("namespace wi_hqh9k.{ns}\n{TWO}\n{body}\nend\n")
}

/// A VARIABLE TWO FIELDS SHARE IS THE HOLDER'S ONE UNKNOWN: over `two(a: Box[T = ?x], b: Box[T =
/// ?x])`, the reads `t.a.v` and `t.b.v`, written `t.a.T` and `t.b.T`, and a binder beside the
/// other field's read are one type. Each field's read named it by its own path before — `t.a.T`
/// against `t.b.T`, refused (MEASURED) — while the pattern alone kept the tie.
#[test]
fn a_variable_two_fields_share_is_one_unknown_for_the_holder() {
    let src = two(
        "tie",
        "  operation r(t: Two) -> Int64 = same_t(t.a.v, t.b.v)\n  operation w(t: Two, x: t.a.T, y: t.b.T) -> Int64 = same_t(x, y)\n  operation p(t: Two) -> Int64 = match t\n    case two(p, q) -> same_t(p.v, t.b.v)\n  operation go() -> Int64 =\n    let t = two(a: leaf(v: \"s\"), b: leaf(v: \"u\"))\n    r(t) + w(t, t.a.v, t.b.v) + p(t)",
    );
    assert_eq!(run_src(&src, "wi_hqh9k.tie.go"), Ok(42));
}

/// CONTROLS — two holders' variables are two unknowns, and the holder's one is no `Int64`.
#[test]
fn a_holders_shared_variable_is_its_own() {
    assert_refused_naming(
        &load_errors(&two(
            "tie_two",
            "  operation r(t: Two, u: Two) -> Int64 = same_t(t.a.v, u.b.v)",
        )),
        &["no common type for type parameter `A` of `same_t`: t.a.T (x), u.b.T (y)"],
        "two holders' shared variables taken for one",
    );
    assert_refused_naming(
        &load_errors(&two("tie_int", "  operation r(t: Two) -> Int64 = takes_int(t.b)")),
        &["takes_int.b (op-arg): expected Box[T = Int64], got Box[T = t.b.T]"],
        "a holder's shared variable taken for an Int64",
    );
}

/// A FIELD THE CONSTRUCTORS TYPE APART HAS NO PATH TYPE, so its binder is not read at the path:
/// `next` is `Box[T = ?]` in `node` and `Self` in `same`, the read `b.next` is refused for it,
/// and each arm's binder keeps its own type — `m` is a `Box[T = Int64]`. Read at the path, `case
/// same(m)` took the opening `case node(n)` had made and was refused "expected Box[T = Int64],
/// got Box[T = b.next.T]" (MEASURED, a first cut of this ticket).
#[test]
fn a_field_the_constructors_type_apart_is_read_by_its_binder() {
    let src = two(
        "ctor_typed",
        "  operation peel(b: Box[T = Int64]) -> Int64 =\n    match b\n      case leaf(_) -> 0\n      case node(n) -> takes_any(n)\n      case same(m) -> takes_int(m)\n  operation go() -> Int64 = peel(same(next: leaf(v: 1))) + 1",
    );
    assert_eq!(run_src(&src, "wi_hqh9k.ctor_typed.go"), Ok(42));
}

/// … AND A VARIABLE A CONSTRUCTOR-TYPED FIELD SHARES STAYS ONE FOR THE PATTERN: beside `owt(a:
/// Box[T = ?x], b: Box[T = Int64])`, `b` has no type at the path, so `case two(p, q)` reads
/// neither field at it and `?x` is the pattern's one unknown for `p` and `q`. Read at the path
/// for `a` alone, the tie split, "expected Box[T = t.a.T], got Box[T = ?x]" (MEASURED, a cut of
/// this ticket).
#[test]
fn a_variable_a_constructor_typed_field_shares_is_one_for_the_pattern() {
    let src = r#"
namespace wi_hqh9k.mixed
  import anthill.prelude.{Int64}
  sort Box
    sort T = ?
    entity leaf(v: T)
  end
  sort Two
    entity two(a: Box[T = ?x], b: Box[T = ?x])
    entity owt(a: Box[T = ?x], b: Box[T = Int64])
  end
  operation agree[A](p: Box[T = A], q: Box[T = A]) -> Int64 = 41
  operation f(t: Two) -> Int64 = match t
    case two(p, q) -> agree(p, q) + 1
    case owt(p, q) -> 0
  operation go() -> Int64 = f(two(a: leaf(v: "s"), b: leaf(v: "u")))
end
"#;
    assert_eq!(run_src(src, "wi_hqh9k.mixed.go"), Ok(42));
}

// ── §3 a call's readings of an argument that is no path are one ──────────────────────────────

const CALL: &str = r#"
  import anthill.prelude.{Int64, String}
  sort Strm
    sort T = ?
    entity strm(t: T, fn: (x: T) -> Int64)
  end
  sort Hold2
    entity hold2(s: Strm[T = ?])
  end
  operation inc(x: Int64) -> Int64 = x + 1
  operation slen(x: String) -> Int64 = 3
  operation mk_int() -> Hold2 = hold2(s: strm(t: 1, fn: inc))
  operation mk_str() -> Hold2 = hold2(s: strm(t: "abc", fn: slen))
  operation first(h: Hold2) -> h.s.T = h.s.t
  operation app(h: Hold2, v: h.s.T) -> Int64 =
    let g = h.s.fn
    g(v)
  operation pick(h: Hold2, f: (x: h.s.T) -> h.s.T) -> h.s.T = f(h.s.t)
  operation pick2(h: Hold2, f: (x: h.s.T) -> Int64) -> Int64 = f(h.s.t)
"#;

fn call(ns: &str, body: &str) -> String {
    format!("namespace wi_hqh9k.{ns}\n{CALL}\n{body}\nend\n")
}

/// AT A CALL WHOSE ARGUMENT IS NO PATH, THE HINT AND THE CHECK READ ONE UNKNOWN: `lambda (x) ->
/// 42` for `f: (x: h.s.T) -> Int64` is hinted and checked at the call's one `h.s.T`, positional,
/// named or reordered; and the return `h.s.T` of `pick` is the one its lambda was checked at.
/// Each refused before, "expected ?T -> Int64, got ?T -> Int64" (MEASURED).
#[test]
fn a_calls_readings_of_an_argument_that_is_no_path_are_one() {
    for (ns, call_text) in [
        ("positional", "pick2(mk_str(), lambda (x) -> 42)"),
        ("named", "pick2(h: mk_str(), f: lambda (x) -> 42)"),
        ("reordered", "pick2(f: lambda (x) -> 42, h: mk_str())"),
        ("inner", "pick2(mk_str(), lambda (x) -> pick2(mk_int(), lambda (y) -> 42))"),
        ("returned", "let r = pick(mk_str(), lambda (x) -> x)\n    42"),
    ] {
        let src = call(ns, &format!("  operation go() -> Int64 =\n    {call_text}"));
        assert_eq!(run_src(&src, &format!("wi_hqh9k.{ns}.go")), Ok(42), "{ns}");
    }
}

/// CONTROLS — two calls are two unknowns: `app(mk_int(), first(mk_str()))` would run `inc` on
/// `"abc"`, and is refused; a lambda nested in another call's lambda is not its unknown either;
/// and the unknown is no `Int64` inside the lambda.
#[test]
fn two_calls_read_two_unknowns() {
    for (ns, call_text) in [
        ("two_calls", "app(mk_int(), first(mk_str()))"),
        ("cross", "pick2(mk_str(), lambda (x) -> app(mk_int(), x))"),
    ] {
        assert_refused_naming(
            &load_errors(&call(ns, &format!("  operation go() -> Int64 = {call_text}"))),
            &["app.v (op-arg): expected ?T, got ?T"],
            ns,
        );
    }
    assert_refused_naming(
        &load_errors(&call(
            "as_int",
            "  operation go() -> Int64 = pick2(mk_str(), lambda (x) -> x + 1)",
        )),
        &["add.b (op-arg): expected ?T, got Int64"],
        "a call's unknown taken for an Int64",
    );
}

/// A BARE NULLARY OPERATION ARGUMENT IS A CALL: `get(mk3)` re-keys `get`'s `h` to the symbol
/// `mk3`, which names no value, so `same_list(get(mk3), get(mk3))` reads two unknowns, as the
/// `mk3()` spelling does. Kept as the caller's path `mk3.s`, the two calls shared one opening and
/// the first spelling loaded (MEASURED, a cut of this ticket).
#[test]
fn a_bare_nullary_operation_argument_is_a_call() {
    for (ns, arg) in [("bare", "mk3"), ("called", "mk3()")] {
        let src = nested(
            &format!("nullary_{ns}"),
            &format!(
                "  operation get(h: Hold3) -> h.s.T = h.s.t\n  operation f() -> Int64 = same_list(get({arg}), get({arg}))"
            ),
        );
        assert_refused_naming(
            &load_errors(&src),
            &["no common type for type parameter `A` of `same_list`: List[T = ?T] (x), List[T = ?T] (y)"],
            ns,
        );
    }
}

/// AN ARGUMENT THE CALL WRAPS IN `some(…)` re-keys the option parameter to the argument's own
/// path — `o.value.s` read as `k.value.s` — so the caller's holder `k`, opened at `Hold3`, is read
/// at `Option[T = Hold3]`, and that reading opens afresh. Refused, as before the ticket: the
/// parameter's `o.value.s.T` is no unknown of the caller's. A debug assertion there panicked the
/// load (MEASURED, a cut of this ticket).
#[test]
fn an_argument_the_call_wraps_reads_its_holder_afresh() {
    let src = r#"
namespace wi_hqh9k.wrapped
  import anthill.prelude.{Int64, List, Option}
  sort Strm
    sort T = ?
    entity strm(t: T)
  end
  sort Hold3
    entity hold3(s: Strm[T = List[T = ?]])
  end
  operation f(o: Option[T = Hold3], x: o.value.s.T) -> Int64 = 42
  operation g(k: Hold3) -> Int64 =
    let v = k.s.t
    f(k, v)
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["f.x (op-arg): expected List[T = ?T], got List[T = ?T]"],
        "a parameter's slot through an option taken for the caller's",
    );
}

// ── §4 found beside it: a parameter typed through a field-path projection checks its argument ──

const SWAP: &str = r#"
  import anthill.prelude.{Int64, String}
  sort Box
    sort T = ?
    entity box(v: T, fn: (x: T) -> Int64)
  end
  sort One
    entity one(a: Box[T = ?])
  end
  operation inc(x: Int64) -> Int64 = x + 1
  operation slen(x: String) -> Int64 = 3
  operation agree[A](p: Box[T = A], q: Box[T = A]) -> Int64 = 41
  operation swap[A](p: Box[T = A], q: Box[T = A]) -> Box[T = A] = box(v: q.v, fn: p.fn)
  operation run(b: Box) -> Int64 =
    let g = b.fn
    g(b.v)
"#;

fn swap(ns: &str, body: &str) -> String {
    format!("namespace wi_hqh9k.{ns}\n{SWAP}\n{body}\nend\n")
}

/// AN ARGUMENT AT A PARAMETER A FIELD-PATH PROJECTION TYPES IS CHECKED: `agree[A](p: Box[T = A],
/// q: Box[T = A])` binds `A` to `t.a.T` off `p` and refuses `u.a`'s `Box[T = u.a.T]` at `q`, as
/// its single-reference twin `agree(p, q)` refuses `q.T` for `p.T`. The receiver of `t.a.T`
/// rides the occurrence carrier as a `DotApply` chain, which `node_contains_callable` read as a
/// callable, so the argument check withheld the pair: `swap(t.a, u.a)` loaded, and `run` applied
/// `inc` to `"abc"` — "type mismatch: expected Int64, got String and Int64" at run time
/// (MEASURED, `anthill run` on the tree before). Found while writing §2's tie rows.
#[test]
fn a_parameter_a_field_path_projection_types_checks_its_argument() {
    for (ns, op) in [
        ("swap", "  operation f(t: One, u: One) -> Int64 = run(swap(t.a, u.a))"),
        ("agree", "  operation f(t: One, u: One) -> Int64 = agree(t.a, u.a)"),
        (
            "written",
            "  operation f(t: One, u: One, x: Box[T = t.a.T], y: Box[T = u.a.T]) -> Int64 = agree(x, y)",
        ),
    ] {
        assert_refused_naming(
            &load_errors(&swap(ns, op)),
            &["(op-arg): expected Box[T = t.a.T], got Box[T = u.a.T]"],
            ns,
        );
    }
}

/// CONTROLS — one path's two reads agree, and run; the single-reference twin is refused before
/// and after.
#[test]
fn a_field_path_projection_agrees_with_itself() {
    let src = swap(
        "same_path",
        "  operation f(t: One) -> Int64 = agree(t.a, t.a) + run(swap(t.a, t.a)) - 1\n  operation go() -> Int64 = f(one(a: box(v: 1, fn: inc)))",
    );
    assert_eq!(run_src(&src, "wi_hqh9k.same_path.go"), Ok(42));
    assert_refused_naming(
        &load_errors(&swap(
            "one_segment",
            "  operation f(p: Box, q: Box) -> Int64 = agree(p, q)",
        )),
        &["agree.q (op-arg): expected Box[T = p.T], got Box[T = q.T]"],
        "two parameters' elements taken for one",
    );
}

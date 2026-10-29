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
//! And after it (§6, §7): a spec call that dispatches to an override reads the override at the
//! call as the call reads itself — an argument it wraps in `some(…)` at its payload, a field-path
//! argument at its path, a slot nested in one in the call's record; an override restating its
//! spec's field-path effect refines it; a path's field segment is the field's label, also beside
//! a binder of its name; and the declaration rule reads the spec's and the member's field path
//! over one argument once, so a member written as its spec fits it over a nested slot (§8).
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! MEASURED on 2026-10-29, on the tree this file is committed with, each part disabled alone by
//! a temporary switch, on a binary of this file and the three suites beside it
//! (`wi_p1pvt_field_path_existential_test`, `wi_80zv8_written_wildcard_test`,
//! `wi_0rp29_call_binding_test`; 114 rows, 122 with §4, §5 and the reviews' rows; parts 8, 9,
//! 11 and 12 are the reviews'):
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
//! 11. §5, A WRAPPED ARGUMENT IS REACHED THROUGH THE PAYLOAD (`wrapped_arg_params` answering
//!    none). 3 FAIL: [`an_argument_the_call_wraps_is_its_parameters_payload`],
//!    [`a_wrapped_arguments_nested_slot_is_the_callers`] — both by the record's debug assertion,
//!    the holder `k` read at the option's type — and, on its text, the control
//!    [`a_wrapped_parameters_payload_is_its_arguments_only`] (`k.value.s.T` printed for `k.s.T`).
//! 12. §5, THE PAYLOAD READING IS KEPT IN NO RECORD (`field_type_at_path`'s `reads_the_argument`
//!    false). 1 FAILS, by the record's debug assertion — the holder `ww` read at the option's
//!    type: [`an_argument_the_call_wraps_is_its_parameters_payload`] (its `field_path` call).
//!
//! Parts 13–19 MEASURED the same way on a binary of this file and the twelve suites beside it
//! that read an override at a call or a field path (`wi347_override_refinement_test`, `wi604_…`,
//! `wi606_…`, the four `wi_0rp29_…`, `wi_80zv8_written_wildcard_test`, `wi_gjw9z_…`,
//! `wi_jpsdh_…`, `wi_p1pvt_…`, `wi698_row_param_refinement_test`; 620 rows):
//!
//! 13. §6, A DISPATCHED OVERRIDE READS A WRAPPED ARGUMENT AT ITS PAYLOAD (`CallToOverride::wrapped`
//!    answering none). 2 FAIL: [`a_dispatched_override_reads_the_call_as_the_call_does`] and, on
//!    its text, the control [`a_dispatched_overrides_reading_is_its_arguments_only`].
//! 14. §6, … A FIELD-PATH ARGUMENT AT ITS PATH (`CallToOverride::arg_paths` answering none). 1
//!    FAILS: [`a_dispatched_override_reads_the_call_as_the_call_does`].
//! 15. §6, … IN THE CALL'S RECORD (`override_declared_at_call` reading with no record). 1 FAILS:
//!    [`a_dispatched_overrides_nested_slot_is_the_calls`].
//!    Parts 13 and 14 backed out in one reader alone — the WI-606 fallback's
//!    (`concrete_override_threaded`) or the effects' (`dispatched_impl_effects_of`) — fail the
//!    same two rows each.
//! 16. §6, A FIELD PATH'S RECEIVER IS RENAMED (`substitute_ref_syms_occ` passing an
//!    `ExprCarried`'s receiver expression through). 4 FAIL:
//!    [`an_override_restating_a_field_path_effect_refines_it`], and by the same refusal of
//!    `touch` in their shared fixture, [`a_dispatched_override_reads_the_call_as_the_call_does`],
//!    [`a_dispatched_overrides_nested_slot_is_the_calls`] and
//!    [`a_field_segment_is_its_label_beside_a_binder_of_its_name`].
//! 17. §7, A FIELD SEGMENT IS ITS LABEL (`field_label` answering the name as resolved). 1 FAILS:
//!    [`a_field_segment_is_its_label_beside_a_binder_of_its_name`].
//! 18. §8, THE MEMBER RULE'S ONE RECORD (`Receivers::Compared` keeping nothing). 2 FAIL:
//!    [`a_member_written_as_its_spec_fits_it_over_a_nested_slot`] and, on its text, the control
//!    [`a_member_taking_less_over_a_nested_slot_is_refused`] (the other return refused at the
//!    parameter beside it).
//! 19. §8, … READ AT EITHER DECLARATION'S TYPE (`ComparedOpenings` checking the
//!    holder's type). 1 FAILS, by the record's debug assertion — `h` opened at `cat`, read at
//!    `Animal`: [`a_member_written_as_its_spec_fits_it_over_a_nested_slot`].
//!
//! THE HOLDER-TYPE CHECK is an assertion, not a part: the record speaks for a holder at the type
//! it was opened at, and a build with debug assertions stops where a re-key gives a path another
//! value. With part 11 backed out it fires (above); with every part present no program of the
//! suites reaches it (the full workspace).
//!
//! CONTROLS, passing under every part by design: [`a_nested_slot_stays_apart_where_the_value_does`],
//! [`a_holders_shared_variable_is_its_own`], [`two_calls_read_two_unknowns`] and
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

/// A NESTED SLOT THROUGH A WRAPPED ARGUMENT IS THE CALLER'S: `f(k, k.s.t)` over `f(o: Option[T =
/// Hold3], x: o.value.s.T)` hands `o` the value `some(k)`, so `o.value.s.T` is the caller's
/// `k.s.T`, the one unknown its read `k.s.t` has. Re-keyed as the argument itself, the holder `k`
/// was read at `Option[T = Hold3]`, where a debug assertion panicked the load (MEASURED, a cut of
/// this ticket), and with the assertion gone the call was refused.
#[test]
fn a_wrapped_arguments_nested_slot_is_the_callers() {
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
  operation go() -> Int64 = g(hold3(s: strm(t: [1])))
end
"#;
    assert_eq!(run_src(src, "wi_hqh9k.wrapped.go"), Ok(42));
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

// ── §5 found by the review: a parameter the call hands `some(arg)` is reached through `value` ──

const WRAP: &str = r#"
  import anthill.prelude.{Int64, String, Option}
  sort Strm
    sort T = ?
    entity strm(t: T, fn: (x: T) -> Int64)
  end
  sort Hold2
    entity hold2(s: Strm[T = ?])
  end
  operation inc(x: Int64) -> Int64 = x + 1
  operation slen(x: String) -> Int64 = 3
  operation mk_int() -> Hold2 = hold2(s: strm(t: 41, fn: inc))
  operation mk_str() -> Hold2 = hold2(s: strm(t: "abc", fn: slen))
  operation app(o: Option[T = Hold2], v: o.value.s.T) -> Int64 = match o
    case some(h) ->
      let g = h.s.fn
      g(v)
    case none() -> 0
  operation pk(o: Option[T = Hold2], f: (x: o.value.s.T) -> Int64) -> Int64 = match o
    case some(h) -> f(h.s.t)
    case none() -> 0
  operation whole(o: Option[T = Hold2], x: o.T) -> Int64 = 1
  operation pass(o: Option[T = Hold2], v: o.value.s.T) -> o.value.s.T = v
  sort W
    entity w(k: Hold2)
  end
"#;

fn wrap(ns: &str, body: &str) -> String {
    format!("namespace wi_hqh9k.{ns}\n{WRAP}\n{body}\nend\n")
}

/// AN ARGUMENT THE CALL WRAPS IN `some(…)` IS THE PARAMETER'S PAYLOAD: `app(k, k.s.t)` over
/// `app(o: Option[T = Hold2], v: o.value.s.T)` hands `o` the value `some(k)`, so `o.value.s.T` is
/// the caller's `k.s.T` — positional, named, a lambda hinted through it, a return re-keyed through
/// it, an argument that is a field path or a `let` alias. The parameter was re-keyed as the
/// argument itself, `o.value.s` read as `k.value.s`, a path no value has, and each call was
/// refused (MEASURED). The field-path argument is the reading `o.value` names `ww.k` by: kept in
/// the record as the field `k` of `ww`, the holder `ww` was read at the option's type (MEASURED:
/// the record's assertion, on the review of this part).
#[test]
fn an_argument_the_call_wraps_is_its_parameters_payload() {
    for (ns, call_text) in [
        ("positional", "let k = mk_int()\n    app(k, k.s.t) - 0"),
        ("named", "let k = mk_int()\n    app(v: k.s.t, o: k)"),
        ("hinted", "let k = mk_int()\n    pk(k, lambda (x) -> 42)"),
        ("returned", "let k = mk_int()\n    app(k, pass(k, k.s.t))"),
        ("field_path", "let ww = w(k: mk_int())\n    app(ww.k, ww.k.s.t)"),
        ("aliased", "let k = mk_int()\n    let a = k\n    app(a, k.s.t)"),
    ] {
        let src = wrap(ns, &format!("  operation go() -> Int64 =\n    {call_text}"));
        assert_eq!(run_src(&src, &format!("wi_hqh9k.{ns}.go")), Ok(42), "{ns}");
    }
}

/// CONTROLS — another holder's element is not the payload's: `app(k, j.s.t)` would run `inc` on
/// `"abc"`, and is refused; the option itself is the call's, so a projection off `o` is read at
/// the option the call builds (`o.T` is `Hold2`, `whole(k, k)` loads, `whole(k, 1)` is refused).
#[test]
fn a_wrapped_parameters_payload_is_its_arguments_only() {
    assert_refused_naming(
        &load_errors(&wrap(
            "another",
            "  operation go() -> Int64 =\n    let k = mk_int()\n    let j = mk_str()\n    app(k, j.s.t)",
        )),
        &["app.v (op-arg): expected k.s.T, got j.s.T"],
        "another holder's element passed for the payload's",
    );
    let src = wrap(
        "whole",
        "  operation go() -> Int64 =\n    let k = mk_int()\n    whole(k, k) + 41",
    );
    assert_eq!(run_src(&src, "wi_hqh9k.whole.go"), Ok(42));
    assert_refused_naming(
        &load_errors(&wrap(
            "whole_wrong",
            "  operation go() -> Int64 =\n    let k = mk_int()\n    whole(k, 1)",
        )),
        &["whole.x (op-arg)"],
        "an Int64 passed for the option's element",
    );
}

/// … AND IN AN EFFECT ROW: `fe(k, g2)` over `fe(o: Option[T = Hold], g: (x: Int64) -> Bool @
/// {Error[String], -o.value.s.E})` reads the lacks-row as `-k.s.E`, which the caller's `g2`
/// declares; refused before, "to lack the row `k.value.s.E`" (MEASURED). CONTROL: a callback
/// lacking another holder's row is refused.
#[test]
fn a_wrapped_parameters_payload_row_is_the_arguments() {
    let decls = r#"
  import anthill.prelude.{Int64, Bool, String, Error, Option}
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(t: T)
  end
  sort Hold
    entity hold(s: Strm[T = Int64, E = ?])
  end
  operation pure1(x: Int64) -> Bool = true
  operation fe(o: Option[T = Hold], g: (x: Int64) -> Bool @ {Error[String], -o.value.s.E}) -> Int64 = 41
"#;
    let ok = format!(
        "namespace wi_hqh9k.row\n{decls}\n  operation ce(k: Hold, g2: (x: Int64) -> Bool @ {{Error[String], -k.s.E}}) -> Int64 = fe(k, g2)\n  operation go() -> Int64 = ce(hold(s: strm(t: 1)), pure1) + 1\nend\n"
    );
    assert_eq!(run_src(&ok, "wi_hqh9k.row.go"), Ok(42));
    let wrong = format!(
        "namespace wi_hqh9k.row_wrong\n{decls}\n  operation ce(k: Hold, j: Hold, g2: (x: Int64) -> Bool @ {{Error[String], -j.s.E}}) -> Int64 = fe(k, g2)\nend\n"
    );
    assert_refused_naming(
        &load_errors(&wrong),
        &["fe.g (op-arg)", "to lack the row `k.s.E`"],
        "a callback lacking another holder's row passed for the payload's",
    );
}

// ── §6 an override a spec call dispatches to is read at the call as the call reads itself ─────

const DISPATCH: &str = r#"
  import anthill.prelude.{Int64, Option, List}
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(t: T, fn: (x: T) -> Int64)
  end
  sort Hold
    entity hold(s: Strm[T = ?, E = ?])
  end
  sort Hold3
    entity hold3(s: Strm[T = List[T = ?], E = {}])
  end
  sort W
    entity w(k: Hold)
  end
  operation inc(x: Int64) -> Int64 = x + 1
  operation len(x: List[T = Int64]) -> Int64 = 1
  operation mk() -> Hold = hold(s: strm(t: 40, fn: inc))
  operation mk3() -> Hold3 = hold3(s: strm(t: [1], fn: len))
  operation same_list[A](x: A, y: A) -> Int64 = 42
  sort Sp
    sort T = ?
    effects E = ?
    operation touch(s: Self, o: Option[T = Hold]) -> Int64 effects {s.E, o.value.s.E}
    operation pick(s: Self, o: Option[T = Hold], d: o.value.s.T) -> o.value.s.T effects {s.E}
    operation pickh(s: Self, h: Hold, d: h.s.T) -> h.s.T effects {s.E}
    operation pick3(s: Self, h: Hold3, d: h.s.T) -> h.s.T effects {s.E} = d
  end
  sort Car
    sort V = ?
    effects EC = ?
    entity car(v: V)
    provides Sp[T = V, E = {EC}]
    operation touch(c: Self, o: Option[T = Hold]) -> Int64 effects {EC, o.value.s.E} = 41
    operation pick(c: Self, p: Option[T = Hold], d: p.value.s.T) -> p.value.s.T effects {EC} = match p
      case some(h) -> h.s.t
      case none() -> d
    operation pickh(c: Self, h: Hold, d: h.s.T) -> h.s.T effects {EC} = h.s.t
    operation pick3(c: Self, h: Hold3, d: h.s.T) -> h.s.T effects {EC} = h.s.t
  end
  sort Direct
    effects E = ?
    entity direct
    provides Sp[T = Int64]
    operation touch(c: Self, p: Option[T = Hold]) -> Int64 effects {E, p.value.s.E} = 41
    operation pick(c: Self, o: Option[T = Hold], d: o.value.s.T) -> o.value.s.T effects {E} = d
    operation pickh(c: Self, h: Hold, d: h.s.T) -> h.s.T effects {E} = d
  end
"#;

fn dispatch(ns: &str, body: &str) -> String {
    format!("namespace wi_hqh9k.{ns}\n{DISPATCH}\n{body}\nend\n")
}

/// A SPEC CALL READS ITS OVERRIDE AT THE CALL AS THE CALL READS ITSELF: an argument it wraps in
/// `some(…)` at its payload (`Sp.touch(x, k)` is charged `Car.touch`'s `o.value.s.E` as `k.s.E`),
/// a field-path argument at its path (`Sp.pickh(x, ww.k, ww.k.s.t)`, `h.s.T` is `ww.k.s.T`).
/// Each was refused through the spec and loaded qualified — "undeclared effect: k.value.s.E",
/// "expected ?T, got ww.k.s.T" (MEASURED). Through `Car`, whose row member is not the spec's
/// `E`, the call takes the override's signature (the WI-606 fallback) and is charged its effects;
/// through `Direct`, which has the member, it is charged the effects alone.
#[test]
fn a_dispatched_override_reads_the_call_as_the_call_does() {
    for (ns, x, call) in [
        ("car", "Car[V = Int64, EC = R]", "Sp.touch(x, k)"),
        ("car_named", "Car[V = Int64, EC = R]", "Sp.touch(o: k, s: x)"),
        ("direct", "Direct[E = R]", "Sp.touch(x, k)"),
    ] {
        let src = dispatch(
            &format!("touch_{ns}"),
            &format!("  operation use[R](x: {x}, k: Hold) -> Int64 effects {{R, k.s.E}} = {call}"),
        );
        let errs = load_errors(&src);
        assert!(errs.is_empty(), "`{call}` over `{x}`: {errs:#?}");
    }
    let src = dispatch(
        "touch_path",
        "  operation use[R](x: Car[V = Int64, EC = R], ww: W) -> Int64 effects {R, ww.k.s.E} = Sp.touch(x, ww.k)",
    );
    let errs = load_errors(&src);
    assert!(errs.is_empty(), "`Sp.touch(x, ww.k)`: {errs:#?}");
    for (ns, x, made) in [
        ("car", "Car[V = Int64, EC = {}]", "car(v: 1)"),
        ("direct", "Direct[E = {}]", "direct"),
    ] {
        let src = dispatch(
            &format!("pick_{ns}"),
            &format!(
                "  operation go() -> Int64 =\n    let x: {x} = {made}\n    let h = mk()\n    let g = h.s.fn\n    let ww = w(k: mk())\n    let f = ww.k.s.fn\n    g(Sp.pick(x, h, h.s.t)) - 40 + f(Sp.pickh(x, ww.k, ww.k.s.t))"
            ),
        );
        assert_eq!(run_src(&src, &format!("wi_hqh9k.pick_{ns}.go")), Ok(42), "{ns}");
    }
}

/// … AND A SLOT NESTED IN A FIELD PATH IS THE CALL'S ONE: `same_list(Sp.pick3(x, k, k.s.t),
/// k.s.t)` over `pick3(…, h: Hold3, d: h.s.T) -> h.s.T`, `s: Strm[T = List[T = ?]]`, read
/// `List[T = ?T]` twice, the override's reading opening its own (MEASURED: refused, "these render
/// alike"). The spec operation has a default body here: without one the declaration rule refuses
/// the member, for the same reason, before any call is read.
#[test]
fn a_dispatched_overrides_nested_slot_is_the_calls() {
    let src = dispatch(
        "nested",
        "  operation use[R](x: Car[V = Int64, EC = R], k: Hold3) -> Int64 effects {R} =\n    same_list(Sp.pick3(x, k, k.s.t), k.s.t)\n  operation cc() -> Car[V = Int64, EC = {}] = car(v: 1)\n  operation go() -> Int64 = use(cc(), mk3())",
    );
    assert_eq!(run_src(&src, "wi_hqh9k.nested.go"), Ok(42));
}

/// CONTROLS — another holder's is not the argument's, through the spec as qualified: `use`
/// declaring `j.s.E` for `Sp.touch(x, k)` is refused naming `k.s.E`, and `Sp.pick(x, k, j.s.t)`
/// naming both.
#[test]
fn a_dispatched_overrides_reading_is_its_arguments_only() {
    for (ns, x) in [("car", "Car[V = Int64, EC = R]"), ("direct", "Direct[E = R]")] {
        assert_refused_naming(
            &load_errors(&dispatch(
                &format!("touch_wrong_{ns}"),
                &format!(
                    "  operation use[R](x: {x}, k: Hold, j: Hold) -> Int64 effects {{R, j.s.E}} = Sp.touch(x, k)"
                ),
            )),
            &["use.effects", "undeclared effect: k.s.E"],
            &format!("another holder's row declared over `{x}`"),
        );
        assert_refused_naming(
            &load_errors(&dispatch(
                &format!("pick_wrong_{ns}"),
                &format!(
                    "  operation use[R](x: {x}, k: Hold, j: Hold) -> Int64 effects {{R}} = Sp.pick(x, k, j.s.t) + 0"
                ),
            )),
            &["pick.d (op-arg): expected k.s.T, got j.s.T"],
            &format!("another holder's element passed over `{x}`"),
        );
    }
}

/// AN OVERRIDE RESTATING ITS SPEC'S FIELD-PATH EFFECT REFINES IT: `touch(c: Self, h: Hold)
/// effects {EC, h.s.E}` behind `touch(s: Self, h: Hold) effects {s.E, h.s.E}`. The two `h` are
/// two parameters, read in the spec's names before they are compared, and the rename did not
/// reach a field path's receiver: the override was refused as widening the spec's row
/// (MEASURED). CONTROL: one naming another parameter's row is refused.
#[test]
fn an_override_restating_a_field_path_effect_refines_it() {
    let program = |ns: &str, row: &str| {
        format!(
            r#"namespace wi_hqh9k.{ns}
  import anthill.prelude.Int64
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(t: T)
  end
  sort Hold
    entity hold(s: Strm[T = Int64, E = ?])
  end
  sort Sp
    effects E = ?
    operation touch(s: Self, h: Hold, j: Hold) -> Int64 effects {{s.E, h.s.E}}
  end
  sort Car
    effects EC = ?
    entity car
    provides Sp[E = {{EC}}]
    operation touch(c: Self, h: Hold, j: Hold) -> Int64 effects {{EC, {row}}} = 41
  end
end
"#
        )
    };
    let errs = load_errors(&program("refines", "h.s.E"));
    assert!(errs.is_empty(), "{errs:#?}");
    assert_refused_naming(
        &load_errors(&program("widens", "j.s.E")),
        &["overrides", "the override declares effect `j.s.E`", "effects must not widen"],
        "another parameter's row",
    );
}

// ── §7 a path's field segment is the field's label ───────────────────────────────────────────

/// A FIELD SEGMENT IS ITS LABEL, BESIDE A BINDER OF ITS NAME: the name after a dot is resolved
/// where it is written, so `ww.k` beside `let k = …`, a parameter `k` or a lambda's `k` named that
/// binder, where the field read `ww.k.s` names the field — one path, two symbols, and
/// `Car.pickh(x, ww.k, ww.k.s.t)` was refused, "expected ww.k.s.T, got ww.k.s.T" (MEASURED: the
/// parameter and the lambda; the `let` spelling too, once the call reads the argument's path).
/// CONTROL: the binder's own `k.s.t` is not `ww.k`'s.
#[test]
fn a_field_segment_is_its_label_beside_a_binder_of_its_name() {
    let src = dispatch(
        "label",
        r#"  operation ap(g: (k: Hold) -> Int64) -> Int64 = g(mk())
  operation cc() -> Car[V = Int64, EC = {}] = car(v: 1)
  operation via_let() -> Int64 =
    let k = mk()
    let ww = w(k: mk())
    let v: ww.k.s.T = ww.k.s.t
    let f = ww.k.s.fn
    f(Car.pickh(cc(), ww.k, v)) - f(Sp.pickh(cc(), ww.k, ww.k.s.t)) + 42
  operation via_param(ww: W, k: Hold) -> Int64 =
    let f = ww.k.s.fn
    f(Car.pickh(cc(), ww.k, ww.k.s.t)) + 1
  operation via_lambda(ww: W) -> Int64 = ap(lambda (k) ->
      let f = ww.k.s.fn
      f(Car.pickh(cc(), ww.k, ww.k.s.t)) + 1)
  operation go() -> Int64 = via_let() + via_param(w(k: mk()), mk()) + via_lambda(w(k: mk())) - 84"#,
    );
    assert_eq!(run_src(&src, "wi_hqh9k.label.go"), Ok(42));
    assert_refused_naming(
        &load_errors(&dispatch(
            "label_wrong",
            "  operation go(ww: W, k: Hold) -> Int64 =\n    let f = ww.k.s.fn\n    f(k.s.t)",
        )),
        &["expected ww.k.s.T, got k.s.T"],
        "the binder's element passed for the field's",
    );
}

// ── §8 the declaration rule reads a field path over one argument once ───────────────────────

const MEMBER: &str = r#"
  import anthill.prelude.{Int64, Bool, List}
  sort Strm
    sort T = ?
    effects E = ?
    entity strm(t: T)
  end
  sort Hold3
    entity hold3(s: Strm[T = List[T = ?], E = {}])
  end
  sort Box3
    sort U = ?
    entity box3(s: Strm[T = List[T = ?], E = {}], u: U)
  end
  sort Animal
    entity cat(s: Strm[T = List[T = ?], E = {}])
    entity dog(s: Strm[T = List[T = ?], E = {}])
  end
  operation same_list[A](x: A, y: A) -> Int64 = 42
"#;

fn member(ns: &str, spec: &str, carrier: &str, body: &str) -> String {
    format!(
        "namespace wi_hqh9k.{ns}\n{MEMBER}\n  sort Sp\n    effects E = ?\n{spec}\n  end\n  sort Car\n    effects EC = ?\n    entity car\n    provides Sp[E = {{EC}}]\n{carrier}\n  end\n{body}\nend\n"
    )
}

/// A MEMBER WRITTEN AS ITS SPEC FITS IT OVER A NESTED SLOT: `pick3(c: Self, h: Hold3, d: h.s.T)
/// -> h.s.T` behind the spec's same signature, `s: Strm[T = List[T = ?]]`. The declaration rule
/// read the spec's `h.s.T` and the member's apart, two unknowns, and refused the member as taking
/// less than the spec — at a parametric holder (`h: Box3[U = W]` behind `h: Box3[U = Q]`) and a
/// wider one (`h: Box3` behind `h: Box3[U = Int64]`, `h: Animal` behind `h: cat`) too (MEASURED).
/// The two parameters are one argument, read at either declaration's type. The spec call then
/// runs through the member.
#[test]
fn a_member_written_as_its_spec_fits_it_over_a_nested_slot() {
    let src = member(
        "fits",
        r#"    operation pick3(s: Self, h: Hold3, d: h.s.T) -> h.s.T effects {s.E}
    operation pickw[W](s: Self, h: Box3[U = W], d: h.s.T, w: W) -> h.s.T effects {s.E}
    operation pickb(s: Self, h: Box3[U = Int64], d: h.s.T) -> h.s.T effects {s.E}
    operation pickc(s: Self, h: cat, d: h.s.T) -> h.s.T effects {s.E}"#,
        r#"    operation pick3(c: Self, h: Hold3, d: h.s.T) -> h.s.T effects {EC} = h.s.t
    operation pickw[Q](c: Self, h: Box3[U = Q], d: h.s.T, w: Q) -> h.s.T effects {EC} = d
    operation pickb(c: Self, h: Box3, d: h.s.T) -> h.s.T effects {EC} = d
    operation pickc(c: Self, h: Animal, d: h.s.T) -> h.s.T effects {EC} = d"#,
        r#"  operation use[R](x: Car[EC = R], k: Hold3) -> Int64 effects {R} =
    same_list(Sp.pick3(x, k, k.s.t), k.s.t)
  operation cc() -> Car[EC = {}] = car
  operation go() -> Int64 = use(cc(), hold3(s: strm(t: [1])))"#,
    );
    assert_eq!(run_src(&src, "wi_hqh9k.fits.go"), Ok(42));
}

/// CONTROLS — a member that does take less is still refused, where it does: a parameter narrower
/// than the spec's `h.s.T` (`d: List[T = Int64]`), a return that is not the spec's (`->
/// List[T = Int64]`, refused at the return, where it was refused at the parameter beside it), a
/// holder narrower than the spec's (`h: cat` behind `h: Animal`) or unrelated to it (`Box3[U =
/// Bool]` behind `Box3[U = Int64]`), the last two at the holder itself.
#[test]
fn a_member_taking_less_over_a_nested_slot_is_refused() {
    let spec = "    operation pick3(s: Self, h: Hold3, d: h.s.T) -> h.s.T effects {s.E}";
    for (ns, carrier, expected) in [
        (
            "narrower_param",
            "    operation pick3(c: Self, h: Hold3, d: List[T = Int64]) -> h.s.T effects {EC} = h.s.t",
            "parameter 3 (`d: List[T = Int64]`) takes less than the spec's",
        ),
        (
            "other_return",
            "    operation pick3(c: Self, h: Hold3, d: h.s.T) -> List[T = Int64] effects {EC} = [1]",
            "the member returns `List[T = Int64]`, which is not a subtype of the spec's",
        ),
    ] {
        assert_refused_naming(
            &load_errors(&member(ns, spec, carrier, "")),
            &["does not fit", expected],
            ns,
        );
    }
    for (ns, spec, carrier, expected) in [
        (
            "narrower_holder",
            "    operation pickc(s: Self, h: Animal, d: h.s.T) -> h.s.T effects {s.E}",
            "    operation pickc(c: Self, h: cat, d: h.s.T) -> h.s.T effects {EC} = d",
            "parameter 2 is `cat` where the spec's is `Animal`",
        ),
        (
            "other_holder",
            "    operation pickb(s: Self, h: Box3[U = Int64], d: h.s.T) -> h.s.T effects {s.E}",
            "    operation pickb(c: Self, h: Box3[U = Bool], d: h.s.T) -> h.s.T effects {EC} = d",
            "parameter 2 is `Box3[U = Bool]` where the spec's is `Box3[U = Int64]`",
        ),
    ] {
        assert_refused_naming(
            &load_errors(&member(ns, spec, carrier, "")),
            &["does not fit", expected],
            ns,
        );
    }
}

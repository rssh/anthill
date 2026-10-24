//! WI-20260820-RDNS4 — A ROW PARAMETER SEVERAL CALLBACK SLOTS NAME IS THE UNION OF WHAT THEIR
//! ARGUMENTS RAISE, in any order of the arguments.
//!
//! `two[Rho](a: () -> Int64 @ {Rho}, b: () -> Int64 @ {Rho})` at a pure `a` and a `b` writing a
//! cell was refused at `b`: "expected callback effects admitted by parameter `b` … (a closed
//! row)". The call's argument loops unified each callback's row with its slot's in parameter
//! order, and a unification binds the tail to the least row ONE argument needs, closed — so `a`
//! made `Rho = {}`, and the same two arguments the other way round loaded (MEASURED). The loops
//! now relate a callback's parameters and result to its slot's and leave the row to the pass
//! that reads every argument naming the tail (`infer_discharged_row_tails`), where the
//! argument's row is one that pass solves (`slot_at_argument_row`).
//!
//! EVERY ROW DRIVES WHAT IT CLAIMS: an admitted program RUNS, and its value says which cells were
//! written (`n * 100 + c * 10 + d`, the cells starting at 1 and 2); a refusal is asserted by the
//! words that name it, beside the program that differs in one thing and runs.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! NINE PARTS, each backed out alone and RUN over this file and the `wi329`, `wi_450ka`,
//! `wi_6mpn2`, `wi_1tjqh`, `wi_9wvt7` and `wi_0rp29` rows:
//!
//! 1. THE ARGUMENT LOOPS LEAVE THE ROW TO THE PASS (`slot_at_argument_row` answering the slot as
//!    written). 9 FAIL: [`the_tickets_two_witnesses_load_and_run`],
//!    [`a_pure_and_a_writing_callback_share_the_row_in_either_order`],
//!    [`two_writing_callbacks_take_the_union_of_their_rows`],
//!    [`a_try_catch_of_two_callbacks_runs`],
//!    [`a_try_catch_body_raising_an_undecided_error_keeps_it_for_the_row`], each refused at its
//!    second callback; [`a_union_wider_than_the_caller_declares_is_refused`] and
//!    [`a_slots_absence_denies_what_another_callback_raises`] on the wording, refused at the
//!    second callback's slot rather than where the union is denied; and
//!    `wi_450ka_own_row_in_a_slot_row_test::a_row_two_callbacks_share_holds_both_of_the_callers_own_rows`
//!    and `wi_6mpn2_label_beside_row_parameter_test::a_row_two_slots_share_takes_both_callbacks_rows`.
//! 2. THE PASS RUNS WHILE A SLOT'S TAIL IS UNBOUND, not only while a type parameter is (the gate
//!    it had, "every type parameter bound: nothing to solve"). 1 FAILS:
//!    [`a_callback_with_an_open_row_beside_a_writing_one`], "undeclared effect: ??rho".
//! 3. THE PASS PAIRS LABELS ONE TO ONE (`pair_present_labels`; the subtype path's covering in
//!    its place). 3 FAIL: [`a_try_catch_body_raising_an_undecided_error_keeps_it_for_the_row`],
//!    `wi_9wvt7_reify_rule_body_test::an_unfilled_pattern_slot_is_refused_where_it_is_written`
//!    (a rule variable's payload made `Other`, and the call loaded) and
//!    `wi_9wvt7_clock_handler_test::a_drain_escaping_a_rule_body_reify_gets_no_boundary_advice`.
//! 4. A CALL'S WALKED ROW IS READ THROUGH THE VIEW (both readers wrapping it as an `effects_rows`
//!    term or occurrence again). 1 FAILS: [`a_callback_with_an_open_row_beside_a_writing_one`],
//!    a panic — and its `gen`-first program panics on the tree before this ticket too.
//! 5. A TAIL NAMED ANYWHERE BUT IN THE CALLBACK SLOTS' ROWS IS NOT LEFT TO THE PASS
//!    (`tail_named_outside_callback_rows`). 1 FAILS:
//!    [`a_tail_a_nested_callback_names_is_unified_as_before`], refused "(a closed row)".
//! 6. AN ENTITY-CARRIED ROW WRAPPED ON ITS SPINE (`wrap_bare_effect_expr_as_row`'s `Value::Entity`
//!    arm panicking again). 1 FAILS here: [`a_function_result_at_the_shared_row_is_applied`], a
//!    panic on every build before it; and `ctd6d_row_carrier_tests::an_entity_carried_bare_row_wraps_on_its_spine`
//!    in the library's tests.
//! 7. A TYPE PARAMETER SEVERAL SLOTS' LABELS NAME FIXED BY THE ARGUMENTS TOGETHER
//!    (`fix_label_type_params` not run). 2 FAIL:
//!    [`a_payload_two_slots_share_takes_what_both_arguments_offer`] and
//!    [`a_payload_two_slots_share_the_arguments_disagree_on_is_refused`].
//! 8. …ONLY WHERE TWO ARGUMENTS OR MORE OFFER IT A VALUE (one argument's labels left to the
//!    pairing). 1 FAILS: `wi_9wvt7_reify_rule_body_test::an_unfilled_pattern_slot_is_refused_where_it_is_written`
//!    — one `reify` body raising `Error[P]` and `Error[Other]` fixed `T1 = Other`, which made the
//!    rule variable's payload `Other`.
//! 9. …AND, WHERE SEVERAL VALUES FIT EVERY ARGUMENT, THE CANONICAL FIRST OF THEM (none bound, the
//!    pairing left to decide). 1 FAILS:
//!    [`a_payload_several_values_fit_is_the_canonical_first_in_either_order`], refused at `use`'s
//!    effects with `b` written first.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// `use(q, r)` over two cells, declaring `{declares}`, whose body is `body`; `go()` is pure,
/// runs it over cells holding 1 and 2, and answers `n * 100 + c * 10 + d`.
fn program(ns: &str, declares: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Unit, String, Cell, Modify, Error, Result, Function, Clock, Option}}
  import anthill.prelude.Result.{{ok, err}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.reflect.{{TypePattern}}

  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n

  operation clocked() -> Int64 effects {{Clock}} = 5

  operation gen[E]() -> Int64 effects {{E}} = 3

  sort Boom
    entity boom(why: String)
  end
  operation boomOr(n: Int64) -> Int64 effects {{Error[Boom], Error}} =
    if n < 0 then Error.raise(boom("negative")) else n

  operation two[Rho](a: () -> Int64 @ {{Rho}}, b: () -> Int64 @ {{Rho}}) -> Int64 effects {{Rho}} =
    a() * 10 + b()

  operation three[Rho](a: () -> Int64 @ {{Rho}}, b: () -> Int64 @ {{Rho}}, c: () -> Int64 @ {{Rho}}) -> Int64
    effects {{Rho}}
  = a() * 100 + b() * 10 + c()

  operation two_fn[Rho](a: Function[A = Int64, B = Int64, E = Rho], b: Function[A = Int64, B = Int64, E = Rho]) -> Int64
    effects {{Rho}}
  = a(3) * 10 + b(4)

  operation two_opt[Rho](a: Option[T = () -> Int64 @ {{Rho}}], b: () -> Int64 @ {{Rho}}) -> Int64 effects {{Rho}} =
    b()

  operation mk[Rho](a: () -> Int64 @ {{Rho}}, b: () -> Int64 @ {{Rho}}, f: Function[A = Int64, B = Int64, E = Rho]) -> Function[A = Int64, B = Int64, E = Rho] =
    f

  operation guard[E, Rho](f: () -> Int64 @ {{Error[E], Rho}}) -> Int64
    effects {{Rho}}
    requires TypePattern[T = E]
  =
    match Error.reify(f)
      case ok(v) -> v
      case err(e) -> 9

  operation two_e[E, Rho](a: () -> Int64 @ {{Error[E], Rho}}, b: () -> Int64 @ {{Error[E], Rho}}) -> Int64
    effects {{Rho}}
    requires TypePattern[T = E]
  = guard(a) * 10 + guard(b)

  operation boomOrI(n: Int64) -> Int64 effects {{Error[Boom], Error[Int64]}} =
    if n < 0 then Error.raise(boom("negative")) else Error.raise(n)

  operation quietS() -> Int64 effects {{Error[String]}} = 4

  operation iOrS(n: Int64) -> Int64 effects {{Error[Int64], Error[String]}} =
    if n > 0 then Error.raise(n) else Error.raise("none")

  operation boomIS(n: Int64) -> Int64 effects {{Error[Boom], Error[Int64], Error[String]}} =
    if n > 0 then Error.raise(n) else Error.raise(boom("none"))

  operation two_lacks[Rho](a: () -> Int64 @ {{Rho, -Clock}}, b: () -> Int64 @ {{Rho}}) -> Int64 effects {{Rho}} =
    a() * 10 + b()

  operation try_catch[Rho, P](body: () -> Int64 @ {{Error[P], Rho}}, recover: (e: P) -> Int64 @ {{Rho}}) -> Int64
    effects {{Rho}}
    requires TypePattern[T = P]
  =
    match Error.reify(body)
      case ok(v) -> v
      case err(e) -> recover(e)

  operation use(q: Cell[V = Int64], r: Cell[V = Int64]) -> Int64 effects {{{declares}}} =
{body}

  operation go() -> Int64 =
    let c: Cell[V = Int64] = Cell.new(1)
    let d: Cell[V = Int64] = Cell.new(2)
    let n = use(c, d)
    n * 100 + Cell.get(c) * 10 + Cell.get(d)
end
"#
    )
}

fn runs(tag: &str, declares: &str, body: &str) -> Result<i64, String> {
    let ns = format!("wirdns4.{tag}");
    run_int64(&program(&ns, declares, body), &format!("{ns}.go"))
}

fn refused(tag: &str, declares: &str, body: &str) -> Vec<String> {
    load_errors_of(&program(&format!("wirdns4.{tag}"), declares, body))
}

/// THE TICKET'S TWO WITNESSES, as it wrote them: a handled label in `a` and a `{Clock}` `b`,
/// and the same with no handled label at all, under a declared `effects {Clock}`. Both were
/// refused at `b`, "… (a closed row), got the lambda argument declares `Clock`" (MEASURED). Each
/// runs to `b`'s 5 (the handler shape's body ignores its `a`).
#[test]
fn the_tickets_two_witnesses_load_and_run() {
    let witnesses = [
        (
            "handled",
            "operation two_h[Rho](a: () -> Int64 @ {Error[Int64], Rho}, b: () -> Int64 @ {Rho}) -> Int64\n    effects {Rho}\n  = b()",
            "two_h(lambda () -> only_fails(), lambda () -> clocked())",
        ),
        (
            "plain",
            "operation two_plain[Rho](a: () -> Int64 @ {Rho}, b: () -> Int64 @ {Rho}) -> Int64\n    effects {Rho}\n  = a() * 0 + b()",
            "two_plain(lambda () -> pure_body(), lambda () -> clocked())",
        ),
    ];
    for (tag, two, call) in witnesses {
        let ns = format!("wirdns4.witness_{tag}");
        let src = format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, Error, Clock}}
  operation only_fails() -> Int64
    effects {{Error[Int64]}}
  = 41
  operation pure_body() -> Int64
    effects {{}}
  = 7
  operation clocked() -> Int64
    effects {{Clock}}
  = 5
  {two}
  operation t() -> Int64
    effects {{Clock}}
  = {call}
end
"#
        );
        assert_eq!(run_int64(&src, &format!("{ns}.t")), Ok(5), "the {tag} witness");
    }
}

/// A PURE CALLBACK AND A WRITING ONE, IN EITHER ORDER AND EVERY SPELLING: `Rho = {Modify[r]}`.
/// `a` answers 3, `b` 4. Pure first was refused at the writer; writer first ran (MEASURED).
#[test]
fn a_pure_and_a_writing_callback_share_the_row_in_either_order() {
    let pure_first = [
        ("lambda", "    two(lambda () -> 3, lambda () -> put(r, 4))"),
        ("let", "    let f = lambda () -> 3\n    let g = lambda () -> put(r, 4)\n    two(f, g)"),
        ("named", "    two(b: lambda () -> put(r, 4), a: lambda () -> 3)"),
        ("function", "    two_fn(lambda (n: Int64) -> n, lambda (n: Int64) -> put(r, n))"),
    ];
    for (spelling, body) in pure_first {
        assert_eq!(runs(&format!("pure_first_{spelling}"), "Modify[r]", body), Ok(3414), "{spelling}");
    }
    let writer_first = [
        ("lambda", "    two(lambda () -> put(r, 3), lambda () -> 4)"),
        ("named", "    two(b: lambda () -> 4, a: lambda () -> put(r, 3))"),
        ("function", "    two_fn(lambda (n: Int64) -> put(r, n), lambda (n: Int64) -> n)"),
    ];
    for (spelling, body) in writer_first {
        assert_eq!(runs(&format!("writer_first_{spelling}"), "Modify[r]", body), Ok(3413), "{spelling}");
    }
}

/// TWO CALLBACKS WRITING TWO CELLS: `Rho = {Modify[q], Modify[r]}`, and three callbacks the
/// union of three. Each was refused at the second writer, whatever the order (MEASURED).
#[test]
fn two_writing_callbacks_take_the_union_of_their_rows() {
    let both = "Modify[q], Modify[r]";
    assert_eq!(runs("both_qr", both, "    two(lambda () -> put(q, 3), lambda () -> put(r, 4))"), Ok(3434));
    assert_eq!(runs("both_rq", both, "    two(lambda () -> put(r, 3), lambda () -> put(q, 4))"), Ok(3443));
    assert_eq!(
        runs("three", both, "    three(lambda () -> 5, lambda () -> put(q, 6), lambda () -> put(r, 7))"),
        Ok(56767),
    );
}

/// THE CONTROL: THE UNION IS STILL HELD TO WHAT THE CALLER DECLARES. `use` declaring one of
/// the two writes is refused at its own effects, naming the other, in either order — and the
/// bracket that says too little is refused at the callback it leaves out. Refused on every
/// build; before, at the second callback's slot, so the first two assertions fail on their
/// wording under part 1.
#[test]
fn a_union_wider_than_the_caller_declares_is_refused() {
    for (tag, body) in [
        ("qr", "    two(lambda () -> put(q, 3), lambda () -> put(r, 4))"),
        ("rq", "    two(lambda () -> put(r, 4), lambda () -> put(q, 3))"),
    ] {
        assert_refused_naming(
            &refused(&format!("under_{tag}"), "Modify[r]", body),
            &["use.effects", "undeclared effect", "Modify[T = q]"],
            &format!("a union of two writes under a `use` declaring one ({tag})"),
        );
    }
    assert_refused_naming(
        &refused(
            "bracket_short",
            "Modify[q], Modify[r]",
            "    two[Rho = {Modify[r]}](lambda () -> put(q, 3), lambda () -> put(r, 4))",
        ),
        &["type mismatch in two.a (op-arg)", "Modify[T = q]"],
        "a bracket leaving out the first callback's write",
    );
}

/// A SLOT'S ABSENCE HOLDS THE UNION: `a: … @ {Rho, -Clock}` makes `Rho` lack `Clock`, so a `b`
/// raising `Clock` has no row to raise it in — refused in either order, the row parameter left
/// unbound ("expected a type for 'Rho'"), as a slot denying its own callback's label is
/// (`wi_9wvt7_guarded_callback_row_test`). A `b` writing a cell is admitted.
#[test]
fn a_slots_absence_denies_what_another_callback_raises() {
    for (tag, call) in [
        ("ab", "    two_lacks(lambda () -> 3, lambda () -> clocked())"),
        ("ba", "    two_lacks(b: lambda () -> clocked(), a: lambda () -> 3)"),
    ] {
        assert_refused_naming(
            &refused(&format!("lacks_{tag}"), "Clock", call),
            &["two_lacks.type_arg", "expected a type for 'Rho'"],
            &format!("`{}`", call.trim()),
        );
    }
    assert_eq!(
        runs("lacks_ok", "Modify[r]", "    two_lacks(lambda () -> 3, lambda () -> put(r, 4))"),
        Ok(3414),
    );
}

/// A LIBRARY `try_catch` OVER `Error.reify`, ITS TWO CALLBACKS SHARING ONE ROW (proposal 027.4
/// named it as waiting on this ticket): the body writes `q` and raises, the handler writes `r`.
/// The body's row less `Error[Int64]`, beside the handler's: `{Modify[q], Modify[r]}`. Raised:
/// the body wrote 6, the handler wrote and answered 7 — 767; not raised, the body's 6 — 662.
/// Both orders of the arguments. Each was refused at the callback written second, "… (a closed
/// row), got the lambda argument declares …" (MEASURED).
#[test]
fn a_try_catch_of_two_callbacks_runs() {
    let both = "Modify[q], Modify[r]";
    let raise = "lambda () -> Error.raise(put(q, 6))";
    let quiet = "lambda () -> put(q, 6)";
    let recover = "lambda (e: Int64) -> put(r, e + 1)";
    assert_eq!(runs("catch_raised", both, &format!("    try_catch({raise}, {recover})")), Ok(767));
    assert_eq!(
        runs("catch_raised_named", both, &format!("    try_catch(recover: {recover}, body: {raise})")),
        Ok(767),
    );
    assert_eq!(runs("catch_quiet", both, &format!("    try_catch({quiet}, {recover})")), Ok(662));
}

/// … AND A BODY DECLARING AN UNDECIDED `Error` BESIDE `Error[Boom]`: the body's `Error[Boom]`
/// pairs with the slot's `Error[P]`, and the undecided `Error` is the rest of its row, which
/// `use` declares. It raises `boom`, the handler writes 9: 919. The pairing is one to one:
/// with the subtype path's covering in its place, the slot's one `Error[P]` took both labels,
/// the undecided payload made `Boom`, and the call was refused at `body`, "… (a closed row),
/// got the lambda argument declares `Error`".
#[test]
fn a_try_catch_body_raising_an_undecided_error_keeps_it_for_the_row() {
    let ns = "wirdns4.catch_undecided";
    let src = program(
        ns,
        "Error, Modify[r]",
        "    try_catch(lambda () -> boomOr(-1), lambda (e: Boom) -> put(r, 9))",
    )
    .replace("  operation go() -> Int64 =", "  operation go() -> Int64 effects {Error} =");
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(919));
}

/// A CALLBACK WHOSE OWN ROW IS OPEN — `gen[E]`, a generic operation passed as a value — binds
/// `Rho` to a row open at a fresh tail, and the other callback's row is what that tail takes,
/// in either order: `gen` answers 3, the writer 4 or 3. That tail is no type parameter of
/// `two`, so the inference cannot stop at "every type parameter is bound": stopped there, the
/// tail stayed open and the caller was refused, "undeclared effect: ??rho".
///
/// THE ROW SO BOUND IS A TERM ROW OPEN AT A TAIL BOUND TO AN OCCURRENCE ROW (`open(?f)`, `?f :=
/// {Modify[r]}`), and the walk of the call's row hands it back as an entity: the call's row
/// reader panicked, "effect row on a THIRD carrier" — for `gen` first on every build, and for
/// `gen` second once the row is the union. Read at the call, in a lambda's row and through a
/// second generic call.
#[test]
fn a_callback_with_an_open_row_beside_a_writing_one() {
    assert_eq!(runs("gen_first", "Modify[r]", "    two(gen, lambda () -> put(r, 4))"), Ok(3414));
    assert_eq!(runs("gen_second", "Modify[r]", "    two(lambda () -> put(r, 3), gen)"), Ok(3313));
    assert_eq!(
        runs("gen_in_lambda", "Modify[r]", "    let f = lambda () -> two(gen, lambda () -> put(r, 4))\n    f()"),
        Ok(3414),
    );
    assert_eq!(
        runs("gen_nested", "Modify[r]", "    two(lambda () -> two(gen, lambda () -> put(r, 4)), gen)"),
        Ok(34314),
    );
}

/// A TAIL A NESTED CALLBACK NAMES TOO is met by unification as the arguments are, not left to
/// the pass: `two_opt[Rho](a: Option[T = () -> Int64 @ {Rho}], b: () -> Int64 @ {Rho})` with the
/// writer `b` first unifies `Rho = {Modify[r]}` there, and the pure callback in the option
/// conforms — `two_opt` answers `b`'s 4: 414, as on the build before this ticket. Left to the pass, `b` was
/// refused "(a closed row)": the option's unification closed the row before the pass ran. The
/// other order is refused on every build (the option, unified first, closes the row; a nested
/// callback is no slot the pass reads).
#[test]
fn a_tail_a_nested_callback_names_is_unified_as_before() {
    assert_eq!(
        runs("opt_writer_first", "Modify[r]", "    two_opt(b: lambda () -> put(r, 4), a: some(lambda () -> 3))"),
        Ok(414),
    );
}

/// A `Function` RESULT WHOSE ROW IS THE SHARED TAIL, open at a tail an open callback row left
/// for a writer's row: `mk(gen, lambda () -> put(r, 4), f)` returns `f` at `E = Rho`, and the
/// row read off the walked result is an entity spine. Applying it panicked, "effect row on a
/// THIRD carrier", on every build. It answers `f(5)`, no cell written: 512.
#[test]
fn a_function_result_at_the_shared_row_is_applied() {
    assert_eq!(
        runs(
            "fn_result",
            "Modify[r]",
            "    let g = mk(gen, lambda () -> put(r, 4), lambda (n: Int64) -> n)\n    g(5)",
        ),
        Ok(512),
    );
}

/// A TYPE PARAMETER BOTH SLOTS' LABELS NAME TAKES THE PAYLOAD BOTH ARGUMENTS OFFER, in either
/// order: `two_e[E, Rho](a: … @ {Error[E], Rho}, b: … @ {Error[E], Rho})` discharges `Error[E]`
/// from each (`guard`, over `Error.reify`). `a` writes `q` and raises 5; `b` may raise `Boom` or
/// an `Int64` and raises 7. `E = Int64` is the one payload both offer, and `b`'s `Error[Boom]`
/// is the row's: both caught, 9 and 9, `q` written — 9952. Each order was refused on the build
/// before (the first pair fixed `E`, and the other order's label went to `Rho`).
#[test]
fn a_payload_two_slots_share_takes_what_both_arguments_offer() {
    let ns_of = |tag: &str| format!("wirdns4.{tag}");
    for (tag, call) in [
        ("payload_ab", "two_e(lambda () -> Error.raise(put(q, 5)), lambda () -> boomOrI(7))"),
        ("payload_ba", "two_e(b: lambda () -> boomOrI(7), a: lambda () -> Error.raise(put(q, 5)))"),
    ] {
        let ns = ns_of(tag);
        let src = program(&ns, "Modify[q], Error[Boom]", &format!("    {call}"))
            .replace("  operation go() -> Int64 =", "  operation go() -> Int64 effects {Error[Boom]} =");
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(9952), "`{call}`");
    }
}

/// … AND WHERE THE ARGUMENTS OFFER NO ONE PAYLOAD THE CALL IS REFUSED, in either order, naming
/// each in the order written — §8.1's refusal of a parameter whose arguments disagree. `a` raises an `Int64`, `b`
/// declares `Error[String]`: `E = Int64` (`b`'s label to the row) loaded with `a` first and
/// `E = String` was refused with `b` first (MEASURED). The bracket the refusal asks for runs: `a`
/// caught, 9; `b` answers 4; `q` written — 9452.
#[test]
fn a_payload_two_slots_share_the_arguments_disagree_on_is_refused() {
    for (tag, call, listed) in [
        ("disagree_ab", "two_e(lambda () -> Error.raise(put(q, 5)), lambda () -> quietS())", "Int64 (a), String (b)"),
        ("disagree_ba", "two_e(b: lambda () -> quietS(), a: lambda () -> Error.raise(put(q, 5)))", "String (b), Int64 (a)"),
    ] {
        let src = program(&format!("wirdns4.{tag}"), "Modify[q], Error[String]", &format!("    {call}"))
            .replace("  operation go() -> Int64 =", "  operation go() -> Int64 effects {Error[String]} =");
        let errs = load_errors_of(&src);
        assert_eq!(errs.len(), 1, "`{call}`: the one refusal, got {errs:#?}");
        assert_refused_naming(
            &errs,
            &["type mismatch in two_e.type_args", "no type every argument's labels give type parameter `E` of `two_e`", listed],
            &format!("`{call}`"),
        );
    }
    let ns = "wirdns4.disagree_bracket";
    let src = program(
        ns,
        "Modify[q], Error[String]",
        "    two_e[E = Int64](lambda () -> Error.raise(put(q, 5)), lambda () -> quietS())",
    )
    .replace("  operation go() -> Int64 =", "  operation go() -> Int64 effects {Error[String]} =");
    assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(9452));
}

/// … AND WHERE SEVERAL PAYLOADS FIT EVERY ARGUMENT, the first in the canonical label order is
/// bound, whichever argument is written first: `a` may raise `Int64` or `String`, `b` `Boom`,
/// `Int64` or `String`, so `E = Int64` and the rest is the row. Both raise an `Int64`, both are
/// caught, `q` written — 9952. Left to the pairing, `b` first made `E = Boom` (its first label),
/// and `a`'s `Error[Int64]` went to the row, which `use` does not declare: refused.
#[test]
fn a_payload_several_values_fit_is_the_canonical_first_in_either_order() {
    for (tag, call) in [
        ("several_ab", "two_e(lambda () -> iOrS(put(q, 5)), lambda () -> boomIS(7))"),
        ("several_ba", "two_e(b: lambda () -> boomIS(7), a: lambda () -> iOrS(put(q, 5)))"),
    ] {
        let ns = format!("wirdns4.{tag}");
        let src = program(&ns, "Modify[q], Error[String], Error[Boom]", &format!("    {call}"))
            .replace("  operation go() -> Int64 =", "  operation go() -> Int64 effects {Error[String], Error[Boom]} =");
        assert_eq!(run_int64(&src, &format!("{ns}.go")), Ok(9952), "`{call}`");
    }
}

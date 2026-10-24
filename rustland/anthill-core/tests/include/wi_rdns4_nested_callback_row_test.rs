//! WI-20260820-RDNS4 — A CALLBACK'S ROW IS JUDGED WHEREVER THE CALLBACK STANDS, and a row
//! parameter the callbacks in a parameter's option share is inferred as one passed bare is.
//!
//! The row of a callback was checked at an operation's callback parameter alone. One standing
//! in an option's payload, a list's element, a result, a tuple, a sort of no declared variance,
//! a callback's result, an entity field, a function value's parameter or the `some(…)` an
//! option's slot wraps a bare one in reached a closed row unread, and the pure operation that
//! received it ran its effect: `run_opt(some(lambda () -> put(r, 4)))` over `o: Option[T = () ->
//! Int64 @ {}]` wrote the cell (MEASURED, on the build before this ticket too). And read, a row
//! parameter two options' callbacks share was decided by the first argument, as a bare
//! callback's was before this ticket.
//!
//! EVERY ROW DRIVES WHAT IT CLAIMS: an admitted program RUNS, its value saying which cell was
//! written (`n * 10 + c`, the cell starting at 2); a refusal is asserted by the words that name
//! it, beside the program that differs in one thing and runs.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! SEVEN PARTS, each backed out alone and RUN over this file, `wi_rdns4_shared_row_tail_test` and
//! the `wi329`, `wi_450ka`, `wi_6mpn2`, `wi_1tjqh`, `wi_9wvt7`, `wi_0rp29` and `wi_nekr0` rows:
//!
//! 1. AN ARROW HELD BELOW A CHECKED TYPE'S TOP JUDGED (`callback_rows_error`'s nested pairs).
//!    3 FAIL, each refusal loading and running:
//!    [`a_callback_in_an_option_is_held_to_the_options_row`],
//!    [`a_callback_in_a_list_a_result_a_tuple_or_an_invariant_sort_is_held_to_its_row`] and
//!    [`a_callback_a_callback_returns_is_held_to_its_row`].
//! 2. THE ARROW A SITE CHECKS ITS WRITTEN VALUE AGAINST JUDGED (its top pair). 4 FAIL:
//!    [`an_entity_fields_callback_is_held_to_the_fields_row`],
//!    [`a_list_elements_callback_is_held_to_the_element_types_row`],
//!    [`a_function_values_callback_is_held_to_its_parameters_row`] and
//!    [`a_bare_callback_an_option_wraps_is_held_to_the_options_row`].
//! 3. THE CALLBACKS A PARAMETER HOLDS READ BY THE ROW INFERENCE (`map_held_arrows` reading the
//!    parameter's top alone, in the loops' slot and the pass). 1 FAILS:
//!    [`a_row_parameter_callbacks_in_options_share_is_their_union_in_either_order`], refused at
//!    the second option with the pure one first.
//! 4. TWO ARROWS BELOW THE TOP THAT DIFFER IN A ROW PRINTED WITH THEIR ROWS (`Spelling::Rows`).
//!    1 FAILS: [`a_mismatch_of_nested_arrows_prints_their_rows`], "these render alike".
//! 5. A VARIABLE NOT WALKED AGAIN INSIDE ITS OWN BINDING (`map_held_arrows_on`'s `entered`).
//!    [`a_cyclic_binding_the_arguments_leave_is_walked_once`] overflows the stack, which aborts
//!    the test binary: measured with that row alone.
//! 6. AN ARROW'S RESULT READ (`map_held_arrows` stopping at a callable). 1 FAILS:
//!    [`a_callback_a_callback_returns_is_held_to_its_row`].
//! 7. A PAYLOAD CALLBACK'S ROW REFUSAL REPORTED AS IT IS (`some_coercion` reporting its outer pair).
//!    1 FAILS: [`a_bare_callback_an_option_wraps_is_held_to_the_options_row`], on the wording.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// `use(r)` over a cell, declaring `{declares}`, whose body is `body`; `go()` declares `Clock`
/// where `use` does — the cell is its own — runs it over a cell holding 2, and answers
/// `n * 10 + c`.
fn program(ns: &str, declares: &str, body: &str) -> String {
    let go_declares = if declares.contains("Clock") { "Clock" } else { "" };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Cell, Modify, Option, List, Result, Function, Clock}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.Result.{{ok, err}}
  import anthill.prelude.List.{{cons, nil}}

  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n

  operation clocked() -> Int64 effects {{Clock}} = 5

  operation run_opt(o: Option[T = () -> Int64 @ {{}}]) -> Int64 =
    match o
      case some(f) -> f()
      case none -> 0

  operation run_opt_r[R](o: Option[T = () -> Int64 @ {{R}}]) -> Int64 effects {{R}} =
    match o
      case some(f) -> f()
      case none -> 0

  operation run_list(xs: List[T = () -> Int64 @ {{}}]) -> Int64 =
    match xs
      case cons(f, rest) -> f()
      case nil -> 0

  operation run_res(o: Result[T = () -> Int64 @ {{}}, E = Int64]) -> Int64 =
    match o
      case ok(f) -> f()
      case err(e) -> 0

  operation run_tup(t: (f: () -> Int64 @ {{}}, n: Int64)) -> Int64 =
    let g = t.f
    g() + t.n

  sort Inv
    sort T = ?
    entity inv(v: T)
  end
  operation run_inv(i: Inv[T = () -> Int64 @ {{}}]) -> Int64 =
    match i
      case inv(v) -> v()

  sort Holder
    entity holder(f: () -> Int64 @ {{}})
  end
  operation run_holder(h: Holder) -> Int64 =
    match h
      case holder(f) -> f()

  sort FHolder
    entity fh(f: Function[A = Int64, B = Int64])
  end
  operation run_fh(h: FHolder) -> Int64 =
    match h
      case fh(f) -> f(4)

  sort Box
    effects EB = ?
    entity box(g: () -> Int64 @ {{EB}})
  end
  operation run_box(b: Box[EB = {{}}]) -> Int64 =
    match b
      case box(g) -> g()
  operation run_box_r(b: Box[EB = {{Modify[q]}}], q: Cell[V = Int64]) -> Int64 effects {{Modify[q]}} =
    match b
      case box(g) -> g()

  sort OHolder
    entity oh(o: Option[T = () -> Int64 @ {{}}])
  end
  operation run_oh(h: OHolder) -> Int64 =
    match h
      case oh(o) -> run_opt(o)

  operation curried(f: () -> () -> Int64 @ {{}}) -> Int64 =
    let g = f()
    g()
  operation curried_r[R](f: () -> () -> Int64 @ {{R}}) -> Int64 effects {{R}} =
    let g = f()
    g()

  operation two_ab[A, B](f: (x: A) -> B, g: (y: B) -> A) -> Int64 = 1

  operation opt2[Rho](a: Option[T = () -> Int64 @ {{Rho}}], b: Option[T = () -> Int64 @ {{Rho}}]) -> Int64
    effects {{Rho}}
  = run_opt_r(a) * 10 + run_opt_r(b)

  operation two_opt[Rho](a: Option[T = () -> Int64 @ {{Rho}}], b: () -> Int64 @ {{Rho}}) -> Int64
    effects {{Rho}}
  = run_opt_r(a) * 10 + b()

  operation use(r: Cell[V = Int64]) -> Int64 effects {{{declares}}} =
{body}

  operation go() -> Int64 effects {{{go_declares}}} =
    let c: Cell[V = Int64] = Cell.new(2)
    let n = use(c)
    n * 10 + Cell.get(c)
end
"#
    )
}

fn runs(tag: &str, declares: &str, body: &str) -> Result<i64, String> {
    let ns = format!("wirdns4n.{tag}");
    run_int64(&program(&ns, declares, body), &format!("{ns}.go"))
}

fn refused(tag: &str, declares: &str, body: &str) -> Vec<String> {
    load_errors_of(&program(&format!("wirdns4n.{tag}"), declares, body))
}

/// A CALLBACK IN AN OPTION IS HELD TO THE OPTION'S ROW: `run_opt(some(lambda () -> put(r, 4)))`
/// over `o: Option[T = () -> Int64 @ {}]` is refused — it loaded on every build, and `run_opt`,
/// declaring no effect, wrote the cell (MEASURED) — and so is `some(clocked)`, a `let`-held
/// option and an `use` declaring the write, which the option's row still does not admit. A pure
/// callback there runs, 3 (32); at a row parameter the write is the call's (`run_opt_r`), 4 (44).
#[test]
fn a_callback_in_an_option_is_held_to_the_options_row() {
    for (tag, declares, body, label) in [
        ("opt_writer", "", "    run_opt(some(lambda () -> put(r, 4)))", "Modify[T = r]"),
        ("opt_writer_declared", "Modify[r]", "    run_opt(some(lambda () -> put(r, 4)))", "Modify[T = r]"),
        ("opt_let", "", "    let o = some(lambda () -> put(r, 4))\n    run_opt(o)", "Modify[T = r]"),
        ("opt_clock", "Clock", "    run_opt(some(lambda () -> clocked()))", "Clock"),
    ] {
        assert_refused_naming(
            &refused(tag, declares, body),
            &["run_opt.o (op-arg)", "an arrow inside the declared type (a closed row)", label],
            &format!("`{}`", body.trim()),
        );
    }
    assert_eq!(runs("opt_pure", "", "    run_opt(some(lambda () -> 3))"), Ok(32));
    assert_eq!(runs("opt_row", "Modify[r]", "    run_opt_r(some(lambda () -> put(r, 4)))"), Ok(44));
}

/// … AND IN A LIST, A RESULT, A TUPLE'S COMPONENT AND A SORT OF NO DECLARED VARIANCE, each loading
/// and writing the cell on every build before (MEASURED). Each pure twin runs.
#[test]
fn a_callback_in_a_list_a_result_a_tuple_or_an_invariant_sort_is_held_to_its_row() {
    for (tag, writer, pure, value, at) in [
        ("list", "    let xs = [lambda () -> put(r, 4)]\n    run_list(xs)", "    let xs = [lambda () -> 3]\n    run_list(xs)", 32, "run_list.xs (op-arg)"),
        ("result", "    run_res(ok(lambda () -> put(r, 4)))", "    run_res(ok(lambda () -> 3))", 32, "run_res.o (op-arg)"),
        ("tuple", "    run_tup((f: lambda () -> put(r, 4), n: 1))", "    run_tup((f: lambda () -> 3, n: 1))", 42, "run_tup.t (op-arg)"),
        ("inv", "    run_inv(inv(lambda () -> put(r, 4)))", "    run_inv(inv(lambda () -> 3))", 32, "run_inv.i (op-arg)"),
    ] {
        assert_refused_naming(
            &refused(&format!("{tag}_writer"), "", writer),
            &[at, "an arrow inside the declared type (a closed row)", "Modify[T = r]"],
            &format!("`{}`", writer.trim()),
        );
        assert_eq!(runs(&format!("{tag}_pure"), "", pure), Ok(value), "`{}`", pure.trim());
    }
}

/// AN ENTITY FIELD'S CALLBACK IS HELD TO THE FIELD'S ROW: `holder(f: () -> Int64 @ {})`, a
/// `Function[A, B]` field (pure by its default) and a field at the sort's row parameter fixed by
/// a bracket (`box[EB = {}]`) each refuse a writing lambda — each loaded and wrote the cell on
/// every build before (MEASURED). Their pure twins run, and a field at a row parameter the write
/// is given to runs it: 44.
#[test]
fn an_entity_fields_callback_is_held_to_the_fields_row() {
    for (tag, writer, at) in [
        ("holder", "    run_holder(holder(lambda () -> put(r, 4)))", "holder.f (entity-field)"),
        ("function", "    run_fh(fh(lambda (n: Int64) -> put(r, n)))", "fh.f (entity-field)"),
        ("box", "    run_box(box[EB = {}](g: lambda () -> put(r, 4)))", "box.g (entity-field)"),
    ] {
        assert_refused_naming(
            &refused(&format!("field_{tag}"), "", writer),
            &[at, "the declared arrow (a closed row)", "Modify[T = r]"],
            &format!("`{}`", writer.trim()),
        );
    }
    assert_eq!(runs("field_holder_pure", "", "    run_holder(holder(lambda () -> 3))"), Ok(32));
    assert_eq!(runs("field_function_pure", "", "    run_fh(fh(lambda (n: Int64) -> n))"), Ok(42));
    assert_eq!(
        runs("field_box_row", "Modify[r]", "    run_box_r(box[EB = {Modify[r]}](g: lambda () -> put(r, 4)), r)"),
        Ok(44),
    );
}

/// A LIST ELEMENT'S CALLBACK IS HELD TO THE ELEMENT TYPE'S ROW: a literal at `run_list`'s
/// parameter takes the slot's element type (§4.6), and a writing lambda there was admitted and
/// run (MEASURED). Refused at the element; the pure element runs.
#[test]
fn a_list_elements_callback_is_held_to_the_element_types_row() {
    assert_refused_naming(
        &refused("element_writer", "", "    run_list([lambda () -> put(r, 4)])"),
        &["list.element 1 (collection-element)", "the declared arrow (a closed row)", "Modify[T = r]"],
        "`run_list([lambda () -> put(r, 4)])`",
    );
    assert_eq!(runs("element_pure", "", "    run_list([lambda () -> 3])"), Ok(32));
}

/// A ROW PARAMETER THE CALLBACKS IN TWO OPTIONS SHARE IS THEIR UNION, in either order, as for two
/// bare callbacks: `opt2(some(pure), some(writer))` binds `Rho = {Modify[r]}` and runs, 34 (344),
/// the other way round 43 (434); and so does an option beside a bare callback (`two_opt`), 34.
/// With the option's row read by the check but not by the inference, the pure one written first
/// closed the row and the writer was refused at its option. A caller declaring less than the
/// union is refused at its own effects in either order — on the build before, the pure-first
/// order loaded and wrote the cell from a `use` declaring nothing (MEASURED).
#[test]
fn a_row_parameter_callbacks_in_options_share_is_their_union_in_either_order() {
    for (tag, body, value) in [
        ("opt2_pure_first", "    opt2(some(lambda () -> 3), some(lambda () -> put(r, 4)))", 344),
        ("opt2_writer_first", "    opt2(some(lambda () -> put(r, 4)), some(lambda () -> 3))", 434),
        ("two_opt_pure_first", "    two_opt(some(lambda () -> 3), lambda () -> put(r, 4))", 344),
        ("two_opt_writer_first", "    two_opt(b: lambda () -> put(r, 4), a: some(lambda () -> 3))", 344),
    ] {
        assert_eq!(runs(tag, "Modify[r]", body), Ok(value), "`{}`", body.trim());
    }
    for (tag, body) in [
        ("under_pure_first", "    opt2(some(lambda () -> 3), some(lambda () -> put(r, 4)))"),
        ("under_writer_first", "    opt2(some(lambda () -> put(r, 4)), some(lambda () -> 3))"),
    ] {
        assert_refused_naming(
            &refused(tag, "", body),
            &["use.effects", "undeclared effect", "Modify[T = r]"],
            &format!("`{}`", body.trim()),
        );
    }
}

/// TWO TYPES THAT DIFFER ONLY IN THE ROW OF AN ARROW BELOW THEIR TOP ARE PRINTED WITH THEIR ROWS:
/// an operation reference in an option at a pure option — refused on every build, by the
/// whole-type relation — and a `let` annotation printed `expected Option[T = () -> Int64], got
/// Option[T = () -> Int64] (these render alike …)`.
#[test]
fn a_mismatch_of_nested_arrows_prints_their_rows() {
    for (tag, declares, body, actual) in [
        ("print_eta", "Clock", "    run_opt(some(clocked))", "got Option[T = () -> Int64 @ {Clock}]"),
        (
            "print_let",
            "",
            "    let o: Option[T = () -> Int64 @ {}] = some(lambda () -> put(r, 4))\n    run_opt(o)",
            "got Option[T = () -> Int64 @ {Modify[T = r]}]",
        ),
    ] {
        let errs = refused(tag, declares, body);
        assert_refused_naming(&errs, &["expected Option[T = () -> Int64 @ {}]", actual], &format!("`{}`", body.trim()));
        assert!(
            errs.iter().all(|e| !e.contains("render alike")),
            "`{}`: the rows say the difference, got {errs:#?}",
            body.trim()
        );
    }
}

/// A FUNCTION VALUE'S PARAMETER HOLDS ITS CALLBACK TO ITS ROW: `h(lambda () -> put(r, 4))` over
/// `let h: (g: () -> Int64 @ {}) -> Int64 = …` loaded and wrote the cell from a `use` declaring
/// nothing (MEASURED, on every build before). Refused; a pure callback runs, 3.
#[test]
fn a_function_values_callback_is_held_to_its_parameters_row() {
    let h = "    let h: (g: () -> Int64 @ {}) -> Int64 = lambda (g) -> g()\n";
    assert_refused_naming(
        &refused("value_writer", "", &format!("{h}    h(lambda () -> put(r, 4))")),
        &["h._1 (op-arg)", "the declared arrow (a closed row)", "Modify[T = r]"],
        "`h(lambda () -> put(r, 4))`",
    );
    assert_eq!(runs("value_pure", "", &format!("{h}    h(lambda () -> 3)")), Ok(32));
}

/// A BARE CALLBACK AN OPTION'S SLOT WRAPS IN `some(…)` IS HELD TO THE OPTION'S ROW, at an argument
/// and at a field: `run_opt(lambda () -> put(r, 4))` and `oh(lambda () -> put(r, 4))` loaded and
/// wrote the cell (MEASURED, on every build before). Refused naming the row — the coercion's own
/// outer pair (`expected Option[T = () -> Int64], got () -> Int64`) says nothing of it; the pure
/// callback runs, 3.
#[test]
fn a_bare_callback_an_option_wraps_is_held_to_the_options_row() {
    for (tag, body, at) in [
        ("wrapped_arg", "    run_opt(lambda () -> put(r, 4))", "run_opt.o (op-arg)"),
        ("wrapped_field", "    run_oh(oh(lambda () -> put(r, 4)))", "oh.o (entity-field)"),
    ] {
        assert_refused_naming(
            &refused(tag, "", body),
            &[at, "the declared arrow (a closed row)", "Modify[T = r]"],
            &format!("`{}`", body.trim()),
        );
    }
    assert_eq!(runs("wrapped_pure", "", "    run_opt(lambda () -> 3)"), Ok(32));
}

/// A CALLBACK A CALLBACK RETURNS IS HELD TO ITS ROW: `curried(lambda () -> lambda () -> put(r, 4))`
/// over `f: () -> () -> Int64 @ {}` loaded and wrote the cell (MEASURED, on every build before).
/// Refused; the pure one runs, 3; at a row parameter the write is the call's (`curried_r`), 4.
#[test]
fn a_callback_a_callback_returns_is_held_to_its_row() {
    assert_refused_naming(
        &refused("returned_writer", "", "    curried(lambda () -> lambda () -> put(r, 4))"),
        &["curried.f (op-arg)", "an arrow inside the declared type (a closed row)", "Modify[T = r]"],
        "`curried(lambda () -> lambda () -> put(r, 4))`",
    );
    assert_eq!(runs("returned_pure", "", "    curried(lambda () -> lambda () -> 3)"), Ok(32));
    assert_eq!(
        runs("returned_row", "Modify[r]", "    curried_r(lambda () -> lambda () -> put(r, 4))"),
        Ok(44),
    );
}

/// A BINDING THE ARGUMENTS LEAVE CYCLIC IS WALKED ONCE: `two_ab[A, B](f: (x: A) -> B, g: (y: B)
/// -> A)` given `let`-held `lambda (x) -> [x]` and `lambda (y) -> [y]` makes `A` a list of lists of
/// itself, and the walk down the callbacks' results followed it until the stack overflowed, where
/// the call runs (MEASURED, family `d-mutual-callbacks`): 1 (12).
#[test]
fn a_cyclic_binding_the_arguments_leave_is_walked_once() {
    assert_eq!(
        runs("cyclic", "", "    let f = lambda (x) -> [x]\n    let g = lambda (y) -> [y]\n    two_ab(f, g)"),
        Ok(12),
    );
}

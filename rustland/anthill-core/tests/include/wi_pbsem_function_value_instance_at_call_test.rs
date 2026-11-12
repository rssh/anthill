//! WI-20261112-PBSEM — an operation taken as a function value whose carrier a later argument
//! fixes is given its dictionaries at the instance the call fixes (kernel-language §5.4: it
//! is the lambda that calls the operation, typed at the instance the value is used at).
//!
//! Over `useS[P](x: P) -> Int64 requires Desc[T = P]`, `Sp { sort P = ?  requires Desc[T = P]
//! operation t(x: P) -> Int64 }` and `app[X](f: (x: X) -> Int64, x: X) -> Int64 = f(x)`, with
//! `Desc` provided at `Leaf` (7) and `Pebble` (9), `app(useS, leaf)` loaded and stopped at run
//! time ("`__req_desc` not bound"), and `app(Sp.t, leaf)` was refused as an unsatisfiable
//! requirement (WI-420): the reference was typed against `(x: X) -> Int64` before `leaf` fixed
//! `X`, and its dictionary was built there. Now a reference whose slot holds a variable is held
//! (`HeldFunctionValue`), and the call — or the construction — whose argument it is gives it
//! its dictionaries once its σ is complete, at the slot as σ reads it; one no call fixes is
//! given them where the walk ends, at the slot it met, as before.
//!
//! Found beside it, each fixed with a row here: the sort's clause taken as a value read the
//! sort half of the caller's chain alone, so a caller's own `requires Desc[T = Q]` did not
//! answer `app(Sp.t, y)` where it answers `Sp.t(y)`; and `Sp.t` written in a construction's
//! field took no arrow from the field (`some(Sp.t)`, `boxed(f: Sp.t, …)`), being an
//! application with no arguments rather than a bare name.
//!
//! ## Back-outs, one at a time
//!
//! Measured by temporary switches over all of `wi_tests` (9,213 rows, before the list and
//! tuple row was added; that row and the descent were measured over this file, and the open
//! slot's row, added by review, is not in these counts). Each fails
//! rows of this file only, except (6), which fails as well the two rows elsewhere this change
//! rewrote:
//!
//! 1. **The reference attached where it is typed** (no hold): 8 — every row but the twins and
//!    the forwarding row; `app(useS, stone)` loads, as on the parent.
//! 2. **No completion at a call**: 7 — the construction row, which its construction
//!    completes, and the forwarding row, which the walk's end answers, pass.
//! 3. **No completion at a construction**: 1 — `a_construction_fixes_its_field`.
//! 4. **A slot still open at a construction attached there** (no re-hold): 1 —
//!    `a_value_in_a_construction_takes_the_instance_its_call_fixes`.
//! 5. **A variable test that reads a bare sort parameter as no variable** (`collect_vars`): 1 —
//!    `a_callee_sort_parameter_slot_is_read_at_the_call`.
//! 6. **The value's sort half read off the caller's sort clauses alone**
//!    (`enclosing_dict_chain`): 3 — `a_callers_own_requires_answers_a_sort_clause_value`,
//!    `wi_wn9p8 an_operations_own_slot_reaches_an_eta` and `wi_80zv8
//!    a_sibling_passed_as_a_function_value_is_placed_by_its_arrow`, the two rows that pinned
//!    the old reading as the function-value route's limit.
//! 7. **`Sp.t` in a field read as no operation name**: 2 — the two construction rows.
//! 8. **A call's argument not read through its constructions**: 2 — the option row and the
//!    list and tuple row.
//!
//! Pass under every back-out, by design: `the_twins_are_unchanged`.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// `Desc` provided at `Leaf` (7) and `Pebble` (9), `Stone` providing nothing, the operation's
/// clause `useS` and the sort's clause `Sp.t`, and `app`, beside `decls`.
fn program(ns: &str, decls: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.{{Int64, Option}}
  import anthill.prelude.Option.{{some, none}}
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
  sort Pebble
    entity pebble
    provides Desc[T = Pebble]
    operation describe(x: Pebble) -> Int64 = 9
  end
  sort Stone
    entity stone
  end
  sort Sp
    sort P = ?
    requires Desc[T = P]
    operation t(x: P) -> Int64 = Desc.describe(x)
  end
  operation useS[P](x: P) -> Int64 requires Desc[T = P] = Desc.describe(x)
  operation app[X](f: (x: X) -> Int64, x: X) -> Int64 = f(x)
{decls}
end
"#
    )
}

#[track_caller]
fn runs_to(ns: &str, decls: &str, entry: &str, want: i64) {
    let src = program(ns, decls);
    assert_eq!(run_int64(&src, &format!("{ns}.{entry}")), Ok(want), "`{entry}`");
}

/// 073 §5.4's own program, and its twin at the other carrier.
#[test]
fn an_operation_clause_value_takes_the_instance_its_call_fixes() {
    let decls = "  operation main() -> Int64 = app(useS, leaf)\n  operation other() -> Int64 = app(useS, pebble)";
    runs_to("t.pbsem.op", decls, "main", 7);
    runs_to("t.pbsem.op", decls, "other", 9);
}

#[test]
fn a_sort_clause_value_takes_the_instance_its_call_fixes() {
    let decls = "  operation main() -> Int64 = app(Sp.t, leaf)\n  operation other() -> Int64 = app(Sp.t, pebble)";
    runs_to("t.pbsem.sort", decls, "main", 7);
    runs_to("t.pbsem.sort", decls, "other", 9);
}

/// Named arguments, the value after the argument that fixes it, and two references to one
/// operation at two carriers in one body, each held apart.
#[test]
fn every_argument_order_reads_the_one_instance() {
    let decls = r#"  operation app2[X](x: X, f: (x: X) -> Int64) -> Int64 = f(x)
  operation named() -> Int64 = app(x: leaf, f: useS) + app(f: Sp.t, x: pebble)
  operation rev() -> Int64 = app2(pebble, useS) + app2(leaf, Sp.t)
  operation two() -> Int64 = app(useS, leaf) + app(useS, pebble) + app(Sp.t, pebble)"#;
    runs_to("t.pbsem.order", decls, "named", 16);
    runs_to("t.pbsem.order", decls, "rev", 16);
    runs_to("t.pbsem.order", decls, "two", 25);
}

/// A slot typed by the callee's SORT parameter, written as a bare head (`X`), is a variable the
/// call fixes as an operation's own parameter is.
#[test]
fn a_callee_sort_parameter_slot_is_read_at_the_call() {
    let decls = r#"  sort Run
    sort X = ?
    operation go(f: (x: X) -> Int64, x: X) -> Int64 = f(x)
  end
  operation main() -> Int64 = Run.go(useS, pebble) + Run.go(Sp.t, leaf)"#;
    runs_to("t.pbsem.sortparam", decls, "main", 16);
}

/// A value in a construction written as the argument: the construction fixes nothing of the
/// call's `X`, and the call does.
#[test]
fn a_value_in_a_construction_takes_the_instance_its_call_fixes() {
    let decls = r#"  operation appOpt[X](o: Option[T = (x: X) -> Int64], x: X) -> Int64 =
    match o
      case some(f) -> f(x)
      case none -> 0
  operation main() -> Int64 = appOpt(some(useS), leaf) + appOpt(some(Sp.t), pebble)"#;
    runs_to("t.pbsem.nested", decls, "main", 16);
}

/// A list's and a tuple's element, which are constructions too.
#[test]
fn a_value_in_a_list_or_a_tuple_takes_the_instance_its_call_fixes() {
    let decls = r#"  import anthill.prelude.List
  import anthill.prelude.List.{cons, nil}
  operation appAll[X](fs: List[T = (x: X) -> Int64], x: X) -> Int64 =
    match fs
      case cons(f, rest) -> f(x) + appAll(rest, x)
      case nil -> 0
  operation appT[X](p: (f: (x: X) -> Int64, v: X)) -> Int64 = match p case (f, v) -> f(v)
  operation lists() -> Int64 = appAll([useS], pebble) + appAll([Sp.t], leaf)
  operation tuples() -> Int64 = appT((f: useS, v: pebble)) + appT((f: Sp.t, v: leaf))"#;
    runs_to("t.pbsem.lit", decls, "lists", 16);
    runs_to("t.pbsem.lit", decls, "tuples", 16);
}

/// A construction whose sibling field fixes the carrier of a function value in another.
#[test]
fn a_construction_fixes_its_field() {
    let decls = r#"  sort Boxed
    sort X = ?
    entity boxed(f: (x: X) -> Int64, v: X)
  end
  operation run(b: Boxed) -> Int64 = match b case boxed(f, v) -> f(v)
  operation main() -> Int64 = run(boxed(f: useS, v: leaf)) + run(boxed(f: Sp.t, v: pebble))"#;
    runs_to("t.pbsem.ctor", decls, "main", 16);
}

/// At a carrier no provision answers the value is refused at load, as the direct call is.
#[test]
fn a_carrier_no_provision_answers_is_refused_as_the_direct_call_is() {
    let direct = load_errors_of(&program("t.pbsem.rock", "  operation main() -> Int64 = useS(stone)"));
    assert_refused_naming(&direct, &["Desc[T = t.pbsem.rock.Stone]", "provides no"], "the direct call");
    let value = load_errors_of(&program("t.pbsem.rock", "  operation main() -> Int64 = app(useS, stone)"));
    assert_refused_naming(
        &value,
        &["Desc[T = t.pbsem.rock.Stone]", "used as a function value", "provides no"],
        "the operation's clause",
    );
    let sort = load_errors_of(&program("t.pbsem.rock", "  operation main() -> Int64 = app(Sp.t, stone)"));
    assert_refused_naming(&sort, &["Sp.t", "used as a function value"], "the sort's clause");
}

/// Found beside it: the sort's clause taken as a value at the caller's own type parameter is
/// answered by the caller's `requires`, as the direct call `Sp.t(y)` is — the value read the
/// sort half of the caller's chain alone, and was refused (WI-420) at an argument and at a `let`
/// annotated at `Q`. Without the `requires` both spellings are refused.
#[test]
fn a_callers_own_requires_answers_a_sort_clause_value() {
    let decls = r#"  operation fwd[Q](y: Q) -> Int64 requires Desc[T = Q] = app(Sp.t, y)
  operation fwdLet[Q](y: Q) -> Int64 requires Desc[T = Q] =
    let f: (x: Q) -> Int64 = Sp.t
    f(y)
  operation main() -> Int64 = fwd(pebble) + fwd(leaf) + fwdLet(pebble)"#;
    runs_to("t.pbsem.fwd", decls, "main", 25);
    let direct = load_errors_of(&program("t.pbsem.fwdno", "  operation fwd[Q](y: Q) -> Int64 = Sp.t(y)"));
    assert_refused_naming(&direct, &["Sp.t", "cannot be supplied"], "the direct call");
    let value = load_errors_of(&program("t.pbsem.fwdno", "  operation fwd[Q](y: Q) -> Int64 = app(Sp.t, y)"));
    assert_refused_naming(&value, &["Sp.t", "used as a function value"], "the value");
}

/// A slot no argument fixes is refused at the call, naming the parameter, for both clause
/// kinds — `app0(useS)` was refused so before, and `app0(Sp.t)` as an unsatisfiable requirement
/// at the reference (WI-420). A slot whose variable is only in its row (`@ {EffP}`) fixes the
/// instance where the value is written.
#[test]
fn a_slot_no_argument_fixes_is_refused_at_the_call() {
    for (ns, value) in [("t.pbsem.open", "useS"), ("t.pbsem.open2", "Sp.t")] {
        let decls = format!(
            "  operation app0[X](f: (x: X) -> Int64) -> Int64 = 0\n  operation main() -> Int64 = app0({value})"
        );
        let errs = load_errors_of(&program(ns, &decls));
        assert_refused_naming(&errs, &["app0.type_arg", "expected a type for 'X'"], value);
    }
    let row = r#"  operation applyRow[EffP](f: (x: Leaf) -> Int64 @ {EffP}) -> Int64 effects {EffP} = f(leaf)
  operation main() -> Int64 = applyRow(useS) + applyRow(Sp.t)"#;
    runs_to("t.pbsem.row", row, "main", 14);
}

/// The twins the ticket measured running: the direct calls, the annotated lambdas, and a slot
/// that fixes the carrier where the value is written. Pass with or without the change.
#[test]
fn the_twins_are_unchanged() {
    let decls = r#"  operation applyLeaf(f: (x: Leaf) -> Int64) -> Int64 = f(leaf)
  operation direct() -> Int64 = useS(leaf) + Sp.t(leaf)
  operation lam() -> Int64 = app(lambda (x: Leaf) -> useS(x), leaf) + app(lambda (x: Leaf) -> Sp.t(x), leaf)
  operation slot() -> Int64 = applyLeaf(useS) + applyLeaf(Sp.t)"#;
    runs_to("t.pbsem.twins", decls, "direct", 14);
    runs_to("t.pbsem.twins", decls, "lam", 14);
    runs_to("t.pbsem.twins", decls, "slot", 14);
}

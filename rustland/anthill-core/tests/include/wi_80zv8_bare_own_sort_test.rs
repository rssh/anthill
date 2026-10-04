//! WI-20261001-80ZV8 — A BARE REFERENCE TO THE ENCLOSING SORT IS THE SORT AT `?`, AND A
//! SORT'S PARAMETER NEEDS A CARRIER (proposal 070 §1.3, §1.4; user, 2026-10-04).
//!
//! Inside `sort Cell`, `Cell` is `Cell[V = ?]`: any cell, as everywhere else — "it should be
//! the same as `Cell[V = ?]`". For one day it was a load error instead ("inside its own
//! definition a sort is written in full"), which is how the forgotten `Self`s of the stdlib
//! and of these fixtures were found; the error is gone, and what was wrong with the
//! spelling it guarded is refused where it is wrong:
//!
//! ```anthill
//! operation get(c: Cell) -> V          -- refused: `V` has no carrier
//! operation get(c: Self) -> V          -- `c` is the carrier
//! operation get(c: Cell) -> c.V        -- that cell's `V`, by projection
//! ```
//!
//! `c: Cell` is any cell, so the `V` beside it is not its `V` — it is the operation's type
//! parameter, which the caller's expected type would choose (`asString(c: Cell[V = Int64])
//! -> String = Cell.get(c)` loaded, MEASURED). The signature uses `V`, takes a `Cell` that
//! is not the carrier, and has no carrier: "projection without carrier".
//!
//! Each row RUNS or names its refusal.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! TO BE MEASURED BEFORE THIS IS COMMITTED, and not yet: the rule changed four times on
//! 2026-10-04 and the measurement taken that morning was of the load error this file no
//! longer tests. The parts, each to be disabled in turn on a temporary binary:
//!
//! 1. the loader's `?` in a slot the enclosing sort's reference leaves out
//!    (`Loader::own_sort_slots_left_out` answering none);
//! 2. an effect label's own name left alone (`effect_label_head` never set);
//! 3. a companion receiver's own bracket left alone (`call_receiver_head` never set);
//! 4. an alias followed (`alias_expansion` not asked);
//! 5. `Self` read in an applied rule-head bound, and 6. a parameter of the sort named
//!    there read as its variable (`Loader::convert_term_inner`, each arm off);
//! 7. a parameter with no variable not filled;
//! 8. the carrier check (`check_sort_parameter_carriers` not run; run but honouring no
//!    carrier; run but reading a use off variables only);
//! 9. a `let` annotation's `?` taking its value's type (typing/build.rs).

use crate::common::{
    assert_refused_naming, load_errors_of as load_errors, load_kb_with, run_int64 as run_src,
    shown_rows,
};

// ── The bare name is the sort at `?` ────────────────────────────────────────

/// `Box`, its own name written bare in every position a type is written in, and `go`.
fn bare_program(ns: &str, second: &str, go: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Bool}}
  sort Rel
    sort A = ?
    operation weigh(r: Self) -> Int64
  end
  sort Box
    sort T = ?
    entity box(v: T)
    entity node(next: Box)
    provides Rel[A = Box]
    operation weigh(r: Self) -> Int64 = 42
    operation both(a: Self, b: {second}) -> Int64 = 5
    operation some(s: Self) -> Box = box(v: "s")
    operation keep(s: Self) -> Self =
      let t: Box = s
      t
  end
  namespace Box
    operation more(b: Box) -> Int64 = 1
  end
  operation takes_int(b: Box[T = Int64]) -> Int64 = 1
  operation takes_any[A](b: Box[T = A]) -> Int64 = 1
  operation use(r: Rel[A = Box[T = String]]) -> Int64 = Rel.weigh(r)
  operation go() -> Int64 =
    let x: Box[T = Int64] = box(v: 1)
    {go}
end
"#
    )
}

/// EVERY POSITION, ONE PROGRAM, AND IT RUNS: a parameter takes a `Box` of another element
/// type; a field holds one; a `provides` binding provides at every `Box`; a return is a
/// `Box` the operation picks; an annotation takes its value's type; a secondary entry's
/// parameter is any `Box`. Under the tie each of these was this instance's; while the load
/// error stood none of them loaded.
#[test]
fn a_bare_reference_to_the_enclosing_sort_is_the_sort_at_a_wildcard() {
    let go = "Box.both(x, box(v: \"s\")) + takes_any(Box.some(x)) \
              + takes_int(Box.keep(node(next: box(v: true)))) + Box.more(box(v: 7)) + use(x) - 8";
    for (ns, second) in [("wi80zv8b.any1", "Box"), ("wi80zv8b.any2", "Box[T = ?]")] {
        assert_eq!(
            run_src(&bare_program(ns, second, go), &format!("{ns}.go")),
            Ok(42),
            "{second}"
        );
    }
}

/// …AND IT IS NOT THIS INSTANCE. CONTROLS, each the same program with one word changed:
/// `b: Self` holds the second argument to the receiver's element type, and the bare return
/// is no `Box` of `Int64` to a consumer that asks for one.
#[test]
fn a_bare_reference_to_the_enclosing_sort_is_not_this_instance() {
    let this = bare_program("wi80zv8b.this", "Self", "Box.both(x, box(v: \"s\"))");
    assert_refused_naming(
        &load_errors(&this),
        &["both.b (op-arg): expected Box[T = Int64], got Box[T = String]"],
        "a second instance where the parameter is `Self`",
    );
    let picked = bare_program("wi80zv8b.ret", "Box", "takes_int(Box.some(x))");
    assert_refused_naming(
        &load_errors(&picked),
        &["takes_int.b (op-arg): expected Box[T = Int64], got Box[T = ?T]"],
        "a bare return read as a `Box` of `Int64`",
    );
}

/// A PARTIAL reference leaves the rest to `?`, and an ALIAS of the sort is the sort it stands
/// for: `Pair[L = Int64]` takes any `R`; `sort MyPair = Pair` is any `Pair`; `sort IntPair =
/// Pair[L = Int64]` is a `Pair` of `Int64` and any `R` — and holds its argument to the `L` it
/// fixes.
#[test]
fn a_partial_reference_and_an_alias_leave_the_rest_to_a_wildcard() {
    let program = |ns: &str, go: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Bool}}
  sort Pair
    sort L = ?
    sort R = ?
    entity pair(l: L, r: R)
    operation left(p: Pair[L = Int64]) -> Int64 = 10
    operation al(s: Self, o: MyPair) -> Int64 = 10
    operation il(s: Self, o: IntPair) -> Int64 = 10
  end
  sort MyPair = Pair
  sort IntPair = Pair[L = Int64]
  operation go() -> Int64 = {go}
end
"#
        )
    };
    let runs = "Pair.left(pair(l: 1, r: \"s\")) + Pair.left(pair(l: 1, r: true)) \
                + Pair.al(pair(l: 1, r: 2), pair(l: \"a\", r: true)) \
                + Pair.il(pair(l: 1, r: 2), pair(l: 3, r: \"s\")) + 2";
    assert_eq!(run_src(&program("wi80zv8b.part", runs), "wi80zv8b.part.go"), Ok(42));
    assert_refused_naming(
        &load_errors(&program(
            "wi80zv8b.fixed",
            "Pair.il(pair(l: 1, r: 2), pair(l: \"x\", r: 1))",
        )),
        &["il.o (op-arg): expected Pair[L = Int64", "got Pair[L = String"],
        "an argument against the slot the alias fixes",
    );
}

// ── What is not a reference to the sort ─────────────────────────────────────

/// AN EFFECT LABEL is compared by identity, not expanded (kernel-language.md §8.1), so a
/// label naming the enclosing sort is not a reference to it and takes no `?` — in an
/// `effects` clause and in an arrow's row alike. With the `?` written into it the label is
/// another label, and the declared row no longer names the registered effect.
#[test]
fn an_effect_label_naming_the_enclosing_sort_is_not_a_reference_to_it() {
    let src = r#"
namespace wi80zv8b.label
  import anthill.prelude.{Int64, Effect}
  sort Fx
    sort T = ?
    provides Effect[T = Fx[?]]
    operation run(x: T) -> T effects Fx
    operation each(f: (x: T) -> T @ {Fx}) -> Int64 = 1
  end
end
"#;
    assert_eq!(load_errors(src), Vec::<String>::new());
}

/// A COMPANION RECEIVER'S BRACKET IS A CALL'S BRACKET — `Box[T = T].keep(b)` is `Box.keep[T
/// = T](b)` in its other spelling — and what it leaves out the call's arguments fix (§1.1).
/// Both spellings run.
#[test]
fn a_companion_receivers_own_bracket_is_a_calls_bracket() {
    let program = |call: &str| {
        format!(
            r#"
namespace wi80zv8b.recv
  import anthill.prelude.{{Int64, Option}}
  sort Box
    sort T = ?
    sort U = ?
    entity box(v: T)
    operation keep(b: Self) -> Self = b
    operation via(b: Self) -> Int64 =
      {call}
  end
  operation go() -> Int64 = Box.via(box(v: 7))
end
"#
        )
    };
    for call in [
        "match Box[T = T].keep(b) case box(_) -> 1",
        "match Box.keep[T = T](b) case box(_) -> 1",
    ] {
        assert_eq!(run_src(&program(call), "wi80zv8b.recv.go"), Ok(1), "{call}");
    }
}

// ── A rule head's applied bound ─────────────────────────────────────────────

/// A RULE HEAD'S APPLIED BOUND IS A TERM, converted as one — and it reads `Self`, and the
/// sort's own parameters, as a type door does; a bare reference to the sort in it is any
/// instance, as a bare sort in a bound always was. `Self` there was refused ("It means
/// nothing here; write the sort's name"), and `Box[T = T]` there loaded clean and answered
/// NOTHING, its `T` a reference to the parameter's symbol (MEASURED; the second predates the
/// proposal). The `?x: T` form of the same bounds, lowered by the type door, always answered.
#[test]
fn a_bound_that_is_a_term_reads_self_and_the_sorts_parameters() {
    let program = |ns: &str, bound: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, Option}}
  import anthill.prelude.Option.{{some}}
  sort Box
    sort T = ?
    entity box(v: T)
    rule twin(x: {bound}, y: {bound}) :- y = x
  end
  rule both(1) :- Box.twin(some(box(v: 1)), some(box(v: 1)))
end
"#
        )
    };
    for (ns, bound) in [
        ("wi80zv8b.term1", "Option[T = Self]"),
        ("wi80zv8b.term2", "Option[T = Box[T = T]]"),
        ("wi80zv8b.term3", "Option[T = Box[T = ?]]"),
        ("wi80zv8b.term4", "Option[T = Box]"),
    ] {
        let mut kb = load_kb_with(&program(ns, bound));
        assert_eq!(
            shown_rows(&mut kb, &format!("{ns}.both")),
            vec![("1".to_owned(), true)],
            "{bound}"
        );
    }
}

// ── A sort's parameter needs a carrier ──────────────────────────────────────

/// `Cell`, with `ops` as its operations, and a driver over a cell of `Int64`.
fn cell_program(ns: &str, ops: &str, go: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Bool, List}}
  sort Zero
    sort T = ?
    operation zero() -> T
    operation same(a: T, b: T) -> Bool
  end
  sort Cell
    sort V = ?
    entity cell(v: V)
    {ops}
  end
  operation go() -> Int64 =
    let c: Cell[V = Int64] = cell(v: 42)
    {go}
end
"#
    )
}

/// `V` BESIDE A `Cell` THAT IS NOT THE CARRIER IS REFUSED AT THE DEFINITION: `get(c: Cell)
/// -> V` takes any cell and returns the operation's own `V`, which every reader takes for
/// that cell's. Bare or written `?`, in the return or in another parameter, at the top of a
/// parameter's type or inside it — and with no body to notice. It loaded, and
/// `asString(c: Cell[V = Int64]) -> String = Cell.get(c)` read an `Int64` cell as a `String`
/// (MEASURED).
#[test]
fn a_sort_parameter_used_beside_the_sort_needs_a_carrier() {
    let top = [
        "expected a carrier for `V` — a parameter typed `Self`",
        "`V` used with no carrier: `c` is any `Cell`",
        "Type `c` as `Self` to make it the carrier, or write `c.V`",
    ];
    for (ns, op) in [
        ("wi80zv8b.c1", "operation get(c: Cell) -> V"),
        ("wi80zv8b.c2", "operation get(c: Cell[V = ?]) -> V"),
        ("wi80zv8b.c3", "operation get(c: Cell, x: V) -> Int64 = 1"),
    ] {
        let errors = load_errors(&cell_program(ns, op, "0"));
        assert_refused_naming(&errors, &top, op);
        assert_refused_naming(&errors, &[&format!("type mismatch in {ns}.Cell.get.c")], op);
    }
    assert_refused_naming(
        &load_errors(&cell_program(
            "wi80zv8b.c4",
            "operation total(xs: List[T = Cell]) -> V",
            "0",
        )),
        &[
            "`V` used with no carrier: `xs` holds any `Cell`",
            "Write that `Cell` as `Self` to make it the carrier",
        ],
        "a `Cell` nested in a parameter's type",
    );
}

/// THE TWO SPELLINGS THE REFUSAL OFFERS, each of which says whose `V`: `get(c: Self) -> V`
/// makes `c` the carrier, and `get(c: Cell) -> c.V` takes any cell and returns that cell's.
/// Both run, and both hold their result to the argument's `V`.
#[test]
fn self_makes_the_carrier_and_a_projection_names_the_parameters_own() {
    for (ns, op) in [
        ("wi80zv8b.r1", "operation get(c: Self) -> V = match c case cell(x) -> x"),
        ("wi80zv8b.r2", "operation get(c: Cell) -> c.V = match c case cell(x) -> x"),
    ] {
        assert_eq!(
            run_src(&cell_program(ns, op, "Cell.get(c)"), &format!("{ns}.go")),
            Ok(42),
            "{op}"
        );
        let ns = format!("{ns}s");
        let as_string = format!(
            "{op}\n  end\n  sort Other\n    entity other(n: Int64)\n    operation asString(c: \
             Cell[V = Int64]) -> String = Cell.get(c)"
        );
        assert_refused_naming(
            &load_errors(&cell_program(&ns, &as_string, "0")),
            &["asString.return (op-return): expected String, got Int64"],
            op,
        );
    }
}

/// WHAT THE CARRIER RULE LEAVES ALONE, each because one of its three conditions fails: an
/// operation that takes no value of its sort (a constructor, a nullary producer, a spec's
/// operations over its parameter); one that has its carrier beside another instance; one
/// that names the other instance's parameter itself; and one that does not use `V`. They
/// load and run.
#[test]
fn what_the_carrier_rule_leaves_alone_loads_and_runs() {
    let ops = "operation new(x: V) -> Self = cell(v: x)\n    \
               operation first(s: Self, o: Cell) -> V = match s case cell(x) -> x\n    \
               operation named[X](o: Cell[V = X]) -> Int64 = 1\n    \
               operation same(a: Cell, b: Cell) -> Int64 = 1";
    let go = "Cell.first(Cell.new(40), cell(v: \"s\")) + Cell.named(cell(v: true)) \
              + Cell.same(c, cell(v: \"s\"))";
    assert_eq!(
        run_src(&cell_program("wi80zv8b.alone", ops, go), "wi80zv8b.alone.go"),
        Ok(42)
    );
}

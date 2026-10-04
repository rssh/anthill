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
//! MEASURED (2026-10-04), each part present but disabled. Parts 5, 6, 8 and 9 were measured
//! again on the tree stage (e) of the proposal is committed with — a temporary binary of 52
//! suites and 1037 rows, `wi_80zv8_tie_removed_test`'s — and their lists are that
//! measurement's. Parts 1–4 and 7 are the LOADER's `?`, which stage (e) DELETED with the
//! readers it was written to keep a slot left out away from; they are kept as the record of
//! what it held (on a binary of 28 suites and 707 rows, the tree this file was first
//! committed with), and cannot be backed out any more.
//!
//! DELETED AT STAGE (e) — what the loader's `?` held while it stood:
//!
//! 1. THE LOADER'S `?` in a slot the enclosing sort's reference leaves out
//!    (`Loader::own_sort_slots_left_out` answering none). 6 FAILED:
//!    [`a_bare_reference_to_the_enclosing_sort_is_the_sort_at_a_wildcard`],
//!    [`a_partial_reference_and_an_alias_leave_the_rest_to_a_wildcard`],
//!    [`what_the_carrier_rule_leaves_alone_loads_and_runs`], and `wi1078
//!    a_self_sort_return_that_leaves_a_slot_open_is_opened_at_the_consumer`, `wi836
//!    the_bare_sort_ref_spelling_is_any_instance_and_its_result_is_opened`,
//!    `wi_0rp29_call_binding an_alias_of_the_carrier_in_a_binding_is_the_carrier`. The same
//!    six failed again at stage (e), on the committed tree with the fill switched off and
//!    the tie's readers still there — which is the measurement the deletion rests on
//!    (`wi_80zv8_tie_removed_test`, measurement 3).
//! 2. AN EFFECT LABEL'S OWN NAME LEFT ALONE (`effect_label_head` never set). 1 FAILED:
//!    [`an_effect_label_naming_the_enclosing_sort_is_not_a_reference_to_it`]. The first
//!    measurement failed NO row: the row declared its rows and incurred neither. It has
//!    bodies now.
//! 3. A COMPANION RECEIVER'S OWN BRACKET LEFT ALONE (`call_receiver_head` never set). 1
//!    FAILED: [`a_companion_receivers_own_bracket_is_a_calls_bracket`], on what its refusal
//!    prints — the one difference five programs found; the first measurement failed no row.
//! 4. AN ALIAS FOLLOWED (`alias_expansion` not asked). 2 FAILED:
//!    [`a_partial_reference_and_an_alias_leave_the_rest_to_a_wildcard`] and
//!    `wi_0rp29_call_binding an_alias_of_the_carrier_in_a_binding_is_the_carrier`.
//! 7. A PARAMETER WITH NO VARIABLE NOT FILLED. 1 FAILED: `wi1000
//!    a_dotted_declaration_name_is_not_the_entrys_content`, by a panic where it pins a
//!    refusal.
//!
//! STANDING:
//!
//! 5. `Self` READ IN AN APPLIED RULE-HEAD BOUND, and 6. A PARAMETER OF THE SORT NAMED THERE
//!    READ AS ITS VARIABLE (`Loader::convert_term_inner`, each arm off). 1 FAILS under each:
//!    [`a_bound_that_is_a_term_reads_self_and_the_sorts_parameters`].
//! 8. THE CARRIER CHECK (`check_sort_parameter_carriers`). Not run: 3 FAIL,
//!    [`a_sort_parameter_used_beside_the_sort_needs_a_carrier`],
//!    [`another_instance_on_purpose_names_its_own_parameter`] and `wi_80zv8_tie_removed
//!    a_sort_parameter_beside_an_alias_of_the_sort_needs_a_carrier`. Run but honouring no
//!    carrier: 9 FAIL, every signature that has its carrier beside another instance —
//!    [`a_bare_reference_to_the_enclosing_sort_is_the_sort_at_a_wildcard`],
//!    [`a_partial_reference_and_an_alias_leave_the_rest_to_a_wildcard`],
//!    [`what_the_carrier_rule_leaves_alone_loads_and_runs`], `wi_80zv8_written_wildcard`'s
//!    `a_parameter_at_a_wildcard_takes_any_instance` and
//!    `a_provision_at_a_wildcard_is_provided_at_every_instance`, `wi_0rp29_call_binding
//!    a_projection_of_the_bound_parameter_is_an_instance_of_its_own`, `wi_0rp29_member_rule
//!    a_witness_member_receiver_typed_by_the_spec_reads_the_provisions_bindings`,
//!    `wi_0rp29_nested_projection_value_in_type
//!    the_fallbacks_callback_row_takes_a_field_paths_head`, and the `wi_80zv8_tie_removed`
//!    row. Run but reading a use off variables only, not a stored reference to the
//!    parameter: 3 FAIL, the three of "not run". Run but reading a parameter's type as
//!    written, an alias unread: 1 FAILS, the `wi_80zv8_tie_removed` row — and with it
//!    [`a_partial_reference_and_an_alias_leave_the_rest_to_a_wildcard`] drops out of the
//!    "no carrier" nine, which is how the alias reading was found missing once the loader
//!    no longer followed the alias for it.
//! 9. A `let` ANNOTATION'S `?` TAKES ITS VALUE'S TYPE (typing/build.rs). 1 FAILS:
//!    [`a_bare_reference_to_the_enclosing_sort_is_the_sort_at_a_wildcard`], by its spelling
//!    that WRITES the `?` (`let t: Box[T = ?] = s` in `keep`). The bare spelling beside it
//!    is a slot left out, which the annotation rewrite of WI-374 gives the value's type —
//!    since stage (e) the two are one type by two routes, and the row runs both.
//!
//! While the loader wrote the `?`, a bare name WAS a written `?`, and rows of this file
//! failed under `wi_80zv8_written_wildcard_test`'s parts 1, 2 and 8 with that file's own.
//! They no longer do: its part 1 was the tie and is deleted, and re-measured at stage (e)
//! its parts 2 and 8 fail no row of this file — a bare name's slot is left out, not written.
//! [`a_bare_reference_to_the_enclosing_sort_is_not_this_instance`] and
//! [`self_makes_the_carrier_and_a_projection_names_the_parameters_own`], which failed under
//! that part 1 alone — the tie taken for a written `?` — fail under no part re-measured, and
//! passed in `wi_80zv8_tie_removed_test`'s measurement 3 too: nothing left on this tree
//! turns them round. They stay for the verdicts they name.

use crate::common::{
    assert_refused_naming, load_errors_of as load_errors, load_kb_with, run_int64 as run_src,
    shown_rows,
};

// ── The bare name is the sort at `?` ────────────────────────────────────────

/// `Box`, its own name written bare in every position a type is written in, and `go`.
/// `second` is how the second parameter of `both` and the annotation in `keep` are spelt.
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
      let t: {second} = s
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
/// error stood none of them loaded. Run twice — the parameter and the annotation left bare,
/// and written `Box[T = ?]`: one type, by two routes since stage (e) (a slot left out and a
/// written variable), which is why the second spelling is here.
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

/// A PARTIAL reference leaves the rest open, and an ALIAS of the sort is the sort it stands
/// for: `Pair[L = Int64]` takes any `R`; `sort MyPair = Pair` is any `Pair`; `sort IntPair =
/// Pair[L = Int64]` is a `Pair` of `Int64` and any `R` — and holds its argument to the `L` it
/// fixes. The refusal prints the alias by its name, as it does outside the sort (while the
/// loader wrote the `?` into such a reference it printed the expansion, `Pair[L = Int64, R =
/// ?_]`).
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
        &["il.o (op-arg): expected IntPair, got Pair[L = String"],
        "an argument against the slot the alias fixes",
    );
}

// ── What is not a reference to the sort ─────────────────────────────────────

/// AN EFFECT LABEL is compared by identity, not expanded (kernel-language.md §8.1), so a
/// label naming the enclosing sort is a label like any other — in an `effects` clause and
/// in an arrow's row alike: `twice` incurs `run`'s `Fx` under a declared `Fx`, and `each`
/// the same through the callback's row.
///
/// WHAT IT GUARDED, while the loader wrote a `?` into every slot the enclosing sort's name
/// left out (stage (d)): with the `?` written into a label each mention was a label of its
/// own — `twice` incurred `run`'s `Fx[T = ?]` under a declared `Fx[T = ?]` that is another
/// variable, and was refused its own declared row, `expected declared: [Fx[T = ?_]], got
/// undeclared effect: Fx[T = ?_]` (MEASURED then; a flag kept the label out of the fill).
/// The fill is deleted (stage (e)) and the flag with it; the row stays for the verdict.
///
/// The bodies are what drive it: as first written this row declared the two rows and
/// incurred neither.
#[test]
fn an_effect_label_naming_the_enclosing_sort_is_not_a_reference_to_it() {
    let src = r#"
namespace wi80zv8b.label
  import anthill.prelude.{Int64, Effect}
  sort Fx
    sort T = ?
    provides Effect[T = Fx[?]]
    operation run(x: T) -> T effects Fx
    operation twice(x: T) -> T effects Fx = Fx.run(Fx.run(x))
    operation each(f: (x: T) -> T @ {Fx}, x: T) -> T effects Fx = f(x)
  end
end
"#;
    assert_eq!(load_errors(src), Vec::<String>::new());
}

/// A COMPANION RECEIVER'S BRACKET IS A CALL'S BRACKET — `Box[T = T].keep(b)` is `Box.keep[T
/// = T](b)` in its other spelling — and what it leaves out the call's arguments fix (§1.1).
/// Both spellings run.
///
/// WHAT THE CALL DOES NOT FIX EITHER IS LEFT OUT OF ITS RESULT, in both spellings alike:
/// `Box[T = String].fresh()` where an `Int64` is wanted is `got Box[T = String]`. While the
/// loader wrote a `?` into every slot the enclosing sort's name left out (stage (d)) a
/// flag kept the receiver's bracket out of that fill: with the `?` written into it the
/// refusal was `got Box[T = String, U = ?_]` there and `got Box[T = String]` for the
/// callee's bracket (MEASURED then) — the one difference found, a bracket's own `?`
/// reading as unfixed everywhere else. The fill is deleted (stage (e)) and the flag with
/// it; the row stays for the verdict.
#[test]
fn a_companion_receivers_own_bracket_is_a_calls_bracket() {
    let program = |call: &str| {
        format!(
            r#"
namespace wi80zv8b.recv
  import anthill.prelude.{{Int64, String, Option}}
  sort Box
    sort T = ?
    sort U = ?
    entity box(v: T)
    operation keep(b: Self) -> Self = b
    operation fresh() -> Self
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
    for call in ["Box[T = String].fresh()", "Box.fresh[T = String]()"] {
        let errors = load_errors(&program(call));
        assert_refused_naming(&errors, &["expected Int64, got Box[T = String]"], call);
        assert!(
            !errors.join(" | ").contains("U ="),
            "{call}: a slot the bracket leaves out is not in the result, got: {errors:?}"
        );
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
        "give its `V` a name of its own (`[X]`, `c: Cell[V = X]`)",
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
            "give its `V` a name of its own (`[X]`, `Cell[V = X]`)",
        ],
        "a `Cell` nested in a parameter's type",
    );
}

/// … AND THE THIRD THING THE REFUSAL OFFERS, for the signature the first two would change
/// the meaning of: `withValue(c: Cell, v: V) -> Self` takes ANOTHER cell on purpose and
/// returns one of this instance. It is refused as the rest are — `V` is used and `c` is no
/// carrier — and neither `c: Self` nor `c.V` is what its author meant; naming the other
/// cell's parameter is, and that spelling loads and runs: a cell of `String` handed in, a
/// cell of `Int64` out, 5 + 37. The advice was not offered before /code-review asked what
/// the refusal says to this author.
#[test]
fn another_instance_on_purpose_names_its_own_parameter() {
    assert_refused_naming(
        &load_errors(&cell_program(
            "wi80zv8b.w1",
            "operation withValue(c: Cell, v: V) -> Self = cell(v: v)",
            "0",
        )),
        &[
            "type mismatch in wi80zv8b.w1.Cell.withValue.c",
            "where `c` is another `Cell` on purpose, give its `V` a name of its own (`[X]`, `c: \
             Cell[V = X]`)",
        ],
        "another cell taken on purpose, its `V` left open",
    );
    assert_eq!(
        run_src(
            &cell_program(
                "wi80zv8b.w2",
                "operation withValue[X](c: Cell[V = X], v: V) -> Self = cell(v: v)",
                "match Cell.withValue(cell(v: \"s\"), 5)\n      case cell(n) -> n + 37",
            ),
            "wi80zv8b.w2.go"
        ),
        Ok(42)
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

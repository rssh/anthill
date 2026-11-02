//! WI-20260823-ZF3AK (proposal 055 umbrella A) — the umbrella's end-to-end acceptance.
//! Its four parts each pinned their own rows; this file holds the one clause no part
//! drove for a nominal type, and says where every other clause is pinned.
//!
//! THE CLAUSE DRIVEN HERE: "a generic `id` infers `Type`" — proposal 055 §2: "against a
//! generic `idT[T](x: T)` it infers `T = Type` exactly as `idT(5)` infers `T = Int64`".
//! `wi_rxt6s_dotted_sort_type_value_test` drives it for a sort named by a dotted path;
//! these rows drive it for a bare, an applied and a positional `Cell`, through an
//! unannotated `let` and inside a collection, and show the inferred `T` meeting a
//! destination as `Type`.
//!
//! WHERE THE OTHER CLAUSES ARE PINNED:
//! * `operation t() -> Type = Cell[Int64]` evaluates to the canonical type —
//!   `wi707_type_application_value_test::an_evaluated_type_is_the_written_one`;
//! * an unannotated `let` — `wi_wahb6_type_value_classification_test::an_unannotated_let_denotes_and_evaluates`;
//! * a collection of nominal types, driven — `wi_q0093_type_value_occurrence_matrix_test::list_set_and_tuple_elements_denote`;
//! * a `String` / `Bool` destination naming the denoted sort —
//!   `wi_q0093_…::a_string_or_bool_destination_names_the_denoted_sort` and
//!   `a_boolean_position_refuses_a_type_value_and_says_which_slot`;
//! * constructor, callee, head, binder, label, member-name and `TypeExpr` controls — the
//!   adjacent-role rows of `wi_q0093_…` and
//!   `wi_wahb6_…::an_eponymous_constructor_keeps_its_construction_reading`;
//! * the dot-receiver split — `wi_papx0_dot_receiver_split_test`, `wi_papx0_written_type_member_test`;
//! * the expectation no longer classifies — `wi_jm6zw_expectation_classifier_retired_test`;
//! * WI-206 / WI-707 / WI-708 / WI-709 / WI-710 — their own files.
//!
//! BACK-OUT, MEASURED: with both loader predicates forced `false` for this file's programs
//! (`bare_name_denotes_type`, and `build_load`'s `is_type_value` — WAHB6's back-out; the
//! stdlib's own bodies hold type values, so a switch over every load refuses the stdlib
//! first), `a_generic_identity_infers_type_for_every_face`,
//! `the_inferred_parameter_meets_a_destination_as_type`,
//! `an_unannotated_let_meets_a_destination_as_type` and
//! `a_bracket_on_the_callee_keeps_its_meaning` fail: each written sort reaches the typer
//! unrecorded and is refused as `UnclassifiedTypeValue` ("expected a type value recorded
//! where the sort is written"). `the_same_inference_without_a_type_value` passes either
//! way by design: it measures the inference with no type value in it.

use crate::common::{assert_applied_cell, assert_bare_cell, interp_for, list_heads, load_errors_of};

const SRC: &str = r#"
namespace test.zf3ak
  import anthill.prelude.{Cell, Int64, List, Type}

  operation idT[T](x: T) -> T = x

  operation bare() -> Type = idT(Cell)
  operation applied() -> Type = idT(Cell[V = Int64])
  operation positional() -> Type = idT(Cell[Int64])
  operation via_let() -> Type =
    let u = idT(Cell[Int64])
    u
  operation elems() -> List[T = Type] = [idT(Cell), idT(Cell[V = Int64])]
  operation typed_callee() -> Type = idT[T = Type](Cell[V = Int64])
end
"#;

/// `go` passes `body` to a `String` parameter or a `Bool` condition.
fn destination_program(i: usize, body: &str) -> String {
    format!(
        r#"
namespace test.zf3akneg{i}
  import anthill.prelude.{{Bool, Cell, Int64, String, Type}}
  operation idT[T](x: T) -> T = x
  operation sz(s: String) -> Int64 = 1
  operation go() -> Int64 = {body}
end
"#
    )
}

/// `idT` hands its argument back, so each row asserts the type term that arrived at the
/// callee and left it. The positional `Cell[Int64]` comes back keyed by `V`, as the named
/// one does.
#[test]
fn a_generic_identity_infers_type_for_every_face() {
    let mut interp = interp_for(SRC);
    for (op, applied) in [
        ("bare", false),
        ("applied", true),
        ("positional", true),
        ("via_let", true),
    ] {
        let v = interp
            .call(&format!("test.zf3ak.{op}"), &[])
            .unwrap_or_else(|e| panic!("{op}: {e:?}"));
        if applied {
            assert_applied_cell(interp.kb(), &v, op);
        } else {
            assert_bare_cell(interp.kb(), &v, op);
        }
    }
    let list = interp
        .call("test.zf3ak.elems", &[])
        .unwrap_or_else(|e| panic!("elems: {e:?}"));
    let elems = list_heads(&list);
    assert_eq!(elems.len(), 2, "two list elements, got {list:?}");
    assert_bare_cell(interp.kb(), &elems[0], "list element 0");
    assert_applied_cell(interp.kb(), &elems[1], "list element 1");
}

/// The inferred `T` is `Type`: the call's result meets a `String` or `Bool` destination as
/// `Type`, as `idT(5)`'s meets it as `Int64`. The message names no sort — the destination
/// sees the call's result, and a `Type` that a call returned denotes nothing at that
/// position (`denoted_type_value`'s rule).
#[test]
fn the_inferred_parameter_meets_a_destination_as_type() {
    for (i, (body, said)) in [
        ("sz(idT(Cell))", "sz.s (op-arg): expected String, got Type"),
        ("sz(idT(Cell[V = Int64]))", "sz.s (op-arg): expected String, got Type"),
        ("if idT(Cell) then 1 else 2", "if.condition (boolean-position): expected Bool, got Type"),
        (
            "if idT(Cell[V = Int64]) then 1 else 2",
            "if.condition (boolean-position): expected Bool, got Type",
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let errs = load_errors_of(&destination_program(i, body));
        assert!(
            errs.iter().any(|e| e.contains(said) && !e.contains("got Type (")),
            "`{body}`: expected `{said}`, got {errs:?}"
        );
    }
}

/// An unannotated `let` infers `Type` too: its name meets the `String` destination as
/// `Type`, bound to the written type or to `idT`'s result.
#[test]
fn an_unannotated_let_meets_a_destination_as_type() {
    for (i, body) in [
        "\n    let u = Cell[Int64]\n    sz(u)",
        "\n    let u = Cell\n    sz(u)",
        "\n    let u = idT(Cell[V = Int64])\n    sz(u)",
    ]
    .into_iter()
    .enumerate()
    {
        let errs = load_errors_of(&destination_program(20 + i, body));
        assert!(
            errs.iter()
                .any(|e| e.contains("sz.s (op-arg): expected String, got Type")),
            "`{body}`: {errs:?}"
        );
    }
}

/// CONTROL, passes either way: the same inference with no type value — `idT(5)` meets the
/// `String` destination as `Int64`, and `idT("s")` is the true call.
#[test]
fn the_same_inference_without_a_type_value() {
    let errs = load_errors_of(&destination_program(10, "sz(idT(5))"));
    assert!(
        errs.iter()
            .any(|e| e.contains("sz.s (op-arg): expected String, got Int64")),
        "`sz(idT(5))`: {errs:?}"
    );
    let errs = load_errors_of(&destination_program(11, r#"sz(idT("s"))"#));
    assert!(errs.is_empty(), "`sz(idT(\"s\"))` is the true call: {errs:?}");
}

/// A bracket on the callee binds the callee's parameter: `idT[T = Type](Cell[V = Int64])`
/// runs, and `idT[T = String](Cell)` is refused at the argument, naming the sort the
/// written argument denotes, bare and applied.
#[test]
fn a_bracket_on_the_callee_keeps_its_meaning() {
    let mut interp = interp_for(SRC);
    let v = interp
        .call("test.zf3ak.typed_callee", &[])
        .unwrap_or_else(|e| panic!("typed_callee: {e:?}"));
    assert_applied_cell(interp.kb(), &v, "typed_callee");

    for (i, (arg, said)) in [
        ("Cell", "idT.x (op-arg): expected String, got Type (Cell)"),
        (
            "Cell[V = Int64]",
            "idT.x (op-arg): expected String, got Type (Cell[V = Int64])",
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let errs = load_errors_of(&format!(
            r#"
namespace test.zf3akcallee{i}
  import anthill.prelude.{{Cell, Int64, String}}
  operation idT[T](x: T) -> T = x
  operation go() -> String = idT[T = String]({arg})
end
"#
        ));
        assert!(
            errs.iter().any(|e| e.contains(said)),
            "the bracket fixes `T`, so `{arg}` is checked at `String`: {errs:?}"
        );
    }
}

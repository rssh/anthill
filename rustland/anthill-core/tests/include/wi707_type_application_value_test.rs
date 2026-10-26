//! WI-707 — a PARAMETERIZED type expression used as a VALUE argument:
//! `is_modifiable(Cell[V = Int64])`, `facts_of(kb(), List[T = Int64])`.
//!
//! Before this, a `Type`-declared parameter accepted only a BARE reference — a
//! free-standing entity (`facts_of(kb(), WorkItem)`) or, since WI-206, a bare sort
//! (`is_modifiable(Cell)`). The parser already produced the right shape for the
//! parameterized form (`Cell[V = Int64]` → `Fn{Cell, V: Ref(Int64)}`), but the
//! loader lowered it to an `Expr::Apply` whose arguments were typed as VALUE
//! expressions, so the inner `Int64` died as `UnresolvedName`. The gap was shared by
//! every `Type`-taking reflect op.
//!
//! WI-707 made a SORT-headed application in a slot that expects a `Type` read as a
//! parameterized TYPE by having the typer hint each argument as a `Type`. That
//! expectation-directed reading is gone (WI-20260824-WAHB6 records the application as an
//! `Expr::TypeValue` where it is written, in an operation body; WI-20260824-JM6ZW in a
//! rule body, and retired the hint): the slot's `Type` now only VALIDATES the value. Eval
//! assembles the type term as before (`start_sort_type` / `finish_sort_type`). These rows
//! pass in both worlds — the answers did not move, the decision did.

use anthill_core::eval::Value;
use anthill_core::kb::term_view::views_structurally_equal;

use crate::common::{bare_sort_name, interp_for, try_load_kb_with, type_application};

/// The WI-206 acceptance line, now reachable FROM SOURCE: a parameterized instance
/// of a modifiable sort is modifiable, and a `List[T = Int64]` is not. The op answers
/// whether a `Modify` can fire on a place of the type — the typer's predicate since
/// 2026-10-16 (WI-20260823-TR8CF) — so the NESTED `Map[…, V = Cell[V = Int64]]` is
/// modifiable too: its argument holds cells. It answered false while the op read only
/// the head sort (`Map` carries no claim).
#[test]
fn parameterized_type_as_a_value_argument() {
    let src = r#"
namespace test.wi707
  import anthill.prelude.{Cell, Int64, String, Bool, List, Map}
  import anthill.reflect.{is_modifiable}

  operation cell_named() -> Bool = is_modifiable(Cell[V = Int64])
  operation cell_positional() -> Bool = is_modifiable(Cell[Int64])
  operation list_int() -> Bool = is_modifiable(List[T = Int64])
  -- A NESTED application: the `Type` hint must recurse into the arguments, or the
  -- inner `Cell[V = Int64]` would be typed as a value expression and fail.
  operation nested() -> Bool = is_modifiable(Map[K = String, V = Cell[V = Int64]])
end
"#;
    let mut interp = interp_for(src);

    for (op, want) in [
        ("cell_named", true),
        ("cell_positional", true),
        ("list_int", false),
        ("nested", true),
    ] {
        let got = interp
            .call(&format!("test.wi707.{op}"), &[])
            .unwrap_or_else(|e| panic!("{op}: {e:?}"));
        assert!(
            matches!(got, Value::Bool(b) if b == want),
            "{op}: expected {want} — a `Modify` fires on a place of a type that is, or \
             holds, a modifiable sort: `Cell`'s instances and a `Map` of cells do, a \
             `List` of `Int64` does not — got {got:?}"
        );
    }
}

/// The same surface on the other `Type`-taking reflect ops — the gap was never
/// specific to `is_modifiable`.
#[test]
fn other_type_taking_reflect_ops_accept_a_parameterized_type() {
    let src = r#"
namespace test.wi707b
  import anthill.prelude.{Int64, List}
  import anthill.reflect.{Term}
  import anthill.reflect.KB.{kb, facts_of}

  operation facts() -> List[T = Term] = facts_of(kb(), List[T = Int64])
end
"#;
    let mut interp = interp_for(src);
    interp
        .call("test.wi707b.facts", &[])
        .expect("facts_of with a parameterized type");
}

/// The assembled value is the type the loader builds for a type WRITTEN in type position
/// (`make_parameterized_type`): read through the view, whatever carries it, it has that
/// type's head, its keys and its arguments, so the two are one type. A hand-rolled
/// application would diverge on a binding's key (`V` read off the declaration) and on the
/// empty-bindings case, which a consumer reading only the head sort would not see.
///
/// The POSITIONAL spelling binds the sort's declared type params in order, so
/// `Cell[Int64]` is that same type too — the loader's rule.
#[test]
fn an_evaluated_type_is_the_written_one() {
    let src = r#"
namespace test.wi707c
  import anthill.prelude.{Cell, Int64, Type}

  operation named_form() -> Type = Cell[V = Int64]
  operation positional_form() -> Type = Cell[Int64]
end
"#;
    let mut interp = interp_for(src);
    let value_of = |interp: &mut anthill_core::eval::Interpreter, op: &str| {
        interp
            .call(&format!("test.wi707c.{op}"), &[])
            .unwrap_or_else(|e| panic!("{op}: {e:?}"))
    };
    let named_form = value_of(&mut interp, "named_form");
    let positional_form = value_of(&mut interp, "positional_form");
    assert!(
        views_structurally_equal(interp.kb(), &named_form, &positional_form),
        "`Cell[Int64]` must bind the declared type param `V`, making it the SAME type as \
         `Cell[V = Int64]` — the loader's rule for positionals: {named_form:?} vs \
         {positional_form:?}"
    );

    // Shape: the base sort is the functor, the binding is keyed by the type-param name.
    let Some((functor, named)) = type_application(interp.kb(), &named_form) else {
        panic!("expected a parameterized type, got {named_form:?}");
    };
    assert_eq!(interp.kb().local_name_of(functor), "Cell", "the base sort is the functor");
    assert_eq!(named.len(), 1, "one type argument");
    assert_eq!(interp.kb().local_name_of(named[0].0), "V", "keyed by the declared type-param name");
    assert_eq!(
        bare_sort_name(interp.kb(), &named[0].1).as_deref(),
        Some("Int64"),
        "the type argument is Int64"
    );

    // The type the CANONICAL builder makes — what the loader lowers a written type with.
    let canonical = {
        let kb = interp.kb_mut();
        let cell = kb.try_resolve_symbol("anthill.prelude.Cell").expect("Cell");
        let int64 = kb
            .try_resolve_symbol("anthill.prelude.Int64")
            .expect("Int64");
        let v = kb.intern("V");
        let base = kb.make_sort_ref(cell);
        let int_ref = kb.make_sort_ref(int64);
        Value::term(kb.make_parameterized_type(base, &[(v, int_ref)]))
    };
    assert!(
        views_structurally_equal(interp.kb(), &canonical, &named_form),
        "an evaluated `Cell[V = Int64]` must be the type the canonical builder (and so the \
         loader, for a written annotation) produces: {named_form:?}"
    );
}

/// A `Type`-declared entity FIELD takes a sort / sort application too — the
/// constructor slot reads a sort exactly as an operation parameter does. (Before
/// this, only the operation-parameter form worked, an asymmetry a reflection-driven
/// listing hits immediately.)
#[test]
fn a_type_declared_entity_field_accepts_a_sort() {
    let src = r#"
namespace test.wi707d
  import anthill.prelude.{Cell, Int64, Type}

  entity ResourceRow(t: Type, label: Int64)

  operation bare() -> ResourceRow = ResourceRow(t: Cell, label: 1)
  operation applied() -> ResourceRow = ResourceRow(t: Cell[V = Int64], label: 2)
end
"#;
    try_load_kb_with(src).unwrap_or_else(|errs| {
        panic!("a `Type`-declared field must accept a sort name / application: {errs:?}")
    });
}

/// A sort application in an ordinary value slot does not load. THE INVARIANT IS
/// UNCHANGED; what the rejection is MADE OF changed under proposal 055 §2
/// (WI-20260824-WAHB6) — see the peer row in `wi206_is_modifiable_test`.
///
/// The old wording is worth recording, because it is what the proposal cites as the
/// symptom: outside a `Type` slot no argument got the `Type` hint, so the INNER
/// argument `Int64` failed first as an unresolved name and the application itself was
/// never judged. The arguments are now classified rather than hinted, so the error
/// lands where the mistake is — at the destination.
#[test]
fn a_sort_application_in_a_non_type_slot_is_still_an_error() {
    let src = r#"
namespace test.wi707e
  import anthill.prelude.{Cell, Int64}

  operation stray() -> Int64 = Cell[V = Int64]
end
"#;
    let errs = match try_load_kb_with(src) {
        Err(errs) => errs,
        Ok(_) => panic!("a type application in an Int64 slot must not load"),
    };
    // BACK-OUT: without the classification this still fails, as an unresolved name on
    // the inner `Int64`, so `contains("got Type")` is the half that inverts and
    // `Err(..)` is the half that holds either way.
    assert!(
        errs.iter()
            .any(|e| e.contains("expected Int64") && e.contains("got Type")),
        "expected the ordinary destination mismatch proposal 055 §2 specifies \
         (`expected Int64, got Type`), got {errs:?}"
    );
}

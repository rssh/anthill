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
//! Now a SORT-headed application in a slot that expects a `Type` reads as a
//! parameterized TYPE: the typer hints each argument as a `Type` (which is what lets
//! a nested application recurse) and types the node as `Type`; eval assembles the
//! type term (`start_sort_type` / `finish_sort_type`).

use anthill_core::eval::Value;
use anthill_core::kb::term::Term;

use crate::common::{interp_for, try_load_kb_with};

/// The WI-206 acceptance line, now reachable FROM SOURCE: a parameterized instance
/// of a modifiable sort is modifiable (the op keys on the head sort), and a
/// parameterized instance of a non-modifiable sort is not.
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
        ("nested", false),
    ] {
        let got = interp
            .call(&format!("test.wi707.{op}"), &[])
            .unwrap_or_else(|e| panic!("{op}: {e:?}"));
        assert!(
            matches!(got, Value::Bool(b) if b == want),
            "{op}: expected {want} — only Cell has a `Modifiable[T = …]` fact, and a \
             parameterized instance answers as its base sort does — got {got:?}"
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
    interp.call("test.wi707b.facts", &[]).expect("facts_of with a parameterized type");
}

/// The assembled value is the SAME hash-consed type term the loader builds for a
/// type WRITTEN in type position — both go through `make_parameterized_type`. Pinned
/// by identity (`TermId`), not just shape: a hand-rolled `Term::Fn` would diverge on
/// named-arg canonical ORDER and on the empty-bindings case, and the divergence would
/// be invisible to any consumer that only reads the head sort.
///
/// The POSITIONAL spelling binds the sort's declared type params in order, so
/// `Cell[Int64]` is that same term too — the loader's rule.
#[test]
fn an_evaluated_type_is_the_same_term_as_a_written_one() {
    let src = r#"
namespace test.wi707c
  import anthill.prelude.{Cell, Int64, Type}

  operation named_form() -> Type = Cell[V = Int64]
  operation positional_form() -> Type = Cell[Int64]

  -- The SAME type, written in TYPE position: the loader lowers this annotation with
  -- the canonical builder, so the evaluated forms above must hash-cons to it.
  operation written(c: Cell[V = Int64]) -> Int64 = 0
end
"#;
    let mut interp = interp_for(src);

    let term_of = |interp: &mut anthill_core::eval::Interpreter, op: &str| {
        let v = interp.call(&format!("test.wi707c.{op}"), &[]).unwrap_or_else(|e| panic!("{op}: {e:?}"));
        match v {
            Value::Term { id, .. } => id,
            other => panic!("{op}: a type application must evaluate to a Term-carried type, got {other:?}"),
        }
    };
    let named_id = term_of(&mut interp, "named_form");
    let positional_id = term_of(&mut interp, "positional_form");

    assert_eq!(
        named_id, positional_id,
        "`Cell[Int64]` must bind the declared type param `V`, making it the SAME \
         hash-consed term as `Cell[V = Int64]` — the loader's rule for positionals"
    );

    // Shape: the base sort is the functor, the binding is keyed by the type-param name.
    let (functor, named) = match interp.kb().get_term(named_id).clone() {
        Term::Fn { functor, named_args, .. } => (functor, named_args),
        other => panic!("expected a parameterized `Fn` type term, got {other:?}"),
    };
    assert_eq!(interp.kb().resolve_sym(functor), "Cell", "the base sort is the functor");
    assert_eq!(named.len(), 1, "one type argument");
    assert_eq!(interp.kb().resolve_sym(named[0].0), "V", "keyed by the declared type-param name");
    match interp.kb().get_term(named[0].1).clone() {
        Term::Ref(s) | Term::Ident(s) => {
            assert_eq!(interp.kb().resolve_sym(s), "Int64", "the type argument is Int64")
        }
        other => panic!("expected the argument to be a sort reference, got {other:?}"),
    }

    // Identity against the CANONICAL builder — `make_parameterized_type` is what the
    // loader lowers a written type with, so an evaluated type must hash-cons to the
    // very same TermId. This is what a hand-rolled `Term::Fn` in eval would break
    // (diverging on named-arg canonical order, and on the empty-bindings case), and
    // the divergence is invisible to any consumer that only reads the head sort.
    let canonical = {
        let kb = interp.kb_mut();
        let cell = kb.try_resolve_symbol("anthill.prelude.Cell").expect("Cell");
        let int64 = kb.try_resolve_symbol("anthill.prelude.Int64").expect("Int64");
        let v = kb.intern("V");
        let base = kb.make_sort_ref(cell);
        let int_ref = kb.make_sort_ref(int64);
        kb.make_parameterized_type(base, &[(v, int_ref)])
    };
    assert_eq!(
        canonical, named_id,
        "an evaluated `Cell[V = Int64]` must be the SAME hash-consed term the canonical \
         builder (and so the loader, for a written annotation) produces"
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

/// The reading stays confined to slots that ASK for a `Type`: a sort application in
/// an ordinary value slot is still a loud error, not a silently-built type value.
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
    // The diagnostic names the inner type ARGUMENT (`Int64`), not the applied sort:
    // outside a `Type` slot the arguments get no `Type` hint, so each is typed as an
    // ordinary value expression and the first one fails before the application itself
    // is judged. Loud either way, which is the invariant under test — the wording is
    // the loader's existing bare-name diagnostic, not something this WI shapes.
    assert!(
        errs.iter().any(|e| e.contains("unresolved")),
        "expected a loud unresolved-name diagnostic, got {errs:?}"
    );
}

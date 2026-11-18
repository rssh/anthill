//! A polymorphic entry op reached from the host: `Driver` declares `requires
//! WorkItemStore[State]` with `State` open, and its body calls `WorkItemStore.lookup` through
//! the spec. The host call is typed as the same call in an operation body (proposal 074 §1.4):
//! the cell handed at `Cell[V = WIS]` fixes `State`, and `WorkItemStore[State = WIS]` is built
//! from `FileBasedWorkitemStore`'s provision, so the body reaches that impl's `lookup`. A cell
//! handed at no type leaves `State` open, and the call is refused where it is typed.
//!
//! WI-236 gave the host `call_with_requirements`, through which it handed the dictionary over
//! by hand; WI-20261113-S4D63 removed it, and these rows are its rows on the typed call.
//!
//! BACK-OUT: none to measure — the typed call is the only host entry. The refusal row is the
//! control of the two that run: the same call, the cell at no type.

use anthill_core::eval::{self, EvalError, HostValue, Interpreter, Value};
use anthill_core::kb::KnowledgeBase;

const WIS: &str = "anthill.todo.store.FileBasedWorkitemStore.WIS";

const POLY_DRIVER: &str = r#"
namespace test.wi236_poly
  import anthill.prelude.{Cell, Option, String}
  import anthill.stage0.{WorkItem}
  import anthill.todo.store.{WorkItemStore, FileBasedWorkitemStore, WIS}

  sort Driver
    sort State = ?
    requires WorkItemStore[State]

    operation drive(s: Cell[State], id: String) -> Option[T = WorkItem]
      effects Error
    =
      WorkItemStore.lookup(s, id)
  end
end
"#;

fn interp_with(driver: &str) -> Interpreter {
    let kb: KnowledgeBase = crate::common::expect_loaded(
        crate::common::load_anthill_todo_store_bundle(&[driver]).into_result(),
    );
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp);
    interp
}

/// A cell holding `wis(backend: FakeBackend())`. The backend is a stand-in entity: `lookup`
/// reads the KB's work items, not the backend, so an empty store answers `none()`.
///
/// THE CONSTRUCTOR ITSELF, resolved: a symbol interned from a name ending in `wis` is a second
/// symbol, which `lookup`'s `case wis(_)` does not match.
fn wis_cell(interp: &mut Interpreter) -> Value {
    let wis = interp
        .kb()
        .try_resolve_symbol(&format!("{WIS}.wis"))
        .expect("`WIS.wis` is loaded");
    let backend = interp.kb_mut().intern("backend");
    let fake = interp.kb_mut().intern("FakeBackend");
    let state = Value::Entity {
        functor: wis,
        pos: vec![].into(),
        named: vec![(
            backend,
            Value::Entity { functor: fake, pos: vec![].into(), named: vec![].into() },
        )]
        .into(),
    };
    Value::Cell(interp.alloc_cell(state))
}

/// The cell at `Cell[V = WIS]`.
fn typed_wis_cell(interp: &mut Interpreter) -> HostValue {
    let cell = wis_cell(interp);
    let at = crate::common::cell_type(interp.kb_mut(), WIS);
    HostValue::typed(cell, at)
}

fn is_none(interp: &Interpreter, v: &Value) -> bool {
    matches!(v, Value::Entity { functor, pos, named }
        if interp.kb().qualified_name_of(*functor) == "anthill.prelude.Option.none"
            && pos.is_empty() && named.is_empty())
}

/// The cell at `Cell[V = WIS]` fixes `State`; the body's `lookup` reaches
/// `FileBasedWorkitemStore`'s, which answers `none()` on the empty store.
#[test]
fn polymorphic_entry_op_runs_at_the_cells_type() {
    let mut interp = interp_with(POLY_DRIVER);
    let cell = typed_wis_cell(&mut interp);
    let got = interp
        .call("test.wi236_poly.Driver.drive", &[cell, Value::Str("WI-001".into()).into()])
        .map(|h| h.value);
    assert!(
        matches!(&got, Ok(v) if is_none(&interp, v)),
        "the impl's `lookup` answers none() on an empty store; got {got:?}"
    );
}

/// The control: the same call with the cell at no type leaves `State` open, so the
/// `WorkItemStore` it owes is at a type nothing fixes, and the call is refused before it runs.
#[test]
fn a_cell_at_no_type_is_refused() {
    let mut interp = interp_with(POLY_DRIVER);
    let cell = wis_cell(&mut interp);
    let got = interp.call(
        "test.wi236_poly.Driver.drive",
        &HostValue::all(&[cell, Value::Str("WI-001".into())]),
    );
    assert!(
        matches!(&got, Err(EvalError::HostCallRefused { detail, .. })
            if detail.contains("WorkItemStore")),
        "the `WorkItemStore` at an open `State` is refused at the call; got {got:?}"
    );
    assert_eq!(interp.activation_depth(), 0, "the refused call leaves no frame");
}

/// Mirrors the bundle's `main.anthill`: the entry op (`main`) calls a sibling (`cmd_inner`)
/// which calls the spec op. The requirement the entry was handed reaches the sibling's
/// dispatch: `none()` → 1.
const MULTI_OP_DRIVER: &str = r#"
namespace test.wi236_multi
  import anthill.prelude.{Cell, Option, String, Int64}
  import anthill.stage0.{WorkItem}
  import anthill.todo.store.{WorkItemStore, FileBasedWorkitemStore, WIS}
  import anthill.prelude.Option.{none, some}

  sort Driver
    sort State = ?
    requires WorkItemStore[State]

    operation main(s: Cell[State], id: String) -> Int64
      effects Error
    =
      cmd_inner(s, id)

    operation cmd_inner(s: Cell[State], id: String) -> Int64
      effects Error
    =
      match WorkItemStore.lookup(s, id)
        case none() -> 1
        case some(_) -> 0
  end
end
"#;

#[test]
fn nested_op_dispatches_spec_call_via_inherited_requires() {
    let mut interp = interp_with(MULTI_OP_DRIVER);
    let cell = typed_wis_cell(&mut interp);
    let got = interp
        .call("test.wi236_multi.Driver.main", &[cell, Value::Str("WI-001".into()).into()])
        .map(|h| h.value);
    assert!(matches!(got, Ok(Value::Int(1))), "`none()` → 1 through the sibling; got {got:?}");
}

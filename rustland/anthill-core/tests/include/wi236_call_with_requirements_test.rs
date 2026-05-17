//! Host API for seeding cross-sort requirement dictionaries at entry-op
//! call. Pins that `Interpreter::call_with_requirements` lets a Rust
//! caller supply a real impl-rooted dictionary so a polymorphic entry op
//! (parent sort with `requires WorkItemStore[State]`) actually reaches the
//! impl body — whereas the plain `Interpreter::call` seeds self-referential
//! placeholders and the cross-sort dispatch mis-resolves.


use anthill_core::eval::{self, EvalError, Interpreter, Value};
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;
use smallvec::SmallVec;

/// Polymorphic Driver: `sort State = ?; requires WorkItemStore[State]`
/// with one body-bearing op that calls `WorkItemStore.lookup` through
/// the spec. Loading-time dispatch can't pick an impl (S is open); the
/// real choice happens at call time when the host supplies a dictionary.
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

fn load_with_driver() -> KnowledgeBase {
    let mut files = crate::common::collect_stdlib_and_rust_bindings();
    files.push(crate::common::workspace_root().join("anthill-todo/domain.anthill"));
    files.push(crate::common::workspace_root().join("anthill-todo/store.anthill"));

    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(POLY_DRIVER).expect("parse driver"));
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver)
        .unwrap_or_else(|errs| {
            for e in &errs { eprintln!("{}", e); }
            panic!("load failed with {} errors", errs.len());
        });
    kb
}

/// Build a Value::Cell holding `wis(FakeBackend, 0)`. The backend is a
/// stand-in entity — these tests don't exercise retrieve (no
/// IndexedFileStore is registered), only the dispatch path that should
/// reach FileBasedWorkitemStore.lookup's body.
fn build_cell_wis(interp: &mut Interpreter) -> Value {
    let wis_sym = interp.kb_mut()
        .intern("anthill.todo.store.FileBasedWorkitemStore.wis");
    let backend_field = interp.kb_mut().intern("backend");
    let counter_field = interp.kb_mut().intern("id_counter");
    let fake_backend_sym = interp.kb_mut().intern("FakeBackend");
    let wis_value = Value::Entity {
        functor: wis_sym,
        pos: vec![],
        named: vec![
            (backend_field, Value::Entity {
                functor: fake_backend_sym,
                pos: vec![],
                named: vec![],
            }),
            (counter_field, Value::Int(1)),
        ],
    };
    let handle = interp.alloc_cell(wis_value);
    Value::Cell(handle)
}

#[test]
fn polymorphic_entry_op_runs_when_dict_supplied() {
    let kb = load_with_driver();
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp).expect("builtins");

    let cell = build_cell_wis(&mut interp);
    let id_arg = Value::Str("WI-001".to_string());

    // FileBasedWorkitemStore has no own `requires`, so the dictionary's
    // sub-dicts list is empty.
    let filebased = interp.kb_mut()
        .intern("anthill.todo.store.FileBasedWorkitemStore");
    let dict = interp.alloc_requirement(filebased, SmallVec::new());
    let mut requirements: SmallVec<[_; 2]> = SmallVec::new();
    requirements.push(dict);

    let result = interp.call_with_requirements(
        "test.wi236_poly.Driver.drive",
        &[cell, id_arg],
        requirements,
    );

    match result {
        Ok(v) => {
            // The op returns Option[Term]. With no actual store
            // registered for the backend's canonical key, retrieve
            // either fails or no-ops. Either way the call must have
            // reached past the dispatch boundary — that's the test.
            eprintln!("[wi236] OK: {v:?}");
        }
        Err(e) => {
            let msg = format!("{e:?}");
            eprintln!("[wi236] err: {msg}");
            assert!(
                !msg.contains("frame has only")
                    && !msg.contains("OperationBodyMissing")
                    && !msg.contains("unknown operation"),
                "call_with_requirements should have crossed the dispatch \
                 boundary into the impl body; got {msg}"
            );
        }
    }
}

#[test]
fn arity_mismatch_when_requirements_count_wrong() {
    let kb = load_with_driver();
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp).expect("builtins");

    let cell = build_cell_wis(&mut interp);
    let id_arg = Value::Str("WI-001".to_string());

    // Driver has 1 requires (WorkItemStore[State]). Passing 0 dicts
    // must surface as a clear arity error at the boundary, not as
    // some internal slot mismatch.
    let result = interp.call_with_requirements(
        "test.wi236_poly.Driver.drive",
        &[cell, id_arg],
        SmallVec::new(),
    );
    match result {
        Err(EvalError::Internal(msg)) => {
            assert!(msg.contains("expected 1 requirement slot"), "got {msg}");
        }
        other => panic!("expected boundary-side arity error, got {other:?}"),
    }
}

#[test]
fn plain_call_on_polymorphic_op_documents_the_gap() {
    // Calling the polymorphic Driver.drive via the legacy
    // `interp.call` path seeds self-referential placeholders whose
    // `functor = Driver` doesn't match the cross-sort dispatch the
    // body needs — pin the failure so the gap stays documented until
    // `call_with_requirements` becomes the standard polymorphic
    // entry path.
    let kb = load_with_driver();
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp).expect("builtins");

    let cell = build_cell_wis(&mut interp);
    let id_arg = Value::Str("WI-001".to_string());

    let result = interp.call(
        "test.wi236_poly.Driver.drive",
        &[cell, id_arg],
    );
    eprintln!("[wi236-gap] plain-call result: {result:?}");
    // We don't assert a specific error shape here — the point is
    // that some failure occurs along the cross-sort dispatch path
    // when the dictionary isn't real. The companion test
    // (`polymorphic_entry_op_runs_when_dict_supplied`) shows the
    // fix.
    assert!(
        result.is_err(),
        "plain interp.call on a cross-sort polymorphic entry op \
         should fail (self-referential placeholder can't reach the \
         real impl); WI-236's call_with_requirements is the fix"
    );
}

/// Multi-op Driver mirroring the bundle's main.anthill: an entry op
/// (`main`) dispatches to a nested op (`cmd_inner`) which calls a spec
/// op (`WorkItemStore.lookup`). Pins that the requires dictionary
/// supplied to the entry op propagates through the sibling call to the
/// nested op's spec-op dispatch site.
const MULTI_OP_DRIVER: &str = r#"
namespace test.wi236_multi
  import anthill.prelude.{Cell, Option, String, Int}
  import anthill.stage0.{WorkItem}
  import anthill.todo.store.{WorkItemStore, FileBasedWorkitemStore, WIS}

  sort Driver
    sort State = ?
    requires WorkItemStore[State]

    operation main(s: Cell[State], id: String) -> Int
      effects Error
    =
      cmd_inner(s, id)

    operation cmd_inner(s: Cell[State], id: String) -> Int
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
    // Reproduce the bundle's main → dispatch → cmd_X chain: the spec
    // call sits in a sibling op, not the entry op itself. The typer's
    // dispatch classification must still fire so the runtime reaches
    // the impl body instead of erroring `unknown operation: lookup`.
    let mut files = crate::common::collect_stdlib_and_rust_bindings();
    files.push(crate::common::workspace_root().join("anthill-todo/domain.anthill"));
    files.push(crate::common::workspace_root().join("anthill-todo/store.anthill"));

    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(MULTI_OP_DRIVER).expect("parse multi-op driver"));
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver)
        .unwrap_or_else(|errs| {
            for e in &errs { eprintln!("{}", e); }
            panic!("load failed with {} errors", errs.len());
        });

    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp).expect("builtins");

    let cell = build_cell_wis(&mut interp);
    let id_arg = Value::Str("WI-001".to_string());

    let filebased = interp.kb_mut()
        .intern("anthill.todo.store.FileBasedWorkitemStore");
    let dict = interp.alloc_requirement(filebased, SmallVec::new());
    let mut requirements: SmallVec<[_; 2]> = SmallVec::new();
    requirements.push(dict);

    let result = interp.call_with_requirements(
        "test.wi236_multi.Driver.main",
        &[cell, id_arg],
        requirements,
    );
    match result {
        Ok(v) => eprintln!("[wi236-multi] OK: {v:?}"),
        Err(e) => {
            let msg = format!("{e:?}");
            eprintln!("[wi236-multi] err: {msg}");
            assert!(
                !msg.contains("unknown operation"),
                "nested-op dispatch should reach FileBasedWorkitemStore.lookup \
                 via the inherited requires; got {msg}"
            );
        }
    }
}

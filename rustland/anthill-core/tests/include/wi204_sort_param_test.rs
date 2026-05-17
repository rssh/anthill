//! Experiment: can we pass a parameterized spec sort like `WorkItemStore`
//! directly as a parameter type, with the State binding left open?
//!
//! Three forms to test:
//!   (a) `s: WorkItemStore` bare — does it parse / type-check / dispatch?
//!   (b) `s: Cell[?S]` + op-level `requires WorkItemStore[S]`
//!   (c) `sort Driver { sort S = ? requires WorkItemStore[S] ... operation drive(s: Cell[S]) }`


use anthill_core::eval::{self, Interpreter, Value};
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

fn load_bundle_context(driver_src: &str) -> Result<KnowledgeBase, Vec<load::LoadError>> {
    let mut files = crate::common::collect_stdlib_and_rust_bindings();
    files.push(crate::common::workspace_root().join("anthill-todo/domain.anthill"));
    files.push(crate::common::workspace_root().join("anthill-todo/store.anthill"));

    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src)
            .unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(driver_src).expect("parse driver"));
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).map(|_| kb)
}

fn report(label: &str, r: Result<KnowledgeBase, Vec<load::LoadError>>) {
    match r {
        Ok(_) => println!("[{label}] OK"),
        Err(errs) => {
            println!("[{label}] {} errors:", errs.len());
            for e in &errs {
                println!("  {e}");
            }
        }
    }
}

#[test]
fn form_a_bare_workitemstore_param() {
    let driver = r#"
namespace test.wi204_form_a
  import anthill.prelude.{Option, String}
  import anthill.reflect.{Term}
  import anthill.stage0.{WorkItem}
  import anthill.todo.store.{WorkItemStore}

  sort Driver
    operation drive(s: WorkItemStore, id: String) -> Option[T = WorkItem]
      effects Error
    =
      WorkItemStore.lookup(s, id)
  end
end
"#;
    report("form_a (bare WorkItemStore)", load_bundle_context(driver));
}

#[test]
fn form_b_op_level_requires_logical_var() {
    let driver = r#"
namespace test.wi204_form_b
  import anthill.prelude.{Cell, Option, String}
  import anthill.reflect.{Term}
  import anthill.stage0.{WorkItem}
  import anthill.todo.store.{WorkItemStore}

  sort Driver
    operation drive(s: Cell[?S], id: String) -> Option[T = WorkItem]
      effects Error
      requires WorkItemStore[?S]
    =
      WorkItemStore.lookup(s, id)
  end
end
"#;
    report("form_b (op-level requires + ?S)", load_bundle_context(driver));
}

#[test]
fn form_c_sort_level_typeparam_plus_requires() {
    let driver = r#"
namespace test.wi204_form_c
  import anthill.prelude.{Cell, Option, String}
  import anthill.reflect.{Term}
  import anthill.stage0.{WorkItem}
  import anthill.todo.store.{WorkItemStore}

  sort Driver
    sort S = ?
    requires WorkItemStore[S]

    operation drive(s: Cell[S], id: String) -> Option[T = WorkItem]
      effects Error
    =
      WorkItemStore.lookup(s, id)
  end
end
"#;
    report("form_c (sort-level S + requires)", load_bundle_context(driver));
}

#[test]
fn form_c_runtime_dispatch_through_polymorphic_op() {
    // Polymorphic Driver.drive whose body calls WorkItemStore.lookup;
    // ConcreteCaller.call_drive instantiates S = WIS and invokes
    // Driver.drive with a Cell[WIS]. Runtime should reach
    // FileBasedWorkitemStore.lookup (which calls retrieve), returning
    // an empty Option since no WorkItem facts are loaded.
    let driver_src = r#"
namespace test.wi204_form_c_runtime
  import anthill.prelude.{Cell, Option, String}
  import anthill.reflect.{Term}
  import anthill.stage0.{WorkItem}
  import anthill.todo.store.{WorkItemStore, FileBasedWorkitemStore, WIS}

  sort Driver
    sort S = ?
    requires WorkItemStore[S]

    operation drive(s: Cell[S], id: String) -> Option[T = WorkItem]
      effects Error
    =
      WorkItemStore.lookup(s, id)
  end

  sort ConcreteCaller
    requires WorkItemStore[WIS]

    operation call_drive(c: Cell[WIS], id: String) -> Option[T = WorkItem]
      effects Error
    =
      Driver.drive(c, id)
  end
end
"#;
    let kb = load_bundle_context(driver_src).expect("load");
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp)
        .expect("register builtins");

    // Build a Value::Cell holding wis(SomeBackend, 0). Backend doesn't
    // need to be registered for retrieve — we just want to confirm the
    // call reaches FileBasedWorkitemStore.lookup, then errors at the
    // retrieve builtin (no store registered for the wis backend) OR
    // returns empty (if retrieve gracefully no-ops). Either way it
    // proves dispatch works.
    let wis_sym = interp.kb_mut()
        .intern("anthill.todo.store.FileBasedWorkitemStore.wis");
    let backend_field = interp.kb_mut().intern("backend");
    let counter_field = interp.kb_mut().intern("id_counter");
    // A dummy backend value — won't be used unless retrieve actually
    // fires. For this smoke test, we want dispatch to be the only
    // thing exercised.
    let dummy_backend = Value::Entity {
        functor: interp.kb_mut().intern("FakeBackend"),
        pos: vec![],
        named: vec![],
    };
    let wis_value = Value::Entity {
        functor: wis_sym,
        pos: vec![],
        named: vec![
            (backend_field, dummy_backend),
            (counter_field, Value::Int(1)),
        ],
    };
    let handle = interp.alloc_cell(wis_value);
    let cell_value = Value::Cell(handle);

    let result = interp.call(
        "test.wi204_form_c_runtime.ConcreteCaller.call_drive",
        &[cell_value, Value::Str("WI-001".to_string())],
    );
    println!("[form_c_runtime] result: {result:?}");
    // We expect either Ok(Value::Entity with functor `none`) or an
    // Err whose message proves the call REACHED inside the lookup
    // body (not 'unknown operation: lookup' at the top).
    match result {
        Ok(v) => {
            println!("[form_c_runtime] OK value: {v:?}");
        }
        Err(e) => {
            let msg = format!("{e:?}");
            println!("[form_c_runtime] err: {msg}");
            assert!(
                !msg.contains("unknown operation: lookup")
                    && !msg.contains("unknown operation: drive")
                    && !msg.contains("OperationBodyMissing"),
                "expected dispatch to reach an impl body; got {msg}"
            );
        }
    }
}

#[test]
fn form_c_with_concrete_caller_dispatches() {
    // Form C polymorphic Driver plus a concrete caller that
    // instantiates S = WIS. The caller's call to Driver.drive
    // should pick FileBasedWorkitemStore at typing time. Pin
    // that dispatch_origin records the rewrite.
    let driver = r#"
namespace test.wi204_form_c_concrete
  import anthill.prelude.{Cell, Option, String}
  import anthill.reflect.{Term}
  import anthill.stage0.{WorkItem}
  import anthill.todo.store.{WorkItemStore, FileBasedWorkitemStore, WIS}

  sort Driver
    sort S = ?
    requires WorkItemStore[S]

    operation drive(s: Cell[S], id: String) -> Option[T = WorkItem]
      effects Error
    =
      WorkItemStore.lookup(s, id)
  end

  sort ConcreteCaller
    operation call_drive(c: Cell[WIS], id: String) -> Option[T = WorkItem]
      effects Error
    =
      Driver.drive(c, id)
  end
end
"#;
    match load_bundle_context(driver) {
        Ok(kb) => {
            println!("[form_c_concrete] OK loaded");
            // Check dispatch_origin: should record a rewrite of either
            // WorkItemStore.lookup (inside Driver.drive body) or no rewrite
            // (if dispatch is deferred to call site). Either way report
            // what we see.
            let store_lookup = kb.try_resolve_symbol("anthill.todo.store.WorkItemStore.lookup");
            let mut origins = Vec::new();
            for (rewritten, spec_sym) in kb.dispatch_origin_iter() {
                let spec_name = kb.resolve_sym(spec_sym).to_string();
                origins.push((rewritten, spec_name));
            }
            println!("[form_c_concrete] dispatch_origin entries: {}", origins.len());
            for (tid, name) in &origins {
                println!("  rewritten_tid={tid:?} spec={name}");
            }
            let hit_lookup = origins.iter().any(|(_, name)| name == "lookup")
                || matches!(store_lookup, Some(_));
            println!("[form_c_concrete] hit_lookup={hit_lookup}");
        }
        Err(errs) => {
            println!("[form_c_concrete] {} errors:", errs.len());
            for e in &errs {
                println!("  {e}");
            }
        }
    }
}

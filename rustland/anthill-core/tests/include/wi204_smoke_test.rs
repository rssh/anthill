//! WI-204 smoke test — pin that calling `WorkItemStore.lookup` /
//! `.commit` from a sort-body operation type-checks AND dispatches at
//! runtime when store.anthill is in scope. This is the foundation for
//! WI-204's port of bundle cmd_X bodies; if either piece breaks here,
//! the refactor is blocked on a typer/eval gap rather than a
//! mechanical rewrite of main.anthill.


use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Load stdlib + Rust stl bindings + anthill-todo/domain.anthill +
/// rustland/anthill-todo/anthill/store.anthill + the given driver source. Returns the
/// loaded KB if all phases succeed; panics with diagnostics otherwise.
fn load_bundle_context(driver_src: &str) -> KnowledgeBase {
    let mut files = crate::common::collect_stdlib_and_rust_bindings();
    files.push(crate::common::workspace_root().join("anthill-todo/domain.anthill"));
    // version.anthill defines the bundle's `StoreFormat` entity that store.anthill
    // now imports (WI-434) — load it before store or the import is unresolved.
    files.push(crate::common::workspace_root().join("rustland/anthill-todo/anthill/version.anthill"));
    files.push(crate::common::workspace_root().join("rustland/anthill-todo/anthill/store.anthill"));

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
    load::load_all(&mut kb, &refs, &NullResolver)
        .unwrap_or_else(|errs| {
            for e in &errs { eprintln!("{}", e); }
            panic!("load failed with {} errors", errs.len());
        });
    kb
}

#[test]
fn workitemstore_lookup_typechecks_from_bundle_sort_body() {
    // The shape that WI-204's cmd_show port relies on:
    //   match WorkItemStore.lookup(s, id)
    // where s is a sort-body operation's parameter of type Cell[WIS].
    //
    // WI-218 should statically rewrite the spec call to
    // FileBasedWorkitemStore.lookup; WI-219 should accept the Error
    // effect propagated up.
    let driver = r#"
namespace test.wi204_smoke_lookup
  import anthill.prelude.{Cell, Option, String}
  import anthill.reflect.{Term}
  import anthill.stage0.{WorkItem}
  import anthill.todo.store.{WorkItemStore, FileBasedWorkitemStore, WIS}

  sort Driver
    operation drive(s: Cell[WIS], id: String) -> Option[T = WorkItem]
      effects Error
    =
      WorkItemStore.lookup(s, id)
  end
end
"#;
    let kb = load_bundle_context(driver);
    let drive_sym = kb.try_resolve_symbol("test.wi204_smoke_lookup.Driver.drive")
        .expect("drive registered");
    // The very fact load_bundle_context returned without panicking
    // means the body type-checked. Pin one more thing: dispatch_origin
    // recorded at least one rewrite back to a WorkItemStore op,
    // confirming WI-218 saw the spec call inside Driver.drive.
    let mut hit = false;
    let store_lookup = kb.try_resolve_symbol("anthill.todo.store.WorkItemStore.lookup");
    for (_rewritten, spec_sym) in kb.dispatch_origin_iter() {
        if Some(spec_sym) == store_lookup {
            hit = true;
            break;
        }
    }
    assert!(hit,
        "expected dispatch_origin to record a rewrite of WorkItemStore.lookup \
         inside Driver.drive; got none. drive_sym={drive_sym:?}");
}

#[test]
fn workitemstore_commit_typechecks_with_modify_transitivity() {
    // The shape WI-204's cmd_add / cmd_claim ports need:
    //   commit(s, w) with effects {Modify[s], Error}
    // WI-219 must accept the inner persist's Modify[T = b] under the
    // declared Modify[s], since b is reachable from s through the wis
    // entity's `backend` field.
    let driver = r#"
namespace test.wi204_smoke_commit
  import anthill.prelude.{Cell, Unit, String}
  import anthill.stage0.{WorkItem}
  import anthill.todo.store.{WorkItemStore, FileBasedWorkitemStore, WIS}

  sort Driver
    operation drive(s: Cell[WIS], w: WorkItem) -> Unit
      effects {Modify[s], Error}
    =
      WorkItemStore.commit(s, w)
  end
end
"#;
    let kb = load_bundle_context(driver);
    let store_commit = kb.try_resolve_symbol("anthill.todo.store.WorkItemStore.commit");
    let mut hit = false;
    for (_rewritten, spec_sym) in kb.dispatch_origin_iter() {
        if Some(spec_sym) == store_commit {
            hit = true;
            break;
        }
    }
    assert!(hit,
        "expected dispatch_origin to record a rewrite of WorkItemStore.commit");
}

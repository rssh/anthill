//! WI-204 follow-up — reproducer for the typer env-loss bug noted in
//! WI-204's last feedback.
//!
//! Bug shape: a let-bound entity constructor whose value is then passed
//! to a spec op causes that spec op's `check_apply` to see
//! `env.enclosing_sort = None`. The requires-chain slot lookup then
//! fails and dispatch errors with
//!   "WI-210 dispatch failed: no impl of X for the per-call bindings".
//!
//! Workaround in production code (main.anthill) is to (a) inline the
//! constructor as a direct arg or (b) factor field-rebuilding into a
//! helper op (function call preserves env). This test pins both shapes:
//! the direct/inline case classifies, the let-bound case currently does
//! not. Once the typer fix lands, the let-bound assertion should flip
//! to also classify, and this test will catch regressions.
//!
//! Shape mirrors the cmd_claim / cmd_add bodies that hit the bug.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::typing::CallClass;
use anthill_core::parse;

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

/// Walk all op bodies and collect every spec-op call site whose
/// classification names `commit_sym` as the spec op being called.
fn commit_classifications(kb: &KnowledgeBase, commit_sym: anthill_core::intern::Symbol)
    -> Vec<CallClass>
{
    let mut hits = Vec::new();
    for (_, body) in kb.op_bodies_iter() {
        anthill_core::kb::node_occurrence::visit_classifications(body, &mut |_, c| {
            let names_commit = match c {
                CallClass::DeferToRequirement { spec_op_sym, .. } => *spec_op_sym == commit_sym,
                CallClass::ConcreteApplyWithin { spec_op_sym, .. } => *spec_op_sym == commit_sym,
                CallClass::PinNow { spec_op_sym, .. } => *spec_op_sym == commit_sym,
                CallClass::UnresolvedSpecOp { spec_op_sym, .. } => *spec_op_sym == commit_sym,
                CallClass::EtaOpRef { .. } => false,
            };
            if names_commit {
                hits.push(c.clone());
            }
        });
    }
    hits
}

/// Sanity baseline: a sort that `requires WorkItemStore[State]` and
/// calls `WorkItemStore.commit(s, wi)` directly (parameter `wi`, no
/// let-bound constructor in the way) classifies the call site as
/// DeferToRequirement, anchored to the enclosing Main sort.
#[test]
fn direct_call_classifies_as_defer() {
    let driver = r#"
namespace test.wi204_let_ctor_env_direct
  import anthill.prelude.{Cell, Int64}
  import anthill.stage0.{WorkItem}
  import anthill.todo.store.{WorkItemStore, FileBasedWorkitemStore, WIS}

  sort Main
    sort State = ?
    requires WorkItemStore[State]

    operation direct(s: Cell[State], wi: WorkItem) -> Int64
      effects {Modify[s], Error}
    =
      let _ = WorkItemStore.commit(s, wi)
      0
  end
end
"#;
    let kb = load_bundle_context(driver);
    let commit_sym = kb
        .try_resolve_symbol("anthill.todo.store.WorkItemStore.commit")
        .expect("WorkItemStore.commit");
    let outer = kb
        .try_resolve_symbol("test.wi204_let_ctor_env_direct.Main")
        .expect("Main sort");

    let hits = commit_classifications(&kb, commit_sym);
    let defer = hits.iter().find_map(|c| match c {
        CallClass::DeferToRequirement { enclosing_sort, .. } => Some(*enclosing_sort),
        _ => None,
    });
    assert_eq!(
        defer,
        Some(Some(outer)),
        "direct WorkItemStore.commit(s, wi) call must classify as \
         DeferToRequirement with enclosing_sort=Main; got {hits:?}"
    );
}

/// Bug reproducer: same sort body, but the WorkItem reaches `commit`
/// via a let-bound entity constructor. The expected classification is
/// still `DeferToRequirement { enclosing_sort: Some(Main) }`. Today the
/// typer drops `enclosing_sort` after the let-bound Constructor's
/// `TypeResult.env`, dispatch sees no requires chain, and the call site
/// either fails dispatch or classifies without the enclosing context.
///
/// This test asserts the *correct* behavior — once the typer fix lands
/// it should pass; until then it pins the bug.
#[test]
fn let_bound_constructor_does_not_drop_enclosing_sort() {
    let driver = r#"
namespace test.wi204_let_ctor_env_let
  import anthill.prelude.{Cell, Int64, Option, List, none, nil}
  import anthill.stage0.{WorkItem, Open}
  import anthill.todo.store.{WorkItemStore, FileBasedWorkitemStore, WIS}

  sort Main
    sort State = ?
    requires WorkItemStore[State]

    operation with_let_ctor(s: Cell[State]) -> Int64
      effects {Modify[s], Error}
    =
      let w = WorkItem(
        id: "WI-test",
        description: none(),
        context: none(),
        acceptance: nil(),
        depends_on: none(),
        generates: none(),
        requires_capability: none(),
        status: Open())
      let _ = WorkItemStore.commit(s, w)
      0
  end
end
"#;
    let kb = load_bundle_context(driver);
    let commit_sym = kb
        .try_resolve_symbol("anthill.todo.store.WorkItemStore.commit")
        .expect("WorkItemStore.commit");
    let outer = kb
        .try_resolve_symbol("test.wi204_let_ctor_env_let.Main")
        .expect("Main sort");

    let hits = commit_classifications(&kb, commit_sym);
    assert!(
        !hits.is_empty(),
        "WorkItemStore.commit call site after let-bound WorkItem(...) \
         must classify (any form); got nothing — typer probably bailed \
         on the call entirely (DispatchOutcome::NoMatch path eprintln's \
         and returns None)"
    );

    // The specific assertion that flips the bug: the call site must
    // see the enclosing Main sort. If env.enclosing_sort dropped to
    // None, `DeferToRequirement` won't fire (no requires chain visible)
    // and we'd either see a ConcreteApplyWithin with enclosing_sort=None
    // or nothing at all.
    let defer = hits.iter().find_map(|c| match c {
        CallClass::DeferToRequirement { enclosing_sort, .. } => Some(*enclosing_sort),
        _ => None,
    });
    assert_eq!(
        defer,
        Some(Some(outer)),
        "let-bound WorkItem(...) then passed to WorkItemStore.commit(s, w) \
         must classify as DeferToRequirement with enclosing_sort=Main \
         (same as the direct shape); got {hits:?}. \
         If this regression is present, the typer's TypeResult.env \
         propagation through let-bound Constructor expressions is \
         losing the enclosing-sort context (see WI-204 feedback)."
    );
}

//! WI-219: Modify-transitivity in effect typing.
//!
//! When an op declares `effects Modify[s]` and its body pattern-matches
//! `s` to extract a sub-resource `b`, calling another op with
//! `effects Modify[b]` should be accepted — `b` is reachable from `s`,
//! so Modify[s] subsumes (or local-resource elides) Modify[b].

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, LoadResult, NullResolver};
use anthill_core::kb::typing::type_check_sorts;
use anthill_core::parse;


fn load_stdlib_kb() -> KnowledgeBase {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let parsed: Vec<_> = files.iter()
        .map(|p| parse::parse(&std::fs::read_to_string(p).unwrap()).unwrap())
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).expect("stdlib load");
    kb
}

fn load_stdlib_and_project_kb() -> KnowledgeBase {
    let mut kb = load_stdlib_kb();
    // Load anthill-todo's domain.anthill to get stage0 / WorkItem / WorkStatus,
    // plus version.anthill for the bundle's `StoreFormat` entity that store.anthill
    // now imports (WI-434) — without it store.anthill's import is unresolved.
    let project_files = vec![
        crate::common::workspace_root().join("rustland/anthill-todo/anthill/domain.anthill"),
        crate::common::workspace_root().join("rustland/anthill-todo/anthill/version.anthill"),
    ];
    let parsed: Vec<_> = project_files.iter()
        .map(|p| parse::parse(&std::fs::read_to_string(p).unwrap()).unwrap())
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    load::load_all(&mut kb, &refs, &NullResolver).expect("project domain load");
    kb
}

fn load_with_stdlib(source: &str) -> (KnowledgeBase, LoadResult) {
    let mut kb = load_stdlib_kb();
    let parsed = parse::parse(source).expect("parse failed");
    let result = load::load(&mut kb, &parsed, &NullResolver).expect("load failed");
    (kb, result)
}

#[test]
fn store_anthill_typechecks() {
    // Load rustland/anthill-todo/anthill/store.anthill alongside the project domain.
    // This is the actual code WI-219's description claims fails.
    let mut kb = load_stdlib_and_project_kb();
    let store_path = crate::common::workspace_root().join("rustland/anthill-todo/anthill/store.anthill");
    let store_src = std::fs::read_to_string(&store_path).expect("read store.anthill");
    let parsed = parse::parse(&store_src).expect("parse store.anthill");
    let result = load::load(&mut kb, &parsed, &NullResolver).expect("load store.anthill");
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    let effect_errors: Vec<_> = errors.iter()
        .filter(|e| {
            let m = format!("{}", e);
            m.contains("undeclared effect") || m.contains("Modify")
        })
        .collect();
    assert!(
        effect_errors.is_empty(),
        "store.anthill should typecheck cleanly; got: {:#?}",
        effect_errors
    );
}

#[test]
fn commit_pattern_calling_stdlib_persist() {
    // Mirrors rustland/anthill-todo/anthill/store.anthill::FileBasedWorkitemStore::commit:
    // - Cell[V = State] s, pattern-matches on Cell.get(s) into st(b, c)
    // - Calls anthill.persistence.persist(b, term, meta), which has
    //   effects {Modify[store], Error}. After WI-209 substitution, this
    //   becomes Modify[T = b] at the call site.
    // - Op declares effects {Modify[s], Error}.
    // The pattern-bound b should be local; Modify[T = b] should not surface.
    let source = r#"
namespace anthill.test.wi219.commit_test
  import anthill.prelude.{Cell, Int64, Unit, List}
  import anthill.prelude.Meta.{Meta}
  import anthill.persistence.{Store, persist}
  import anthill.reflect.{Term}

  -- A backing store impl satisfying anthill.persistence.Store
  sort MyBackend
    fact Store
    entity bk(id: Int64)
  end

  sort MyState
    entity st(b: MyBackend, c: Int64)
  end

  sort MyStore
    operation commit(s: Cell[V = MyState], t: Term) -> Unit
      effects {Modify[s], Error}
    =
      match Cell.get(s)
        case st(b, c) ->
          let _ = persist(b, t, Meta(entries: nil()))
          Cell.set(s, st(b, c + 1))
  end
end
"#;
    let (mut kb, result) = load_with_stdlib(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    let effect_errors: Vec<_> = errors.iter()
        .filter(|e| {
            let m = format!("{}", e);
            m.contains("undeclared effect") || m.contains("Modify")
        })
        .collect();
    assert!(
        effect_errors.is_empty(),
        "commit calling stdlib persist should typecheck; got: {:#?}",
        effect_errors
    );
}

#[test]
fn modify_on_pattern_bound_subterm_does_not_leak() {
    // commit declares `effects Modify[s]` and pattern-matches s into
    // `st(b, c)`. Inside the case, calling persist(b, ...) produces
    // `Modify[b]`. Since `b` is pattern-bound, it's a local resource
    // and should NOT escape as an undeclared external effect.

    let source = r#"
namespace anthill.test.wi219
  import anthill.prelude.{Cell, Int64, Unit}

  -- A "backend" resource that supports persist
  sort Backend
    entity bk(id: Int64)

    operation persist(b: Backend, value: Int64) -> Unit
      effects Modify[b]
  end

  -- Wrapper state holds the backend plus a counter
  sort StoreState
    entity st(backend: Backend, counter: Int64)
  end

  -- Operation declaring Modify[s] and persisting on s.backend
  -- via pattern-bound `b`.
  sort Store
    operation commit(s: Cell[V = StoreState], value: Int64) -> Unit
      effects Modify[s]
    =
      match Cell.get(s)
        case st(b, c) ->
          persist(b, value)
  end
end
"#;
    let (mut kb, result) = load_with_stdlib(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    let effect_errors: Vec<_> = errors.iter()
        .filter(|e| format!("{}", e).contains("undeclared effect"))
        .collect();
    assert!(
        effect_errors.is_empty(),
        "Modify[b] (b pattern-bound from s) should not surface as undeclared; got: {:?}",
        effect_errors
    );
}

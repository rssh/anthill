//! WI-506 — a declared `Modify[c]` covers an incurred `Modify[c.field]`
//! (field-access projection), proposal 037 §"Effect-row convention" ("Modify[s]
//! covers everything reachable from s").
//!
//! Before this, only the pattern-bound-local path worked (WI-219 elides a
//! match-bound `Modify[r]`); a field-projection body `Cell.set(c.rep, …)` incurs
//! `Modify[c.rep]`, which the declared-effects check compared structurally
//! against `Modify[c]` and rejected. The fix roots a `Modify[place]` to its head
//! parameter for coverage: a declared `Modify[c]` (path `[c]`) covers an incurred
//! `Modify[c.rep]` (path `[c, rep]`) because `[c]` is a prefix.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

fn load_result(source: &str) -> Result<(), Vec<String>> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| parse::parse(&std::fs::read_to_string(p).unwrap()).unwrap())
        .collect();
    parsed.push(parse::parse(source).expect("parse user source"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver)
        .map(|_| ())
        .map_err(|errs| errs.iter().map(|e| format!("{}", e)).collect())
}

/// The trip-wire: a field-projection body (`Cell.set(c.rep, …)`, NO pattern
/// match) under declared `Modify[c]` must typecheck.
#[test]
fn declared_modify_covers_field_projection() {
    let src = r#"
namespace test.wi506.field
  import anthill.prelude.{Unit, Cell, List}
  import anthill.prelude.List.{nil, cons}

  sort Wrap
    sort T = ?
    entity wrap(rep: Cell[V = List[T]])

    operation push(c: Wrap, elem: T) -> Unit
      effects Modify[c]
    =
      Cell.set(c.rep, cons(head: elem, tail: Cell.get(c.rep)))
  end
end
"#;
    load_result(src).expect("declared Modify[c] must cover incurred Modify[c.rep]");
}

/// Regression: the pattern-bound form (WI-219 local-elision) still works.
#[test]
fn pattern_bound_form_still_works() {
    let src = r#"
namespace test.wi506.pat
  import anthill.prelude.{Unit, Cell, List}
  import anthill.prelude.List.{nil, cons}

  sort Wrap
    sort T = ?
    entity wrap(rep: Cell[V = List[T]])

    operation push(c: Wrap, elem: T) -> Unit
      effects Modify[c]
    =
      match c
        case wrap(r) -> Cell.set(r, cons(head: elem, tail: Cell.get(r)))
  end
end
"#;
    load_result(src).expect("the pattern-bound form must still typecheck");
}

/// Soundness: a declared `Modify[a]` must NOT cover an incurred `Modify[b.rep]`
/// on a DIFFERENT parameter `b` (the coverage is directional, head-matched).
#[test]
fn declared_modify_does_not_cover_other_param_field() {
    let src = r#"
namespace test.wi506.wrong
  import anthill.prelude.{Unit, Cell, List}

  sort Wrap
    sort T = ?
    entity wrap(rep: Cell[V = List[T]])

    operation move_into(a: Wrap, b: Wrap) -> Unit
      effects Modify[a]
    =
      Cell.set(b.rep, Cell.get(a.rep))
  end
end
"#;
    let errs = load_result(src)
        .expect_err("Modify[a] must NOT cover a mutation of b.rep (b != a)");
    assert!(
        errs.iter().any(|e| e.contains("undeclared effect") || e.contains("Modify")),
        "expected an undeclared-effect error for b.rep under Modify[a]; got: {errs:?}",
    );
}

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

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
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
    let errs = load_result(src).expect_err("Modify[a] must NOT cover a mutation of b.rep (b != a)");
    assert!(
        errs.iter()
            .any(|e| e.contains("undeclared effect") || e.contains("Modify")),
        "expected an undeclared-effect error for b.rep under Modify[a]; got: {errs:?}",
    );
}

/// WI-20260823-39AD2 — THE ARGUMENT SHAPES THAT RE-KEY, AND THE ONE THAT DOES NOT.
///
/// `param_to_arg_sym` / `param_to_arg_head` populate from exactly two argument shapes:
/// a bare VARIABLE reference (`Cell.set(k, 1)` → `Modify[c]` becomes `Modify[k]`) and a
/// field PROJECTION (`Cell.set(c.rep, 1)` → the head `c`, the rest of this file). An
/// argument that is neither — an APPLICATION, `Cell.set(mk(), 1)` — gets no entry, and
/// the callee's own parameter name SURVIVES into the caller's row: the diagnostic reads
/// `undeclared effect: Modify[T = c]`, naming `Cell.set`'s parameter, a symbol nowhere
/// in the caller's text.
///
/// PRE-EXISTING AND INDEPENDENT of the ticket that pinned it — measured on `Cell.set`,
/// whose row has read `Modify[c]` since proposal 037, with the effects.anthill change
/// backed out. WI-20260823-39AD2 only made it REACHABLE through a second op:
/// `ModifyRuntime.set` now declares `Modify[target]` too, so the ambient-resource idiom
/// `set(counter(), n)` (a nullary constructor naming a global slot — the shape
/// `prelude/effects.anthill`'s runtime note describes, and the one `eval_test`'s m5
/// fixtures were written in) is not writable today. Those fixtures now take the resource
/// as a PARAMETER; this row is what says the ambient spelling is missing rather than
/// letting it disappear from the record.
///
/// ASSERTS THE LEAK, NOT A WISH. It is loud, not silent, so the current behaviour is
/// safe — but the message names a symbol the author cannot see. When the re-key learns
/// this shape, this row flips to `Ok`.
#[test]
fn an_application_argument_does_not_rekey_and_leaks_the_callees_param_name() {
    let src = r#"
namespace test.wi39ad2.app_arg
  import anthill.prelude.{Unit, Int64, Cell, Modify}

  -- CONTROL: a bare variable argument DOES re-key. This arm passes today and must
  -- keep passing — it is what makes the arm below a gap rather than "Modify never
  -- re-keys".
  operation via_var(k: Cell[V = Int64]) -> Unit
    effects Modify[k]
  = Cell.set(k, 1)
end
"#;
    assert!(
        load_result(src).is_ok(),
        "a bare-variable argument must re-key the callee's Modify onto it"
    );

    let src_app = r#"
namespace test.wi39ad2.app_arg_gap
  import anthill.prelude.{Unit, Int64, Cell, Modify}

  operation mk() -> Cell[V = Int64] effects Modify[result] = Cell.new(0)

  -- THE GAP: `mk()` is an application, so nothing maps `Cell.set`'s `c` onto it.
  operation via_app() -> Unit
    effects {}
  = Cell.set(mk(), 1)
end
"#;
    let errs = load_result(src_app).expect_err("the un-re-keyed label must still be loud");
    assert!(
        // ASSERT THE LEAKED SYMBOL, not merely "some Modify escaped": `mk()` declares
        // `Modify[result]` two lines up in the same fixture, so a substring test on
        // `Modify` alone would be satisfied by an escape this row is not about.
        errs.iter()
            .any(|e| e.contains("undeclared effect") && e.contains("Modify[T = c]")),
        "expected `Cell.set`'s own parameter `c` to surface un-re-keyed; got: {errs:#?}"
    );
}

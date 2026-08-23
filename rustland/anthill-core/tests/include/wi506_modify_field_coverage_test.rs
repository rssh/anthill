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

/// WI-20260823-4GBQV — THE ARGUMENT SHAPES THAT NAME A PLACE, AND WHAT HAPPENS TO THE
/// ONE THAT DOES NOT.
///
/// `param_to_arg_sym` / `param_to_arg_head` populate from the shapes that DENOTE a place:
/// a bare VARIABLE (`Cell.set(k, 1)` ⟹ `Modify[c]` becomes `Modify[k]`), a field
/// PROJECTION off one (`Cell.set(c.rep, 1)` ⟹ the head `c`, the rest of this file), and —
/// as of this ticket — a NULLARY CONSTRUCTOR naming an ambient resource
/// (`set(counter(), n)`, driven end-to-end in
/// `eval_test::m5_modify_an_ambient_resource_write_then_read`).
///
/// AN APPLICATION IS NOT ONE, and stays refused. `Cell.set(mk(), 1)` passes a value that
/// no name denotes: `Env` maps resource NAMES to terms (kernel-language.md §5.6), and
/// `mk()`'s result is fresh per call, so there is no slot for `Modify[c]` to be re-keyed
/// onto. WHAT CHANGED IS THE MESSAGE. Before WI-20260823-4GBQV the label survived
/// un-re-keyed and surfaced far away as `undeclared effect: Modify[T = c]` — naming
/// `Cell.set`'s parameter, a symbol nowhere in the caller's text. It now reports at the
/// CALL, against the caller's own `mk(…)`, and prescribes the `let` binding that works.
///
/// THREE ARMS, THREE DIFFERENT QUESTIONS, and the file's own controls:
///   * `via_var` — a bare variable re-keys. Passes both before and after, by design: it
///     is what stops the third arm reading as "Modify never re-keys".
///   * `via_let` — the PRESCRIBED REPAIR, driven rather than described. A message naming
///     a repair that does not load is the defect WI-K88TN's (D) axis records.
///   * `via_app` — the refusal, asserted on the CALLER's token (`mk`) and on the ABSENCE
///     of the callee's (`Modify[T = c]`), so a regression to the leak fails it in the
///     direction it regressed.
#[test]
fn an_application_argument_is_refused_naming_the_callers_own_expression() {
    let src = r#"
namespace test.wi4gbqv.app_arg
  import anthill.prelude.{Unit, Int64, Cell, Modify}

  -- CONTROL: a bare variable argument DOES re-key. Passed before this ticket and must
  -- keep passing.
  operation via_var(k: Cell[V = Int64]) -> Unit
    effects Modify[k]
  = Cell.set(k, 1)
end
"#;
    assert!(
        load_result(src).is_ok(),
        "a bare-variable argument must re-key the callee's Modify onto it"
    );

    let src_let = r#"
namespace test.wi4gbqv.let_repair
  import anthill.prelude.{Unit, Int64, Cell, Modify}

  operation mk() -> Cell[V = Int64] effects Modify[result] = Cell.new(0)

  -- THE REPAIR the refusal below prescribes: bind the application to a name, then pass
  -- the name. Driven, so the message cannot prescribe something that does not load.
  -- The row is EMPTY and not `Modify[x]`: `x` is a body local, out of scope in the
  -- signature (`unresolved name 'x'`), and a mutation of a value the operation itself
  -- made and never lets escape is not an observable effect — so binding the argument
  -- both names a place for the re-key AND elides the label. Measured, not assumed:
  -- spelling `effects Modify[x]` here is two load errors.
  operation via_let() -> Unit
    effects {}
  =
    let x = mk()
    Cell.set(x, 1)
end
"#;
    assert!(
        load_result(src_let).is_ok(),
        "`let x = mk()` then `Cell.set(x, 1)` is the prescribed repair and must load"
    );

    let src_app = r#"
namespace test.wi4gbqv.app_arg_refused
  import anthill.prelude.{Unit, Int64, Cell, Modify}

  operation mk() -> Cell[V = Int64] effects Modify[result] = Cell.new(0)

  -- THE REFUSAL: `mk()` is an application, which names no slot in `Env`.
  operation via_app() -> Unit
    effects {}
  = Cell.set(mk(), 1)
end
"#;
    let errs = load_result(src_app).expect_err("an argument naming no place must be refused");
    assert!(
        errs.iter()
            .any(|e| e.contains("names no resource") && e.contains("mk")),
        "expected the refusal to name the CALLER's own `mk(…)`; got: {errs:#?}"
    );
    assert!(
        // THE REGRESSION DIRECTION. The defect was the callee's parameter leaking into
        // the caller's row; asserting its ABSENCE is what fails if the leak returns,
        // which asserting the new message alone would not.
        !errs.iter().any(|e| e.contains("Modify[T = c]")),
        "`Cell.set`'s own parameter `c` must not surface in the caller's diagnostic; \
         got: {errs:#?}"
    );
}

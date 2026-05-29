//! WI-279 — dot dispatch as a client of the type-directed `[simp]` engine.
//!
//! A value-receiver dot form `?x.method(args)` / `?x.field` reaches the typer
//! as an `Expr::DotApply` (a pre-dispatch form). The typer dispatches it via
//! the receiver's least declared sort (`min_sort`):
//!   - method (default fallback): resolve `name` to an operation declared on
//!     that sort, synthesize `Apply(op, [receiver, ...args])`, re-type it.
//!   - no match: a clear `DotDispatchNoMatch` diagnostic at the dot's span.
//!
//! The receiver `?x` resolves to its in-scope binding (param / let / lambda /
//! match) — the typer runs with the lexical env in hand — so a method on the
//! binding's sort is found with no import.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver, LoadError};
use anthill_core::parse;

/// Load stdlib + `extra` source; return the KB plus any load errors
/// (type-check errors surface here via `type_check_sorts`).
fn load_capturing_errors(extra: &str) -> (KnowledgeBase, Vec<LoadError>) {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => (kb, vec![]),
        Err(errs) => (kb, errs),
    }
}

fn errors_text(errs: &[LoadError]) -> String {
    errs.iter().map(|e| format!("{e}")).collect::<Vec<_>>().join("\n")
}

// ── Acceptance item 1: `?x.method(args)` dispatch via receiver sort ─────

#[test]
fn dot_method_zero_arg_dispatches_via_param_receiver() {
    // `?b.peek()`: `?b` resolves to param `b: Box`, min_sort = Box; `peek` is
    // declared on Box → dispatch synthesizes `peek(b)` → Int. No import.
    let src = r#"
        namespace wi279.method
          export Box
          sort Box
            entity box(value: Int)
            operation peek(b: Box) -> Int = 42
            operation use_peek(b: Box) -> Int = ?b.peek()
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(),
        "expected ?b.peek() to dispatch to peek(b) and type-check; got:\n{}",
        errors_text(&errs));
}

#[test]
fn dot_method_with_args_dispatches() {
    // `?b.add_to(1)` → `add_to(b, 1)`: receiver becomes the first positional
    // arg, the call's own args follow.
    let src = r#"
        namespace wi279.method_args
          export Box
          sort Box
            entity box(value: Int)
            operation add_to(b: Box, k: Int) -> Int = k
            operation use_add(b: Box) -> Int = ?b.add_to(1)
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(),
        "expected ?b.add_to(1) to dispatch to add_to(b, 1); got:\n{}",
        errors_text(&errs));
}

#[test]
fn dot_method_dispatches_with_no_import_across_sorts() {
    // The method lives on a *different* sort than the caller — found via the
    // receiver's sort, not lexical scope / import. `?inner` resolves to a
    // field of `Holder`'s constructor via the match binding.
    let src = r#"
        namespace wi279.cross
          export Box, Holder
          sort Box
            entity box(value: Int)
            operation peek(b: Box) -> Int = 7
          end
          sort Holder
            entity holder(inner: Box)
            operation use_holder(h: Holder) -> Int =
              match h
                case holder(inner) -> ?inner.peek()
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(),
        "expected match-bound ?inner.peek() to dispatch to Box.peek with no import; got:\n{}",
        errors_text(&errs));
}

#[test]
fn dot_method_chaining_dispatches_each_level() {
    // `?b.bump().bump()`: the inner dispatch yields `bump(b): Box`, whose
    // result is the receiver of the outer `.bump()`. Each level dispatches via
    // the (rewritten) receiver's sort.
    let src = r#"
        namespace wi279.chain
          export Box
          sort Box
            entity box(value: Int)
            operation bump(b: Box) -> Box = b
            operation use_chain(b: Box) -> Box = ?b.bump().bump()
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(),
        "expected chained ?b.bump().bump() to dispatch at each level; got:\n{}",
        errors_text(&errs));
}

#[test]
fn dot_method_generic_type_param_infers_through_dispatch() {
    // `?b.idfn(42)` → `idfn(b, 42)`: the dispatched call rides normal Apply
    // type-param inference (043 §6.6) — `U` is pinned from the arg `42` (Int),
    // so the call's return type is Int and the body type-checks.
    let src = r#"
        namespace wi279.generic
          export Box
          sort Box
            entity box(value: Int)
            operation idfn[U](b: Box, u: U) -> U = u
            operation use_gen(b: Box) -> Int = ?b.idfn(42)
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(),
        "expected ?b.idfn(42) to dispatch and infer U = Int; got:\n{}",
        errors_text(&errs));
}

// ── Acceptance item 3: receivers referencing let/match-bound locals ─────

#[test]
fn dot_let_bound_receiver_dispatches() {
    // `let x = b` binds x: Box; `?x.peek()` resolves x and dispatches.
    let src = r#"
        namespace wi279.letbound
          export Box
          sort Box
            entity box(value: Int)
            operation peek(b: Box) -> Int = 1
            operation use_let(b: Box) -> Int =
              let x = b
              ?x.peek()
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(),
        "expected let-bound ?x.peek() to dispatch; got:\n{}",
        errors_text(&errs));
}

// ── Acceptance item 4: clear no-match error at the dot span ─────────────

#[test]
fn dot_no_match_reports_clear_error_at_span() {
    // `?b.nope()`: receiver resolves to Box, but Box has no `nope` operation →
    // a DotDispatchNoMatch naming the member and the receiver's sort.
    let src = r#"
        namespace wi279.nomatch
          export Box
          sort Box
            entity box(value: Int)
            operation use_bad(b: Box) -> Int = ?b.nope()
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    let text = errors_text(&errs);
    assert!(!errs.is_empty(), "expected a no-match error for ?b.nope()");
    assert!(text.contains("no such member (dot dispatch)") && text.contains("nope"),
        "expected a dot-dispatch no-match diagnostic naming 'nope'; got:\n{text}");
    assert!(text.contains("Box"),
        "expected the no-match diagnostic to name the receiver's sort Box; got:\n{text}");
}

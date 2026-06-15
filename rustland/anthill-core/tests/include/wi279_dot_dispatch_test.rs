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
    // declared on Box → dispatch synthesizes `peek(b)` → Int64. No import.
    let src = r#"
        namespace wi279.method
          export Box
          sort Box
            entity box(value: Int64)
            operation peek(b: Box) -> Int64 = 42
            operation use_peek(b: Box) -> Int64 = ?b.peek()
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
            entity box(value: Int64)
            operation add_to(b: Box, k: Int64) -> Int64 = k
            operation use_add(b: Box) -> Int64 = ?b.add_to(1)
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
            entity box(value: Int64)
            operation peek(b: Box) -> Int64 = 7
          end
          sort Holder
            entity holder(inner: Box)
            operation use_holder(h: Holder) -> Int64 =
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
            entity box(value: Int64)
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
    // type-param inference (043 §6.6) — `U` is pinned from the arg `42` (Int64),
    // so the call's return type is Int64 and the body type-checks.
    let src = r#"
        namespace wi279.generic
          export Box
          sort Box
            entity box(value: Int64)
            operation idfn[U](b: Box, u: U) -> U = u
            operation use_gen(b: Box) -> Int64 = ?b.idfn(42)
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(),
        "expected ?b.idfn(42) to dispatch and infer U = Int64; got:\n{}",
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
            entity box(value: Int64)
            operation peek(b: Box) -> Int64 = 1
            operation use_let(b: Box) -> Int64 =
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
            entity box(value: Int64)
            operation use_bad(b: Box) -> Int64 = ?b.nope()
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

// ── Acceptance item 2: sort-specific dot rule overrides the default ──────

#[test]
fn dot_rule_override_enables_dispatch() {
    // `special` is NOT an operation on Box, so the default fallback would fail
    // (no-match). A sort-specific [simp] dot rule rewrites `?b.special(x)` to
    // `regular(b, x)` — so the body type-checks ONLY IF the override fires.
    let src = r#"
        namespace wi279.override
          export Box
          sort Box
            entity box(value: Int64)
            operation regular(b: Box, x: Int64) -> Int64 = x
            rule dr: dot_apply(?e, special, ?x) = regular(?e, ?x) [simp]
            operation use_override(b: Box) -> Int64 = ?b.special(7)
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(),
        "expected the [simp] dot rule to rewrite ?b.special(7) -> regular(b, 7) \
         (no `special` op exists, so the body type-checks only if the rule fired); got:\n{}",
        errors_text(&errs));
}

#[test]
fn dot_rule_override_is_sort_scoped() {
    // A dot rule for `special` declared in Box must NOT fire for a non-Box
    // receiver (the enclosing-sort guard). `Other` has no `special` op and the
    // Box rule's guard excludes it, so `?o.special(7)` is a clean no-match —
    // the Box rule does not hijack the member name across sorts.
    let src = r#"
        namespace wi279.override_scoped
          export Box, Other
          sort Box
            entity box(value: Int64)
            operation regular(b: Box, x: Int64) -> Int64 = x
            rule dr: dot_apply(?e, special, ?x) = regular(?e, ?x) [simp]
          end
          sort Other
            entity other(tag: Int64)
            operation use_other(o: Other) -> Int64 = ?o.special(7)
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    let text = errors_text(&errs);
    assert!(!errs.is_empty(),
        "expected a no-match for ?o.special(7): the Box dot rule must not fire for an Other receiver");
    assert!(text.contains("no such member (dot dispatch)") && text.contains("special"),
        "expected a dot-dispatch no-match naming 'special' for the Other receiver; got:\n{text}");
}

#[test]
fn dot_rule_nonlinear_lhs_does_not_fire_on_distinct_args() {
    // A non-linear LHS `dot_apply(?e, special, ?e)` requires the receiver and
    // the arg to be the SAME term. `?b.special(7)` has distinct receiver (b) and
    // arg (7), so the implied equality fails — the rule must NOT fire (the
    // matcher honours the substitution's contradiction). With no `special` op,
    // the result is a clean no-match, not an unsound rewrite to `regular(b)`.
    let src = r#"
        namespace wi279.nonlinear
          export Box
          sort Box
            entity box(value: Int64)
            operation regular(b: Box) -> Int64 = 0
            rule dr: dot_apply(?e, special, ?e) = regular(?e) [simp]
            operation use_nl(b: Box) -> Int64 = ?b.special(7)
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    let text = errors_text(&errs);
    assert!(!errs.is_empty(),
        "expected a no-match: the non-linear rule must not fire when receiver != arg");
    assert!(text.contains("no such member (dot dispatch)") && text.contains("special"),
        "expected a dot-dispatch no-match naming 'special'; got:\n{text}");
}

// ── Acceptance: `?x.field` constructor-field access (INC 1b) ────────────

/// Call a nullary op and expect an Int64 result.
fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

#[test]
fn dot_field_reads_entity_field_and_evals() {
    // `?b.value`: `value` is not an operation on Box, so the method fallback
    // misses; the field fallback synthesizes `field_access(b, "value")`, typed
    // as the field's type (Int64) and evaluated by reading the named field off
    // the runtime entity.
    let src = r#"
namespace wi279.field
  import anthill.prelude.Int64
  sort Box
    entity box(value: Int64)
    operation read(b: Box) -> Int64 = ?b.value
  end
  operation t() -> Int64 = box(value: 42).read()
end
"#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(),
        "expected ?b.value to dispatch to the field; got:\n{}", errors_text(&errs));
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi279.field.t"), 42);
}

#[test]
fn dot_field_generic_param_substitutes_and_evals() {
    // `?o.value` on `o: Option[T = Int64]`: the field `value: T` resolves with
    // the receiver's type-arg substituted (T = Int64, via `resolve_field_type`),
    // and at runtime reads the `some` payload — the substitution path threaded
    // end to end through the field fallback.
    let src = r#"
namespace wi279.genfield
  import anthill.prelude.{Int64, Option}
  import anthill.prelude.Option.some
  operation read(o: Option[T = Int64]) -> Int64 = ?o.value
  operation t() -> Int64 = read(some(value: 42))
end
"#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(),
        "expected ?o.value to dispatch with T = Int64; got:\n{}", errors_text(&errs));
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi279.genfield.t"), 42);
}

#[test]
fn dot_field_unknown_member_reports_no_match() {
    // `?b.nope`: not an operation and not a field of Box → the field fallback's
    // `resolve_field_type` miss falls through to a clean no-match at the dot span.
    let src = r#"
        namespace wi279.nofield
          export Box
          sort Box
            entity box(value: Int64)
            operation use_bad(b: Box) -> Int64 = ?b.nope
          end
        end
    "#;
    let (_kb, errs) = load_capturing_errors(src);
    let text = errors_text(&errs);
    assert!(!errs.is_empty(), "expected a no-match error for ?b.nope");
    assert!(text.contains("no such member (dot dispatch)") && text.contains("nope"),
        "expected a dot-dispatch no-match naming 'nope'; got:\n{text}");
}

#[test]
fn dot_method_and_field_eval_end_to_end() {
    // End-to-end runnability of the `?x` value-receiver dot forms (eval now
    // resolves the `Expr::Var(Global)` receiver by name): `?b.total(10)` →
    // `total(b, 10)`, whose body reads `?b.value` (field) and adds. With
    // `box(value: 5)` the result is `5 + 10 = 15`.
    let src = r#"
namespace wi279.e2e
  import anthill.prelude.Int64
  sort Box
    entity box(value: Int64)
    operation total(b: Box, n: Int64) -> Int64 = ?b.value + n
    operation run(b: Box) -> Int64 = ?b.total(10)
  end
  operation t() -> Int64 = box(value: 5).run()
end
"#;
    let (_kb, errs) = load_capturing_errors(src);
    assert!(errs.is_empty(),
        "expected ?b.total(10) + ?b.value to dispatch; got:\n{}", errors_text(&errs));
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "wi279.e2e.t"), 15);
}

//! Phase F tests: F.1 effect-aware return wrapping, F.2 wildcard-let
//! statement-position lowering.
//!
//! F.1 — operations declaring `effects Error` get their return type
//! wrapped in `tl::expected<T, std::string>`. Calls to
//! `anthill.prelude.Error.raise(e)` lower to `tl::make_unexpected(e)`.
//!
//! F.2 — `let _ = expr; body` emits `expr;` (statement) instead of
//! `auto _ = expr;` so the surrounding IIFE compiles when expr is
//! `void` (a side-effecting call).

use super::common;

use anthill_cpp_gen::emit_traits_struct;
use common::{load_kb_with, load_kb_with_lenient};

#[test]
fn error_effect_wraps_return_in_tl_expected() {
    let source = r#"
        namespace test.expr_f_err
          import anthill.prelude.{Int64}
          sort Calc
            operation safe_div(a: Int64, b: Int64) -> Int64 effects Error = a
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_traits_struct(&mut kb, "test.expr_f_err.Calc")
        .expect("emit Calc");

    assert!(
        cpp.contains("static tl::expected<int64_t, std::string> safe_div(int64_t a, int64_t b)"),
        "Error effect should wrap return type as tl::expected:\n{cpp}"
    );
}

#[test]
fn raise_lowers_to_make_unexpected() {
    // The body returns `raise("boom")` directly; lowering should
    // emit `tl::make_unexpected("boom")` so the value matches the
    // wrapped return type. The lenient loader is needed because the
    // typer doesn't yet model raise's `Nothing` return as compatible
    // with `Int64`.
    let source = r#"
        namespace test.expr_f_raise
          import anthill.prelude.{Int64, Error}
          import anthill.prelude.Error.{raise}
          sort Calc
            operation always_fail() -> Int64 effects Error =
              raise("boom")
          end
        end
    "#;
    let mut kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&mut kb, "test.expr_f_raise.Calc")
        .expect("emit Calc");

    assert!(
        cpp.contains("tl::expected<int64_t, std::string>"),
        "return type should be wrapped:\n{cpp}"
    );
    assert!(
        cpp.contains("return tl::make_unexpected(\"boom\");"),
        "raise should lower to tl::make_unexpected:\n{cpp}"
    );
}

#[test]
fn error_effect_in_effects_set_still_wraps() {
    // Multiple effects in `{Error, Modify[self]}` — the loader stores
    // them as a list. We pick out Error from anywhere in that list.
    let source = r#"
        namespace test.expr_f_multi
          import anthill.prelude.{Int64}
          entity Calc(state: Int64)
          sort CalcOps
            operation step(self: Calc) -> Int64 effects {Error, Modify[self]} = 0
          end
        end
    "#;
    let mut kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&mut kb, "test.expr_f_multi.CalcOps")
        .expect("emit CalcOps");

    assert!(
        cpp.contains("tl::expected<int64_t, std::string>"),
        "multi-effect set with Error should still wrap return:\n{cpp}"
    );
}

#[test]
fn no_error_effect_keeps_plain_return_type() {
    // Sanity: an op with `Modify[self]` but no Error stays unwrapped.
    let source = r#"
        namespace test.expr_f_modify_only
          import anthill.prelude.{Int64}
          entity Calc(state: Int64)
          sort CalcOps
            operation poke(self: Calc) -> Int64 effects Modify[self] = 0
          end
        end
    "#;
    let mut kb = load_kb_with_lenient(source);
    let cpp = emit_traits_struct(&mut kb, "test.expr_f_modify_only.CalcOps")
        .expect("emit CalcOps");

    assert!(
        !cpp.contains("tl::expected"),
        "Modify-only op should not be wrapped:\n{cpp}"
    );
    assert!(
        cpp.contains("static int64_t poke("),
        "plain int64_t return type missing:\n{cpp}"
    );
}

#[test]
fn wildcard_let_emits_discard_statement() {
    // `let _ = side_effect(...)` should emit the call as a
    // statement, not as `auto _ = …;` — `auto _` doesn't compile when
    // the call returns `void`.
    let source = r#"
        namespace test.expr_f_void
          import anthill.prelude.{Int64}
          sort Calc
            operation sink(x: Int64) -> Int64 = x
            operation chain(x: Int64) -> Int64 =
              let _ = sink(x)
              add(x, 1)
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_traits_struct(&mut kb, "test.expr_f_void.Calc")
        .expect("emit Calc");

    // Discard slot prints `expr; ` (no `auto _ = `).
    assert!(
        cpp.contains("[&]() { sink(x); return (x + 1); }()"),
        "wildcard let should emit statement-discard:\n{cpp}"
    );
}

#[test]
fn wildcard_let_followed_by_named_let_composes() {
    // Mix: `let _ = a; let y = b; body` produces `a; auto y = b; return body;`.
    let source = r#"
        namespace test.expr_f_mix
          import anthill.prelude.{Int64}
          sort Calc
            operation sink(x: Int64) -> Int64 = x
            operation step(x: Int64) -> Int64 =
              let _ = sink(x)
              let y = add(x, 1)
              add(y, 1)
          end
        end
    "#;
    let mut kb = load_kb_with(source);
    let cpp = emit_traits_struct(&mut kb, "test.expr_f_mix.Calc")
        .expect("emit Calc");

    assert!(
        cpp.contains("[&]() { sink(x); auto y = (x + 1); return (y + 1); }()"),
        "wildcard+named let mix should compose:\n{cpp}"
    );
}

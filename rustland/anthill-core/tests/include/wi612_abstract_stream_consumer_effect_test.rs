//! WI-612 — typer (abstract-E effect threading, carrier-param CONSUMER variant):
//! a qualified `Iterable` consumer (`isEmpty` / `find`) over a bare `Stream`
//! receiver whose access row `E` is ABSTRACT (unwritten) must thread the incurred
//! effect as the receiver's projection `s.E` instead of leaking it as `?_`.
//!
//! `f(s: Stream[T = Int64]) -> Bool effects s.E = Iterable.isEmpty(s)`: `s`'s E is
//! unwritten, so the carrier-param binding (`bind_spec_params_from_carrier_param`
//! via `parameterized_vid_bindings`) finds no `E` type-arg on `Stream[T = Int64]`
//! → `Iterable.E` stays unbound → the incurred effect leaks `?_`, and the op is
//! rejected with `f.effects: expected declared [s.E], got undeclared effect: ?_`.
//! Distinct from WI-604 (the CONCRETE case: a bare Stream with WRITTEN `E = {}`).
//! Here `E` is UNWRITTEN, so the receiver's abstract `E` must thread as the
//! self-projection `s.E`.

/// Merely LOADING `f` proves the abstract access row threaded as `s.E` — before
/// WI-612 this raised `undeclared effect: ?_`.
#[test]
fn wi612_isempty_over_abstract_stream_threads_projection() {
    let src = r#"
namespace test.wi612
  import anthill.prelude.{Stream, Bool, Int64, Iterable}

  operation f(s: Stream[T = Int64]) -> Bool effects s.E =
    Iterable.isEmpty(s)
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.is_empty(),
        "Iterable.isEmpty(s) over an abstract-E Stream param should thread the \
         access row as s.E:\n{}",
        errs.join("\n")
    );
}

/// `find` leaks the SAME `?_` (its `effects {E, EffP}` carries the abstract `E`).
#[test]
fn wi612_find_over_abstract_stream_threads_projection() {
    let src = r#"
namespace test.wi612b
  import anthill.prelude.{Stream, Bool, Int64, Option, Iterable}

  operation is_big(n: Int64) -> Bool = n > 2

  operation g(s: Stream[T = Int64]) -> Option[Int64] effects s.E =
    Iterable.find(s, is_big)
end
"#;
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.is_empty(),
        "Iterable.find(s, p) over an abstract-E Stream param should thread the \
         access row as s.E:\n{}",
        errs.join("\n")
    );
}

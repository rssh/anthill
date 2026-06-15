//! WI-476 — name resolution resolves an unqualified name in its LOCAL
//! ENVIRONMENT (enclosing scope / imports / `requires`), with no global
//! short-name fallback. A name that is not in scope is left for the typer to
//! reject as an unknown functor, rather than being silently rescued by a scan
//! over every qualified name in the KB.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

fn load_errors(src: &str) -> Vec<String> {
    let parsed = parse::parse(src).expect("parse");
    let refs = vec![&parsed];
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

/// A namespace-level operation calling a SIBLING operation in the same
/// namespace resolves through the enclosing-namespace scope chain — no import,
/// no fallback.
#[test]
fn namespace_sibling_op_resolves() {
    let src = r#"
namespace test.wi476.ok
  import anthill.prelude.Int64
  operation f(x: Int64) -> Int64 = x
  operation use_f() -> Int64 = f(42)
end
"#;
    let errs = load_errors(src);
    assert!(errs.is_empty(), "expected no load errors, got: {errs:?}");
}

/// A `requires`-brought spec operation resolves inside the requiring sort's
/// body via the `requires` scope link (the model's case 4): `zero()` inside
/// `Box.zeroLike` resolves to `HasZero.zero` because `Box requires HasZero[T]`.
#[test]
fn requires_brought_spec_op_resolves_in_scope() {
    let src = r#"
namespace test.wi476.req
  import anthill.prelude.Int64

  sort HasZero
    sort T = ?
    operation zero() -> T
  end

  sort Tag
    entity tag(n: Int64)
  end
  operation tagZero() -> Tag = tag(n: 42)
  fact HasZero[T = Tag, zero = tagZero]

  sort Box
    sort T = ?
    requires HasZero[T]
    entity box(content: T)
    operation zeroLike(b: Box) -> T =
      match b
        case box(_) -> zero()
  end
end
"#;
    let errs = load_errors(src);
    assert!(errs.is_empty(), "expected no load errors, got: {errs:?}");
}

/// The WI-463 dissolution: a spec operation called unqualified from a scope
/// that neither imports nor `requires` the spec does NOT resolve (no global
/// short-name fallback rescues it), so the typer reports an unknown functor.
#[test]
fn unqualified_spec_op_without_requires_is_unknown() {
    let src = r#"
namespace test.wi476.noreq
  import anthill.prelude.Int64

  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end

  sort Tag
    entity tag(n: Int64)
  end
  operation tagCombine(x: Tag, y: Tag) -> Tag = tag(n: 99)
  fact Combiner[T = Tag, combine = tagCombine]

  operation runCombine(a: Tag, b: Tag) -> Tag = combine(a, b)
end
"#;
    let errs = load_errors(src);
    assert!(
        errs.iter().any(|e| e.contains("combine")),
        "an unqualified spec-op call with no import/requires must be a loud \
         unknown-functor error; got: {errs:?}"
    );
}

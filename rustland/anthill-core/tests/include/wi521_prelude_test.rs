//! WI-521 — the implicit PRELUDE (cons / nil / some / none, the arithmetic and
//! comparison operator targets, the logic operators not / or / push_choice)
//! resolves via a LOWEST-PRECEDENCE fallback (`prelude_qualified`), not a
//! `_global` import.
//!
//! The distinguishing property vs the old flat `add_import(_global, …)`: a user
//! name that clashes with a prelude name is NEVER ambiguous — the user's wins.
//! With the flat injection, an imported `eq` plus the `_global` `eq` resolved to
//! `Ambiguous` (a load error); that footgun is exactly what the WI-476 collision
//! blocklist worked around. The fallback fires only when scope resolution fails,
//! so the clash cannot happen.

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

/// Load the full stdlib plus `extra`, returning load/type error strings ([] = clean).
fn load_stdlib_errors(extra: &str) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

/// A user-defined operation named `eq` (clashing with the prelude `Eq.eq`),
/// imported and used in another namespace, loads CLEAN — the prelude is
/// shadowable and never ambiguous. Under the old flat `_global` injection the use
/// site saw both the imported `eq` and the `_global` `eq` → `Ambiguous` error.
#[test]
fn user_eq_shadows_prelude_without_ambiguity() {
    let src = r#"
namespace test.wi521.mymod
  import anthill.prelude.{Bool, Int64}
  operation eq(x: Int64, y: Int64) -> Bool = true
end
namespace test.wi521.user
  import anthill.prelude.{Bool, Int64}
  import test.wi521.mymod.{eq}
  operation use_eq(x: Int64) -> Bool = eq(x, x)
end
"#;
    let errs = load_stdlib_errors(src);
    assert!(
        errs.is_empty(),
        "a user `eq` shadowing the prelude must load clean (no ambiguity); got: {errs:?}"
    );
}

/// Bare prelude operators resolve with NO import line — the fallback supplies them.
#[test]
fn bare_prelude_names_resolve_without_import() {
    let src = r#"
namespace test.wi521.use
  import anthill.prelude.{Int64, Bool}
  operation plus(x: Int64, y: Int64) -> Int64 = add(x, y)
  operation same(x: Int64, y: Int64) -> Bool = eq(x, y)
end
"#;
    let errs = load_stdlib_errors(src);
    assert!(
        errs.is_empty(),
        "bare prelude `add` / `eq` must resolve without importing them; got: {errs:?}"
    );
}

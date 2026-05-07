//! WI-071 — bare-Type positional SortBinding for parameterized type
//! references. `Map[String, Int]` is the user-facing shorthand for
//! `Map[K = String, V = Int]`; positional bindings map to the sort's
//! type parameters in declaration order.
//!
//! Before this fix, `type_expr_to_term`'s Parameterized arm silently
//! dropped positional bindings ("// Positional bindings without param
//! name — skip for now"), so `Map[String, Int]` parsed and loaded but
//! produced a `parameterized(base: Map)` with no K/V mapping at all.
//! The fix consults `KnowledgeBase::type_params_of_sort` (which now
//! returns declaration order via the new `Scope::type_params_ordered`
//! Vec) to map index 0 → first param, index 1 → second, etc.

mod common;

use anthill_core::parse;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};

/// Load a tiny test program and assert it has no errors. Returns the
/// KB so the caller can probe further.
fn load_ok(source: &str) -> KnowledgeBase {
    let parsed = parse::parse(source).expect("parse");
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let stdlib_dir = common::stdlib_dir();
    let stdlib_files = common::collect_anthill_files(&stdlib_dir);
    let stdlib_parsed: Vec<_> = stdlib_files.iter()
        .map(|p| parse::parse(&std::fs::read_to_string(p).unwrap()).expect("stdlib parse"))
        .collect();
    let refs: Vec<_> = stdlib_parsed.iter().chain(std::iter::once(&parsed)).collect();
    if let Err(errs) = load::load_all(&mut kb, &refs, &NullResolver) {
        for e in &errs {
            eprintln!("load error: {e}");
        }
        panic!("load failed with {} errors", errs.len());
    }
    kb
}

#[test]
fn positional_two_params_maps_to_declaration_order() {
    // Map declares `sort K = ?; sort V = ?` in that order. The
    // positional form `Map[String, Int]` must produce the same
    // parameterized type as the named form `Map[K = String, V = Int]`.
    // We verify by loading two operations side-by-side and checking
    // the typer accepts both equivalently.
    let src = r#"
namespace test.wi071_pos
  import anthill.prelude.{Map, String, Int}
  import anthill.prelude.Map.{empty, put, get}

  operation positional() -> Map[String, Int] = put(empty(), "a", 1)
  operation named() -> Map[K = String, V = Int] = put(empty(), "a", 1)

  -- Same return type for both — so a third op assigning one to a
  -- variable of the other's annotated type should typecheck. If the
  -- positional form silently dropped its bindings (the pre-fix
  -- behaviour), the typer would see the result as Map[K=?, V=?] vs
  -- Map[K=String, V=Int] and complain.
  operation cross_check() -> Map[String, Int] = named()
end
"#;
    let _kb = load_ok(src);
}

#[test]
fn positional_single_param_preserves_existing_behaviour() {
    // Single-param sorts (List, Option, Stream) used to work by
    // accident under the old pre-fix code path that allowed
    // Type-only-without-param via convert_term. Make sure the new
    // declaration-order lookup still routes correctly.
    let src = r#"
namespace test.wi071_single
  import anthill.prelude.{List, Option, Int}
  import anthill.prelude.List.{cons, nil}

  operation make_list() -> List[Int] = cons(1, nil())
  operation maybe() -> Option[Int] = none()
end
"#;
    let _kb = load_ok(src);
}

#[test]
fn named_binding_overrides_positional_cursor() {
    // Mixed forms: a named binding assigns by name regardless of the
    // positional cursor's location. After a named binding, the
    // positional cursor stays where it was (positional indices count
    // only positional bindings, not named).
    let src = r#"
namespace test.wi071_mixed
  import anthill.prelude.{Map, String, Int}
  import anthill.prelude.Map.{empty}

  -- V named explicitly; K still resolves positionally to "String".
  operation mixed1() -> Map[String, V = Int] = empty()

  -- K named explicitly; V resolves positionally to "Int".
  operation mixed2() -> Map[K = String, Int] = empty()
end
"#;
    let _kb = load_ok(src);
}

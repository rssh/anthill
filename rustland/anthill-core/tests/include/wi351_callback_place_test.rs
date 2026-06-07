//! WI-351 — `op.param` projection: callback parameter/result places.
//!
//! Generalizes proposal 041's lone `<op>.result` to the full set of
//! operation-frame *places* the `Modify`-effect feed/flow analysis references
//! (docs/design/modify-effect-derive.md §"Where flow facts live"): `op.param`,
//! `op.callback.param`, `op.callback.result`. The loader
//! (`scan_operation_params`) registers a place symbol for each, qualified under
//! the op (and callback) name, so a fact/rule referencing `foldLeft.f.a` /
//! `foldLeft.f.result` resolves — the shared prerequisite for WI-352/353.
//!
//! These tests pin the public *resolution* (`try_resolve_symbol`) through the
//! full stdlib load path WI-352 will run on; the place→role contract
//! (`PlaceRole`, `pub(crate)`) is unit-tested in `kb::load`.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Load stdlib + a user source together (the path the effect check runs on).
fn load_with(source: &str) -> KnowledgeBase {
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
    load::load_all(&mut kb, &refs, &NullResolver).expect("stdlib + user load");
    kb
}

#[test]
fn foldleft_callback_places_resolve() {
    // A foldLeft-shaped HOF loaded alongside the full stdlib. Every projection
    // reference the feed/flow analysis names must resolve to a place symbol.
    let source = r#"
namespace anthill.test.wi351
  import anthill.prelude.{List, Int64}

  operation reduce[S, T](xs: List[T = T], z: S, f: (a: S, t: T) -> S) -> S
end
"#;
    let kb = load_with(source);
    let p = "anthill.test.wi351.reduce";
    for place in [
        // op params
        format!("{p}.xs"),
        format!("{p}.z"),
        format!("{p}.f"),
        // callback params + result
        format!("{p}.f.a"),
        format!("{p}.f.t"),
        format!("{p}.f.result"),
        // op result (proposal 041, unchanged)
        format!("{p}.result"),
    ] {
        assert!(
            kb.try_resolve_symbol(&place).is_some(),
            "callback/param place `{place}` should resolve",
        );
    }
}

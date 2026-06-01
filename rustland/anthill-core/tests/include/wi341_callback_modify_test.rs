//! WI-341 (loader binder context) + WI-360 (end-to-end callback `Modify`
//! propagation). A callback parameter whose arrow effect modifies its OWN param
//! — `f: (a: Cell) -> Unit @ Modify[a]` — now LOADS: the binder `a` resolves to
//! the registered `CallbackParam` place `<op>.f.a` (it used to fail as
//! `UnresolvedName "a"`). Applied over a list element, that latent `Modify[f.a]`
//! flows to the op boundary, where the WI-353 classifier re-keys it via the
//! WI-352 flow facts and surfaces `Modify[l]` — the full pipeline, from source.

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

/// Load stdlib + user source together (the path the effect check runs on) and
/// surface load errors as strings rather than panicking.
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
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver)
        .map(|_| ())
        .map_err(|errs| errs.iter().map(|e| format!("{}", e)).collect())
}

/// A `foreach` whose callback modifies the element it is handed. `?decl` is the
/// op-level effects clause (empty, or `effects Modify[l]`).
fn each_src(decl: &str) -> String {
    format!(
        r#"
namespace anthill.test.wi341
  import anthill.prelude.{{List, Unit, Cell}}

  operation each(l: List[T = Cell], f: (a: Cell) -> Unit @ Modify[a]) -> Unit{decl} =
    match l
      case nil() -> ()
      case cons(h, rest) -> f(h)
end
"#
    )
}

#[test]
fn callback_modify_arrow_param_loads() {
    // The headline WI-341 fix: a callback arrow effect referencing its OWN param
    // (`Modify[a]`) must LOAD — `a` resolves to the place `each.f.a`, not
    // `UnresolvedName "a"`. With the surfaced `Modify[l]` declared, it is clean.
    let errs = load_result(&each_src(" effects Modify[l]"));
    assert!(
        errs.is_ok(),
        "callback `Modify[a]` must load (binder `a` -> place each.f.a) and, with \
         `effects Modify[l]` declared, type clean; got: {:#?}",
        errs.err()
    );
}

#[test]
fn callback_element_modify_surfaces_on_list_from_source() {
    // The WI-360 acceptance, end-to-end: without the declaration, the modify on
    // the element callback must surface as `Modify[l]` at the boundary and be
    // reported undeclared — proving the full pipeline (binder->place ->
    // body row Modify[f.a] -> WI-352 flow -> WI-353 re-key -> Modify[l]) fired.
    let errs = load_result(&each_src(""))
        .expect_err("a foreach whose callback modifies its element must surface Modify[l]");
    assert!(
        errs.iter().any(|e| e.contains("Modify") && e.contains('l')),
        "expected an undeclared `Modify[l]` effect error (the surfaced, re-keyed \
         label); got: {:#?}",
        errs,
    );
}

#[test]
fn arrow_param_name_colliding_with_type_param_is_not_captured() {
    // WI-341 over-capture guard: the binder scope must apply ONLY to the arrow's
    // effect labels, not its param/return TYPE positions. Here the arrow param
    // `a` shares a name with the op type-param `a`; `(a: a) -> a` must type as the
    // type-param (so `f(v)` checks), not capture the type `a` to the place `f.a`.
    let src = r#"
namespace anthill.test.wi341collide
  import anthill.prelude.{Unit}

  operation apply_id[a](v: a, f: (a: a) -> a) -> a = f(v)
end
"#;
    load_result(src).expect(
        "an arrow param name colliding with a type-param must not corrupt the \
         arrow's param/return types",
    );
}

#[test]
fn non_modifying_callback_needs_no_effect() {
    // Control: a callback with no effect surfaces nothing — `each` stays pure and
    // needs no declaration. (Guards against the binder context spuriously
    // minting an effect.)
    let src = r#"
namespace anthill.test.wi341pure
  import anthill.prelude.{List, Unit, Cell}

  operation each(l: List[T = Cell], f: (a: Cell) -> Unit) -> Unit =
    match l
      case nil() -> ()
      case cons(h, rest) -> f(h)
end
"#;
    load_result(src).expect("a non-modifying callback must leave `each` pure");
}

//! WI-20260924-R97NK — a type alias is no more visible than what it names (§8.6).
//!
//! `namespace lib` with `internal sort Hidden` and a public `sort PubAlias = Hidden`: every
//! other scope could write `x: lib.PubAlias`, reach `lib.PubAlias.mk(…)`, and — since
//! F8PYZ reads an alias through in a spec clause — `provides lib.PubAlias[…]`, while the
//! direct spellings `lib.Hidden` are refused "'lib.Hidden' is internal to 'lib'". Found by
//! F8PYZ's review.
//!
//! USER DECISION (2026-09-27): refuse AT THE DECLARATION — a public alias whose definition
//! names an `internal` name hidden from outside is a load error, at any depth of the
//! definition (`List[T = Hidden]`) and by any leading part of a path. `internal sort
//! PubAlias = Hidden` is the alias the owner writes; it works inside its scope and is
//! refused outside like the sort it names. Not a re-export: an `import` is not one either
//! (§8.6, WI-369).
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! MEASURED 2026-09-27 by making `refuse_public_alias_of_internal` return at once: the four
//! `…_is_refused` rows fail (each program loads clean). Every other row passes either way
//! by design — they are the controls: the direct spelling refused, and the `internal` alias
//! (the repair the refusal names) working inside `lib` and refused outside it.

use crate::common::{assert_refused_naming, interp_for_files, try_load_kb_with_files};
use anthill_core::eval::Value;

/// `lib`: an `internal` spec `Store` and an `internal` data sort `Hidden`, the `aliases`
/// under test, and a carrier providing `Store` through `StoreAlias`. `go` drives the spec
/// clause (dispatch on `Store`, answered only by that provision), `unbox` the type position
/// (a field read through a value typed by `HiddenAlias`).
fn lib(aliases: &str) -> String {
    format!(
        r#"
namespace lib
  import anthill.prelude.{{Int64}}
  internal sort Store
    sort State = ?
    operation peek(s: State) -> Int64
  end
  internal sort Hidden
    entity mk(v: Int64)
  end
{aliases}
  sort WIS
    entity wis(n: Int64)
  end
  sort FileStore
    provides StoreAlias[State = WIS]
    operation peek(s: WIS) -> Int64 = s.n
  end
  operation unbox(h: HiddenAlias) -> Int64 = h.v
  operation go() -> Int64 = Store.peek(wis(n: 9))
  operation go2() -> Int64 = unbox(Hidden.mk(v: 3))
end
"#
    )
}

const INTERNAL_ALIASES: &str =
    "  internal sort StoreAlias = Store\n  internal sort HiddenAlias = Hidden";

fn errors(sources: &[&str]) -> Vec<String> {
    try_load_kb_with_files(sources).err().unwrap_or_default()
}

fn call(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{op}` must run to an Int64: {other:?}"),
    }
}

#[track_caller]
fn assert_public_alias_refused(errs: &[String], alias: &str, hidden: &str, why: &str) {
    assert_refused_naming(
        errs,
        &[
            &format!("type alias '{alias}' is public but names '{hidden}'"),
            "declare it `internal sort`",
        ],
        why,
    );
}

#[track_caller]
fn assert_forbidden(errs: &[String], name: &str, why: &str) {
    assert_refused_naming(errs, &[&format!("'{name}' is internal to 'lib'")], why);
}

// ── the refusal ─────────────────────────────────────────────────────────────────────────

/// The type position. Was: loaded, and `x: lib.HiddenAlias` loaded from any namespace.
#[test]
fn a_public_alias_of_an_internal_sort_is_refused() {
    let src = lib("  internal sort StoreAlias = Store\n  sort HiddenAlias = Hidden");
    assert_public_alias_refused(
        &errors(&[&src]),
        "lib.HiddenAlias",
        "lib.Hidden",
        "a public alias of an internal data sort",
    );
}

/// The spec clause. Was: loaded, and `provides lib.StoreAlias[…]` loaded from anywhere.
#[test]
fn a_public_alias_of_an_internal_spec_is_refused() {
    let src = lib("  sort StoreAlias = Store\n  internal sort HiddenAlias = Hidden");
    assert_public_alias_refused(
        &errors(&[&src]),
        "lib.StoreAlias",
        "lib.Store",
        "a public alias of an internal spec",
    );
}

/// The hidden name as a type ARGUMENT is named all the same.
#[test]
fn a_public_alias_applying_an_internal_sort_is_refused() {
    let src = lib(&format!(
        "{INTERNAL_ALIASES}\n  import anthill.prelude.List\n  sort Hiddens = List[T = Hidden]"
    ));
    assert_public_alias_refused(
        &errors(&[&src]),
        "lib.Hiddens",
        "lib.Hidden",
        "a public alias naming an internal sort as an argument",
    );
}

/// A scope ENCLOSED by `lib` sees `Hidden`, so it can write the alias — and a public one
/// there would publish it just the same.
#[test]
fn a_public_alias_in_an_enclosed_scope_is_refused() {
    let src = lib(&format!(
        "{INTERNAL_ALIASES}\n  namespace sub\n    sort SubAlias = lib.Hidden\n  end"
    ));
    assert_public_alias_refused(
        &errors(&[&src]),
        "lib.sub.SubAlias",
        "lib.Hidden",
        "a public alias of an internal sort, declared in an enclosed namespace",
    );
}

// ── the controls: the repair, and the direct spelling ───────────────────────────────────

/// The repair works where it is visible: inside `lib` the `internal` aliases drive the spec
/// clause (the provision through `StoreAlias` answers the dispatch) and the type position
/// (a `HiddenAlias` value has `Hidden`'s field). An enclosed scope may alias it `internal`.
#[test]
fn an_internal_alias_works_inside_its_scope() {
    let with_sub = format!(
        "{INTERNAL_ALIASES}\n  namespace sub\n    internal sort SubAlias = lib.Hidden\n  end"
    );
    let src = lib(&with_sub);
    let mut interp = interp_for_files(&[&src]);
    assert_eq!(call(&mut interp, "lib.go"), 9);
    assert_eq!(call(&mut interp, "lib.go2"), 3);
}

fn outside_type(ty: &str) -> String {
    format!(
        r#"
namespace user
  import anthill.prelude.{{Int64}}
  operation f(x: {ty}) -> Int64 = 1
end
"#
    )
}

fn outside_provision(spec: &str) -> String {
    format!(
        r#"
namespace user
  import anthill.prelude.{{Int64}}
  sort Mine
    provides {spec}[State = lib.WIS]
    operation peek(s: lib.WIS) -> Int64 = 1
  end
end
"#
    )
}

/// Outside `lib`, the internal alias in a type position is refused as the internal name it is.
#[test]
fn an_internal_alias_in_a_type_position_outside_is_forbidden() {
    let src = lib(INTERNAL_ALIASES);
    assert_forbidden(
        &errors(&[&src, &outside_type("lib.HiddenAlias")]),
        "lib.HiddenAlias",
        "the internal alias named in a type position from another namespace",
    );
}

/// The control: the sort it names, directly.
#[test]
fn an_internal_sort_in_a_type_position_outside_is_forbidden() {
    let src = lib(INTERNAL_ALIASES);
    assert_forbidden(
        &errors(&[&src, &outside_type("lib.Hidden")]),
        "lib.Hidden",
        "the internal sort named in a type position from another namespace",
    );
}

/// Outside `lib`, the internal alias in a spec clause is refused the same way.
#[test]
fn an_internal_alias_in_a_spec_clause_outside_is_forbidden() {
    let src = lib(INTERNAL_ALIASES);
    assert_forbidden(
        &errors(&[&src, &outside_provision("lib.StoreAlias")]),
        "lib.StoreAlias",
        "the internal alias named in a provision from another namespace",
    );
}

/// The control: the spec it names, directly.
#[test]
fn an_internal_spec_in_a_spec_clause_outside_is_forbidden() {
    let src = lib(INTERNAL_ALIASES);
    assert_forbidden(
        &errors(&[&src, &outside_provision("lib.Store")]),
        "lib.Store",
        "the internal spec named in a provision from another namespace",
    );
}

/// A public alias of a PUBLIC sort is untouched: it loads and is usable from outside.
#[test]
fn a_public_alias_of_a_public_sort_is_usable_outside() {
    let src = lib(&format!("{INTERNAL_ALIASES}\n  sort WisAlias = WIS"));
    let user = r#"
namespace user
  import anthill.prelude.{Int64}
  operation n(w: lib.WisAlias) -> Int64 = w.n
  operation go() -> Int64 = n(lib.WIS.wis(n: 4))
end
"#;
    let mut interp = interp_for_files(&[&src, user]);
    assert_eq!(call(&mut interp, "user.go"), 4);
}

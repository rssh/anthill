//! WI-639 — distributive dot projection `x.(m1, …, mn)`.
//!
//! Generalizes WI-638's single-field `x.f` to a MEMBER LIST: `x.(m1, …, mn)`
//! desugars (at convert) to the ordered/named tuple `(m1: x.m1, …, mn: x.mn)`
//! — distribute the receiver `x` over the members, each `x.mi` an ordinary
//! dot-dispatch (WI-638), the result keyed by the member names. A bare member
//! auto-labels (`x.(f)` ⇒ key `f`); `a: f` renames (key `a`, member `f`); a
//! single member 1-collapses to the bare `x.m` value. Two load-bearing rules:
//! the result is the ORDERED/NAMED tuple (labels preserved, never positional
//! `_1/_2`), and members resolve at TYPING (never a value-position scope
//! symbol) — so `x`/`y` below are members of the receiver, not free idents.
//!
//! Desugaring early means no new typer/eval arm: the existing WI-638
//! field-access typing + named-tuple-literal typing + eval carry it.

use anthill_core::eval::Value;
// The projection label guards are convert-time (purely syntactic, no type info
// needed), so they surface as PARSE errors, not load errors — hence
// `common::parse_errs` rather than `try_load_kb_with` for those cases.
use crate::common::{interp_for, parse_errs, try_load_kb_with};

fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// THE acceptance shape: keep-projection over a literal (schema narrows to the
/// selected columns), rename-projection, single-member 1-collapse, and a
/// named-tuple PARAM projected then re-read. Members (`x`, `y`, …) are never
/// declared as values — they resolve as receiver components at typing.
#[test]
fn distributive_projection_types_and_evals() {
    let src = r#"
namespace test.wi639
  import anthill.prelude.{Int64}
  operation keep_x() -> Int64
    = (x: 10, y: 20, z: 30).(x, y).x
  operation keep_y() -> Int64
    = (x: 10, y: 20, z: 30).(x, y).y
  operation rename_a() -> Int64
    = (x: 10, y: 20).(a: x, b: y).a
  operation rename_b() -> Int64
    = (x: 10, y: 20).(a: x, b: y).b
  operation single_collapse() -> Int64
    = (x: 10, y: 20).(x)
  operation single_rename_collapse() -> Int64
    = (x: 10, y: 20).(a: x)
  operation param_keep(t: (x: Int64, y: Int64)) -> (x: Int64, y: Int64)
    = t.(x, y)
  operation use_param() -> Int64
    = param_keep((x: 7, y: 9)).y
end
"#;
    assert!(
        try_load_kb_with(src).is_ok(),
        "distributive projection must type-check; got: {:?}",
        try_load_kb_with(src).err(),
    );
    let mut interp = interp_for(src);
    // keep: `(x,y)` selects x and y, drops z — re-read by name off the result.
    assert_eq!(run_int(&mut interp, "test.wi639.keep_x"), 10, "(…).(x, y).x");
    assert_eq!(run_int(&mut interp, "test.wi639.keep_y"), 20, "(…).(x, y).y");
    // rename: keys are `a`/`b`, values sourced from `x`/`y`.
    assert_eq!(run_int(&mut interp, "test.wi639.rename_a"), 10, "(x,y).(a: x, b: y).a");
    assert_eq!(run_int(&mut interp, "test.wi639.rename_b"), 20, "(x,y).(a: x, b: y).b");
    // 1-collapse: a single member is the scalar value, not a 1-tuple.
    assert_eq!(run_int(&mut interp, "test.wi639.single_collapse"), 10, "(x,y).(x) ⇒ 10");
    assert_eq!(run_int(&mut interp, "test.wi639.single_rename_collapse"), 10, "(x,y).(a: x) ⇒ 10");
    // param: projection of a named-tuple param, returned as a tuple and re-read.
    assert_eq!(run_int(&mut interp, "test.wi639.use_param"), 9, "param_keep((7,9)).y");
}

/// Projection is schema-preserving/narrowing: the result carries EXACTLY the
/// projected keys. A keep-projection `(x, y)` over `(x, y, z)` yields a value
/// whose `z` no longer exists — reading `.z` off it is a loud dot-dispatch
/// error, proving the projection is the narrowed ordered/named tuple (not the
/// original, and not positional).
#[test]
fn keep_projection_narrows_schema() {
    let src = r#"
namespace test.wi639narrow
  import anthill.prelude.{Int64}
  operation bad() -> Int64
    = (x: 10, y: 20, z: 30).(x, y).z
end
"#;
    let errs = match try_load_kb_with(src) {
        Ok(_) => panic!("reading a projected-away column `.z` must NOT load"),
        Err(errs) => errs,
    };
    assert!(
        errs.iter().any(|e| e.contains("dot dispatch")),
        "narrowed-away column must surface a dot-dispatch error; got: {errs:?}",
    );
}

/// Rename genuinely re-keys: after `.(a: x, b: y)` the source key `x` is gone,
/// so `.x` off the renamed result is a loud error (only `a`/`b` remain). This
/// confirms the result is keyed by the LABELS, not the source members.
#[test]
fn rename_projection_rekeys_schema() {
    let src = r#"
namespace test.wi639rekey
  import anthill.prelude.{Int64}
  operation bad() -> Int64
    = (x: 10, y: 20).(a: x, b: y).x
end
"#;
    let errs = match try_load_kb_with(src) {
        Ok(_) => panic!("reading a source key `.x` after rename must NOT load"),
        Err(errs) => errs,
    };
    assert!(
        errs.iter().any(|e| e.contains("dot dispatch")),
        "renamed-away key must surface a dot-dispatch error; got: {errs:?}",
    );
}

/// A projected member that the receiver does NOT declare is a loud
/// dot-dispatch error — the desugaring adds resolutions, it does not swallow
/// a genuine mismatch (mirrors WI-638's absent-component negative).
#[test]
fn absent_projected_member_is_a_loud_error() {
    let src = r#"
namespace test.wi639neg
  import anthill.prelude.{Int64}
  operation bad(t: (x: Int64, y: Int64)) -> (x: Int64, w: Int64)
    = t.(x, w)
end
"#;
    let errs = match try_load_kb_with(src) {
        Ok(_) => panic!("projecting an absent member `t.(x, w)` must NOT load"),
        Err(errs) => errs,
    };
    assert!(
        errs.iter().any(|e| e.contains("dot dispatch")),
        "absent projected member must surface a dot-dispatch error; got: {errs:?}",
    );
}

/// A DUPLICATE projected key is a loud load error, not a silent
/// last-column-wins. Both a repeated bare member (`x.(a, a)`) and a rename
/// collision (`x.(k: a, k: b)`) would otherwise build a duplicate-key named
/// tuple whose second column is silently dropped (typing + eval both resolve
/// the FIRST match) — a real footgun the guard turns loud.
#[test]
fn duplicate_projection_key_is_a_loud_error() {
    for (name, body) in [
        ("bare", "(a: 1, b: 2).(a, a)"),
        ("rename", "(a: 1, b: 2).(k: a, k: b)"),
    ] {
        let src = format!(
            "namespace test.wi639dup\n  import anthill.prelude.{{Int64}}\n  \
             operation bad() -> Int64\n    = {body}.a\nend\n"
        );
        let errs = parse_errs(&src);
        assert!(
            errs.iter().any(|e| e.contains("duplicate distributive projection key")),
            "duplicate key ({name}) `{body}` must surface a loud error; got: {errs:?}",
        );
    }
}

/// A `_`-prefixed projected key (bare positional-component members `x.(_1, _2)`)
/// is a loud error: `_`-keyed tuple fields are re-slotted POSITIONALLY at eval,
/// so a reordered projection would silently return the wrong column. Projection
/// is named-only; positional selection is `(x.f1, x.f2)` written out.
#[test]
fn positional_component_projection_key_is_a_loud_error() {
    let src = r#"
namespace test.wi639pos
  import anthill.prelude.{Int64}
  operation bad() -> Int64
    = (100, 200).(_2, _1)._1
end
"#;
    let errs = parse_errs(src);
    assert!(
        errs.iter().any(|e| e.contains("colliding with the positional-tuple convention")),
        "`_`-prefixed key must surface a loud error; got: {errs:?}",
    );
}

/// The guard is narrow: RENAMING a positional component to a non-`_` label is
/// fine — `x.(a: _1, b: _2)` builds the named tuple `(a: x._1, b: x._2)`, which
/// evaluates and re-reads correctly (the result keys `a`/`b` are not
/// positional). Confirms the guard rejects only the ambiguous `_`-keyed result.
#[test]
fn renaming_positional_components_is_allowed() {
    let src = r#"
namespace test.wi639posok
  import anthill.prelude.{Int64}
  operation swap_a() -> Int64
    = (100, 200).(a: _2, b: _1).a
  operation swap_b() -> Int64
    = (100, 200).(a: _2, b: _1).b
end
"#;
    assert!(
        try_load_kb_with(src).is_ok(),
        "renaming positional components must type-check; got: {:?}",
        try_load_kb_with(src).err(),
    );
    let mut interp = interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi639posok.swap_a"), 200, "(a: _2, b: _1).a = t._2");
    assert_eq!(run_int(&mut interp, "test.wi639posok.swap_b"), 100, "(a: _2, b: _1).b = t._1");
}

/// Projection composes with WI-638 single-field access and nests: a projected
/// component can itself be projected, and a projection can feed a `.f`.
#[test]
fn distributive_projection_composes_with_field_access() {
    let src = r#"
namespace test.wi639c
  import anthill.prelude.{Int64}
  operation nested() -> Int64
    = (a: (m: 5, n: 6), b: 7, c: 8).(a, b).a.n
  operation project_then_field() -> Int64
    = (x: 100, y: 200, z: 300).(x, y).x
end
"#;
    assert!(
        try_load_kb_with(src).is_ok(),
        "composed projection must type-check; got: {:?}",
        try_load_kb_with(src).err(),
    );
    let mut interp = interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi639c.nested"), 6, "(a:(m,n), b, c).(a, b).a.n");
    assert_eq!(run_int(&mut interp, "test.wi639c.project_then_field"), 100, ".(x, y).x");
}

//! WI-775 — a name-keyed tuple must not satisfy a POSITIONAL `_N`-keyed one.
//!
//! `align_named_tuple_fields`' WI-442 positional fallback admitted any two
//! equal-arity field lists as long as ONE side was the canonical `_1.._n`
//! convention. That let a VALUE of type `(a: Int64, b: Int64)` be passed where
//! `(_1: Int64, _2: Int64)` was declared — and reading `._1` off it then went to
//! `Value::Tuple.pos`, which is EMPTY for a name-keyed tuple, so evaluation
//! raised `Internal("field_access: tuple has no component '_1'")`. Both
//! directions were measured to load clean and trap only when run, so the
//! rejection tests below must be paired with the end-to-end drives further down.
//!
//! The fix splits the two positions the fallback had conflated. A DATA tuple
//! aligns by NAME (a component's name is its access path); an ARROW'S PARAMETER
//! LIST keeps the positional fallback (a parameter list is applied positionally,
//! so binder names need not agree). `TupleAlign` in `kb/typing.rs` states which.

use crate::common::{interp_for, try_load_kb_with};

fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// Assert the program is refused with the located op-arg type mismatch naming
/// BOTH shapes — not merely "some error", which a typo would also satisfy.
fn assert_arg_mismatch(src: &str, expected_ty: &str, got_ty: &str) {
    let errs = match try_load_kb_with(src) {
        Ok(_) => panic!("must NOT load: `{got_ty}` passed where `{expected_ty}` is declared"),
        Err(errs) => errs,
    };
    let want = format!("expected {expected_ty}, got {got_ty}");
    assert!(
        errs.iter().any(|e| e.contains("type mismatch") && e.contains(&want)),
        "rejection must be the op-arg type mismatch `{want}`; got: {errs:?}",
    );
}

/// THE ticket repro verbatim, arity 1 — the shape WI-766 widened the hole to by
/// making `(_1: T)` writable. (The body is the arity-2 `(a: 5, b: 6)` because a
/// ONE-component tuple value `(a: 5)` is not writable; width subtyping narrows
/// it to the declared arity-1 return.)
#[test]
fn name_keyed_tuple_does_not_satisfy_positional_param_arity1() {
    assert_arg_mismatch(
        r#"
namespace test.wi775a
  import anthill.prelude.{Int64}
  operation get1(t: (_1: Int64)) -> Int64
    = t._1
  operation one() -> (a: Int64)
    = (a: 5, b: 6)
  operation drive() -> Int64
    = get1(one())
end
"#,
        "(_1: Int64)",
        "(a: Int64)",
    );
}

/// The PRE-EXISTING arity-2 control from the ticket — legal syntax before
/// WI-766, same soundness hole. Reading `t._1` off a name-keyed value trapped.
#[test]
fn name_keyed_tuple_does_not_satisfy_positional_param_arity2() {
    assert_arg_mismatch(
        r#"
namespace test.wi775b
  import anthill.prelude.{Int64}
  operation get1(t: (_1: Int64, _2: Int64)) -> Int64
    = t._1
  operation two() -> (a: Int64, b: Int64)
    = (a: 5, b: 6)
  operation drive() -> Int64
    = get1(two())
end
"#,
        "(_1: Int64, _2: Int64)",
        "(a: Int64, b: Int64)",
    );
}

/// The dual direction, equally unsound: a POSITIONAL value fed to a NAME-keyed
/// parameter, where `t.a` would read `named` — empty for a positional tuple.
/// Measured pre-fix as `Internal("field_access: tuple has no component 'a'")`.
#[test]
fn positional_tuple_does_not_satisfy_name_keyed_param() {
    assert_arg_mismatch(
        r#"
namespace test.wi775c
  import anthill.prelude.{Int64}
  operation get_a(t: (a: Int64, b: Int64)) -> Int64
    = t.a
  operation two() -> (_1: Int64, _2: Int64)
    = (5, 6)
  operation drive() -> Int64
    = get_a(two())
end
"#,
        "(a: Int64, b: Int64)",
        "(_1: Int64, _2: Int64)",
    );
}

/// What must KEEP working on the DATA side: matching keying, both conventions —
/// driven end-to-end, since the bug was invisible at load.
#[test]
fn matching_keying_still_types_and_evals() {
    let src = r#"
namespace test.wi775ok
  import anthill.prelude.{Int64}
  operation get_a(t: (a: Int64, b: Int64)) -> Int64
    = t.a
  operation named_src() -> (a: Int64, b: Int64)
    = (a: 5, b: 6)
  operation drive_named() -> Int64
    = get_a(named_src())

  operation get_1(t: (_1: Int64, _2: Int64)) -> Int64
    = t._1
  operation pos_src() -> (_1: Int64, _2: Int64)
    = (5, 6)
  operation drive_pos() -> Int64
    = get_1(pos_src())
end
"#;
    assert!(
        try_load_kb_with(src).is_ok(),
        "same-keying tuples must still type-check; got: {:?}",
        try_load_kb_with(src).err(),
    );
    let mut interp = interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi775ok.drive_named"), 5, "name-keyed round trip");
    assert_eq!(run_int(&mut interp, "test.wi775ok.drive_pos"), 5, "positional round trip");
}

/// The SAME hole on the `Function[A, B]` surface, which `arrow_parts` decomposes
/// like an arrow. A `Function[A = (acc: Int64, x: Int64), B = Int64]` slot given
/// a two-param op's eta arrow `(_1, _2)` used to load and then trap at eval with
/// `ArityMismatch { expected: 2, got: 1 }` — `A` is the ARGUMENT's data type (it
/// is what flows to `apply(f, x: A)`), not an applied-positionally parameter
/// list, so it aligns by name. Measured on the pre-fix tree; this is why
/// `arrow_function_compatible` deliberately stays on the data-tuple relation.
#[test]
fn function_sort_argument_type_does_not_bridge_keyings() {
    assert_arg_mismatch(
        r#"
namespace test.wi775f
  import anthill.prelude.{Int64, Function}
  operation add2(a: Int64, b: Int64) -> Int64
    = a + b
  operation apply2(f: Function[A = (acc: Int64, x: Int64), B = Int64]) -> Int64
    = f((acc: 1, x: 2))
  operation drive() -> Int64
    = apply2(add2)
end
"#,
        "Function[A = (acc: Int64, x: Int64), B = Int64]",
        "(_1: Int64, _2: Int64) -> Int64",
    );
}

/// `Function` against `Function`, which reaches the alignment through the
/// parameterized-binding walk rather than either arrow path. Pre-fix this loaded
/// and trapped with the very WI-775 error — `field_access: tuple has no
/// component '_1'` — when the positional callee projected the name-keyed value.
#[test]
fn function_vs_function_argument_type_does_not_bridge_keyings() {
    assert_arg_mismatch(
        r#"
namespace test.wi775g
  import anthill.prelude.{Int64, Function}
  operation take(f: Function[A = (acc: Int64, x: Int64), B = Int64]) -> Int64
    = f((acc: 1, x: 2))
  operation give(g: Function[A = (_1: Int64, _2: Int64), B = Int64]) -> Int64
    = take(g)
end
"#,
        "Function[A = (acc: Int64, x: Int64), B = Int64]",
        "Function[A = (_1: Int64, _2: Int64), B = Int64]",
    );
}

/// THE boundary the fix must NOT cross: an arrow's PARAMETER LIST still aligns
/// positionally. `foldLeft`'s callback is declared `f: (acc: Acc, x: xs.T)`
/// (`stdlib/anthill/prelude/list.anthill`), while a two-param op passed for it
/// arrives as the eta arrow `(_1, _2)` — the WI-442 case, and the ONLY consumer
/// of the positional fallback measured across the whole workspace suite. If the
/// data-tuple tightening above leaked into parameter lists, this stops loading.
#[test]
fn arrow_parameter_lists_still_align_positionally() {
    let src = r#"
namespace test.wi775param
  import anthill.prelude.{Int64, List}
  import anthill.prelude.FiniteCollection.{foldLeft}
  operation shift(acc: Int64, x: Int64) -> Int64
    = acc * 10 + x
  operation fold_it() -> Int64
    = foldLeft([1, 2, 3], 0, shift)
end
"#;
    assert!(
        try_load_kb_with(src).is_ok(),
        "a multi-param op's eta arrow `(_1, _2)` must still satisfy a callback \
         declared `(acc, x)`; got: {:?}",
        try_load_kb_with(src).err(),
    );
    let mut interp = interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi775param.fold_it"), 123, "foldLeft shift over [1,2,3]");
}

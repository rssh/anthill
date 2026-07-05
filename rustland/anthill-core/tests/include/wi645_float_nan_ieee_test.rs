//! WI-645 — the interpreter's SEMANTIC Float equality/ordering (`Eq.eq`/`neq`,
//! `Ordered.gt`/`lt`/`gte`/`lte`) must follow IEEE 754 on NaN, matching the C++
//! codegen (`Eq.eq` -> `==`, `Ordered.gt` -> `>`) and the stdlib's own contract
//! (`float.anthill:19-20`: "Float.eq returns false for NaN (NaN != NaN in IEEE)").
//!
//! Today it does NOT: eval `Eq.eq` = `builtin_eq` = `views_structurally_equal`,
//! which compares Float leaves as `OrderedFloat<f64>` ("all NaN values equal";
//! "NaN is the largest"), so `eq(nan,nan)=true`, `neq(nan,nan)=false`,
//! `gt(nan,1.0)=true` — the opposite of the compiled code and the documented
//! contract (same Anthill program, opposite answers by backend).
//!
//! The fix must SPLIT: the STRUCTURAL layer (`===`/`struct_eq`, `Literal` Hash/Eq
//! for hash-consing) stays on `OrderedFloat` — `nan === nan` is structural
//! identity and correctly `true` — while only the SEMANTIC `Eq`/`Ordered` builtins
//! switch to raw-`f64` IEEE compare. `struct_eq_on_nan_stays_structural` guards the
//! first half; `eq_ordered_on_nan_follow_ieee` (ignored until the fix) specifies the
//! second.

fn interp(src: &str) -> anthill_core::eval::Interpreter {
    crate::common::interp_for(src)
}

fn call_bool(i: &mut anthill_core::eval::Interpreter, op: &str) -> bool {
    i.call(op, &[])
        .unwrap_or_else(|e| panic!("call {op}: {e:?}"))
        .as_bool()
        .unwrap_or_else(|| panic!("call {op}: not a Bool"))
}

const SRC: &str = r#"
namespace test.wi645
  import anthill.prelude.{Bool, Float}
  import anthill.prelude.Float.{nan}
  import anthill.prelude.Eq.{eq, neq}
  import anthill.prelude.Ordered.{gt, lt, gte, lte}

  operation eq_nan() -> Bool  = eq(nan, nan)
  operation neq_nan() -> Bool = neq(nan, nan)
  operation gt_nan() -> Bool  = gt(nan, 1.0)
  operation lt_nan() -> Bool  = lt(nan, 1.0)
  operation gte_nan() -> Bool = gte(nan, 1.0)
  operation lte_nan() -> Bool = lte(nan, 1.0)
  operation seq_nan() -> Bool = nan === nan
end
"#;

/// `===` is STRUCTURAL identity — `nan === nan` is `true` and MUST stay so after
/// the IEEE fix (reflection / dedup / hash-consing depend on it). This is the
/// correct, must-not-regress half of WI-645.
#[test]
fn struct_eq_on_nan_stays_structural() {
    let mut i = interp(SRC);
    assert!(
        call_bool(&mut i, "test.wi645.seq_nan"),
        "`nan === nan` must be true (structural identity) — struct_eq stays on OrderedFloat",
    );
}

/// The IEEE target for the SEMANTIC ops. FAILS today (interpreter uses
/// `OrderedFloat`); un-ignore when WI-645 lands.
#[test]
#[ignore = "WI-645: interpreter Float eq/neq/ordered use OrderedFloat, not IEEE — fix pending"]
fn eq_ordered_on_nan_follow_ieee() {
    let mut i = interp(SRC);
    // IEEE 754: a NaN operand makes == false, != true, and every ordering
    // comparison false (NaN is UNORDERED). This is what the C++ codegen already
    // does (`eq`->`==`, `gt`->`>`) and what stdlib float.anthill documents.
    assert!(!call_bool(&mut i, "test.wi645.eq_nan"), "eq(nan, nan) must be false (IEEE)");
    assert!(call_bool(&mut i, "test.wi645.neq_nan"), "neq(nan, nan) must be true (IEEE)");
    assert!(!call_bool(&mut i, "test.wi645.gt_nan"), "gt(nan, 1.0) must be false (IEEE unordered)");
    assert!(!call_bool(&mut i, "test.wi645.lt_nan"), "lt(nan, 1.0) must be false (IEEE unordered)");
    assert!(!call_bool(&mut i, "test.wi645.gte_nan"), "gte(nan, 1.0) must be false (IEEE unordered)");
    assert!(!call_bool(&mut i, "test.wi645.lte_nan"), "lte(nan, 1.0) must be false (IEEE unordered)");
}

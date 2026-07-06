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
//!
//! WI-644 / proposal 004 landed *direction B*: `PartialEq ⊂ Eq` (and `PartialOrd ⊂
//! Ordered`) split; `Float` provides only the PARTIAL bases (`PartialEq`/`PartialOrd`),
//! and its semantic `eq`/`neq`/`gt`/`lt`/… are IEEE (this test). The reflexivity
//! shortcut in `sem_eq_core` and the structural `builtin_eq` are gated to skip a raw
//! Float operand pair (eval `float_ieee_eq`, resolver `value_f64`). `struct_eq`
//! (`===`) stays on `OrderedFloat` — the first test below.

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
  import anthill.prelude.{Bool, Float, TotalFloat}
  import anthill.prelude.TotalFloat.{TotalFloat}
  import anthill.prelude.Float.{nan}
  import anthill.prelude.PartialEq.{eq, neq}
  import anthill.prelude.PartialOrd.{gt, lt, gte, lte}

  -- WI-644: TotalFloat is the LAWFUL (reflexive) wrapper — its structural entity
  -- equality equates all NaNs, so `eq` is reflexive, UNLIKE raw partial Float.
  operation tf_eq_nan() -> Bool = eq(TotalFloat(raw: nan), TotalFloat(raw: nan))

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

/// The IEEE target for the SEMANTIC ops — delivered by WI-644 / proposal 004
/// (direction B: PartialEq/PartialOrd split; Float provides only the partial bases,
/// whose eq/ordering builtins are IEEE).
#[test]
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

/// WI-644 / proposal 004: `TotalFloat` is the LAWFUL wrapper — its equality is
/// structural (entity) equality, which equates all NaNs and IS reflexive. So
/// `eq(TotalFloat(nan), TotalFloat(nan))` is TRUE, the opposite of raw partial
/// `Float`'s IEEE `false` above. This is what makes `TotalFloat` a lawful `Eq` key
/// (`Map[K = TotalFloat]`) while raw `Float` is not.
#[test]
fn totalfloat_eq_is_lawful_reflexive_on_nan() {
    let mut i = interp(SRC);
    assert!(
        call_bool(&mut i, "test.wi645.tf_eq_nan"),
        "eq(TotalFloat(nan), TotalFloat(nan)) must be true — TotalFloat's structural \
         equality is reflexive/total, unlike raw Float's IEEE eq",
    );
}

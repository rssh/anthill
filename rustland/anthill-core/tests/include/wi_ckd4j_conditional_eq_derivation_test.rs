//! WI-20260918-CKD4J — `eq_derive` derives CONDITIONAL `PartialEq`/`Eq` rows for a
//! parametric sort, and reads a composite's parametric-typed field through them.
//!
//! Before this, `eq_derive` derived nothing for a parametric sort (`List`, `Option`,
//! `SortedSet`, a user `Box[T]`) nor for a composite with a parametric-typed field
//! (`holder(o: Option[T = Int64])`), so a `requires Eq` consumer (`List.contains`)
//! refused all five at LOAD (WI-1102's positive discharge) while `eq` on the very same
//! values worked. The derivation now asserts the WI-869 form `pair.anthill` hand-writes —
//! `provides PartialEq[S] :- PartialEq[T]`, `provides Eq[S] :- Eq[T]` — over the
//! parameters a sort's fields mention (`eq_derive::derive_conditional_eq`).
//!
//! ── WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT ──────────────────────────────
//!
//! Removing the `derive_conditional_eq` call from the pipeline fails every row of
//! `the_five_refused_programs_answer`: each program is then the load refusal quoted
//! above. PASS EITHER WAY BY DESIGN:
//! `a_float_element_is_still_refused` is refused before this change for want of any row,
//! and after it because the row is CONDITIONAL — it is the test that FAILS against the
//! naive fix (an unconditional `Eq[List]`), which is what it is for;
//! `pair_keeps_its_written_rows` pins that a carrier that already provides is skipped.

use anthill_core::eval::value::Value;

const PROGRAM: &str = r#"
namespace wickd4j.derive
  import anthill.prelude.{Bool, Int64, List, Option, SortedSet}
  import anthill.prelude.List.{cons, nil, contains}
  import anthill.prelude.Option.{some, none}
  sort Box
    sort T = ?
    entity box(v: T)
  end
  sort Holder
    entity holder(o: Option[T = Int64])
  end
  sort D
    operation boxYes(n: Int64) -> Int64 = if contains(cons(head: box(v: 1), tail: nil), box(v: 1)) then 1 else 0
    operation boxNo(n: Int64) -> Int64 = if contains(cons(head: box(v: 1), tail: nil), box(v: 2)) then 1 else 0
    operation holderYes(n: Int64) -> Int64 = if contains(cons(head: holder(o: some(1)), tail: nil), holder(o: some(1))) then 1 else 0
    operation holderNo(n: Int64) -> Int64 = if contains(cons(head: holder(o: some(1)), tail: nil), holder(o: none)) then 1 else 0
    operation optionYes(n: Int64) -> Int64 = if contains(cons(head: some(1), tail: nil), some(1)) then 1 else 0
    operation optionNo(n: Int64) -> Int64 = if contains(cons(head: some(1), tail: nil), some(2)) then 1 else 0
    operation listYes(n: Int64) -> Int64 =
      if contains(cons(head: cons(head: 1, tail: nil), tail: nil), cons(head: 1, tail: nil)) then 1 else 0
    operation listNo(n: Int64) -> Int64 =
      if contains(cons(head: cons(head: 1, tail: nil), tail: nil), cons(head: 2, tail: nil)) then 1 else 0
    operation sortedSetYes(n: Int64) -> Int64 =
      let a = SortedSet.insert(SortedSet.empty[T = Int64](), 1)
      let b = SortedSet.insert(SortedSet.empty[T = Int64](), 1)
      if contains(cons(head: a, tail: nil), b) then 1 else 0
    operation sortedSetNo(n: Int64) -> Int64 =
      let a = SortedSet.insert(SortedSet.empty[T = Int64](), 1)
      let b = SortedSet.insert(SortedSet.empty[T = Int64](), 2)
      if contains(cons(head: a, tail: nil), b) then 1 else 0
  end
end
"#;

fn eval_int(src: &str, op: &str) -> i64 {
    let mut interp = crate::common::interp_for(src);
    match interp.call(op, &[Value::Int(0)]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{op}: expected an Int, got {other:?}"),
    }
}

fn refusals(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src).err().unwrap_or_default()
}

/// The ticket's five programs, each beside its NEGATIVE TWIN: a `contains` answering
/// `true` vacuously would pass the first row of a pair and fail the second.
#[test]
fn the_five_refused_programs_answer() {
    assert_eq!(refusals(PROGRAM), Vec::<String>::new());
    for case in ["box", "holder", "option", "list", "sortedSet"] {
        assert_eq!(eval_int(PROGRAM, &format!("wickd4j.derive.D.{case}Yes")), 1, "{case}");
        assert_eq!(eval_int(PROGRAM, &format!("wickd4j.derive.D.{case}No")), 0, "{case}");
    }
}

/// THE CONTROL THAT DISTINGUISHES A CONDITIONAL ROW FROM AN UNCONDITIONAL ONE: an element
/// with no lawful equality keeps the container unlawful. `Option[T = Float]` is the row
/// an unconditional `Eq[Option]` would admit.
#[test]
fn a_float_element_is_still_refused() {
    let src = r#"
namespace wickd4j.float
  import anthill.prelude.{Bool, Int64, Float, List, Option}
  import anthill.prelude.List.{cons, nil, contains}
  import anthill.prelude.Option.{some}
  sort D
    operation floats(n: Int64) -> Int64 = if contains(cons(head: 1.5, tail: nil), 1.5) then 1 else 0
    operation options(n: Int64) -> Int64 = if contains(cons(head: some(1.5), tail: nil), some(1.5)) then 1 else 0
  end
end
"#;
    let errs = refusals(src);
    for want in [
        "`anthill.prelude.Eq[T = anthill.prelude.Float]` cannot be supplied",
        "`anthill.prelude.Eq[T = anthill.prelude.Option[T = anthill.prelude.Float]]` cannot be supplied",
    ] {
        assert!(errs.iter().any(|e| e.contains(want)), "want {want}; got {errs:?}");
    }
}

/// A carrier that already provides is SKIPPED: `Pair` writes its own four conditional
/// provisions, and the derivation adds no `PartialEq`/`Eq` clause beside them.
#[test]
fn pair_keeps_its_written_rows() {
    let kb = crate::common::load_kb_with("namespace wickd4j.pair\nend\n");
    let pair = kb.try_resolve_symbol("anthill.prelude.Pair").expect("Pair");
    for spec in ["anthill.prelude.PartialEq", "anthill.prelude.Eq"] {
        let spec_sym = kb.try_resolve_symbol(spec).expect(spec);
        assert_eq!(
            kb.provides_clause_count(pair, spec_sym),
            1,
            "{spec}: one written clause, nothing derived beside it"
        );
    }
}

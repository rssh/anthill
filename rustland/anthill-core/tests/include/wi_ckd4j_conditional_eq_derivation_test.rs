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

// ── The `NonEq` mirror ──────────────────────────────────────────────────────────

/// `NaN` behind a PARAMETRIC constructor, and behind a composite's parametric-typed
/// field, is compared FIELD-WISE, so IEEE's `nan != nan` holds through it. Each row
/// beside a NaN-free twin that must stay equal, and a `TotalFloat` row that must stay
/// equal too — a non-parametric boundary still shields its `Float`.
///
/// CONTROL, measured before the mirror: the four NaN rows ALL answered 1 — the
/// structural shortcut, because the partial-carrier gate stopped at `some` / `cons` /
/// `holder` / `hp` without looking inside. Backing out `partial_transparent_carriers`
/// (the gate walking through a parametric constructor) restores 1 for the `Option` and
/// `List` rows, and for `Holder`'s, whose field IS an `Option`; backing out the argument
/// walk in `composite_field_sorts` leaves `Holder` and `HoldPair` unclassified, so they
/// take the shortcut at their own head.
#[test]
fn nan_behind_a_parametric_type_is_not_equal_to_itself() {
    let src = r#"
namespace wickd4j.nan
  import anthill.prelude.{Bool, Int64, Float, Option, List, Pair, TotalFloat}
  import anthill.prelude.Option.{some}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Pair.{pair}
  import anthill.prelude.Float.{nan}
  import anthill.prelude.PartialEq.{eq}
  sort Holder
    entity holder(o: Option[T = Float])
  end
  sort HoldPair
    entity hp(p: Pair[A = Float, B = Int64])
  end
  sort D
    operation optNan(n: Int64) -> Int64 = if eq(some(nan), some(nan)) then 1 else 0
    operation optOne(n: Int64) -> Int64 = if eq(some(1.0), some(1.0)) then 1 else 0
    operation lstNan(n: Int64) -> Int64 =
      if eq(cons(head: nan, tail: nil), cons(head: nan, tail: nil)) then 1 else 0
    operation lstOne(n: Int64) -> Int64 =
      if eq(cons(head: 1.0, tail: nil), cons(head: 1.0, tail: nil)) then 1 else 0
    operation holderNan(n: Int64) -> Int64 =
      if eq(holder(o: some(nan)), holder(o: some(nan))) then 1 else 0
    operation holderOne(n: Int64) -> Int64 =
      if eq(holder(o: some(1.0)), holder(o: some(1.0))) then 1 else 0
    operation hpNan(n: Int64) -> Int64 =
      if eq(hp(p: pair(fst: nan, snd: 1)), hp(p: pair(fst: nan, snd: 1))) then 1 else 0
    operation hpOne(n: Int64) -> Int64 =
      if eq(hp(p: pair(fst: 1.0, snd: 1)), hp(p: pair(fst: 1.0, snd: 1))) then 1 else 0
    operation optTotal(n: Int64) -> Int64 =
      if eq(some(TotalFloat(raw: nan)), some(TotalFloat(raw: nan))) then 1 else 0
  end
end
"#;
    assert_eq!(refusals(src), Vec::<String>::new());
    for (op, want) in [
        ("optNan", 0),
        ("optOne", 1),
        ("lstNan", 0),
        ("lstOne", 1),
        ("holderNan", 0),
        ("holderOne", 1),
        ("hpNan", 0),
        ("hpOne", 1),
        ("optTotal", 1),
    ] {
        assert_eq!(eval_int(src, &format!("wickd4j.nan.D.{op}")), want, "{op}");
    }
}

/// A composite whose `Float` sits behind a parametric field CLASSIFIES `Partial`: it
/// derives `NonEq`, so a hand-written `provides Eq[Holder]` is refused (`Eq` ⊥
/// `NonEq`, WI-658) — the false claim the mirror exists to catch. CONTROL: the same
/// line over `Option[T = Int64]` loads (that `Holder` is lawful). Before the mirror the
/// first program LOADED: nothing classified `Holder`.
#[test]
fn a_float_behind_a_parametric_field_classifies_partial() {
    let prog = |elem: &str| {
        format!(
            r#"
namespace wickd4j.partial
  import anthill.prelude.{{Int64, Float, Option, Eq}}
  sort Holder
    entity holder(o: Option[T = {elem}])
    provides Eq[T = Holder]
  end
end
"#
        )
    };
    let errs = refusals(&prog("Float"));
    assert!(
        errs.iter().any(|e| e.contains("wickd4j.partial.Holder") && e.contains("NonEq")),
        "a `Float` behind `Option` makes `Holder` NonEq, so `provides Eq` is refused; \
         got {errs:?}"
    );
    assert_eq!(refusals(&prog("Int64")), Vec::<String>::new());
}

/// A `Partial` composite HAS a partial equality, and says so where the typer can read
/// it: `requires PartialEq[X]` at `pt(x: Float)` / `holder(o: Option[T = Float])` loads
/// and answers — 1 on equal values, 0 on NaN. CONTROL: its `PartialEq` row used to be
/// asserted only after the typer, beside the `NonEq` one, and this program was refused
/// at load ("`PartialEq[T = Pt]` cannot be supplied").
#[test]
fn a_partial_composite_satisfies_requires_partial_eq() {
    let src = r#"
namespace wickd4j.pe
  import anthill.prelude.{Bool, Int64, Float, Option, PartialEq}
  import anthill.prelude.Option.{some}
  import anthill.prelude.Float.{nan}
  import anthill.prelude.PartialEq.{eq}
  sort Pt
    entity pt(x: Float)
  end
  sort Holder
    entity holder(o: Option[T = Float])
  end
  sort D
    operation same[X](a: X, b: X) -> Bool requires PartialEq[X] = eq(a, b)
    operation ptOne(n: Int64) -> Int64 = if same(pt(x: 1.0), pt(x: 1.0)) then 1 else 0
    operation ptNan(n: Int64) -> Int64 = if same(pt(x: nan), pt(x: nan)) then 1 else 0
    operation hOne(n: Int64) -> Int64 = if same(holder(o: some(1.0)), holder(o: some(1.0))) then 1 else 0
    operation hNan(n: Int64) -> Int64 = if same(holder(o: some(nan)), holder(o: some(nan))) then 1 else 0
  end
end
"#;
    assert_eq!(refusals(src), Vec::<String>::new());
    for (op, want) in [("ptOne", 1), ("ptNan", 0), ("hOne", 1), ("hNan", 0)] {
        assert_eq!(eval_int(src, &format!("wickd4j.pe.D.{op}")), want, "{op}");
    }
}

//! WI-20261121-TV0PA — A PROVISION OF `Eq` GIVES `PartialEq` UNDER ITS OWN CONDITIONS, OWN OR A
//! WITNESS'S; A WITNESS THAT WRITES `Eq` ALONE SPEAKS FOR ITS CARRIER; AND AN EQUALITY NO `eq`
//! ANSWERS IS REFUSED AT LOAD (filed with the user 2026-11-21).
//!
//! `eq.anthill` says `Eq provides PartialEq[T = T]`: a carrier writing `provides Eq[X]` thereby
//! provides `PartialEq[X]`, one `eq`, one equality. Three things kept that from holding, each
//! MEASURED on c3371cd0 with the programs below:
//!
//! * the forwarded row was derived for an UNCONDITIONAL provision only — `Box provides
//!   Eq[Self] :- Eq[T]` with its own `eq` was refused at `eq(box(v: 1), box(v: 2))`, "`Box`
//!   provides `Eq`, which requires `PartialEq`" (`typing::derive_forwarded_provisions`, which
//!   now copies each clause of the source onto the derived row);
//! * the derivation read which sort a provision is about at the parameter an operation
//!   receives on, and `Eq` declares none — so `sort W { provides Eq[T = C]; operation eq(…) =
//!   true }` was filed under `W`, `C` derived its own equality beside it, and `eq(c(v: 1),
//!   c(v: 2))` answered 0, `W.eq` never called (`eq_derive::spoken_for`, then through
//!   `typing::provisions_about`; since WI-20261121-JE2MT `EqualityProvisions::speak_for`, each
//!   provision read at its carrier by `typing::ProvisionsOfSpec`);
//! * a witness with no `eq` loaded clean and died at the first comparison,
//!   `EqualityWithNoMember` — `PartialEq.eq` is a builtin, which the provider-coverage check
//!   reads as backing every provider (`eq_derive::equality_reaching_no_eq`, a load error).
//!
//! BACK-OUTS, MEASURED 2026-11-21 on the selected binary, one at a time:
//! * the forwarding of a conditioned row backed out (`forwarded_rows_to_derive` skipping a
//!   conditioned carrier row again) FAILS 5:
//!   [`a_conditional_eq_gives_partial_eq_under_its_condition`],
//!   [`a_parametric_witness_of_eq_answers_under_its_condition`],
//!   [`a_conditional_ord_conditions_its_derived_floor`], and the two refusal rows
//!   [`a_witness_with_no_eq_is_refused_at_load`] and
//!   [`an_own_provision_no_member_can_answer_is_refused_naming_what_was_written`] — the check
//!   reads `PartialEq` rows, and a conditional `Eq` then has none;
//! * `spoken_for` read through `provision_carriers_of_spec` again (the witness criterion's
//!   parameter, a helper WI-20261121-JE2MT retired) FAILS 4:
//!   [`a_witness_that_writes_eq_alone_speaks_for_its_carrier`],
//!   [`a_parametric_witness_of_eq_answers_under_its_condition`],
//!   [`a_witness_of_eq_over_a_float_composite_is_its_whole_equality`] and
//!   [`a_witness_with_no_eq_is_refused_at_load`] (its first case loads clean, `C` deriving its
//!   own equality);
//! * `equality_reaching_no_eq` not called FAILS [`a_witness_with_no_eq_is_refused_at_load`],
//!   [`an_own_provision_no_member_can_answer_is_refused_naming_what_was_written`], and the
//!   fixtures elsewhere that now pin the refusal (`wi1098`'s witness row, `wi_cbrd2`'s
//!   parametric row, `wi_szkv7`'s two later-load rows over a refused earlier one);
//! * `written_without_member` asking `provision_is_conditional` of `PartialEq` alone again FAILS
//!   [`an_own_provision_no_member_can_answer_is_refused_naming_what_was_written`] alone (the
//!   refusal says "with no condition" of a provision written with one).
//!
//! [`the_carriers_own_equality_is_unchanged`] passes under all four, by design: the rows that
//! answered before this ticket answer the same.
//!
//! A composite HOLDING a sort whose equality is a witness's (`d(c: C)`) derived no equality, its
//! field's being one the derivation did not read, and a comparison of two `D`s was refused at the
//! call: WI-20261121-DBR8V, `wi_dbr8v_witnessed_field_test`.

use crate::common::{assert_refused_naming, load_errors_of as load_errors, load_kb_with, run_int64};

/// `decls` and an entry `main` answering `call` as 1 (true) or 0 (false). Each `eq` written in a
/// fixture is `= true`, so 1 for two DISTINCT values is that `eq`'s answer and 0 the structural
/// one.
fn program(ns: &str, decls: &str, call: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Eq, PartialEq, NonEq, Int64, Float, Bool}}
  import anthill.prelude.PartialEq.{{eq}}
  {decls}
  operation b(t: Bool) -> Int64 = if t then 1 else 0
  operation main() -> Int64 = b({call})
end
"#
    )
}

fn run(ns: &str, decls: &str, call: &str) -> Result<i64, String> {
    run_int64(&program(ns, decls, call), &format!("{ns}.main"))
}

const BOX_COND_EQ: &str = r#"
  sort Box
    sort T = ?
    entity box(v: T)
    provides Eq[Self] :- Eq[T]
    operation eq(x: Box, y: Box) -> Bool = true
  end
"#;

/// (2) — the carrier's own conditional `Eq` gives `PartialEq` under the same condition: `Box`'s
/// `eq` answers at `Box[Int64]`, and `Box[Float]` has no equality, `Eq[Float]` not holding. RED
/// with the conditioned row not forwarded, at the first assertion: refused "`Box` provides `Eq`,
/// which requires `PartialEq`".
#[test]
fn a_conditional_eq_gives_partial_eq_under_its_condition() {
    let ns = "witv0pa.cond";
    assert_eq!(run(ns, BOX_COND_EQ, "eq(box(v: 1), box(v: 2))"), Ok(1));
    let kb = load_kb_with(&program(ns, BOX_COND_EQ, "eq(box(v: 1), box(v: 2))"));
    let sym = |n: &str| kb.try_resolve_symbol(n).unwrap_or_else(|| panic!("`{n}` resolves"));
    let (bx, pe) = (sym("witv0pa.cond.Box"), sym("anthill.prelude.PartialEq"));
    assert!(
        kb.provision_has_conditions(bx, pe),
        "the `PartialEq` derived from a conditional `Eq` carries its condition"
    );
    assert_refused_naming(
        &load_errors(&program(ns, BOX_COND_EQ, "eq(box(v: 1.5), box(v: 2.5))")),
        &["no impl matches", "anthill.prelude.Eq[T = anthill.prelude.Float]"],
        "a `Box[Float]` comparison, where the condition does not hold",
    );
}

/// (3) — a witness that writes `Eq` alone is `C`'s equality: its `eq` answers, and `C` derives
/// none beside it. RED with `spoken_for` read at the receiving parameter: 0, `C`'s derived
/// structural equality answering instead.
#[test]
fn a_witness_that_writes_eq_alone_speaks_for_its_carrier() {
    let decls = r#"
  sort C
    entity c(v: Int64)
  end
  sort W
    provides Eq[T = C]
    operation eq(x: C, y: C) -> Bool = true
  end
"#;
    assert_eq!(run("witv0pa.wit", decls, "eq(c(v: 1), c(v: 2))"), Ok(1));
}

/// (4) — the parametric witness: `W2`'s `eq` answers at `Box[Int64]`, under its condition, and
/// `Box[Float]` is refused. RED with either of the first two fixes backed out: with the
/// conditioned row not forwarded, refused for the missing `PartialEq[Box[Int64]]`; with
/// `spoken_for` as before, 0 — `Box`'s derived equality.
#[test]
fn a_parametric_witness_of_eq_answers_under_its_condition() {
    let decls = r#"
  sort Box
    sort T = ?
    entity box(v: T)
  end
  sort W2
    sort A = ?
    provides Eq[T = Box[T = A]] :- Eq[T = A]
    operation eq(x: Box[T = A], y: Box[T = A]) -> Bool = true
  end
"#;
    let ns = "witv0pa.pwit";
    assert_eq!(run(ns, decls, "eq(box(v: 1), box(v: 2))"), Ok(1));
    assert_refused_naming(
        &load_errors(&program(ns, decls, "eq(box(v: 1.5), box(v: 2.5))")),
        &["no impl matches", "anthill.prelude.Eq[T = anthill.prelude.Float]"],
        "a `Box[Float]` comparison, where the witness's condition does not hold",
    );
}

/// A witness's lawful `eq` over a composite with a `Float` field is the composite's whole
/// equality: `C` derives neither `PartialEq` nor `NonEq` beside it. RED with `spoken_for` as
/// before: 0, and the KB provided `NonEq` for `C` beside the witness's `Eq` — the two-equality
/// state `EqualityOfEarlierSort` refuses across loads, made in one.
#[test]
fn a_witness_of_eq_over_a_float_composite_is_its_whole_equality() {
    let decls = r#"
  sort C
    entity c(v: Float)
  end
  sort W
    provides Eq[T = C]
    operation eq(x: C, y: C) -> Bool = true
  end
"#;
    let ns = "witv0pa.float";
    let src = program(ns, decls, "eq(c(v: 1.5), c(v: 2.5))");
    assert_eq!(run_int64(&src, &format!("{ns}.main")), Ok(1));
    let kb = load_kb_with(&src);
    let sym = |n: &str| kb.try_resolve_symbol(n).unwrap_or_else(|| panic!("`{n}` resolves"));
    assert!(
        !kb.sort_provides(sym("witv0pa.float.C"), sym("anthill.prelude.NonEq")),
        "`C`'s equality is the witness's lawful one, and no `NonEq` is derived beside it"
    );
}

/// A witness with no `eq` leaves its carrier's equality answered by nothing, and is refused at
/// load — of `Eq`, of `PartialEq`, and parametric. RED with the check not made: each loads clean
/// and the comparison dies at run time, `EqualityWithNoMember`; with `spoken_for` as before, the
/// two `Eq` witnesses load and answer 0 — the carrier's derived equality — and the `PartialEq`
/// one still fails at run time.
#[test]
fn a_witness_with_no_eq_is_refused_at_load() {
    let cases = [
        (
            "witv0pa.noeq_eq",
            "sort C\n    entity c(v: Int64)\n  end\n  sort W\n    provides Eq[T = C]\n  end",
            "eq(c(v: 1), c(v: 2))",
            "witv0pa.noeq_eq.C",
            "witv0pa.noeq_eq.W",
            "anthill.prelude.Eq",
        ),
        (
            "witv0pa.noeq_peq",
            "sort C\n    entity c(v: Int64)\n  end\n  sort W\n    provides PartialEq[T = C]\n  end",
            "eq(c(v: 1), c(v: 2))",
            "witv0pa.noeq_peq.C",
            "witv0pa.noeq_peq.W",
            "anthill.prelude.PartialEq",
        ),
        (
            "witv0pa.noeq_param",
            "sort Box\n    sort T = ?\n    entity box(v: T)\n  end\n  sort W2\n    sort A = ?\n    \
             provides Eq[T = Box[T = A]] :- Eq[T = A]\n  end",
            "eq(box(v: 1), box(v: 2))",
            "witv0pa.noeq_param.Box",
            "witv0pa.noeq_param.W2",
            "anthill.prelude.Eq",
        ),
    ];
    for (ns, decls, call, carrier, witness, spec) in cases {
        assert_refused_naming(
            &load_errors(&program(ns, decls, call)),
            &[
                &format!("`{carrier}`'s equality is provided by the witness `{witness}`'s `provides {spec}[…]`"),
                "no `eq` answers it",
                &format!("give `{witness}` an `operation eq` over `{carrier}`"),
            ],
            &format!("{ns}: a witness with no `eq`"),
        );
    }
}

/// The carrier's own provision, where no member can be derived for it — a condition at another
/// spec than `PartialEq` gives the member's frame no `PartialEq[T]` — is refused at load too,
/// naming the provision written: `provides Eq[Self] :- Eq[T]` was refused as a `PartialEq` "with
/// no condition", and `provides PartialEq[Self] :- Eq[T]` loaded and died at the comparison,
/// `EqualityWithNoMember`. The written shape a member is derived under answers structurally
/// (control). RED with `written_without_member` asking of `PartialEq` alone: the first is refused
/// "with no condition"; with the check not made: the second loads.
#[test]
fn an_own_provision_no_member_can_answer_is_refused_naming_what_was_written() {
    for (ns, provision, spec) in [
        ("witv0pa.own_eq", "provides Eq[Self] :- Eq[T]", "anthill.prelude.Eq"),
        ("witv0pa.own_peq", "provides PartialEq[Self] :- Eq[T]", "anthill.prelude.PartialEq"),
    ] {
        let decls = format!("sort Box\n    sort T = ?\n    entity box(v: T)\n    {provision}\n  end");
        let errs = load_errors(&program(ns, &decls, "eq(box(v: 1), box(v: 2))"));
        assert_refused_naming(
            &errs,
            &[
                &format!("`{ns}.Box`'s equality is provided by its own `provides {spec}[…]`"),
                "(`provides PartialEq[Self] :- PartialEq[T]`)",
            ],
            &format!("{ns}: `{provision}` with no `eq`"),
        );
        assert!(
            !errs.iter().any(|e| e.contains("with no condition")),
            "{ns}: the provision has a condition, and the refusal must not say otherwise: {errs:?}"
        );
    }
    let derived_shape = "sort Box\n    sort T = ?\n    entity box(v: T)\n    \
                         provides PartialEq[Self] :- PartialEq[T]\n    provides Eq[Self] :- Eq[T]\n  end";
    assert_eq!(run("witv0pa.own_shape", derived_shape, "eq(box(v: 1), box(v: 2))"), Ok(0));
}

/// The forwarding is the tower's, not `Eq`'s alone: a conditional `Ord` gives the `WeakOrd` it
/// provides under its condition, so the carrier's `compare` answers through `WeakOrd` at
/// `Foo[Int64]` — the repair `ProvisionConditionsTooWeak` now names for a derived floor
/// (`wi_p5g39_provision_assumptions_test::a_derived_floor_is_told_to_write_its_own_clause`). RED
/// with the conditioned row not forwarded: refused, no `WeakOrd[Foo[Int64]]`.
#[test]
fn a_conditional_ord_conditions_its_derived_floor() {
    let src = r#"
namespace witv0pa.ord
  import anthill.prelude.{PartialEq, Eq, PartialOrd, Ord, WeakOrd, Int64}
  enum Foo
    sort A = ?
    entity foo(a: A)
    provides PartialEq[Self] :- PartialEq[A]
    provides Eq[Self] :- Eq[A]
    provides PartialOrd[Self] :- Ord[A]
    provides Ord[Self] :- Ord[A]
    operation compare(x: Self, y: Self) -> Int64 = 7
  end
  operation main() -> Int64 = WeakOrd.compare(foo(a: 1), foo(a: 2))
end
"#;
    assert_eq!(run_int64(src, "witv0pa.ord.main"), Ok(7));
}

/// CONTROLS, passing either way by design: the carrier's own unconditional `Eq`, with its `eq`
/// (1) and with none (0, the derived member); and a witness that adds the law `Eq` to a
/// carrier's own `PartialEq`, with its `eq` (1) and with the derived member (0) — the
/// carrier's own answers, the witness writing none.
#[test]
fn the_carriers_own_equality_is_unchanged() {
    let cases = [
        ("witv0pa.c1", "sort C\n entity c(v: Int64)\n provides Eq[T = C]\n operation eq(x: C, y: C) -> Bool = true\n end", 1),
        ("witv0pa.c2", "sort C\n entity c(v: Int64)\n provides Eq[T = C]\n end", 0),
        (
            "witv0pa.c3",
            "sort C\n entity c(v: Int64)\n provides PartialEq[T = C]\n operation eq(x: C, y: C) -> Bool = true\n end\n \
             sort W\n provides Eq[T = C]\n end",
            1,
        ),
        ("witv0pa.c4", "sort C\n entity c(v: Int64)\n provides PartialEq[T = C]\n end\n sort W\n provides Eq[T = C]\n end", 0),
    ];
    for (ns, decls, want) in cases {
        assert_eq!(run(ns, decls, "eq(c(v: 1), c(v: 2))"), Ok(want), "{ns}");
    }
}

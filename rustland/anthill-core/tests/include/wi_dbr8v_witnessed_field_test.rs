//! WI-20261121-DBR8V — A COMPOSITE HOLDING A SORT WHOSE EQUALITY IS A WITNESS'S DERIVES ITS
//! EQUALITY THROUGH THE WITNESS (filed with the user 2026-11-21).
//!
//! `kernel-language.md` §8.3 says the load "derives the same for every composite holding" a
//! sort a witness speaks for. It derived nothing: the derivation read a field's equality from
//! the provisions filed under the field's own sort, and a witness's row is filed under the
//! witness. MEASURED on 31b367def, with the programs below:
//!
//! * `d(c: C)` beside `sort W { provides Eq[T = C]; operation eq(…) = true }` — and beside a
//!   `PartialEq` witness alike — derived `D` no equality, and `eq(d(…), d(…))` was refused at the
//!   call, "`D` provides no `PartialEq`" (`EqualityProvisions::witnessed`, read by both halves of
//!   the derivation then: `total_composites` and `field_conditions`, one since WI-20261102-YX17K);
//! * with a `Float` inside `C`, the classifier did not see the witness's `eq`: the `PartialEq` row
//!   `Eq provides PartialEq[T = T]` forwards was written below it, and `W.eq` was judged at `W`
//!   alone, where it fits nothing. So `C` was `Partial`, `D` with it, and `D` — a candidate for
//!   `PartialEq` alone — was derived `NonEq` beside the witness's lawful `eq` once the field was
//!   read through an `Eq` row (MEASURED on a first cut of this ticket). The forwarding of the
//!   written rows now runs before the first sort-operations table (`load::load_phase_inner`);
//! * a conditional parametric witness, `W2 provides Eq[T = Box[T = A]] :- Eq[T = A]`, left a field
//!   `Box[T = X]` undecided. It is read through its binding: the field needs `Eq[X]`
//!   (`eq_derive::witness_needs`). A witness at one application (`Box[T = Int64]`) still leaves
//!   the field undecided, and the holder's comparison is refused at the call.
//!
//! BACK-OUTS, MEASURED 2026-11-23 on the selected binary, one at a time:
//! * the witness read backed out (`EqualityProvisions::witnessed` answering `None`) FAILS
//!   [`a_holder_of_an_eq_witnessed_sort_derives_through_the_witness`],
//!   [`a_holder_of_a_partial_eq_witnessed_sort_derives_partial_eq`],
//!   [`a_float_inside_a_witnessed_sort_leaves_its_holder_lawful`],
//!   [`a_conditional_parametric_witness_is_read_through_its_binding`] and
//!   [`an_unconditional_parametric_witness_decides_the_field_outright`];
//! * a parametric witness not translated (`witness_needs` answering `None` at a sort with
//!   parameters) FAILS [`a_conditional_parametric_witness_is_read_through_its_binding`] and
//!   [`an_unconditional_parametric_witness_decides_the_field_outright`];
//! * the forwarding of the written rows not run ahead of the table FAILS
//!   [`a_float_inside_a_witnessed_sort_leaves_its_holder_lawful`],
//!   [`a_conditional_parametric_witness_is_read_through_its_binding`] and
//!   [`an_unconditional_parametric_witness_decides_the_field_outright`], each refused at the
//!   call: an `Eq`-only witness has no `PartialEq` row yet when a field is read for `PartialEq`,
//!   and the `Float` holder, `Partial` with `C` undecided, is a candidate for nothing else;
//! * the `NonEq` mirror keeping a clause beside `Eq` at its parameter FAILS
//!   [`a_conditional_parametric_witness_is_read_through_its_binding`] and
//!   [`a_holder_partial_nowhere_derives_no_noneq`] (each holder provides a `NonEq` that holds
//!   nowhere).
//!
//! [`a_witness_at_one_application_leaves_its_holder_undecided`] and
//! [`a_holder_of_a_derived_equality_is_unchanged`] pass under all four, by design.

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

/// Which of `Eq`, `PartialEq` and `NonEq` the sort `ns.sort` provides, in that order, over the
/// program `decls` with a `main` that compares nothing.
fn equality_of(ns: &str, decls: &str, sort: &str) -> Vec<&'static str> {
    let kb = load_kb_with(&program(ns, decls, "true"));
    let sym = |n: &str| kb.try_resolve_symbol(n).unwrap_or_else(|| panic!("`{n}` resolves"));
    let carrier = sym(&format!("{ns}.{sort}"));
    ["Eq", "PartialEq", "NonEq"]
        .into_iter()
        .filter(|spec| kb.sort_provides(carrier, sym(&format!("anthill.prelude.{spec}"))))
        .collect()
}

/// `C` and its holder `D`, with `C`'s field of type `field`.
fn holder(field: &str) -> String {
    format!("sort C\n    entity c(v: {field})\n  end\n  sort D\n    entity d(c: C)\n  end")
}

/// A witness `W` giving `C` its `spec` equality, with an `eq` that answers true.
fn witness(spec: &str) -> String {
    format!("sort W\n    provides {spec}[T = C]\n    operation eq(x: C, y: C) -> Bool = true\n  end")
}

/// The ticket's program: `D`'s derived `eq` compares `c` through `W.eq`, so two `D`s whose `C`s
/// differ are equal, and `D` is lawful as `C` is. RED with the witness read backed out: refused at
/// the call, "`D` provides no `PartialEq`".
#[test]
fn a_holder_of_an_eq_witnessed_sort_derives_through_the_witness() {
    let (ns, decls) = ("widbr8v.eq", format!("{}\n  {}", holder("Int64"), witness("Eq")));
    assert_eq!(run(ns, &decls, "eq(d(c: c(v: 1)), d(c: c(v: 2)))"), Ok(1));
    assert_eq!(equality_of(ns, &decls, "D"), ["Eq", "PartialEq"]);
}

/// A `PartialEq` witness gives `D` the `PartialEq` it gives `C`, and no `Eq`: `C` has none. RED
/// with the witness read backed out, as above.
#[test]
fn a_holder_of_a_partial_eq_witnessed_sort_derives_partial_eq() {
    let (ns, decls) = ("widbr8v.peq", format!("{}\n  {}", holder("Int64"), witness("PartialEq")));
    assert_eq!(run(ns, &decls, "eq(d(c: c(v: 1)), d(c: c(v: 2)))"), Ok(1));
    assert_eq!(equality_of(ns, &decls, "D"), ["PartialEq"]);
}

/// A `Float` inside `C` is behind the witness's lawful `eq`, so `D` is lawful too: `Eq`, and no
/// `NonEq` beside it. RED with the witness read backed out, or the written rows forwarded below
/// the classifier: refused at the call.
#[test]
fn a_float_inside_a_witnessed_sort_leaves_its_holder_lawful() {
    let (ns, decls) = ("widbr8v.float", format!("{}\n  {}", holder("Float"), witness("Eq")));
    assert_eq!(run(ns, &decls, "eq(d(c: c(v: 1.5)), d(c: c(v: 2.5)))"), Ok(1));
    assert_eq!(equality_of(ns, &decls, "D"), ["Eq", "PartialEq"]);
    assert!(equality_of(ns, &decls, "C").is_empty(), "`C`'s equality is the witness's alone");
}

const BOX_COND_WITNESS: &str = r#"
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

/// A conditional parametric witness is read through its binding: a field `Box[T = X]` needs
/// `Eq[X]`. At `Int64` the holder answers through `W2.eq`, monomorphic or parametric; at `Float`
/// it is refused where `W2`'s condition fails; and the parametric holder's `PartialEq` carries the
/// condition, with no `NonEq` beside it — where `Eq[U]` fails it has no equality at all. RED with
/// the witness read or its translation backed out, or the written rows forwarded below the
/// classifier: refused at the first call; with the `NonEq` mirror's clause kept: `H` provides
/// `NonEq`.
#[test]
fn a_conditional_parametric_witness_is_read_through_its_binding() {
    let mono = format!("{BOX_COND_WITNESS}  sort H\n    entity h(b: Box[T = Int64])\n  end");
    assert_eq!(run("widbr8v.cmono", &mono, "eq(h(b: box(v: 1)), h(b: box(v: 2)))"), Ok(1));
    assert_eq!(equality_of("widbr8v.cmono", &mono, "H"), ["Eq", "PartialEq"]);
    let poly = format!("{BOX_COND_WITNESS}  sort H\n    sort U = ?\n    entity h(b: Box[T = U])\n  end");
    assert_eq!(run("widbr8v.cpoly", &poly, "eq(h(b: box(v: 1)), h(b: box(v: 2)))"), Ok(1));
    assert_refused_naming(
        &load_errors(&program("widbr8v.cpoly", &poly, "eq(h(b: box(v: 1.5)), h(b: box(v: 2.5)))")),
        &["no impl matches", "anthill.prelude.Eq[T = anthill.prelude.Float]"],
        "an `H[Float]` comparison, where `W2`'s condition does not hold",
    );
    assert_eq!(equality_of("widbr8v.cpoly", &poly, "H"), ["Eq", "PartialEq"]);
    let kb = load_kb_with(&program("widbr8v.cpoly", &poly, "true"));
    let sym = |n: &str| kb.try_resolve_symbol(n).unwrap_or_else(|| panic!("`{n}` resolves"));
    assert!(
        kb.provision_has_conditions(sym("widbr8v.cpoly.H"), sym("anthill.prelude.PartialEq")),
        "`H`'s `PartialEq` holds under `W2`'s condition, at `U`"
    );
}

/// A parametric witness with no condition decides the field at every argument. RED with the
/// witness read or its translation backed out, or the written rows forwarded below the
/// classifier: refused at the call.
#[test]
fn an_unconditional_parametric_witness_decides_the_field_outright() {
    let decls = r#"
  sort Box
    sort T = ?
    entity box(v: T)
  end
  sort W3
    sort A = ?
    provides Eq[T = Box[T = A]]
    operation eq(x: Box[T = A], y: Box[T = A]) -> Bool = true
  end
  sort H
    sort U = ?
    entity h(b: Box[T = U])
  end
"#;
    assert_eq!(run("widbr8v.upoly", decls, "eq(h(b: box(v: 1)), h(b: box(v: 2)))"), Ok(1));
}

/// A witness at ONE application of a parametric sort (`Box[T = Int64]`) is not translated: a
/// field's arguments would have to match the application, not condition it. The holder derives
/// nothing and its comparison is refused at the call, while the witness answers a direct one
/// (control). Passes with every back-out, by design: this is the shape left undecided.
#[test]
fn a_witness_at_one_application_leaves_its_holder_undecided() {
    let witness = r#"
  sort Box
    sort T = ?
    entity box(v: T)
  end
  sort W4
    provides Eq[T = Box[T = Int64]]
    operation eq(x: Box[T = Int64], y: Box[T = Int64]) -> Bool = true
  end
"#;
    assert_eq!(run("widbr8v.ground", witness, "eq(box(v: 1), box(v: 2))"), Ok(1));
    let decls = format!("{witness}  sort H\n    entity h(b: Box[T = Int64])\n  end");
    assert_refused_naming(
        &load_errors(&program("widbr8v.ground", &decls, "eq(h(b: box(v: 1)), h(b: box(v: 2)))")),
        &["`widbr8v.ground.H` provides no `anthill.prelude.PartialEq`"],
        "a holder of a field the witness does not decide",
    );
}

/// A holder of a sort whose equality is its own derived one compares structurally, as before.
/// Passes with every back-out, by design.
#[test]
fn a_holder_of_a_derived_equality_is_unchanged() {
    let decls = holder("Int64");
    assert_eq!(run("widbr8v.own", &decls, "eq(d(c: c(v: 1)), d(c: c(v: 2)))"), Ok(0));
    assert_eq!(run("widbr8v.own", &decls, "eq(d(c: c(v: 1)), d(c: c(v: 1)))"), Ok(1));
}

/// The `NonEq` mirror gives no clause at a parameter whose `Eq` the holder's `PartialEq` needs:
/// `NonEq[T]` beside `Eq[T]` holds nowhere. A field of a sort that requires `Eq` of its argument
/// (`Set[T = T]`) is such a parameter, with no witness involved: `S` provided `NonEq :- NonEq[T],
/// Eq[T]` before this ticket. RED with the clause kept: `S` provides `NonEq`.
#[test]
fn a_holder_partial_nowhere_derives_no_noneq() {
    let decls = "sort S\n    sort T = ?\n    entity s(xs: anthill.prelude.Set[T = T])\n  end";
    assert_eq!(equality_of("widbr8v.set", decls, "S"), ["Eq", "PartialEq"]);
}

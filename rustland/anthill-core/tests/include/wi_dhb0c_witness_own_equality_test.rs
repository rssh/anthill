//! WI-20261126-DHB0C — A WITNESS'S `eq` WRITTEN FOR THE SORT IT WITNESSES IS NOT ITS OWN EQUALITY
//! (kernel-language §8.7, *A member that does not fit is no supplier*; decided with the user
//! 2026-11-26: the load is refused, and the refusal says how to write it).
//!
//! `W` has values (`entity w(n: Int64)`) and witnesses `Other`'s equality — `provides
//! PartialEq[T = Other]`, `provides Eq[T = Other]` — through `operation eq(a: Other, b:
//! Other)`. The verdict on whether a carrier's member supplies its own `eq` was reached "at one
//! of" the provisions dispatching to it, the carrier's witness provisions among them, and `W.eq`
//! fits at `PartialEq[T = Other]`. So `W.eq` was read as `W`'s own equality: `W` was a boundary of
//! the derivation, nothing was derived for it, and `eq(w(n: 1), w(n: 2))` was refused at load,
//! "no impl matches — unresolved: PartialEq[T = W]" (MEASURED before the change, the first row's
//! program).
//!
//! Now a carrier's member is judged at the provisions about its OWN values, or at the carrier
//! where there are none; its witness provisions are judged per carrier witnessed
//! (WI-20261126-Q1WE9). `W.eq` supplies `W` nothing, `W` derives its equality, and its written
//! `eq` holds the name the derived member is declared under — NNQ1S's refused `eq`, refused in the
//! comparison's words, with a clause naming the witness provision it does fit and the fix. The
//! same `W` with its member named `oeq` and bound loads, and is the second row.
//!
//! THE READERS MOVED WITH IT: every reader that took a witness's member through
//! `carrier_own_op` — the provider's verdict about its own values — reads the verdict at the
//! carrier it witnesses (`typing::witness_own_op`, `typing::provision_own_op`), or the member its
//! name reaches where that is the question (`typing::member_declared_under`). A witness with no
//! values of its own has a member that fits nowhere its own values are compared; read through
//! `carrier_own_op` it gave `Other` no `eq`.
//!
//! WHAT FAILS WHEN (each measured by making the change and running this file and the Q1WE9 rows):
//!
//! * the carrier's own witness provisions counted again in `member_fits_spec_op`: the first row
//!   (the "no impl matches" refusal, no NNQ1S text).
//! * `witness_own_op` read through `carrier_own_op`: the third row and
//!   `wi_q1we9_witness_member_fit_test::a_witness_whose_eq_takes_the_witnessed_values_still_answers`
//!   (`Other`'s `eq` no member, `EqualityReachesNoEq`).
//! * the NNQ1S refusal asked at a witness provision too (`p.witness.is_none()` dropped): the first
//!   row — the comparison at `PartialEq[T = Other]` refuses nothing, and the once-per-carrier mark
//!   then silences the refusal at `W`'s derived row.
//! * the witness clause left off (`eq_fits_only_as_a_witness` answering `None`): the first row.
//!
//! PASS EITHER WAY, BY DESIGN: [`the_same_member_renamed_and_bound_answers_both_sorts`] (the
//! ticket's control, unchanged) and [`an_eq_that_fits_nothing_is_refused_without_a_witness_clause`]
//! (NNQ1S's refusal, which the clause must not reach).
//!
//! TWO FINDINGS OF THE SAME KIND, FOLDED IN (decided with the user, 2026-11-26), in the second
//! half of this file — a reader taking a witness's provision as its provider's own:
//!
//! 1. THE DERIVATION read "`W` provides `PartialEq`" off `W`'s witness rows (`sort_provides`, keyed
//!    by provider), so which specs `W` witnessed decided whether its own values had an equality.
//!    It asks `typing::sort_provides_for_itself` now, whose "own" is `typing::provision_is_own`,
//!    the one owner `provision_carrier` reads too.
//! 2. AN OPERATION BINDING ON `Eq` was dropped by the forwarding to `PartialEq`, and read by the
//!    eq-dispatch index as the provider's own. The forwarding carries it to the floor that
//!    declares the operation, the index sweeps `PartialEq`'s rows alone, and a binding that names
//!    no parameter and no operation is refused where it is written
//!    (`typing::check_provision_binding_names`).
//!
//! And a third reader of the kind, found by the rows: the `Eq`/`NonEq` exclusion
//! (`typing::check_eq_noneq_exclusive`) counted a witness's `Eq[T = Other]` for the witness.
//!
//! WHAT FAILS WHEN, the second half (measured as the first):
//!
//! * the derivation asking `sort_provides` again: [`a_witness_of_partial_eq_alone_still_derives_its_own_equality`].
//! * the carry left off: the six rows that bind `eq` on an `Eq` line.
//! * the eq-dispatch index sweeping `Eq`'s rows again: the three of them that witness `Other`.
//! * the binding-name check left off: [`a_binding_that_names_nothing_is_refused`].
//! * "own" read through `witness_dispatch_carrier`, or the exclusion keyed by provider again:
//!   [`a_partial_witness_of_eq_derives_its_own_partial_equality`].
//! * the exclusion skipping witness rows (not judging them at the carrier they name):
//!   [`a_witness_eq_at_a_noneq_carrier_is_refused`].
//!
//! On the tree before (MEASURED, this file and the Q1WE9 rows over its sources), nine rows fail
//! and nine pass: the controls above, the valueless witness (the reader move is what keeps it),
//! [`a_witness_of_both_specs_derives_its_own_equality`] (by design — the answers it had), and
//! Q1WE9's rows.

use anthill_core::eval::value::Value;
use anthill_core::eval::{self, Interpreter};
use anthill_core::kb::KnowledgeBase;

use crate::common::{assert_refused_naming, load_errors_of, try_load_kb_with_files};

/// `W`, with values, witnessing `Other`'s equality: `w_member` among its declarations, and
/// `binding` written into its `PartialEq` provision (`""` for none). The probes compare two `W`s
/// that differ, two that do not, and two `Other`s that differ.
fn program(ns: &str, w_member: &str, binding: &str) -> String {
    format!(
        "namespace test.dhb0c.{ns}\n  import anthill.prelude.{{Eq, PartialEq, Int64, Bool}}\n  \
         sort Other\n    entity o(n: Int64)\n  end\n  \
         sort W\n    entity w(n: Int64)\n    provides PartialEq[T = Other{binding}]\n    \
         provides Eq[T = Other]\n    {w_member}\n  end\n  \
         sort Check\n    import anthill.prelude.PartialEq.{{eq}}\n    \
         operation ws() -> Bool = eq(W.w(n: 1), W.w(n: 2))\n    \
         operation wsame() -> Bool = eq(W.w(n: 1), W.w(n: 1))\n    \
         operation other() -> Bool = eq(Other.o(n: 1), Other.o(n: 2))\n  end\nend\n"
    )
}

fn bool_of(kb: KnowledgeBase, op: &str) -> bool {
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp);
    match interp.call(op, &anthill_core::eval::HostValue::all(&[])).map(|h| h.value) {
        Ok(Value::Bool(b)) => b,
        other => panic!("`{op}` did not run to a Bool: {other:?}"),
    }
}

/// THE TICKET'S PROGRAM: `W.eq(a: Other, b: Other)` is no equality of `W`'s values, and it holds
/// the name `W`'s derived one is declared under — refused as NNQ1S refuses an `eq` that does not
/// fit, and the refusal names the witness provision it does fit, and the fix. It was refused at
/// the two calls comparing `W`s instead, "no impl matches — unresolved: PartialEq[T = W]".
#[test]
fn a_witness_with_values_whose_eq_takes_the_witnessed_values_is_refused() {
    let ns = "ticket";
    let errors = load_errors_of(&program(ns, "operation eq(a: Other, b: Other) -> Bool = true", ""));
    assert_refused_naming(
        &errors,
        &[
            "'test.dhb0c.ticket.W' provides 'anthill.prelude.PartialEq' but its own member 'eq' \
             does not fit 'anthill.prelude.PartialEq.eq'",
            "parameter 1 is `Other` where the spec's is `W`",
            "It fits `W`'s provision of `PartialEq` for `Other`, where it answers that sort's \
             equality",
            "Give the member another name and bind it in that provision (`eq = W.<name>`)",
        ],
        "`W`'s `eq` is `Other`'s equality, not `W`'s",
    );
    assert!(
        !errors.iter().any(|e| e.contains("no impl matches")),
        "refused at the member, not at the calls: {errors:#?}"
    );
}

/// THE CONTROL: the same member named `oeq` and bound by the provision. `W`'s equality is derived
/// — two `W`s that differ are not equal, two that do not are — and `Other`'s is `oeq`, `true`
/// where the fields differ. Passes either way by design.
#[test]
fn the_same_member_renamed_and_bound_answers_both_sorts() {
    let ns = "control";
    let src = program(ns, "operation oeq(a: Other, b: Other) -> Bool = true", ", eq = W.oeq");
    let kb = try_load_kb_with_files(&[src.as_str()]).unwrap_or_else(|e| panic!("must load: {e:#?}"));
    let at = |op: &str| format!("test.dhb0c.{ns}.Check.{op}");
    assert!(!bool_of(kb.deep_clone().expect("copy"), &at("ws")), "`W`'s derived equality");
    assert!(bool_of(kb.deep_clone().expect("copy"), &at("wsame")), "`W`'s derived equality");
    assert!(bool_of(kb, &at("other")), "`Other`'s equality is the bound `oeq`");
}

/// A WITNESS WITH NO VALUES OF ITS OWN still answers `Other`'s equality with its `eq`, through a
/// call that names the spec and through one that reaches `Other`'s `PartialEq` as a requirement
/// (the dictionary's suppliers). Its member fits nowhere its own values are compared — it has
/// none — and the witness route reads the verdict at `Other`'s provision. Read through the
/// provider's own verdict, `Other` had no `eq` and the load was refused.
#[test]
fn a_valueless_witness_answers_the_witnessed_sort_with_its_eq() {
    let src = "namespace test.dhb0c.vl\n  import anthill.prelude.{Eq, PartialEq, Int64, Bool}\n  \
               import anthill.prelude.PartialEq.{eq}\n  \
               sort Other\n    entity o(n: Int64)\n  end\n  \
               sort W\n    provides PartialEq[T = Other]\n    provides Eq[T = Other]\n    \
               operation eq(a: Other, b: Other) -> Bool = true\n  end\n  \
               sort Same\n    sort T = ?\n    requires PartialEq[T]\n    \
               operation same(a: T, b: T) -> Bool = eq(a, b)\n  end\n  \
               sort Check\n    \
               operation other() -> Bool = eq(Other.o(n: 1), Other.o(n: 2))\n    \
               operation generic() -> Bool = Same.same(Other.o(n: 1), Other.o(n: 2))\n  end\nend\n";
    let kb = try_load_kb_with_files(&[src]).unwrap_or_else(|e| panic!("must load: {e:#?}"));
    assert!(bool_of(kb.deep_clone().expect("copy"), "test.dhb0c.vl.Check.other"), "`W.eq` answers `Other`");
    assert!(bool_of(kb, "test.dhb0c.vl.Check.generic"), "`W.eq` answers `Other` through `requires`");
}

/// NNQ1S's refusal where the member fits no witness provision: no clause about one. Passes either
/// way by design — the control that the clause is asked only where the member fits one.
#[test]
fn an_eq_that_fits_nothing_is_refused_without_a_witness_clause() {
    let src = "namespace test.dhb0c.plain\n  import anthill.prelude.{Int64, Bool}\n  \
               sort P\n    entity p(x: Int64)\n    operation eq(a: Int64, b: Int64) -> Bool = true\n  end\n\
               end\n";
    let errors = load_errors_of(src);
    assert_refused_naming(
        &errors,
        &[
            "'test.dhb0c.plain.P' provides 'anthill.prelude.PartialEq' but its own member 'eq' \
             does not fit",
            "parameter 1 is `Int64` where the spec's is `P`",
        ],
        "an `eq` over two `Int64`s",
    );
    assert!(
        !errors.iter().any(|e| e.contains("It fits")),
        "no witness provision to name: {errors:#?}"
    );
}


// ── THE TWO FINDINGS FOLDED IN (decided with the user, 2026-11-26) ──────────────────────────────
//
// Each program below is `W`, with values, witnessing `Other`'s equality through a member named
// `oeq` that a binding names; what varies is WHICH line carries the binding and which lines are
// written. The probes are the first rows': `ws()` two `W`s that differ, `wsame()` two that do
// not, `other()` two `Other`s that differ.

/// `W` with `w_body` as its declarations, beside `Other` and the probes.
fn witness_program(ns: &str, w_body: &str) -> String {
    format!(
        "namespace test.dhb0c.{ns}\n  import anthill.prelude.{{Eq, PartialEq, Int64, Bool}}\n  \
         sort Other\n    entity o(n: Int64)\n  end\n  \
         sort W\n    entity w(n: Int64)\n{w_body}\n    \
         operation oeq(a: Other, b: Other) -> Bool = true\n  end\n  \
         sort Check\n    import anthill.prelude.PartialEq.{{eq}}\n    \
         operation ws() -> Bool = eq(W.w(n: 1), W.w(n: 2))\n    \
         operation wsame() -> Bool = eq(W.w(n: 1), W.w(n: 1))\n    \
         operation other() -> Bool = eq(Other.o(n: 1), Other.o(n: 2))\n  end\nend\n"
    )
}

/// `(ws(), wsame(), other())` of a program that must load.
fn probes(ns: &str, w_body: &str) -> (bool, bool, bool) {
    let src = witness_program(ns, w_body);
    let kb = try_load_kb_with_files(&[src.as_str()]).unwrap_or_else(|e| panic!("{ns} must load: {e:#?}"));
    let at = |op: &str| format!("test.dhb0c.{ns}.Check.{op}");
    (
        bool_of(kb.deep_clone().expect("copy"), &at("ws")),
        bool_of(kb.deep_clone().expect("copy"), &at("wsame")),
        bool_of(kb, &at("other")),
    )
}

/// `W`'s values compared by their derived equality, `Other`'s by the bound `oeq`.
const DERIVED_AND_BOUND: (bool, bool, bool) = (false, true, true);

/// FINDING 2 — WHICH SPECS A SORT WITNESSES DOES NOT DECIDE ITS OWN EQUALITY. With only the
/// `PartialEq` line, `W`'s own values were derived nothing — the derivation read `W provides
/// PartialEq[T = Other]` as `W` already providing its own (`sort_provides`, keyed by provider) —
/// and `eq(w(n: 1), w(n: 2))` was refused, "unresolved: PartialEq[T = W]". With the `Eq` line
/// beside it `W` had one, through a `Hash[T = W]` that `derive_hash` gave it on reading `W
/// provides Eq[T = Other]` as its own, and the forwarding from that.
#[test]
fn a_witness_of_partial_eq_alone_still_derives_its_own_equality() {
    let body = "    provides PartialEq[T = Other, eq = W.oeq]";
    assert_eq!(probes("peqonly", body), DERIVED_AND_BOUND);
}

/// The same with the `Eq` line written too: the answers it had, no longer by the `Hash` route.
/// Passes either way by design.
#[test]
fn a_witness_of_both_specs_derives_its_own_equality() {
    let body = "    provides PartialEq[T = Other, eq = W.oeq]\n    provides Eq[T = Other]";
    assert_eq!(probes("both", body), DERIVED_AND_BOUND);
}

/// FINDING 1 — AN OPERATION BINDING GOES WITH THE FORWARDING TO THE FLOOR THAT DECLARES IT. `eq =
/// W.oeq` written on `Eq`, the only line: the `PartialEq[T = Other]` row the forwarding derives
/// carries it. Before, the derived row dropped it — the load refused "no `eq` answers it: none is
/// written" — and the eq-dispatch index, sweeping `Eq`'s rows too, read the binding as `W`'s own
/// (`Eq` declares no operation receiving on `T`, so its row was no witness's), so `W` was a
/// boundary and its own values were refused as well.
#[test]
fn an_eq_bound_on_the_eq_line_answers_the_witnessed_sort() {
    let body = "    provides Eq[T = Other, eq = W.oeq]";
    assert_eq!(probes("eqline", body), DERIVED_AND_BOUND);
}

/// The binding on `Eq` beside a `PartialEq` line that binds none: one provider's rows of one spec
/// at one application are one dictionary, and the derived row's `eq` is in it.
#[test]
fn an_eq_bound_on_the_eq_line_beside_an_unbound_partial_eq_answers() {
    let body = "    provides PartialEq[T = Other]\n    provides Eq[T = Other, eq = W.oeq]";
    assert_eq!(probes("split", body), DERIVED_AND_BOUND);
}

/// The same `eq` bound on both lines is one binding; two different ones are a tie, refused as two
/// bindings of one operation are.
#[test]
fn an_eq_bound_twice_is_one_binding_and_two_are_a_tie() {
    let body = "    provides PartialEq[T = Other, eq = W.oeq]\n    provides Eq[T = Other, eq = W.oeq]";
    assert_eq!(probes("agree", body), DERIVED_AND_BOUND);
    let clash = "    provides PartialEq[T = Other, eq = W.oeq]\n    provides Eq[T = Other, eq = W.peq]\n    \
                 operation peq(a: Other, b: Other) -> Bool = false";
    assert_refused_naming(
        &load_errors_of(&witness_program("clash", clash)),
        &["2 distinct `eq` implementations for carrier 'test.dhb0c.clash.Other'", "W.oeq", "W.peq"],
        "two `eq`s bound for `Other`",
    );
}

/// A carrier writing its own `PartialEq` with no binding, and binding its `eq` on its `Eq` line:
/// the carried binding answers, and no derived member stands beside it — the two rows are one
/// application, one dictionary (found by review: a tie was the risk). Fails with the carry backed
/// out.
#[test]
fn a_carriers_eq_bound_on_its_eq_line_beside_its_unbound_partial_eq_answers() {
    let src = "namespace test.dhb0c.ownsplit\n  import anthill.prelude.{Eq, PartialEq, Int64, Bool}\n  \
               sort C\n    entity c(n: Int64)\n    provides PartialEq[T = C]\n    \
               provides Eq[T = C, eq = C.ceq]\n    operation ceq(a: C, b: C) -> Bool = true\n  end\n  \
               sort Check\n    import anthill.prelude.PartialEq.{eq}\n    \
               operation d() -> Bool = eq(C.c(n: 1), C.c(n: 2))\n  end\nend\n";
    let kb = try_load_kb_with_files(&[src]).unwrap_or_else(|e| panic!("must load: {e:#?}"));
    assert!(bool_of(kb, "test.dhb0c.ownsplit.Check.d"), "`C`'s `eq` is the bound `ceq`");
}

/// A carrier binding its OWN `eq` on its `Eq` line: the binding answers its own values. MEASURED
/// on the tree before: it LOADED and died at the call, `EqualityWithNoMember` — the forwarded
/// `PartialEq[T = W]` row had no `eq`, and the typed call reached no member. Fails with the carry
/// backed out.
#[test]
fn an_eq_bound_on_a_carriers_own_eq_line_answers_it() {
    let src = "namespace test.dhb0c.selfeq\n  import anthill.prelude.{Eq, PartialEq, Int64, Bool}\n  \
               sort W\n    entity w(n: Int64)\n    provides Eq[T = W, eq = W.weq]\n    \
               operation weq(a: W, b: W) -> Bool = true\n  end\n  \
               sort Check\n    import anthill.prelude.PartialEq.{eq}\n    \
               operation ws() -> Bool = eq(W.w(n: 1), W.w(n: 2))\n  end\nend\n";
    let kb = try_load_kb_with_files(&[src]).unwrap_or_else(|e| panic!("must load: {e:#?}"));
    assert!(bool_of(kb, "test.dhb0c.selfeq.Check.ws"), "`W`'s `eq` is the bound `weq`");
}

/// A BINDING THAT NAMES NOTHING IS REFUSED where it is written. `foo = W.oeq` loaded, the binding
/// read by nothing, and the load was refused downstream for the `eq` it left out — naming the
/// absence, not the name.
#[test]
fn a_binding_that_names_nothing_is_refused() {
    let body = "    provides PartialEq[T = Other, foo = W.oeq]\n    provides Eq[T = Other]";
    assert_refused_naming(
        &load_errors_of(&witness_program("foo", body)),
        &[
            "`provides anthill.prelude.PartialEq[…]` on `test.dhb0c.foo.W` binds `foo`, which is no \
             parameter of `anthill.prelude.PartialEq` and no operation of it or of a spec it provides",
            "its parameters are `T`",
        ],
        "`foo` names nothing of `PartialEq`",
    );
}

/// A WITNESS'S OWN VALUES THAT ARE PARTIAL get `PartialEq` and `NonEq`, whatever it witnesses. `W`
/// holds a `Float` and witnesses `Other`'s `Eq`. The witness's `Eq[T = Other]` read as `W`'s own,
/// `W` was derived no `PartialEq` and its comparisons refused, "unresolved: PartialEq[T = W]", and
/// once it was derived one, the `Eq`/`NonEq` exclusion refused `W` as providing both. Fails with
/// "own" read through `witness_dispatch_carrier` (which finds no carrier on `Eq`, so every `Eq`
/// row is its provider's own), and with the exclusion keyed by provider again.
#[test]
fn a_partial_witness_of_eq_derives_its_own_partial_equality() {
    let src = "namespace test.dhb0c.pw\n  import anthill.prelude.{Eq, PartialEq, Int64, Bool, Float}\n  \
               sort Other\n    entity o(n: Int64)\n  end\n  \
               sort W\n    entity w(x: Float)\n    provides Eq[T = Other, eq = W.oeq]\n    \
               operation oeq(a: Other, b: Other) -> Bool = true\n  end\n  \
               sort Check\n    import anthill.prelude.PartialEq.{eq}\n    \
               operation ws() -> Bool = eq(W.w(x: 1.0), W.w(x: 2.0))\n    \
               operation wsame() -> Bool = eq(W.w(x: 1.0), W.w(x: 1.0))\n    \
               operation other() -> Bool = eq(Other.o(n: 1), Other.o(n: 2))\n  end\nend\n";
    let kb = try_load_kb_with_files(&[src]).unwrap_or_else(|e| panic!("must load: {e:#?}"));
    let at = |op: &str| format!("test.dhb0c.pw.Check.{op}");
    assert!(!bool_of(kb.deep_clone().expect("copy"), &at("ws")), "`W`'s derived equality");
    assert!(bool_of(kb.deep_clone().expect("copy"), &at("wsame")), "`W`'s derived equality");
    assert!(bool_of(kb, &at("other")), "`Other`'s equality is the bound `oeq`");
}

/// THE `Eq`/`NonEq` EXCLUSION AT THE CARRIER A WITNESS NAMES: `C` writes `PartialEq` and `NonEq`
/// for itself, and a witness `W` claims `Eq[T = C]`. Keyed by provider, `W` held `Eq` and `C`
/// `NonEq`, and nothing conflicted: the load accepted a lawful and a partial claim about one
/// sort (MEASURED). Fails with the exclusion skipping witness rows, or keyed by provider again.
#[test]
fn a_witness_eq_at_a_noneq_carrier_is_refused() {
    let src = "namespace test.dhb0c.wnoneq\n  import anthill.prelude.{Eq, PartialEq, NonEq, Int64, Bool}\n  \
               sort C\n    entity c(n: Int64)\n    provides PartialEq[T = C]\n    provides NonEq[T = C]\n  end\n  \
               sort W\n    provides Eq[T = C, eq = W.ceq]\n    \
               operation ceq(a: C, b: C) -> Bool = true\n  end\nend\n";
    assert_refused_naming(
        &load_errors_of(src),
        &["'test.dhb0c.wnoneq.C' provides both 'Eq' and 'NonEq'"],
        "a witness's lawful `Eq` beside `C`'s own `NonEq`",
    );
}

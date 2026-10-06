//! WI-20260829-9NJTX — THE PROVIDER-VIEW INSTANTIATION IS A REWRITE OF THE VIEW, NOT A
//! BINDING IN THE CALLER'S SUBSTITUTION.
//!
//! `parameterized_compatible_view`, checking a carrier against a spec view it provides
//! (`List[T = Row]` at `Iterable[Element = Row]`), must read the provider fact's
//! carrier-side values — `Iterable.Element ↦ List.T` — as THIS instance's values. It did
//! that by `subst.bind_value`-ing each of the actual base's canonical param vars to the
//! instance's binding and letting the comparison resolve through them (WI-441).
//!
//! THE VAR IT BINDS IS THE SORT'S, NOT THE INSTANCE'S. There is one `List.T` — one
//! `Var::Global` behind the `SortAlias` — shared by every `List` type and every comparison
//! that runs in a given `Substitution`. The bind outlives the comparison, and the loop
//! guarded itself with `if subst.resolve_as_value(vid).is_none()`, so the FIRST `List`
//! compared in a substitution decided what `List.T` meant for all the rest.
//!
//! THE CALLER THAT MAKES IT VISIBLE is the ordinary one: `check_call`'s positional
//! argument loop pushes a `TypeError` and CONTINUES on the same `subst`, so argument 2 is
//! checked in the substitution argument 1 left behind. Both directions were driven:
//!
//! | program                                     | before | after | what it shows |
//! |---------------------------------------------|--------|-------|---------------|
//! | [`the_second_argument_conforms_on_its_own`] | 0      | 0     | CONTROL — `List[T = Int64]` really does conform to `Iterable[Element = Int64]` |
//! | [`a_first_argument_that_conforms_does_not_capture_the_second`] | **1** | **0** | a WELL-TYPED program was refused |
//! | [`a_failed_first_argument_does_not_capture_the_second`] | **2** | **1** | a spurious SECOND error on a program with one mistake |
//! | [`a_genuine_mismatch_is_still_refused`]     | 1      | 1     | CONTROL — the repair does not make the relation permissive |
//! | [`two_arguments_of_one_element_type`]       | 1      | 1     | CONTROL — the degenerate row. Both arguments are `List[T = Int64]`, so the stale value IS the right one and nothing moves. It is here because it is the row the defect CANNOT reach, and a fixture that only varied the expected side would have looked green |
//! | [`a_direct_one_hop_provider_is_captured_too`] | **1** | **0** | the same capture through a DIRECT provision — the defect is not GNPG7's |
//!
//! WHAT FAILS WHEN THE CHANGE IS BACKED OUT: the three bold rows, and only those —
//! measured, 3 passed / 3 failed on the restored `typing.rs`. The three controls pass
//! either way by design; they are what makes the movers attributable to the residue rather
//! than to the relation getting looser.
//!
//! WHY NOT THE REPAIR THE TICKET NAMED. WI-20260829-9NJTX asked for probe-and-commit — run
//! the instantiation and the per-param loop on a cloned subst, commit only on success —
//! because the residue it saw was the one a FAILED comparison leaves. That was applied and
//! MEASURED on these same five programs: `a_failed_first_argument_does_not_capture_the_second`
//! went 2 → 1, and `a_first_argument_that_conforms_does_not_capture_the_second` stayed at
//! 1. Rollback on failure cannot help a comparison that SUCCEEDS, and the succeeding one
//! is the row where a correct program is rejected. So the repair is not rollback: the
//! instantiation is applied to the provider view up front, through a scratch child of
//! `subst` that never escapes, and the caller's substitution is not written by it at all.
//!
//! WHAT THE REPAIR ABSORBED, and the one number that says the two legs of the provider arm
//! did not just move work around: `pv` now ARRIVES instantiated, so the arm's second leg
//! (re-walk `pv` through `subst`, gated on `pvr != pv`) has nothing left to resolve.
//! Instrumented on both trees over `wi_tests`: before, 10,313 reaches, 59 of them resolved
//! further, and 39 of those ACCEPTED a binding the first leg rejected; after, 13,149
//! reaches and zero resolve further — those 39 are decided by the first leg now. The leg is
//! kept, and the site says why.
//!
//! WHY IT SURFACED NOW: WI-20260829-GNPG7 widened the population reaching this loop from a
//! DIRECTLY-providing actual to any TRANSITIVELY-providing one, which is what puts the
//! `Iterable` rows above (`List provides Stream provides Iterable`) in it, and its
//! /code-review filed this ticket off that widening. The defect itself is older:
//! [`a_direct_one_hop_provider_is_captured_too`] is captured through a DIRECT provision
//! and reaches none of GNPG7's composition.
//!
//! WI-20261005-KSSA4 — THE FIXTURE IS A SPEC THAT IS ITS OWN CARRIER NOW. The rows were
//! written over `Iterable` and `FiniteCollection`, which are specs over a parameter: a
//! `List` provides them and is not one, so `takes(a: Iterable[Element = Row])` refuses
//! every argument and the provider view is not reached. `Walk` below receives on `Self`,
//! so a `Bag` IS a `Walk` and the relation still reads its provision — which RENAMES the
//! parameter (`Walk.Element ↦ Bag.V`), the shape the capture needs, and reaches `Walk` in
//! one hop for `Bag` and in two for `Deep`. The verdicts are the table's "after" column.
//! THE BACK-OUT, RE-MEASURED ON THIS FIXTURE — the instantiation published into the
//! caller's substitution where the parameter is still free there, so the first instance
//! compared decides for the rest: the three bold rows fail and the three controls pass, as
//! the table says, with `wi_0rp29_member_rule_test
//! …another_parameter_typed_by_the_spec_is_any_provider_control`.

use crate::common::try_load_kb_with;

fn load_errors(src: &str) -> Vec<String> {
    match try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(es) => es.to_vec(),
    }
}

/// `Row` exists to give the two arguments DIFFERENT element types — the axis the defect is
/// about. `Bag provides Walk[Element = V]` directly; `Deep` reaches `Walk` in two hops
/// (`Deep provides Mid[Item = D]`, `Mid provides Walk[Element = Item]`).
fn program(params: &str, args: &str, call: &str) -> String {
    format!(
        r#"
namespace test.njtx
  import anthill.prelude.{{Int64, Bool}}
  sort Row
    import anthill.prelude.Int64
    entity row(a: Int64)
  end
  sort Walk
    import anthill.prelude.Int64
    sort Element = ?
    operation steps(w: Self) -> Int64
  end
  sort Mid
    import anthill.prelude.Int64
    sort Item = ?
    provides Walk[Element = Item]
    operation steps(w: Self) -> Int64 = 2
  end
  sort Bag
    import anthill.prelude.Int64
    sort V = ?
    entity bag(v: V)
    provides Walk[Element = V]
    operation steps(w: Self) -> Int64 = 1
  end
  sort Deep
    import anthill.prelude.Int64
    sort D = ?
    entity deep(d: D)
    provides Mid[Item = D]
    operation steps(w: Self) -> Int64 = 3
  end
  operation takes({params}) -> Int64 = 1
  operation drive({args}) -> Int64 = takes({call})
end
"#
    )
}

/// CONTROL, and the one that makes the two moving rows readable: `Deep[D = Int64]` IS
/// admissible at `Walk[Element = Int64]`. Green either way.
#[test]
fn the_second_argument_conforms_on_its_own() {
    assert_eq!(
        load_errors(&program(
            "b: Walk[Element = Int64]",
            "ys: Deep[D = Int64]",
            "ys"
        )),
        Vec::<String>::new()
    );
}

/// THE ROW THAT REJECTS A CORRECT PROGRAM. Both arguments conform. Argument 1 SUCCEEDS and
/// used to leave the carrier's parameter bound to `Row` behind; argument 2's `Element` then
/// composed to `Row` and was refused against `Int64` — RED before the change on the
/// original fixture, with exactly the `takes.b` error.
#[test]
fn a_first_argument_that_conforms_does_not_capture_the_second() {
    assert_eq!(
        load_errors(&program(
            "a: Walk[Element = Row], b: Walk[Element = Int64]",
            "xs: Deep[D = Row], ys: Deep[D = Int64]",
            "xs, ys"
        )),
        Vec::<String>::new()
    );
}

/// THE ROW THE TICKET DESCRIBED: argument 1 genuinely does not conform, and its FAILED
/// comparison left the same residue. The program has ONE mistake and reported two.
#[test]
fn a_failed_first_argument_does_not_capture_the_second() {
    let errs = load_errors(&program(
        "a: Walk[Element = Bool], b: Walk[Element = Int64]",
        "xs: Deep[D = Row], ys: Deep[D = Int64]",
        "xs, ys",
    ));
    assert_eq!(errs.len(), 1, "expected only the takes.a mismatch, got {errs:#?}");
    assert!(
        errs[0].contains("takes.a") && errs[0].contains("Walk[Element = Bool]"),
        "wrong error: {errs:#?}"
    );
}

/// CONTROL — the relation did not get permissive. A `Deep[D = Int64]` at
/// `Walk[Element = Bool]` is still one located mismatch. Green either way; it fails if
/// the repair were to make the composed `Element` resolve to nothing and wildcard-accept.
#[test]
fn a_genuine_mismatch_is_still_refused() {
    let errs = load_errors(&program(
        "a: Walk[Element = Bool]",
        "xs: Deep[D = Int64]",
        "xs",
    ));
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert!(errs[0].contains("takes.a"), "{errs:#?}");
}

/// CONTROL, and the row that says why the fixture varies the ARGUMENT's element type
/// rather than only the parameter's: with both arguments `Deep[D = Int64]` the captured
/// value is the correct one and the defect is invisible. One error, before and after.
#[test]
fn two_arguments_of_one_element_type() {
    let errs = load_errors(&program(
        "a: Walk[Element = Bool], b: Walk[Element = Int64]",
        "xs: Deep[D = Int64], ys: Deep[D = Int64]",
        "xs, ys",
    ));
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert!(errs[0].contains("takes.a"), "{errs:#?}");
}

/// THE DEFECT IS NOT GNPG7'S. `Bag provides Walk[Element = V]` DIRECTLY, so this row is
/// served by `provider_spec_view_bindings` — the direct reader `subtype_provider_view`
/// tries FIRST — and needs none of GNPG7's composition. RED before the change on the
/// original fixture, with the same spurious `takes.b`.
///
/// IT HAS TO BE A PROVISION THAT RENAMES THE PARAM. A spec whose parameter the carrier
/// names alike finds the actual's own argument by key identity, and the provider arm — the
/// only reader of the instantiated values — never runs for it: the first cut of the
/// original row, written over `Stream[T = Row, E = {}]`, was GREEN BOTH WAYS for that
/// reason. `Walk.Element ↦ Bag.V` is the shape the defect is about.
#[test]
fn a_direct_one_hop_provider_is_captured_too() {
    assert_eq!(
        load_errors(&program(
            "a: Walk[Element = Row], b: Walk[Element = Int64]",
            "xs: Bag[V = Row], ys: Bag[V = Int64]",
            "xs, ys"
        )),
        Vec::<String>::new()
    );
}

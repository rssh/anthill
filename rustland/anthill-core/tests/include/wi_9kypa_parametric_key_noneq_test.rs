//! WI-20260919-9KYPA — a parametric container at an UNLAWFUL ARGUMENT is refused where
//! the type is WRITTEN: `Set[T = List[T = Float]]`, `Map[K = Option[T = Float]]`.
//!
//! The last leg of WI-20260918-CKD4J's `NonEq` mirror, and the gap kernel-language.md §8.3
//! used to name ("a key whose unlawfulness is in its ARGUMENT … is a known remaining
//! gap"). MEASURED at 99b962a5, one fixture per row: `Set[T = Float]` REFUSED,
//! `Set[T = Pt]` REFUSED, `Set[T = Holder]` REFUSED — but `Set[T = List[T = Float]]` and
//! `Set[T = Option[T = Float]]` both LOADED, because `check_use_site_requires_eq` read the
//! KEY'S OWN provisions and `List` provides no `NonEq` of its own.
//!
//! Two parts, and neither alone closes it:
//!  (a) `eq_derive::derive_conditional_noneq` derives the mirror row `provides NonEq[List]
//!      :- NonEq[T]`, ONE CLAUSE PER PARAMETER (a disjunction, where the `Eq` half is a
//!      conjunction in one clause), each clause also carrying the `PartialEq` conditions
//!      that `NonEq requires PartialEq` obliges it to.
//!  (b) `check_use_site_requires_eq` RESOLVES the goal `NonEq[T = <the whole written
//!      type>]` (`typing::noneq_holds_at`) instead of reading the head carrier's
//!      provisions, so the conditional row descends into the written argument.
//!
//! ── WHICH TESTS FAIL WHEN EACH PART IS BACKED OUT ───────────────────────────────
//!
//! Remove (a) — the `derive_conditional_noneq` call in `eq_derive::run` — and
//! `a_parametric_key_at_an_unlawful_argument_is_refused` fails on every row: the goal
//! resolves against nothing, so the keys load. Remove (b) — restore the
//! `sort_provides(carrier, NonEq)` read — and the SAME test still passes while
//! `a_parametric_key_at_a_lawful_argument_still_loads` fails on every row: the provision
//! EDGE ignores the argument, so `List[T = Int64]` is refused too. That pair is why both
//! tests are here; either one alone is passed by a wrong implementation.
//!
//! MEASURED, by backing each out in turn: without (a), `a_parametric_key_at_an_unlawful_
//! argument_is_refused`, `the_goal_descends_through_nested_arguments` and
//! `a_parametric_carrier_holds_a_conditional_pair` fail, and the lawful-argument rows pass.
//! Without (b), `a_parametric_key_at_a_lawful_argument_still_loads`,
//! `a_total_float_argument_is_a_lawful_key` and the nested control fail, and the refusal
//! row passes.
//!
//! `an_unconditional_eq_noneq_pair_is_still_refused` is the control on the third change:
//! `check_eq_noneq_exclusive` had to learn to admit a conditional pair (it now sees one at
//! every parametric carrier in the stdlib), and a check that merely stopped refusing would
//! pass the admission row and fail this one.
//!
//! PASS EITHER WAY BY DESIGN: `a_tuple_key_is_still_the_open_gap` (no sort, so no
//! provision — out of scope both before and after, pinned so it stays documented).

fn refusals(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src).err().unwrap_or_default()
}

/// `operation k(s: <container>) -> Int64` — the written-type position the ticket measured
/// in, and the shortest one that records a `ParameterizedSite`.
fn key_program(ns: &str, container: &str) -> String {
    format!(
        r#"
namespace wi9kypa.{ns}
  import anthill.prelude.{{Int64, Float, Set, Map, List, Option}}
  sort D
    operation k(s: {container}) -> Int64 = 1
  end
end
"#
    )
}

/// The refusal must name all four parts, the same four `wi835_use_site_requires_scope_test`
/// holds the non-parametric refusal to: the CONTAINER, its own PARAMETER, the required
/// SPEC, and the carrier bound there — which for a parametric key is the WHOLE type, not
/// its head sort.
fn assert_key_refused(errs: &[String], container: &str, param: &str, carrier: &str) {
    assert!(
        errs.iter().any(|e| {
            e.contains(container)
                && e.contains(carrier)
                && e.contains("anthill.prelude.Eq")
                && e.contains(&format!("`{param}`"))
        }),
        "expected a `{container}` requires-`Eq`-at-`{param}` refusal naming `{carrier}`; got:\n{}",
        errs.join("\n"),
    );
}

/// THE TICKET'S ACCEPTANCE. Both containers, both arguments, each naming the whole key.
#[test]
fn a_parametric_key_at_an_unlawful_argument_is_refused() {
    for (ns, container, holder, param, key) in [
        (
            "seta",
            "Set[T = List[T = Float]]",
            "anthill.prelude.Set",
            "T",
            "anthill.prelude.List[T = anthill.prelude.Float]",
        ),
        (
            "mapa",
            "Map[K = Option[T = Float], V = Int64]",
            "anthill.prelude.Map",
            "K",
            "anthill.prelude.Option[T = anthill.prelude.Float]",
        ),
    ] {
        let errs = refusals(&key_program(ns, container));
        assert_key_refused(&errs, holder, param, key);
    }
}

/// THE CONTROL THAT THE REFUSAL IS CONDITIONAL, not a blanket one for parametric keys.
/// The same two containers over a LAWFUL argument load — which is the whole reason (b) had
/// to resolve a goal rather than read the `NonEq` provision edge, since that edge is
/// present at `List` either way.
#[test]
fn a_parametric_key_at_a_lawful_argument_still_loads() {
    for (ns, container) in [
        ("setb", "Set[T = List[T = Int64]]"),
        ("mapb", "Map[K = Option[T = Int64], V = Int64]"),
    ] {
        assert_eq!(
            refusals(&key_program(ns, container)),
            Vec::<String>::new(),
            "{container} is a lawful key and must load"
        );
    }
}

/// NESTING, both ways round: the unlawful argument one level deeper, and a parametric key
/// whose own argument is parametric-and-lawful. `List[T = Option[T = Float]]` is unlawful
/// because the conditional row descends TWICE.
#[test]
fn the_goal_descends_through_nested_arguments() {
    let errs = refusals(&key_program("nest", "Set[T = List[T = Option[T = Float]]]"));
    assert_key_refused(
        &errs,
        "anthill.prelude.Set",
        "T",
        "anthill.prelude.List[T = anthill.prelude.Option[T = anthill.prelude.Float]]",
    );
    assert_eq!(
        refusals(&key_program("nestok", "Set[T = List[T = Option[T = Int64]]]")),
        Vec::<String>::new(),
        "the same nesting over a lawful leaf must load"
    );
}

/// A NON-parametric boundary still SHIELDS its `Float`: `TotalFloat` declares its own
/// total `eq`, so a container of it is a lawful key at any depth.
///
/// MEASURED: this row passes with (a) backed out and FAILS with (b) backed out — it is a
/// second witness for the lawful-argument control, one level down and through a boundary
/// rather than through a primitive.
#[test]
fn a_total_float_argument_is_a_lawful_key() {
    let src = r#"
namespace wi9kypa.total
  import anthill.prelude.{Int64, Set, List, TotalFloat}
  sort D
    operation k(s: Set[T = List[T = TotalFloat]]) -> Int64 = 1
  end
end
"#;
    assert_eq!(refusals(src), Vec::<String>::new());
}

/// `Eq` ⊥ `NonEq` STILL REFUSES AN UNCONDITIONAL PAIR. `check_eq_noneq_exclusive` now
/// admits a conditional pair — it sees one at `List`, `Option`, `Result` and `SortedSet` —
/// and this is the control that the admission is by CONDITION and not a weakening: a
/// non-parametric composite reaching `Float` derives an UNCONDITIONAL `NonEq`, so a
/// hand-written `provides Eq` beside it is still a load error.
#[test]
fn an_unconditional_eq_noneq_pair_is_still_refused() {
    let src = r#"
namespace wi9kypa.excl
  import anthill.prelude.{Float, Eq}
  sort Pt
    entity pt(x: Float)
    provides Eq[T = Pt]
  end
end
"#;
    let errs = refusals(src);
    assert!(
        errs.iter()
            .any(|e| e.contains("wi9kypa.excl.Pt") && e.contains("NonEq")),
        "an unconditional `Eq` beside a derived unconditional `NonEq` is still WI-658's \
         error; got {errs:?}"
    );
}

/// THE ADMISSION, read directly off the KB rather than inferred from a clean load: the
/// stdlib's parametric carriers hold BOTH a conditional `Eq` and a conditional `NonEq`,
/// and both rows are conditional — which is exactly what
/// `an_unconditional_eq_noneq_pair_is_still_refused` shows is not admitted.
#[test]
fn a_parametric_carrier_holds_a_conditional_pair() {
    let kb = crate::common::load_kb_with("namespace wi9kypa.rows\nend\n");
    for carrier in ["anthill.prelude.List", "anthill.prelude.Option"] {
        let c = kb.try_resolve_symbol(carrier).expect(carrier);
        for spec in [
            "anthill.prelude.PartialEq",
            "anthill.prelude.Eq",
            "anthill.prelude.NonEq",
        ] {
            let s = kb.try_resolve_symbol(spec).expect(spec);
            assert!(
                kb.provides_clause_count(c, s) >= 1,
                "{carrier} must provide {spec}"
            );
            assert!(
                kb.provision_has_conditions(c, s),
                "{carrier}'s {spec} must be CONDITIONAL — an unconditional one would \
                 claim `{carrier}[T = Float]` either lawful or unlawful outright"
            );
        }
    }
    // `Float` is the unconditional leaf the whole derivation bottoms out in, and the
    // contrast that makes the assertions above mean something.
    let f = kb.try_resolve_symbol("anthill.prelude.Float").expect("Float");
    let ne = kb.try_resolve_symbol("anthill.prelude.NonEq").expect("NonEq");
    assert!(
        !kb.provision_has_conditions(f, ne),
        "`Float`'s `NonEq` is the unconditional partial leaf"
    );
}

/// PASSES EITHER WAY BY DESIGN — the remaining gap, pinned so it stays documented. A named
/// TUPLE key has no sort to carry a provision, so neither the derived row nor the goal
/// that reads it reaches it. `wi835_use_site_requires_scope_test` owns the same pin at the
/// `Map` return position; this one is here so the gap is stated beside the leg that closed.
#[test]
fn a_tuple_key_is_still_the_open_gap() {
    assert_eq!(
        refusals(&key_program("tup", "Map[K = (a: Float), V = Int64]")),
        Vec::<String>::new(),
        "a named-tuple key is out of scope; see kernel-language.md §8.3"
    );
}

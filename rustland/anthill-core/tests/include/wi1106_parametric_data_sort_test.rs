//! WI-1106 — A SORT WITH CONSTRUCTORS IS A DATA SORT, WHATEVER ITS PARAMETERS.
//!
//! WI-407 wrote that rule and attached `&& spec_params.is_empty()` to it, deliberately
//! keeping "a parametric data sort like `List` on its old path". The half-rule is what
//! made a parametric data sort a *spec*: `maybe_emit_fact_provides_info` skipped
//! `fact Color[Holder]` over a non-parametric `Color` with `entity red/green`, and
//! filed a provision for the identical text one type parameter later.
//!
//! TWO DEFECTS FELL OUT OF IT, both measured before the fix:
//!
//! 1. THE PARAMETER READ AS THE CARRIER. `fact Polynom[Int64]` in
//!    `anthill-testcases/ring-polynom` — "Polynom[Int64] is a valid instantiation", per
//!    its own comment — filed `Int64 provides Polynom`. `Int64` is the polynomial's
//!    RING PARAMETER, not a polynomial.
//! 2. A FIELD VALUE READ AS THE CARRIER. `fact Box(value: Other)` — an ordinary
//!    construction over an eponymous parametric sort — filed `Other provides Box`. This
//!    is exactly what `wi407_provider_edges_test::data_sort_fact_does_not_widen_*`
//!    pins against for a non-parametric data sort, reachable again by adding a type
//!    parameter. The ticket asked whether a bare sort name can even sit in a value slot
//!    (WI-707/WI-206 refuse one in an ordinary value position); the answer is that a
//!    field typed by a TYPE PARAMETER accepts it, so yes.
//!
//! THE FIX IS ONE CONJUNCT, and it cost nothing: instrumenting the emission across the
//! whole corpus and all 29 test binaries recorded 216_121 provisions, of which NINE
//! had a constructor-bearing functor — seven `Polynom`, and the two fixtures written
//! to demonstrate defect 2. No legitimate provision comes from a sort with
//! constructors.
//!
//! WHY NOT THE WRITTEN SURFACE, which is what the ticket proposed. Parse records
//! `[…]`-vs-`(…)` (`mark_type_application`, WI-927) and the plan was to read it:
//! brackets apply types, parens construct. MEASURED, that premise is false — the two
//! defects above are BRACKETED data facts, as is wi210's `fact Wi210Color[count = ?]`
//! and wi407's `fact FwdColor[FwdHolder]`. Brackets do not imply a provision, so the
//! surface cannot decide this; the functor's own constructors can, and do. (The
//! surface distribution is not close: of those 216_121 emissions, 206_788 were
//! bracketed, 9_331 bare, and 2 parenthesised — both of them defect 2.)
//!
//! WHAT THIS BUYS ELSEWHERE: the carrier-derivation arm below the gate is now
//! CONSTRUCTION-FREE by construction — a sort with no constructors cannot be
//! constructed — which is what let WI-933's refusal drop its narrowing and cover
//! `fact Spec[T = ?]` too. That half is pinned in `wi933_carrierless_provision_test`.
//!
//! TWO MORE DEFECTS OF THE SAME FAMILY were found reviewing this change and fixed
//! here rather than deferred, since each is a few lines once measured:
//!
//! 3. `provides` DID NOT TAKE THE RULE AT ALL, so `provides <DataSort>` filed the
//!    is-a that `fact <DataSort>` refuses — at BOTH arities, so it was not this
//!    ticket's doing. kernel-language §5.1 says the two spellings "record the same
//!    PROVISION" and that "neither can say something about a carrier the other
//!    cannot"; over a constructor-bearing spec that was false, and an author could
//!    reach the refused widening by changing one keyword. `load_provides_clause` now
//!    asks the same question — of the PROVIDED spec, not the provider, which is the
//!    one place the two sides' predicates genuinely differ. Instrumented over corpus
//!    and suite: ZERO provisions name a constructor-bearing spec, so the gate is free.
//! 4. A CARRIER BINDING THAT RESOLVED TO NOTHING was accepted as a carrier. A literal
//!    lowers to `Term::Const` in a paren field slot (already declined) but to a TYPE
//!    NAME in a bracket, so `fact Spec[T = 1]` filed a provision under a symbol named
//!    `1` — tripping `typing.rs`'s WI-672 `debug_assert` in debug and misbucketing it
//!    silently in release. The derivation now asks whether the symbol resolved, which
//!    is the repair that assert's own message asks for. Tuple and arrow bindings lower
//!    the same way and are covered by the same filter.
//!
//! ON BACK-OUT (restore `spec_params.is_empty() &&`), MEASURED — three fail and two do
//! not, and which two is the point. The last three tests have their own back-outs,
//! noted at each:
//!
//! | test | on back-out of the gate |
//! |---|---|
//! | `a_construction_over_a_parametric_sort_files_no_provider_edge` | FAILS — defect 2 at the index |
//! | `the_bogus_edge_no_longer_changes_what_the_upcast_is_refused_for` | FAILS — defect 2 driven |
//! | `a_parametric_data_sorts_type_argument_is_not_its_carrier` | FAILS — defect 1 |
//! | `the_sort_body_position_takes_the_rule_too` | FAILS — the position the widening changes |
//! | `a_constructor_less_parametric_spec_still_provides` | passes either way (BY DESIGN — the control saying the widening did not stop provisions altogether; a rule that skipped everything would satisfy the three above) |
//! | `a_non_parametric_data_sort_was_already_skipped` | passes either way (BY DESIGN — WI-407's half, unchanged; the rule is a widening, not a replacement) |
//! | `the_provides_spelling_agrees_with_the_fact_spelling` | passes either way (it measures defect 3's own fix in `load_provides_clause`) |
//! | `a_binding_that_resolved_to_nothing_is_refused_not_filed` | passes either way (it measures defect 4's own fix, the resolution filter) |
//!
//! One test OUTSIDE this file fails too, and that coupling is deliberate:
//! `wi933_carrierless_provision_test::a_data_construction_over_a_parametric_sort_is_not_
//! a_provision_claim`. WI-933's refusal was narrowed to a bare shape over a
//! constructor-less functor precisely to miss the constructions this gate now stops
//! earlier; with the narrowing removed and the gate restored, they reach the refusal
//! again. The gate is what LICENSES the unconditional refusal, so backing out either
//! alone is not a state the tree is meant to hold.

use anthill_core::kb::KnowledgeBase;
use anthill_core::persistence::print::TermPrinter;
use crate::common::try_load_kb_with;

fn errors(src: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_default()
}

/// Every `anthill.reflect.SortProvidesInfo` head in `kb`, rendered. Mirrors
/// `wi210_dispatch_test::provides_info_heads` — the direct reader, so a test can say
/// "no edge was filed" rather than inferring it from a downstream symptom.
fn provides_info_heads(kb: &mut KnowledgeBase) -> Vec<String> {
    let sym = match kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo") {
        Some(s) => s,
        None => return Vec::new(),
    };
    let rids: Vec<_> = kb.rules_by_functor(sym).into_iter().collect();
    let heads: Vec<_> = rids.iter().map(|&r| kb.rule_head(r)).collect();
    let printer = TermPrinter::new(kb);
    heads.into_iter().map(|h| printer.print_term(h)).collect()
}

/// DEFECT 2, at the emission. `fact Wi1106Box(value: Wi1106Other)` constructs a value;
/// it says nothing about `Wi1106Other` satisfying anything. Asserted at the
/// `SortProvidesInfo` index rather than through a symptom, so it cannot pass because
/// some later pass happened to reject the program for another reason — which is
/// exactly how the driven twin below reads when it is wrong.
#[test]
fn a_construction_over_a_parametric_sort_files_no_provider_edge() {
    let mut kb = try_load_kb_with(
        r#"
namespace test.wi1106.emit
  import anthill.prelude.{Int64}

  sort Wi1106Other
    entity wi1106_o
  end

  sort Wi1106Box
    sort T = ?
    entity Wi1106Box(value: T)
  end

  fact Wi1106Box(value: Wi1106Other)
end
"#,
    )
    .expect("the construction must load clean");
    let heads = provides_info_heads(&mut kb);
    assert!(
        !heads
            .iter()
            .any(|h| h.contains("Wi1106Other") && h.contains("Wi1106Box")),
        "a field value is not a carrier — `fact Wi1106Box(value: Wi1106Other)` must \
         file no `Wi1106Other provides Wi1106Box`; saw:\n{heads:#?}"
    );
}

/// DEFECT 2, DRIVEN — and the two legs must give the SAME message, which is the whole
/// point. A bogus provider edge does not merely add a fact: it makes the upcast
/// `Wi1106Other -> Wi1106Box` *admissible*, so the refusal that follows is about
/// something else entirely. MEASURED before the fix: with the data fact the loader got
/// past subtyping and complained that the upcast "leaves its member(s) 'T' unbound"
/// (the avoidance problem); without it, the plain "expected …, got …". Two different
/// errors from one edge is the observable.
///
/// So this asserts the message, not merely that an error exists — an
/// `!errs.is_empty()` test would have been green throughout the defect's whole life.
#[test]
fn the_bogus_edge_no_longer_changes_what_the_upcast_is_refused_for() {
    const WITH_FACT: &str = r#"
namespace test.wi1106.driven
  import anthill.prelude.{Int64}

  sort Wi1106Other2
    entity wi1106_o2
  end

  sort Wi1106Box2
    sort T = ?
    entity Wi1106Box2(value: T)
  end

  fact Wi1106Box2(value: Wi1106Other2)

  operation wi1106_widen(o: Wi1106Other2) -> Wi1106Box2 = o
end
"#;
    // The control: the identical program with the data fact removed. Its verdict is
    // what the fixture above must now match.
    let control = WITH_FACT.replace("  fact Wi1106Box2(value: Wi1106Other2)\n", "");
    assert!(control != WITH_FACT, "the control must remove the fact line");

    let ctl_errs = errors(&control);
    assert!(
        ctl_errs
            .iter()
            .any(|e| e.contains("expected Wi1106Box2") && e.contains("got Wi1106Other2")),
        "control: with no fact at all the upcast is a plain sort mismatch; got \
         {ctl_errs:?}"
    );

    let errs = errors(WITH_FACT);
    assert!(
        errs.iter()
            .any(|e| e.contains("expected Wi1106Box2") && e.contains("got Wi1106Other2")),
        "a DATA construction must leave the upcast refused for exactly the same reason \
         as the control — if it is refused for anything else, the construction was \
         read as an is-a; got {errs:?}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("avoidance")),
        "and specifically not the avoidance refusal, which is what the bogus edge \
         produced: the upcast was ADMITTED and then failed on an unbound member; got \
         {errs:?}"
    );
}

/// DEFECT 1: the spec's own TYPE PARAMETER read as its carrier. `fact Polynom[Int64]`
/// is `anthill-testcases/ring-polynom`'s line, and its comment says what it means —
/// "Polynom[Int64] is a valid instantiation (Int64 satisfies Ring)". Not "Int64 is a
/// polynomial", which is what was filed.
///
/// Distinct from the test above because the carrier arrives by a different route: the
/// leading POSITIONAL, translated against `spec_params`, rather than a named field
/// value. Same gate, two producers — and a fix that closed only one would leave the
/// shipped test-case fixture still filing its edge.
#[test]
fn a_parametric_data_sorts_type_argument_is_not_its_carrier() {
    let mut kb = try_load_kb_with(
        r#"
namespace test.wi1106.polynom
  import anthill.prelude.{Int64}

  sort Wi1106Ring
    sort T = ?
    operation wi1106_add(a: T, b: T) -> T
  end

  sort Wi1106Poly
    sort R = ?
    entity wi1106_poly(coefficient: R)
  end

  fact Wi1106Poly[Int64]
end
"#,
    )
    .expect("the instantiation fact must load clean");
    let heads = provides_info_heads(&mut kb);
    assert!(
        !heads
            .iter()
            .any(|h| h.contains("Wi1106Poly") && h.contains("Int64")),
        "`fact Wi1106Poly[Int64]` binds the sort's PARAMETER; it does not make Int64 a \
         Wi1106Poly; saw:\n{heads:#?}"
    );
}

/// THE CONTROL FOR THE WIDENING: a real spec — parametric, NO constructors — still
/// files its edge, and the edge still carries subtyping. Without this the three tests
/// above are satisfied by a loader that stopped emitting provisions altogether.
#[test]
fn a_constructor_less_parametric_spec_still_provides() {
    let src = r#"
namespace test.wi1106.spec
  import anthill.prelude.{Int64}

  sort Wi1106Spec
    sort T = ?
    operation wi1106_describe(x: T) -> Int64 = 0
  end

  sort Wi1106Carrier
    entity wi1106_c
  end

  fact Wi1106Spec[Wi1106Carrier]
end
"#;
    let mut kb = try_load_kb_with(src).expect("the provision must load clean");
    let heads = provides_info_heads(&mut kb);
    assert!(
        heads
            .iter()
            .any(|h| h.contains("Wi1106Carrier") && h.contains("Wi1106Spec")),
        "a spec with no constructors keeps its provider edge — the gate must widen to \
         DATA sorts only; saw:\n{heads:#?}"
    );
}

/// THE SORT-BODY POSITION IS INCLUDED, and this pins it because it is the one place
/// the widening changes a previously-clean program.
///
/// `sort Sub { fact DataSort[T = Int64] }` reads as "Sub is-a DataSort" and no longer
/// files that edge, so an upcast written against it becomes a type error. That is
/// correct — a sort is not a subtype of a data sort, which is precisely what
/// `wi407_provider_edges_test::data_sort_fact_does_not_widen_*` refuses — and it is
/// not a new class of behaviour: the NON-parametric twin has behaved this way since
/// WI-407, MEASURED identical on both sides of this change. What the widening does is
/// stop the arity from deciding.
///
/// THE DROP IS SILENT, and that is a real cost stated rather than hidden: nothing is
/// reported at the `fact` line, so the author sees a type mismatch at the *use*. It
/// cannot simply be made loud — `sort Holder { fact Colour[count = ?] }` is a
/// legitimate data fact, pinned clean by wi210
/// `fact_for_non_spec_sort_does_not_emit_provides_info` — so telling a data assertion
/// from a mis-written claim in this position is a question this rule does not answer.
///
/// `provides` AGREES HERE, and did not before: `provides DataSort[…]` in the same body
/// used to file the provision and let the upcast conform, at BOTH arities. That made
/// kernel-language §5.1 — the two spellings "record the same PROVISION", "neither can
/// say something about a carrier the other cannot" — false over a constructor-bearing
/// spec. `load_provides_clause` now applies the same rule, reading the PROVIDED spec's
/// constructors (not the provider's, which would refuse every concrete carrier in the
/// stdlib). Driven below.
#[test]
fn the_sort_body_position_takes_the_rule_too() {
    const WITH_FACT: &str = r#"
namespace test.wi1106.sortbody
  import anthill.prelude.{Int64}

  sort Wi1106Data
    sort T = ?
    entity wi1106_data(v: T)
  end

  sort Wi1106Sub
    entity wi1106_sub
    fact Wi1106Data[T = Int64]
  end

  operation wi1106_up(s: Wi1106Sub) -> Wi1106Data[T = Int64] = s
end
"#;
    let errs = errors(WITH_FACT);
    assert!(
        errs.iter().any(|e| e.contains("Wi1106Sub")),
        "a sort-body `fact` naming a DATA sort files no is-a, so the upcast must be \
         refused — the arity must not decide it; got {errs:?}"
    );

    // CONTROL, and the reason the assertion above is about the UPCAST rather than
    // about an error existing: the identical body over a constructor-LESS sort still
    // provides, so the widening did not simply disable sort-body facts.
    let spec_version = WITH_FACT
        .replace("Wi1106Data\n    sort T = ?\n    entity wi1106_data(v: T)", "Wi1106Data\n    sort T = ?")
        .replace("test.wi1106.sortbody", "test.wi1106.sortbody_ctl");
    assert!(
        !spec_version.contains("entity wi1106_data"),
        "the control must remove the constructor"
    );
    let ctl_errs = errors(&spec_version);
    assert!(
        ctl_errs.is_empty(),
        "control: with no constructor `Wi1106Data` is a spec, the sort-body `fact` \
         files its provision, and the same upcast conforms; got {ctl_errs:?}"
    );
}

/// THE `provides` SPELLING TAKES THE SAME RULE, at both arities — the half that was
/// silently disagreeing until this ticket. §5.1 says a sort body's `provides Spec[…]`
/// and `fact Spec[…]` record the same provision and that neither can say something
/// about a carrier the other cannot; over a constructor-bearing spec `provides` filed
/// the is-a and `fact` did not, so an author could reach the widening `fact` refuses
/// by changing one keyword.
///
/// Both arities are driven, because the `fact` side's defect WAS arity-dependent and
/// this side's was not — testing only the parametric one would have read as "fixed
/// together" when they were broken differently.
#[test]
fn the_provides_spelling_agrees_with_the_fact_spelling() {
    for (label, decl) in [
        ("non-parametric", "sort Wi1106PC
    entity wi1106_pc_red
    entity wi1106_pc_green
  end"),
        ("parametric", "sort Wi1106PC
    sort T = ?
    entity wi1106_pc(v: T)
  end"),
    ] {
        let src = format!(
            r#"
namespace test.wi1106.prov
  import anthill.prelude.{{Int64}}

  {decl}

  sort Wi1106PSub
    entity wi1106_psub
    provides Wi1106PC
  end

  operation wi1106_pup(s: Wi1106PSub) -> Wi1106PC = s
end
"#
        );
        let errs = errors(&src);
        assert!(
            errs.iter().any(|e| e.contains("Wi1106PSub")),
            "{label}: `provides Wi1106PC` names a DATA sort, so it files no is-a and              the upcast must be refused — exactly as the `fact` spelling is; got              {errs:?}"
        );
    }

    // CONTROL — a constructor-LESS spec keeps its `provides`, so the gate reads the
    // PROVIDED spec's constructors and not the provider's. Without this leg the loop
    // above is satisfied by a rule that refuses every `provides` in the language.
    //
    // The spec is NON-parametric on purpose. Written with a `sort T = ?` the upcast is
    // admitted and then refused by the AVOIDANCE check (`T` would escape unbound) — a
    // real error about something else, which would fail this control while the
    // provision it is testing had been filed perfectly well. Measured, and worth the
    // note: "some error occurred" is not what this leg asks.
    let ctl = errors(
        r#"
namespace test.wi1106.prov_ctl
  import anthill.prelude.{Int64}

  sort Wi1106PSpec
    operation wi1106_pd(x: Wi1106PSpec) -> Int64 = 0
  end

  sort Wi1106PSub2
    entity wi1106_psub2
    provides Wi1106PSpec
  end

  operation wi1106_pup2(s: Wi1106PSub2) -> Wi1106PSpec = s
end
"#,
    );
    assert!(
        ctl.is_empty(),
        "control: the provider has constructors and the SPEC does not, so the          provision stands and the upcast conforms; got {ctl:?}"
    );
}

/// A CARRIER BINDING THAT RESOLVED TO NOTHING is not a carrier. In a PAREN field slot
/// a literal lowers to `Term::Const` and was already declined; in a BRACKET the
/// converter lowers `1` as a TYPE NAME, so `fact Spec[T = 1]` arrived as a
/// `Term::Ident` and was taken as the carrier — filing the provision under a symbol
/// named `1`, which tripped `typing.rs`'s WI-672 `debug_assert` in a debug build and
/// silently misbucketed it in release. The derivation now asks whether the symbol
/// resolved at all, which is what that assert's own message asks for ("resolve the
/// `provides` carrier at its producer").
///
/// The tuple and arrow shapes lower the same way and are covered by the same filter,
/// so all three are driven — they were three separate reports and one cause.
#[test]
fn a_binding_that_resolved_to_nothing_is_refused_not_filed() {
    for binding in ["1", "(a: Int64)", "(x: Int64) -> Int64"] {
        let src = format!(
            r#"
namespace test.wi1106.unres
  import anthill.prelude.{{Int64}}

  sort Wi1106URSpec
    sort T = ?
    operation wi1106_ur(x: T) -> Int64 = 0
  end

  fact Wi1106URSpec[T = {binding}]
end
"#
        );
        let errs = errors(&src);
        assert!(
            errs.iter()
                .any(|e| e.contains("its bindings name no type")),
            "`[T = {binding}]` names no type, so it must be refused rather than filed              under an unresolved carrier; got {errs:?}"
        );
    }

    // CONTROL — the same bracket with a real type still provides, so the filter
    // rejects unresolved names rather than bracketed carriers in general.
    let mut kb = try_load_kb_with(
        r#"
namespace test.wi1106.unres_ctl
  import anthill.prelude.{Int64}

  sort Wi1106URSpec2
    sort T = ?
    operation wi1106_ur2(x: T) -> Int64 = 0
  end

  sort Wi1106URCarrier
    entity wi1106_urc
  end

  fact Wi1106URSpec2[T = Wi1106URCarrier]
end
"#,
    )
    .expect("a resolved carrier binding must load clean");
    let heads = provides_info_heads(&mut kb);
    assert!(
        heads
            .iter()
            .any(|h| h.contains("Wi1106URCarrier") && h.contains("Wi1106URSpec2")),
        "control: a bracket naming a real type still files its provision; saw:\n{heads:#?}"
    );
}

/// WI-407's original rule, unchanged: the NON-parametric data sort was already skipped.
/// Passes either way, and is here so the change reads as widening one conjunct rather
/// than replacing the rule — the two `data_sort_fact_does_not_widen_*` pins in
/// `wi407_provider_edges_test` are its driven half.
#[test]
fn a_non_parametric_data_sort_was_already_skipped() {
    let mut kb = try_load_kb_with(
        r#"
namespace test.wi1106.nonparam
  sort Wi1106Colour
    entity wi1106_red
    entity wi1106_green
  end

  sort Wi1106Holder
    entity wi1106_h
  end

  fact Wi1106Colour[Wi1106Holder]
end
"#,
    )
    .expect("the data fact must load clean");
    let heads = provides_info_heads(&mut kb);
    assert!(
        !heads
            .iter()
            .any(|h| h.contains("Wi1106Holder") && h.contains("Wi1106Colour")),
        "a non-parametric data sort files no edge, as it did before; saw:\n{heads:#?}"
    );
}

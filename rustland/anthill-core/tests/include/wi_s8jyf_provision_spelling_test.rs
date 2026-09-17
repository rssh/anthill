//! WI-20260917-S8JYF — `provides` IS THE ONLY SPELLING OF A PROVISION, at BOTH
//! levels, and a bracketed `fact` head must name a type.
//!
//! THE DEFECT, measured on the tree this ticket was filed against:
//!
//! ```text
//! provides NoSuchSpecXyz[T = Carrier]   ->  error: unresolved name 'NoSuchSpecXyz'
//! fact     NoSuchSpecXyz[T = Carrier]   ->  LOADS CLEAN, emits nothing, warns nothing
//! ```
//!
//! A `fact Spec[…]` was a PROVISION only when `Spec` resolved to a sort. With the
//! spec unimported the identical text minted an ordinary fact-only predicate — no
//! provision, no diagnostic — so a missing import silently reclassified the claim.
//! The live witness cleared a whole review cycle: `wi698_row_param_refinement_test`
//! shipped `fact Effect[T = K]` with `Effect` MISSING from the import list.
//!
//! WHY NO DIAGNOSTIC COULD FIX IT. The two readings are undecidable from the text.
//! `sort Rec { fact helper(1) }` is a legitimate fact-only predicate scoped to `Rec`,
//! and `sort Rec { fact SomeSpec[T = …] }` was a provision; they are told apart ONLY
//! by whether the functor resolves to a Sort — exactly the thing that fails when the
//! spec is not imported. A parse-shape test cannot separate them either: `fact Box`
//! and `fact somePredicate` are the same shape at every level, CST included.
//!
//! SO THE SECOND READING IS REMOVED (058 §4, completed at both levels). A `fact` is
//! an ordinary fact wherever it stands; an author who means a provision writes
//! `provides` — in the carrier's own body, or in a `namespace <Carrier>` SECONDARY
//! ENTRY (059 R2/R3) where the carrier has no body to write it in. `provides`
//! already refuses an unresolved spec loudly, so the silence has nowhere left to
//! live. WI-862 had deprecated the IN-SORT half only, which was the half with ZERO
//! corpus sites; every one of the twenty real sites was namespace-level.
//!
//! WHAT EACH TEST HOLDS, AND WHICH FAIL WHEN THE CHANGE IS BACKED OUT — measured by
//! restoring `maybe_emit_fact_provides_info` and its call site, not predicted.
//!
//! | test | on back-out |
//! |---|---|
//! | [`a_fact_in_a_sort_body_records_no_provision`] | FAILS — the fact records one |
//! | [`a_namespace_level_fact_records_no_provision`] | FAILS — the fact records one |
//! | [`the_secondary_entry_records_what_the_fact_used_to`] | passes either way (BY DESIGN — the `provides` route is what the migration moves TO, and it must work before and after; it is here so no other row can pass vacuously against a loader that records nothing at all) |
//! | [`the_provision_dispatches_and_the_fact_does_not`] | FAILS — its fact leg dispatches |
//! | [`an_unresolved_bracketed_head_declares_a_predicate_rather_than_being_refused`] | passes either way (BY DESIGN — it pins the gate this ticket deliberately does NOT add; a gate that was built and removed) |
//! | [`a_bracketed_fact_head_over_a_declared_sort_still_loads`] | passes either way (BY DESIGN — its control) |
//! | [`a_parenthesised_head_records_no_provision`] | FAILS — the mirror defect: it banked a provision binding a spec parameter to the literal `1` |
//! | [`an_effect_kind_registers_through_provides_only`] | FAILS on its fact leg — the fact registered the kind |
//!
//! STILL OUT OF REACH, and deliberately: the BARE in-sort claim (`sort X { fact Box }`,
//! WI-365's effect-row-only spec, which has no bindings to write). It is textually
//! identical to an ordinary nullary fact, so no surface gate separates them — and after
//! the retirement it simply IS one. Every corpus site was bracketed.

use crate::common::{sort_provisions, try_load_kb_with};

/// Load errors for `src` (stdlib + host bindings + `src`), empty when clean.
fn errors(src: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_default()
}

/// Provisions of `spec_qn` recorded by `src`, by carrier. Panics on a dirty load, so
/// a row asserting "no provision" cannot pass because the program failed to load.
fn provisions_of(src: &str, spec_qn: &str) -> Vec<String> {
    let kb = match try_load_kb_with(src) {
        Ok(kb) => kb,
        Err(errs) => panic!("fixture did not load: {}", errs.join(" | ")),
    };
    sort_provisions(&kb)
        .into_iter()
        .filter(|(_, spec)| spec == spec_qn)
        .map(|(carrier, _)| carrier)
        .collect()
}

/// `Sp` is a spec with one member, defaulted so no carrier owes backing — otherwise a
/// green run could be `check_provider_operations` complaining about a provision that
/// WAS emitted, which is the opposite of what these rows measure.
const SPEC: &str = r#"
  sort Sp
    sort T = ?
    operation describe(x: T) -> Int64 = 0
  end
"#;

// ── The retirement: a `fact` records nothing, at either level ────────────────

/// IN A SORT BODY. `sort Carrier { fact Sp[T = Carrier] }` used to record the same
/// provision `provides Sp[T = Carrier]` records (058 §4, measured end to end); it
/// records none now.
#[test]
fn a_fact_in_a_sort_body_records_no_provision() {
    let src = format!(
        r#"
namespace s8jyf.inbody
  import anthill.prelude.{{Int64}}
{SPEC}
  sort Carrier
    entity carrier
    fact Sp[T = Carrier]
  end
end
"#
    );
    assert_eq!(
        provisions_of(&src, "s8jyf.inbody.Sp"),
        Vec::<String>::new(),
        "a `fact` in a sort body is an ordinary fact and records no provision"
    );
}

/// AT NAMESPACE LEVEL — the half 058 §4's deprecation did not cover, and where every
/// corpus site was. The carrier used to be DERIVED from the binding value.
#[test]
fn a_namespace_level_fact_records_no_provision() {
    let src = format!(
        r#"
namespace s8jyf.atns
  import anthill.prelude.{{Int64}}
{SPEC}
  sort Carrier
    entity carrier
  end
  fact Sp[T = Carrier]
end
"#
    );
    assert_eq!(
        provisions_of(&src, "s8jyf.atns.Sp"),
        Vec::<String>::new(),
        "a namespace-level `fact` records no provision; nothing derives a carrier \
         from a binding value any more"
    );
}

/// THE MIGRATION TARGET, and the control for the two rows above: the secondary entry
/// records exactly what the namespace-level fact used to — provider `Carrier`.
#[test]
fn the_secondary_entry_records_what_the_fact_used_to() {
    let src = format!(
        r#"
namespace s8jyf.entry
  import anthill.prelude.{{Int64}}
{SPEC}
  sort Carrier
    entity carrier
  end
  namespace Carrier
    provides Sp[T = Carrier]
  end
end
"#
    );
    assert_eq!(
        provisions_of(&src, "s8jyf.entry.Sp"),
        vec!["s8jyf.entry.Carrier".to_string()],
        "a `namespace <Carrier>` secondary entry files the provision under the carrier"
    );
}

/// AND IT DISPATCHES — the capability, driven rather than inferred from the fact row.
/// The carrier's own `describe` must be reached through the spec name, which happens
/// only if the provision reached the dispatch tables; the fact leg answers the spec's
/// DEFAULT instead, which is what "records nothing" costs at run time.
#[test]
fn the_provision_dispatches_and_the_fact_does_not() {
    let program = |ns: &str, claim: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
{SPEC}
  sort Carrier
    entity carrier
{claim}
    operation describe(x: Carrier) -> Int64 = 42
  end
  sort Driver
    operation drive() -> Int64 = Sp.describe(carrier())
  end
end
"#
        )
    };
    let drive = |ns: &str, claim: &str| {
        let src = program(ns, claim);
        let mut interp = crate::common::interp_for(&src);
        format!("{:?}", interp.call(&format!("{ns}.Driver.drive"), &[]))
    };
    assert_eq!(
        drive("s8jyf.disp.yes", "    provides Sp[T = Carrier]"),
        "Ok(Int(42))",
        "the provision routes `Sp.describe` to the carrier's own member"
    );
    assert_eq!(
        drive("s8jyf.disp.no", "    fact Sp[T = Carrier]"),
        "Ok(Int(0))",
        "the `fact` claims nothing, so the call takes the spec's default body"
    );
}

// ── What the retirement does NOT add: a gate at the head ─────────────────────

/// NO DIAGNOSTIC REPLACES THE SECOND READING, and this row is what says so rather
/// than leaving it to be re-derived.
///
/// A gate was built and REMOVED. 055-implementation §7 lists the fact HEAD beside
/// three sibling positions where a bracketed application over an unresolved name
/// already reports — a rule-body goal (`rule r(1) :- NoSuchSpec[T = C]`) and a fact
/// DATA slot (`fact p(NoSuchType[T = C])`) both say the name "names nothing" — and the
/// head looked like the fourth. It is not. Those three are REFERENCE positions, where
/// a name must resolve; a clause head is a DECLARATION (WI-20260821-RDGQC: a fact head
/// declares its predicate at the scope it is written in), so a head that resolves to
/// nothing is not an error but the ordinary way to introduce a predicate — including a
/// bracketed one carrying a type argument, which
/// `wi_c7anm_head_parameter_column_test::a_bracketed_head_binds_a_type_argument_not_a_
/// parameter` drives. MEASURED: refusing an unresolved bracketed head took that test
/// with it, and the only thing separating the two texts is that one name is
/// capitalized — which §2.3 does not read.
///
/// So what closes the ticket's silence is the retirement, not a diagnostic: with one
/// reading left there is no provision for a missing import to demote.
#[test]
fn an_unresolved_bracketed_head_declares_a_predicate_rather_than_being_refused() {
    let src = r#"
namespace s8jyf.head
  import anthill.prelude.{Int64}
  sort Red
    entity red
  end
  fact seedr(red())
  fact myrel[T = Red]
  rule probe(?t) :- myrel[T = ?t]
end
"#;
    assert_eq!(
        errors(src),
        Vec::<String>::new(),
        "a bracketed head introduces its predicate; the bracket binds a type argument"
    );
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(
        crate::common::query_unary(&mut kb, "s8jyf.head.probe")
            .into_iter()
            .map(|(v, _)| format!("{v:?}"))
            .collect::<Vec<_>>()
            .len(),
        1,
        "and the predicate answers — the head is a declaration, not a reference"
    );
}

/// THE CONTROL that keeps the row above from being about brackets at all: the same
/// bracketed shape over names that DO resolve loads clean, including a parametric DATA
/// sort, whose ordinary instantiation fact (`fact Polynom[Int64]`,
/// `anthill-testcases/ring-polynom`) must keep loading.
#[test]
fn a_bracketed_fact_head_over_a_declared_sort_still_loads() {
    let src = format!(
        r#"
namespace s8jyf.gate.ok
  import anthill.prelude.{{Int64}}
{SPEC}
  sort Poly
    sort R = ?
    entity poly(x: R)
  end
  fact Sp[T = Int64]
  fact Poly[Int64]
end
"#
    );
    assert_eq!(errors(&src), Vec::<String>::new());
}

// ── The mirror defect, and the effect-kind registration ──────────────────────

/// THE PARENS MIRROR DEFECT. `fact MySpec(T: 1)` used to bank `SortProvidesInfo(
/// sort_ref: Carrier, spec: SortView(MySpec, T: 1))` — a spec parameter bound to the
/// LITERAL 1. No `fact` is a provision now, so no parenthesised head can be read as
/// one, and the shape needs no gate of its own.
#[test]
fn a_parenthesised_head_records_no_provision() {
    let src = format!(
        r#"
namespace s8jyf.parens
  import anthill.prelude.{{Int64}}
{SPEC}
  sort Carrier
    entity carrier
    fact Sp(T: 1)
  end
end
"#
    );
    assert_eq!(
        provisions_of(&src, "s8jyf.parens.Sp"),
        Vec::<String>::new(),
        "a parenthesised head is a construction/assertion, never a provision"
    );
}

/// §5.5's EFFECT-KIND REGISTRATION migrates with everything else, and this drives the
/// capability rather than reading the provision row back: an operation may declare
/// `effects {MyEff}` only if `MyEff` is registered.
#[test]
fn an_effect_kind_registers_through_provides_only() {
    let program = |ns: &str, claim: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, Effect}}
  sort MyEff
{claim}
  end
  operation act(x: Int64) -> Int64 effects {{MyEff}}
end
"#
        )
    };
    assert_eq!(
        errors(&program("s8jyf.eff.yes", "    provides Effect[T = MyEff]")),
        Vec::<String>::new(),
        "`provides Effect[…]` registers the kind"
    );
    let errs = errors(&program("s8jyf.eff.no", "    fact Effect[T = MyEff]"));
    assert!(
        errs.iter()
            .any(|e| e.contains("is not a REGISTERED effect kind")),
        "a `fact` must not register an effect kind; got {errs:?}"
    );
}

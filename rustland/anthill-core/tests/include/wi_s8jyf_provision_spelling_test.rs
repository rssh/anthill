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
//! never a provision, and since WI-20261107-FDJ0E one headed by a sort's type application
//! is refused naming `provides`; an author who means a provision writes
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
//! | [`a_fact_in_a_sort_body_records_no_provision`] | FAILS — the fact records one (refused since WI-20261107-FDJ0E) |
//! | [`a_namespace_level_fact_records_no_provision`] | FAILS — the fact records one (refused since WI-20261107-FDJ0E) |
//! | [`the_secondary_entry_records_what_the_fact_used_to`] | passes either way (BY DESIGN — the `provides` route is what the migration moves TO, and it must work before and after; it is here so no other row can pass vacuously against a loader that records nothing at all) |
//! | [`the_provision_dispatches_and_the_fact_does_not`] | FAILS — its fact leg dispatches (refused since WI-20261107-FDJ0E) |
//! | [`an_unresolved_bracketed_head_is_refused`] | passes either way (BY DESIGN — this ticket adds no gate at the head; the refusal is WI-20260823-53W12's bracket on a relation, and fails with that backed out) |
//! | [`a_bracketed_fact_head_over_a_declared_sort_is_refused`] | WI-20261107-FDJ0E's refusal, not this ticket's |
//! | [`a_parenthesised_head_records_no_provision`] | FAILS — the mirror defect: it banked a provision binding a spec parameter to the literal `1` |
//! | [`an_effect_kind_registers_through_provides_only`] | FAILS on its fact leg — the fact registered the kind |
//!
//! THE BARE in-sort claim (`sort X { fact Box }`, WI-365's effect-row-only spec, which has
//! no bindings to write) was out of reach here and after the retirement simply was a nullary
//! fact. Since WI-20261107-FDJ0E a bare sort at a head is refused as its bracket is, `Box`
//! being `Box[…]` with every parameter open (`wi_fdj0e_type_application_goal_test`).

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
    assert_head_refused(&errors(&src), "Sp");
}

/// The refusal of a clause headed by `sort`'s type application (WI-20261107-FDJ0E), which
/// records nothing because it does not load.
fn assert_head_refused(errs: &[String], sort: &str) {
    assert!(
        errs.iter().any(|e| e.contains(&format!("`{sort}[…]` heads a clause")) && e.contains(&format!("`provides {sort}[…]`"))),
        "a clause headed by `{sort}[…]` is refused naming `provides`: {errs:?}"
    );
}

/// The same refusal over a sort with constructors, which provides itself: its repair is a
/// relation's argument.
fn assert_data_head_refused(errs: &[String], sort: &str) {
    assert!(
        errs.iter().any(|e| e.contains(&format!("`{sort}[…]` heads a clause"))
            && e.contains(&format!("`{sort}` declares constructors, so it provides itself"))),
        "a clause headed by `{sort}[…]` is refused naming a relation's argument: {errs:?}"
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
    assert_head_refused(&errors(&src), "Sp");
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
/// only if the provision reached the dispatch tables; the fact leg answered the spec's
/// DEFAULT instead, which is what "records nothing" cost at run time, and is refused at
/// load since WI-20261107-FDJ0E.
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
    assert_head_refused(&errors(&program("s8jyf.disp.no", "    fact Sp[T = Carrier]")), "Sp");
}

// ── What the retirement does NOT add: a gate at the head ─────────────────────

/// THE MISSING IMPORT IS LOUD, by a rule that reads no capitalization (WI-20260823-53W12,
/// user 2026-11-02). A clause head is a DECLARATION (WI-20260821-RDGQC), so a head that
/// resolves to nothing introduces its predicate, and a gate refusing an unresolved
/// bracketed head as an unresolved SPEC was built here and removed: it also refused
/// `fact myrel[T = Red]`, a predicate declared with a bracket, and the two texts differed
/// only in a capital letter, which §2.3 does not read. What refuses both now is the
/// bracket: a rule is an operation (proposal 060 §2.1), a bracket on either binds its type
/// parameters, and a relation is declared by its columns or with a type parameter. So the
/// missing-import shape is refused where it is written, saying no sort of the name is in
/// scope, and the column it stored before is written `myrel(T: Red)`.
#[test]
fn an_unresolved_bracketed_head_is_refused() {
    let src = r#"
namespace s8jyf.head
  import anthill.prelude.{Int64}
  sort Red
    entity red
  end
  fact seedr(red())
  fact myrel[T = Red]
  rule probe(?t) :- myrel(T: ?t)
end
"#;
    let errs = errors(src);
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(
        errs[0].contains("`myrel[…]` declares the relation `myrel` with a bracket")
            && errs[0].contains("No sort `myrel` is in scope here"),
        "{errs:?}"
    );
}

/// The same bracketed shape over names that DO resolve is a clause headed by a sort's type
/// application — a spec's and a parametric DATA sort's (the instantiation fact `fact
/// Polynom[Int64]` `anthill-testcases/ring-polynom` wrote) — refused, each once, naming
/// `provides`, not as a relation's bracket (WI-20261107-FDJ0E; it loaded before).
#[test]
fn a_bracketed_fact_head_over_a_declared_sort_is_refused() {
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
    let errs = errors(&src);
    assert_eq!(errs.len(), 2, "{errs:?}");
    assert_head_refused(&errs, "Sp");
    assert_data_head_refused(&errs, "Poly");
    assert!(!errs.iter().any(|e| e.contains("declares the relation")), "{errs:?}");
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
    // Since WI-20260902-JB6RS it is not even a fact: `Sp` names no constructor, predicate
    // or operation, so `Sp(…)` is refused where it is written — and so records nothing.
    let errs = errors(&src);
    assert!(
        errs.iter().any(|e| e.contains("`Sp(…)` is an application")),
        "a parenthesised head over a spec is refused, never a provision: {errs:?}"
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
  operation act(x: Int64) -> Int64 effects {{MyEff}} = 0
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

//! WI-946 — the belongs-to readers that had reached for the STRICT parent view.
//!
//! `KnowledgeBase::strict_parent_sort` (renamed here from
//! `constructor_parent_sort`) answers `None` for an EPONYMOUS `sort E { entity
//! E(…) }` and a free-standing `entity E(…)`, because §6.3/WI-926 make those one
//! symbol whose belongs-to edge is REFLEXIVE. Under its old name nothing said so,
//! and every "which sort does this belong to" reader picked it. WI-926/937/942
//! each fixed ONE such site; this file drives the rest.
//!
//! Every SUBJECT below is paired with a CONTROL that writes the SAME declaration
//! the sort-NESTED way. The two spellings disagreeing on whether a program is
//! accepted is the defect §6.3 exists to rule out, so the control is not decoration
//! — it is the statement of what "correct" means, and it passes both before and
//! after the change by design. Each subject FAILS if its conversion is backed out
//! (revert `sort_of_constructor` → `strict_parent_sort` at the named site).
//!
//! CONVERTED, each with the subject that fails under a revert of THAT site alone
//! (measured one site at a time, not as a batch):
//!   - `check_value_sort_membership` (via `check_value_against_sort_ref`) — silent accept
//!   - `check_value_against_parameterized` — silent accept
//!   - `Pattern::Constructor` pattern subst — FALSE rejection
//!   - `check_constructor` → `finish_constructor_type` — silent accept
//!   - `head_result_carrier` (the WI-652 eq-override probe) — under-report
//!   - `ctor_sort_sym` / `same_ctor_sort` (body_specialize.rs) — loud decline downstream
//!
//! CONVERTED WITHOUT ITS OWN SUBJECT, and said so rather than implied:
//!   - `constructor_value_type` — `check_constructor`'s WI-578 twin. Reverting it alone
//!     fails nothing; the strict/total difference is invisible through `value_type_term`,
//!     which answers a bare sort ref for both spellings. Converted for the no-drift tie,
//!     pinned by `the_value_typer_answers_both_spellings_alike`.
//!
//! NOT converted, measured and recorded at their sites:
//!   - `tuple_field_expected_from_ctor` — no probe made the hint's absence observable
//!     (`probe_tuple_field_hint_absence_is_unobservable`).
//!   - `pattern_var_ctor_sym` — the disjunct is unreachable; the written pattern name
//!     is a fresh binder symbol (`probe_pattern_var_ctor_fallback_is_unreachable`).

use anthill_core::eval::value::Value as EvalValue;
use anthill_core::kb::node_occurrence::{Expr, NodeOccurrence};
use anthill_core::kb::subst::Substitution;
use anthill_core::kb::term::{Literal, Term};
use anthill_core::kb::typing::{
    type_check_sorts, type_check_sorts_typed, value_type_term, TypeError,
};
use anthill_core::span::{SourceId, SourceSpan};
use std::rc::Rc;

/// Typed field/return errors for a source loaded on top of the stdlib.
fn typed_errors(source: &str) -> Vec<TypeError> {
    let (mut kb, result) = crate::common::load_stdlib_kb_with_source(source);
    type_check_sorts_typed(&mut kb, &result.defined_sorts)
}

/// Load-time errors (the channel that carries op-return conformance and
/// `EqOverrideUnbacked`).
fn load_errors(source: &str) -> Vec<String> {
    crate::common::try_load_kb_with(source).err().unwrap_or_default()
}

// ── The §6.3 shapes, as the KB records them ─────────────────────────────────
// The premise the whole file rests on, asserted rather than assumed: the strict
// view is blind to exactly the two spellings §6.3 calls equivalent to the third.

#[test]
fn strict_view_is_blind_to_the_reflexive_belongs_to_edge() {
    let source = r#"
sort Vec3
  entity Vec3(x: Float)
end
entity Loose(y: Float)
sort Shape
  entity Circle(r: Float)
end
"#;
    let (kb, _r) = crate::common::load_stdlib_kb_with_source(source);
    let sym = |n: &str| kb.try_resolve_symbol(n).unwrap_or_else(|| panic!("no symbol {n}"));

    // EPONYMOUS and FREE-STANDING: the edge is reflexive, so only the total view sees it.
    for name in ["Vec3", "Loose"] {
        let s = sym(name);
        assert_eq!(kb.sort_of_constructor(s), Some(s), "{name}: belongs-to is reflexive");
        assert_eq!(kb.strict_parent_sort(s), None, "{name}: the strict view cuts it");
    }
    // SORT-NESTED: the two agree, which is why the defect was invisible in the suite.
    let circle = sym("Shape.Circle");
    let shape = sym("Shape");
    assert_eq!(kb.sort_of_constructor(circle), Some(shape));
    assert_eq!(kb.strict_parent_sort(circle), Some(shape));
}

// ── 1. check_value_sort_membership — a field value of a FOREIGN sort ────────
// Was a SILENT ACCEPT: `parent?` returned early on the strict view's `None`.

const FIELD_MISMATCH_NESTED: &str = r#"
sort Colour
  entity Red
  entity Green
end
sort Shape
  entity Circle(r: Float)
end
sort Holder
  entity Holder(c: Colour)
end
fact Holder(c: Circle(r: 1.0))
"#;

const FIELD_MISMATCH_EPONYMOUS: &str = r#"
sort Colour
  entity Red
  entity Green
end
sort Vec3
  entity Vec3(x: Float)
end
sort Holder
  entity Holder(c: Colour)
end
fact Holder(c: Vec3(x: 1.0))
"#;

const FIELD_MISMATCH_FREE_STANDING: &str = r#"
sort Colour
  entity Red
  entity Green
end
entity Loose(x: Float)
sort Holder
  entity Holder(c: Colour)
end
fact Holder(c: Loose(x: 1.0))
"#;

/// CONTROL — passes with and without the change; it states what the subjects owe.
#[test]
fn control_a_nested_carrier_in_a_foreign_field_is_refused() {
    let errors = typed_errors(FIELD_MISMATCH_NESTED);
    assert_eq!(errors.len(), 1, "expected one field error, got {errors:?}");
}

#[test]
fn an_eponymous_carrier_in_a_foreign_field_is_refused() {
    let errors = typed_errors(FIELD_MISMATCH_EPONYMOUS);
    assert!(
        !errors.is_empty(),
        "`fact Holder(c: Vec3(...))` on a `Colour` field loaded clean — the strict view's \
         `None` reached `check_value_sort_membership`'s `parent?` as a silent accept"
    );
}

#[test]
fn a_free_standing_carrier_in_a_foreign_field_is_refused() {
    let errors = typed_errors(FIELD_MISMATCH_FREE_STANDING);
    assert!(!errors.is_empty(), "the free-standing spelling must be refused too");
}

/// The check must not OVER-fire: an eponymous carrier in its own field is fine.
#[test]
fn control_an_eponymous_carrier_in_its_own_field_is_accepted() {
    let errors = typed_errors(
        r#"
sort Vec3
  entity Vec3(x: Float)
end
sort Holder
  entity Holder(v: Vec3)
end
fact Holder(v: Vec3(x: 1.0))
"#,
    );
    assert!(errors.is_empty(), "an eponymous carrier in its OWN field must load, got {errors:?}");
}

/// A field declared `anthill.reflect.Term` holds a QUOTED term, so ANY carrier
/// conforms — the WI-385 rule `is_reflect_term_type` owns. Reaching the membership
/// check for a free-standing carrier (conversion 1) is what first EXERCISED that
/// rule here: before it, `entity Holder(pat: Term)` + `fact Holder(pat: Thing(...))`
/// (WI-716) was accepted only because the check was skipped, while the sort-NESTED
/// carrier in the same field was REFUSED. Both spellings are now accepted, for the
/// stated reason rather than by omission.
#[test]
fn a_quoted_term_field_accepts_either_spelling_of_carrier() {
    for (label, src) in [
        (
            "free-standing",
            r#"
namespace wi946.termfield.freestanding
  import anthill.reflect.Term
  entity Thing(id: String)
  entity Holder(pat: Term)
  fact Holder(pat: Thing(id: "z"))
end
"#,
        ),
        (
            "sort-nested",
            r#"
namespace wi946.termfield.nested
  import anthill.reflect.Term
  sort Shape
    entity Circle(r: Float)
  end
  entity Holder(pat: Term)
  fact Holder(pat: Circle(r: 1.0))
end
"#,
        ),
    ] {
        let errs = load_errors(src);
        assert!(errs.is_empty(), "{label} carrier must quote into a Term field: {errs:?}");
    }
}

// ── 2. check_value_against_parameterized — the WI-274 binding-precise check ──

const PARAM_FIELD_NESTED: &str = r#"
namespace wi946.paramfield.nested
  import anthill.prelude.{List, Int64, Float}
  sort Shape
    entity Circle(r: Float)
  end
  sort Holder
    entity Holder(l: List[T = Int64])
  end
  fact Holder(l: Circle(r: 1.0))
end
"#;

const PARAM_FIELD_EPONYMOUS: &str = r#"
namespace wi946.paramfield.eponymous
  import anthill.prelude.{List, Int64, Float}
  sort Vec3
    entity Vec3(x: Float)
  end
  sort Holder
    entity Holder(l: List[T = Int64])
  end
  fact Holder(l: Vec3(x: 1.0))
end
"#;

#[test]
fn control_a_nested_carrier_in_a_parameterized_field_is_refused() {
    let errors = typed_errors(PARAM_FIELD_NESTED);
    assert_eq!(errors.len(), 1, "expected one field error, got {errors:?}");
}

#[test]
fn an_eponymous_carrier_in_a_parameterized_field_is_refused() {
    let errors = typed_errors(PARAM_FIELD_EPONYMOUS);
    assert!(
        !errors.is_empty(),
        "the strict view's `None` skipped the belongs-to guard entirely and fell through \
         to the per-field walk, which the foreign carrier's own fields satisfy"
    );
}

// ── 3. Pattern::Constructor — the destructure's type-param substitution ─────
// Was a FALSE REJECTION: `build_pattern_subst` never ran, so the bound field kept
// the abstract `T` and the (correct) return type was reported as a mismatch.

const DESTRUCTURE_NESTED: &str = r#"
sort Crate
  sort T = ?
  entity Boxed(v: T)
  operation peek(c: Crate[T = Int64]) -> Int64 =
    match c
      case Boxed(v) -> v
    end
end
"#;

const DESTRUCTURE_EPONYMOUS: &str = r#"
sort Box
  sort T = ?
  entity Box(v: T)
  operation peek(b: Box[T = Int64]) -> Int64 =
    match b
      case Box(v) -> v
    end
end
"#;

#[test]
fn control_a_nested_parametric_destructure_resolves_its_type_param() {
    let errors = typed_errors(DESTRUCTURE_NESTED);
    assert!(errors.is_empty(), "`Boxed(v)` over `Crate[T = Int64]` binds v: Int64, got {errors:?}");
}

#[test]
fn an_eponymous_parametric_destructure_resolves_its_type_param() {
    let errors = typed_errors(DESTRUCTURE_EPONYMOUS);
    assert!(
        errors.is_empty(),
        "`case Box(v) -> v` returning Int64 out of a `Box[T = Int64]` was REJECTED — with no \
         parent sort there was no pattern subst, so `v` stayed the abstract `T`: {errors:?}"
    );
}

// ── 4. finish_constructor_type — the BUILT type's param bindings ────────────
// Was a SILENT ACCEPT: `finish_constructor_type` short-circuits on a `None`
// parent, so the build lost its bindings and a wrong declared binding conformed.

const BUILD_NESTED: &str = r#"
namespace wi946.build.nested
  import anthill.prelude.{Int64, String}
  sort Crate
    sort T = ?
    entity Boxed(v: T)
    operation mk(x: Int64) -> Crate[T = String] = Boxed(x)
  end
end
"#;

const BUILD_EPONYMOUS: &str = r#"
namespace wi946.build.eponymous
  import anthill.prelude.{Int64, String}
  sort Box
    sort T = ?
    entity Box(v: T)
    operation mk(x: Int64) -> Box[T = String] = Box(x)
  end
end
"#;

#[test]
fn control_a_nested_parametric_build_refuses_a_wrong_binding() {
    let errs = load_errors(BUILD_NESTED);
    assert!(
        errs.iter().any(|e| e.contains("Crate[T = Int64]")),
        "Boxed(Int64) must build Crate[T = Int64] and fail the declared Crate[T = String]: {errs:?}"
    );
}

#[test]
fn an_eponymous_parametric_build_refuses_a_wrong_binding() {
    let errs = load_errors(BUILD_EPONYMOUS);
    assert!(
        !errs.is_empty(),
        "`operation mk(x: Int64) -> Box[T = String] = Box(x)` loaded CLEAN — the build \
         produced a bare `Box` with no bindings to contradict the declaration"
    );
}

/// The VALUE typer (`constructor_value_type`) is `check_constructor`'s twin: WI-578
/// routes both through `finish_constructor_type` so ONE declaration yields ONE type.
/// It is converted with its twin and has NO independent failing case — measured, not
/// assumed: through `value_type_term` a constructed parametric value types as the BARE
/// sort ref under EITHER view, for either spelling, so the strict/total difference is
/// invisible from here. What justifies the conversion is the tie itself — leaving this
/// half on the strict view would make the two producers disagree for an eponymous
/// parametric sort, which is the drift the shared tail exists to prevent. This test
/// pins the parity that claim rests on.
fn built_value_type_is_parameterized(source: &str, ctor_qn: &str) -> bool {
    let (mut kb, _r) = crate::common::load_stdlib_kb_with_source(source);
    let ctor = kb.try_resolve_symbol(ctor_qn).unwrap_or_else(|| panic!("no ctor {ctor_qn}"));
    // Key the field by the DECLARED symbol — `constructor_value_type` matches named
    // children against `entity_field_types` by symbol identity.
    let (field, _) = kb.entity_field_types(ctor).expect("field schema")[0].clone();
    let value = EvalValue::Entity {
        functor: ctor,
        pos: vec![].into(),
        named: vec![(field, EvalValue::Int(5))].into(),
    };
    let ty = value_type_term(&mut kb, &Substitution::new(), &value);
    // A parameterized type is `Fn{S, named: [(T, Int64)]}`; a binding-less build is
    // the bare `Ref(S)` / `Fn{S}` sort ref.
    matches!(kb.get_term(ty.expect_term()), Term::Fn { named_args, .. } if !named_args.is_empty())
}

const VALUE_BUILD_NESTED: &str = r#"
namespace wi946.valuebuild.nested
  import anthill.prelude.{Int64}
  sort Crate
    sort T = ?
    entity Boxed(v: T)
  end
end
"#;

const VALUE_BUILD_EPONYMOUS: &str = r#"
namespace wi946.valuebuild.eponymous
  import anthill.prelude.{Int64}
  sort Box
    sort T = ?
    entity Box(v: T)
  end
end
"#;

#[test]
fn the_value_typer_answers_both_spellings_alike() {
    let nested =
        built_value_type_is_parameterized(VALUE_BUILD_NESTED, "wi946.valuebuild.nested.Crate.Boxed");
    let eponymous =
        built_value_type_is_parameterized(VALUE_BUILD_EPONYMOUS, "wi946.valuebuild.eponymous.Box");
    assert_eq!(
        nested, eponymous,
        "the two spellings must type alike here (parameterized: nested={nested}, \
         eponymous={eponymous})"
    );
    assert!(
        !nested,
        "measured: neither spelling reconstructs params through the value typer — if either \
         gains a parameterized build, this site needs its own subject test"
    );
}

/// The build must not OVER-fire: the RIGHT binding still loads.
#[test]
fn control_an_eponymous_parametric_build_accepts_the_right_binding() {
    let errs = load_errors(
        r#"
namespace wi946.build.eponymous.ok
  import anthill.prelude.{Int64}
  sort Box
    sort T = ?
    entity Box(v: T)
    operation mk(x: Int64) -> Box[T = Int64] = Box(x)
  end
end
"#,
    );
    assert!(errs.is_empty(), "the matching binding must still load, got {errs:?}");
}

// ── 5. head_result_carrier — the WI-652 eq-override-backing probe ───────────
// Was an UNDER-REPORT: a constructor-headed operand of an eponymous carrier
// resolved no carrier, so its unbacked `eq` override went unflagged.

const UNBACKED_EQ_NESTED: &str = r#"
namespace wi946.unbackedeq.nested
  import anthill.prelude.{Bool, Int64, Eq, PartialEq}
  sort Crate
    entity Boxed(v: Int64)
    operation eq(a: Crate, b: Crate) -> Bool
    provides Eq[T = Crate]
    provides PartialEq[T = Crate]
  end
  sort Drv
    operation same() -> Bool
    rule same() :- eq(Boxed(v: 1), Boxed(v: 2))
  end
end
"#;

const UNBACKED_EQ_EPONYMOUS: &str = r#"
namespace wi946.unbackedeq.eponymous
  import anthill.prelude.{Bool, Int64, Eq, PartialEq}
  sort Boxy
    entity Boxy(v: Int64)
    operation eq(a: Boxy, b: Boxy) -> Bool
    provides Eq[T = Boxy]
    provides PartialEq[T = Boxy]
  end
  sort Drv
    operation same() -> Bool
    rule same() :- eq(Boxy(v: 1), Boxy(v: 2))
  end
end
"#;

fn flags_unbacked_eq(errs: &[String], carrier: &str) -> bool {
    errs.iter().any(|e| e.contains("override declared but unimplemented") && e.contains(carrier))
}

#[test]
fn control_a_nested_ctor_operand_flags_an_unbacked_eq_override() {
    let errs = load_errors(UNBACKED_EQ_NESTED);
    assert!(
        flags_unbacked_eq(&errs, "Crate"),
        "`eq(Boxed(..), Boxed(..))` over an unbacked `Crate.eq` must be refused: {errs:?}"
    );
}

#[test]
fn an_eponymous_ctor_operand_flags_an_unbacked_eq_override() {
    let errs = load_errors(UNBACKED_EQ_EPONYMOUS);
    assert!(
        flags_unbacked_eq(&errs, "Boxy"),
        "`eq(Boxy(..), Boxy(..))` loaded CLEAN — `head_result_carrier` resolved no carrier \
         for the eponymous constructor, so the comparison that would silently misdecide at \
         resolution was never named at load: {errs:?}"
    );
}

// ── 6. same_ctor_sort — a definite non-match must be definite ───────────────
// Was a LOUD DECLINE downstream: the pattern arm read as undecidable, the residual
// stayed a `match`, and `flatten_arms` refused the whole per-call-site synth.

const SIBLINGS_ALL_NESTED: &str = r#"
namespace wi946.siblings.nested
  import anthill.prelude.{Int64}
  sort Mixed
    entity MixA(a: Int64)
    entity MixB(b: Int64)
  end
  sort Ops
    operation pick(m: Mixed) -> Int64 =
      match m
        case MixA(a) -> a
        case MixB(b) -> b
  end
end
"#;

const SIBLINGS_WITH_EPONYMOUS: &str = r#"
namespace wi946.siblings.eponymous
  import anthill.prelude.{Int64}
  sort Mix
    entity Mix(a: Int64)
    entity Other(b: Int64)
  end
  sort Ops
    operation pick(m: Mix) -> Int64 =
      match m
        case Mix(a) -> a
        case Other(b) -> b
  end
end
"#;

/// Drive the WI-687 per-call-site defining-rule synth at a concrete sibling
/// constructor. The generic (abstract-parameter) path declines a `match` body, so
/// this specialized path is the one that must reduce — and it only reduces if the
/// FIRST arm's pattern is a definite non-match against the argument's head.
fn synthesizes_at(source: &str, op_qn: &str, ctor_qn: &str, field: &str) -> bool {
    let (mut kb, _r) = crate::common::load_stdlib_kb_with_source(source);
    let sp = SourceSpan::new(SourceId::from_raw(0), 0, 0);
    let op = kb.try_resolve_symbol(op_qn).unwrap_or_else(|| panic!("no op {op_qn}"));
    let ctor = kb.try_resolve_symbol(ctor_qn).unwrap_or_else(|| panic!("no ctor {ctor_qn}"));
    let fsym = kb.intern(field);
    let five = NodeOccurrence::new_expr(Expr::Const(Literal::Int(5)), sp, None);
    let arg: Rc<NodeOccurrence> = NodeOccurrence::new_expr(
        Expr::Constructor {
            name: ctor,
            pos_args: vec![],
            named_args: vec![(fsym, five)],
            from_projection: false,
        },
        sp,
        None,
    );
    kb.synthesize_op_defining_rule_at(op, &[arg]).is_some()
}

#[test]
fn control_all_nested_siblings_synthesize_a_defining_rule() {
    assert!(
        synthesizes_at(
            SIBLINGS_ALL_NESTED,
            "wi946.siblings.nested.Ops.pick",
            "wi946.siblings.nested.Mixed.MixB",
            "b",
        ),
        "two sort-nested siblings must reduce at a concrete argument"
    );
}

#[test]
fn an_eponymous_ctor_and_its_sibling_are_the_same_sort() {
    assert!(
        synthesizes_at(
            SIBLINGS_WITH_EPONYMOUS,
            "wi946.siblings.eponymous.Ops.pick",
            "wi946.siblings.eponymous.Mix.Other",
            "b",
        ),
        "`same_ctor_sort(Mix, Other)` was FALSE though both are variants of `sort Mix`, so \
         the `case Mix(a)` arm read as undecidable, the residual stayed a `match`, and \
         `flatten_arms` declined the whole synth"
    );
}

// ── Recorded, NOT converted ────────────────────────────────────────────────
// These two probes pass identically before and after the change. They exist to
// pin the measurement that kept their sites on the strict view, so a later reader
// re-opens the question with evidence rather than re-deriving it.

/// `tuple_field_expected_from_ctor` keeps the strict view: with no hint, the
/// components still type bottom-up to what the hint would have pushed.
#[test]
fn probe_tuple_field_hint_absence_is_unobservable() {
    for (label, src) in [
        (
            "nested",
            r#"
namespace wi946.tuplehint.nested
  import anthill.prelude.{Int64}
  sort Crate
    sort T = ?
    entity Boxed(v: T)
    operation mk(a: Int64, b: Int64) -> Crate[T = (Int64, Int64)] = Boxed((a, b))
  end
end
"#,
        ),
        (
            "eponymous",
            r#"
namespace wi946.tuplehint.eponymous
  import anthill.prelude.{Int64}
  sort Box
    sort T = ?
    entity Box(v: T)
    operation mk(a: Int64, b: Int64) -> Box[T = (Int64, Int64)] = Box((a, b))
  end
end
"#,
        ),
    ] {
        assert!(load_errors(src).is_empty(), "{label} tuple field must load: {:?}", load_errors(src));
    }
}

/// `pattern_var_ctor_sym` keeps the strict view: the disjunct guarding it cannot
/// fire, because the written pattern name is a FRESH BINDER symbol. `Blue` is a
/// genuine `is_constructor_symbol` nullary constructor of another enum, yet is
/// treated as a catch-all binder exactly as the free-standing `Bare` is — if the
/// name resolved to the entity, this test's first case would report `missing Green`.
#[test]
fn probe_pattern_var_ctor_fallback_is_unreachable() {
    let missing = |source: &str| -> Vec<String> {
        let (mut kb, result) = crate::common::load_stdlib_kb_with_source(source);
        type_check_sorts(&mut kb, &result.defined_sorts)
            .iter()
            .map(|e| format!("{e}"))
            .filter(|s| s.contains("missing"))
            .collect()
    };

    // BASELINE — the exhaustiveness check is live in this shape.
    assert!(
        !missing(
            r#"
enum Colour
  entity Red
  entity Green
end
sort Test
  operation name(c: Colour) -> String =
    match c
      case Red -> "r"
    end
end
"#
        )
        .is_empty(),
        "baseline: a genuinely non-exhaustive match must report a missing case"
    );

    for (label, extra_decl, arm) in [
        ("nested nullary ctor", "enum Other\n  entity Blue\nend", "Blue"),
        ("free-standing entity", "entity Bare", "Bare"),
        ("eponymous sort", "sort Solo\n  entity Solo\nend", "Solo"),
    ] {
        let src = format!(
            r#"
enum Colour
  entity Red
  entity Green
end
{extra_decl}
sort Test
  operation name(c: Colour) -> String =
    match c
      case Red -> "r"
      case {arm} -> "x"
    end
end
"#
        );
        assert!(
            missing(&src).is_empty(),
            "{label}: the arm reads as a catch-all BINDER (fresh binder symbol), so no \
             missing case is reported — same answer for all three spellings"
        );
    }
}

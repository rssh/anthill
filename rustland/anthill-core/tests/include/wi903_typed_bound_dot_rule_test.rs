//! WI-903 — a typed rule pattern (`?x: T`) on a DOT rule is REFUSED at load.
//!
//! WI-582's bound is enforced by exactly ONE site: the resolver's
//! `apply_eq_rules` / `typed_pattern_bounds_hold`, over a `@[simp]` directional
//! rewrite. `load.rs` therefore refuses the annotation on every
//! other rule shape LOUDLY — "a non-rewrite rule would silently ignore it".
//!
//! A DOT rule (`rule dr: dot_apply(?e, m, ?x) = rhs @[simp]`, WI-279 INC2) passed
//! that check and then ignored the bound anyway: it is fired by
//! `typing::try_fire_dot_rule` against a surface `Expr::DotApply` occurrence — a
//! typer-side path that never reads `kb.rule_type_bounds` — and the resolver
//! never sees a `dot_apply` head at all. MEASURED before the fix: an
//! UNSATISFIABLE bound (`?x: String` against a literal `5`) loaded clean and
//! FIRED.
//!
//! The fix is the loader's, not the firing site's: the typer does not enforce
//! typed bounds ANYWHERE (`simp_rewrite::try_fire` skips such rules outright), so
//! a rule shape only the typer can fire can never enforce one. Refusing it makes
//! that unrepresentable instead of adding a second, divergent enforcer.
//!
//! Both of the loader's gates are now asked in a FIRING site's own terms, which
//! closed a sibling leak the same question exposed — see
//! `typed_bound_on_a_guarded_equation_is_refused`. The plain WI-582 case (an
//! operation-headed `@[simp]` equation keeps its bound) is not re-pinned here: it
//! is `wi582_typed_rule_pattern_test`'s subject, asserted there with its DeBruijn
//! index and its three firing behaviours.

use crate::common::{head_short, load_kb_with, try_load_kb_with};
// The effectful-rewrite gate's marker is OWNED by the suite that asserts it
// PRESENT — re-spelling the literal here, where it is asserted ABSENT, would pass
// vacuously the moment that rendering changed.
use crate::wi757_macro_diagnostic_test::EFFECTFUL_REWRITE_MARKER;

/// The refusal's stable marker — the ticket id the loader stamps on it.
const WI903: &str = "WI-903";

/// Errors mentioning `needle`, for asserting presence/absence of one diagnostic
/// without pinning the whole rendering.
fn mentioning<'a>(errs: &'a [String], needle: &str) -> Vec<&'a String> {
    errs.iter().filter(|e| e.contains(needle)).collect()
}

/// A dot rule whose argument bound is UNSATISFIABLE at the only call site: `?x:
/// String` against `?h.bump(5)`. `bump` exists ONLY as this rule, so whether the
/// rule fires is directly observable — the consumer's body is `wrapped(...)` if
/// it fired, and the load fails on an unknown member if it did not.
///
/// `{bound}` is spliced so the annotated and unannotated forms differ in exactly
/// the annotation, and nothing else can explain a behaviour difference.
fn dot_rule_src(bound: &str) -> String {
    format!(
        r#"
namespace test.wi903
  import anthill.prelude.{{Int64, String}}
  import anthill.prelude.Numeric.{{add}}
  import anthill.prelude.Additive.{{add}}

  sort Holder
    entity holder(value: Int64)

    operation wrapped(h: Holder, v: Int64) -> Int64 = add(v, 100)

    rule dr: dot_apply(?e, bump, ?x{bound}) <=> wrapped(?e, ?x) @[simp]

    operation consumer(h: Holder) -> Int64 = ?h.bump(5)
  end
end
"#
    )
}

/// The defect, as a refusal: the annotated form does not load, and the message
/// names the rule (`dr`) so the author can find it.
#[test]
fn typed_bound_dot_rule_is_refused_at_load() {
    let errs = try_load_kb_with(&dot_rule_src(": String"))
        .err()
        .expect("a typed-bound dot rule must be refused at load");
    let found = mentioning(&errs, WI903);
    let [msg] = found[..] else {
        panic!("expected exactly one WI-903 refusal, got: {errs:?}");
    };
    assert!(
        msg.contains("dr"),
        "the refusal must name the offending rule so it can be found: {msg}",
    );
    assert!(
        msg.contains("dot_apply"),
        "the refusal must name the rule SHAPE it is about: {msg}",
    );
    // LOCATED — the whole reason this is a span-bearing variant and not a
    // `LoadError::Other`. Without this the diagnostic could silently degrade to the
    // unlocated rendering (and, being keyed on that rendering, `dedup_load_errors`
    // would then collapse two offending rules) with the suite still green.
    let head_line = dot_rule_src(": String")
        .lines()
        .position(|l| l.contains("rule dr:"))
        .expect("the fixture has the rule line")
        + 1;
    assert!(
        msg.starts_with(&format!("{head_line}:")),
        "the refusal must carry the rule head's location, got: {msg}",
    );
}

/// The refusal is keyed on the ANNOTATION, not on the dot-rule shape: the same
/// rule without `: String` still loads and still fires (WI-279 INC2 intact).
#[test]
fn unannotated_dot_rule_still_loads_and_fires() {
    let kb = load_kb_with(&dot_rule_src(""));
    let consumer = kb
        .try_resolve_symbol("test.wi903.Holder.consumer")
        .expect("consumer resolves");
    let body = kb.op_body_node(consumer).expect("consumer has a body node");
    assert_eq!(
        head_short(&kb, &body),
        "wrapped",
        "the unannotated dot rule must still rewrite `?h.bump(5)` to `wrapped(h, 5)`",
    );
}

/// The sibling leak, found by the same question and MEASURED the same way — AND THE
/// ROW THAT SHOWS THE DISCIPLINE PAYING OFF.
///
/// The loader used to ask its OWN version of "is this a rewrite" — `is_equational_head`
/// plus a `@[simp]`/`@[unfold]` tag — which was wider than the predicate the resolver
/// actually fires on. A GUARDED equation therefore installed its bound while no site
/// could read it: measured `rule_type_bounds == [(1, …)]` with
/// `kb.is_equation(rid) == false`. WI-903 made the loader ask `is_directional_equation`
/// instead, and the guarded case became refused.
///
/// WI-20260820-8RJK8 THEN MADE IT FIRE, and because the loader borrows the firing
/// site's predicate rather than restating it, the refusal narrowed with NO EDIT AT THE
/// LOADER. A `@[simp]`-tagged guarded equation is a directional rewrite, so
/// `fire_simp_equation` runs `typed_pattern_bounds_hold` on it and the bound has its
/// reader — it is KEPT below. The UNTAGGED spelling is still refused, and for the
/// reason it always had: nothing fires it (`@[simp]` is the enablement, WI-881).
///
/// Both rows over ONE program text, so nothing but the tag differs.
#[test]
fn typed_bound_on_a_guarded_equation_follows_the_tag() {
    const SRC: &str = r#"
namespace test.wi903guarded
  import anthill.prelude.{Int64}
  import anthill.prelude.Ord.{gt}

  sort Summable
    sort T = ?
  end


  sort Lib
    operation pick(x: Int64, y: Int64) -> Int64
    rule pk: pick(?x: Summable.T, ?y) = ?y :- gt(?y, 0) TAG
  end
end

namespace anthill.prelude.Int64
  import test.wi903guarded.Summable
  provides Summable[T = Int64]
end
"#;
    // TAGGED: a conditional rewrite, so the bound is installed and enforced at the match.
    let kb = load_kb_with(&SRC.replace("TAG", "@[simp]"));
    let rid = kb
        .rule_id_by_qn("test.wi903guarded.Lib.pk")
        .expect("the tagged guarded equation loads");
    assert_eq!(
        kb.rule_type_bounds(rid).len(),
        1,
        "a TAGGED guarded equation is fired by `fire_simp_equation`, which enforces \
         typed-pattern bounds — so the bound is kept, not refused",
    );

    // UNTAGGED: nothing fires it, so the bound would be ignored — still refused.
    let errs = try_load_kb_with(&SRC.replace("TAG", ""))
        .err()
        .expect("an untagged equation cannot enforce a bound");
    let found = mentioning(&errs, "WI-582");
    let [msg] = found[..] else {
        panic!("expected exactly one typed-pattern refusal, got: {errs:?}");
    };
    assert!(
        msg.contains("pk"),
        "the refusal must name the offending rule: {msg}"
    );
    // …and must NOT tell the author to drop the guard: a `Spec[T]` INTRODUCER guard
    // is where the bound comes from in the `k[T](?x: T, ?y) = ?x :- Summable[T]`
    // spelling (`wi619_two_ary_head_introducer_test`), which folds and loads fine.
    assert!(
        !msg.contains("drop its `:- …` guard"),
        "the advice must not push the author toward deleting the guard that \
         SUPPLIES the bound in the introducer form: {msg}",
    );
    assert!(
        !msg.contains("bodyless"),
        "the message must no longer say a rewrite is bodyless — since 8RJK8 a tagged \
         guarded equation IS one, and the untagged rule's fault is the missing tag: {msg}",
    );
}

/// A dot rule written OUTSIDE a sort, its `rule_domain` a namespace — the residual
/// WI-906 recorded at `simp_rewrite::is_typer_fired_dot_rule`. The refusal is keyed on
/// the rule's shape and does not ask the typer's per-receiver enclosing-sort guard, so
/// this rule is refused a bound although no receiver passes that guard. The one place
/// its bound would be read is a defect's path (WI-20261105-8412E: a dot left as a term
/// in the right-hand side of a typed-bound equation, which the resolver alone fires),
/// and the user decided (2026-11-05) the bound stays refused there too.
///
/// `RULE_IN_SORT` / `RULE_OUTSIDE` place the one rule text, and `CALLER` is written
/// beside the sort either way, so the two placements differ in where the rule is and in
/// nothing else.
const PLACED_DOT_RULE: &str = r#"
namespace test.wi903ns
  import anthill.prelude.{Int64, String}
  import anthill.prelude.Numeric.{add}

  sort Holder
    entity holder(value: Int64)
    operation wrapped(h: Holder, v: Int64) -> Int64 = add(v, 100)
RULE_IN_SORT
  end
RULE_OUTSIDE
CALLER
end
"#;

/// `PLACED_DOT_RULE` with the rule `inside` its sort or beside it, its `?x` annotated
/// `bound`, and `caller` written beside the sort.
fn placed_dot_rule(inside: bool, bound: &str, caller: &str) -> String {
    let rule = format!("  rule dr: dot_apply(?e, bump, ?x{bound}) <=> Holder.wrapped(?e, ?x) @[simp]");
    let (in_sort, outside) = if inside { (rule, String::new()) } else { (String::new(), rule) };
    PLACED_DOT_RULE
        .replace("RULE_IN_SORT", &in_sort)
        .replace("RULE_OUTSIDE", &outside)
        .replace("CALLER", caller)
}

const CONSUMER: &str = "  operation consumer(h: Holder) -> Int64 = ?h.bump(5)";

#[test]
fn typed_bound_on_a_dot_rule_outside_a_sort_is_refused() {
    let errs = try_load_kb_with(&placed_dot_rule(false, ": String", ""))
        .err()
        .expect("a typed-bound dot rule outside a sort is refused like any other");
    let found = mentioning(&errs, WI903);
    let [msg] = found[..] else {
        panic!("expected exactly one WI-903 refusal, got: {errs:?}");
    };
    assert!(msg.contains("dr"), "the refusal must name the rule: {msg}");
    // CONTROL: without the annotation the rule loads — the refusal is the bound's.
    assert!(
        try_load_kb_with(&placed_dot_rule(false, "", "")).is_ok(),
        "the unannotated rule must load"
    );
}

/// …and it fires at no dot call: beside the sort, `?h.bump(5)` finds no member. Passes
/// either way by design — it pins a property of the dot path, not of the refusal. The
/// next row is its control.
#[test]
fn a_dot_rule_outside_a_sort_fires_at_no_dot_call() {
    let errs = try_load_kb_with(&placed_dot_rule(false, "", CONSUMER))
        .err()
        .expect("the dot call must find no member: the rule beside the sort does not fire");
    assert!(
        errs.iter().any(|e| e.contains("bump") && e.contains("no such member")),
        "expected the dot call to be answered `no such member`, got: {errs:?}"
    );
}

/// The control for the row above (found missing by `/code-review`): the SAME fixture
/// and the same caller, with only the rule moved into its sort — and the call is
/// rewritten. So "no such member" above is the rule's placement, not the caller's or
/// the fixture's.
#[test]
fn the_same_dot_rule_inside_its_sort_fires_at_that_call() {
    let kb = load_kb_with(&placed_dot_rule(true, "", CONSUMER));
    let consumer = kb
        .try_resolve_symbol("test.wi903ns.consumer")
        .expect("consumer resolves");
    let body = kb.op_body_node(consumer).expect("consumer has a body node");
    assert_eq!(
        head_short(&kb, &body),
        "wrapped",
        "inside its sort, the dot rule must rewrite `?h.bump(5)` to `wrapped(h, 5)`",
    );
}

/// The knock-on this ticket retires. The WI-702/054 effectful-rewrite gate exempts
/// a MACRO-headed RHS whose call the expander evaluates away, keyed (via
/// `macro_expanded_rhs_head`) on the conditions `simp_rewrite::try_fire` applies —
/// one being "no typed-pattern bounds". Since WI-902 the DOT site expands macros
/// too, so an `Error`-declaring macro under a typed-bound dot rule was refused by
/// that gate as well, for a call that is in fact expanded away.
///
/// With the bound refused at load, no dot rule carries bounds, so the gate's
/// condition is exact again: this source is refused ONCE — for the bound — and the
/// effectful-rewrite message is gone.
#[test]
fn effectful_macro_under_a_typed_bound_dot_rule_is_refused_only_for_the_bound() {
    const SRC: &str = r#"
namespace test.wi903macro
  import anthill.prelude.{Int64, String}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Numeric.{add}
  import anthill.reflect.{NodeOccurrence, make_apply}

  sort Boom
    entity boom(why: String)
  end

  sort Holder
    entity holder(value: Int64)

    operation wrapped(h: Holder, v: Int64) -> Int64 = add(v, 100)

    -- Declares `Error` (the WI-757 rejection channel) without raising: the
    -- effectful-rewrite gate is about the DECLARED row, not a taken raise.
    operation wrap(r: NodeOccurrence, x: NodeOccurrence) -> NodeOccurrence effects Error[Boom] =
      make_apply("test.wi903macro.Holder.wrapped", cons(r, cons(x, nil())), r)

    rule dr: dot_apply(?e, bump, ?x: String) <=> wrap(?e, ?x) @[simp]

    operation consumer(h: Holder) -> Int64 = ?h.bump(5)
  end
end
"#;
    let errs = try_load_kb_with(SRC)
        .err()
        .expect("the typed bound must fail the load");
    assert_eq!(
        mentioning(&errs, WI903).len(),
        1,
        "the bound is the ONE reason this source is refused: {errs:?}",
    );
    assert!(
        mentioning(&errs, EFFECTFUL_REWRITE_MARKER).is_empty(),
        "the effectful-rewrite gate must no longer fire for a macro the dot site \
         expands away — that divergence is what WI-903 retires: {errs:?}",
    );
}

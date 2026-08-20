//! WI-902 — a compile-time MACRO expands at the DOT-RULE firing site too.
//!
//! There are two typer-side `[simp]` firing sites. `simp_rewrite::try_fire`
//! (the Apply/Constructor redex) builds the RHS template and then macro-expands
//! it, so `rule trigger(?x) <=> wrap(?x) [simp]` runs `wrap` at compile time
//! (WI-722) and a `wrap` that rejects reports through the WI-757 channel.
//! `typing::try_fire_dot_rule` — the WI-279 INC2 sort-scoped path, `rule dr:
//! dot_apply(?e, m, ?x) = wrap(?e, ?x) [simp]` — ended at the template and never
//! expanded, so a macro-headed dot rule silently declined: the pattern vars
//! arrived at `wrap` as their VALUE types and the author read the residual
//! template's `op-arg` mismatch — exactly the message WI-757 exists to replace.
//!
//! Both sites now share ONE step (`simp_rewrite::instantiate_rhs`: substitute,
//! then expand-if-macro), so these assertions are the dot-site mirror of the
//! WI-722 / WI-757 suites.

use crate::common::{head_short, interp_for, load_kb_with, try_load_kb_with};
// The rejection marker + filter are the WI-757 suite's, not re-spelled here: both
// suites assert the marker's ABSENCE to prove a decline, so one owner keeps a
// rendering change from making either pass vacuously.
use crate::wi757_macro_diagnostic_test::rejections;
use anthill_core::eval::Value;

/// A sort whose `bump` member exists ONLY as a macro-headed dot rule. `wrap`
/// builds `wrapped(h, x)` — a functor DIFFERENT from the macro's own name, so a
/// real expansion is observable and a kept template is not mistaken for one.
const EXPANDS: &str = r#"
namespace test.wi902
  import anthill.prelude.{Int64}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Numeric.{add}
  import anthill.reflect.{NodeOccurrence, make_apply}

  sort Holder
    entity holder(value: Int64)

    -- The macro's OUTPUT target — an ordinary op, never a macro.
    operation wrapped(h: Holder, v: Int64) -> Int64 = add(v, 100)

    -- The MACRO: receiver occurrence + argument occurrence -> occurrence.
    operation wrap(r: NodeOccurrence, x: NodeOccurrence) -> NodeOccurrence =
      make_apply("test.wi902.Holder.wrapped", cons(r, cons(x, nil())), r)

    -- No `bump` operation exists: the body below type-checks only if this rule
    -- fires AND its macro RHS is expanded away.
    rule dr: dot_apply(?e, bump, ?x) <=> wrap(?e, ?x) [simp]

    operation consumer(h: Holder) -> Int64 = ?h.bump(5)

    -- A nullary entry point, so the rewrite can be observed by EVALUATION too.
    operation run() -> Int64 = consumer(holder(value: 1))
  end
end
"#;

/// The macro fires at COMPILE time from a dot rule: the consumer's stored body is
/// `wrapped(h, 5)`, the macro's output — not the `wrap(...)` template and not the
/// original `?h.bump(5)`.
#[test]
fn dot_rule_macro_expands_at_compile_time() {
    let kb = load_kb_with(EXPANDS);
    let consumer = kb
        .try_resolve_symbol("test.wi902.Holder.consumer")
        .expect("consumer resolves");
    let body = kb.op_body_node(consumer).expect("consumer has a body node");
    assert_eq!(
        head_short(&kb, &body),
        "wrapped",
        "the dot rule's macro RHS should have been expanded to `wrapped(...)` at \
         compile time (a `wrap` head means the template was kept)",
    );
}

/// End-to-end: the macro-built occurrence re-types and evaluates —
/// `?h.bump(5)` → `wrapped(h, 5)` → `add(5, 100)` → `105`.
#[test]
fn dot_rule_macro_output_re_types_and_evaluates() {
    let mut interp = interp_for(EXPANDS);
    let got = interp
        .call("test.wi902.Holder.run", &[])
        .expect("run evaluates");
    match got {
        Value::Int(n) => assert_eq!(n, 105, "wrapped(h, 5) = add(5, 100) = 105"),
        other => panic!("expected Int(105), got {other:?}"),
    }
}

/// A macro that REJECTS from a dot rule reports through WI-757's channel — the
/// macro's own words at the redex — rather than the residual template's `op-arg`
/// mismatch on a parameter the author never wrote.
///
/// Located at the DOT REDEX: a `raise` carries a payload and no occurrence, so the
/// span is the reporter's (043.1 §7 / WI-901 is the op that would narrow it), and
/// the reporter here is the DotApply frame — the whole `?h.bump(5)`, not the
/// enclosing operation and not the rule.
#[test]
fn dot_rule_macro_rejection_reports_through_the_wi757_channel() {
    const SRC: &str = r#"
namespace test.wi902reject
  import anthill.prelude.{Int64, String}
  import anthill.reflect.{NodeOccurrence}

  sort Boom
    entity boom(why: String)
  end

  sort Holder
    entity holder(value: Int64)

    -- The macro REJECTS: it raises, which WI-757 turns into a rejection.
    operation wrap(r: NodeOccurrence, x: NodeOccurrence) -> NodeOccurrence effects Error[Boom] =
      Error.raise(boom(why: "bump is not translatable here"))

    rule dr: dot_apply(?e, bump, ?x) <=> wrap(?e, ?x) [simp]

    operation consumer(h: Holder) -> Int64 = ?h.bump(5)
  end
end
"#;
    let errs = try_load_kb_with(SRC)
        .err()
        .expect("a rejecting macro must fail the load");
    let [rejection] = rejections(&errs)[..] else {
        panic!("expected exactly one macro rejection, got: {errs:?}");
    };
    for fragment in [
        "test.wi902reject.Holder.wrap",
        "bump is not translatable here",
    ] {
        assert!(
            rejection.contains(fragment),
            "missing {fragment:?} in: {rejection}"
        );
    }
    assert!(
        !errs.iter().any(|e| e.contains("op-arg")),
        "the residual template's op-arg type error must not be what the author reads, \
         got: {errs:?}",
    );
    // The dot redex `?h.bump(5)` — computed from the source, so an edit to the
    // fixture cannot silently un-anchor the assertion.
    let line = SRC
        .lines()
        .position(|l| l.contains("?h.bump(5)"))
        .expect("the fixture's redex")
        + 1;
    let col = SRC.lines().nth(line - 1).unwrap().find("?h.bump").unwrap() + 1;
    assert!(
        rejection.starts_with(&format!("{line}:{col}:")),
        "expected the rejection at the dot redex ({line}:{col}), got: {rejection}",
    );
}

/// The DECLINE path is unchanged at the dot site: a macro outside the expander's
/// positional surface (a NAMED-argument RHS head) is left as a template, and the
/// author reads its own downstream type-check — the WI-722 contract, mirrored
/// from `wi757_macro_diagnostic_test::a_macro_that_is_not_applicable_still_declines_quietly`.
#[test]
fn dot_rule_macro_that_is_not_applicable_still_declines_quietly() {
    const SRC: &str = r#"
namespace test.wi902decline
  import anthill.prelude.{Int64}
  import anthill.prelude.List.{cons, nil}
  import anthill.reflect.{NodeOccurrence, make_apply}

  sort Holder
    entity holder(value: Int64)
    operation wrapped(h: Holder, v: Int64) -> Int64 = v
    operation wrap(r: NodeOccurrence, x: NodeOccurrence) -> NodeOccurrence =
      make_apply("test.wi902decline.Holder.wrapped", cons(r, cons(x, nil())), r)

    rule dr: dot_apply(?e, bump, ?x) <=> wrap(r: ?e, x: ?x) [simp]

    operation consumer(h: Holder) -> Int64 = ?h.bump(5)
  end
end
"#;
    let errs = try_load_kb_with(SRC)
        .err()
        .expect("the kept template must fail to type-check");
    assert!(
        rejections(&errs).is_empty(),
        "a macro that is merely not applicable must DECLINE, not reject: {errs:?}",
    );
    assert!(
        errs.iter()
            .any(|e| e.contains("(op-arg)") && e.contains("expected NodeOccurrence")),
        "the kept template's own type-check is what must surface, got: {errs:?}",
    );
}

/// SELECTION reads BOTH equation buckets, which is what lets a dot rule spelled `<=>`
/// fire at all.
///
/// This site used to re-scan the `eq` bucket alone, so a `<=>` dot rule was never a
/// candidate and silently did not fire — while `is_equation`, `stored_lhs_functor`,
/// `open_equation` and `rule_domain`, everything downstream of selection, are all
/// connective-agnostic. It matters for WI-902 in particular because 043.1 writes its
/// macro rules `<=>` (`rule where(?r, ?c) <=> guarded_of(?r, ?c) [simp]`), so the
/// dot-rule macro expansion above would have been dead for the idiomatic spelling.
///
/// WI-888 REPLACED THIS TEST'S CONTROL, and the replacement is stated rather than
/// quietly dropped. It used to drive the SAME rule twice, once per connective, and
/// assert both fired — a genuine two-arm pin while both spellings loaded. A bodyless
/// `=` head is now a load error, so that arm cannot exist: the `=` row below asserts
/// the REFUSAL instead, which is a different claim.
///
/// What guards the original regression now is the corpus, not this test: after the
/// migration EVERY equation in the stdlib is `<=>`, so an eq-only rescan here would
/// stop firing all of them at once rather than one idiomatic spelling silently. That is
/// a strictly louder guard, and it is the honest thing to say — this test no longer
/// measures it.
#[test]
fn a_unify_spelled_dot_rule_fires_and_an_eq_spelled_one_is_refused() {
    let src = |ns: &str, conn: &str| {
        format!(
            r#"
namespace test.wi902conn{ns}
  import anthill.prelude.{{Int64}}
  sort Holder
    entity holder(value: Int64)
    operation regular(h: Holder, v: Int64) -> Int64 = v
    -- No `bump` operation exists, so this body type-checks only if the rule fired.
    rule dr: dot_apply(?e, bump, ?x) {conn} regular(?e, ?x) [simp]
    operation consumer(h: Holder) -> Int64 = ?h.bump(5)
  end
end
"#
        )
    };
    assert!(
        try_load_kb_with(&src("unify", "<=>")).is_ok(),
        "a `<=>`-spelled [simp] dot rule must fire: {:?}",
        try_load_kb_with(&src("unify", "<=>")).err(),
    );
    // The `=` arm: refused at the HEAD, before selection is ever reached. The subject is
    // the desugar's own `dot_apply`, so the refusal names no user callable — it must
    // still name the substitute spelling.
    let errs = try_load_kb_with(&src("eq", "="))
        .err()
        .expect("a bodyless `=` head is refused (WI-888)");
    let joined = errs.join("\n");
    assert!(
        joined.contains("<=>"),
        "the refusal must name the substitute spelling, got: {joined}",
    );
}

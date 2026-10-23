//! WI-905 — a call a `@[simp]` rewrite reaches only where it fires is held, there, to
//! the refusal a rule naming an effectful operation gets at load.
//!
//! The load-time gate (`typing::check_simp_effectful_ops`) refuses a rule for each
//! potentially effectful operation it NAMES. Three calls a rule puts in a body are known
//! only at the call it fires on, and are judged at that call: a dot in the rule's text,
//! whose operation is its receiver's; the call a dot rule replaces; and a call its macro
//! builds. Every refused program below loaded clean on the tree before, and the ones
//! that ran performed the effect with no diagnostic.
//!
//! The gate also stopped reading a dot's member by the name it resolves to where the
//! rule is written. That reading caught a dot on the rule's own sort, and refused a dot
//! that reaches a pure operation when the rule's sort had an effectful one of the name.
//!
//! BACK-OUT, measured with each part switched off alone in one build:
//!  * the dot check (`typing::effectful_rewrite_call`): the seven `a_dot_…` refusal rows
//!    (another sort, an argument, an operation-headed rule, a sort-denoting receiver, the
//!    rule's own sort, a rule body and a const, a rewrite inside a rewrite) and
//!    `the_refusal_is_located_in_the_callers_file` fail; switched off at the
//!    sort-denoting receiver alone (`typing::written_sort_dot`), its one row fails;
//!  * the gate's reading by name (`collect_op_functors_in_term`): `a_pure_operation_…`
//!    and `a_rule_no_call_fires_on_…` fail, and `a_dot_on_the_rules_own_sort_…` fails
//!    on its count — the gate's refusal joins the call's;
//!  * the replaced call (`typing::replaced_call_refusal`): the two
//!    `a_dot_rule_replacing_…` rows fail;
//!  * the macro's calls (`simp_rewrite::effectful_macro_call`): the two `a_call_a_macro_…`
//!    rows fail — the nested one has a pure root, so a check of the root alone fails it.
//! The controls — a pure dot, a dot rule that replaces no call, a pure macro target, the
//! caller's own effectful argument a macro gives back — pass either way by design.

use crate::common::{interp_for, load_errors_of, load_kb_with, try_load_kb_with_named_files};
use crate::wi757_macro_diagnostic_test::EFFECTFUL_REWRITE_MARKER;
use anthill_core::eval::Value;

/// `Other.risky` raises, so it is effectful; `Other.calm` is its pure twin.
const DECLS: &str = r#"
  import anthill.prelude.{Int64, String}
  import anthill.prelude.Numeric.{add}
  sort Boom
    entity boom(why: String)
  end
  sort Other
    entity other(v: Int64)
    operation risky(o: Other, x: Int64) -> Int64 effects Error[Boom] =
      Error.raise(boom(why: "risky ran"))
    operation calm(o: Other, x: Int64) -> Int64 = add(x, 100)
  end
"#;

fn program(ns: &str, body: &str) -> String {
    format!("namespace test.{ns}\n{DECLS}\n{body}\nend\n")
}

/// The one refusal `src` loads with, which must say `clause` of `rule` reaching `op`,
/// located on the line of `src` holding `at` — the call the rule fired on.
fn refused_once(src: &str, rule: &str, clause: &str, op: &str, at: &str) {
    let errs = load_errors_of(src);
    let [err] = &errs[..] else {
        panic!("expected exactly one refusal, got: {errs:#?}");
    };
    for fragment in [rule, clause, op, EFFECTFUL_REWRITE_MARKER] {
        assert!(err.contains(fragment), "missing {fragment:?} in: {err}");
    }
    let line = 1 + src
        .lines()
        .position(|l| l.contains(at))
        .unwrap_or_else(|| panic!("no line of the fixture holds {at:?}"));
    assert!(
        err.starts_with(&format!("{line}:")),
        "the refusal should be located at line {line}, the call's, got: {err}",
    );
}

const DOT: &str = "rewrite not to reach potentially effectful operation";
const REPLACED: &str = "dot rule not to replace a call of potentially effectful operation";
const MACRO: &str = "rewrite not to build, by its macro, a call of potentially effectful operation";

fn int_of(src: &str, op: &str) -> i64 {
    match interp_for(src).call(op, &[]).expect("the entry point evaluates") {
        Value::Int(n) => n,
        other => panic!("expected an Int64, got {other:?}"),
    }
}

/// A dot that reaches an operation of another sort, through a chain — the shape the
/// gate could not see, as `risky` names nothing where the rule is written.
#[test]
fn a_dot_on_another_sort_in_the_rules_text_is_refused_at_the_call() {
    let src = program(
        "wi905chain",
        r#"
  sort Holder
    entity holder(value: Int64)
    operation inner(h: Holder) -> Other = other(v: 1)
    rule dr: dot_apply(?e, bump, ?x) <=> ?e.inner().risky(?x) @[simp]
    operation consumer(h: Holder) -> Int64 effects Error[Boom] = h.bump(5)
  end"#,
    );
    refused_once(&src, "`test.wi905chain.Holder.dr`", DOT, "`test.wi905chain.Other.risky`", "h.bump(");
}

/// A dot on a dot rule's argument: its receiver's type is the caller's, so no reading
/// of the rule alone could tell which operation it reaches.
#[test]
fn a_dot_on_a_dot_rules_argument_is_refused_at_the_call() {
    let src = program(
        "wi905arg",
        r#"
  sort Holder
    entity holder(value: Int64)
    rule dr: dot_apply(?e, bump, ?x) <=> ?x.risky(1) @[simp]
    operation consumer(h: Holder) -> Int64 effects Error[Boom] = h.bump(other(v: 2))
  end"#,
    );
    refused_once(&src, "`test.wi905arg.Holder.dr`", DOT, "`test.wi905arg.Other.risky`", "h.bump(");
}

/// Not only a dot rule: an operation-headed `@[simp]` rule whose right-hand side calls
/// by a dot. The named spelling `Other.risky(?o, 1)` is the gate's to refuse.
#[test]
fn a_dot_in_an_operation_headed_rewrite_is_refused_at_the_call() {
    let src = program(
        "wi905head",
        r#"
  operation trigger(o: Other) -> Int64
  rule trig: trigger(?o) <=> ?o.risky(1) @[simp]
  operation consumer() -> Int64 effects Error[Boom] = trigger(other(v: 2))"#,
    );
    refused_once(&src, "`test.wi905head.trig`", DOT, "`test.wi905head.Other.risky`", "trigger(other(");
}

/// A dot whose receiver denotes a sort, `(Other).m(…)`: the call the written `Other.m(…)`
/// makes, which a rewrite's text reaches by the dot all the same.
#[test]
fn a_dot_on_a_sort_denoting_receiver_is_refused_at_the_call() {
    let src = program(
        "wi905sort",
        r#"
  sort Loud
    operation shout(x: Int64) -> Int64 effects Error[Boom] = Error.raise(boom(why: "no"))
  end
  operation trig(n: Int64) -> Int64
  rule t: trig(?n) <=> (Loud).shout(?n) @[simp]
  operation consumer() -> Int64 effects Error[Boom] = trig(1)"#,
    );
    refused_once(&src, "`test.wi905sort.t`", DOT, "`test.wi905sort.Loud.shout`", "= trig(1)");
}

/// The ticket's own program: the dot reaches a member of the rule's own sort. Refused
/// once, at the call — no longer at the rule by the member's name.
#[test]
fn a_dot_on_the_rules_own_sort_is_refused_at_the_call() {
    let src = program(
        "wi905own",
        r#"
  sort Holder
    entity holder(value: Int64)
    operation risky(h: Holder, x: Int64) -> Int64 effects Error[Boom] =
      Error.raise(boom(why: "no"))
    rule dr: dot_apply(?e, bump, ?x) <=> ?e.risky(?x) @[simp]
    operation consumer(h: Holder) -> Int64 effects Error[Boom] = h.bump(5)
  end"#,
    );
    refused_once(&src, "`test.wi905own.Holder.dr`", DOT, "`test.wi905own.Holder.risky`", "h.bump(");
}

/// The refusal is located at the call in the body being typed, in that body's file —
/// not at the dot, whose span is in the rule's file. Two files, the rule in the first.
#[test]
fn the_refusal_is_located_in_the_callers_file() {
    let lib = program(
        "wi905lib",
        r#"
  sort Holder
    entity holder(value: Int64)
    operation inner(h: Holder) -> Other = other(v: 1)
    rule dr: dot_apply(?e, bump, ?x) <=> ?e.inner().risky(?x) @[simp]
  end"#,
    );
    let app = "namespace test.wi905app\n  import anthill.prelude.{Int64}\n  import test.wi905lib.{Holder, Boom}\n  import test.wi905lib.Holder.{holder}\n\n  operation consumer() -> Int64 effects Error[Boom] = holder(value: 1).bump(5)\nend\n";
    let errs = try_load_kb_with_named_files(&[("lib.anthill", &lib), ("app.anthill", app)])
        .err()
        .expect("the call must be refused");
    let [err] = &errs[..] else {
        panic!("expected exactly one refusal, got: {errs:#?}");
    };
    assert!(err.contains(DOT), "not the dot's refusal: {err}");
    assert!(
        err.starts_with("app.anthill:6:"),
        "the refusal should name the call's file and line, got: {err}",
    );
}

/// The dot reaches `Other.calm`, which is pure; the rule's sort has an effectful
/// `calm` of its own. The gate refused this by the name `calm` has where the rule is
/// written; the call runs `Other.calm`.
#[test]
fn a_pure_operation_a_dot_reaches_is_not_refused_for_a_same_named_member() {
    let src = program(
        "wi905pure",
        r#"
  sort Holder
    entity holder(value: Int64)
    operation inner(h: Holder) -> Other = other(v: 1)
    operation calm(h: Holder, x: Int64) -> Int64 effects Error[Boom] =
      Error.raise(boom(why: "no"))
    rule dr: dot_apply(?e, bump, ?x) <=> ?e.inner().calm(?x) @[simp]
    operation consumer(h: Holder) -> Int64 = h.bump(5)
    operation run() -> Int64 = consumer(holder(value: 1))
  end"#,
    );
    assert_eq!(int_of(&src, "test.wi905pure.Holder.run"), 105);
}

/// CONTROL, either way: a pure dot in a rewrite's text fires as before.
#[test]
fn a_pure_dot_in_a_rewrites_text_still_fires() {
    let src = program(
        "wi905calm",
        r#"
  sort Holder
    entity holder(value: Int64)
    operation inner(h: Holder) -> Other = other(v: 1)
    rule dr: dot_apply(?e, bump, ?x) <=> ?e.inner().calm(?x) @[simp]
    operation consumer(h: Holder) -> Int64 = h.bump(5)
    operation run() -> Int64 = consumer(holder(value: 1))
  end"#,
    );
    assert_eq!(int_of(&src, "test.wi905calm.Holder.run"), 105);
}

/// The decision this ticket made, pinned: what a dot reaches is judged at a call the
/// rule fires on, so a rule no call fires on is refused for none of it — here the
/// member of its own sort that the gate used to read by name.
#[test]
fn a_rule_no_call_fires_on_is_not_refused_for_its_dots() {
    let src = program(
        "wi905unfired",
        r#"
  sort Holder
    entity holder(value: Int64)
    operation risky(h: Holder, x: Int64) -> Int64 effects Error[Boom] =
      Error.raise(boom(why: "no"))
    rule dr: dot_apply(?e, bump, ?x) <=> ?e.risky(?x) @[simp]
  end"#,
    );
    load_kb_with(&src);
}

/// The two other places a dot is typed: a rule body, and a const's value. One refusal
/// each, the rewrite's — the const's purity gate does not add a second.
#[test]
fn a_dot_in_a_rewrites_text_is_refused_in_a_rule_body_and_a_const() {
    let sort = r#"
  sort Holder
    entity holder(value: Int64)
    operation inner(h: Holder) -> Other = other(v: 1)
    rule dr: dot_apply(?e, bump, ?x) <=> ?e.inner().risky(?x) @[simp]
  end"#;
    for (ns, site) in [
        ("wi905rule", "  rule p(?r) :- ?r <=> holder(value: 1).bump(5)"),
        ("wi905const", "  const c: Int64 = holder(value: 1).bump(5)"),
    ] {
        let src = program(ns, &format!("{sort}\n{site}"));
        refused_once(
            &src,
            &format!("`test.{ns}.Holder.dr`"),
            DOT,
            &format!("`test.{ns}.Other.risky`"),
            site.trim(),
        );
    }
}

/// A rewrite inside a rewrite's text: the dot is the inner rule's, and the refusal
/// names that rule.
#[test]
fn a_dot_in_a_rewrite_a_rewrite_wrote_names_the_inner_rule() {
    let src = program(
        "wi905nest",
        r#"
  sort Holder
    entity holder(value: Int64)
    operation inner(h: Holder) -> Other = other(v: 1)
    rule dr: dot_apply(?e, bump, ?x) <=> ?e.inner().risky(?x) @[simp]
  end
  operation trig(h: Holder) -> Int64
  rule outer: trig(?h) <=> ?h.bump(1) @[simp]
  operation consumer(h: Holder) -> Int64 effects Error[Boom] = trig(h)"#,
    );
    refused_once(&src, "`test.wi905nest.Holder.dr`", DOT, "`test.wi905nest.Other.risky`", "= trig(h)");
}

/// A dot rule declared on a spec fires on a provider, and replaces the provider's own
/// effectful member: the call was dropped, silently.
#[test]
fn a_dot_rule_replacing_a_providers_effectful_member_is_refused_at_the_call() {
    let src = program(
        "wi905drop",
        r#"
  sort Desc
    sort T = ?
    operation tag(x: T) -> Int64
    rule dr: dot_apply(?e, bump, ?x) <=> ?x @[simp]
  end
  sort Coin
    entity coin(n: Int64)
    provides Desc[T = Coin]
    operation tag(x: Coin) -> Int64 = 1
    operation bump(c: Coin, x: Int64) -> Int64 effects Error[Boom] =
      Error.raise(boom(why: "no"))
    operation consumer() -> Int64 effects Error[Boom] = coin(n: 1).bump(5)
  end"#,
    );
    refused_once(&src, "`test.wi905drop.Desc.dr`", REPLACED, "`test.wi905drop.Coin.bump`", "coin(n: 1).bump(");
}

/// …and the operation a provided spec supplies by default, which the dot reaches
/// without the rule.
#[test]
fn a_dot_rule_replacing_a_provided_specs_effectful_default_is_refused_at_the_call() {
    let src = program(
        "wi905dflt",
        r#"
  sort Bumper
    sort T = ?
    operation bump(x: T, n: Int64) -> Int64 effects Error[Boom] =
      Error.raise(boom(why: "no"))
  end
  sort Coin
    entity coin(n: Int64)
    provides Bumper[T = Coin]
    rule dr: dot_apply(?e, bump, ?x) <=> ?x @[simp]
    operation consumer() -> Int64 effects Error[Boom] = coin(n: 1).bump(5)
  end"#,
    );
    refused_once(&src, "`test.wi905dflt.Coin.dr`", REPLACED, "`test.wi905dflt.Bumper.bump`", "coin(n: 1).bump(");
}

/// CONTROL, either way: a dot rule supplying a member no one declares replaces no call.
#[test]
fn a_dot_rule_supplying_an_undeclared_member_still_fires() {
    let src = program(
        "wi905supply",
        r#"
  sort Holder
    entity holder(value: Int64)
    rule dr: dot_apply(?e, bump, ?x) <=> add(?x, 1) @[simp]
    operation run() -> Int64 = holder(value: 1).bump(5)
  end"#,
    );
    assert_eq!(int_of(&src, "test.wi905supply.Holder.run"), 6);
}

const MACRO_RULE: &str = r#"
  import anthill.prelude.List.{cons, nil}
  import anthill.reflect.{NodeOccurrence, make_apply}
  sort Holder
    entity holder(value: Int64)
    operation wrap(r: NodeOccurrence, x: NodeOccurrence) -> NodeOccurrence =
      make_apply("TARGET", cons(r, cons(x, nil())), r)
    rule dr: dot_apply(?e, bump, ?x) <=> wrap(?e, ?x) @[simp]
"#;

/// A macro-headed rule whose macro builds a call of an effectful operation. The gate
/// exempts the macro, whose call is evaluated away; what it builds stays in the body.
#[test]
fn a_call_a_macro_builds_to_an_effectful_operation_is_refused_at_the_call() {
    let ns = "wi905macro";
    let rule = MACRO_RULE.replace("TARGET", &format!("test.{ns}.Holder.loud"));
    let src = program(
        ns,
        &format!(
            "{rule}    operation loud(h: Holder, v: Int64) -> Int64 effects Error[Boom] =\n      Error.raise(boom(why: \"no\"))\n    operation consumer(h: Holder) -> Int64 effects Error[Boom] = h.bump(5)\n  end"
        ),
    );
    refused_once(&src, &format!("`test.{ns}.Holder.dr`"), MACRO, &format!("`test.{ns}.Holder.loud`"), "h.bump(");
}

/// A call the macro builds INSIDE another it builds is read too: the expansion is
/// `quiet(h, loud(h, 5))`, every node of it the macro's.
#[test]
fn a_call_a_macro_builds_inside_another_is_refused_at_the_call() {
    let ns = "wi905macronest";
    let rule = MACRO_RULE.replace(
        "make_apply(\"TARGET\", cons(r, cons(x, nil())), r)",
        &format!(
            "make_apply(\"test.{ns}.Holder.quiet\", cons(r, cons(make_apply(\"test.{ns}.Holder.loud\", cons(r, cons(x, nil())), r), nil())), r)"
        ),
    );
    let src = program(
        ns,
        &format!(
            "{rule}    operation quiet(h: Holder, v: Int64) -> Int64 = add(v, 100)\n    operation loud(h: Holder, v: Int64) -> Int64 effects Error[Boom] =\n      Error.raise(boom(why: \"no\"))\n    operation consumer(h: Holder) -> Int64 effects Error[Boom] = h.bump(5)\n  end"
        ),
    );
    refused_once(&src, &format!("`test.{ns}.Holder.dr`"), MACRO, &format!("`test.{ns}.Holder.loud`"), "h.bump(");
}

/// CONTROL, either way: what the macro is handed and gives back is the caller's text. The
/// caller's own effectful argument is not the rewrite's call, and runs once — the raise is
/// what `run` returns.
#[test]
fn a_callers_effectful_argument_a_macro_gives_back_is_not_refused() {
    let ns = "wi905macroarg";
    let rule = MACRO_RULE.replace("TARGET", &format!("test.{ns}.Holder.quiet"));
    let src = program(
        ns,
        &format!(
            "{rule}    operation quiet(h: Holder, v: Int64) -> Int64 = add(v, 100)\n    operation run() -> Int64 effects Error[Boom] = holder(value: 1).bump(other(v: 1).risky(5))\n  end"
        ),
    );
    let raised = interp_for(&src)
        .call(&format!("test.{ns}.Holder.run"), &[])
        .expect_err("the caller's `risky` raises");
    assert!(format!("{raised:?}").contains("risky ran"), "not the caller's raise: {raised:?}");
}

/// CONTROL, either way: the same macro building a pure call expands and runs.
#[test]
fn a_macro_building_a_pure_call_still_expands() {
    let ns = "wi905macropure";
    let rule = MACRO_RULE.replace("TARGET", &format!("test.{ns}.Holder.quiet"));
    let src = program(
        ns,
        &format!(
            "{rule}    operation quiet(h: Holder, v: Int64) -> Int64 = add(v, 100)\n    operation run() -> Int64 = holder(value: 1).bump(5)\n  end"
        ),
    );
    assert_eq!(int_of(&src, &format!("test.{ns}.Holder.run")), 105);
}

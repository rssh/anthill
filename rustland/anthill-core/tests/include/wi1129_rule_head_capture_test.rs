//! WI-1129 (proposal 056 §2.3) — the RULE-HEAD REST PATTERN, the second face of
//! variadic capture.
//!
//! `rule trigger(?x, ...?args) <=> pick(?x, ?args) [simp]` fires on a redex whose
//! named arguments the head does not name, binding `?args` to a record OCCURRENCE
//! of the leftovers. The macro on the right-hand side reads that record as SYNTAX
//! — its component LABELS through `sub_occurrence_labels`, its children through
//! `sub_occurrences` — and splices a call built out of both, so the asserted value
//! moves if either channel breaks. That is the capability the operation face
//! (WI-727) cannot give: it hands the callee a record whose components are TYPES,
//! and a name reaches type position only as a denoted (spec §4.5, no singleton
//! types), so a captured `a` arrives there as `Int64`.
//!
//! BACK-OUT MEASUREMENT. Mutate `KnowledgeBase::record_rule_head_capture`
//! (kb/mod.rs) into a no-op — a present-but-wrong back-out, so the fixture still
//! LOADS and this file measures capability rather than loadability. Then
//! `simp_rewrite::try_fire` never folds, the head `trigger(?x, ?args)` fails to
//! match a redex written `trigger(5, a: 7)` (one positional against two), the rule
//! does not fire, and `trigger`'s own body answers 5 in place of every splice.
//! MEASURED: 4 failed, 6 passed — the four capability tests
//! (`capture_binds_the_leftover_named_arguments`, `labels_select_the_spliced_-
//! callee`, `an_empty_capture_still_fires_the_rule`, `the_rewrite_is_in_the_-
//! stored_body`) all go red; the six position-refusal tests stay green, correctly,
//! since they measure the CONVERTER and this back-out does not touch it.
//!
//! CONTROLS, green under that same back-out and BY DESIGN — they live in their own
//! fixtures, so the back-out cannot take them down with it and their greenness
//! says something: `wi722_compile_time_macro_test` (a `[simp]` macro rule with NO
//! capture, 7 passed), `wi727_fix_test` (the OPERATION face this must leave
//! untouched, 17 passed) and `wi1127_condition_param_test` (`where_run` /
//! `join_run`'s reuse of that face, 12 passed).

use anthill_core::eval::Value;

/// `trigger` declares BOTH faces, as a real client does: the `...args: R`
/// parameter is what makes `trigger(5, a: 7)` a well-formed call at all (WI-727),
/// and the `[simp]` rule captures the same residue as syntax. So the arms differ
/// only in whether the rule-head capture works — with it, the macro's splice;
/// without it, `trigger`'s own body, which returns `x`.
const SRC: &str = r#"
namespace test.wi1129
  import anthill.prelude.{Int64, String}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Numeric.{add}
  import anthill.prelude.String.{concat}
  import anthill.reflect.{NodeOccurrence, make_apply, sub_occurrences, sub_occurrence_labels}

  -- The splice targets. WHICH one is picked is read from the captured record's
  -- LABELS; the second argument is a captured SUB-OCCURRENCE; the first is the
  -- head's ordinary declared argument `?x`.
  operation kept_a(v: Int64, w: Int64) -> Int64 = add(add(v, w), 100)
  operation kept_b(v: Int64, w: Int64) -> Int64 = add(add(v, w), 200)
  operation kept_none(v: Int64) -> Int64 = add(v, 300)

  -- The MACRO (occurrence -> occurrence, so the `[simp]` engine evaluates it at
  -- compile time). `args` is the captured record.
  operation pick(x: NodeOccurrence, args: NodeOccurrence) -> NodeOccurrence =
    match sub_occurrence_labels(args)
      case cons(l, _) ->
        make_apply(concat("test.wi1129.kept_", l), cons(x, sub_occurrences(args)), x)
      case nil() -> make_apply("test.wi1129.kept_none", cons(x, nil()), x)

  operation trigger[R](x: Int64, ...args: R) -> Int64 = x

  rule trigger(?x, ...?args) <=> pick(?x, ?args) [simp]

  operation drive_a() -> Int64 = trigger(5, a: 7)
  operation drive_b() -> Int64 = trigger(5, b: 7)
  operation drive_empty() -> Int64 = trigger(5)
end
"#;

fn drive(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp
        .call(&format!("test.wi1129.{op}"), &[])
        .unwrap_or_else(|e| panic!("{op}: {e}"))
    {
        Value::Int(n) => n,
        other => panic!("{op}: expected Int, got {other:?}"),
    }
}

/// The capture ARRIVES, and its sub-occurrences are spliceable. `trigger(5, a: 7)`
/// rewrites to `kept_a(5, 7)` = 5 + 7 + 100: the `5` is the head's declared `?x`,
/// the `7` is the captured component reused in place.
#[test]
fn capture_binds_the_leftover_named_arguments() {
    let mut interp = crate::common::interp_for(SRC);
    assert_eq!(
        drive(&mut interp, "drive_a"),
        112,
        "trigger(5, a: 7) should rewrite to kept_a(5, 7) = add(add(5, 7), 100)",
    );
}

/// The LABEL channel is real, not incidental: the same shape with the component
/// named `b` instead of `a` picks a DIFFERENT callee, so the macro read the name
/// and not the position. This is the half `sub_occurrences` alone cannot show —
/// its list is identical in both rows.
#[test]
fn labels_select_the_spliced_callee() {
    let mut interp = crate::common::interp_for(SRC);
    assert_eq!(drive(&mut interp, "drive_a"), 112, "label `a` -> kept_a");
    assert_eq!(drive(&mut interp, "drive_b"), 212, "label `b` -> kept_b");
}

/// An EMPTY capture is a legitimate degenerate case, not a failure (056 §3 OQ #6,
/// the same verdict the operation face reaches for `r.fix()`): the macro sees a
/// record with no components and splices `kept_none(5)` = 305.
///
/// `kept_none` ADDS 300 rather than returning `v`, and that is the whole point of
/// the constant: the identity spelling made this row read 5 in BOTH arms — the
/// rule fired and spliced `kept_none(5)`, or it did not fire and `trigger`'s own
/// body returned `x` — so it measured nothing. MEASURED: it was the one row that
/// stayed green under the back-out below.
#[test]
fn an_empty_capture_still_fires_the_rule() {
    let mut interp = crate::common::interp_for(SRC);
    assert_eq!(drive(&mut interp, "drive_empty"), 305);
}

/// The rewrite happens at COMPILE time — the consumer's STORED body is the macro's
/// output, not the `trigger` redex nor the `pick` template.
#[test]
fn the_rewrite_is_in_the_stored_body() {
    let kb = crate::common::load_kb_with(SRC);
    let sym = kb
        .try_resolve_symbol("test.wi1129.drive_a")
        .expect("drive_a");
    let body = kb.op_body_node(sym).expect("drive_a has a body node");
    assert_eq!(
        crate::common::head_short(&kb, &body),
        "kept_a",
        "the macro should have rewritten the body at compile time",
    );
}

// ── Where a `...` may be written ────────────────────────────────────────────
//
// The marker parses in ANY call — a rule head and an operation-body call are the
// same `fn_term` production — and it MEANS something in exactly one position. Each
// row below is a position with no reader, and each must be a LOCATED refusal
// rather than a marker read as an ordinary argument (which is what dropping it
// would silently produce). These are conversion-time, so they are asserted through
// `parse`, not through the loader.

const PREAMBLE: &str = r#"
namespace test.wi1129r
  import anthill.prelude.{Int64}
  import anthill.prelude.List.{cons, nil}
  import anthill.reflect.{NodeOccurrence, make_apply}
  operation wrapped(v: Int64) -> Int64 = v
  operation pick(x: NodeOccurrence, args: NodeOccurrence) -> NodeOccurrence =
    make_apply("test.wi1129r.wrapped", cons(x, nil()), x)
  operation trigger[R](x: Int64, ...args: R) -> Int64 = x
"#;

fn refusal(tail: &str) -> String {
    let src = format!("{PREAMBLE}{tail}");
    match anthill_core::parse::parse(&src) {
        Err(errs) => errs
            .iter()
            .map(|e| e.message.clone())
            .collect::<Vec<_>>()
            .join(" | "),
        Ok(_) => panic!("expected a refusal, but this parsed clean:\n{tail}"),
    }
}

#[test]
fn a_capture_head_without_simp_is_refused() {
    let msg = refusal("  rule trigger(?x, ...?args) <=> pick(?x, ?args)\nend\n");
    assert!(
        msg.contains("needs the `[simp]` tag"),
        "expected the missing-tag refusal, got: {msg}",
    );
}

#[test]
fn a_second_capture_is_refused() {
    // MEASURED before the converter kept a LIST of rest slots: this loaded clean,
    // the second `...` overwriting the first, so `?a` became an ordinary argument
    // in silence.
    let msg = refusal("  rule trigger(?x, ...?a, ...?b) <=> pick(?x, ?a) [simp]\nend\n");
    assert!(
        msg.contains("at most one variadic capture"),
        "expected the at-most-one refusal, got: {msg}",
    );
}

#[test]
fn a_non_trailing_capture_is_refused() {
    let msg = refusal("  rule trigger(...?args, ?x) <=> pick(?x, ?args) [simp]\nend\n");
    assert!(
        msg.contains("must be the LAST positional argument"),
        "expected the trailing refusal, got: {msg}",
    );
}

#[test]
fn a_capture_outside_a_simp_head_lhs_is_refused() {
    // Four positions the head walk never inspects — the equation's RHS, a rule
    // BODY goal, an operation BODY call, and a head that is not an equation at all
    // — all reported by the one stray sweep that runs after the file converts.
    for tail in [
        "  rule trigger(?x, ?args) <=> pick(?x, ...?args) [simp]\nend\n",
        "  rule trigger(?x, ?y) <=> pick(?x, ?y) :- wrapped(...?z)\nend\n",
        "  operation bad(v: Int64) -> Int64 = wrapped(...?z)\nend\n",
        "  rule trigger(?x, ...?args)\nend\n",
        "  rule trigger(?x, ?y) <=> pick(?x, wrapped(...?y)) [simp]\nend\n",
    ] {
        let msg = refusal(tail);
        assert!(
            msg.contains("may appear only as the LAST positional argument of a `[simp]` rule head"),
            "expected the stray-capture refusal for `{tail}`, got: {msg}",
        );
    }
}

#[test]
fn a_capture_in_a_proof_step_head_is_refused() {
    // A proof step's `Rule` never reaches `load_rule` — `encode_proof_step` reads its
    // heads and encodes a `ProofStep` term — so a capture recorded on one would have
    // NO reader. The converter therefore leaves the marker unclaimed and the stray
    // sweep reports it. MEASURED before that: with `convert_proof_step` calling
    // `claim_rule_head_captures`, a `[simp]`-tagged step CLAIMED the marker with no
    // diagnostic, and the rest pattern degraded to an ordinary positional argument in
    // silence. Written `[simp]` deliberately — the untagged spelling is refused by a
    // different branch and would not have measured this.
    let msg = refusal(
        "  rule lem: trigger(?x, ?y) <=> pick(?x, ?y)\n  proof lem\n    \
         rule s: trigger(?x, ...?args) <=> pick(?x, ?args) [simp] by derivation\n  \
         end\nend\n",
    );
    assert!(
        msg.contains("may appear only as the LAST positional argument of a `[simp]` rule head"),
        "expected the stray-capture refusal for a proof step, got: {msg}",
    );
}

#[test]
fn a_capture_on_a_dot_form_is_refused() {
    // The dot-headed `[simp]` rule is fired by `typing::try_fire_dot_rule`, whose
    // matcher has no fold step, so a `...` there would bind nothing. MEASURED
    // before `push_dot_method_call` grew its own arm: the whole `rest_arg` node
    // fell through that loop's `_ => {}` and the capture variable left the head in
    // silence.
    let msg = refusal("  rule ?r.trigger(...?args) <=> pick(?r, ?args) [simp]\nend\n");
    assert!(
        msg.contains("not supported on a dot-form call"),
        "expected the dot-form refusal, got: {msg}",
    );
}

#[test]
fn a_capture_in_a_tuple_literal_is_a_syntax_error() {
    // `rest_arg` is admitted by the `fn_term` argument list alone, not by the
    // shared `_fn_arg` a tuple literal uses — so this one is refused by the
    // GRAMMAR, one step earlier than the rest.
    let msg = refusal("  rule trigger(?x, ...?args) <=> pick(?x, (1, ...?args)) [simp]\nend\n");
    assert!(
        msg.contains("syntax error"),
        "expected a syntax error, got: {msg}",
    );
}

// ── The DOT surface (WI-731's own spelling) ─────────────────────────────────

/// The capture is read at the APPLICATIVE redex, so the question a driving client
/// asks — does `r.rename(who: r.name)` work — is whether the dot form reaches one.
/// It does, and by a route this ticket did not have to touch: the DotApply method
/// fallback synthesizes `trigger(receiver, a: 7)` and re-visits it, and the Apply
/// frame fires `[simp]` BEFORE `check_apply_iter` (so before the OPERATION face's
/// `normalize_variadic_capture` would fold the same leftovers into a `args:` named
/// argument — the two faces cannot double-capture).
///
/// The rule is written INSIDE the sort: a free-standing `rule trigger(…)` beside a
/// `Box.trigger` member is refused by the 059 R4 name-capture rule, which is about
/// the member name, not about this feature.
const DOT_SRC: &str = r#"
namespace test.wi1129dot
  import anthill.prelude.{Int64, String}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Numeric.{add}
  import anthill.prelude.String.{concat}
  import anthill.reflect.{NodeOccurrence, make_apply, sub_occurrences, sub_occurrence_labels}

  sort Box
    entity box(v: Int64)
    operation trigger[R](b: Box, ...args: R) -> Int64 = b.v
    rule trigger(?b, ...?args) <=> test.wi1129dot.pick(?b, ?args) [simp]
  end

  operation kept_a(b: Box, w: Int64) -> Int64 = add(add(b.v, w), 100)

  operation pick(x: NodeOccurrence, args: NodeOccurrence) -> NodeOccurrence =
    match sub_occurrence_labels(args)
      case cons(l, _) ->
        make_apply(concat("test.wi1129dot.kept_", l), cons(x, sub_occurrences(args)), x)
      case nil() -> x

  operation drive_dot() -> Int64 = box(v: 5).trigger(a: 7)
end
"#;

#[test]
fn the_dot_surface_reaches_the_capture() {
    let mut interp = crate::common::interp_for(DOT_SRC);
    match interp
        .call("test.wi1129dot.drive_dot", &[])
        .expect("drive_dot evaluates")
    {
        // kept_a(box(v: 5), 7) = add(add(5, 7), 100)
        Value::Int(n) => assert_eq!(n, 112),
        other => panic!("expected Int(112), got {other:?}"),
    }
}

/// WI-1129: `fold_capture_redex` builds the capture record as
/// `anthill.reflect.TupleLiteral` and resolves that name OUTRIGHT — its own `None`
/// means "this redex does not match", and an unresolvable constructor is not that, so
/// declining would make a capture rule silently never fire with nothing said anywhere.
/// The fold is total only because `register_prelude` DEFINES the name (through
/// `register_stdlib_scopes`, beside `SetLiteral` / `ListLiteral`) on every load path,
/// before any rule loads. This pins that.
///
/// A BARE load — no stdlib at all, the embedder's configuration — is the arm that can
/// distinguish it: MEASURED, `KnowledgeBase::new()` alone answers `None` for the same
/// name, so it is `load_all`'s bootstrap and not the constructor's mere existence that
/// makes this hold. Every other test in this file loads the full stdlib and would pass
/// whatever the bootstrap did.
#[test]
fn the_capture_record_constructor_is_bootstrapped() {
    const BARE: &str = r#"
namespace test.wi1129bare
  operation trigger(x: Int64) -> Int64 = x
end
"#;
    let parsed = anthill_core::parse::parse(BARE).expect("parse");
    let mut kb = anthill_core::kb::KnowledgeBase::new();
    assert!(
        kb.try_resolve_symbol("anthill.reflect.TupleLiteral").is_none(),
        "the control: a KB that has loaded nothing does NOT have the constructor, \
         so this test's arm is the bootstrap and not a tautology",
    );
    anthill_core::kb::load::load_all(&mut kb, &[&parsed], &anthill_core::kb::load::NullResolver)
        .unwrap_or_else(|e| panic!("bare load: {e:?}"));
    assert!(
        kb.try_resolve_symbol("anthill.reflect.TupleLiteral").is_some(),
        "a bare load must still define the capture record constructor — \
         `fold_capture_redex` resolves it outright",
    );
}

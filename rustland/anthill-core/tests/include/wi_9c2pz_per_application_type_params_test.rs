//! WI-20260819-9C2PZ (WI-741 follow-up) — a callee's type parameters are instantiated
//! with FRESH variables PER APPLICATION, so what a rule-body call records is a type of
//! something at THAT call site.
//!
//! `collect_rule_var_types` read a callee's declared param / field type straight out of
//! the signature and never instantiated it. Every written occurrence of one type
//! parameter denotes ONE canonical variable KB-wide (WI-954), so every `eq` call in every
//! rule in the KB recorded the same `anthill.prelude.PartialEq.T` — for variables of
//! unrelated types. WI-741 made that survivable without touching the conflation: a bare
//! parameter neither displaced nor contradicted a concrete type, and
//! `relation_clause_columns` normalized it to a variable keyed BY THE PARAMETER SYMBOL so
//! column correlation survived. Three costs remained, and this file measures all three:
//!
//!  1. TWO INDEPENDENT CALLS WERE ONE CORRELATION CLASS. `rule twoeq(?x, ?n) :- gen(?x,
//!     ?n), eq(?x, "a"), eq(?n, 1)` recorded both variables at the one `PartialEq.T`, so
//!     the relation's two columns shared one variable and the CORRECT citation
//!     `twoeq("a", 1)` was REFUSED.
//!  2. A VARIABLE FORCED EQUAL TO A CONCRETE ONE DID NOT INHERIT ITS TYPE. `rule r(?x,
//!     ?y) :- eq(?x, ?y), parent(of: ?x, is: ?)` typed `?x` `String` and left `?y`
//!     unknown, though `eq` forces them equal and the information was in the call. (The
//!     fixtures below add a generator subgoal for each variable, because `eq` is a TEST
//!     and never a binder — kernel-language.md §5.3 — so the ticket's shape as written
//!     types correctly but drains nothing.)
//!  3. WHICH CORRELATION CLASS A VARIABLE JOINED was decided by whichever parameter
//!     reached it first: a variable constrained by `eq` and then by `gt` kept
//!     `PartialEq.T` and never joined `PartialOrd.T`'s class, though the two calls
//!     together link all three variables.
//!
//! THE SECOND HALF OF THE CHANGE IS WHAT DELIVERS (2), and it is the step WI-741
//! explicitly declared UNSOUND: resolve `var_types` through the substitution the
//! collector builds and used to drop. WI-741 was right at the time — with the parameter
//! uninstantiated, that substitution binds the ONE alias every `eq` in the rule shares,
//! so resolving through it typed an `Int64` variable `String`. Per-application
//! instantiation is what makes each binding local to the call that made it. The two
//! halves ship together for that reason, and neither is separately correct.
//!
//! WHAT IS NOT MEASURED HERE, DELIBERATELY. That instantiating must not DESTROY the
//! within-call correlation is owned by `wi714_applied_correlated_columns_reject_-
//! contradiction` / `wi714_applied_unconstrained_column_accepts_and_narrows` (`pair_eq(?x,
//! ?y) :- eq(?x, ?y)` still refuses `pair_eq(5, "s")` and still narrows), and that two
//! spec calls at different carriers in one rule are not a contradiction is owned by
//! `wi741_two_spec_calls_at_different_carriers_do_not_contradict`. Those pins pass
//! UNCHANGED and are not duplicated.
//!
//! CONTROLS — MEASURED, by backing each half out in place (mutating it to a no-op, not
//! deleting it, so every fixture still loads and a red means the row and not the file).
//! Every fixture also lives in its OWN namespace, so a back-out's load error cannot take a
//! neighbouring test's fixture down with it.
//!
//! | test | instantiation | literal channel | resolve through σ |
//! |---|---|---|---|
//! | `two_independent_eq_calls_are_two_columns` | **FAILS** (load) | ok | ok |
//! | `the_two_columns_keep_their_own_types` | **FAILS** | **FAILS** | **FAILS** |
//! | `eq_does_not_propagate_into_an_int_column` | **FAILS** | ok | ok |
//! | `the_inherited_type_reaches_the_published_schema` | **FAILS** | ok | **FAILS** |
//! | `a_variable_joins_every_class_its_calls_link_it_to` | **FAILS** | ok | **FAILS** |
//! | `eq_propagates_a_concrete_type_to_both_columns` | ok | ok | ok |
//! | `a_transitively_linked_relation_still_drains` | ok | ok | ok |
//!
//! THE LAST TWO ROWS PASS UNDER EVERY BACK-OUT, and that is stated rather than papered
//! over: they are the VALUE arms — the ones that actually run the relation and read what
//! comes out — and every row that measures something is a refusal. Without them the file
//! would prove that the schemas changed and nothing about whether the relations still
//! work. Each says so at its own site.
//!
//! The four tests in the SECOND section answer to a different back-out — the first cut of
//! this change, which set `subst.contradiction` on every disagreement — and carry their
//! own control note there rather than a column in this table.

use crate::common::{interp_for, list_heads, try_load_kb_with};
use anthill_core::eval::Value;

/// The `Int64` an operation returned, loudly.
fn int_of(v: &Value, what: &str) -> i64 {
    match v {
        Value::Int(i) => *i,
        other => panic!("{what}: expected an Int64, got {other:?}"),
    }
}

// ── (1) Two independent `eq` calls are two correlation classes ────────────

/// The ticket's own shape. `gen` is a RULE subgoal, which types nothing at all, so the
/// only typing source for either column is its own `eq` call — which is what makes the
/// two calls' independence observable.
const TWO_EQ_GOOD: &str = r#"
namespace test.wi9c2pz.two
  import anthill.prelude.{String, Int64, List}
  import anthill.prelude.List.{length}
  import anthill.prelude.PartialEq.{eq}

  sort S
    entity src(s: String, n: Int64)
  end
  fact src(s: "a", n: 1)
  fact src(s: "b", n: 2)

  rule gen(?s, ?n) :- src(s: ?s, n: ?n)
  rule twoeq(?x, ?n) :- gen(?x, ?n), eq(?x, "a"), eq(?n, 1)

  operation matchedRows() -> Int64 effects Error =
    let r = twoeq("a", 1)
    length(r.takeN(50))

  operation missedRows() -> Int64 effects Error =
    let r = twoeq("b", 1)
    length(r.takeN(50))
end
"#;

/// The SAME relation cited with its two arguments swapped. Its own namespace because it
/// must not load.
const TWO_EQ_SWAPPED: &str = r#"
namespace test.wi9c2pz.twoswap
  import anthill.prelude.{String, Int64, List}
  import anthill.prelude.List.{length}
  import anthill.prelude.PartialEq.{eq}

  sort S
    entity src(s: String, n: Int64)
  end
  fact src(s: "a", n: 1)

  rule gen(?s, ?n) :- src(s: ?s, n: ?n)
  rule twoeq(?x, ?n) :- gen(?x, ?n), eq(?x, "a"), eq(?n, 1)

  operation swapped() -> Int64 effects Error =
    let r = twoeq(1, "a")
    length(r.takeN(50))
end
"#;

/// The correct citation LOADS and DRAINS. Before the change this was a load error —
/// "argument binding column `n` has an incompatible type" — because both columns shared
/// the one `PartialEq.T`, so `"a"` pinned it to `String` and `1` then failed against it.
///
/// CONTROL: back out the per-application instantiation and this test fails at LOAD.
#[test]
fn wi9c2pz_two_independent_eq_calls_are_two_columns() {
    let mut interp = interp_for(TWO_EQ_GOOD);
    let rows = interp
        .call("test.wi9c2pz.two.matchedRows", &[])
        .expect("two independent `eq` calls must not correlate the two columns");
    assert_eq!(
        int_of(&rows, "matchedRows"),
        1,
        "`src(s: \"a\", n: 1)` is the one row satisfying both filters"
    );
    // The filters are REAL — a citation that agrees with the relation on neither clause
    // drains nothing, so the row above is not an artefact of an unfiltered drain.
    let rows = interp
        .call("test.wi9c2pz.two.missedRows", &[])
        .expect("call missedRows");
    assert_eq!(int_of(&rows, "missedRows"), 0);
}

/// And the columns are TYPED, not merely independent: swapping the two arguments is a
/// loud refusal naming the offending column. This is the other polarity, and it is what
/// separates the repair from "the columns became two unconstrained wildcards" — which
/// would accept both citations equally. What types them is the LITERAL argument channel:
/// a literal is not a variable, so before this change it constrained nothing at all.
///
/// CONTROL: this row reddens on ALL THREE back-outs and so isolates none of them — it is
/// the end-to-end row. The literal channel is the half it is here for: back that out alone
/// and it fails by LOADING CLEAN while every other row stays green, which is the only
/// measurement in the file that the literal channel exists at all.
#[test]
fn wi9c2pz_the_two_columns_keep_their_own_types() {
    let errs = try_load_kb_with(TWO_EQ_SWAPPED)
        .err()
        .expect("`twoeq(1, \"a\")` binds a String column with an Int64 and must be refused");
    let text = errs.join("\n");
    assert!(
        text.contains("argument binding column `x` has an incompatible type"),
        "the refusal must name the column whose type the argument violates; got:\n{text}"
    );
}

// ── (2) `eq` propagates a concrete type to the variable it links ──────────

/// `eq(?x, ?y)` forces the two variables to one type and `parent.of` types `?x`
/// `String`, so `?y` is a `String` too. Cited UNBOUND, so nothing at the citation can
/// narrow the columns — the relation's own published schema has to carry it.
const EQ_PROPAGATES_STR: &str = r#"
namespace test.wi9c2pz.propstr
  import anthill.prelude.{String, Int64, List}
  import anthill.prelude.PartialEq.{eq}

  sort S
    entity parent(of: String, is: String)
  end
  fact parent(of: "root", is: "top")

  -- a RULE subgoal types nothing but BINDS at run time, which is what lets `eq`
  -- (a test, never a binder — kernel-language.md §5) filter rather than generate
  rule name(?n) :- parent(of: ?n, is: ?)
  rule linked(?x, ?y) :- name(?x), name(?y), eq(?x, ?y), parent(of: ?x, is: ?)

  operation rows() -> List[(x: String, y: String)] effects Error =
    let q = linked
    q.takeN(3)
end
"#;

/// The SAME relation with an `Int64` claim — the discriminating direction. Its own
/// namespace because it must not load.
const EQ_PROPAGATES_INT: &str = r#"
namespace test.wi9c2pz.propint
  import anthill.prelude.{String, Int64, List}
  import anthill.prelude.PartialEq.{eq}

  sort S
    entity parent(of: String, is: String)
  end
  fact parent(of: "root", is: "top")

  rule name(?n) :- parent(of: ?n, is: ?)
  rule linked(?x, ?y) :- name(?x), name(?y), eq(?x, ?y), parent(of: ?x, is: ?)

  -- ONLY the `y` column differs: `x` is `String` through `parent.of` either way, so a
  -- refusal here can come from nothing but the type `?y` inherits through `eq`
  operation rows() -> List[(x: String, y: Int64)] effects Error =
    let q = linked
    q.takeN(3)
end
"#;

/// BOTH columns type `String`, and the relation drains its row: `?y` inherits the type
/// `eq` links it to. Before the change `?y` kept the bare parameter and the `Int64`
/// claim below was accepted just as readily.
///
/// CONTROL: NONE — measured, this arm passes under all three back-outs, and it is kept
/// for what it is rather than dressed up. An unresolved column is an open variable, which
/// a `String` claim satisfies and a `String` value fills, so no back-out can redden it.
/// What it does buy is the only evidence in this file that the relation still RUNS and
/// still yields both columns; the measuring rows are all refusals, and a suite of refusals
/// stays green on a change that broke the drain entirely. The propagation itself is
/// measured by [`wi9c2pz_the_inherited_type_reaches_the_published_schema`].
#[test]
fn wi9c2pz_eq_propagates_a_concrete_type_to_both_columns() {
    let mut interp = interp_for(EQ_PROPAGATES_STR);
    let v = interp
        .call("test.wi9c2pz.propstr.rows", &[])
        .expect("a relation whose columns `eq` links must publish both as String");
    let rows = list_heads(&v);
    assert_eq!(rows.len(), 1, "one `parent` fact, so one linked row");
    // BOTH columns, read by name — a row count alone would pass on a relation that
    // dropped a column, which is the shape this ticket is about.
    match &rows[0] {
        Value::Tuple { pos, named } if pos.is_empty() && named.len() == 2 => {
            // WI-20260827-3ZNBC — read what each column DENOTES, not the variant.
            let vals: Vec<Option<String>> = named
                .iter()
                .map(|(_, v)| crate::common::scalar_str(interp.kb(), v))
                .collect();
            assert!(
                vals[0].as_deref() == Some("root") && vals[1].as_deref() == Some("root"),
                "both columns carry the `String` the link propagates, got {named:?}"
            );
        }
        other => panic!("expected a two-column row, got {other:?}"),
    }
}

/// The `Int64` claim over the same relation is REFUSED, and the refusal names the
/// `String` the relation actually publishes for BOTH columns. This is the assertion the
/// propagation turns on: it fails if `?y` is left as an open variable, which would unify
/// with `Int64` and load.
///
/// CONTROL: back out the instantiation and this test fails by LOADING CLEAN. It does NOT
/// redden on backing out the resolve step, and that measurement is worth keeping: the two
/// columns still share ONE variable there, so the citation's own `String` narrows it and
/// the `Int64` claim fails anyway. What this row measures is the CORRELATION; the
/// propagation reaching the published SCHEMA is
/// [`wi9c2pz_the_inherited_type_reaches_the_published_schema`]'s.
#[test]
fn wi9c2pz_eq_does_not_propagate_into_an_int_column() {
    let errs = try_load_kb_with(EQ_PROPAGATES_INT)
        .err()
        .expect("claiming Int64 columns over a String-linked relation must be refused");
    let text = errs.join("\n");
    assert!(
        text.contains("(x: String, y: String)"),
        "the refusal must name both columns as String — `?y` inherits through `eq`; got:\n{text}"
    );
}

/// A SECOND clause typing the `y` column `Int64`. The cross-clause lub can only report
/// the two disjoint if clause one reached `String` for `y` — which nothing but the link
/// through `eq` gives it.
const EQ_PROPAGATES_TWO_CLAUSE: &str = r#"
namespace test.wi9c2pz.proplub
  import anthill.prelude.{String, Int64, List}
  import anthill.prelude.PartialEq.{eq}

  sort S
    entity parent(of: String, is: String)
    entity scored(who: String, pts: Int64)
  end
  fact parent(of: "root", is: "top")

  rule name(?n) :- parent(of: ?n, is: ?)
  rule linked(?x, ?y) :- name(?x), name(?y), eq(?x, ?y), parent(of: ?x, is: ?)
  rule linked(?x, ?y) :- scored(who: ?x, pts: ?y)

  operation rows() -> List[(x: String, y: String)] effects Error =
    let q = linked
    q.takeN(3)
end
"#;

/// The SCHEMA carries it, not just the citation: a second clause typing `y` `Int64` makes
/// the relation DISJOINT, which the cross-clause lub can only see if the `eq` clause
/// published `String` for `y`. This is the row that isolates the resolve-through-the-
/// substitution step from the citation-time narrowing its siblings could ride on.
///
/// CONTROL: back out the instantiation OR the resolve step and this test fails by LOADING
/// CLEAN — clause one contributes an unknown for `y` and the lub takes `Int64`.
#[test]
fn wi9c2pz_the_inherited_type_reaches_the_published_schema() {
    let errs = try_load_kb_with(EQ_PROPAGATES_TWO_CLAUSE)
        .err()
        .expect("a String `y` column against an Int64 one must be a disjoint refusal");
    let text = errs.join("\n");
    assert!(
        text.contains("disjoint types for column `y`"),
        "the lub must report column `y` disjoint — `x` is String in both clauses; got:\n{text}"
    );
}

// ── (3) A variable joins EVERY class its calls link it to ─────────────────

/// `eq(?x, ?y)` and `gt(?y, ?z)` share `?y`, so all three variables carry one type. The
/// generator is again a rule subgoal, so the calls are the only typing source.
const CHAIN_OK: &str = r#"
namespace test.wi9c2pz.ch
  import anthill.prelude.{String, Int64, List}
  import anthill.prelude.List.{length}
  import anthill.prelude.PartialOrd.{gt}
  import anthill.prelude.PartialEq.{eq}

  sort G
    entity g(a: Int64, b: Int64, c: Int64)
  end
  fact g(a: 2, b: 2, c: 1)

  rule gen3(?x, ?y, ?z) :- g(a: ?x, b: ?y, c: ?z)
  rule chain(?x, ?y, ?z) :- gen3(?x, ?y, ?z), eq(?x, ?y), gt(?y, ?z)

  operation rows() -> Int64 effects Error =
    let r = chain(2, 2, 1)
    length(r.takeN(50))
end
"#;

/// The SAME relation cited with a `String` in the `z` slot — which only the transitive
/// link `x ~ y ~ z` can refuse. Its own namespace because it must not load.
const CHAIN_BAD: &str = r#"
namespace test.wi9c2pz.chainbad
  import anthill.prelude.{String, Int64, List}
  import anthill.prelude.List.{length}
  import anthill.prelude.PartialOrd.{gt}
  import anthill.prelude.PartialEq.{eq}

  sort G
    entity g(a: Int64, b: Int64, c: Int64)
  end
  fact g(a: 2, b: 2, c: 1)

  rule gen3(?x, ?y, ?z) :- g(a: ?x, b: ?y, c: ?z)
  rule chain(?x, ?y, ?z) :- gen3(?x, ?y, ?z), eq(?x, ?y), gt(?y, ?z)

  operation rows() -> Int64 effects Error =
    let r = chain(2, 2, "x")
    length(r.takeN(50))
end
"#;

/// The chain LOADS and DRAINS with three consistent arguments — the survival arm, so the
/// refusal below is not just "this relation refuses everything".
///
/// CONTROL: NONE, measured — it passes under all three back-outs by design, exactly as
/// the header's table says. Its job is to keep the refusal below honest.
#[test]
fn wi9c2pz_a_transitively_linked_relation_still_drains() {
    let mut interp = interp_for(CHAIN_OK);
    let rows = interp
        .call("test.wi9c2pz.ch.rows", &[])
        .expect("a consistently-cited chain relation must load and drain");
    assert_eq!(int_of(&rows, "rows"), 1, "`g(a: 2, b: 2, c: 1)` satisfies it");
}

/// A `String` in the third slot is refused, and only the transitive link can refuse it:
/// `?z` meets no `eq` of its own. Before the change `?z` joined `PartialOrd.T`'s class
/// while `?x`/`?y` sat in `PartialEq.T`'s, so the two classes never met and this loaded.
///
/// CONTROL: back out the instantiation OR the resolve-through-σ step and this test fails
/// by LOADING CLEAN. It needs both, and the resolve half is why: `eq` puts `?x`/`?y` on
/// one variable and `gt` puts `?y`/`?z` on another, and the two are married only in the
/// substitution — which, unresolved, leaves `?z` in a class of its own.
#[test]
fn wi9c2pz_a_variable_joins_every_class_its_calls_link_it_to() {
    let errs = try_load_kb_with(CHAIN_BAD)
        .err()
        .expect("`chain(2, 2, \"x\")` violates the transitive link and must be refused");
    let text = errs.join("\n");
    assert!(
        text.contains("argument binding column `z` has an incompatible type"),
        "the refusal must name column `z`, which only the `eq`→`gt` link types; got:\n{text}"
    );
}

// ── The located diagnostic the contradiction flag must not swallow ────────
//
// Found by /code-review on the first cut, which set `subst.contradiction` on every
// disagreement. That flag makes `type_rule_bodies` skip the rule — no dispatch, no
// WI-603 stamping, and for a NAMESPACE-level rule no report at all — so three shapes
// that used to name the offending argument and its span went silent. The repair is
// stated at `constrain_vid`: a disagreement involving a CALL's parameter is that call's
// argument error, which the ordinary call check reports precisely; only two DECLARED
// positions of one variable are a variable-type contradiction.
//
// CONTROL for all four tests below: they fail on the first cut. `f1`/`f2`/`f2b` fail by
// LOADING CLEAN at namespace level (and, written inside a sort, by reporting the vague
// rule-level contradiction instead); `f3` passes either way and says so at its site.

/// `eq` over two variables the same rule types `Int64` and `String`.
const MISTYPED_CALL: &str = r#"
namespace test.wi9c2pz.mistyped
  import anthill.prelude.{String, Int64}
  import anthill.prelude.PartialEq.{eq}
  sort S
    entity row(a: Int64, s: String)
  end
  rule bad(?a, ?s) :- row(a: ?a, s: ?s), eq(?a, ?s)
end
"#;

/// A LITERAL against a variable the rule types `Float` — the channel this ticket added.
const MISTYPED_LITERAL: &str = r#"
namespace test.wi9c2pz.mislit
  import anthill.prelude.{String, Int64, Float}
  import anthill.prelude.PartialEq.{eq}
  sort S
    entity holder(n: Int64, f: Float)
  end
  rule bad(?n, ?f) :- holder(n: ?n, f: ?f), eq(?f, 0)
end
"#;

/// The literal pins the parameter FIRST and the declared position arrives second — the
/// shape that decides the rule is on the RECORD's provenance, not only on this call's.
const MISTYPED_LITERAL_FIRST: &str = r#"
namespace test.wi9c2pz.mislitfirst
  import anthill.prelude.{String, Int64}
  import anthill.prelude.PartialEq.{eq}
  sort S
    entity scored(who: String, pts: Int64)
  end
  rule bad(?x) :- eq(?x, "s"), scored(who: ?, pts: ?x)
end
"#;

/// Two DECLARED positions of one variable that disagree — no call involved.
const DECLARED_CONTRADICTION: &str = r#"
namespace test.wi9c2pz.declared
  import anthill.prelude.{String, Int64}
  sort S
    entity parent(of: String, is: String)
    entity scored(who: String, pts: Int64)
    rule bad(?x) :- parent(of: ?x, is: ?), scored(who: ?, pts: ?x)
  end
end
"#;

/// The refusal must name the ARGUMENT and its span, not the rule.
fn assert_located_op_arg(src: &str, expected: &str, got: &str) {
    let errs = try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("a mistyped spec-op call must be refused:\n{src}"));
    let text = errs.join("\n");
    assert!(
        text.contains("eq.b (op-arg)")
            && text.contains(&format!("expected {expected}, got {got}")),
        "expected the located `eq.b (op-arg)` refusal naming {expected}/{got}; got:\n{text}"
    );
    assert!(
        !text.contains("contradictory variable types"),
        "the rule-level contradiction must NOT fire — it skips the very check that \
         produced the message above; got:\n{text}"
    );
}

/// A mistyped `eq` over two concretely-typed variables keeps its located refusal.
#[test]
fn wi9c2pz_a_mistyped_call_still_names_its_argument() {
    assert_located_op_arg(MISTYPED_CALL, "Int64", "String");
}

/// And so does a mistyped LITERAL argument — the channel this ticket added must not
/// swallow the diagnostic it makes reachable.
#[test]
fn wi9c2pz_a_mistyped_literal_still_names_its_argument() {
    assert_located_op_arg(MISTYPED_LITERAL, "Float", "Int64");
}

/// Order-independently: the literal pins the parameter first, the declared position
/// takes over, and the call is still checked against the declared type.
#[test]
fn wi9c2pz_a_declared_position_takes_over_from_a_pinned_parameter() {
    assert_located_op_arg(MISTYPED_LITERAL_FIRST, "Int64", "String");
}

/// The variable-type contradiction that IS one still fires. Two entity-field positions
/// disagree, no call is involved, and nothing else reports it.
///
/// CONTROL: NONE — this passes on the first cut and on HEAD too, by design. It is the
/// survival pin that keeps the three tests above from being satisfied by deleting the
/// contradiction flag outright.
#[test]
fn wi9c2pz_two_declared_positions_that_disagree_are_still_a_contradiction() {
    let errs = try_load_kb_with(DECLARED_CONTRADICTION)
        .err()
        .expect("two disagreeing declared positions must still be refused");
    let text = errs.join("\n");
    assert!(
        text.contains("contradictory variable types"),
        "expected the rule-level contradiction, which owns this shape alone; got:\n{text}"
    );
}

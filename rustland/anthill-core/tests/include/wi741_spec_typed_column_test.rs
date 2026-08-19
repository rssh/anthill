//! WI-741 (WI-714 follow-up) — a relation column typed ONLY by a SPEC operation.
//!
//! `collect_rule_var_types` records a variable's type by reading the DECLARED param
//! type straight out of the callee's signature; it never instantiates. So a spec
//! operation hands back its own parameter: `eq(?x, "root")` records `?x` at
//! `anthill.prelude.PartialEq.T`, a `Term::Ref` to the parameter symbol. That symbol
//! is not a type of anything at the call site — every rule in the KB that calls `eq`
//! records the SAME symbol, for variables of unrelated types.
//!
//! Two consequences, both fixed here, both measured:
//!
//!  1. As a relation COLUMN type it is a THIRD spelling of "unknown", alongside the
//!     `TypeVar` inference wildcard and the raw `Var::Global` WI-714 taught
//!     `join_column_types` about. The cross-clause lub met it as a rival type and
//!     reported the column disjoint, so a two-clause relation mixing it with a
//!     concretely-typed clause failed to LOAD, though both clauses plainly meant
//!     `String`. `relation_clause_columns` now normalizes it into the raw
//!     `Var::Global` at the producer, so "unknown" stays spelled ONE way.
//!
//!  2. As a var type it CONTRADICTED. `constrain_vid` unified it, and `unify_types`
//!     resolves the parameter to its ONE shared alias var — so two `eq` calls at
//!     different carriers in one rule bound that single var twice and the rule was
//!     declared to have "contradictory variable types". A contradictory rule is
//!     neither dot-dispatched nor stamped, and for a namespace-level rule the report
//!     is suppressed, so the loss was silent. A bare parameter now never contradicts
//!     a concrete type and never overwrites one.
//!
//! WHAT THE NORMALIZATION MUST NOT DESTROY. The parameter answers TWO questions, and
//! only the first has the answer "nothing": *what type is this column* (nothing), and
//! *which columns share a type* (a real fact — `rule pair_eq(?x, ?y) :- eq(?x, ?y)`
//! types both columns at the one `PartialEq.T`, and WI-714's applied type-check threads
//! that correlation so `pair_eq(5, "s")` is refused). Minting a FRESH var per column
//! erases it; measured, that broke exactly
//! `wi714_applied_correlated_columns_reject_contradiction` and
//! `wi714_applied_unconstrained_column_accepts_and_narrows`, which are the pins that own
//! this invariant and are not duplicated here. `relation_clause_columns` therefore mints
//! one var per distinct PARAMETER SYMBOL, so columns that shared the parameter still
//! share the var.
//!
//! WI-741's OWN hypothesized fix — resolve `var_types` through the substitution
//! `collect_rule_var_types` drops — was falsified before any of this was written, by
//! instrumenting the collector: for `eq(?x, "root")` that substitution is EMPTY (a
//! literal argument is not a var, so nothing constrains the parameter at all), and
//! where it is non-empty it holds the ONE shared alias — in the `mix` shape of
//! `wi741_two_spec_calls_at_different_carriers_do_not_contradict` it binds that alias
//! to `String`, which would have typed the `Int64` variable `String`.

use anthill_core::eval::Value;
use anthill_core::kb::node_occurrence::{for_each_child, Expr, NodeOccurrence};
use anthill_core::kb::KnowledgeBase;
use std::rc::Rc;

use crate::common::{interp_for, list_column_strings, load_kb_with, try_load_kb_with};

/// The ticket's own shape: one clause typed only by `eq`, one typed by an entity
/// field. Every fixture gets its OWN namespace so a back-out's load error cannot
/// take a neighbouring test's fixture down with it.
const NAMED: &str = r#"
namespace test.wi741.ground
  import anthill.prelude.{String, Int64, List}
  import anthill.prelude.List.{length}

  sort Family
    entity parent(of: String, is: String)
  end
  fact parent(of: "root", is: "top")
  fact parent(of: "bart", is: "homer")

  -- `?x`'s ONLY typing source is the spec op `eq`, whose param type is `PartialEq.T`
  rule tagged(?x) :- eq(?x, "root")
  -- `?x` is typed `String` by `parent.of`
  rule tagged(?x) :- parent(of: ?x, is: ?)

  -- a GROUND applied citation drains both clauses (`Relation[Unit]`, so it is counted)
  operation rootRows() -> Int64 effects Error =
    let r = tagged("root")
    length(r.takeN(50))

  operation bartRows() -> Int64 effects Error =
    let r = tagged("bart")
    length(r.takeN(50))

  operation missingRows() -> Int64 effects Error =
    let r = tagged("nobody")
    length(r.takeN(50))
end
"#;

/// The SAME relation, cited by an operation that claims an `Int64` column. Its own
/// namespace because it must NOT load, and a dirty fixture must not be shared.
const NAMED_CLAIMED_INT: &str = r#"
namespace test.wi741.claimint
  import anthill.prelude.{String, Int64, List}

  sort Family
    entity parent(of: String, is: String)
  end
  rule tagged(?x) :- eq(?x, "root")
  rule tagged(?x) :- parent(of: ?x, is: ?)

  operation rows() -> List[(x: Int64)] effects Error =
    let r = tagged
    r.takeN(50)
end
"#;

/// A spec-typed column that GENERATES: the values come from a rule subgoal (which
/// types nothing at all), and `eq` only filters — so the column's sole typing source
/// is still the spec op, but the relation can be drained unbound.
const GENERATED: &str = r#"
namespace test.wi741.generated
  import anthill.prelude.{String, Int64, List}

  sort Family
    entity parent(of: String, is: String)
  end
  fact parent(of: "root", is: "top")
  fact parent(of: "bart", is: "homer")

  -- a RULE subgoal types nothing, so `?x` below is typed only by `eq`
  rule source(?x) :- parent(of: ?x, is: ?)

  rule picked(?x) :- source(?x), eq(?x, "root")
  rule picked(?x) :- parent(of: ?x, is: "homer")

  operation rows() -> List[(x: String)] effects Error =
    let r = picked
    r.takeN(50)
end
"#;

/// A SINGLE-clause relation whose only column is typed by a spec op — the path the
/// producer normalization reaches but the cross-clause lub never does.
const SOLO: &str = r#"
namespace test.wi741.solo
  import anthill.prelude.{String, Int64, List}

  sort Family
    entity parent(of: String, is: String)
  end
  fact parent(of: "root", is: "top")

  rule source(?x) :- parent(of: ?x, is: ?)
  -- one clause, and `?x` is typed only by `eq`
  rule only(?x) :- source(?x), eq(?x, "root")

  operation rows() -> List[(x: String)] effects Error =
    let r = only
    r.takeN(50)
end
"#;

/// Two clauses that really do disagree — the guard that must SURVIVE the relaxation.
const DISJOINT: &str = r#"
namespace test.wi741.disjoint
  import anthill.prelude.{String, Int64, List}

  sort S
    entity parent(of: String, is: String)
    entity scored(who: String, pts: Int64)
  end
  rule mixed(?x) :- parent(of: ?x, is: ?)
  rule mixed(?x) :- scored(who: ?, pts: ?x)

  operation rows() -> List[(x: String)] effects Error =
    let r = mixed
    r.takeN(50)
end
"#;

/// A clause whose column is typed `String` only because a CONCRETE constraint
/// displaced the spec parameter on the same variable, against an `Int64` clause.
const CONCRETE_OUTVOTES: &str = r#"
namespace test.wi741.outvotes
  import anthill.prelude.{String, Int64, List}

  sort S
    entity parent(of: String, is: String)
    entity scored(who: String, pts: Int64)
  end
  -- `?x` is constrained by `eq` (the bare parameter) AND by `parent.of` (`String`)
  rule mixed(?x) :- eq(?x, ?y), parent(of: ?x, is: ?y)
  rule mixed(?x) :- scored(who: ?, pts: ?x)

  operation rows() -> List[(x: String)] effects Error =
    let r = mixed
    r.takeN(50)
end
"#;

/// Two `eq` calls at DIFFERENT carriers in one rule, each also pinned concretely —
/// the shape whose four variables were all recorded at the one shared `PartialEq.T`.
/// The rule carries a DOT, which the typer only dispatches for a NON-contradictory
/// rule, so a surviving `Expr::DotApply` is the observable.
const TWO_CARRIERS: &str = r#"
namespace test.wi741.twocarriers
  import anthill.prelude.{String, Int64}

  sort Box
    entity box(value: Int64)
    operation peek(b: Box) -> Int64 = ?b.value
  end
  sort Holder
    entity holder(b: Box, n: Int64, s: String)
  end

  rule peeks(?b, ?n, ?s)
    :- holder(b: ?b, n: ?n, s: ?s), eq(?n, ?b.peek()), eq(?s, "x")
end
"#;

/// The `Int64` an operation returned, loudly.
fn int_of(v: &Value, what: &str) -> i64 {
    match v {
        Value::Int(i) => *i,
        other => panic!("{what}: expected an Int64, got {other:?}"),
    }
}

/// Does any body atom of any non-fact rule under `functor_qn` still carry an
/// `Expr::DotApply`? After dispatch a value dot is gone. Local rather than shared
/// with the WI-282 suite: that file keeps its own copy and neither is public.
fn rule_bodies_have_dot(kb: &KnowledgeBase, functor_qn: &str) -> bool {
    fn occ_has_dot(occ: &Rc<NodeOccurrence>) -> bool {
        let Some(expr) = occ.as_expr() else {
            return false;
        };
        if matches!(expr, Expr::DotApply { .. }) {
            return true;
        }
        let mut found = false;
        for_each_child(expr, |c| found = found || occ_has_dot(c));
        found
    }
    let sym = kb
        .try_resolve_symbol(functor_qn)
        .unwrap_or_else(|| panic!("`{functor_qn}` must resolve — the fixture names it"));
    kb.rules_by_functor(sym)
        .into_iter()
        .filter(|&rid| !kb.is_fact(rid))
        .any(|rid| kb.rule_body_nodes(rid).iter().any(occ_has_dot))
}

// ── Acceptance ────────────────────────────────────────────────────────────

/// The ticket's shape LOADS, and both clauses are live in the drained relation.
///
/// Back out `relation_clause_columns`' normalization and this fails at LOAD with
/// "disjoint types for column `x`". Backing out `constrain_vid` alone leaves it
/// green — `eq(?x, "root")` puts only ONE constraint on `?x`, so there is nothing
/// for a concrete type to displace; that axis is measured by
/// [`wi741_a_concretely_typed_clause_still_out_votes`].
#[test]
fn wi741_a_spec_typed_column_joins_a_concrete_one() {
    let mut interp = interp_for(NAMED);
    // "root" satisfies BOTH clauses: `eq("root", "root")`, and `parent(of: "root")`.
    // A schema that silently dropped a clause would answer 1.
    let rows = interp
        .call("test.wi741.ground.rootRows", &[])
        .expect("a spec-typed column must not veto the relation's schema");
    assert_eq!(int_of(&rows, "rootRows"), 2, "both clauses derive `root`");
    // "bart" satisfies only the `parent` clause — the `eq` clause is a real filter.
    let rows = interp
        .call("test.wi741.ground.bartRows", &[])
        .expect("call bartRows");
    assert_eq!(int_of(&rows, "bartRows"), 1);
    let rows = interp
        .call("test.wi741.ground.missingRows", &[])
        .expect("call missingRows");
    assert_eq!(int_of(&rows, "missingRows"), 0);
}

/// The joined column is typed `String` — not a WILDCARD that would unify with
/// anything. This is the assertion the acceptance turns on: normalizing the spec
/// parameter to a fresh `Var::Global` makes the clause contribute NO information, and
/// the lub must then take `String` from the clause that knows.
///
/// `Int64` is the discriminating claim, and it was checked in both directions: a
/// relation whose column really IS a fresh var (the single-clause `SOLO` shape, whose
/// one clause is typed only by `eq`) ACCEPTS `List[(x: Int64)]` and loads clean. So a
/// refusal here can only come from a column that reached a concrete `String`, and this
/// test would go green on a fix that relaxed the column into a wildcard and stopped.
///
/// Backing out `relation_clause_columns` fails it the other way — with the disjoint
/// load error, before the citation is ever typed.
#[test]
fn wi741_the_joined_column_is_typed_string_not_a_wildcard() {
    let errs = try_load_kb_with(NAMED_CLAIMED_INT)
        .err()
        .expect("claiming an `Int64` column over a `String` relation must be refused");
    let text = errs.join("\n");
    assert!(
        text.contains("(x: String)") && text.contains("(x: Int64)"),
        "the refusal must name the relation's OWN column type; got:\n{text}"
    );
}

/// The same column drained UNBOUND, values and all: the spec op filters, a rule
/// subgoal generates. Fails at LOAD without the normalization, for the same reason
/// as the first test.
#[test]
fn wi741_a_spec_typed_column_drains_its_values() {
    let mut interp = interp_for(GENERATED);
    let v = interp
        .call("test.wi741.generated.rows", &[])
        .expect("a spec-filtered column must drain");
    let mut got = list_column_strings(&v);
    got.sort();
    // `root` from the `eq`-filtered clause, `bart` from the `parent` clause.
    assert_eq!(got, vec!["bart".to_string(), "root".to_string()]);
}

/// A SINGLE-clause spec-typed relation still loads and drains — a no-regression pin on
/// the path the relaxation reaches but the lub does not.
///
/// THIS TEST PASSES WITH AND WITHOUT EITHER AXIS BACKED OUT, by design, and that null
/// result is itself the finding: it was written to measure WHERE the normalization
/// belongs (producer vs. lub), and it showed there is no behavioral difference to
/// measure. A bare `PartialEq.T` column cites exactly as leniently as a fresh
/// `Var::Global` one, because a type parameter IS a wildcard to every consumer that
/// meets it. The producer placement is therefore justified by the invariant it keeps —
/// one spelling of "unknown" downstream — not by an observable this suite can pin.
#[test]
fn wi741_a_single_clause_spec_typed_column_still_drains() {
    let mut interp = interp_for(SOLO);
    let v = interp
        .call("test.wi741.solo.rows", &[])
        .expect("a one-clause spec-typed relation must load and drain");
    assert_eq!(list_column_strings(&v), vec!["root".to_string()]);
}

// ── The guards that must survive ──────────────────────────────────────────

/// A genuinely disjoint pair is STILL a loud load error. This one passes both with
/// and WITHOUT the change, by design — it is the survival pin for the relaxation,
/// not a measurement of it.
#[test]
fn wi741_a_genuinely_disjoint_pair_is_still_loud() {
    let errs = try_load_kb_with(DISJOINT)
        .err()
        .expect("a `String` column against an `Int64` column must stay a load error");
    let text = errs.join("\n");
    assert!(
        text.contains("disjoint types for column `x`"),
        "expected the disjoint-column refusal; got:\n{text}"
    );
}

/// A clause typed `String` THROUGH a spec op — `eq(?x, ?y)` records the bare
/// parameter, `parent.of` then displaces it with `String` — still out-votes an
/// `Int64` clause, loudly.
///
/// This is the `constrain_vid` axis, and the reason the fix is not just "drop every
/// parameter". Back out `constrain_vid` and this test FAILS by loading clean: `?x`
/// keeps `PartialEq.T`, `relation_clause_columns` normalizes it to "unknown", the
/// clause contributes nothing, and the relation silently becomes `Relation[(x:
/// Int64)]` — information the producer had, and lost.
#[test]
fn wi741_a_concretely_typed_clause_still_out_votes() {
    let errs = try_load_kb_with(CONCRETE_OUTVOTES)
        .err()
        .expect("a clause typed String through a spec op must still out-vote an Int64 clause");
    let text = errs.join("\n");
    assert!(
        text.contains("disjoint types for column `x`"),
        "expected the disjoint-column refusal; got:\n{text}"
    );
}

/// Two spec calls at different carriers in one rule are NOT a contradiction. The
/// observable is dot dispatch, which the typer skips for a rule it believes
/// contradictory: back out `constrain_vid` and `?b.peek()` survives into SLD as a raw
/// `Expr::DotApply`. The rule is namespace-level, so the contradiction is not
/// reported — the load stays clean either way and only the dot tells the two apart.
#[test]
fn wi741_two_spec_calls_at_different_carriers_do_not_contradict() {
    let kb = load_kb_with(TWO_CARRIERS);
    assert!(
        !rule_bodies_have_dot(&kb, "test.wi741.twocarriers.peeks"),
        "`?b.peek()` must be dispatched — a rule the typer believes contradictory is \
         neither dispatched nor stamped"
    );
}


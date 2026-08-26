//! WI-741 (WI-714 follow-up) — a relation column typed ONLY by a SPEC operation.
//!
//! `collect_rule_var_types` records a variable's type by reading the DECLARED param
//! type straight out of the callee's signature; it never instantiates. So a spec
//! operation hands back its own parameter: `eq(?x, "root")` records `?x` at
//! `anthill.prelude.PartialEq.T`, a `Term::Ref` to the parameter symbol. That symbol
//! is not a type of anything at the call site — every rule in the KB that calls `eq`
//! records the SAME symbol, for variables of unrelated types.
//!
//! Two consequences, both measured:
//!
//!  1. As a relation COLUMN type it is a THIRD spelling of "unknown", alongside the
//!     `TypeVar` inference wildcard and the raw `Var::Global` WI-714 taught
//!     `join_column_types` about. The cross-clause lub met it as a rival type and
//!     reported the column disjoint, so a two-clause relation mixing it with a
//!     concretely-typed clause failed to LOAD, though both clauses plainly meant
//!     `String`.
//!
//!  2. As a var type it CONTRADICTED. `constrain_vid` unified it, and `unify_types`
//!     resolves the parameter to its ONE shared alias var — so two `eq` calls at
//!     different carriers in one rule bound that single var twice and the rule was
//!     declared to have "contradictory variable types". A contradictory rule is
//!     neither dot-dispatched nor stamped, and for a namespace-level rule the report
//!     is suppressed, so the loss was silent.
//!
//! ## WI-20260819-9C2PZ REPLACED THE MECHANISM UNDER THESE TESTS
//!
//! WI-741 repaired both symptoms while leaving the CONFLATION in place, with two pieces
//! of code that no longer exist: `relation_clause_columns` normalized a bare parameter
//! into a variable minted ONE PER PARAMETER SYMBOL (so columns sharing the parameter kept
//! sharing a variable), and `constrain_vid` carried two arms under which a bare parameter
//! neither displaced a recorded entry nor contradicted one.
//!
//! The callee's parameters are now instantiated with fresh variables PER APPLICATION
//! (`instantiate_declared_type`), which removes the cause instead of the symptoms, so
//! both pieces were deleted — the `constrain_vid` arms after being measured unreachable
//! across the whole corpus. WI-741's own hypothesized fix, "resolve `var_types` through
//! the substitution `collect_rule_var_types` drops", is also IN now: it was genuinely
//! unsound while the parameter was shared (it bound the one alias, and would have typed
//! an `Int64` variable `String`), and per-application instantiation is exactly what makes
//! it sound.
//!
//! WHAT THE REPAIR MUST NOT DESTROY is unchanged and still lives elsewhere: the parameter
//! answers TWO questions, and only the first has the answer "nothing" — *what type is
//! this column* (nothing) and *which columns share a type* (a real fact). Minting a FRESH
//! var per COLUMN erases the second; measured, that broke exactly
//! `wi714_applied_correlated_columns_reject_contradiction` and
//! `wi714_applied_unconstrained_column_accepts_and_narrows`, which own that invariant and
//! are not duplicated here. A per-APPLICATION mint keeps it (one call, one variable) and
//! additionally tells two INDEPENDENT calls apart, which a parameter-symbol-keyed mint
//! could not.
//!
//! CONTROLS, RE-MEASURED under the new mechanism (the old ones named deleted code): four
//! of these seven tests redden when the instantiation is backed out
//! (`…joins_a_concrete_one`, `…typed_string_not_a_wildcard`, `…drains_its_values`,
//! `…do_not_contradict`), one when the resolve-through-σ step is
//! (`…still_out_votes`), and two pass under every back-out by design and say so at their
//! sites.

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
  import anthill.prelude.PartialEq.{eq}

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
  import anthill.prelude.PartialEq.{eq}

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
  import anthill.prelude.PartialEq.{eq}

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
  import anthill.prelude.PartialEq.{eq}

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
  import anthill.prelude.PartialEq.{eq}

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
  import anthill.prelude.PartialEq.{eq}

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
/// CONTROL: back out the per-application instantiation and this fails at LOAD with
/// "disjoint types for column `x`". It does not redden on the other two halves —
/// `eq(?x, "root")` puts only ONE constraint on `?x`, so there is nothing for a concrete
/// type to displace; the resolve-through-σ axis is measured by
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
/// `Int64` is the discriminating claim. When WI-741 wrote this, the both-directions
/// check was the single-clause `SOLO` shape ACCEPTING `List[(x: Int64)]`, proving a
/// column that really is a fresh var admits anything. That cross-check no longer holds
/// and its retirement is a gain, not a gap: WI-20260819-9C2PZ reads the LITERAL argument
/// of `eq(?x, "root")`, so `SOLO`'s column reaches a concrete `String` too and now
/// refuses `Int64` (measured). The claim this test makes stands on its own — a refusal
/// naming `(x: String)` against `(x: Int64)` cannot come from a wildcard column.
///
/// CONTROL: back out the instantiation and it fails the other way — with the disjoint
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
/// subgoal generates.
///
/// CONTROL: back out the instantiation and it fails at LOAD, for the same reason as the
/// first test.
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
/// THIS TEST PASSES UNDER EVERY BACK-OUT, by design, and that null result is itself the
/// finding — re-measured under WI-20260819-9C2PZ and still null. It was written to
/// measure WHERE the "unknown" normalization belongs (producer vs. lub) and showed there
/// is no behavioral difference to measure: a bare `PartialEq.T` column cites exactly as
/// leniently as a fresh `Var::Global` one, because a type parameter IS a wildcard to
/// every consumer that meets it. What it still buys is the only evidence here that a
/// one-clause spec-typed relation RUNS; every measuring row in this file is a refusal or
/// a two-clause load.
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
/// This is the axis that says the fix is not just "drop every parameter": the clause
/// KNOWS `?x` is a `String` and must not lose it.
///
/// CONTROL: back out the resolve-through-σ step and this test FAILS by loading clean.
/// `eq(?x, ?y)` puts both variables on this call's fresh parameter variable and
/// `parent.of` binds THAT variable to `String` — in the substitution. Unresolved, the
/// column publishes the bare variable, contributes nothing to the lub, and the relation
/// silently becomes `Relation[(x: Int64)]` — information the producer had, and lost.
/// (Under WI-741 the same failure came from backing out `constrain_vid`, which held the
/// concrete-displaces-parameter rule this now gets from ordinary unification.)
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
/// observable is dot dispatch, which the typer only runs for a NON-contradictory rule.
///
/// CONTROL: back out the instantiation and `?b.peek()` survives into SLD as a raw
/// `Expr::DotApply`. The rule is namespace-level, so the contradiction is not reported —
/// the load stays clean either way and only the dot tells the two apart. (Under WI-741
/// the same failure came from backing out `constrain_vid`'s never-contradict arm; the
/// per-application variable makes the unification simply correct instead.)
#[test]
fn wi741_two_spec_calls_at_different_carriers_do_not_contradict() {
    let kb = load_kb_with(TWO_CARRIERS);
    assert!(
        !rule_bodies_have_dot(&kb, "test.wi741.twocarriers.peeks"),
        "`?b.peek()` must be dispatched — a rule the typer believes contradictory is \
         neither dispatched nor stamped"
    );
}



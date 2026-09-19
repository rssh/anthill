//! WI-20260827-W1YKH: the term-accessor family reads ANY carrier.
//!
//! A rule body hands an operand over as an OCCURRENCE (`Value::Node`, or an `Entity`
//! wrapping one) — the resolver's σ-applied goals are deliberately not interned (see
//! the representation note in CLAUDE.md). Two reflect readers matched `Value::Term`
//! alone and so refused every rule-body call, each failing in a DIFFERENT and equally
//! unhelpful way:
//!
//!   * `term_field` raised `TypeMismatch`, which the bridge dispositions as a `Fault`:
//!     the goal delays and the search is MARKED INCOMPLETE ("a goal could not be
//!     evaluated"). So the failure is reported — an earlier version of this comment said
//!     it was swallowed silently, which was wrong and came from reading a probe's stdout
//!     with stderr discarded. The value answer is `None` by design (WI-483: a callee's
//!     failure must not break the enclosing rule), so a reader still gets NO DATA from a
//!     reflect accessor it was entitled to read;
//!   * `term_list_items` raised `EvalError::Internal`, which `bridge_op_to_eval` treats
//!     as an invariant breach and ASSERTS on — a rule body PANICKED the process.
//!
//! The repair is one idea in two places: READ the carrier through `TermView`, never
//! lower it. `term_functor_name` always worked because it already did.
//!
//! WHAT ELSE THIS CHANGE TOUCHES, AND WHY — the boundary is easy to get wrong in both
//! directions, so each is stated:
//!   * `meta_has_flag` / `meta_value` answered from a rule body ALL ALONG (they lower
//!     through the `Node`-aware `value_to_term`), so they were never part of this
//!     family's defect. They are rewritten as view reads anyway, because `meta` is
//!     migrating off `TermId` onto values (user direction, 2026-09-16). The history is
//!     worth keeping: an earlier draft justified the rewrite as fixing a leak — one
//!     interned term per joined row — and that is FALSE. The store is hash-consed, so
//!     lowering an already-interned structure allocates nothing, and a growth test
//!     written to pin the claim PASSED with the whole change backed out. What the
//!     rewrite really buys is one owner for the by-local-name lookup and a read path
//!     that no longer demands `&mut KnowledgeBase`.
//!   * `replace_named_arg` / `unify` CONSTRUCT and unify terms rather than read them,
//!     so a `TermId` is what they genuinely need.
//!
//! AND ONE THING THE FIX ITSELF FORCED: `term_to_string` lowered via `alloc_from_value`,
//! which refuses every `Node` as an `EvalError::Internal` — the bridge's assert. That
//! was unreachable while the accessors all hard-matched `Value::Term`; once `term_field`
//! hands back a child on its own carrier it is reachable, through the shipped chain
//! `term_field` → `term_list_items` → `term_to_string` in `anthill-todo`. It now takes
//! the `Node`-aware boundary, which is correct there because printing is a LEAF.
//!
//! WHAT FAILS WHEN THE CHANGE IS BACKED OUT — verified by reverting `eval/builtins.rs`
//! and re-running, not asserted from reading:
//!   * `a_field_read_answers_definitely_from_a_rule_body` — FAILED: every solution goes
//!     conditional (non-empty `residual`), so the DEFINITE count drops to 0.
//!   * `a_missing_field_answers_none_rather_than_flounders` — FAILED, same way.
//!   * `a_list_read_does_not_panic_from_a_rule_body` — FAILED: panics in the bridge
//!     (`resolve.rs`) rather than reaching any assertion.
//!   * `a_list_read_folds_a_real_spine` — the emptiness row above is satisfied by a
//!     walker that answers `None` for everything, so this one drives a list with
//!     elements in it and asserts the COUNT.
//!   * `a_functor_read_answers_either_way` and `a_flag_read_answers_either_way` — ok
//!     BOTH ways, by design. They are the CONTROLS: they pin that the fixture's join
//!     yields rows and that `counts` really separates definite from residual, so the
//!     rows above cannot pass vacuously on an empty join.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, TermId, Var};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

/// A sort whose two constructors carry different blocks. `subject_meta` narrows the
/// `DeclarationMeta` join to THIS file's `marked`, so the fixture is load-bearing: an
/// earlier draft joined the whole KB and every row stayed green with the sort deleted.
const FIXTURE: &str = r#"
namespace test.w1ykh
  import anthill.prelude.{Bool, String, Option, Int64, List}
  import anthill.prelude.Option.{some, none}
  import anthill.reflect.{Term, DeclarationMeta, term_field, term_list_items,
                          term_functor_name, meta_has_flag, meta_value, as_term, term_as_int,
                          term_to_string}

  sort Subject
    entity plain(x: Int64)
    entity marked(x: Int64) @[Tag: "kept"]
  end

  -- The rows below join DeclarationMeta for `Subject`'s own constructors ONLY — the
  -- `term_functor_name` guard pins each `?m` to a block this file declares. Joining the
  -- whole KB would let any stdlib `@[…]` satisfy them, and then the fixture above could
  -- be deleted with every row still green (measured: it could).
  rule subject_meta(?m) :-
    DeclarationMeta(name: ?n, meta: ?m), term_functor_name(?n) = some("marked")

  -- POSITIVE read, spelled as a REFUTATION of `none()` rather than as a match on the
  -- payload. `some(?v)` would not do: an unbound variable inside the pattern does not
  -- bind here (§5.3 — `eq` never binds, WI-20260822-F0HHB), so that row answers 0
  -- whether the reader works or not. `not(… === none())` needs the call to RUN and to
  -- FIND the key, which is exactly the claim, and it is measured to fail when the
  -- reader is backed out.
  rule reads_a_field(?m)   :- subject_meta(?m), not(term_field(?m, "Tag") === none())
  rule reads_a_missing(?m) :- subject_meta(?m), term_field(?m, "absent") === none()
  rule reads_a_flag(?m)    :- subject_meta(?m), meta_has_flag(?m, "Tag") = true
  -- `meta_value` READ FROM A RULE BODY: the block rides as an occurrence here, so this
  -- is the row that fails if the meta readers stop reading carriers.
  --
  -- A REFUTATION OF `none()`, not a match on the payload, and that is forced rather
  -- than chosen. MEASURED: `some(?v)` answers 0 because an unbound var inside the
  -- pattern does not bind (§5.3, WI-20260822-F0HHB); and NO ground spelling matches
  -- either — `= some("kept")` and `= some(as_term("kept"))` both answer 0, because the
  -- payload is the key's child on its own carrier (a `Term`-carried `Const`) while both
  -- of those are a bare `String`. So a rule body can assert THAT the key was found and
  -- not WHAT it holds. Recorded on the ticket as a usability gap in `meta_value`, not
  -- fixed here.
  rule reads_a_meta_value(?m) :- subject_meta(?m), not(meta_value(?m, "Tag") === none())
  rule reads_a_functor(?m) :- subject_meta(?m), term_functor_name(?m) = some("meta")

  -- The rule-body row for the list reader: its bug was a PANIC, so reaching any answer
  -- at all is what this guards. A `meta(…)` block is not a cons spine, so `[]` is the
  -- honest answer — which is also what a totally broken walker returns, hence
  -- `three_items` below, where the walker is driven on a REAL spine.
  rule reads_a_list(?m)    :- subject_meta(?m), term_list_items(?m) === []

  -- Driven from an OPERATION body, where an unbound result binds (a rule body's does
  -- not — §5.3, `eq` never binds, WI-20260822-F0HHB), so the walker's CONTENT can be
  -- asserted rather than only its emptiness.
  operation three_items() -> Int64 = List.length(term_list_items(as_term([1, 2, 3])))

  -- THIS ITEM'S HEADLINE ROW. `as_term` is the identity at the host level, so
  -- `as_term(some(7))` hands on a `Value::Entity` — "the canonical way to GET a term is
  -- rejected by the operation that exists to READ one". Measured at filing as a
  -- SUSPENSION; it must now answer, and the field it reads is the Int 7.
  -- A LEAF term: `7` is a `Const`, not `Fn`-shaped, so the contract says `none()`.
  operation field_of_a_literal() -> Option[T = Term] = term_field(as_term(7), "value")

  -- The field `term_field` hands back rides on ITS OWN carrier; printing it is the
  -- shipped chain's last step.
  operation print_a_field() -> String =
    match term_field(as_term(some(7)), "value")
      case none() -> ""
      case some(t) -> term_to_string(t)

  operation field_of_as_term() -> Option[T = Int64] =
    match term_field(as_term(some(7)), "value")
      case none() -> none()
      case some(t) -> term_as_int(t)
end
"#;

/// `<rule>(?m)`, as a goal.
fn goal(kb: &mut KnowledgeBase, rule: &str) -> TermId {
    let sym = kb
        .try_resolve_symbol(&format!("test.w1ykh.{rule}"))
        .unwrap_or_else(|| panic!("`{rule}` is not in the KB — the fixture did not load it"));
    let name = kb.intern("m");
    let vid = kb.fresh_var(name);
    let arg = kb.alloc(Term::Var(Var::Global(vid)));
    kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::from_slice(&[arg]),
        named_args: SmallVec::new(),
    })
}

/// (definite, conditional) solution counts for `<rule>(?m)`.
///
/// THE SPLIT IS THE WHOLE POINT. A floundered goal still yields a `Solution` — with a
/// non-empty `residual` — so `!sols.is_empty()` passes just as well on a reader that
/// never ran. Only the DEFINITE count tells the two apart.
fn counts(kb: &mut KnowledgeBase, rule: &str) -> (usize, usize) {
    let g = goal(kb, rule);
    let sols = kb.resolve(&[g], &ResolveConfig::default());
    let definite = sols.iter().filter(|s| s.residual.is_empty()).count();
    (definite, sols.len() - definite)
}

fn fixture_kb() -> KnowledgeBase {
    crate::common::load_kb_with(FIXTURE)
}

#[test]
fn a_field_read_answers_definitely_from_a_rule_body() {
    let mut kb = fixture_kb();
    // THE POSITIVE READ. `marked` carries `@[Tag: "kept"]`, so the field is THERE, and
    // a reader that cannot see the rule body's carrier answers `none()` — which this
    // row refutes. Its `= none()` twin below cannot distinguish that case from an
    // honestly-absent key, which is why both rows exist.
    //
    // WHY NOT `= some(?v)`: measured, that answers 0 with the fix IN, because an
    // unbound variable inside the pattern does not bind (§5.3, `eq` never binds —
    // WI-20260822-F0HHB owns it). A row spelled that way would fail for a reason that
    // has nothing to do with this ticket.
    let (definite, conditional) = counts(&mut kb, "reads_a_field");
    assert_eq!(
        definite, 1,
        "`not(term_field(?m, \"Tag\") = none())` answered {definite} definite \
         ({conditional} conditional) — `marked`'s block carries `Tag`, so the reader \
         must FIND it on the rule body's occurrence carrier"
    );
}

#[test]
fn a_missing_field_answers_none_rather_than_flounders() {
    let mut kb = fixture_kb();
    let (definite, conditional) = counts(&mut kb, "reads_a_missing");
    assert_eq!(
        definite, 1,
        "`term_field(?m, \"absent\") = none()` answered {definite} definite \
         ({conditional} conditional) — a key the block does not carry must answer \
         `none()` DEFINITELY, not residualize"
    );
}

#[test]
fn a_list_read_does_not_panic_from_a_rule_body() {
    let mut kb = fixture_kb();
    // Before the fix this did not return a value to assert on: `alloc_from_value`
    // answered `UnsupportedVariant("Node")` as an `EvalError::Internal`, and the
    // SLD→eval bridge asserts on that. Reaching the assertion below at all is what
    // this row guards; `a_list_read_folds_a_real_spine` covers the CONTENT.
    let (definite, conditional) = counts(&mut kb, "reads_a_list");
    assert_eq!(
        definite, 1,
        "`term_list_items(?m) === []` answered {definite} definite \
         ({conditional} conditional) — a `meta(…)` block is not a cons spine, so the \
         one joined row's answer is the EMPTY list"
    );
}

#[test]
fn a_list_read_folds_a_real_spine() {
    // The emptiness row above is satisfied by a walker that returns `None` for
    // EVERYTHING, so the spine logic needs a list with elements in it. Driven from an
    // operation body because a rule body cannot bind a host op's result (this ticket's
    // second, unfixed finding), so this is where the CONTENT can be asserted.
    let mut interp = crate::common::interp_for(FIXTURE);
    let n = match interp.call("test.w1ykh.three_items", &[]) {
        Ok(anthill_core::eval::Value::Int(n)) => n,
        other => panic!("`three_items` must evaluate to an Int64: {other:?}"),
    };
    assert_eq!(
        n, 3,
        "`term_list_items(as_term([1, 2, 3]))` folded {n} items — the cons/nil spine \
         walk is what this measures, and an all-`None` walker answers 0 here while \
         still satisfying the emptiness row"
    );
}

#[test]
fn a_field_reads_through_as_term() {
    // THE HEADLINE ROW of WI-20260827-W1YKH: `as_term(some(7))` hands on a
    // `Value::Entity`, and `term_field` refused exactly that carrier — "the canonical
    // way to GET a term is rejected by the operation that exists to READ one". Measured
    // at filing as a SUSPENSION, with the correct answer `some(7)`.
    //
    // Driven from an operation body so the result BINDS (a rule body's `=` does not —
    // §5.3), and read all the way down to the Int rather than stopping at `some(…)`:
    // the point is that the field's VALUE survives the carrier, not merely that some
    // option came back.
    let mut interp = crate::common::interp_for(FIXTURE);
    let got = interp
        .call("test.w1ykh.field_of_as_term", &[])
        .expect("`field_of_as_term` must evaluate");
    let anthill_core::eval::Value::Entity { functor, named, .. } = &got else {
        panic!("expected `some(value: 7)`, got {got:?}")
    };
    assert_eq!(
        interp.kb().local_name_of(*functor),
        "some",
        "`term_field(as_term(some(7)), \"value\")` answered {got:?} — at filing this \
         SUSPENDED, because `as_term` yields a `Value::Entity` the reader refused"
    );
    let inner = named
        .iter()
        .find_map(|(k, v)| (interp.kb().local_name_of(*k) == "value").then(|| v.clone()))
        .unwrap_or_else(|| panic!("`some(value: …)`: {got:?}"));
    assert!(
        matches!(inner, anthill_core::eval::Value::Int(7)),
        "the field's value must survive the carrier: {inner:?}"
    );
}

#[test]
fn a_meta_value_read_answers_from_a_rule_body() {
    let mut kb = fixture_kb();
    // A CONTROL, and labelled honestly this time: it passes BOTH ways. An earlier
    // version of this comment claimed it was the row that fails when the `kb/load.rs`
    // half is backed out — false, and it contradicted this file's own header, which
    // says the meta readers answered from a rule body all along. Reverting them to
    // `value_to_term` + `load::meta_value` still finds the `Tag` key, so this still
    // answers 1. What it pins is that the REWRITE changed no answer, which is the only
    // claim the meta half makes (/code-review).
    //
    // WHAT IT DOES NOT ASSERT, said here rather than left to be assumed: the payload's
    // VALUE. See the fixture comment — no spelling of `= some(…)` matches it from a
    // rule body, so this row proves the key was FOUND on the occurrence carrier and
    // stops there.
    let (definite, conditional) = counts(&mut kb, "reads_a_meta_value");
    assert_eq!(
        definite, 1,
        "`not(meta_value(?m, \"Tag\") = none())` answered {definite} definite \
         ({conditional} conditional) — `marked`'s block carries `@[Tag: \"kept\"]`, so the \
         reader must find it on the rule body's occurrence carrier"
    );
}

#[test]
fn a_flag_read_answers_either_way() {
    let mut kb = fixture_kb();
    let (definite, conditional) = counts(&mut kb, "reads_a_flag");
    // CONTROL, and what it controls is a REWRITE rather than an absence: `meta_has_flag`
    // always answered from a rule body and is rewritten here for the meta→values
    // migration, so it must give the SAME answer before and after. It passes both ways
    // by design. An earlier version of this comment called the reader "UNCHANGED by this
    // ticket", which was false (/code-review).
    assert!(
        definite > 0,
        "`meta_has_flag(?m, \"Tag\") = true` answered no definite solution \
         ({definite} definite, {conditional} conditional) — `subject_meta` yields \
         exactly `marked`'s block, which carries `@[Tag: \"kept\"]`"
    );
}

#[test]
fn a_leaf_term_answers_none_rather_than_raising() {
    // THE CONTRACT HALF of the receiver rule, and the half a draft of this change broke:
    // a term that is not `Fn`-shaped has no named args and must answer `none()`, which
    // is what `anthill-todo`'s `unwrapped_string` — documented "Total by design" — is
    // built on. A guard that tests the head for `Functor` raises here instead.
    let mut interp = crate::common::interp_for(FIXTURE);
    let got = interp
        .call("test.w1ykh.field_of_a_literal", &[])
        .expect("a literal term must ANSWER, not raise");
    assert!(
        matches!(&got, anthill_core::eval::Value::Entity { functor, .. }
                 if interp.kb().local_name_of(*functor) == "none"),
        "`term_field(as_term(7), \"value\")` must answer `none()`: {got:?}"
    );
}

#[test]
fn a_non_term_carrier_raises_rather_than_answering_none() {
    // THE OTHER HALF: a value that is no term at all must RAISE, never be spelled as
    // `none()` / `[]` — W1YKH's acceptance ("no accessor answers `none()` for a carrier
    // it simply did not recognise"). Driven through `Unit`, which reads as
    // `ViewHead::Functor { functor: None }` and so slips past a bare `Functor { .. }`
    // test — the exact hole /code-review found in the first guard.
    let mut interp = crate::common::interp_for(FIXTURE);
    let unit = anthill_core::eval::Value::Unit;
    for op in ["anthill.reflect.term_field", "anthill.reflect.term_list_items"] {
        let args: Vec<anthill_core::eval::Value> = if op.ends_with("term_field") {
            vec![unit.clone(), anthill_core::eval::Value::Str("x".into())]
        } else {
            vec![unit.clone()]
        };
        let r = interp.call(op, &args);
        assert!(
            r.is_err(),
            "`{op}` on a functor-less aggregate must RAISE, not answer: {r:?}"
        );
    }
}

#[test]
fn a_node_carried_term_prints_without_interning() {
    // `term_to_string` lowered through `alloc_from_value`, which refuses every `Node` as
    // an `EvalError::Internal` — the disposition the bridge ASSERTS on. Unreachable
    // while the accessors all hard-matched `Value::Term`; live once they hand back a
    // child on its own carrier, through a chain that ships in anthill-todo. Nothing
    // drove it until /code-review said so.
    //
    // ALSO A GROWTH ROW: printing must not intern. `print_occurrence` renders the
    // occurrence natively, so the store must not move — an earlier draft reached for
    // `value_to_term` here and would have pinned one transient tree per printed row.
    let mut interp = crate::common::interp_for(FIXTURE);
    let before = interp.kb().term_store_len();
    let printed = interp
        .call("test.w1ykh.print_a_field", &[])
        .expect("`print_a_field` must evaluate");
    let grew = interp.kb().term_store_len() - before;
    match &printed {
        anthill_core::eval::Value::Str(s) => assert!(
            s.contains('7'),
            "the printed text must be the field's own: {s:?}"
        ),
        other => panic!("expected a String: {other:?}"),
    }
    assert!(
        grew <= 2,
        "printing grew the hash-consed store by {grew} — `term_to_string` is lowering \
         its receiver instead of printing the occurrence"
    );
}

#[test]
fn a_functor_read_answers_either_way() {
    let mut kb = fixture_kb();
    let (definite, conditional) = counts(&mut kb, "reads_a_functor");
    // CONTROL — `term_functor_name` reads the occurrence HEAD and never lowered, so it
    // answered before this ticket and answers after. It earns its place by pinning the
    // two assumptions the rows above rest on: that the fixture's join yields rows at
    // all, and that `counts` really does separate definite from residual.
    assert!(
        definite > 0,
        "the control answered no definite solution ({definite} definite, \
         {conditional} conditional) — the fixture joins no rows, so the rows above \
         would pass vacuously"
    );
}

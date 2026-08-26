//! WI-1044 — a TOP-LEVEL QUERY on a defaulted spec op must dispatch like the same
//! goal written as a rule body: to the implementation the carrier SUPPLIES (WI-444 /
//! WI-1010), and never to the spec's default over one.
//!
//! ## The measurement, on WI-1026's own fixture
//!
//! `program(ns, ONE_LEAF, ONE_SUPPLY, …)` — one supplier, arriving by the WI-431
//! instance-fact route — driven two ways, before any code changed:
//!
//! | how the goal is written | before | after |
//! |---|---|---|
//! | `rule answer(?r) :- Desc.describe(leaf(), ?r)`, queried as `answer(?r)` | `Int(7)` | unchanged |
//! | `Desc.describe(leaf(), ?r)` as a TOP-LEVEL QUERY | **`Int(1)`** — the DEFAULT | **`Int(7)`** |
//!
//! Both definite. One goal text, two answers, decided by nothing but whether a rule
//! happened to be wrapped around it — which is WI-1026's own defect surviving in the
//! population that ticket could not reach.
//!
//! And with TWO suppliers, the same fixture minus every operation and rule, so that
//! nothing but the query names the call:
//!
//! | | before | after |
//! |---|---|---|
//! | the program loads | clean | clean (correctly — 058 §4.9 refuses at the CALL) |
//! | `Desc.describe(leaf(), ?r)` as a query | **`Int(1)`, definite** | **REFUSED**, both rivals named |
//!
//! The load refusal WI-1026 delivered was not bypassed by accident: there was nothing
//! to bypass. A tie is refused where the CALL is, and this call is in neither a rule
//! body nor an operation body.
//!
//! ## Why the fix is two pieces and not one
//!
//! **The ANSWER is the resolver's** (`classify_unstamped_spec_op_call`). `reduce_op_value`
//! read the typer's pin and fell back to the SPELLED functor when there was none — and
//! for a defaulted spec op the spelled functor's body is the DEFAULT. A query goal
//! passes no typer pass at all: `type_rule_bodies` walks the rules the loader stored,
//! and a query belongs to no rule, so the occurrence the WI-938 hook materializes out
//! of the goal term carries no `CallClass`. The resolver now classifies such a call
//! from the values its arguments carry, through
//! [`anthill_core::eval::eval::spec_op_dispatch_by_value`] — the same owner eval's
//! step-3 override reads — and stamps the verdict with the typer's own writer
//! (`classify_pin_or_apply_within`), so Pin-vs-NeedsDict is not decided a second way.
//!
//! **The REFUSAL is the query's own load moment's** (`ambiguous_query_dispatch`). The
//! resolver has no diagnostic channel — `BuiltinResult` is Success / Bindings / Delay /
//! Failure, and `bridge_op_to_eval` residualizes an `AmbiguousSpecOpDispatch` to `None`
//! by design, because a bridged eval may not abort an enclosing rule. So the tie is
//! caught where a query's other unreadable-text refusals are caught: ahead of the run,
//! over the converted pattern, beside `ambiguous_query_names` and for its stated reason
//! ("no single reading for the run to be an answer TO"). The resolver still DECLINES to
//! reduce such a call, so the two cannot disagree — one refuses, the other answers
//! nothing, and neither produces the default.
//!
//! ## What this fix turned out to be WIDER than the ticket said, and why that stands
//!
//! The ticket scoped the population to "query goals and runtime-asserted rules … never
//! pass `type_rule_bodies`". That is not the whole of it. A stored rule body DOES pass
//! that walk and still comes out `Unclassified` whenever the typer could not pin the
//! carrier — `rule via(?x, ?r) :- Desc.describe(?x, ?r)`, receiver bound only by the
//! caller, which 058 §3.3 puts out of scope for compile-stage selection. Classifying
//! on demand fires there too, and MEASURED it moved two delivered assertions:
//! `wi1040_require_clause_dictionary_test`'s `the_same_clause_without_require_runs_the_-
//! spec_default` and `the_check_only_spelling_is_unchanged`, both of which pinned `1`.
//!
//! It stands, because `1` was the same defect one spelling over: eval's step 3 has
//! ALWAYS dispatched that call by value (`resolve_carrier_override_by_value`), so
//! `operation probe(x: T) = Desc.describe(x)` answered `7` while the identical
//! unpinnable call in a rule body answered `1`. Narrowing this to "only what the WI-938
//! hook built" would have needed a flag threaded from one caller — a gate keyed on
//! WHERE the call was written, which is the shape this whole cluster exists to delete.
//! Both WI-1040 tests are re-aimed at their sites, and the discrimination the headline
//! lost is picked up by `a_two_supplier_carrier_dispatches_silently_through_the_-
//! dictionary`, which was documented "PASSES EITHER WAY" and is now a live control.
//!
//! ## What fails when each piece is backed out — MEASURED, one revert each
//!
//! | test | resolver classification | query-side refusal | `runtime_carrier_sort` Node arm |
//! |---|---|---|---|
//! | `a_top_level_query_reaches_the_supplied_impl` | **FAILS** (`Int(1)`) | ok | **FAILS** (`Int(1)`) |
//! | `the_query_and_the_rule_body_answer_alike` | **FAILS** | ok | **FAILS** |
//! | `a_two_supplier_query_never_answers_the_default` | **FAILS** (`Int(1)`) | ok | **FAILS** |
//! | `a_two_supplier_query_is_refused` | ok | **FAILS** | ok |
//! | `the_query_refusal_shares_the_load_refusals_message_body` | ok | **FAILS** | ok |
//! | `a_backtracked_receiver_reclassifies_per_carrier` | **FAILS** (`[1, 1]`) | ok | **FAILS** |
//! | `the_query_goal_carries_no_typer_stamp` | ok | ok | ok |
//! | `a_carrier_with_no_supplier_still_runs_the_default_at_a_query` | ok | ok | ok |
//! | `wi1026::*` (whole suite) | ok | ok | ok |
//!
//! The `runtime_carrier_sort` column is a third piece and is why it is listed: that
//! function excluded `Value::Node` from the carriers a value may name, while its own
//! callee `value_functor` answers for one ("an occurrence lowers too"). The resolver
//! hands its arguments in the occurrence carrier, so without widening that arm every
//! classification here reports "no supplier" and the fix is inert — the WI-1016 rule
//! that both carriers must key alike, unapplied. It is listed as a column rather than
//! folded into the first because it is an independent edit in a different file, and a
//! reader backing out "the WI-1044 change" would otherwise leave it behind. Columns 1
//! and 3 have the SAME failure set, which is what "prerequisite" means here — neither
//! is sufficient alone.
//!
//! THE TWO REFUSAL ROWS SURVIVE COLUMN 3, and the first draft of this table predicted
//! otherwise. The query walk reads its arguments as `Value::term(tid)` off the
//! converted pattern, never in the occurrence carrier, so the Node arm is not on its
//! path at all. The two faces of this fix therefore do not share that dependency —
//! which is worth knowing, because it means the refusal keeps working on a query the
//! resolver has stopped being able to classify.
//!
//! `a_backtracked_receiver_reclassifies_per_carrier` FAILS in columns 1 and 3 —
//! MEASURED `[1, 1]`, the spec default twice — and the first draft of this table said
//! it passed either way. It does not, but note WHY it fails, because it is not what
//! the test is FOR: with the classification out, neither carrier is reached, so the
//! failure is the ticket's headline defect again rather than the σ hazard. What it is
//! for is a change to `with_fresh_vars` / the WI-938 rebuild that started SHARING one
//! occurrence across activations — nothing else in the tree would notice that, and the
//! reversed-order half of the test is what makes a stuck stamp impossible to pass by
//! coincidence.
//!
//! The last two pass EITHER WAY **by design**. `the_query_goal_carries_no_typer_stamp`
//! pins the PRECONDITION this ticket is about (the goal reaches the WI-938 hook with no
//! `CallClass`, so it is that path being exercised and not a pre-typed rule) — it must
//! keep holding, or the other tests stop measuring the population they name. And the
//! no-supplier row is what makes a default a default; it is the control the refusal
//! must not consume.
//!
//! REFERENCE: `/code-review` 2026-08-07 finding 1; WI-1026 sec 20; WI-1012; WI-938;
//! WI-1037; WI-1042; `docs/design/058-implementation.md` §3.7, §4.9.

use anthill_core::eval::Value;
use anthill_core::kb::KnowledgeBase;

use crate::wi1026_rule_body_spec_op_dispatch_test::{one_supplier, program, two_suppliers};

/// The TWO-supplier fixture with NO rule and NO operation naming the call — so the
/// only site that mentions `Desc.describe` is the query itself. That subtraction is
/// the whole point: leave WI-1026's rule in and its LOAD refusal fires, and whatever
/// the query does is masked (the contamination WI-1026's own header records for the
/// mirror-image case).
fn two_suppliers_query_only(ns: &str) -> String {
    two_suppliers(ns, "")
}

/// The converted query term for `pattern`, by the CLI's own path
/// (`load::convert_query_term` at `<global>`, via
/// [`crate::common::query_pattern_term`]) rather than a hand-built resolver goal.
/// A hand-built `Term::Fn` would be a different goal from the one `anthill query`
/// resolves, and this ticket is about the query path specifically.
fn query_term(kb: &mut KnowledgeBase, pattern: &str) -> anthill_core::kb::term::TermId {
    crate::common::query_pattern_term(kb, pattern)
}

/// Every solution of top-level query `pattern` as `(the reified LAST positional, the
/// solution is definite)`. The result column of a functional-relation goal is
/// positional and last (WI-938), so that is the slot to read.
fn query_answers(kb: &mut KnowledgeBase, pattern: &str) -> Vec<(Value, bool)> {
    use anthill_core::kb::resolve::ResolveConfig;
    use anthill_core::kb::term::Term;
    let goal = query_term(kb, pattern);
    let r_var = match kb.get_term(goal) {
        Term::Fn { pos_args, .. } => *pos_args.last().expect("pattern has no positional args"),
        other => panic!("query pattern `{pattern}` is not an application: {other:?}"),
    };
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .map(|sol| (kb.reify(r_var, &sol.subst), sol.is_definite()))
        .collect()
}

/// The single definite Int answer of top-level query `pattern`. Panics on any other
/// shape, `[]` included: "the query returned nothing" is one of the two symptoms this
/// ticket exists to stop, so it must never read as a pass.
fn query_int(kb: &mut KnowledgeBase, pattern: &str) -> i64 {
    match query_answers(kb, pattern).as_slice() {
        [(Value::Int(i), true)] => *i,
        other => panic!("`{pattern}` must answer exactly one definite Int, got {other:?}"),
    }
}

/// The qualified spelling of the call under test, as a QUERY PATTERN. Every name is
/// fully qualified because the pattern is converted at `<global>`, which imports
/// nothing (the CLI's `-i` flags are what widen it).
fn describe_pattern(ns: &str) -> String {
    format!("{ns}.Desc.describe({ns}.Leaf.leaf(), ?r)")
}

/// THE HEADLINE. One supplier, reaching the carrier through a WI-431 instance fact —
/// the route with no typer pin to inherit even where a typer runs — and the goal
/// written as a top-level query rather than inside a rule. Before this it answered
/// `1`, the spec's own default, definite.
#[test]
fn a_top_level_query_reaches_the_supplied_impl() {
    let ns = "test.wi1044.one";
    let src = one_supplier(ns, "");
    let mut kb = crate::common::load_kb_with(&src);
    assert_eq!(
        query_int(&mut kb, &describe_pattern(ns)),
        7,
        "a top-level query must reach the fact-bound impl, not the spec's default",
    );
}

/// THE PAIRING, and the claim the headline alone cannot make: the SAME call text
/// answers the SAME thing whether a rule is wrapped around it or not. Asserted in one
/// program, so a difference here cannot be a difference of fixture.
///
/// A test on the query arm alone would pass equally if the rule body had regressed to
/// `1` too, and would then read as agreement.
#[test]
fn the_query_and_the_rule_body_answer_alike() {
    let ns = "test.wi1044.alike";
    let src = one_supplier(ns, "  rule answer(?r) :- Desc.describe(leaf(), ?r)\n");
    let mut kb = crate::common::load_kb_with(&src);
    let via_rule = crate::common::query_unary(&mut kb, &format!("{ns}.answer"));
    let via_query = query_answers(&mut kb, &describe_pattern(ns));
    assert!(
        matches!(via_rule.as_slice(), [(Value::Int(7), true)]),
        "the rule-body arm must still answer the supplied impl (WI-1026): {via_rule:?}",
    );
    assert_eq!(
        format!("{via_query:?}"),
        format!("{via_rule:?}"),
        "one goal text must not answer two ways depending on where it is written",
    );
}

/// THE TIE, at the query's own load moment. The program is LEGAL — 058 §4.9 refuses a
/// tie at the CALL, and with no rule and no operation in the file there is no call for
/// the loader to refuse — so the query is where it must be caught.
///
/// Asserts the message, not merely that something failed: each rival is named by its
/// SUPPLY ROUTE, because the three routes are three different syntaxes and the author
/// has to know which text to delete.
#[test]
fn a_two_supplier_query_is_refused() {
    let ns = "test.wi1044.tie";
    let src = two_suppliers_query_only(ns);
    let mut kb = crate::common::load_kb_with(&src);
    let qt = query_term(&mut kb, &describe_pattern(ns));
    let msgs = kb.ambiguous_query_dispatch(qt);
    let msg = msgs.join("\n");
    assert_eq!(msgs.len(), 1, "one call, one refusal: {msg}");
    assert!(msg.contains("ambiguous dispatch"), "{msg}");
    assert!(
        msg.contains("Desc.describe"),
        "the spec op must be named: {msg}"
    );
    assert!(
        msg.contains(&format!("carrier `{ns}.Leaf`")),
        "the carrier must be named: {msg}"
    );
    assert!(
        msg.contains(&format!("the carrier's own member '{ns}.Leaf.describe'")),
        "route 1 named by its route: {msg}",
    );
    assert!(
        msg.contains(&format!(
            "an instance fact binding `describe = {ns}.otherDescribe`"
        )),
        "route 2 quoted by the BINDING the author wrote: {msg}",
    );
}

/// The refusal above shares the LOAD face's message body, so the query face cannot
/// grow a fourth wording for the refusal WI-1012 wrote once.
///
/// Compared against the rule-body spelling of the same program with the `line:col`
/// prefix stripped — a query pattern is a whole CLI argument and so has no line to
/// report, which is the one difference the two faces are allowed.
#[test]
fn the_query_refusal_shares_the_load_refusals_message_body() {
    let ns = "test.wi1044.faces";
    let rule_src = two_suppliers(ns, "  rule answer(?r) :- Desc.describe(leaf(), ?r)\n");
    let load_msg = crate::wi1012_static_supplier_tie_test::refusal(&rule_src);
    let (_, load_body) = crate::wi1012_static_supplier_tie_test::located(&load_msg);

    let mut kb = crate::common::load_kb_with(&two_suppliers_query_only(ns));
    let qt = query_term(&mut kb, &describe_pattern(ns));
    let query_body = kb.ambiguous_query_dispatch(qt).join("\n");

    assert_eq!(
        query_body, load_body,
        "one refusal, one message body — the query face must not drift from the load face",
    );
}

/// THE OTHER HALF OF THE TIE, and the one the refusal above does not cover: whatever
/// the query front door does, the RESOLVER must not answer the spec's default for a
/// call with two suppliers. Driven through `kb.resolve` directly, with no front door
/// in the way, because that is what every other resolver consumer sees.
///
/// Asserts NO definite answer rather than a specific empty shape: the resolver leaves
/// such a call un-reduced, the WI-938 hook then declines to `unify` the result column
/// with it, and what that produces is the pre-WI-938 outcome (no answer). What must
/// never come back is `Int(1)`.
#[test]
fn a_two_supplier_query_never_answers_the_default() {
    let ns = "test.wi1044.tierun";
    let src = two_suppliers_query_only(ns);
    let mut kb = crate::common::load_kb_with(&src);
    let answers = query_answers(&mut kb, &describe_pattern(ns));
    assert!(
        !answers
            .iter()
            .any(|(v, definite)| *definite && matches!(v, Value::Int(_))),
        "a two-supplier carrier must not produce a definite Int — the only one \
         reachable by folding is the spec's DEFAULT, which is the wrong answer this \
         ticket exists to stop: {answers:?}",
    );
}

/// THE PRECONDITION, pinned so the tests above keep measuring the population they
/// name: the query goal reaches resolution with NO typer stamp on it. This is what
/// makes it the WI-938 materialization path and not a pre-typed rule body — a query
/// term is a hash-consed `TermId` belonging to no rule, so `type_rule_bodies` never
/// walks it and the occurrence the hook builds out of it is fresh.
///
/// PASSES EITHER WAY by design. It asserts the SHAPE of the input, which this ticket
/// does not change; what it stops is a future stamp-at-conversion making the other
/// tests pass through a path they do not claim to exercise.
#[test]
fn the_query_goal_carries_no_typer_stamp() {
    use anthill_core::kb::node_occurrence::materialize_from_handle;
    let ns = "test.wi1044.unstamped";
    let src = one_supplier(ns, "");
    let mut kb = crate::common::load_kb_with(&src);
    let qt = query_term(&mut kb, &describe_pattern(ns));
    // The goal as the WI-938 hook first sees it — the same `materialize_from_handle`
    // that hook calls for a `Value::Term` goal.
    let occ = materialize_from_handle(&kb, qt);
    assert!(
        occ.classified_apply_target().is_none(),
        "the query goal must arrive unclassified; if a typer pass has started \
         stamping it, the tests above are exercising a different path",
    );
    // …and no rule heads this functor, so the hook is the ONLY route to an answer.
    let spec_op = kb
        .try_resolve_symbol(&format!("{ns}.Desc.describe"))
        .expect("the spec op must resolve");
    assert_eq!(
        kb.rules_by_functor(spec_op).len(),
        0,
        "a clause on the spec op would answer this goal without the hook, and the \
         measurement would be about that clause instead",
    );
}

/// THE STAMP MUST NOT OUTLIVE THE σ THAT PRODUCED IT — the one invariant this ticket
/// introduces and the only one nothing else in the tree states.
///
/// `classify_pin_or_apply_within` writes into a `RefCell` on a shared
/// `Rc<NodeOccurrence>`. Every previous writer of that stamp was the TYPER, whose
/// verdict is σ-independent, so "an occurrence is never classified under two different
/// substitutions" had never needed saying. A value-directed verdict IS σ-dependent: the
/// carrier comes from what the receiver is bound to. If one occurrence were reduced
/// under two σ binding the receiver to different carriers, the second reduction would
/// silently run the first carrier's implementation.
///
/// DRIVEN, in both shapes that reach the classification and in both fact orders, on a
/// program where the two carriers answer DIFFERENT numbers (`Leaf` → 7, `Twig` → 5):
///
///   * the GOAL shape, through the WI-938 hook — answers `[7, 5]`;
///   * the OPERAND shape, folded inside a `gt` — `gt(describe(?x), 6)` keeps exactly
///     ONE row of two, and `gt(…, 4)` keeps both. A stuck stamp would fold 7 for both
///     rows and `gt(…, 6)` would keep two.
///
/// Both hold because each activation gets its OWN occurrence: the goal hook builds a
/// fresh `rebuilt_expr` per attempt, and a rule body is opened through
/// `with_fresh_vars` / `body_rename`, which substitute rather than share. That is the
/// invariant — stated here because it is load-bearing and not obvious, and asserted
/// here because a change to either opener would break it silently everywhere else.
///
/// Both fact orders are driven deliberately: with one order a stuck stamp could still
/// produce the right count by luck (if the sticky carrier happens to be the one the
/// threshold admits), and the reversed order is what removes that coincidence.
#[test]
fn a_backtracked_receiver_reclassifies_per_carrier() {
    let program = |first: &str, second: &str, tail: &str| {
        format!(
            r#"namespace test.wi1044.bt
  import anthill.prelude.Int64
  -- WI-20260825-KD9SW: a WRITTEN bare `gt` names its operation by import.
  import anthill.prelude.PartialOrd.{{gt}}

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Leaf
    entity leaf
  end

  sort Twig
    entity twig
  end

  operation leafDescribe(x: Leaf) -> Int64 = 7
  operation twigDescribe(x: Twig) -> Int64 = 5

  fact Desc[T = Leaf, describe = leafDescribe]
  fact Desc[T = Twig, describe = twigDescribe]

  fact pick({first}())
  fact pick({second}())

{tail}end
"#
        )
    };
    let definite = |first: &str, second: &str, tail: &str| -> Vec<Value> {
        let src = program(first, second, tail);
        let mut kb = crate::common::load_kb_with(&src);
        crate::common::query_unary(&mut kb, "test.wi1044.bt.answer")
            .into_iter()
            .filter(|(_, d)| *d)
            .map(|(v, _)| v)
            .collect()
    };

    // THE GOAL SHAPE. Two carriers, two different supplied answers, one rule body.
    // The answers are compared as a SORTED SET: which order the two rows come back in
    // is the resolver's clause-selection business and not this test's subject —
    // asserting it would couple this to that (measured: `[5, 7]` for the `leaf`-first
    // fixture, so the order is not the fact order and pinning it would be pinning an
    // accident). What must hold is that BOTH suppliers are reached, which a stuck
    // stamp makes impossible: it would answer one number twice.
    for (first, second) in [("leaf", "twig"), ("twig", "leaf")] {
        let got = definite(
            first,
            second,
            "  rule answer(?r) :- pick(?x), Desc.describe(?x, ?r)\n",
        );
        let mut ints: Vec<i64> = got
            .iter()
            .filter_map(|v| match v {
                Value::Int(i) => Some(*i),
                _ => None,
            })
            .collect();
        ints.sort();
        assert_eq!(
            ints,
            vec![5, 7],
            "each activation must reclassify from ITS OWN receiver ({first} first)",
        );
    }

    // THE OPERAND SHAPE, where the call is folded inside a builtin rather than
    // decided by the hook. The threshold separates the two carriers, so a stamp that
    // survived backtracking would show up as a COUNT.
    let gt = |n: i32| format!("  rule answer(?r) :- pick(?r), gt(Desc.describe(?r), {n})\n");
    for (first, second) in [("leaf", "twig"), ("twig", "leaf")] {
        assert_eq!(
            definite(first, second, &gt(6)).len(),
            1,
            "only `Leaf` supplies a 7 > 6; a stamp stuck to the first carrier would \
             fold 7 for both rows and keep two ({first} first)",
        );
        assert_eq!(
            definite(first, second, &gt(4)).len(),
            2,
            "…and the same fixture keeps BOTH rows at a threshold under 5, so the row \
             above is a real filter and not an unrelated failure ({first} first)",
        );
    }
}

/// THE CONTROL THE REFUSAL MUST NOT CONSUME: a carrier with NO supplier still runs the
/// spec's default at a query, exactly as it does in a rule body
/// (`wi1026::a_carrier_with_no_supplier_still_runs_the_default_in_a_rule_body`). This
/// is every defaulted spec-op call in the tree, and it is what makes a default a
/// default (WI-1010: defaults fill GAPS, they do not SHADOW).
///
/// PASSES EITHER WAY by design — `NoSupplier` is the verdict that leaves the fold
/// alone, so backing the classification out cannot move it.
#[test]
fn a_carrier_with_no_supplier_still_runs_the_default_at_a_query() {
    let ns = "test.wi1044.gap";
    let src = program(ns, "    provides Desc[T = Leaf]\n", "", "");
    let mut kb = crate::common::load_kb_with(&src);
    assert_eq!(
        query_int(&mut kb, &describe_pattern(ns)),
        1,
        "no supplier — the spec's default must still run at a query",
    );
}

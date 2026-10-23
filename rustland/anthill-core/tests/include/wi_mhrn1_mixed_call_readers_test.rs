//! WI-20260930-MHRN1 — A RULE-BODY CALL'S ARGUMENTS ARE READ BY THE PARAMETER THEY BIND.
//!
//! In a MIXED call positional arguments rank among the parameters the labels left open
//! (`positional_param_indices`), so the one at index `i` need not be bound to parameter `i`:
//! `sub2(5, x: 1)` over `(x, y)` is `x := 1, y := 5`. WI-20260929-0RP29 moved the readers of
//! a TYPED call to that ranking (`bound_arg`). A rule body's calls are mostly not reordered
//! by a typer, and five readers of one still paired by index:
//!
//!  1. the resolver's reduction of the call (`reduce_op_value`) — "positional `i`, else the
//!     label", so the positional argument took the labelled parameter too, another was left
//!     with nothing, and the call stayed un-reduced: a conditional residual, a constraint
//!     guard that never fired;
//!  2. the resolver's by-value classification of a call no typer saw
//!     (`classify_unstamped_spec_op_call`), which read "positional `i`, else the parameter's
//!     own symbol" and so found no labelled argument at all: a query's call with a label
//!     ran the spec's default;
//!  3. the typer's positionalizer (`align_call_args_to_params`), behind the conditions a
//!     clause is given for its calls — it aligned nothing, so the call was given no
//!     condition and the caller's dictionary never reached it;
//!  4. the pre-pass that types a rule's variables from the calls they are passed to
//!     (`constrain_application`) — a variable took the type of the parameter at its index;
//!  5. the value typer's receiver of a self-returning spec operation
//!     (`self_return_spec_op_result_type`).
//!
//! All five ask one owner now (`bound_arg` / `bound_args`). And the reduction reads a label
//! against the operation the call NAMES, not against the member a carrier supplies for it,
//! which may spell its parameters otherwise.
//!
//! A RESULT COLUMN BELONGS TO THE ALL-POSITIONAL SPELLING. A goal written at arity + 1 is
//! the functional-relation view, its last positional argument the result (kernel §5.3:
//! "named arguments are not this shape"; proposal 069 §1.1 gives a labelled goal its result
//! by the name `result:`). So a goal with a label and one positional argument more than the
//! labels leave open is over-applied. A spec operation's goal was refused for it at load; a
//! plain operation's loaded and answered nothing, as did one written past arity + 1 or short
//! of its arity. All are refused now, by one verdict (`operation_goal_arity_error`, raised by
//! the pass that refuses a goal with no reading).
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! MEASURED 2026-10-12, each part restored to what it read before, the others in place:
//!
//! 1. `reduce_op_value` reading "positional `i`, else the label". 8 FAIL:
//!    [`a_mixed_call_runs_in_a_rule_body`],
//!    [`a_mixed_call_decides_a_constraint_guard_and_a_negation`],
//!    [`a_labelled_call_with_a_positional_argument_left_over_does_not_run`], both dictionary
//!    rows, and three whose mixed call must run for the row to answer at all:
//!    [`a_query_s_mixed_call_reaches_the_supplied_member`],
//!    [`a_rule_variable_is_typed_by_the_parameter_it_fills`] and
//!    [`a_label_is_read_against_the_operation_the_call_names`].
//! 2. `classify_unstamped_spec_op_call` reading by index and by the parameter's own symbol.
//!    2 FAIL: [`a_query_s_mixed_call_reaches_the_supplied_member`] — it answers the spec's
//!    default — and the query half of [`a_label_is_read_against_the_operation_the_call_names`].
//! 3. The reduction's labels read against the supplying member's parameter names. 1 FAILS:
//!    [`a_label_is_read_against_the_operation_the_call_names`].
//! 4. `align_call_args_to_params` by index. 2 FAIL:
//!    [`a_mixed_bool_view_call_answers_through_the_callers_dictionary`] and
//!    [`a_mixed_value_slot_call_takes_the_callers_dictionary`].
//! 5. `constrain_application` by index. 1 FAILS:
//!    [`a_rule_variable_is_typed_by_the_parameter_it_fills`].
//! 6. `self_return_spec_op_result_type` by index. 1 FAILS:
//!    [`a_law_over_a_receiver_passed_by_label_fires`].
//! 7. The rule-less operation's goal left unjudged (`operation_goal_arity_error` not asked).
//!    1 FAILS: [`a_labelled_goal_with_a_result_column_is_refused`].
//!
//! THREE ROWS PASS UNDER EVERY BACK-OUT, BY DESIGN.
//! [`the_spellings_that_ranked_alike_are_unchanged`]: a call with no label, with every
//! argument labelled, or with its labels last ranks each positional argument to the index
//! it is written at. [`a_mixed_spec_operation_call_is_a_written_requirements_witness`]: a
//! SPEC operation's call is typed where it stands, and the typer stores a mixed one with
//! its arguments in parameter order, so the positionalizer is handed a positional call.
//! What reaches it mixed is an ORDINARY operation's call, which a rule body only
//! name-checks — the two dictionary rows. [`the_goals_with_a_reading_still_load`]: what the
//! new refusal must leave alone.

use anthill_core::eval::Value;
use anthill_core::kb::term::Term;
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

/// Two rival `Ord[Int64]` beside `Int64`'s own, so `compare(1, 5)` has three answers
/// (`Descending` 4, `Ascending` -4, `Int64`'s own -1); `Util`'s operations over two and
/// three parameters; and a spec with a carrier that supplies it.
const PRELUDE: &str = r#"
  import anthill.prelude.{Int64, Bool, Error, EmptyStream, Relation, Ord, WeakOrd, PartialOrd, PartialEq, Eq}

  sort Ascending
    import anthill.prelude.Numeric.{sub}
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(a, b)
  end

  sort Descending
    import anthill.prelude.Numeric.{sub}
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)
  end

  -- body-less, one parameter: a call at a carrier that provides none is refused at load
  sort Tag
    sort T = ?
    operation tag(x: T) -> Int64
  end

  -- DEFAULTED, two parameters: the default answers 1, the carrier's own member `k + 7`
  sort Desc
    sort T = ?
    operation describe(x: T, k: Int64) -> Int64 = 1
  end

  sort Leaf
    entity leaf
    provides Tag[T = Leaf]
    operation tag(x: Leaf) -> Int64 = 7
    provides Desc[T = Leaf]
    operation describe(x: Leaf, k: Int64) -> Int64 = Int64.add(k, 7)
  end

  -- a carrier whose member spells the parameters otherwise: `k + 20`
  sort Twig
    entity twig
    provides Desc[T = Twig]
    operation describe(item: Twig, n: Int64) -> Int64 = Int64.add(n, 20)
  end

  sort Util
    operation sign[A](x: A, y: A) -> Int64 requires WeakOrd[T = A] = WeakOrd.compare(x, y)
    operation isLess[A](x: A, y: A) -> Bool requires WeakOrd[T = A] =
      Int64.lt(WeakOrd.compare(x, y), 0)
    operation sub2(x: Int64, y: Int64) -> Int64 = Int64.sub(x, y)
    operation lt2(x: Int64, y: Int64) -> Bool = Int64.lt(x, y)
    operation three(a: Int64, b: Int64, c: Int64) -> Int64 =
      Int64.sub(Int64.mul(a, 100), Int64.add(Int64.mul(b, 10), c))
    operation ok(k: Int64, l: Leaf) -> Bool = true
  end

  fact holds(leaf())
  fact num(n: 3)
"#;

fn program(ns: &str, body: &str) -> String {
    format!("namespace {ns}\n{PRELUDE}\n{body}end\n")
}

fn one(kb: &mut KnowledgeBase, qn: &str) -> Option<i64> {
    crate::common::one_definite_int(kb, qn)
}

fn load_errors(ns: &str, body: &str) -> String {
    crate::common::try_load_kb_with(&program(ns, body))
        .err()
        .unwrap_or_else(|| panic!("expected a load refusal; it loaded clean:\n{body}"))
        .join("\n")
}

// ── 1. The resolver's reduction ─────────────────────────────────────────────

/// A mixed call RUNS in a rule body, in a value slot and as a `Bool` operation's goal, and
/// binds the arguments its operation-body twin binds: `x := 1, y := 5`, and over three
/// parameters `a := 3, b := 1, c := 2`. Each was one conditional row with the call left
/// standing (`unify(?_, sub2(5, x: 1))`).
#[test]
fn a_mixed_call_runs_in_a_rule_body() {
    let mut kb = crate::common::load_kb_with(&program(
        "wimhrn1.runs",
        "  rule value(?c) :- ?c <=> Util.sub2(5, x: 1)\n  \
         rule goal(?c) :- Util.lt2(5, x: 1), ?c <=> 1\n  \
         rule ofThree(?c) :- ?c <=> Util.three(1, 2, a: 3)\n  \
         operation inBody() -> Int64 = Util.three(1, 2, a: 3)\n  \
         rule body(?c) :- ?c <=> inBody()\n",
    ));
    assert_eq!(one(&mut kb, "wimhrn1.runs.value"), Some(-4), "`sub2(x: 1, y: 5)`");
    assert_eq!(one(&mut kb, "wimhrn1.runs.goal"), Some(1), "`lt2(x: 1, y: 5)` holds");
    assert_eq!(one(&mut kb, "wimhrn1.runs.ofThree"), Some(288), "`three(a: 3, b: 1, c: 2)`");
    assert_eq!(one(&mut kb, "wimhrn1.runs.body"), Some(288), "as the operation body reads it");
}

/// CONTROL — passes with every part backed out, BY DESIGN. A call with no label, with every
/// argument labelled, or with its labels last ranks each positional argument to its own
/// index, so the index read and the ranking agree on it.
#[test]
fn the_spellings_that_ranked_alike_are_unchanged() {
    let mut kb = crate::common::load_kb_with(&program(
        "wimhrn1.alike",
        "  rule positional(?c) :- ?c <=> Util.sub2(1, 5)\n  \
         rule named(?c) :- ?c <=> Util.sub2(y: 5, x: 1)\n  \
         rule trailing(?c) :- ?c <=> Util.sub2(1, y: 5)\n  \
         rule relational(?c) :- Util.sub2(1, 5, ?c)\n  \
         rule condition(?c) :- Util.lt2(x: 1, y: 5), ?c <=> 1\n",
    ));
    for (rule, want) in [
        ("positional", -4),
        ("named", -4),
        ("trailing", -4),
        ("relational", -4),
        ("condition", 1),
    ] {
        assert_eq!(one(&mut kb, &format!("wimhrn1.alike.{rule}")), Some(want), "{rule}");
    }
}

/// The sites where the un-reduced call was WRONG rather than conditional. A constraint's
/// guard that never decides never fires: `no ?n: num(n: ?n) -: Util.lt2(5, x: ?n)` over
/// `num(n: 3)` — `lt2(x: 3, y: 5)` holds, a violation — loaded clean. And a negation over
/// the call was left standing where it decides.
#[test]
fn a_mixed_call_decides_a_constraint_guard_and_a_negation() {
    let errs = load_errors(
        "wimhrn1.guard",
        "  constraint small: no ?n: num(n: ?n) -: Util.lt2(5, x: ?n)\n",
    );
    assert!(errs.contains("small"), "the constraint is violated by `num(n: 3)`: {errs}");
    let mut kb = crate::common::load_kb_with(&program(
        "wimhrn1.negated",
        "  constraint large: no ?n: num(n: ?n) -: Util.lt2(1, x: ?n)\n  \
         rule holds5(?c) :- not(Util.lt2(1, x: 5)), ?c <=> 1\n  \
         rule fails5(?c) :- not(Util.lt2(5, x: 1)), ?c <=> 1\n",
    ));
    assert_eq!(one(&mut kb, "wimhrn1.negated.holds5"), Some(1), "`lt2(x: 5, y: 1)` is false");
    let rows = crate::common::query_unary(&mut kb, "wimhrn1.negated.fails5");
    assert!(rows.is_empty(), "`lt2(x: 1, y: 5)` holds, so its negation fails: {rows:?}");
}

/// A LABEL NAMES A PARAMETER OF THE OPERATION THE CALL IS WRITTEN ON, whatever the member
/// that answers it calls its own. `Twig`'s `describe(item, n)` supplies
/// `Desc.describe(x, k)`: the call's `x:` and `k:` are read against `Desc.describe`, and
/// the arguments handed to the member one for one. Read against the member's names no
/// label named anything, and the call was left standing — in the rule body, where the
/// typer keeps an all-labelled call's labels, and in a query.
#[test]
fn a_label_is_read_against_the_operation_the_call_names() {
    let ns = "wimhrn1.renamed";
    let mut kb = crate::common::load_kb_with(&program(
        ns,
        "  rule inRule(?r) :- ?r <=> Desc.describe(k: 1, x: twig())\n  \
         operation inBody() -> Int64 = Desc.describe(k: 1, x: twig())\n  \
         rule viaBody(?r) :- ?r <=> inBody()\n",
    ));
    assert_eq!(one(&mut kb, &format!("{ns}.viaBody")), Some(21), "the operation body's answer");
    assert_eq!(one(&mut kb, &format!("{ns}.inRule")), Some(21), "`Twig`'s own `describe`");
    for call in [
        format!("{ns}.Desc.describe(k: 1, x: {ns}.Twig.twig())"),
        format!("{ns}.Desc.describe(1, x: {ns}.Twig.twig())"),
    ] {
        let rows = query_first(&mut kb, &format!("?r <=> {call}"));
        assert!(
            matches!(rows.as_slice(), [(v, true)] if crate::common::scalar_int(&kb, v) == Some(21)),
            "`{call}` is `Twig`'s own `describe`, `1 + 20`; got {rows:?}",
        );
    }
}

/// A LABELLED call with a positional argument no parameter takes is not run with one of its
/// arguments dropped. `sub2(1, 9, y: 5)` has one parameter open and two positional
/// arguments: read by index it ran as `sub2(1, 9)` — the label lost to the positional
/// argument at its parameter's index — and answered `-8`, definitely. Written in a clause it
/// is refused at load, as in an operation body (WI-20261013-R1W5A); asked as a goal built at
/// run time, which no typer sees, it is left standing.
#[test]
fn a_labelled_call_with_a_positional_argument_left_over_does_not_run() {
    let errs = crate::common::load_errors_of(&program(
        "wimhrn1.surplusw",
        "  rule leftOver(?c) :- ?c <=> Util.sub2(1, 9, y: 5)\n",
    ));
    crate::common::assert_refused_naming(
        &errs,
        &["sub2.arity", "2 positional arguments for the 1 parameter no label names"],
        "the written call",
    );
    let mut kb = crate::common::load_kb_with(&program("wimhrn1.surplus", ""));
    let rows = query_first(&mut kb, "?c <=> wimhrn1.surplus.Util.sub2(1, 9, y: 5)");
    assert!(
        matches!(rows.as_slice(), [(_, false)]),
        "one undecided row, the call un-reduced; got {rows:?}",
    );
}

// ── 2. The by-value classification of a call no typer saw ────────────────────

/// The first positional argument of a top-level query `pattern`, in every answer.
fn query_first(kb: &mut KnowledgeBase, pattern: &str) -> Vec<(Value, bool)> {
    use anthill_core::kb::resolve::ResolveConfig;
    use anthill_core::kb::term_view::TermView;
    let goal = crate::common::query_pattern_term(kb, pattern);
    let var = TermView::pos_arg(&goal, kb, 0)
        .unwrap_or_else(|| panic!("`{pattern}` has no first argument"))
        .to_value();
    kb.resolve(&[goal], &ResolveConfig::default())
        .iter()
        .map(|sol| (kb.reify_value(&var, &sol.subst), sol.is_definite()))
        .collect()
}

/// A top-level QUERY is typed by nothing, so its call on a defaulted spec operation is
/// classified by the value of its carrier argument — the one bound to the carrier
/// parameter, by position or by its label. That read took "positional `i`, else the
/// argument stored under the parameter's own symbol", and a WRITTEN label is the bare name:
/// so with a label anywhere the carrier was not found, the call was left unclassified, and
/// the spec's DEFAULT ran. `describe(k: 1, x: leaf())` and `describe(leaf(), k: 1)` answered
/// `1`, definitely; `describe(1, x: leaf())` was left standing by the reduction. All answer
/// `8` now, as the positional spelling always did.
#[test]
fn a_query_s_mixed_call_reaches_the_supplied_member() {
    let ns = "wimhrn1.query";
    let mut kb = crate::common::load_kb_with(&program(ns, ""));
    for call in [
        format!("{ns}.Desc.describe({ns}.Leaf.leaf(), 1)"),
        format!("{ns}.Desc.describe(k: 1, x: {ns}.Leaf.leaf())"),
        format!("{ns}.Desc.describe({ns}.Leaf.leaf(), k: 1)"),
        format!("{ns}.Desc.describe(1, x: {ns}.Leaf.leaf())"),
    ] {
        let rows = query_first(&mut kb, &format!("?r <=> {call}"));
        assert!(
            matches!(rows.as_slice(), [(v, true)] if crate::common::scalar_int(&kb, v) == Some(8)),
            "`{call}` is `Leaf`'s own `describe`, `1 + 7`; got {rows:?}",
        );
    }
}

// ── 3. The positionalizer ───────────────────────────────────────────────────

fn drive_bool(src: &str, entry: &str) -> bool {
    let mut interp = crate::common::interp_for(src);
    match interp.call(entry, &[]) {
        Ok(Value::Bool(b)) => b,
        other => panic!("{entry}: expected a Bool, got {other:?}"),
    }
}

fn drive_int(src: &str, entry: &str) -> i64 {
    let mut interp = crate::common::interp_for(src);
    match interp.call(entry, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{entry}: expected an Int64, got {other:?}"),
    }
}

/// WI-20260925-P7VP4's Bool-view row, the call spelled mixed. `isLess`'s own
/// `requires WeakOrd[T = A]` is a condition of `less`, filled by the rival `citeLess`'s
/// caller chose: under `Descending` `compare(1, 5)` is `4`, so `less(1, 5)` is empty; under
/// `Ascending` it holds. Aligned by index the call got no condition and derived `Int64`'s
/// own `-1` under both.
#[test]
fn a_mixed_bool_view_call_answers_through_the_callers_dictionary() {
    let src = program(
        "wimhrn1.boolview",
        "  rule less(?a, ?b) :- Util.isLess(?b, x: ?a)\n  \
         sort Driver\n    \
         operation citeLess[A](x: A, y: A) -> Bool effects {Error, Error[EmptyStream]}\n      \
         requires WeakOrd[T = A] =\n      \
         let r = less(x, y)\n      \
         r.isEmpty\n    \
         operation lessDesc() -> Bool effects {Error, Error[EmptyStream]} =\n      \
         citeLess[A = Int64, WeakOrd = Descending](1, 5)\n    \
         operation lessAsc() -> Bool effects {Error, Error[EmptyStream]} =\n      \
         citeLess[A = Int64, WeakOrd = Ascending](1, 5)\n  \
         end\n",
    );
    assert!(
        drive_bool(&src, "wimhrn1.boolview.Driver.lessDesc"),
        "`Descending`: 1 is not less than 5, so `less(1, 5)` is empty",
    );
    assert!(
        !drive_bool(&src, "wimhrn1.boolview.Driver.lessAsc"),
        "`Ascending`: it is, so `less(1, 5)` holds",
    );
}

/// WI-20260925-P7VP4's slot program, the call spelled mixed in a value slot: `sign`'s
/// `requires` is `viaOp`'s condition and the caller's rival fills it. Aligned by index:
/// `-1` both ways, the slot derived from `1`'s type.
#[test]
fn a_mixed_value_slot_call_takes_the_callers_dictionary() {
    let src = program(
        "wimhrn1.slots",
        "  rule viaOp(?a, ?b, ?c) :- ?c <=> Util.sign(?b, x: ?a)\n  \
         sort Driver\n    \
         operation cite[A](x: A, y: A) -> Int64 effects {Error, Error[EmptyStream]}\n      \
         requires WeakOrd[T = A] = viaOp(x, y).head.c\n    \
         operation desc() -> Int64 effects {Error, Error[EmptyStream]} =\n      \
         cite[A = Int64, WeakOrd = Descending](1, 5)\n    \
         operation asc() -> Int64 effects {Error, Error[EmptyStream]} =\n      \
         cite[A = Int64, WeakOrd = Ascending](1, 5)\n  \
         end\n",
    );
    assert_eq!(
        (
            drive_int(&src, "wimhrn1.slots.Driver.desc"),
            drive_int(&src, "wimhrn1.slots.Driver.asc"),
        ),
        (4, -4),
        "`sign(x: 1, y: 5)` through the rival the CALLER chose",
    );
}

/// CONTROL — passes with every part backed out, BY DESIGN. A mixed call on a SPEC operation
/// is the witness of a written `require`, its labelled carrier argument grounding the
/// instance: the typer has put the call's arguments in parameter order by the time the
/// witness is read, so no reader here sees it mixed. It pins the answer, `Leaf`'s own member.
#[test]
fn a_mixed_spec_operation_call_is_a_written_requirements_witness() {
    let mut kb = crate::common::load_kb_with(&program(
        "wimhrn1.witness",
        "  rule answer(?r) :- ?d = require[Desc], holds(?x), ?r <=> Desc.describe(1, x: ?x)\n",
    ));
    assert_eq!(one(&mut kb, "wimhrn1.witness.answer"), Some(8), "`Leaf`'s own `describe`");
}

// ── 4. A rule variable's type ───────────────────────────────────────────────

/// `?l` is passed to `ok`'s parameter `l: Leaf` — the one the label `k:` leaves open — and
/// is typed by it. By index it was typed `Int64`, `k`'s type, and the clause was refused at
/// `Tag.tag(?l, ?c)`: "`Int64` provides no `Tag`", a carrier the clause never had.
#[test]
fn a_rule_variable_is_typed_by_the_parameter_it_fills() {
    let mut kb = crate::common::load_kb_with(&program(
        "wimhrn1.vartype",
        "  rule tagged(?c) :- holds(?l), Util.ok(?l, k: 1), Tag.tag(?l, ?c)\n",
    ));
    assert_eq!(one(&mut kb, "wimhrn1.vartype.tagged"), Some(7), "`Leaf`'s own `tag`");
}

// ── 5. The value typer's receiver ───────────────────────────────────────────

/// WI-611's fixture with the law written over a receiver passed BY LABEL:
/// `member(?x, insert(?x, s: ?s))`.
const BAG: &str = r#"
namespace wimhrn1.bag
  import anthill.prelude.{Int64, Bool, Eq}
  import wimhrn1.bag.Bag.{member, insert}

  sort Bag
    sort T = ?
    requires Eq[T]
    operation {
      insert(s: Self, x: T) -> Self
      member(x: T, s: Self) -> Bool
    }
    rule {
      member_insert: member(?x, insert(?x, s: ?s)) <=> true @[simp]
    }
  end

  sort IntBag
    entity ibag
    provides Bag[T = Int64]
    operation insert(s: IntBag, x: Int64) -> IntBag = s
    operation member(x: Int64, s: IntBag) -> Bool = true
  end
end
"#;

/// The label the law's own `insert(?x, s: ?s)` pattern is stored with, so the redex below
/// is the term the pattern matches.
fn law_receiver_label(kb: &KnowledgeBase, insert: anthill_core::intern::Symbol) -> anthill_core::intern::Symbol {
    for rid in kb.live_rule_ids() {
        let Some(head) = kb.fact_head_term(rid) else { continue };
        let Term::Fn { pos_args, .. } = kb.get_term(head) else { continue };
        let Some(Term::Fn { pos_args: lhs_args, .. }) = pos_args.first().map(|l| kb.get_term(*l)) else {
            continue;
        };
        for arg in lhs_args.iter() {
            if let Term::Fn { functor, named_args, .. } = kb.get_term(*arg) {
                if *functor == insert {
                    if let Some((label, _)) = named_args.first() {
                        return *label;
                    }
                }
            }
        }
    }
    panic!("no law holds an `insert(…, s: …)` pattern");
}

/// A self-returning spec operation's result is its RECEIVER's carrier, and the receiver is
/// the argument bound to the receiver parameter: in `insert(5, s: ibag())` the labelled one.
/// So the subterm types as `IntBag`, `member`'s carrier argument provides `Bag`, and the law
/// fires. Read by index the receiver was `5`: `Int64` provides no `Bag`, the subterm kept
/// the abstract return, and the guard suspended — the redex stood.
#[test]
fn a_law_over_a_receiver_passed_by_label_fires() {
    let mut kb = crate::common::load_kb_with(BAG);
    let sym = |kb: &KnowledgeBase, qn: &str| {
        kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("resolve {qn}"))
    };
    let member = sym(&kb, "wimhrn1.bag.Bag.member");
    let insert = sym(&kb, "wimhrn1.bag.Bag.insert");
    let ibag_sym = sym(&kb, "wimhrn1.bag.IntBag.ibag");
    let label = law_receiver_label(&kb, insert);
    let ibag = kb.alloc(Term::Fn {
        functor: ibag_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    let five = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(5)));
    let ins = kb.alloc(Term::Fn {
        functor: insert,
        pos_args: SmallVec::from_slice(&[five]),
        named_args: SmallVec::from_slice(&[(label, ibag)]),
    });
    let term = kb.alloc(Term::Fn {
        functor: member,
        pos_args: SmallVec::from_slice(&[five, ins]),
        named_args: SmallVec::new(),
    });
    let result = kb.simplify(term);
    assert!(
        result != term
            && !matches!(kb.get_term(result), Term::Fn { functor, .. } if *functor == member),
        "`member(5, insert(5, s: ibag()))` rewrites away: got {:?}",
        kb.get_term(result),
    );
}

// ── 6. A result column belongs to the all-positional spelling ───────────────

/// A goal with a label and one positional argument more than the labels leave open is not
/// the functional-relation view, on a plain operation as on a spec operation: both are
/// refused at load, and told why. The plain one loaded and answered nothing. A goal past
/// arity + 1, one short of its arity, and a label that names no parameter are the same
/// verdict's — and it is given wherever a goal is proved: in a `|` branch and in a
/// quantifier's body too.
#[test]
fn a_labelled_goal_with_a_result_column_is_refused() {
    let no_label = "only where the call writes no label";
    for (ns, goal, callee, open) in [
        ("wimhrn1.plainlead", "Util.sign(?b, ?c, x: ?a)", "sign.arity", "(`y`)"),
        ("wimhrn1.plaintrail", "Util.sign(?a, ?c, y: ?b)", "sign.arity", "(`x`)"),
        ("wimhrn1.plainall", "Util.sign(?c, x: ?a, y: ?b)", "sign.arity", "0 parameters"),
        ("wimhrn1.spec", "Desc.describe(?a, ?c, k: ?b)", "describe.arity", "(`x`)"),
        ("wimhrn1.branch", "(Util.sign(?b, ?c, x: ?a) | ?c <=> 3)", "sign.arity", "(`y`)"),
    ] {
        let errs = load_errors(ns, &format!("  rule r(?a, ?b, ?c) :- {goal}\n"));
        assert!(
            errs.contains(callee)
                && errs.contains("got 3 arguments")
                && errs.contains(open)
                && errs.contains(no_label)
                && !errs.contains("no argument fills"),
            "`{goal}`: {errs}",
        );
    }
    for (ns, goal, got) in [
        ("wimhrn1.twoover", "Util.sub2(1, 5, ?c, ?c)", "got 4 arguments"),
        ("wimhrn1.short", "Util.lt2(1), ?c <=> 1", "no argument fills parameter `y`"),
        ("wimhrn1.scope", "(forall ?e in [1, 2]: Util.lt2(?e, 5, 7, 8)), ?c <=> 1", "got 4 arguments"),
        ("wimhrn1.bogus", "Util.lt2(5, bogus: 1), ?c <=> 1", "names no parameter"),
    ] {
        let errs = load_errors(ns, &format!("  rule r(?c) :- {goal}\n"));
        assert!(errs.contains(got) && !errs.contains(no_label), "`{goal}`: {errs}");
    }
}

/// CONTROL — passes with the verdict backed out, BY DESIGN. What it must not refuse: a
/// goal at arity + 1 written without a label, a `Bool` operation's goal with its labels
/// whole, and a goal on an operation its own clauses define, whatever shape they have.
#[test]
fn the_goals_with_a_reading_still_load() {
    let mut kb = crate::common::load_kb_with(&program(
        "wimhrn1.readable",
        "  sort Box\n    \
         entity mk(v: Int64)\n    \
         operation wide(b: Box, k: Int64) -> Int64\n    \
         rule wide(mk(v: ?v), ?k, ?r, extra: ?e) :- ?e <=> 0, ?r <=> ?v\n  \
         end\n  \
         rule relational(?c) :- Util.sub2(1, 5, ?c)\n  \
         rule condition(?c) :- Util.lt2(y: 5, x: 1), ?c <=> 1\n  \
         rule clauses(?c) :- Box.wide(Box.mk(4), 1, ?c, extra: ?)\n",
    ));
    assert_eq!(one(&mut kb, "wimhrn1.readable.relational"), Some(-4));
    assert_eq!(one(&mut kb, "wimhrn1.readable.condition"), Some(1));
    assert_eq!(one(&mut kb, "wimhrn1.readable.clauses"), Some(4));
}

//! WI-20260925-P7VP4 — a rule-body call's requirement is a CONDITION OF THE CLAUSE
//! (`docs/design/requirement-channel.md` §5, "The call site drives it; `require[X]` is only
//! the explicit form"). Decided by the user, 2026-09-25: the typer INFERS the condition the
//! author could have written, rather than refusing the clause until they write it.
//!
//! ## Increment 1 — a call to a spec operation whose carrier is not known at load
//!
//! `rule cmp(?a, ?b, ?c) :- WeakOrd.compare(?a, ?b, ?c)` writes no `require`. Its call gets
//! the read `find_dictionary(WeakOrd, WeakOrd.compare, ?a, ?b, out: ?d)` before it and
//! dispatches through `?d`, so a citation routes the CALLER's dictionary to it exactly as it
//! routes a written `require[WeakOrd[T]]` (060-implementation §7.3, S2) — and a clause no
//! caller hands one to derives its own from the value, as value-directed dispatch did.
//!
//! ## Increment 4 — an ordinary operation's own `requires`
//!
//! `rule viaOp(?a, ?b, ?c) :- Util.sign(?a, ?b, ?c)` calls an operation that `requires
//! WeakOrd[T = A]` and writes nothing. The call gets one condition per slot of `sign`'s
//! dictionary chain — `find_dictionary(WeakOrd, Util.sign, ?a, ?b, slot: 0, out: ?d)` — and
//! carries them. A citation fills the slot from its caller; a slot nobody fills stays
//! unbound and the bridge derives it from the values, as it did before.
//!
//! ## Back-out
//!
//! Remove the `infer_rule_body_requirements(kb)` call in `type_check_sorts_collect`: both
//! CASE rows fail — both selections answer `-1`, `Int64`'s own `compare`, because the
//! caller's dictionary stays in the caller's frame and the call dispatches on its value.
//! Remove the router's slot branch (`slot_read_index` in `route_requirement_read`): the SLOT
//! case row fails, and only it. Remove the bridge's use of a supplied slot
//! (`BridgeSlot::Supplied` — `resolve_bridge_requirements_supplied` handed none): EIGHT rows
//! fail, every one whose caller fills a slot — the SLOT case row, the two Bool-view rows,
//! `a_slot_routes_whichever_parameter_pins_it`, `a_subtype_argument_does_not_block_a_slot_-
//! route`, `a_supplied_slot_is_not_re_derived`, `a_negated_partly_routed_citation_decides` and
//! `a_woven_slot_call_that_waits_keeps_its_slots` (measured, WI-20260925-YNCY3). The router's
//! two measured choices — pin the CALLEE's parameters first, and keep a variable when substituting —
//! each failed the same row the same way (`-1, -1`) before they were made. Remove
//! `check_rule_body_operation_requires`' reading of a WOVEN call, or look the inference
//! pass up through `try_resolve_symbol` in `is_inferred_requirement_read` (where it is never
//! found, so every inferred read counts as the author's declaration), and the UNFILLABLE
//! row fails — the call loads clean. Make `arg_type_unknown_at_load` read only the stamp
//! and the KNOWN-ARGUMENTS row fails (`rich()` carries none, so its call is woven).
//! Remove `type_rule_bodies`' skip of a woven body and the SECOND-PHASE row fails — the
//! next load re-types the woven call and refuses it as a post-elaboration form. Remove the
//! pass's `has_equational_head` exclusion and the EQUATION row fails — stdlib's inert
//! `rule isEmpty(?s) <=> eq(length(?s), 0)` gets a read and a woven call. The CONTROL rows
//! pass either way by design, and each says why at its site.

use std::rc::Rc;

use anthill_core::eval::Value;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::node_occurrence::{for_each_child, Expr, NodeOccurrence};
use anthill_core::parse;

/// WI-870's pair of opposite `Ord[Int64]` rivals beside `Int64`'s own provision, so the
/// three answers to `compare(1, 5)` differ: `Descending` gives `4`, `Ascending` `-4`, and
/// `Int64`'s own `-1` (the fixture of `wi_5g28a_rule_dictionary_test`, with its rules'
/// `require`s DELETED — the whole point).
const ORD_PROGRAM: &str = r#"
namespace wip7vp4.ord
  import anthill.prelude.{Int64, Error, EmptyStream, Relation, Ord, WeakOrd, PartialOrd, PartialEq, Eq}

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

  -- the rule WRITES NOTHING: its call's requirement is the clause's condition
  rule cmp(?a, ?b, ?c) :- WeakOrd.compare(?a, ?b, ?c)
  -- a query-shaped caller of it: a rule goal hands `cmp` no dictionary
  rule cmpOne(?c) :- cmp(1, 5, ?c)

  -- the call at a CONCRETE carrier: decided at load, by the carrier
  rule cmpInt(?c) :- WeakOrd.compare(1, 5, ?c)

  sort Driver
    operation viaRule[A](x: A, y: A) -> Int64 effects {Error, Error[EmptyStream]}
      requires WeakOrd[T = A] = cmp(x, y).head.c
    operation viaInt[A](x: A) -> Int64 effects {Error, Error[EmptyStream]}
      requires WeakOrd[T = A] = cmpInt().head.c

    operation ruleDesc() -> Int64 effects {Error, Error[EmptyStream]} =
      viaRule[A = Int64, WeakOrd = Descending](1, 5)
    operation ruleAsc() -> Int64 effects {Error, Error[EmptyStream]} =
      viaRule[A = Int64, WeakOrd = Ascending](1, 5)
    operation intDesc() -> Int64 effects {Error, Error[EmptyStream]} =
      viaInt[A = Int64, WeakOrd = Descending](1)
    -- a caller that holds NO dictionary
    operation plain() -> Int64 effects {Error, Error[EmptyStream]} = cmp(1, 5).head.c
  end
end
"#;

/// Call a nullary driver on a FRESH interpreter — a trapped call poisons later calls on a
/// shared one, and `interp_for` panics on a dirty load, so a value here is also a
/// clean-load assertion.
fn drive(entry: &str) -> i64 {
    let mut interp = crate::common::interp_for(ORD_PROGRAM);
    match interp.call(&format!("wip7vp4.ord.Driver.{entry}"), &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{entry}: expected an Int64, got {other:?}"),
    }
}

/// THE CASE. `viaRule` holds `WeakOrd[A]` and its caller chose the rival; `cmp` never
/// mentions `WeakOrd` beyond calling it. The inferred read is the clause's implicit
/// parameter, the citation routes `viaRule`'s slot to it, and the call dispatches through
/// what arrived. FAILS when the inference is backed out — both answer `-1`.
#[test]
fn a_clause_that_writes_nothing_answers_through_the_callers_dictionary() {
    assert_eq!(
        (drive("ruleDesc"), drive("ruleAsc")),
        (4, -4),
        "the call's requirement is a condition of `cmp`, filled by the rival the CALLER chose",
    );
}

/// CONTROL — passes either way, BY DESIGN. A caller that holds no dictionary: the clause
/// derives its own from the values, `Int64`'s own provision among three.
#[test]
fn a_caller_without_a_dictionary_answers_as_before() {
    assert_eq!(drive("plain"), -1, "`Int64`'s own `compare`, derived in the clause");
}

/// CONTROL — passes either way, BY DESIGN. A resolution with nothing to hand in: `cmpOne`'s
/// goal passes `cmp` no dictionary, so the inferred read derives at `1`'s type — one
/// definite answer, `Int64`'s own.
#[test]
fn a_query_derives_the_condition_from_the_value() {
    let mut kb = crate::common::load_kb_with(ORD_PROGRAM);
    let rows = crate::common::query_unary(&mut kb, "wip7vp4.ord.cmpOne");
    assert!(
        rows.len() == 1 && rows[0].1 && crate::common::scalar_int(&kb, &rows[0].0) == Some(-1),
        "`compare(1, 5)` at `Int64`'s own provision, definitely; got {rows:?}",
    );
}

/// CONTROL — passes either way, BY DESIGN. A call at a CONCRETE carrier is decided at load
/// by that carrier and gets no condition: the caller's `WeakOrd[A]` is for `A`, and the
/// clause wrote `Int64` — so `Descending` does not reach it.
#[test]
fn a_call_at_a_concrete_carrier_keeps_its_own_route() {
    assert_eq!(drive("intDesc"), -1, "`cmpInt`'s `compare(1, 5)` is `Int64`'s own");
}

/// A SECOND LOAD PHASE over a KB whose clause was woven. The typer runs again on every
/// later phase, over every live rule, and must not re-type an elaborated body — it has no
/// surface case for the woven call. `dbl`'s call is NESTED in `eq`, whose operands the
/// rule-body typer checks — a DEFAULTED spec op, which a value slot weaves; a woven call at
/// goal position is never typed there, which is why this row needs the nesting. FAILS with
/// the re-typing skip backed out: the second load is refused ("expected surface expression,
/// got bottom / post-elaboration form"). The woven clause then still answers through what it
/// inferred.
#[test]
fn a_woven_clause_survives_a_second_load_phase() {
    let mut kb = crate::common::load_kb_with(&fix_program(
        "wip7vp4.phases",
        "  rule dbl(?x) :- PartialEq.eq(Scale.twice(?x), 6)\n  \
         rule dblOne(?y) :- dbl(rod()), ?y <=> 1\n",
    ));
    let second = parse::parse(
        r#"
namespace wip7vp4.second
  import anthill.prelude.Int64
  fact seen(n: Int64)
end
"#,
    )
    .expect("parse the second phase");
    if let Err(errs) = load::load_all(&mut kb, &[&second], &NullResolver) {
        panic!(
            "the second phase must load over a woven clause: {:?}",
            errs.iter().map(|e| e.to_string()).collect::<Vec<_>>()
        );
    }
    let woven = kb
        .rule_ids_by_qn("wip7vp4.phases.dbl")
        .into_iter()
        .any(|rid| kb.rule_body_nodes(rid).iter().any(holds_woven_call));
    assert!(woven, "`dbl`'s nested call is woven — the shape this row is about");
    assert_eq!(
        crate::common::one_definite_int(&mut kb, "wip7vp4.phases.dblOne"),
        Some(1),
        "after the second phase the woven `dbl` still answers, definitely",
    );
}

/// Does this stored body hold a WOVEN call anywhere — what the pass leaves behind?
fn holds_woven_call(occ: &Rc<NodeOccurrence>) -> bool {
    let mut stack = vec![Rc::clone(occ)];
    while let Some(o) = stack.pop() {
        let Some(expr) = o.as_expr() else { continue };
        if matches!(expr, Expr::ApplyWithin { .. }) {
            return true;
        }
        for_each_child(expr, |c| stack.push(Rc::clone(c)));
    }
    false
}

/// An EQUATION is left alone: it is no clause whose body runs as goals. Asserted over the
/// POPULATION — every equational rule the stdlib and this fixture load — rather than one
/// fixture, because the equation that drove the exclusion is a stdlib law: String's
/// untagged `rule isEmpty(?s) <=> eq(length(?s), 0)`, whose `length` is a spec operation at
/// a carrier not known at load. FAILS with the exclusion backed out.
#[test]
fn an_equation_gets_no_inferred_condition() {
    let kb = crate::common::load_kb_with(ORD_PROGRAM);
    let woven: Vec<String> = kb
        .live_rule_ids()
        .into_iter()
        .filter(|&rid| kb.has_equational_head(rid))
        .filter(|&rid| kb.rule_body_nodes(rid).iter().any(holds_woven_call))
        .map(|rid| format!("{rid:?}"))
        .collect();
    assert!(woven.is_empty(), "equations with a woven call: {woven:?}");
}

/// A CARRIER NO GOAL EVER BINDS: `?x` is free for the whole clause, so the inferred read
/// cannot derive and the woven call cannot dispatch — both DELAY, and the clause flounders
/// into one CONDITIONAL row with `?r` still free. Before this ticket the unwoven call fell
/// through the WI-938 hook and answered NOTHING, which that hook's own site records as its
/// open half ("making that case DELAY instead of answering nothing"); a condition closes it
/// for every call that gets one. What must never happen either way is `?r` bound to the
/// un-reduced call (WI-1057), so the row asserts the value too. Its supplier-less twin, which
/// gets no condition and keeps the old outcome, is
/// `wi1043_bodyless_rule_body_test::an_unground_body_less_goal_binds_no_residual`.
///
/// FAILS with the inference backed out — the row then answers nothing.
#[test]
fn an_unground_woven_call_delays() {
    const PROGRAM: &str = r#"
namespace wip7vp4.unground
  import anthill.prelude.Int64
  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end
  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
  rule answer(?r) :- Desc.describe(?x, ?r)
end
"#;
    let mut kb = crate::common::load_kb_with(PROGRAM);
    let rows = crate::common::query_unary(&mut kb, "wip7vp4.unground.answer");
    assert!(
        rows.len() == 1 && !rows[0].1 && matches!(rows[0].0, Value::Var(_)),
        "one UNDECIDED row with `?r` free — the woven call delayed on its carrier; got {rows:?}",
    );
}

// ── Increment 4: an ordinary operation's own `requires` ─────────────────────

/// `Util.sign` is an ORDINARY operation — not a spec op — whose body dispatches through its
/// own `requires WeakOrd[T = A]` slot. The rivals are [`ORD_PROGRAM`]'s.
const SLOT_PROGRAM: &str = r#"
namespace wip7vp4.slots
  import anthill.prelude.{Int64, Error, EmptyStream, Relation, Ord, WeakOrd, PartialOrd, PartialEq, Eq}

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

  sort Util
    operation sign[A](x: A, y: A) -> Int64 requires WeakOrd[T = A] = WeakOrd.compare(x, y)
  end

  -- the rule WRITES NOTHING: `sign`'s `requires` is the clause's condition
  rule viaOp(?a, ?b, ?c) :- Util.sign(?a, ?b, ?c)
  rule viaOpOne(?c) :- viaOp(1, 5, ?c)

  sort Driver
    operation cite[A](x: A, y: A) -> Int64 effects {Error, Error[EmptyStream]}
      requires WeakOrd[T = A] = viaOp(x, y).head.c
    operation desc() -> Int64 effects {Error, Error[EmptyStream]} =
      cite[A = Int64, WeakOrd = Descending](1, 5)
    operation asc() -> Int64 effects {Error, Error[EmptyStream]} =
      cite[A = Int64, WeakOrd = Ascending](1, 5)
    operation plain() -> Int64 effects {Error, Error[EmptyStream]} = viaOp(1, 5).head.c
  end
end
"#;

fn drive_slots(entry: &str) -> i64 {
    let mut interp = crate::common::interp_for(SLOT_PROGRAM);
    match interp.call(&format!("wip7vp4.slots.Driver.{entry}"), &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{entry}: expected an Int64, got {other:?}"),
    }
}

/// THE CASE, for an operation's own `requires`. `cite` holds `WeakOrd[A]`, its caller chose
/// the rival, and `viaOp` only calls `sign`: the slot condition is routed from `cite`'s own
/// slot, and `sign`'s body dispatches `compare` through what arrived. FAILS with the
/// inference backed out — `-1` both ways, the slot derived from `1`'s type.
#[test]
fn an_operations_own_requires_is_filled_by_the_callers_dictionary() {
    assert_eq!(
        (drive_slots("desc"), drive_slots("asc")),
        (4, -4),
        "`sign`'s `WeakOrd[A]` is a condition of `viaOp`, filled by the rival the CALLER chose",
    );
}

/// CONTROL — passes either way, BY DESIGN. Nothing handed in, by an operation or by a rule
/// goal: the slot stays unbound and the bridge derives it from the values — `Int64`'s own.
#[test]
fn an_unfilled_slot_is_derived_as_before() {
    assert_eq!(drive_slots("plain"), -1, "`Int64`'s own `compare`, derived by the bridge");
    let mut kb = crate::common::load_kb_with(SLOT_PROGRAM);
    let rows = crate::common::query_unary(&mut kb, "wip7vp4.slots.viaOpOne");
    assert!(
        rows.len() == 1 && rows[0].1 && crate::common::scalar_int(&kb, &rows[0].0) == Some(-1),
        "a rule goal hands `viaOp` nothing: one definite `-1`; got {rows:?}",
    );
}

/// `Plain` provides no `Desc`; `Rich` does, answering 7 — WI-20260917-NR6FJ's shapes.
const NR6FJ_PROGRAM: &str = r#"
namespace wip7vp4.nr6fj
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64 = 1
  end

  sort Plain
    entity plain
  end

  sort Rich
    import anthill.prelude.Int64
    entity rich
    provides Desc[T = Rich]
    operation describe(x: Rich) -> Int64 = 7
  end

  operation viaRich(x: Rich) -> Int64 requires Desc[T = Rich] = Desc.describe(x)
  rule answerRich(?r) :- viaRich(rich(), ?r)
{tail}end
"#;

/// A slot NOTHING can fill stays a LOAD refusal when its call is woven. `viaAny`'s own
/// `requires Desc[T = Plain]` names a concrete carrier that provides nothing, and the call's
/// argument is unknown at load — so the call gets slot conditions and is woven before
/// NR6FJ's check runs. An inferred condition must not hide it: the check reads the woven
/// call as the call it is. FAILS with that reading backed out — it loads clean.
#[test]
fn a_woven_call_whose_slot_nothing_can_fill_is_still_refused() {
    let tail = "  operation viaAny[U](x: U) -> Int64 requires Desc[T = Plain] = 5\n  \
                rule answer(?v, ?r) :- viaAny(?v, ?r)\n";
    let errs = crate::common::try_load_kb_with(&NR6FJ_PROGRAM.replace("{tail}", tail))
        .err()
        .unwrap_or_else(|| panic!("expected NR6FJ's refusal; it loaded clean"))
        .join("\n");
    assert!(
        errs.contains("viaAny") && errs.contains("Plain"),
        "the refusal names the callee and the carrier that provides nothing: {errs}",
    );
}

/// A call whose every argument is KNOWN AT LOAD gets no condition — its chain is pinned
/// already, the typer's and the bridge's route — and still answers through its carrier.
/// `rich()` is a ground constructor the typer stamps no type on, which is why the test is
/// "holds no variable" before it is "stamped ground". FAILS with the stamp-only reading:
/// `answerRich`'s call is woven. The ANSWER passes either way, by design.
#[test]
fn a_call_whose_arguments_are_known_at_load_gets_no_condition() {
    let mut kb = crate::common::load_kb_with(&NR6FJ_PROGRAM.replace("{tail}", ""));
    let woven = kb
        .rule_ids_by_qn("wip7vp4.nr6fj.answerRich")
        .into_iter()
        .any(|rid| kb.rule_body_nodes(rid).iter().any(holds_woven_call));
    assert!(!woven, "`viaRich(rich(), ?r)`'s argument is known at load: no condition, no weave");
    let rows = crate::common::query_unary(&mut kb, "wip7vp4.nr6fj.answerRich");
    assert!(
        rows.len() == 1 && rows[0].1 && crate::common::scalar_int(&kb, &rows[0].0) == Some(7),
        "`Rich`'s own `describe`, definitely; got {rows:?}",
    );
}

// ── Review fixes: each row drives one fix, and fails with it backed out ─────

/// The rivals, `Util.sign` and `Desc`/`Leaf` the rows below share.
const FIX_PRELUDE: &str = r#"
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

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    entity leaf
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end

  sort Util
    operation sign[A](x: A, y: A) -> Int64 requires WeakOrd[T = A] = WeakOrd.compare(x, y)
    operation isLess[A](x: A, y: A) -> Bool requires WeakOrd[T = A] =
      Int64.lt(WeakOrd.compare(x, y), 0)
  end

  -- a DEFAULTED spec op: bodied, so a VALUE slot reduces it — and weaves it — where a
  -- body-less one is symbolic data
  sort Scale
    sort T = ?
    operation unit(x: T) -> Int64
    operation twice(x: T) -> Int64 = Int64.add(unit(x), unit(x))
  end

  sort Rod
    entity rod
    provides Scale[T = Rod]
    operation unit(x: Rod) -> Int64 = 3
  end
"#;

fn fix_program(ns: &str, body: &str) -> String {
    format!("namespace {ns}\n{FIX_PRELUDE}\n{body}end\n")
}

/// A woven call NESTED in another woven call — an inner spec-op call (a DEFAULTED one, which a
/// value slot weaves) as an argument of an outer slot call. Weaving call after call lost the
/// outer one once the inner weave had rebuilt its node: the load PANICKED on the "not found in
/// its body" assertion. Both calls are woven now, the inner one INSIDE the woven outer one.
/// This row guards that panic and the structure; it does not drive the clause, because the
/// nested shape answers nothing with or without the weave — a bridged call reduces no argument
/// but a host operation's (WI-1040's `a_covered_call_nested_in_another_covered_call_is_woven_-
/// with_it` drives a nested weave through a FOLDED outer body). FAILS with the one-pass
/// `weave_calls` backed out to sequential weaves.
#[test]
fn a_call_nested_in_a_woven_call_is_woven_too() {
    let kb = crate::common::load_kb_with(&fix_program(
        "wip7vp4.nest",
        "  rule nested(?x, ?z, ?c) :- Util.sign(Scale.twice(?x), ?z, ?c)\n",
    ));
    let woven: Vec<(String, bool, Vec<String>)> = crate::common::body_calls(&kb, "wip7vp4.nest.nested")
        .into_iter()
        .filter(|(_, woven, _)| *woven)
        .collect();
    assert_eq!(
        woven,
        vec![
            ("sign".to_string(), true, vec!["twice".to_string()]),
            ("twice".to_string(), true, Vec::new()),
        ],
        "the outer `sign` is woven, holding the woven inner `twice`",
    );
}

/// A spec-op call that does not ALIGN to its parameters — `y` names no parameter of
/// `describe` — is the typer's to refuse. It reads headless (`Suspend`), and before the
/// alignment gate it became a demand and `inferred_read` hit `unreachable!`, PANICKING the
/// load (release builds too). FAILS with the gate in `inferred_demand` backed out.
#[test]
fn a_call_that_does_not_align_is_refused_not_a_panic() {
    let errs = crate::common::try_load_kb_with(&fix_program(
        "wip7vp4.unaligned",
        "  rule bad(?v, ?r) :- ?r = Desc.describe(y: ?v)\n",
    ))
    .err()
    .unwrap_or_else(|| panic!("the unaligned call is a load error"))
    .join("\n");
    assert!(errs.contains("describe"), "the typer names the call: {errs}");
}

/// A WRITTEN `requires(Derived[T])` grounded by an INHERITED witness — a call to an
/// operation of `Base`, which `Derived` requires. The inference used to weave that call
/// first (its spec, `Base`, is not the written `Derived`), and the witness scan (plain
/// applications only) then found none: "no such call in the rule body". FAILS with
/// `infer_rule_body_requirements` moved back before `record_find_dictionary_grounding`.
#[test]
fn a_written_requires_keeps_its_inherited_witness() {
    let mut kb = crate::common::load_kb_with(&fix_program(
        "wip7vp4.inherited",
        "  sort Base\n    sort T = ?\n    operation op(x: T) -> Int64\n  end\n  \
         sort Derived\n    sort T = ?\n    requires Base[T = T]\n  end\n  \
         sort Leaf2\n    entity leaf2\n    provides Base[T = Leaf2]\n    \
         provides Derived[T = Leaf2]\n    operation op(x: Leaf2) -> Int64 = 5\n  end\n  \
         rule viaDerived(?x, ?r) :- requires(Derived[T]), Base.op(?x, ?r)\n  \
         rule derivedOne(?r) :- viaDerived(leaf2(), ?r)\n",
    ));
    assert_eq!(crate::common::one_definite_int(&mut kb, "wip7vp4.inherited.derivedOne"), Some(5), "`Leaf2`'s own `op`");
}

/// A call at its DECLARED arity in GOAL position is woven only for the BOOL VIEW
/// (`eq(isLess(..), true)`), whose gate reads a woven head: `less(1, 5)` answers through it
/// (the CITED face is `a_bool_view_call_answers_through_the_callers_dictionary`). A bare
/// NON-Bool call there is WI-583's load error, which a woven call would slip past, so it is
/// not woven. FAILS, first assertion, with the Bool-view gate reading only the view — the
/// woven `less` answers nothing; second assertion, with `woven_goal_has_reader` admitting
/// every declared-arity call — it loads clean.
#[test]
fn a_goal_at_its_declared_arity_is_woven_only_for_the_bool_view() {
    let mut kb = crate::common::load_kb_with(&fix_program(
        "wip7vp4.declared",
        "  rule less(?a, ?b) :- Util.isLess(?a, ?b)\n  \
         rule lessOne(?x) :- less(1, 5), ?x <=> 1\n",
    ));
    assert_eq!(crate::common::one_definite_int(&mut kb, "wip7vp4.declared.lessOne"), Some(1), "`1 < 5` through the Bool view");
    let errs = crate::common::try_load_kb_with(&fix_program(
        "wip7vp4.bare",
        "  rule bare(?a, ?b) :- Util.sign(?a, ?b)\n",
    ))
    .err()
    .unwrap_or_else(|| panic!("a bare non-Bool goal is WI-583's load error"))
    .join("\n");
    assert!(errs.contains("no relational reading"), "{errs}");
}

/// A call inside a SCOPE — a bounded quantifier's body — whose carrier is bound only there.
/// A read placed before the top-level goal would wait on `?e` for ever, and the woven call
/// on the read: the clause floundered where value dispatch answers. (`twice` is bodied: the
/// inference never weaves a body-less spec op below the top-level goal at all.) FAILS with the
/// demand walk descending into goal positions again.
#[test]
fn a_call_inside_a_quantifier_keeps_its_value_dispatch() {
    let mut kb = crate::common::load_kb_with(&fix_program(
        "wip7vp4.scope",
        "  rule allSix(?xs) :- (forall ?e in ?xs: Scale.twice(?e, 6))\n  \
         rule sixOne(?x) :- allSix([rod(), rod()]), ?x <=> 1\n",
    ));
    assert_eq!(crate::common::one_definite_int(&mut kb, "wip7vp4.scope.sixOne"), Some(1), "each element doubled by value");
}

/// A cited slot call that must WAIT — its second argument is bound by a later goal. The
/// slot arm handed back the plain call, and the retry reduced it with no slots: the answer
/// was `Int64`'s own `-1` where the caller chose `Descending` (4), and `five(?a)` written
/// first gave 4 — goal order decided it. FAILS with the slot arm returning its plain call.
#[test]
fn a_woven_slot_call_that_waits_keeps_its_slots() {
    let driver = "  rule five(?x) :- ?x <=> 5\n  \
                  rule late(?b, ?c) :- Util.sign(?b, ?a, ?c), five(?a)\n  \
                  sort Driver\n    \
                  operation citeLate[A](x: A) -> Int64 effects {Error, Error[EmptyStream]}\n      \
                  requires WeakOrd[T = A] = late(x).head.c\n    \
                  operation lateDesc() -> Int64 effects {Error, Error[EmptyStream]} =\n      \
                  citeLate[A = Int64, WeakOrd = Descending](1)\n  \
                  end\n";
    let mut interp = crate::common::interp_for(&fix_program("wip7vp4.waits", driver));
    match interp.call("wip7vp4.waits.Driver.lateDesc", &[]) {
        Ok(Value::Int(n)) => assert_eq!(n, 4, "`Descending`'s compare(1, 5), after `?a` is bound"),
        other => panic!("expected an Int64, got {other:?}"),
    }
}

/// A slot whose parameter is pinned through ANOTHER parameter: `sign`'s `x` is `?a`, a body
/// variable, and its `A` is pinned by `y`, the column `?b`. A one-step read of the pins saw
/// the witness variable, routed nothing, and the call derived `Int64`'s own (`1`) where the
/// caller chose `Descending` (`-4`). FAILS with `op_slot_route` reading `resolve_as_value`.
#[test]
fn a_slot_routes_whichever_parameter_pins_it() {
    let driver = "  rule same2(?x, ?y) :- ?x <=> ?y\n  \
                  rule rOrder(?b, ?y, ?c) :- same2(?y, ?a), Util.sign(?a, ?b, ?c)\n  \
                  sort Driver\n    \
                  operation citeOrder[A](x: A, y: A) -> Int64 effects {Error, Error[EmptyStream]}\n      \
                  requires WeakOrd[T = A] = rOrder(x, y).head.c\n    \
                  operation orderDesc() -> Int64 effects {Error, Error[EmptyStream]} =\n      \
                  citeOrder[A = Int64, WeakOrd = Descending](1, 5)\n  \
                  end\n";
    let mut interp = crate::common::interp_for(&fix_program("wip7vp4.order", driver));
    match interp.call("wip7vp4.order.Driver.orderDesc", &[]) {
        Ok(Value::Int(n)) => assert_eq!(n, -4, "`Descending`'s compare(5, 1)"),
        other => panic!("expected an Int64, got {other:?}"),
    }
}

/// The FIRST slot supplied by the caller, the second derived: `Score` has two RIVAL
/// witnesses at `Colour` and no provision on `Colour` itself, so deriving the first slot
/// from the value TIES. The derivation used to run over the whole chain before the caller's
/// dictionary was placed, and the tie suspended the call. FAILS with
/// `resolve_bridge_requirements_supplied` handed no supplied slots.
#[test]
fn a_supplied_slot_is_not_re_derived() {
    const PROGRAM: &str = r#"
namespace wip7vp4.partial
  import anthill.prelude.{Int64, Error, EmptyStream, PartialEq}

  sort Score
    sort T = ?
    operation score(x: T) -> Int64
  end

  sort Colour
    entity red
    entity blue
  end

  sort ByName
    provides Score[T = Colour]
    operation score(x: Colour) -> Int64 =
      match x
        case red() -> 1
        case blue() -> 3
  end

  sort ByHeat
    provides Score[T = Colour]
    operation score(x: Colour) -> Int64 =
      match x
        case red() -> 3
        case blue() -> 1
  end

  sort Util
    operation both[A, B](x: A, y: B) -> Int64 requires Score[T = A], PartialEq[T = B] =
      Score.score(x)
  end

  -- `?b` is no head column, so its slot is never routed: only the first slot is supplied
  rule viaBoth(?a, ?c) :- ?b <=> 7, Util.both(?a, ?b, ?c)

  sort Driver
    operation cite[A](x: A) -> Int64 effects {Error, Error[EmptyStream]}
      requires Score[T = A] = viaBoth(x).head.c
    operation heat() -> Int64 effects {Error, Error[EmptyStream]} =
      cite[A = Colour, Score = ByHeat](red())
  end
end
"#;
    let mut interp = crate::common::interp_for(PROGRAM);
    match interp.call("wip7vp4.partial.Driver.heat", &[]) {
        Ok(Value::Int(n)) => assert_eq!(n, 3, "`ByHeat`'s score of `red`"),
        other => panic!("expected an Int64, got {other:?}"),
    }
}

/// An UNCITED slot call whose arguments nothing binds now DELAYS — the woven call waits on
/// an unevaluated call, as increment 1's does — where the unwoven call answered nothing.
/// Pinned so the change is stated rather than silent. FAILS with the inference backed out
/// (no row at all).
#[test]
fn an_unground_slot_call_delays() {
    let mut kb = crate::common::load_kb_with(&fix_program(
        "wip7vp4.unground2",
        "  rule free(?c) :- Util.sign(?s, ?t, ?c)\n",
    ));
    let rows = crate::common::query_unary(&mut kb, "wip7vp4.unground2.free");
    assert!(
        rows.len() == 1 && !rows[0].1 && matches!(rows[0].0, Value::Var(_)),
        "one UNDECIDED row with `?c` free: {rows:?}",
    );
}

// ── Review fixes, round 2: each row drives one fix, and fails with it backed out ─────

/// An UNPINNED body-less spec op in a VALUE slot is symbolic algebra — the term the rule wrote
/// (kernel-language §5.3, "what the gate still declines") — so it gets no condition: `mk`
/// binds `?s` to the written `Shape.circle(num(v: 1))`, not to `Num.circle`'s result, although
/// `Num` provides `Shape`. (A call whose carrier is known at load is PINNED by the typer and
/// dispatched — `?s <=> Shape.circle(num(v: 1))` binds `num(v: 9)` — and is no demand of the
/// inference either way.) FAILS with `inferred_demand` admitting a body-less op in a value
/// slot: the operand is woven and dispatched, and `?s` is `num(v: 9)`.
#[test]
fn a_body_less_operand_stays_the_term_the_rule_wrote() {
    const PROGRAM: &str = r#"
namespace wip7vp4.symbolic
  import anthill.prelude.Int64

  sort Shape
    sort T = ?
    operation circle(r: T) -> T
  end

  sort Num
    entity num(v: Int64)
    provides Shape[T = Num]
    operation circle(r: Num) -> Num = num(v: 9)
  end

  rule mk(?r, ?s) :- ?s <=> Shape.circle(?r)
  rule mkOne(?s) :- mk(num(v: 1), ?s)
end
"#;
    let mut kb = crate::common::load_kb_with(PROGRAM);
    let shown = crate::common::shown_rows(&mut kb, "wip7vp4.symbolic.mkOne");
    assert!(
        shown.len() == 1 && shown[0].1 && shown[0].0.contains("circle(num(v: 1))"),
        "`?s` is the term `mk` wrote, not `Num.circle`'s `num(v: 9)`; got {shown:?}",
    );
}

/// A call inside a DEFERRED data form — an `if` branch — gets no condition: a read before the
/// goal would run whether or not the branch is taken. `pick(false, 5, ?e)` takes the `else`,
/// so nothing ever calls `twice` on `5`, an `Int64` with no `Scale`. (`twice` is a DEFAULTED
/// spec op: a body-less one in a value slot is symbolic data and gets no condition anywhere.)
/// FAILS with the demand walk entering an `if`: the hoisted read on `5` fails the clause, and
/// `pickOne` is empty.
#[test]
fn a_call_in_an_untaken_branch_gets_no_condition() {
    let mut kb = crate::common::load_kb_with(&fix_program(
        "wip7vp4.deferred",
        "  rule pick(?f, ?v, ?e) :- ?e <=> (if ?f then Scale.twice(?v) else 1)\n  \
         rule pickOne(?x) :- pick(false, 5, ?e), ?x <=> 1\n",
    ));
    assert_eq!(crate::common::one_definite_int(&mut kb, "wip7vp4.deferred.pickOne"), Some(1), "the `else` calls nothing");
}

/// THE STATED LIMIT, pinned: a call in a `|` BRANCH gets no condition, because the only place
/// a read can go is before the TOP-level goal — a citation's reads are laid out over the body's
/// top-level goals (`requirement_read_counts`) — and there it runs whichever branch is taken.
/// So the call keeps VALUE dispatch, as before this ticket (its caller's dictionary does not
/// reach it — the stated limit), and the OTHER branch keeps its answers: `pickB(?x, ?c)` with
/// `?x` free answers `99`, definitely, by its second branch. FAILS with the demand walk entering
/// goal positions: the read hoisted before the `|` waits on `?x`, which only the first branch
/// would use, and `99` comes back CONDITIONAL. The CONTROL, `pickRod`, answers `6` and `99`
/// either way, by design: with `?x` bound the hoisted read derives, and costs nothing.
#[test]
fn a_call_in_a_branch_keeps_value_dispatch() {
    let mut kb = crate::common::load_kb_with(&fix_program(
        "wip7vp4.branch",
        "  rule pickB(?x, ?c) :- (Scale.twice(?x, ?c) | ?c <=> 99)\n  \
         rule pickRod(?c) :- pickB(rod(), ?c)\n  \
         rule pickFree(?c) :- pickB(?x, ?c)\n",
    ));
    let mut definite = |rel: &str| {
        let mut ns: Vec<i64> = crate::common::query_unary(&mut kb, rel)
            .iter()
            .filter(|(_, d)| *d)
            .filter_map(|(v, _)| crate::common::scalar_int(&kb, v))
            .collect();
        ns.sort();
        ns
    };
    assert_eq!(definite("wip7vp4.branch.pickRod"), vec![6, 99], "both branches, the first by value");
    assert_eq!(definite("wip7vp4.branch.pickFree"), vec![99], "the second branch, undisturbed");
}

/// A BOOL-VIEW goal answers through the CALLER's dictionary. `less` calls `isLess` at its
/// declared arity — `eq(isLess(?a, ?b), true)` — and `citeLess`'s caller chose: under
/// `Descending` `compare(1, 5)` is `4`, so `1` is not less than `5` and `less(1, 5)` is empty;
/// under `Ascending` it is `-4`, and it holds. FAILS with `woven_goal_has_reader` declining the
/// Bool view — the call derives `Int64`'s own `-1`, `less` holds, `lessDesc` is `false` — and,
/// through `lessAsc`, with the Bool-view gate reading only the view: the woven call answers
/// nothing, so `less` is empty under both.
#[test]
fn a_bool_view_call_answers_through_the_callers_dictionary() {
    let driver = "  rule less(?a, ?b) :- Util.isLess(?a, ?b)\n  \
                  sort Driver\n    \
                  operation citeLess[A](x: A, y: A) -> Bool effects {Error, Error[EmptyStream]}\n      \
                  requires WeakOrd[T = A] =\n      \
                  let r = less(x, y)\n      \
                  r.isEmpty\n    \
                  operation lessDesc() -> Bool effects {Error, Error[EmptyStream]} =\n      \
                  citeLess[A = Int64, WeakOrd = Descending](1, 5)\n    \
                  operation lessAsc() -> Bool effects {Error, Error[EmptyStream]} =\n      \
                  citeLess[A = Int64, WeakOrd = Ascending](1, 5)\n  \
                  end\n";
    let mut interp = crate::common::interp_for(&fix_program("wip7vp4.boolview", driver));
    let mut empty = |entry: &str| match interp.call(&format!("wip7vp4.boolview.Driver.{entry}"), &[]) {
        Ok(Value::Bool(b)) => b,
        other => panic!("{entry}: expected a Bool, got {other:?}"),
    };
    assert!(empty("lessDesc"), "`Descending`: 1 is not less than 5, so `less(1, 5)` is empty");
    assert!(!empty("lessAsc"), "`Ascending`: it is, so `less(1, 5)` holds");
}

/// A NEGATED citation that routes some of its relation's reads and not others DECIDES:
/// `viaBoth`'s first slot is routed from `negCite`'s caller and its second is not, and the
/// marker's slot for the unrouted one is a GROUND sentinel, so `not(…)` sees a ground goal.
/// `ByHeat` scores `red` 3, so `viaBoth(red(), 3)` holds and its negation is empty; `ByName`
/// scores it 1. FAILS with the unrouted slot an unbound variable: `step_naf` delays the
/// negation, and the drain raises `RelationFloundered` for both.
#[test]
fn a_negated_partly_routed_citation_decides() {
    const PROGRAM: &str = r#"
namespace wip7vp4.negated
  import anthill.prelude.{Int64, Bool, Error, EmptyStream, PartialEq}
  import anthill.prelude.Relation.{negate}

  sort Score
    sort T = ?
    operation score(x: T) -> Int64
  end

  sort Colour
    entity red
    entity blue
  end

  sort ByName
    provides Score[T = Colour]
    operation score(x: Colour) -> Int64 =
      match x
        case red() -> 1
        case blue() -> 3
  end

  sort ByHeat
    provides Score[T = Colour]
    operation score(x: Colour) -> Int64 =
      match x
        case red() -> 3
        case blue() -> 1
  end

  sort Util
    operation both[A, B](x: A, y: B) -> Int64 requires Score[T = A], PartialEq[T = B] =
      Score.score(x)
  end

  -- `?b` is no head column, so its slot is never routed: only the first slot is supplied
  rule viaBoth(?a, ?c) :- ?b <=> 7, Util.both(?a, ?b, ?c)

  sort Driver
    operation negCite[A](x: A) -> Bool effects {Error, Error[EmptyStream]}
      requires Score[T = A] =
      let r = negate(viaBoth(x, 3))
      r.isEmpty
    operation negHeat() -> Bool effects {Error, Error[EmptyStream]} =
      negCite[A = Colour, Score = ByHeat](red())
    operation negName() -> Bool effects {Error, Error[EmptyStream]} =
      negCite[A = Colour, Score = ByName](red())
  end
end
"#;
    let mut interp = crate::common::interp_for(PROGRAM);
    let mut empty = |entry: &str| match interp.call(&format!("wip7vp4.negated.Driver.{entry}"), &[]) {
        Ok(Value::Bool(b)) => b,
        other => panic!("{entry}: expected a Bool, got {other:?}"),
    };
    assert!(empty("negHeat"), "`ByHeat`: `viaBoth(red(), 3)` holds, so its negation is empty");
    assert!(!empty("negName"), "`ByName`: it does not, so its negation holds");
}

/// A call whose carrier's ONLY instance is a WITNESS provision — WI-450's `sort Rival provides
/// Desc[T = Leaf]`, filed under `Rival` — answers through it: the inferred read asks both
/// channels (`carrier_provides_spec`), as value dispatch does. FAILS with the guard core
/// asking `sort_provides` alone: the read DontFires on `leaf()` and `answer` is empty.
#[test]
fn a_witness_supplied_carrier_answers_through_the_inferred_read() {
    let ns = "wip7vp4.witness";
    let src = crate::wi1035_dot_member_supplier_tie_test::body_less(
        ns,
        "",
        crate::wi1027_bodyless_supplier_tie_test::RIVAL_WITNESS,
        "  rule viaVar(?x, ?r) :- Desc.describe(?x, ?r)\n  rule answer(?r) :- viaVar(leaf(), ?r)\n",
    );
    assert_eq!(
        crate::wi1026_rule_body_spec_op_dispatch_test::answer(ns, &src),
        9,
        "`Rival`'s `describe`, the witness's",
    );
}

/// A slot whose callee has a parameter a SUBTYPE argument cannot pin is still routed by the
/// others. `sign2`'s `s: Shape` takes `circle()`, a `Circle` — `Circle provides Shape` — which
/// does not UNIFY with `Shape` (unification is not subsumption) and pins nothing; `x` and `y`
/// pin `A`. FAILS with `op_slot_route` refusing the whole route on that parameter: the slot
/// is derived from the values, `Int64`'s own `-1`, where the caller chose `Descending` (`4`).
#[test]
fn a_subtype_argument_does_not_block_a_slot_route() {
    let driver = "  sort Shape\n  end\n  \
                  sort Circle\n    provides Shape\n    entity circle\n  end\n  \
                  sort Util2\n    \
                  operation sign2[A](x: A, y: A, s: Shape) -> Int64 requires WeakOrd[T = A] =\n      \
                  WeakOrd.compare(x, y)\n  \
                  end\n  \
                  rule viaS(?a, ?b, ?s, ?c) :- Util2.sign2(?a, ?b, ?s, ?c)\n  \
                  sort Driver\n    \
                  operation citeS[A](x: A, y: A) -> Int64 effects {Error, Error[EmptyStream]}\n      \
                  requires WeakOrd[T = A] = viaS(x, y, circle()).head.c\n    \
                  operation subtypeDesc() -> Int64 effects {Error, Error[EmptyStream]} =\n      \
                  citeS[A = Int64, WeakOrd = Descending](1, 5)\n  \
                  end\n";
    let mut interp = crate::common::interp_for(&fix_program("wip7vp4.subtype", driver));
    match interp.call("wip7vp4.subtype.Driver.subtypeDesc", &[]) {
        Ok(Value::Int(n)) => assert_eq!(n, 4, "`Descending`'s compare(1, 5)"),
        other => panic!("expected an Int64, got {other:?}"),
    }
}

/// A DISPATCH-woven call that must WAIT keeps its dictionary. `zeroPlus` is carrier-less, so
/// only the clause's dictionary names its implementation — `Wrap`'s, a CONDITIONAL provider
/// whose body reads its element's dictionary out of the one it is dispatched through (NAR1X's
/// shape). Its content argument `?n` is bound by a LATER goal, so the first attempt waits and
/// the retry must see the woven call again: `104` over `wrap(inner: sum())`, `106` over
/// `prod()` — two element providers, so no value can stand in for the dictionary. FAILS with
/// the dispatch arm handing back its plain target call: the WI-938 hook stores it, the retry
/// reaches `Wrap.zeroPlus` with no dictionary, and its element's slot cannot be derived.
#[test]
fn a_dispatched_call_that_waits_keeps_its_dictionary() {
    const PROGRAM: &str = r#"
namespace wip7vp4.waitsdispatch
  import anthill.prelude.Int64

  sort Zeroable
    sort T = ?
    operation zero() -> Int64
    operation zeroPlus(n: Int64) -> Int64
    operation tag(x: T) -> Int64 = 0
  end

  sort Sum
    import anthill.prelude.Int64
    entity sum
    provides Zeroable[T = Sum]
    operation zero() -> Int64 = 3
    operation zeroPlus(n: Int64) -> Int64 = Int64.add(3, n)
    operation tag(x: Sum) -> Int64 = 1
  end

  sort Prod
    import anthill.prelude.Int64
    entity prod
    provides Zeroable[T = Prod]
    operation zero() -> Int64 = 5
    operation zeroPlus(n: Int64) -> Int64 = Int64.add(5, n)
    operation tag(x: Prod) -> Int64 = 2
  end

  sort Wrap
    import anthill.prelude.Int64
    sort E = ?
    entity wrap(inner: E)
    provides Zeroable[T = Wrap] :- Zeroable[E] where
      operation zero() -> Int64 = Int64.add(Zeroable.zero(), 100)
      operation zeroPlus(n: Int64) -> Int64 = Int64.add(Int64.add(Zeroable.zero(), 100), n)
      operation tag(x: Wrap) -> Int64 = 9
    end
  end

  rule via(?x, ?r) :- require[Zeroable[T]], Zeroable.tag(?x, ?t), Zeroable.zeroPlus(?n, ?r), ?n <=> 1
  rule sumAnswer(?r) :- via(wrap(inner: sum()), ?r)
  rule prodAnswer(?r) :- via(wrap(inner: prod()), ?r)
end
"#;
    let mut kb = crate::common::load_kb_with(PROGRAM);
    assert_eq!(
        crate::common::one_definite_int(&mut kb, "wip7vp4.waitsdispatch.sumAnswer"),
        Some(104),
        "`Wrap.zeroPlus(1)`: `Sum`'s `zero()` + 100 + 1, through the element's dictionary",
    );
    assert_eq!(
        crate::common::one_definite_int(&mut kb, "wip7vp4.waitsdispatch.prodAnswer"),
        Some(106),
        "the element's number, not a constant: `Prod`'s `zero()` + 100 + 1",
    );
}

// ── Review fixes, round 3: each row drives one fix, and fails with it backed out ─────

/// A call with a CONCRETE carrier among its arguments keeps value dispatch, though the guard
/// answers `Suspend` for it (`?x` is not known at load): `toN`'s `?u` is a `String`, the
/// second carrier of `Conv`, and the call is left unwoven. `go` answers `7`. FAILS, first
/// assertion, with `inferred_demand`'s concrete-carrier check removed: the call is woven. The
/// ANSWER passes either way since WI-20260925-PRVA2 (c): woven, its read asks the provision at
/// `(Meters, String)`, which `Meters`' row binds (measured, `7`); before (c) the read asked
/// `String` to provide `Conv`, DontFired, and `go` was empty.
#[test]
fn a_call_with_a_concrete_carrier_among_its_arguments_keeps_value_dispatch() {
    const MIXED: &str = r#"
namespace wip7vp4.mixed
  import anthill.prelude.{Int64, String}

  sort Conv
    sort A = ?
    sort B = ?
    operation conv(a: A, b: B) -> Int64
  end

  sort Meters
    entity m(v: Int64)
    provides Conv[A = Meters, B = String]
    operation conv(a: Meters, b: String) -> Int64 = 7
  end

  rule toN(?x, ?r) :- ?u <=> "km", Conv.conv(?x, ?u, ?r)
  rule go(?r) :- toN(m(v: 3), ?r)
end
"#;
    let mut kb = crate::common::load_kb_with(MIXED);
    assert_eq!(
        crate::common::body_calls(&kb, "wip7vp4.mixed.toN"),
        vec![("conv".to_string(), false, Vec::new()), ("unify".to_string(), false, Vec::new())],
        "the call is left unwoven: its concrete carrier decides it",
    );
    assert_eq!(crate::common::one_definite_int(&mut kb, "wip7vp4.mixed.go"), Some(7), "`Meters.conv`, by value");
}

/// A WITNESS-supplied carrier beside a second carrier LOADS: `W provides Conv[A = Leaf2, B =
/// Int64]`, and `r`'s call reads `?l: Leaf2`, `?n: Int64`. The load check asked each carrier
/// to provide `Conv`: `Leaf2` does (a witness provision), `Int64` never will — it is the
/// provision's second binding — and the program was refused. Round 3 filed `Leaf2` as not
/// known at load to dodge that; WI-20260925-PRVA2 (c) asks the provision at `(Leaf2, Int64)`,
/// which `W`'s row binds, and removed the filter (it had turned into a hidden refusal). `r`
/// answers `9`, `W`'s. FAILS with the per-carrier question restored for carriers at several
/// parameters: the load is refused, "`Int64` provides no `Conv`".
#[test]
fn a_witness_carrier_beside_a_second_carrier_loads() {
    const WITNESS2: &str = r#"
namespace wip7vp4.witness2
  import anthill.prelude.Int64

  sort Conv
    sort A = ?
    sort B = ?
    operation conv(a: A, b: B) -> Int64
  end

  sort Leaf2
    entity leaf2
  end

  sort W
    provides Conv[A = Leaf2, B = Int64]
    operation conv(a: Leaf2, b: Int64) -> Int64 = 9
  end

  entity seed(l: Leaf2, n: Int64)
  fact seed(l: leaf2(), n: 4)

  rule r(?x) :- seed(l: ?l, n: ?n), Conv.conv(?l, ?n, ?x)
end
"#;
    let mut kb = crate::common::load_kb_with(WITNESS2);
    assert_eq!(crate::common::one_definite_int(&mut kb, "wip7vp4.witness2.r"), Some(9), "`W.conv`");
}

/// A clause holding a WOVEN goal is not refuted when it opens. `lessH`'s `?p(?a)` — a
/// higher-order call, non-reorderable — delays the whole clause on the caller's unbound `?p`
/// (WI-670's open-time pre-check), and the pre-check first asks whether a conjunct REFUTES the
/// clause regardless: the woven `isLess` goal heads the reflect twin `apply_within` on the view,
/// which no clause has — zero candidates, read as a refutation. It is skipped: the clause
/// delays, `known` binds `?p`, and `q` answers. (A `ground(?a)` or `nonvar(?a)` in its place
/// types `?a`, so the call is not woven and never reaches the question.) FAILS with the skip
/// removed: the clause is refuted at opening and `q` is empty.
#[test]
fn a_clause_with_a_woven_goal_is_not_refuted_at_opening() {
    let mut kb = crate::common::load_kb_with(&fix_program(
        "wip7vp4.opening",
        "  entity known(p: ?)\n  \
         rule isPos(?n) :- Int64.gt(?n, 0)\n  \
         fact known(p: isPos)\n  \
         rule lessH(?p, ?a, ?b) :- ?p(?a), Util.isLess(?a, ?b)\n  \
         rule q(?r) :- lessH(?p, 1, 5), known(p: ?p), ?r <=> 1\n",
    ));
    assert_eq!(crate::common::one_definite_int(&mut kb, "wip7vp4.opening.q"), Some(1), "`isPos(1)` and `isLess(1, 5)`, once `?p` is bound");
}

/// A woven Bool-view call keeps its WI-580 CASE SPLIT. `warm` is a DEFAULTED spec op whose body
/// `match`es on `c`; `w`'s call is woven (its carrier `?x` is unknown at load), and `wRod` asks
/// it with `?c` unbound: the split reads the call through the member its dictionary selects —
/// the default, `Rod` supplying none — and narrows `?c` to `red`, definitely; cited with the
/// rival `Cool`, it splits through `Cool`'s own `warm` and finds `blue`. FAILS with
/// `op_call_as_occ`'s woven arm removed: no split, the bridge waits on `?c`, and `wRod` is one
/// floundered row.
#[test]
fn a_woven_bool_view_call_keeps_its_case_split() {
    const SPLIT: &str = r#"
namespace wip7vp4.split
  import anthill.prelude.{Int64, Bool}

  sort Colour
    entity red
    entity blue
  end

  sort Palette
    sort T = ?
    operation tint(x: T) -> Int64
    operation warm(c: Colour, x: T) -> Bool =
      match c
        case red() -> true
        case blue() -> false
  end

  sort Rod
    entity rod
    provides Palette[T = Rod]
    operation tint(x: Rod) -> Int64 = 1
  end

  -- a rival whose `warm` is the other way round: a citation that hands it in must split
  -- through ITS body
  sort Cool
    provides Palette[T = Rod]
    operation tint(x: Rod) -> Int64 = 2
    operation warm(c: Colour, x: Rod) -> Bool =
      match c
        case red() -> false
        case blue() -> true
  end

  rule w(?c, ?x) :- Palette.warm(?c, ?x)
  rule wRod(?c) :- w(?c, rod())

  sort Driver
    import anthill.prelude.{Error, EmptyStream}
    operation citeW[X](x: X) -> Colour effects {Error, Error[EmptyStream]}
      requires Palette[T = X] = w(x: x).head.c
    operation warmCool() -> Colour effects {Error, Error[EmptyStream]} =
      citeW[X = Rod, Palette = Cool](rod())
  end
end
"#;
    let mut interp = crate::common::interp_for(SPLIT);
    let cited = interp.call("wip7vp4.split.Driver.warmCool", &[]).expect("`warmCool` answers");
    let shown = crate::common::show_value(interp.kb(), &cited);
    assert!(shown.ends_with("blue"), "`Cool`'s `warm` holds at `blue()`, not `red()`: {shown}");
    let mut kb = crate::common::load_kb_with(SPLIT);
    let shown = crate::common::shown_rows(&mut kb, "wip7vp4.split.wRod");
    assert_eq!(shown, vec![("red".to_string(), true)], "`warm(red(), rod())` holds; `blue()` does not");
}

/// A Bool-view call written with NAMED arguments answers through the caller's dictionary, as
/// its positional twin does (`a_bool_view_call_answers_through_the_callers_dictionary`): it is
/// woven like it, and its labels reach the callee's parameters. FAILS two ways: with
/// `woven_goal_has_reader` refusing named arguments, the call is not woven and derives `Int64`'s
/// own `-1` — `lessN(1, 5)` holds under `Descending` too; and with `reduce_op_value` reading a
/// named argument by the parameter's symbol alone, the written label `x` matches no `…isLess.x`
/// and the call never reduces — one conditional row under both.
#[test]
fn a_named_argument_bool_view_call_answers_through_the_callers_dictionary() {
    let driver = "  rule lessN(?a, ?b) :- Util.isLess(x: ?a, y: ?b)\n  \
                  sort Driver\n    \
                  operation citeLessN[A](x: A, y: A) -> Bool effects {Error, Error[EmptyStream]}\n      \
                  requires WeakOrd[T = A] =\n      \
                  let r = lessN(x, y)\n      \
                  r.isEmpty\n    \
                  operation lessNDesc() -> Bool effects {Error, Error[EmptyStream]} =\n      \
                  citeLessN[A = Int64, WeakOrd = Descending](1, 5)\n    \
                  operation lessNAsc() -> Bool effects {Error, Error[EmptyStream]} =\n      \
                  citeLessN[A = Int64, WeakOrd = Ascending](1, 5)\n  \
                  end\n";
    let mut interp = crate::common::interp_for(&fix_program("wip7vp4.named", driver));
    let mut empty = |entry: &str| match interp.call(&format!("wip7vp4.named.Driver.{entry}"), &[]) {
        Ok(Value::Bool(b)) => b,
        other => panic!("{entry}: expected a Bool, got {other:?}"),
    };
    assert!(empty("lessNDesc"), "`Descending`: 1 is not less than 5, so `lessN(1, 5)` is empty");
    assert!(!empty("lessNAsc"), "`Ascending`: it is, so `lessN(1, 5)` holds");
}

/// A `@[simp]` LAW fires at a carrier whose only instance is a WITNESS provision, as the run-time
/// read's guard does since this ticket: both ask the one guard core, which asks both channels
/// (`carrier_provides_spec`). `Rival provides Magma[T = Leaf]` with an `op2` that answers its
/// second argument, and `Magma`'s law `op2(?a, ?b) <=> ?a`: the typer rewrites `r`'s call at
/// load and `r` is `l1`. FAILS with the guard core asking `sort_provides` alone: the law does not
/// fire at `Leaf`, the call dispatches to `Rival.op2`, and `r` is `l2`.
#[test]
fn a_simp_law_fires_at_a_witness_supplied_carrier() {
    const LAW: &str = r#"
namespace wip7vp4.law
  sort Leaf
    entity l1
    entity l2
  end

  sort Magma
    sort T = ?
    operation op2(a: T, b: T) -> T
    rule op2(?a, ?b) <=> ?a @[simp]
  end

  sort Rival
    provides Magma[T = Leaf]
    operation op2(a: Leaf, b: Leaf) -> Leaf = b
  end

  rule r(?z) :- ?z <=> Magma.op2(l1(), l2())
end
"#;
    let mut kb = crate::common::load_kb_with(LAW);
    let shown = crate::common::shown_rows(&mut kb, "wip7vp4.law.r");
    assert_eq!(shown, vec![("l1".to_string(), true)], "the law's left projection");
}

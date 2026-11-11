//! WI-20260925-P7VP4 inferred a rule-body call's requirement as a condition of its clause;
//! proposal 060.1 stage 2 (WI-20261104-J9SSG) WITHDREW the inference: a rule takes a dictionary
//! only where it declares one, with the head's introducer and a guard (kernel-language §5.3).
//! Every program of this file is the one P7VP4 measured, rewritten to declare what its call
//! needs, and each row is driven to the answer it gave:
//!
//! ```text
//!   rule cmp(?a, ?b, ?c) :- WeakOrd.compare(?a, ?b, ?c)                       -- refused
//!   rule cmp[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], WeakOrd.compare(?a, ?b, ?c) -- answers
//! ```
//!
//! What the inference wove — a spec operation's call through its dictionary, an ordinary
//! operation's call through the slots of its chain — is woven now through the guard's
//! dictionary (`declared_guard_of`, `slot_route`), and a citation routes the caller's choice
//! to it as before. A call or goal at a type a head column reaches, which the clause declares
//! nothing at, is refused at load, naming the introducer and guard to write (the refusal rows:
//! the operand row's `r1` / `r2`, and `the_refusal_names_no_repair_that_is_not_one`). One at a
//! variable no head column reaches, which no caller can fix, reads its dictionary from the value
//! when it runs, as for a query (`an_unground_woven_call_delays`, `an_unground_slot_call_delays`,
//! the branch row's `pickFree`).
//!
//! ## Back-out
//!
//! The refusal rows FAIL with `infer_rule_body_requirements`' refusals backed out (the clause
//! loads, as it did with the inference). The declared rows FAIL with the guard's weave backed
//! out (`declared_guard_of` and `slot_route`'s `Guard` answering `None`): a call at the
//! clause's parameter is then refused as undeclared. A row's own note names what else it
//! measures; where a note says what an inferred read did, that is what the row first
//! measured, before the stage that withdrew it.
//!
//! ## Stated limits
//!
//! A requirement no argument names is refused in every position (the typer's refusal, before
//! the weave), and a bracket on a rule-body call names no repair (`the_refusal_names_no_-
//! repair_that_is_not_one`).

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

  -- the rule DECLARES the requirement its call needs
  rule cmp[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], WeakOrd.compare(?a, ?b, ?c)
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
        "  rule dbl[A](?x: A) :- Scale[T = A], PartialEq.eq(Scale.twice(?x), 6)\n  \
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

/// A CARRIER NOTHING BINDS. `rule answer(?r) :- Desc.describe(?x, ?r)` leaves `?x` free, at a
/// type no head column reaches: no caller can fix it, so the call's dictionary is found from
/// the value when it runs, as for a query, and nothing is declared (060.1 §4). The value never
/// comes, and the call waits: one UNDECIDED row with `?r` free, never `?r` bound to the
/// un-reduced call (WI-1057). So does the clause that declares it, `?x` a column at `A`,
/// queried with `?x` free: it waits on the guard's read. Its supplier-less twin is
/// `wi1043_bodyless_rule_body_test::an_unground_body_less_goal_binds_no_residual`. The first
/// half FAILS with the call at a local variable refused as a head column's is
/// (`type_reaches_the_head` answering yes); the declared half passes either way, by design.
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
        "one UNDECIDED row with `?r` free — the call waits on its carrier; got {rows:?}",
    );
    let declared = PROGRAM.replace(
        "rule answer(?r) :- Desc.describe(?x, ?r)",
        "rule answer[A](?x: A, ?r) :- Desc[T = A], Desc.describe(?x, ?r)",
    );
    let mut kb = crate::common::load_kb_with(&declared);
    let goal = crate::common::query_pattern_term(&mut kb, "wip7vp4.unground.answer(?x, ?r)");
    let solutions = kb.resolve(&[goal], &anthill_core::kb::resolve::ResolveConfig::default());
    assert!(
        solutions.len() == 1 && !solutions[0].is_definite(),
        "one UNDECIDED row — the guard's read waits on `?x`; got {} rows",
        solutions.len(),
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

  -- the rule DECLARES `sign`'s `requires`
  rule viaOp[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], Util.sign(?a, ?b, ?c)
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
  import anthill.prelude.{Int64, Bool, List, Error, EmptyStream, Relation, Ord, WeakOrd, PartialOrd, PartialEq, Eq}

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

  -- DEFAULTED spec ops (`twice`, `scaled`), bodied over the provider's `unit`
  sort Scale
    sort T = ?
    operation unit(x: T) -> Int64
    operation twice(x: T) -> Int64 = Int64.add(unit(x), unit(x))
    operation scaled(x: T, n: Int64) -> Int64 = Int64.add(unit(x), n)
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
///
/// The inner call fills a parameter that is no carrier of the outer's: since
/// WI-20261013-WF14Z a call's result types the slot it fills, so `Util.sign(Scale.twice(?x),
/// ?z, ?c)`, the row's first spelling, reads `sign`'s `A` as `twice`'s `Int64` and is decided
/// at load, not woven.
#[test]
fn a_call_nested_in_a_woven_call_is_woven_too() {
    let kb = crate::common::load_kb_with(&fix_program(
        "wip7vp4.nest",
        "  rule nested[A, B](?x: A, ?y: B, ?c) :- Scale[T = A], Scale[T = B], \
         Scale.scaled(?y, Scale.twice(?x), ?c)\n",
    ));
    let woven: Vec<(String, bool, Vec<String>)> = crate::common::body_calls(&kb, "wip7vp4.nest.nested")
        .into_iter()
        .filter(|(_, woven, _)| *woven)
        .collect();
    assert_eq!(
        woven,
        vec![
            ("scaled".to_string(), true, vec!["twice".to_string()]),
            ("twice".to_string(), true, Vec::new()),
        ],
        "the outer `scaled` is woven, holding the woven inner `twice`",
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

/// A DECLARED `Derived` beside a call to an operation of `Base`, which `Derived` requires: the
/// call answers `Leaf2`'s own `op`. The guard was `requires(Derived[T])`, grounded by that call
/// as an INHERITED witness, and the inference used to weave the call first (its spec, `Base`,
/// is not the written `Derived`), so the witness scan (plain applications only) found none —
/// "no such call in the rule body"; the row FAILED with `infer_rule_body_requirements` moved
/// back before `record_find_dictionary_grounding`. Proposal 060.1 §5 removed `requires(X)`, and
/// the introducer's guard needs no witness: the row passes either way now.
#[test]
fn a_written_requires_keeps_its_inherited_witness() {
    let mut kb = crate::common::load_kb_with(&fix_program(
        "wip7vp4.inherited",
        "  sort Base\n    sort T = ?\n    operation op(x: T) -> Int64\n  end\n  \
         sort Derived\n    sort T = ?\n    requires Base[T = T]\n  end\n  \
         sort Leaf2\n    entity leaf2\n    provides Base[T = Leaf2]\n    \
         provides Derived[T = Leaf2]\n    operation op(x: Leaf2) -> Int64 = 5\n  end\n  \
         rule viaDerived[A](?x: A, ?r) :- Derived[T = A], Base.op(?x, ?r)\n  \
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
        "  rule less[A](?a: A, ?b: A) :- WeakOrd[T = A], Util.isLess(?a, ?b)\n  \
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

/// A call inside a SCOPE — a bounded quantifier's body — whose carrier is bound only there has
/// its read beside it in the body, where `?e` is bound, and uncited the read derives `Rod`'s
/// instance from each element. FAILS with the read placed before the top-level goal instead
/// (measured with a temporary switch): there it names `?e` outside the quantifier, where `?e` is
/// never bound, and `sixOne`'s answer comes back conditional.
#[test]
fn a_call_inside_a_quantifier_reads_its_condition_in_the_body() {
    let mut kb = crate::common::load_kb_with(&fix_program(
        "wip7vp4.scope",
        "  rule allSix[A](?xs: List[T = A]) :- Scale[T = A], (forall ?e in ?xs: Scale.twice(?e, 6))\n  \
         rule sixOne(?x) :- allSix([rod(), rod()]), ?x <=> 1\n",
    ));
    assert_eq!(crate::common::one_definite_int(&mut kb, "wip7vp4.scope.sixOne"), Some(1), "each element doubled by value");
}

/// A cited slot call that must WAIT — its second argument is bound by a later goal. The
/// slot arm handed back the plain call, and the retry reduced it with no slots: the answer
/// was `Int64`'s own `-1` where the caller chose `Descending` (4), and the binding goal written
/// first gave 4 — goal order decided it. FAILS with the slot arm returning its plain call.
///
/// `?a` is bound by `same2` from a column the citation fills, so the clause types it at the
/// citing operation's `A`. Bound by `five(?a)` over `rule five(?x) :- ?x <=> 5`, as this row
/// first wrote it, `?a` is an `Int64` since WI-20261013-WF14Z (a rule goal reads its callee's
/// columns): `sign` is decided at load and the citation at `A` is refused.
#[test]
fn a_woven_slot_call_that_waits_keeps_its_slots() {
    let driver = "  rule same2(?x, ?y) :- ?x <=> ?y\n  \
                  rule late[A](?b: A, ?e: A, ?c) :- WeakOrd[T = A], Util.sign(?b, ?a, ?c), same2(?e, ?a)\n  \
                  sort Driver\n    \
                  operation citeLate[A](x: A, y: A) -> Int64 effects {Error, Error[EmptyStream]}\n      \
                  requires WeakOrd[T = A] = late(x, y).head.c\n    \
                  operation lateDesc() -> Int64 effects {Error, Error[EmptyStream]} =\n      \
                  citeLate[A = Int64, WeakOrd = Descending](1, 5)\n  \
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
                  rule rOrder[A](?b: A, ?y: A, ?c) :- WeakOrd[T = A], same2(?y, ?a), Util.sign(?a, ?b, ?c)\n  \
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
  rule viaBoth[A](?a: A, ?c) :- Score[T = A], ?b <=> 7, Util.both(?a, ?b, ?c)

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

/// An operation's own `requires` at arguments nothing binds, local to the clause: `free`'s call
/// is at a type no head column reaches, its slot found from the values when it runs (060.1 §4),
/// and it waits: one UNDECIDED row with `?c` free. Declared, `?s` and `?t` columns at `A`, and
/// queried with both free, the clause waits on its guard's read. The first half FAILS with a
/// slot at a local variable refused as a head column's is; the declared half passes either
/// way, by design.
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
    let mut kb = crate::common::load_kb_with(&fix_program(
        "wip7vp4.unground2",
        "  rule free[A](?s: A, ?t: A, ?c) :- WeakOrd[T = A], Util.sign(?s, ?t, ?c)\n",
    ));
    let goal = crate::common::query_pattern_term(&mut kb, "wip7vp4.unground2.free(?s, ?t, ?c)");
    let solutions = kb.resolve(&[goal], &anthill_core::kb::resolve::ResolveConfig::default());
    assert!(
        solutions.len() == 1 && !solutions[0].is_definite(),
        "one UNDECIDED row; got {} rows",
        solutions.len(),
    );
}

// ── Review fixes, round 2: each row drives one fix, and fails with it backed out ─────

/// An UNPINNED body-less spec op in a VALUE slot is the clause's condition, as at goal position
/// (WI-20261013-RYDNV): `mk`'s call is woven behind a `find_dictionary`, and `mkOne` derives
/// `Num`'s dictionary from the value. It got none — the inference read the call as symbolic
/// algebra there — which made a dot through another variable's requirement slot answer by the
/// values where its goal spelling answered through the citation
/// (`wi_0rrqp…::a_dot_through_another_variables_slot_is_the_call`). FAILS with that decline
/// restored: the call is not woven.
///
/// What it EVALUATES TO changed with WI-20260926-K4JGC. It was the term the rule wrote —
/// "symbolic algebra", kernel-language §5.3's "what the gate still declines" — and `?s` was
/// `Shape.circle(num(v: 1))`. Proposal 068 §1 retired that reading: an operation application
/// is a computation, and a body-less spec op at a ground carrier DISPATCHES by that carrier
/// wherever it is written, so `?s` is `Num.circle`'s `num(v: 9)`. FAILS with K4JGC backed
/// out: `?s` is the written term again.
#[test]
fn a_body_less_operand_is_the_clauses_condition() {
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

  rule mk[A](?r: A, ?s) :- Shape[T = A], ?s <=> Shape.circle(?r)
  rule mkOne(?s) :- mk(num(v: 1), ?s)
end
"#;
    let mut kb = crate::common::load_kb_with(PROGRAM);
    assert_eq!(
        crate::common::body_calls(&kb, "wip7vp4.symbolic.mk"),
        vec![
            ("circle".to_string(), true, Vec::new()),
            ("domain".to_string(), false, Vec::new()),
            ("find_dictionary".to_string(), false, Vec::new()),
            ("unify".to_string(), false, Vec::new()),
        ],
        "the body-less operand is woven behind its guard's `find_dictionary`, beside the \
         typed column's `domain` test",
    );
    let rows = crate::common::query_unary(&mut kb, "wip7vp4.symbolic.mkOne");
    let [(s, true)] = rows.as_slice() else {
        panic!("one definite row; got {rows:?}");
    };
    let functor = crate::common::entity_functor(&kb, s).map(|f| kb.local_name_of(f).to_string());
    let v = crate::common::entity_field(&kb, s, "v", 0);
    assert_eq!(
        (functor.as_deref(), crate::common::scalar_int(&kb, &v)),
        (Some("num"), Some(9)),
        "`?s` is `Num.circle`'s value `num(v: 9)`, dispatched by the ground carrier",
    );
}

/// A call in an `if` branch that is not taken costs its clause nothing. The call is its
/// clause's condition, and its read, before the goal, finds no `Scale` at `5`, an `Int64`: it
/// binds that absence, which only the `then` branch would read. `pick(false, 5, ?e)` takes the
/// `else`, so `pickOne` answers 1. (`twice` is a DEFAULTED spec op: a body-less one in a value
/// slot is symbolic data and gets no condition anywhere.) FAILS with a read under a form
/// failing on a missing provider, as a goal's read does: the read on `5` fails the clause, and
/// `pickOne` is empty.
#[test]
fn a_call_in_an_untaken_branch_costs_its_clause_nothing() {
    let mut kb = crate::common::load_kb_with(&fix_program(
        "wip7vp4.deferred",
        "  rule pick[A](?f, ?v: A, ?e) :- Scale[T = A], ?e <=> (if ?f then Scale.twice(?v) else 1)\n  \
         rule pickOne(?x) :- pick(false, rod(), ?e), ?x <=> 1\n",
    ));
    assert_eq!(crate::common::one_definite_int(&mut kb, "wip7vp4.deferred.pickOne"), Some(1), "the `else` calls nothing");
}

/// A call in an `|` BRANCH has its read beside it in the branch, so the read runs only where
/// that branch is taken, and the OTHER branch keeps its answers: `pickB(?x, ?c)` with `?x` free
/// answers `99`, definitely, by its second branch. (That a citation reaches the call is
/// `wi_rydnv_one_classification_test::a_call_in_a_branch_is_its_clauses_condition`.) FAILS with
/// the read placed before the top-level goal instead (measured with a temporary switch): it
/// waits on `?x`, which only the first branch uses, and `pickFree` has no definite answer. The
/// CONTROL, `pickRod`, answers `6` and `99` either way, by design: with `?x` bound the hoisted
/// read derives, and costs nothing.
#[test]
fn a_call_in_a_branch_reads_its_condition_in_the_branch() {
    let mut kb = crate::common::load_kb_with(&fix_program(
        "wip7vp4.branch",
        "  rule pickB[A](?x: A, ?c) :- Scale[T = A], (Scale.twice(?x, ?c) | ?c <=> 99)\n  \
         rule pickRod(?c) :- pickB(rod(), ?c)\n",
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
    // A goal at a variable no head column reaches loads, its dictionary read from the value
    // when it runs (060.1 §4). The declared requirement is the whole clause's, not one
    // branch's: with `?x` never bound the guard's read waits, and the `99` branch with it —
    // no definite answer, where the inferred read stood in the first branch alone.
    let mut kb = crate::common::load_kb_with(&fix_program(
        "wip7vp4.branchfree",
        "  rule pickB[A](?x: A, ?c) :- Scale[T = A], (Scale.twice(?x, ?c) | ?c <=> 99)\n  \
         rule pickFree(?c) :- pickB(?x, ?c)\n",
    ));
    let rows = crate::common::query_unary(&mut kb, "wip7vp4.branchfree.pickFree");
    assert!(
        !rows.is_empty() && rows.iter().all(|(_, d)| !*d),
        "the clause waits on its requirement, both branches with it: {rows:?}",
    );
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
    let driver = "  rule less[A](?a: A, ?b: A) :- WeakOrd[T = A], Util.isLess(?a, ?b)\n  \
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
  rule viaBoth[A](?a: A, ?c) :- Score[T = A], ?b <=> 7, Util.both(?a, ?b, ?c)

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
        "  rule viaVar[A](?x: A, ?r) :- Desc[T = A], Desc.describe(?x, ?r)\n  rule answer(?r) :- viaVar(leaf(), ?r)\n",
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
                  rule viaS[A](?a: A, ?b: A, ?s, ?c) :- WeakOrd[T = A], Util2.sign2(?a, ?b, ?s, ?c)\n  \
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
    provides Zeroable[T = Self] :- Zeroable[E] where
      operation zero() -> Int64 = Int64.add(Zeroable.zero[T = E](), 100)
      operation zeroPlus(n: Int64) -> Int64 = Int64.add(Int64.add(Zeroable.zero[T = E](), 100), n)
      operation tag(x: Self) -> Int64 = 9
    end
  end

  rule via[A](?x: A, ?r) :- require z: Zeroable[T = A], z.tag(?x, ?t), z.zeroPlus(?n, ?r), ?n <=> 1
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

/// A call with a CONCRETE carrier beside an open one is its clause's condition, as one whose
/// carriers are all open is (requirement-channel.md §5.2's conditional class: an element of the
/// instance is open, and the argument's value grounds it): `toN`'s `?u` is a `String`, the
/// second carrier of `Conv`, `?x` the first, and the call is woven. Its read asks the provision
/// at `(Meters, String)`, which `Meters`' row binds, and `go` answers `7`. It was left unwoven,
/// decided by the value — the concrete carrier read as deciding it (WI-20261013-RYDNV moved the
/// first assertion); the ANSWER passes either way since WI-20260925-PRVA2 (c).
#[test]
fn a_call_with_a_concrete_carrier_beside_an_open_one_is_its_clauses_condition() {
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

  rule toN[X](?x: X, ?r) :- Conv[A = X, B = String], ?u <=> "km", Conv.conv(?x, ?u, ?r)
  rule go(?r) :- toN(m(v: 3), ?r)
end
"#;
    let mut kb = crate::common::load_kb_with(MIXED);
    assert!(
        crate::common::body_calls(&kb, "wip7vp4.mixed.toN")
            .iter()
            .any(|(callee, woven, _)| callee == "conv" && *woven),
        "the call is woven: its open carrier is the clause's condition",
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
         rule lessH[A](?p, ?a: A, ?b: A) :- WeakOrd[T = A], ?p(?a), Util.isLess(?a, ?b)\n  \
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

  rule w[X](?c, ?x: X) :- Palette[T = X], Palette.warm(?c, ?x)
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
    let driver = "  rule lessN[A](?a: A, ?b: A) :- WeakOrd[T = A], Util.isLess(x: ?a, y: ?b)\n  \
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

// ── Stated limits, measured 2026-10-08: where a callee's requirement is not yet a condition ──

/// A sort `sort` whose `cite` cites `rule(x, y)` holding `WeakOrd[A]`, with a nullary entry
/// under each rival (`desc`, `asc`) and one that holds no dictionary (`plain`).
fn cite_driver(sort: &str, rule: &str) -> String {
    format!(
        "  sort {sort}\n    \
         operation cite[A](x: A, y: A) -> Int64 effects {{Error, Error[EmptyStream]}}\n      \
         requires WeakOrd[T = A] = {rule}(x, y).head.c\n    \
         operation desc() -> Int64 effects {{Error, Error[EmptyStream]}} =\n      \
         cite[A = Int64, WeakOrd = Descending](1, 5)\n    \
         operation asc() -> Int64 effects {{Error, Error[EmptyStream]}} =\n      \
         cite[A = Int64, WeakOrd = Ascending](1, 5)\n    \
         operation plain() -> Int64 effects {{Error, Error[EmptyStream]}} = {rule}(1, 5).head.c\n  \
         end\n"
    )
}

/// `(desc, asc, plain)` of a [`cite_driver`] sort of the loaded program — one interpreter for
/// the three: none of them may trap, and a trap fails the row at its own call.
fn cited(interp: &mut anthill_core::eval::Interpreter, ns: &str, sort: &str) -> (i64, i64, i64) {
    let mut run = |entry: &str| match interp.call(&format!("{ns}.{sort}.{entry}"), &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{sort}.{entry}: expected an Int64, got {other:?}"),
    };
    (run("desc"), run("asc"), run("plain"))
}

/// The refusals of a [`fix_program`] whose every clause in `clauses` is refused as a
/// rule-body goal no route discharges: each names `callee` and `WeakOrd`, and there is one
/// per clause — a clause that started to load takes one away.
fn refused_per_clause(ns: &str, decls: &str, clauses: &[&str], callee: &str) -> Vec<String> {
    let errs = crate::common::load_errors_of(&fix_program(ns, &format!("{decls}{}", clauses.concat())));
    crate::common::assert_refused_naming(
        &errs,
        &[callee, "anthill.prelude.WeakOrd", "RULE-body goal"],
        "a requirement at a rule variable, in a position the rule-body typer checks",
    );
    let refused = errs.iter().filter(|e| e.contains("RULE-body goal") && e.contains(callee)).count();
    assert_eq!(refused, clauses.len(), "one refusal per clause; got:\n{}", errs.join("\n"));
    errs
}

/// A sort that `requires`: its member's dictionary chain is its sort's, not its own.
const HOLDER: &str = "  sort Holder\n    sort A = ?\n    requires WeakOrd[T = A]\n    \
    operation hsign(x: A, y: A) -> Int64 = WeakOrd.compare(x, y)\n  end\n";

/// A RULE GOAL PASSES ITS CALLEE ITS CALLER'S DICTIONARY. `r` reaches the call through
/// `inner`, a goal of its body, and hands `inner` what its own citer handed it for `inner`'s
/// condition (060-implementation §7.3's S7, WI-20261102-ATVC1): the caller's `Descending`
/// reaches `inner` through `r` as it does cited directly, and uncited `inner` derives
/// `Int64`'s own. Before S7 the half through `r` answered `(-1, -1, -1)`. The DIRECT half
/// FAILS with the inference backed out (`-1, -1, -1`); the half through `r` FAILS with it or
/// with S7's pass backed out.
#[test]
fn a_rule_goal_passes_its_callee_the_callers_dictionary() {
    let ns = "wip7vp4.viarule";
    let body = format!(
        "  rule inner[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], WeakOrd.compare(?a, ?b, ?c)\n  \
         rule r[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], inner(?a, ?b, ?c)\n{}{}",
        cite_driver("Direct", "inner"),
        cite_driver("Through", "r"),
    );
    let mut interp = crate::common::interp_for(&fix_program(ns, &body));
    assert_eq!(
        cited(&mut interp, ns, "Direct"),
        (4, -4, -1),
        "cited directly, `inner` is handed the rival its caller chose",
    );
    assert_eq!(
        cited(&mut interp, ns, "Through"),
        (4, -4, -1),
        "through `r`, `inner` is handed the rival its caller chose",
    );
}

/// AN OPERATION'S OWN `requires` IS A CONDITION OF THE CLAUSE IN EVERY POSITION: `?c <=>
/// Util.sign(?a, ?b)` is woven like the goal form and answers through the caller's dictionary;
/// FAILS with the inference backed out (`-1, -1, -1`). As an operand of `=` — `?c =
/// Util.sign(?a, ?b)`, `PartialEq.eq(Util.sign(?a, ?b), ?c)` — the call gets the same
/// condition, and so it does under the introducer (WI-20261013-RYDNV, one classification per
/// call): it was refused there, for a requirement the clause's text does not determine,
/// while the goal and `<=>` spellings got the condition. What `=` answers over such an operand
/// is `=`'s: at literals the clause loads and its `=` is undecided, `?c` free — `=` never binds
/// (kernel-language §8.3), so the compare waits for `?c` — and so is a citation's answer of the
/// woven `=` spelling.
///
/// The rows of a `require[WeakOrd[T]]` beside the call — refused as one no body call grounds,
/// a bracket holding what its spec REQUIRES and not the spec (`scope_contract_covers_dep`) —
/// and of a `require[WeakOrd[T = Int64]]` beside two typed head bindings, which named no one
/// of them, went with the form (proposal 060.1 §5); the introducer's guard, `r5`, is the
/// requirement the clause declares.
#[test]
fn an_operations_own_requires_is_its_clauses_condition_in_every_position() {
    let ns = "wip7vp4.operand";
    let woven = format!(
        "  rule r[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], ?c <=> Util.sign(?a, ?b)\n  \
         rule lit(?c) :- ?c = Util.sign(1, 5)\n{}",
        cite_driver("Driver", "r"),
    );
    let mut interp = crate::common::interp_for(&fix_program(ns, &woven));
    assert_eq!(
        cited(&mut interp, ns, "Driver"),
        (4, -4, -1),
        "`sign`'s `WeakOrd[A]` is `r`'s condition where the call is a `<=>` operand",
    );
    let mut kb = crate::common::load_kb_with(&fix_program(ns, &woven));
    let rows = crate::common::query_unary(&mut kb, &format!("{ns}.lit"));
    assert!(
        rows.len() == 1 && !rows[0].1 && matches!(rows[0].0, Value::Var(_)),
        "at literals the clause loads and its `=` is undecided, `?c` free: {rows:?}",
    );
    let ns = "wip7vp4.operandeq";
    let errs = crate::common::load_errors_of(&fix_program(
        ns,
        "  rule r1(?a, ?b, ?c) :- ?c = Util.sign(?a, ?b)\n  \
           rule r2(?a, ?b, ?c) :- PartialEq.eq(Util.sign(?a, ?b), ?c)\n",
    ));
    for rule in ["r1.body", "r2.body"] {
        assert!(
            errs.iter().any(|e| e.contains(rule) && e.contains("a requirement of `WeakOrd` the clause declares")),
            "`{rule}`: the operand's call at an undeclared type is refused: {errs:?}",
        );
    }
    let kb = crate::common::load_kb_with(&fix_program(
        ns,
        "  rule r5[A](?a: A, ?b: A, ?c) :- WeakOrd[A], ?c = Util.sign(?a, ?b)\n  \
           rule r6[A](?a: A, ?b: A, ?c) :- WeakOrd[A], PartialEq.eq(Util.sign(?a, ?b), ?c)\n",
    ));
    for rule in ["r5", "r6"] {
        let woven = kb
            .rule_ids_by_qn(&format!("{ns}.{rule}"))
            .into_iter()
            .any(|rid| kb.rule_body_nodes(rid).iter().any(holds_woven_call));
        assert!(woven, "`{rule}`: the operand's call carries the clause's condition");
    }
}

/// A MEMBER OF A SORT THAT `requires` IS A CONDITION OF THE CLAUSE wherever its arguments are
/// rule variables the clause does not type — as a goal, in a value slot, under the introducer
/// — as `Util.sign` is (WI-20261013-RYDNV): `Holder`'s `WeakOrd[T = A]` at the `A` the
/// arguments carry is woven as the slots of `hsign`'s chain, and cited under a rival answers 4
/// / -4, uncited `Int64`'s own -1. It was refused in every position: the typer checked the
/// sort's requirement as an operation body's and refused it, and the inference read `Holder`, a
/// sort with a type parameter, as one whose members are dispatched, and wove nothing — with
/// the refusal switched off the clause loaded and answered -1 under both rivals. FAILS with the
/// sort's requirement checked as an operation body's again
/// (`sort_requirements_carried_by_arguments` answering no): refused; and with the inference
/// declining it as before (`woven_call_dispatches` read as `spec_op_call_parent`): -1, -1, -1.
/// (A `require[WeakOrd[T]]` beside the call held no requirement of `Holder`'s and was refused as
/// one no body call grounds; the form went with proposal 060.1 §5, and `memberintro` is the
/// clause's declared requirement.)
///
/// THE REPAIRS THE REFUSAL NAMED, each run, still answer: an argument whose type is known at
/// load pins the chain (`lit`, `Int64`'s own); and `hsign` called from an operation that
/// declares the requirement, that operation written as the clause's goal.
#[test]
fn a_member_of_a_sort_that_requires_is_its_clauses_condition() {
    for (ns, clause) in [
        ("wip7vp4.membergoal", "  rule r[A](?a: A, ?b: A, ?c) :- WeakOrd[A], Holder.hsign(?a, ?b, ?c)\n"),
        ("wip7vp4.memberval", "  rule r[A](?a: A, ?b: A, ?c) :- WeakOrd[A], ?c <=> Holder.hsign(?a, ?b)\n"),
    ] {
        let src = fix_program(ns, &format!("{HOLDER}{clause}{}", cite_driver("Driver", "r")));
        let mut interp = crate::common::interp_for(&src);
        assert_eq!(cited(&mut interp, ns, "Driver"), (4, -4, -1), "{ns}");
    }
    // A HEAD TYPED `Int64` PINS THE CHAIN (068-implementation §6.2, decision 1; 7D48J's
    // 2026-10-08 note, row 3): the clause reads the head's bound, so `hsign` is at `Int64` and
    // decided at load, as at literals — `Int64`'s own `-1` for `(1, 5)`. Read without the
    // bound, the clause was refused as the others are. FAILS with the head bound read as no
    // position (`settle_head_bounds`).
    let mut kb = crate::common::load_kb_with(&fix_program(
        "wip7vp4.memberhead",
        &format!(
            "{HOLDER}  rule m4(?a: Int64, ?b: Int64, ?c) :- Holder.hsign(?a, ?b, ?c)\n  \
             rule q4(?c) :- m4(1, 5, ?c)\n"
        ),
    ));
    assert_eq!(
        crate::common::one_definite_int(&mut kb, "wip7vp4.memberhead.q4"),
        Some(-1)
    );
    let ns = "wip7vp4.memberok";
    let repaired = format!(
        "{HOLDER}  sort Via\n    \
         operation hs[A](x: A, y: A) -> Int64 requires WeakOrd[T = A] = Holder.hsign(x, y)\n  \
         end\n  \
         rule r[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], Via.hs(?a, ?b, ?c)\n  \
         rule lit(?c) :- Holder.hsign(1, 5, ?c)\n{}",
        cite_driver("Driver", "r"),
    );
    let mut interp = crate::common::interp_for(&fix_program(ns, &repaired));
    assert_eq!(
        cited(&mut interp, ns, "Driver"),
        (4, -4, -1),
        "through an operation that declares the requirement, written as a goal",
    );
    let mut kb = crate::common::load_kb_with(&fix_program(ns, &repaired));
    assert_eq!(
        crate::common::one_definite_int(&mut kb, &format!("{ns}.lit")),
        Some(-1),
        "at literals the chain is pinned at load: `Int64`'s own `compare`",
    );
}

/// A REQUIREMENT NO ARGUMENT NAMES IS REFUSED, IN EVERY POSITION (WI-20261013-RYDNV, the
/// refused class): `mk`'s `WeakOrd[T = B]` is at a parameter no argument carries and nothing
/// fixes, so no value could derive it and no condition of the clause can be read for it —
/// refused at the goal and in a value slot, as an operation body calling `Mk.mk()` is (there
/// for the unconstrained `B` itself). It loaded, got no condition, and answered from a body
/// that never reads the slot. FAILS with the requirement left to the clause whether or not an
/// argument carries it (`own_requirements_carried_by_arguments`): both load and answer 5.
#[test]
fn a_requirement_no_argument_names_is_refused_in_every_position() {
    let decl = "  sort Mk\n    operation mk[B]() -> Int64 requires WeakOrd[T = B] = 5\n  end\n";
    for (spelling, clause) in [("goal", "  rule five(?c) :- Mk.mk(?c)\n"), ("value", "  rule five(?c) :- ?c <=> Mk.mk()\n")] {
        crate::common::assert_refused_naming(
            &crate::common::load_errors_of(&fix_program("wip7vp4.unanchored", &format!("{decl}{clause}"))),
            &["wip7vp4.unanchored.Mk.mk", "nothing in the clause determines which `anthill.prelude.WeakOrd`"],
            spelling,
        );
    }
    let errs = crate::common::load_errors_of(&fix_program(
        "wip7vp4.unanchoredop",
        &format!("{decl}  sort User\n    operation use() -> Int64 = Mk.mk()\n  end\n"),
    ));
    crate::common::assert_refused_naming(
        &errs,
        &["expected a type for 'B', got unconstrained"],
        "an operation body is refused for the parameter nothing fixes",
    );
}

/// THE REFUSAL NAMES NO REPAIR THAT IS NOT ONE, each one run. A bare `size(?ls, ?n)` owes
/// `FiniteCollection`'s `Iterable[…]` and is refused. The refusal named a bracket of the
/// REQUIREMENT's spec, `require[Iterable[…]]`, which holds nothing — a bracket holds what
/// its spec requires — and ended with the tail every such refusal gets, offering an explicit
/// type argument, which a rule-body call refuses. It names the callee's spec, and no tail:
///   * the advised instance written at the call, `FiniteCollection[C = List[T =
///     String]].size(…)`, loads and answers the list's size, and so does an argument whose
///     type is known at load (`pinned`);
///   * the type argument the tail offered is a load error.
/// (The advice was the clause's `require[FiniteCollection[…]]` until proposal 060.1 §5
/// removed that form; the guard at the head's introducer holds what it held, and is run here.
/// The row also ran the `require[Iterable[…]]` advised before, refused.)
/// FAILS with the advice naming the requirement's spec again, and with the tail appended
/// again; the verdicts pass either way
/// (`wi_nx4fd_functional_relation_row_param_test::the_woven_spelling_is_the_repair` is the
/// written instance's own row).
#[test]
fn the_refusal_names_no_repair_that_is_not_one() {
    let program = |clause: &str| {
        format!(
            "namespace wip7vp4.advice\n  \
             import anthill.prelude.{{Int64, String, List, FiniteCollection, Iterable}}\n  \
             import anthill.prelude.FiniteCollection.{{size}}\n  \
             rule sized(?ls, ?n) :- {clause}(?ls, ?n)\n  \
             rule two(?n) :- sized([\"a\", \"b\"], ?n)\n  \
             rule pinned(?n) :- size([\"a\", \"b\"], ?n)\nend\n"
        )
    };
    let bare = crate::common::load_errors_of(&program("size"));
    crate::common::assert_refused_naming(
        &bare,
        &[
            "RULE-body goal",
            "Declare `FiniteCollection` at a type parameter the head introduces",
            "`rule r[C](?x: C, …) :- FiniteCollection[…]`",
            "write the instance at the call, `FiniteCollection[…].size(…)`",
            "pin the element at this call",
        ],
        "the bare goal is refused and told the guard and the instance that hold `Iterable`",
    );
    assert!(
        !bare.iter().any(|e| e.contains("`Iterable[…].size(…)`") || e.contains("explicit type argument")),
        "neither an instance that holds nothing nor a type argument is advised: {bare:?}",
    );
    let mut kb = crate::common::load_kb_with(&program("FiniteCollection[C = List[T = String]].size"));
    assert_eq!(crate::common::one_definite_int(&mut kb, "wip7vp4.advice.two"), Some(2));
    assert_eq!(crate::common::one_definite_int(&mut kb, "wip7vp4.advice.pinned"), Some(2));
    // The guard the advice names, run.
    let guarded = program("size").replace(
        "rule sized(?ls, ?n) :- size(?ls, ?n)",
        "rule sized[C](?ls: C, ?n) :- FiniteCollection[C = C], size(?ls, ?n)",
    );
    let mut kb = crate::common::load_kb_with(&guarded);
    assert_eq!(crate::common::one_definite_int(&mut kb, "wip7vp4.advice.two"), Some(2));
    crate::common::assert_refused_naming(
        &crate::common::load_errors_of(&program("size[C = List[T = String]]")),
        &["call-site type arguments"],
        "the type argument the tail offered is no rule-body spelling",
    );
}

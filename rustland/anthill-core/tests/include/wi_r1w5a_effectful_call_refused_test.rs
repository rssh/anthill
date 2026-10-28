//! WI-20261013-R1W5A (068 C1c, second part) — A CALL IN A RULE BODY WHOSE TYPED ROW HOLDS AN
//! EFFECT OTHER THAN `Error` IS REFUSED AT LOAD (kernel-language §5.3): a rule body performs no
//! effect. The row is the call's as an operation body types it (the first part,
//! `wi_r1w5a_call_typed_as_an_operation_body_test`), with what it binds itself masked as at an
//! operation's boundary — a `let`'s own resource, and a fresh region the call's value cannot
//! carry — and an open row variable is no effect. `Modify[result]`, a fresh cell the call hands
//! back, counts. Before, a write through a host function that performs it itself ran
//! (`hofWR` answered 9), a read that asks a handler was declined at run time, and a goal on an
//! effectful operation found no clause and failed, so `not(stamp(3))` held.
//!
//! A FUNCTION A RULE HANDS OVER IS HELD TO ITS OWN ROW (user, 2026-10-23): to a relation —
//! which applies it, if at all, in a clause that cannot see whose it is — and to an operation
//! whose row it leaves open, a callback that writes its own parameter binding no row
//! parameter. `applies(lambda () -> now(), ?r)` over `rule applies(?f, ?r) :- applyThunk(?f,
//! ?r)` and `useVia(?c, lambda (x) -> Cell.set(x, 9), ?u)` are refused; `applies` itself, and
//! a pure function handed over, load. It answered nothing before, silently: a function
//! handed to a relation through its head does not reach the call.
//!
//! RUN TIME KEEPS THE DECLINE for a goal no typer sees — a query's, or one a rule builds at run
//! time (`?p(?x, ?r)` over an operation it passes as data): such a goal on an effectful
//! operation is undecided, the decline reported as the bridge reports one, where it failed.
//!
//! THE FUNCTION IS FOUND WHERE THE CLAUSE KNOWS IT (user, 2026-10-23): written in the goal,
//! an operation's result, a side of `<=>` (`?f <=> (lambda () -> now())`, which types `?f`, as
//! does a list or a value holding one), a relation's column (`giveF(?f)`), or a value of a
//! data sort whose field holds one (`?b <=> box(f: …)`). A relation whose column already
//! holds such a function is not handed it: it can apply none.
//!
//! Not this part's, and measured on the way (2026-10-23, the same on 083cb6b8): a closure
//! handed to another relation through its head answers nothing, pure or not; a constraint's
//! goal is not walked by this typing (WI-20261023-76KZN).
//!
//! ## Back-out
//!
//! Each piece made a no-op in place under a switch of its own, one optimized build, the whole
//! `wi_tests` binary run under each (measured 2026-10-23):
//!
//! | backed out | fails |
//! |---|---|
//! | the refusal (`refuse_performed_effects`) | `an_effectful_call_written_in_a_rule_body_is_refused_at_load`, `a_call_beneath_an_entered_call_is_refused_once`, and the written clause beside each moved row: `wi_9wvt7_clock_handler…::a_clock_read_written_in_a_rule_body_is_refused_at_load`, `wi_9wvt7_reify_rule_body…::an_effectful_thunk_is_refused_at_load`, `wi_dqd5w…::a_concretely_effectful_bool_op_is_still_refused`, `wi_nx4fd…::a_concretely_effectful_op_is_still_refused_at_arity_plus_one`, `wi_nfxpz…::a_state_effect_beside_error_still_refuses` |
//! | at a body-less spec operation's call, the walk's recursing shape | `an_effectful_call_written_in_a_rule_body_is_refused_at_load` (`viaReify`, `viaMap`), and the clock and reify rows above |
//! | once: an effect a call beneath reported is skipped | `a_call_beneath_an_entered_call_is_refused_once` |
//! | an equation's guard left to the rewrite gate | `an_equations_guard_is_refused_by_the_rewrite_gate_alone` |
//! | a `let`'s own resource masked (`external_effects`) | `a_let_keeping_its_cell_to_itself_loads` |
//! | a fresh region the value cannot carry masked | `a_let_keeping_its_cell_to_itself_loads` |
//! | `Error` no effect | the stdlib does not load (7 650 tests): its rule bodies call `Error`-rowed operations (`Filesystem.status`) |
//! | an open row no effect | 12: `a_function_value_and_an_open_row_load` and the first row here, `wi_dqd5w…::an_unground_spec_op_goal_still_suspends`, `wi_nx4fd` ×2, `wi_p7vp4…::the_refusal_names_no_repair_that_is_not_one`, `wi_shed7` ×3, `wi_x9pb4` ×3 |
//! | the run-time decline (`effectful_goal_declined`) | 14: `an_effectful_goal_built_at_run_time_is_undecided`, `a_drained_relation_over_a_declined_goal_names_the_effect`, `wi_9wvt7_clock_handler` ×9, `wi_9wvt7_review5`, and `wi_dqd5w`'s and `wi_nx4fd`'s query rows |
//! | the decline a schedule, not a fault (an unhandled effect scheduled again, 9WVT7's back-out) | 15: those 14 but `wi_9wvt7_clock_handler…::a_clock_read_at_run_time_is_not_performed`, and that file's two bridge rows, the const read and the guarded member |
//! | a goal's call error the goal's (`rewritten_functional_goal`) | `a_goal_and_its_value_spelling_are_refused_alike` |
//! | a function handed to a relation (`refuse_handed_functions`) | `an_effectful_call_written_in_a_rule_body_is_refused_at_load` at `handsLambda`, `handsColumn`, `handsValue`, `handsInData`, `handsUnderNot`, `handsInOr`; `two_functions_handed_in_one_goal_are_two_refusals` |
//! | a function handed to an operation whose row stays open (`refuse_performed_effects`' second half) | `an_effectful_call_written_in_a_rule_body_is_refused_at_load` at `writesOwnParam`, `storeWriter` |
//! | only a parameter the call applies (`applied_function_args`) | `a_function_the_call_does_not_apply_loads` |
//! | once per place, not per atom (`push_rule_body_effect`'s span test) | `two_functions_handed_in_one_goal_are_two_refusals` |
//! | a side of `<=>` that holds a lambda typing the other (`LatePosition::LambdaValue`) | `an_effectful_call_written_in_a_rule_body_is_refused_at_load` at `handsBound`, `handsBoundList`, `handsGiven` (`giveF`'s column is no function then); `a_column_that_holds_the_function_is_not_handed_it` |
//! | what a type holds read past its arrow — fields, type arguments (`effects_held`) | `an_effectful_call_written_in_a_rule_body_is_refused_at_load` at `handsBoundList`, `handsHolder` |
//! | a field's row read at the type's argument (`/code-review`'s finding, measured on the CLI before the fix) | `an_effectful_call_written_in_a_rule_body_is_refused_at_load` at `handsParamHolder`, `handsWrittenHolder` |
//! | a column that holds the function not handed it (`refuse_handed_functions`' `given`) | `a_column_that_holds_the_function_is_not_handed_it` |
//! | the decline's reading strict on `Bool`, its effect named by the member's head (the two `/code-review` findings, measured on the CLI before the fix) | `an_effectful_goal_built_at_run_time_is_undecided`: `pick(true)` answers nothing, `stampIf(true, ?r)` names `EffectExpression.guarded` |
//!
//! NOT DRIVEN, and said rather than claimed: the refusal at a goal whose call an equation
//! rewrites (`rewritten_functional_goal`'s typed call) fails no row backed out. An equation
//! whose right side names an operation with an effect is refused by the rewrite gate, and one
//! that reaches it by a dot is refused where the rewrite fires, so the rewritten call it types
//! holds none.
//!
//! CONTROLS, green under every back-out: `a_callee_keeping_its_cell_to_itself_runs`,
//! `a_function_value_and_an_open_row_load`, `a_pure_goal_built_at_run_time_answers`,
//! `a_pure_function_handed_over_loads`; `a_function_the_call_does_not_apply_loads` passes
//! under all but its own.

use crate::common::{
    assert_refused_naming, fault_messages, load_errors_of, load_kb_with, query_pattern_term,
    query_unary,
};
use anthill_core::eval::Value;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term_view::TermView;

const PROGRAM: &str = r#"
namespace test.r1w5a.eff
  import anthill.prelude.{Int64, String, Bool, Unit, Cell, Error, Result, List, Option}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Time.{now, Clock}
  import anthill.prelude.PartialEq.{eq}
  import anthill.kernel.{or}
  import anthill.persistence.{Store}

  sort Boom
    entity boom(why: String)
  end
  sort St
    entity st(n: Int64)
    operation stampIt(s: St) -> String effects {Clock} = now()
  end

  operation mkVia[Rho](f: () -> Cell[V = Int64] @ {Rho}) -> Cell[V = Int64] effects {Rho} = f()
  operation useVia[Rho](c: Cell[V = Int64], k: (Cell[V = Int64]) -> Unit @ {Rho}) -> Unit effects {Rho} = k(c)
  operation applyThunk[Rho](f: () -> String @ {Rho}) -> String effects {Rho} = f()
  operation plainStamp() -> String effects {Clock} = now()
  operation stamp() -> Int64 effects {Clock} = 3
  operation stampAt(n: Int64) -> String effects {Clock} = now()
  operation stampOr(n: Int64) -> String effects {Clock, Error[Boom]} =
    if n < 0 then Error.raise(boom("negative")) else now()
  operation loudFlag(x: Int64) -> Bool effects {Clock} = x === 1
  operation stampIf(b: Bool) -> String effects { Clock :- eq(b, true) } =
    if b then now() else "none"
  operation pick[T](x: T) -> T effects {Clock} = x
  operation id(x: String) -> String = x
  operation boomNow() -> Int64 effects {Error[Boom]} = Error.raise(boom("neg"))
  operation localCell(n: Int64) -> Int64 =
    let c = Cell.new(n)
    let _ = Cell.set(c, n + 6)
    Cell.get(c)

  operation withStore[Rho](s: Store, f: (s: Store) -> Bool @ {Rho}) -> Bool effects {Rho} = f(s)
  operation clockThunk() -> () -> String @ {Clock} = lambda () -> now()
  operation pureThunk() -> () -> String = lambda () -> "x"
  sort Box
    entity box(f: () -> String @ {Clock})
  end
  sort PBox
    entity pbox(f: () -> String)
  end
  sort Box2
    effects R = ?
    entity box2(f: () -> String @ {R})
  end

  -- A relation that applies the function in its column; it loads, the function its caller
  -- hands it is judged where it is handed.
  rule applies(?f, ?r) :- applyThunk(?f, ?r)
  rule holds(?b, ?r) :- ?r <=> "x"
  -- A relation whose column holds such a function: it gives it, and can apply none.
  rule giveF(?f) :- ?f <=> (lambda () -> now())

  -- A goal built at run time: `?p(?x, ?r)` applies the operation a rule passes as data.
  rule apply2(?p, ?x, ?r) :- ?p(?x, ?r)
  rule viaRuntime(?r) :- apply2(stampAt, 1, ?r)
  rule viaRuntimeNot() :- not(apply2(stampAt, 1, "2000"))
end
"#;

/// Each clause, loaded beside [`PROGRAM`], is refused once, naming the call and the effect.
/// 7D48J's rows (2026-10-16) and this ticket's 2026-10-21 row, then the placements a call
/// takes in a rule body.
const REFUSED: [(&str, &str, &str); 36] = [
    // A field written over the sort's own row parameter is read at the argument the value's
    // type gives it.
    (
        "rule handsParamHolder(?r) :- ?b <=> box2(f: lambda () -> now()), holds(?b, ?r)",
        "a function handed to `test.r1w5a.eff.holds`",
        "Clock",
    ),
    (
        "rule handsWrittenHolder(?r, ?b: Box2[R = {Clock}]) :- holds(?b, ?r)",
        "a function handed to `test.r1w5a.eff.holds`",
        "Clock",
    ),
    // A side of `<=>` or `=` gives the other its type, bare or in parentheses
    // (WI-20261023-2F9HY).
    (
        "rule handsBound(?r) :- ?f <=> (lambda () -> now()), applies(?f, ?r)",
        "a function handed to `test.r1w5a.eff.applies`",
        "Clock",
    ),
    (
        "rule handsBoundBare(?r) :- ?f <=> lambda () -> now(), applies(?f, ?r)",
        "a function handed to `test.r1w5a.eff.applies`",
        "Clock",
    ),
    (
        "rule handsEq(?r) :- ?f = (lambda () -> now()), applies(?f, ?r)",
        "a function handed to `test.r1w5a.eff.applies`",
        "Clock",
    ),
    (
        "rule handsEqBare(?r) :- ?f = lambda () -> now(), applies(?f, ?r)",
        "a function handed to `test.r1w5a.eff.applies`",
        "Clock",
    ),
    (
        "rule handsBoundList(?r) :- ?l <=> [lambda () -> now()], holds(?l, ?r)",
        "a function handed to `test.r1w5a.eff.holds`",
        "Clock",
    ),
    (
        "rule handsHolder(?r) :- ?b <=> box(f: lambda () -> now()), holds(?b, ?r)",
        "a function handed to `test.r1w5a.eff.holds`",
        "Clock",
    ),
    (
        "rule handsGiven(?r) :- giveF(?f), applies(?f, ?r)",
        "a function handed to `test.r1w5a.eff.applies`",
        "Clock",
    ),
    (
        "rule storeWriter(?s, ?r) :- withStore(?s, lambda (s) -> Store.flush(s, []), ?r)",
        "a function handed to `test.r1w5a.eff.withStore`",
        "Modify[T = s]",
    ),
    (
        "rule handsLambda(?r) :- applies(lambda () -> now(), ?r)",
        "a function handed to `test.r1w5a.eff.applies`",
        "Clock",
    ),
    (
        "rule handsColumn(?r) :- clockThunk(?f), applies(?f, ?r)",
        "a function handed to `test.r1w5a.eff.applies`",
        "Clock",
    ),
    (
        "rule handsValue(?r) :- applies(clockThunk(), ?r)",
        "a function handed to `test.r1w5a.eff.applies`",
        "Clock",
    ),
    (
        "rule handsInData(?r) :- holds(box(f: lambda () -> now()), ?r)",
        "a function handed to `test.r1w5a.eff.holds`",
        "Clock",
    ),
    (
        "rule handsUnderNot(?r) :- not(applies(lambda () -> now(), ?r))",
        "a function handed to `test.r1w5a.eff.applies`",
        "Clock",
    ),
    (
        "rule handsInOr(?r) :- or(applies(lambda () -> now(), ?r), ?r <=> \"y\")",
        "a function handed to `test.r1w5a.eff.applies`",
        "Clock",
    ),
    (
        "rule writesOwnParam(?c, ?u) :- useVia(?c, lambda (x) -> Cell.set(x, 9), ?u)",
        "a function handed to `test.r1w5a.eff.useVia`",
        "Modify[T = x]",
    ),
    (
        "rule hofWR(?v) :- mkVia(lambda () -> Cell.new(3), ?c), \
         useVia(?c, lambda (x) -> Cell.set(x, 9), ?u), Cell.get(?c, ?v)",
        "the call `test.r1w5a.eff.mkVia`",
        "Modify[T = result]",
    ),
    (
        "rule hofRW(?v) :- mkVia(lambda () -> Cell.new(3), ?c), Cell.get(?c, ?v), \
         useVia(?c, lambda (x) -> Cell.set(x, 9), ?u)",
        "the call `test.r1w5a.eff.mkVia`",
        "Modify[T = result]",
    ),
    (
        "rule mk(?c) :- mkVia(lambda () -> Cell.new(3), ?c)",
        "the call `test.r1w5a.eff.mkVia`",
        "Modify[T = result]",
    ),
    (
        "rule reifyErr(?r, ?v) :- mkVia(lambda () -> Cell.new(3), ?c), \
         Error.reify(lambda () -> boomNow(), ?r), Cell.get(?c, ?v)",
        "the call `test.r1w5a.eff.mkVia`",
        "Modify[T = result]",
    ),
    (
        "rule viaHof(?r) :- applyThunk(lambda () -> now(), ?r)",
        "the call `test.r1w5a.eff.applyThunk`",
        "Clock",
    ),
    (
        "rule inValueSlot(?r) :- ?r <=> plainStamp()",
        "the call `test.r1w5a.eff.plainStamp`",
        "Clock",
    ),
    ("rule direct(?r) :- now(?r)", "the call `anthill.prelude.Time.now`", "Clock"),
    ("rule notNow() :- not(now(\"2000\"))", "the call `anthill.prelude.Time.now`", "Clock"),
    (
        "rule notStamp() :- not(plainStamp(\"2000\"))",
        "the call `test.r1w5a.eff.plainStamp`",
        "Clock",
    ),
    ("rule notStamp3() :- not(stamp(3))", "the call `test.r1w5a.eff.stamp`", "Clock"),
    ("rule boolGoal() :- loudFlag(1)", "the call `test.r1w5a.eff.loudFlag`", "Clock"),
    (
        "rule viaReify(?r) :- Error.reify(lambda () -> stampOr(1), ?r)",
        "the call `anthill.prelude.Error.reify`",
        "Clock",
    ),
    (
        "rule viaMap(?r) :- List.mapElems(cons(1, nil()), lambda (x) -> now(), ?r)",
        "the call `anthill.prelude.List.mapElems`",
        "Clock",
    ),
    (
        "rule viaDot(?r) :- st(n: 3) = ?s, ?r <=> ?s.stampIt()",
        "the call `test.r1w5a.eff.St.stampIt`",
        "Clock",
    ),
    (
        "rule viaNested(?r) :- ?r <=> id(plainStamp())",
        "the call `test.r1w5a.eff.id`",
        "Clock",
    ),
    // An `if` is typed whole, as a `let` and a `match` are (WI-20261011-2S5FP).
    (
        "rule viaIf(?r) :- ?r <=> (if 1 < 2 then plainStamp() else \"x\")",
        "this expression",
        "Clock",
    ),
    (
        "rule viaLet(?r) :- ?r <=> (let x = plainStamp()  id(x))",
        "this expression",
        "Clock",
    ),
    (
        "rule viaMatch(?r) :- ?r <=> (match some(3) case some(v) -> plainStamp() case none -> \"n\")",
        "this expression",
        "Clock",
    ),
    (
        "rule escapes(?c) :- ?c <=> (let c = Cell.new(3)  c)",
        "this expression",
        "Modify[T = result]",
    ),
];

fn with(clause: &str) -> String {
    crate::common::replace_in_fixture(PROGRAM, "\nend\n", &format!("\n  {clause}\nend\n"))
}

/// The errors of a refusal of this ticket's kind.
fn effect_refusals(errs: &[String]) -> Vec<&String> {
    errs.iter()
        .filter(|e| e.contains("and a rule body performs no effect"))
        .collect()
}

/// THE ACCEPTANCE: each effectful call written in a rule body, and each effectful function it
/// hands over, is refused at load, once, naming the call and the effect. `hofWR` and `hofRW`
/// are refused twice, once for each: `mkVia` hands back a fresh cell, and the callback handed
/// to `useVia` writes its own parameter. `hofWR` answered 9 and `hofRW` 3, the write performed; `mk` bound
/// a cell; the clock reads were declined at run time; `now(?r)` answered nothing, silently, and
/// each negation held.
#[test]
fn an_effectful_call_written_in_a_rule_body_is_refused_at_load() {
    // Every clause is asked, and the ones that miss are named together, so a back-out is
    // measured row by row.
    let mut missed: Vec<String> = Vec::new();
    for (clause, call, effect) in REFUSED {
        let errs = load_errors_of(&with(clause));
        let named = effect_refusals(&errs)
            .into_iter()
            .filter(|e| {
                e.contains(&format!("{call}, which performs `{effect}`, and a rule body performs no effect"))
            })
            .count();
        if named != 1 {
            missed.push(format!("{clause}: {named} refusals there: {errs:?}"));
        }
    }
    assert!(missed.is_empty(), "each refused once:\n{}", missed.join("\n"));
}

/// Two functions handed in one goal are two refusals, each where it is written.
#[test]
fn two_functions_handed_in_one_goal_are_two_refusals() {
    let errs = load_errors_of(&with(
        "rule holds2(?a, ?b, ?r) :- ?r <=> 1\n  \
         rule twoSites(?r) :- holds2(lambda () -> now(), lambda () -> now(), ?r)",
    ));
    assert_eq!(effect_refusals(&errs).len(), 2, "{errs:?}");
}

/// CONTROL: a function at a parameter the call does not apply is not held to its row, as in
/// an operation body: `op2` performs `R1` alone, and `g`'s `R2` is fixed at `Clock`.
#[test]
fn a_function_the_call_does_not_apply_loads() {
    load_kb_with(&with(
        "operation op2[R1, R2](f: () -> Int64 @ {R1}, g: () -> Int64 @ {R2}) -> Int64 effects {R1} = f()\n  \
         rule unapplied(?f, ?x) :- op2(?f, lambda () -> stamp(), ?x)",
    ));
}

/// ONCE, where the call sits in an argument of a call this walk enters before it types the
/// whole atom: `=` over it, and an arithmetic operation. The enclosing call's row holds the
/// effect too.
#[test]
fn a_call_beneath_an_entered_call_is_refused_once() {
    for clause in [
        "rule viaEq(?r) :- plainStamp() = ?r",
        "rule viaArith(?n) :- ?n = stamp() + 1",
    ] {
        let errs = load_errors_of(&with(clause));
        assert_eq!(effect_refusals(&errs).len(), 1, "{clause}: refused once: {errs:?}");
    }
}

/// An equation's guard is the effectful-rewrite gate's, which refuses every operation it names
/// whose row holds any effect: one refusal, not two.
#[test]
fn an_equations_guard_is_refused_by_the_rewrite_gate_alone() {
    let errs = load_errors_of(&with(
        "operation gate(n: Int64) -> Int64 = 0\n  \
         rule gate(?n) <=> 0 :- String.length(plainStamp()) > ?n @[simp]",
    ));
    assert_refused_naming(
        &errs,
        &["rewrite not to mention potentially effectful operation `test.r1w5a.eff.plainStamp`"],
        "the rewrite gate refuses the guard",
    );
    assert!(effect_refusals(&errs).is_empty(), "the rewrite gate's alone: {errs:?}");
}

/// CONTROL: a callee that writes a cell it keeps to itself has a pure row (WI-314 masks the
/// local cell's `Modify`), and the rule runs it.
#[test]
fn a_callee_keeping_its_cell_to_itself_runs() {
    let mut kb = load_kb_with(&with("rule viaRule(?r) :- localCell(3, ?r)"));
    let rows = query_unary(&mut kb, "test.r1w5a.eff.viaRule");
    assert!(
        matches!(rows.as_slice(), [(v, true)] if v.literal_int64(&kb) == Some(9)),
        "localCell(3) answers 9: {rows:?}"
    );
}

/// CONTROL: a `let` in a rule body that keeps its cell to itself loads — the cell's `Modify`
/// is the `let`'s own, and the fresh region `Cell.new` hands back is masked where the
/// expression's value cannot carry it, as at an operation's boundary. Its twin that hands the
/// cell back is refused (`escapes` above).
///
/// A load verdict and no value: a `let` in a rule body's value slot, also in a call's argument
/// (`idI(let …)`), is bound as written and not evaluated (measured 2026-10-23, the same on
/// 083cb6b8; reported to the user, proposal 068's ground).
#[test]
fn a_let_keeping_its_cell_to_itself_loads() {
    load_kb_with(&with(
        "rule stays(?v) :- ?v <=> (let c = Cell.new(3)  Cell.get(c))\n  \
         rule staysWrite(?v) :- ?v <=> (let c = Cell.new(3)  let _ = Cell.set(c, 5)  Cell.get(c))",
    ));
}

/// A relation whose column holds the function gives it, and is not handed it: `giveF(?f)` is
/// no refusal, where `applies(?f, ?r)` beside it is.
#[test]
fn a_column_that_holds_the_function_is_not_handed_it() {
    load_kb_with(&with("rule receives(?r) :- giveF(?f), ?r <=> \"y\""));
    let errs = load_errors_of(&with("rule handsGiven(?r) :- giveF(?f), applies(?f, ?r)"));
    let refusals = effect_refusals(&errs);
    assert!(
        refusals.len() == 1 && refusals[0].contains("handed to `test.r1w5a.eff.applies`"),
        "{errs:?}"
    );
}

/// CONTROL: a pure function handed over loads — to a relation, and to an operation whose row
/// it binds to `{}`.
#[test]
fn a_pure_function_handed_over_loads() {
    load_kb_with(&with(
        "rule handsPure(?r) :- applies(lambda () -> \"x\", ?r)\n  \
         rule handsPureColumn(?r) :- pureThunk(?f), applies(?f, ?r)\n  \
         rule pureCallback(?c, ?u) :- useVia(?c, lambda (x) -> (), ?u)\n  \
         rule pureHolder(?r) :- ?b <=> pbox(f: lambda () -> \"x\"), holds(?b, ?r)\n  \
         rule pureParamHolder(?r) :- ?b <=> box2(f: lambda () -> \"x\"), holds(?b, ?r)",
    ));
}

/// CONTROL: a function value performs nothing until applied, and a row the clause leaves open
/// names no effect: both load, and the function value is an answer.
#[test]
fn a_function_value_and_an_open_row_load() {
    let mut kb = load_kb_with(&with(
        "rule fnValue(?f) :- ?f <=> (lambda () -> now())\n  \
         rule viaVar(?f, ?r) :- applyThunk(?f, ?r)",
    ));
    let rows = query_unary(&mut kb, "test.r1w5a.eff.fnValue");
    assert!(matches!(rows.as_slice(), [(_, true)]), "one definite answer: {rows:?}");
}

/// RUN TIME KEEPS THE DECLINE: a goal on an effectful operation that no typer saw — a query's,
/// and one a rule builds at run time — is undecided, the decline reported, where it found no
/// clause and failed; a negation over it is undecided, where it held. The decline reads a goal
/// as the typer does (`KnowledgeBase::operation_goal_reading`): `pick(true)`, whose result is a
/// type parameter, is the call. Found by `/code-review`: read strictly as a `Bool`, it failed
/// silently; and the guarded member was named `EffectExpression.guarded`, a row the operation
/// does not declare.
#[test]
fn an_effectful_goal_built_at_run_time_is_undecided() {
    let mut kb = load_kb_with(PROGRAM);
    for pattern in [
        "test.r1w5a.eff.stamp(3)",
        "not(test.r1w5a.eff.stamp(3))",
        "test.r1w5a.eff.stamp(?r)",
        "anthill.prelude.Time.now(?r)",
        "not(anthill.prelude.Time.now(\"2000\"))",
        "test.r1w5a.eff.loudFlag(1)",
        "not(test.r1w5a.eff.loudFlag(1))",
        "test.r1w5a.eff.viaRuntime(?r)",
        "test.r1w5a.eff.viaRuntimeNot()",
        // A guarded member is named by its label, not by its wrapper.
        "test.r1w5a.eff.stampIf(true, ?r)",
        // A result that may be a `Bool` is a reading, as the typer reads it.
        "test.r1w5a.eff.pick(true)",
    ] {
        let goal = query_pattern_term(&mut kb, pattern);
        let (solutions, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
        assert!(
            solutions.len() == 1 && !solutions[0].residual.is_empty() && stats.truncated,
            "{pattern}: one answer, undecided, the search incomplete: {} answers, truncated {}",
            solutions.len(),
            stats.truncated
        );
        assert!(
            stats.errors.iter().any(|e| e
                .message
                .contains("it performs `anthill.prelude.Time.Clock`, and a rule body performs no effect")),
            "{pattern}: the decline is reported: {:?}",
            stats.errors
        );
    }
}

/// A relation over such a goal, drained from an operation body, fails with the decline's
/// reason.
#[test]
fn a_drained_relation_over_a_declined_goal_names_the_effect() {
    let src = crate::common::replace_in_fixture(
        PROGRAM,
        "\nend\n",
        "\n  operation stampCount() -> Int64 effects {Error} = List.length(viaRuntime.takeN(10))\n  \
         rule countFromRule(?n) :- ?n <=> stampCount()\nend\n",
    );
    let messages = fault_messages(&src, "test.r1w5a.eff.countFromRule(?n)");
    assert!(
        messages.iter().any(|m| m.contains("`test.r1w5a.eff.stampCount` could not be evaluated")
            && m.contains("it performs `anthill.prelude.Time.Clock`")),
        "the drain's failure carries the declined effect: {messages:?}"
    );
}

/// CONTROL for the run-time rows: the same route over a pure operation answers.
#[test]
fn a_pure_goal_built_at_run_time_answers() {
    let src = crate::common::replace_in_fixture(
        PROGRAM,
        "\nend\n",
        "\n  operation pureAt(n: Int64) -> String = \"p\"\n  \
         rule viaRuntimePure(?r) :- apply2(pureAt, 1, ?r)\nend\n",
    );
    let mut kb = load_kb_with(&src);
    let rows = query_unary(&mut kb, "test.r1w5a.eff.viaRuntimePure");
    assert!(
        matches!(rows.as_slice(), [(Value::Str(s), true)] if s == "p"),
        "answers \"p\": {rows:?}"
    );
}

/// ONE CALL, ONE VERDICT IN BOTH SPELLINGS (the first part's, found here): a goal
/// `f(args, ?r)` is `?r <=> f(args)`, so an error typing that call is the goal's. Over an
/// equation whose right side reaches an effectful member by a dot, the value-slot spelling was
/// refused and the goal loaded: typed as written, it met no equation.
#[test]
fn a_goal_and_its_value_spelling_are_refused_alike() {
    let src = |clause: &str| {
        format!(
            r#"
namespace test.r1w5a.rw
  import anthill.prelude.{{Int64, String}}
  import anthill.prelude.Time.{{now, Clock}}
  sort Other
    entity other(v: Int64)
    operation risky(o: Other) -> String effects {{Clock}} = now()
  end
  operation trigger(o: Other) -> String
  rule trigger(?o) <=> ?o.risky() @[simp]
  {clause}
end
"#
        )
    };
    for clause in [
        "rule viaGoal(?r) :- trigger(other(v: 2), ?r)",
        "rule viaValue(?r) :- ?r <=> trigger(other(v: 2))",
    ] {
        assert_refused_naming(
            &load_errors_of(&src(clause)),
            &["Other.risky", "by a dot in its text"],
            clause,
        );
    }
}

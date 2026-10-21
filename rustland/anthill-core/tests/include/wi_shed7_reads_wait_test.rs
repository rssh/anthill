//! WI-20260925-SHED7 (proposal 068 §2 and §2.2, decided with the user 2026-10-21) — a
//! rule-body call RUNS until it READS a variable the rule has not bound, and a goal waiting
//! on a variable is asked again as soon as it is bound.
//!
//! THE CASE: a solver that reads its cells through `Stream.splitFirst` instead of writing
//! the list pattern did not finish. The typed head's `fill` generates `vs`, and the check
//! `splitFirst(?r3) <=> none()` should cut every list longer than three cells — but it waited
//! on its turn behind every goal the `fill` pushed in front of it, so it saw each list only
//! once the `fill` had finished it (wake-on-bind, 068 §2.2); and when it was asked it waited
//! again, because the bridge declined any argument holding an unbound variable, so
//! `splitFirst(cons(head: f(), tail: ?t))` waited for `?t` (reads, 068 §2). The `fill`
//! went on to every longer list and the search ended at the depth limit: `truncated`, an
//! unsatisfiable formula reported as undecided.
//!
//! THE RULE: the bridge hands a call's unbound variables to the interpreter
//! (`Interpreter::bridge_unknowns`), and the run SUSPENDS where it would read one — a
//! pattern position that tests it, a host function handed it, an `if` or a guard on it, a
//! dispatch on its carrier, a call through it, a requirement its type would decide — and
//! runs where it only passes one along. Each row in `every_read_waits` is a pair: the read
//! with the variable OPEN waits (one conditional row, no fault), and the same call with the
//! variable bound LATER in the body answers.
//!
//! BACK-OUT, measured one hook at a time in one build (temporary switches) over this file,
//! `wi_shed7_fillable_test`, `wi1037_*`, `wi_p7vp4_*` and `wi756_*`:
//!  * the bridge gate restored (no call with an unbound argument runs) — `splitPartial`,
//!    `insertFree`, `readBind`, `readWait`, `readUnsat`, and `wi756`'s
//!    `a_conclude_that_is_not_a_goal_shape_stays_unlowered`;
//!  * wake-on-bind removed — `readBind`, `readWait`, `readUnsat`; the count reset on a wake
//!    removed — `wi_shed7_fillable_test`'s `parPattern` (the typed head's type test, woken
//!    cell by cell, reached the residualization gate before the `fill` ran);
//!  * each read hook — the rows at `every_read_waits`; the bridge entry's dispatch check —
//!    `wi1037`'s `an_unbound_carrier_answers_nothing_rather_than_the_default`; an absent
//!    requirement slot — `wi_p7vp4`'s `an_unground_slot_call_delays`.

use anthill_core::kb::resolve::ResolveConfig;

const READS: &str = r#"
namespace shed7reads
  import anthill.prelude.{List, Int64, Bool, Error, Additive, Option, Pair, Stream, WeakOrd}
  import anthill.prelude.List.{cons, nil}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}

  sort Bit
    entity t
    entity f
  end

  sort Box
    entity box(v: Int64)
  end

  sort Ops
    operation firstIsOne(xs: List[T = Int64]) -> Bool =
      match xs
        case cons(1, _) -> true
        case _ -> false
    operation unbox(b: Box) -> Int64 =
      let box(v) = b
      v
    operation viaLambda(b: Box) -> Int64 =
      let g = lambda box(v) -> v
      g(b)
    operation pick(b: Bool) -> Int64 = if b then 1 else 2
    operation guarded(x: Int64, b: Bool) -> Int64 =
      match x
        case y | b -> 1
        case _ -> 2
    operation inc(x: Int64) -> Int64 = Int64.add(x, 1)
    operation applyTo(f: (x: Int64) -> Int64, x: Int64) -> Int64 = f(x)
  end

  -- a call that only PASSES an unbound variable along runs
  rule splitPartial(?x) :- ?l <=> cons(head: f(), tail: ?t), Stream.splitFirst(?l) <=> some(pair(fst: ?x, snd: ?r))
  rule splitOpen(?x)    :- Stream.splitFirst(?l) <=> some(pair(fst: ?x, snd: ?r))
  rule insertFree(?n)   :- List.insert(List.empty(), ?r) <=> ?l, List.length(?l) <=> ?n

  -- every READ of one waits, and answers once it is bound
  rule literalOpen(?r)   :- Ops.firstIsOne([?h]) <=> ?r
  rule literalLater(?r)  :- Ops.firstIsOne([?h]) <=> ?r, ?h <=> 1
  rule letOpen(?r)       :- Ops.unbox(?b) <=> ?r
  rule letLater(?r)      :- Ops.unbox(?b) <=> ?r, ?b <=> box(v: 7)
  rule lambdaOpen(?r)    :- Ops.viaLambda(?b) <=> ?r
  rule lambdaLater(?r)   :- Ops.viaLambda(?b) <=> ?r, ?b <=> box(v: 8)
  rule ifOpen(?r)        :- Ops.pick(?b) <=> ?r
  rule ifLater(?r)       :- Ops.pick(?b) <=> ?r, ?b <=> true
  rule guardOpen(?r)     :- Ops.guarded(5, ?b) <=> ?r
  rule guardLater(?r)    :- Ops.guarded(5, ?b) <=> ?r, ?b <=> false
  rule hostOpen(?r)      :- Ops.inc(?x) <=> ?r
  rule hostLater(?r)     :- Ops.inc(?x) <=> ?r, ?x <=> 3
  rule entryOpen(?r)     :- Int64.add(?x, 1) <=> ?r
  rule entryLater(?r)    :- Int64.add(?x, 1) <=> ?r, ?x <=> 3
  rule specOpen(?r)      :- Additive.add(2, ?y) <=> ?r
  rule specLater(?r)     :- Additive.add(2, ?y) <=> ?r, ?y <=> 3
  rule localOpen(?r)     :- Ops.applyTo(?f, 3) <=> ?r
  rule toStrOpen(?r)     :- Int64.to_string(?x) <=> ?r
  rule toStrLater(?r)    :- Int64.to_string(?x) <=> ?r, ?x <=> 42
  rule byValueOpen(?r)   :- ?a <=> 2, WeakOrd.compare(?a, ?b) <=> ?r
  rule byValueLater(?r)  :- ?a <=> 2, WeakOrd.compare(?a, ?b) <=> ?r, ?b <=> 5
  rule containsOpen(?r)  :- List.contains(cons(head: ?h, tail: nil()), t()) <=> ?r
  rule containsLater(?r) :- List.contains(cons(head: ?h, tail: nil()), t()) <=> ?r, ?h <=> t()
  rule lengthOpen(?r)    :- List.length(cons(head: t(), tail: ?rest)) <=> ?r
  rule lengthLater(?r)   :- List.length(cons(head: t(), tail: ?rest)) <=> ?r, ?rest <=> [f()]

  -- the solver that READS its cells, against the one that writes the pattern
  fact neg(t(), f())
  fact neg(f(), t())
  rule or2(?a, ?)  :- ?a <=> t()
  rule or2(?a, ?b) :- ?a <=> f(), ?b <=> t()

  rule readBind(vs: List[T = Bit])
    :- Stream.splitFirst(vs)  <=> some(pair(fst: ?p, snd: ?r1)),
       Stream.splitFirst(?r1) <=> some(pair(fst: ?q, snd: ?r2)),
       Stream.splitFirst(?r2) <=> some(pair(fst: ?r, snd: ?r3)),
       Stream.splitFirst(?r3) <=> none(),
       neg(?p, ?np), neg(?q, ?nq), neg(?r, ?nr),
       or2(?p, ?nq), or2(?q, ?r), or2(?np, ?nr)
  rule readWait(vs: List[T = Bit])
    :- Stream.splitFirst(vs)  <=> some(pair(fst: ?p, snd: ?r1)),
       Stream.splitFirst(?r1) <=> some(pair(fst: ?q, snd: ?r2)),
       Stream.splitFirst(?r2) <=> some(pair(fst: ?r, snd: ?r3)),
       Stream.splitFirst(?r3) <=> none(),
       ?p != ?q, ?q != ?r
  rule readUnsat(vs: List[T = Bit])
    :- Stream.splitFirst(vs)  <=> some(pair(fst: ?p, snd: ?r1)),
       Stream.splitFirst(?r1) <=> some(pair(fst: ?q, snd: ?r2)),
       Stream.splitFirst(?r2) <=> some(pair(fst: ?r, snd: ?r3)),
       Stream.splitFirst(?r3) <=> none(),
       ?p != ?q, ?q != ?r, ?p != ?r
  rule checkGiven(1)    :- readBind([t(), t(), f()])
  rule checkRefused(1)  :- readBind([t(), t(), t()])
  rule complete(?q)     :- readWait([t(), ?q, ?r])
end
"#;

/// The rows of `rule`, shown, with whether the search finished and what it faulted.
fn run(kb: &mut anthill_core::kb::KnowledgeBase, rule: &str) -> (Vec<(String, bool)>, bool, usize) {
    let qn = format!("shed7reads.{rule}");
    let goal = crate::common::query_pattern_term(kb, &format!("{qn}(?x)"));
    let (_, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
    let rows = crate::common::shown_rows(kb, &qn);
    (rows, !stats.truncated, stats.errors.len())
}

/// One undecided row with the variable still free, and no fault: the call WAITED.
fn waits(kb: &mut anthill_core::kb::KnowledgeBase, rule: &str) -> Result<(), String> {
    let (rows, _, faults) = run(kb, rule);
    if faults != 0 {
        return Err(format!("`{rule}`: a read of an unbound variable is no fault ({faults})"));
    }
    if rows.len() != 1 || rows[0].1 {
        return Err(format!("`{rule}`: one undecided row — the call waits — got {rows:?}"));
    }
    Ok(())
}

fn answers(kb: &mut anthill_core::kb::KnowledgeBase, rule: &str, want: &str) -> Result<(), String> {
    let (rows, finished, faults) = run(kb, rule);
    if faults != 0 || !finished || rows != vec![(want.to_string(), true)] {
        return Err(format!(
            "`{rule}`: expected `{want}`, definite, finished, no fault — got {rows:?}, \
             finished {finished}, {faults} fault(s)"
        ));
    }
    Ok(())
}

/// Every row's verdict, so a back-out names all the rows it moves rather than the first.
fn all(results: Vec<Result<(), String>>) {
    let failed: Vec<String> = results.into_iter().filter_map(Result::err).collect();
    assert!(failed.is_empty(), "{}", failed.join("\n"));
}

/// A call that only PASSES an unbound variable along runs: `List.splitFirst` reads the first
/// cell of `cons(head: f(), tail: ?t)`, not `?t`, and `List.insert` stores its element.
/// FAILS with the bridge's gate restored: `splitPartial` and `insertFree` wait.
/// `splitOpen` passes either way, by design: choosing the carrier of `?l` reads it.
#[test]
fn a_call_runs_until_it_reads() {
    let mut kb = crate::common::load_kb_with(READS);
    all(vec![
        answers(&mut kb, "splitPartial", "f"),
        waits(&mut kb, "splitOpen"),
        answers(&mut kb, "insertFree", "1"),
    ]);
}

/// Every READ of an unbound variable waits, and answers once the variable is bound. With the
/// hook named backed out, these rows fail (MEASURED) — the LATER row of a pair too, since it
/// asks its call once before the binding and that ask answers wrongly or faults:
/// the pattern record (`match_pattern`) or its consumers (`match_or_wait`) — `literal`,
/// `let`, `lambda`, `length`; the `if` condition — `if`; the `match` guard — `guard`; a
/// call through a local — `localOpen`; a host function (`call_host`) — `host`, `contains`
/// (`eq` answered `false`), `toStr` (the bridge's own host entry), `byValue` (a spec
/// implementation chosen by value at the bridge), and `wi_p7vp4`'s
/// `a_woven_slot_call_that_waits_keeps_its_slots`. `entry` and `spec` pass either way, by
/// design: the resolver evaluates `Int64.add` itself and waits on an unbound operand.
#[test]
fn every_read_waits() {
    let mut kb = crate::common::load_kb_with(READS);
    let mut results = Vec::new();
    for (open, later, want) in [
        ("literalOpen", "literalLater", "true"),
        ("letOpen", "letLater", "7"),
        ("lambdaOpen", "lambdaLater", "8"),
        ("ifOpen", "ifLater", "1"),
        ("guardOpen", "guardLater", "2"),
        ("hostOpen", "hostLater", "4"),
        ("entryOpen", "entryLater", "4"),
        ("specOpen", "specLater", "5"),
        ("containsOpen", "containsLater", "true"),
        ("lengthOpen", "lengthLater", "2"),
        ("toStrOpen", "toStrLater", "\"42\""),
        ("byValueOpen", "byValueLater", "-1"),
    ] {
        results.push(waits(&mut kb, open));
        results.push(answers(&mut kb, later, want));
    }
    results.push(waits(&mut kb, "localOpen"));
    all(results);
}

/// THE CASE: the solver that reads its cells finishes in every mode, at about the cost of the
/// one that writes `vs <=> [?p, ?q, ?r]` (MEASURED: 365 / 169 / 173 steps against 319 / 152
/// / 158). FAILS with wake-on-bind removed or the bridge's gate restored: `readBind`,
/// `readWait` and `readUnsat` are cut at the depth limit — the last an unsatisfiable formula
/// reported as undecided. `checkGiven`, `checkRefused` and `complete` pass either way, by
/// design: a given list is read, not generated.
#[test]
fn the_split_first_solver_finishes() {
    let mut kb = crate::common::load_kb_with(READS);
    let mut results = Vec::new();
    for (rule, models) in [
        ("readBind", vec!["[f, f, t]", "[t, t, f]"]),
        ("readWait", vec!["[f, t, f]", "[t, f, t]"]),
        ("readUnsat", vec![]),
    ] {
        let (rows, finished, faults) = run(&mut kb, rule);
        let mut got: Vec<String> = rows.iter().map(|(v, _)| v.clone()).collect();
        got.sort();
        results.push(
            if faults == 0 && finished && rows.iter().all(|(_, d)| *d) && got == models {
                Ok(())
            } else {
                Err(format!(
                    "`{rule}`: expected {models:?}, definite, finished, no fault — got {rows:?}, \
                     finished {finished}, {faults} fault(s)"
                ))
            },
        );
    }
    results.push(answers(&mut kb, "checkGiven", "1"));
    results.push(answers(&mut kb, "complete", "f"));
    all(results);
    let (rows, finished, _) = run(&mut kb, "checkRefused");
    assert!(rows.is_empty() && finished, "`checkRefused`: no model, decided: {rows:?}");
}

/// A RIGID variable — a `forall` binder's eigenvariable — is not one of the rule's unknowns:
/// nothing binds it, so a call over it stays the term it is (SYMBOLIC, kernel-language §8.3)
/// and the quantified goal is undecided, as before this change. FAILS with the bridge's
/// rigid decline backed out (MEASURED): the bridge runs `isPos(n)`, hands the eigenvariable
/// to `Int64.gt`, and both rows fault "expected Ord scalars of matching type".
#[test]
fn a_rigid_variable_keeps_the_call_symbolic() {
    const RIGID: &str = r#"
namespace shed7rigid
  import anthill.prelude.{Int64, Bool}
  sort Ops
    operation isPos(x: Int64) -> Bool = Int64.gt(x, 0)
    operation isNeg(x: Int64) -> Bool = Int64.lt(x, 0)
  end
  rule allPos(1) :- (forall(?n), Int64.gt(?n, 0) -: Ops.isPos(?n) <=> true)
  rule allNeg(1) :- (forall(?n), Int64.gt(?n, 0) -: Ops.isNeg(?n) <=> true)
end
"#;
    let mut kb = crate::common::load_kb_with(RIGID);
    for rule in ["allPos", "allNeg"] {
        let qn = format!("shed7rigid.{rule}");
        let goal = crate::common::query_pattern_term(&mut kb, &format!("{qn}(?x)"));
        let (_, stats) = kb.resolve_with_stats(&[goal], &ResolveConfig::default());
        assert!(stats.errors.is_empty(), "`{rule}`: no fault: {:?}", stats.errors);
        let rows = crate::common::shown_rows(&mut kb, &qn);
        assert_eq!(rows, vec![("1".to_string(), false)], "`{rule}`: undecided");
    }
}

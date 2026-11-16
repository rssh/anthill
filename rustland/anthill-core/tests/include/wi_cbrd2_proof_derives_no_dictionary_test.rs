//! A PROOF READS NO DICTIONARY FROM THE VALUES (WI-20261105-CBRD2). A guard is refuted, and a
//! precondition proved, while a load's operation bodies are typed, before its rule bodies are:
//! a rule such a proof runs has no requirement reads yet. `made[A = Int64, WeakOrd =
//! Descending](1, 5)` returns the relation of `rule cmp[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A],
//! WeakOrd.compare(?a, ?b, ?c)`; a guard reading its first row ran `WeakOrd.compare` with the
//! provider the values give, `Int64`'s own (`-1`), where the run takes `Descending` (`4`). So
//! `effects { Boom :- firstIs(r, 4) }` was refuted at `g(made[…](1, 5))`, and `Boom` dropped at
//! a call that incurs it; `requires firstIs(r, -1)` was proved at `h(made[…](1, 5))`, a
//! precondition the run violates. Inside a proof (`KnowledgeBase::gamma_proof_depth`) the eval bridge
//! derives no call's dictionaries from its arguments, and the proof is undecided where it
//! would need them.
//!
//! ## What fails with the change backed out
//!
//! Measured with a temporary switch (the bridge derives inside a proof), then removed. The
//! control is the switch unset: every row passes.
//!
//! * [`a_guard_reading_a_relation_a_rule_answers_reads_no_dictionary`] fails at `firstIs(r,
//!   4)`: the program loads clean.
//! * [`a_precondition_reading_a_relation_a_rule_answers_reads_no_dictionary`] fails at
//!   `firstIs(r, -1)`: the precondition is proved, the program loading clean.
//!
//! [`a_relation_needing_no_dictionary_is_still_decided`] passes either way by design.

use anthill_core::kb::resolve::bridge_derivations_by_this_thread;

use crate::common::{load_errors_of, load_stdlib_kb};

fn src(ns: &str, guard: &str, arg: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Error, EmptyStream, Relation, Ord, WeakOrd, Effect}}
  import anthill.prelude.PartialEq.{{eq}}
  sort Descending
    import anthill.prelude.Numeric.{{sub}}
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)
  end
  sort Boom
    entity Bang
    provides Effect[T = Boom]
  end
  rule cmp[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], WeakOrd.compare(?a, ?b, ?c)
  rule same(?k, ?c) :- ?c <=> ?k
  operation made[A](x: A, y: A) -> Relation[T = (c: Int64), E = {{Error}}]
    requires WeakOrd[T = A] = cmp(x, y)
  operation madeN(k: Int64) -> Relation[T = (c: Int64), E = {{Error}}] = same(k)
  operation firstIs(r: Relation[T = (c: Int64), E = {{Error}}], k: Int64) -> Bool
    effects {{Error, Error[EmptyStream]}} = eq(r.head.c, k)
  operation g(r: Relation[T = (c: Int64), E = {{Error}}]) -> Int64 effects {{ Boom :- {guard} }} = 0
  operation caller() -> Int64 = g({arg})
  operation h(r: Relation[T = (c: Int64), E = {{Error}}]) -> Int64 requires {guard} = 0
  operation precond() -> Int64 = h({arg})
  operation madeDesc() -> Int64 effects {{Error, Error[EmptyStream]}} =
    made[A = Int64, WeakOrd = Descending](1, 5).head.c
end
"#
    )
}

/// The load's errors and the dictionaries it derived from values, the shared base loaded first.
fn errors_and_derived(src: &str) -> (Vec<String>, usize) {
    drop(load_stdlib_kb());
    let before = bridge_derivations_by_this_thread();
    let errs = load_errors_of(src);
    (errs, bridge_derivations_by_this_thread() - before)
}

/// `made[…, WeakOrd = Descending](1, 5)`'s first row is `c = 4` when it runs. Neither
/// `firstIs(r, 4)` nor `firstIs(r, -1)` is decided at load, so `Boom` is owed at both, and each
/// as `h`'s precondition is unproved; and no dictionary is read from the values, `madeDesc`'s
/// `.head` guard included.
#[test]
fn a_guard_reading_a_relation_a_rule_answers_reads_no_dictionary() {
    for (n, guard) in ["firstIs(r, 4)", "firstIs(r, -1)"].into_iter().enumerate() {
        let program = src(
            &format!("test.cbrd2.pd.r{n}"),
            guard,
            "made[A = Int64, WeakOrd = Descending](1, 5)",
        );
        let (errs, derived) = errors_and_derived(&program);
        assert!(
            errs.iter().any(|e| e.contains("undeclared effect: Boom")),
            "{guard}: {errs:?}"
        );
        assert_eq!(derived, 0, "{guard}: a dictionary derived from the values");
    }
}

/// `h`'s `requires firstIs(r, -1)`, which the run violates, is not proved at `h(made[…](1, 5))`.
#[test]
fn a_precondition_reading_a_relation_a_rule_answers_reads_no_dictionary() {
    for (n, guard) in ["firstIs(r, -1)", "firstIs(r, 4)"].into_iter().enumerate() {
        let program = src(
            &format!("test.cbrd2.pd.p{n}"),
            guard,
            "made[A = Int64, WeakOrd = Descending](1, 5)",
        );
        let (errs, _) = errors_and_derived(&program);
        assert!(
            errs.iter().any(|e| e.contains("h.requires") && e.contains("precondition")),
            "{guard}: {errs:?}"
        );
    }
}

/// The control: `madeN(2)`'s rule needs no dictionary, and a proof still reads its first row,
/// `c = 2`: `firstIs(r, 4)` is refuted, owing nothing and refusing `h`'s precondition;
/// `firstIs(r, 2)` holds, owing `Boom` and proving it.
#[test]
fn a_relation_needing_no_dictionary_is_still_decided() {
    for (n, (guard, holds)) in [("firstIs(r, 4)", false), ("firstIs(r, 2)", true)].into_iter().enumerate() {
        let (errs, _) = errors_and_derived(&src(&format!("test.cbrd2.pd.t{n}"), guard, "madeN(2)"));
        let owes = errs.iter().any(|e| e.contains("undeclared effect: Boom"));
        let unproved = errs.iter().any(|e| e.contains("h.requires") && e.contains("precondition"));
        assert_eq!((owes, unproved, errs.len()), (holds, !holds, 1), "{guard}: {errs:?}");
    }
}

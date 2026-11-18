//! A LOAD'S PROOFS ARE MADE OVER ITS WHOLE PROGRAM, AS A LATER LOAD'S ARE OVER AN EARLIER ONE
//! (WI-20261117-8J8NG, kernel-language §5.3 and the proofs paragraph of §5.4). Typing an
//! operation body runs rules — a guard is refuted, a precondition proved — and a body's citation
//! is routed to the requirement reads of the clauses it cites. So a load types and elaborates
//! every rule before its bodies (`typing::elaborate_rules`), routes a citation where it is typed
//! (`typing::route_citation`), passes a law's goals the instances the law holds
//! (`rule_goal_routes`), and types a body a proof reaches before its turn there
//! (`typing::body_readiness`).
//!
//! MEASURED BEFORE, on main (2026-11-17, `0f5e444be`), each case in one load and in two — the
//! rules in an earlier, sealed load:
//!
//! * `rule cmp` run by the proof of `firstIs(made[A = Int64, WeakOrd = Descending](1, 5), k)`:
//!   undecided in one load (`Boom` owed and the precondition unproved, whatever `k`); in two,
//!   decided — `k = 4` holds, `k = -1` is refuted — but only with `made`, whose body cites
//!   `cmp`, in the earlier load too: its citation was routed at the end of the run.
//! * A law whose guard calls `nz[A](?b: A) :- EuclideanDomain[T = A], Additive[T = A],
//!   neq(?b, zero)`: undecided in one load AND in two — the law's goal was routed nothing in any
//!   load — and the two-load case overflowed a 2 MiB test thread at opt-level 0. That `nz`'s
//!   `neq` reads an inferred `PartialEq`, which nothing routes and a proof does not derive, so it
//!   stays undecided in every load after this ticket too, and no row here loads it: it now
//!   overflows a 2 MiB thread in one load as well, in the discrimination tree's recursive skip of
//!   a long key path (`SubstTree::skip_subtree_then_continue`). The rows declare `PartialEq`.
//! * `big(n) = n.gt(3)` written after the caller whose guard calls it: the load ABORTED
//!   ("unhandled Expr variant in eval"); written before, it loaded clean.
//!
//! ## What fails with the change backed out
//!
//! Measured one axis at a time over `wi_8j8ng`, `wi_cbrd2`, `wi_22s8n`, `wi_v0rpw`, `wi_5g28a` and
//! `wi_j9ssg`, on the shared base (2026-11-18, after `/code-review`); the control, nothing backed
//! out, passes every row.
//!
//! * The rule sweep after the bodies, as before: [`a_rule_a_proof_runs_is_elaborated_before_the_bodies`],
//!   [`a_laws_goal_is_passed_the_laws_instances`], `wi_22s8n`'s `guard_rows` and
//!   `precondition_rows`, and `wi_cbrd2_proof_derives_no_dictionary_test`'s guard and
//!   precondition rows.
//! * The contracts not typed ahead of the sweep (`type_contracts_ahead`):
//!   `wi_cbrd2_contract_member_goal_test::a_precondition_naming_a_member_is_proved_at_it` and
//!   `wi_cbrd2_effect_guard_comparison_test::a_rule_body_precondition_is_refuted_at_its_carriers_eq`,
//!   each on its count: a rule body's call is refuted at its callee's contract as typed.
//! * Every citation routed at the end of the run, none where its body is typed:
//!   [`a_rule_a_proof_runs_is_elaborated_before_the_bodies`] and the two `wi_cbrd2` rows above.
//! * A refused bracket's bare citation routed:
//!   `wi_j9ssg_rule_citation_bracket_test::a_bracket_on_a_paren_less_reference_is_refused`, a
//!   second refusal of the same bracket.
//! * A law's goals routed nothing: [`a_laws_goal_is_passed_the_laws_instances`] overflows a 2
//!   MiB test thread at opt-level 0 and aborts the binary — the proof the route spares.
//! * No body typed on demand, one the run has not reached answering "not typed":
//!   [`a_body_a_proof_runs_before_its_turn_is_typed_there`],
//!   [`a_rule_a_proof_runs_is_elaborated_before_the_bodies`] (the callers written before `made`),
//!   [`a_body_typed_from_a_guard_is_typed_as_at_its_turn`],
//!   [`a_constant_a_proof_reads_before_its_turn_is_typed_there`], and
//!   `wi_cbrd2_effect_guard_comparison_test::a_rule_body_precondition_is_refuted_at_its_carriers_eq`
//!   — `Color.eq`, reached from the rule sweep's refutation, which is why a body the sweep reaches
//!   is typed there and not answered "not typed" (`typing::body_readiness`).
//! * A begun body run as stored: [`a_proof_that_reaches_the_body_being_typed_is_undecided`] and
//!   [`a_body_whose_typing_failed_is_not_run`].
//! * A body typed on demand inside the depths of what reached it:
//!   [`a_body_typed_from_a_guard_is_typed_as_at_its_turn`] alone. Before that row, all of
//!   `wi_tests` passed with this backed out: the other bodies typed on demand there are reached
//!   from a proof, whose own depth they share.
//! * The constants not typed on demand: [`a_constant_a_proof_reads_before_its_turn_is_typed_there`].
//! * A body typed on demand run whether or not it came out typed:
//!   [`a_body_whose_typing_failed_is_not_run`].
//!
//! PASSES EITHER WAY, BY DESIGN: the rows of [`a_laws_goal_is_passed_the_laws_instances`] over
//! `NZ_PLAIN`, and those at a zero divisor — read in the same functions as the rows that fail.
//! NOT DRIVEN, and said rather than claimed: the readiness of a spec's default body asked only
//! where it runs, past the carrier override (`Interpreter::runnable_operation_body`) — a load's
//! proof reaches no value-directed override, the typer pinning a ground receiver's call to its
//! member; the queues' marks for a typer run made inside a run, which none makes; a body reached
//! under an applied layer; and the contracts pass handed only the operations that declare a
//! comparison, which changes no verdict.

use anthill_core::kb::load::{self, LoadOptions};

use crate::common::{load_errors_of, load_in_a_later_call, load_stdlib_kb, rendered_load_errors};

/// The errors of `lib` and `program` as one file — one load, in every recipe.
fn one_load(lib: &str, program: &str) -> Vec<String> {
    load_errors_of(&format!("{lib}\n{program}"))
}

/// The errors of `program` loaded after `lib`, `lib` in its own sealed load — the control: what
/// a later load's proofs answer. `lib`'s own errors, if any, prefixed `LIB:`.
fn two_loads(lib: &str, program: &str) -> Vec<String> {
    let mut kb = load_stdlib_kb();
    if let Err(e) = load_in_a_later_call(&mut kb, lib, LoadOptions::default()) {
        return rendered_load_errors(e).into_iter().map(|s| format!("LIB: {s}")).collect();
    }
    load::seal_declarations(&mut kb);
    match load_in_a_later_call(&mut kb, program, LoadOptions::default()) {
        Ok(_) => Vec::new(),
        Err(e) => rendered_load_errors(e),
    }
}

fn owes_boom(errors: &[String]) -> bool {
    errors.iter().any(|e| e.contains("undeclared effect: Boom"))
}

fn unproved(errors: &[String], op: &str) -> bool {
    errors
        .iter()
        .any(|e| e.contains(&format!("{op}.requires")) && e.contains("unsatisfied precondition"))
}

// ── A rule a proof runs: `cmp`, through `made`'s citation ───────────────────────────────────

const CMP_HEAD: &str = r#"
  import anthill.prelude.{Int64, Bool, Error, EmptyStream, Relation, Ord, WeakOrd, Effect}
  import anthill.prelude.PartialEq.{eq}"#;

fn cmp_ns(ns: &str, body: &str) -> String {
    format!("namespace {ns}{CMP_HEAD}\n{body}\nend\n")
}

/// `Descending`'s `compare(1, 5)` is `4`; `Int64`'s own is `-1`.
const CMP_RULE: &str = r#"  sort Descending
    import anthill.prelude.Numeric.{sub}
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)
  end
  rule cmp[A](?a: A, ?b: A, ?c) :- WeakOrd[T = A], WeakOrd.compare(?a, ?b, ?c)"#;

const MADE: &str = r#"  operation made[A](x: A, y: A) -> Relation[T = (c: Int64), E = {Error}]
    requires WeakOrd[T = A] = cmp(x, y)
  operation firstIs(r: Relation[T = (c: Int64), E = {Error}], k: Int64) -> Bool
    effects {Error, Error[EmptyStream]} = eq(r.head.c, k)"#;

/// `g`'s guard and `h`'s precondition read the first row of `made[…](1, 5)`.
fn callers(k: &str) -> String {
    format!(
        r#"  sort Boom
    entity Bang
    provides Effect[T = Boom]
  end
  operation g(r: Relation[T = (c: Int64), E = {{Error}}]) -> Int64 effects {{ Boom :- firstIs(r, {k}) }} = 0
  operation caller() -> Int64 = g(made[A = Int64, WeakOrd = Descending](1, 5))
  operation h(r: Relation[T = (c: Int64), E = {{Error}}]) -> Int64 requires firstIs(r, {k}) = 0
  operation precond() -> Int64 = h(made[A = Int64, WeakOrd = Descending](1, 5))"#
    )
}

/// The first row of `made[A = Int64, WeakOrd = Descending](1, 5)` is `c = 4`: `firstIs(r, 4)`
/// holds — `Boom` owed, `h`'s precondition proved — and `firstIs(r, -1)` is refuted. In one load
/// as with `cmp` and `made` in an earlier one, and with `cmp` alone there; and with the callers
/// written before `made`, whose body a proof then runs before its turn.
#[test]
fn a_rule_a_proof_runs_is_elaborated_before_the_bodies() {
    for (i, (k, holds)) in [("4", true), ("-1", false)].into_iter().enumerate() {
        let ns = |tag: &str| format!("test.s8j.cmp{i}{tag}");
        let rows = [
            ("one load", one_load(&cmp_ns(&ns("a"), CMP_RULE), &cmp_ns(&ns("a"), &format!("{MADE}\n{}", callers(k))))),
            (
                "one load, the callers written before made",
                one_load(&cmp_ns(&ns("b"), CMP_RULE), &cmp_ns(&ns("b"), &format!("{}\n{MADE}", callers(k)))),
            ),
            (
                "cmp earlier",
                two_loads(&cmp_ns(&ns("c"), CMP_RULE), &cmp_ns(&ns("c"), &format!("{MADE}\n{}", callers(k)))),
            ),
            (
                "cmp and made earlier",
                two_loads(&cmp_ns(&ns("d"), &format!("{CMP_RULE}\n{MADE}")), &cmp_ns(&ns("d"), &callers(k))),
            ),
        ];
        for (how, errs) in rows {
            assert_eq!(
                (owes_boom(&errs), unproved(&errs, "h")),
                (holds, !holds),
                "firstIs(r, {k}), {how}: {errs:?}"
            );
            assert_eq!(errs.len(), 1, "firstIs(r, {k}), {how}: {errs:?}");
        }
    }
}

// ── A law's goal of a relation that needs a dictionary ─────────────────────────────────────

const LAW_HEAD: &str = r#"
  import anthill.prelude.{Int64, BigInt, Bool, PartialEq, Effect, EuclideanDomain, Additive}
  import anthill.prelude.PartialEq.{eq, neq}
  import anthill.prelude.Additive.{zero}
  import anthill.prelude.Multiplicative.{mul}
  import anthill.prelude.Divisible.{div}"#;

fn law_ns(ns: &str, body: &str) -> String {
    format!("namespace {ns}{LAW_HEAD}\n{body}\nend\n")
}

/// `nz` takes the divisor's `PartialEq` and `Additive`, each declared; the law's guard calls it,
/// and declares both beside its `EuclideanDomain`.
const NZ: &str = "  rule nz[A](?b: A) :- PartialEq[T = A], Additive[T = A], neq(?b, zero)";
/// The control: an `nz` that needs no dictionary, decided before as now.
const NZ_PLAIN: &str = "  rule nz(?b) :- neq(?b, 0)";
const LAW: &str = "  rule mul_div: div[A](mul(?a, ?b: A), ?b) = ?a :- EuclideanDomain[T = A], Additive[T = A], \
                   PartialEq[T = A], nz(?b)";

fn risky(ty: &str, contract: &str, call: &str) -> String {
    format!(
        "  sort Boom\n    entity Bang\n    provides Effect[T = Boom]\n  end\n  \
         operation risky(a: {ty}, b: {ty}) -> {ty} {contract} = a\n  \
         operation c(x: {ty}) -> {ty} = {call}"
    )
}

/// The law proves `(a * b) / b = a` at a divisor its guard holds of — `nz` passed the law's
/// instances — and not at a zero one, in one load as with the law and `nz` in an earlier one.
#[test]
fn a_laws_goal_is_passed_the_laws_instances() {
    let guard = "effects { Boom :- neq((a * b) / b, a) }";
    let pre = "requires eq((a * b) / b, a)";
    for (i, (nz, ty, call, decided)) in [
        (NZ, "Int64", "risky(x, 2)", true),
        (NZ, "BigInt", "risky(x, 2n)", true),
        (NZ, "Int64", "risky(x, 0)", false),
        (NZ_PLAIN, "Int64", "risky(x, 2)", true),
        (NZ_PLAIN, "Int64", "risky(x, 0)", false),
    ]
    .into_iter()
    .enumerate()
    {
        for (j, (contract, what)) in [(guard, "guard"), (pre, "precondition")].into_iter().enumerate() {
            let ns = |tag: &str| format!("test.s8j.law{i}{j}{tag}");
            let lib = |tag: &str| law_ns(&ns(tag), &format!("{nz}\n{LAW}"));
            let prog = |tag: &str| law_ns(&ns(tag), &risky(ty, contract, call));
            for (how, errs) in [("one load", one_load(&lib("a"), &prog("a"))), ("two loads", two_loads(&lib("b"), &prog("b")))] {
                let undecided = if what == "guard" { owes_boom(&errs) } else { unproved(&errs, "risky") };
                assert_eq!(!undecided, decided, "{nz} {ty} {call}, {what}, {how}: {errs:?}");
                assert_eq!(errs.len(), usize::from(undecided), "{nz} {ty} {call}, {what}, {how}: {errs:?}");
            }
        }
    }
}

// ── A body a proof runs before its turn ─────────────────────────────────────────────────────

fn big_program(ns: &str, callee_first: bool, arg: &str) -> String {
    let callee = "  operation big(n: Int64) -> Bool = n.gt(3)";
    let rest = format!(
        "  sort Boom\n    entity Bang\n    provides Effect[T = Boom]\n  end\n  \
         operation g(n: Int64) -> Int64 effects {{ Boom :- big(n) }} = 0\n  \
         operation caller() -> Int64 = g({arg})"
    );
    let body = if callee_first { format!("{callee}\n{rest}") } else { format!("{rest}\n{callee}") };
    format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64, Bool, Effect}}\n  \
         import anthill.prelude.PartialOrd.{{gt}}\n{body}\nend\n"
    )
}

/// `big(1)` is false and `big(5)` true, wherever `big` is written: the guard is refuted at
/// `g(1)` and holds at `g(5)`.
#[test]
fn a_body_a_proof_runs_before_its_turn_is_typed_there() {
    for (i, (callee_first, arg, owes)) in [
        (true, "1", false),
        (false, "1", false),
        (true, "5", true),
        (false, "5", true),
    ]
    .into_iter()
    .enumerate()
    {
        let errs = load_errors_of(&big_program(&format!("test.s8j.big{i}"), callee_first, arg));
        assert_eq!(owes_boom(&errs), owes, "big written first {callee_first}, g({arg}): {errs:?}");
        assert_eq!(errs.len(), usize::from(owes), "big written first {callee_first}, g({arg}): {errs:?}");
    }
}

/// A proof made while `f`'s body is typed reaches `f` again — `g(f(0))` in `f`'s own body — and
/// is undecided there: `Boom` is owed, where `f(0)` is `0` and the guard would be refuted.
#[test]
fn a_proof_that_reaches_the_body_being_typed_is_undecided() {
    let src = r#"
namespace test.s8j.rec
  import anthill.prelude.{Int64, Bool, Effect}
  import anthill.prelude.PartialOrd.{gt}
  import anthill.prelude.Numeric.{add}
  sort Boom
    entity Bang
    provides Effect[T = Boom]
  end
  operation g(x: Int64) -> Int64 effects { Boom :- gt(x, 5) } = x
  operation f(n: Int64) -> Int64 = if n.gt(0) then n.add(g(f(0))) else 0
end
"#;
    let errs = load_errors_of(src);
    assert!(
        errs.iter().any(|e| e.contains("f.effects") && e.contains("undeclared effect: Boom")),
        "{errs:?}"
    );
    assert_eq!(errs.len(), 1, "{errs:?}");
}

/// A body typed where a `@[simp]` guard reaches it is typed as at its turn — its own guarded
/// equations fire as there, and are not a guard nested in the one that reached it. `two(5)`'s
/// guard `big(5)` runs `big`, written after `main`, whose `fold(5)` is `1` by its equation: so
/// `big` is true, `two(5)` rewrites to `2`, and `big(1)` stays true when called.
#[test]
fn a_body_typed_from_a_guard_is_typed_as_at_its_turn() {
    let src = r#"
namespace test.s8j.simp
  import anthill.prelude.{Int64, Bool}
  import anthill.prelude.PartialEq.{eq}
  import anthill.prelude.PartialOrd.{gt}
  operation two(x: Int64) -> Int64 = 0
  rule two(?x) = 2 :- big(?x) @[simp]
  operation main() -> Int64 = two(5)
  operation big(n: Int64) -> Bool = eq(fold(5), 1)
  operation fold(x: Int64) -> Int64 = 0
  rule fold(?x) = 1 :- gt(?x, 2) @[simp]
end
"#;
    let mut interp = crate::common::interp_for(src);
    let main = interp.call("test.s8j.simp.main", &anthill_core::eval::HostValue::all(&[])).map(|h| h.value);
    let big = interp.call("test.s8j.simp.big", &anthill_core::eval::HostValue::all(&[anthill_core::eval::Value::Int(1)])).map(|h| h.value);
    assert!(matches!(main, Ok(anthill_core::eval::Value::Int(2))), "main(): {main:?}");
    assert!(matches!(big, Ok(anthill_core::eval::Value::Bool(true))), "big(1): {big:?}");
}

/// A constant a proof reads before its turn is typed there as a body is: `caller`'s guard runs
/// `lim(0)`, whose body reads `LIMIT`, typed after the operation bodies — its value `3.add(4)`
/// read as loaded aborted the load. `g(10)` owes `Boom` (`10 > 7`) and `g(1)` does not.
#[test]
fn a_constant_a_proof_reads_before_its_turn_is_typed_there() {
    for (i, (arg, owes)) in [("10", true), ("1", false)].into_iter().enumerate() {
        let src = format!(
            r#"
namespace test.s8j.const{i}
  import anthill.prelude.{{Int64, Bool, Effect}}
  import anthill.prelude.PartialOrd.{{gt}}
  import anthill.prelude.Numeric.{{add}}
  sort Boom
    entity Bang
    provides Effect[T = Boom]
  end
  operation g(n: Int64) -> Int64 effects {{ Boom :- gt(n, lim(0)) }} = 0
  operation caller() -> Int64 = g({arg})
  operation lim(k: Int64) -> Int64 = LIMIT.add(k)
  const LIMIT: Int64 = 3.add(4)
end
"#
        );
        let errs = load_errors_of(&src);
        assert_eq!(owes_boom(&errs), owes, "g({arg}): {errs:?}");
        assert_eq!(errs.len(), usize::from(owes), "g({arg}): {errs:?}");
    }
}

/// A body whose typing failed is not run by a proof that reaches it: `big`'s `n.gt("x")` is
/// refused, and `g(1)`'s guard over it is undecided — `Boom` owed — where its text as loaded
/// aborted the load.
#[test]
fn a_body_whose_typing_failed_is_not_run() {
    let src = r#"
namespace test.s8j.failed
  import anthill.prelude.{Int64, Bool, Effect, String}
  import anthill.prelude.PartialOrd.{gt}
  sort Boom
    entity Bang
    provides Effect[T = Boom]
  end
  operation g(n: Int64) -> Int64 effects { Boom :- big(n) } = 0
  operation caller() -> Int64 = g(1)
  operation big(n: Int64) -> Bool = n.gt("x")
end
"#;
    let errs = load_errors_of(src);
    assert!(owes_boom(&errs), "{errs:?}");
    assert!(
        errs.iter().any(|e| e.contains("gt.b") && e.contains("expected Int64, got String")),
        "{errs:?}"
    );
    assert_eq!(errs.len(), 2, "{errs:?}");
}

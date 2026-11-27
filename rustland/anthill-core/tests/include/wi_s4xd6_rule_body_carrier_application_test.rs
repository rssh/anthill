//! WI-20261127-S4XD6 — a rule-body call of a spec operation is held to the APPLICATION its
//! carrier is, not only to the carrier's sort; so beside a provider at another instance of the
//! same sort it is refused, as the same call in an operation body is.
//!
//! `Store2 { sort State = ?  peek2(s: State, t: State) -> Int64 }` over `CB` at `Buf[T =
//! String, N = Bool]` (answers `s.v + 20`) and `mky() -> Buf[T = Int64, N = Bool]`. MEASURED
//! on the parent commit (8595d254f): beside `CB` alone, `rule rr(?r) :- Store2.peek2(mky(),
//! mky(), ?r)` loaded and `rr(?r)` answered `21` — `CB`'s member run on an `Int64` buffer —
//! while `operation oo() -> Int64 = Store2.peek2(mky(), mky())` is refused, "no such row
//! answers at these bindings". So did a defaulted member, the receiver spelling, an argument
//! whose element is open (`mkb([])`) in either place, a head variable typed at the `Int64`
//! buffer, and the same call as a top-level query.
//!
//! WHAT WAS GOING ON. The rule-body owner of the question (`check_one_spec_op_requirement`)
//! decides on the carrier decision the `@[simp]` guard and the run time share, which reads each
//! carrier as its SORT: `CB`'s witness row is filed at `Buf`, so `Buf` "provides" `Store2` and
//! the call fired. When the call runs, the value it is handed is `buf(v: 1)`, which carries no
//! type argument (`T` and `N` are no field's), so the dispatch reads `Buf` alone and takes the
//! one row there. Beside `CA` at `Buf[T = Int64, N = Bool]` the typer's dispatch at the call's
//! types pins `CA` before the run, which is why that case answered right (11) in either order.
//!
//! THE FIX: where the call fixes its carriers at applications of a sort, the goal at those types
//! is resolved after the walk (`CarrierApplication`), and no row answering it is the refusal an
//! operation body's call gets (`unprovided_spec_at`). With it, this pass's refusals carry the
//! file they were found in, so they render at `file:line:col` — they ended "at 256..275".
//!
//! Every row DRIVES the program: it resolves `rr(?r)` to the value that names the provider
//! reached, or the refusal names the requirement at the instance the call is at.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! Measured by backing each part out alone and running this file:
//!
//! 1. THE APPLICATION CHECK (the `Fire` arm of `check_one_spec_op_requirement` queueing a
//!    `CarrierApplication`). 8 FAIL: seven load and answer 21 —
//!    [`beside_the_other_provider_alone_the_call_is_refused`],
//!    [`the_refusal_is_the_operation_bodys`],
//!    [`a_defaulted_member_is_refused_alike`],
//!    [`an_open_argument_takes_what_the_other_says_in_either_place`],
//!    [`a_receiver_call_is_refused_alike`],
//!    [`a_head_variable_typed_at_the_application_is_refused`] and
//!    [`a_query_of_the_call_is_refused_alike`] — and [`the_refusals_name_their_line`], whose
//!    application half then loads.
//! 2. THE QUERY ROUTE ALONE (the application check's call in `rule_goal_routes`). 1 FAILS:
//!    [`a_query_of_the_call_is_refused_alike`].
//! 3. THE FILE ON THIS PASS'S REFUSALS (`check_rule_body_requirements`' sources, in
//!    `elaborate_rules`). 2 FAIL: [`the_refusals_name_their_line`] (both halves render a byte
//!    range, `at 701..731`), and [`the_refusal_is_the_operation_bodys`], whose rule-body sentence
//!    then ends in one.
//!
//! 4. THE AGREEMENT OF TWO ARGUMENTS AT ONE PARAMETER (`CarrierApplication::refusal`'s
//!    `also_at` walk, found by the gate): its rows are not here. Without it a call the typer
//!    already refuses as a mismatch got a second diagnosis, at the type of whichever argument
//!    came first — `[zz4n.inner.rel] = 7` was refused twice, and
//!    `wi_2nxac …the_dot_chain_bit_needs_no_table_in_a_collection_literal` and
//!    `wi_4nekz …the_reading_survives_every_enclosing_atom`, which count ONE diagnosis, FAIL.
//!
//! PASS EITHER WAY, by design: [`beside_the_provider_at_its_instance_the_call_answers_it`] (the
//! typer pins `CA`), [`the_provider_at_the_calls_instance_answers_it`] (`CB` at its own `T =
//! String`), [`a_generic_witness_answers_every_instance`] (the resolution finds `AnyB`), and the
//! two other-sort refusals, [`a_carrier_of_another_sort_is_refused`] and
//! [`an_entity_sort_beside_a_provider_at_another_is_refused`], which the carrier decision
//! makes on the sort.

use crate::common::{
    assert_refused_naming, definite_unary, load_errors_of, load_kb_with, query_pattern_refusals,
};
use anthill_core::eval::Value;

const PRELUDE: &str = "  import anthill.prelude.{Int64, String, List, Bool}";

/// `Store2`, `Buf[T, N]`, `mky`, `mks` and `mkb`, the providers `providers`, then `body`.
fn program(ns: &str, providers: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
{PRELUDE}

  sort Store2
    sort State = ?
    operation peek2(s: State, t: State) -> Int64
    operation peek3(s: State, t: State) -> Int64 = 0
  end

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: Int64)
  end

  operation mky() -> Buf[T = Int64, N = Bool] = buf(v: 1)
  operation mks() -> Buf[T = String, N = Bool] = buf(v: 1)
  operation mkb[E](xs: List[T = E]) -> Buf[T = E, N = Bool] = buf(v: 1)
{providers}
{body}
end
"#
    )
}

/// A provider `name` of `Store2` at `Buf[T = t, N = Bool]`; each operation answers `s.v +
/// offset`, so the answer names the provider that ran.
fn provider(name: &str, t: &str, offset: i64) -> String {
    let at = format!("Buf[T = {t}, N = Bool]");
    format!(
        r#"
  sort {name}
    provides Store2[State = {at}]
    operation peek2(s: {at}, t: {at}) -> Int64 = s.v + {offset}
    operation peek3(s: {at}, t: {at}) -> Int64 = s.v + {offset}
  end
"#
    )
}

/// `CA` (`T = Int64`, +10).
fn ca() -> String {
    provider("CA", "Int64", 10)
}

/// `CB` (`T = String`, +20).
fn cb() -> String {
    provider("CB", "String", 20)
}

/// `rr(?r)`'s definite answers, the program loaded clean.
fn answers(ns: &str, providers: &str, body: &str) -> Vec<i64> {
    let mut kb = load_kb_with(&program(ns, providers, body));
    definite_unary(&mut kb, &format!("{ns}.rr"))
        .into_iter()
        .map(|v| match v {
            Value::Int(i) => i,
            other => panic!("`{ns}.rr` must answer an Int64, got {other:?}"),
        })
        .collect()
}

/// The load's refusals.
fn refusals(ns: &str, providers: &str, body: &str) -> Vec<String> {
    load_errors_of(&program(ns, providers, body))
}

/// The tokens the refusal of a call at `Buf[T = Int64, N = Bool]` beside `CB` alone names: the
/// requirement at the call's instance, the provider that is at another, and why it does not
/// answer.
fn at_int64_beside_cb(ns: &str) -> Vec<String> {
    vec![
        format!("requirement `{ns}.Store2[State = {ns}.Buf[T = anthill.prelude.Int64, N = anthill.prelude.Bool]]` cannot be supplied"),
        format!("`{ns}.CB` provides `{ns}.Store2` at `{ns}.Buf`, but no such row answers at these bindings"),
    ]
}

fn assert_refused_at_int64(errs: &[String], ns: &str, why: &str) {
    let tokens = at_int64_beside_cb(ns);
    let tokens: Vec<&str> = tokens.iter().map(String::as_str).collect();
    assert_refused_naming(errs, &tokens, why);
}

// ── the ticket's call ─────────────────────────────────────────────────────────────────────

#[test]
fn beside_the_other_provider_alone_the_call_is_refused() {
    let ns = "wis4xd6.alone";
    let errs = refusals(ns, &cb(), "  rule rr(?r) :- Store2.peek2(mky(), mky(), ?r)");
    assert_refused_at_int64(&errs, ns, "beside `CB` alone, a call at the `Int64` buffer");
}

/// One call, one sentence, wherever it is written: the rule body's refusal carries the
/// operation body's, requirement and repair alike.
#[test]
fn the_refusal_is_the_operation_bodys() {
    let in_rule = refusals("wis4xd6.same", &cb(), "  rule rr(?r) :- Store2.peek2(mky(), mky(), ?r)");
    let in_op = refusals("wis4xd6.same", &cb(), "  operation oo() -> Int64 = Store2.peek2(mky(), mky())");
    let sentence = |errs: &[String]| -> String {
        let [e] = errs else { panic!("one refusal each, got {errs:?}") };
        let at = e.find("requirement `").unwrap_or_else(|| panic!("names the requirement: {e}"));
        e[at..].to_string()
    };
    assert_eq!(sentence(&in_rule), sentence(&in_op), "the rule body and the operation body say one thing");
}

#[test]
fn beside_the_provider_at_its_instance_the_call_answers_it() {
    let body = "  rule rr(?r) :- Store2.peek2(mky(), mky(), ?r)";
    assert_eq!(answers("wis4xd6.ab", &format!("{}{}", ca(), cb()), body), vec![11]);
    assert_eq!(answers("wis4xd6.ba", &format!("{}{}", cb(), ca()), body), vec![11]);
}

#[test]
fn the_provider_at_the_calls_instance_answers_it() {
    assert_eq!(answers("wis4xd6.own", &cb(), "  rule rr(?r) :- Store2.peek2(mks(), mks(), ?r)"), vec![21]);
}

/// A provision at a type parameter of its provider (`Buf[T = E, N = Bool]`) answers at every
/// `T`: the search, not the sort, decides.
#[test]
fn a_generic_witness_answers_every_instance() {
    let any = r#"
  sort AnyB
    sort E = ?
    provides Store2[State = Buf[T = E, N = Bool]]
    operation peek2(s: Buf[T = E, N = Bool], t: Buf[T = E, N = Bool]) -> Int64 = s.v + 30
  end
"#;
    assert_eq!(answers("wis4xd6.any", any, "  rule rr(?r) :- Store2.peek2(mky(), mky(), ?r)"), vec![31]);
}

// ── the other spellings of the call ───────────────────────────────────────────────────────

/// A defaulted member of a spec with an abstract one owes the instance as the body-less one
/// does (WI-883): it ran `CB.peek3` too.
#[test]
fn a_defaulted_member_is_refused_alike() {
    let ns = "wis4xd6.dflt";
    let errs = refusals(ns, &cb(), "  rule rr(?r) :- Store2.peek3(mky(), mky(), ?r)");
    let tokens = [
        format!("requirement `{ns}.Store2[State = {ns}.Buf[T = anthill.prelude.Int64, N = anthill.prelude.Bool]]` cannot be supplied for call to `{ns}.Store2.peek3`"),
        format!("`{ns}.CB` provides `{ns}.Store2` at `{ns}.Buf`"),
    ];
    let tokens: Vec<&str> = tokens.iter().map(String::as_str).collect();
    assert_refused_naming(&errs, &tokens, "a defaulted member at the `Int64` buffer");
}

/// `mkb([])`'s element is open, and takes what the other argument says (kernel-language §5.4):
/// the call is at the `Int64` buffer with the open one first or second.
#[test]
fn an_open_argument_takes_what_the_other_says_in_either_place() {
    for (ns, call) in [
        ("wis4xd6.open_first", "Store2.peek2(mkb([]), mky(), ?r)"),
        ("wis4xd6.open_second", "Store2.peek2(mky(), mkb([]), ?r)"),
    ] {
        let errs = refusals(ns, &cb(), &format!("  rule rr(?r) :- {call}"));
        assert_refused_at_int64(&errs, ns, call);
    }
}

#[test]
fn a_receiver_call_is_refused_alike() {
    let ns = "wis4xd6.recv";
    let errs = refusals(ns, &cb(), "  rule rr(?r) :- mky().peek2(mky(), ?r)");
    assert_refused_at_int64(&errs, ns, "`mky().peek2(mky(), ?r)`");
}

/// A head variable written with its type fixes the application as a constructor's value does;
/// at `CB`'s own instance the same clause answers.
#[test]
fn a_head_variable_typed_at_the_application_is_refused() {
    let ns = "wis4xd6.head";
    let errs = refusals(
        ns,
        &cb(),
        "  rule rr(?b: Buf[T = Int64, N = Bool], ?r) :- Store2.peek2(?b, ?b, ?r)",
    );
    assert_refused_at_int64(&errs, ns, "a head variable typed at the `Int64` buffer");
    let errs = refusals(
        "wis4xd6.head_own",
        &cb(),
        "  rule rr(?b: Buf[T = String, N = Bool], ?r) :- Store2.peek2(?b, ?b, ?r)",
    );
    assert!(errs.is_empty(), "at `CB`'s own instance the clause loads: {errs:?}");
}

/// A query's call is typed as a clause's is, by the same owner.
#[test]
fn a_query_of_the_call_is_refused_alike() {
    let ns = "wis4xd6.query";
    let mut kb = load_kb_with(&program(ns, &cb(), ""));
    let errs = query_pattern_refusals(&mut kb, &format!("{ns}.Store2.peek2({ns}.mky(), {ns}.mky(), ?r)"));
    assert_refused_at_int64(&errs, ns, "the query `Store2.peek2(mky(), mky(), ?r)`");
}

// ── the refusals the carrier's sort decides stand ─────────────────────────────────────────

const STORE1: &str = r#"
  sort Store1
    sort State = ?
    operation peek1(s: State) -> Int64
  end
"#;

#[test]
fn a_carrier_of_another_sort_is_refused() {
    let ns = "wis4xd6.other";
    let providers = format!(
        "{STORE1}\n  sort C1\n    provides Store1[State = String]\n    operation peek1(s: String) -> Int64 = 1\n  end\n"
    );
    let errs = refusals(ns, &providers, "  rule rr(?r) :- Store1.peek1(5, ?r)");
    assert_refused_naming(
        &errs,
        &["`anthill.prelude.Int64` provides no `wis4xd6.other.Store1`", "no call here can discharge it"],
        "`Store1.peek1(5, ?r)` beside a provider at `String`",
    );
}

#[test]
fn an_entity_sort_beside_a_provider_at_another_is_refused() {
    let ns = "wis4xd6.entity";
    let providers = format!(
        "{STORE1}\n  sort P\n    entity p(v: Int64)\n  end\n  sort Q\n    entity q(v: Int64)\n  end\n  \
         sort C1\n    provides Store1[State = Q]\n    operation peek1(s: Q) -> Int64 = 1\n  end\n"
    );
    let errs = refusals(ns, &providers, "  rule rr(?r) :- Store1.peek1(p(v: 1), ?r)");
    assert_refused_naming(
        &errs,
        &["`wis4xd6.entity.P` provides no `wis4xd6.entity.Store1`"],
        "`Store1.peek1(p(v: 1), ?r)` beside a provider at `Q`",
    );
}

// ── where the refusal is ──────────────────────────────────────────────────────────────────

/// This pass's refusals render at the line and column of the call, the application's and the
/// sort's: they ended "at 701..731", a byte range of no named file. A test's source has no file
/// name, so the place is the line and the column the call starts at (`  rule rr(?r) :- ` is 17
/// characters).
#[test]
fn the_refusals_name_their_line() {
    let rule_line = |src: &str| -> usize {
        1 + src.lines().position(|l| l.contains("rule rr")).expect("the program writes `rr`")
    };
    let store1 = format!(
        "{STORE1}\n  sort C1\n    provides Store1[State = String]\n    operation peek1(s: String) -> Int64 = 1\n  end\n"
    );
    for (what, src) in [
        (
            "the application's",
            program("wis4xd6.line", &cb(), "  rule rr(?r) :- Store2.peek2(mky(), mky(), ?r)"),
        ),
        ("the sort's", program("wis4xd6.line_sort", &store1, "  rule rr(?r) :- Store1.peek1(5, ?r)")),
    ] {
        let errs = load_errors_of(&src);
        let [e] = errs.as_slice() else { panic!("{what}: one refusal, got {errs:?}") };
        let at = format!("{}:18: ", rule_line(&src));
        assert!(e.starts_with(&at), "{what} refusal is at `{at}`: {e}");
    }
}

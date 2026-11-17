//! A BIGINT DIVISION BY A KNOWN ZERO IS CHARGED ITS EFFECT (WI-20261109-5VM2G).
//! `BigInt.div(to_bigint(7), to_bigint(0))` loaded with no effect declared, and the host
//! raised `DivisionByZero` from an operation that declares none. Four causes, each a row
//! below (decided with the user, 2026-11-16):
//!
//! * The guard compared a `BigInt` divisor with the `Int64` literal `0` — apart, so the effect
//!   was dropped. A `BigInt` constant had no literal: it is now written `0n`, and the guard is
//!   `PartialEq.eq(b, 0n)`. An unsuffixed integer too large for `Int64` is refused rather than
//!   read as a `BigInt`.
//! * A carrier's guard could not be spelled in its own type: the override refinement check
//!   covered a guarded atom only by the spec's guard spelled identically, and the spec's, over
//!   `T`, wrote `0`. An unconditional spec atom now covers a guarded one of its label (§8.7),
//!   and the spec rows are unconditional.
//! * A body-less operation's guard was never typed (§5.4 says every guard is): the checker
//!   skipped an operation with no body and no default.
//! * A guard's own nullary call, `zero()`, is the bare name `zero` as a term, which the
//!   resolver compared as a datum unequal to every number. A conjunct reading a term that is
//!   not its value — that name, a `const`, a call of a function parameter — is undecided now,
//!   for a guard, a precondition and a contract alike (found by /code-review: the precondition
//!   and the contract proof read the same goal).
//!
//! The literal's printed form reaches the JSON store too: a `BigInt` field reads back as a
//! `BigInt` ([`a_bigint_field_round_trips_through_json`]).
//!
//! ## What fails with the change backed out
//!
//! Measured one at a time, each with the rest of the change in place (2026-11-16):
//!
//! * The stdlib guards back to `PartialEq.eq(b, 0)`, the refinement rule (a guarded atom
//!   covered only by a guarded spec atom), or the converter's `bigint_literal` arm: every row
//!   fails — the stdlib load is refused (its guard is typed; `Int64.div` does not refine
//!   `Divisible.div`; `0n` does not parse).
//! * The stdlib guards back AND body-less operations not typed:
//!   [`a_bigint_division_by_a_known_zero_owes_its_effect`] (each division loads),
//!   [`a_body_less_operations_contract_comparisons_are_typed`],
//!   [`a_call_in_a_body_less_contract_is_held_to_its_precondition`].
//! * Body-less operations not typed (the `(None, None) => continue` restored): the last two.
//! * `clause_goal` gating no conjunct: [`a_guard_whose_own_term_is_not_its_value_is_undecided`],
//!   [`a_guard_reading_a_const_or_a_function_parameter_is_undecided`],
//!   [`a_contract_reading_a_term_that_is_not_its_value_is_not_proved`].
//! * A bare operation name read as its value: the first and the third of those.
//! * A `const` read as its value, or a function parameter's call as a goal the resolver
//!   answers: [`a_guard_reading_a_const_or_a_function_parameter_is_undecided`].
//! * The contract proof discharging a conjunct with no goal:
//!   [`a_contract_reading_a_term_that_is_not_its_value_is_not_proved`].
//! * A proof reading a conjunct as a refutation does (every argument a value, not only a
//!   comparison's operands): `wi_bxmpk_goal_value_carried_test::a_contract_requires_holding_a_
//!   lambda_is_assumed_either_way` and `wi_drgcp_precondition_goal_spelling_test::a_type_
//!   application_in_a_goal_is_written_as_a_type`, whose predicate arguments a fact matches as
//!   written.
//! * The body-less operation's precondition sink not drained:
//!   [`a_call_in_a_body_less_contract_is_held_to_its_precondition`].
//! * The JSON reader reading a number by its shape: [`a_bigint_field_round_trips_through_json`].
//! * An overflowing literal read as a `BigInt`, or `write_literal` printing bare digits:
//!   [`a_bigint_literal_is_spelled_with_n`].
//!
//! [`a_bigint_division_by_a_known_non_zero_owes_nothing`] and
//! [`the_int64_and_parameter_controls_keep_their_verdicts`] pass under every back-out that
//! leaves the stdlib loading, by design: the controls the ticket named.

use anthill_core::eval::Value;
use anthill_core::kb::proof_verify::{verify_proofs, ProofVerdict};
use anthill_core::kb::term::Literal;
use anthill_core::persistence::print::write_literal;
use anthill_core::persistence::term_ser;

use crate::common::{load_errors_of, load_kb_with, parse_errs, parses_clean, query_unary};

const DIV0: &str = "undeclared effect: Error[T = DivisionByZero]";

fn division(ns: &str, body: &str) -> String {
    format!(
        "namespace {ns}\n  \
         import anthill.prelude.{{Int64, BigInt, PartialEq, String}}\n  \
         import anthill.prelude.BigInt.{{to_bigint}}\n  \
         {body}\nend\n"
    )
}

/// A program declaring the effect `Boom` beside `decls`.
fn with_boom(ns: &str, decls: &str) -> String {
    format!(
        "namespace {ns}\n  \
         import anthill.prelude.{{Int64, Bool, BigInt, PartialEq, Eq, Effect}}\n  \
         import anthill.prelude.PartialEq.{{eq}}\n  \
         import anthill.prelude.BigInt.{{to_bigint}}\n  \
         sort Boom\n    entity Bang\n    provides Effect[T = Boom]\n  end\n\
         {decls}\nend\n"
    )
}

#[test]
fn a_bigint_division_by_a_known_zero_owes_its_effect() {
    for (i, call) in [
        "BigInt.div(to_bigint(7), to_bigint(0))",
        "BigInt.mod(to_bigint(7), to_bigint(0))",
        "BigInt.rem(to_bigint(7), to_bigint(0))",
        "to_bigint(7) / to_bigint(0)",
        "BigInt.div(7n, 0n)",
        "7n / 0n",
    ]
    .iter()
    .enumerate()
    {
        let errs = load_errors_of(&division(
            &format!("test.vm2g.zero{i}"),
            &format!("operation bz() -> BigInt = {call}"),
        ));
        assert!(errs.iter().any(|e| e.contains(DIV0)), "{call}: {errs:?}");
    }
}

#[test]
fn a_bigint_division_by_a_known_non_zero_owes_nothing() {
    for (i, call) in [
        "BigInt.div(to_bigint(7), to_bigint(2))",
        "BigInt.mod(to_bigint(7), to_bigint(2))",
        "BigInt.rem(to_bigint(7), to_bigint(2))",
        "to_bigint(7) / to_bigint(2)",
        "7n / -2n",
    ]
    .iter()
    .enumerate()
    {
        let errs = load_errors_of(&division(
            &format!("test.vm2g.nonzero{i}"),
            &format!("operation b2() -> BigInt = {call}"),
        ));
        assert!(errs.is_empty(), "{call}: {errs:?}");
    }
}

#[test]
fn the_int64_and_parameter_controls_keep_their_verdicts() {
    for (i, (decl, owes)) in [
        ("operation i0() -> Int64 = Int64.div(7, 0)", true),
        ("operation is() -> Int64 = Int64.div(7, Int64.sub(1, 1))", true),
        ("operation ip(b: Int64) -> Int64 = Int64.div(7, b)", true),
        ("operation bp(b: BigInt) -> BigInt = BigInt.div(to_bigint(7), b)", true),
        ("operation i2() -> Int64 = 7 / 2", false),
    ]
    .iter()
    .enumerate()
    {
        let errs = load_errors_of(&division(&format!("test.vm2g.ctl{i}"), decl));
        assert_eq!(errs.iter().any(|e| e.contains(DIV0)), *owes, "{decl}: {errs:?}");
    }
}

/// `0n` is a `BigInt` whatever its size, equal to `to_bigint(0)`, and prints with its suffix;
/// an unsuffixed literal too large for `Int64` is refused, naming the suffix.
#[test]
fn a_bigint_literal_is_spelled_with_n() {
    let mut kb = load_kb_with(&division(
        "test.vm2g.lit",
        "fact big(v: 0n)\n  \
         fact big(v: -7n)\n  \
         fact big(v: 123456789012345678901234567890n)\n  \
         rule all(?v) :- big(v: ?v)\n  \
         rule zero(?v) :- big(v: ?v), PartialEq.eq(?v, to_bigint(0))",
    ));
    let mut all: Vec<String> = query_unary(&mut kb, "test.vm2g.lit.all")
        .into_iter()
        .map(|(v, _)| match v {
            Value::BigInt(n) => n.to_string(),
            other => panic!("expected a BigInt, got {other:?}"),
        })
        .collect();
    all.sort();
    assert_eq!(all, ["-7", "0", "123456789012345678901234567890"]);
    let zero = query_unary(&mut kb, "test.vm2g.lit.zero");
    assert_eq!(zero.len(), 1, "0n = to_bigint(0): {zero:?}");

    let errs = parse_errs("fact big(v: 99999999999999999999)");
    assert!(
        errs.iter().any(|e| e.contains(
            "integer literal 99999999999999999999 overflows Int64; write 99999999999999999999n for a BigInt"
        )),
        "{errs:?}"
    );
    parses_clean("fact big(v: 9223372036854775807)");

    let mut printed = String::new();
    write_literal(&Literal::BigInt(5.into()), &mut printed);
    assert_eq!(printed, "5n");
}

/// A `BigInt` field written to JSON reads back as a `BigInt`: a small one is written as a
/// JSON number and was read back as an `Int64`, a large one as its digits and read back as a
/// `String`.
#[test]
fn a_bigint_field_round_trips_through_json() {
    let mut kb = load_kb_with(&division(
        "test.vm2g.json",
        "entity Acct(name: String, balance: BigInt)\n  \
         fact Acct(name: \"a\", balance: 5n)\n  \
         fact Acct(name: \"b\", balance: 123456789012345678901234567890n)\n  \
         rule bal(?b) :- Acct(name: ?, balance: ?b)",
    ));
    let acct = kb.try_resolve_symbol("test.vm2g.json.Acct").expect("Acct");
    let rids = kb.rules_by_functor(acct);
    let json = term_ser::serialize_json(&kb, "test.vm2g.json.Acct", &rids).expect("serialize");
    for rid in rids {
        kb.retract(rid);
    }
    assert!(query_unary(&mut kb, "test.vm2g.json.bal").is_empty());
    let domain = kb.intern("test_domain");
    let loaded = term_ser::load_json(&mut kb, &json, domain).unwrap_or_else(|e| panic!("{e:?}: {json}"));
    assert_eq!(loaded, 2, "{json}");
    let mut got: Vec<String> = query_unary(&mut kb, "test.vm2g.json.bal")
        .into_iter()
        .map(|(v, _)| match v {
            Value::BigInt(n) => n.to_string(),
            other => panic!("expected a BigInt, got {other:?}"),
        })
        .collect();
    got.sort();
    assert_eq!(got, ["123456789012345678901234567890", "5"]);
}

/// §8.7: a guarded member atom narrows an unconditional spec atom of its label. The other
/// direction, and a label the spec does not declare, are still refused.
#[test]
fn an_unconditional_spec_effect_covers_a_guarded_member_effect() {
    let program = |ns: &str, spec_row: &str, member_row: &str| {
        with_boom(
            ns,
            &format!(
                "  sort Bust\n    entity Burst\n    provides Effect[T = Bust]\n  end\n  \
                 sort Chk\n    sort T = ?\n    \
                 operation risky(c: T, d: T) -> Int64 effects {{ {spec_row} }}\n  end\n  \
                 sort Color\n    entity Red\n    entity Green\n    \
                 provides PartialEq[T = Color]\n    provides Eq[T = Color]\n    \
                 provides Chk[T = Color]\n    \
                 operation risky(c: Color, d: Color) -> Int64 effects {{ {member_row} }} = 0\n  end\n"
            ),
        )
    };
    for (ns, spec_row, member_row, refused) in [
        ("test.vm2g.cov", "Boom", "Boom :- eq(c, d)", false),
        ("test.vm2g.covlabel", "Boom", "Bust :- eq(c, d)", true),
        ("test.vm2g.covback", "Boom :- eq(c, d)", "Boom", true),
    ] {
        let errs = load_errors_of(&program(ns, spec_row, member_row));
        assert_eq!(
            errs.iter().any(|e| e.contains("does not refine")),
            refused,
            "{ns}: {errs:?}"
        );
    }
}

/// A body-less operation's guard and value contract are typed as a bodied one's are: a spec
/// operation's guard over `T` compares a `T`, and a requirement over a `Bool` a `Bool`.
#[test]
fn a_body_less_operations_contract_comparisons_are_typed() {
    let errs = load_errors_of(&with_boom(
        "test.vm2g.bodyless",
        "  sort Chk\n    sort T = ?\n    \
         operation risky(c: T) -> Int64 effects { Boom :- eq(c, 1) }\n  end\n  \
         sort Lk\n    operation pick(c: Bool) -> Int64 requires eq(c, 1)\n  end\n",
    ));
    for site in ["Chk.risky.effects", "Lk.pick.requires"] {
        assert!(
            errs.iter()
                .any(|e| e.contains(site) && e.contains("to compare two values of one type")),
            "{site}: {errs:?}"
        );
    }
    let errs = load_errors_of(&with_boom(
        "test.vm2g.bodylessok",
        "  sort Chk\n    sort T = ?\n    \
         operation risky(c: T, d: T) -> Int64 effects { Boom :- eq(c, d) }\n  end\n  \
         sort Lk\n    operation pick(c: Bool) -> Int64 requires eq(c, true)\n  end\n",
    ));
    assert!(errs.is_empty(), "{errs:?}");
}

/// `zero()` in a guard is the bare name `zero`, a datum to the resolver: the conjunct is
/// undecided, and the effect kept. A call with an argument is its value, and decided.
#[test]
fn a_guard_whose_own_term_is_not_its_value_is_undecided() {
    for (ns, guard, arg, owes) in [
        ("test.vm2g.own0", "PartialEq.eq(b, zero())", "to_bigint(0)", true),
        ("test.vm2g.own2", "PartialEq.eq(b, zero())", "to_bigint(2)", true),
        ("test.vm2g.call0", "PartialEq.eq(b, to_bigint(0))", "to_bigint(0)", true),
        ("test.vm2g.call2", "PartialEq.eq(b, to_bigint(0))", "to_bigint(2)", false),
    ] {
        let errs = load_errors_of(&with_boom(
            ns,
            &format!(
                "  import anthill.prelude.Additive.{{zero}}\n  \
                 operation risky(b: BigInt) -> BigInt effects {{ Boom :- {guard} }} = b\n  \
                 operation caller() -> BigInt = risky({arg})\n"
            ),
        ));
        assert_eq!(
            errs.iter().any(|e| e.contains("undeclared effect: Boom")),
            owes,
            "{ns}: {errs:?}"
        );
    }
}

/// A guard reading a `const` (a clause keeps it as its name) or calling a function parameter
/// (no clause answers it) is undecided: the effect is kept at a call its value would incur.
#[test]
fn a_guard_reading_a_const_or_a_function_parameter_is_undecided() {
    for (ns, decls) in [
        (
            "test.vm2g.cnst",
            "  const LIMIT: Int64 = 0\n  \
             operation risky(b: Int64) -> Int64 effects { Boom :- eq(b, LIMIT) } = b\n  \
             operation caller() -> Int64 = risky(0)\n",
        ),
        (
            "test.vm2g.fparam",
            "  operation risky(g: (x: Int64) -> Bool, b: Int64) -> Int64 effects { Boom :- g(b) } = b\n  \
             operation caller() -> Int64 = risky(lambda x -> true, 1)\n",
        ),
    ] {
        let errs = load_errors_of(&with_boom(ns, decls));
        assert!(
            errs.iter().any(|e| e.contains("caller.effects") && e.contains("undeclared effect: Boom")),
            "{ns}: {errs:?}"
        );
    }
}

/// A precondition and a postcondition reading `zero()` are not proved: the proof compared the
/// datum `zero` with a number, so `neq(to_bigint(0), zero)` held. A call with a term that is
/// its value is decided, either way.
#[test]
fn a_contract_reading_a_term_that_is_not_its_value_is_not_proved() {
    let pre = |ns: &str, clause: &str, arg: &str| {
        with_boom(
            ns,
            &format!(
                "  import anthill.prelude.Additive.{{zero}}\n  \
                 operation f(b: BigInt) -> BigInt requires {clause} = b\n  \
                 operation caller() -> BigInt = f({arg})\n"
            ),
        )
    };
    for (ns, clause, arg, refused) in [
        ("test.vm2g.pre0", "PartialEq.neq(b, zero())", "to_bigint(0)", true),
        ("test.vm2g.pre5", "PartialEq.neq(b, zero())", "to_bigint(5)", true),
        ("test.vm2g.prec0", "PartialEq.neq(b, to_bigint(0))", "to_bigint(0)", true),
        ("test.vm2g.prec5", "PartialEq.neq(b, to_bigint(0))", "to_bigint(5)", false),
    ] {
        let errs = load_errors_of(&pre(ns, clause, arg));
        assert_eq!(
            errs.iter().any(|e| e.contains("f.requires") && e.contains("unsatisfied precondition")),
            refused,
            "{ns}: {errs:?}"
        );
    }

    let post = |ns: &str, clause: &str, body: &str| {
        with_boom(
            ns,
            &format!(
                "  import anthill.prelude.Additive.{{zero}}\n  \
                 sort Z\n    \
                 operation z() -> BigInt\n      ensures {clause}\n      = {body}\n    \
                 proof z.ensures by derivation end\n  \
                 end\n"
            ),
        )
    };
    let verdict = |src: String| {
        let mut kb = load_kb_with(&src);
        verify_proofs(&mut kb)
            .into_iter()
            .find(|r| r.rule_qn.ends_with("z.ensures"))
            .expect("a report for z.ensures")
            .verdict
    };
    match verdict(post("test.vm2g.post0", "PartialEq.neq(result, zero())", "to_bigint(0)")) {
        ProofVerdict::Failed { reason } => assert!(reason.contains("not its value"), "{reason}"),
        other => panic!("`neq(result, zero())` over `to_bigint(0)` must not discharge: {other:?}"),
    }
    let control = verdict(post("test.vm2g.postc", "PartialEq.neq(result, to_bigint(0))", "to_bigint(5)"));
    assert!(matches!(control, ProofVerdict::Discharged), "{control:?}");
}

/// A call in a body-less operation's contract is held to its own precondition, as a call in a
/// body is: typing the contract records the failure, and it is reported.
#[test]
fn a_call_in_a_body_less_contract_is_held_to_its_precondition() {
    let errs = load_errors_of(&with_boom(
        "test.vm2g.sink",
        "  import anthill.prelude.PartialEq.{neq}\n  \
         operation needy(x: Int64) -> Int64 requires neq(x, 0) = x\n  \
         sort Sp\n    sort T = ?\n    \
         operation spec(b: T) -> Int64 requires eq(needy(0), 1)\n  end\n",
    ));
    assert!(
        errs.iter().any(|e| e.contains("needy.requires") && e.contains("unsatisfied precondition")),
        "{errs:?}"
    );
}

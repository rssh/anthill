//! WI-20261008-7B15V — an applied type alias is one type in every spelling: over `sort Box[V]`
//! and `sort CB = Box`, `CB[Int64]` is `Box[V = Int64]` as a companion receiver, through a name a
//! `let` bound to it, as a value, and in a rule body (§5.1, "an alias in a name is read
//! through"; §5.3, a type in a rule-body call's argument).
//!
//! A. THE TICKET'S SPELLINGS. Filed on 2026-10-08, when `CB[Int64].wrap(5)` answered 5 and
//!    `let t = CB[Int64]` was refused ("`CB` is over-applied … it declares no type
//!    parameters"). WI-20260908-9WVT7 (cef5913b) read an applied alias as the sort it stands for
//!    in a value position and WI-20261008-HZVQA made a receiver through an alias carry what it
//!    fixes, which closed it; no row held the applied spellings until these.
//! B. FOUND ON THE WAY: a type written as an argument of a call in a rule body's value slot kept a
//!    positional unbound — `?n <=> idt(Box[Int64])` answered `Box[Int64]` where an operation
//!    body answers `Box[V = Int64]`, so `isIB(CB[Int64])` was false, nested entries too
//!    (`List[T = Box[Int64]]`), and a fact holding `Box[V = Int64]` was not found through it. The
//!    operation-body walk leaves a positional for the evaluator to bind, and the resolver hands
//!    the node to the callee unevaluated; the loader now binds it (`type_value_as_one_term`).
//! C. FOUND ON THE WAY: binding again what an alias fixes (`IP[L = Bool]`) was reported twice in
//!    a type position — the alias's refusal, then "binds the type parameter 'L' more than once" —
//!    and the alias's `L = Int64` stayed in the type, so a receiver, an annotation, a rule head's
//!    bound and a provision each added a mismatch, and a rule's bounding guard was dropped
//!    ("no bounding guard", "unresolved name"). The value position already reported it once. The
//!    refusal now takes the alias's binding out (`Loader::refuse_type_alias_rebinding`), for
//!    every caller, and the two hand-written filters that did so in a value position are gone.
//!    A head's bound over a variable a guard bounds (`?x: A[Out = String]` beside `ITagger[A]`)
//!    called the guard's spec "a type alias"; it names the variable now
//!    (`Loader::refuse_guard_rebinding`).
//!
//! WHAT FAILS UNDER WHICH BACK-OUT — MEASURED, each switched off alone in one build, over this
//! file and the whole `wi_tests` binary:
//!
//!   * an alias's application read as its own name (`Loader::applied_value_alias`, 9WVT7's
//!     reader) → the ticket's refusal again ("`CB` is over-applied … it declares no type
//!     parameters"): the let-bound half of [`an_applied_alias_is_one_receiver_in_every_spelling`]
//!     and of [`each_spelling_binds_the_slot_the_alias_leaves_open`], every half of
//!     [`an_applied_alias_is_the_type_as_a_value`],
//!     [`a_type_in_a_rule_body_calls_argument_is_the_type_an_operation_body_holds`] and
//!     [`a_fact_holding_the_type_is_found_through_a_calls_argument`] (refused at `CB[Int64]`),
//!     the let-bound case of [`binding_again_what_the_alias_fixes_is_one_report_wherever_it_is_written`]
//!     (a second report), and outside this file four rows of `wi_9wvt7_value_position_alias_test`
//!     and two of `wi_kpbvx_alias_carries_default_test`;
//!   * a rule-body call's type argument left as the operation-body walk built it →
//!     [`a_type_in_a_rule_body_calls_argument_is_the_type_an_operation_body_holds`],
//!     [`a_fact_holding_the_type_is_found_through_a_calls_argument`] and the rule-body half of
//!     [`an_applied_alias_is_the_type_as_a_value`], and nothing else;
//!   * the alias's binding left in place after the refusal →
//!     [`binding_again_what_the_alias_fixes_is_one_report_wherever_it_is_written`] and
//!     `wi_9wvt7_value_position_alias_test::binding_again_what_the_alias_fixes_is_refused_once`.
//!
//!   PASS EITHER WAY, by design: the written and rule-body halves of
//!   [`an_applied_alias_is_one_receiver_in_every_spelling`] — a written receiver's bracket is read
//!   as a type, through the type position's alias reading (§5.1), which none of the three
//!   touches; they are what the let-bound spelling must agree with —
//!   [`a_named_entry_in_a_rule_body_calls_argument_was_already_the_type`], the control, and
//!   [`a_name_written_twice_after_an_alias_is_two_reports`], the fence for a refusal reporting
//!   once per written key.

use anthill_core::eval::Value;

use crate::common::{assert_refused_naming, load_errors_of, load_kb_with, query_unary, run_int64};

/// The sorts and aliases the rows are about.
const DECLS: &str = "  sort Box[V]\n    entity mk(v: V)\n    operation wrap(x: V) -> V = x\n    \
                     operation same(t: Type) -> Type = t\n  end\n  sort Duo[L, R]\n    entity \
                     duo(l: L, r: R)\n    operation first(x: L, y: R) -> L = x\n  end\n  sort D[A, B \
                     = Int64]\n    entity dd(a: A)\n  end\n  sort CB = Box\n  sort IP = Duo[L = \
                     Int64]\n  sort Hold\n    entity held(t: Type)\n  end\n  operation bit(c: Bool) \
                     -> Int64 = if c then 1 else 0\n  operation idt(t: Type) -> Type = t\n  \
                     operation isIB(t: Type) -> Bool = PartialEq.eq(t, Box[V = Int64])\n  \
                     operation isIPS(t: Type) -> Bool = PartialEq.eq(t, Duo[L = Int64, R = \
                     String])\n  operation isLIB(t: Type) -> Bool = PartialEq.eq(t, List[T = Box[V \
                     = Int64]])\n  operation isDS(t: Type) -> Bool = PartialEq.eq(t, D[A = String, \
                     B = Int64])\n";

/// A program in `test.<ns>` with the rows' declarations and `body`.
fn program(ns: &str, body: &str) -> String {
    format!(
        "namespace test.{ns}\n  import anthill.prelude.{{Int64, String, Bool, List, Type, \
         PartialEq}}\n{DECLS}{body}\nend\n"
    )
}

/// `test.<ns>.go()`'s value, or why it did not load or run.
fn run(ns: &str, body: &str) -> Result<i64, String> {
    run_int64(&program(ns, body), &format!("test.{ns}.go"))
}

/// The answers of `test.<ns>.r(?n)`.
fn rule_answers(ns: &str, body: &str) -> Vec<i64> {
    let mut kb = load_kb_with(&program(ns, body));
    query_unary(&mut kb, &format!("test.{ns}.r"))
        .into_iter()
        .map(|(v, definite)| match v {
            Value::Int(n) if definite => n,
            other => panic!("{ns}: expected a definite Int64, got {other:?}"),
        })
        .collect()
}

/// `go() -> Int64` calling `call` on the receiver written out.
fn written(recv: &str, call: &str) -> String {
    format!("  operation go() -> Int64 = {recv}.{call}")
}

/// The same call through a name a `let` bound to the receiver.
fn bound(recv: &str, call: &str) -> String {
    format!("  operation go() -> Int64 =\n    let t = {recv}\n    t.{call}")
}

/// The same call in a rule body's value slot.
fn in_rule(recv: &str, call: &str) -> String {
    format!("  rule r(?n) :- ?n <=> {recv}.{call}")
}

/// The applied aliases the ticket names, each with a call its member answers 5 to: positional,
/// named, and an alias that fixes one of two parameters.
const RECEIVERS: [(&str, &str, &str); 4] = [
    ("pos", "CB[Int64]", "wrap(5)"),
    ("named", "CB[V = Int64]", "wrap(5)"),
    ("partial", "IP[String]", "first(5, \"s\")"),
    ("partialnamed", "IP[R = String]", "first(5, \"s\")"),
];

// ── A. the ticket's spellings ─────────────────────────────────────────────────────────────

/// AN APPLIED ALIAS IS ONE RECEIVER: written, let-bound and in a rule body the call answers.
/// Before, the let-bound spelling was refused: the alias declares no type parameters.
///
/// FAILS with an alias's application read as its own name: the let-bound half.
#[test]
fn an_applied_alias_is_one_receiver_in_every_spelling() {
    for (tag, recv, call) in RECEIVERS {
        assert_eq!(run(&format!("b15vw{tag}"), &written(recv, call)), Ok(5), "written {recv}");
        assert_eq!(run(&format!("b15vb{tag}"), &bound(recv, call)), Ok(5), "let-bound {recv}");
        assert_eq!(rule_answers(&format!("b15vr{tag}"), &in_rule(recv, call)), vec![5], "rule {recv}");
    }
}

/// AS A VALUE an applied alias is the type it stands for, in an operation body, through a `let`
/// and as a rule-body call's argument.
///
/// FAILS with an alias's application read as its own name (every half), and with a rule-body
/// call's type argument left unbound (the rule-body positional terms, 1 and 4).
#[test]
fn an_applied_alias_is_the_type_as_a_value() {
    let sum = "bit(isIB(CB[Int64])) + 2 * bit(isIB(CB[V = Int64])) + 4 * bit(isIPS(IP[String])) + \
               8 * bit(isIPS(IP[R = String]))";
    assert_eq!(run("b15vvalue", &format!("  operation go() -> Int64 = {sum}")), Ok(15));
    let via_let = "  operation go() -> Int64 =\n    let a = CB[Int64]\n    let b = IP[String]\n    \
                   bit(isIB(a)) + 2 * bit(isIPS(b))";
    assert_eq!(run("b15vvaluelet", via_let), Ok(3));
    assert_eq!(rule_answers("b15vvaluerule", &format!("  rule r(?n) :- ?n <=> {sum}")), vec![15]);
}

/// THE SPELLINGS BIND THE SAME SLOT: `IP[String]` fixes `R`, the slot `IP` leaves open, and the
/// alias's `L` stands, so each spelling refuses the same argument naming the same parameter.
///
/// FAILS with an alias's application read as its own name: the let-bound half is refused for
/// the over-application instead.
#[test]
fn each_spelling_binds_the_slot_the_alias_leaves_open() {
    type Spelling = fn(&str, &str) -> String;
    let spellings: [(&str, Spelling); 3] = [("w", written), ("b", bound), ("r", in_rule)];
    for (tag, spell) in spellings {
        for (case, recv, call, token) in [
            ("v", "CB[Int64]", "wrap(\"s\")", "wrap.x (op-arg): expected Int64, got String"),
            ("r", "IP[String]", "first(5, 7)", "first.y (op-arg): expected String, got Int64"),
            ("l", "IP[String]", "first(\"a\", \"s\")", "first.x (op-arg): expected Int64, got String"),
        ] {
            let ns = format!("b15vslot{tag}{case}");
            assert_refused_naming(
                &load_errors_of(&program(&ns, &spell(recv, call))),
                &[token],
                &format!("{ns}: {recv}.{call}"),
            );
        }
    }
}

// ── B. a type in a rule-body call's argument ──────────────────────────────────────────────

/// A TYPE WRITTEN AS A RULE-BODY CALL'S ARGUMENT is the type an operation body holds for the same
/// text: a positional bound to its parameter, at any depth, through an alias, as a dot call's
/// argument, and beside a slot its default fills. Each term is 0 before.
///
/// FAILS with a rule-body call's type argument left as the operation-body walk built it: 0; and
/// with an alias's application read as its own name, refused at `CB[Int64]`.
#[test]
fn a_type_in_a_rule_body_calls_argument_is_the_type_an_operation_body_holds() {
    let sum = "bit(isIB(Box[Int64])) + 2 * bit(isIB(CB[Int64])) + 4 * bit(isIPS(Duo[Int64, \
               String])) + 8 * bit(isLIB(List[T = Box[Int64]])) + 16 * bit(isIB(Box.same(Box[Int64]))) \
               + 32 * bit(isDS(D[String]))";
    assert_eq!(run("b15vargop", &format!("  operation go() -> Int64 = {sum}")), Ok(63));
    assert_eq!(rule_answers("b15vargrule", &format!("  rule r(?n) :- ?n <=> {sum}")), vec![63]);
}

/// A FACT HOLDING THE TYPE is found by a goal reading the value a call's argument handed on.
///
/// FAILS with a rule-body call's type argument left unbound: no answer; and with an alias's
/// application read as its own name, refused.
#[test]
fn a_fact_holding_the_type_is_found_through_a_calls_argument() {
    let body = "  fact held(t: Box[V = Int64])\n  rule r(?n) :- ?t <=> idt(CB[Int64]), held(t: ?t), \
                ?n <=> 1";
    assert_eq!(rule_answers("b15vheld", body), vec![1]);
}

/// THE NAMED SPELLING was the type before: the control the rows above are measured against.
#[test]
fn a_named_entry_in_a_rule_body_calls_argument_was_already_the_type() {
    let sum = "bit(isIB(Box[V = Int64])) + 2 * bit(isIPS(Duo[L = Int64, R = String]))";
    assert_eq!(rule_answers("b15vargnamed", &format!("  rule r(?n) :- ?n <=> {sum}")), vec![3]);
}

// ── C. binding again what the alias fixes ─────────────────────────────────────────────────

/// BINDING AGAIN WHAT THE ALIAS FIXES is one report wherever it is written: the alias's refusal,
/// with no second "binds more than once" and nothing a reader of the alias's binding then finds
/// wrong with the written one.
///
/// A head's bound over a variable a guard bounds names the variable, not the guard's spec: it
/// was "'Tagger' is a type alias", beside the second report.
///
/// FAILS with the alias's binding left in place after the refusal: a parameter, an annotation,
/// a companion receiver, a rule head's bound, a provision, a bounding guard and a head's bound
/// over the variable a guard bounds report two to four; with an alias's application read as its
/// own name, the let-bound case reports two.
#[test]
fn binding_again_what_the_alias_fixes_is_one_report_wherever_it_is_written() {
    const TAG: &str = "  sort Tag\n    sort T = ?\n    operation tag(x: T) -> Int64\n  end\n";
    const TAGGER: &str = "  sort Tagger\n    sort C = ?\n    sort Out = ?\n    operation tag(x: C) -> \
                          Out\n  end\n  sort ITagger = Tagger[Out = Int64]\n  fact item(1)\n";
    for (tag, body) in [
        ("param", "  operation go(x: IP[L = Bool]) -> Int64 = 1".to_owned()),
        ("nested", "  operation go(x: List[T = IP[L = Bool]]) -> Int64 = 1".to_owned()),
        (
            "annot",
            "  operation go() -> Int64 =\n    let v: IP[L = Bool] = duo(l: true, r: \"s\")\n    1"
                .to_owned(),
        ),
        ("written", "  operation go() -> Bool = IP[L = Bool].first(true, \"s\")".to_owned()),
        ("bound", "  operation go() -> Bool =\n    let t = IP[L = Bool]\n    t.first(true, \"s\")".to_owned()),
        ("value", "  operation go() -> Type = IP[L = Bool]".to_owned()),
        ("fact", "  fact held(t: IP[L = Bool])".to_owned()),
        ("head", "  rule rr(?x: IP[L = Bool]) :- ?x <=> duo(l: true, r: \"s\")".to_owned()),
        (
            "provides",
            format!(
                "{TAG}  sort Prov\n    provides Tag[T = IP[L = Bool]]\n    operation tag(x: Duo[L = \
                 Bool]) -> Int64 = 1\n  end"
            ),
        ),
        ("guard", format!("{TAGGER}  rule ints[A](?x: A) :- item(?x), ITagger[C = A, Out = String]")),
    ] {
        let ns = format!("b15vagain{tag}");
        let errs = load_errors_of(&program(&ns, &body));
        assert_refused_naming(
            &errs,
            &["already binds", "which the application binds again"],
            &format!("{ns}: {body}"),
        );
        assert_eq!(errs.len(), 1, "{ns}: one report: {errs:#?}");
    }
    let body = format!("{TAGGER}  rule ints[A](?x: A[Out = String]) :- item(?x), ITagger[A]");
    let errs = load_errors_of(&program("b15vagainheadvar", &body));
    assert_refused_naming(
        &errs,
        &["the rule variable `A` is bounded by a guard that binds `Out` to `Int64`, which the \
           bound binds again"],
        "a head's bound over a guarded variable",
    );
    assert_eq!(errs.len(), 1, "one report: {errs:#?}");
}

/// A NAME WRITTEN TWICE after an alias is two mistakes and two reports: the alias's binding
/// written again, and the parameter written twice.
///
/// PASSES EITHER WAY, by design: the fence for a refusal that reports once per written key.
#[test]
fn a_name_written_twice_after_an_alias_is_two_reports() {
    for (tag, body) in [
        ("param", "  operation go(x: IP[L = Bool, L = String]) -> Int64 = 1"),
        ("value", "  operation go() -> Type = IP[L = Bool, L = String]"),
    ] {
        let ns = format!("b15vtwice{tag}");
        let errs = load_errors_of(&program(&ns, body));
        assert_refused_naming(
            &errs,
            &["which the application binds again", "binds the type parameter 'L' more than once"],
            &format!("{ns}: {body}"),
        );
        assert_eq!(errs.len(), 2, "{ns}: two reports: {errs:#?}");
    }
}

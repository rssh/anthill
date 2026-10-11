//! WI-20261011-2QZ3F — a `const`'s value is typed as an operation body is, and the typed
//! value is what is kept (kernel-language.md §5.3, §5.9).
//!
//! THE RULE. A `@[simp]` equation fires in a const's value on the calls it matches, a
//! dot call there becomes the call it dispatches to, and the evaluator, the purity gate
//! and the code generators read that text. With `operation dbl(n: Int64) -> Int64` and
//! `rule dbl(?n) <=> ?n + ?n @[simp]`, `const c: Int64 = dbl(4)` is 8.
//!
//! BEFORE. The value was typed with no equation applied and the typed text was dropped
//! (`typing/sorts.rs`, `check_constant_bodies`), and the evaluator ran the value as
//! written. The const loaded clean and its first read died `OperationBodyMissing`,
//! "operation has no body: …dbl"; a program that never read it ran to its end. Where the
//! operation had a body beside a guarded equation the const read the body's answer, a
//! different VALUE from the same call in an operation body, with nothing said.
//!
//! EVERY ROW HAS ITS OWN SOURCE.
//!
//! CONTROLS — each measured by backing the named piece out and running this file.
//!
//!   THE EQUATIONS OFF in `check_constant_bodies` (the gate read as off). FAIL, each
//!   dying `OperationBodyMissing` unless said:
//!     an_equation_defines_a_call_in_a_consts_value
//!     the_call_under_an_operator_is_rewritten_too
//!     the_call_is_read_at_every_site_of_the_value — the row stops at its first site;
//!       each of the seven was run alone against the tree before this change, and died
//!     a_sorts_const_is_typed_the_same
//!     an_equation_over_a_constructor_pattern_fires
//!     a_guarded_equation_decides_the_value — reads -2, the body's answer
//!     the_right_hand_side_may_name_a_const
//!     a_const_over_such_a_const
//!     a_rules_text_reads_an_internal_member_from_outside — both spellings
//!     a_spec_operation_in_the_right_hand_side_is_dispatched — both callers
//!     a_cycle_through_an_equation_is_told_as_a_cycle
//!     a_rewritten_value_is_held_to_the_declared_type — loads clean
//!     the_value_typed_again_is_the_same_value
//!     a_value_a_macro_spliced_is_admitted — dies on `Relation.where`, which the
//!       equation that hands it to the macro defines
//!   and the other dot rows pass: a dot call is dispatched with the equations off too.
//!
//!   THE WRITE-BACK OUT (the typed value dropped, the gate as it stands). FAIL: every
//!   row above but `a_rewritten_value_is_held_to_the_declared_type` — the relation's
//!   refused, "method/dot call" — and
//!     a_dot_call_of_an_effect_free_operation_is_admitted — refused, "method/dot call"
//!     a_field_read_by_dot_is_admitted — the same
//!     a_dot_call_of_an_effectful_operation_is_refused_by_name — refused, not by name
//!
//!   THE GATE'S `Spliced` LEAF OUT. FAIL:
//!     a_value_a_macro_spliced_is_admitted — refused, "unsupported expression form"
//!
//!   THE GATE TELLING A STANDING DOT WHATEVER ELSE WAS TOLD (`already_refused` not
//!   asked). FAIL, each on a second error that advises an operation:
//!     a_dot_the_typer_refuses_is_told_once
//!     a_value_the_typer_refuses_is_not_judged_for_its_dot
//!   THE GATE NEVER TELLING ONE. FAIL, loading clean:
//!     a_standing_dot_no_typer_run_refused_is_refused_by_the_gate
//!   Under `ANTHILL_TYPER_ORACLE=1` that row asserts the oracle's finding instead, and
//!   FAILS with the oracle's half of the const sweep out (`oracle_type_sealed_constants`
//!   not called): the later load is refused by the gate and nothing stops the run.
//!
//!   A CONST'S VALUE NOT HELD TO THE OPERATION-BODY REFUSALS (`TypingEnv::in_evaluated_-
//!   body` answering for an operation alone). FAIL, each loading clean:
//!     a_call_at_a_carrier_that_provides_no_such_spec_is_refused — and dies
//!       `OperationBodyMissing` when read
//!     a_defaulted_call_at_a_non_instance_is_refused — and reads the default's 1
//!     a_defaulted_call_whose_provision_is_conditional_and_unmet_is_refused — the same
//!
//!   PASS with all of it backed out, by design — what the change must not move:
//!     a_const_over_a_bodied_operation_reads_as_it_did
//!     the_same_call_in_an_operation_body_runs
//!     a_const_that_names_another_const
//!     a_clause_defined_call_in_a_const_is_still_refused
//!     an_equation_over_an_effectful_operation_is_refused_at_the_rule
//!     a_defaulted_call_at_an_instance_runs
//!
//!   BEHIND A SEAL the rows are in `wi_9bkz4_sealed_bodies_test`, section (1b): a later
//!   load's rule over a call in a sealed const's value is refused, one that reaches none
//!   loads, and a const of the program's own rewritten by a sealed equation stays the
//!   program's.
//!
//!   NOT COVERED, each the same in an operation body: a bare reference `const c: Int64 =
//!   tau` to a nullary operation an equation defines is not a redex (§5.4); an equation
//!   does not see through a binding. A const of a sort read dotted from outside the sort
//!   (`S.c`) did not resolve before this change and does not after.

use anthill_core::kb::load::{self, LoadOptions};
use anthill_core::kb::typing::{type_check_sorts, Loaded};

use crate::common::{
    assert_refused_naming, load_errors_of, load_in_a_later_call, load_kb_with, load_outcome,
    rendered_load_errors, run_int64,
};

/// `namespace test.<ns>` holding `decls`, with the names every row writes imported.
fn program(ns: &str, decls: &str) -> String {
    format!(
        "namespace test.{ns}\n  import anthill.prelude.{{Int64, Bool, String, List, Error, Function}}\n  import anthill.prelude.PartialOrd.{{lt}}\n{decls}\nend\n"
    )
}

/// `dbl`, defined by an equation alone.
const DBL: &str =
    "  operation dbl(n: Int64) -> Int64\n  rule dbl(?n) <=> ?n + ?n @[simp]\n";

/// A one-field `Box` with a bodied `open`.
const BOX: &str = "  sort Box\n    entity mk(v: Int64)\n    operation open(b: Box) -> Int64 =\n      match b\n        case mk(v) -> v\n  end\n";

/// A spec `Shown` and a `Leaf` that provides it, answering 7.
const SHOWN: &str = "  sort Shown\n    sort T = ?\n    operation show(x: T) -> Int64\n  end\n  sort Leaf\n    entity leaf\n    provides Shown[T = Leaf]\n    operation show(x: Leaf) -> Int64 = 7\n  end\n";

fn assert_reads(ns: &str, decls: &str, entry: &str, expected: i64) {
    let source = program(ns, decls);
    assert_eq!(
        run_int64(&source, &format!("test.{ns}.{entry}")),
        Ok(expected),
        "`{entry}` of:\n{source}"
    );
}

// ── The value ────────────────────────────────────────────────────────

/// The ticket's program.
#[test]
fn an_equation_defines_a_call_in_a_consts_value() {
    assert_reads(
        "q2a",
        &format!("{DBL}  const c: Int64 = dbl(4)\n  operation rd() -> Int64 = c"),
        "rd",
        8,
    );
}

/// The call is not the whole value.
#[test]
fn the_call_under_an_operator_is_rewritten_too() {
    assert_reads(
        "q2b",
        &format!(
            "{DBL}  operation three() -> Int64 = 3\n  const c: Int64 = three() + dbl(4)\n  operation rd() -> Int64 = c"
        ),
        "rd",
        11,
    );
}

/// One call at every site a value writes one: the equation reaches each.
#[test]
fn the_call_is_read_at_every_site_of_the_value() {
    let sites: [(&str, String, i64); 7] = [
        (
            "an `if` condition",
            format!("{DBL}  const c: Int64 = if dbl(1) > 1 then 1 else 0\n  operation rd() -> Int64 = c"),
            1,
        ),
        (
            "a `let`",
            format!("{DBL}  const c: Int64 =\n    let x = dbl(2)\n    x + 1\n  operation rd() -> Int64 = c"),
            5,
        ),
        (
            "a match arm's body",
            format!("{DBL}{BOX}  const c: Int64 =\n    match Box.mk(1)\n      case mk(v) -> dbl(v) + 10\n  operation rd() -> Int64 = c"),
            12,
        ),
        (
            "a match arm's guard",
            format!("{DBL}{BOX}  const c: Int64 =\n    match Box.mk(1)\n      case mk(v) | dbl(v) > 1 -> 5\n      case _ -> 0\n  operation rd() -> Int64 = c"),
            5,
        ),
        (
            "a constructor's argument",
            format!("{DBL}{BOX}  const p: Box = Box.mk(dbl(4))\n  operation rd() -> Int64 = Box.open(p)"),
            8,
        ),
        (
            "a list's element",
            format!("{DBL}  const xs: List[T = Int64] = [dbl(1), dbl(2)]\n  operation rd() -> Int64 =\n    match xs\n      case cons(h, t) -> h\n      case nil -> 0"),
            2,
        ),
        (
            "a lambda the const holds",
            format!("{DBL}  const f: Function[A = Int64, B = Int64] = lambda x -> dbl(x)\n  operation rd() -> Int64 =\n    let g = f\n    g(4)"),
            8,
        ),
    ];
    for (i, (site, decls, expected)) in sites.iter().enumerate() {
        let ns = format!("q2site{i}");
        let source = program(&ns, decls);
        assert_eq!(
            run_int64(&source, &format!("test.{ns}.rd")),
            Ok(*expected),
            "{site}:\n{source}"
        );
    }
}

/// A const a sort declares, over the sort's own operation and equation.
#[test]
fn a_sorts_const_is_typed_the_same() {
    assert_reads(
        "q2sort",
        "  sort S\n    entity s0\n    operation dbl(n: Int64) -> Int64\n    rule dbl(?n) <=> ?n + ?n @[simp]\n    const c: Int64 = dbl(4)\n    operation rd() -> Int64 = c\n  end",
        "S.rd",
        8,
    );
}

/// The left-hand side is a pattern over a constructor.
#[test]
fn an_equation_over_a_constructor_pattern_fires() {
    assert_reads(
        "q2pat",
        "  sort Box\n    entity mk(v: Int64)\n    operation open(b: Box) -> Int64\n    rule open(mk(v: ?v)) <=> ?v @[simp]\n  end\n  const c: Int64 = Box.open(Box.mk(4))\n  operation rd() -> Int64 = c",
        "rd",
        4,
    );
}

/// A guarded equation beside a BODY. Nothing died here before: the const read the
/// body's `-2` and the operation body beside it read the equation's `0`.
#[test]
fn a_guarded_equation_decides_the_value() {
    let decls = "  operation dbl(n: Int64) -> Int64 = n + n\n  rule dbl(?n) = 0 :- lt(?n, 0) @[simp]\n  const c: Int64 = dbl(-1)\n  const d: Int64 = dbl(3)\n  operation rc() -> Int64 = c\n  operation rd() -> Int64 = d\n  operation inBody() -> Int64 = dbl(-1)";
    assert_reads("q2guard", decls, "rc", 0);
    // The guard is refuted at 3, and an operation body always read the equation.
    assert_reads("q2guardd", decls, "rd", 6);
    assert_reads("q2guardb", decls, "inBody", 0);
}

/// The right-hand side names a const, and is read as the rule wrote it.
#[test]
fn the_right_hand_side_may_name_a_const() {
    assert_reads(
        "q2rhs",
        "  const K: Int64 = 3\n  operation plusk(n: Int64) -> Int64\n  rule plusk(?n) <=> ?n + K @[simp]\n  const c: Int64 = plusk(4)\n  operation rd() -> Int64 = c",
        "rd",
        7,
    );
}

#[test]
fn a_const_over_such_a_const() {
    assert_reads(
        "q2chain",
        &format!("{DBL}  const a: Int64 = dbl(4)\n  const b: Int64 = a + 1\n  operation rd() -> Int64 = b"),
        "rd",
        9,
    );
}

/// A rule's text is judged where the rule is written: its `internal` member is in reach
/// from a const outside the sort, named or by dot.
#[test]
fn a_rules_text_reads_an_internal_member_from_outside() {
    for (ns, rhs) in [("q2intn", "peek(?b)"), ("q2intd", "?b.peek()")] {
        assert_reads(
            ns,
            &format!(
                "  sort Box\n    entity mk(v: Int64)\n    internal operation peek(b: Box) -> Int64 =\n      match b\n        case mk(v) -> v\n    operation open(b: Box) -> Int64\n    rule open(?b) <=> {rhs} @[simp]\n  end\n  const c: Int64 = Box.open(Box.mk(4))\n  operation rd() -> Int64 = c"
            ),
            "rd",
            4,
        );
    }
}

/// A const has no requirement frame. A spec operation the equation writes is dispatched
/// where the value is typed, and so is an operation that requires the spec.
#[test]
fn a_spec_operation_in_the_right_hand_side_is_dispatched() {
    assert_reads(
        "q2spec",
        &format!(
            "{SHOWN}  operation sh(x: Leaf) -> Int64\n  rule sh(?x) <=> Shown.show(?x) @[simp]\n  const c: Int64 = sh(Leaf.leaf())\n  operation rd() -> Int64 = c"
        ),
        "rd",
        7,
    );
    assert_reads(
        "q2req",
        &format!(
            "{SHOWN}  operation show2[X](x: X) -> Int64\n    requires Shown[T = X]\n  = Shown.show(x)\n  operation sh(x: Leaf) -> Int64\n  rule sh(?x) <=> show2(?x) @[simp]\n  const c: Int64 = sh(Leaf.leaf())\n  operation rd() -> Int64 = c"
        ),
        "rd",
        7,
    );
}

/// An equation that leads back to the const: the cycle is the fold's to report.
#[test]
fn a_cycle_through_an_equation_is_told_as_a_cycle() {
    let source = program(
        "q2cyc",
        "  operation f() -> Int64\n  rule f() <=> c @[simp]\n  const c: Int64 = f()\n  operation rd() -> Int64 = c",
    );
    let died = run_int64(&source, "test.q2cyc.rd").expect_err("the read cannot answer");
    assert!(died.contains("ConstCycle"), "got: {died}");
}

/// The declared type is compared with the value as typed.
#[test]
fn a_rewritten_value_is_held_to_the_declared_type() {
    let errs = load_errors_of(&program(
        "q2ty",
        "  operation dbl(n: Int64) -> Int64\n  rule dbl(?n) <=> \"s\" @[simp]\n  const c: Int64 = dbl(4)",
    ));
    assert_refused_naming(
        &errs,
        &["c.value", "expected Int64", "got String"],
        "the equation's text is a String",
    );
}

/// A second typer run over the same KB finds the value typed and leaves it, and a copy
/// of the KB holds the typed value.
#[test]
fn the_value_typed_again_is_the_same_value() {
    let source = program(
        "q2again",
        &format!("{DBL}  const c: Int64 = dbl(4)\n  operation rd() -> Int64 = c"),
    );
    let mut kb = load_kb_with(&source);
    let again = type_check_sorts(&mut kb, Loaded::nothing());
    assert!(again.is_empty(), "typed again: {again:?}");
    let copy = kb.deep_clone().expect("the KB copies");
    for (which, kb) in [("the KB typed twice", kb), ("its copy", copy)] {
        let mut interp = anthill_core::eval::Interpreter::new(kb);
        anthill_core::eval::builtins::register_standard_builtins(&mut interp)
            .expect("standard builtins");
        match interp.call("test.q2again.rd", &[]) {
            Ok(anthill_core::eval::Value::Int(8)) => {}
            other => panic!("{which}: `rd` did not run to 8: {other:?}"),
        }
    }
}

// ── The purity gate reads the typed value ────────────────────────────

/// A dot call is the call it dispatched to by the time the gate reads it, and that
/// operation declares no effects.
#[test]
fn a_dot_call_of_an_effect_free_operation_is_admitted() {
    assert_reads(
        "q2dot",
        &format!("{BOX}  const c: Int64 = Box.mk(4).open()\n  operation rd() -> Int64 = c"),
        "rd",
        4,
    );
}

#[test]
fn a_field_read_by_dot_is_admitted() {
    assert_reads(
        "q2fld",
        &format!("{BOX}  const c: Int64 = Box.mk(4).v\n  operation rd() -> Int64 = c"),
        "rd",
        4,
    );
}

/// …and one that declares an effect is refused for it, by name.
#[test]
fn a_dot_call_of_an_effectful_operation_is_refused_by_name() {
    let errs = load_errors_of(&program(
        "q2fx",
        "  sort Box\n    entity mk(v: Int64)\n    operation risky(b: Box) -> Int64\n      effects Error\n    = 1\n  end\n  const c: Int64 = Box.mk(4).risky()",
    ));
    assert_refused_naming(
        &errs,
        &["test.q2fx.c", "calls effectful operation", "Box.risky"],
        "the dispatched call is effectful",
    );
}

/// A dot the typer could not dispatch is the typer's to tell, and is told once: the
/// gate does not add that its purity cannot be verified.
#[test]
fn a_dot_the_typer_refuses_is_told_once() {
    let errs = load_errors_of(&program(
        "q2nodot",
        "  operation three() -> Int64 = 3\n  const c: Int64 = 4.three()",
    ));
    assert_eq!(errs.len(), 1, "got: {errs:?}");
    assert_refused_naming(&errs, &["three", "no such member"], "`three` is no member of Int64");
}

/// Nor does it for a dot that would have dispatched, in a value refused for something
/// else: with the argument repaired this const loads and reads 4.
#[test]
fn a_value_the_typer_refuses_is_not_judged_for_its_dot() {
    let errs = load_errors_of(&program(
        "q2other",
        &format!(
            "{BOX}  operation takes(a: Int64, b: Int64) -> Int64 = a\n  const c: Int64 = takes(Box.mk(4).open(), \"s\")"
        ),
    ));
    assert_eq!(errs.len(), 1, "got: {errs:?}");
    assert_refused_naming(&errs, &["takes.b", "expected Int64", "got String"], "the argument");
}

/// A dot standing in a value NO typer run of the load refused is the gate's to refuse.
/// The one way there: a load refused for the dot, sealed all the same, and a load after
/// it — the sweep skips the sealed value, and nothing else stands before the evaluator.
#[test]
fn a_standing_dot_no_typer_run_refused_is_refused_by_the_gate() {
    let (mut kb, refused) = load_outcome(&program(
        "q2carry",
        "  operation three() -> Int64 = 3\n  const c: Int64 = 4.three()",
    ))
    .kb_and_errors();
    assert!(!refused.is_empty(), "the fixture: the first load is refused");
    load::seal_declarations(&mut kb);
    let mut load_later = || {
        load_in_a_later_call(
            &mut kb,
            "namespace test.q2carrylater\n  import anthill.prelude.{Int64}\n  operation one() -> Int64 = 1\nend\n",
            LoadOptions::default(),
        )
        .map(|_| ())
        .map_err(rendered_load_errors)
    };
    // `ANTHILL_TYPER_ORACLE=1` types the sealed value again and stops the run for what
    // that reports: the same finding by the instrument, and the row that drives the
    // oracle's half of the const sweep.
    if std::env::var("ANTHILL_TYPER_ORACLE").is_ok_and(|v| v == "1") {
        let stopped = std::panic::catch_unwind(std::panic::AssertUnwindSafe(load_later))
            .expect_err("the oracle stops a run in which a sealed value types differently");
        let said = stopped.downcast_ref::<String>().cloned().unwrap_or_default();
        assert!(
            said.contains("typing a sealed constant's value again reported"),
            "got: {said}"
        );
        return;
    }
    let later = load_later()
        .expect_err("a load over a KB whose sealed const holds a standing dot is refused");
    assert_refused_naming(&later, &["test.q2carry.c", "method/dot call"], "the gate's own refusal");
}

/// A compile-time macro leaves a value where its call stood (`where`'s query recipe),
/// and a value is pure: a const may hold the relation.
#[test]
fn a_value_a_macro_spliced_is_admitted() {
    let source = "namespace test.q2rel\n  import anthill.prelude.{Int64, String, List, Error, Relation}\n  import anthill.prelude.List.{length}\n  import anthill.prelude.PartialEq.{eq}\n  sort People\n    entity person(name: String, age: Int64)\n  end\n  fact person(name: \"alice\", age: 30)\n  fact person(name: \"bob\", age: 25)\n  fact person(name: \"carol\", age: 30)\n  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)\n  const thirty: Relation[T = (name: String, age: Int64)] = person_row.where(lambda c -> eq(c.age, 30))\n  operation rd() -> Int64 effects Error =\n    let r = thirty\n    length(r.takeN(100))\nend\n";
    assert_eq!(run_int64(source, "test.q2rel.rd"), Ok(2), "{source}");
}

/// The gate never meets an effect an equation spliced in: a rule over an effectful
/// operation is refused where it is written.
#[test]
fn an_equation_over_an_effectful_operation_is_refused_at_the_rule() {
    let errs = load_errors_of(&program(
        "q2rulefx",
        "  operation risky(n: Int64) -> Int64\n    effects Error\n  = n\n  operation dbl(n: Int64) -> Int64\n  rule dbl(?n) <=> risky(?n) @[simp]\n  const c: Int64 = dbl(4)",
    ));
    assert_refused_naming(&errs, &["risky"], "the rule's right-hand side is effectful");
}

// ── A value is held to what an operation body is ─────────────────────

/// A spec with one defaulted member and one abstract, and a `Vec3` that provides it not.
const DESC: &str = "  sort Vec3\n    entity v3(x: Int64)\n  end\n  sort Desc\n    sort T = ?\n    operation name(x: T) -> Int64 = 1\n    operation code(x: T) -> Int64\n  end\n";

/// `Fin`, provided by `Good`, and by `Wrap[S]` on the condition that `S` provides it.
const FIN: &str = "  sort Fin\n    sort C = ?\n    operation count(c: C) -> Int64 = 1\n    operation raw(c: C) -> Int64\n  end\n  sort Wrap\n    sort S = ?\n    entity wrap(s: S)\n  end\n  sort Good\n    entity good\n    provides Fin[C = Good]\n    operation raw(c: Good) -> Int64 = 2\n  end\n  sort Bad\n    entity bad\n  end\n  sort WrapFin\n    sort S = ?\n    requires Fin[C = S]\n    provides Fin[C = Wrap[S = S]]\n    operation raw(c: Wrap[S = S]) -> Int64 = 3\n  end\n";

/// A body-less spec operation at a carrier that provides no such spec has nothing to
/// run. The const is refused where the operation body is, in the same words.
#[test]
fn a_call_at_a_carrier_that_provides_no_such_spec_is_refused() {
    for (ns, site) in [
        ("q2nospecc", "  const c: Int64 = Shown.show(Other.other())"),
        ("q2nospeco", "  operation c() -> Int64 = Shown.show(Other.other())"),
    ] {
        let errs = load_errors_of(&program(
            ns,
            &format!("{SHOWN}  sort Other\n    entity other\n  end\n{site}"),
        ));
        assert_refused_naming(&errs, &["Shown.show", "Other` provides no"], site);
    }
}

/// A defaulted member at a carrier that is no instance would run the default for a
/// carrier that never took the spec on.
#[test]
fn a_defaulted_call_at_a_non_instance_is_refused() {
    for (ns, site) in [
        ("q2noinstc", "  const c: Int64 = Desc.name(Vec3.v3(1))"),
        ("q2noinsto", "  operation c() -> Int64 = Desc.name(Vec3.v3(1))"),
    ] {
        let errs = load_errors_of(&program(ns, &format!("{DESC}{site}")));
        assert_refused_naming(&errs, &["Desc.name", "Vec3` provides no"], site);
    }
}

/// `Wrap[S = Bad]` has a provision of `Fin`, on a condition `Bad` does not meet.
#[test]
fn a_defaulted_call_whose_provision_is_conditional_and_unmet_is_refused() {
    for (ns, site) in [
        ("q2condc", "  const c: Int64 = Fin.count(Wrap.wrap(Bad.bad()))"),
        ("q2condo", "  operation c() -> Int64 = Fin.count(Wrap.wrap(Bad.bad()))"),
    ] {
        let errs = load_errors_of(&program(ns, &format!("{FIN}{site}")));
        assert_refused_naming(&errs, &["Fin.count", "no impl matches", "Fin[C = "], site);
    }
}

/// …and where the condition is met the default runs, in both.
#[test]
fn a_defaulted_call_at_an_instance_runs() {
    assert_reads(
        "q2condok",
        &format!("{FIN}  const c: Int64 = Fin.count(Wrap.wrap(Good.good()))\n  operation rd() -> Int64 = c"),
        "rd",
        1,
    );
    assert_reads(
        "q2condokop",
        &format!("{FIN}  operation rd() -> Int64 = Fin.count(Wrap.wrap(Good.good()))"),
        "rd",
        1,
    );
}

// ── What does not move ───────────────────────────────────────────────

#[test]
fn a_const_over_a_bodied_operation_reads_as_it_did() {
    assert_reads(
        "q2bodied",
        "  operation three() -> Int64 = 3\n  const c: Int64 = three() + 1\n  operation rd() -> Int64 = c",
        "rd",
        4,
    );
}

#[test]
fn the_same_call_in_an_operation_body_runs() {
    assert_reads(
        "q2op",
        &format!("{DBL}  operation go() -> Int64 = dbl(4)"),
        "go",
        8,
    );
}

#[test]
fn a_const_that_names_another_const() {
    assert_reads(
        "q2alias",
        "  const a: Int64 = 5\n  const b: Int64 = a\n  operation rd() -> Int64 = b",
        "rd",
        5,
    );
}

/// An operation clauses alone define has nothing a call runs, and no equation to apply.
#[test]
fn a_clause_defined_call_in_a_const_is_still_refused() {
    let errs = load_errors_of(&program(
        "q2clause",
        "  operation four() -> Int64\n  rule four(4) :- true\n  const c: Int64 = four()",
    ));
    assert_refused_naming(&errs, &["four", "defined by clauses alone"], "no equation defines `four`");
}

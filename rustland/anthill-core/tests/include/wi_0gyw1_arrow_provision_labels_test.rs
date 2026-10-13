//! WI-20261013-0GYW1 — a provision at an arrow is looked up as two arrows are related: the
//! parameter lists by position, the names lining up or one list written without names.
//!
//! `sort P { provides Apply[F = (Int64, Int64) -> Int64] … }` and a call at `(p: Int64, q:
//! Int64) -> Int64`: one arrow where a value is passed (kernel-language §4.4) and where a
//! requirement is held against a call (§5.2), and two where a provision was looked up — the
//! call was refused, "no provision of `Apply` answers at `(p: Int64, q: Int64) -> Int64`".
//!
//! THE MECHANISM. `match_candidate_against_goal` read an arrow as an application of the
//! `Arrow` extractor and its parameter list as a named tuple whose `fields` were matched as
//! data, each field's name a leaf. A provision's arrow is now matched part by part, the
//! parts paired by `arrow_part_pairs` — the pairing the requirement cover (`parts_verdict`)
//! reads two arrows by: the parameters of a list by `TupleAlign::PARAM_LIST`.
//!
//! EVERY ROW DRIVES WHAT IT CLAIMS: the call runs, and each provider answers its own number,
//! so the answer names the provider reached. A refusal is asserted by its words.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! ONE PART — arm (1.5) of `match_candidate_against_goal` not taken, so an arrow reaches
//! arm (2) again. 9 FAIL of this file's 13, and each call a failing row makes was run
//! alone against the tree before the change, where it has the verdict the row's text says:
//! [`a_provider_at_the_arrow_without_names_answers_a_call_at_the_arrow_with_them`],
//! [`a_requirement_at_the_one_is_supplied_by_a_provider_at_the_other`],
//! [`a_selected_witness_at_the_other_spelling_supplies`],
//! [`a_list_of_any_length_is_paired_the_same`],
//! [`an_arrow_inside_another_type_is_matched_the_same`],
//! [`an_arrow_over_a_type_holding_a_value_is_matched_the_same`],
//! [`two_providers_that_differ_only_in_the_names_are_a_tie`],
//! [`a_provider_over_its_own_parameter_answers_at_either_spelling`] and
//! [`the_call_answers_wherever_it_is_written`].
//!
//! PASS EITHER WAY, by design: [`two_lists_of_unrelated_names_stay_two_arrows`] and
//! [`a_sole_parameter_is_its_type_and_a_tuple_there_is_data`], which say what the change
//! did not widen; [`two_providers_at_one_spelling_were_a_tie_already`], the rule the new
//! tie is an instance of; and [`one_carrier_at_both_spellings_is_one_candidate`], which
//! only one of its two provisions answered before.
//!
//! NOT COVERED HERE, and why:
//! * THE LOAD-TIME AGREEMENT OF ONE CARRIER'S PROVISIONS (`provision_bindings_agree`) still
//!   compares an arrow by identity: `provides Two[A = (Int64, Int64) -> Int64, B = Int64]`
//!   beside `provides Two[A = (p: Int64, q: Int64) -> Int64, B = String]` is two
//!   applications there and loads, and the two spellings at a second parameter of one
//!   application are a conflict. That check buckets, and the pairing is no equivalence —
//!   the list without names pairs with `(p, q)` and with `(x, y)`, which do not pair with
//!   each other; read by it, three provisions at the three lists were a conflict or not by
//!   the order they were written in (measured, and backed out).
//! * A CALL IN A RULE BODY. `rule r(?v) :- ?v = Apply.run(mk())` over a provider at
//!   `mk`'s own arrow does not run (the relation flounders), with or without names, so no
//!   row there tells the two spellings apart. The tie is refused there as in an operation
//!   body.
//! * A PROVIDER'S OWN PARAMETER STANDING TWICE in its arrow (`provides Apply[F = (A) -> A]`)
//!   is `provision_own_parameter_in_structural_type_test`'s: the rows here over such a
//!   provider bind it once.

use crate::common::{assert_refused_naming, interp_for, load_errors_of};
use anthill_core::eval::Value;

/// The arrow of two parameters written without names, with names, and with other names.
const BARE: &str = "(Int64, Int64) -> Int64";
const NAMED: &str = "(p: Int64, q: Int64) -> Int64";
const OTHER: &str = "(x: Int64, y: Int64) -> Int64";
/// A value of any of them; applied to `(1, 2)` it answers 1.
const FIRST: &str = "lambda (x: Int64, y: Int64) -> x";

/// The refusal of a call at an arrow no provision answers.
const NO_PROVISION: &[&str] = &["a tuple or an arrow, and no provision of", "answers at it"];

/// `Buf[T, N]` — `N` the value-in-type argument — `Box[T]`, whose value does not hold its
/// `T`, and the spec `Apply`, whose one parameter `F` is the type its operation receives.
/// `body` follows.
fn program(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, String, List, Error}}

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end

  sort Box
    sort T = ?
    entity box(n: Int64)
  end

  sort Apply
    sort F = ?
    operation run(f: F) -> Int64
  end
{body}
end
"#
    )
}

/// A sort `name` providing `Apply` at `at`; its `run` answers `answer`, which names it.
fn provider(name: &str, at: &str, answer: i64) -> String {
    format!(
        "\n  sort {name}\n    provides Apply[F = {at}]\n    \
         operation run(f: {at}) -> Int64 = {answer}\n  end\n"
    )
}

/// `operation via(f: {at}) -> Int64 = Apply.run(f)`.
fn via(at: &str) -> String {
    format!("\n  operation via(f: {at}) -> Int64 = Apply.run(f)\n")
}

/// `User requires Apply[F = {at}]`; its `via(f: {at})` calls `Apply.run(f)`.
fn user(at: &str) -> String {
    format!(
        "\n  sort User\n    requires Apply[F = {at}]\n    \
         operation via(f: {at}) -> Int64 = Apply.run(f)\n  end\n"
    )
}

/// `program(ns, body)` with `go() = {go}` appended.
fn with_go(ns: &str, body: &str, go: &str) -> String {
    program(ns, &format!("{body}\n  operation go() -> Int64 = {go}"))
}

/// [`with_go`], loaded, and `go` run.
fn answers(ns: &str, body: &str, go: &str) -> i64 {
    let src = with_go(ns, body, go);
    let mut interp = interp_for(&src);
    let entry = format!("{ns}.go");
    match interp.call(&entry, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{entry}` must run to an Int64: {other:?}\n{src}"),
    }
}

/// [`with_go`]'s load errors.
fn refusal(ns: &str, body: &str, go: &str) -> Vec<String> {
    load_errors_of(&with_go(ns, body, go))
}

// ── the ticket's programs ─────────────────────────────────────────────────────────────

/// THE TICKET'S PROGRAM (1) AND THE PAIR SWAPPED (2): the provider at the arrow written
/// without names and the call at the one with them, and the other way round. Each was
/// refused, "no provision of `Apply` answers at …".
#[test]
fn a_provider_at_the_arrow_without_names_answers_a_call_at_the_arrow_with_them() {
    for (name, provided, called) in [("bare_named", BARE, NAMED), ("named_bare", NAMED, BARE)] {
        let body = format!("{}{}", provider("P", provided, 30), via(called));
        assert_eq!(
            answers(&format!("wi0gyw1.call_{name}"), &body, &format!("via({FIRST})")),
            30,
            "a provider at `{provided}` answers a call at `{called}`"
        );
    }
    // The member reads its parameter by the names its own declaration writes, whichever
    // spelling the provision and the call have: `f(q: 1, p: 2)` hands 2 to the first slot.
    let body = format!(
        "\n  sort P\n    provides Apply[F = {BARE}]\n    \
         operation run(f: {NAMED}) -> Int64 = f(q: 1, p: 2)\n  end\n{}",
        via(OTHER)
    );
    assert_eq!(answers("wi0gyw1.call_member_names", &body, &format!("via({FIRST})")), 2);
}

/// THE TICKET'S PROGRAM (3): a sort's requirement at the one spelling, the only provider at
/// the other. `User.via(…)` was refused, "no impl provides `Apply`".
#[test]
fn a_requirement_at_the_one_is_supplied_by_a_provider_at_the_other() {
    for (name, provided, required) in [("bare_named", BARE, NAMED), ("named_bare", NAMED, BARE)] {
        let body = format!("{}{}", provider("P", provided, 30), user(required));
        assert_eq!(
            answers(&format!("wi0gyw1.requires_{name}"), &body, &format!("User.via({FIRST})")),
            30,
            "`requires Apply[F = {required}]` is supplied by a provider at `{provided}`"
        );
    }
}

/// THE TICKET'S PROGRAM (4): two providers at the one spelling, the requirement at the
/// other, and the call selects one. Refused, "the call selected `P2`, which provides no
/// instance at these bindings".
#[test]
fn a_selected_witness_at_the_other_spelling_supplies() {
    for (name, provided, required) in [("bare_named", BARE, NAMED), ("named_bare", NAMED, BARE)] {
        let body = format!(
            "{}{}{}",
            provider("P1", provided, 10),
            provider("P2", provided, 30),
            user(required)
        );
        assert_eq!(
            answers(
                &format!("wi0gyw1.selected_{name}"),
                &body,
                &format!("User.via[Apply = P2]({FIRST})")
            ),
            30,
            "`[Apply = P2]`, a provider at `{provided}`, supplies `requires Apply[F = {required}]`"
        );
    }
}

// ── the control: what stays two arrows ────────────────────────────────────────────────

/// TWO LISTS OF UNRELATED NAMES STAY TWO ARROWS, as they do where a value is passed: other
/// names, the same names in another order, one name of three different, and `_2, _1`, which
/// is not the list written without names. Each of the ticket's three shapes is refused as
/// it was. Passes with the change backed out, by design.
#[test]
fn two_lists_of_unrelated_names_stay_two_arrows() {
    let rows = [
        ("other", OTHER, NAMED, FIRST),
        ("permuted", "(q: Int64, p: Int64) -> Int64", NAMED, FIRST),
        (
            "one_of_three",
            "(p: Int64, x: Int64, r: Int64) -> Int64",
            "(p: Int64, q: Int64, r: Int64) -> Int64",
            "lambda (a: Int64, b: Int64, c: Int64) -> a",
        ),
        ("not_positional", "(_2: Int64, _1: Int64) -> Int64", NAMED, FIRST),
        (
            "another_count",
            BARE,
            "(p: Int64, q: Int64, r: Int64) -> Int64",
            "lambda (a: Int64, b: Int64, c: Int64) -> a",
        ),
        (
            "another_type",
            "(Int64, String) -> Int64",
            "(p: String, q: Int64) -> Int64",
            "lambda (a: String, b: Int64) -> b",
        ),
    ];
    for (name, provided, called, value) in rows {
        let body = format!("{}{}", provider("P", provided, 30), via(called));
        assert_refused_naming(
            &refusal(&format!("wi0gyw1.two_{name}"), &body, &format!("via({value})")),
            NO_PROVISION,
            &format!("a call at `{called}` beside a provider at `{provided}` alone"),
        );
    }
    let required = format!("{}{}", provider("P", OTHER, 30), user(NAMED));
    assert_refused_naming(
        &refusal("wi0gyw1.two_required", &required, &format!("User.via({FIRST})")),
        &["cannot be supplied", "no impl provides"],
        "`requires Apply[F = (p, q) -> …]` beside a provider at `(x, y) -> …` alone",
    );
    let selected = format!(
        "{}{}{}",
        provider("P1", OTHER, 10),
        provider("P2", OTHER, 30),
        user(NAMED)
    );
    assert_refused_naming(
        &refusal("wi0gyw1.two_selected", &selected, &format!("User.via[Apply = P2]({FIRST})")),
        &["cannot be supplied", "provides no instance at these bindings"],
        "`[Apply = P2]`, a provider at `(x, y) -> …`, for a requirement at `(p, q) -> …`",
    );
}

/// A LIST OF ANY LENGTH IS PAIRED THE SAME, with an effect row on the arrow as without one,
/// and the names `_1, _2` written out are the list written without names. Each was refused.
#[test]
fn a_list_of_any_length_is_paired_the_same() {
    let rows = [
        (
            "three",
            "(Int64, Int64, Int64) -> Int64",
            "(p: Int64, q: Int64, r: Int64) -> Int64",
            "lambda (a: Int64, b: Int64, c: Int64) -> a",
        ),
        ("written_positional", "(_1: Int64, _2: Int64) -> Int64", NAMED, FIRST),
        (
            "mixed_types",
            "(Int64, String) -> Int64",
            "(n: Int64, s: String) -> Int64",
            "lambda (a: Int64, b: String) -> a",
        ),
        (
            "effect_row",
            "(Int64, Int64) -> Int64 @ {Error[String]}",
            "(p: Int64, q: Int64) -> Int64 @ {Error[String]}",
            FIRST,
        ),
    ];
    for (name, provided, called, value) in rows {
        let body = format!("{}{}", provider("P", provided, 30), via(called));
        assert_eq!(
            answers(&format!("wi0gyw1.length_{name}"), &body, &format!("via({value})")),
            30,
            "a provider at `{provided}` answers a call at `{called}`"
        );
    }
}

/// A SOLE PARAMETER IS ITS TYPE: its name is no part of the arrow, and a tuple there is
/// data, compared by its labels in their order — two tuples of other labels, and a tuple
/// written without labels beside one with them, are two types. Passes with the change
/// backed out, by design: the change is to a parameter LIST.
#[test]
fn a_sole_parameter_is_its_type_and_a_tuple_there_is_data() {
    let body = format!("{}{}", provider("P", "(Int64) -> Int64", 30), via("(v: Int64) -> Int64"));
    assert_eq!(answers("wi0gyw1.sole_named", &body, "via(lambda (x: Int64) -> x)"), 30);
    let nullary = format!("{}{}", provider("P", "() -> Int64", 30), via("() -> Int64"));
    assert_eq!(answers("wi0gyw1.sole_nullary", &nullary, "via(lambda () -> 1)"), 30);
    let rows = [
        (
            "permuted",
            "((a: Int64, b: Int64)) -> Int64",
            "((b: Int64, a: Int64)) -> Int64",
            "lambda (t: (b: Int64, a: Int64)) -> 1",
        ),
        (
            "positional",
            "((Int64, Int64)) -> Int64",
            "((a: Int64, b: Int64)) -> Int64",
            "lambda (t: (a: Int64, b: Int64)) -> 1",
        ),
    ];
    for (name, provided, called, value) in rows {
        let body = format!("{}{}", provider("P", provided, 30), via(called));
        assert_refused_naming(
            &refusal(&format!("wi0gyw1.sole_{name}"), &body, &format!("via({value})")),
            NO_PROVISION,
            &format!("a call at `{called}` beside a provider at `{provided}` alone"),
        );
    }
}

// ── inside another type ───────────────────────────────────────────────────────────────

/// AN ARROW INSIDE ANOTHER TYPE IS MATCHED THE SAME: a parameter of an arrow, its result, a
/// parameter of a list, a component of a tuple, and an argument of an applied sort. Each of
/// the first five was refused.
///
/// The applied sort has two providers, `P1` at `Box[T = (Int64, Int64) -> Int64]` (10) and
/// `P2` at a `Box` of another arrow (30): a value of a sort is dispatched when the call
/// runs where no provision was matched, and with both left the call died there, "ambiguous
/// dispatch … on carrier `Box`". With a provider of unrelated names in `P1`'s place it
/// still does.
#[test]
fn an_arrow_inside_another_type_is_matched_the_same() {
    let rows = [
        (
            "param",
            format!("({BARE}) -> Int64"),
            format!("({NAMED}) -> Int64"),
            format!("lambda (g: {NAMED}) -> 1"),
        ),
        (
            "result",
            format!("(Int64) -> {BARE}"),
            format!("(Int64) -> {NAMED}"),
            "lambda (n: Int64) -> lambda (a: Int64, b: Int64) -> a".to_string(),
        ),
        (
            "in_a_list",
            format!("(Int64, {BARE}) -> Int64"),
            format!("(n: Int64, g: {NAMED}) -> Int64"),
            format!("lambda (n: Int64, g: {NAMED}) -> n"),
        ),
        (
            "tuple",
            format!("(Int64, {BARE})"),
            format!("(Int64, {NAMED})"),
            format!("(1, {FIRST})"),
        ),
        (
            "named_tuple",
            format!("(a: Int64, g: {BARE})"),
            format!("(a: Int64, g: {NAMED})"),
            format!("(a: 1, g: {FIRST})"),
        ),
    ];
    for (name, provided, called, value) in rows {
        let body = format!("{}{}", provider("P", &provided, 30), via(&called));
        assert_eq!(
            answers(&format!("wi0gyw1.inside_{name}"), &body, &format!("via({value})")),
            30,
            "a provider at `{provided}` answers a call at `{called}`"
        );
    }
    let boxed = |first: &str| {
        format!(
            "{}{}{}",
            provider("P1", &format!("Box[T = {first}]"), 10),
            provider("P2", "Box[T = (Int64) -> Int64]", 30),
            via(&format!("Box[T = {NAMED}]"))
        )
    };
    assert_eq!(answers("wi0gyw1.inside_applied", &boxed(BARE), "via(box(n: 1))"), 10);
    let src = with_go("wi0gyw1.inside_applied_other", &boxed(OTHER), "via(box(n: 1))");
    let mut interp = interp_for(&src);
    let died = interp.call("wi0gyw1.inside_applied_other.go", &[]);
    assert!(
        matches!(&died, Err(e) if format!("{e:?}").contains("AmbiguousSpecOpDispatch")),
        "a `Box` of an arrow of other names is matched by neither provider: {died:?}"
    );
    // … and unrelated names one level down stay two types.
    let body = format!(
        "{}{}",
        provider("P", &format!("({OTHER}) -> Int64"), 30),
        via(&format!("({NAMED}) -> Int64"))
    );
    assert_refused_naming(
        &refusal("wi0gyw1.inside_other", &body, &format!("via(lambda (g: {NAMED}) -> 1)")),
        NO_PROVISION,
        "an arrow whose parameter is an arrow of other names",
    );
}

/// A TYPE HOLDING A VALUE, which rides an occurrence, in a parameter and in the result: read
/// the same. Each was refused; with another value held (`N = 4` for `N = 3`) it still is.
#[test]
fn an_arrow_over_a_type_holding_a_value_is_matched_the_same() {
    let rows = [
        (
            "param",
            "(Buf[T = Int64, N = 3], Int64) -> Int64",
            "(b: Buf[T = Int64, N = 3], k: Int64) -> Int64",
            "lambda (b: Buf[T = Int64, N = 3], k: Int64) -> k",
        ),
        (
            "result",
            "(Int64, Int64) -> Buf[T = Int64, N = 3]",
            "(p: Int64, q: Int64) -> Buf[T = Int64, N = 3]",
            "lambda (p: Int64, q: Int64) -> buf(v: p)",
        ),
    ];
    for (name, provided, called, value) in rows {
        let body = format!("{}{}", provider("P", provided, 30), via(called));
        assert_eq!(
            answers(&format!("wi0gyw1.held_{name}"), &body, &format!("via({value})")),
            30,
            "a provider at `{provided}` answers a call at `{called}`"
        );
    }
    let body = format!(
        "{}{}",
        provider("P", "(Buf[T = Int64, N = 3], Int64) -> Int64", 30),
        via("(b: Buf[T = Int64, N = 4], k: Int64) -> Int64")
    );
    assert_refused_naming(
        &refusal(
            "wi0gyw1.held_other",
            &body,
            "via(lambda (b: Buf[T = Int64, N = 4], k: Int64) -> k)",
        ),
        NO_PROVISION,
        "a parameter holding another value",
    );
}

// ── two providers ─────────────────────────────────────────────────────────────────────

/// TWO PROVIDERS THAT DIFFER ONLY IN THE NAMES ARE TWO PROVIDERS AT ONE ARROW: a call at
/// either spelling selects none and is refused, and the bracket picks either. The call ran
/// the provider at its own spelling (30 at the arrow with names, 10 at the one without),
/// and the bracket naming the other was refused, "provides `Apply`, but not at the
/// bindings this call …". The bracket naming the provider at the call's own spelling —
/// `[Apply = P2]` at the arrow with names, `[Apply = P1]` at the one without — answered
/// as it does now, and passes with the change backed out.
#[test]
fn two_providers_that_differ_only_in_the_names_are_a_tie() {
    let both = format!("{}{}", provider("P1", BARE, 10), provider("P2", NAMED, 30));
    for (name, called) in [("named", NAMED), ("bare", BARE)] {
        assert_refused_naming(
            &refusal(
                &format!("wi0gyw1.tie_{name}"),
                &format!("{both}{}", via(called)),
                &format!("via({FIRST})"),
            ),
            &["ambiguous dispatch", "2 instances provide", "say which"],
            &format!("a call at `{called}` beside a provider at each spelling"),
        );
        for (witness, answer) in [("P1", 10), ("P2", 30)] {
            let picked = format!(
                "{both}\n  operation via(f: {called}) -> Int64 = Apply.run[Apply = {witness}](f)\n"
            );
            assert_eq!(
                answers(
                    &format!("wi0gyw1.tie_{name}_{}", witness.to_lowercase()),
                    &picked,
                    &format!("via({FIRST})")
                ),
                answer,
                "`[Apply = {witness}]` at a call at `{called}`"
            );
        }
    }
}

/// … THE RULE TWO PROVIDERS AT ONE SPELLING ARE HELD TO. Passes with the change backed out,
/// by design.
#[test]
fn two_providers_at_one_spelling_were_a_tie_already() {
    let both = format!("{}{}{}", provider("P1", BARE, 10), provider("P2", BARE, 30), via(BARE));
    assert_refused_naming(
        &refusal("wi0gyw1.tie_already", &both, &format!("via({FIRST})")),
        &["ambiguous dispatch", "2 instances provide", "say which"],
        "a call beside two providers at its own arrow",
    );
}

/// ONE CARRIER PROVIDING AT BOTH SPELLINGS HAS SAID ONE THING TWICE: its two provisions both
/// answer the call, and are one candidate, not a tie of the carrier with itself. Passes with
/// the change backed out, by design — only the provision at the call's spelling answered.
#[test]
fn one_carrier_at_both_spellings_is_one_candidate() {
    let body = format!(
        "\n  sort P\n    provides Apply[F = {BARE}]\n    provides Apply[F = {NAMED}]\n    \
         operation run(f: {BARE}) -> Int64 = 30\n  end\n{}",
        via(NAMED)
    );
    assert_eq!(answers("wi0gyw1.one_carrier", &body, &format!("via({FIRST})")), 30);
}

// ── a provider over its own parameter ─────────────────────────────────────────────────

/// A PROVIDER OVER ITS OWN PARAMETER, `provides Apply[F = (A, A) -> A]`, answers at either
/// spelling, and its own names are held to the call's as a concrete provider's are. The
/// first two were refused.
#[test]
fn a_provider_over_its_own_parameter_answers_at_either_spelling() {
    let generic = |at: &str| {
        format!(
            "\n  sort P\n    sort A = ?\n    provides Apply[F = {at}]\n    \
             operation run(f: {at}) -> Int64 = 30\n  end\n"
        )
    };
    for (name, provided, called) in [
        ("bare_named", "(A, A) -> A", NAMED),
        ("named_bare", "(a: A, b: A) -> A", BARE),
    ] {
        let body = format!("{}{}", generic(provided), via(called));
        assert_eq!(
            answers(&format!("wi0gyw1.generic_{name}"), &body, &format!("via({FIRST})")),
            30,
            "a provider at `{provided}` answers a call at `{called}`"
        );
    }
    let body = format!("{}{}", generic("(a: A, b: A) -> A"), via(NAMED));
    assert_refused_naming(
        &refusal("wi0gyw1.generic_other", &body, &format!("via({FIRST})")),
        NO_PROVISION,
        "a provider at `(a: A, b: A) -> A` beside a call at `(p: Int64, q: Int64) -> Int64`",
    );
}

// ── wherever the call is written ──────────────────────────────────────────────────────

/// WHEREVER THE CALL IS WRITTEN, and however the two arrows are named: a condition, a
/// lambda's body, a match guard, a `let` of the type, the type in the call's brackets (each
/// way round), the operation imported, the arrows behind aliases, an operation taken as a
/// value, a `const`, and an operation's own `requires` over its type parameter. Each was
/// refused.
#[test]
fn the_call_answers_wherever_it_is_written() {
    let p = provider("P", BARE, 30);
    let bodies = [
        (
            "condition",
            format!("\n  operation via(f: {NAMED}) -> Int64 = if Apply.run(f) > 20 then 30 else 0\n"),
        ),
        (
            "lambda",
            format!(
                "\n  operation via(f: {NAMED}) -> Int64 =\n    \
                 let h = lambda (g: {NAMED}) -> Apply.run(g)\n    h(f)\n"
            ),
        ),
        (
            "guard",
            format!(
                "\n  operation via(f: {NAMED}) -> Int64 =\n    let n: Int64 = 3\n    match n\n      \
                 case k | Apply.run(f) > 20 -> 30\n      case _ -> 0\n"
            ),
        ),
        (
            "let",
            format!(
                "\n  operation via(f: {BARE}) -> Int64 =\n    let g: {NAMED} = f\n    Apply.run(g)\n"
            ),
        ),
        (
            "bracket",
            format!("\n  operation via(f: {BARE}) -> Int64 = Apply.run[F = {NAMED}](f)\n"),
        ),
        (
            "import",
            format!(
                "\n  import wi0gyw1.site_import.Apply.run\n  \
                 operation via(f: {NAMED}) -> Int64 = run(f)\n"
            ),
        ),
    ];
    for (name, body) in bodies {
        assert_eq!(
            answers(
                &format!("wi0gyw1.site_{name}"),
                &format!("{p}{body}"),
                &format!("via({FIRST})")
            ),
            30,
            "the call written in a {name}"
        );
    }
    let bracket_bare = format!(
        "{}\n  operation use() -> Int64 = Apply.run[F = {BARE}]({FIRST})\n",
        provider("P", NAMED, 30)
    );
    assert_eq!(answers("wi0gyw1.site_bracket_bare", &bracket_bare, "use()"), 30);
    let aliased = format!(
        "\n  sort FnBare = {BARE}\n  sort FnNamed = {NAMED}\n{}{}",
        provider("P", "FnBare", 30),
        via("FnNamed")
    );
    assert_eq!(answers("wi0gyw1.site_alias", &aliased, &format!("via({FIRST})")), 30);
    let eta = format!(
        "{p}\n  operation add(a: Int64, b: Int64) -> Int64 = a + b\n  \
         operation use() -> Int64 =\n    let g: {NAMED} = add\n    Apply.run(g)\n"
    );
    assert_eq!(answers("wi0gyw1.site_eta", &eta, "use()"), 30);
    let constant = format!(
        "{p}\n  operation mk() -> {NAMED} = {FIRST}\n  const k: Int64 = Apply.run(mk())\n"
    );
    assert_eq!(answers("wi0gyw1.site_const", &constant, "k"), 30);
    let own_requires = format!(
        "{}\n  operation via[T](f: (T, T) -> T) -> Int64 requires Apply[F = (T, T) -> T] = \
         Apply.run(f)\n",
        provider("P", NAMED, 30)
    );
    assert_eq!(
        answers("wi0gyw1.site_own_requires", &own_requires, &format!("via[T = Int64]({FIRST})")),
        30
    );
}

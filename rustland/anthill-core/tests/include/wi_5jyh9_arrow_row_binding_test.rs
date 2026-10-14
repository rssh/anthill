//! WI-20261014-5JYH9 — two arrows are one binding where a provision is looked up, and where a
//! requirement is held against a call, only when their effect rows are the same row
//! (kernel-language §5.2; the user's decision, 2026-10-14: identical rows, not one row
//! conforming to the other).
//!
//! The lookup paired an arrow's parts and handed the two rows to its leaf arm, whose last leg
//! compares heads, and every row has the head `effects_rows`: any row matched any other. So
//! `sort Q { provides Apply[F = (Int64) -> Int64]  operation run(f: (Int64) -> Int64) -> Int64
//! = f(41) }`, reached by `Apply.run(f)` over `f: (Int64) -> Int64 @ {ConsoleOutput}`, ran a
//! function that printed inside a member declared over a pure one — and the same through
//! `requires Apply[F = (Int64) -> Int64]`, whose cover read a row as a leaf too. Passed to an
//! operation taking `(Int64) -> Int64` directly, the same function is refused.
//!
//! A provider that answers at any row writes a row parameter (`@ {R}`); the lookup binds it to
//! the call's row, or to what the call's row has beside the labels written next to it, and the
//! provider's `requires` and conditions are read at that row. A row's tail is the parameter's
//! variable in a clause and its labels are types, so `Error[T = A]` in a row binds and holds
//! `A` as a parameter anywhere in the binding does.
//!
//! EVERY ROW DRIVES WHAT IT CLAIMS: the call runs and answers the provider's number, or the
//! load is refused naming the arrow with its row.
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! MEASURED 2026-10-14, one part at a time, each switched in one build:
//!
//! 1. THE LOOKUP TAKING A ROW FOR A LEAF (`match_candidate_rows` answering yes): 9 of the 11
//!    rows the file had then fail — all but [`a_rows_labels_are_one_row_in_any_order`] and
//!    [`default_marks_at_arrows_compare_rows`]; 7 and 8 below were measured after it.
//! 2. THE COVER TAKING A ROW FOR A LEAF (`rows_verdict` answering precise):
//!    [`a_member_over_a_pure_function_is_not_handed_an_effectful_one`] (its requirement half)
//!    and [`the_requirement_cover_compares_rows`].
//! 3. THE PROVIDER'S ROW PARAMETER NOT PUT INTO ITS REQUIREMENTS (`row_tails_at` answering
//!    `v`): [`the_providers_requirement_and_condition_are_read_at_the_bound_row`], and
//!    `wi_34822_clause_parameter_one_spelling_test::a_requirement_at_a_tuple_or_an_arrow_of_
//!    the_parameter_is_supplied`, whose arrow rows at `@ {R}` the lookup now binds.
//! 4. THE CLAUSE CANON STOPPING AT THE WHOLE ROW, a label's parameter left a variable:
//!    [`a_type_parameter_in_a_label_is_held_to_one_type`].
//! 5. DEFAULT MARKS' ROWS COMPARED AS WRITTEN (`structural_views_overlap` without the open
//!    row): [`default_marks_at_arrows_compare_rows`].
//! 6. AN ARROW'S ROW LEFT OUT OF THE MESSAGES (`arrow_row_shown` answering `None`): the three
//!    rows whose refusals name a row — [`a_member_over_a_pure_function_is_not_handed_an_
//!    effectful_one`], [`default_marks_at_arrows_compare_rows`] and [`the_providers_
//!    requirement_and_condition_are_read_at_the_bound_row`].
//!
//! 7. THE COVER TAKING THE SCOPE'S OWN ROW PARAMETER FOR A TAIL NOTHING HAS DETERMINED
//!    (`rows_verdict`'s `undetermined` always yes):
//!    [`a_requirement_at_the_callers_row_does_not_serve_another_row`] (99 for 91).
//! 8. AN OPEN ROW OVERLAPPING EVERY ROW (`rows_overlap` before its labels were compared):
//!    [`default_marks_at_arrows_compare_rows`], its marks at `@ {ConsoleOutput, R}` beside
//!    the pure arrow refused as overlapping.
//!
//! PASSES UNDER EVERY BACK-OUT, by design: [`a_rows_labels_are_one_row_in_any_order`], the
//! control that one row is one row in any order — a leaf matched it too.

use crate::common::{assert_refused_naming, interp_for, load_errors_of};
use anthill_core::eval::Value;

/// `Apply`, whose parameter is the type its operation receives, and `Mark`, a spec a provider
/// requires; then `body`.
fn program(ns: &str, body: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.Console.{{console, println, ConsoleOutput}}
  import anthill.prelude.{{Int64, String, List, Error, Cell, Modify}}

  sort Apply
    sort F = ?
    operation run(f: F) -> Int64
  end

  sort Mark
    sort T = ?
    operation mark(x: T) -> Int64
  end
{body}
end
"#
    )
}

/// A provider of `Apply` named `name` at `at`, answering `n`.
fn provider(name: &str, at: &str, n: i64) -> String {
    format!(
        "\n  sort {name}\n    provides Apply[F = {at}]\n    \
         operation run(f: {at}) -> Int64 = {n}\n  end\n"
    )
}

/// `AnyRow`, providing `Apply` at `(Int64) -> Int64 @ {{R}}` with `clauses` beside, answering 9.
fn any_row(clauses: &str) -> String {
    format!(
        "\n  sort AnyRow\n    effects R = ?\n{clauses}    \
         provides Apply[F = (Int64) -> Int64 @ {{R}}]\n    \
         operation run(f: (Int64) -> Int64 @ {{R}}) -> Int64 = 9\n  end\n"
    )
}

/// `MarkAt`, providing `Mark` at `at`.
fn mark_at(at: &str) -> String {
    format!(
        "\n  sort MarkAt\n    provides Mark[T = {at}]\n    \
         operation mark(x: {at}) -> Int64 = 1\n  end\n"
    )
}

/// `operation {name}(f: {at}) -> Int64{effects} = Apply.run(f)`.
fn via(name: &str, at: &str, effects: &str) -> String {
    format!("\n  operation {name}(f: {at}) -> Int64{effects} = Apply.run(f)\n")
}

/// `body` and `operation go() -> Int64{effects} = {go}`, run.
fn answers(ns: &str, body: &str, go: &str, effects: &str) -> i64 {
    let src = program(
        ns,
        &format!("{body}\n  operation go() -> Int64{effects} = {go}\n"),
    );
    let mut interp = interp_for(&src);
    let entry = format!("{ns}.go");
    match interp.call(&entry, &[]) {
        Ok(Value::Int(n)) => n,
        other => panic!("`{entry}` must run to an Int64: {other:?}\n{src}"),
    }
}

fn refusal(ns: &str, body: &str) -> Vec<String> {
    load_errors_of(&program(ns, body))
}

const PURE: &str = "(Int64) -> Int64";
const LOGS: &str = "(Int64) -> Int64 @ {ConsoleOutput}";
const ID: &str = "lambda (x: Int64) -> x";
const NO_PROVISION: &[&str] = &["a tuple or an arrow, and no provision of", "answers at it"];

/// THE SOUNDNESS ROWS: a member declared over a pure function is not handed one that writes
/// to the console, through a provision or through a requirement. Each loaded and printed.
#[test]
fn a_member_over_a_pure_function_is_not_handed_an_effectful_one() {
    let printing = "\n  operation go() -> Int64 effects ConsoleOutput =\n    \
                    via(lambda (x: Int64) ->\n      let _ = println(console(), \"hi\")\n      \
                    x + 1)\n";
    let q = "\n  sort Q\n    provides Apply[F = (Int64) -> Int64]\n    \
             operation run(f: (Int64) -> Int64) -> Int64 = f(41)\n  end\n";
    let through_provision = format!(
        "{q}{}{printing}",
        via("via", LOGS, " effects ConsoleOutput")
    );
    assert_refused_naming(
        &refusal("w5jyh9.sound_provision", &through_provision),
        &[
            "its carrier is `Int64 -> Int64 @ {ConsoleOutput}`",
            NO_PROVISION[1],
        ],
        "a pure provider beside a call at an arrow that prints",
    );
    let through_requirement = format!(
        "{q}\n  sort User\n    requires Apply[F = (Int64) -> Int64]\n    \
         operation go2(f: {LOGS}) -> Int64 effects ConsoleOutput = Apply.run(f)\n  end\n\
         \n  operation via(f: {LOGS}) -> Int64 effects ConsoleOutput = User.go2(f)\n{printing}"
    );
    assert_refused_naming(
        &refusal("w5jyh9.sound_requirement", &through_requirement),
        &["Int64 -> Int64 @ {ConsoleOutput}"],
        "a requirement at the pure arrow over a body call at an arrow that prints",
    );
}

/// A LONE PROVIDER ANSWERS AT ITS OWN ROW AND AT NO OTHER: each pair was answered (40) by the
/// provider at the first row for a call at the second; at its own row it answers.
#[test]
fn a_lone_provider_answers_only_at_its_own_row() {
    let rows = [
        (
            "raise_string_at_int",
            "(Int64) -> Int64 @ {Error[T = String]}",
            "(Int64) -> Int64 @ {Error[T = Int64]}",
            " effects Error[T = Int64]",
        ),
        (
            "raise_at_pure",
            "(Int64) -> Int64 @ {Error[T = String]}",
            PURE,
            "",
        ),
        ("pure_at_logs", PURE, LOGS, " effects ConsoleOutput"),
        (
            "logs_at_raise",
            LOGS,
            "(Int64) -> Int64 @ {Error[T = Int64]}",
            " effects Error[T = Int64]",
        ),
    ];
    for (name, provided, called, effects) in rows {
        let body = format!(
            "{}{}",
            provider("Q", provided, 40),
            via("via", called, effects)
        );
        let errs = refusal(
            &format!("w5jyh9.lone_{name}"),
            &format!("{body}\n  operation go() -> Int64{effects} = via({ID})\n"),
        );
        assert_refused_naming(
            &errs,
            NO_PROVISION,
            &format!("a provider at `{provided}` beside a call at `{called}`"),
        );
        let own_effects = if provided == PURE {
            String::new()
        } else if provided == LOGS {
            " effects ConsoleOutput".to_string()
        } else {
            " effects Error[T = String]".to_string()
        };
        let at_own = format!(
            "{}{}",
            provider("Q", provided, 40),
            via("via", provided, &own_effects)
        );
        assert_eq!(
            answers(
                &format!("w5jyh9.own_{name}"),
                &at_own,
                &format!("via({ID})"),
                &own_effects
            ),
            40,
            "the provider at `{provided}` answers at its own row"
        );
    }
}

/// TWO PROVIDERS WHOSE ARROWS DIFFER ONLY IN THE ROW ARE TWO BINDINGS, each answering at its
/// own: both calls were refused as a tie.
#[test]
fn two_providers_differing_only_in_the_row_are_two_bindings() {
    let body = format!(
        "{}{}{}{}",
        provider("Q", PURE, 1),
        provider("Logger", LOGS, 7),
        via("viaPure", PURE, ""),
        via("viaLog", LOGS, " effects ConsoleOutput")
    );
    assert_eq!(
        answers(
            "w5jyh9.two",
            &body,
            &format!("viaPure({ID}) * 10 + viaLog({ID})"),
            " effects ConsoleOutput"
        ),
        17
    );
}

/// A ROW PARAMETER TAKES THE CALL'S ROW: `AnyRow` at `@ {R}` answers a call at a row and at the
/// caller's own row parameter, and beside `Q` at the pure arrow the pure call is `Q`'s, the
/// more specific. A provider at the pure arrow does not answer a call at the caller's row
/// parameter, nor does a requirement need it there when one is written at that row.
#[test]
fn a_row_parameter_takes_the_calls_row() {
    let beside = format!(
        "{}{}{}{}",
        any_row(""),
        provider("Q", PURE, 1),
        via("viaPure", PURE, ""),
        via("viaLog", LOGS, " effects ConsoleOutput")
    );
    assert_eq!(
        answers(
            "w5jyh9.any_beside",
            &beside,
            &format!("viaPure({ID}) * 10 + viaLog({ID})"),
            " effects ConsoleOutput"
        ),
        19
    );
    let generic =
        "\n  operation viaE[E](f: (Int64) -> Int64 @ {E}) -> Int64 effects E = Apply.run(f)\n";
    assert_eq!(
        answers(
            "w5jyh9.callers_row",
            &format!("{}{generic}", any_row("")),
            &format!("viaE({ID})"),
            ""
        ),
        9
    );
    let required = "\n  operation viaE[E](f: (Int64) -> Int64 @ {E}) -> Int64 effects E \
                    requires Apply[F = (Int64) -> Int64 @ {E}] = Apply.run(f)\n";
    assert_eq!(
        answers(
            "w5jyh9.callers_row_required",
            &format!("{}{required}", any_row("")),
            &format!("viaE({ID})"),
            ""
        ),
        9
    );
    assert_refused_naming(
        &refusal(
            "w5jyh9.callers_row_pure",
            &format!("{}{generic}", provider("Q", PURE, 1)),
        ),
        NO_PROVISION,
        "a provider at the pure arrow beside a call at the caller's row parameter",
    );
}

/// THE PROVIDER'S REQUIREMENT AND ITS PROVISION'S CONDITION ARE READ AT THE ROW THE CALL BINDS:
/// `Mark` at `@ {ConsoleOutput}` supplies them for a call at that row, and a call at the pure
/// arrow is refused naming `Mark` at the pure arrow. A requirement was asked at `@ {?R}`, which
/// no provision at a closed row answers, and before the rows were compared any `Mark` did.
#[test]
fn the_providers_requirement_and_condition_are_read_at_the_bound_row() {
    for (name, clauses) in [
        (
            "requires",
            "    requires Mark[T = (Int64) -> Int64 @ {R}]\n",
        ),
        ("condition", ""),
    ] {
        let anyrow = if clauses.is_empty() {
            "\n  sort AnyRow\n    effects R = ?\n    \
             provides Apply[F = (Int64) -> Int64 @ {R}] :- Mark[T = (Int64) -> Int64 @ {R}]\n    \
             operation run(f: (Int64) -> Int64 @ {R}) -> Int64 = 9\n  end\n"
                .to_string()
        } else {
            any_row(clauses)
        };
        let at_logs = format!(
            "{}{anyrow}{}",
            mark_at(LOGS),
            via("viaLog", LOGS, " effects ConsoleOutput")
        );
        assert_eq!(
            answers(
                &format!("w5jyh9.{name}_logs"),
                &at_logs,
                &format!("viaLog({ID})"),
                " effects ConsoleOutput"
            ),
            9,
            "`{name}` at the call's row"
        );
        let at_pure = format!("{}{anyrow}{}", mark_at(LOGS), via("viaPure", PURE, ""));
        assert_refused_naming(
            &refusal(&format!("w5jyh9.{name}_pure"), &at_pure),
            &["no impl matches", "Mark[T = Int64 -> Int64]"],
            &format!("`{name}` at the pure arrow, `Mark` only at `@ {{ConsoleOutput}}`"),
        );
        let raising = "(Int64) -> Int64 @ {Error[T = String]}";
        let other_row = format!(
            "{}{anyrow}{}",
            mark_at(raising),
            via("viaLog", LOGS, " effects ConsoleOutput")
        );
        assert_refused_naming(
            &refusal(&format!("w5jyh9.{name}_other"), &other_row),
            &[
                "no impl matches",
                "Mark[T = Int64 -> Int64 @ {ConsoleOutput}]",
            ],
            &format!("`{name}` at `@ {{ConsoleOutput}}`, `Mark` only at `@ {{Error[T = String]}}`"),
        );
    }
}

/// A TYPE PARAMETER IN A LABEL IS HELD TO ONE TYPE: `P` at `(A) -> A @ {Error[T = A]}` answers
/// at `Error[T = Int64]` beside `Int64`, and not at `Error[T = String]` (it did, 30) nor at the
/// pure arrow.
#[test]
fn a_type_parameter_in_a_label_is_held_to_one_type() {
    let p = "\n  sort P\n    sort A = ?\n    provides Apply[F = (A) -> A @ {Error[T = A]}]\n    \
             operation run(f: (A) -> A @ {Error[T = A]}) -> Int64 = 30\n  end\n";
    let at_int = format!(
        "{p}{}",
        via(
            "via",
            "(Int64) -> Int64 @ {Error[T = Int64]}",
            " effects Error[T = Int64]"
        )
    );
    assert_eq!(
        answers(
            "w5jyh9.label_int",
            &at_int,
            &format!("via({ID})"),
            " effects Error[T = Int64]"
        ),
        30
    );
    for (name, called, effects) in [
        (
            "string",
            "(Int64) -> Int64 @ {Error[T = String]}",
            " effects Error[T = String]",
        ),
        ("pure", PURE, ""),
    ] {
        let body = format!("{p}{}", via("via", called, effects));
        assert_refused_naming(
            &refusal(&format!("w5jyh9.label_{name}"), &body),
            NO_PROVISION,
            &format!("`P` at a call at `{called}`"),
        );
    }
}

/// THE REQUIREMENT COVER COMPARES ROWS: a requirement at `@ {ConsoleOutput}` covers a body call
/// at that row, and a body call at the pure arrow is not read by it — `Q` answers it.
#[test]
fn the_requirement_cover_compares_rows() {
    let user = |go_at: &str, effects: &str| {
        format!(
            "{}{}\n  sort User\n    requires Apply[F = {LOGS}]\n    \
             operation go2(f: {go_at}) -> Int64{effects} = Apply.run(f)\n  end\n",
            provider("Logger", LOGS, 7),
            provider("Q", PURE, 1)
        )
    };
    assert_eq!(
        answers(
            "w5jyh9.cover_logs",
            &user(LOGS, " effects ConsoleOutput"),
            &format!("User.go2({ID})"),
            " effects ConsoleOutput"
        ),
        7
    );
    assert_eq!(
        answers(
            "w5jyh9.cover_pure",
            &user(PURE, ""),
            &format!("User.go2({ID})"),
            ""
        ),
        1
    );
}

/// A REQUIREMENT AT THE CALLER'S OWN ROW PARAMETER DOES NOT SERVE A CALL AT ANOTHER ROW:
/// inside `viaE[E]`, which requires `Apply` at `@ {E}`, `Apply.run(f)` at `@ {E}` reads the
/// requirement — `AnyRow`'s, `E` being `{ConsoleOutput}` at the call (9) — and `Apply.run(g)`
/// at the pure arrow is `Q`'s (1). Read by the requirement, the second answered 9 too.
#[test]
fn a_requirement_at_the_callers_row_does_not_serve_another_row() {
    let body = format!(
        "{}{}
  operation viaE[E](f: (Int64) -> Int64 @ {{E}}, g: {PURE}) -> Int64 effects E \
         requires Apply[F = (Int64) -> Int64 @ {{E}}] =\n    Apply.run(f) * 10 + Apply.run(g)\n\
         \n  operation callIt(f: {LOGS}) -> Int64 effects ConsoleOutput = viaE(f, {ID})\n",
        any_row(""),
        provider("Q", PURE, 1)
    );
    assert_eq!(
        answers(
            "w5jyh9.callers_row_other",
            &body,
            &format!("callIt({ID})"),
            " effects ConsoleOutput"
        ),
        91
    );
}

/// A ROW IS A SET: two labels written in the other order are one row.
#[test]
fn a_rows_labels_are_one_row_in_any_order() {
    let effects = " effects {ConsoleOutput, Error[T = String]}";
    let body = format!(
        "{}{}",
        provider(
            "Two",
            "(Int64) -> Int64 @ {ConsoleOutput, Error[T = String]}",
            12
        ),
        via(
            "via",
            "(Int64) -> Int64 @ {Error[T = String], ConsoleOutput}",
            effects
        )
    );
    assert_eq!(
        answers("w5jyh9.order", &body, &format!("via({ID})"), effects),
        12
    );
}

/// DEFAULT MARKS: at `@ {R}` beside the pure arrow they overlap, a load error naming both
/// carriers with their rows; at two closed rows they coexist, each call answered by its own.
#[test]
fn default_marks_at_arrows_compare_rows() {
    let marks = |first: &str, first_row: &str, second: &str| {
        format!(
            "\n  sort D1\n{first_row}    default provides Apply[F = {first}]\n    \
             operation run(f: {first}) -> Int64 = 1\n  end\n  \
             sort D2\n    default provides Apply[F = {second}]\n    \
             operation run(f: {second}) -> Int64 = 2\n  end\n"
        )
    };
    let overlapping = format!(
        "{}{}",
        marks("(Int64) -> Int64 @ {R}", "    effects R = ?\n", PURE),
        via("viaPure", PURE, "")
    );
    assert_refused_naming(
        &refusal("w5jyh9.defaults_overlap", &overlapping),
        &[
            "overlapping defaults",
            "'Int64 -> Int64 @ {",
            "'Int64 -> Int64'",
        ],
        "default marks at `@ {R}` and at the pure arrow",
    );
    let apart = format!(
        "{}{}{}",
        marks(LOGS, "", PURE),
        via("viaPure", PURE, ""),
        via("viaLog", LOGS, " effects ConsoleOutput")
    );
    assert_eq!(
        answers(
            "w5jyh9.defaults_apart",
            &apart,
            &format!("viaPure({ID}) * 10 + viaLog({ID})"),
            " effects ConsoleOutput"
        ),
        21
    );
    // A row open beside labels is no row a call at the pure arrow binds: the two coexist,
    // each call answered by its own — `D1` at `@ {ConsoleOutput, R}` binds `R` to `{}` at
    // a call at `@ {ConsoleOutput}`. They were refused as overlapping.
    let beside_label = format!(
        "{}{}{}",
        marks(
            "(Int64) -> Int64 @ {ConsoleOutput, R}",
            "    effects R = ?\n",
            PURE
        ),
        via("viaPure", PURE, ""),
        via("viaLog", LOGS, " effects ConsoleOutput")
    );
    assert_eq!(
        answers(
            "w5jyh9.defaults_beside_label",
            &beside_label,
            &format!("viaPure({ID}) * 10 + viaLog({ID})"),
            " effects ConsoleOutput"
        ),
        21
    );
    // One row written in two orders is one carrier.
    let reordered = marks(
        "(Int64) -> Int64 @ {ConsoleOutput, Error[T = String]}",
        "",
        "(Int64) -> Int64 @ {Error[T = String], ConsoleOutput}",
    );
    assert_refused_naming(
        &refusal("w5jyh9.defaults_reordered", &reordered),
        &["default providers of"],
        "default marks at one row written in two orders",
    );
}

/// A ROW HOLDING A VALUE (`Modify[c]`) is bound to the row parameter as any other, on the
/// occurrence it rides, with a label beside it and without; a provider at the pure arrow does
/// not answer it.
#[test]
fn a_row_holding_a_value() {
    let cell = "\n  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =\n    \
                let _ = Cell.set(c, n)\n    n\n";
    let go = "let c: Cell[V = Int64] = Cell.new(1)\n    via(c, lambda (n: Int64) -> put(c, n))";
    for (name, provided, called, effects) in [
        (
            "tail",
            "(Int64) -> Int64 @ {R}",
            "(Int64) -> Int64 @ {Modify[c]}",
            "Modify[c]",
        ),
        (
            "beside",
            "(Int64) -> Int64 @ {Error[T = String], R}",
            "(Int64) -> Int64 @ {Error[T = String], Modify[c]}",
            "{Modify[c], Error[T = String]}",
        ),
    ] {
        let body = format!(
            "\n  sort AnyRow\n    effects R = ?\n    provides Apply[F = {provided}]\n    \
             operation run(f: {provided}) -> Int64 = 9\n  end\n{cell}\
             \n  operation via(c: Cell[V = Int64], f: {called}) -> Int64 effects {effects} = Apply.run(f)\n"
        );
        assert_eq!(
            answers(
                &format!("w5jyh9.value_{name}"),
                &body,
                &format!("\n    {go}"),
                " effects {Error[T = String]}"
            ),
            9,
            "`{name}`"
        );
    }
    let pure = format!(
        "{}{cell}\n  operation via(c: Cell[V = Int64], f: (Int64) -> Int64 @ {{Modify[c]}}) -> Int64 \
         effects Modify[c] = Apply.run(f)\n",
        provider("Q", PURE, 1)
    );
    assert_refused_naming(
        &refusal("w5jyh9.value_pure", &pure),
        NO_PROVISION,
        "a provider at the pure arrow beside a call writing a cell",
    );
}

/// A LAMBDA WRITTEN AT THE CALL is at the row its body has: a pure one is answered by the
/// provider at the pure arrow, one that prints by the provider at `@ {ConsoleOutput}` and not
/// by the pure one.
#[test]
fn a_lambda_written_at_the_call() {
    let printing = "lambda (x: Int64) ->\n      let _ = println(console(), \"hi\")\n      x + 1";
    assert_eq!(
        answers(
            "w5jyh9.lambda_pure",
            &provider("Q", PURE, 1),
            &format!("Apply.run({ID})"),
            ""
        ),
        1
    );
    let logger = provider("Logger", LOGS, 7);
    assert_eq!(
        answers(
            "w5jyh9.lambda_logs",
            &logger,
            &format!("Apply.run({printing})"),
            " effects ConsoleOutput"
        ),
        7
    );
    let refused = format!(
        "{}\n  operation go() -> Int64 effects ConsoleOutput =\n    Apply.run({printing})\n",
        provider("Q", PURE, 1)
    );
    assert_refused_naming(
        &refusal("w5jyh9.lambda_refused", &refused),
        NO_PROVISION,
        "a printing lambda at the pure provider",
    );
}

//! WI-20260929-6NMGQ — a spec-operation call in a lambda's body, at the type of the lambda's
//! unannotated parameter, is answered at the lambda's uses, where that type is known.
//!
//! `let f = lambda x -> Store.peek(x)` under `requires Store[State = Other]`, applied as
//! `f(buf(v: 7))`: when `Store.peek(x)` is typed, `x`'s type is still a variable, an
//! unsolved element matches every binding, and the call was fixed to read the enclosing
//! `requires` — so `OtherImpl.peek` ran on the `Buf` (99) where the annotated twin reaches
//! `Carrier` (37).
//!
//! THE RULE (user, 2026-11-02): such a call is decided once the walk has solved the
//! parameter. A `let`-bound lambda the walk generalizes has an implicit requirement, its
//! quantified type's context, and each application hands it the dictionary at the type it
//! gives the parameter, as a call supplies an operation's `requires`: the enclosing
//! declaration's own dictionary where its `requires` covers the type, a construction where a
//! provider answers it, a load error otherwise. A reference handed on (`apply1(f, …)`) is
//! wrapped, `lambda y -> f(y)`, and the wrapper's application hands it. A parameter with one
//! type reads the dictionary at that type.
//!
//! Every row runs the program to a value that names the provider it reached (`Carrier`
//! answers `v + 30`, `OtherImpl` 99, `IntImpl` `s + 100`), or asserts the refusal's text.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! FIVE PARTS, each backed out by a switch in one build and run over this file's rows and
//! the 50B2K / WI-817 / WI-1083 files beside it:
//!
//! 1. THE HOLD (`classify_or_hold_deferral` records the deferral at the call, as before).
//!    12 FAIL — every row with a `requires` the use's type is not under. Pass by design: the
//!    two rows of a use the requirement covers, [`instances_of_one_sort_are_told_apart_at_the_use`]
//!    (no `requires`), [`a_lambda_nothing_applies_loads`].
//! 2. THE DICTIONARY HANDED AT EACH APPLICATION (the call left to the value's run-time
//!    dispatch instead, as the 50B2K licence did). 4 FAIL (and the two-calls row, added
//!    after, which a slot per spec and parameter answered 22 and value-direction refused):
//!    [`a_use_the_requirement_covers_reads_the_callers_dictionary`] (the caller's selection
//!    is not seen: 99 for 77), [`instances_of_one_sort_are_told_apart_at_the_use`],
//!    [`two_providers_at_the_uses_type_are_refused_at_load`],
//!    [`no_provider_at_the_uses_type_is_refused_at_the_use`] — and five 50B2K / WI-817
//!    refusal rows, whose refusal this build now is. The rest pass by value-direction,
//!    which answers each of them alike where one provider stands at each sort.
//! 3. THE DICTIONARY AT A PARAMETER'S ONE TYPE (left to the value). 1 FAILS:
//!    [`a_parameter_the_body_pins_reads_the_dictionary_at_its_type`] (`AmbiguousSpecOpDispatch`
//!    at run time) — and 50B2K's tuple known-gap row, whose refusal is this branch's.
//! 4. THE WRAPPER OF A REFERENCE HANDED ON. 1 FAILS:
//!    [`a_reference_handed_to_another_operation_carries_its_dictionary`] — and two WI-817 /
//!    50B2K rows that hand a quantified lambda on.
//! 5. EVAL HANDING THE DICTIONARIES TO THE CLOSURE (dropped, as the HO-call exception did).
//!    12 FAIL — every row that runs a quantified lambda; pass: the one-type row and the three
//!    load verdicts.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// `Buf[T, N]`, the spec `Store`, a second state sort `Other`, `Carrier` providing `Store` at
/// `Buf[T = Int64]` (`v + 30`) and `OtherImpl` at `Other` (99); then `extra`, and `user`.
fn program(ns: &str, extra: &str, user: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, Function}}

  sort Buf
    sort T = ?
    sort N = ?
    entity buf(v: T)
  end

  sort Store
    sort State = ?
    operation peek(s: State) -> Int64
  end

  sort Other
    entity other(w: Int64)
  end

  sort Carrier
    provides Store[State = Buf[T = Int64]]
    operation peek(s: Buf[T = Int64]) -> Int64 = s.v + 30
  end

  sort OtherImpl
    provides Store[State = Other]
    operation peek(s: Other) -> Int64 = 99
  end
{extra}
{user}
end
"#
    )
}

/// `User` with `requires` (empty for none) and `go() = body`, called from `main`.
fn user(requires: &str, body: &str) -> String {
    format!(
        "  sort User\n    {requires}\n    operation go() -> Int64 =\n      {body}\n  end\n\
         \n  operation main() -> Int64 = User.go()\n"
    )
}

/// `User[S]` with `requires Store[State = S]` and `go(s: S) = body`, called as `User.go(arg)`.
fn user_over_s(body: &str, arg: &str) -> String {
    format!(
        "  sort User\n    sort S = ?\n    requires Store[State = S]\n    \
         operation go(s: S) -> Int64 =\n      {body}\n  end\n\
         \n  operation main() -> Int64 = User.go({arg})\n"
    )
}

const AT_OTHER: &str = "requires Store[State = Other]";
const LET_F: &str = "let f = lambda x -> Store.peek(x)\n      ";

fn runs(ns: &str, extra: &str, user: &str) -> i64 {
    let src = program(ns, extra, user);
    run_int64(&src, &format!("{ns}.main")).unwrap_or_else(|e| panic!("{ns}: {e}"))
}

/// `apply1[X](fn: (X) -> Int64, a: X) = fn(a)` — a function that applies what it is handed.
const APPLY1: &str =
    "  operation apply1[X](fn: Function[A = X, B = Int64], a: X) -> Int64 = fn(a)\n";

// ── the ticket ──────────────────────────────────────────────────────────────────────────

/// THE TICKET'S PROGRAM: the use is at `Buf`, which the requirement at `Other` does not
/// cover, so `Carrier` answers — as the annotated twin does. Ran `OtherImpl.peek` (99).
#[test]
fn the_ticket_program_reaches_the_provider_at_the_uses_type() {
    let body = format!("{LET_F}f(buf(v: 7))");
    assert_eq!(runs("wi6nmgq.ticket", "", &user(AT_OTHER, &body)), 37);
    let annotated = "let f = lambda (x: Buf[T = Int64]) -> Store.peek(x)\n      f(buf(v: 7))";
    assert_eq!(
        runs("wi6nmgq.ticket_ann", "", &user(AT_OTHER, annotated)),
        37,
        "the annotated twin, which never deferred"
    );
}

/// A use at a type a third provider answers: `IntImpl` (`s + 100`). Ran `OtherImpl` (99).
#[test]
fn a_use_at_another_type_reaches_its_own_provider() {
    let int_impl = "  sort IntImpl\n    provides Store[State = Int64]\n    \
                    operation peek(s: Int64) -> Int64 = s + 100\n  end\n";
    let body = format!("{LET_F}f(7)");
    assert_eq!(runs("wi6nmgq.int", int_impl, &user(AT_OTHER, &body)), 107);
}

/// A USE THE REQUIREMENT COVERS STILL READS IT, and so takes the caller's choice of its
/// provider: with a second provider at `Other`, `User.go[Store = OtherImpl2]()` answers 77.
/// Passes either way by design — the requirement was the right answer here before.
#[test]
fn a_use_the_requirement_covers_reads_the_callers_dictionary() {
    let body = format!("{LET_F}f(other(w: 1))");
    assert_eq!(runs("wi6nmgq.covered", "", &user(AT_OTHER, &body)), 99);
    let second = "  sort OtherImpl2\n    provides Store[State = Other]\n    \
                  operation peek(s: Other) -> Int64 = 77\n  end\n";
    let selected = user(AT_OTHER, &body).replace("User.go()", "User.go[Store = OtherImpl2]()");
    assert_eq!(runs("wi6nmgq.covered_sel", second, &selected), 77);
}

/// TWO USES AT TWO TYPES, each handed its own dictionary: 37 + 99. Answered 198 — both read
/// the requirement — and 136 with no `requires` written.
#[test]
fn two_uses_at_two_types_are_each_answered_at_their_own() {
    let body = format!("{LET_F}f(buf(v: 7)) + f(other(w: 1))");
    assert_eq!(runs("wi6nmgq.two", "", &user(AT_OTHER, &body)), 136);
    assert_eq!(runs("wi6nmgq.two_none", "", &user("", &body)), 136);
}

// ── a requirement over the declaration's own parameter ──────────────────────────────────

/// A use at `S` reads the requirement over `S`, which the caller fills: 37 at `S = Buf`, 99
/// at `S = Other`. Passes either way by design.
#[test]
fn a_use_at_the_declarations_parameter_reads_its_requirement() {
    let body = format!("{LET_F}f(s)");
    assert_eq!(
        runs("wi6nmgq.s_buf", "", &user_over_s(&body, "buf(v: 7)")),
        37
    );
    assert_eq!(
        runs("wi6nmgq.s_other", "", &user_over_s(&body, "other(w: 7)")),
        99
    );
}

/// A use at `Buf` under `requires Store[State = S]` is no use at `S`: with `S = Other` the
/// requirement's provider is `OtherImpl`, and the `Buf` reaches `Carrier`. Ran `OtherImpl`
/// on the `Buf` (99).
#[test]
fn a_use_at_another_type_than_the_parameter_is_not_the_requirements() {
    let body = format!("{LET_F}f(buf(v: 7))");
    assert_eq!(
        runs("wi6nmgq.s_at_buf", "", &user_over_s(&body, "other(w: 1)")),
        37
    );
}

/// ONE LAMBDA USED AT `S` AND AT `Other`: the first is handed the caller's dictionary for
/// `S`, the second `OtherImpl`'s — 37 + 99. One call reading one dictionary ran
/// `Carrier.peek` on the `other(…)` and the run died.
#[test]
fn one_lambda_used_at_the_parameter_and_at_another_type() {
    let body = format!("{LET_F}f(s) + f(other(w: 1))");
    assert_eq!(
        runs("wi6nmgq.mixed", "", &user_over_s(&body, "buf(v: 7)")),
        136
    );
    let two = "let f = lambda x -> Store.peek(x)\n      \
               let g = lambda y -> Store.peek(y)\n      f(s) + g(other(w: 1))";
    assert_eq!(
        runs("wi6nmgq.mixed_two", "", &user_over_s(two, "buf(v: 7)")),
        136,
        "two lambdas, one per type"
    );
}

// ── where the requirement is written, and where the call is ────────────────────────────

/// The operation's own `requires`, a generic operation's, and one reached through another
/// requirement (`Big requires Store[State = State]`): each use at `Buf` reaches `Carrier`,
/// each at `Other` reads the requirement.
#[test]
fn every_requirement_route_answers_at_the_uses_type() {
    let op_scoped = |use_: &str| {
        format!(
            "  sort User\n    operation go() -> Int64 requires Store[State = Other] =\n      \
             {LET_F}{use_}\n  end\n\n  operation main() -> Int64 = User.go()\n"
        )
    };
    assert_eq!(runs("wi6nmgq.op_buf", "", &op_scoped("f(buf(v: 7))")), 37);
    assert_eq!(
        runs("wi6nmgq.op_other", "", &op_scoped("f(other(w: 1))")),
        99
    );
    let generic = format!(
        "  sort User\n    operation go[S](s: S) -> Int64 requires Store[State = S] =\n      \
         {LET_F}f(buf(v: 7))\n  end\n\n  operation main() -> Int64 = User.go(other(w: 1))\n"
    );
    assert_eq!(runs("wi6nmgq.generic", "", &generic), 37);
    let big = "  sort Big\n    sort State = ?\n    requires Store[State = State]\n    \
               operation big(s: State) -> Int64\n  end\n  sort BigImpl\n    \
               provides Big[State = Other]\n    operation big(s: Other) -> Int64 = 1\n  end\n";
    let through = |use_: &str| user("requires Big[State = Other]", &format!("{LET_F}{use_}"));
    assert_eq!(runs("wi6nmgq.big_buf", big, &through("f(buf(v: 7))")), 37);
    assert_eq!(
        runs("wi6nmgq.big_other", big, &through("f(other(w: 1))")),
        99
    );
}

/// The call under an `if`, in its condition, and in a `match` arm: 37 (and `2` for the
/// condition `peek > 50`, false at `Carrier`'s 37, true at `OtherImpl`'s 99).
#[test]
fn the_call_under_a_form_in_the_lambda() {
    let at = |body: &str| {
        user(
            AT_OTHER,
            &format!("let f = lambda x -> {body}\n      f(buf(v: 7))"),
        )
    };
    assert_eq!(
        runs(
            "wi6nmgq.if_arm",
            "",
            &at("if true then Store.peek(x) else 2")
        ),
        37
    );
    assert_eq!(
        runs(
            "wi6nmgq.if_cond",
            "",
            &at("if Store.peek(x) > 50 then 1 else 2")
        ),
        2
    );
    assert_eq!(
        runs(
            "wi6nmgq.match",
            "",
            &at("match 1\n        case 1 -> Store.peek(x)\n        case _ -> 0"),
        ),
        37
    );
}

// ── a lambda handed on ──────────────────────────────────────────────────────────────────

/// A REFERENCE HANDED ON CARRIES ITS DICTIONARY: `apply1(f, buf(v: 7))` applies `f` inside
/// `apply1`, which knows nothing of it; the wrapper the reference is typed into hands it.
/// Ran `OtherImpl` (99).
#[test]
fn a_reference_handed_to_another_operation_carries_its_dictionary() {
    let body = format!("{LET_F}apply1(f, buf(v: 7))");
    assert_eq!(runs("wi6nmgq.hof", APPLY1, &user(AT_OTHER, &body)), 37);
}

/// AN ALIAS AND A NESTED LAMBDA: `let h = f` puts `f`'s instance back into `h`'s quantified
/// type, and `h`'s applications hand the dictionary on; a lambda whose call is another
/// lambda's application of its parameter likewise. Ran `OtherImpl` (99, 198).
#[test]
fn an_alias_and_a_nested_lambda_forward_the_dictionary() {
    let alias = format!("{LET_F}let h = f\n      h(buf(v: 7))");
    assert_eq!(runs("wi6nmgq.alias", "", &user(AT_OTHER, &alias)), 37);
    let both = format!("{LET_F}let h = f\n      h(buf(v: 7)) + f(other(w: 1))");
    assert_eq!(runs("wi6nmgq.alias_both", "", &user(AT_OTHER, &both)), 136);
    let nested = "let f = lambda x -> let g = lambda y -> Store.peek(y)\n        g(x)\n      \
                  f(buf(v: 7))";
    assert_eq!(runs("wi6nmgq.nested", "", &user(AT_OTHER, nested)), 37);
}

/// A PARAMETER WITH ONE TYPE: `takes_buf(x)` in the body pins `x` to `Buf[T = Int64]`, so
/// the lambda is not quantified and its call reads the dictionary at that type — 37 + 7,
/// beside a provider at `Buf[T = Bool]` that the value's sort alone cannot tell from
/// `Carrier`. Ran `OtherImpl` (99 + 7).
#[test]
fn a_parameter_the_body_pins_reads_the_dictionary_at_its_type() {
    let extra = "  operation takes_buf(b: Buf[T = Int64]) -> Int64 = b.v\n  sort CarrierB\n    \
                 provides Store[State = Buf[T = Bool]]\n    \
                 operation peek(s: Buf[T = Bool]) -> Int64 = 55\n  end\n";
    let body = "let f = lambda x -> Store.peek(x) + takes_buf(x)\n      f(buf(v: 7))";
    assert_eq!(runs("wi6nmgq.mono", extra, &user(AT_OTHER, body)), 44);
    assert_eq!(
        runs("wi6nmgq.mono_none", extra, &user("", body)),
        44,
        "with no `requires`"
    );
}

/// TWO CALLS ON ONE PARAMETER, ONE SPEC, TWO BINDINGS: `Conv.conv(x, 5)` and
/// `Conv.conv(x, "s")` are each handed their own dictionary — `ConvI`'s (1) and `ConvS`'s
/// (2), 1 * 10 + 2 — as the annotated twin answers. Read under one slot the first took the
/// second's dictionary (22); left to the value's sort the run died "ambiguous dispatch".
#[test]
fn two_calls_on_one_parameter_are_each_handed_their_own() {
    let src = r#"
namespace wi6nmgq.two_calls
  import anthill.prelude.{Int64, String}

  sort Buf
    sort T = ?
    entity buf(v: T)
  end

  sort Conv
    sort A = ?
    sort B = ?
    operation conv(a: A, b: B) -> Int64
  end

  sort ConvI
    provides Conv[A = Buf[T = Int64], B = Int64]
    operation conv(a: Buf[T = Int64], b: Int64) -> Int64 = 1
  end

  sort ConvS
    provides Conv[A = Buf[T = Int64], B = String]
    operation conv(a: Buf[T = Int64], b: String) -> Int64 = 2
  end

  operation main() -> Int64 =
    let f = lambda x -> Conv.conv(x, 5) * 10 + Conv.conv(x, "s")
    f(buf(v: 7))
end
"#;
    assert_eq!(run_int64(src, "wi6nmgq.two_calls.main"), Ok(12));
}

// ── with no `requires`: told apart, or refused at load ─────────────────────────────────

/// TWO INSTANCES OF ONE SORT ARE TOLD APART: providers at `Buf[T = Int64]` and `Buf[T =
/// Bool]`, no `requires`. The use at `Buf[T = Int64]` is dispatched where it is written, as
/// the annotated twin is (37). Left to the run time it read the value's sort alone and died
/// "ambiguous dispatch … on carrier `Buf`".
#[test]
fn instances_of_one_sort_are_told_apart_at_the_use() {
    let at_bool = "  sort CarrierB\n    provides Store[State = Buf[T = Bool]]\n    \
                   operation peek(s: Buf[T = Bool]) -> Int64 = 55\n  end\n";
    let body = format!("{LET_F}f(buf(v: 7))");
    assert_eq!(runs("wi6nmgq.told_apart", at_bool, &user("", &body)), 37);
}

/// TWO PROVIDERS AT THE USE'S TYPE ARE REFUSED AT LOAD, at the use (`f(buf(v: 7))`, line
/// 38), naming both — as the annotated twin is. Ran `OtherImpl` (99) under the requirement, and died when run without.
#[test]
fn two_providers_at_the_uses_type_are_refused_at_load() {
    let second = "  sort Carrier2\n    provides Store[State = Buf[T = Int64]]\n    \
                  operation peek(s: Buf[T = Int64]) -> Int64 = 55\n  end\n";
    let body = format!("{LET_F}f(buf(v: 7))");
    for (ns, requires) in [("wi6nmgq.amb", AT_OTHER), ("wi6nmgq.amb_none", "")] {
        let errs = load_errors_of(&program(ns, second, &user(requires, &body)));
        assert_refused_naming(
            &errs,
            &["ambiguous among providers", "Carrier", "Carrier2", "38:7:"],
            "two providers at the use's type, reported at the use",
        );
        assert_eq!(errs.len(), 1, "one refusal: {errs:#?}");
    }
}

/// NO PROVIDER AT THE USE'S TYPE IS REFUSED AT THE USE (`f(7)`, line 34), naming the
/// requirement at `Int64`.
#[test]
fn no_provider_at_the_uses_type_is_refused_at_the_use() {
    let body = format!("{LET_F}f(7)");
    let errs = load_errors_of(&program("wi6nmgq.none", "", &user(AT_OTHER, &body)));
    assert_refused_naming(
        &errs,
        &[
            "Store[State = anthill.prelude.Int64]",
            "cannot be supplied",
            "34:7:",
        ],
        "no provider of Store at Int64",
    );
}

/// A LAMBDA NOTHING APPLIES keeps the deferral it had (and runs nothing). Passes either way.
#[test]
fn a_lambda_nothing_applies_loads() {
    let body = format!("{LET_F}1");
    assert_eq!(runs("wi6nmgq.unapplied", "", &user(AT_OTHER, &body)), 1);
}

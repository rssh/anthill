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
//!
//! ── A LAMBDA OF SEVERAL BINDERS (the ticket's second part) ───────────────────────────
//!
//! A lambda of several binders is handed its dictionaries as one of a single binder is
//! (the rows under "a lambda of several binders"). FIVE PARTS, each backed out by a switch in
//! one build and run over this file and fourteen beside it (264 rows: 50B2K, 34J8Z, 6HVXM,
//! MHF0B, PBSEM, KBZ4F, 0RRQP, WF14Z, WI-517 / 605 / 784 / 801 / 817 / 1083):
//!
//! 6. THE COLLECTOR'S `Value::Var` ARM inside a type node — the variable a lambda's own tuple
//!    of binder types holds in its field list. 3 FAIL: the two-uses, one-variable and contested
//!    rows (the lambda is not quantified).
//! 7. THE REWRITER'S `Value::Var` ARM (close / open / σ). 4 FAIL: those three and the
//!    two-binders row (an instance's component stays the quantified variable).
//! 8. THE SITE RE-POINTED to the application's tupled form. 5 FAIL: the two-binders,
//!    two-uses and one-variable rows, and 34J8Z's `a_nested_binder_is_solved_by_its_use` and
//!    MHF0B's `a_call_typed_at_the_callees_variable_answers_the_binder`, whose lambdas the two
//!    arms quantify.
//! 9. THE CARRIERS READ AT THEIR ROOTS. 3 FAIL: the one-variable and contested rows, and
//!    34J8Z's `what_the_shape_does_not_decide_is_unchanged` (an unused `lambda ((a, b), c) ->
//!    a + b`, which loads as `lambda x -> x + x` does).
//! 10. A TYPE PARAMETER OF THE ENCLOSING DECLARATION READ AS NO OPEN PART. 1 FAILS: the
//!    unquantified row.

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

// ── a lambda of several binders ─────────────────────────────────────────────────────────

/// `apply2[X](fn: (x: X, y: Int64) -> Int64, a: X) = fn(a, 1)`.
const APPLY2: &str =
    "  operation apply2[X](fn: (x: X, y: Int64) -> Int64, a: X) -> Int64 = fn(a, 1)\n";

/// `let f = lambda (a, b) -> Store.peek(a) + b`.
const LET_F2: &str = "let f = lambda (a, b) -> Store.peek(a) + b\n      ";

/// THE TICKET'S REMAINING PROGRAM, a lambda of two binders: the component `a` is typed at the
/// use as the single binder is, so `Carrier` answers (37 + 1), applied, handed on, and as its
/// annotated twin. Ran `OtherImpl` (100) before WI-20260904-34J8Z tied a tuple binder's
/// components to its uses. The direct application FAILS with the site re-point backed out: the
/// application is rebuilt as its tupled form after its site is recorded, and the dictionary was
/// handed to the node left behind ("`__ctx_store_…` unbound" at run time) once the lambda is
/// quantified; and with the rewriter's `Value::Var` arm, which leaves the instance's component
/// the quantified variable.
#[test]
fn a_lambda_of_two_binders_reaches_the_provider_at_the_uses_type() {
    let at = |ns: &str, body: &str| runs(ns, APPLY2, &user(AT_OTHER, body));
    assert_eq!(at("wi6nmgq.b2_apply", &format!("{LET_F2}apply2(f, buf(v: 7))")), 38);
    assert_eq!(at("wi6nmgq.b2_direct", &format!("{LET_F2}f(buf(v: 7), 1)")), 38);
    assert_eq!(
        at(
            "wi6nmgq.b2_ann",
            "let f = lambda (a: Buf[T = Int64], b: Int64) -> Store.peek(a) + b\n      \
             apply2(f, buf(v: 7))"
        ),
        38,
        "the annotated twin"
    );
    assert_eq!(
        at("wi6nmgq.b2_second", "let f = lambda (b, a) -> Store.peek(a) + b\n      f(1, buf(v: 7))"),
        38,
        "the carrier second"
    );
    assert_eq!(at("wi6nmgq.b2_covered", &format!("{LET_F2}f(other(w: 1), 1)")), 100);
    assert_eq!(
        at("wi6nmgq.b2_nested", "let f = lambda ((a, b), c) -> Store.peek(a) + c\n      f((buf(v: 7), 1), 2)"),
        39,
        "a nested binder list"
    );
    assert_eq!(
        at(
            "wi6nmgq.b2_let",
            "let f = lambda p -> (let (a, b) = p\n        Store.peek(a) + b)\n      f((buf(v: 7), 1))"
        ),
        38,
        "a `let` taking the parameter apart"
    );
    assert_eq!(
        at(
            "wi6nmgq.b2_match",
            "let f = lambda p -> (match p case (a, b) -> Store.peek(a) + b)\n      f((buf(v: 7), 1))"
        ),
        38,
        "a `match` taking it apart"
    );
}

/// TWO USES OF A LAMBDA OF TWO BINDERS AT TWO TYPES, each handed its own dictionary: (37 + 1)
/// + (99 + 1), as the single binder's 136. Was refused "one type for the lambda's parameter":
/// the lambda's parameter is its own tuple of binder types, `(_1: ?a, _2: ?b)`, and the walks
/// that quantify it and instantiate it read no variable on the value carrier a tuple's field
/// list holds — so `?a` was not free in the lambda's type, the lambda was not quantified, and
/// its call read one dictionary. FAILS with either walk's `Value::Var` arm backed out (the
/// collector: refused; the rewriter: the two instances share `?a`, refused), and with the
/// site re-point (run-time "`__ctx_store_…` unbound").
#[test]
fn two_uses_of_a_lambda_of_two_binders_are_each_answered_at_their_own() {
    let at = |ns: &str, body: &str| runs(ns, "", &user(AT_OTHER, body));
    assert_eq!(
        at("wi6nmgq.b2_two", &format!("{LET_F2}f(buf(v: 7), 1) + f(other(w: 1), 1)")),
        138
    );
    assert_eq!(
        at(
            "wi6nmgq.b2_two_second",
            "let f = lambda (b, a) -> Store.peek(a) + b\n      f(1, buf(v: 7)) + f(1, other(w: 1))"
        ),
        138,
        "the carrier second"
    );
    assert_eq!(
        runs(
            "wi6nmgq.b2_two_s",
            "",
            &user_over_s(&format!("{LET_F2}f(s, 1) + 1000 * f(buf(v: 7), 1)"), "other(w: 1)")
        ),
        38100,
        "at `S = Other` beside `Buf`: 99 + 1, then 1000 × (37 + 1)"
    );
}

/// `Pair`, a spec whose operation takes its carrier twice: `PairBuf` at `Buf[T = Int64]`
/// (`s.v + t.v + 30`), `PairOther` at `Other` (99).
const PAIR: &str = "  sort Pair\n    sort State = ?\n    \
                    operation both(s: State, t: State) -> Int64\n  end\n  \
                    sort PairBuf\n    provides Pair[State = Buf[T = Int64]]\n    \
                    operation both(s: Buf[T = Int64], t: Buf[T = Int64]) -> Int64 = s.v + t.v + 30\n  end\n  \
                    sort PairOther\n    provides Pair[State = Other]\n    \
                    operation both(s: Other, t: Other) -> Int64 = 99\n  end\n";

/// `UserP[S]` with `requires Pair[State = S]` and `go(s: S) = body`, called at `other(w: 1)`.
fn user_pair_over_s(body: &str) -> String {
    format!(
        "  sort UserP\n    sort S = ?\n    requires Pair[State = S]\n    \
         operation go(s: S) -> Int64 =\n      {body}\n  end\n\
         \n  operation main() -> Int64 = UserP.go(other(w: 1))\n"
    )
}

/// TWO BINDERS ONE CALL TAKES AS ONE CARRIER are one variable once the call has unified them —
/// `Pair.both(a, b)` over `lambda (a, b)`, and over the curried `lambda a -> lambda b` — and the
/// lambda is quantified over it as the single binder of `Pair.both(x, x)` is. At two types:
/// (7 + 1 + 30) + 99; at the enclosing `S = Other` beside `Buf`: 99 + 1000 × 38. Read as
/// written, the second binder was bound to the first and so not free, the lambda was not
/// quantified, and its call read one dictionary: two types were refused "one type for the
/// lambda's parameter", and at `S` beside `Buf` the `S` yielded to `Buf` (next row's part) and
/// `PairBuf.both` ran on the `Other` ("entity has no field 'v'"). FAILS with the roots backed
/// out, and with each part the lambda of two binders needs. The single binder's twins (143,
/// 44099) pass either way.
#[test]
fn binders_one_call_unifies_are_quantified_as_one_variable() {
    let main = |body: &str| format!("  operation main() -> Int64 =\n    {body}\n");
    let tuple = "let f = lambda (a, b) -> Pair.both(a, b)\n    ";
    let curried = "let f = lambda a -> lambda b -> Pair.both(a, b)\n    ";
    let single = "let f = lambda x -> Pair.both(x, x)\n    ";
    let two = |ns: &str, src: String| runs(ns, PAIR, &src);
    assert_eq!(
        two(
            "wi6nmgq.link_tuple",
            main(&format!("{tuple}f(buf(v: 7), buf(v: 1)) + f(other(w: 1), other(w: 2))"))
        ),
        137
    );
    assert_eq!(
        two(
            "wi6nmgq.link_curried",
            main(&format!(
                "{curried}let g = f(buf(v: 7))\n    let h = f(other(w: 1))\n    \
                 g(buf(v: 1)) + h(other(w: 2))"
            ))
        ),
        137
    );
    assert_eq!(
        two(
            "wi6nmgq.link_single",
            main(&format!("{single}f(buf(v: 7)) + f(other(w: 1))"))
        ),
        143,
        "the single binder's twin"
    );
    let at_s = |ns: &str, body: &str| runs(ns, PAIR, &user_pair_over_s(body));
    assert_eq!(
        at_s(
            "wi6nmgq.link_tuple_s",
            "let f = lambda (a, b) -> Pair.both(a, b)\n      f(s, s) + 1000 * f(buf(v: 7), buf(v: 1))"
        ),
        38099
    );
    assert_eq!(
        at_s(
            "wi6nmgq.link_curried_s",
            "let f = lambda a -> lambda b -> Pair.both(a, b)\n      let g = f(s)\n      \
             let h = f(buf(v: 7))\n      g(s) + 1000 * h(buf(v: 1))"
        ),
        38099
    );
    assert_eq!(
        at_s(
            "wi6nmgq.link_single_s",
            "let f = lambda x -> Pair.both(x, x)\n      f(s) + 1000 * f(buf(v: 7))"
        ),
        44099,
        "the single binder's twin"
    );
}

/// A LAMBDA LEFT UNQUANTIFIED, USED AT `S` AND AT `Buf`, IS REFUSED naming both: its binder is
/// tied to the enclosing lambda's `y`, so it has one type, and one call reads one dictionary.
/// The enclosing declaration's `S` is a type of its own, not a part still open that a later
/// use's type solves: read as open, it yielded to `Buf` and the use at `S` read `PairBuf`'s
/// dictionary. FAILS with that reading backed out. The twins at one type run (99 + 1000 × 99,
/// and (7 + 1 + 30) + 1000 × (2 + 1 + 30)) either way.
#[test]
fn an_unquantified_lambda_used_at_s_and_at_another_type_is_refused() {
    let body = |uses: &str, arg: &str| {
        format!(
            "let g = lambda y -> (let f = lambda x -> Pair.both(x, y)\n        {uses})\n      g({arg})"
        )
    };
    for (ns, uses, arg) in [
        ("wi6nmgq.unq_s_buf", "f(s) + 1000 * f(buf(v: 7))", "s"),
        ("wi6nmgq.unq_buf_s", "f(buf(v: 7)) + 1000 * f(s)", "buf(v: 7)"),
    ] {
        let errs = load_errors_of(&program(ns, PAIR, &user_pair_over_s(&body(uses, arg))));
        assert_refused_naming(
            &errs,
            &["one type for the lambda's parameter", "`?S`", "`Buf[T = Int64"],
            ns,
        );
    }
    assert_eq!(
        runs("wi6nmgq.unq_s", PAIR, &user_pair_over_s(&body("f(s) + 1000 * f(s)", "s"))),
        99099
    );
    assert_eq!(
        runs(
            "wi6nmgq.unq_buf",
            PAIR,
            &user_pair_over_s(&body("f(buf(v: 7)) + 1000 * f(buf(v: 2))", "buf(v: 1)"))
        ),
        33038
    );
}

/// TWO PARAMETERS OF ONE CARRIER, A READ IN A LAMBDA THAT NAMES NEITHER: refused as the body's
/// own read is (`wi_0rrqp`'s `twoOp`), wherever the lambda's call is handed its dictionary —
/// at the one type its parameter is pinned to, at each application of a quantified lambda,
/// and for a lambda of two binders. The last LOADED, and ran both uses on `Int64`'s own order
/// (−1 + 1000 × −1 over `twoOp(asc(), desc())`): its two binders were not quantified as one
/// variable, its one call read one dictionary, and the use at `A` yielded to the use at
/// `Int64`. FAILS (it loads) with the roots, or either walk's `Value::Var` arm, backed out; the
/// others are refused either way.
#[test]
fn a_contested_slot_read_in_a_lambda_is_refused() {
    let ord = r#"
  import anthill.prelude.{Int64, WeakOrd, Ord}

  sort Ascending
    import anthill.prelude.Numeric.{sub}
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(a, b)
  end

  sort Descending
    import anthill.prelude.Numeric.{sub}
    provides Ord[T = Int64]
    operation compare(a: Int64, b: Int64) -> Int64 = sub(b, a)
  end

  sort CBox
    sort T = ?
    requires O: WeakOrd[T]
    entity cbox(a: T, b: T)
  end
"#;
    let says = "`p`'s slot `O` and `q`'s answer it, two parameters of one carrier, and the read \
                names neither";
    for (ns, lambda, uses) in [
        ("wi6nmgq.contest_pinned", "lambda x -> WeakOrd.compare(x, b)", "f(a)"),
        ("wi6nmgq.contest_gen", "lambda x -> WeakOrd.compare(x, x)", "f(a) + f(3)"),
        ("wi6nmgq.contest_pair", "lambda (x, y) -> WeakOrd.compare(x, y)", "f(a, b)"),
        ("wi6nmgq.contest_pair_gen", "lambda (x, y) -> WeakOrd.compare(x, y)", "f(a, b) + 1000 * f(1, 2)"),
    ] {
        let src = format!(
            "namespace {ns}\n{ord}\n  sort Cite\n    import {ns}.CBox.{{cbox}}\n    \
             operation twoOp[A](p: CBox[T = A], q: CBox[T = A]) -> Int64 =\n      \
             match q case cbox(a, b) -> (let f = {lambda}\n        {uses})\n  end\nend\n"
        );
        let errs = load_errors_of(&src);
        assert_refused_naming(&errs, &[says], ns);
        assert_eq!(errs.len(), 1, "{ns}: one refusal: {errs:#?}");
    }
}

//! WI-20260927-YCPAJ — the requirement the bare-spec sugar SYNTHESIZES (WI-201) is owed at
//! a call, as the one the explicit spelling DECLARES is (WI-20260921-3G1YT).
//!
//! `b: Spec2.B` records `requires Spec2[B = ?P]` with `?P` a BARE variable — no declared
//! symbol, where the explicit `[P](b: P) requires Spec2[B = P]` names `t.useB.P`. The call
//! site pins a requirement by substituting its parameters' symbols
//! (`substitute_spec_via_subst`), so the sugar's `?P` stayed open at every call, the dep
//! read as unpinned, and it was skipped: `useB(wis(…), wis(…))` loaded clean with nothing
//! providing `Spec2[…, B = WIS]`, and a body calling `Spec2.both(a, b)` then dispatched to
//! the `NoSp` provider with a `WIS` argument.
//!
//! A dep the call pins only PART of — `b: Spec2.B` leaves `A` open, so `useB(…, wis(…))`
//! owes `Spec2[B = WIS]` — was admitted in BOTH spellings: the check refused only a fully
//! pinned dep, since the search answers `NoMatch` for any goal that omits an element, a
//! provided one included. It is now refused when every provision row names another ground
//! type at an element the call pins (`no_provision_agrees_with_pins`).
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ────────────────────────────
//!
//! MEASURED 2026-09-27, one back-out at a time:
//!
//! 1. THE `Var::Global` RUNG OF `substitute_spec_via_subst` (the sugar's `?P` is never
//!    pinned): [`an_unprovided_call_through_the_alias_sugar_is_refused`],
//!    [`an_unprovided_call_through_the_direct_sugar_is_refused`] and
//!    [`a_partly_pinned_call_no_row_agrees_with_is_refused`] fail on their SUGAR spelling
//!    (it loads clean). Their EXPLICIT spelling, run first, passes. And
//!    [`a_row_leaving_the_pinned_element_open_keeps_the_call`] fails on its sugar spelling
//!    at EVAL — `__req_spec2 not bound in caller frame`, an `Internal`: the unpinned dep
//!    built no dictionary, so the body's `Spec2.both` had nothing to read.
//! 2. THE PARTLY-PINNED ARM (`no_provision_agrees_with_pins` answers `None`):
//!    [`a_partly_pinned_call_no_row_agrees_with_is_refused`], at its explicit spelling (the
//!    first the loop reaches).
//!
//!    Back-out 1 also fails WI-20260924-0S3YG's two rows on their sugar spelling:
//!    [`a_call_whose_conditional_provision_fails_is_refused`] loads clean, and
//!    [`a_call_whose_conditional_provision_holds_runs`] dies at eval, `__req_store not
//!    bound in caller frame` — even a SUPPLIED sugar call built no dictionary.
//!
//! [`a_provided_call_runs_in_every_spelling`] passes under both back-outs, by design —
//! neither change may refuse a call a provider meets.

use crate::common::{assert_refused_naming, interp_for, try_load_kb_with};
use anthill_core::eval::Value;

/// `Store` over one parameter with `FileStore` providing it at `WIS`; `Spec2` over two, the
/// alias `S2A` fixing its `A` to `WIS`, and `Both` providing it at `A = WIS, B = NoSp`.
fn program(decl: &str, goal: &str) -> String {
    format!(
        r#"
namespace t
  import anthill.prelude.{{Int64}}
  sort WIS
    entity wis(n: Int64)
  end
  sort NoSp
    entity nosp(n: Int64)
  end
  sort Store
    sort State = ?
    operation peek(s: State) -> Int64
  end
  sort FileStore
    provides Store[State = WIS]
    operation peek(s: WIS) -> Int64 = s.n
  end
  sort Spec2
    sort A = ?
    sort B = ?
    operation both(a: A, b: B) -> Int64
  end
  sort S2A = Spec2[A = WIS]
  sort Both
    provides Spec2[A = WIS, B = NoSp]
    operation both(a: WIS, b: NoSp) -> Int64 = a.n + b.n
  end
{decl}
  operation go() -> Int64 = {goal}
end
"#
    )
}

/// The explicit spelling first — the control — then the sugar.
const ALIAS_SPELLINGS: [&str; 2] = [
    "  operation useB[P](a: WIS, b: P) -> Int64 requires Spec2[A = WIS, B = P] = 1",
    "  operation useB(a: WIS, b: S2A.B) -> Int64 = 1",
];

const DIRECT_SPELLINGS: [&str; 2] = [
    "  operation look[S](s: S) -> Int64 requires Store[State = S] = 1",
    "  operation look(s: Store.State) -> Int64 = 1",
];

/// `S2A.B` at `B = WIS` requires `Spec2[A = WIS, B = WIS]`, which nothing provides.
/// Was (sugar): a clean load.
#[test]
fn an_unprovided_call_through_the_alias_sugar_is_refused() {
    for decl in ALIAS_SPELLINGS {
        let errs = try_load_kb_with(&program(decl, "useB(wis(n: 4), wis(n: 5))"))
            .err()
            .unwrap_or_default();
        assert_refused_naming(
            &errs,
            &[
                "t.Spec2[A = t.WIS, B = t.WIS]",
                "cannot be supplied",
                "t.useB",
            ],
            decl,
        );
    }
}

/// `Store.State` at `NoSp` requires `Store[State = NoSp]`, which nothing provides.
/// Was (sugar): a clean load.
#[test]
fn an_unprovided_call_through_the_direct_sugar_is_refused() {
    for decl in DIRECT_SPELLINGS {
        let errs = try_load_kb_with(&program(decl, "look(nosp(n: 4))"))
            .err()
            .unwrap_or_default();
        assert_refused_naming(
            &errs,
            &["t.Store[State = t.NoSp]", "cannot be supplied", "t.look"],
            decl,
        );
    }
}

/// `Spec2.B` alone leaves `A` open, so `useB(…, wis(…))` owes `Spec2[B = WIS]`: `Both`, the
/// only row, names `B = NoSp`, so no `A` makes it answer. Was: a clean load in both
/// spellings, and with the body `Spec2.both(a, b)` it answered 9 off `Both`'s dictionary.
#[test]
fn a_partly_pinned_call_no_row_agrees_with_is_refused() {
    for decl in [
        "  operation useB[P](a: WIS, b: P) -> Int64 requires Spec2[B = P] = Spec2.both(a, b)",
        "  operation useB(a: WIS, b: Spec2.B) -> Int64 = Spec2.both(a, b)",
    ] {
        let errs = try_load_kb_with(&program(decl, "useB(wis(n: 4), wis(n: 5))"))
            .err()
            .unwrap_or_default();
        assert_refused_naming(
            &errs,
            &[
                "t.Spec2[B = t.WIS]",
                "cannot be supplied",
                "`t.Both` provides `t.Spec2[A = t.WIS, B = t.NoSp]`",
            ],
            decl,
        );
    }
}

/// A row whose binding at the pinned element is NOT ground (`Gen provides Spec2[A = WIS, B
/// = G]`) cannot be excluded, so the partly-pinned call stays admitted — and runs, off
/// `Gen`'s dictionary.
#[test]
fn a_row_leaving_the_pinned_element_open_keeps_the_call() {
    let generic = "  sort Gen\n    sort G = ?\n    provides Spec2[A = WIS, B = G]\n    \
                   operation both(a: WIS, b: G) -> Int64 = a.n\n  end\n";
    for decl in [
        "  operation useB[P](a: WIS, b: P) -> Int64 requires Spec2[B = P] = Spec2.both(a, b)",
        "  operation useB(a: WIS, b: Spec2.B) -> Int64 = Spec2.both(a, b)",
    ] {
        let mut interp = interp_for(&program(
            &format!("{generic}{decl}"),
            "useB(wis(n: 4), wis(n: 5))",
        ));
        match interp.call("t.go", &[]) {
            Ok(Value::Int(n)) => assert_eq!(n, 4, "{decl}"),
            other => panic!("{decl}: `t.go` must run to an Int64: {other:?}"),
        }
    }
}

/// WI-20260924-0S3YG — the same class through a CONDITIONAL provision: `Box` provides
/// `Store` at `Box[E = E]` only `:- Special[T = E]`, and `Special` is provided at `WIS`
/// alone.
const CONDITIONAL: &str =
    "  sort Special\n    sort T = ?\n    operation tag(x: T) -> Int64\n  end\n  \
                           sort WisSpecial\n    provides Special[T = WIS]\n    \
                           operation tag(x: WIS) -> Int64 = 1\n  end\n  \
                           sort Box\n    sort E = ?\n    entity box(e: E)\n    \
                           provides Store[State = Box[E = E]] :- Special[T = E]\n    \
                           operation peek(s: Box[E = E]) -> Int64 = 100\n  end\n";

const CONDITIONAL_SPELLINGS: [&str; 2] = [
    "  operation usePeek[P](s: P) -> Int64 requires Store[State = P] = Store.peek(s)",
    "  operation usePeek(s: Store.State) -> Int64 = Store.peek(s)",
];

/// At `Box[E = NoSp]` the condition fails, so `Store[State = Box[E = NoSp]]` has no
/// provider. Was (sugar): a clean load that died at eval, `__req_store not bound in caller
/// frame`.
#[test]
fn a_call_whose_conditional_provision_fails_is_refused() {
    for decl in CONDITIONAL_SPELLINGS {
        let errs = try_load_kb_with(&program(
            &format!("{CONDITIONAL}{decl}"),
            "usePeek(box(e: nosp(n: 1)))",
        ))
        .err()
        .unwrap_or_default();
        assert_refused_naming(
            &errs,
            &[
                "t.Store[State = t.Box[E = t.NoSp]]",
                "cannot be supplied",
                "t.usePeek",
            ],
            decl,
        );
    }
}

/// … and at `Box[E = WIS]` it holds, so the call loads and dispatches to `Box`.
#[test]
fn a_call_whose_conditional_provision_holds_runs() {
    for decl in CONDITIONAL_SPELLINGS {
        let mut interp = interp_for(&program(
            &format!("{CONDITIONAL}{decl}"),
            "usePeek(box(e: wis(n: 1)))",
        ));
        match interp.call("t.go", &[]) {
            Ok(Value::Int(n)) => assert_eq!(n, 100, "{decl}"),
            other => panic!("{decl}: `t.go` must run to an Int64: {other:?}"),
        }
    }
}

/// A call a provider meets loads and runs, the body dispatching through the requirement.
#[test]
fn a_provided_call_runs_in_every_spelling() {
    let rows = [
        (
            "  operation useB[P](a: WIS, b: P) -> Int64 requires Spec2[B = P] = Spec2.both(a, b)",
            "useB(wis(n: 4), nosp(n: 5))",
            9,
        ),
        (
            "  operation useB(a: WIS, b: Spec2.B) -> Int64 = Spec2.both(a, b)",
            "useB(wis(n: 4), nosp(n: 5))",
            9,
        ),
        (
            "  operation useB[P](a: WIS, b: P) -> Int64 requires Spec2[A = WIS, B = P] = Spec2.both(a, b)",
            "useB(wis(n: 4), nosp(n: 5))",
            9,
        ),
        (
            "  operation useB(a: WIS, b: S2A.B) -> Int64 = Spec2.both(a, b)",
            "useB(wis(n: 4), nosp(n: 5))",
            9,
        ),
        (
            "  operation look[S](s: S) -> Int64 requires Store[State = S] = Store.peek(s)",
            "look(wis(n: 7))",
            7,
        ),
        (
            "  operation look(s: Store.State) -> Int64 = Store.peek(s)",
            "look(wis(n: 7))",
            7,
        ),
    ];
    for (decl, goal, want) in rows {
        let mut interp = interp_for(&program(decl, goal));
        match interp.call("t.go", &[]) {
            Ok(Value::Int(n)) => assert_eq!(n, want, "{decl}"),
            other => panic!("{decl}: `t.go` must run to an Int64: {other:?}"),
        }
    }
}

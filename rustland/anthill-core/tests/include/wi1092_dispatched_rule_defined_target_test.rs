//! WI-1092 — an operation the carrier DECLARES and nothing DEFINES answered `false`.
//!
//! A carrier may name its own member as a spec's implementation (`provides
//! PartialEq[T = Color, eq = ceq]`), and that member may be defined by RULES rather
//! than by a body: `dispatch_resolved_operation` finds no body, the eq bridge hands
//! the goal to the SLD resolver, and the clauses decide it. That works, and the first
//! test below drives it on both routes.
//!
//! What did not work is the case where the clauses are not there. `prove_rule_predicate`
//! resolved the goal anyway, exhausted an EMPTY candidate set, and reported `Refuted` —
//! which every caller renders as `Bool(false)`. An absent definition is not a false one,
//! and the difference is not academic: the shape that produces it is an UNTAGGED `<=>`
//! equation (`rule ceq(red, red) <=> true`), whose clause is indexed under the connective
//! so the subject owns none (spec §5.3). Such a program loaded clean and silently
//! computed with "not equal" everywhere its carrier's equality was consulted.
//!
//! It is now the `OperationBodyMissing` §5.3 states for exactly this case, on every eval
//! face; the resolver, which has no error channel, leaves the goal undecided instead of
//! deciding it wrongly.

use anthill_core::eval::{EvalError, Value};

/// The two-route program: one carrier `eq`, reached through a requirement DICTIONARY
/// and by NAME, in the same knowledge base.
///
///   * `Holder.same` is generic over `HT` and `requires PartialEq[T = HT]`, so its
///     `PartialEq.eq(a, b)` is DEFERRED to the frame's dictionary, which resolves to
///     `Color.ceq` (the provision's `eq = ceq` binding is honoured).
///   * `PartialEq.eq(a, b)` on CONCRETE arguments needs no dictionary; the `eq`
///     builtin probes the operands' carrier and dispatches to the same `ceq`.
///
/// NOT AVAILABLE as a variant: the same program with the `requires` deleted. WI-325
/// refuses the abstract call outright ("missing `requires PartialEq[T = …]` on
/// enclosing sort"), so on this spelling the dictionary is not optional.
fn program(rules: &str, call: &str) -> String {
    format!(
        r#"
namespace wi1092.ruledef
  import anthill.prelude.{{Bool, Int64, Eq, PartialEq}}
  sort Color
    entity red
    entity blue
    operation ceq(a: Color, b: Color) -> Bool
{rules}
    provides PartialEq[T = Color, eq = ceq]
    provides Eq[T = Color]
  end
  sort Holder
    sort HT = ?
    requires PartialEq[T = HT]
    operation same(a: HT, b: HT) -> Bool = PartialEq.eq(a, b)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = if {call} then 1 else 0
  end
end
"#
    )
}

fn drive(src: &str) -> Result<Value, EvalError> {
    let mut interp = crate::common::interp_for(src);
    interp.call("wi1092.ruledef.Driver.drive", &[Value::Int(0)])
}

/// A rule-defined `eq` decides BOTH routes, and the clauses are what decides them.
///
/// PASSES EITHER WAY BY DESIGN — a regression guard, not the fix's evidence. It is
/// here because WI-1092 was filed believing this route was broken, and it is the
/// half a fix must not break: making the definition-less case loud must not make a
/// DEFINED one loud too.
///
/// The INVERTED fixture is what makes the guard mean anything. `ceq` there says red
/// equals blue and that red does not equal itself — a `ceq` that DISAGREES with
/// structural equality at every point. Written the agreeing way (`ceq(red, red)`,
/// `ceq(blue, blue)`) the whole test passes with `ceq` never consulted at all, which
/// is how WI-580's twin fixture and WI-1092's own filing both came to measure nothing.
#[test]
fn a_rule_defined_eq_decides_the_dictionary_route_and_the_named_one() {
    // Every pair below is structurally UNEQUAL and `ceq`-EQUAL, or the reverse.
    let inverted = "    rule ceq(red, blue) :- true\n    rule ceq(blue, red) :- true";

    let dispatched = drive(&program(inverted, "Holder.same(red(), blue())"));
    assert!(
        matches!(dispatched, Ok(Value::Int(1))),
        "the DICTIONARY route must answer from `Color.ceq`'s clauses: `ceq(red, blue)` \
         is a clause, so `same(red, blue)` is true even though the two are structurally \
         different; got {dispatched:?}"
    );
    let dispatched_neg = drive(&program(inverted, "Holder.same(red(), red())"));
    assert!(
        matches!(dispatched_neg, Ok(Value::Int(0))),
        "and the same route must REFUTE where the clauses do not reach: `ceq(red, red)` \
         is not a clause, so `same(red, red)` is false even though the two are \
         identical; got {dispatched_neg:?}"
    );

    let named = drive(&program(inverted, "PartialEq.eq(red(), blue())"));
    assert!(
        matches!(named, Ok(Value::Int(1))),
        "the NAMED route reaches the same `ceq` for the same pair, so it must give the \
         same answer as the dictionary route; got {named:?}"
    );
    // The one asymmetry, stated rather than pinned: `PartialEq.eq(red(), red())` is 1
    // here, from the structural fast path, which settles two IDENTICAL operands before
    // any carrier dispatch — so it disagrees with `ceq(red, red)` above. That is a
    // reflexivity assumption over a carrier that also `provides Eq`, not WI-1092's
    // defect, and it is exactly what made the filed "control" vacuous: on identical
    // operands the named route never reaches the carrier's `eq` at all.
}

/// kernel-language.md §8.7's carrier declaration, VERBATIM, driven.
///
/// The spec block this mirrors is the one WI-1092 rewrote: it used to be four `<=>`
/// equations under a bare `fact Eq[T = Color]`, a shape measured to do nothing in
/// either half — the equations define no clause, and with no member bound as the
/// carrier's `eq` nothing dispatches to one anyway. A documented declaration that
/// silently does nothing is worse than no example, so it is driven here.
///
/// WHAT MAKES THIS A DRIVE and not a load check: the DICTIONARY route on a carrier
/// whose `eq` has no definition RAISES (the test below), so `Ok` here is the whole
/// assertion — it is reachable only because the clauses are indexed under `ceq` and
/// the provision points the carrier's equality at it. Both rows are needed: the `0`
/// row would also be `0` from structural equality, and the `1` row from the
/// reflexivity fast path; neither would be `Ok` at all if the declaration were the
/// spec's old one.
///
/// PASSES EITHER WAY BY DESIGN, like the guard above: this declaration ran before the
/// fix too. What it pins is the SPEC TEXT — that the block §8.7 now prints is one a
/// program can execute, which the block it replaced was not.
#[test]
fn the_spec_declaration_for_a_rule_given_eq_runs() {
    let src = r#"
namespace wi1092.spec87
  import anthill.prelude.{Bool, Int64, Eq, PartialEq}
  sort Color
    entity red
    entity green
    entity blue
    operation ceq(a: Color, b: Color) -> Bool
    rule ceq(red, red) :- true
    rule ceq(green, green) :- true
    rule ceq(blue, blue) :- true
    provides PartialEq[T = Color, eq = ceq]
    provides Eq[T = Color]
  end
  sort Holder
    sort HT = ?
    requires PartialEq[T = HT]
    operation same(a: HT, b: HT) -> Bool = PartialEq.eq(a, b)
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = if CALL then 1 else 0
  end
end
"#;
    for (call, want) in [
        ("Holder.same(red(), green())", 0),
        ("Holder.same(green(), green())", 1),
    ] {
        let got = {
            let program = src.replace("CALL", call);
            let mut interp = crate::common::interp_for(&program);
            interp.call("wi1092.spec87.Driver.drive", &[Value::Int(0)])
        };
        assert!(
            matches!(got, Ok(Value::Int(n)) if n == want),
            "the spec §8.7 declaration must RUN through a requirement dictionary: \
             `{call}` = {want}; got {got:?}"
        );
    }
}

/// THE FIX. A `ceq` that is DECLARED and nowhere DEFINED is unrunnable, and says so.
///
/// FAILS WHEN THE CHANGE IS BACKED OUT: every assertion here returned `Ok(Int(0))`
/// before — a silent wrong answer on a program that loads clean and raises nothing.
///
/// The fixture is the one from WI-1092's filing, and its rules are the reason: an
/// untagged `<=>` equation is inert (spec §5.3, WI-881), and its clause is indexed
/// under the connective, so `ceq` ends up with a signature and no definition of any
/// kind — no clause, no body, no host mapping. `[simp]` does not change that here
/// (WI-885: no dictionary entry can be built from a rewrite, and a spelled
/// `PartialEq.eq` call is not a redex of `ceq`), which is why the tagged spelling is
/// driven too.
#[test]
fn a_declared_but_undefined_eq_is_loud_on_every_route() {
    let untagged = "    rule ceq(red, red) <=> true\n    rule ceq(blue, blue) <=> true\n    \
                    rule ceq(red, blue) <=> false\n    rule ceq(blue, red) <=> false";
    let tagged = "    rule ceq(red, red) <=> true [simp]\n    \
                  rule ceq(red, blue) <=> false [simp]";

    for (spelling, rules) in [("untagged", untagged), ("[simp]-tagged", tagged)] {
        // The DICTIONARY route: `Holder.same` resolves `eq` to `Color.ceq` correctly,
        // and then there is nothing to run.
        for call in ["Holder.same(red(), red())", "Holder.same(red(), blue())"] {
            let got = drive(&program(rules, call));
            assert!(
                matches!(&got, Err(EvalError::OperationBodyMissing { name, .. })
                         if name == "wi1092.ruledef.Color.ceq"),
                "{spelling} `{call}`: `Color.ceq` is declared and nothing defines it, so \
                 the call is unrunnable — the WI-818 verdict, not `false`; got {got:?}"
            );
        }
        // The NAMED route, on operands the structural fast path does NOT settle: the
        // `eq` builtin dispatches to the same `ceq` and reports the same verdict.
        let named = drive(&program(rules, "PartialEq.eq(red(), blue())"));
        assert!(
            matches!(&named, Err(EvalError::OperationBodyMissing { name, .. })
                     if name == "wi1092.ruledef.Color.ceq"),
            "{spelling} named route: the carrier named `ceq` as its equality, so a \
             structural answer would report a verdict it disowned; got {named:?}"
        );
    }
}

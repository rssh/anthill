//! WI-20260829-YBBC3 — a COMPOUND EXPRESSION is admissible in every DELIMITED value
//! position, not only as an operation body.
//!
//! WHAT WAS BROKEN. `grammar.js` put `match` / `if` / `let` / `lambda` / `proof` in
//! `_expr_body` — the operation-BODY rule — while call arguments, named-argument values
//! and list elements were built from `_term`, which does not include them. And
//! `paren_expr` wrapped a `_term` too, which is why parenthesizing did not rescue any of
//! them: `f(if c then a else b)` and `f((if c then a else b))` were the SAME syntax
//! error. Six spellings were measured on the capability matrix — that test is
//! `typer_capability_matrix_test::a_compound_expression_is_a_value_expression` now, and
//! its rows are load verdicts where they were parse assertions — and not one of them
//! reached the typer.
//!
//! THE RULE THAT REPLACED IT, and it is a rule rather than a list of repaired sites:
//! every compound form is `prec.right` and extends as far right as it can, so it is
//! admissible exactly where a `,` or a closing bracket STOPS it. That is the four
//! delimited positions below, plus `paren_expr`, which is what reaches the positions with
//! no delimiter (an infix operand, a dot receiver, a `match` scrutinee). A `set_literal`
//! element is deliberately NOT among them — `{ a, b }` is already the block / goal-list
//! spelling and admitting `_expr_body` there is a real `rule { _term • , }` grammar
//! conflict — so a set element takes the parenthesized form like any other atom position.
//!
//! WHY THIS FILE IS NOT ONLY PARSE ASSERTIONS. "It parses" is not evidence that anything
//! works: a compound form in an argument becomes a marker term the loader lowers and the
//! typer must check like any other argument, and none of that had ever run from these
//! positions. Every case here is DRIVEN to a VALUE through `Interpreter::call`, and the
//! refusal cases assert a LOCATED diagnostic, so the file says what the positions do and
//! not merely that the parser accepted them.
//!
//! BACKING THE CHANGE OUT — restore `_positional_fn_arg`, `named_arg`'s `value`,
//! `collection_literal`'s elements and `paren_expr` to `$._term` in `grammar.js`.
//! MEASURED: **10 of the 13 tests here fail**, every one of them at PARSE
//! (`syntax error near \`if true then 7 else\``), and **4 in
//! `typer_capability_matrix_test`** with them —
//! `a_compound_expression_is_a_value_expression`, `a_lambda_inside_a_list_literal`,
//! `every_position_through_a_provision_chain` and
//! `the_remaining_positions_across_their_routes`.
//!
//! The three `control_` tests pass either way, by design and each for its own reason —
//! two of them name a limit the change deliberately did NOT lift (a set element, an infix
//! operand), which is what stops "widen the grammar" from being read as "compound forms
//! are terms now", and the third is the ordinary spellings, which must not move.

use crate::common::{interp_for, try_load_kb_with};
use anthill_core::eval::{Interpreter, Value};

fn expect_int(v: Value) -> i64 {
    v.as_int().unwrap_or_else(|| panic!("expected Int64, got {v:?}"))
}

/// A diagnostic carrying a `line:col:` prefix. Spelled out rather than "contains a
/// colon": every message contains one somewhere, so the loose reading would call an
/// unlocated diagnostic located.
fn is_located(msg: &str) -> bool {
    let mut it = msg.split(':');
    matches!((it.next(), it.next()), (Some(l), Some(c))
        if !l.is_empty() && l.chars().all(|ch| ch.is_ascii_digit())
            && !c.is_empty() && c.chars().all(|ch| ch.is_ascii_digit()))
}

/// One two-field entity plus the helpers every case calls. `pair_up` is deliberately
/// NON-COMMUTATIVE in its two arguments (`a * 100 + b`) — a call whose arguments were
/// mis-delimited would still sum to something, and only a weighted combination says WHICH
/// slot each landed in.
fn program(ops: &str) -> String {
    format!(
        r#"
namespace wiybbc3
  import anthill.prelude.{{Int64, Bool, List, Set}}
  sort Row
    import anthill.prelude.{{Int64, Bool}}
    entity row(a: Int64, flag: Bool)
    operation a_of(r: Row) -> Int64 = match r case row(x, f) -> x
  end
  import wiybbc3.Row.{{row}}
  operation mk(n: Int64) -> Row = row(a: n, flag: true)
  operation takes_int(v: Int64) -> Int64 = v
  operation takes_list(xs: List[T = Int64]) -> Int64 = 1
  operation takes_set(xs: Set[T = Int64]) -> Int64 = 1
  operation pair_up(a: Int64, b: Int64) -> Int64 = a * 100 + b
  operation sum3(xs: List[T = Int64]) -> Int64 = match xs
    case cons(h, t) -> h + sum3(t)
    case nil() -> 0
{ops}
end
"#
    )
}

fn call_main(ops: &str) -> i64 {
    let mut interp: Interpreter = interp_for(&program(ops));
    expect_int(interp.call("wiybbc3.main", &[]).expect("call main"))
}

/// `if` as a call argument, bare and parenthesized. Both spellings were the same syntax
/// error; both now reach the callee and both compute.
#[test]
fn an_if_is_a_call_argument() {
    assert_eq!(call_main("  operation main() -> Int64 = takes_int(if true then 7 else 9)"), 7);
    assert_eq!(call_main("  operation main() -> Int64 = takes_int(if false then 7 else 9)"), 9);
    assert_eq!(call_main("  operation main() -> Int64 = takes_int((if true then 7 else 9))"), 7);
}

/// `match` as a call argument — the form the ticket names first, and the one with the
/// real "where does the arm list end" question, since `repeat1(match_branch)` has no
/// terminator of its own.
#[test]
fn a_match_is_a_call_argument() {
    assert_eq!(
        call_main("  operation main() -> Int64 = takes_int(match mk(7) case row(x, f) -> x)"),
        7
    );
    assert_eq!(
        call_main("  operation main() -> Int64 = takes_int((match mk(7) case row(x, f) -> x))"),
        7
    );
}

/// THE COMMA ENDS THE ARM LIST — the assertion the whole delimited-position rule rests
/// on. `pair_up`'s weighting is what makes this measure the SLOTS: had the `, 3` been
/// swallowed by the match or dropped, the answer would not be 703. A commutative
/// combiner would answer the same for either reading and prove nothing.
#[test]
fn a_comma_ends_a_match_arm_list_in_an_argument() {
    assert_eq!(
        call_main("  operation main() -> Int64 = pair_up(match mk(7) case row(x, f) -> x, 3)"),
        703
    );
    // And the compound form in the SECOND slot, so the rule is not an artefact of the
    // arm list running into the closing paren.
    assert_eq!(
        call_main("  operation main() -> Int64 = pair_up(3, match mk(7) case row(x, f) -> x)"),
        307
    );
}

/// A `let` chain as a call argument. Its body is an `_expr_body` too, so the same
/// delimiter argument carries it.
#[test]
fn a_let_chain_is_a_call_argument() {
    assert_eq!(
        call_main(
            "  operation main() -> Int64 = pair_up(let v = 7\n    v, 3)"
        ),
        703
    );
}

/// A compound expression as a NAMED-argument value. `named_arg` admitted a lambda and
/// nothing else; the value is now an `_expr_body` on the same terms as a positional one.
#[test]
fn a_compound_expression_is_a_named_argument_value() {
    assert_eq!(
        call_main("  operation main() -> Int64 = pair_up(a: if true then 7 else 9, b: 3)"),
        703
    );
    assert_eq!(
        call_main(
            "  operation main() -> Int64 = pair_up(a: match mk(7) case row(x, f) -> x, b: 3)"
        ),
        703
    );
}

/// A compound expression as a TUPLE COMPONENT, positional and named. `tuple_literal`
/// shares the `_fn_arg` grammar with a call, so it is the fourth delimited position and
/// the spec (§4.8) names it; pinned so that claim is checked and not merely written.
#[test]
fn a_compound_expression_is_a_tuple_component() {
    // Driven through a projection so each COMPONENT's value is asserted, not just that
    // the tuple typed: `fst`/`snd` read the two slots back out.
    assert_eq!(
        call_main(
            "  operation main() -> Int64 =\n    let t: (a: Int64, b: Int64) =              (a: if true then 7 else 9, b: 3)\n    pair_up(t.a, t.b)"
        ),
        703
    );
    assert_eq!(
        call_main(
            "  operation main() -> Int64 =\n    let t: (a: Int64, b: Int64) = \
             (a: match mk(7) case row(x, f) -> x, b: 3)\n    pair_up(t.a, t.b)"
        ),
        703
    );
}

/// A compound expression as a LIST ELEMENT — the position
/// `typer_capability_matrix_test::a_lambda_inside_a_list_literal` records through one
/// form, and the reason WI-20260828-5NSZY could not offer "write a lambda instead" as the
/// repair for a bare operation name in a list literal. Summed through `sum3` so each
/// element's VALUE is asserted, not just the literal's length.
#[test]
fn a_compound_expression_is_a_list_element() {
    assert_eq!(
        call_main(
            "  operation main() -> Int64 = sum3([if true then 7 else 9, \
             match mk(20) case row(x, f) -> x, 300])"
        ),
        327
    );
}

/// PARENTHESES ARE THE ESCAPE into the positions with no delimiter. Each of these three
/// is an `_atom_term` slot — an infix operand, a dot receiver, a `match` scrutinee — and
/// the compound form reaches it only because `paren_expr` now wraps an `_expr_body`.
#[test]
fn parentheses_reach_the_undelimited_positions() {
    // infix operand
    assert_eq!(call_main("  operation main() -> Int64 = 100 + (if true then 7 else 9)"), 107);
    // dot receiver
    assert_eq!(
        call_main("  operation main() -> Int64 = (if true then mk(7) else mk(9)).a_of()"),
        7
    );
    // match scrutinee
    assert_eq!(
        call_main(
            "  operation main() -> Int64 = match (if true then mk(7) else mk(9)) \
             case row(x, f) -> x"
        ),
        7
    );
    // set element — a set literal's elements stay `_term`, so this is the ONLY spelling
    // that reaches one (see `control_a_set_element_still_needs_its_parentheses`).
    assert_eq!(
        call_main("  operation main() -> Int64 = takes_set({(if true then 7 else 9), 3})"),
        1
    );
}

/// THE POSITION IS TYPE-CHECKED, which is what stops every case above from being green
/// for the wrong reason. If a compound form in an argument were merely PARSED and then
/// skipped by the typer, all of them would still compute — so the evidence that the
/// position is a real argument is that an ill-typed one is REFUSED, with a span.
#[test]
fn an_ill_typed_compound_argument_is_refused_located() {
    for (what, body) in [
        (
            "a match arm's type",
            "  operation main() -> Int64 = takes_int(match mk(7) case row(x, f) -> f)",
        ),
        (
            "an if branch's type",
            "  operation main() -> Int64 = takes_int(if true then 1 else true)",
        ),
        (
            "a named-argument value's type",
            "  operation main() -> Int64 = pair_up(a: if true then 1 else true, b: 3)",
        ),
        (
            "a list element's type through a parenthesis",
            "  operation main() -> Int64 = sum3([1, (if true then 2 else true)])",
        ),
    ] {
        let errs = try_load_kb_with(&program(body))
            .err()
            .unwrap_or_else(|| panic!("{what}: expected a REFUSAL, but `{body}` loaded clean"));
        // ONE error must satisfy BOTH: an unrelated located companion diagnostic must
        // not stand in for a span on the diagnostic this case is about.
        assert!(
            errs.iter().any(|e| e.contains("Bool") && is_located(e)),
            "{what}: expected a LOCATED (`line:col:`) refusal naming the `Bool`, got {errs:?}"
        );
    }
}

/// CONTROL — a set literal's elements are still `_term`. This is the one delimited
/// position the change did NOT widen, and the reason is a measured grammar conflict
/// (`rule { _term • , }`: `{ a, b }` is already the block / goal-list spelling), not an
/// oversight. It passes with the change backed out, and it is what makes
/// `parentheses_reach_the_undelimited_positions`' set row a claim about the escape rather
/// than an accident.
#[test]
fn control_a_set_element_still_needs_its_parentheses() {
    let src = program("  operation main() -> Int64 = takes_set({if true then 7 else 9, 3})");
    assert!(
        anthill_core::parse::parse(&src).is_err(),
        "a BARE compound form as a set-literal element now parses. If the `rule {{ … }}` \
         conflict was settled, widen `set_literal` too, flip this control into a value \
         assertion beside the parenthesized row, and say here what settled it."
    );
}

/// CONTROL — a compound form is still not an `_atom_term`. `1 + if c then a else b` is a
/// syntax error, and deliberately: `_term` was not widened, only the delimited positions
/// and `paren_expr` were. Passes with the change backed out. Without it, nothing in this
/// file separates "admissible where a delimiter ends it" from "compound forms are terms".
#[test]
fn control_a_bare_compound_form_is_not_an_infix_operand() {
    let src = program("  operation main() -> Int64 = 100 + if true then 7 else 9");
    assert!(
        anthill_core::parse::parse(&src).is_err(),
        "a bare compound form is now an infix operand. That is a LARGER change than \
         WI-20260829-YBBC3 made — `_term` itself would have to admit the compound forms, \
         which also puts them in dot-receiver and pattern positions. Say so at the \
         grammar site before flipping this."
    );
}

/// CONTROL — the ordinary meaning of every widened position is unchanged. A plain term
/// argument, named-argument value and list element still compute what they always did.
/// Passes with the change backed out; it is the row that would catch a widening that
/// re-routed the ORDINARY case through the compound dispatch and broke it.
#[test]
fn control_the_ordinary_spellings_are_unchanged() {
    assert_eq!(call_main("  operation main() -> Int64 = pair_up(7, 3)"), 703);
    assert_eq!(call_main("  operation main() -> Int64 = pair_up(a: 7, b: 3)"), 703);
    assert_eq!(call_main("  operation main() -> Int64 = sum3([1, 2, 300])"), 303);
    assert_eq!(call_main("  operation main() -> Int64 = takes_int((7))"), 7);
}



/// WHAT THE WIDENING ALSO REACHES, MEASURED RATHER THAN ASSUMED. A rule head, a rule body
/// goal and a `fact` argument are all built from the same `_fn_arg` grammar, so widening
/// the ARGUMENT position widens them too: `fact p(if true then 1 else 2)` now loads, where
/// before it was a syntax error.
///
/// AND IT LOADS INTO A TERM NOTHING CAN MATCH BY WRITING IT AGAIN. The same compound form,
/// spelled identically in a `fact` and in a goal, does NOT unify — the goal answers
/// nothing, silently. A variable goal `p(?z)` DOES answer, so the fact is stored and
/// reachable; it is the written form that cannot address it.
///
/// THIS IS NOT NEW, AND THE CONTROL IS WHAT SAYS SO: a `lambda` has been admissible in
/// exactly these positions all along (`_fn_arg` carried it before `_expr_body` did), and
/// it behaves the same way — `fact p(lambda x -> 1)` is not matched by a goal
/// `p(lambda x -> 1)` either. So this is a pre-existing property of a parse-time marker in
/// a rule data position that the widening made reachable through four more spellings; it
/// is not a defect WI-20260829-YBBC3 introduced, and diagnosing it is not that ticket's
/// work. It is filed as WI-20260829-8VGRW.
///
/// PINNED HERE, in the file whose change made it reachable, so that whoever fixes
/// WI-20260829-8VGRW has a test that fails the day it starts working — the `KnownGap`
/// shape used elsewhere in this suite, spelled out because this file has no `Verdict`
/// machinery.
#[test]
fn a_compound_form_in_a_rule_data_position_loads_and_matches_nothing() {
    fn answers(src: &str, qn: &str) -> usize {
        let mut kb = crate::common::load_kb_with(src);
        crate::common::definite_unary(&mut kb, qn).len()
    }
    // `fact`, not a body-less `rule` head: proposal 061 makes a body-less head a
    // DECLARATION that stores no clause, so `rule p(…)` would leave `p` empty and every
    // row here would read 0 for a reason that has nothing to do with this ticket
    // (MEASURED — a plain `rule p(1)` / `rule same(1) :- p(1)` pair answers 0 too).
    const COMPOUND: &str = r#"
namespace wiybbc3rule.compound
  import anthill.prelude.{Int64, Bool}
  fact p(if true then 1 else 2)
  rule written(1) :- p(if true then 1 else 2)
  rule variable(1) :- p(?z)
end
"#;
    // THE FIXTURE ANSWERS AT ALL — asked first, because every other count here is a 0 or a
    // 1 and a fixture that decides nothing would read as a clean negative.
    assert_eq!(
        answers(COMPOUND, "wiybbc3rule.compound.variable"),
        1,
        "the fact must be reachable at all before any row below means anything"
    );
    assert_eq!(
        answers(COMPOUND, "wiybbc3rule.compound.written"),
        0,
        "WI-20260829-8VGRW HAS CLOSED — the written compound form now addresses the \
         fact it is spelled identically to. Flip this to 1, close that ticket, and say \
         what fixed it."
    );

    // THE CONTROL, AND IT IS THE ATTRIBUTION: a `lambda` reaches these positions through
    // the grammar that was there BEFORE this ticket, and behaves identically. It is what
    // says the behaviour above belongs to a parse-time marker in a rule data position and
    // not to the widening. It passes with the widening backed out.
    const LAMBDA: &str = r#"
namespace wiybbc3rule.lam
  import anthill.prelude.{Int64, Bool}
  fact p(lambda x -> 1)
  rule written(1) :- p(lambda x -> 1)
  rule variable(1) :- p(?z)
end
"#;
    assert_eq!(answers(LAMBDA, "wiybbc3rule.lam.variable"), 1);
    assert_eq!(
        answers(LAMBDA, "wiybbc3rule.lam.written"),
        0,
        "the pre-existing `lambda` spelling must behave the same — if it does not, the \
         attribution above is wrong and the widening DID change something here"
    );

    // AND THE ORDINARY TERM DOES MATCH, which is what stops the two rows above from being
    // "rule data positions never match anything".
    const PLAIN: &str = r#"
namespace wiybbc3rule.plain
  import anthill.prelude.{Int64, Bool}
  fact p(1)
  rule written(1) :- p(1)
end
"#;
    assert_eq!(answers(PLAIN, "wiybbc3rule.plain.written"), 1);
}

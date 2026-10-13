//! A call written for a spec operation, and the requirement the MEMBER it is dispatched to
//! states on itself.
//!
//! `Desc.pair` requires `other: Tagger[T = U]` of its own type parameter, and `Coin`
//! provides `Desc` with a member that states the same requirement. A call that selected a
//! provider for it — `Desc.pair[other = Loud](coin(n: 5), "s")` — loaded, and ended
//! `AmbiguousRequirement` where it ran: two providers of `Tagger[T = String]`, of which
//! the call had named one. Where the argument's type has a provision of its own the call
//! answered by that one and said nothing: `Desc.cmp2[WeakOrd = ByLength](coin(n: 5),
//! "bob", "amyy")` gave 1, `String`'s own order, where the lengths give -1. The member's
//! own spelling, `Coin.pair[other = Loud](…)`, answered 13 throughout.
//!
//! The call's substitution and its selections are in the SPEC operation's parameters and
//! names. The member's requirement is written over a type parameter of its own and read
//! back under a name of its own, so nothing the call said reached it: its entry stayed
//! unpinned, no dictionary was built for it at the call, and the member resolved the
//! requirement from its argument values when it ran.
//!
//! What the member is handed now, each backed out below. WHERE THE MEMBER IS KNOWN AS THE
//! CALL IS TYPED (`call_at_member`):
//!
//!   * ITS TYPE PARAMETERS ARE THE SPEC OPERATION'S, by position — the pairing the
//!     override check holds a member to (`paired_type_params`). Each is bound to what the
//!     call bound the spec operation's. The name of a requirement is a type parameter and
//!     is bound with the rest: where it is in a parameter's type (`s: Box[E = U, O =
//!     other]`), to what the argument's type says.
//!   * THE SELECTION FOR A REQUIREMENT, UNDER THE MEMBER'S NAME FOR IT. A requirement of
//!     the member is the spec operation's that reads the same once the parameters are
//!     paired; what each calls it is its own.
//!
//! WHERE IT IS CHOSEN AS THE CALL RUNS — the receiver a parameter of the caller under its
//! own `requires Desc[T = X]`, or the call a spec's default body calling its sibling:
//!
//!   * THE CALL IS STAMPED FOR THE SPEC OPERATION (`stamp_spec_op_supply`), at every way
//!     out of the dispatch that hands it to no member. No dictionary was built at such a
//!     call at all.
//!   * THE MEMBER THAT ANSWERS READS THOSE SLOTS UNDER ITS OWN NAMES
//!     (`member_slots_at_spec_op`, `Interpreter::hand_spec_op_slots`): on the route
//!     through a requirement the caller holds, which took none, and on the route by the
//!     receiver's value, which rebuilt the frame from the dictionary and dropped them.
//!
//! ## Back-out
//!
//! Each mechanism switched off in place and every row of this file run, with the rows of
//! the files that select a provider, state a requirement on an operation or lift one to a
//! function value (wi840, wi841, wi844, wi870, wi1091, wi1094, wi_tx0g6, wi_wn9p8,
//! wi_ee0ep, wi_0rrqp, wi_0k8wd, wi_bqhgd, wi_159s9, wi_28tat and that family; measured
//! 2026-10-13):
//!
//! | backed out | fails |
//! |---|---|
//! | where the member is known: the member handed the call as it was written | nine rows — every one above "A member chosen when the call runs" but the two that pass either way and [`a_rule_body_goal_whose_member_is_found_later_is_left_to_the_bridge`] — and `wi_0k8wd_selection_per_requirement_test::a_selection_for_a_requirement_on_the_dispatched_spec_is_not_the_dispatchs` |
//! | … the member's type parameters left unbound | the same |
//! | … the names of requirements left out of that binding | [`a_name_bound_to_a_parameter_nothing_is_held_for_is_refused`] |
//! | … the selections left under the spec operation's names | [`the_member_reads_it_under_its_own_names`], [`a_name_an_arguments_type_binds_is_the_members`], [`two_requirements_at_one_type_are_two_at_the_member`] — the rows where the member's name is another |
//! | the member's entries not paired with the spec operation's — the parameters not paired in the comparison, or every entry read under its own key | those three and [`two_requirements_reach_a_member_chosen_when_the_call_runs`] |
//! | the entries paired by the sort they require, and not by the requirement as declared | [`two_requirements_at_one_type_are_two_at_the_member`], [`two_requirements_reach_a_member_chosen_when_the_call_runs`] |
//! | where the member is chosen later: the call not stamped for the spec operation | the eight rows under "A member chosen when the call runs" |
//! | … one way out of the dispatch left without the stamp, each on its own | the deferral of a defaulted member: [`the_spec_operations_own_body_reads_what_the_call_filled`]; the deferral to a requirement on the caller's operation: five of the eight; to one on the caller's sort, the receiver typed as the spec, and the receiver typed as an abstract sort that provides it: [`every_way_a_member_is_chosen_later_hands_the_selection`], one program of it each; the block's end: [`a_spec_default_body_hands_its_requirement_to_the_sibling`] |
//! | … the stamp not handed to the member on the route through a requirement the caller holds | the eight less [`a_spec_default_body_hands_its_requirement_to_the_sibling`] and [`a_call_whose_member_is_chosen_later_owes_the_spec_operations_requirement`] |
//! | … not handed on the route by the receiver's value | [`a_spec_default_body_hands_its_requirement_to_the_sibling`] — where the frame is rebuilt from the dictionary; a slot passed on untouched reaches a member that calls it the same |
//! | … a slot handed under the spec operation's name for it, and not the member's | [`two_requirements_reach_a_member_chosen_when_the_call_runs`] |
//! | a rule-body goal stamped as an operation body's call is | [`a_rule_body_goal_whose_member_is_found_later_is_left_to_the_bridge`] |
//!
//! PASS EITHER WAY, BY DESIGN: [`a_member_that_states_no_requirement_is_handed_none`] and
//! [`a_member_restates_the_requirements_as_the_spec_operation_wrote_them`], each saying
//! why at its site; and inside the rows, the member's own spelling beside a dispatched
//! call, the call with one provider to choose from, the rule whose receiver is bound when
//! it runs, and the member that states no requirement.
//!
//! ## Not reached
//!
//!   * THREE WAYS OUT OF THE DISPATCH ARE NOT STAMPED: the two returns of the
//!     instance-fact dispatch, and the licence taken where no provider matches. No
//!     program was built that reaches them with a spec operation that states a
//!     requirement of its own; a call that does is decided from the argument values, as
//!     every such call was.
//!   * A RULE-BODY GOAL is handed to a member that is known where the rule is loaded
//!     ([`a_rule_body_goal_is_handed_to_the_member`]) and is otherwise the bridge's
//!     ([`a_rule_body_goal_whose_member_is_found_later_is_left_to_the_bridge`]). A goal
//!     cannot write a selection, and the bridge reads none.

use anthill_core::eval::{Interpreter, Value};
use crate::common::load_errors_of;

/// Two providers of `Tagger[T = String]` that answer differently and one of `Tagger[T =
/// Int64]`; `Marker`, a second sort to require; and `ByLength`, an order of `String`
/// beside the one `String` has.
const DECLS: &str = r#"
  import anthill.prelude.{Int64, String, Ord, WeakOrd}
  import anthill.prelude.Numeric.{add, mul, sub}

  sort Tagger
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort Quiet
    provides Tagger[T = String]
    operation tag(x: String) -> Int64 = 2
  end
  sort Loud
    provides Tagger[T = String]
    operation tag(x: String) -> Int64 = 3
  end
  sort Plain
    provides Tagger[T = Int64]
    operation tag(x: Int64) -> Int64 = 5
  end
  sort Marker
    sort T = ?
    operation mark(x: T) -> Int64
  end
  sort ByLength
    provides Ord[T = String]
    operation compare(a: String, b: String) -> Int64 = sub(a.length(), b.length())
  end
  sort Box
    sort E = ?
    requires O: Tagger[T = E]
    entity box(v: E)
  end
"#;

/// The report's spec operation: a requirement named `other`, of the operation's own `U`.
const SPEC_PAIR: &str = "    operation pair[U](x: T, y: U) -> Int64 requires other: Tagger[T = U]\n";
/// The member that states it as the spec operation does.
const MEMBER_PAIR: &str =
    "    operation pair[U](x: Coin, y: U) -> Int64 requires other: Tagger[T = U] = add(10, Tagger.tag(y))\n";

/// `Desc` with `spec_ops`, `Coin` providing it with `member_ops`, and a `Driver` with
/// `driver_ops`.
fn program(ns: &str, spec_ops: &str, member_ops: &str, driver_ops: &str) -> String {
    program_with_rules(ns, spec_ops, member_ops, driver_ops, "")
}

/// [`program`] with `rules` written in the namespace, after the sorts.
fn program_with_rules(
    ns: &str,
    spec_ops: &str,
    member_ops: &str,
    driver_ops: &str,
    rules: &str,
) -> String {
    format!(
        "namespace {ns}\n{DECLS}
  sort Desc
    sort T = ?
    operation tag(x: T) -> Int64
{spec_ops}  end
  sort Coin
    entity coin(n: Int64)
    provides Desc[T = Coin]
    operation tag(x: Coin) -> Int64 = 1
{member_ops}  end
  sort Driver
    import {ns}.Coin.{{coin}}
    import {ns}.Box.{{box}}
{driver_ops}  end
{rules}end
"
    )
}

/// The run-time outcome of the nullary `Driver.<op>` on a FRESH interpreter, which panics
/// on a dirty load — so an outcome is also a clean-load assertion.
fn outcome(src: &str, ns: &str, op: &str) -> Result<Value, String> {
    let mut interp: Interpreter = crate::common::interp_for(src);
    interp
        .call(&format!("{ns}.Driver.{op}"), &[])
        .map_err(|e| format!("{e:?}"))
}

fn value(src: &str, ns: &str, op: &str) -> i64 {
    match outcome(src, ns, op) {
        Ok(Value::Int(n)) => n,
        other => panic!("{ns}.Driver.{op}: expected an Int64, got {other:?}"),
    }
}

// ── The report's rows ────────────────────────────────────────────────

/// THE REPORT'S PROGRAM. `Coin.pair` adds 10 to what the selected provider answers for
/// `"s"`: 3 by `Loud`, 2 by `Quiet`. The member's own spelling is the control — it
/// answered 13 before.
#[test]
fn a_selection_is_handed_to_the_member() {
    let ns = "specreq.report";
    let src = program(
        ns,
        SPEC_PAIR,
        MEMBER_PAIR,
        "    operation loud() -> Int64 = Desc.pair[other = Loud](coin(n: 5), \"s\")
    operation quiet() -> Int64 = Desc.pair[other = Quiet](coin(n: 5), \"s\")
    operation member() -> Int64 = Coin.pair[other = Loud](coin(n: 5), \"s\")
",
    );
    assert_eq!(value(&src, ns, "loud"), 13, "`Desc.pair[other = Loud]`");
    assert_eq!(value(&src, ns, "quiet"), 12, "`Desc.pair[other = Quiet]`");
    assert_eq!(value(&src, ns, "member"), 13, "the member's own spelling");
}

/// THE WRONG ANSWER. `String` has an order of its own, so a selection that is not handed
/// over is not a tie: the member finds `String`'s. By length `"bob"` is below `"amyy"`,
/// by `String`'s own order above it. The call that selects nothing is the control, and
/// answers by `String`'s.
#[test]
fn a_selection_is_not_answered_by_the_types_own_provision() {
    let ns = "specreq.own";
    let src = program(
        ns,
        "    operation cmp2[U](x: T, a: U, b: U) -> Int64 requires WeakOrd[T = U]\n",
        "    operation cmp2[U](x: Coin, a: U, b: U) -> Int64 requires WeakOrd[T = U] = WeakOrd.compare(a, b)\n",
        "    operation selected() -> Int64 = Desc.cmp2[WeakOrd = ByLength](coin(n: 5), \"bob\", \"amyy\")
    operation member() -> Int64 = Coin.cmp2[WeakOrd = ByLength](coin(n: 5), \"bob\", \"amyy\")
    operation unselected() -> Int64 = Desc.cmp2(coin(n: 5), \"bob\", \"amyy\")
",
    );
    assert_eq!(value(&src, ns, "selected"), -1, "`Desc.cmp2[WeakOrd = ByLength]`");
    assert_eq!(value(&src, ns, "member"), -1, "the member's own spelling");
    assert_eq!(value(&src, ns, "unselected"), 1, "nothing selected: `String`'s own order");
}

/// THE MEMBER READS THE CALL IN ITS OWN NAMES. The requirement under another name, the
/// type parameter under another name, both, and no name on either side with the provider
/// selected by the sort's name.
#[test]
fn the_member_reads_it_under_its_own_names() {
    let named = [
        ("specreq.names.req", "pair[U](x: Coin, y: U) -> Int64 requires o: Tagger[T = U]"),
        ("specreq.names.param", "pair[V](x: Coin, y: V) -> Int64 requires other: Tagger[T = V]"),
        ("specreq.names.both", "pair[V](x: Coin, y: V) -> Int64 requires o: Tagger[T = V]"),
    ];
    for (ns, member) in named {
        let src = program(
            ns,
            SPEC_PAIR,
            &format!("    operation {member} = add(10, Tagger.tag(y))\n"),
            "    operation loud() -> Int64 = Desc.pair[other = Loud](coin(n: 5), \"s\")
    operation quiet() -> Int64 = Desc.pair[other = Quiet](coin(n: 5), \"s\")
",
        );
        assert_eq!(value(&src, ns, "loud"), 13, "`{member}`, `[other = Loud]`");
        assert_eq!(value(&src, ns, "quiet"), 12, "`{member}`, `[other = Quiet]`");
    }
    let ns = "specreq.names.unnamed";
    let src = program(
        ns,
        "    operation pair[U](x: T, y: U) -> Int64 requires Tagger[T = U]\n",
        "    operation pair[V](x: Coin, y: V) -> Int64 requires Tagger[T = V] = add(10, Tagger.tag(y))\n",
        "    operation loud() -> Int64 = Desc.pair[Tagger = Loud](coin(n: 5), \"s\")
    operation quiet() -> Int64 = Desc.pair[Tagger = Quiet](coin(n: 5), \"s\")
",
    );
    assert_eq!(value(&src, ns, "loud"), 13, "no name on either side, `[Tagger = Loud]`");
    assert_eq!(value(&src, ns, "quiet"), 12, "no name on either side, `[Tagger = Quiet]`");
}

/// TWO REQUIREMENTS THE CALL PUTS AT ONE TYPE ARE TWO AT THE MEMBER. `U` and `V` are both
/// `String`, so the two goals are one text; the member's entries are paired with the spec
/// operation's as declared, each with its own selection. The tens are `y`'s provider, the
/// units `z`'s.
#[test]
fn two_requirements_at_one_type_are_two_at_the_member() {
    let ns = "specreq.two";
    let src = program(
        ns,
        "    operation both[U, V](x: T, y: U, z: V) -> Int64 requires a: Tagger[T = U], b: Tagger[T = V]\n",
        "    operation both[U, V](x: Coin, y: U, z: V) -> Int64 requires p: Tagger[T = U], q: Tagger[T = V] \
         = add(mul(10, Tagger.tag(y)), Tagger.tag(z))\n",
        "    operation ab() -> Int64 = Desc.both[a = Loud, b = Quiet](coin(n: 5), \"s\", \"t\")
    operation ba() -> Int64 = Desc.both[a = Quiet, b = Loud](coin(n: 5), \"s\", \"t\")
",
    );
    assert_eq!(value(&src, ns, "ab"), 32, "`a = Loud, b = Quiet`");
    assert_eq!(value(&src, ns, "ba"), 23, "`a = Quiet, b = Loud`");
}

/// WHAT THE ROWS ABOVE REST ON: A MEMBER RESTATES THE SPEC OPERATION'S REQUIREMENTS AS
/// THEY ARE WRITTEN, or states none. In another order, or a part of them, the member is
/// refused where it is declared, as one that requires what the spec operation does not.
/// So no row here has a member whose entries are the spec operation's in another order,
/// and a change that admits one owes this file the rows for it. Passes with and without
/// this file's change: the refusal is the override check's.
#[test]
fn a_member_restates_the_requirements_as_the_spec_operation_wrote_them() {
    for (ns, member) in [
        ("specreq.restated.order", "Marker[T = V], Tagger[T = U]"),
        ("specreq.restated.part", "Marker[T = V]"),
    ] {
        let errors = load_errors_of(&program(
            ns,
            "    operation both[U, V](x: T, y: U, z: V) -> Int64 requires Tagger[T = U], Marker[T = V]\n",
            &format!("    operation both[U, V](x: Coin, y: U, z: V) -> Int64 requires {member} = 1\n"),
            "",
        ));
        let joined = errors.join("\n");
        for token in [&format!("'{ns}.Coin' overrides '{ns}.Desc.both'"), "it strengthens the precondition"] {
            assert!(
                joined.contains(token),
                "a member that `requires {member}`: the refusal names `{token}`; got {errors:#?}"
            );
        }
    }
}

/// A REQUIREMENT THE CALLER HOLDS IS THE MEMBER'S. `relay` requires `Tagger[T = A]` and
/// calls the spec operation at its own `A`; the provider its caller selected is the one
/// the member reads.
#[test]
fn a_requirement_the_caller_holds_is_handed_on() {
    let ns = "specreq.forward";
    let src = program(
        ns,
        "    operation pair[U](x: T, y: U) -> Int64 requires Tagger[T = U]\n",
        "    operation pair[U](x: Coin, y: U) -> Int64 requires Tagger[T = U] = add(10, Tagger.tag(y))\n",
        "    operation relay[A](c: Coin, a: A) -> Int64 requires Tagger[T = A] = Desc.pair(c, a)
    operation loud() -> Int64 = relay[Tagger = Loud](coin(n: 5), \"s\")
    operation quiet() -> Int64 = relay[Tagger = Quiet](coin(n: 5), \"s\")
",
    );
    assert_eq!(value(&src, ns, "loud"), 13, "`relay[Tagger = Loud]`");
    assert_eq!(value(&src, ns, "quiet"), 12, "`relay[Tagger = Quiet]`");
}

/// The spec operation and the member each put the requirement's name in a parameter's
/// type, under names of their own.
const KEEP: (&str, &str) = (
    "    operation keep[U](x: T, s: Box[E = U, O = other]) -> Int64 requires other: Tagger[T = U]\n",
    "    operation keep[U](x: Coin, s: Box[E = U, O = o]) -> Int64 requires o: Tagger[T = U] \
     = add(10, Tagger.tag(s.v))\n",
);

/// A NAME THE ARGUMENT'S TYPE BINDS IS THE MEMBER'S NAME. The provider is written in the
/// box's type and nowhere at the call. Where the box's type names a provider the member
/// reads that one; where it names a parameter of the caller, the member reads the
/// dictionary the caller holds for that parameter.
#[test]
fn a_name_an_arguments_type_binds_is_the_members() {
    let ns = "specreq.byarg";
    let src = program(
        ns,
        KEEP.0,
        KEEP.1,
        "    operation mkLoud() -> Box[E = String, O = Loud] = box(v: \"s\")
    operation mkQuiet() -> Box[E = String, O = Quiet] = box(v: \"s\")
    operation loud() -> Int64 = Desc.keep(coin(n: 5), mkLoud())
    operation quiet() -> Int64 = Desc.keep(coin(n: 5), mkQuiet())
    operation relay[A, P](c: Coin, b: Box[E = A, O = P]) -> Int64 requires P: Tagger[T = A] = Desc.keep(c, b)
    operation relayedLoud() -> Int64 = relay(coin(n: 5), mkLoud())
    operation relayedQuiet() -> Int64 = relay(coin(n: 5), mkQuiet())
",
    );
    assert_eq!(value(&src, ns, "loud"), 13, "a box typed `O = Loud`");
    assert_eq!(value(&src, ns, "quiet"), 12, "a box typed `O = Quiet`");
    assert_eq!(value(&src, ns, "relayedLoud"), 13, "relayed, a box typed `O = Loud`");
    assert_eq!(value(&src, ns, "relayedQuiet"), 12, "relayed, a box typed `O = Quiet`");
}

/// …AND A PARAMETER THE CALLER HOLDS NO DICTIONARY FOR IS REFUSED, in the spec
/// operation's spelling as in the member's. `relay` takes a box typed `O = P` and requires
/// nothing of `P`. The member's spelling was refused before; the spec operation's loaded.
#[test]
fn a_name_bound_to_a_parameter_nothing_is_held_for_is_refused() {
    for (ns, callee) in [("specreq.unheld.spec", "Desc"), ("specreq.unheld.member", "Coin")] {
        let errors = load_errors_of(&program(
            ns,
            KEEP.0,
            KEEP.1,
            &format!(
                "    operation relay[A, P](c: Coin, b: Box[E = A, O = P]) -> Int64 = {callee}.keep(c, b)\n"
            ),
        ));
        let joined = errors.join("\n");
        for token in [
            &format!("cannot be supplied for call to `{ns}.Coin.keep`"),
            "named slot `o`",
            "nothing in the enclosing scope holds a dictionary FOR `P`",
        ] {
            assert!(
                joined.contains(token),
                "`{callee}.keep(c, b)`: the refusal names `{token}`; got {errors:#?}"
            );
        }
    }
}

/// A CALL THAT SELECTS NOTHING IS DECIDED WHERE IT IS WRITTEN. Two providers of `Tagger[T
/// = String]` and none selected: the member's spelling was a load error naming both, and
/// the spec operation's loaded and tied where it ran. With one provider to choose from
/// both answer by it — the control, as before.
#[test]
fn a_call_that_selects_nothing_is_decided_where_it_is_written() {
    let ops = (
        "    operation pair[U](x: T, y: U) -> Int64 requires Tagger[T = U]\n",
        "    operation pair[U](x: Coin, y: U) -> Int64 requires Tagger[T = U] = add(10, Tagger.tag(y))\n",
    );
    for (ns, callee) in [("specreq.tie.spec", "Desc"), ("specreq.tie.member", "Coin")] {
        let errors = load_errors_of(&program(
            ns,
            ops.0,
            ops.1,
            &format!("    operation run() -> Int64 = {callee}.pair(coin(n: 5), \"s\")\n"),
        ));
        let joined = errors.join("\n");
        for token in [
            "ambiguous among providers",
            &format!("{ns}.Quiet"),
            &format!("{ns}.Loud"),
            &format!("cannot be supplied for call to `{ns}.Coin.pair`"),
        ] {
            assert!(
                joined.contains(token),
                "`{callee}.pair(coin(n: 5), \"s\")`: the refusal names `{token}`; got {errors:#?}"
            );
        }
    }
    let ns = "specreq.tie.one";
    let src = program(
        ns,
        ops.0,
        ops.1,
        "    operation spec() -> Int64 = Desc.pair(coin(n: 5), 7)
    operation member() -> Int64 = Coin.pair(coin(n: 5), 7)
",
    );
    assert_eq!(value(&src, ns, "spec"), 15, "one provider of `Tagger[T = Int64]`");
    assert_eq!(value(&src, ns, "member"), 15, "the member's own spelling");
}

/// THE CALL AS A RULE-BODY GOAL. A goal's requirement is owed where the rule is loaded,
/// so the member's entry left unpinned was a refusal there and not a search when the goal
/// ran: `?r <=> Desc.pair(Coin.coin(n: 5), 7)` was refused, "this is a RULE-body goal, and
/// nothing in the clause determines which `Tagger` instance it means … this call pins no
/// element" — of a call whose argument is the literal `7`. It answers by the one provider
/// of `Tagger[T = Int64]`, and by `String`'s own order where nothing is selected. A goal
/// with two providers to choose from is refused naming both, as the call is in an
/// operation's body.
#[test]
fn a_rule_body_goal_is_handed_to_the_member() {
    let ops = (
        "    operation pair[U](x: T, y: U) -> Int64 requires Tagger[T = U]
    operation cmp2[U](x: T, a: U, b: U) -> Int64 requires WeakOrd[T = U]
",
        "    operation pair[U](x: Coin, y: U) -> Int64 requires Tagger[T = U] = add(10, Tagger.tag(y))
    operation cmp2[U](x: Coin, a: U, b: U) -> Int64 requires WeakOrd[T = U] = WeakOrd.compare(a, b)
",
    );
    let ns = "specreq.rule";
    let mut kb = crate::common::load_kb_with(&program_with_rules(
        ns,
        ops.0,
        ops.1,
        "",
        "  fact held(Coin.coin(n: 5))
  rule one(?r) :- ?r <=> Desc.pair(Coin.coin(n: 5), 7)
  rule own(?r) :- ?r <=> Desc.cmp2(Coin.coin(n: 5), \"bob\", \"amyy\")
  rule later(?r) :- held(?c), ?r <=> Desc.pair(?c, 7)
",
    ));
    // `later` is the control: its receiver is bound when the goal runs, the member is
    // found from the value, and it answered 15 before.
    for (rule, expected) in [("one", 15), ("own", 1), ("later", 15)] {
        let answers = crate::common::query_unary(&mut kb, &format!("{ns}.{rule}"));
        let values: Vec<&Value> = answers.iter().map(|(v, _)| v).collect();
        assert!(
            matches!(values.as_slice(), [Value::Int(n)] if *n == expected),
            "`{rule}(?r)`: one answer, {expected}; got {values:?}"
        );
    }

    let ns = "specreq.rule.tie";
    let errors = load_errors_of(&program_with_rules(
        ns,
        ops.0,
        ops.1,
        "",
        "  rule tied(?r) :- ?r <=> Desc.pair(Coin.coin(n: 5), \"s\")\n",
    ));
    let joined = errors.join("\n");
    for token in ["ambiguous among providers", &format!("{ns}.Quiet"), &format!("{ns}.Loud")] {
        assert!(
            joined.contains(token),
            "a goal with two providers to choose from: the refusal names `{token}`; got {errors:#?}"
        );
    }
}

/// A GOAL WHOSE MEMBER IS FOUND WHEN IT RUNS IS LEFT TO THE BRIDGE, as it was. Neither the
/// receiver nor the argument has a type at load, so nothing there says which `Tagger` the
/// goal means; the bridge finds the member and the provider from the values, and the goal
/// answers (proposal 068 §3). An operation body's call in that position is stamped for
/// the spec operation; a goal stamped the same way is refused at load, "this is a
/// RULE-body goal, and nothing in the clause determines which `Tagger` instance it means",
/// which is the outcome this row holds off. One provider for each type, so that nothing
/// but the values decides.
#[test]
fn a_rule_body_goal_whose_member_is_found_later_is_left_to_the_bridge() {
    let ns = "specreq.bridge";
    let mut kb = crate::common::load_kb_with(&format!(
        "namespace {ns}
  import anthill.prelude.{{Int64, String}}
  import anthill.prelude.Numeric.{{add}}
  sort Tagger
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort Quiet
    provides Tagger[T = String]
    operation tag(x: String) -> Int64 = 2
  end
  sort Plain
    provides Tagger[T = Int64]
    operation tag(x: Int64) -> Int64 = 5
  end
  sort Desc
    sort T = ?
    operation pair[U](x: T, y: U) -> Int64 requires Tagger[T = U]
  end
  sort Coin
    entity coin(n: Int64)
    provides Desc[T = Coin]
    operation pair[U](x: Coin, y: U) -> Int64 requires Tagger[T = U] = add(10, Tagger.tag(y))
  end
  fact held(Coin.coin(n: 5))
  fact word(\"s\")
  rule answer(?r) :- held(?c), word(?w), ?r <=> Desc.pair(?c, ?w)
end
"
    ));
    let answers = crate::common::query_unary(&mut kb, &format!("{ns}.answer"));
    let values: Vec<&Value> = answers.iter().map(|(v, _)| v).collect();
    assert!(
        matches!(values.as_slice(), [Value::Int(12)]),
        "`answer(?r)`: one answer, 12; got {values:?}"
    );
}

/// A MEMBER THAT STATES NO REQUIREMENT IS HANDED NONE, and the call's selection for the
/// spec operation's is not an error there. Passes either way: such a member has no entry
/// of its own to fill.
#[test]
fn a_member_that_states_no_requirement_is_handed_none() {
    let ns = "specreq.none";
    let src = program(
        ns,
        SPEC_PAIR,
        "    operation pair[U](x: Coin, y: U) -> Int64 = 10\n",
        "    operation run() -> Int64 = Desc.pair[other = Loud](coin(n: 5), \"s\")\n",
    );
    assert_eq!(value(&src, ns, "run"), 10);
}

// ── A member chosen when the call runs ───────────────────────────────

/// `cmp2` and `pair` as the spec operation and the member state them, unnamed.
const RUN_TIME_OPS: (&str, &str) = (
    "    operation pair[U](x: T, y: U) -> Int64 requires Tagger[T = U]
    operation cmp2[U](x: T, a: U, b: U) -> Int64 requires WeakOrd[T = U]
",
    "    operation pair[U](x: Coin, y: U) -> Int64 requires Tagger[T = U] = add(10, Tagger.tag(y))
    operation cmp2[U](x: Coin, a: U, b: U) -> Int64 requires WeakOrd[T = U] = WeakOrd.compare(a, b)
",
);

/// THE RECEIVER IS A PARAMETER OF THE CALLER, under `requires Desc[T = X]`: which member
/// answers is known when the call runs. A provider selected at the call was dropped there
/// — `String`'s own order answered, 1 where the lengths give -1 — and two providers with
/// neither the type's own tied where the call ran. The call that selects nothing is the
/// control, and answers by `String`'s.
#[test]
fn a_member_chosen_when_the_call_runs_is_handed_the_selection() {
    let ns = "specreq.runtime.selected";
    let src = program(
        ns,
        RUN_TIME_OPS.0,
        RUN_TIME_OPS.1,
        "    operation byLength[X](x: X) -> Int64 requires Desc[T = X] = Desc.cmp2[WeakOrd = ByLength](x, \"bob\", \"amyy\")
    operation byOwn[X](x: X) -> Int64 requires Desc[T = X] = Desc.cmp2(x, \"bob\", \"amyy\")
    operation loudAt[X](x: X) -> Int64 requires Desc[T = X] = Desc.pair[Tagger = Loud](x, \"s\")
    operation quietAt[X](x: X) -> Int64 requires Desc[T = X] = Desc.pair[Tagger = Quiet](x, \"s\")
    operation selected() -> Int64 = byLength(coin(n: 5))
    operation unselected() -> Int64 = byOwn(coin(n: 5))
    operation loud() -> Int64 = loudAt(coin(n: 5))
    operation quiet() -> Int64 = quietAt(coin(n: 5))
",
    );
    assert_eq!(value(&src, ns, "selected"), -1, "`Desc.cmp2[WeakOrd = ByLength](x, …)`");
    assert_eq!(value(&src, ns, "unselected"), 1, "nothing selected: `String`'s own order");
    assert_eq!(value(&src, ns, "loud"), 13, "`Desc.pair[Tagger = Loud](x, …)`");
    assert_eq!(value(&src, ns, "quiet"), 12, "`Desc.pair[Tagger = Quiet](x, …)`");
}

/// THE OTHER WAYS A MEMBER IS CHOSEN LATER, each its own way out of the dispatch: the
/// requirement that covers the receiver held on the caller's SORT; the receiver typed as
/// the spec itself, so its value chooses; and the receiver typed as an abstract sort that
/// provides the spec.
#[test]
fn every_way_a_member_is_chosen_later_hands_the_selection() {
    // On the caller's sort.
    let ns = "specreq.runtime.onsort";
    let src = format!(
        "namespace {ns}\n{DECLS}
  sort Desc
    sort T = ?
    operation pair[U](x: T, y: U) -> Int64 requires Tagger[T = U]
  end
  sort Coin
    entity coin(n: Int64)
    provides Desc[T = Coin]
    operation pair[U](x: Coin, y: U) -> Int64 requires Tagger[T = U] = add(10, Tagger.tag(y))
  end
  sort Holder
    sort X = ?
    requires Desc[T = X]
    entity hold(x: X)
    operation loudOf(h: Self) -> Int64 = Desc.pair[Tagger = Loud](h.x, \"s\")
    operation quietOf(h: Self) -> Int64 = Desc.pair[Tagger = Quiet](h.x, \"s\")
  end
  sort Driver
    import {ns}.Coin.{{coin}}
    import {ns}.Holder.{{hold}}
    operation loud() -> Int64 = Holder.loudOf(hold(x: coin(n: 5)))
    operation quiet() -> Int64 = Holder.quietOf(hold(x: coin(n: 5)))
  end
end
"
    );
    assert_eq!(value(&src, ns, "loud"), 13, "held on the caller's sort, `[Tagger = Loud]`");
    assert_eq!(value(&src, ns, "quiet"), 12, "held on the caller's sort, `[Tagger = Quiet]`");

    // The receiver typed as the spec: `Circle` adds 10, `Square` 20.
    let ns = "specreq.runtime.selfspec";
    let src = format!(
        "namespace {ns}\n{DECLS}
  sort Shape
    operation tagged[U](s: Shape, y: U) -> Int64 requires Tagger[T = U]
  end
  sort Circle
    entity circle(r: Int64)
    provides Shape
    operation tagged[U](s: Circle, y: U) -> Int64 requires Tagger[T = U] = add(10, Tagger.tag(y))
  end
  sort Square
    entity square(a: Int64)
    provides Shape
    operation tagged[U](s: Square, y: U) -> Int64 requires Tagger[T = U] = add(20, Tagger.tag(y))
  end
  sort Driver
    import {ns}.Circle.{{circle}}
    import {ns}.Square.{{square}}
    operation loudOf(s: Shape) -> Int64 = Shape.tagged[Tagger = Loud](s, \"s\")
    operation quietOf(s: Shape) -> Int64 = Shape.tagged[Tagger = Quiet](s, \"s\")
    operation loud() -> Int64 = loudOf(circle(r: 1))
    operation quiet() -> Int64 = quietOf(square(a: 1))
  end
end
"
    );
    assert_eq!(value(&src, ns, "loud"), 13, "a `Shape` that is a circle, `[Tagger = Loud]`");
    assert_eq!(value(&src, ns, "quiet"), 22, "a `Shape` that is a square, `[Tagger = Quiet]`");

    // The receiver typed as an abstract sort that provides the spec, with its own body.
    let ns = "specreq.runtime.abstract";
    let src = format!(
        "namespace {ns}\n{DECLS}
  sort Desc
    sort T = ?
    operation pair[U](x: T, y: U) -> Int64 requires Tagger[T = U]
  end
  sort Shape
    operation area(s: Shape) -> Int64
    provides Desc[T = Shape]
    operation pair[U](x: Shape, y: U) -> Int64 requires Tagger[T = U] = add(50, Tagger.tag(y))
  end
  sort Circle
    entity circle(r: Int64)
    provides Shape
    operation area(s: Circle) -> Int64 = 3
  end
  sort Driver
    import {ns}.Circle.{{circle}}
    operation loudOf(s: Shape) -> Int64 = Desc.pair[Tagger = Loud](s, \"s\")
    operation quietOf(s: Shape) -> Int64 = Desc.pair[Tagger = Quiet](s, \"s\")
    operation loud() -> Int64 = loudOf(circle(r: 1))
    operation quiet() -> Int64 = quietOf(circle(r: 1))
  end
end
"
    );
    assert_eq!(value(&src, ns, "loud"), 53, "a `Shape` where `Desc[T = Shape]` is asked, `[Tagger = Loud]`");
    assert_eq!(value(&src, ns, "quiet"), 52, "a `Shape` where `Desc[T = Shape]` is asked, `[Tagger = Quiet]`");
}

/// …WHATEVER THE MEMBER CALLS THE REQUIREMENT: the spec operation calls it `other`, the
/// member `o`. A frame's slot is named by the sort it requires, so one requirement on a
/// sort is one slot name in both operations and this row passes with the slots handed
/// over by name; [`two_requirements_reach_a_member_chosen_when_the_call_runs`] is where
/// the names differ.
#[test]
fn a_member_chosen_when_the_call_runs_reads_it_under_its_own_name() {
    let ns = "specreq.runtime.names";
    let src = program(
        ns,
        SPEC_PAIR,
        "    operation pair[V](x: Coin, y: V) -> Int64 requires o: Tagger[T = V] = add(10, Tagger.tag(y))\n",
        "    operation loudAt[X](x: X) -> Int64 requires Desc[T = X] = Desc.pair[other = Loud](x, \"s\")
    operation quietAt[X](x: X) -> Int64 requires Desc[T = X] = Desc.pair[other = Quiet](x, \"s\")
    operation loud() -> Int64 = loudAt(coin(n: 5))
    operation quiet() -> Int64 = quietAt(coin(n: 5))
",
    );
    assert_eq!(value(&src, ns, "loud"), 13, "`[other = Loud]`, read as `o`");
    assert_eq!(value(&src, ns, "quiet"), 12, "`[other = Quiet]`, read as `o`");
}

/// TWO REQUIREMENTS ON ONE SORT, EACH TO ITS OWN SLOT OF THE MEMBER. A frame's slot is
/// named by the sort it requires, and where an operation states two on one sort, by the
/// requirement as that operation wrote it — so the member's two slots are not called what
/// the spec operation's are, and a slot handed over by its name reaches neither. The tens
/// are `y`'s provider, the units `z`'s.
#[test]
fn two_requirements_reach_a_member_chosen_when_the_call_runs() {
    let ns = "specreq.runtime.two";
    let src = program(
        ns,
        "    operation both[U, V](x: T, y: U, z: V) -> Int64 requires a: Tagger[T = U], b: Tagger[T = V]\n",
        "    operation both[U, V](x: Coin, y: U, z: V) -> Int64 requires p: Tagger[T = U], q: Tagger[T = V] \
         = add(mul(10, Tagger.tag(y)), Tagger.tag(z))\n",
        "    operation abAt[X](x: X) -> Int64 requires Desc[T = X] = Desc.both[a = Loud, b = Quiet](x, \"s\", \"t\")
    operation baAt[X](x: X) -> Int64 requires Desc[T = X] = Desc.both[a = Quiet, b = Loud](x, \"s\", \"t\")
    operation ab() -> Int64 = abAt(coin(n: 5))
    operation ba() -> Int64 = baAt(coin(n: 5))
",
    );
    assert_eq!(value(&src, ns, "ab"), 32, "`a = Loud, b = Quiet`");
    assert_eq!(value(&src, ns, "ba"), 23, "`a = Quiet, b = Loud`");
}

/// A REQUIREMENT THE CALLER HOLDS IS HANDED ON THERE TOO. `gen` requires `Tagger[T = A]`
/// beside `Desc[T = X]`, and its own caller selects the provider.
#[test]
fn the_callers_requirement_reaches_a_member_chosen_when_the_call_runs() {
    let ns = "specreq.runtime.forward";
    let src = program(
        ns,
        RUN_TIME_OPS.0,
        RUN_TIME_OPS.1,
        "    operation gen[X, A](x: X, a: A) -> Int64 requires Desc[T = X], Tagger[T = A] = Desc.pair(x, a)
    operation loud() -> Int64 = gen[Tagger = Loud](coin(n: 5), \"s\")
    operation quiet() -> Int64 = gen[Tagger = Quiet](coin(n: 5), \"s\")
",
    );
    assert_eq!(value(&src, ns, "loud"), 13, "`gen[Tagger = Loud]`");
    assert_eq!(value(&src, ns, "quiet"), 12, "`gen[Tagger = Quiet]`");
}

/// A SPEC'S DEFAULT BODY CALLS ITS SIBLING, and hands it the requirement it holds itself.
/// `twice` is `Desc`'s own body and doubles what `pair` answers; `Coin` states `pair` and
/// not `twice`, so the sibling's member is found from the receiver's value.
#[test]
fn a_spec_default_body_hands_its_requirement_to_the_sibling() {
    let ns = "specreq.runtime.sibling";
    let src = program(
        ns,
        "    operation pair[U](x: T, y: U) -> Int64 requires Tagger[T = U]
    operation twice[U](x: T, y: U) -> Int64 requires Tagger[T = U] = mul(2, Desc.pair(x, y))
",
        "    operation pair[U](x: Coin, y: U) -> Int64 requires Tagger[T = U] = add(10, Tagger.tag(y))\n",
        "    operation loud() -> Int64 = Desc.twice[Tagger = Loud](coin(n: 5), \"s\")
    operation quiet() -> Int64 = Desc.twice[Tagger = Quiet](coin(n: 5), \"s\")
",
    );
    assert_eq!(value(&src, ns, "loud"), 26, "`Desc.twice[Tagger = Loud]`");
    assert_eq!(value(&src, ns, "quiet"), 24, "`Desc.twice[Tagger = Quiet]`");
}

/// WHERE NO MEMBER ANSWERS, THE SPEC OPERATION'S OWN BODY READS IT; and a member that
/// states no requirement is handed none. `solo` has a body in `Desc` and `Coin` states
/// none of its own; `bare` is stated by `Coin` without the requirement. The second passes
/// either way.
#[test]
fn the_spec_operations_own_body_reads_what_the_call_filled() {
    let ns = "specreq.runtime.default";
    let src = program(
        ns,
        "    operation solo[U](x: T, y: U) -> Int64 requires Tagger[T = U] = add(100, Tagger.tag(y))
    operation bare[U](x: T, y: U) -> Int64 requires Tagger[T = U]
",
        "    operation bare[U](x: Coin, y: U) -> Int64 = 10\n",
        "    operation soloAt[X](x: X) -> Int64 requires Desc[T = X] = Desc.solo[Tagger = Loud](x, \"s\")
    operation bareAt[X](x: X) -> Int64 requires Desc[T = X] = Desc.bare[Tagger = Loud](x, \"s\")
    operation solo() -> Int64 = soloAt(coin(n: 5))
    operation bare() -> Int64 = bareAt(coin(n: 5))
",
    );
    assert_eq!(value(&src, ns, "solo"), 103, "`Desc.solo[Tagger = Loud](x, …)`, the spec's own body");
    assert_eq!(value(&src, ns, "bare"), 10, "a member that states no requirement");
}

/// THE CALL OWES THE SPEC OPERATION'S REQUIREMENT WHERE IT IS WRITTEN, the member being
/// unknown there. Two providers and none selected, and a type parameter of the caller it
/// requires nothing of: each loaded, and was decided from the value where the call ran —
/// a tie, or whatever provider the value's type had. With one provider to choose from
/// the call answers by it, as before.
#[test]
fn a_call_whose_member_is_chosen_later_owes_the_spec_operations_requirement() {
    let refused = |ns: &str, caller: &str, tokens: &[&str]| {
        let errors = load_errors_of(&program(ns, RUN_TIME_OPS.0, RUN_TIME_OPS.1, caller));
        let joined = errors.join("\n");
        for token in tokens {
            assert!(
                joined.contains(token),
                "`{}`: the refusal names `{token}`; got {errors:#?}",
                caller.trim()
            );
        }
    };
    let ns = "specreq.runtime.tie";
    refused(
        ns,
        "    operation gen[X](x: X) -> Int64 requires Desc[T = X] = Desc.pair(x, \"s\")\n",
        &[
            &format!("cannot be supplied for call to `{ns}.Desc.pair`"),
            "ambiguous among providers",
            &format!("{ns}.Quiet"),
            &format!("{ns}.Loud"),
        ],
    );
    let ns = "specreq.runtime.unheld";
    refused(
        ns,
        "    operation gen[X, A](x: X, a: A) -> Int64 requires Desc[T = X] = Desc.pair(x, a)\n",
        &[
            &format!("cannot be supplied for call to `{ns}.Desc.pair`"),
            "its carrier is `A`, a type parameter of the CALLING operation",
        ],
    );
    let ns = "specreq.runtime.one";
    let src = program(
        ns,
        RUN_TIME_OPS.0,
        RUN_TIME_OPS.1,
        "    operation gen[X](x: X) -> Int64 requires Desc[T = X] = Desc.pair(x, 7)
    operation run() -> Int64 = gen(coin(n: 5))
",
    );
    assert_eq!(value(&src, ns, "run"), 15, "one provider of `Tagger[T = Int64]`");
}

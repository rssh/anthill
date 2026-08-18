//! WI-20260818-7X7NK — a `.( )` projection that names no column of the relation it projects
//! reports THE PROJECTION, not a member lookup.
//!
//! THE DEFECT. §6.8 desugars `r.(nosuch)` to the marked tuple `(nosuch: r.nosuch)`, so the
//! projection is recognized at the TUPLE while `r.nosuch` is typed one level down as an
//! ordinary dot access. `nosuch` is neither a column nor a member, so dot dispatch fails
//! first and the build frame's `collect_arg_errors` surfaces its message — "expected
//! operation declared on the receiver's sort, got no such member (dot dispatch)". Every word
//! of that is true and none of it answers the question the author asked: they wrote a column
//! selection and were told their relation has no METHOD of that name, with no hint of what
//! columns it does have.
//!
//! WHAT THE TICKET ASKED FOR, RESTATED. It was filed out of WI-1128 against the 1-collapse
//! (`ages.(age)` on a one-column relation, which 1-collapsed at convert time and so never
//! built a projection at all). WI-20260818-YQB1Y dropped the collapse, that spelling now
//! WORKS, and the ticket's own re-check re-measured the route as unchanged for the case that
//! remained: a MISTYPED column name, at every receiver arity. So the collapse framing is gone
//! from the acceptance and only shape (b) — carry the `.( )` provenance to the failure site —
//! still described a fix.
//!
//! THE SHAPE THAT WAS CHOSEN, and why not shape (a). (a) was "at the dot-dispatch
//! no-such-member site, if the receiver is a `Relation` whose schema is not a named tuple,
//! say so" — it has NO POPULATION since YQB1Y, because a relation schema is always a named
//! tuple or `Unit`. (b) needed a new node-level flag when it was written down; it does not,
//! because WI-762 already marks the desugared tuple (`Expr::Constructor::from_projection`)
//! and the fields hang off it. So the fix reads the mark the parent already carries, at the
//! frame that short-circuits, and the marker the ticket costed was free.
//!
//! THE FALLTHROUGH IS NOT BROKEN, which was the ticket's own reason for not fixing this
//! inline: `r.isEmpty` and `r.(isEmpty)` are the same node shape as the failing projection.
//! Both still work, and both are DRIVEN below rather than asserted to load — a `.( )` naming
//! a non-column MEMBER is the §6.8 tuple `(isEmpty: Bool)` and stays one, because the
//! diagnostic fires only on a field that already FAILED.
//!
//! THREE DEFECTS THE ARMS COULD NOT SEE, all found by review, all with the same blind spot:
//! every arm that measures the diagnostic names a member that exists NOWHERE, so all of them
//! agreed with a reading that is only right for that case.
//!  * "THE FIELD FAILED" IS NOT "THE MEMBER DOES NOT EXIST". The first cut re-asked every
//!    failing field as a column lookup, so `r.(takeN)` — a member that IS reachable and merely
//!    wants its `n` argument — was told "no member `takeN` is reachable on it either", which
//!    is FALSE, and the arity error that said what to do was thrown away. The gate is the
//!    failure's VARIANT (`DotDispatchNoMatch`, for that field's own member).
//!  * ORDER DEPENDENCE. Answering only the FIRST failing field meant `r.(takeN, nosuch)` fell
//!    through entirely and reported `nosuch` through dot dispatch again — the ticket's own
//!    defect, one coordinate over, on a surface where field order is the author's arbitrary
//!    choice.
//!  * A DROPPED SIBLING. The rewrite returned ONE error in place of the aggregator over the
//!    whole list, so `r.(nosuch, takeN)` lost `takeN`'s arity error with nothing said.
//! The fix answers each field on its own and hands the COMPLETE list to `aggregate_errors`.
//! `..._a_real_member_failing_for_another_reason_keeps_its_own_error` and
//! `..._a_mixed_projection_answers_each_field_in_both_orders` are the witnesses; nothing else
//! here moves when either is backed out.
//!
//! CONTROLS — each names the back-out it answers to, because they do not share one.
//!  * `..._an_ordinary_member_call_on_a_relation_still_works`,
//!    `..._a_member_inside_a_projection_is_still_a_tuple` and
//!    `..._a_projection_that_does_name_columns_still_projects` pass with AND without the whole
//!    change, by design: they measure that the load-bearing fallthrough survived it.
//!  * `..._a_real_member_failing_for_another_reason_keeps_its_own_error` fails on the VARIANT
//!    gate alone, and `..._a_mixed_projection_answers_each_field_in_both_orders` on the
//!    per-field rewrite alone (restoring the first-failing-field selection drops it and
//!    nothing else).
//!  * `..._an_unmarked_constructor_arg_keeps_the_member_message` fails on the MARK gate alone.
//!  * `..._a_parameterized_non_relation_receiver_keeps_the_member_message` fails on the
//!    `Relation` SORT gate alone — and `..._a_non_relation_receiver_keeps_the_member_message`
//!    does NOT, which its own note explains.
//!  * `..._a_membership_receiver_says_it_has_no_columns_at_all` fails on the whole change AND
//!    on `projection_columns`' empty-schema branch.
//! The remaining error arms fail on the whole change: each asserts the new text AND
//! `!contains` dot dispatch's, so restoring the old route fails them on both halves.
//!
//! THE CONTROL SOURCE IS ITS OWN NAMESPACE, not a fixture shared with the error arms. Each
//! arm is a LOAD failure, and a load failure is whole-file: parking a control beside one
//! would kill the control too and prove nothing about it.

use crate::common::{interp_for, try_load_kb_with};
use anthill_core::eval::Value;

fn load_errs(src: &str) -> String {
    match try_load_kb_with(src) {
        Ok(_) => String::new(),
        Err(e) => e.join("\n"),
    }
}

/// The domain every arm shares, spliced ahead of a per-arm operation. A TWO-column relation
/// and a ONE-column one, so the arms can measure both receiver arities — the ticket's
/// re-check measured both and found one route.
const DOMAIN: &str = r#"
namespace test.x7nk
  import anthill.prelude.{String, Int64, Bool, List, Option}
  import anthill.prelude.Stream.{isEmpty}
  import anthill.prelude.PartialEq.{eq}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)

  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)   -- (name, age)
  rule adults(?who) :- person(name: ?who, age: 30)                 -- (who: String)
  rule anyone() :- person(name: ?n, age: ?a)                       -- Unit (membership)
"#;

fn src_with(op: &str) -> String {
    format!("{DOMAIN}\n{op}\nend\n")
}

/// The two halves every error arm asserts: the projection's own message arrived, and dot
/// dispatch's did NOT. The `!contains` is the half that fails on a back-out for the right
/// reason — without it an arm would pass on a message that merely happened to mention the
/// column name.
fn assert_names_the_projection(errs: &str, member: &str, columns: &str) {
    assert!(
        errs.contains(&format!("the projection selects column `{member}`")),
        "expected the projection's own message, got: {errs}"
    );
    assert!(
        errs.contains(&format!("its columns are: {columns}")),
        "expected the schema's column list `{columns}`, got: {errs}"
    );
    assert!(
        !errs.contains("no such member (dot dispatch)"),
        "dot dispatch's message still reaches the author: {errs}"
    );
}

/// ONE-COLUMN receiver — the arity the ticket was filed at. `adults.(nosuch)` names the
/// projection and lists the one column the relation has.
#[test]
fn x7nk_a_one_column_projection_names_the_projection() {
    let errs = load_errs(&src_with(
        r#"
  operation bad() -> List[(nosuch: String)] effects Error =
    let c = adults.(nosuch)
    c.takeN(9)
"#,
    ));
    assert_names_the_projection(&errs, "nosuch", "who");
}

/// MULTI-COLUMN receiver, and a projection whose OTHER member is fine. The good member types
/// as a column, so only the bad one is reported — and the column list is the receiver's, not
/// the projection's.
#[test]
fn x7nk_a_multi_column_projection_names_only_the_bad_member() {
    let errs = load_errs(&src_with(
        r#"
  operation bad() -> List[(name: String, nosuch: String)] effects Error =
    let r = person_row
    let c = r.(name, nosuch)
    c.takeN(9)
"#,
    ));
    assert_names_the_projection(&errs, "nosuch", "name, age");
}

/// A RENAME names the SOURCE column, never the result key. `r.(a: nosuch)` is wrong about
/// `nosuch`; `a` is a key the author is free to invent. This is what the member SYMBOL
/// (rather than the tuple label) is threaded out of `relation_column_access_parts` for — the
/// two are the same symbol in every other arm, so this is the only test that can tell them
/// apart.
#[test]
fn x7nk_a_rename_names_the_source_column_not_the_result_key() {
    let errs = load_errs(&src_with(
        r#"
  operation bad() -> List[(a: String)] effects Error =
    let r = person_row
    let c = r.(a: nosuch)
    c.takeN(9)
"#,
    ));
    assert_names_the_projection(&errs, "nosuch", "name, age");
    assert!(
        errs.contains("<dot projection>.nosuch"),
        "the error must be located at the source column, got: {errs}"
    );
    assert!(
        !errs.contains("<dot projection>.a"),
        "the result key is not what is wrong: {errs}"
    );
}

/// A MEMBERSHIP receiver — schema `Unit`, which since WI-20260818-YQB1Y means zero columns
/// and only zero columns, so EVERY member fails this way. It gets its own sentence in
/// `projection_columns` rather than the column list's empty rendering: "(its columns are: )"
/// reads as a rendering bug, not as the fact that there is nothing to select. TWO back-outs
/// fail this arm — dropping the diagnostic (like every error arm here) and dropping that
/// empty-schema branch (only this one).
#[test]
fn x7nk_a_membership_receiver_says_it_has_no_columns_at_all() {
    let errs = load_errs(&src_with(
        r#"
  operation bad() -> List[(nosuch: String)] effects Error =
    let r = anyone
    let c = r.(nosuch)
    c.takeN(9)
"#,
    ));
    assert!(
        errs.contains("the projection selects column `nosuch`"),
        "expected the projection's own message, got: {errs}"
    );
    assert!(
        errs.contains("it has NONE"),
        "expected the zero-column schema named as such, got: {errs}"
    );
    assert!(
        !errs.contains("its columns are: )"),
        "the empty column list must not render as an empty list: {errs}"
    );
    assert!(
        !errs.contains("no such member (dot dispatch)"),
        "dot dispatch's message still reaches the author: {errs}"
    );
}

/// A COMPUTED receiver — `person_row.where(…).(nosuch)`, no intervening `let`. The receiver's
/// type comes from the node's own stamp rather than the value env, which is a different rung
/// of `projection_receiver_type`; without it this arm would fall back to dot dispatch.
#[test]
fn x7nk_a_computed_receiver_reports_the_projection_too() {
    let errs = load_errs(&src_with(
        r#"
  operation bad() -> List[(nosuch: String)] effects Error =
    let c = person_row.where(lambda x -> eq(x.age, 30)).(nosuch)
    c.takeN(9)
"#,
    ));
    assert_names_the_projection(&errs, "nosuch", "name, age");
}

/// CONTROL — passes with and without the change. THE fallthrough the ticket refused to break:
/// an ordinary single-member dot call on a relation. DRIVEN, not loaded: `isEmpty` comes off
/// `Stream`, which `Relation` satisfies, and the call has to return an answer.
#[test]
fn x7nk_an_ordinary_member_call_on_a_relation_still_works() {
    let mut interp = interp_for(&src_with(
        r#"
  operation empty() -> Bool effects Error =
    let r = person_row
    r.isEmpty
"#,
    ));
    match interp.call("test.x7nk.empty", &[]) {
        Ok(Value::Bool(b)) => assert!(!b, "person_row has two rows, so it is not empty"),
        other => panic!("expected a Bool, got {other:?}"),
    }
}

/// CONTROL — passes with and without the change. §6.8 admits ANY member after `.(`, not only
/// a column, so `r.(isEmpty)` is the tuple `(isEmpty: Bool)` and must stay one. This is the
/// arm the diagnostic could most easily have swallowed: it is a marked projection over a
/// Relation naming something that is not a column. It does not fire because the field
/// SUCCEEDS, which is the gate — not because the member was recognized.
#[test]
fn x7nk_a_member_inside_a_projection_is_still_a_tuple() {
    let mut interp = interp_for(&src_with(
        r#"
  operation emptyCol() -> (isEmpty: Bool) effects Error =
    let r = person_row
    r.(isEmpty)
"#,
    ));
    match interp.call("test.x7nk.emptyCol", &[]) {
        Ok(v @ Value::Tuple { .. }) => match crate::common::sole_column(&v) {
            Value::Bool(b) => assert!(!b, "person_row has two rows, so it is not empty"),
            other => panic!("expected a Bool component, got {other:?}"),
        },
        other => panic!("expected a one-component named tuple, got {other:?}"),
    }
}

/// CONTROL — passes with and without the change. A projection that DOES name columns still
/// projects, at both arities, and yields a relation rather than a tuple of them.
#[test]
fn x7nk_a_projection_that_does_name_columns_still_projects() {
    let mut interp = interp_for(&src_with(
        r#"
  operation one() -> List[(who: String)] effects Error =
    let r = adults
    r.(who).takeN(9)

  operation two() -> List[(name: String, age: Int64)] effects Error =
    let r = person_row
    r.(name, age).takeN(9)
"#,
    ));
    let one = interp
        .call("test.x7nk.one", &[])
        .unwrap_or_else(|e| panic!("one: {e:?}"));
    assert_eq!(crate::common::list_column_strings(&one), vec!["alice"]);
    let two = interp
        .call("test.x7nk.two", &[])
        .unwrap_or_else(|e| panic!("two: {e:?}"));
    // The ROW SHAPE, not just the count: a two-column projection's rows are TWO-component
    // named tuples of a `String` and an `Int64`. A tuple OF two single-column relations —
    // the reading WI-762's mark exists to rule out — does not drain to this. The COLUMN
    // NAMES are pinned by the declared `List[(name: String, age: Int64)]` above, which is a
    // load-time check; the arity and the component types are what only a drain can show.
    let rows = crate::common::list_heads(&two);
    assert_eq!(rows.len(), 2, "expected both source rows, got {two:?}");
    for row in &rows {
        match row {
            Value::Tuple { pos, named } if pos.is_empty() && named.len() == 2 => {
                assert!(
                    matches!(&named[0].1, Value::Str(_)) && matches!(&named[1].1, Value::Int(_)),
                    "expected a (String, Int64) row, got {row:?}"
                );
            }
            other => panic!("expected a two-component named-tuple row, got {other:?}"),
        }
    }
}

/// A MIXED projection — one member that exists but is misused (`takeN`, missing its `n`) and
/// one that exists nowhere (`nosuch`) — in BOTH orders. Each field gets the message its own
/// failure earns, and NEITHER is dropped.
///
/// THE TWO DEFECTS THIS PINS, both of which the first cut shipped and no other arm here can
/// see, because every other arm's fields fail the same way as each other:
///  * ORDER DEPENDENCE. Picking the FIRST failing field meant `(takeN, nosuch)` fell through
///    entirely and reported `nosuch` through dot dispatch again — the ticket's own defect, one
///    coordinate over, on a surface where the order is the author's arbitrary choice.
///  * A DROPPED SIBLING. When the gate DID fire, its early return stood in for the aggregator
///    over the whole list, so `(nosuch, takeN)` lost `takeN`'s arity error — the actionable
///    one — with nothing said.
/// The two arms are each other's control: the assertions are identical and only the source
/// order differs, so a fix that is order-dependent in either direction fails one of them.
#[test]
fn x7nk_a_mixed_projection_answers_each_field_in_both_orders() {
    for members in ["takeN, nosuch", "nosuch, takeN"] {
        let errs = load_errs(&src_with(&format!(
            r#"
  operation bad() -> Bool effects Error =
    let r = person_row
    let c = r.({members})
    true
"#
        )));
        assert!(
            errs.contains("the projection selects column `nosuch`"),
            "`nosuch` must be re-asked as a projection in `r.({members})`, got: {errs}"
        );
        assert!(
            !errs.contains("no such member (dot dispatch)"),
            "dot dispatch's message still reaches the author in `r.({members})`: {errs}"
        );
        assert!(
            errs.contains("no argument fills parameter `n`"),
            "`takeN`'s own arity error must survive in `r.({members})`, got: {errs}"
        );
    }
}

/// CONTROL for the SECOND gate — the field's failure is `DotDispatchNoMatch`, and nothing
/// else. FOUND BY REVIEW, not by the arms above, and it was a WRONG ANSWER rather than a poor
/// one: `r.(takeN)` fails because `Stream.takeN` needs its `n` argument — the member IS
/// reachable — and reading "the field failed" as "the member does not exist" reported "no
/// member `takeN` is reachable on it either", which is FALSE, and threw away the arity error
/// that said what to do.
///
/// The same hijack covered every other way a real member's field can fail (a requirement
/// refusal, an effect mismatch) and — sharpest — `TypeErrorContext::DotProjection`'s OWN
/// first population, WI-759's "the member resolves but its type does not", which this
/// diagnostic shares that context with. This arm is the only one that measures the variant
/// gate: back it out and the arity message here is replaced by the column message, while
/// every other test in this file still passes.
#[test]
fn x7nk_a_real_member_failing_for_another_reason_keeps_its_own_error() {
    let errs = load_errs(&src_with(
        r#"
  operation bad() -> Bool effects Error =
    let r = person_row
    let c = r.(takeN)
    true
"#,
    ));
    assert!(
        errs.contains("no argument fills parameter `n`"),
        "expected takeN's own arity error, got: {errs}"
    );
    assert!(
        !errs.contains("the projection selects column"),
        "a member that EXISTS must not be reported as a missing column: {errs}"
    );
    assert!(
        !errs.contains("is reachable on it either"),
        "the diagnostic must not claim an existing member is unreachable: {errs}"
    );
}

/// CONTROL for the FIRST gate — the surface-form mark. A bad relation member in an ordinary
/// constructor argument is not a projection and keeps dot dispatch's message. This is the arm
/// that fails if the `Expr::Constructor { from_projection: true }` test is dropped: everything
/// else about `some(value: r.nosuch)` matches — a marked-looking constructor, a named field
/// that is a bare `DotApply` on a `Relation`, a member that names no column — and only the
/// mark separates it from a projection the author actually wrote.
#[test]
fn x7nk_an_unmarked_constructor_arg_keeps_the_member_message() {
    let errs = load_errs(&src_with(
        r#"
  operation bad() -> Option[T = String] effects Error =
    let r = person_row
    some(value: r.nosuch)
"#,
    ));
    assert!(
        errs.contains("no such member (dot dispatch)"),
        "expected dot dispatch's message for a non-projection argument, got: {errs}"
    );
    assert!(
        !errs.contains("the projection selects column"),
        "an ordinary constructor argument is not a projection: {errs}"
    );
}

/// CONTROL — passes with and without the change. A NON-relation receiver keeps dot dispatch's
/// message, and that is the right one: over an entity, `p.(nosuch)` IS a member lookup by
/// §6.8, and the message names the receiver's own sort.
///
/// This arm does NOT measure the second gate, and saying so is the point of the note: an
/// entity type is not parameterized, so with the `Relation` test removed the schema read
/// (`extract_type_param(.., "T")`) declines anyway and the message is unchanged. The arm
/// below is the one that trips on it.
#[test]
fn x7nk_a_non_relation_receiver_keeps_the_member_message() {
    let errs = load_errs(&src_with(
        r#"
  operation bad() -> Bool effects Error =
    let p = person(name: "a", age: 1)
    let q = p.(nosuch)
    true
"#,
    ));
    assert!(
        errs.contains("no such member (dot dispatch)"),
        "expected dot dispatch's message over a non-relation receiver, got: {errs}"
    );
    assert!(
        errs.contains("Person.nosuch"),
        "expected the receiver's own sort to be named, got: {errs}"
    );
}

/// CONTROL for the THIRD gate — the receiver's sort is `Relation`. A `List[T = String]`
/// receiver is PARAMETERIZED and has a `T`, so it clears every step of the schema read that
/// an entity receiver stops at; only the sort test separates it. With that test removed this
/// arm reports `String` "is not a relation schema" for a projection over a list, which names
/// a relation the author never wrote.
///
/// This is the gate the ticket weighed as a smell ("keying a DIAGNOSTIC on a receiver SORT").
/// It is the SAME gate `build_relation_projection` already uses to decide projection-vs-tuple
/// — not a new one — and `Relation` is one kernel sort, named by §6.8 and declared in
/// `stdlib/anthill/prelude/relation.anthill`, not an open stdlib operation set, which is the
/// population the "nothing keys on an operation's identity" discipline is about.
#[test]
fn x7nk_a_parameterized_non_relation_receiver_keeps_the_member_message() {
    let errs = load_errs(&src_with(
        r#"
  operation bad() -> Bool effects Error =
    let xs = ["a", "b"]
    let q = xs.(nosuch)
    true
"#,
    ));
    assert!(
        errs.contains("no such member (dot dispatch)"),
        "expected dot dispatch's message over a List receiver, got: {errs}"
    );
    assert!(
        !errs.contains("is not a relation schema"),
        "a projection over a list must not be reported against a relation schema: {errs}"
    );
}

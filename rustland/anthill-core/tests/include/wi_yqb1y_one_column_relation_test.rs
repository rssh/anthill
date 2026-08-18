//! WI-20260818-YQB1Y (proposal 052 OQ5, option A) — a ONE-COLUMN relation composes like any
//! other, because its schema names its column.
//!
//! THIS FILE REPLACES `wi1128_one_collapse_join_test`, which measured the REFUSALS the
//! 1-collapse forced. It is a replacement rather than a patch because WI-1128's own recorded
//! limits said so at their sites: "if that lands, this becomes a correct schema or a loud
//! error, THIS TEST FAILS, and the limit is RETIRED rather than patched".
//!
//! WHAT CHANGED, in one sentence: `collapse_schema` used to present a one-column schema as
//! the sole column's TYPE, discarding its `Symbol`, so the relation's ARITY was erased and
//! three distinct schemas became indistinguishable. `relation_schema_type` now returns the
//! full named tuple at every arity, and the VALUE (`materialize_solution`) and TERM (the
//! `.( )` desugar in parse/convert.rs) halves moved with it — which is what
//! kernel-language.md §6.8 required of any revision of that paired convention.
//!
//! THE FOUR REFUSALS THAT WERE THE OLD FILE'S SUBJECT ARE GONE, and each for its own reason:
//!  * `Concat` over a one-column operand — the merged schema can name the column now.
//!  * `Concat` over a MEMBERSHIP (`Unit`) operand — `Unit` means zero columns and ONLY zero
//!    columns, so merging one contributes no fields and the merged type matches the merged
//!    row exactly. (It used to be refused because `Unit` was also a one-`Unit`-column
//!    relation, so "nothing to merge" could drop a column the value still carried.)
//!  * `Without` over a one-column receiver — `fix` can drop the only column by name.
//!  * `Project` over a one-column receiver — and this one was not even reachable from the
//!    dot surface, because `r.(f)` 1-collapsed at convert time into the member access `r.f`
//!    (WI-20260818-7X7NK's "no such member").
//!
//! AND THE CASE THAT COULD NOT BE REFUSED IS NOW CORRECT. A schema that IS a named tuple
//! used to read equally as "n columns" and as "ONE column whose type is that n-field tuple",
//! which no type-level check could separate — so a join with a tuple-typed column
//! type-checked against a merged schema the row did not have. That was a SILENT WRONG
//! ANSWER, and `yqb1y_a_tuple_typed_column_is_one_column` is where it is measured.
//!
//! CONTROLS. Every test here fails on SOME back-out of this change and each names its own,
//! because they do not all answer to the same one: most fail on restoring the 1-collapse,
//! `yqb1y_merging_two_membership_relations_is_unit` fails on restoring `Concat`'s direct
//! `named_tuple_value` call, and the two arms of
//! `yqb1y_concat_and_without_are_inverses_at_arity_one` split between the collapse and the
//! one-pass reduction boundary. No arm passes under every back-out: this file measures only
//! what the change made possible.
//!
//! WHAT THIS DID **NOT** CLOSE, measured rather than assumed, because WI-20260818-7X7NK asked
//! to be re-checked here: a projection naming a column the schema does NOT have still reports
//! dot dispatch's "no such member" rather than `projection_columns`' own message. MEASURED on
//! this tree, at both receiver arities — `adults.(nosuch)` and `person_row.(nosuch)` each give
//! "expected operation declared on the receiver's sort, got no such member (dot dispatch)".
//! The route is unchanged: a projection field whose member does not resolve makes the
//! recognizer decline, and the call falls through to ordinary dot dispatch. That fallthrough
//! is load-bearing (`r.isEmpty` is the same node shape), so it stays 7X7NK's decision. No test
//! here pins it — it would pass with and without this change, which is what that file's own
//! rule forbids.

use crate::common::{interp_for, try_load_kb_with};
use anthill_core::eval::{Interpreter, Value};

fn load_errs(src: &str) -> String {
    match try_load_kb_with(src) {
        Ok(_) => String::new(),
        Err(e) => e.join("\n"),
    }
}

/// A two-column relation, a ONE-column one whose column is named `who`, and a ZERO-column
/// (membership) one. The column names are deliberately DISJOINT from `person_row`'s, because
/// `Concat` still enforces disjoint field names and a merged row keyed by name could not
/// mean anything else.
const SRC: &str = r#"
namespace test.yqb1y
  import anthill.prelude.{String, Int64, Bool, List}
  import anthill.prelude.Relation.{join, fix, where}
  import anthill.prelude.PartialEq.{eq}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)

  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)  -- (name, age)
  rule adults(?who) :- person(name: ?who, age: 30)                -- (who: String)
  rule anyone() :- person(name: ?n, age: ?a)                      -- Unit (membership)
"#;

/// JOIN WITH A ONE-COLUMN OPERAND — the ticket's headline, driven end-to-end.
///
/// Three things at once, and each was blocked by a different half of the old design:
///  * the merged SCHEMA names all three columns (`Concat` used to refuse the operand);
///  * the CONDITION reads the one-column row's column by name (`q.who` — the natural
///    spelling WI-1128 recorded as blocked by a SECOND, independent blocker, the whole-row
///    sentinel, which is deleted rather than keyed per binder because a row is a tuple now
///    and no column variable carries it);
///  * the VALUES are right: alice is an adult and joins with her own row, bob is not.
///
/// The declared return type IS the schema assertion — it type-checks only if `Concat` merged
/// exactly `(name, age)` with `(who)`.
///
/// BACK-OUT: FAILS at LOAD. On the pre-change tree `adults`'s schema is the bare `String`,
/// so `Concat` refuses operand `b` ("its schema is `String`, not a named-tuple type").
#[test]
fn yqb1y_join_with_a_one_column_operand_runs() {
    let src = format!(
        "{SRC}
  operation joined() -> List[(name: String, age: Int64, who: String)] effects Error =
    person_row.join(adults, lambda (c, q) -> eq(c.name, q.who)).takeN(5)
end
"
    );
    assert!(
        load_errs(&src).is_empty(),
        "a join with a one-column operand must LOAD; got:\n{}",
        load_errs(&src)
    );
    let mut interp = interp_for(&src);
    let rows = interp
        .call("test.yqb1y.joined", &[])
        .expect("the join runs");
    let got = rows_of(&interp, &rows);
    assert_eq!(
        got,
        vec![vec![
            "name=alice".to_string(),
            "age=30".to_string(),
            "who=alice".to_string(),
        ]],
        "only alice is an adult, so exactly her row survives the join — and the merged row \
         carries all three columns UNDER THEIR NAMES"
    );
}

/// JOIN WITH A MEMBERSHIP OPERAND IS A FILTER, and now types as one.
///
/// `Unit` contributes no columns, so the merged schema is the left operand's — which is
/// exactly what `join_run` builds from the two values (`cols1 ++ cols2`, and `cols2` is
/// empty). The declared two-column return type is the assertion; the condition then filters
/// to alice alone, so a join that silently dropped the condition would return bob too.
///
/// TWO IDENTICAL ROWS, and that is correct rather than a leak: `anyone` is PROVED once per
/// person (two facts), and a join is the bag product of the two queries conjoined with the
/// condition (052 OQ6). So the membership operand contributes MULTIPLICITY while
/// contributing no COLUMN — which is exactly the distinction this test is about.
///
/// BACK-OUT: FAILS at LOAD — `Concat` refused a `Unit` operand outright, because `Unit`
/// could not be told from a single `Unit`-typed column.
#[test]
fn yqb1y_join_with_a_membership_operand_is_a_filter() {
    let src = format!(
        "{SRC}
  operation filtered() -> List[(name: String, age: Int64)] effects Error =
    person_row.join(anyone, lambda (c, q) -> eq(c.age, 30)).takeN(5)
end
"
    );
    assert!(
        load_errs(&src).is_empty(),
        "joining a membership relation must LOAD, merging no columns; got:\n{}",
        load_errs(&src)
    );
    let mut interp = interp_for(&src);
    let rows = interp
        .call("test.yqb1y.filtered", &[])
        .expect("the membership join runs");
    let alice = vec!["name=alice".to_string(), "age=30".to_string()];
    assert_eq!(
        rows_of(&interp, &rows),
        vec![alice.clone(), alice],
        "a membership operand adds no COLUMN (two fields per row, not three) while still \
         contributing its two proofs as multiplicity, and the condition still filters bob out"
    );
}

/// `fix` DROPS THE ONLY COLUMN of a one-column relation, leaving the membership relation
/// whose non-emptiness is the answer.
///
/// Both polarities, because `isEmpty` over a relation that silently failed to restrict would
/// answer one of them by accident: alice IS an adult and zed is not.
///
/// BACK-OUT: FAILS at LOAD. `Without` refused a one-column receiver and its message sent the
/// author to APPLY the relation instead — advice that existed only because of the collapse.
#[test]
fn yqb1y_fix_drops_the_only_column() {
    let src = format!(
        "{SRC}
  operation aliceIsAdult() -> Bool effects Error = adults.fix(who: \"alice\").isEmpty
  operation zedIsAdult() -> Bool effects Error = adults.fix(who: \"zed\").isEmpty
end
"
    );
    assert!(
        load_errs(&src).is_empty(),
        "`fix` over a one-column relation must LOAD; got:\n{}",
        load_errs(&src)
    );
    let mut interp = interp_for(&src);
    match interp
        .call("test.yqb1y.aliceIsAdult", &[])
        .expect("aliceIsAdult runs")
    {
        Value::Bool(b) => assert!(!b, "alice is an adult, so the restricted relation is NON-empty"),
        other => panic!("expected Bool, got {other:?}"),
    }
    let mut interp = interp_for(&src);
    match interp
        .call("test.yqb1y.zedIsAdult", &[])
        .expect("zedIsAdult runs")
    {
        Value::Bool(b) => assert!(b, "zed is nobody, so the restricted relation is empty"),
        other => panic!("expected Bool, got {other:?}"),
    }
}

/// PROJECTING A ONE-COLUMN RELATION, on the DOT surface — the case that could not even reach
/// `Project`'s reducer before, because `r.(f)` 1-collapsed at convert time to the member
/// access `r.f` and dot dispatch reported "no such member" (WI-20260818-7X7NK).
///
/// The RENAME form is used deliberately: a single renamed member (`r.(years: who)`) used to
/// collapse AND drop the label, so rename only manifested at two or more columns. Here it
/// manifests at one, which is what makes the assertion about the result KEY and not merely
/// about the values.
///
/// BACK-OUT: FAILS at LOAD — `adults.(years: who)` desugars to `adults.who` on the pre-change
/// tree, and `adults`'s schema is the bare `String`, which has no `who` member.
#[test]
fn yqb1y_a_one_member_projection_keeps_its_key() {
    let src = format!(
        "{SRC}
  operation renamed() -> List[(years: String)] effects Error =
    let p = adults.(years: who)
    p.takeN(5)
end
"
    );
    assert!(
        load_errs(&src).is_empty(),
        "a one-member projection must LOAD as a one-column relation; got:\n{}",
        load_errs(&src)
    );
    let mut interp = interp_for(&src);
    let rows = interp
        .call("test.yqb1y.renamed", &[])
        .expect("the projection runs");
    assert_eq!(
        rows_of(&interp, &rows),
        vec![vec!["years=alice".to_string()]],
        "the projected row is keyed by the RESULT key `years`, not by the source column"
    );
}

/// THE SILENT WRONG ANSWER IS GONE — the case WI-1128 recorded as unrefusable and as this
/// ticket's strongest single argument.
///
/// `pairs` has ONE column `p` whose TYPE is the two-field tuple `(a: Int64, b: String)`.
/// Under the collapse its schema was that tuple, byte-for-byte identical to a TWO-column
/// schema over `a`/`b` — so a join type-checked against a four-column merged schema while
/// the row `join_run` materialized had three, with `a`/`b` promised and never delivered and
/// `p` delivered and never promised. No type check could exist: the two schemas were the
/// SAME TYPE.
///
/// Both directions are asserted, because the refusal alone would not show the case is now
/// USABLE and the acceptance alone would not show the lie is closed:
///  * the four-column declaration is a LOAD ERROR;
///  * the three-column one loads, runs, and the row's `p` column reads back as the tuple.
///
/// BACK-OUT: FAILS on BOTH arms, oppositely — the four-column declaration loads clean on the
/// pre-change tree (that is the recorded limit), and the three-column one does not load
/// there at all (`Concat` sees `pairs`'s schema as a named tuple and collides on `a`/`b`…
/// no: it merges them, and the declared `(name, age, p)` then disagrees).
#[test]
fn yqb1y_a_tuple_typed_column_is_one_column() {
    const HEAD: &str = r#"
namespace test.yqb1ynested
  import anthill.prelude.{String, Int64, Bool, List}
  import anthill.prelude.Relation.{join}
  import anthill.prelude.PartialEq.{eq}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)

  sort Holder
    entity pair_holder(p: (a: Int64, b: String))
  end
  fact pair_holder(p: (a: 1, b: "x"))
  rule pairs(?p) :- pair_holder(p: ?p)   -- ONE column `p`, typed (a: Int64, b: String)
"#;
    // The old lie: four columns claimed, three materialized. Now a load error.
    let wrong = load_errs(&format!(
        "{HEAD}
  operation joined() -> List[(name: String, age: Int64, a: Int64, b: String)] effects Error =
    person_row.join(pairs, lambda (c, q) -> eq(c.age, 30)).takeN(5)
end
"
    ));
    assert!(
        wrong.contains("(name: String, age: Int64, p: (a: Int64, b: String))"),
        "the merged schema must be the THREE-column one the row actually has, so the \
         four-column declaration is refused and the message shows it; got:\n{wrong}"
    );

    // And the honest declaration works, with the tuple-typed column readable by name.
    let right = format!(
        "{HEAD}
  operation joined() -> List[(name: String, age: Int64, p: (a: Int64, b: String))] effects Error =
    person_row.join(pairs, lambda (c, q) -> eq(c.age, 30)).takeN(5)
end
"
    );
    assert!(
        load_errs(&right).is_empty(),
        "the three-column declaration IS the merged schema; got:\n{}",
        load_errs(&right)
    );
    let mut interp = interp_for(&right);
    let rows = interp
        .call("test.yqb1ynested.joined", &[])
        .expect("the join runs");
    let Value::Entity { named, .. } = &rows else {
        panic!("expected a cons list, got {rows:?}")
    };
    let row = named
        .iter()
        .find_map(|(_, v)| matches!(v, Value::Tuple { .. }).then(|| v.clone()))
        .expect("the first row");
    let Value::Tuple { named: fields, .. } = &row else {
        unreachable!()
    };
    assert_eq!(
        fields.len(),
        3,
        "the row has the two left columns plus the sole right column `p` — and so does its \
         TYPE, which is the whole point"
    );
}

/// `Concat` AND `Without` ARE INVERSES AT ARITY ONE — the limit kernel-language.md §6.8
/// recorded as a known cost of the collapse ("the collapse drops the column *name*, so
/// `Concat[A = Without[T = (a: A, b: B), Drop = (b: B)], B = (c: C)]` stalls with `A` where a
/// named tuple is required, and nothing downstream can supply the lost `a`").
///
/// TWO THINGS HAD TO MOVE, and only one of them is the collapse:
///  * the RESIDUAL. `Without` now leaves `(a: Int64)`, a perfectly ordinary named tuple, so
///    there is no lost name for anything to supply.
///  * the REDUCTION BOUNDARY. It made ONE pass over `TYPE_CTORS`, and a ctor whose operand is
///    a SIBLING member defers on it — so with `Concat` ahead of `Without` the outer `Concat`
///    deferred, `Without` then reduced, and nothing revisited the outer one. That stall was
///    invisible while the residual was unusable anyway. The boundary is now a FIXPOINT.
///
/// BOTH NESTING DIRECTIONS ARE ASSERTED, and the second one is why the fix is a fixpoint and
/// not a reorder. They are DUALS — each wants the other member reduced first — so no array
/// order satisfies both, and the first attempt at this ticket reordered `TYPE_CTORS` to serve
/// the `Concat[Without[…]]` direction and MEASURABLY regressed `Without[Concat[…]]`, which had
/// loaded clean before. Found in review; the reorder was reverted and the fixpoint replaced
/// it. Asserting only the first direction is exactly what let that regression through.
///
/// `wi776_one_collapse_diagnostic_test::concat_over_a_collapsed_without_still_stalls` used to
/// pin the OPPOSITE of the first arm — deliberately, as a tripwire reading "someone re-reads
/// the decision". This is that re-reading, so the pin is inverted rather than deleted.
///
/// BACK-OUT, and the two arms answer to DIFFERENT back-outs, which is the point of having
/// both:
///  * restore the collapse → arm 1 fails (`Without` yields the bare `Int64`, which `Concat`
///    refuses); arm 2 still passes, since its inner `Concat` never reaches arity one.
///  * replace the fixpoint with the one-pass loop → exactly ONE arm fails, whichever one the
///    array order does not favour. With `TYPE_CTORS` as it stands (`Concat` first) that is
///    arm 1.
#[test]
fn yqb1y_concat_and_without_are_inverses_at_arity_one() {
    // Drop `b`, then merge `(c: Bool)` — the §6.8 shape, verbatim.
    let errs = load_errs(
        r#"
namespace test.yqb1yinv
  import anthill.prelude.{String, Int64, Bool, Concat, Without}
  operation resid() -> Concat[A = Without[T = (a: Int64, b: String), Drop = (b: String)], B = (c: Bool)]
  operation use_it() -> (a: Int64, c: Bool) = resid()
end
"#,
    );
    assert!(
        errs.is_empty(),
        "dropping `b` then merging `(c: Bool)` must reduce to `(a: Int64, c: Bool)`; got:\n{errs}"
    );

    // THE DUAL: merge first, then drop. This one loaded before this ticket and must keep
    // loading — it is the direction a `TYPE_CTORS` reorder would have broken.
    let errs = load_errs(
        r#"
namespace test.yqb1yinv2
  import anthill.prelude.{String, Int64, Concat, Without}
  operation resid() -> Without[T = Concat[A = (a: Int64), B = (b: String)], Drop = (b: String)]
  operation use_it() -> (a: Int64) = resid()
end
"#,
    );
    assert!(
        errs.is_empty(),
        "merging `(b: String)` then dropping it must reduce back to `(a: Int64)`; got:\n{errs}"
    );
}

/// MERGING TWO MEMBERSHIP RELATIONS IS `Unit`, NOT THE EMPTY TUPLE `()` — review-found, and it
/// is this ticket's own defect one arity further down.
///
/// `schema_fields` reads a `Unit` operand as the EMPTY field list, which is what lets a
/// membership operand merge as zero columns. So `merged` can legitimately come out empty, and
/// `concat_named_tuple_types` was the one schema producer in the family still calling
/// `named_tuple_value` directly instead of [`relation_schema_type`] — which builds `()` for an
/// empty field list, a type that is NOT `Unit` and NOT what `materialize_solution` produces for
/// a zero-column row (`Value::Unit`). That is precisely the type-disagrees-with-its-own-value
/// lie this ticket set out to remove.
///
/// BOTH readers are driven, because they fail differently: the drain's declared `List[Unit]`
/// caught the wrong TYPE, and `negate` caught the wrong ARITY — `Membership` read `()` as an
/// open schema and reported "free column(s): " with an empty list.
///
/// BACK-OUT: FAILS. With `named_tuple_value` restored, `both` reports
/// `expected List[T = Unit], got List[T = ()]` and `neg` reports the empty free-column list.
#[test]
fn yqb1y_merging_two_membership_relations_is_unit() {
    let errs = load_errs(
        r#"
namespace test.yqb1ymem
  import anthill.prelude.{String, Int64, Bool, List, Unit}
  import anthill.prelude.Relation.{join, negate}
  import anthill.prelude.PartialEq.{eq}
  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  rule anyone() :- person(name: ?n, age: ?a)

  -- the merged schema of two 0-column relations is `Unit`, so the drain is `List[Unit]`
  operation both() -> List[Unit] effects Error =
    anyone.join(anyone, lambda (c, q) -> eq(1, 1)).takeN(5)

  -- and `Membership` accepts it, which it cannot do for an empty NAMED TUPLE
  operation neg() -> Bool effects Error =
    negate(anyone.join(anyone, lambda (c, q) -> eq(1, 1))).isEmpty
end
"#,
    );
    assert!(
        errs.is_empty(),
        "a membership x membership join must type as `Relation[T = Unit]`, which is what its \
         row actually is; got:\n{errs}"
    );
}

/// Render a drained relation as one `Vec<String>` of `key=value` per row, in column order.
///
/// The KEYS are what most of this file asserts, so they are resolved through the KB rather
/// than printed as `Symbol(n)`: the whole change is that a column has a name in the type and
/// in the row, and an assertion that could not read the name would measure only the values.
/// LOUD on any other shape — a lenient walk would let a wrong column set read as a pass.
fn rows_of(interp: &Interpreter, v: &Value) -> Vec<Vec<String>> {
    crate::common::list_heads(v)
        .into_iter()
        .map(|row| match row {
            Value::Tuple { pos, named } if pos.is_empty() => named
                .iter()
                .map(|(k, val)| {
                    let key = interp.kb().local_name_of(*k).to_string();
                    match val {
                        Value::Str(s) => format!("{key}={s}"),
                        Value::Int(n) => format!("{key}={n}"),
                        other => panic!("unexpected column carrier {other:?}"),
                    }
                })
                .collect(),
            other => panic!("expected a named-tuple row, got {other:?}"),
        })
        .collect()
}



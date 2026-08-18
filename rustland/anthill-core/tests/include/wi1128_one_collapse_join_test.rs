//! WI-1128 (WI-714 / WI-731 follow-up) — `join` over a 1-COLLAPSED or MEMBERSHIP operand.
//!
//! THE TICKET WAS A QUESTION, AND THE ANSWER IS "REFUSE" — with two different reasons, which
//! is the part that needed deciding. It was filed on the hypothesis that a 1-collapsed
//! operand's column name is "likely RECOVERABLE at the boundary rather than reconstructed —
//! find the site that collapses it and read the pre-collapse name there". MEASURED, IT IS
//! NOT. `collapse_schema` (kb/typing.rs) IS that site: it returns the sole column's TYPE and
//! discards its `Symbol`. But it runs where a relation's OWN type is built, and that is not
//! on the path from a later `join` — by then an operand carries nothing but its type, and it
//! may be any expression (a `let`-bound value, a `where`, a projection), not the citation
//! whose column list the collapse saw. Reading the name off an argument OCCURRENCE that
//! happens to be a bare rule citation would make `r.join(ages, …)` and `let a = ages;
//! r.join(a, …)` behave differently — a fallback, not a fix.
//!
//! Recovering it means keeping the column in the SCHEMA while the value half still collapses
//! — kernel-language.md §6.8's paired type-and-value convention, recorded there as weighed
//! and declined, with the consequence for this family already spelled out ("nothing
//! downstream can supply the lost `a`"). 052 OQ5 now carries the redesign that would lift it.
//!
//! THE MEMBERSHIP (0-column) CASE IS DECIDED SEPARATELY, and is refused for a STRONGER
//! reason than a missing name: `Unit` is also what a relation with ONE `Unit`-typed column
//! collapses to (`wi728_a_unit_typed_column_is_indistinguishable_from_no_columns` pins that
//! limit, and is not duplicated here). So reading `Unit` as "no columns to merge" would
//! compute a merged schema with FEWER columns than the row `join_run` materializes from the
//! two values — a type disagreeing with its own value, which is the WI-737 lie rather than a
//! refusal. `negate` affords the same imprecision only because its runtime guard re-asks the
//! question against the value's own `columns`; a merged schema TYPE has no such backstop.
//!
//! AND THE ERASURE IS OF ARITY, NOT MERELY OF THE NAME — review-found on this change, and it
//! corrected the conclusion above rather than decorating it. A collapsed schema no longer
//! says how many columns it came from, so `Unit` reads as both 0 and 1 columns, AND a named
//! tuple reads as both n columns and ONE column whose type is that n-field tuple. The second
//! ambiguity CANNOT be refused — the collapsed reading is spelled exactly like the ordinary
//! working case — so `join` accepts it and computes a merged schema that disagrees with the
//! row it materializes. `fix` / `project` / `negate` meet the same ambiguity and catch it at
//! RUNTIME, because each asks the value "is there a column of this name?"; merging is
//! name-free, so `Concat` is the one member of the family with no backstop on either side.
//! Both halves are pinned below as a recorded limit.
//!
//! WHAT THIS FILE MEASURES, THEN: that the two REFUSALS are told apart, that each names its
//! own reason and its own route forward, that a shape which is no relation schema at all is
//! not blamed on a collapse it never underwent — and that the one case which cannot be
//! refused stays visible rather than latent.
//!
//! THE BACK-OUT, MEASURED (restore the single pre-WI-1128 string — "`concat` operand `a`
//! must be a named-tuple type (a relation with at least two named columns); a 1-collapse /
//! membership schema is not supported" — for all three shapes, and the matching one for
//! `Without`): **6 of the 11 tests below FAIL**. The five that pass either way each measure
//! a boundary this change did not move, and each says so at its site —
//! `project_over_a_one_collapsed_relation_is_still_refused`,
//! `where_over_a_one_collapsed_relation_still_runs`,
//! `the_route_the_fix_refusal_names_runs`,
//! `a_tuple_typed_column_is_indistinguishable_from_two_columns` and
//! `the_siblings_of_concat_catch_the_same_ambiguity_at_runtime`. Backed out by MUTATING the
//! messages, not by deleting the arms: deleting them would have failed to compile and
//! measured nothing.
//!
//! THE POSITIVE CONTROL IS `wi714_join_test` — a 2-column × 2-column join that RUNS and
//! selects the right rows. It lives in its own fixture on purpose: a control sharing a
//! namespace with these arms would die of the arms' own load errors and prove nothing.

use crate::common::{interp_for, try_load_kb_with};
use anthill_core::eval::Value;

fn load_errs(src: &str) -> String {
    match try_load_kb_with(src) {
        Ok(_) => String::new(),
        Err(e) => e.join("\n"),
    }
}

/// Two 2-column relations plus the two degenerate ones the refusals are about: `ages` has
/// ONE free column (its schema 1-collapses to `Int64`, the name `age` is gone from the type)
/// and `anyone` has ZERO (a membership relation, schema `Unit`).
const SRC: &str = r#"
namespace test.wi1128
  import anthill.prelude.{String, Int64, Bool, List}
  import anthill.prelude.Relation.{join, where}
  import anthill.prelude.PartialEq.{eq}

  sort Person
    entity person(name: String, age: Int64)
  end
  fact person(name: "alice", age: 30)
  fact person(name: "bob", age: 25)

  rule person_row(?name, ?age) :- person(name: ?name, age: ?age)   -- (name, age)
  rule ages(?age) :- person(age: ?age)                             -- Int64  (1-collapse)
  rule anyone() :- person(name: ?n, age: ?a)                       -- Unit   (membership)
"#;

/// A 1-COLLAPSED operand names the collapse, the type it collapsed to, and a route forward.
///
/// BACK-OUT: FAILS. The old message named neither the element type nor a route — it said
/// only "must be a named-tuple type … is not supported", which tells an author that
/// something is unsupported without telling them what they wrote or what to write instead.
#[test]
fn wi1128_a_one_collapsed_join_operand_names_the_collapse() {
    let errs = load_errs(&format!(
        "{SRC}
  operation p() -> Bool effects Error =
    person_row.join(ages, lambda (c, q) -> eq(c.age, 1)).isEmpty
end
"
    ));
    assert!(
        !errs.is_empty(),
        "a join with a 1-collapsed operand must stay a LOUD load error"
    );
    assert!(
        errs.contains("its schema is `Int64`")
            && errs.contains("ONE-COLUMN relation, the 1-collapse"),
        "the message must name the ELEMENT type it collapsed to and say the NAME was \
         dropped; got:\n{errs}"
    );
    assert!(
        errs.contains("rule body"),
        "the message must name the route that works (a rule body joins by shared logic \
         variables, needing no schema); got:\n{errs}"
    );
}

/// A MEMBERSHIP (0-column) operand is a DIFFERENT refusal — this is the arm that carries the
/// ticket's "decide it, do not let it fall out of the 1-column fix".
///
/// Asserted as a DIFFERENCE, not only as content: the two messages must not be the same
/// string, since the whole question was whether these are one case or two.
///
/// BACK-OUT: FAILS on both assertions — one string covered both shapes, so the messages were
/// byte-identical and neither said "MEMBERSHIP".
#[test]
fn wi1128_a_membership_join_operand_is_a_separate_refusal() {
    let collapsed = load_errs(&format!(
        "{SRC}
  operation p() -> Bool effects Error =
    person_row.join(ages, lambda (c, q) -> eq(c.age, 1)).isEmpty
end
"
    ));
    let membership = load_errs(&format!(
        "{SRC}
  operation p() -> Bool effects Error =
    person_row.join(anyone, lambda (c, q) -> eq(c.age, 1)).isEmpty
end
"
    ));
    assert!(
        !membership.is_empty(),
        "a join with a membership operand must stay a LOUD load error"
    );
    assert!(
        membership.contains("MEMBERSHIP") && membership.contains("`Unit`"),
        "the membership refusal must name the shape it refused; got:\n{membership}"
    );
    assert!(
        !membership.contains("ONE-COLUMN relation, the 1-collapse"),
        "a 0-column relation never had a name to drop — it must not be blamed on the \
         1-collapse; got:\n{membership}"
    );
    assert_ne!(
        collapsed, membership,
        "the 1-collapsed and membership operands are two questions and must not share one \
         message"
    );
}

/// The reason the membership case is refused rather than treated as an empty merge must be
/// IN the message: `Unit` cannot tell a 0-column relation from a 1-column `Unit`-typed one,
/// so "nothing to merge" could drop a real column that the joined relation still
/// materializes.
///
/// BACK-OUT: FAILS (no such sentence existed).
#[test]
fn wi1128_the_membership_refusal_states_the_unit_ambiguity() {
    let errs = load_errs(&format!(
        "{SRC}
  operation p() -> Bool effects Error =
    person_row.join(anyone, lambda (c, q) -> eq(c.age, 1)).isEmpty
end
"
    ));
    assert!(
        errs.contains("`Unit`-typed column") && errs.contains("still materializes"),
        "the refusal must say WHY `Unit` is not read as `no columns` — the type cannot \
         separate it from a single `Unit`-typed column, and the value would keep that \
         column; got:\n{errs}"
    );
}

/// Both operand positions get the same treatment, from ONE reader
/// (`concat_operand_fields`), so `a` and `b` cannot drift apart.
///
/// BACK-OUT: FAILS, on the wording half only — MEASURED against a faithful back-out that
/// keeps the old per-operand letters, where both `operand \`a\`` / `operand \`b\`` assertions
/// still hold and both collapse-wording assertions do not. Kept for the letters anyway,
/// because the two positions were separate `match` arms before this change and are one
/// function after it — a drift this would catch.
#[test]
fn wi1128_either_operand_position_is_named() {
    let right = load_errs(&format!(
        "{SRC}
  operation p() -> Bool effects Error =
    person_row.join(ages, lambda (c, q) -> eq(c.age, 1)).isEmpty
end
"
    ));
    let left = load_errs(&format!(
        "{SRC}
  operation p() -> Bool effects Error =
    ages.join(person_row, lambda (c, q) -> eq(q.age, 1)).isEmpty
end
"
    ));
    assert!(
        right.contains("operand `b`") && right.contains("ONE-COLUMN relation, the 1-collapse"),
        "a collapsed RIGHT operand is `b`; got:\n{right}"
    );
    assert!(
        left.contains("operand `a`") && left.contains("ONE-COLUMN relation, the 1-collapse"),
        "a collapsed LEFT operand is `a`; got:\n{left}"
    );
}

/// A shape that is NO relation schema at all — an arrow in a written `Concat` — gets a shape
/// claim, not the collapse story. The rule `membership_schema_type` states for its own
/// catch-all ("a shape this cannot name gets a shape claim, not an invented column"), now
/// held by `Concat` too.
///
/// Written rather than surfaced through `join`, because `join`'s operands come from relation
/// arguments and cannot be an arrow: this is the WRITTEN-type population, the same one
/// `wi734_denoted_operand_is_still_loud` exercises.
///
/// BACK-OUT: FAILS — the old message blamed "a 1-collapse / membership schema" for an
/// operand that is neither.
#[test]
fn wi1128_a_non_schema_operand_is_not_blamed_on_the_collapse() {
    let errs = load_errs(
        r#"
namespace test.wi1128arrow
  import anthill.prelude.{Int64, Bool, Concat}
  operation q() -> Concat[A = (x: Int64) -> Bool, B = (c: Bool)]
  operation use_it() -> (c: Bool) = q()
end
"#,
    );
    assert!(
        errs.contains("no relation schema at all"),
        "an arrow operand must be told what it IS, not blamed on a collapse; got:\n{errs}"
    );
    assert!(
        !errs.contains("ONE-COLUMN relation, the 1-collapse") && !errs.contains("MEMBERSHIP"),
        "neither degenerate-arity story applies to an arrow; got:\n{errs}"
    );
}

/// THE CENSUS, second reader: `fix`'s `Without` refuses a 1-collapsed receiver for the same
/// missing name — so a recovered name would have fixed BOTH, and the ticket's "a fix measured
/// on Concat alone would leave the others refusing" is why this arm is here. Its route
/// forward differs from `join`'s, which is why the message is phrased per operation rather
/// than shared: to restrict a one-column relation you APPLY it, you do not `fix` its only
/// column away.
///
/// BACK-OUT: FAILS (the old `Without` message named neither the element type nor the route).
#[test]
fn wi1128_fix_over_a_one_collapsed_relation_names_the_route() {
    let errs = load_errs(&format!(
        "{SRC}
  operation p() -> Bool effects Error =
    ages.fix(age: 1).isEmpty
end
"
    ));
    assert!(
        errs.contains("its schema is `Int64`") && errs.contains("APPLY the relation"),
        "`fix` over a 1-collapsed relation must name the collapse and the route that works; \
         got:\n{errs}"
    );
}

/// THE ROUTE THE `fix` REFUSAL NAMES MUST ACTUALLY WORK — a message that sends an author
/// somewhere is a claim, and this drives it. `ages` has one column, so `ages.fix(age: …)` is
/// refused by the test above; APPLYING it binds that column instead, giving the membership
/// relation whose non-emptiness IS the answer.
///
/// Both polarities, because `isEmpty` on a relation that silently failed to bind anything
/// would answer one of them by accident: 30 IS a stored age (non-empty) and 99 is not
/// (empty). A single-polarity assertion would pass on a route that always returns the same
/// thing.
///
/// BACK-OUT: passes either way, by design — application is not what this change touched.
/// It is here because this change is what put the advice in a user-facing message, and
/// unmeasured advice is the thing that goes stale silently.
#[test]
fn wi1128_the_route_the_fix_refusal_names_runs() {
    let src = format!(
        "{SRC}
  operation stored() -> Bool effects Error = ages(30).isEmpty
  operation absent() -> Bool effects Error = ages(99).isEmpty
end
"
    );
    let mut interp = interp_for(&src);
    match interp.call("test.wi1128.stored", &[]).expect("ages(30) runs") {
        Value::Bool(b) => assert!(!b, "30 is a stored age, so the applied relation is NON-empty"),
        other => panic!("expected Bool, got {other:?}"),
    }
    let mut interp = interp_for(&src);
    match interp.call("test.wi1128.absent", &[]).expect("ages(99) runs") {
        Value::Bool(b) => assert!(b, "99 is not a stored age, so the applied relation is empty"),
        other => panic!("expected Bool, got {other:?}"),
    }
}

/// THE CASE THAT IS NOT REFUSED, AND CANNOT BE — a RECORDED LIMIT, pinned so it stays
/// visible rather than latent. Review-found on this change, and it corrected the ticket's
/// own conclusion: the collapse erases ARITY, not merely the name, so a schema that IS a
/// named tuple reads equally as "n columns" and as "ONE column whose type is that n-field
/// tuple". The second is spelled exactly like the ordinary working case, so no type-level
/// check separates them — refusing it would refuse every ordinary join.
///
/// What that costs, driven here: `pairs` has ONE column `p` typed `(a: Int64, b: String)`,
/// so joining it with a 2-column relation type-checks against a FOUR-column merged schema
/// while the row actually materialized has THREE columns — `(name, age, p)` — with `a`/`b`
/// promised by the type and never delivered, and `p` delivered and never promised. This is
/// the type-disagrees-with-its-own-value lie the membership arm above is refused to avoid,
/// arriving through the one door that cannot be closed.
///
/// `Concat` is the only member of the family with no runtime backstop; the sibling arm
/// below drives the contrast. OWNED BY WI-20260818-YQB1Y: if that lands, this becomes
/// a correct schema or a loud error, THIS TEST FAILS, and the limit is RETIRED rather than
/// patched — the wi728 discipline for exactly this shape of recorded limit.
///
/// BACK-OUT: passes either way, by design — this measures a pre-existing boundary the
/// change did not move. It is here because this change is what documented the boundary.
#[test]
fn wi1128_a_tuple_typed_column_is_indistinguishable_from_two_columns() {
    let src = r#"
namespace test.wi1128nested
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

  -- The declared merged schema claims FOUR columns. It type-checks, and it is wrong.
  operation joined() -> List[(name: String, age: Int64, a: Int64, b: String)] effects Error =
    person_row.join(pairs, lambda (c, q) -> eq(c.age, 30)).takeN(5)
end
"#;
    assert!(
        load_errs(src).is_empty(),
        "the recorded limit is that this LOADS — if it now refuses, retire the limit \
         (kernel-language.md §6.8, 052 OQ5) rather than patching this test"
    );
    let mut interp = interp_for(src);
    let rows = interp
        .call("test.wi1128nested.joined", &[])
        .expect("the join runs — the RUNTIME merge is correct; only the type is not");
    // Walk to the first row and read its field labels: three, not the four declared.
    let mut labels: Vec<String> = Vec::new();
    if let Value::Entity { named, .. } = &rows {
        for (_k, v) in named.iter() {
            if let Value::Tuple { named: fields, .. } = v {
                labels = fields.iter().map(|(k, _)| format!("{k:?}")).collect();
            }
        }
    }
    assert_eq!(
        labels.len(),
        3,
        "the materialized row has the two left columns plus the sole right column `p` — \
         THREE — while the declared schema promised four; that gap is the limit"
    );
}

/// THE CONTRAST that makes the arm above a statement about `Concat` specifically rather
/// than about the collapse in general: `fix` meets the SAME type-level ambiguity and is
/// caught LOUDLY at runtime, because it asks the value a question the value can answer —
/// "is there a column of this name?". Merging is name-free, so `Concat` has no such
/// question and nothing to detect.
///
/// Driven through `fix` alone; `project`'s guard is the same shape ("project_run: the
/// projection selects column `a`, which is not in the relation's schema", measured) and is
/// not duplicated here.
///
/// BACK-OUT: passes either way, by design — the runtime guards are pre-existing. Its value
/// is that it pins the ASYMMETRY the census turns on: if `fix` ever loses its guard, the
/// claim "`Concat` is the only member without a backstop" stops being true and this fails.
#[test]
fn wi1128_the_siblings_of_concat_catch_the_same_ambiguity_at_runtime() {
    let src = r#"
namespace test.wi1128nested2
  import anthill.prelude.{String, Int64, Bool}
  import anthill.prelude.Relation.{fix}
  sort Holder
    entity pair_holder(p: (a: Int64, b: String))
  end
  fact pair_holder(p: (a: 1, b: "x"))
  rule pairs(?p) :- pair_holder(p: ?p)
  -- `a` is an INNER field of the sole column `p`, not a column. The typer is fooled.
  operation fixed() -> Bool effects Error = pairs.fix(a: 1).isEmpty
end
"#;
    assert!(
        load_errs(src).is_empty(),
        "the type-level check is fooled here too — that is the shared half"
    );
    let mut interp = interp_for(src);
    let err = interp
        .call("test.wi1128nested2.fixed", &[])
        .expect_err("`fix` has a RUNTIME guard reading the value's own columns");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("which is not in the relation's schema"),
        "the guard must name the column the schema does not have; got: {msg}"
    );
}

/// THE CENSUS, third reader: `project`. A 1-collapsed receiver is REFUSED — the program does
/// not silently load — but the message is dot dispatch's, not `Project`'s: `r.(f)`
/// 1-collapses at convert time to `r.f` (§6.8), so `ages.(age)` is a member call on a
/// `Relation` and the projection recognizer is never reached. `projection_columns`' own
/// message is therefore visible only to a WRITTEN `Project[T, Keep]`.
///
/// Only the REFUSAL is asserted, not the wording: pinning today's fallthrough text would
/// break whoever improves it, and the census row is "refused, with a message that names the
/// wrong thing", which the doc comment records.
///
/// BACK-OUT: passes either way, by design — this arm documents a boundary this change did
/// not move.
#[test]
fn wi1128_project_over_a_one_collapsed_relation_is_still_refused() {
    let errs = load_errs(&format!(
        "{SRC}
  operation p() -> Bool effects Error =
    ages.(age).isEmpty
end
"
    ));
    assert!(
        !errs.is_empty(),
        "a projection of a 1-collapsed relation must not load silently"
    );
}

/// THE CENSUS ROW THAT IS NOT A REFUSAL, and it drives values rather than a load: `where` is
/// the one composition operation that does NOT pay for the collapse, because a 1-collapsed
/// row is reached with a BARE binder (`eq(c, 1)`, the `WHOLE_ROW_HOLE`) and a bare binder
/// needs no column name. So the census answer is not "the collapse breaks composition" but
/// "it breaks the schema-COMPUTING operations".
///
/// Driven, not merely loaded: the filter keeps only `age = 30`, so a `where` that compiled
/// to nothing would return the other row too. `isEmpty` alone would pass on a broken filter.
///
/// BACK-OUT: passes either way, by design — this measures a capability the change did not
/// touch, and its value is that it FAILS if a later attempt to fix the collapse breaks the
/// one path that works today.
#[test]
fn wi1128_where_over_a_one_collapsed_relation_still_runs() {
    let mut interp = interp_for(&format!(
        "{SRC}
  operation kept() -> List[Int64] effects Error =
    ages.where(lambda c -> eq(c, 30)).takeN(5)
end
"
    ));
    let r = interp
        .call("test.wi1128.kept", &[])
        .expect("`where` over a 1-collapsed relation runs");
    // Walk the cons list; each element is the 1-collapsed row VALUE — a bare `Int64`, not a
    // 1-field tuple (the value half of the collapse, §6.8).
    let mut ages: Vec<i64> = Vec::new();
    let mut cur = r;
    while let Value::Entity { named, .. } = &cur {
        if named.is_empty() {
            break;
        }
        let mut head: Option<i64> = None;
        let mut tail: Option<Value> = None;
        for (_k, v) in named.iter() {
            match v {
                Value::Int(n) => head = Some(*n),
                Value::Entity { .. } => tail = Some(v.clone()),
                other => panic!("unexpected row carrier {other:?}"),
            }
        }
        match (head, tail) {
            (Some(n), Some(t)) => {
                ages.push(n);
                cur = t;
            }
            _ => break,
        }
    }
    assert_eq!(
        ages,
        vec![30],
        "the condition must actually filter: alice(30) is kept and bob(25) is dropped"
    );
}

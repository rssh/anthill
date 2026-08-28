//! WI-731 — `rename`: RE-KEY a relation's columns IN PLACE, so two relations that share a
//! column name can `join`.
//!
//! THE PROBLEM. A schema's column names are distinct (§4.5), so `Concat` refuses two operands
//! that share one and `join` refuses the pair. Column names are chosen by whoever wrote the
//! RULE (`rule_head_var_slots` takes a positional head arg's own variable name), so a
//! collision is two independently-authored rules both picking `?name` — and a SELF-JOIN
//! collides on every column by construction. The decided fix is EXPLICIT renaming, not
//! automatic qualification: qualifying only on collision would make a rule author ADDING a
//! column silently rename columns in someone else's downstream join result, so the result
//! schema would stop being a function of the two relations.
//!
//! `project` already renames (`r.(person: name)`) but SELECTS too, so renaming one column of
//! a six-column relation means listing all six. That gap is what `rename` closes; it is not
//! sugar for `project`.
//!
//! THE MECHANISM, AND THE PREMISE THAT CHANGED UNDER IT. This ticket recorded itself as
//! blocked on the rule-head macro face (WI-1129) for a stated reason: a variadic capture
//! builds its record's type from each argument's TYPE, and §4.5 has no singleton types, so a
//! captured NAME arrives as `String` and cannot reach the type level. That is true of a name
//! written as a string. It is not true of the surface actually decided, `r.rename(who:
//! r.name)`, whose operand is the one-column relation `r.name` — and since WI-20260818-YQB1Y
//! a one-column relation's schema NAMES its column, so the source rides in
//! `Relation[T = (name: String)]`. MEASURED at the reduction boundary before anything was
//! built: `Map = (who: Relation[T = (name: String), E = …])`. Under the collapse it would have
//! been `Relation[T = String]` — the name genuinely gone, exactly as the ticket said.
//!
//! So `rename` is an ORDINARY operation with a variadic capture — `fix`'s shape (proposal
//! 056 §2.1) — with NO compile-time macro, no `[simp]` rule, no rule-head rest pattern, and
//! nothing keyed on `rename`'s identity in the typer. `Rename[T, Map]` is a general type
//! constructor beside `Concat` / `Without` / `Project`, reducing at the same boundary.
//!
//! BACK-OUT MEASUREMENTS, each mutating a site rather than deleting it, so the fixture still
//! LOADS and these measure capability rather than loadability. No two arms answer to the same
//! one:
//!  * the type-level RE-KEYING (`rename_schema_type` keeps every column's original key):
//!    7 fail, 5 pass. The five are the refusals that fire BEFORE the re-key, correctly.
//!  * the runtime IDENTITY check (match a source by NAME instead of by column VARIABLE):
//!    1 fails — `..._a_foreign_source_column_is_refused` — and under that back-out the
//!    program RUNS, silently renaming the receiver's own same-named column. A wrong answer,
//!    which is why that arm exists.
//!  * the source-column TYPE check: 1 fails — `..._a_source_of_the_wrong_type_is_refused`.
//!  * the NAME half of the runtime match (match by `VarId` alone, the shipped first cut):
//!    1 fails — `..._a_receiver_sharing_one_variable_renames_only_the_named_column`.
//!  * the error CLASSIFICATION (raise the foreign-source refusal as `EvalError::Internal`):
//!    1 fails — `..._a_foreign_source_column_is_refused`, on its second assertion.
//!  * `schema_columns_tail`'s zero-column sentence: 2 fail, one on EACH side of the shared
//!    owner — this file's `..._a_membership_receiver_...` and
//!    `wi_7x7nk_..._x7nk_a_membership_receiver_...`. That pair is why the wording has one
//!    owner: the projection site had the sentence and the rename site, added in the same
//!    change, was left printing an empty list.
//!
//! THREE OF THOSE SIX WERE FOUND BY REVIEW, NOT BY THESE ARMS, and the first is the one worth
//! naming: matching a source by its column VARIABLE alone looked exact — more exact than a
//! name — but a relation may carry ONE variable in TWO columns, so `p.rename(z: p.a)` over
//! `p = r.(a: id, b: id)` re-keyed both and returned a row with two `z` columns and no `b`.
//! It loaded clean and ran. Every arm here used a receiver whose columns had distinct
//! variables, so none of them could see it.
//!
//! THE ONE THING THE TYPE CANNOT SEE is WHICH relation a source came from, since
//! `Relation[T = (name: String)]` states no provenance. `r.rename(who: other.name)` therefore
//! type-checks, and the RUNTIME refuses it — it matches a source by its column VARIABLE, which
//! `r.name` inherits from `r`. That is a real limit of the type-directed route and it is
//! measured, not assumed: `rename_a_foreign_source_column_is_refused`.

use crate::common::{interp_for, try_load_kb_with};
use anthill_core::eval::Value;

fn load_errs(src: &str) -> String {
    match try_load_kb_with(src) {
        Ok(_) => String::new(),
        Err(e) => e.join("\n"),
    }
}

/// THREE columns, so a MIDDLE one can be renamed — the only arity that can tell "in place"
/// from "renamed first". Two `name`-carrying relations, so the join collision is real.
const SRC: &str = r#"
namespace test.wi731
  import anthill.prelude.{String, Int64, Bool, List}
  import anthill.prelude.Relation.{rename, join}
  import anthill.prelude.PartialEq.{eq}

  sort Person
    entity person(id: Int64, name: String, age: Int64)
    entity pet(owner: Int64, name: String)
  end
  fact person(id: 1, name: "alice", age: 30)
  fact person(id: 2, name: "bob", age: 25)
  fact pet(owner: 1, name: "cat")
  fact pet(owner: 2, name: "dog")

  rule person_row(?id, ?name, ?age) :- person(id: ?id, name: ?name, age: ?age)
  rule pet_row(?owner, ?name) :- pet(owner: ?owner, name: ?name)

  -- A relation whose `name` column is an Int64, so a foreign source can share person_row's
  -- column NAME while differing in TYPE — the half of the provenance hole a type CAN close.
  rule tag_row(?id, ?name) :- person(id: ?id, name: ?, age: ?name)

  -- A MEMBERSHIP relation: zero columns, so every rename source names nothing.
  rule anyone() :- person(id: ?, name: ?, age: ?)

  -- A MIDDLE column renamed. The declared return pins the TYPE's order; the test pins the
  -- materialized ROW's order, which is the half a type cannot state.
  operation middle() -> List[(id: Int64, who: String, age: Int64)] effects Error =
    let r = person_row
    r.rename(who: r.name).takeN(9)

  -- A SWAP is legal: the collision test is over the RESULT, and a swap leaves no duplicate.
  operation swap() -> List[(id: Int64, age: String, name: Int64)] effects Error =
    let r = person_row
    r.rename(age: r.name, name: r.age).takeN(9)

  -- THE DRIVING CLIENT: both operands have `name`, which `join` refuses. Rename one side.
  operation owners() -> List[(id: Int64, name: String, age: Int64, owner: Int64, petName: String)]
      effects Error =
    let p = person_row
    let q = pet_row
    let q2 = q.rename(petName: q.name)
    p.join(q2, lambda (c, d) -> eq(c.id, d.owner)).takeN(9)

  -- A SELF-JOIN, where every column collides by construction.
  operation selfjoin()
      -> List[(id: Int64, name: String, age: Int64, id2: Int64, name2: String, age2: Int64)]
      effects Error =
    let p = person_row
    let p2 = p.rename(id2: p.id, name2: p.name, age2: p.age)
    p.join(p2, lambda (c, d) -> eq(c.id, d.id2)).takeN(9)

  -- CONTROL: no rename anywhere. Every arm above must be shown to need one.
  operation plain() -> List[(id: Int64, name: String, age: Int64)] effects Error =
    person_row.takeN(9)

  -- A receiver carrying ONE column VARIABLE in TWO columns. `r.(a: id, b: id)` is a legal
  -- projection (a duplicate SOURCE is not refused; only a duplicate result key is), and it
  -- is what makes "the column variable" not a key.
  operation dupVar() -> List[(z: Int64, b: Int64)] effects Error =
    let r = person_row
    let p = r.(a: id, b: id)
    p.rename(z: p.a).takeN(9)

  -- CONTROL 2: the same `let` binding as `middle`, WITHOUT the rename — so a difference
  -- between this and `middle` is the rename's, and a difference between this and `plain`
  -- is the binding's.
  operation plainLet() -> List[(id: Int64, name: String, age: Int64)] effects Error =
    let r = person_row
    r.takeN(9)
end
"#;

/// One source line per refusal, spliced into the shared domain — each is a LOAD failure, and
/// a load failure is whole-file, so they cannot share a fixture with the driven arms.
fn refusal(op_body: &str) -> String {
    let domain = SRC.split("  -- A MIDDLE column").next().expect("domain");
    format!(
        "{domain}\n  operation bad() -> Bool effects Error =\n    let r = person_row\n    \
         let q = {op_body}\n    true\nend\n"
    )
}

fn rows(v: &Value) -> Vec<Vec<(String, Value)>> {
    crate::common::list_heads(v)
        .iter()
        .map(|row| match row {
            Value::Tuple { pos, named } if pos.is_empty() => {
                named.iter().map(|(_, v)| v.clone()).enumerate().fold(
                    Vec::new(),
                    |mut acc, (i, v)| {
                        acc.push((i.to_string(), v));
                        acc
                    },
                )
            }
            other => panic!("expected a named-tuple row, got {other:?}"),
        })
        .collect()
}

/// THE ORDER OF THE MATERIALIZED ROW, over three columns with the MIDDLE one renamed. A
/// two-column fixture cannot distinguish "in place" from "renamed first"; this one can.
///
/// This is deliberately NOT a test that a reordered schema fails to type-check — it would
/// not. §4.5 makes permutation a subtyping rule, so a permuted named tuple is the SAME type,
/// and the ticket's original justification for in-place renaming ("a reordering rename would
/// silently change the schema type of every downstream consumer") was measured false and
/// corrected on the ticket. The conclusion survived on a narrower reader: §6.7 says a
/// destructuring binder falls back to the VALUE's own component order where no tuple type is
/// known for the pattern. So the VALUE's order is what there is to pin, and it is pinned here.
#[test]
fn wi731_a_renamed_column_keeps_its_position() {
    let mut interp = interp_for(SRC);
    let v = interp
        .call("test.wi731.middle", &[])
        .unwrap_or_else(|e| panic!("middle: {e:?}"));
    let got = rows(&v);
    let kb = interp.kb();
    assert_eq!(got.len(), 2, "expected both rows, got {v:?}");
    for row in &got {
        assert_eq!(row.len(), 3, "expected three columns, got {row:?}");
        // WI-20260827-3ZNBC — a column is the bound value ON ITS OWN CARRIER, so the
        // question is what each one DENOTES (`Int64` vs `String`), not which `Value`
        // variant happens to carry it. That is also the sharper assertion: it is the
        // sorts that pin which column is where.
        assert!(
            crate::common::scalar_int(kb, &row[0].1).is_some(),
            "column 0 must still be `id`, got {row:?}"
        );
        assert!(
            crate::common::scalar_str(kb, &row[1].1).is_some(),
            "the RENAMED column must stay in the middle, got {row:?}"
        );
        assert!(
            crate::common::scalar_int(kb, &row[2].1).is_some(),
            "column 2 must still be `age`, got {row:?}"
        );
    }
}

/// The renamed relation is the SAME relation — `rename` touches the schema and never the
/// query, so no row and no multiplicity moves. `plainLet()` is the control: the identical
/// drain, same `let` binding, no rename.
///
/// A MULTISET, NOT A SEQUENCE, and the difference was measured rather than assumed. Written
/// first as a sequence compare over two SEPARATE interpreters, this failed — `middle` drained
/// `[bob, alice]` against `plain`'s `[alice, bob]`. That is not `rename` reordering anything:
/// within ONE interpreter all three arms drain `[1, 2]` (probed), and what moved the order was
/// the interpreter's own CALL HISTORY. A relation is a BAG (052 OQ6) with no row-order
/// guarantee, so the sequence claim was never this suite's to make; the multiset claim is, and
/// it is the one that says `rename` changed no row. Both arms run on ONE interpreter for the
/// same reason.
#[test]
fn wi731_rename_changes_no_row() {
    let mut interp = interp_for(SRC);
    let renamed = interp
        .call("test.wi731.middle", &[])
        .unwrap_or_else(|e| panic!("middle: {e:?}"));
    let plain = interp
        .call("test.wi731.plainLet", &[])
        .unwrap_or_else(|e| panic!("plainLet: {e:?}"));
    let mut vals = |v: &Value| -> Vec<Vec<String>> {
        let mut out: Vec<Vec<String>> = rows(v)
            .iter()
            .map(|r| r.iter().map(|(_, v)| format!("{v:?}")).collect())
            .collect();
        out.sort();
        out
    };
    let (a, b) = (vals(&renamed), vals(&plain));
    assert_eq!(a.len(), 2, "expected both rows, got {renamed:?}");
    assert_eq!(
        a, b,
        "rename must leave the same rows, with the same values in the same COLUMN positions"
    );
}

/// A SWAP: `(id, name, age)` renamed `age: r.name, name: r.age`. Legal because the collision
/// test is over the RESULT — the intermediate state has two `name`s, the result none.
#[test]
fn wi731_a_swap_is_legal_and_stays_in_place() {
    let mut interp = interp_for(SRC);
    let v = interp
        .call("test.wi731.swap", &[])
        .unwrap_or_else(|e| panic!("swap: {e:?}"));
    let all = rows(&v);
    let kb = interp.kb();
    for row in &all {
        assert_eq!(row.len(), 3, "expected three columns, got {row:?}");
        // Position 1 held `name: String` and now answers to `age`; position 2 held
        // `age: Int64` and now answers to `name`. The VALUES did not move — only the keys.
        // Read carrier-neutrally (WI-20260827-3ZNBC), as in the test above.
        assert!(
            crate::common::scalar_str(kb, &row[1].1).is_some()
                && crate::common::scalar_int(kb, &row[2].1).is_some(),
            "a swap re-keys in place; it must not move the values, got {row:?}"
        );
    }
}

/// THE DRIVING CLIENT — a join whose operands share `name`, which the collision guard refuses
/// until one side is renamed. Driven end-to-end: the joined rows are the ones the condition
/// selects, not merely a schema that type-checks.
#[test]
fn wi731_a_join_over_a_shared_column_name_runs_after_a_rename() {
    let mut interp = interp_for(SRC);
    let v = interp
        .call("test.wi731.owners", &[])
        .unwrap_or_else(|e| panic!("owners: {e:?}"));
    let got = rows(&v);
    assert_eq!(
        got.len(),
        2,
        "one row per (person, their pet) pair — the condition must FILTER, not multiply \
         (a cartesian product of 2x2 would be 4), got {v:?}"
    );
    for row in &got {
        assert_eq!(row.len(), 5, "expected the merged schema's five columns");
        let owner_id = &row[3].1;
        let person_id = &row[0].1;
        assert_eq!(
            format!("{person_id:?}"),
            format!("{owner_id:?}"),
            "the join condition pairs a person with THEIR pet, got {row:?}"
        );
    }
}

/// A SELF-JOIN, where every column collides. The strongest arm: without `rename` there is no
/// spelling of this at all.
#[test]
fn wi731_a_self_join_runs_after_renaming_every_column() {
    let mut interp = interp_for(SRC);
    let v = interp
        .call("test.wi731.selfjoin", &[])
        .unwrap_or_else(|e| panic!("selfjoin: {e:?}"));
    let got = rows(&v);
    assert_eq!(
        got.len(),
        2,
        "`eq(c.id, d.id2)` is the diagonal — two rows, not the 2x2 product, got {v:?}"
    );
    for row in &got {
        assert_eq!(row.len(), 6, "expected both rows' columns");
        assert_eq!(
            format!("{:?}", row[0].1),
            format!("{:?}", row[3].1),
            "the diagonal pairs each row with ITSELF, got {row:?}"
        );
    }
}

/// A source naming no column. The message lists what the schema does have.
#[test]
fn wi731_a_source_naming_no_column_is_refused() {
    // Written through `.( )` rather than `r.nosuch`, because a BARE dot access on a relation
    // fails one level earlier as a member lookup (that surface is WI-20260818-7X7NK's) and
    // never reaches the `Rename` reduction. This spelling reaches it.
    let errs = load_errs(&refusal("r.rename(who: r.(nosuch))"));
    assert!(
        errs.contains("nosuch"),
        "the refusal must name the column that does not exist, got: {errs}"
    );
}

/// A result name that would COLLIDE with a column that is not itself renamed away. The
/// silent reading is a schema with two columns of one name, which no field lookup could
/// answer — so this is the refusal that matters most.
#[test]
fn wi731_a_rename_onto_a_surviving_column_is_refused() {
    let errs = load_errs(&refusal("r.rename(name: r.age)"));
    assert!(
        errs.contains("would leave TWO columns named `name`"),
        "expected the collision refusal, got: {errs}"
    );
}

/// ONE column renamed TWICE — two result names for one source, which no schema can hold.
#[test]
fn wi731_renaming_one_column_twice_is_refused() {
    let errs = load_errs(&refusal("r.rename(x: r.name, y: r.name)"));
    assert!(
        errs.contains("renames column `name` twice"),
        "expected the double-rename refusal, got: {errs}"
    );
}

/// The source must be exactly ONE column. A whole relation names no single column to rename,
/// and the message says which ones it has.
#[test]
fn wi731_a_multi_column_source_is_refused() {
    let errs = load_errs(&refusal("r.rename(who: r)"));
    assert!(
        errs.contains("must name ONE source column") && errs.contains("3 columns"),
        "expected the arity refusal naming the operand's columns, got: {errs}"
    );
}

/// A non-relation source.
#[test]
fn wi731_a_non_relation_source_is_refused() {
    let errs = load_errs(&refusal("r.rename(who: 5)"));
    assert!(
        errs.contains("no relation at all"),
        "expected the non-relation refusal, got: {errs}"
    );
}

/// A foreign source whose column shares the NAME but not the TYPE is caught at LOAD — the
/// `Map` entry states a type, and it must match the column it renames (the membership+type
/// pair `Without` checks of a captured argument). This is the half of the provenance hole a
/// type can close; the arm below is the half it cannot.
#[test]
fn wi731_a_source_of_the_wrong_type_is_refused() {
    let errs = load_errs(&refusal("r.rename(who: tag_row.name)"));
    assert!(
        errs.contains("from a source column of type"),
        "expected the source-type refusal, got: {errs}"
    );
}

/// A RECEIVER WITH ONE VARIABLE IN TWO COLUMNS re-keys exactly the column NAMED. Found by
/// review against the first cut, which matched a source by its `VarId` alone: `r.(a: id, b:
/// id)` is a legal projection — `keep_spec_projections` refuses a duplicate RESULT key, never
/// a duplicate source — so both columns carried one variable and `p.rename(z: p.a)` re-keyed
/// BOTH. It returned a row with two `z` columns and no `b`: a wrong ROW, disagreeing with the
/// type `Rename` had computed, violating label distinctness (§4.5), and leaving `row.b`
/// unanswerable. It loaded and ran clean.
///
/// So the source is matched by NAME **and** variable — the name selects the column (names are
/// distinct within a schema, and it is the same key the type side resolves against `T`), and
/// the variable checks provenance. This arm fails if the name half is dropped; the arm below
/// fails if the variable half is.
#[test]
fn wi731_a_receiver_sharing_one_variable_renames_only_the_named_column() {
    let mut interp = interp_for(SRC);
    let v = interp
        .call("test.wi731.dupVar", &[])
        .unwrap_or_else(|e| panic!("dupVar: {e:?}"));
    for row in crate::common::list_heads(&v) {
        let Value::Tuple { pos, named } = &row else {
            panic!("expected a named-tuple row, got {row:?}")
        };
        assert!(pos.is_empty() && named.len() == 2, "got {row:?}");
        // The KEYS must DIFFER. Under the `VarId`-only match both were `z` — the same
        // `Symbol` — so this comparison is exactly the defect's witness, and it needs no name
        // rendering (the interpreter's `kb` is private, and the NAMES are pinned at load
        // anyway by the declared `List[(z: Int64, b: Int64)]`).
        assert_ne!(
            named[0].0, named[1].0,
            "only the column NAMED `a` may be re-keyed; `b` shares its variable and must keep \
             its own name — got two columns under one key in {row:?}"
        );
    }
}

/// A MEMBERSHIP receiver has no columns at all, and the refusal says so rather than printing
/// an empty list. The wording is `schema_columns_tail`'s, shared with `projection_columns` —
/// the projection site got this sentence and the rename site was left with the empty
/// rendering, which is why there is one owner now and an arm on each side of it.
#[test]
fn wi731_a_membership_receiver_says_it_has_no_columns_at_all() {
    // Its own source rather than `refusal()`'s one-expression slot: the receiver must be
    // `let`-bound first, because a bare rule ref takes a dot ACCESS but not a dot CALL (the
    // WI-443/F1 limitation `where`/`join` share) and the unbound spelling fails one step
    // earlier as an unknown functor, before any `Rename` reduction.
    let domain = SRC.split("  -- A MIDDLE column").next().expect("domain");
    let errs = load_errs(&format!(
        "{domain}\n  operation bad() -> Bool effects Error =\n    let r = person_row\n    \
         let m = anyone\n    let q = m.rename(who: r.name)\n    true\nend\n"
    ));
    assert!(
        errs.contains("it has NONE"),
        "expected the zero-column sentence, got: {errs}"
    );
    assert!(
        !errs.contains("does not have (its columns are: )"),
        "the empty column list must not render as an empty list: {errs}"
    );
}

/// THE LIMIT OF THE TYPE-DIRECTED ROUTE, measured rather than asserted. A source column taken
/// from a DIFFERENT relation type-checks — `Relation[T = (name: String)]` states no
/// provenance, so the reduction cannot tell `r.name` from `pet_row.name` — and the runtime
/// refuses it by the column's VARIABLE, which carries the relation it came from.
///
/// This is the arm that fails if the runtime's identity check is weakened to a name compare:
/// under a name compare this program RUNS and silently renames `r`'s own `name`, which is a
/// wrong answer rather than an error.
#[test]
fn wi731_a_foreign_source_column_is_refused() {
    let src = format!(
        "{}\n  operation bad() -> List[(id: Int64, who: String, age: Int64)] effects Error =\n \
         let r = person_row\n    let other = pet_row\n    r.rename(who: other.name).takeN(9)\nend\n",
        SRC.split("  -- A MIDDLE column").next().expect("domain")
    );
    let mut interp = interp_for(&src);
    let err = interp
        .call("test.wi731.bad", &[])
        .expect_err("a foreign source column must not silently rename the receiver's own");
    let text = format!("{err:?}");
    assert!(
        text.contains("DIFFERENT relation"),
        "expected the foreign-source refusal, got: {text}"
    );
    // NOT `EvalError::Internal`, and this half is the one review added. The resolver bridge
    // `debug_assert`s on that variant (kb/resolve.rs), so classifying an ordinary user
    // mistake as an evaluator-invariant violation would abort a debug build and silently
    // residualize a release one the moment `rename` is reached from a rule body — the trap
    // `UnpinnedRequirement` records having fallen into. This assertion is what stops it
    // being reclassified back.
    assert!(
        !text.contains("Internal"),
        "a user mistake must not be an evaluator-invariant error: {text}"
    );
}

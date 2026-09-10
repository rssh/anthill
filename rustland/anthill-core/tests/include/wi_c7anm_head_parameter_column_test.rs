//! WI-20260909-C7ANM — a sigil-free head parameter (060 §2.1) is a COLUMN, and it
//! holds the column position the author WROTE it in.
//!
//! §2.1 says `rule g(x: Red, ?d)` is the same rule as `rule g(?x: Red, ?d)`. It was
//! not. `Term::Fn` files a call's arguments into a positional list and a named list,
//! which loses the interleaving between the two, and the loader rebuilt the head by
//! APPENDING each parameter after the positional args — so the clause above compiled
//! to `g(?d, ?x)`. Both of the ticket's symptoms are that one wrong order:
//!
//!  * `g(red(), ?z)` answered `?z = red` — the value that occupied the OTHER column,
//!    a definite answer nobody asked for; and
//!  * `g(blue(), ?z)` was ADMITTED, because `blue()` landed in the unconstrained
//!    column while the `x: Red` bound sat correctly on a variable the body binds to
//!    `red`. The bound was never unenforced — it was enforced on the wrong slot.
//!
//! THE SIGIL TWIN IS THE YARDSTICK, and it is a control, not a duplicate: every
//! `*_sigil` row here passes BOTH with the repair and without it BY DESIGN. What the
//! suite asserts is that the sigil-free spelling answers EXACTLY what its twin does —
//! by VALUE and by REFUSAL, never by a clean load.
//!
//! WHICH ROWS FAIL WHEN THE REPAIR IS BACKED OUT. The repair is FOUR AXES at one
//! function, and each was backed out separately against these ten rows — MEASURED, not
//! predicted. Axes 3 and 4 came from `/code-review`; axis 3 is a defect this ticket's
//! own axis-1 assert INTRODUCED, and 4 is the same "both spellings, one answer"
//! invariant broken one head further along.
//!
//! AXIS 1 — THE COLUMN ORDER (`rule_head_written_columns` replaced by appending the
//! parameters after the positional args, as before). 4 of 10 fail:
//!
//!  * `a_parameter_holds_its_written_column` — on both sigil-free rows: `?z = red`
//!    where the twin says unbound, and 1 answer where the twin refuses. Its two sigil
//!    rows pass either way, which is what makes them the yardstick.
//!  * `a_middle_parameter_is_the_middle_column` — the middle column comes back empty.
//!  * `a_parameter_name_is_one_variable_across_a_multi_head_rule` — the two heads write
//!    the parameter in OPPOSITE positions, so it measures this axis too.
//!  * `the_declared_column_schema_follows_the_written_order` — the reported tuple
//!    becomes `(a: ?a, b: ?b, x: Red)`. A SECOND reader of the same order (the 052
//!    relation schema, reached through the typer, not the resolver), which is why it is
//!    its own row rather than a restatement of the others.
//!
//! AXIS 2 — THE RE-INTERNED KEY (`self.reintern(key)` dropped). 1 of 10 fails:
//!
//!  * `a_non_parameter_named_arg_keeps_its_key` — at LOAD. It is the ONLY row that
//!    fails, and only because it has its own fixture: with the clause in `SRC`, the load
//!    error took six of seven rows down at once, all for that one reason, which is
//!    per-row evidence of nothing.
//!
//! AXIS 3 — THE BRACKET DECLINE (`is_type_application` gate removed). 2 of 10 fail:
//!
//!  * `a_bracketed_head_binds_a_type_argument_not_a_parameter` — the `rule` spelling
//!    stops meaning what the `fact` spelling means. Its `fact` half passes either way.
//!  * `a_bracketed_head_may_carry_a_positional_argument_too` — a PANIC out of the
//!    loader, from axis 1's own assert.
//!
//! AXIS 4 — ONE VARIABLE PER PARAMETER NAME PER RULE (a fresh var minted per head).
//! 1 of 10 fails:
//!
//!  * `a_parameter_name_is_one_variable_across_a_multi_head_rule` — the FIRST head's
//!    column floundered. Its sigil twin and its last-head rows pass either way.
//!
//! A FIFTH ARRANGEMENT, measured because the ticket's four rows do not rule it out:
//! putting the parameters FIRST rather than in written order. It passes
//! `a_parameter_holds_its_written_column` and still fails 3 —
//! `a_parameter_written_last_keeps_its_column`,
//! `a_middle_parameter_is_the_middle_column` and the schema row. That is what the
//! parameter-last pair is FOR: it passes under the real defect BY DESIGN, so it is dead
//! weight against axis 1 and the only row that catches this.
//!
//! PASS EITHER WAY UNDER ALL FOUR AXES, BY DESIGN: `a_lone_parameter_is_unaffected`
//! (one column has no order to get wrong — the shape `wi742` already drives, and the
//! defect needed a SECOND head variable to show) and
//! `an_untyped_bare_head_name_is_still_a_constant` (it claims no bound, so it never
//! reaches the reclassifier and must keep the meaning the spec gives it).

use anthill_core::eval::Value;
use anthill_core::kb::KnowledgeBase;

/// One answer column, read the way a consumer reads it: the entity's functor name, or
/// the literal string `"unbound"` for a variable that came back free.
///
/// A STRING rather than a count, because a count cannot tell the defect apart from the
/// repair here: the broken spelling answered ONE row too, holding the wrong value.
fn column(kb: &mut KnowledgeBase, qn: &str) -> Vec<String> {
    let rows = crate::common::query_unary(kb, qn);
    rows.iter()
        .map(|(v, definite)| {
            assert!(*definite, "{qn}: a floundered answer is not a decision");
            match v {
                Value::Var(_) => "unbound".to_owned(),
                other => match crate::common::entity_functor(kb, other) {
                    Some(s) => kb.local_name_of(s).to_string(),
                    None => panic!("{qn}: answer is neither a variable nor an entity: {other:?}"),
                },
            }
        })
        .collect()
}

/// Two sorts, one seeded relation, and NO `require` / projection / dictionary anywhere
/// — the defect is the head form itself.
///
/// Each `p_*` probe calls the relation under test from a rule BODY and hands back the
/// second column, which is what lets `column` read the binding by name.
const SRC: &str = r#"
namespace test.c7anm
  sort Red
    entity red
  end
  sort Blue
    entity blue
  end
  fact seedr(red())
  fact seedb(blue())

  -- THE PAIR UNDER TEST: one character apart.
  rule gfree(x: Red, ?d) :- seedr(x)
  rule gsig(?x: Red, ?d) :- seedr(?x)

  -- The parameter written LAST — the order the append got right by accident.
  rule hfree(?d, x: Red) :- seedr(x)
  rule hsig(?d, ?x: Red) :- seedr(?x)

  -- The parameter in the MIDDLE of three columns.
  rule tri(?a, x: Red, ?b) :- seedr(x), seedb(?a), seedb(?b)

  -- CONTROLS.
  rule lone(x: Red) :- seedr(x)
  rule untyped(x, ?d) :- seedr(?d)

  rule p_gfree_red(?d)  :- gfree(red(), ?d)
  rule p_gfree_blue(?d) :- gfree(blue(), ?d)
  rule p_gsig_red(?d)   :- gsig(red(), ?d)
  rule p_gsig_blue(?d)  :- gsig(blue(), ?d)

  rule p_hfree_red(?d)  :- hfree(?d, red())
  rule p_hfree_blue(?d) :- hfree(?d, blue())
  rule p_hsig_red(?d)   :- hsig(?d, red())
  rule p_hsig_blue(?d)  :- hsig(?d, blue())

  rule p_tri_middle(?m) :- tri(blue(), ?m, blue())
  rule p_tri_first(?a)  :- tri(?a, red(), blue())

  rule p_lone(?x)       :- lone(?x)
  rule p_untyped_named(?d) :- untyped(x, ?d)
  rule p_untyped_wrong(?d) :- untyped(?d, blue())
end
"#;

#[test]
fn a_parameter_holds_its_written_column() {
    let mut kb = crate::common::load_kb_with(SRC);
    // THE FOUR ROWS THE TICKET SPECIFIES. The sigil-free spelling must answer exactly
    // what its twin answers.
    //
    // Column 0 is the PARAMETER, which the body binds to `red`; column 1 is the free
    // `?d` the caller passed. So `g(red(), ?z)` decides and leaves `?z` free…
    assert_eq!(column(&mut kb, "test.c7anm.p_gfree_red"), ["unbound"]);
    assert_eq!(column(&mut kb, "test.c7anm.p_gsig_red"), ["unbound"]);
    // …and `g(blue(), ?z)` is REFUSED — `blue()` is not a `Red`, and column 0 is where
    // the bound is. The refusal is half the claim: a `?z = red` answer here is exactly
    // the defect.
    assert!(column(&mut kb, "test.c7anm.p_gfree_blue").is_empty());
    assert!(column(&mut kb, "test.c7anm.p_gsig_blue").is_empty());
}

#[test]
fn a_parameter_written_last_keeps_its_column() {
    // PASSES EITHER WAY BY DESIGN — see the module header. `rule h(?d, x: Red)` is the
    // one order an append-last rebuild produced correctly, so this row is what keeps a
    // repair honest: put the parameters FIRST instead and this goes red while every
    // other row stays green.
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(column(&mut kb, "test.c7anm.p_hfree_red"), ["unbound"]);
    assert_eq!(column(&mut kb, "test.c7anm.p_hsig_red"), ["unbound"]);
    assert!(column(&mut kb, "test.c7anm.p_hfree_blue").is_empty());
    assert!(column(&mut kb, "test.c7anm.p_hsig_blue").is_empty());
}

#[test]
fn a_middle_parameter_is_the_middle_column() {
    // Three columns, the parameter between two positional ones — the shape that
    // distinguishes "written order" from either end. The answer is a VALUE (`red`, the
    // only thing `seedr` can bind the parameter to), not a count.
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(column(&mut kb, "test.c7anm.p_tri_middle"), ["red"]);
    assert_eq!(column(&mut kb, "test.c7anm.p_tri_first"), ["blue"]);
}

/// ITS OWN FIXTURE, and ONE column, so this row measures ONE axis. A named argument
/// whose value is a VARIABLE stays a named argument (spec: `rule reaches(from: ?a, to:
/// ?b)`), so this head is one column — `x` — plus the key `from:`. With a single column
/// there is no order to get wrong, which leaves the re-intern as the only thing the row
/// can fail on.
///
/// It cannot live in `SRC`: a mis-interned key is a LOAD error, and a load error in a
/// shared fixture fails every row that shares it (MEASURED — six of seven, all for one
/// reason, which is no per-row evidence at all).
const MIXED_SRC: &str = r#"
namespace test.c7anm.mixed
  sort Red
    entity red
  end
  sort Blue
    entity blue
  end
  fact seedr(red())
  fact seedb(blue())

  rule mixed(from: ?a, x: Red) :- seedr(x), seedb(?a)
  rule p_mixed(?x) :- mixed(from: blue(), ?x)
end
"#;

#[test]
fn a_non_parameter_named_arg_keeps_its_key() {
    // A non-parameter named arg can only occur BESIDE a parameter, which is why the
    // mis-interned key went unseen: a head with no parameter never reaches the rebuild
    // at all.
    //
    // The load error it produced named a KB symbol that merely SHARES AN INDEX with the
    // parse-table entry for `from` — `TypeExtractor` in one fixture, `NamedTuple` in
    // another — so the row asserts the key WORKS rather than pinning the wrong name.
    let mut kb = crate::common::load_kb_with(MIXED_SRC);
    assert_eq!(column(&mut kb, "test.c7anm.mixed.p_mixed"), ["red"]);
}

#[test]
fn a_lone_parameter_is_unaffected() {
    // PASSES EITHER WAY BY DESIGN: with one column there is no order to get wrong, and
    // this is the shape `wi742_typed_relational_head_test` already drives. It is here
    // to say so — the defect needed a SECOND head variable to show.
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(column(&mut kb, "test.c7anm.p_lone"), ["red"]);
}

#[test]
fn an_untyped_bare_head_name_is_still_a_constant() {
    // PASSES EITHER WAY BY DESIGN. `rule untyped(x, ?d)` claims no bound, so `x` never
    // reaches the reclassifier at all and keeps the meaning the spec gives it — a
    // symbolic constant column, not a variable. Both rows below are that claim: the
    // body's `untyped(x, ?d)` matches because both spellings of `x` denote one
    // unresolved name, and `untyped(?d, blue())` finds nothing because column 1 is
    // bound to `red`.
    let mut kb = crate::common::load_kb_with(SRC);
    assert_eq!(column(&mut kb, "test.c7anm.p_untyped_named"), ["red"]);
    assert!(column(&mut kb, "test.c7anm.p_untyped_wrong").is_empty());
}

/// A BRACKET is a type application, not a parameter list. `Spec[T = Red]` binds the
/// spec's type argument `T`, and `T = Red` inside it is not §2.1's `name: Type`. The
/// two are byte-identical once built, so only the written surface separates them —
/// which is exactly what `SimpleTermStore::is_type_application` records.
///
/// The `fact` spelling is the CONTROL and the yardstick: it never routes through the
/// §2.1 rebuild, so it always meant the type binding, and the `rule` spelling must mean
/// the same thing.
fn bracket_src(head: &str) -> String {
    format!(
        r#"
namespace test.c7anm.bracket
  import anthill.prelude.Int64
  sort Red
    entity red
  end
  fact seedr(red())
{head}  rule probe(?t) :- myrel[T = ?t]
end
"#
    )
}

#[test]
fn a_bracketed_head_binds_a_type_argument_not_a_parameter() {
    // Driven, both spellings, one answer — `?t = Red`, the sort the bracket bound.
    let mut by_rule =
        crate::common::load_kb_with(&bracket_src("  rule myrel[T = Red] :- seedr(?x)\n"));
    assert_eq!(
        column(&mut by_rule, "test.c7anm.bracket.probe"),
        ["Red"],
        "the `rule` spelling of a bracketed head must bind the type argument"
    );
    let mut by_fact = crate::common::load_kb_with(&bracket_src("  fact myrel[T = Red]\n"));
    assert_eq!(column(&mut by_fact, "test.c7anm.bracket.probe"), ["Red"]);
}

#[test]
fn a_bracketed_head_may_carry_a_positional_argument_too() {
    // `Spec[Pos, T = Named]` is built by the BRACKET frame, which records no written
    // order — a bracket is not an argument list — so a §2.1 rebuild reaching it finds
    // positional args it has no order to place, and ASSERTS. It has to decline at the
    // surface instead: a compiler panic is not a diagnostic.
    //
    // Driven rather than load-only, so the row says what the head MEANS and not only
    // that it survived: the bracket binds `T`, and the positional slot stays a slot.
    let mut kb = crate::common::load_kb_with(
        r#"
namespace test.c7anm.bracket2
  import anthill.prelude.Int64
  sort Red
    entity red
  end
  fact seedr(red())
  rule myrel[Int64, T = Red] :- seedr(?x)
  rule probe(?t) :- myrel[Int64, T = ?t]
end
"#,
    );
    assert_eq!(column(&mut kb, "test.c7anm.bracket2.probe"), ["Red"]);
}

/// A MULTI-HEAD rule: two heads, one shared body, one parameter name. The parameter map
/// is cleared per RULE, not per head, precisely so the shared body can read every head's
/// names — so a parameter name must denote ONE variable across the whole rule.
const MULTI_HEAD_SRC: &str = r#"
namespace test.c7anm.multi
  sort Red
    entity red
  end
  sort Blue
    entity blue
  end
  fact seedr(red())
  fact seedb(blue())

  rule twin: aa(x: Red, ?d), bb(?d, x: Red) :- seedr(x), seedb(?d)
  rule sig:  cc(?x: Red, ?e), dd(?e, ?x: Red) :- seedr(?x), seedb(?e)

  rule p_aa_first(?p)  :- aa(?p, blue())
  rule p_bb_last(?p)   :- bb(blue(), ?p)
  rule p_cc_first(?p)  :- cc(?p, blue())
  rule p_dd_last(?p)   :- dd(blue(), ?p)
end
"#;

#[test]
fn a_parameter_name_is_one_variable_across_a_multi_head_rule() {
    // THE FIRST head is the one that broke: each head minted a fresh variable and
    // overwrote the map, so only the LAST head's variable was the one the body bound.
    // `aa`'s column came back FREE with an undischarged `domain(?p, Red)` — a
    // FLOUNDERED answer, which `column` refuses as a decision.
    //
    // The `cc`/`dd` pair is the sigil twin and the yardstick: `?x` in two heads is one
    // parse variable, so that spelling always shared its KB variable.
    let mut kb = crate::common::load_kb_with(MULTI_HEAD_SRC);
    assert_eq!(column(&mut kb, "test.c7anm.multi.p_aa_first"), ["red"]);
    assert_eq!(column(&mut kb, "test.c7anm.multi.p_cc_first"), ["red"]);
    // The LAST head passed either way — stated so the row above is not read as
    // measuring both.
    assert_eq!(column(&mut kb, "test.c7anm.multi.p_bb_last"), ["red"]);
    assert_eq!(column(&mut kb, "test.c7anm.multi.p_dd_last"), ["red"]);
}

/// A relation's DECLARED column schema (052) reads the same head. It is a second
/// consumer of the written order, reached through the typer rather than the resolver,
/// so it gets its own row: the resolver rows above would all pass with a schema that
/// still reported the columns in the wrong order.
const COLUMN_SRC: &str = r#"
namespace test.c7anm.cols
  import anthill.prelude.{List, Int64}
  sort Red
    entity red
  end
  fact seedr(red())
  rule tri(?a, x: Red, ?b) :- seedr(x), seedr(?a), seedr(?b)
  operation rows() -> List[T = Int64] effects Error =
    let r = tri
    r.takeN(5)
end
"#;

#[test]
fn the_declared_column_schema_follows_the_written_order() {
    // Asserted through the type ERROR, which is the shortest way to make the typer
    // print the tuple it inferred. `x: Red` is the MIDDLE column, named and typed;
    // appending it last reported `(a: ?a, b: ?b, x: Red)`.
    crate::common::expect_load_errors(
        crate::common::try_load_kb_with(COLUMN_SRC),
        &["got List[T = (a: ?a, x: Red, b: ?b)]"],
    );
}

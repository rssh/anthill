//! THE LAW AT A TYPED EQUALITY IS READ OFF ITS CLASS (WI-20261105-CBRD2). `Eq`'s law `eq_refl`
//! answers a comparison of identical operands without asking the member (kernel-language §8.3).
//! Where the typer decided the call, the law is read off what it decided
//! (`KnowledgeBase::eq_call_law`): the member, and for a member derived field by field the
//! dictionary it is entered with — lawful where the provider provides `Eq`, or provides it under
//! a condition every condition's dictionary meets (`dictionary_is_lawful`). It was read off the
//! operands: the resolver asked the equality index whether each operand's constructor heads a
//! carrier whose own `eq` decides identical operands, and walked the values for a lawful carrier
//! at each constructor; the interpreter walked them for a derived member and asked the index of
//! the operand's constructor for a member with type parameters of its own. An equality call
//! pinned to such a member keeps the law, as its class says; a direct call of the member does
//! not.
//!
//! The verdicts are the ones the operands gave, so the rows measure the reading
//! (`resolve::eq_index_reads_by_this_thread`, which counts each answer the index gives about a
//! constructor) beside them.
//!
//! ## What fails with the change backed out
//!
//! Measured with temporary switches, then removed. The control is each switch unset: every
//! row passes.
//!
//! * The resolver reading the law off the operands:
//!   [`a_rule_body_equality_reads_its_law_off_the_member`] and
//!   [`a_composite_equality_reads_its_law_off_the_dictionary`] fail on the index reads.
//! * The interpreter reading a derived member's law and a generic member's off the operands:
//!   [`an_operation_body_equality_reads_its_law_off_the_class`] fails on the index reads, and
//!   so does [`a_composite_equality_reads_its_law_off_the_dictionary`], whose `Option.eq` the
//!   resolver enters through the bridge (`some(1.5) = some(1.5)`).
//! * The law not carried to where an equality call's operands are in:
//!   [`an_operation_body_equality_reads_its_law_off_the_class`] fails, `atX()` answering 0, and
//!   on the route through the dictionary the typer built alone
//!   [`an_equality_call_through_a_dictionary_keeps_its_law`], `atY()` answering 0, and on the
//!   route through the caller's frame alone
//!   [`an_equality_call_filling_its_members_requirement_keeps_its_law`], `atR()` answering 0.
//!   The branch for a pinned member's own slots carries the law too; no program here reaches
//!   it.

use anthill_core::kb::resolve::eq_index_reads_by_this_thread;

use crate::common::{load_kb_with, load_stdlib_kb, query_pattern_term, run_int64};

/// `Pt`'s own `eq` holds of no pair; `lawful` says whether `Pt` provides `Eq` beside it.
fn src(ns: &str, lawful: bool, decls: &str) -> String {
    let eq = if lawful { "    provides Eq[T = Pt]\n" } else { "" };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Float, Bool, Eq, PartialEq, Option}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.PartialEq.{{eq}}
  sort Pt
    entity pt(x: Int64)
    provides PartialEq[T = Pt]
{eq}    operation eq(a: Pt, b: Pt) -> Bool = false
  end
{decls}
end
"#
    )
}

/// `f`'s result and the index's answers it read, the shared base loaded first.
fn counting<R>(f: impl FnOnce() -> R) -> (R, usize) {
    drop(load_stdlib_kb());
    let before = eq_index_reads_by_this_thread();
    let r = f();
    (r, eq_index_reads_by_this_thread() - before)
}

/// Whether `<ns>.<rule>` holds definitely, and the index's answers its search read.
fn holds(src: &str, ns: &str, rule: &str) -> (bool, usize) {
    let mut kb = load_kb_with(src);
    let goal = query_pattern_term(&mut kb, &format!("{ns}.{rule}"));
    let (got, reads) = counting(|| kb.resolve(&[goal], &Default::default()));
    (got.iter().any(|s| s.is_definite()), reads)
}

/// `pt(x: 1) = pt(x: 1)` holds by the law where `Pt` provides `Eq`, and is `Pt.eq`'s `false`
/// where it does not; `pt(x: 1) = pt(x: 2)` is the member's either way.
#[test]
fn a_rule_body_equality_reads_its_law_off_the_member() {
    let rules = "  rule same() :- pt(x: 1) = pt(x: 1)\n  rule apart() :- pt(x: 1) = pt(x: 2)";
    for (ns, lawful) in [("test.cbrd2.law.rl", true), ("test.cbrd2.law.rp", false)] {
        let program = src(ns, lawful, rules);
        for (rule, want) in [("same()", lawful), ("apart()", false)] {
            let (got, reads) = holds(&program, ns, rule);
            assert_eq!(reads, 0, "{ns}: `{rule}` read the equality index");
            assert_eq!(got, want, "{ns}: `{rule}`");
        }
    }
}

/// At `Option[T = Pt]` the law holds where `Pt`'s does, read off the dictionary of `Option`'s
/// derived `eq`; at `Option[T = Float]` never, `Float` providing no `Eq`, and its member
/// compares by IEEE equality.
#[test]
fn a_composite_equality_reads_its_law_off_the_dictionary() {
    let rules = "  rule same() :- some(pt(x: 1)) = some(pt(x: 1))\n  \
                 rule floats() :- some(1.5) = some(1.5)\n  \
                 rule nans() :- some(Float.nan) = some(Float.nan)";
    for (ns, lawful) in [("test.cbrd2.law.ol", true), ("test.cbrd2.law.op", false)] {
        let program = src(ns, lawful, rules);
        for (rule, want) in [("same()", lawful), ("floats()", true), ("nans()", false)] {
            let (got, reads) = holds(&program, ns, rule);
            assert_eq!(reads, 0, "{ns}: `{rule}` read the equality index");
            assert_eq!(got, want, "{ns}: `{rule}`");
        }
    }
}

/// In an operation body: `Pt`'s law and `Option[T = Pt]`'s as in a rule body, and a generic
/// operation bound as `X`'s `eq` beside `provides Eq[T = X]` keeps the law at the equality
/// call (`atX`) and not at a direct call of itself (`atInt`).
#[test]
fn an_operation_body_equality_reads_its_law_off_the_class() {
    let ops = r#"
  operation same() -> Int64 = if pt(x: 1) = pt(x: 1) then 1 else 0
  operation someSame() -> Int64 = if some(pt(x: 1)) = some(pt(x: 1)) then 1 else 0
  operation never[A](x: A, y: A) -> Bool = false
  sort X
    entity xx(n: Int64)
  end
  namespace X
    import anthill.prelude.{PartialEq, Eq}
    provides PartialEq[T = X, eq = never]
    provides Eq[T = X]
  end
  operation atX() -> Int64 = if PartialEq.eq(xx(1), xx(1)) then 1 else 0
  operation atInt() -> Int64 = if never(1, 1) then 1 else 0
"#;
    for (ns, lawful) in [("test.cbrd2.law.bl", true), ("test.cbrd2.law.bp", false)] {
        let program = src(ns, lawful, ops);
        let want = i64::from(lawful);
        for (entry, want) in [("same", want), ("someSame", want), ("atX", 1), ("atInt", 0)] {
            let (got, reads) = counting(|| run_int64(&program, &format!("{ns}.{entry}")));
            assert_eq!(reads, 0, "{ns}: `{entry}` read the equality index");
            assert_eq!(got, Ok(want), "{ns}: `{entry}`");
        }
    }
}

/// A generic operation of a sort that requires a dictionary, bound as the sort's `eq`, is entered
/// through the dictionary the typer built: the equality call keeps the law there too (`atY`).
#[test]
fn an_equality_call_through_a_dictionary_keeps_its_law() {
    let program = r#"namespace test.cbrd2.law.dict
  import anthill.prelude.{Int64, Bool, PartialEq, Eq}
  sort Tag
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort Int64Tag
    provides Tag[T = Int64]
    operation tag(x: Int64) -> Int64 = 7
  end
  sort Y
    sort T = ?
    requires Tag[T = T]
    entity yy(v: T)
    operation sameY[A](a: Y, b: Y) -> Bool = false
    provides PartialEq[T = Y, eq = sameY]
    provides Eq[T = Y]
  end
  operation atY() -> Int64 = if PartialEq.eq(yy(v: 1), yy(v: 1)) then 1 else 0
  operation apartY() -> Int64 = if PartialEq.eq(yy(v: 1), yy(v: 2)) then 1 else 0
end
"#;
    for (entry, want) in [("atY", 1), ("apartY", 0)] {
        let (got, reads) = counting(|| run_int64(program, &format!("test.cbrd2.law.dict.{entry}")));
        assert_eq!(reads, 0, "`{entry}` read the equality index");
        assert_eq!(got, Ok(want), "`{entry}`");
    }
}

/// A generic operation with a `requires` of its own, bound as a carrier's `eq`, is entered with
/// the slot its call fills, through the caller's frame: the equality call keeps the law there
/// too (`atR`). It answered 0 while the law was read off a dictionary frame alone.
#[test]
fn an_equality_call_filling_its_members_requirement_keeps_its_law() {
    let program = r#"namespace test.cbrd2.law.slot
  import anthill.prelude.{Int64, Bool, PartialEq, Eq}
  sort Tag
    sort T = ?
    operation tag(x: T) -> Int64
  end
  operation sameR[A](a: A, b: A) -> Bool requires Tag[T = A] = false
  sort R
    entity rr(n: Int64)
  end
  sort RTag
    provides Tag[T = R]
    operation tag(x: R) -> Int64 = 3
  end
  namespace R
    import anthill.prelude.{PartialEq, Eq}
    provides PartialEq[T = R, eq = sameR]
    provides Eq[T = R]
  end
  operation atR() -> Int64 = if PartialEq.eq(rr(n: 1), rr(n: 1)) then 1 else 0
  operation apartR() -> Int64 = if PartialEq.eq(rr(n: 1), rr(n: 2)) then 1 else 0
end
"#;
    for (entry, want) in [("atR", 1), ("apartR", 0)] {
        let (got, reads) = counting(|| run_int64(program, &format!("test.cbrd2.law.slot.{entry}")));
        assert_eq!(reads, 0, "`{entry}` read the equality index");
        assert_eq!(got, Ok(want), "`{entry}`");
    }
}

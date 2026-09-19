//! WI-20260919-1Z3E7 (proposal 066) — a provision's `:- goals` are in scope exactly for
//! the operations written in its `where` block.
//!
//! Before this, every body of a carrier was checked as if every provision's conditions
//! were sort-level `requires` (the per-sort dictionary chain was each body's scope), so
//! an operation that belongs to no provision could read a condition, and the condition
//! then became that operation's requirement, charged to its callers and stated in no
//! definition. MEASURED on CKD4J: `Box3.inner` using `PartialEq[T]` loaded, and
//! `Box3.inner(box3(v: fe(1.5)), …)` was refused naming a requirement of `Box3` nobody
//! wrote. Now the condition's slot is HIDDEN from every body but its members'
//! (`ProviderDictChain::hidden_from_body`): it keeps its index and name — the layout is
//! per sort — and answers no goal.
//!
//! ── WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT ──────────────────────────────
//!
//! Making `hidden_from_body` hide nothing (the pre-066 scope) fails
//! `a_non_member_reading_a_condition_is_a_load_error` and
//! `a_sibling_blocks_condition_is_out_of_scope`: both programs then LOAD. That is the
//! control that the refusal is this change's — the same programs loaded before it.
//! Removing the `where` production from the grammar fails every test here that writes a
//! block (a parse error). PASS EITHER WAY BY DESIGN: `a_helper_with_its_own_requires_*`
//! — the repair 066 §1 prescribes for a helper must keep working, block or no block.

use anthill_core::eval::value::Value;

/// The member form, both body spellings. `eq` reads `PartialEq[T]` inside the block.
fn member_program(ns: &str, curly: bool) -> String {
    let (open, close) = if curly { ("where {", "}") } else { ("where", "end") };
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Bool, Int64, PartialEq}}
  import anthill.prelude.PartialEq.{{eq}}
  sort Box
    sort T = ?
    entity box(v: T)
    provides PartialEq[Box] :- PartialEq[T] {open}
      operation eq(a: Box, b: Box) -> Bool =
        match a
          case box(x) -> match b case box(y) -> PartialEq.eq(x, y)
    {close}
  end
  sort D
    operation yes(n: Int64) -> Int64 = if eq(box(v: 1), box(v: 1)) then 1 else 0
    -- The negative twin: an `eq` answering `true` vacuously would fail here.
    operation no(n: Int64) -> Int64 = if eq(box(v: 1), box(v: 2)) then 1 else 0
  end
end
"#
    )
}

fn eval_int(src: &str, op: &str) -> i64 {
    let mut interp = crate::common::interp_for(src);
    match interp.call(op, &[Value::Int(0)]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{op}: expected an Int, got {other:?}"),
    }
}

fn refusals(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src).err().unwrap_or_default()
}

#[test]
fn a_block_member_reads_its_condition_and_answers() {
    for (curly, ns) in [(false, "wi1z3e7.endform"), (true, "wi1z3e7.curly")] {
        let src = member_program(ns, curly);
        assert_eq!(refusals(&src), Vec::<String>::new(), "curly = {curly}");
        assert_eq!(eval_int(&src, &format!("{ns}.D.yes")), 1, "curly = {curly}");
        assert_eq!(eval_int(&src, &format!("{ns}.D.no")), 0, "curly = {curly}");
    }
}

/// The SAME `eq`, written after the one-line clause instead of inside a block. Loaded
/// before 066 (the control); now the condition is out of scope for it.
#[test]
fn a_non_member_reading_a_condition_is_a_load_error() {
    let src = r#"
namespace wi1z3e7.outside
  import anthill.prelude.{Bool, Int64, PartialEq}
  sort Box
    sort T = ?
    entity box(v: T)
    provides PartialEq[Box] :- PartialEq[T]
    operation eq(a: Box, b: Box) -> Bool =
      match a
        case box(x) -> match b case box(y) -> PartialEq.eq(x, y)
  end
end
"#;
    let errs = refusals(src);
    assert!(
        errs.iter().any(|e| e.contains("wi1z3e7.outside.Box.eq")
            && e.contains("`provides PartialEq[…] :- … where … end`")),
        "a body outside the block must be refused naming the provision's block; got {errs:?}"
    );
}

/// A member of ONE provision reading ANOTHER provision's condition: the sibling's
/// block is not its scope.
#[test]
fn a_sibling_blocks_condition_is_out_of_scope() {
    let src = r#"
namespace wi1z3e7.sibling
  import anthill.prelude.{Bool, Int64, PartialEq}
  sort Size
    sort T = ?
    operation size(x: T) -> Int64
  end
  sort Box
    sort T = ?
    entity box(v: T)
    provides PartialEq[Box] :- PartialEq[T] where
      operation eq(a: Box, b: Box) -> Bool =
        match a
          case box(x) -> match b case box(y) -> PartialEq.eq(x, y)
    end
    provides Size[Box] :- Size[T] where
      operation size(b: Box) -> Int64 =
        match b
          case box(x) -> if PartialEq.eq(x, x) then Size.size(x) else 0
    end
  end
end
"#;
    let errs = refusals(src);
    assert!(
        errs.iter().any(|e| e.contains("wi1z3e7.sibling.Box.size")
            && e.contains("`provides PartialEq[…] :- … where … end`")),
        "`size` is a member of `Size`, not of `PartialEq`; got {errs:?}"
    );
    assert_eq!(
        errs.len(),
        1,
        "`size`'s own `Size[T]` and `eq`'s `PartialEq[T]` are in scope; got {errs:?}"
    );
}

/// 066 §5 Q2's repair: a helper that is no spec member states its own `requires`, and
/// needs no block — both for a component compare (`inner`) and for a compare of whole
/// boxes, whose `PartialEq[T]` is the `Box` provision's SUB-goal (`same`).
#[test]
fn a_helper_with_its_own_requires_needs_no_block() {
    let src = r#"
namespace wi1z3e7.helper
  import anthill.prelude.{Bool, Int64, PartialEq}
  sort Box
    sort T = ?
    entity box(v: T)
    provides PartialEq[Box] :- PartialEq[T] where
      operation eq(a: Box, b: Box) -> Bool =
        match a
          case box(x) -> match b case box(y) -> PartialEq.eq(x, y)
    end
    operation inner(a: Box, b: Box) -> Bool requires PartialEq[T] =
      match a
        case box(x) -> match b case box(y) -> PartialEq.eq(x, y)
    operation same(a: Box, b: Box) -> Bool requires PartialEq[T] = PartialEq.eq(a, b)
  end
  sort D
    operation innerYes(n: Int64) -> Int64 = if Box.inner(box(v: 1), box(v: 1)) then 1 else 0
    operation innerNo(n: Int64) -> Int64 = if Box.inner(box(v: 1), box(v: 2)) then 1 else 0
    operation sameYes(n: Int64) -> Int64 = if Box.same(box(v: 1), box(v: 1)) then 1 else 0
    operation sameNo(n: Int64) -> Int64 = if Box.same(box(v: 1), box(v: 2)) then 1 else 0
  end
end
"#;
    assert_eq!(refusals(src), Vec::<String>::new());
    assert_eq!(eval_int(src, "wi1z3e7.helper.D.innerYes"), 1);
    assert_eq!(eval_int(src, "wi1z3e7.helper.D.innerNo"), 0);
    assert_eq!(eval_int(src, "wi1z3e7.helper.D.sameYes"), 1);
    assert_eq!(eval_int(src, "wi1z3e7.helper.D.sameNo"), 0);
}

/// A member block's operations are the CARRIER's; a namespace body has none.
#[test]
fn a_block_outside_a_sort_body_is_refused() {
    let src = r#"
namespace wi1z3e7.ns
  import anthill.prelude.{Bool, PartialEq}
  provides PartialEq[Nothing] where
    operation eq(a: Bool, b: Bool) -> Bool = true
  end
end
"#;
    let errs = anthill_core::parse::parse(src).expect_err("a parse-time refusal");
    assert!(
        errs.iter()
            .any(|e| e.message.contains("admitted only in a sort or enum body")),
        "got {errs:?}"
    );
}

/// 066 §5 Q2: the block holds the provided spec's OWN members. A helper written in it
/// would type against evidence its dispatch does not bring, so it is refused and sent
/// outside with its own `requires` (`a_helper_with_its_own_requires_needs_no_block`).
#[test]
fn a_block_holds_only_the_specs_own_members() {
    let src = r#"
namespace wi1z3e7.notmember
  import anthill.prelude.{Bool, Int64, PartialEq}
  sort Box
    sort T = ?
    entity box(v: T)
    provides PartialEq[Box] :- PartialEq[T] where
      operation eq(a: Box, b: Box) -> Bool =
        match a
          case box(x) -> match b case box(y) -> PartialEq.eq(x, y)
      operation helper(a: Box) -> Int64 = 1
    end
  end
end
"#;
    let errs = refusals(src);
    assert!(
        errs.iter().any(|e| e.contains("wi1z3e7.notmember.Box.helper")
            && e.contains("declares no operation `helper`")),
        "got {errs:?}"
    );
}

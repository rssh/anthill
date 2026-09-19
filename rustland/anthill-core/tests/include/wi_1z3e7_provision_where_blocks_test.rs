//! WI-20260919-1Z3E7 (proposal 066) — a provision's `:- goals` are in scope exactly for
//! the operations written in its `where` block, and (§7) each provision has a dictionary
//! layout of its own.
//!
//! Before this, every body of a carrier was checked as if every provision's conditions
//! were sort-level `requires` (the per-sort dictionary chain was each body's scope), so
//! an operation that belongs to no provision could read a condition, and the condition
//! then became that operation's requirement, charged to its callers and stated in no
//! definition. MEASURED on CKD4J: `Box3.inner` using `PartialEq[T]` loaded, and
//! `Box3.inner(box3(v: fe(1.5)), …)` was refused naming a requirement of `Box3` nobody
//! wrote. Now a body's chain is its provision's — the sort-level `requires` then that
//! provision's conditions (`provider_dict_entries(sort, provision)`), the sort-level
//! chain alone outside every block — so a condition of another provision is simply not
//! in its scope.
//!
//! ── WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT ──────────────────────────────
//!
//! Laying a carrier out as ONE chain again (every provision's conditions in every body's
//! scope) fails `a_non_member_reading_a_condition_is_a_load_error` and
//! `a_sibling_blocks_condition_is_out_of_scope` — both programs then LOAD — and
//! `each_provision_has_its_own_layout` / `alternative_clauses_hold_when_one_does`, whose
//! controls are stated at their sites. Removing the `where` production from the grammar
//! fails every test here that writes a block (a parse error). PASS EITHER WAY BY DESIGN:
//! `a_helper_with_its_own_requires_needs_no_block` — the repair 066 §1 prescribes for a
//! helper must keep working, block or no block.

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

/// 066 §7.5: a member backs only its own clause, so a `where` block on one of TWO
/// clauses of one spec would leave the other clause without the member. Refused until
/// blocks are instances of their own.
#[test]
fn a_block_on_one_of_two_clauses_of_a_spec_is_refused() {
    let src = r#"
namespace wi1z3e7.twoclauses
  import anthill.prelude.{Bool, Int64, PartialEq, Eq}
  sort Box
    sort T = ?
    entity box(v: T)
    provides PartialEq[Box] :- PartialEq[T] where
      operation eq(a: Box, b: Box) -> Bool =
        match a
          case box(x) -> match b case box(y) -> PartialEq.eq(x, y)
    end
    provides PartialEq[Box] :- Eq[T]
  end
end
"#;
    let errs = refusals(src);
    assert!(
        errs.iter().any(|e| e.contains("provides `anthill.prelude.PartialEq` in 2 clauses")),
        "got {errs:?}"
    );
}

// ── §7: a layout per provision ───────────────────────────────────────────────────

/// Proposal 066 §7.1 — THE LAYOUT IS PER PROVISION. `Pair` has no sort-level
/// `requires`, so its members' frames are exactly their provisions' conditions and an
/// operation outside every block reads nothing. Under WI-869's one chain per carrier
/// every one of these was the same TEN slots. CONTROL: back §7 out (one chain) and the
/// four lengths below all read 10.
#[test]
fn each_provision_has_its_own_layout() {
    use anthill_core::kb::typing::provider_dict_entries;
    let mut kb = crate::common::load_kb_with("namespace wi1z3e7.layout\nend\n");
    let sym = |kb: &anthill_core::kb::KnowledgeBase, qn: &str| {
        kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("{qn} is loaded"))
    };
    let pair = sym(&kb, "anthill.prelude.Pair");
    let partial_eq = sym(&kb, "anthill.prelude.PartialEq");
    let weak_ord = sym(&kb, "anthill.prelude.WeakOrd");
    let lens: Vec<usize> = [None, Some(partial_eq), Some(weak_ord)]
        .into_iter()
        .map(|p| provider_dict_entries(&mut kb, pair, p).len())
        .collect();
    assert_eq!(lens, vec![0, 2, 2], "sort-level / PartialEq block / WeakOrd block");
}

/// Proposal 066 §7 — TWO CLAUSES OF ONE SPEC ARE ALTERNATIVES: the provision holds where
/// EITHER clause's conditions do. `Box[OnlyA]` satisfies the first clause and not the
/// second. CONTROL: under WI-869's one chain both clauses' conditions were strict slots
/// of every `Show` dispatch, so this call was refused for the missing `SB[OnlyA]`.
#[test]
fn alternative_clauses_hold_when_one_does() {
    let src = r#"
namespace wi1z3e7.alt
  import anthill.prelude.{Int64}
  sort Show
    sort T = ?
    operation show(x: T) -> Int64
  end
  sort SA
    sort T = ?
    operation sa(x: T) -> Int64
  end
  sort SB
    sort T = ?
    operation sb(x: T) -> Int64
  end
  sort OnlyA
    entity oa
    provides SA[T = OnlyA]
    operation sa(x: OnlyA) -> Int64 = 1
  end
  sort Neither
    entity ne
  end
  enum Box
    sort A = ?
    entity box(v: A)
    provides Show[T = Box] :- SA[A]
    provides Show[T = Box] :- SB[A]
    operation show(x: Box) -> Int64 = 5
  end
  sort D
    operation viaA(n: Int64) -> Int64 = Show.show(box(v: oa))
  end
end
"#;
    assert_eq!(refusals(src), Vec::<String>::new());
    assert_eq!(eval_int(src, "wi1z3e7.alt.D.viaA"), 5);
    // …and where NEITHER holds the call is still refused.
    let neither = src.replace(
        "    operation viaA(n: Int64) -> Int64 = Show.show(box(v: oa))\n",
        "    operation viaA(n: Int64) -> Int64 = Show.show(box(v: ne))\n",
    );
    let errs = refusals(&neither);
    assert!(
        errs.iter().any(|e| e.contains("wi1z3e7.alt.Show.show")),
        "no alternative holds for `Box[Neither]`; got {errs:?}"
    );
}

/// Proposal 066 §7.4 — a helper calling a MEMBER directly (`Box.eq(a, b)`, or the
/// receiver spelling `a.eq(b)`) gets the member's provision dictionary built at the call,
/// its condition answered by the helper's own `requires`. CONTROL: the same-sort
/// inherit alone (WI-418) hands `Box.eq` the helper's frame, which holds no `PartialEq`
/// condition slot, and the read is unbound at eval. Without the `requires` the call is
/// the ordinary load refusal.
#[test]
fn a_helper_calling_a_member_directly_builds_its_dictionary() {
    let src = r#"
namespace wi1z3e7.direct
  import anthill.prelude.{Bool, Int64, PartialEq}
  sort Box
    sort T = ?
    entity box(v: T)
    provides PartialEq[Box] :- PartialEq[T] where
      operation eq(a: Box, b: Box) -> Bool =
        match a
          case box(x) -> match b case box(y) -> PartialEq.eq(x, y)
    end
    operation same(a: Box, b: Box) -> Bool requires PartialEq[T] = Box.eq(a, b)
    operation dot(a: Box, b: Box) -> Bool requires PartialEq[T] = a.eq(b)
  end
  sort D
    operation sameYes(n: Int64) -> Int64 = if Box.same(box(v: 1), box(v: 1)) then 1 else 0
    operation sameNo(n: Int64) -> Int64 = if Box.same(box(v: 1), box(v: 2)) then 1 else 0
    operation dotYes(n: Int64) -> Int64 = if Box.dot(box(v: 1), box(v: 1)) then 1 else 0
    operation dotNo(n: Int64) -> Int64 = if Box.dot(box(v: 1), box(v: 2)) then 1 else 0
  end
end
"#;
    assert_eq!(refusals(src), Vec::<String>::new());
    assert_eq!(eval_int(src, "wi1z3e7.direct.D.sameYes"), 1);
    assert_eq!(eval_int(src, "wi1z3e7.direct.D.sameNo"), 0);
    assert_eq!(eval_int(src, "wi1z3e7.direct.D.dotYes"), 1);
    assert_eq!(eval_int(src, "wi1z3e7.direct.D.dotNo"), 0);
    let bare = src
        .replace(
            "operation same(a: Box, b: Box) -> Bool requires PartialEq[T] =",
            "operation same(a: Box, b: Box) -> Bool =",
        )
        .replace(
            "    operation dot(a: Box, b: Box) -> Bool requires PartialEq[T] = a.eq(b)\n",
            "",
        )
        .replace("    operation dotYes(n: Int64) -> Int64 = if Box.dot(box(v: 1), box(v: 1)) then 1 else 0\n", "")
        .replace("    operation dotNo(n: Int64) -> Int64 = if Box.dot(box(v: 1), box(v: 2)) then 1 else 0\n", "");
    let errs = refusals(&bare);
    assert!(
        errs.iter().any(|e| e.contains("`wi1z3e7.direct.Box.same` calls `wi1z3e7.direct.Box.eq`")
            && e.contains("or give it its own `requires PartialEq[…]`")),
        "with no `PartialEq[T]` in scope the member's condition cannot be supplied, and \
         the refusal names the helper's repair; got {errs:?}"
    );
}

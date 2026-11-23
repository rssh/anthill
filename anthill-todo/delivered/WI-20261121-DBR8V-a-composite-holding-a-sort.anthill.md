## Attributes

- id: WI-20261121-DBR8V-a-composite-holding-a-sort
- created: 2026-11-21T18:00:42Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-23T15:38:26Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A COMPOSITE HOLDING A SORT WHOSE EQUALITY IS A WITNESS'S DERIVES NO EQUALITY, so a comparison of two of its values is refused at the call (filed with the user 2026-11-21, beside WI-20261121-TV0PA). kernel-language.md, Closed by the load: the load "derives the same for every composite holding it". MEASURED after TV0PA:

  sort C { entity c(v: Int64) }
  sort D { entity d(c: C) }
  sort W { provides Eq[T = C]; operation eq(x: C, y: C) -> Bool = true }
  operation main() -> Bool = eq(d(c: c(v: 1)), d(c: c(v: 2)))

is refused at the call, "`D` provides no `PartialEq`"; the expected answer is true (D's derived eq compares field `c` through W.eq). The same with `W provides PartialEq[T = C]` was refused before TV0PA too; with `Eq` it used to load and answer false, C deriving its own structural equality and W ignored (the defect TV0PA fixed, which is what moved this case). CAUSE: eq_derive's Total half (total_composites, `provides_eq` = sort_provides(field, Eq)) and conditional half (field_conditions, `sort_provides(head, spec)` + provision_conditions(head)) read a field's equality from provisions filed under the field's own sort; a witness's row is filed under the witness. TO DO: (a) both halves read an UNCONDITIONAL witness provision about the field's sort (typing::provisions_about) as deciding it, with no condition; (b) the classifier's Float boundary (is_eq_boundary over EqDispatchIndex, built before derive_forwarded_provisions) sees an Eq-only witness's eq — else `d(c: C)` with C holding a Float classifies Partial and derives NonEq although W makes C lawful; (c) a CONDITIONAL parametric witness (`W2 provides Eq[T = Box[T = A]] :- Eq[T = A]`) — translate its condition into the holder's parameters, or leave the field undecided (refused at the call) and say so. ACCEPTANCE: the program above answers true; the PartialEq-witness variant answers true; the Float-field variant derives Eq (not NonEq) for D; the conditional parametric case decided per (c), each back-out measured; full workspace green; scaland testFull.

## Changes

### 2026-11-23T15:38:24Z — feedback — user

Delivered (closed with the user 2026-11-23) in 41ebd5c5b. (a) both halves of the derivation read a witness's provision at a field's sort (EqualityProvisions::witnessed): the ticket's program and the PartialEq-witness variant answer true. (b) the cause was the pass order, not the index: W.eq was judged at W alone and filed as supplying nothing, the forwarded PartialEq row being written below the classifier; the forwarding of the written rows now runs before the first sort-operations table, and the Float-field variant derives Eq and PartialEq for D, no NonEq. (c) a conditional parametric witness is translated through its binding (witness_needs): Box[T = X] needs Eq[X] (Int64 answers, Float is refused naming Eq[Float]); a witness at one application, a condition over a parameter its binding does not name, or one provider writing the spec at several carriers under a condition, leaves the holder undecided and refused at the call — kernel-language 8.3's sentence, approved by the user. The NonEq mirror gives no clause at a parameter whose Eq the holder's PartialEq needs (a Set[T = T] field's holder included). Rows: wi_dbr8v_witnessed_field_test (8), each back-out measured. /code-review (high): 5 findings, 1 fixed, 2 not needed, 2 skipped (the call-site refusal does not name the unread witness; the extra per-load reads are untimed). Gate 12636 / 0; families green; scaland testFull 811 + 51 (2 skipped) + 1.


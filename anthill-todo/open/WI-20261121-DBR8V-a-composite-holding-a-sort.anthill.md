## Attributes

- id: WI-20261121-DBR8V-a-composite-holding-a-sort
- created: 2026-11-21T18:00:42Z

- status: Open
- status_agent: user
- status_at: 2026-11-21T18:00:42Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A COMPOSITE HOLDING A SORT WHOSE EQUALITY IS A WITNESS'S DERIVES NO EQUALITY, so a comparison of two of its values is refused at the call (filed with the user 2026-11-21, beside WI-20261121-TV0PA). kernel-language.md, Closed by the load: the load "derives the same for every composite holding it". MEASURED after TV0PA:

  sort C { entity c(v: Int64) }
  sort D { entity d(c: C) }
  sort W { provides Eq[T = C]; operation eq(x: C, y: C) -> Bool = true }
  operation main() -> Bool = eq(d(c: c(v: 1)), d(c: c(v: 2)))

is refused at the call, "`D` provides no `PartialEq`"; the expected answer is true (D's derived eq compares field `c` through W.eq). The same with `W provides PartialEq[T = C]` was refused before TV0PA too; with `Eq` it used to load and answer false, C deriving its own structural equality and W ignored (the defect TV0PA fixed, which is what moved this case). CAUSE: eq_derive's Total half (total_composites, `provides_eq` = sort_provides(field, Eq)) and conditional half (field_conditions, `sort_provides(head, spec)` + provision_conditions(head)) read a field's equality from provisions filed under the field's own sort; a witness's row is filed under the witness. TO DO: (a) both halves read an UNCONDITIONAL witness provision about the field's sort (typing::provisions_about) as deciding it, with no condition; (b) the classifier's Float boundary (is_eq_boundary over EqDispatchIndex, built before derive_forwarded_provisions) sees an Eq-only witness's eq — else `d(c: C)` with C holding a Float classifies Partial and derives NonEq although W makes C lawful; (c) a CONDITIONAL parametric witness (`W2 provides Eq[T = Box[T = A]] :- Eq[T = A]`) — translate its condition into the holder's parameters, or leave the field undecided (refused at the call) and say so. ACCEPTANCE: the program above answers true; the PartialEq-witness variant answers true; the Float-field variant derives Eq (not NonEq) for D; the conditional parametric case decided per (c), each back-out measured; full workspace green; scaland testFull.


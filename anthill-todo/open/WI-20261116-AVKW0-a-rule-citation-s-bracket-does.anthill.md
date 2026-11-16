## Attributes

- id: WI-20261116-AVKW0-a-rule-citation-s-bracket-does
- created: 2026-11-16T10:13:00Z

- status: Open
- status_agent: claude
- status_at: 2026-11-16T10:13:00Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A RULE CITATION'S BRACKET DOES NOT SELECT A SORT'S NAMED REQUIREMENT. 060.1 §8.2 decided (2026-11-04) that a sort's named requirement slot is filled only by what the citation writes, for an operation and a rule alike. PROGRAM: sort Mon { sort T = ?  operation op(x: T) -> Int64 }, sort Sum and sort Product each providing Mon[T = Int64] (op = 1 and 2), sort Semi1 { sort T = ?  requires Plus: Mon[T = T]  rule d(?x: T, ?r) :- Mon.op(?x, ?r) }, rule directSum(?r) :- Semi1[T = Int64, Plus = Sum].d(1, ?r), rule directProduct(?r) :- Semi1[T = Int64, Plus = Product].d(1, ?r). MEASURED on 7c63d768: refused at load, 'requirement Mon[T = Int64] of Semi1 cannot be supplied for the citation of Semi1.d; constructing Mon[T = Int64] is ambiguous among providers: Sum, Product'. The citation builds the clause's read from the provisions at Int64 and never reads `Plus = Sum` from its bracket. Calling through the name in the rule body (Plus.op(?x, ?r)) is refused as naming nothing. The read WI-20261105-CBRD2 hands a goal of another clause of the sort (its sort's requirement) carries no name either. WANTED: directSum answers 1 and directProduct 2; a citation writing neither name is refused naming the slot, as an operation's citation is. ACCEPTANCE: rows driving both citations, the citation that names no slot, and a goal of another clause of the sort (rule s(?x: T, ?r) :- keepMon(?x, ?r) over rule keepMon[A](?x: A, ?r) :- Mon[A], Mon.op(?x, ?r)); full workspace green via rustland/scripts/test.sh.


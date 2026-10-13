## Attributes

- id: WI-20261013-M32C2-a-list-literal-at-a-position
- created: 2026-10-13T08:03:56Z

- status: Open
- status_agent: claude
- status_at: 2026-10-13T08:03:56Z

- acceptance: cargo-test

- tags: typing

## Description

A LIST LITERAL AT A POSITION TYPED AT A SORT ITS ELEMENTS PROVIDE IS REFUSED WHERE THE ELEMENTS ARE OF TWO PROVIDERS — the literal joins its elements without reading the type the position expects. Measured 2026-10-13 on 34b21d28 with WI-20261003-4DYR6's change, and the same on 34b21d28 itself for the sort with a type parameter; found while delivering that ticket.

THE PROGRAM. `sort Sp { operation size(s: Sp) -> Int64 }`, `sort Car { entity car(n: Int64); provides Sp; operation size(c: Car) -> Int64 = 40 }`, `sort Van { entity van(n: Int64); provides Sp; operation size(c: Van) -> Int64 = 2 }`, `operation total(xs: List[T = Sp]) -> Int64 = List.foldLeft(xs, 0, lambda (acc, c) -> acc + Sp.size(c))`: `total([car(n: 1), van(n: 2)])` is a load error, 'type mismatch in list.element 2 (collection-element-join): expected Car, got Van'. The same with `sort T = ?` in `Sp` and `provides Sp[T = Int64]`.

WHAT LOADS. `operation both(a: Sp, b: Sp) -> List[T = Sp] = [a, b]` with `total(both(car(n: 1), van(n: 2)))`, which answers 42; a literal of one provider's values.

WHAT. The literal's element type is the join of its elements, taken before the position is read. Where the position expects `List[T = Sp]` and each element is admissible at `Sp`, the element type is the position's. Decide which holds — the expected type is read before the join, or the join of two providers of one sort is that sort where a position asks for it — and say so in kernel-language §4.6 (collection literals) and §8.1.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; driven): the program answers 42 for both spellings of `Sp`; a literal whose elements have no common type at the position is still refused, naming the position's type; a literal with no expected type joins as it does today.


## Attributes

- id: WI-20261013-M32C2-a-list-literal-at-a-position
- created: 2026-10-13T08:03:56Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-14T18:00:30Z

- acceptance: cargo-test

- tags: typing

## Description

A LIST LITERAL AT A POSITION TYPED AT A SORT ITS ELEMENTS PROVIDE IS REFUSED WHERE THE ELEMENTS ARE OF TWO PROVIDERS — the literal joins its elements without reading the type the position expects. Measured 2026-10-13 on 34b21d28 with WI-20261003-4DYR6's change, and the same on 34b21d28 itself for the sort with a type parameter; found while delivering that ticket.

THE PROGRAM. `sort Sp { operation size(s: Sp) -> Int64 }`, `sort Car { entity car(n: Int64); provides Sp; operation size(c: Car) -> Int64 = 40 }`, `sort Van { entity van(n: Int64); provides Sp; operation size(c: Van) -> Int64 = 2 }`, `operation total(xs: List[T = Sp]) -> Int64 = List.foldLeft(xs, 0, lambda (acc, c) -> acc + Sp.size(c))`: `total([car(n: 1), van(n: 2)])` is a load error, 'type mismatch in list.element 2 (collection-element-join): expected Car, got Van'. The same with `sort T = ?` in `Sp` and `provides Sp[T = Int64]`.

WHAT LOADS. `operation both(a: Sp, b: Sp) -> List[T = Sp] = [a, b]` with `total(both(car(n: 1), van(n: 2)))`, which answers 42; a literal of one provider's values.

WHAT. The literal's element type is the join of its elements, taken before the position is read. Where the position expects `List[T = Sp]` and each element is admissible at `Sp`, the element type is the position's. Decide which holds — the expected type is read before the join, or the join of two providers of one sort is that sort where a position asks for it — and say so in kernel-language §4.6 (collection literals) and §8.1.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; driven): the program answers 42 for both spellings of `Sp`; a literal whose elements have no common type at the position is still refused, naming the position's type; a literal with no expected type joins as it does today.

## Changes

### 2026-10-14T18:00:27Z — feedback — user

DELIVERED in 910b2fa1. Decided with the user 2026-10-14: the slot's type first. An argument or field slot whose element type holds no parameter the call instantiates declares it, as a return and an annotated let do, and each element is checked against it: the ticket's program answers 42 for both spellings of Sp; total([car(n: 1), 5]) is refused at the element, 'expected Sp, got Int64'; a literal at no expected type (an unannotated let) joins as before. The slot is read as the call has it (cnt[A = Sp]([...]), List.append[T = Sp](ss, [...]), Box[V = Sp].box(xs: [...]) declare); a WRITTEN parameter the call instantiates (the callee's [A], its sort's T, a construction's V) leaves the literal to its join, so cnt([car, van]) and box(xs: [car, van]) at a declared Box[V = Sp] are refused. An UNWRITTEN one is no parameter (user: 'When variable is not written - we can't reference it'): List[T = Sp] and List[T = Sp[T = ?]] check each element on its own, so providers at different T fill one list; List[T = Sp[T = X]] over the operation's own [X] is one X. Also delivered: a call of an arrow-typed variable takes every slot hint a named call takes (f(red(v: 1)) at (c: Colour.red) was refused); from /code-review, a construction in an argument is expected at the slot's type where that reaches a variant field (takeBox(box(x: red(v: 1))) was refused), and a literal of variants in a parametric field reads the expected instance. kernel-language 4.6, 8.1, 8.2. Rows: wi_m32c2_list_literal_at_a_slot_test (16), eight back-outs measured. Full workspace 9,864 passed, 0 failed; wi_tests under the node carrier 7,226; families green both ways; scaland testFull 688 + 45 + 1.


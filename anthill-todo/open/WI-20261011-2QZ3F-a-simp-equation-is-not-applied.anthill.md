## Attributes

- id: WI-20261011-2QZ3F-a-simp-equation-is-not-applied
- created: 2026-10-11T12:18:53Z

- status: Open
- status_agent: claude
- status_at: 2026-10-11T12:18:53Z

- acceptance: cargo-test

- tags: typing

## Description

A `@[simp]` EQUATION IS NOT APPLIED IN A `const`'S VALUE: THE CALL IT DEFINES LOADS CLEAN THERE AND DIES AT THE CONST'S FIRST USE. Measured 2026-10-11 on a2ab1619; found while delivering WI-20261011-12VZB, on the row that runs one call at every site an operation body writes one.

THE PROGRAM. `operation dbl(n: Int64) -> Int64`, `rule dbl(?n) <=> ?n + ?n @[simp]`, `const c: Int64 = dbl(4)`. The load is clean. A read of `c` dies `OperationBodyMissing`, "operation has no body: test.k.dbl". `operation go() -> Int64 = dbl(4)` in the same file runs to 8, and so does the call in an `if` condition, under a lambda, in a match arm and, since a2ab1619, in a match guard. `const c: Int64 = three() + dbl(4)` over a bodied `three() = 3` dies the same way; `const c: Int64 = three() + 1` is 4. A program that never reads `c` runs to its end: the value is folded at first demand (kernel-language.md §5.9), so nothing is said until then.

MECHANISM. `typing/sorts.rs` `check_constant_bodies` types the initializer with `type_check_node_gated(kb, &env, &body, Some(expected), false, &[])` — equations off, no rule ids — and drops the node the check returns: "Keep this validation on the stored source, without simp write-back" (WI-20261006-HK87X, 2bf3a2f7). The evaluator then runs the initializer as written.

THE NEIGHBOUR THAT IS REFUSED. `operation four() -> Int64` with `rule four(4) :- true` and `const c: Int64 = four()` is a load error since WI-20261011-CR6GD, "defined by clauses alone" (`wi_cr6gd_clause_defined_call_test::a_call_in_a_const_is_refused`). So a const's value is already judged for an operation a call can run. The equation-defined operation passes that judgement because its equation is what a call runs — everywhere but here.

WHAT, and a decision comes first. §5.3 names the firing sites — the resolver's rewriter, the typer's operation-body pass, the dot-rule pass — and says every one answers alike; it does not say whether a const's value is one. (a) It is: the initializer is typed with equations on and the typed node is what is stored, as an operation body is. Owed with it: the seal, where a later load's rule that rewrites a sealed const's value is refused (`kb/typing/sealed.rs`), and a reading of what HK87X kept away — "No runtime requirement frame belongs to a constant initializer", which a right-hand side that calls a spec operation may want. (b) It is not: the call is refused where it is written, as the clause-defined one is, naming the equation and the repair. Either ends the clean load of a program that cannot run; the spec gains the sentence for whichever is taken.

NOT THIS TICKET. A dot call in a const's value is refused as non-foldable, "method/dot call" — the purity gate of §5.9, its own rule. A computed const in a clause's data slot is refused (WI-20261001-KDMQS). A const reference in goal position is WI-20260822-NDG34.

CONTROL. Under (a) `c` reads 8 and the `three() + dbl(4)` const reads 11, each dying on the tree before; a later load's rule over a call in a sealed const's value is refused, and loads clean before. Under (b) both consts are load errors naming `dbl`, each loading clean before. Passing either way by design: the const over a bodied operation (4), the same call in an operation body (8), the clause-defined const's refusal, and a const that names another const.


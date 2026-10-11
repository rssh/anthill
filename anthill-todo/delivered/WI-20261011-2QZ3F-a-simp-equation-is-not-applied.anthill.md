## Attributes

- id: WI-20261011-2QZ3F-a-simp-equation-is-not-applied
- created: 2026-10-11T12:18:53Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-11T13:44:41Z

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

## Changes

### 2026-10-11T13:44:35Z — feedback — claude

DELIVERED 2026-10-11 — A CONST'S VALUE IS TYPED AS AN OPERATION BODY IS, AND THE TYPED VALUE IS WHAT IS KEPT (commit cdb2dca9). The ticket's programs run: const c: Int64 = dbl(4) reads 8 and const c: Int64 = three() + dbl(4) reads 11.

THE DECISIONS, the user's, 2026-10-11, asked with the programs measured on e45f3ee7 and on a two-line prototype. (1) Reading (a): a const's value is a firing site, typed with the equations applied and stored as typed, as an operation body is. (2) The purity gate judges the value as typed, not as written: a dot call that dispatches to an operation with no effects is admitted (const c: Int64 = Box.mk(4).open() reads 4; it was refused, 'method/dot call'), and one that dispatches to an effectful operation is refused by that operation's name.

WHAT CHANGED. typing/sorts.rs check_constant_bodies types each value under the same @[simp] gate an operation body has and writes the typed node back (KnowledgeBase::set_const_body_node); the evaluator, the purity gate (load.rs check_const_purity) and the C++ generator read that node. The const sweep runs before the seal's refusal and skips a sealed load's values (constant_values_by_seal). A const is a sealed load's by the source its value was WRITTEN in, NodeOccurrence::written_site: an equation that rewrites a value at its top leaves its right-hand side as the root, and that node's span is in the rule's file. typing/sealed.rs asks operation bodies and const values alike (SealedBody): a later load's rule that rewrites or breaks a sealed const's value is refused, 'rewrites the value of const …', and ANTHILL_TYPER_ORACLE=1 types sealed values too.

WHAT WAS WORSE THAN THE TICKET SAID. Beside a bodied operation with a guarded equation nothing died: operation dbl(n) = n + n, rule dbl(?n) = 0 :- lt(?n, 0) @[simp], const c: Int64 = dbl(-1) read -2 where the same call in an operation body read 0. And the C++ generator refused the header of a const over an equation-defined call ('has no body and no C++ realization'); it lowers inline constexpr int64_t EIGHT = (4 + 4) now.

FOUND BY THE REVIEW AND FIXED IN THE SAME COMMIT. (1) A const's value was not held to the refusals written for an operation body, which asked env.enclosing_op().is_some(): a body-less spec operation at a carrier that provides no such spec loaded clean in a const and died at its first read, and a defaulted one ran the default for a carrier that is no instance, or whose conditional provision is unmet. The three gates ask TypingEnv::in_evaluated_body now, and the const is refused in the words the operation body is. On e45f3ee7 as well: not this ticket's cause, the same death. (2) The gate reads typed values, which can hold a value a compile-time macro spliced: Expr::Spliced is a pure leaf, so const thirty: Relation[…] = person_row.where(lambda c -> eq(c.age, 30)) loads and drains to 2. (3) A value the typer refuses is still as written when the gate reads it, and the gate added 'method/dot call … use an operation' about a dot that dispatches once the value types. A standing dot is the gate's to tell only when the load has told nothing else. (4) One reader of the @[simp] gate for the three drivers that type a body (typing/expr.rs simp_gate). Ten findings, ten fixed.

CONTROLS, each measured by back-out; the headers of wi_2qz3f_const_value_equation_test and of section (1b) of wi_9bkz4_sealed_bodies_test have the lists. Equations off in the sweep: 14 rows of the first file and 3 of the second fail. The write-back out: 16 and 3. The sweep typing sealed values again, or the refusal asking no const: the two refused rows. The refusal made without typing: the row that keeps it exact. The seal read off the stored root's own span: the third load of a_programs_const_rewritten_by_a_sealed_equation_stays_the_programs is refused for a const no seal holds. in_evaluated_body for an operation alone: three rows load clean. The gate telling a standing dot whatever else was told: two rows; never telling one: one row, which under the oracle asserts the oracle's finding and fails with oracle_type_sealed_constants not called. The Spliced leaf out: the relation row. The C++ row fails with the write-back out, on the message above.

SPEC, edited on the user's two answers. kernel-language.md §5.3 says a const's value is typed as an operation body is and gives the two programs; §5.9 says the typed value is what is folded, judged by the gate and lowered, what the gate does with a dot call and with a macro's value, and that a call is refused where the same call in an operation body is; §8.3's sealed-bodies rule names const values.

NOT COVERED, each the same in an operation body: a bare reference const c: Int64 = tau to a nullary operation an equation defines is not a redex; an equation does not see through a binding. SEEN ON THE WAY AND NOT CHANGED, both on e45f3ee7 as well, put to the user: a const declared twice loads clean and the second replaces the first — WI-1049's note lists const+const as not refused, with the distinctness domain an open question — and behind the seal a program that declares anthill.cli.help.NAME_COLUMN again loads clean; a const written dotted in an operation body (S.c, Float.infinity) does not resolve, 'expected resolved name, got unresolved'.

RUNS. Full workspace on cdb2dca9: 36 binaries, 9222 passed, 0 failed; on the merge with origin/main (275746a0, A3NND beside it): 9240 passed, 0 failed. anthill-core under ANTHILL_TEST_TWO_STEP_LOAD=1 and ANTHILL_TEST_FRESH_LOAD=1 on cdb2dca9's tree: 8323 passed, 0 failed, each. Under ANTHILL_TYPER_ORACLE=1 that tree stopped on one row, the standing dot behind a seal — the oracle's own finding, 'typing a sealed constant's value again reported' — and the row asserts that finding under the oracle since; on the merge: 8341 passed, 0 failed. /code-review run.


## Attributes

- id: WI-20261008-A3FY2-in-a-rule-body-a-parenthesized
- created: 2026-10-08T09:06:20Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-12T06:10:13Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-055

## Description

IN A RULE BODY A PARENTHESIZED TYPE RECEIVER IS REFUSED WITH AN UNRESOLVED-NAME MESSAGE — `rule r(?x) :- ?x <=> (Box).tag()` fails with "type mismatch in Box.name: expected resolved name, got unresolved", and `(Box[V = Int64]).tag()` with the same about `Int64`, while `?x <=> Box.tag()` and `?x <=> Box[V = Int64].tag()` bind 7. In an operation body all four answer 7. Measured 2026-10-08 on fd1cf282.

WHY. Since WI-20260824-PAPX0 a parenthesized receiver is a value receiver (`is_value_receiver`, parse/convert.rs), so the rule-body lowering gets a `dot_apply` whose receiver is a sort name. An operation body classifies that name as a type value and the typer's `denoted_sort_dot` answers; the rule-body walk does neither. Before PAPX0 the receiver was dropped and the program was refused as well, so the verdict did not change. The message is not about what is wrong.

WHAT. Give the rule body the operation body's reading — the dot is the written companion call — or refuse in a sentence that names the parenthesized type receiver and the spelling that works. Umbrella A (WI-20260823-ZF3AK) carries the type-value classification through operation expressions; check whether a rule-body classification is already planned before building one here.

CONTROL. `(Box).tag()` and `(Box[V = Int64]).tag()` in a rule body beside their unparenthesized spellings, resolved and the binding asserted (or the refusal's distinguishing words). Say which rows fail with the change backed out.

DONE WHEN: a rule body answers the parenthesized spelling as it answers the written one, or refuses it in words about the receiver; the gate is green.

## Changes

### 2026-10-12T06:10:07Z — feedback — claude

DELIVERED 2026-10-12, 7c82a84b. A rule body answers the parenthesized spelling as it answers the written one: `rule r(?x) :- ?x <=> (Box).tag()` and `?x <=> (Box[V = Int64]).tag()` bind 7. WHICH READING: the operation body's, the first of the two the Description offers; kernel-language §5.4 states the rule for every body, and the spec had it before the code did. THE PLANNED CLASSIFICATION the Description asks about is umbrella B (WI-20260823-53W12), for every rule-body occurrence; this ticket classifies the receiver of a dot only and leaves the rest to it. HOW, two steps. (1) Loader: `dot_apply_expr` hands a receiver written as a type — a bare sort name, or a bracket on a sort — to the walk that builds an operation body (`Loader::written_type_receiver_occurrence`), so it is the `Expr::TypeValue` it is there. (2) Typer: `type_rule_bodies` replaces every such dot in the rule's own term by the call its written spelling makes (`written_type_dots_as_calls`, through PAPX0's member resolution), before the variable types are collected and before the dispatch walk, so the two spellings are one node. STEP 2 CAME FROM /code-review of the first cut, which left the dot to the dispatch walk. The walk reads a dot and a written call differently, and three programs had two verdicts: `?z <=> (Hold).keep(?c), ?x <=> ?c.bump()` bound `cnt(n: 4).bump` where the written call answers 5 (the call's parameter types `?c`; a dot's does not); `(Hold).take("s")` was refused where `Hold.take("s")` loads; `(Hold).open(4)`, over an operation an equation defines, answered 4 where the written call keeps a residual. My fixture sort was parametric, where a written call is checked too, so its rows had agreed. ONE REFUSAL: a constructor reached through such a receiver in a rule body's own term, with its qualified name as the spelling to write — the written name leaves an omitted field open and the call the dot makes did not, so `holds((Sh).pt(1))` answered nothing where `holds(Sh.pt(1))` answers. Under a compound expression, and where an equation carries the dot into an operation body, it constructs. kernel-language §5.4 has the sentence (user, 2026-10-12). MEASURED AND NOT CHANGED: (a) a sort named by a dotted path, `(Outer.Inner).deep()` or `(ns.Box).tag()`, is refused with the unresolved-name message in an operation body as well — a dotted sort name is no type value there (`nm(Outer.Inner)` and `let t = Outer.Inner` are refused the same way), so the rule body follows; a row pins it, and a bracket on the path is read in both bodies. (b) An equation's right-hand side is read where it is spliced: typed in an operation body, left as written where the resolver splices it under `simplify`; a value dot there has the same gap. (c) A refused dot leaves its rule untyped for the run, so a second error in that rule shows after the first is repaired. (d) A rule of the sort reached so, `(Box).rows(?x)`, is refused as PAPX0's rule has it (operations and constructors only) — R653S's question has that row in a rule body too. (e) A structural type in the bracket, `(Box[V = (Int64) -> Int64]).tag()`, is refused in both bodies where the written call answers. (f) A constraint's body and a contract expression are terms, not rule bodies, and are not reached. ROWS: `wi_a3fy2_rule_body_type_receiver_test`, 14, one fixture per row. BACK-OUTS, each measured against the module: the loader's receiver (11 rows fail, on the unresolved-name refusal); the replacement before the body is read (`both_spellings_are_one_call_to_every_reader`); the constructor refusal (`a_constructor_in_a_rule_body_is_written_by_its_name`); that refusal asked of every rule-body text (`a_constructor_under_a_compound_expression_is_the_operation_bodys`). ACCEPTANCE: rustland/scripts/test.sh, 36 suites, 9354 passed, 0 failed, 14 ignored, on a26210f3 with the change; the module also under ANTHILL_TEST_FRESH_LOAD, ANTHILL_TEST_TWO_STEP_LOAD and ANTHILL_TEST_NODE_CARRIER; sbt testFull 634 passed, 0 failed (no Scala or stdlib file changed). FOUND ON THE WAY, rows on WI-20260926-7D48J (a dot on a rule variable whose type nothing determines is never evaluated) and WI-20260926-DSEXA (a query pattern does not evaluate a nullary call).


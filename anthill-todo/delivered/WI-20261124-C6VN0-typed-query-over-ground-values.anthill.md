## Attributes

- id: WI-20261124-C6VN0-typed-query-over-ground-values
- created: 2026-11-24T06:15:07Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-24T09:30:50Z

- acceptance: cargo-test

## Description

Typed query over ground values: an = between two empty lists is refused (no element type for nil)
WHO NEEDS IT. anthill-traces (its WI-20261122-FHMJ4, the check command) decides an operation's requires / ensures on recorded values. It builds each clause's goals term to term: a parameter, result and a field access over a record value are replaced by the value terms (route A of its design, §4.4), and the goals go to execute_typed_logical_query_with (WI-20261122-96QKW) as one LogicalQuery, which the typer types from the values.
WHAT HAPPENS. MEASURED 2026-11-24 on bba37887f, through anthill-traces. An operation op(xs: List[Int64], ys: List[Int64]) with requires (xs = ys), given xs = ys = [] (each decoded at List[Int64] by persistence::term_ser::decode_value, so the term nil): the query PartialEq.eq(nil, nil) is refused, LowerError::QueryRefused "type mismatch in anthill.prelude.PartialEq.eq.dispatch: expected matching impl for per-call bindings, got no impl matches — unresolved: anthill.prelude.PartialEq[T = anthill.prelude.List.T] (no impl provides anthill.prelude.PartialEq; …)". Given [1] and [1], the same clause types and holds. The same for a field: requires (a.items = b.items) over two records whose items: List[Int64] are both empty is refused, and decided when they are not. The element type is in the declaration — xs: List[Int64], the field items: List[Int64] — and is lost when the value term takes the expression's place: nil carries none.
WHY IT MATTERS. A frame clause written s.items = result.items, the common way to say an operation leaves a part of a record state unchanged, is undecided whenever that list is empty — in a state with no entity of that kind yet, which is where a trace of a system usually begins. anthill-traces reports such a clause undecided, never as holding, and its fixtures avoid empty lists to stay decidable.
WHAT WAS TRIED (read from code, 2026-11-24): a call-site type argument in the clause, PartialEq.eq[T = List[Int64]](xs, ys), is refused at load ("call-site type arguments PartialEq.eq[…](…) are not supported here"); LogicalQuery (reflect.anthill) has no typed variable or ascription a query could carry the type in. A grep for 'ascri' in kernel-language.md and reflect.anthill found only the refusal of a typed column on a declaration; among the Expr constructors of reflect.anthill none is an ascription a goal could be written with (a let's type annotation is on the let).
WHAT IS ASKED. A way for a caller of execute_typed_logical_query_with (and of refute_typed_logical_query_with, WI-20261123-5MMGP, which types the same way) to give the declared type of a ground value it puts in a goal, so that the typer types the goal at that type: e.g. a typed pattern / ascription node in LogicalQuery, or a typed variable bound to the value by a goal. The shape is anthill's to choose. WI-20261122-3QJ36 (typed, substituted contract goals) would cover this case as well; this item is the narrower piece a term-to-term caller needs meanwhile.
WHAT IS NOT ASKED. A default for an element type nobody gives: a bare PartialEq.eq(nil, nil) with no declared type may stay refused.
DONE WHEN. Rows driven from outside the crate, through the typed execute:
(1) PartialEq.eq(nil, nil), the operands declared List[Int64]: holds;
(2) PartialEq.eq(nil, [1]), declared List[Int64]: no solution, complete (violated);
(3) an operand of a sort with its own eq, declared at that sort: that sort's eq decides, not the structure (the control that the declared type, not the value, picks the equality);
(4) a declared type that does not fit the value: refused (QueryRefused), not ignored;
(5) the control: the same queries with no declared type type and answer as before.

## Changes

### 2026-11-24T09:30:36Z — feedback — claude

Delivered in 8b0f58bcd. Shape decided with the user 2026-11-24: route B, a query's typed variable types its variable (kernel-language 5.3 already said it reads as a rule head's, which the implementation did not do: the written PartialEq.eq(?xs: List[Int64], ?ys: List[Int64]) was refused, the variable getting a guard only), and a LogicalQuery value writes one with typed_query(var: ?x, type: T, query: q), which is ?x: T written in q (proposal 010.1 Q2, answered for a typed variable). A caller keeps a variable where an expression stood, declares it at the expression's declared type (an OperationInfo parameter's type_name, a field's type) and binds it, ?xs <=> nil. Rows driven from outside the crate through execute_typed_logical_query_with and refute_typed_logical_query_with (anthill-core/tests/include/wi_c6vn0_typed_query_variable_value_test.rs): (1) nil, nil declared List[Int64]: holds, Answered; (2) nil, [1]: no answer, Refuted (complete); (3) pt(1, 2), pt(1, 9) declared Pt: Pt's own eq holds them equal, === refutes (a Pt value names its sort, so the declaration and the value agree there); (4) ["a"] declared List[Int64]: QueryRefused naming ?xs; a var that is no variable: LowerError::TypedQueryNotAVariable; the untyped execute_logical_query: LowerError::TypedQueryUntyped; (5) undeclared: as before (nil/nil refused, [1]/[1] holds). Also: a typed_query under negation or in a branch types that goal alone; two types for one variable where they meet are refused. Agreed with the user: a rule-head argument that does not fit its bound (same(nil, ["a"]) refuted at run time, not refused) stays out of scope; the bare nil = [1] (refused in any body, [1] = nil loads) was sized large and filed as WI-20261124-V260E. Found on the way and fixed in the same commit: SubstTree::skip_subtree_then_continue recursed once per stored node; one more LogicalQuery constructor took wi_jee0e's no_premise_search past the 2 MiB test thread. Gate 12690 / 0; families green on both carriers; scaland testFull 811 + 51 (2 skipped) + 1.


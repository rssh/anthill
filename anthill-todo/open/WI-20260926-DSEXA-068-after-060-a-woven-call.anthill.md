## Attributes

- id: WI-20260926-DSEXA-068-after-060-a-woven-call
- created: 2026-09-26T09:54:11Z

- status: Open
- status_agent: user
- status_at: 2026-09-26T09:54:11Z

- acceptance: cargo-test

- depends_on: WI-20260926-K4JGC-an-operation-call-in-a-rule, WI-20261013-GFS6A-068-d1a-a-woven-call-is, WI-20261013-DEY66-068-d1b-the-per-consumer, WI-20261013-2HX69-068-d1c-the-unfold-threads, WI-20261013-WPVVY-a-labelled-call-of-a-builtin, WI-20260911-5G28A-rule-head-type-variables-open

- tags: proposal-068

## Description

068 AFTER 060: A WOVEN CALL WAITING FOR ITS DICTIONARY IS SUSPENDED ON IT; THE PER-CONSUMER REDUCTIONS RETIRE; THE WI-580 UNFOLD THREADS DICTIONARIES. Step D1 of the 068/060 sequence — the part of proposal 068 that needs 060's requirement channel.

 1. DICTIONARY BLOCKERS (068 §2.1). A call woven by P7VP4 as `apply_within(fn, args, requirements = [?d])` is SUSPENDED with `?d` among its blockers (WI-20260926-CYNPE's mechanism): typing created `?d` and the goal that may bind it, so the blocker is read off the call, not discovered. A dictionary that turns CONCRETE with no supplier for the member makes the call UNREDUCED — parked, never retried, a NAMED residual cause (WI-20260923-KCNA0's acceptance at run time).
 2. RETIRE THE PER-CONSUMER REDUCTIONS (068 §8 step 3): `reduce_op_value`'s call-by-name fold, `body_specialize`'s reducer and `unify_values`' evaluate-on-reach become WI-20260926-K4JGC's walker. Goal arguments are evaluated before the head match, so `unify_match_values` stays structural.
 3. THE UNFOLD (068 §8 step 4): `unfold_eq_operand` reads OTHER through WI-20260926-K4JGC's strategy and threads dictionaries as clause conditions (as P7VP4 does for rule-body calls) instead of declining every operation with `requires`; WI-20260827-XBHX3's gate goes. XBHX3's rows: `C.bpick(?c) = box(v: C.tag(red()))` answers `?c = red` definite; `C.pick(?c) = C.mk(red())` (custom `Eq`, WI-20260827-P1TPE) is never a wrong refutation; `append(?a, [3]) = append(?b, [4])` terminates.
 4. kernel-language §5.3 ("what the gate still declines") and §8.1's rule-body typing sentence.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven, back-out stated at its site): a woven call whose dictionary is bound only by a LATER goal answers once it is bound, and conditionally if never; KCNA0's rows name their cause; XBHX3's three rows as above; no consumer reduces an operand by its own path (the retired functions are gone, not bypassed). CONTROLS: P7VP4's and SHED7's rows unchanged; classic-mini unchanged (tiny-sat 2, alphabet-words 27/12/100, map-colouring 6).

## Changes

### 2026-09-30T04:03:44Z — feedback — user

FROM WI-20260926-K4JGC (user, 2026-09-30): P7VP4's load-time refusal to weave an UNPINNED body-less spec op in a value slot (inferred_demand) was KEPT, although 068-implementation §1.3 says it 'goes with K4JGC'. Removing it gives a call like Set.insert(...) a find_dictionary(…, out: ?d) condition that DontFires at a ground carrier no provider supplies — a DEFINITE failure, where 068 §2 says such a call is UNREDUCED (undecided, never false). K4JGC dispatches the call at run time by its ground carrier instead (reduce_op_value's dispatch_body_less, now on for every evaluated call), which gives the right value where a provider exists (wi_p7vp4_rule_body_requirements_test::a_body_less_operand_stays_the_term_the_rule_wrote: ?s = num(v: 9)). Retiring the refusal belongs here, with dictionary blockers: a find_dictionary that finds NO provider at a ground carrier must answer UNREDUCED, not fail.

### 2026-10-08T07:06:30Z — feedback — claude

FROM WI-20260925-P7VP4 (2026-10-08, 81ea3c9e): item 3's shape at an operation with its own `requires`, pinned. `rule lit(?c) :- ?c = Util.sign(1, 5)` over `sign[A](x: A, y: A) requires WeakOrd[T = A]` loads and answers one UNDECIDED row with `?c` free (relation_floundered when an operation reads it), where `?c <=> Util.sign(1, 5)` answers -1. Row: wi_p7vp4_rule_body_requirements_test::an_operations_own_requires_is_inferred_in_a_value_slot_and_refused_as_an_eq_operand (its `lit` half), which turns when the unfold threads dictionaries. The same operand at rule variables is a load error today and is recorded on WI-20260926-7D48J.

### 2026-10-11T20:15:46Z — feedback — user

ROW FROM WI-20261011-3HN0N (2026-10-11, b3f238c0), for item 3 and for item 2's `body_specialize` reducer: NARROWING DOES NOT GO THROUGH A `match` ON A TUPLE OF THE ARGUMENTS. With `operation firstof(xs: List[T = Int64], d: Int64) -> Int64 = match (xs, d) case (cons(h, t), _) -> h case (nil, dd) -> dd`, `rule value(?r) :- firstof(?xs, 9) = 9, ?r <=> ?xs` answers one conditional row, residual `eq(firstof(?_, 9), 9)`; the same operation written `match xs case cons(h, t) -> h case nil -> d` answers two definite rows, `?r = cons(head: 9, tail: ?t)` and `?r = nil`. With ground arguments the tuple spelling answers (`?r <=> firstof([], 9)` is 9), and `not(firstof(?xs, 9) = 9)` stays conditional — incomplete, not unsound. AS FAR AS READ: `folded_call_match` case-splits only where the scrutinee is itself the unbound variable, and here it is a tuple holding one; and `match_pattern_occ`'s tuple arm (kb/body_specialize.rs) decides a tuple pattern against `Expr::TupleLit` only — an operation body writes the tuple as the constructor node over `TupleLiteral`, for which `occ_head_ctor` is `Some`, so the arm 'a known non-tuple scrutinee can't match a tuple pattern' would answer a definite non-match if the reducer were reached with one. Not driven to that answer: the residual above is what a program gets. The walker that replaces the reducer reads a tuple scrutinee component by component, on either node.

### 2026-10-11T21:16:33Z — feedback — claude

ROW FOUND WITH WI-20261008-A3FY2 (2026-10-11, a26210f3) — A QUERY PATTERN DOES NOT EVALUATE A NULLARY CALL, one of 068 §6 carriers that are not typed and must answer as the typed path does. With `operation seven() -> Int64 = 7`, `operation inc(n: Int64) -> Int64 = n + 1` and `sort Box[V] { operation tag() -> Int64 = 7 }` in namespace `ns`, through `anthill query`: `?x <=> ns.inc(3)` answers 4; `?x <=> ns.seven()` binds `?x = seven` and `ns.seven() <=> ?x` the same, definite; `?x <=> ns.Box.tag()` binds `tag`; `?x = ns.seven()` is a residual `eq(?x, seven)`; `?x <=> ns.inc(ns.seven())` is a residual under the warning that `inc` could not be evaluated (expected Int64, got Node). The rule `r(?x) :- ?x <=> seven()` queried as `ns.r(?x)` answers 7. A dot in a query is not dispatched either: `?x <=> (ns.Box).tag()` binds `dot_apply(Box, tag, args: ?args)`, and `?x <=> ns.Box[V = Int64].wrap(5)` is refused (a companion receiver bracket is not read in a query pattern).

### 2026-10-12T12:33:25Z — feedback — claude

FOUND WITH WI-20260930-MHRN1 (2026-10-12), NOT CHANGED THERE: a LABELLED call on a BUILTIN-tagged operation is read by index in a rule body. The builtin's own goal reader takes pos_arg(0) / pos_arg(1) (builtin_cmp, builtin_arith) and answers Failure when one is missing, and reduce_op_value hands a builtin callee back untouched. MEASURED, before and after MHRN1 alike: `:- Int64.lt(a: 1, b: 5)` answers no solutions — a DEFINITE failure, so `not(Int64.lt(a: 1, b: 5))` holds — where `Int64.lt(1, 5)` answers 1; `?c <=> Int64.sub(a: 5, b: 1)` and `?c <=> Int64.sub(1, a: 5)` are conditional residuals where `Int64.sub(5, 1)` answers 4 and the operation-body spellings answer 4. (The typer keeps an all-labelled call's labels when it reorders it, so the typed rule body reaches the builtin labelled.) An ORDINARY operation's labelled call is bound through one owner since MHRN1 — typing::bound_args, read by KnowledgeBase::call_args_in_param_order — and the builtins are the readers of a call's arguments by parameter that are left.

### 2026-10-12T12:48:08Z — feedback — claude

ON THE LABELLED BUILTIN CALL ABOVE — where it goes wrong and where a fix sits (read 2026-10-12; left for this ticket by the user, not fixed with MHRN1). A tagged operation's call never reaches the parameter pairing MHRN1 moved to typing::bound_args: its handler reads the goal's positions (operand 0, operand 1, a third positional as the result) and looks up no parameter list. The two entries treat a label differently, which is why one spelling is incomplete and the other wrong: the VALUE entry (resolve/evaluate.rs run_builtin_for_value) declines a call with named_arity != 0, so `?c <=> Int64.sub(1, a: 5)` is left standing, undecided; the GOAL entry (execute_builtin -> builtin_cmp / builtin_arith) has no such check, finds no operand 0 and answers Failure, so `:- Int64.lt(a: 1, b: 5)` fails definitely and `not(Int64.lt(a: 1, b: 5))` answers 1 (MEASURED). A fix has one place: before a tag's handler is dispatched, at both entries, rewrite a labelled goal into positional order through bound_args over the operation's declared parameters — only where every label names a declared parameter, since some tagged names take labels by design (`find_dictionary(…, out: ?d)`).

### 2026-10-13T08:05:34Z — feedback — claude

SPLIT INTO FOUR PARTS (user, 2026-10-13); this ticket stays open over them and is done when they are. D1a WI-20261013-GFS6A-068-d1a-a-woven-call-is — a woven call suspended on its dictionary (item 1); holds, from WI-20261003-4DYR6, the two rule-body programs measured there (a head variable's dictionary never fetched over a sort with a type parameter; a woven defaulted call running the default). It needs nothing of 7D48J and is unblocked. D1b WI-20261013-DEY66-068-d1b-the-per-consumer — the per-consumer reductions retire (item 2); holds the notes of 2026-10-11 (3HN0N, a match on a tuple; A3FY2, a nullary call in a query pattern); after C1d. D1c WI-20261013-2HX69-068-d1c-the-unfold-threads — the unfold threads dictionaries (items 3 and 4); holds XBHX3's rows and the 2026-10-08 note's lit row; after D1b. D1d WI-20261013-WPVVY-a-labelled-call-of-a-builtin — a labelled call of a builtin-tagged operation, the two notes of 2026-10-12; it needs nothing else of the sequence and is unblocked. MOVED TO 7D48J's last part (C1d WI-20261013-RYDNV-068-c1d-one-classification-per): the 2026-09-30 note's retirement of the load-time refusal to weave an unpinned body-less operation in a value slot — it is the inference's decision, which C1d replaces, and it reads D1a's answer.

### 2026-10-13T10:07:36Z — feedback — claude

ROW FOUND WITH WI-20260925-0RRQP (2026-10-13, 33ffa2a4), not classified into a part: A SELECTION WRITTEN IN AN OPERATION'S BODY IS LOST WHEN THAT OPERATION IS RUN AS A RULE'S GOAL. Over P7VP4's own fixture — `rule cmp(?a, ?b, ?c) :- WeakOrd.compare(?a, ?b, ?c)`, `operation viaRule[A](x: A, y: A) -> Int64 … requires WeakOrd[T = A] = cmp(x, y).head.c`, `operation ruleDesc() = viaRule[A = Int64, WeakOrd = Descending](1, 5)` — `interp.call` of `ruleDesc` answers 4, and `rule q(?r) :- ?r <=> Driver.ruleDesc()` answers -1, `Int64`'s own. The same with 0RRQP's `via[A](p: Pr[T = A]) requires WeakOrd[T = A] = ordPr(p).head.c`. It is the operation-level `requires` selected by the spec's name that is lost: a sort-level named requirement selected the same way, `Box.orderOf[T = Int64, O = Descending](box(a: 1, b: 5))` in a nullary driver, answers 4 as a rule's goal. Unchanged by 0RRQP; pinned there as a stated limit, `a_driver_run_as_a_rules_goal_derives`, which fails when this is cured.

### 2026-10-13T17:54:36Z — feedback — claude

ONE MORE MEASURED ROW, found while WI-20261013-0GYW1's programs were run (a730f11b, and the same on da39cc3d): a call of a body-less spec operation AT AN ARROW, written in a rule body, does not run. sort Apply { sort F = ?  operation run(f: F) -> Int64 }, sort P { provides Apply[F = (Int64, Int64) -> Int64]  operation run(f: (Int64, Int64) -> Int64) -> Int64 = 30 }, operation mk() -> (Int64, Int64) -> Int64 = lambda (x: Int64, y: Int64) -> x, rule r(?v) :- ?v = Apply.run(mk()): r.takeN(5) ends 'relation_floundered(goals: [eq(Var, run(mk))])', where the same call in an operation body answers 30. The typer pins the dictionary at the arrow, a concrete carrier, so by 068 2.1 nothing is generated and the call is CONCRETE; a function value has no sort the evaluator could dispatch on, so the call is left unreduced. With two providers at the arrow the rule-body call is refused at load as a tie, as in an operation body. Whether a call pinned at a tuple or an arrow carries its dictionary into the clause is this ticket's item 1 or a row beside it.


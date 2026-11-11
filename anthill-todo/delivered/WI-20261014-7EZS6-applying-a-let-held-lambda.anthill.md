## Attributes

- id: WI-20261014-7EZS6-applying-a-let-held-lambda
- created: 2026-10-14T08:24:53Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-11T16:36:51Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261015-809JN-proposal-050-1-stage-1-a-write

- tags: typing, proposal-050.1

## Description

Applying a let-held lambda that writes its own parameter is refused for an undeclared write to that parameter.

PROGRAM (measured 2026-10-14, plain and ANTHILL_TEST_NODE_CARRIER=1 alike):

  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =
    let _ = Cell.set(c, n)
    n
  operation go() -> Int64 effects {Error[String]} =
    let r: Cell[V = Int64] = Cell.new(1)
    let w = lambda (z: Cell[V = Int64]) -> put(z, 5)
    let n = w(r)
    n * 10 + Cell.get(r)

is refused: "type mismatch in go.effects (op-effects): expected declared: [Error[T = String]], got undeclared effect: Modify[T = z]". The lambda's write to its own parameter z reaches go's row as written, where the application w(r) makes it a write to r — a let-local cell, which go owes nothing for. Handed to an operation instead (apply(r: Cell[V = Int64], f: (z: Cell[V = Int64]) -> Int64 @ {Modify[z]}) -> Int64 effects {Modify[r]} = f(r), then apply(r, w)) the same lambda runs to 55.

EXPECTED: w(r) is 55, the write read as Modify[r] at the application, as an operation's parameter is read at a call.

WHERE TO LOOK: found during 1TJQH; the application of a let-held function value (apply.rs, function-value Path 2) types the callee's row with its own binders unrenamed — callback_at_slot renames a callback's binders where it meets a slot, and nothing renames a called value's binders to its arguments.

## Changes

### 2026-10-14T08:25:11Z — feedback — user

CORRECTION to WHERE TO LOOK: the reading of apply.rs is a guess, not measured — what is measured is the program and its refusal, and the twin through an operation's slot running to 55.

### 2026-10-14T08:35:06Z — feedback — user

ACCEPTANCE ADDENDUM (user, 2026-10-14: fold it here, one fix should close both) — A SOUNDNESS HOLE BY THE SAME MECHANISM, found by the family e-applied-arrow. use[R](q: Cell[V = Int64], r: Cell[V = Int64], h: (n: Int64) -> Int64 @ {R}, w: (z: Cell[V = Int64]) -> Int64 @ {Modify[z]}) -> Int64 = (let v = w; v(q)) DECLARES NO EFFECTS AND RUNS, writing q (go: use(c, d, lambda (n: Int64) -> n, lambda (z: Cell[V = Int64]) -> put(z, 5)) gives 552); the same with w at @ {Modify[z], EW}. Applying w(q) directly is refused, correctly. So applying a function value does not rename its own parameter to the argument, and the label left over is reported as undeclared where the parameter is a lambda's (this ticket's program) and DROPPED where it is a callback parameter's (this one). EXPECTED: v(q) is the write Modify[q], refused where use declares none and running where it declares it. The family's exceptions name this ticket for both; when the fix lands they excuse nothing and the run says so.

### 2026-10-16T12:47:24Z — feedback — user

SOUNDNESS HALF OF THE ADDENDUM CLOSED, COARSELY (2026-10-16, flow_derive `traced` facts — the boundary classifier drops a callback parameter's Modify only for a place the flow pass followed in full). A callback parameter applied through an alias (`let v = w; v(q)`) declaring no effects no longer runs: `w` read as a value escapes, its places carry no `traced` fact, and the label is kept on every MODIFIABLE input. The family e-applied-arrow's 6 `UNSOUND runs` alias rows (typed=parameter, applied=alias, declares=none) are now refused, and their 4 exceptions naming this ticket are removed. NOT the EXPECTED answer: `v(q)` is charged to every modifiable input (`q` and `r`), so a `use` declaring only `Modify[q]` is refused where this ticket expects it to run. The exact answer — renaming a function value's own parameter to its argument at the application — and the lambda half (a let-held lambda's undeclared `Modify[z]`, the remaining OneVerdict exceptions) stay with this ticket.

### 2026-11-11T16:36:50Z — feedback — claude

DELIVERED (measured on the tree over 29613621). Applying a function value reads its own parameters at the arguments (050.1 §5.2), as a call of an operation by name does: kb/typing/projection.rs ApplicationPlaces pairs each binder the arrow records (arrow_own_binders; for an arrow written in a parameter list, the places of every callback its row names, callback_of_place) with the argument at its position, classified as a named call's argument (ArgPlaces); each label of the row is incurred over the arguments' places (at_call), a binder taking the whole tuple of several arguments is charged onto each component naming a place, an argument naming no place under a Modify is refused as at a named call (placeless_refusal), and the guarded-row hold reads the labels as incurred. The ticket's program runs to 55; the addendum gives 552 with Modify[q] declared and is refused naming q, not r, without it; the family e-applied-arrow's four 7EZS6 exceptions are removed and excuse nothing (6 verdict lines moved: unannotated/tuple writes-own declares=all × call/alias now run 552; annotated × call/alias lose op-effects beside UnresolvedName, the 6T5C6 exception). Callbacks now read as named calls: v1/walk/mk_one/mk_list/fold_g give their named twins' verdicts (noted on WI-20261016-HE2J6 and WI-20261015-X57XR); f(first(l, d)) and f(tok) are refused naming no place as put(first(l, d), 5) and touch(tok) are; let t = tok; f(t) loads where it charged the unrelated Modify[c]; a join if b then f else g applied to q charges {q}, not {q, r}. No source program reaches the flow facts' CallbackParam arm any more (trace over the gate and every family): its sub-rules' rows moved to kb::region::wi353_tests (noted on WI-20261015-038RQ). Rows: wi_7ezs6_application_reads_parameters_at_arguments_test (9), wi341_callback_modify_test rewritten (8 rows beside named twins), wi353_tests::the_flow_facts_charge_a_callback_place_by_its_feeds (13 programs); rows changed: review 9 (2), EDPF6, N2YEK's applied case, 809JN's lambda-parameter row, 4GBQV's fixture. Back-outs, each part alone by a temporary switch over 53 suites (1385 rows): re-key off 18 fail, callback binders off 15, placeless refusal off 4, guarded mapping off 1, whole-tuple binder off 1; each flow sub-rule's back-out fails its programs of the unit row. /code-review (high, 5: 3 fixed — binders of every callback a joined row names, the row mapped once, the join row; 2 no change — a placeless argument under a guarded row is refused naming no place, measured; the interned short name is the hold's own pattern). No spec change: §5.6 'at a call, the target is re-keyed onto the argument' and §4.4's note on an arrow's own parameters say it; 027.1's pipeline sentence corrected. Full workspace 11,902 passed and 0 failed; families green on both carriers; scaland 1 + 51 + 800.


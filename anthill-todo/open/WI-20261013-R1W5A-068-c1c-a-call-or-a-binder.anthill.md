## Attributes

- id: WI-20261013-R1W5A-068-c1c-a-call-or-a-binder
- created: 2026-10-13T08:03:19Z

- status: Open
- status_agent: claude
- status_at: 2026-10-13T08:03:19Z

- acceptance: cargo-test

- depends_on: WI-20261013-WF14Z-068-c1b-a-rule-variable-is

- tags: proposal-068, typing

## Description

068 C1c — A CALL OR A BINDER FORM IN A RULE BODY IS TYPED AS AN OPERATION BODY IS, EQUATIONS OFF (068 §3). Part 3 of WI-20260926-7D48J. One call has one answer whatever shape the rule-body walk hands the typer. ROWS: over `sort Box { entity mk(v: Int64); operation peek(b: Box) -> Int64 = b.v; operation open(b: Box) -> Int64; rule open(?b) <=> peek(?b) @[simp] }`, the three spellings `?x <=> Box.open(Box.mk(4))`, `?x <=> Box.mk(4).open()` and the first over `sort Box[V]` agree, and `?x <=> dbl(2)` agrees with `?x <=> app(lambda (y: Int64) -> dbl(y), 2)` over `rule dbl(?n) <=> ?n + ?n @[simp]` (7D48J note 2026-10-11, 3HN0N); the lambda case as C1a decides it, on wi_3hn0n_tuple_on_rhs_test's five rows; an ordinary operation's call in a value slot is held to its parameter list — over `operation sub2(x: Int64, y: Int64) -> Int64`, `?c <=> Util.sub2(1, 5, 9)`, `Util.sub2(1, 5, bogus: 9)`, `Util.sub2(1)` and an argument of the wrong type are load errors, as the goal is since MHRN1 (note 2026-10-12); row (1) of the 2026-09-26 note (a typer `@[simp]` law whose right side calls body-less operations leaves them unpinned); `()` left by an equation in a fragment's argument (WI-20261011-7G99A, its program 5). The new load errors match C1a's count. ACCEPTANCE (cargo-test, driven): the fragments' stamps land on the stored occurrences; each row with its back-out named at its site. CONTROLS: an operation body's typing unchanged; classic-mini unchanged.

## Changes

### 2026-10-21T18:15:29Z — feedback — user

C1a DECIDED (WI-20261013-GGXCX, user 2026-10-21; docs/design/068-implementation.md §6.2): THE LAMBDA CASE IS DECIDED — EQUATIONS ARE ON in a fragment's typing, as in an operation body (068 §3's simp OFF reversed); the stored fragment is the rewritten one; `@[simp]` still never fires inside §1.1's evaluation. So this part's 'equations off' reads 'equations on': over `operation dbl(n: Int64) -> Int64`, `rule dbl(?n) <=> ?n + ?n @[simp]`, `?x <=> dbl(2)` (a residual today), the lambda row (4 today), the goal `dbl(2, ?x)` (no answer today, silently) and `dbl(2) = 4` all answer 4, and `?x <=> app(dbl, 2)` is refused as in an operation body ('no bare reference to this operation can supply'); the three spellings of `Box.open` agree at 4; the 2026-09-26 `twice` row answers 14, the rewritten node typed so the calls it leaves are pinned. The rows the 2026-10-13 equations-off measurement reddened (wi_rm247 x2, kernel_mint_address, wi939, wi_p7vp4, wi_3hn0n x4) are controls, green before and after. THE C1c LOAD ERRORS, each counted on the corpus and the suite before it refuses (start: GGXCX's 2026-10-13 count): a call's argument list and types in a value slot; a function value no bare reference can supply; an effectful application by its typed row.

### 2026-10-21T19:50:16Z — feedback — user

ROW ADDED (2026-10-21, found fixing an Error-row goal view inline): a bodied operation whose row holds a concrete effect other than `Error` still has no goal view, so its goal FAILS and a negation over it proves a falsehood — `operation stamp() -> Int64 effects {Clock} = 3`, `rule n() :- not(stamp(3))` answers true, definitely (the same family as 7D48J's 2026-10-16 `not(now("2000"))` row). This part's typed-row refusal of an effectful application at load is what answers it; run time keeps the decline for what no typer sees, which should leave such a goal undecided, not failed.

### 2026-10-22T05:42:52Z — feedback — user

FROM WI-20261013-WF14Z (2026-10-22, its second part): A RULE-BODY CALL DOES NOT PERFORM THE SOME-COERCION. Over `sort Opt { operation len(o: Option[T = Int64]) -> Int64 = match o case some(v) -> v case none -> 0 }`, `rule viaHead(?a: Int64, ?r) :- ?r <=> Opt.len(?a)` queried `viaHead(3, ?r)` answers conditionally — `len` raised `match_failed(occurrence: var_ref(name: o), scrutinee: 3)`, residual `unify(?_, len(3))` — where the operation-body twin `operation twin(a: Int64) -> Int64 = Opt.len(a)`, reached as `?r <=> twin(3)`, wraps `a` and answers 3. kernel-language says the call-side conversions apply at every argument position; the clause typing reads the call so since WF14Z's second part (an `Option` parameter is the call's placeholder, a bare `T` meets it by the some-coercion, row an_option_parameter_is_the_calls_placeholder), so the load records nothing and the wrapping is the rewrite of a fragment typed as an operation body is — decision 4's 'the stored fragment is the rewritten one'. A row this part owes: `viaHead(3, ?r)` answers 3.


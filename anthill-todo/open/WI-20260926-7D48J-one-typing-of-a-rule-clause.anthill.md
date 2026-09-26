## Attributes

- id: WI-20260926-7D48J-one-typing-of-a-rule-clause
- created: 2026-09-26T09:52:03Z

- status: Open
- status_agent: user
- status_at: 2026-09-26T09:52:03Z

- acceptance: cargo-test

- depends_on: WI-20260925-P7VP4-a-rule-body-call-s-requires

- tags: proposal-068, typing

## Description

ONE TYPING OF A RULE CLAUSE FOR 060's INFERENCE AND 068's FRAGMENTS — today rule-body typing ties a body term to nothing, so 060's inferred conditions cannot be routed, and 068 §3's fragments have no clause environment to be typed in. Step C1 of the 068/060 sequence: where the two proposals meet. DESIGN FIRST.

WHAT EACH SIDE NEEDS FROM RULE-BODY TYPING.
 * 060 (WI-20260925-P7VP4): `infer_rule_body_requirements` decides per call with its own `spec_op_call_carrier_outcome`, over the types `collect_rule_var_types` stamps. WI-20260925-0RRQP measured what those stamps are: in `rule order(?p, ?c) :- ?p <=> box(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)` inside `sort Box[T] requires O: WeakOrd[T]`, `?x` and `?y` share one per-call placeholder and `?p` is a bare `?T` — nothing says `?x` is at `Box`'s `T`, so the inferred condition cannot be routed to the caller's `O`.
 * 068 §3: each functional fragment (an operation application or a binder form) is typed by the operation-body typer, `type_check_node_at`, simp OFF, in an environment carrying the rule's variable types — and §1 says the walk "never types" data (constructors, tuples, goal atoms).
They meet at a data position: routing a condition needs a constructor's result type to reach a variable through `<=>`, which 068 §1 leaves untyped.

DECIDE (recorded in docs/design/068-implementation.md and docs/design/requirement-channel.md, with the user):
 1. The clause environment: rule variables typed by unification across goals, `<=>` sides and constructor result types, tied to the enclosing sort's parameters (a rule sees its sort's `requires` — user, 2026-09-25, on P7VP4).
 2. How far data is typed — amend 068 §1's "never types those" to exactly what (1) needs, answering WI-1058's three reasons (lost expectation, lost scope, rewriting) for each data position admitted.
 3. The typer's per-call classification — pinned at a concrete carrier / needs a dictionary / value-directed where a variable's type is undetermined (the WI-282 exemption) — as the ONE input of P7VP4's inference, replacing its own `spec_op_call_carrier_outcome` reading, so the two cannot disagree.
 4. Which new load errors 068 §3 brings (the count comes from ACG10's step-1 census).
THEN implement.

0RRQP STAYS ITS OWN TICKET (user, 2026-09-26): it may be fixed narrowly first; this ticket keeps its rows.

ACCEPTANCE (cargo-test via rustland/scripts/test.sh; driven): the fragments' stamps land on the stored occurrences; P7VP4's inference reads the typer's classification — a call the clause typing now places at a concrete carrier is pinned at load and not woven, a row per class, each back-out reddening its own row; the new load errors match the census; P7VP4's, SHED7's and 0RRQP's rows unchanged or flipped as the design records. CONTROLS: an operation body's typing unchanged; classic-mini unchanged.

## Changes

### 2026-09-26T13:26:05Z — feedback — user

ROWS ADDED FROM THE PRVA2 REVIEW (filed on ACG10 2026-09-26, now in 068's problem section). (1) A TYPER @[simp] LAW WHOSE RIGHT SIDE CALLS BODY-LESS SPEC OPS leaves those calls unpinned: with rule twice(?a, ?b) <=> Int64.add(conv(?a, ?b), conv(?a, ?b)) @[simp], ?r <=> Conv.twice(m(v: 3), "km") is a conditional unify(?_, add(conv(..), conv(..))); untagged it answers 14 (the one-parameter control is identical). The clause typing this ticket designs runs with simp OFF (068 §3) — this row is the measurement that says why, and joins the acceptance. (2) THE LOAD-TIME HALF of a call with no argument at its spec's carrier parameter: Conv.tag(b: B) has none at A, so ?s <=> "km", Conv.tag(?s, ?r) answers nothing, silently; with require[Conv[A = Meters, B = String]] it answers 3 (since PRVA2 (c)). Under 060 §3's anchor rule a read nothing grounds is refused at typing unless a require supplies it; the clause typing decides which, and the run-time half (whatever still reaches run time answers undecided, never nothing) is WI-20260926-CYNPE's.


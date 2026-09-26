## Attributes

- id: WI-20260925-B79ZJ-a-rule-body-call-inside-a
- created: 2026-09-25T22:22:46Z

- status: Open
- status_agent: user
- status_at: 2026-09-25T22:22:46Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20260925-P7VP4-a-rule-body-call-s-requires

- tags: typing

## Description

A RULE-BODY CALL INSIDE A `|` / `&` BRANCH, A `not(…)` OR A QUANTIFIER BODY GETS NO CONDITION — WI-20260925-P7VP4's stated limit (user, 2026-09-25): the caller's dictionary does not reach it, and it keeps value-directed dispatch.

TODAY (18cca07a). `infer_rule_body_requirements` places each inferred read immediately before the TOP-LEVEL goal holding its call, so its walk stops at every goal position below the top one (and at deferred data forms — lambda / let / match / if — which a rule body carries unevaluated). Pinned by `wi_p7vp4_rule_body_requirements_test::a_call_in_a_branch_keeps_value_dispatch` and `a_call_inside_a_quantifier_keeps_its_value_dispatch`. Example: `rule pick(?a, ?b, ?c) :- (WeakOrd.compare(?a, ?b, ?c) | ?c <=> 99)` cited as `viaPick[A = Int64, WeakOrd = Descending](1, 5)` answers `Int64`'s own `-1` from the branch, where the same call as a top-level goal answers `Descending`'s `4`.

WHY NOT HOIST THE READ — MEASURED on 18cca07a with the walk entering goal positions: a read before the `|` runs whichever branch is taken. With its witness unbound it WAITS, and the OTHER branch's definite answer comes back CONDITIONAL (`pickB(?x, ?c) :- (Scale.twice(?x, ?c) | ?c <=> 99)`: `pickFree` lost its definite `99`); with a witness whose type has no instance it FAILS the clause for a branch never taken. A read inside a quantifier body names a binder out of scope and waits for ever.

WHAT A FIX NEEDS:
 (1) PLACEMENT inside the scope: the branch goal `G` becomes `and(read, G')` (the read immediately before its call, inside the connective's argument); a quantifier body likewise; `not(…)` needs a decision — a read inside the negand with an unbound `out` makes the negated goal non-ground, so `step_naf` delays (a routed `out` is bound at clause opening and is fine; an unrouted one must derive before the negation or stand aside).
 (2) THE CITATION LAYOUT over nested reads: `requirement_read_counts` / `requirement_read_specs` / `requirement_read_out`, `settle_citation_routes`' enumeration and `bind_citation_reads` (which finds reads in the OPENED body) all read TOP-LEVEL reads only today. One canonical order (pre-order through the goal connectives) for all of them.
 (3) THE RESOLVER'S READERS of a woven call reached through a connective. MEASURED: a woven call inside an `|` branch IS read today (`pickRod` answered `6` through it with the walk entering the branch), so `or` may need nothing — confirm for `&`, `not` (a builtin reading its negand off the goal's view) and a quantifier body; and WI-670's `body_refuted_by_ground_conjunct` reads a woven goal's head as `apply_within` (see WI-20260925-P7VP4's round-2 review).

ACCEPTANCE, driven by value: `pick` under `WeakOrd = Descending` answers `4` from the branch; `pickFree` keeps its definite `99`; a call in a `not(…)` and in a `forall ?e in ?xs: …` body answers through the caller's dictionary when cited; every uncited clause answers as before (value dispatch). CONTROLS stated at their sites. Full workspace green via rustland/scripts/test.sh; scaland testFull.


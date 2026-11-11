## Attributes

- id: WI-20261015-038RQ-proposal-050-1-stage-5-the
- created: 2026-10-15T13:47:56Z

- status: Open
- status_agent: user
- status_at: 2026-10-15T13:47:56Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261014-7EZS6-applying-a-let-held-lambda

- tags: proposal-050.1, typing

## Description

Proposal 050.1, stage 5: the flow facts retired for an operation with a body — once a label over a name is resolved by its regions (stage 1) and applying a function value aliases its parameter to the argument (WI-20261014-7EZS6), the flow-derivation pass (kb/flow_derive.rs, WI-352) and keep_modify at the boundary (region.rs, the CallbackParam arm, WI-353) say nothing the regions do not.

EXPECTED: measure first what still reads them — the CallbackParam arm and the flow facts backed out over the suites; remove both for operations with a body; keep reflect/feed.anthill's vocabulary only if a reader remains (proposal 046 §4.3). The programs they served keep their verdicts through the regions: match l case cons(h, rest) -> f(h) over a callback parameter f writing its own parameter is charged Modify[l] (measured on 5da88f1f: refused where the operation declares nothing), and the wi353 rows.

## Changes

### 2026-11-11T16:36:36Z — feedback — claude

WI-20261014-7EZS6 delivered: no source program reaches the CallbackParam arm of op_boundary_effects any more — a temporary trace of the arm over the full gate and every family, on both carriers, found only the wi353 unit rows, which call op_boundary_effects with a synthetic label. The source rows that drove the arm's sub-rules (traced, a () -> T callback read as callable, the type gate on re-key targets, the type-variable result, holds_no_value's spellings, feed.anthill's fresh output on an untraced result) moved to kb::region::wi353_tests::the_flow_facts_charge_a_callback_place_by_its_feeds, with callbacks whose arrows write no row and the label given by hand; each sub-rule backed out alone fails it (measured, listed at the row). Those unit rows go with the arm. The measurement this stage asks for first is therefore done for the source side: backing out the arm moves no source verdict.


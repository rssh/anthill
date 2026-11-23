# Project actions

What the project is doing now, in order, and where each action's method lives. Replaced as actions
move, not appended to; the history is in the tickets, `converging.md` and `converging-history.md`.

As of 2026-11-23.

## 1. One answer per question — consolidate the typer's decisions

Why: `converging.md` §3.11 and §4 q18, `converging-history.md` §3.10. The typer is 42% of
production code and took 60% of the last month's growth. The one fortnight in the series in which
the open stock fell is the fortnight that deleted the most (Oct 25 → Nov 8: 39% of added lines,
060.1 and 073 retiring second answers). That is one observation; §4 q3's first prediction of
2026-11-23 tests it per fortnight.

Method: `one-answer-per-question.md`.

| question | map | tickets | family | next step |
|---|---|---|---|---|
| which implementation runs a call | `docs/design/supplier-question-map.md` | WI-20261025-7K84M, delivered 2026-10-25 | `f-supplier-routes` (no exceptions) | done; the rule-body route stays proposal 068's |
| may A stand where B is expected | `docs/design/compatibility-question-map.md` | WI-20261025-053QV, WI-20261025-27050, both Open (last touched Nov 13 and Nov 2); known: 05ZQE Open, DYX5E PreOpened, G37HS delivered | `g-compatibility` | measure the matrix again on today's tree (073 and 074 moved the ground), then the two tickets |
| which of a spec's parameters a provision binds | `docs/design/spec-carrier-set.md` | WI-20261121-JE2MT, WI-20261122-CXR5B, WI-20261121-DBR8V, delivered 2026-11-22/23 | none; rows in `wi_cxr5b_*` | done — both stages of the correction delivered |
| what a name refers to | — | 1Y96B delivered 2026-11-01; FTV0Q Open | — | map — next |
| what effect row a call has | — | — | — | map |

## 2. The work list — WI-1126's first part

Why: `converging.md` §3.11, `converging-history.md` §3.10. The gate of §1 ("until the base is
stable") has a ticket, WI-1126, whose own file has not changed since 2026-08-19. Its first part
turns the open stock into a count that can go down.

Method: decisions by the user, not code — a verdict on each of the 85 numbered proposals; the
base's open holes (the spec's 16 open citations in part, and the base constructs no program uses,
`Suspension` the plainest); the 230 Open tickets sorted into what 0.1.0 needs and what moves to
PreOpened. `converging.md` §4 q19 adds one decision to it: whether requests from programs outside
the repository (anthill-traces, the shop model) are base work or PreOpened.

State: one verdict — proposal 005 rejected on 2026-10-30 (`docs/proposals/rejected/`).

Next step: the other 84 verdicts.

## 3. Measure — the next `converging.md` sitting

When: about 2026-12-21, to score the five predictions registered on 2026-11-23 (§4 q3) and to read
the series again.

Method: `converging.md` §5 — both tracker recipes over the window `234cbe83..<new sitting>`, the
line classifier, the move-proof churn split by fortnight, the term shares with the per-word column,
the suite's day table. The state table at the top is replaced.

Open: `rustland/target/` was cleaned on 2026-11-19 and the suite's logs before it are gone, so the
day table has no reading between Oct 25 and Nov 19. Keeping the per-day row somewhere tracked as the
runs happen is not decided.

## Standing rules

From `CLAUDE.md` and the user's practice: commit to `main`; before a commit that is not
documentation only, the full gate green (`rustland/scripts/test.sh`) and `/code-review` run; ask
before filing a ticket, and before changing the spec; prefer fixing inline to filing a follow-up.

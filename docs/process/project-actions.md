# Project actions

What the project is doing now, in order, and where each action's method lives. Replaced as actions
move, not appended to; the history is in the tickets and in `converging.md`.

As of 2026-10-25.

## 1. One answer per question — consolidate the typer's decisions

Why: `converging.md` §3.10 and §4 q18. Every closed item still brings 1.3 tickets and about 240
lines of production code; the typer is 38% of production code and half of every month's growth;
a question answered in several places gives one program several verdicts.

Method: `one-answer-per-question.md`.

| question | map | tickets | family | next step |
|---|---|---|---|---|
| which implementation runs a call | `docs/design/supplier-question-map.md` | WI-20261025-7K84M, delivered 2026-10-25 | `f-supplier-routes` (no exceptions) | done; the rule-body route stays proposal 068's |
| may A stand where B is expected | `docs/design/compatibility-question-map.md` | WI-20261025-053QV (a spec over a parameter admits its provider at a typed position), WI-20261025-27050 (provision lookup and type patterns ask the one relation), and known: G37HS, 05ZQE, DYX5E | `g-compatibility` | review the draft §8.2 wording in 053QV; word 27050's `TypePattern` change (065 §2, 071 §1.2) |
| what a name refers to | — | 1Y96B, FTV0Q (to read first) | — | map — next |
| what effect row a call has | — | — | — | map |

## 2. The work list — WI-1126's first part

Why: `converging.md` §3.10. The gate of §1 ("until the base is stable") has a ticket, WI-1126, that
has had no note since 2026-08-19. Its first part turns the open stock into a count that can go
down.

Method: decisions by the user, not code — a verdict on each of the 80 numbered proposals; the
base's open holes (the spec's 17 open citations in part, and the base constructs no program uses,
`Suspension` the plainest); the 240 Open tickets sorted into what 0.1.0 needs and what moves to
PreOpened.

Next step: not started.

## 3. Measure — the next `converging.md` sitting

When: about 2026-11-05, to score the seven predictions registered on 2026-10-05 (§4 q3, interim
score of 2026-10-25 there) and to read the series again.

Method: `converging.md` §5 — both tracker recipes, the line classifier, the move-proof churn, the
term shares with the per-word column, the suite's day table. The state table at the top is replaced.

## Standing rules

From `CLAUDE.md` and the user's practice: commit to `main`; before a commit that is not
documentation only, the full gate green (`rustland/scripts/test.sh`) and `/code-review` run; ask
before filing a ticket, and before changing the spec; prefer fixing inline to filing a follow-up.

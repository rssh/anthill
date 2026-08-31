## Attributes

- id: WI-20260830-E0JE6-rename-guardians-harness-to
- created: 2026-08-30T20:27:49Z

- status: Open
- status_agent: user
- status_at: 2026-08-30T20:27:49Z

- acceptance: cargo-test, scaland-sbt-test

- tags: guardians

## Description

RENAME `guardians.Harness` TO `AgentGenerator` AND `guardians.Checker` TO `AgentChecker`, so the names say which of the two parties each one is. The ICTERI-2026 article now uses the new names (Listing 7); the example does not, so this is a divergence like the ones in WI-20260830-THZ8R.

WHY `Harness` IS THE WRONG NAME, and it is not only taste. The sort has two operations, `render_task` and `generate`: it renders a prompt and produces a candidate. That is a GENERATOR. "Harness" names the whole generate-and-check rig, which is what `attempt` and `open_round` are -- so the current name claims the loop while describing one half of it, and a reader looking at `attempt(h: Harness, llm: Llm, chk: Checker, ...)` cannot tell from the names why there are two parameters rather than one component with a helper.

MEASURED AS A READING FAILURE, not a hypothesis: a reader of the article's listing asked, in order, 'why is Checker not in Harness', 'I can't understand attempt outside of harness', and then proposed the merge. Two differently-named parties -- generator and checker -- answer that before any prose does.

SCOPE. `sort guardians.Harness` and `sort guardians.Checker` (lib/harness.anthill); the carriers `FileHarness` and `LoadChecker`; the signatures of `attempt` and `open_round`; the fixtures under fixtures/agent/ that name either sort (checker.anthill, rejected/{steering,frontier,minting}_checker.anthill, rejected/forged_llm.anthill); any `provides Checker[C = ...]` clause.

ACCEPTANCE: no live occurrence of `Harness` or bare `Checker` outside a comment recording the old name; the guardians suite green with every fixture still accepted or refused FOR ITS OWN REASON, diagnostic substrings unchanged.


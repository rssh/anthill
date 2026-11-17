## Attributes

- id: WI-20261117-8J8NG-elaborate-every-rule-before
- created: 2026-11-17T22:13:25Z

- status: Open
- status_agent: claude
- status_at: 2026-11-17T22:13:25Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261117-22S8N-a-law-is-not-usable-by-a-guard

- tags: typing

## Description

ELABORATE EVERY RULE BEFORE THE OPERATION BODIES WHOSE TYPING RUNS IT. Typing an operation body runs rules: a guard is refuted, a precondition proved, an in-body proof and a contract's proof discharged (prove_from_gamma), and each may run a relation's clauses and take a guarded = law as a premise. Since WI-20261117-22S8N the untagged guarded = laws are elaborated AHEAD of the bodies (typing::laws_elaborated_ahead: typed, the goals of their bounds, the reads of their declared requirements woven); every other rule is typed and woven in the sweep AFTER them (type_rule_bodies RuleBodies::NotSealed, install_typed_head_domain_goals, install_rule_provider_dictionaries, check_rule_body_requirements, infer_rule_body_requirements, route_rule_goal_requirements). So a relation of the SAME load that a proof runs has no requirement reads yet, and where it needs a dictionary the proof is undecided (WI-20261105-CBRD2: a proof derives no dictionary from the values, gamma_proof_depth) — sound, a lost precision, and an order a later load does not have. Known cases: a law whose guard calls a relation of the same file that needs a dictionary (stated in kernel-language §5.3 since 22S8N); CBRD2's rule cmp, run by the guard proof of made[A = Int64, WeakOrd = Descending](1, 5) in wi_5g28a. If typing requires prepared rules, the rules come first. MEASURE FIRST: each case in one load and in two (rule in an earlier load) — is the later-load proof decided, and what does it answer. TO DECIDE: (1) which rule passes read what the bodies' typing leaves — settle_citation_routes routes the citations queued while bodies are typed, check_eq_override_backing reads body stamps; anything else must be found, not assumed; (2) the @[simp] guarded equations, which bodies FIRE (guard_holds at typing) and whose right-hand side the weave rewrites — kept after the bodies by 22S8N; (3) the stdlib's own load then types its bodies over prepared rules, and error order moves (law and rule errors before body errors). The laws-ahead split (RuleBodies::Ahead / NotSealed { ahead }, Clauses::Ahead) is then one sweep ahead of the bodies. Note: ANTHILL_TYPER_ORACLE=1 already fails on main (List.foldLeft, List.foldRight, Delay.delayForce rewritten when typed again), so it cannot control this change until that is fixed. ACCEPTANCE: each measured case decided in one load as in two; wi_22s8n, wi_v0rpw and wi_5g28a green under all three recipes; families green; full workspace green via rustland/scripts/test.sh.


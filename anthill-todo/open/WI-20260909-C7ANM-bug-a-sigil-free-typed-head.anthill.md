## Attributes

- id: WI-20260909-C7ANM-bug-a-sigil-free-typed-head
- created: 2026-09-09T20:24:38Z

- status: Open
- status_agent: user
- status_at: 2026-09-09T20:24:38Z

- acceptance: cargo-test

- tags: vvm1r

## Description

BUG: a SIGIL-FREE typed head parameter (WI-742 sec 2.1's `rule g(x: Red, ?d)` form) does not enforce its bound AND mis-binds the head variable beside it. Clean load, definite WRONG answer, and the sigil twin one character away gets both right.

MEASURED 2026-09-09 on clean HEAD sources (b09aa9f1..276ceda3), with NO require, NO projection and no dictionary machinery anywhere in the fixture. Four rows, two controlled pairs differing only in the sigil:

  sort Red { entity red }  sort Blue { entity blue }  fact seedr(red())

  rule g(x: Red, ?d)  :- seedr(x)      -- sigil-free
  rule g(?x: Red, ?d) :- seedr(?x)     -- sigil twin

  QUERY              SIGIL-FREE            SIGIL
  g(red(),  ?z)      ?z = Ref(red)         ?z UNBOUND       <- correct
  g(blue(), ?z)      ?z = Ref(red)         no solution      <- correct

TWO DEFECTS IN ONE, and they are separable:

  (1) THE BOUND IS NOT ENFORCED. `g(blue(), ?z)` is admitted where `x: Red` says it must not be. The sigil form refuses it, so the enforcement channel EXISTS (`typed_pattern_bounds_hold` over `KnowledgeBase::rule_type_bounds`) and the sigil-free form is not reaching it.

  (2) THE SIBLING VARIABLE IS BOUND TO THE PARAMETER'S OWN VALUE. `?d` — which the caller passed as a free `?z` — comes back holding `red`, a value that never occupied its position. That is the silent class: a clean load and a definite answer nobody asked for.

WHERE TO LOOK, and none of it is verified — this is a direction, not a diagnosis (WI-741's rule). `convert_rule_head_with_params` (load.rs) mints a fresh `VarId` per sigil-free parameter into `Loader::rule_param_vars` and routes the bound through `rule_head_type_bounds` -> `install_rule_type_bounds`, which keys by DE BRUIJN INDEX computed as `globals.len() - 1 - position`. Both symptoms are consistent with the parameter's variable not being where the head's `globals` list says it is — an off-by-one or an absent entry would explain the bound testing the wrong slot AND the neighbouring variable receiving this one's argument. VERIFY BEFORE BUILDING: print the rule's `globals`, the stored head term and `rule_type_bounds` for both spellings and see where they diverge, rather than assuming the index arithmetic is the fault.

WHY IT IS FILED SEPARATELY rather than folded into its dependant: nothing in it involves a `require`, a dictionary, a projection or a spec. It is the parameter form itself, and it is wrong for every clause that writes one beside another head variable — a population this umbrella does not bound.

WHAT IT BLOCKS. WI-20260909-S8CBV gate (1) — the rule-body `require[Desc[T = p.E]]` bracket — cannot be DRIVEN without it. A projection's receiver must be a sigil-free head name: `?p.E` is a PARSE ERROR (`syntax error near `.E``, measured), so the sigil spelling that works here cannot carry one. S8CBV's gate-1 machinery is BUILT and correct as far as it can be measured (see that ticket's feedback and `scratchpad/s8cbv-gate1-attempt.diff`); what it lacks is a head form whose parameter binds.

ACCEPTANCE. The four rows above, as a controlled pair: the sigil-free spelling must answer EXACTLY what its sigil twin answers — `?z` unbound at `g(red(), ?z)`, and NO SOLUTION at `g(blue(), ?z)`. Assert by VALUE and by refusal, not by a clean load. CONTROLS, each stated at its site: the SIGIL twin passes either way BY DESIGN and is the yardstick; an UNTYPED sigil-free parameter (`rule g(x, ?d)`) must keep whatever it answers today, since no bound is claimed for it; and a clause with the parameter ALONE (`rule g(x: Red) :- seedr(x)`) must be unaffected — it is the shape `wi742` already drives, and the defect needs a SECOND head variable to show. Say which rows fail when the repair is backed out. cargo-test green via scripts/test.sh.


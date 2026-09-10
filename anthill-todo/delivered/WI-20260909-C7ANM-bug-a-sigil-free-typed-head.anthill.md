## Attributes

- id: WI-20260909-C7ANM-bug-a-sigil-free-typed-head
- created: 2026-09-09T20:24:38Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-10T06:17:07Z

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

## Changes

### 2026-09-10T06:16:59Z — feedback — user

DELIVERED. Both symptoms were ONE root cause, and it was not the de Bruijn arithmetic the ticket pointed at. `Term::Fn` files a call's arguments into a positional list and a named list, which loses the INTERLEAVING; `convert_rule_head_with_params` rebuilt the head by APPENDING each parameter after the positional args, so `rule gfree(x: Red, ?d)` compiled to `gfree(?d, ?x)`. Dumped heads before and after:

  before:  gfree globals = [d, x]  bounds = [(dB 0 -> Red)]   -- dB 0 IS x; x is column 1
           gsig  globals = [x, d]  bounds = [(dB 1 -> Red)]
  after:   gfree globals = [x, d]  bounds = [(dB 1 -> Red)]    -- identical to the twin

So the bound was never unenforced (symptom 1) and no variable was mis-bound (symptom 2): `x` was correctly bound and correctly guarded, and it was in the wrong COLUMN. `g(blue(), ?z)` was admitted because `blue()` landed in the unconstrained column; `?z` came back `red` because it landed in `x`'s.

THE REPAIR, four axes at one function, each backed out separately against the ten rows of `wi_c7anm_head_parameter_column_test`:

 1. WRITTEN COLUMN ORDER. `SimpleTermStore::arg_order` records a call's slot order when — and only when — the list MIXES positional and named slots (the one shape the split cannot express); `rule_head_written_columns` reassembles the head from it. Recorded at the ONE converter frame that builds an argument list. 4 of 10 fail on back-out.
 2. THE RE-INTERNED KEY. A non-parameter named arg kept its PARSE-table symbol as the head's key, so `rule mixed(from: ?a, x: Red)` came out with `from:` spelled as whatever KB symbol shared that index (MEASURED: `TypeExtractor` in one fixture, `NamedTuple` in another) and a body goal writing `mixed(from: …)` was refused. Reachable only from the same mixed head. 1 of 10 fails.
 3. THE BRACKET DECLINE (`/code-review`). A `[…]` bracket is a TYPE APPLICATION, so `T = Red` inside one is a type argument, not a §2.1 parameter. Without the gate, `rule myrel[T = Red]` was rebuilt as `myrel(?T)` — the `rule` and `fact` spellings of one bracketed head meant different things — and `rule myrel[Int64, T = Red]` PANICKED axis 1's own assert, since a bracket is built by a frame that records no order. One decline repairs both. 2 of 10 fail.
 4. ONE VARIABLE PER PARAMETER NAME PER RULE (`/code-review`). The parameter map is cleared per RULE, not per head, and the heads share one body — but each head minted a FRESH var and overwrote the map, so every head but the LAST got a column the body never binds. MEASURED on `rule twin: aa(x: Red, ?d), bb(?d, x: Red) :- …`: `aa(?p, blue())` came back FLOUNDERED with a residual `domain(?p, Red)` where the sigil twin answered `?p = red`. 1 of 10 fails.

A FIFTH ARRANGEMENT was measured because the ticket's four rows do not rule it out: parameters FIRST rather than in written order passes the ticket's own acceptance and still fails 3 rows. That is what `a_parameter_written_last_keeps_its_column` is for — it passes under the real defect BY DESIGN, so it is dead weight against axis 1 and the only row that catches this.

TWO MORE `/code-review` FINDINGS FIXED HERE rather than filed: the loader now reports a LoadError where it panicked (the admitting predicate says yes to any UNRESOLVED functor — a wider door than the census that closes it, so a panic was reachable in principle), and `rule_head_written_columns`' parameter is named `parse_keyed_params` with its symbol table stated, because the sibling list in the same loop is KB-keyed and "make them symmetric" is the one edit that must not be made.

ACCEPTANCE, met exactly. The sigil-free spelling answers what its twin answers, by VALUE and by REFUSAL: `g(red(), ?z)` -> `?z` unbound, `g(blue(), ?z)` -> no solution, both spellings. Controls stated at their sites: the SIGIL twin (yardstick, passes either way), an UNTYPED sigil-free head (never reaches the reclassifier), and the parameter ALONE (one column has no order to get wrong). A SECOND reader of the same order is its own row — the 052 declared column schema reports `(a: ?a, x: Red, b: ?b)` through the typer, not the resolver.

WORKSPACE: 36 binaries, 6766 passed, 0 failed via scripts/test.sh. `/code-review` run twice; every finding of both passes is either fixed here or filed.

WHAT THIS UNBLOCKS: WI-20260909-S8CBV gate (1). Its blocker was exactly this — a projection receiver must be a sigil-free head name because `?p.E` is a parse error. RE-MEASURE (4) there rather than trusting the parked note, as that ticket itself says.

WHAT IS NOT FIXED, and it is FILED as WI-20260910-7NBZX after discussion: the reclassifier reaches only a rule's head ATOM in a CLAUSE. An EQUATIONAL head declines at the connective, so `rule pk: pick(a: Red, ?b) <=> 7 [simp]` loads clean and is INERT where its sigil twin rewrites `pick(red(), 1)` to `7` (driven). A BODY-LESS head loads clean where its sigil twin is refused. Both are written into `docs/kernel-language.md` §2.1 under "Where the two spellings do NOT yet agree", because a gap parked only in a ticket rots.


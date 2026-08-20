## Attributes

- id: WI-20260820-8RJK8-a-guarded-equation-fires
- created: 2026-08-20T12:57:54Z

- status: Open
- status_agent: claude
- status_at: 2026-08-20T12:57:54Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A GUARDED EQUATION FIRES NOWHERE — `lhs <=> rhs :- guard` is accepted, indexed when tagged, and read by no firing site. Split out of WI-292's "SIBLING GAP" note, which is the only place in the tracker that owned this and which is DELIVERED, so the gap had no live owner. Surfaced again by WI-888, whose refusal message now tells authors "a guarded equation is read by no firing site" and points here.

DRIVEN, NOT CODE-READ, with a control (2026-08-20). `rule pick(?a, ?b) <=> ?a :- Int64.gt(?a, ?b) [simp]` with the guard TRUE at the redex (`pick(9, 2)`): `OperationBodyMissing`. The IDENTICAL rule unguarded: `Ok(Int(9))`. So the guard alone is what kills it, and the fixture is sound.

WI-292's DIAGNOSIS IS WRONG ON THE TAGGED CASE, corrected here rather than carried forward. It said guarded equations "are not even indexed, because is_equation requires an EMPTY body", conflating two mechanisms. Measured, counting `rules_by_functor(anthill.kernel.unify)` over four (body x tag) combinations against a rule-free base of 20:
  guarded  [simp]  -> 21  INDEXED
  guarded untagged -> 20  not indexed
  bodyless [simp]  -> 21  INDEXED
  bodyless untagged-> 20  not indexed
INDEXING TRACKS THE TAG ALONE (WI-139 unindexes untagged equational HEADS by shape, body irrelevant). So a `[simp]`-guarded equation IS in the bucket and IS reachable by `simp_equation_rids`; selection is not the blocker. The blocker is that every firing site gates on `KnowledgeBase::is_equation`, whose FIRST clause is `entry.body_nodes.is_empty()` — `is_directional_equation` (resolve.rs, what `fire_simp_equation` and `apply_eq_rules` gate on) and `is_simp_equation` (simp_rewrite.rs, what the typer's `try_fire` selects by) both build on it. Nothing anywhere evaluates a matched equation's body.

THE STDLIB POPULATION IS 15, AND NONE OF THEM IS TAGGED — the number that decides how this must be accepted. field.anthill:25-27 (mul/div/recip guarded by `neq(?b, 0)`), indexed_seq.anthill:25-26 (`nth` out-of-bounds, lo and hi), list.anthill:257 (`nth` recursive step), logical_stream.anthill:84/86 (`interleave`, both splitFirst cases), map.anthill:119 (`get` past a different key — sitting directly beneath its `<=>` [simp] siblings), stream.anthill:114/115/118/119/120/121 (headOption/head/tail/isEmpty). Every one is UNTAGGED, so each is dead for TWO independent reasons: no `[simp]` (unindexed, not directional) and a non-empty body (not `is_equation`). CONSEQUENCE FOR ACCEPTANCE: relaxing the body clause alone changes NOTHING for any of the 15 — a suite that goes green on that fix has measured nothing. Either the stdlib rules are tagged as part of this, or the ticket decides that a guarded equation does not need the tag, and says why against WI-881 ("`[simp]` is the enablement").

WHAT MUST BE DECIDED, not just implemented.
(1) IS `[simp]` THE ENABLEMENT HERE TOO? Fifteen authors wrote these untagged, which reads as "this is the definition, not a normalization hint". WI-881/WI-888 say the tag is what enables. Pick one and state it at the site; if the tag stays required, the 15 need it added and that is a behaviour change to the stdlib, not a relabel.
(2) WHO PROVES THE GUARD, and WHEN. Post-match, against the match substitution. The resolver has SLD; the typer's `try_fire` runs at type-check time over occurrences and has no prover in the same sense. The two firing sites may not be able to answer alike, and if only one can, say which and what the other does.
(3) THE UNDECIDED GUARD IS THE SOUNDNESS CASE — the WI-067 hazard WI-292 was built around: a guard that is neither proved nor refuted must SUSPEND (do not fire), never NAF-decide. `splitFirst(?s) = none` over an abstract stream is exactly that shape, and six of the fifteen are it.
(4) TERMINATION. `list.anthill:257` and `logical_stream.anthill:84` are RECURSIVE guarded rewrites; firing them makes the normalizer recurse under a guard for the first time. Bound it or state the bound that already applies.

NOT A DUPLICATE OF WI-292, which is delivered and was the TYPE-directed half (read the redex's carried type to discharge a SORT-LEVEL `requires`, the Set/Map dormancy). This is the VALUE-guard half: an explicit `:- guard` on the rule itself. WI-292's own note says so ("NOT type-directed -- a separate firing concern ... Likely its own WI"). Prerequisites it named are all Delivered: WI-584 (var-RHS instantiation), WI-578 (typed-value substrate), WI-502 (umbrella), WI-292 itself.

LIKELY CONSUMER, worth checking at claim time rather than assumed: WI-567 (open) is blocked on "a guard discharges iff its predicate bottoms out in NATIVE scalar builtins ... isEmpty and Eq[List].eq are anthill-RULE-defined, so refuting them needs the rules FIRED on the prove path". `Stream.isEmpty` IS one of the fifteen above (stream.anthill:120/121), so firing guarded equations is at least part of what WI-567 needs. WI-566 cites the same wall. Neither lists this in `depends_on` today.

ACCEPTANCE: a guarded equation whose guard HOLDS at the redex fires and the test asserts the VALUE (`pick(9, 2)` -> 9), with the guard-FALSE row asserting it does not fire and an UNDER-DETERMINED row asserting it suspends rather than deciding; the control is the same rule unguarded, which fires either way, kept in its own fixture; at least one of the fifteen stdlib rules is driven to a value end-to-end, so "it loads" is not the evidence; the decision on (1) is written at the firing site and in kernel-language.md 5.3 beside the equational-rules paragraph, which currently says only that a guarded head keeps its `=` spelling; full workspace green via rustland/scripts/test.sh.

REFERENCE: WI-292 (delivered, the SIBLING GAP note this is split from, and the wrong indexing claim corrected above), WI-881 (`[simp]` is the enablement), WI-888 (the refusal message that points here), WI-139 (unindexing by head shape), WI-067 (never NAF-decide an undetermined obligation), WI-584/WI-578/WI-502 (delivered prerequisites), kb/mod.rs `is_equation`, kb/resolve.rs `is_directional_equation` / `apply_eq_rules`, kb/simp_rewrite.rs `is_simp_equation` / `fire_simp_equation`, docs/design/constrained-term-substrate.md "Conditional rewrite rules".


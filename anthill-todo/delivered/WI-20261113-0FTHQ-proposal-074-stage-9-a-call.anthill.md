## Attributes

- id: WI-20261113-0FTHQ-proposal-074-stage-9-a-call
- created: 2026-11-13T23:22:34Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-24T15:50:06Z

- acceptance: cargo-test

- tags: proposal-074

## Description

PROPOSAL 074 STAGE 9 — A CALL USES THE DICTIONARY ITS OPERATION IS HANDED (docs/proposals/074-typeclass-instance-is-a-dictionary.md §5, decided with the user 2026-11-13) (§2, "Which dictionary a call uses"; T13; split from stage 1 after the third review). `viaParam` and `viaMember`, handed `Alt`'s dictionary, answer 2; a bracket naming `Leaf` outranks the handed dictionary; a call two handed dictionaries answer is refused at load. What a handed dictionary covers: `f(d: Additive[T = Meters], …) = sum2(a, b)` handed `ProjAdditive`'s dictionary (or any second provider at a type) answers through it; `o: Ord[T = Int64]` handed answers `WeakOrd.compare(1, 2)` through its chain; `o` beside `w: WeakOrd[T = Int64]`, and a lambda binder beside the operation's dictionary at one spec and type, refused at load. Until stage 1 lands, the rows hand a dictionary as the tree does today (`viaParam(Tag[T = Leaf])`), and stage 1 rewrites them with 073's rows. Spec text written with the stage and agreed with the user before it is committed. ACCEPTANCE: each row driven to its value (a load is no evidence); each part backed out by a temporary switch and the failing rows named; full workspace green via rustland/scripts/test.sh; scripts/families.sh green on both carriers; scaland sbt testFull green.

## Changes

### 2026-11-24T15:50:02Z — feedback — user

DECISIONS (2026-11-24, with the user). Measured first on the binary, before the stage: viaParam(t: Tag[T = Leaf]) handed Alt's dictionary answered Leaf's 1, viaMember 1, viaOpen 2 (already), viaCallee/viaOp over a second Additive[T = Meters] m(v: 5), a call through o: Strict[T = Big]'s chain refused as ambiguous, f[X](t: Tag[T = X], x: X) = Tag.tag(x) refused 'missing requires', two parameters at one type / a parameter beside a clause / a lambda's binder beside the operation's parameter each loaded and read the first, and Tag.tag[Tag = Leaf](...) refused as naming a concrete provider (058 3.5 check 3). Decided: a bracket may name any provider, one with constructors included, everywhere (check 3 removed; TX0G6 had refused it, CXR5B narrowed it). Found doing it: a parameter is read at its own members and at the types its type writes, an entry each, so a call written at h.C (Hold.ask[C = h.C]()) still reads h; a parameter's carried named slot (FromParam) is not counted as handed, the argument's slot outranking a clause (WI-1094); the operation's own type parameter in a parameter's type is read as a clause names it (<op>.X), which the stage adds (it was refused before).

### 2026-11-24T15:50:04Z — feedback — user

DELIVERED (2026-11-24, 82c8cc2e3): a call uses the dictionary its operation is handed -- a parameter at its members and at the types its type writes, a lambda's binder, a clause -- before the provider chosen at load; a call two handed dictionaries answer is refused at load, at its own spec and at a callee's requirement; a bracket may name any provider. Acceptance: rows driven (wi_0fthq_handed_dictionary_test, 11: T13 2, the member and the type-parameter readings 2, the bracket over the handed dictionary 1 / 2, a callee's requirement m(v: 10), through the chain 1, five refusals naming both); each of 7 parts backed out by a temporary switch over all of anthill-core (11618 rows, control clean), every part failing named rows; 8 rows that pinned check 3 rewritten to drive the bracket, q2c01 req3's refusal moved to the call; /code-review (xhigh) found the written-types entry read off the term carrier alone (inert under ANTHILL_TEST_NODE_CARRIER=1), fixed. Gate 12700 / 0; families green on both carriers; scaland testFull 811 + 51 (2 skipped) + 1. kernel-language 5.4, 8.2 and proposal 074 agreed with the user.


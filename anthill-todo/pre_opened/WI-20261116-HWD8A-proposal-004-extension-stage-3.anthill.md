## Attributes

- id: WI-20261116-HWD8A-proposal-004-extension-stage-3
- created: 2026-11-16T20:30:28Z

- status: PreOpened
- status_agent: claude
- status_at: 2026-11-16T20:30:35Z

- acceptance: cargo-test

- depends_on: WI-20261116-411A7-proposal-004-extension-stage-2

- tags: proposal-004

## Description

PROPOSAL 004 EXTENSION, STAGE 3 (PARKED, TO DECIDE): SortDomain AND TYPE PATTERNS AT A TUPLE. docs/proposals/004-tuple-sorts.md, 'Extension (2026-11-16): a tuple is a NamedTuple', open question 1: which specs a tuple derives beyond PartialEq, Eq (stage 1, WI-20261116-JWCNN) and TypeValue (stage 2, WI-20261116-411A7). Proposed there as possible additions, NOT decided: SortDomain at a tuple (its domain filled from its components' domains, as a sort's SortDomain is), and type patterns at a tuple (proposal 071), with which an Error.reify boundary catches an Error[(Int64, Int64)] payload — today a reify at a tuple payload waits on a tuple's instance (proposal 065, the open question withdrawn by the user 2026-10-16; WI-20260908-9WVT7's second review). Lexicographic Ord is not proposed. Related, and kept with WI-20261021-VF8GT: the arrow half of the formers, and a tuple type written as a value in a rule body's data slot (VF8GT's (3)). TO DO FIRST: decide open question 1 with the user, then write this stage's programs and acceptance (measured today, the answer under the rule, each back-out named at its row).


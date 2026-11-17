## Attributes

- id: WI-20261116-HWD8A-proposal-004-extension-stage-3
- created: 2026-11-16T20:30:28Z

- status: Open
- status_agent: claude
- status_at: 2026-11-17T07:12:27Z

- acceptance: cargo-test

- depends_on: WI-20261116-411A7-proposal-004-extension-stage-2

- tags: proposal-004

## Description

PROPOSAL 004 EXTENSION, STAGE 3 (PARKED, TO DECIDE): SortDomain AND TYPE PATTERNS AT A TUPLE. docs/proposals/004-tuple-sorts.md, 'Extension (2026-11-16): a tuple is a NamedTuple', open question 1: which specs a tuple derives beyond PartialEq, Eq (stage 1, WI-20261116-JWCNN) and TypeValue (stage 2, WI-20261116-411A7). Proposed there as possible additions, NOT decided: SortDomain at a tuple (its domain filled from its components' domains, as a sort's SortDomain is), and type patterns at a tuple (proposal 071), with which an Error.reify boundary catches an Error[(Int64, Int64)] payload — today a reify at a tuple payload waits on a tuple's instance (proposal 065, the open question withdrawn by the user 2026-10-16; WI-20260908-9WVT7's second review). Lexicographic Ord is not proposed. Related, and kept with WI-20261021-VF8GT: the arrow half of the formers, and a tuple type written as a value in a rule body's data slot (VF8GT's (3)). TO DO FIRST: decide open question 1 with the user, then write this stage's programs and acceptance (measured today, the answer under the rule, each back-out named at its row).

## Changes

### 2026-11-17T07:12:25Z — feedback — claude

DECIDED (user, 2026-11-17), proposal 004 open question 1: a tuple provides SortDomain and type patterns; Ord is not proposed. A tuple pattern admits a type as every pattern does, when the type is a subtype of an instance of it, and <: at a tuple is by label with width and permutation (004 rule 1, kernel-language §4.5). PROGRAMS, measured on b026a4af. SortDomain, over enum Colour (red, green, blue): (S1) rule pair(?x: (Colour, Bool)) :- true — today pair(?x) is one conditional answer, residual domain(?_, (Colour, Bool)); under the rule six definite answers. Likewise (c: Colour, b: Bool), six; Option[T = (Colour, Bool)], seven (none and six somes); (Colour, (Bool, Bool)), twelve. (S2) rule mixed(?x: (Colour, Int64)) :- ?x = (Colour.red, 3) — today residual domain(?_, (Colour, Int64)), eq(?_, (red, 3)); under the rule (red, 3), the Int64 component filled as a primitive is. Type patterns, over operation boom() -> Int64 effects Error[T = (a: Int64, b: String)] = Error.raise((a: 1, b: "x")): (P1) Error.reify[T1 = (a: Int64, b: String)](lambda () -> boom()) — today refused at load (TypePattern at a tuple, "a STRUCTURAL FORMER"); under the rule err((a: 1, b: "x")). (P2) T1 = (a: Int64) — today refused, and the typer leaves Error[(a: Int64, b: String)] in the row ("undeclared effect"); under the rule caught (width) and the label discharged. (P3) T1 = (b: String, a: Int64) — the same; caught (permutation). (P4) T1 = (Int64, String), the label declared on the caller — under the rule not admitted (labels _1, _2): the raise passes the boundary to the caller. (P5) rule caught(?x) :- Error.reify(lambda () -> boom(), ?x) — today refused; under the rule err((a: 1, b: "x")). (P6) TypePattern.admits[T = (a: Int64)](type_value[T = (a: Int64, b: String)]()) true, admits[T = (Int64, String)] at the same type false, admits[T = (a: Option)] at (a: Option[T = Int64]) true (an open slot inside a tuple) — today each refused at load ("a tuple has no type pattern"). WHERE: typing::synth tuple_pattern_refusal goes; type_admits compares two tuples by label with width and permutation (today the run-time error "both named tuples, and a type pattern does not compare two of them"); the typer reify discharge of an Error label reads the same test; SortDomain at a tuple derived from its components (as tuple_instance builds PartialEq, Eq and TypeValue), its fill the tuples of their domains. ACCEPTANCE: the programs above driven to their answers; a tuple with an arrow component still refused (VF8GT); kernel-language §5.4 (TypePattern: a tuple admitted by <:) and the SortDomain paragraph, agreed first; full workspace green via rustland/scripts/test.sh; families green on both carriers; each part backed out at its row.


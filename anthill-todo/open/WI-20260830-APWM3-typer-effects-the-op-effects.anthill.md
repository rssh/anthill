## Attributes

- id: WI-20260830-APWM3-typer-effects-the-op-effects
- created: 2026-08-30T10:11:59Z

- status: Open
- status_agent: user
- status_at: 2026-08-30T10:11:59Z

- acceptance: cargo-test

## Description

TYPER/EFFECTS: the op-effects COVERAGE check does not flatten a row projected off a CONCRETE carrier, so a polymorphic row cannot be spelled at the carrier that instantiates it — and fixing that without teaching 054 to look THROUGH a row would open a `Branch × External` evasion.

MEASURED on the guardians example after `guardians.Llm` gained `effects E = ?`
(the `Stream` shape, WI-320/045). One operation, one parameter type varied,
`effects {llm.E, Error} = h.generate(llm, p)`:

  | llm: Llm      (the SPEC)   | E is an abstract row VAR      | LOADS   |
  | llm: FakeLlm  (E = {})     | E is the EMPTY row            | LOADS   |
  | llm: LiveLlm  (E={External})| merge[present[External],empty]| REFUSED |

The refusal:
  expected declared: [{merge[left = present[label = External], right = empty_row]}, Error]
  got undeclared effect: External

So the projection RESOLVES — the diagnostic prints a merge term that denotes exactly
{External} — but the coverage comparison asks 'is the label External among the declared
members' and sees the whole merge as ONE OPAQUE MEMBER. Abstract has nothing to flatten;
empty flattens to nothing; only a NON-EMPTY CONCRETE instantiation trips it.

The machinery exists and the mirror direction is already fixed: typing.rs:16198 (WI-375)
decomposes an `effects_rows(…)` wrapper on the BODY side precisely so 'the effect
machinery sees flat labels, not the wrapper as one opaque effect (which rendered as a
spurious undeclared effect: {empty_row})'. `decompose_effect_row_raw` already walks
left/right merge nodes. It is not reaching the DECLARED side here.

WHY IT MATTERS BEYOND ERGONOMICS. Today the only row that loads at a concrete carrier is
the OVER-declared literal one (`{External, Error}`), which is the opposite of what row
polymorphism is for. And `{Branch, llm.E, Error}` at LiveLlm is refused TODAY BY THIS GAP,
not by proposal 054 — `check_branch_external_exclusion` (typing.rs:59197) matches the
row's LITERAL labels. Fix the coverage gap alone and that row LOADS, and a Branch region
performs External. The two must move together.

NOT A BLOCKER FOR THE EXAMPLE: every guardians operation takes `llm: Llm` (the spec), so
the shipped change never reaches the broken case. Found because a test typed its parameter
`llm: LiveLlm` and was then refused for the WRONG REASON — which made the `Branch` in its
row inert (dropping it changed nothing on either leg). Found by /code-review.

ACCEPTANCE — THE REAL CHECK, and it is one test with two rows that must fail for DIFFERENT
reasons:
  (1) `effects {llm.E, Error}` at `llm: LiveLlm` must LOAD (the gap closed);
  (2) `effects {Branch, llm.E, Error}` at `llm: LiveLlm` must be REFUSED **by 054**, with
      the 'at most one of `Branch` / `External`' diagnostic — NOT by a coverage error.
Row (2) is the guard on the evasion: it passes today for the wrong reason, so it must be
asserted on the DIAGNOSTIC TEXT, and the test must say so at its site.


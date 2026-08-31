## Attributes

- id: WI-20260830-APWM3-typer-effects-the-op-effects
- created: 2026-08-30T10:11:59Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-31T14:49:42Z

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

## Changes

### 2026-08-31T14:49:37Z — feedback — user

DELIVERY RECORD. Both acceptance rows behave as specified, each isolated by its own back-out; full suite 6219 passed / 0 failed.

TWO CHANGES THAT COULD NOT SHIP APART:

1. COVERAGE (`typing.rs`, op-effects check). `explode_declared_effect_row` flattens a declared atom that is itself a ROW, so the members of a projected `llm.E` are compared against the incurred labels instead of the whole `merge[...]` term. `effects {llm.E, Error}` at `llm: LiveLlm` now LOADS. The `expected declared: [...]` half of the diagnostic is built from the same flattening, so the message's two halves are finally comparable. Absences ride out of the same walk, replacing the separate top-level `absent` scan — so a `-X` buried in a projected row is visible to the denial reader too.

2. 054's EXCLUSION. `declared_row_labels_read_through` eliminates each element's projections against that fact's own parameter types (over the new PAIRED walk `op_info::all_operation_params_and_effects`) and flattens, so `check_branch_external_exclusion` sees `External` through `llm.E`. Without it, change 1 alone LETS `{Branch, llm.E, Error}` LOAD — a Branch region performing External. Measured, not reasoned: that row loaded on the intermediate tree.

BACK-OUT MATRIX (in the acceptance test's doc, measured on all three trees):

                                   delivered    un-flatten     exclusion reads
                                                coverage       the RAW row
  Llm      {llm.E, Error}          LOADS        LOADS          LOADS
  FakeLlm  {llm.E, Error}          LOADS        LOADS          LOADS
  LiveLlm  {llm.E, Error}          LOADS        REFUSED-cov    LOADS
  FakeLlm  {Branch, llm.E, Error}  LOADS        LOADS          LOADS
  LiveLlm  {Branch, llm.E, Error}  REFUSED-054  REFUSED-cov    LOADS

Each back-out moves exactly one row and reds only the acceptance test. Row 4 is the control that makes row 5 mean anything: 054 excludes a CO-OCCURRENCE, not the `Branch` label.

A REGRESSION THIS TICKET CREATED AND FIXED, found by /code-review on the delivering diff. Flattening removed an ACCIDENTAL refusal: `effects {llm.E, Error, -External}` at LiveLlm had been caught downstream, because the coverage check could not match the incurred `External` and fell through to the denial arm. Once the match succeeded, nothing caught it — a body performing `External` under a row denying it LOADED CLEAN. `check_declared_row_contradiction` now discharges projections first (taking `eliminate_declared_row_projections`, the elimination half of the same helper). That exposed a LATENT bug of its own: its hand-written `row_shaped` list read the LOCAL name and spelled the wrapper `"effects_rows"`, but the `effects_rows` wrapper's local name is `EffectsRows` — so a wrapped row matched no arm, was not a TYPE head either, and contributed NOTHING in silence. It now uses the shared `effect_value_is_row_shaped` (QUALIFIED functor). Test: `a_denial_is_not_evaded_by_projecting_the_label_it_denies`, with the literal `{External, -External}` as its control and two carriers that must still load.

THE WI-818 GUARDED-ADMISSION LEG IS NOW DEAD ON THE CORPUS AND WAS KEPT. Instrumented across the whole suite: 19 312 firings with the flattening backed out (`Stream.head`, `Stream.tail`, `List.head` — the WI-818 primitives themselves), 0 with it in, because `decompose_effect_row`'s guarded arm states the same conservative-presence rule and now runs first. What is left to it is the atom the explode DECLINES, a shape I could not construct to drive. Kept with the numbers written at the site: it costs one qualified-name compare on an already-failing path, and dropping it would refuse `Stream.head` outright if any decline path exists that reading missed.

ALSO: `docs/kernel-language.md` §5.5 gains "a row ELEMENT may be a projection, and it stands for the row it resolves to — not for one label", with the three-carrier table and which rules are read through. `examples/guardians/lib/harness.anthill`'s note that the `Branch` story "is NOT yet true" now states that it is, pointing at the test.

FOLLOW-UP FILED: WI-20260831-RSRP5 — `check_modify_targets` and `check_effect_registration` still read the raw row. TWO gates, not the three originally filed (the contradiction one is delivered here). The registration one has a SPEC EXEMPTION to renegotiate first: §5.5 lists "a receiver projection (`s.E`)" among the positions that name no kind.


# Local Proofs (in-body and control-flow)

**Status:** Draft (2026-06-23)
**Slice of:** [025-proof-constructs](../proposals/025-proof-constructs.md) §"In-body and control-flow proofs"
**Consumes / produces:** [050-local-interpretation](../proposals/050-local-interpretation.md) (the logical environment `Γ`)
**Consumer:** [048-conditional-effects](../proposals/048-conditional-effects.md) / WI-067 (effect discharge, Tier 2)
**WI:** WI-538

## What

A `proof` that appears **inside an operation body** or a **control-flow branch**
(an `if` arm or a `match` arm), discharging an obligation that arises *at that
program point* — the Tier-2 fallback for when the automatic flow (Tier 1) could
not refute a guarded effect's guard. It **reads `Γ`** (the local facts narrowed
by enclosing bindings + branch conditions) as premises and **writes** its
verified conclusion back into `Γ` for the code after it.

## Syntax

A local proof is the **same `proof` construct**, just in **statement** position —
it precedes a continuation expression, the "binding, then body" shape `let`
already uses. It is **not a new proof kind**: it reuses the existing `target` /
`by <strategy>` / `using` clauses verbatim. The one addition is an **optional**
`conclude <P>` clause.

```anthill
operation safe_div(a: Int, b: Int) -> Int =
  if neq(b, 0) then
    proof b_nonzero by derivation
      conclude neq(b, 0)
    end
    div(a, b)                 -- div's guard eq(b,0) is refuted from Γ ∪ { neq(b,0) }
  else
    0
```

**Two forms — `conclude` is optional** (settled with the project owner 2026-06-23):

- **Short form** — `proof <rule> by <strategy> end <body>`, no `conclude`,
  exactly like a top-level proof. The proposition is the **target rule's head**
  (resolved up the lexical scope chain, since an op body declares no rules of its
  own), proved from `Γ`. This is the uncommon in-body case. *(Impl note: the
  current Tier-A wiring treats the target as a **0-ary atom**, so short-form
  discharge fires only for genuinely 0-ary rules — an N-ary head fails the
  unifier soundly; reconstructing N-ary heads with fresh vars is a follow-on.)*
- **`conclude` form** — `proof <handle> by <strategy> conclude <P> end <body>`.
  The goal is the **inline proposition `P`**; `<handle>` is then only a citation
  name. This is the common in-body case — the motivating guard-discharge
  obligation (`neq(b, 0)` over a *local parameter* `b`) has no top-level rule to
  name, so the short form cannot express it. `conclude` takes a full term, so an
  id-only goal (`conclude p`) is unambiguous (it sits in the `conclude` slot,
  never confused with targeting a rule named `p`); `target` stays a parse-time
  name, so no "rule-name-or-expression" disambiguation is needed and the
  top-level `proof` grammar is untouched.

Clause meanings:

- `<target>` — a rule reference (short form) or a citation handle (`conclude`
  form); always a name.
- `by <strategy>` — `derivation` (SLD, Tier-A inline) | `<tool>` (`z3`, …,
  Tier-B). Omitting `by` ⇒ an **open** obligation — it contributes nothing to
  `Γ` (the "Open" state below; distinct from a *pending* external proof, which
  has a strategy and does contribute, provisionally).
- `conclude <P>` — the inline proposition this proof establishes; **`P` is the
  fact added to `Γ`** on discharge. Supplies, for a local proof, what a companion
  proof's *rule-name target* supplies for a top-level one.

Grammar delta: a new `proof_statement` node joins `_expr_body` beside
`let_chain` / `if_expr`, reusing `proof_using_list` / `proof_strategy` and adding
the one `conclude` keyword; the top-level `proof_declaration` is unchanged. The op
body / branch arm thus becomes `statement* trailing-expr` (`let x = e <body>` is
the existing sequencing precedent).

## Discharge model — decoupled, two tiers

Discharge is **separate from use**, exactly as for top-level proofs today: load
records a *pending* `ProofRecord`; the `anthill prove` phase discharges it
(possibly with an external tool) and records a `ProofWitness`; a *consumer* (a
`using` cite) checks the recorded **verdict**, it never re-runs the tool. A local
proof is just another producer/consumer in that scheme, split by **what its
discharge needs**:

### Tier A — `by derivation`: discharged INLINE, in `anthill-core`

`by derivation` is bounded SLD resolution, and the resolver + the
`ResolveConfig.gamma` overlay + the `prove_from_gamma` bridge are **all in
`anthill-core`**. So the typer discharges a `by derivation` local proof **on the
spot**, against the live `Γ`: `prove_from_gamma(kb, &Γ, conclude)`. Verified ⇒
`conclude` is `assume`d into `Γ` for the downstream code. No external tool, no
extra pass, **no soundness gap**.

### Tier B — external (`by z3` / tool): accepted provisionally, verified by an extra pass

The typer **cannot run z3** — `anthill-smt-gen` is *downstream* of
`anthill-core`. So at an external local proof the typer:

1. **snapshots `Γ`** at that point onto the `ProofRecord` (rendered as assumption
   clauses — the existing `ProofConfig.assumptions` / context channel), so the
   premises survive past the transient typing pass;
2. marks the proof **`externally-verified, pending`**;
3. provisionally `assume`s `conclude` into `Γ` so typing proceeds.

The actual z3 discharge happens in the **extra pass** (below).

### Three states, not two

The conclusion's presence in `Γ` is keyed to the proof's *verification state* —
and "unverified" splits in two, which is the crux:

| State | When | `Γ` | Sound because |
|-------|------|-----|---------------|
| **Verified** | Tier-A SLD proves it inline now; or a `Discharged` witness is on record | `conclude` ∈ `Γ`, final | proven |
| **Pending (claimed)** | Tier-B external, has a strategy + `conclude`, verdict deferred to the gate | `conclude` ∈ `Γ` **provisionally** | the **mandatory gate** (§Soundness) |
| **Open / disproved** | no discharge strategy (a bare obligation); or SLD exhausted; or a recorded `Failed` | `conclude` ∉ `Γ` | conservative |

The **pending** row is what makes a z3 proof usable for effect discharge *at
all*. Effect discharge is a **typing-time** decision, yet a z3 proof is verified
only in the **later** pass — and that pass needs `Γ` (the proof's premises),
which the typer itself produces:

```
discharge (typing) → needs z3 verdict → needs Γ (premises) → needs typer
        └────────────────────────────────────────────────────────┘  cycle
```

Withholding `conclude` until z3 has run would deadlock this cycle and make
external proofs **dead weight for effects**. So the typer provisionally assumes a
*strategied* proof's conclusion and proceeds; soundness is recovered by the
mandatory gate, **not** by withholding the fact. Only a proof with **no discharge
path** (a bare obligation) — or one the resolver/tool has **refuted** — adds
nothing.

This **refines** 025's "an unverified proof contributes nothing": for an in-body
proof feeding effect discharge, a *pending-but-strategied* proof contributes
**provisionally**, gated. (A *bare* obligation, with no `by`, still contributes
nothing — that part of 025 is unchanged.)

## The extra pass — who calls it

The extra pass **is the existing `anthill prove`** (`run_prove`,
`anthill-cli/src/prove.rs`), generalized so `collect_proof_records` also picks up
in-body `ProofRecord`s. Because z3 lives in `anthill-smt-gen`, the pass is
orchestrated by **`anthill-cli`** — the layer above both core and smt-gen —
**never by the typer**:

```
anthill-cli                          ← orchestrates the extra pass
 ├ anthill-core    (typer, Γ, SLD)   ← produces ProofRecords + Γ snapshots
 └ anthill-smt-gen (z3)              ← the extra pass dispatches here
```

**Triggering — automatic (resolved, OQ-A).** `anthill check` *chains* the pass:
`load → type → discharge-pending` in one invocation, so a green `check` means
**verified** — no separate step to remember. `anthill prove` remains as a
standalone (CI, explicit re-discharge), no longer load-bearing for correctness.

This is only viable because discharge is **cached**: the proof system already
keys on `ProofRecord.state_hash` + witness sidecars (+ WI-177's epoch). A local
proof's **`Γ` snapshot becomes part of its cache key**, so `check` re-runs z3
only when the proof's KB-context *or its `Γ` premises* changed — `discharge-the-
changed + replay-the-cached`. (The snapshot we need for the gate to *have*
premises thus doubles as the staleness key — a code edit that alters `Γ` at the
proof point invalidates exactly that proof.)

It can verify a *local* proof only because the typer persisted its **`Γ`
snapshot** onto the `ProofRecord`: the pass injects those as assumptions, runs
z3, and records the witness, flipping `result` to `Discharged` / `Failed`. (A
top-level proof needs no snapshot — its context is the static scope / `requires`
chain.)

## Soundness

- **Tier A** (`by derivation`) is verified on the spot — no gap.
- **Tier B** (external) is **"assume, pending external check"**: the program is
  *provisionally* typed (effects provisionally discharged), but **verified** only
  once the extra pass confirms. The extra pass is a **required gate** — a
  `Failed` verdict fails the build. Same contract `by z3` *top-level* proofs
  already have (trust `proposed` / pending until discharged), extended to flow
  facts.
- **The invariant.** A *verified build* is one in which **every pending proof a
  discharge leaned on has been confirmed** by `anthill prove`. Until then the
  discharge is provisional; a `Failed` (or never-run) gate means the build is
  **not** verified, so nothing unsound ships.
- **Provisional discharge is not NAF.** The 048 rule forbids dropping an effect
  on *failure to prove* `guard`; here the effect is dropped on the **presence of
  a proof obligation that will be checked** under a hard gate. NAF drops on the
  *absence* of a counterexample and is never revisited; a pending proof is an
  explicit, recorded obligation whose negative verdict fails the build. The
  difference is *when* it is verified, not *whether*.
- **Visibility (OQ-B, resolved).** `anthill check` chains the gate, so normally
  "green" *means* verified. When the gate can't confirm a relied-upon proof —
  it's pending, missing, refuted, or z3 is unavailable — `check` does **not** look
  clean: it **warns** (and `--require-proofs` errors). So a provisional discharge
  is never silently mistaken for a verified one.

## Lexical scope (citation) and `Γ` feedback

- A local proof cites lemmas (`using <name>`) up its **scope chain**: earlier
  sibling proofs in the same body/branch → proofs in any enclosing branch/body →
  top-level proofs/rules at sort/namespace scope. This is the proof-side mirror
  of `Γ`'s nesting ([050](../proposals/050-local-interpretation.md) §"Nesting"): an enclosing
  scope's *facts* arrive via `Γ`, its *proofs* via the citable set. A proof in
  the `else` branch sees neither the facts nor the proofs that exist only in
  `then`.
- A `conclude P` that is **verified** (or **pending**, provisionally — see the
  three-state table) is `assume`d into `Γ` for the code after the proof (the 050
  in-body-`proof` modification rule) — symmetric to a call's `ensures`, so the
  lemma feeds later discharge, `requires`-checks, and sibling proofs. An **open**
  obligation feeds nothing.

## Pipeline

```
parse → load   (proof ⇒ ProofRecord fact, result = Pending)
      → TYPE   (anthill-core; forward over Γ per body/branch):
          local proof, by derivation → prove_from_gamma(Γ); on ⊨ assume(conclude) into Γ
          local proof, external       → snapshot Γ onto ProofRecord; assume(conclude) provisionally
      → [extra pass — anthill-cli]  anthill prove  (or chained in anthill check):
          collect_proof_records (incl. in-body) → dispatch (z3 via smt-gen / SLD) → witnesses
```

## Scope (WI-538) and deferrals

**Delivered (the construct + Tier-A, 2026-06-23):**
- grammar — `proof_statement` in `_expr_body` (optional `conclude`, trailing
  continuation), reusing `proof_using_list` / `proof_strategy`; top-level
  `proof_declaration` untouched;
- IR / load — `proof_stmt` parse term (`ParseAux::ProofStmt` metadata) →
  `Expr::Proof { target, strategy, using, conclude, body }` occurrence;
- typer hook — **Tier-A inline discharge** via `prove_from_gamma` + the `Γ`
  feedback (a verified goal → `Γ` for the continuation, the proposal-050
  in-body-`proof` modification rule). The goal is the `conclude` proposition, or
  — short form — the `target` rule as a 0-ary atom;
- `using` cites are carried on the occurrence (the lexical-scope-citation channel
  is present).

**Deferred (follow-on):**
- **Tier-B recording** — the `Γ` snapshot onto a `ProofRecord` + provisional
  accept. Until the prove-pass **gate** lands (below), an external (`by z3`)
  in-body proof is treated **conservatively** — it contributes nothing to `Γ`
  (sound: never a silent drop), rather than provisionally assuming its conclusion
  (which is unsound without the gate). So Tier-B recording is **gated on** the
  prove-pass generalization, and they ship together.
- **`using`-as-hypotheses** — the carried cites are not yet spliced into the
  discharge context (the cited lemmas don't yet seed `prove_from_gamma`).
- the **WI-067 dispatch glue** (auto-find a local proof for an un-refuted guard,
  check it against the same `Γ`) — WI-067's own scope note owns it. This is also
  the consumer that makes the Tier-A discharge *outcome* observable end-to-end
  (the typer's `Γ` is otherwise write-only — refute_guard has no caller yet).
- generalizing `collect_proof_records` + the `anthill check` chaining for in-body
  proofs (the prove-pass gate) — a follow-on once Tier-B is exercised.

## Open questions

- **A. Extra-pass triggering — RESOLVED: automatic.** `anthill check` chains the
  discharge pass (`load → type → discharge-pending`), so a green check is a
  verified one; `anthill prove` remains a standalone for CI / explicit
  re-discharge. Kept fast by the cache (the `Γ`-snapshot is part of the staleness
  key — see §"The extra pass").
- **B. Pending / missing-proof reporting — RESOLVED: warn (degrade), don't
  block.** When a discharge leaned on a proof that is missing / pending /
  undischarged — including when z3 is unavailable or times out during an
  automatic `check` (the A′ case) — `check` **completes but emits a loud
  warning** ("relied on N unverified proof(s); not fully verified"). It does
  **not** silently trust (the warning is the honest provisional signal) and does
  **not** hard-block by default (so a z3-less dev/CI run still works). A strict
  **`--require-proofs`** flag escalates the warning to an error for airtight CI.
- **C. `Γ`-snapshot fidelity — deferred to implementation.** Render *every* `Γ`
  fact as an assumption, or only those reachable from `conclude`'s variables (a
  smaller, faster preamble)? Settle this while writing the snapshot code — start
  with all-facts (simplest, correct) and narrow if the preamble proves a hot path.
- **D. Discharge-status channel — RESOLVED: the typer is verdict-free.** It might
  seem the typer could read a recorded verdict from the in-KB `ProofRecord.result`
  (it *can* read KB facts; it cannot reach the smt-gen sidecar). But the verdict
  is never in **source** — `proof … end` carries none — so every `load` asserts
  `result: Pending`, and the real verdict lives only in the downstream sidecar
  core can't reach. For the typer to "know" a prior discharge, something **above
  core** would have to read the sidecar and **inject** it into the `ProofRecord`
  *before* a (separable) typing pass — an architectural cost we don't pay, because
  **automatic triggering (A)** runs the gate *after* typing: the verdict doesn't
  exist yet at typing time, so the typer is **always provisional** by
  construction. Conclusion: the typer only produces **obligations + `Γ`
  snapshots** and treats external proofs as provisional; **all verdict read/write
  lives in the post-typing cli gate**, via the existing proof cache
  (`state_hash` / sidecar / WI-177 epoch). Re-proving avoidance is the gate's
  cache, invisible to the typer.

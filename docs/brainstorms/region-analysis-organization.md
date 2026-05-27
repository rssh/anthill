# Brainstorm — Organizing the region / escape analysis

**Status:** brainstorm (design exploration). **Date:** 2026-05-27.
**Drives:** WI-314 (make `Modify[result]` non-viral — escape / result-reachability
masking) and its growth into proposal 046's full region analysis.

## The question

WI-314 needs an escape / result-reachability analysis over the typed body: at a
call `c = f(...)` where `f : Modify[result]`, re-key `Modify[result]` → `Modify[c]`,
then **mask** it if `c` does not escape the operation (never reaches its result),
or **propagate** it (re-keyed as the op's own `Modify[result]`) if it does. This is
the narrow slice of 046's full region analysis (provenance: input / fresh-output /
local; aliasing; HOF feed-relationships). **Where and how should this analysis
live, for maintainability — given it must start narrow and grow into the 046
superset?**

## What already exists (the ground truth that shapes the answer)

The typer (`typing.rs`) is **already** the relevant traversal:

- An explicit **work-stack** down/up walk (`TypeWorkOp` / `TypeBuildFrame`, e.g.
  `LetFinal`, `Stamp`) over the `NodeOccurrence` tree — *down* carries a
  `TypingEnv`; *up* returns a `TypeResult { ty, env, effects, node }`.
- It already does **boundary masking**: `external_effects()` (typing.rs:486) drops
  effects whose resource is a *local resource*, called at the op / branch boundary
  (1712, 6773); `TypingEnv.local_resources` / `declare_local_resource` (449) are
  populated for **let** (1579) and **match-case** (4558) bindings;
  `extract_effect_resource_sym` (499) already sees through WI-302 `denoted`.

So the down/up traversal, the scope env, the effect row, and a *first masking rule*
(`drop Modify[local]`) are **already in the typer**. The escape analysis is the
*same walk* over the *same data*, plus (a) result-binding re-keying and (b) making
the existing drop escape-aware.

## Options

### (1) Single-walk engine with pluggable mini-phases
The typer's walk *becomes* a generic engine that runs registered **plugins**
(mini-phases) in **one** pass — descend hook (down-data) + ascend hook (up-data).
Typing is one plugin; region analysis another; future analyses are more plugins.
(Corrected framing: *not* a second traversal — the *same* walk hosts many phases.)
- **+** One walk, many analyses — no re-walk, no per-node data to persist. New
  analysis = new plugin. With typing itself a plugin there are ≥2 clients at once,
  so it is *not* a framework-for-one. The natural **destination** if the compiler
  will accrue several fused phases.
- **−** A substantial refactor: invert the typer's control into engine + hooks;
  define shared vs per-plugin state. **Intra-node ordering** becomes a design
  problem — region needs *this node's* type/effects, so typing-up must precede
  region-up at each ascend (attribute-grammar dependency ordering). And `[simp]`
  **rewrites the tree during typing**, so the region plugin must run on the
  *post-rewrite* node (strictly after typing's up-step). Fusing couples phase
  lifecycles — the cost side of the fused-vs-separate (nanopass) tradeoff.

### (2) Separate pass after the typer
Region analysis as its own pass consuming the typed tree.
- **+** Clean separation of concerns; testable in isolation; keeps `typing.rs` from
  growing.
- **−** The analysis is *about effect rows*, which the typer produces and **already
  partially masks**. A post-pass either re-derives effects, or needs per-node
  effect/region data **persisted** on the tree (today `effects` is folded up into
  `TypeResult`, not stored per node). And it **splits masking** across two homes
  (typer: let/match locals; pass: escape) → duplication / drift. Plus a second full
  traversal. "Separate" in name, tightly coupled to typer output in fact.

### (3) Ad-hoc inside the typer, extract later
Write it inline where the typer already walks; move it out as a follow-up task.
- **+** Reuses everything (traversal, env, effects, existing masking); least new
  infrastructure; fastest to a green WI-314.
- **−** Bloats an already-large `typing.rs`; entangles typing with region logic;
  "extract later" is a well-known anti-pattern that rarely happens once entangled.
  Hard to grow into the full 046 analysis from scattered code.

### (3′) — recommended: option 3 done as a factored *module*
The disciplined form of (3): **grow the existing standalone functions**
(`external_effects`, `extract_effect_resource_sym`, `merge_effects`,
`local_resources`) into a **cohesive, separately-testable region/effect module**
with a clear interface — *given a node + env + child results → masked / re-keyed
effect row* — that the **typer calls at its existing boundary frames**. Not a
generic framework (1), not a post-pass (2), not scattered inline (3).
- **+** Reuses the typer's single traversal (no second walk) and the live effect
  data — while isolating region *logic* behind an interface (testable; no monolith).
  Designed to **grow** from narrow (reachability) to full (046 provenance / aliasing
  / HOF) in one place. The codebase already trends this way — `external_effects`
  et al. *are* exactly such functions; this just keeps new logic out of the main
  loop from day one, so "extract later" is unnecessary.
- **−** Requires drawing the module boundary deliberately (what the typer drives vs.
  what the module decides).

## Maintainability verdict

The real axis is **fused vs. separate**, and **how many phases are coming**. (1)
fuses everything into one walk (less re-walking, more intra-walk coupling +
ordering); (2) is the nanopass extreme (more walks, each simple and independently
debuggable); (3′) sits between — the typer calls a region *module* at its boundary
frames, i.e. an **informal, hardcoded-call-site plugin**, which is exactly the
*precursor* to (1).

**Recommend (3′) now, as the first step toward (1).** It already runs region
analysis *inside the typer's single walk* (the point of (1)) without the upfront
engine refactor, and it promotes cleanly: when a *second* mini-phase appears,
extract the engine and register both — designing the plugin/hook interface against
≥2 real clients instead of guessing from one. The intra-node ordering and the
`[simp]`-rewrites-during-typing constraint are faced either way; (3′) faces them at
one concrete call site first, which is the cheapest place to get them right.

**Go straight to (1) instead if** the roadmap already has several fused mini-phases
imminent (region, linearity/borrow, purity, cost, …) — then the engine has multiple
clients on day one and region is simply its first plugin. **Go to (2)** if the team
prefers nanopass-style separate passes for debuggability and will persist per-node
type/effect data.

**The deciding question:** how many fused mini-phases are actually coming? One →
(3′) and promote later; several imminent → build (1)'s engine now.

## Relation to 046

WI-314 is the narrow **result-reachability** slice; 046 is the **superset**
(input / fresh-output / local provenance, aliasing, HOF feed-relationships via
`[feeds:]` / `callee_body`). (3′)'s module is the shared home: WI-314 lands the
reachability + escape-aware masking; 046 grows the *same* module with provenance and
the HOF cases. (1) or (2) would force re-architecting at that growth point; (3′)
does not.

# Occurrences in the Expr IR

## Status: Design — verified IR architecture + a traversal principle

---

## The Expr IR is occurrence-structured

The `Expr` IR is **`ExprOccurrence ⇄ Expr` alternating, all the way down**: an
`ExprOccurrence` resolves to an `Expr`; every child slot of every `Expr` entity is itself an
`ExprOccurrence`. There is no bare-`Expr` layer in a well-formed body.

Verified facts (current state):
- The stored op body is occurrence-wrapped — `convert_expr_child` (`load.rs:3312`) wraps
  every `ExprOccurrence`-typed child slot in `Term::Const(Literal::Handle(Occurrence,
  occ_id))`; `OperationInfo.body` is itself an `ExprOccurrence` handle.
- `OccurrenceStore` (`src/kb/occurrence.rs`) is a `Vec<OccurrenceEntry>`, a plain owned
  field on `KnowledgeBase`. `OccurrenceId` is a dense index into it. Each entry is
  `{ term, span, owner, is_expr }`; occurrences are **not** hash-consed — one per source
  position.
- **`term` is content; the occurrence is identity.** The hash-consed `Expr` `TermId` is
  shared structural content — one `TermId` for every structurally-identical occurrence
  anywhere. The `OccurrenceId` is the per-position identity (span, owner). Terms are
  anthill's universal substrate and aren't going away; an occurrence *has* a term. What is
  removable is *working with bare `Expr` terms as if they had identity*.
- Today the typer, eval, and transformers all peel handles to bare terms at descent
  (`typing.rs:605`, `resolve_handle` at `typing.rs:518`) and discard the `OccurrenceId` —
  the places the principle below is not yet followed.

## Passes traverse at the occurrence level

**Principle.** Any pass that walks and produces/annotates the `Expr` IR — the typer,
transformer / elaboration passes — traverses **occurrence-to-occurrence**: `OccurrenceId` is
the recursion unit. It must not peel an `ExprOccurrence` to its bare `Expr` `TermId` and
recurse on the term.

**Why.** Peeling to the bare term discards per-position identity. That discard is what made
the WI-237 dispatch-collapse possible — the typer peeled at `typing.rs:605` and keyed a side
table by the shared `TermId`, so two source occurrences of one call collapsed to one entry.
(The names-model decision in `operation-call-model.md` removes that collapse's *correctness*
sting; the discard still costs every downstream consumer its source identity — diagnostics
lose spans, debug loses traceability.) Identity is free if you never throw it away;
unrecoverable once you do.

**Concretely.**
- The typer's `type_check_expr` recurses on `OccurrenceId`, keeping `occ_id` in hand.
- Transformer passes consume occurrences and produce occurrences — synthesized IR gets fresh
  occurrences, not bare `Expr` children.
- Per-node data a pass produces belongs on `OccurrenceEntry`, not a
  `HashMap<OccurrenceId, _>` side table — `OccurrenceId` is a dense `Vec` index, so the
  store is already the table.

**The one legitimate peel.** Reading an occurrence's bare `term` to *inspect content at the
current node* (match the functor, read a literal) is fine — that is not recursing, and the
`OccurrenceId` stays in hand. Peeling to *descend* is the violation.

**Eval is different.** Eval *consumes* the IR to produce `Value`s; its recursion bottoms out
in term reduction, so the recursion-unit rule doesn't apply. The weaker rule that does:
**carry, don't discard** — eval keeps the `occ` on its step-stack frame so span / owner /
phase survive into runtime errors and traces.

## Occurrences carry debug identity

Occurrences are the IR's debug substrate. Two design elements support that:

- **`phase: OccurrencePhase`** — a design addition to `OccurrenceEntry`. `Source` for
  occurrences created at load (`mark_expr_span`), `Elaborated { origin: OccurrenceId }` for
  ones synthesized by a later pass, with `origin` back-pointing at the source occurrence.
  Debug tells user-written nodes from compiler-synthesized ones and traces the chain.
- A pass that synthesizes IR gives each synthesized node a fresh occurrence (span inherited
  from the originating source occurrence, `owner` = the enclosing op) — never a bare `Expr`.

With `phase` and the eval frame's carried `occ`, every node — user-written or synthesized —
has a span, an owner, and (if synthesized) an origin chain. That is what makes the IR
debuggable.

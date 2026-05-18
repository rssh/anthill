# Brainstorm plan: HOF inheritance — sharpness vs simplicity

**Status:** Deferred (no driver yet)
**Relates to:** [027.1 §Open question 1](../proposals/027.1-alloc-effect-and-allocator-revision.md) (HOF inheritance + closure-capture appendix), [027.1 §Discharge through higher-order combinators](../proposals/027.1-alloc-effect-and-allocator-revision.md)

## Goal

Decide whether to keep the conservative-union HOF rule indefinitely, or add annotations that allow sharper analysis. The decision also resolves the closure-capture appendix (same conservative-vs-sharp question, redirected from result-aliasing to closure-disposition).

## Trigger to run this session

Don't schedule speculatively. Run when at least one concrete driver surfaces:

- A stdlib operation where conservative over-reporting blocks useful effect-row inference.
- A rustus-pattern codegen case where over-reported effects produce unidiomatic Rust signatures (cf. `docs/rust-forward-mapping.md` §5.6–5.7 — tight discharge yields tight Rust signatures).
- An agent or integration workflow where false-positive effect rows trigger noisy refactors.
- An `examples/github-todo/`-style pluggable-backend case where the over-reported HOF effects break interchangeability.

Until then, the proposal's "ship conservative, revisit later" stance stands.

## Inputs to gather before the session

- **Pattern catalog**: over-reporting patterns in current stdlib (`compose`, `fold`, plus any HOFs added since).
- **Synchronous-callback catalog**: cases in `examples/` (especially `examples/github-todo/`) where a closure is passed and invoked synchronously without being stored.
- **Codegen diff**: concrete Rust signatures that would tighten under each candidate annotation.
- **Precedent one-pager**: comparison of Tofte–Talpin regions, OCaml-style row polymorphism, Rust's `Fn`/`FnMut`/`FnOnce`, Frank's adjustment calculus, Koka's effect handlers.

## Topics to cover

### 1. Real cost of the conservative rule

What concrete code, in what file, fails to type-check tightly today? Driver evidence is the gate — speculation isn't.

### 2. Three candidate annotation families

| Family | What it expresses | Surface impact | Covers |
|---|---|---|---|
| **Result-aliasing markers** | "f's result does/doesn't alias its argument" | Narrowest; signature-level annotation per function-typed param | `compose`/`fold` over-report |
| **Closure-disposition markers** | "this closure is invoked synchronously and discarded" vs "stored long-term" — anthill analog of Rust's `Fn`/`FnMut`/`FnOnce` | Medium; per-parameter annotation | Closure-capture appendix from 027.1 OQ1 |
| **Region polymorphism** | Full Tofte–Talpin lifetime-style regions on effect rows | Largest; pervasive signature changes; new kind on effect parameters | Both above as special cases; future cell-precise `Read[c]` |

### 3. Cross-language fit

- Rust codegen: region polymorphism plays well with lifetimes. Closure-disposition maps naturally to `Fn`/`FnMut`/`FnOnce` traits. Result-aliasing markers translate to borrow shapes.
- Scala codegen: monadic effects — closure-disposition is awkward; region polymorphism is alien. Result-aliasing markers are language-neutral.
- SMT-LIB: irrelevant for any of these — effects don't translate to SMT.

### 4. Migration path

Opt-in (existing signatures stay conservative, annotations sharpen specific call sites) vs mandatory (every signature must classify). Default to opt-in for backward compat. Frame any chosen annotation as a *refinement* that lets the typer make a sharper inference, not as a *replacement* for the conservative default.

### 5. Typer implementation cost per option

- Result-aliasing markers: small (annotation table + check at substitution site).
- Closure-disposition markers: medium (annotation table + escape-detection respects disposition).
- Region polymorphism: large (new region-kind, region-variable scoping, region-equality machinery — months of typer work).

### 6. Confirmation that closure-capture is covered

Verify the chosen direction handles 027.1 OQ1's closure-capture appendix without needing separate machinery. If not, that's a strike against.

## Decision outputs

- Which annotation family (or "stay conservative — no change").
- If any change adopted: phased implementation plan with each phase landing independently.
- Updated 027.1 §"Discharge through higher-order combinators" text, or a fresh 027.2 if scope warrants.
- 027.1 OQ1 collapsed to a settled decision (delete the OQ).

## Not in scope for this session

- Effect-system overhaul beyond HOF inheritance — 027.1's other choices stand.
- Reconsidering whether discharge analysis is the right model — settled by 027.1.
- Re-litigating the value-vs-sort-level target distinction — settled by the catalog reframe.

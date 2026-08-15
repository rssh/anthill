# Brainstorm plan: HOF inheritance — sharpness vs simplicity

**Status:** RESOLVED BY CONSTRUCTION (WI-266, 2026-08-15) — this session was never held, and no longer needs to be. The plan below is kept as the historical record of the question.
**Relates to:** [027.1 §Discharge through higher-order combinators](../proposals/027.1-alloc-effect-and-allocator-revision.md) (rewritten to the shipped rule), [027.1 §Resolved — HOF inheritance](../proposals/027.1-alloc-effect-and-allocator-revision.md) (the decision record that collapses Open question 1)

## Outcome

The session was gated on a driver appearing against the conservative-union rule. **No driver could appear, because the conservative rule was never implemented.** While this plan sat deferred, proposals [045](../proposals/045-effect-sets-and-expressions.md) and [046](../proposals/046-region-tracking-and-effect-derive.md) landed the sharp analysis instead, and today's stdlib is written against it:

```anthill
-- stdlib/anthill/prelude/iterable.anthill:61
operation map[Dst, EffP](c: C, f: (x: Element) -> Dst @ {EffP, -Modify[x]})
    -> Stream[Dst, {E, EffP}]
```

Against this plan's three candidate annotation families, the answer is:

| Family | Outcome |
|---|---|
| Result-aliasing markers | **Not adopted.** The feed-relationship is derived from the operation's *body* (WI-352), so the common case carries no annotation at all; a body-less operation declares it as `[feeds: …]` metadata (046 §4.2), whose carrier landed with WI-087/WI-309. |
| Closure-disposition markers | **Adopted, in effect-row currency.** The 045 `lacks` constraint on a callback binder — `-Modify[x]` — with call-site checking (WI-440) and stdlib consumers in `filter` / `find` / `map` (WI-441). Not an anthill `Fn` / `FnMut` / `FnOnce`. |
| Region polymorphism | **Not adopted.** Tofte–Talpin *substitution* is what the boundary classifier performs (WI-353), but signatures stayed region-monomorphic — the months of typer work this plan priced were not spent. |

The plan's §6 check — does the chosen direction cover the closure-capture appendix without separate machinery? — passes: a captured target is a place like any other, and keep/drop comes from its provenance rather than from a declared callee disposition.

Two topics from §3 and §5 are *not* closed by this and are recorded in 027.1's resolved-question entry: dependent-effect abstraction (a callback whose effect denotes its own binder, pinned by `wi424_iterable_members_test`), and cross-language fit for the emitters (Rust erases arrow effect rows; C++ refuses a denoted-bearing arrow parameter).

---

## Goal

Decide whether to keep the conservative-union HOF rule indefinitely, or add annotations that allow sharper analysis. The decision also resolves the closure-capture appendix (same conservative-vs-sharp question, redirected from result-aliasing to closure-disposition).

## Trigger to run this session

Don't schedule speculatively. Run when at least one concrete driver surfaces:

- A stdlib operation where conservative over-reporting blocks useful effect-row inference.
- A rustus-pattern codegen case where over-reported effects produce unidiomatic Rust signatures (cf. `docs/rust-forward-mapping.md` §5.6–5.7 — tight discharge yields tight Rust signatures).
- An agent or integration workflow where false-positive effect rows trigger noisy refactors.
- An `examples/github-todo/`-style pluggable-backend case where the over-reported HOF effects break interchangeability.

Until then, the proposal's "ship conservative, revisit later" stance stands.

> *Historical.* None of these four drivers ever fired, and none could have: the conservative rule they were watching was not the one in the tree. See §Outcome above.

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

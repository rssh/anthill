# Proposal 044 — Unified name resolution: visible-by-default + import-side disambiguation

## Status

Draft. Drivers:
- The two implementations (`rustland/`, `scaland/`) have **divergent name-resolution algorithms** that have drifted apart; we want one algorithm implemented identically on both sides.
- `docs/kernel-language.md` has **no consolidated name-resolution section** — resolution is described only in scattered prose (§5.1 qualified/short names, §5.1 import forms, §8.6 visibility). The precise scope-walk, the import fallback chain, and the nested-scope lookup (`find_in_nested_scope`) are undocumented.
- The `export` statement is verbose boilerplate in stdlib (41 of 55 files carry one), and the spec's stated "internal by default" (§8.6) does **not** match either implementation.

This proposal records the current behavior, the empirical findings from an attempted "visible-by-default" migration, and a target model. It does **not** change code yet — implementation is gated on resolving the open question in §5.

## Background — resolution as actually implemented (ground truth: Rust)

There is no single spec for this today; extracted from `rustland/anthill-core/src/intern.rs` and `kb/load.rs`.

### Scope model

Each scope holds: `locals` (short_name → Symbol), `imports` (alias short_name → Symbol), `exports` (a set of short names), `parents` (`ScopeInclusion`s, each flagged `is_enclosing`), and `type_params`.

### `resolve_in_scope(name, scope)`

1. `scope.locals[name]` → Found (shadows everything below).
2. `scope.imports[name]` → Found.
3. Else recurse into parent scopes. A **non-enclosing** parent is skipped if `name` is one of its `type_params`, or if the parent has a non-empty `exports` set that doesn't contain `name`. **Enclosing** parents (sort/namespace body nesting) bypass the export filter.
4. Collect, dedup → 0 NotFound / 1 Found / ≥2 Ambiguous.

### Import forms

- **Plain** `import a.b.C` → alias `C` locally + add `a.b` as a non-enclosing parent.
- **Selective** `import a.b.{C}` → alias only; resolved by a 3-step fallback: (1) `by_qualified_name["a.b.C"]`, (2) `resolve_in_scope(C, a.b)`, (3) `find_in_nested_scope` (`a.b.<one-segment>.C`, unique match — resolves an entity defined one scope deeper, e.g. `…platform.ExecutionPlatform.execution_platform`).
- **Wildcard** `import a.b.*` → add `a.b` as a non-enclosing parent.

### What `export` actually does

Two distinct jobs are conflated in the single `exports` set:

1. **User `export X` statements** — restrict what crosses the namespace/sort boundary to importers and requirers.
2. **Auto variant-exposure** (loader-internal) — the loader adds a sort's entity-variant short names to its `exports` and links the sort scope as a non-enclosing parent of the enclosing namespace, so bare `Open` resolves to `WorkStatus.Open` *without* the sort's operations leaking. An **empty** `exports` set disables the filter (everything leaks), so this only restricts sorts that have variants.

## The two implementations diverge

| | rustland | scaland |
|---|---|---|
| User `export` list | enforced whitelist (jobs 1 & 2) | auto-`addExport`s **every** member, so the whitelist never restricts |
| Empty `exports` | "visible to all" default | n/a (never empty) |
| Variant exposure | yes (job 2) | not implemented this way |
| "internal by default" (spec §8.6) | false (empty ⇒ all) | false (everything auto-exported) |

So the spec is wrong on both, and the two engines don't agree.

## Empirical findings (attempted "drop export, visible-by-default" / "Model C")

A prototype that makes resolution ignore the `export` whitelist:

- **scaland:** clean — full suite 167/167 green. Removing the whitelist exposes no colliding names.
- **rustland:** **87 `wi_tests` fail** (baseline 129/0). The representative failure:

  ```
  AmbiguousSymbol { name: "eq",
    candidates: ["anthill.prelude.Eq.eq", "anthill.prelude.Ordered.eq"],
    scope_name: "Numeric" }
  ```

  `Ordered` inherits `eq` from `Eq` (spec auto-binding, §8.7), producing a **distinct** `anthill.prelude.Ordered.eq` symbol alongside `anthill.prelude.Eq.eq`. A scope that sees both as parents (e.g. `Numeric requires Ordered, Eq`) finds bare `eq` twice → `Ambiguous`. Today, `Ordered`'s `export` list **omits `eq`**, suppressing the inherited copy.

**Conclusion:** `export` is *not* decorative in Rust — it is the current mechanism for **disambiguating inherited operations**. "Drop `export`, shorter programs" cannot be done without first replacing that disambiguation mechanism.

## Proposed model

Two parts. Part A is uncontroversial; Part B is the open design question.

### A. Visibility = visible-by-default, `internal` is the only hide gate

- A declaration is visible to importers and across `requires`/wildcard boundaries **by default**.
- `internal`-prefixed declarations are hidden from cross-scope resolution (still resolvable within their own scope).
- `public` keeps its meaning (visible everywhere, even without import).
- The `export` statement and `export` visibility prefix become **no-ops**, then are removed from the grammar (tracked: WI-289). stdlib loses ~41 `export` blocks.
- The loader's **variant-exposure** stays, but moves to a dedicated `exposed` set (auto-populated from entity variants only) so it is no longer tangled with user `export`. Both implementations adopt the same `exposed` mechanism.

This is mechanical *once* Part B removes export's disambiguation duty.

### B. Disambiguation of inherited operations moves to the consumer/import side

The spec already points here (§8.7): *"different namespaces can provide different instantiations of the same spec… a consumer chooses which to use via `import`."* Candidate rules (pick one in review):

- **B1 — provenance/origin dedup.** If the multiple candidates for a bare name all trace to the **same originating definition** (e.g. `Ordered.eq` is the inherited image of `Eq.eq`), collapse them to one — not ambiguous. Requires tracking the origin symbol through `requires`/auto-binding so inherited copies carry a back-pointer.
- **B2 — inheritance aliases, not copies.** `Ordered` gaining `eq` should create an **alias** to `Eq.eq`, not a fresh `Ordered.eq` symbol. Then the two candidates are literally the same `Symbol` and dedup is automatic. (Changes how spec auto-binding materializes inherited operations.)
- **B3 — nearest-wins.** Prefer the candidate reachable through the shortest `requires` chain; ambiguous only on a true tie of distinct origins.
- **B4 — explicit consumer selection.** Keep ambiguity an error, but require the consumer to disambiguate with a selective `import` (which the resolver then prefers). Most spec-faithful, but pushes boilerplate onto consumers.

**Recommendation:** B2 (alias, don't copy) is the cleanest — it makes the ambiguity disappear structurally and matches the intuition that "Ordered's eq *is* Eq's eq." B1 is the fallback if aliasing is too invasive in the typer.

### One algorithm

After A+B, both implementations implement the identical `resolve_in_scope` (locals → imports → filtered parents, where the only parent filters are `type_params`, `internal`, and the `exposed` variant set) and the identical import fallback chain. This is then written into `docs/kernel-language.md` as a new "Name Resolution" section.

## Migration plan

1. **Decide B** (this proposal's review).
2. Implement B (origin tracking or aliasing) in **rustland** first (ground truth); confirm the 87 `wi_tests` pass with `export` whitelisting disabled.
3. Mirror the identical algorithm in **scaland**.
4. Flip visibility to Part A on both; make `export` a no-op; add `exposed` variant mechanism to scaland.
5. Strip `export` statements from stdlib (one mechanical pass; both engines stay green).
6. Document the unified algorithm in `kernel-language.md` (§8.6 rewrite + new Name Resolution section); fix the false "internal by default" claim.
7. Remove `export` from the grammar (WI-289).

## Acceptance criteria

- `rustland` and `scaland` implement the same documented resolution algorithm; a shared cross-impl fixture resolves identically.
- stdlib carries no `export` statements; both engines load it green.
- `internal` hides a name from import/wildcard/parent resolution (tested on both sides).
- The `Eq`/`Ordered`/`Numeric` `eq` case resolves unambiguously with no `export` whitelist.
- `kernel-language.md` has a Name Resolution section matching the implementation.

## Open questions

- **B selection** (origin-dedup vs aliasing vs nearest-wins vs explicit) — the gating decision.
- Does `public` (visible without import) interact with B? Probably orthogonal.
- `find_in_nested_scope` depth: keep it at exactly one intermediate segment, or generalize? (Today: one level, unique match.)
- Should `requires`-inherited operations be walked by resolution at all, or only surfaced through explicit `Sort.op` / dispatch?

## Related

- WI-289 — remove the `export` statement/prefix from the grammar (downstream of step 7).
- Proposal 038 — builtin-sort spec/binding split (introduced the `sort anthill.prelude.X` forms whose inherited operations trigger the `eq` ambiguity).
- §8.7 Algebras (operation auto-binding) — the source of inherited-operation symbols.

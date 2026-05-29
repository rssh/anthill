# Binder types off the hash-consed term store (arrows first)

## Status

Design (2026-05-29). **Internal representation only — no external/language
change.** The surface syntax, semantics, and observable behavior of types are
unchanged; this concerns how arrow (and dependent) types are *represented and
stored* inside the KB. Same category as `occurrence-as-value-type.md` (the
NodeOccurrence migration), which moved expression binders off the hash-consed
store; this extends the same lesson to types.

Drivers:

1. **Principle correction (landed).** `CLAUDE.md` no longer says "types are
   terms." The load-bearing claim is *"we can use logical variables in types as
   in logical terms"* — types **unify** (substitution, occurs-check). Being a
   type does **not** imply being a hash-consed `TermId`. Hash-consing is a
   storage choice for **ground, searched structure** (facts, rule heads, query
   patterns, nominal sort identities); it is **inappropriate for binders**.
2. **WI-341 step 2.** Alpha-equivalence for effect rows that reference a binder
   (`-Modify[c]`, `Modify[result]`) kept colliding with the hash-consed store
   (De Bruijn fighting the rule opener; arrow sharing vs. per-binder identity).
   The difficulty is an **artifact of forcing the arrow binder into the global
   dedup store**, not an intrinsic hard problem. WI-341 step 1 (result-region by
   symbol identity, not spelling) is delivered; this design is step 2.
3. **§5.5 / 046 dependent arrows.** Higher-order calls whose callback row
   references the callback's own parameter (`foreach(λ x → set(x, …))` ⇒
   `{Modify[x]}`) make arrows genuinely *dependent* — effects/return reference
   the binder. That is when the binder aspect stops being ignorable.

## Relates to

- **CLAUDE.md** principle correction (this design is its implementation arc).
- **045 / 046** — effect rows ride on the type representation; alpha-equivalence
  of arrows with binder-referencing effects is needed for §5.5 to type-check
  without spurious rejection.
- **041** — `result` reserved return binder; **042** — operation type params.
- **`occurrence-as-value-type.md`** (WI-242 / WI-246 / WI-251) — the
  NodeOccurrence migration; this is the same lesson extended from expression
  bodies to types. Three concrete connections:
  - It **already reserves a `NodeKind::Type { ... }` future-kind slot** (the
    `// Future kinds … Type { … }` comment in its `NodeKind` enum). Option C
    below fills that slot rather than inventing a parallel mechanism.
  - Its **"which IDs survive" / "four reasons for an arena"** framing is exactly
    the lens here: `TermId`/hash-consing survives only for content with a real
    *hash-consing* justification (structural sharing of ground, searched
    content). Binders have none — they are not structurally shared (alpha-
    equivalence) and not search keys.
  - It explicitly routes **"type terms" → hash-consed `Term`** (its loader
    table + "what stays as-is"). That routing is **correct for non-binder type
    terms** and **expedient, not principled, for binder types** — the boundary
    this design moves.
  - **Caveat it surfaces:** `NodeOccurrence` is fundamentally *positional*
    (span, owner, classification). A type *as written in source* is positional
    (fits `NodeKind::Type`); a type *value the unifier manipulates* (synthesized,
    instantiated, variable-bearing) is **not** positional. This design targets
    the latter — see §5 / Open Questions on whether the binder-aware type *value*
    reuses that substrate or is its own thing.
- **WI-341** — step 1 delivered; this absorbs step 2.
- **WI-328** — effect-label comparison leans on hash-cons identity today
  (works for the symbol-distinguished cases); it migrates with the type rep.

## 1. The distinction the old mantra hid

"Types are terms" conflated two independent claims:

| Claim | Status |
|---|---|
| Types carry **logical variables and unify** (subst, walk, occurs-check) | **Necessary** — the real content. |
| Types are **hash-consed `TermId`s** in the global `TermStore` | **An implementation choice**, not implied by the first. |

Unification needs a structure-with-variables, a substitution, `walk`, and an
occurs-check. It does **not** need global structural deduplication. Hash-consing
buys O(1) structural equality, memory sharing, and discrimination-tree indexing
— all of which pay off for **ground, searched** content and barely (or
negatively) for compound/binder types.

## 2. Why hash-consing fights binders

A hash-consed store wants **canonical, context-free, structurally-deduplicated**
terms: identical structure ⇒ identical `TermId`. A **binder** has
context-dependent identity: `(c: Cell) -> R ! {-Modify[c]}` and
`(d: Cell) -> R ! {-Modify[d]}` are the **same** type (alpha-equivalent), yet
their naive structures differ; and a `result` binder is *distinct per operation*
even though spelled identically. Reconciling "structural identity" with
"alpha-equivalence + per-binder distinctness" inside one global dedup store
forces either:

- **De Bruijn indices inside the shared term** — which collide with the KB's
  existing rule-level `Var::DeBruijn` (opened by `term_from_debruijn`), because
  arrow types appear inside rule/fact terms the rule opener walks; or
- **per-binder fresh `Var::Global`s** — which fragment arrow sharing and turn
  alpha-equivalence into an ad-hoc "unify up to renaming" special case.

Both are taxes paid only because the binder lives in the global store. Today the
tax is unpaid only because arrows are treated as **non-dependent** (effects
reference sorts / external resources, never the binder). The moment effects or
return types depend on the binder (§5.5), the tax comes due.

## 3. What actually wants hash-consing (and what doesn't)

| Content | Searched? | Binder? | Hash-cons? |
|---|---|---|---|
| Facts, rule heads, query patterns | yes (discrim tree) | no | **yes** |
| Nominal sort identities (`by_sort`/`by_domain`/`fact_dedup` keys) | yes | no | **yes** (interned `Symbol`s) |
| Non-binder structural types (`Int`, `List[T]`, `Option[Int]`, `Pair[A,B]`) | no | no | **optional** (sharing is nice, not required) |
| **Arrow / dependent types** | no | **yes** | **no** |

Arrows are not search keys in the discrimination tree (they are *unified* during
checking, not *matched* during SLD). So the indexing benefit barely applies, and
the sharing / O(1)-equality benefits are dominated by the binder tax.

## 4. The change

Give **arrow (and dependent) types a binder-aware representation that is not
hash-consed into the global `TermStore`.** The arrow carries its own parameter
scope **locally**; references from its effects/return to that scope are resolved
within the arrow structure; alpha-equivalence and per-binder distinctness are the
arrow representation's responsibility, not the term store's.

Non-binder structural types may continue to be hash-consed (sharing is a fine
optimization where there is no binder); nominal sort identities stay interned.
The boundary is **binder-ness**, not type-ness.

Difficulties this dissolves:

- **Alpha-equivalence** becomes local: two arrows are equal iff their
  binder-local normal forms match — no global-store canonicalization, no
  cross-arrow symbol collisions.
- **The rule-opener collision disappears**: arrow-internal binder references
  never live in the global term the rule opener walks.
- **`result` and HOF `c`** are ordinary references into an arrow's (or
  operation's) own binder scope — `Modify[result]` is "modify *this* arrow's
  result binder," distinct per arrow by construction, no `<op>.result` name
  surgery and no shared-`Var` fragmentation.

## 5. Representation — peer options (the central open question)

(Framed as peers, no status-quo default.)

- **A. Locally-nameless arrow node.** A dedicated value-typed `ArrowType`
  (Rc-linked, like `NodeOccurrence`) whose binder references are De Bruijn
  indices **local to the arrow** (a separate index space from rule De Bruijn).
  Alpha-equivalence = structural equality of the locally-nameless form. Pro:
  canonical, cheap equality, no capture. Con: a second De Bruijn discipline.
- **B. Explicit-named-scope arrow node.** The arrow carries an explicit binder
  list (`params`, `result`) and references are names resolved within that scope;
  unification aligns binders positionally ("unify up to alpha"). Pro: readable,
  no index arithmetic. Con: equality/dedup is up-to-alpha, not structural.
- **C. Fill the reserved `NodeKind::Type` slot.** Types ride the value-typed,
  Rc-linked, binder-capable substrate `occurrence-as-value-type.md` already
  defined (the reserved `Type { … }` kind), and reflection binds them via the
  existing `Value::Node(Rc<NodeOccurrence>)` carrier. Pro: one binder story for
  expressions *and* types; fills an anticipated slot; no new value carrier. Con:
  `NodeOccurrence` is **positional** (span/owner/classification) — a great fit
  for a *source-written* type occurrence, an awkward fit for a *synthesized /
  instantiated* type **value** the unifier mints with no span. May split into
  "type occurrence = `NodeKind::Type`" vs "type value = its own binder-aware
  thing."
- **D. Hybrid shell.** Non-binder types stay hash-consed `TermId`; an arrow is a
  thin `TermId` leaf/opaque handle that *points at* an out-of-store binder node
  (A/B), so existing `TermId`-typed slots keep compiling while binders live
  out-of-band. Pro: smallest blast radius, incremental. Con: reintroduces a
  handle indirection reminiscent of the deleted `HandleKind::Occurrence` — must
  not recreate its problems.

Leaning (to refine, not fix): the **type value** the unifier manipulates wants
**A** (locally-nameless, non-positional, cheap structural alpha-equality), or
**D-over-A** during migration; a **source-written type occurrence** can fill
**C**'s `NodeKind::Type` slot (it *is* positional). The two need not be the same
representation — keeping them distinct avoids forcing span/positional baggage
onto synthesized type values. The exact encoding is the decision this document
exists to force; see Open Questions.

## 6. Touch-points (to scope the staged work, not to do at once)

Types are woven as `TermId` through the codebase:

- `kb/term.rs` — `Type.*` entities are `Term::Fn` today; arrow becomes a binder
  node (or shell + node).
- `kb/typing.rs` — `unify_types` / `unify_arrow` gain a binder-aware arrow arm;
  `arrow_parts`, `effects_rows_*`, the WI-307 row functions consume it.
- `kb/subst.rs` — `Substitution` binds `VarId → Value` (`Value::Term(TermId)`
  dominant). A non-`TermId` arrow needs a `Value` carrier (`Value::Type`?), or
  stays reachable via the shell (D).
- `kb/op_info.rs` — `OpInfoRecord` references types as `TermId`
  (`params`, `return_type`, `effects`).
- `kb/region.rs` — result/region effects (WI-314); `result` becomes an
  arrow/op binder reference instead of a qualified symbol (subsumes WI-341 step 1).
- `persistence` / `reflect` / `codegen` — type printing/reflection read types as
  terms today.
- `scaland` — mirrors the Rust type representation (note the parallel impact;
  the recurring "scaland lags" pattern).

## 7. Staging

1. **Adopt the principle** — done (CLAUDE.md). Stops new work doubling down on
   hash-consed binders (e.g. the abandoned De-Bruijn-in-store step-2 plan).
2. **Arrows first.** Both the binding *and* the cost live in the arrow. Pick the
   representation (§5), introduce the binder-aware arrow, route `unify_arrow`
   and the row functions through it, keep non-binder types as-is.
3. **Dependent effects/return (§5.5 / 046).** Once arrows are binder-aware,
   `-Modify[c]` / `Modify[result]` / dependent returns are local references —
   the alpha-equivalence and well-scopedness properties 045/046 need fall out.
4. **(Optional, later)** revisit whether other compound types benefit from
   leaving the store; likely not.

Non-goals: removing hash-consing for facts/rules/nominal identities; migrating
non-binder structural types; building §5.5 region analysis (that's 046).

## 8. Open questions

1. **Representation (§5 A–D)** — the central call. Sub-question:
   **type occurrence vs type value** — are a source-written type (positional,
   `NodeKind::Type`) and the unifier's type value (non-positional, binder-aware)
   one representation or two? `occurrence-as-value-type.md` reserves the slot for
   the former; this design's hard part is the latter.
2. **Substitution carrier** — how a non-`TermId` arrow sits where the subst
   binds `VarId → Value`. Reuse the existing `Value::Node(Rc<NodeOccurrence>)`
   (if types ride `NodeKind::Type`), add a `Value::Type`, or keep a `TermId`
   shell facade (D).
3. **Equality / caching** — without hash-cons identity, what backs the fast
   paths that use `TermId ==` today (`a_effects == b_effects`, dispatch caches)?
   Per-node canonical hashing, or up-to-alpha equality with memoization?
4. **Reflection** — a binder-aware arrow needs a reflected shape (does
   `denoted` / `effects_rows` change? cf. WI-328 / WI-341).
5. **Scala port** — parallel impact in `scaland`.
6. **042 interaction** — operation type-params are binders too; do they share
   the arrow's binder mechanism?

## 9. What "done" looks like (staged)

- Principle adopted in CLAUDE.md (done).
- An arrow with a binder-referencing effect (`(c: Cell) -> R ! {-Modify[c]}`) is
  **alpha-equivalent** to its renamed twin under unification, with **no** De
  Bruijn indices in the global term store and **no** collision with rule-level
  De Bruijn — pinned by a test.
- `Modify[result]` distinctness/identity carried by the arrow/op binder, not by
  `<op>.result` name surgery (subsumes WI-341 step 1's registry).
- v1a row tests, WI-328 lacks tests, WI-314 region tests stay green through the
  migration; full `cargo-test` green.

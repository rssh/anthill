# Kernel Desugaring Vocab — Provenance-Based Resolution

## Status: DELIVERED (2026-06-20)

**WI-040** (commit `88ae38c`) and **WI-521** (commit `7688c83`) both shipped. The
mechanism that landed is the **reserved-name / lowest-precedence fallback** (this
doc's "Primary approach" below), *not* node-keyed converter provenance (kept below
as a documented escape hatch only) and *not* a literal `anthill.prelude` import
edge. Concretely: one `pub(crate) fn implicit_qualified(name)` =
`kernel_vocab_qualified(name).or_else(prelude_qualified(name))` over two
fully-qualified `&[&str]` lists, consulted *after* scope resolution fails in
**three** resolvers — `remap_name_str` (loader), `resolve_name_in_kb_opt` (query
patterns), and `KnowledgeBase::resolve_name_in_global` (the reflect bridge). A user
name in scope always wins, so a name can never go `Ambiguous` against a user name —
which dissolved the WI-476 collision blocklist. The boolean-`!` / NAF-`not` split
was deferred to **WI-529**. The rest of this doc is the design reasoning that led
there; read §"Primary approach" for what shipped.

This is an **implementation design** doc, not a proposal. There is no user-facing
language change here — the surface syntax (`match` / `if` / `let` / `lambda`,
member access `x.f`, list/set/tuple literals) is unchanged. This doc covers how
the *compiler-internal* names those constructs desugar to should be resolved,
replacing the current global-import scheme.

Tickets: **WI-040** (reframed to Part A — this design). **WI-521** (Part C — the
Prelude-surface decision, §C below). Background on the current scheme: **WI-476**
(deleted the `resolve_by_short_name` fallback, and in its place global-imported the
kernel desugaring vocab). Collection-literal type-direction: **WI-007 / WI-285 /
WI-393**.

## The problem

The converter and loader synthesize names a user never writes — the reflect
`Expr` / `Pattern` constructors for desugared `match` / `if` / `let` / `lambda`,
`field_access` for member access, the literal *carriers* `ListLiteral` /
`SetLiteral` / `TupleLiteral`, and reflection primitives (`as_term`,
`occurrence_*`, …). The converter emits each as a plain short `Symbol` in the
parse-IR symbol table (`convert.rs` `intern("field_access")` at ~743,
`intern("let_expr")` at ~1511, `intern("ListLiteral")` at ~1408, …), with **no
marker** distinguishing it from a user-written identifier of the same name.

Because the name carries no provenance, the loader can only resolve it the way it
resolves any name: by scope. So WI-476 made these names visible by
**global-importing them into `_global`** — a hardcoded list `KERNEL_VOCAB_QUALIFIED`
(`load.rs` ~740–778) registered by `register_kernel_vocab_imports` at the end of
`scan_definitions` (~731), plus the older per-name imports for the literal carriers
(`load.rs` ~2404–2406).

This works, but it puts compiler-internal names into the **user's** name-resolution
namespace, which forces a **collision blocklist**: `kind` / `fields` / `rules` /
`kb` / `constructor` / `not` are deliberately *excluded* from the vocab list
(`load.rs` ~765–770) because a user might write `rule kind(…)` / `entity constructor`,
and a global import would silently shadow it. The blocklist is the tell — you only
need it because two namespaces that should be disjoint share `_global`. It is also
fragile: every new desugaring name is a new collision question, resolved by hand.

## The model

A kernel-synthesized reference is **not a name lookup**. When the converter
desugars a `match`, it is referring to *the* `anthill.reflect.Expr.match_expr` —
a definite, known entity — not "whatever `match_expr` resolves to in this scope."
The only reason it currently round-trips through scope resolution is an accident
of the convert/load split: at convert time the KB does not yet exist (the prelude
is not loaded), so the converter cannot hand back a KB `Symbol` — it emits a short
name and defers resolution to load.

**Carry the provenance across that split.** Tag, at the converter, the fact that a
functor is a *kernel reference to qualified target Q*. At load, resolve a kernel
reference by **direct `by_qualified_name[Q]` lookup**, never `resolve_in_scope`.
Then nothing kernel-internal ever enters the user namespace, and the blocklist
disappears: a user writing `match_expr` as an identifier is simply a normal name
(resolvable, or a loud unknown), never a silent shadow of a kernel constructor.

## The three-way split

The vocab the global-import scheme lumps together actually divides by *who emits
the reference and when*. Each kind has a different correct home. This split is the
load-bearing content of this doc.

### A. Converter-static vocab → converter provenance (this design)

Names the converter always emits by a fixed static name:

- reflect `Expr` constructors: `match_expr`, `if_expr`, `let_expr`, `lambda_expr`,
  `ho_apply`, `dot_apply`, `var_ref`, `int_lit`, `bigint_lit`, `float_lit`,
  `string_lit`, `bool_lit`
- reflect `Pattern` constructors: `var_pattern`, `tuple_pattern`,
  `named_tuple_pattern`, `constructor_pattern`, `literal_pattern`, `wildcard`
- reflection primitives: `field_access`, `as_term`, `source_span`,
  `occurrence_owner`, `occurrence_span`, `occurrence_term`, `sub_occurrences`
- **the literal carriers**: `ListLiteral`, `SetLiteral`, `TupleLiteral`

The converter knows the qualified target of every one of these statically. They
are exactly the set this design resolves by provenance, and exactly the set whose
global imports (the `KERNEL_VOCAB_QUALIFIED` list + the carrier imports at
~2404–2406) and collision blocklist this design **deletes**.

Note the literal *carriers* belong here even though collection literals are
type-dependent (see §B): the carrier `ListLiteral` is a fixed name the converter
always emits for `[…]`; what is type-dependent is the *constructor it later lowers
to*, which the converter never emits.

### B. Type-directed collection constructors → already direct, nothing to tag

`cons` / `nil`, and the set/tuple constructors, are **not** converter-emitted. A
collection literal is type-dependent: the converter emits a neutral carrier
(`Fn{ functor: ListLiteral, … }`, `convert.rs` ~1397–1447) and the concrete
constructor is chosen *downstream, from the resolved type*:

- **Loader rule/fact path** (`convert_term_with_expected`, WI-007, `load.rs`
  ~5427–5444): rewrites `ListLiteral → cons/nil` **only when the `expected` type
  is List-shaped**; otherwise the `ListLiteral` carrier survives into the KB for
  the carrier-provider machinery. The `cons`/`nil` come from `build_list_with_tail`,
  which resolves `kb.resolve_symbol("anthill.prelude.List.cons")` — **a direct
  qualified lookup**.
- **Typer occurrence path** (`TypeBuildFrame::ListLit`, `typing.rs` ~4054–4088):
  does not lower to `cons`/`nil` at all — it infers the element type
  (type-directed, from elements or `element_hint`) and builds the *type*
  `List[T = elem]` via `make_sort_ref_by_name("anthill.prelude.List")` — again
  **direct, qualified**. Value-level materialization is deferred to eval
  (`eval.rs` ~1580, via resolved reflect symbols) — also direct.

So **every concrete collection constructor/type is already resolved by direct
qualified lookup**, end to end. There is no parse `Symbol` to carry provenance on
(the producer is Rust code naming the FQN literally), and no need — these paths
never touched the global imports. Provenance neither can nor should reach into the
typer; the typer is an independent direct-resolver.

Consequence: committing `[…] → List.cons` *at the converter* would be wrong — the
type-dependence means the carrier must stay neutral until the type is known. (The
WI-040 feedback's literal suggestion, "build cons chains directly when desugaring,"
predates WI-007/285/393 and has the wrong shape; the right shape is neutral-carrier
+ type-directed lowering, which the code already implements.)

### C. User-facing names → auto-imported Prelude (WI-521, decided)

Everything a user can legitimately name comes from one place: a real, auto-imported
Prelude. This covers two groups currently flat-injected into `_global`:

- **Bare constructors** `cons` / `nil` / `some` / `none` (`load.rs` ~2393–2396).
  The *list-literal* path resolves `cons`/`nil` directly via the §B builders, so
  these imports serve only a user writing `cons(x, xs)` / `some(v)` *explicitly*.
- **Operator targets** `add` / `sub` / `mul` / `eq` / `neq` / `lt` / `gt` / … and
  the arithmetic/comparison block (~2419–2436). Note these *are*
  converter-synthesized: the infix desugarer (`parse/pratt.rs` ~50–58) lowers
  `+`→`add`, `=`→`eq`, `<`→`lt`, … via `symbols.intern(entry.functor)` — a plain
  short symbol that today resolves through scope to the `_global` import. So `a + b`
  uses these imports just as much as an explicit `add(a, b)` does.

**Decision (2026-06-19): operator targets resolve via the Prelude, *not* via
provenance.** They are converter-synthesized and could be folded into Part A — but
they denote *user-facing* spec ops (`Numeric.add`, `Eq.eq`), so the cleaner rule is:
one source for every user-nameable name. The cost is the Haskell model — `1 + 2`
is Prelude-dependent (it fails if a namespace hides/lacks the Prelude). Do **not**
"optimize" operators into the node-keyed provenance table; that split was considered
and rejected here.

**WI-521** therefore builds a real, named, **shadowable** `anthill.prelude` Prelude
module that every namespace *implicitly imports* via a genuine import edge,
replacing the flat `add_import(_global, …)` injection (a user's local `eq` shadows
the Prelude `eq`; `Numeric.add` still dispatches to user instances under `+`). It is
sequenced after WI-040 (so `_global` holds no kernel-internal names by then) but
touches disjoint imports, so it does not conflict. Part A (WI-040) is purely
compiler-internal names; Part C (WI-521) is purely user-facing names. They must not
be conflated again.

## Two loader paths (derisk, 2026-06-20)

A read-only probe of the loader corrected a wrong assumption in the first draft:
there are **two** paths that turn a parse term into a resolved KB term, and they
handle the kernel vocab *differently today*.

1. **Op-body path** (`build_load` / `LoadBuildFrame`, load.rs ~6223+). The
   synthesized Expr/Pattern frames (`MatchExpr`, `IfExpr`, `LetExpr`, `Lambda`,
   `PatternConstructor`, `PatternTuple`, `DotApply`) are built from
   **`ExprBuilderSyms`** (load.rs ~4785), a struct whose fields are populated by
   **direct `kb.resolve_symbol("anthill.reflect.Expr.match_expr")`** lookups. This
   path **already resolves the vocab directly**, scope-independently — it is
   *frame-structural provenance* (the `LoadBuildFrame` variant itself is the
   "synthesized" tag) and does **not** rely on the `_global` imports. Only user
   `ApplyOrConstructor` frames go through `remap_symbol`. **Nothing to change here.**

2. **Rule/fact term path** (`convert_term_with_expected`, load.rs ~5334). Resolves
   *every* functor — including synthesized `field_access` (from `x.f`), `dot_apply`,
   and the literal carriers — as a generic `Term::Fn` via `remap_symbol` (~5425) →
   the `_global` import. This is the **only** path that genuinely needs node-keyed
   provenance, because here name alone cannot distinguish a synthesized
   `field_access` from a user identifier `field_access`.

So this design's mechanism applies to **path 2 only**. The op-body path is the
existence proof that direct resolution works; node-keyed provenance is simply how
path 2 catches up, since (unlike path 2's generic `Term::Fn`) the op-body builder
already knows structurally which nodes it synthesized.

The reflect Expr/Pattern *constructor* names (`match_expr`, `if_expr`, …) are
defined in `reflect.anthill` (self-scope); a grep finds no stdlib rule naming them
bare via the `_global` import, so deleting those imports is likely safe — but
**confirm against the `reflect.typing_pass` reflection rules** before deleting, in
case a reflection rule body relies on the bare name.

## Primary approach (2026-06-20): reserved names, direct resolution

The synthesized vocab **already has reserved qualified homes** — every name lives in
`anthill.reflect.*` (the `Expr`/`Pattern` constructors, `field_access`, `dot_apply`,
`occurrence_*`), `anthill.prelude.List.*` (`cons`/`nil`), or `anthill.kernel.*`. So
the simplest correct fix is not provenance at all: **treat these as kernel-reserved
names and resolve every synthesized reference directly to its qualified target**,
the way path 1's `ExprBuilderSyms` already does. Generalize that resolved-symbol
cache to path 2 (`convert_term`): for the names `convert_term` itself synthesizes
(`field_access`, `dot_apply`, the literal carriers), resolve via a direct
name→qualified map instead of `remap_symbol`. Both paths then bypass `_global`
entirely.

**Why this needs no node-keying and no collision blocklist.** Node-keying was the
draft's answer to "a user might write `match_expr` and mean their own thing." But
the names the converter actually *synthesizes* are kernel-owned and not plausible
user definitions — and the genuinely user-definable names the blocklist guarded
(`kind`, `fields`, `rules`, `kb`, `constructor`) are **not in the synthesized set at
all** (grep of `convert.rs` finds no `intern("kind")` etc.; they are reflect-API
names that resolve via explicit import and are untouched). So a synthesized
reference resolving unconditionally to its reserved qualified target shadows
nothing. We stop `_global`-importing the synthesized vocab entirely, and the
blocklist dissolves because there is no longer a kernel/user name overlap in
`_global` to guard.

This collapses WI-040 to: **path 2 mirrors path 1** (a direct name→qualified map),
plus deleting the `_global` imports of the synthesized vocab and the blocklist.
No `ParsedFile` change, no converter side-table.

The one accepted trade-off: a reserved name (`field_access`, `match_expr`, …)
becomes **non-shadowable** — a user cannot define their own `field_access` operation
that wins over `reflect.field_access`. Given these are kernel desugaring targets,
that is the correct semantics (it matches how `+`/`match` are reserved). If a future
desugaring ever needs a name that *is* legitimately user-definable, the node-keyed
provenance mechanism below is the escape hatch — but the current vocab needs none of
it.

The candidate namespaces the user floated (`reflect` / `kernel` / `bootstrap` /
`prelude`) are about *where* the reserved ops live. The existing `reflect` / `kernel`
/ `prelude.List` homes already suffice; a dedicated `anthill.kernel` (or a new
`anthill.bootstrap`) namespace consolidating them is optional polish, not required.

## Fallback mechanism: node-keyed provenance

> Retained for the record and as the escape hatch named above. **Not needed for the
> current synthesized vocab** — prefer the reserved-name approach. Node-keying earns
> its cost only for a synthesized name that genuinely collides with a user-definable
> name in the same position; the present vocab has none.

## Production: converter side (`parse/convert.rs`)

Provenance must key on the **emitted node**, not the symbol. The converter interns
`match_expr` to the *same* `Symbol` whether it synthesized the node or a user typed
`match_expr` as an identifier — so a `Symbol`-keyed table would hijack the user's
occurrence exactly as the global import does today (see §"Why node-keyed"). Tag the
`TermId` the converter allocates instead:

```rust
/// Alloc a kernel-synthesized functor node and record its qualified target.
/// The short name stays in the term (printers/tests see it unchanged); the
/// recorded `TermId` is what the loader resolves directly, scope-independently.
fn kernel_fn(&mut self, short: &str, qualified: &'static str,
             pos: SmallVec<[TermId; 4]>, named: SmallVec<[(Symbol, TermId); 2]>,
             span: Span) -> TermId {
    let functor = self.symbols.intern(short);
    let id = self.terms.alloc(Term::Fn { functor, pos_args: pos, named_args: named }, span);
    self.kernel_refs.insert(id, qualified);   // HashMap<TermId, &'static str>
    id
}
```

Route every Part-A emission site through it (the literal carriers via the
equivalent on their `alloc_fn_term`/build path). The short→qualified table is
exactly today's `KERNEL_VOCAB_QUALIFIED` (load.rs ~740–778) plus the three carriers
— it **moves** from the loader to the converter, where the knowledge actually lives
(the converter is the thing that knows it emitted a `match_expr`). A single helper
makes every future desugaring name a one-line addition with no collision question.

`kernel_refs` rides on `ParsedFile` alongside `symbols` / `terms`
(`parse/ir.rs` ~77–81).

## Consumption: loader side (`kb/load.rs`)

Because provenance is node-keyed, the guard lives at the **conversion site that
holds the parse `TermId`** — `convert_term_with_expected(parse_id, …)` (~5334),
which already resolves the functor via `remap_symbol(functor)` at ~5425 — not
inside `remap_symbol` (which sees only a `Symbol`). The `Term::Fn` arm gains a
front guard:

```rust
// at the top of the Term::Fn arm in convert_term_with_expected, parse_id in scope
if let Some(&q) = self.parsed.kernel_refs.get(&parse_id) {
    // Kernel reference: direct, scope-independent. Loud if the stdlib
    // invariant is broken — these targets are guaranteed loaded.
    let functor = *self.kb.symbols.by_qualified_name.get(q)
        .unwrap_or_else(|| panic!("kernel vocab {q} not loaded"));
    // …reuse the existing Fn rebuild with this functor instead of remap_symbol…
}
```

The carrier handling at ~5425 (`new_functor = self.remap_symbol(functor)`, where
`functor` is `ListLiteral`) now takes its functor from this guard instead of the
global import, so the WI-007 desugaring downstream is unaffected.

The **op-body path needs no guard** (see §"Two loader paths"): its synthesized
frames already resolve directly via `ExprBuilderSyms`. An alternative to the
converter side-table — worth weighing during implementation — is to give path 2 the
same treatment structurally: where `convert_term_with_expected` *itself* synthesizes
a node (e.g. the `field_access`/`dot_apply` it builds from a parse `field_access`),
resolve via a cached `ExprBuilderSyms`-style symbol directly, and reserve node-keyed
`kernel_refs` only for cases where path 2 cannot tell synthesized from user-written
structurally. If every synthesized node in path 2 turns out to be loader-recognizable
(as the op-body frames are), the converter side-table may be unnecessary and the
whole fix collapses to "path 2 mirrors path 1." Resolve this before building the
side-table — it is the crux of the remaining design work.

## Why node-keyed (and not a `Term` variant)

Provenance is carried as `kernel_refs: HashMap<TermId, &'static str>` on
`ParsedFile`, keyed on the emitted parse node.

**Node-keyed, not symbol-keyed — this is what kills the blocklist.** The whole
point of Part A is that a user writing `match_expr` / `kind` / `constructor` /
`rule kind(…)` resolves to *their own* meaning, not the kernel one. A `Symbol`-keyed
table fails that: the converter and the user intern the same string to the same
`Symbol`, so tagging the `Symbol` re-hijacks the user's occurrence — the blocklist
problem relocated, not removed. Tagging the *node* the converter allocated means a
user-written occurrence is a different `TermId`, untagged, and falls through to
ordinary scope resolution (their definition, or a loud unknown). The blocklist then
has nothing to guard and is deleted.

**A side-table, not a `Term::KernelRef` variant:**

- The term shape stays `Term::Fn { functor: <short sym> }`, so the printer
  (`persistence/print.rs`), hash-consing, `Term::subterms()`, and the many tests
  that match on functor *name* are all untouched — near-zero blast radius.
- A new `Term` variant must be threaded through every `Term` consumer.
  `Term::ParseAux` (WI-271) is precedent for a parse-only variant, but it is
  `unreachable!` KB-side; a kernel reference must survive *into* conversion, so a
  variant would be more invasive, not less.
- Provenance is metadata *about a specific occurrence*, not a structural
  distinction in the term. A node-keyed side-table models that honestly.

## What gets deleted

**By WI-040 (Part A):**

- `register_kernel_vocab_imports` and the `KERNEL_VOCAB_QUALIFIED` global-import
  list (`load.rs` ~731, ~740–788). The list's contents move to the converter as
  the `kernel_fn` short→qualified table.
- The literal-carrier global imports `ListLiteral` / `SetLiteral` / `TupleLiteral`
  (`load.rs` ~2404–2406).
- **The entire collision blocklist** — the `kind` / `fields` / `rules` / `kb` /
  `constructor` / `not` exclusion and its rationale comment (`load.rs` ~765–770).
  With no kernel-internal names in `_global` *and* node-keyed provenance, there is
  nothing to collide with.

**By WI-521 (Part C), separately:** the flat `add_import(_global, …)` of the
user-facing names — `cons` / `nil` / `some` / `none` (~2393–2396) and the
arithmetic/comparison block (~2419–2436) — replaced by the implicit Prelude import.

Not touched by either: the WI-476 deletion of `resolve_by_short_name` and the
`NotFound → bare intern` behavior in `remap_name_str` (~5103–5111), which remain
correct. (The reflect `*Info` sorts and `not`/`push_choice`/`or` at ~2397–2417 are
neither converter-synthesized nor plain prelude operators; categorize them when
WI-521 lands — likely explicit stdlib imports.)

## Regression guard

The test that proves the win — and is the real guard, in the project's
loud-over-silent spirit — is that **a user definition colliding with a former
blocklist name now loads without silent shadowing**: e.g. a program with
`rule kind(…)` or `entity constructor` (or `entity match_expr`, exercising a
Part-A name) loads and resolves to the *user's* definition, with the kernel
desugaring still resolving its own `match_expr` correctly via provenance. That is
exactly the case the blocklist was hand-guarding; under this design it is correct
by construction rather than by maintained exclusion.

Plus the existing full workspace suite must stay green — the guard sits on the main
term/occurrence conversion path (around `remap_symbol`), so the change is a cascade
and must be verified end to end (`scripts/test.sh`).

## Open questions

- **Inventory completeness.** Part A lists the names known today. The migration's
  main labor is finding *every* Part-A emission site in `convert.rs` (they are
  scattered — `field_access` ~743, `dot_apply` ~1386, `let_expr` ~1511, the
  literals ~1397–1447, and more) and routing each through `kernel_fn`. A missed
  site stays silently working *while the global imports exist* (the `_global` import
  still catches its untagged node), then — once those imports are deleted — falls
  through to `resolve_in_scope` and becomes a loud unknown-functor error at load.
  That loud failure is the *correct* mode, but it only fires for paths the tests
  exercise. So the migration needs a **completeness check**: confirm that *no*
  Part-A name reaches `resolve_in_scope` at all. Cheap form — full suite green
  implies no missed site on tested paths. Thorough form (recommended) — temporarily
  instrument `resolve_in_scope` to log any call whose name is in the Part-A set, run
  the suite, and require zero hits (the same probe technique WI-476 used on
  `resolve_by_short_name`). This is a one-time migration audit, unrelated to the
  loader's `scan_definitions` sub-passes.
- **Cross-implementation.** Scala (`scaland/`) mirrors the loader but does not load
  operations (see the dual-impl notes); whether it needs the same treatment depends
  on how far its desugaring goes. Out of scope here; flag if the two diverge.

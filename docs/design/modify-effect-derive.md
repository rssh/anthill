# `effect_derive` for `Modify` — feed-relationships, binder identity, masking

**Status:** design (implementation strategy). **Date:** 2026-05-30.
**Realizes:** proposal `046-region-tracking-and-effect-derive.md` (the `Modify`
slice of `effect_derive`) on top of proposal `045-effect-sets-and-expressions.md`.
**Builds on:** `kb/region.rs` (WI-314 boundary masking), WI-328 lacks-constraints,
WI-341 binder-identity-as-logic-var, WI-342/348 value carriers.
**Companion:** `docs/brainstorms/region-analysis-organization.md` (where the
analysis lives), `docs/design/value-facts-carrier-agnostic-resolver.md` (how
`OperationInfo` carries denoted metadata).
**Tracking:** WI-351 (`op.param` places — shared prerequisite) → WI-358
(single-param named-arrow grammar) → WI-352 (load-time flow-derivation pass) →
WI-353 (`region.rs` op-boundary classifier — **delivered** `ef9aae5`, masking
only) → WI-341 (binder-as-value-var / loader binder context) + WI-342
(entity-representation migration) → WI-360 (front-end emit of a callback's
`Modify[a]` → place `f.a`, activates WI-353 end-to-end); WI-354 (in-operation
rule ergonomics, deferred). The `find`-style `-Modify(a)` *checking* direction
rides on WI-341.

## The question

046 fixes the *form* of `effect_derive` (the 4-argument input, the well-scoped
output) but leaves three implementation bodies open: reading the
feed-relationship, region abstraction, and the binder representation that lets a
callback parameter survive into a caller-scope effect row. This document pins
down **how those three plug into machinery that already exists**, and in
particular settles the representation question:

> A callback's effect row mentions the callback's *own parameter* —
> `p : a -> Bool @ { ?E, -Modify(a) }`. `a` is bound by `p`'s arrow and is
> meaningless to the caller (046 §1). How is `a` represented so that (i) the
> signature is well-scoped, (ii) it unifies against an actual predicate at a
> call site, and (iii) a higher-order op can propagate it into its own output
> row?

The short answer: `a` is **a binder, represented the same way rules already
represent binders** — De Bruijn in storage, opened to a fresh logic var at use.
Once that is true, two of the three "open details" stop being new work: the
purity-constraint case (`find`) falls out of the *existing* WI-328
lacks-check, and only the propagating case (`foreach`/`foldLeft`) needs the new
feed analysis.

## 1. The algorithm is not Tofte–Talpin

Tofte–Talpin infer **regions and effects together**, with region-polymorphic
`letrec` and a **fixpoint over region equations** spanning the whole program —
they answer "what region does every allocation live in." Anthill does not need
that. The regions are already in hand: a `Modify[c]` label names a concrete
resource, and `region.rs` already masks at the operation boundary
(`op_boundary_effects`). What 046 adds is one bounded, **per-operation** question:

> For a higher-order op, **where does each callback parameter get fed from**,
> expressed in the op's *own* args / retval?

That is a shallow **forward dataflow over the op body**, not a global fixpoint:

1. Walk the body for `apply(f, e)` nodes where `f` is a higher-order parameter.
2. Find `e`'s **origin(s)** — which of the op's own data it comes from, read as
   relations off the body (`member(e, xs)`; the accumulator chain; a field of an
   argument; a fresh local). See §3 for the relational form.
3. The callback's latent `Modify[its-param]` instantiates to `Modify[e]`; the op
   then runs each origin through the **boundary classifier**
   `region.rs:op_boundary_effects` — the *same* keep/drop decision WI-314 already
   makes (region.rs:176):
   - origin is another **argument** → keep, re-keyed to that argument;
   - origin reaches the **retval** → keep, re-keyed to `result` (exactly the
     `result_type_admits_region` test, region.rs:113);
   - origin is a fresh **local** that does not escape → drop.

**"Let masking decide" = run the origin(s) through `op_boundary_effects`** — that
function *is* the decision (keep params + result-escaping regions, drop
non-escaping locals). Nothing else "decides"; the phrase just means the per-origin
keep/drop is the existing boundary classification, not a new rule.

A *single* origin classifies directly. **"Mixed" provenance** means an origin has
**more than one** source at once — `foldLeft`'s accumulator is both the seed `z`
(a parameter → kept) *and* `f`'s own outputs (fresh regions → kept iff they escape
via the result, else dropped). There is no merged verdict to invent: each
component is classified independently by the same `op_boundary_effects`, and the
result is the union of the kept ones. The accumulator is loop-carried, so deriving
its component *set* from the recursive `seed_or_result` relation is a **provenance
fixpoint** — but over the *finite* lattice `{ param, fresh-output, local }`, so it
stabilizes in one unfold (base `z`, step `f`'s result); it is **not** T&T's
region-equation fixpoint. Producing that component set is the one genuinely
deferred body (046 Open detail #1); the decision *over* it is just
`op_boundary_effects` run per component.

So T&T's "letrec + region-unification fixpoint" collapses to **provenance
classification of fed values, cached once per op.** This *is* the classifier
`op_boundary_effects` already is; 046 grows its category set from
`{ result, local, param }` to `{ input-arg, fresh-output, local, callback-fed }`.

## 2. Binder identity — the representation, and why unification "just works"

`Modify[a]`'s problem is that `a` is a **binder of the callback's arrow**. Two
scopes need to name it:

- **Inside the callback's own arrow** (`a -> Bool @ { …, -Modify(a) }`): `a` is
  bound by *that arrow*. Represent it alpha-canonically as a **De Bruijn param
  index local to the arrow** (param 0). Then `find`'s `p` and an actual
  `q : c -> Bool @ { Modify[c] }` compare and print identically — `a` and `c` are
  the same binder.
- **From the enclosing op's frame** (where a `fed` rule references it): name it
  by the qualified param — `foreach.f`'s parameter (positionally `_2_1` = "arg 2,
  param 1"). This is the *same binder* seen from the operation's frame. A `fed`
  rule relates it to the op's data — `fed(foreach.f, ?x) :- member(?x, foreach.xs)`
  (§3).

`_2_1` is not a new kind of thing: it is the **value-level analog of
`Var::DeBruijn(n)`** — the alpha-invariant coordinate of a binder, exactly what
rules store today.

### Unification: open the binder, don't match the name

The substitutions unify **the same way rules already do** — store De Bruijn,
**open to a fresh `Value::Var` at the call site** (`term_from_debruijn` /
`with_fresh_vars` + WI-109 `Value::Var`). This is the mechanism WI-341 already
identified as the correct replacement for today's `substitute_ref_syms`
(param-symbol → arg-symbol *string* substitution, which is precisely why
`-Modify(a)` cannot unify cleanly now). Walk through `find(l0, q)` where
`q : Cell[Int64] -> Bool @ { Modify[c] }`:

```
open find's sig:   T fresh; callback arrow param a → fresh value-var V
unify p ~ q:       arrow params align   V ~ q's-param-var  → V := that var
                   effect rows unify     -Modify(V)  vs  q's { Modify[V] }
                   → WI-328 lacks-check sees present + absent on the SAME var
                   → REJECT   (find demands a non-modifying predicate; q modifies)
```

So for the **checking** direction (`find`'s `-Modify(a)`) there is **no feed
machinery at all**. Once callback params are arrow-bound value-vars opened on
unification, the *existing* WI-328 lacks-constraint side-table does the whole
job: `-Modify(a)` becomes `-Modify(V)`, `q`'s `Modify[V]` clashes, reject. The
answer to "how can these substitutions be unified" is therefore: **don't unify
by name — open the binder to a fresh logic var alpha-canonically (the De Bruijn
path rules already use), and structural arrow-unification aligns it.**

## 3. The feed-relationship is a relational environment, not a descriptor language

Feeds matter only for the **propagation** direction (`foreach`/`foldLeft`, where
the callback's modify must surface in the higher-order op's *output* row). 046
§4.2 proposed expressing it with a bespoke **descriptor language**
(`element_of(xs)`, `threaded(z, f)`). Reject that: a reader who meets
`element_of(xs)` cannot tell what it means, and it is a second notation bolted
onto a language that is *already* a relational knowledge base. Express the feed
instead as **ordinary relations over logic variables** — the kernel's own
`rule`/relation substrate, resolved by the KB's existing SLD.

The feed is: *the callback's application, plus the relations binding its
arguments to the op's own parameters.* It needs **no new syntax and no new
keyword** — write it as an ordinary `rule` over a `fed` relation, with parameters
referenced by qualified name (`op.param`, generalizing proposal 041's
`op.result`):

```
rule fed(foreach.f, ?x)  :- member(?x, foreach.xs)

rule fed(foldLeft.f, (acc: ?a, elem: ?e))
       :- member(?e, foldLeft.xs), seed_or_result(?a, foldLeft.z, foldLeft.f)
```

`fed` is a relation (a sort, defined like `Modifiable`); `fed(foreach.f, ?x)` is
a head term; `member(?e, foldLeft.xs)` is an ordinary body atom. Every piece is
something the reader can look up and the resolver can solve: `member` is the
defined list relation; `seed_or_result(?a, z, f)` is a *named* relation (the
loop-carried accumulator — `?a` is the seed `z` or `f`'s own output) whose
definition is readable, not an opaque `threaded`. This needs no `feeds` meta-entry
and no `feeds` clause keyword — it is plain KB data, and therefore
**SLD-resolvable**: `effect_derive` queries it exactly as it queries
`OperationInfo` (WI-348), rather than parsing an inert descriptor term.

### Why relations, not a descriptor language

- **Legibility.** `member(?x, xs)` / `seed_or_result(?a, z, f)` explain themselves;
  `element_of(xs)` / `threaded(z, f)` do not. The complaint that motivated this
  section ("reader sees `element_of(xs)` and doesn't understand it") is answered
  by using relations that are defined, not tokens that are stipulated.
- **It is the *unsolved* form of the substitution.** The whole feed step is still
  substitution (below); a relational environment is just the substitution written
  as **constraints** instead of a solved map. At a call site you **resolve** the
  relations against the actual arguments (SLD — already in the KB) and the
  solution *is* the substitution. "Describe the environment" and "keep
  substitution" are the same thing at two stages: declare relations → resolve →
  substitution → well-scoped row.
- **Extensibility for free.** The finer cases need no new vocabulary, just
  different relations: `first(?x, xs)` instead of `member(?x, xs)`, an index
  relation `nth(?x, xs, ?i)`, etc. You add a relation the reader and resolver
  already handle, not a descriptor-language production.

### A fully-defined feed spec (foldLeft)

`member` / `seed_or_result` above read like undefined primitives. They are not —
at analysis time `xs` is a *symbolic parameter*, not a concrete list, so `member`
cannot be runtime list-membership; it is a **labeled dataflow edge**. Grounding
that, the whole feed + masking is a small self-contained spec with nothing
undefined: a `flow(kind, from, to)` fact vocabulary, a per-op set of ground
`flow`/`provenance` facts (derived from the body or declared), and generic
reachability/masking rules defined once.

```anthill
namespace anthill.effect.feed
  import anthill.prelude.{Symbol}

  -- A. Vocabulary + analysis — defined ONCE, for every operation

  sort FlowKind                        -- what was hiding inside `member`/`threaded`
    entity direct                      -- y is x itself        (identity / threading)
    entity element_of                  -- y is an element of x  (the old `member`)
    entity field_of(field: Symbol)     -- y is x.field
  end
  sort Flow                            -- flow facts ARE the feed-relationship
    entity flow(kind: FlowKind, from: Symbol, to: Symbol)
  end
  sort Provenance
    entity input  entity fresh_output  entity op_result  entity local
  end
  sort PlaceProvenance
    entity provenance(place: Symbol, is: Provenance)
  end

  rule reaches(?from, ?to) :- flow(kind: ?k, from: ?from, to: ?to)
  rule reaches(?from, ?to) :- flow(kind: ?k, from: ?from, to: ?mid),
                              reaches(?mid, ?to)
  rule origin(?place, ?src) :- reaches(?src, ?place)

  -- a Modify on ?p surfaces as Modify on an input origin …
  rule keep_modify(?p, ?r) :- origin(?p, ?r), provenance(?r, input)
  -- … or on the op result a fresh output escapes through.
  rule keep_modify(?p, ?result) :- origin(?p, ?src),
                                    provenance(?src, fresh_output),
                                    reaches(?src, ?result),
                                    provenance(?result, op_result)
  -- (fresh-but-non-escaping, and locals: no fact — drop is absence.)

  -- B. foldLeft's feed — ground facts (derived / declared)
  --    foldLeft[S,T,E](xs: List[T], z: S, f: (a:S, t:T) -> S @ E): S
  fact flow(kind: element_of, from: foldLeft.xs,       to: foldLeft.f.t)
  fact flow(kind: direct,     from: foldLeft.z,        to: foldLeft.f.a)    -- "base"
  fact flow(kind: direct,     from: foldLeft.f.result, to: foldLeft.f.a)    -- "step"
  fact flow(kind: direct,     from: foldLeft.f.result, to: foldLeft.result)
  fact flow(kind: direct,     from: foldLeft.z,        to: foldLeft.result)
  fact provenance(place: foldLeft.xs,       is: input)
  fact provenance(place: foldLeft.z,        is: input)
  fact provenance(place: foldLeft.f.result, is: fresh_output)
  fact provenance(place: foldLeft.result,   is: op_result)
end
```

Resolution answers masking directly — `:- keep_modify(foldLeft.f.a, ?r)` gives
`?r = foldLeft.z` (the seed, input) and `?r = foldLeft.result` (f's output escapes
the result); `:- keep_modify(foldLeft.f.t, ?r)` gives `?r = foldLeft.xs` (via the
`element_of` edge). The three things that read as undefined dissolve: **`member`**
is the `element_of` kind on one `flow` fact (not a predicate — `xs` is symbolic);
**base / step** are the two `flow(direct, …, foldLeft.f.a)` facts (seed and
loop-carried output); **the accumulator** is just the place `foldLeft.f.a`. And
the graph is *acyclic* (`f.result` is a source — the opaque callback's interior is
not walked), so `reaches` terminates with no fixpoint machinery.

### Derived from a body — the same facts, auto-generated

For an anthill-defined op nobody writes the facts above; a **load pass derives
them** from the body. Given the native form:

```anthill
operation foldLeft[S, T, E](xs: List[T], z: S, f: (a: S, t: T) -> S @ E) -> S effects E =
  match xs
    case nil()         -> z
    case cons(h, rest) -> foldLeft(rest, f(z, h), f)
```

each body construct emits one edge (the application surface — `f(z, h)` vs
`apply(f, (z, h))` — does not matter; the pass keys on the application
occurrence and its argument positions):

```
cons(h, rest) := xs        ⇒  flow(element_of, xs, <h>)
f(z, h)        z→a, h→t     ⇒  flow(direct, z, f.a) ;  flow(element_of, xs, f.t)
foldLeft(rest, f(z,h), f)  ⇒  flow(direct, f.result, z)        -- z-arg is f's result
case nil()      -> z        ⇒  flow(direct, z, result)
case cons(...)  -> foldLeft ⇒  flow(direct, f.result, result)  -- accumulator returned
```

The result is **byte-for-byte the facts a bodyless op would declare** (the
`f.result → z` edge here vs the earlier `f.result → f.a` are equivalent under
reachability, since `z → f.a`). Two splits to note: **`flow` comes from the body**
(destructuring / application / return nodes); **`provenance` comes from the
signature** (which names are parameters, which is the result, which params are
callbacks — so `f.result` is `fresh_output`). One representation, two producers —
the loader for native ops, the author for opaque primitives.

### Role of `kind` — precision only, never soundness

`kind` (`direct` / `element_of` / `field_of`) is consulted at **exactly one
place: the region re-key.** Note that `reaches` / `origin` / `keep_modify` never
inspect it — whether a modify propagates, escapes, or drops depends only on which
places connect and their `provenance`. `kind` matters once a label is *kept*, to
say **which region** it names — it is a projection on the source region:

| kind | re-key of `Modify[callback-param]` fed from source `s` |
|------|--------|
| `direct` | `Modify[s]` — same region (identity) |
| `element_of` | `Modify[`element-region of `s]` — descend into elements |
| `field_of(n)` | `Modify[s.n]` — descend into the field |

The load-bearing invariant: **soundness never depends on `kind`.** Collapsing
every edge to `direct` (re-key to the *whole* source) is always sound — the whole
region *contains* the real sub-region, so an observer of the coarse region is a
superset of observers of the fine one; you never miss an effect. (Under-claiming a
*smaller* region would be unsound, but coarsening whole-ward never is.) So `kind`
is purely a **precision knob**, needed only when the lattice distinguishes a part
from its whole:

- `element_of` — disjointness / cardinality / linearity (modifies *elements* vs
  *spine*). This is the field that *carries* the "finer-than-region surplus" of
  §"Does the environment ever carry information substitution lacks?".
- `field_of` — per-field escape precision (the WI-316 case); even there it is
  precision, since over-claiming `Modify[result]` is already sound.

There are thus **two conservative axes**, both sound coarsenings: (1) **flow
presence** — conservative = all-to-all (no body); (2) **`kind`** — conservative =
treat every edge as `direct`. **046 v1 should keep the `kind` field but ignore it
in keep/drop and re-key everything as `direct`** — the core cases (Cell.new
masking WI-314; foldLeft/foreach at region granularity) do not consume it; it is
the hook for the finer lattice, present in the data, paid for only when used.

### Where `flow` facts live — and the declaration-syntax choice

Most ops never declare flow: it is **derived**, not written.

- **Native ops** — the load pass emits `flow` from the body (above). Nothing to
  write.
- **Bodyless ops with defining rules/laws** — the stdlib idiom places each op's
  laws right under it (`rule length(cons(?x,?xs)) = add(1, length(?xs))`). The
  flow pass reads flow from those laws exactly as from a body, so a primitive that
  is *specified by rules* needs no flow declaration either.
- **Only fully-opaque FFI** (no body, no laws) must declare flow by hand.

That last set is small, but for it the **top-level qualified-fact form is too
verbose to use** — five `fact flow(kind: direct, from: foldLeft.z, to: foldLeft.f.a)`
lines plus provenance, detached from the op, every name fully qualified. The
grammar offers no relief today: `operation_clause` is only
`requires`/`ensures`/`effects` + an optional `= body` + a `meta_block` — **no
fact/rule form inside an operation.** So a usable declared form needs one of two
small additions:

- **(A) a flow *table*** — a compact, columnar `meta`-like block scoped to the op,
  e.g. rows `xs --element_of--> f.t`, `z --> f.a`, `f.result --> z`. Narrow,
  dense, flow-specific; one bespoke grammar production.
- **(B) rules/facts inside an operation** — a general in-op block (reusing the
  `rule_body` term grammar) so the edges are written with **bare params in scope**
  (`direct(z, f.a)`, `element_of(xs, f.t)`), co-located with the op. More syntax
  than (A) but **reusable** for any per-op relational annotation, and closer to
  the stdlib's existing op-plus-laws idiom. *(Either way, `ensures` must not be
  overloaded — it is a runtime postcondition.)*

Recommendation: **(B)** — a general "relations inside an operation" facility is
more in character with anthill's relational core and the existing sibling-law
idiom, and it subsumes (A). It is a **small separate proposal**, not part of the
`effect_derive` work, and not needed for v1 (native + law-specified ops cover the
stdlib). A **shared prerequisite** for *all* forms — top-level, table, or in-op —
is the callback/param projection reference (`f.a`, `f.result`, `result`), i.e.
041's `op.result` generalized to `op.param`; that is the one piece this slice
actually requires.

### The pipeline is two substitutions, both already in the codebase

Once the environment is resolved, well-scoping is *composing two substitutions
the codebase already has*:

1. **Feed substitution** — `callback-param ↦ argument-term`, the SLD solution of
   the feed relations (`foreach`'s `?x ↦ h` against the call, or directly off the
   body in the native case). Eliminates the callback param.
2. **Reachability re-key** — `argument-term ↦ the argument/region it is reachable
   from` (`h ↦ region-of(xs)`, because `member(h, xs)`). This is *literally*
   `region.rs:rekey_resource` (`from → to`), the same re-key WI-314 already runs
   for `Cell.new.result → c`. Eliminates the body-local.

After both, the row mentions only arguments → well-scoped (046 §1's elimination
obligation is exactly "compose substitutions until no callback/callee param
remains"). Then `op_boundary_effects` masks as today. The pipeline is **resolve
(feed relations) → substitute → re-key → mask** — operations that all already
exist; no descriptor evaluator, no separate region-abstraction operator. 046's
"region abstraction" worry — a loop yields *unbounded* denotations (`h₁, h₂, …`)
to collapse — never materializes: effects **name regions**, not denotations, so
re-keying the per-iteration local to its source argument's region is itself the
finite collapse.

### One representation, two producers, one cache — derived once at load

The feed-relationship is **op-intrinsic** (it depends on the op's body /
signature, not the call site), so it is derived **once at load** and cached —
never re-analyzed per call. The cache *is* the `fed` rules:

- **bodyless op** (primitive, FFI) — you **declare** the rule:
  `rule fed(foreach.f, ?x) :- member(?x, foreach.xs)`.
- **anthill-defined op** — a **load-time pass** runs the §1 body dataflow once and
  **asserts the identical rule**, derived from the body. `operation_body`
  (WI-305) is the source: `cons(h, t) := xs; apply(f, (acc: z, elem: h))` already
  contains `member(h, xs)` and the accumulator structure as occurrences, so the
  pass reads the feed off it — the same reachability walk `region.rs` already does
  for return types (`result_type_admits_region`; WI-316 is the field-reachability
  extension), now pointed at arguments. This mirrors the existing
  `infer_effects_row_requires` load pass (WI-320), which synthesizes `requires`
  from operation `effects` at load.

After load, both producers leave the same thing: an ordinary `RuleEntry` in the
KB, discrimination-indexed on the `fed` functor and the qualified op-param
`foreach.f`. Per call, `effect_derive` resolves `fed(foreach.f, ?_)` by SLD —
**the body is walked exactly once (at load), never at a call site.** No `feeds`
field on `OperationInfo`, no `op_feeds` side-table, no value-fact extension: the
KB's rule store *is* the cache, and the qualified symbol in the head carries the
binding-to-the-operation a metadata field would have (so two ops sharing an arrow
`Type` still get distinct feeds). The only new dependency is the qualified
`op.param` reference — proposal 041's `op.result` generalized.

**Source priority:** a declared `fed` rule overrides; else the loader derives one
from `operation_body`; else (no body, no declaration) the feed is absent and `E`
stays an opaque row variable (sound, coarse).

### Does the environment ever carry information substitution lacks?

Bounding the "it stays substitution" claim. In the **current region-granular**
`Modify` system: essentially no.

- **Native ops:** never — the body *is* the environment, so it has strictly more
  than any summary of it.
- **Bodyless ops:** the declared relations resolve to substitution-shaped content
  (`param ↦ region-reachable-from-arg`) — not surplus. The **one** thing a *flat*
  substitution cannot express is self-reference: the accumulator
  `seed_or_result(?a, z, f) ≡ ?a ↦ z ⊔ f(?a, _)` references the callback's own
  output. That fixpoint is exactly why the threaded feed is a **relation** (which
  can be recursive) rather than a flat map — and a recursive body already
  encodes it. So it is information absent from *non-recursive* substitution, not
  from substitution/relations in general.

The environment would carry **genuinely analyzable surplus only under a finer-
than-region lattice**, which 046 does not introduce:

- **cardinality** — `member(?x, xs)` (every element) vs `first(?x, xs)` (one);
  region masking collapses both to `Modify[xs]`, but a **linearity / uniqueness**
  or **disjoint-writes / parallelism** analysis would consume the distinction;
- **index/shape dependence** — `nth(?x, xs, ?i)` keyed to a callback index
  argument (dependent effects).

So the relational form earns finer-grained keep only if the effect lattice later
grows finer than regions; at region granularity it is the *unsolved* form of
`(feed-substitution ∘ reachability)`, with recursion available for the threaded
fixpoint.

## 4. Synthesis — one mechanism, mostly already built

| concern | mechanism | status |
|---|---|---|
| callback param identity | arrow-bound De Bruijn → fresh `Value::Var` on open | machinery exists (`term_from_debruijn` / WI-109); **WI-341** redirect |
| `-Modify(a)` checking | open + arrow-unify + WI-328 lacks side-table | lacks machinery **delivered** |
| feed-relationship | derived from `operation_body` at load into `fed` rules (also declarable for bodyless ops); resolved by SLD per call | **new** (this doc §1/§3); cached as KB rules, no `OperationInfo` field |
| propagation + masking | new provenance category in `region.rs:op_boundary_effects` | extends the existing boundary classifier |

This is the first non-default contribution to `effect_derive` dispatch (046 §5):
control effects (`Error`/`Branch`) stay on the default derivation; only `Modify`
consumes `ctx`/regions, so its host-dataflow step is a **builtin the `Modify`
`effect_derive` rule calls**, not a separate dispatch path.

### Sequencing

1. **WI-341 binder-as-value-var** — replace the `substitute_ref_syms` string hack
   with De Bruijn-opened `Value::Var` callback params. This alone makes
   `find`-style `-Modify(a)` purity constraints check correctly off WI-328, with
   no feed analysis. It is the prerequisite for everything below.
2. **Reachability re-key over arguments** — generalize `region.rs`'s return-type
   reachability walk (`result_type_admits_region` / `rekey_resource`) to *trace a
   body-local back to the argument it came from* (`h ↦ region-of(xs)`). This is
   the second substitution of §3; it is what gives the feed step a well-scoped
   result, and it subsumes the WI-316 field-reachability deferral.
3. **`fed` rules as the feed cache** — bodyless ops *declare* them; a **load-time
   pass** *derives and asserts* the identical rule from `operation_body` for
   native ops (mirrors `infer_effects_row_requires`, WI-320), so the body is
   analyzed once at load, never per call. Both leave an ordinary KB rule resolved
   by SLD; needs the qualified `op.param` reference (041's `op.result`
   generalized) but no new syntax and no `OperationInfo` field.
4. **Mixed-provenance fixpoint** in `region.rs` — the loop-carried accumulator's
   component set (seed ∪ `f`'s outputs) over the finite provenance lattice, each
   component then classified by the same `op_boundary_effects` (§1).

The honest read: step 1 unblocks the purity-constraint case (`find`) and is
mostly de-entrenchment of an existing hack; step 2 is the load-bearing new work
(it is *substitution* — the second re-key — not a descriptor evaluator); steps
3–4 are thin once step 2 exists and bite only for the propagating HOFs
(`foreach`/`foldLeft`).

## Prior art

Region inference — Tofte & Talpin 1997 (the fixpoint we *avoid*). Latent effect
incurred per application site with region/param vars instantiated — Talpin &
Jouvelot 1992 (the substitution we *do* — but on a callback the op applies, read
from its body rather than its type). Local-state-externally-pure — Launchbury &
Peyton Jones `runST` 1994 (the masking of fresh, non-escaping regions).

# Proposal 046 — Making `effect_derive` correct: its input and output, by case analysis

## Status: Draft (2026-05-25)

> **Purpose: make 045 correct.** 045 specifies `effect_derive` — the relation that
> gives a call's effect row. Run over the cases, *some come out correct and some
> incorrect* (ill-scoped). This document works through the cases to pin down the
> correct **input** and **output** of `effect_derive`, so 045's specification of it
> is right. `denoted` (region-keyed effects) stays in **045**; this is plumbing,
> not a separate feature. The *implementation* details of the hard cases may be
> deferred — but the **input/output types must be correct now**.

## 1. The correctness property: the output must be well-scoped

`effect_derive(…) → output_row`. The one non-negotiable property:

> **`output_row` is well-scoped in the caller's environment** — it contains **no
> variable bound by the callee's (or a callback's) parameters.** Every such
> variable must be eliminated by resolving it against the call's actual data.

A row that mentions a parameter of the thing being called is meaningless to the
caller. That single property is what separates the correct cases from the
incorrect ones below.

## 2. The cases

Form under test: `effect_derive(callee_sig, args, ctx) → output_row`, where
`args` are `(denotation, type)` pairs and the effect field may be region-keyed
(`Modify[p]`, `p` a parameter). "Correct?" = is the output well-scoped?

```
case        call                         naive output                       correct?
────────────────────────────────────────────────────────────────────────────────────
intro       set(c, v)                    { Modify[c] }                      ✓  c = arg, in caller scope
            c ↦ actual arg by subst

two params  swap(a, b)                   { Modify[a],                       ✓  a,b = args, in caller scope
                                            Modify[b] }

construct   map(λ x → Cell.new(x))       { Modify[result] }                 ✓  result flows out, not a callback param

two HO      option_fold(o, ifN, ifS)     merge(R1, R2)                      ✓  R1,R2 are the args' rows
                                                                               (no callee param escapes)

discharge   handle(body)                 body row minus Error               ✓  via the handler's type

HOF + param foreach(λ x → set(x, …))     { Modify[x] }                      ✗  x = the CALLBACK'S param;
                                                                               bound by its arrow → ESCAPES.
                                                                               (there's x, but no xs)

threading   foldLeft(xs, z, λ(a,e)…)     { Modify[a],                       ✗  a, e are the callback's params
                                            Modify[e] }                        → escape; not resolved to z / xs
```

The first five are **correct**: every parameter in the effect field is the
*callee's own* parameter, and step-substitution resolves it to the actual
argument (`c ↦ the cell`, …), which is in the caller's scope. The last two are
**incorrect**: the escaping variable is a **callback's** parameter, and at the
HOF call there is no argument to substitute it with — `foreach` binds `x` to
*elements of `xs`* only *inside its own body*.

## 3. Diagnosis

The incorrect cases share one shape: **a higher-order call whose callback row
references the callback's own parameter.** The output then names a variable bound
by the callback's arrow, which is out of scope at the caller. To make it
well-scoped you must **eliminate that parameter** — resolve it to whatever the
HOF feeds the callback (`x ↦ elements(xs)`; `a ↦ z`/threaded). That mapping is the
**feed-relationship**.

> **Feed-relationship** (working definition): *which of its own arguments a
> higher-order operation passes to each callback parameter when it applies the
> callback* — e.g. `foreach` passes each **element of `xs`** as the callback's
> argument. It is read off the `apply(f, …)` nodes in the operation's body.
> This is the standard "a function's **latent effect** is incurred, with its
> parameter/region variables instantiated, at each **application site**"
> (Talpin & Jouvelot, *The Type and Effect Discipline*, 1992; region
> substitution in Tofte & Talpin 1997) — here applied to a *callback* that the
> operation itself applies. The substitution is not in `foreach`'s *type*
> (`(List[A], Function[A,Unit,E]) -> Unit effects E` — `E` is opaque); it lives in its
> *body* (`apply(f, elem)`, `elem` from `xs`).

So the form `effect_derive(callee_sig, args, ctx)` is **insufficient**: it has
no input from which to eliminate a callback's parameter.

## 4. The input that fixes it

The feed-relationship lives in the callee's body, which anthill already keeps as
a `NodeOccurrence` (`operation_body`, WI-305). So the corrected input adds the
callee's body:

```
effect_derive(callee_sig, callee_body, args, ctx)  →  output_row
```

- **`callee_sig`** — the callee's **signature record**. For a **named operation**
  it is its **`OperationInfo`** — arrow type + `effects` row + `requires`/
  `ensures` + any **`feeds` metadata** (this is *how the metadata is passed* — it
  is a field of `OperationInfo`, not of the `Type`). For a **HO parameter** (a
  value, not a named op) it is just the parameter's arrow `Type` (no
  `OperationInfo`, no metadata).
- **`callee_body`** — the callee's **body occurrence** (or `none` for abstract /
  foreign callees). The **feed-relationship** is read from it — *how* a callback's
  parameters are bound to the callee's own arguments. This is the input the
  3-arg form lacked. (For abstract operations with no body, the feed-relationship
  is instead **declared as metadata on the operation's `OperationInfo`** — bound
  to the operation, not the `Type` — see §4.2.)
- **`args`** — `(denotation, type)` per argument; denotations resolve the
  *callee's own* parameters (`denoted(pᵢ) ↦ denoted(argᵢ)`).
- **`ctx`** — the typing environment (provenance, active handlers).

**Output:** a **well-scoped** row (§1) — all callee/callback parameters
eliminated, region-keyed labels resolved to caller-scope regions or abstracted
to a region variable.

### 4.1 Concrete instantiation — the `foreach` call

For `foreach(l, λ x → set(x, get(x) + 1))` with `l : List[Cell[Int64]]`, the four
arguments are:

```
effect_derive(

  callee_sig =                                          -- foreach's OperationInfo
     ( xs: List[A], f: Function[A, Unit, E] ) -> Unit effects E  -- no feeds declared here
                                                                 -- (so callee_body is used below)

  callee_body =                                          -- foreach's body occurrence
     match xs:
        nil        → unit
        cons(h, t) → apply(f, h) ; foreach(t, f)
                          └── feed-relationship: f's param ↦ h,  h ∈ elements(xs)

  args = [
     ( denotation: l ,
       type:       List[Cell[Int64]] ),
     ( denotation: λ x → set(x, get(x)+1) ,
       type:       (Cell[Int64]) -> Unit @ { Modify[x] } )
                                              └── x = the lambda's parameter
  ],

  ctx =                                                  -- typing environment
     { l : List[Cell[Int64]]  (an input/parameter) ;  no active handlers }
)
```

Deriving:

```
step 1  unify ( List[A], Function[A,Unit,E] ) ~ args' types
        ⇒  A := Cell[Int64] ,  E := { Modify[x] }

naïve   output = E = { Modify[x] }      ✗ ILL-SCOPED
        (x is the lambda's parameter — there is x, but no l)

correct read callee_body ⇒ feed-relationship  x ↦ elements(l)
        substitute        ⇒ { Modify[elements of l] }
        abstract to region ⇒ { Modify[ρₗ] }  (ρₗ = region of l's elements)   ✓ well-scoped
                              └── this read+abstract step is the deferred 046 detail
```

So the *form* is fully determined (the four arguments above), `ctx` says `l` is
an input region (so it is kept, not masked), and only the `callee_body`-read +
region-abstraction is the deferred body.

### 4.2 Feed-relationship from metadata (abstract / foreign operations)

`callee_body` is only *one* source of the feed-relationship. An **abstract
operation** — a primitive, an FFI binding, a body written in another language —
has **no anthill body to read**, but it can still **declare the feed-relationship
as metadata**, using anthill's **existing `[key: value]` metadata syntax** (the
`meta_entry` form — same as `[simp]`, `[trust: …]`; open-keyed, value a `Term`).
The key is `feeds`; the value is a term saying how each higher-order parameter is
**applied** — `f(<descriptor per parameter>)`:

```
operation foreach[A, E](xs: List[A], f: (A) -> Unit @ E) -> Unit effects E
   [feeds: f(element_of(xs))]

operation foldLeft[A, B, E](xs: List[A], z: B, f: (B, A) -> B @ E) -> B effects E
   [feeds: f(threaded(z, f), element_of(xs))]
```

> **Surface-syntax note.** Effects on a *function/arrow type* use `@`
> (`(A) -> Unit @ E`), arrow params are parenthesized, the operation's own effect
> is the `effects E` clause, and operation type parameters are a bare list
> `[A, B, E]` (there is no `effects` keyword inside `[...]`). The `! E` /
> `[…, effects E]` / unparenthesized-arrow forms used in the schematic blocks of
> §2 and §4.1 are informal exposition, not grammar.
>
> **`feeds` need not be a meta-entry — it can be a plain `rule`.** `[feeds: …]`
> is an open-keyed `meta_entry` (no new keyword), but its value is one inert
> `Term`. The feed-relationship is better written as ordinary KB rules over a
> `fed` relation, with parameters referenced by qualified name (`op.param`,
> generalizing proposal 041's `op.result`):
>
> ```
> rule fed(foreach.f, ?x)  :- member(?x, foreach.xs)
> rule fed(foldLeft.f, (acc: ?a, elem: ?e))
>        :- member(?e, foldLeft.xs), seed_or_result(?a, foldLeft.z, foldLeft.f)
> ```
>
> This adds no syntax and keeps the feed-relationship **SLD-resolvable** — the
> `effect_derive` builtin queries it like any other relation (and like
> `OperationInfo` itself, WI-348) rather than parsing an inert descriptor. See
> `docs/design/modify-effect-derive.md` §3.

`[feeds: f(…)]` is an ordinary `meta_entry`: key `feeds`, value the term `f(…)`
whose argument positions hold a **descriptor** per callback parameter
(`element_of(xs)`, `threaded(z, f)`). Those descriptors are exactly the
substitutions `effect_derive` applies to the callback's parameters — the same
`x ↦ elements(l)` the body-read would yield, but **declared** rather than
inferred from code. Reading them:

- **`element_of(xs)`** — ranges over the elements of `xs` (all input-provenance).
- **`threaded(z, f)`** — the **accumulator chain**: the seed `z` and every
  intermediate result `f` produces (`z`, `f(z,x₁)`, `f(f(z,x₁),x₂)`, …). It is
  self-referential (depends on `f`'s own outputs), so its provenance is *mixed* —
  `z` is input, the intermediates are `f`'s outputs. This loop-carried
  dependency is the subtle case for masking.

(This `element_of`/`threaded` **descriptor language** is the part still to be
specified — see Open detail.)

This:

- gives **abstract / foreign operations** effect-checking — the annotation is
  the only source, and it suffices;
- restores **modularity** — a call site needs only the callee operation's
  signature record, never its body;
- **binds to the operation, not the `Type`.** The feed metadata lives on the
  callee's **`OperationInfo`** (it is a property of *that operation*); it is
  **not** in `callee_sig` / the arrow `Type`, which is hash-consed and shared
  across operations (two ops with the same signature share one arrow `TermId`
  but may have different `feeds`). `effect_derive` obtains it from the callee
  operation's `OperationInfo` (by symbol); the arrow `Type` stays metadata-free,
  so `effect_derive`'s argument list need not grow. **It is not present today:**
  `OperationInfo` (`reflect.anthill`) carries only
  `name`/`params`/`return_type`/`effects`/`requires`/`ensures` — no feed field.
  Implementing `feeds` means **adding a field to `OperationInfo`** (WI-309).
  `callee_body` is the fallback for anthill-defined ops that don't declare it;
  for a higher-order *parameter* (a value, not a named op) there is no
  `OperationInfo` at all — only its arrow type.

> **Status:** `feeds` is *proposed*, not implemented — no test. It **reuses the
> existing `[key: value]` meta-entry syntax**, which operation declarations
> *already accept* (grammar `operation_declaration`, and the IR `Operation.meta`)
> — but the **loader silently drops it** (`load.rs` never reads `op.meta`) and
> `OperationInfo` has no field to expose it. So loading + surfacing operation
> metadata is a **prerequisite** (WI-309), on top of which `[feeds: …]` and its
> descriptor language are this proposal's work. This section specifies the
> *form*, not existing behavior.

**Source priority** for the feed-relationship: declared `feeds` metadata (if
present) → else read `callee_body` (if the op is anthill-defined) → else opaque
(`E` left as a row variable — the conservative result, sound but coarse).

## 4.3 Stdlib vocabulary — the feed-relationship as relations

> **Supersedes the descriptor-language framing of §4.2.** §4.2 sketched the
> feed-relationship as a bespoke descriptor language (`element_of(xs)`,
> `threaded(z, f)`) carried in `[feeds: …]` metadata. That is **rejected**: a
> reader cannot tell what `element_of(xs)` means, and anthill is *already* a
> relational KB. The feed-relationship is instead a **set of ordinary relations**
> over places — defined in the stdlib, derived (not hand-written) for native ops,
> and resolved by SLD. Full design + the worked `foldLeft` spec:
> `docs/design/modify-effect-derive.md`.

The feed-relationship is realized by a small **reflect-layer vocabulary** (home:
`stdlib/anthill/reflect/`, alongside `reflect/typing.anthill` — these are
typing/effect-derivation *analysis* relations the typer queries, not surface
effects). Places are named by qualified path (`foldLeft.xs`, `foldLeft.f.a`,
`foldLeft.f.result`, `foldLeft.result`) — the `op.param` reference, proposal 041's
`op.result` generalized (WI-351).

```anthill
sort FlowKind                       -- the kind of a dataflow edge
  entity direct                     --   y is x itself        (identity / threading)
  entity element_of                 --   y is an element of x
  entity field_of(field: Symbol)    --   y is x.field
end
sort Flow
  entity flow(kind: FlowKind, from: Symbol, to: Symbol)     -- these facts ARE the feed
end
sort Provenance
  entity input  entity fresh_output  entity op_result  entity local
end
sort PlaceProvenance
  entity provenance(place: Symbol, is: Provenance)
end

rule reaches(?from, ?to) :- flow(kind: ?k, from: ?from, to: ?to)
rule reaches(?from, ?to) :- flow(kind: ?k, from: ?from, to: ?mid), reaches(?mid, ?to)
rule origin(?place, ?src) :- reaches(?src, ?place)

rule keep_modify(?p, ?r)      :- origin(?p, ?r), provenance(?r, input)
rule keep_modify(?p, ?result) :- origin(?p, ?src), provenance(?src, fresh_output),
                                 reaches(?src, ?result), provenance(?result, op_result)
```

**Naming.** `flow` / `provenance` / `reaches` / `origin` are **effect-agnostic**
dataflow relations (the substrate generalizes — `Modify` is just the *first*
non-default `effect_derive` contributor, §5); only `keep_modify` is
`Modify`-specific masking. So the substrate is **not** named `flow_modify` — its
`Modify`-scoping for v1 lives in the namespace and in `keep_modify`, leaving the
dataflow primitive reusable by a future effect's derivation.

**What is derived vs declared.** For an anthill-defined op the `flow` facts are
**derived from the body** (and from defining rules/laws) by a load pass and
asserted top-level — *identical* to what a bodyless op would declare; `provenance`
comes from the signature. Only fully-opaque FFI declares by hand. So this
vocabulary is realized by **WI-352** (the flow-derivation pass defines these sorts
and asserts the facts); **WI-353** (`region.rs`) is the `keep_modify` consumer at
the operation boundary. The `kind` field is **precision-only** — soundness never
depends on it (collapsing every edge to `direct` re-keys to a containing region,
always sound); v1 keeps the field but treats every edge as `direct`.

## 5. What is type vs. what is deferred detail

This document fixes the **input/output types** of `effect_derive` — that is what
makes 045 correct:

- the **4-argument input** (`callee_body` is the missing one), and
- the **well-scoped output** obligation.

For the correct cases (intro/swap/alloc/two-HO/discharge), the *implementation*
is also given — type + unification + own-parameter substitution (the **default**
derivation, 045 §5.2.1). For the incorrect-without-it cases (HOF +
callback-parameter), the implementation that *produces* a well-scoped output —
read the feed-relationship from `callee_body`, substitute the callback parameter,
then **abstract** the (unbounded) result into a region and apply
**provenance/masking** — is **deferred in detail** (it needs region abstraction,
escape analysis, and a recursion fixpoint). But its **interface is now correct**,
so the deferred work plugs in without changing the form.

Concretely, this is **`Modify`'s per-effect derivation** (045 §5.2.1): the
`effect_derive` rule in the `Modify` sort. Because it consumes `ctx`/regions, the
host-dataflow step is a **builtin its body calls** — a primitive the rule
invokes, not a separate dispatch path. It is the first non-default contribution
to the `effect_derive` dispatch — control effects (`Error`/`Branch`) stay on the
default. So this proposal *is* the `Modify` slice of `effect_derive`; it touches
none of the framework or the other effects.

## 6. Feedback to 045

- Update 045's `effect_derive` signature to the **4-argument** form above; state
  the **well-scoped-output** property as its correctness condition.
- 045 keeps `denoted` and own-parameter substitution (the correct cases) — those
  are *not* moved here.
- 045 marks the HOF+callback-parameter case as: *interface correct, well-scoped
  output required; the body that reads `callee_body` + region abstraction +
  masking is the deferred detail.*

## Open detail (deferred bodies, not types)

1. **Reading the feed-relationship** — from `callee_body` (intensional read; needs
   a **recursion fixpoint** for `foldLeft`) or from **declared `feeds` metadata**
   (§4.2; the descriptor language `element_of`/`threaded` to be specified).
2. **Region abstraction** — collapsing unbounded per-iteration denotations into a
   finite region so loops have finite, well-scoped effects.
3. **Provenance / masking** — input vs. fresh-output regions; discharging a
   fresh, non-escaping region (so a local-state op is externally pure).
4. **Aliasing** — two parameters that are the same cell.

## Prior art

- Region inference — Tofte & Talpin 1997. Local-state-externally-pure —
  Launchbury & Peyton Jones (`runST`) 1994. Type-and-effect — Talpin & Jouvelot
  1992. Handler identity — Koka named handlers; OCaml 5 effect instances.

## Relation to 045

045 owns the effect-row design including `denoted`. This document's sole job is
to **correct `effect_derive`'s form** (its input and output) by case analysis,
so 045's specification of `effect_derive` is sound. The deferred items above are
*implementation bodies* behind that now-correct interface, not changes to it.

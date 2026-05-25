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

Form under test: `effect_derive(callee_type, args, ctx) → output_row`, where
`args` are `(denotation, type)` pairs and the effect field may be region-keyed
(`Modify[denoted(p)]`, `p` a parameter). "Correct?" = is the output well-scoped?

```
case        call                         naive output                       correct?
────────────────────────────────────────────────────────────────────────────────────
intro       set(c, v)                    { Modify[denoted(c)] }             ✓  c = arg, in caller scope
            c ↦ actual arg by subst

two params  swap(a, b)                   { Modify[denoted(a)],              ✓  a,b = args, in caller scope
                                            Modify[denoted(b)] }

alloc       map(λ x → Cell.new(x))       { Alloc }                          ✓  no parameter reference

two HO      option_fold(o, ifN, ifS)     merge(R1, R2)                      ✓  R1,R2 are the args' rows
                                                                               (no callee param escapes)

discharge   handle(body)                 body row minus Error               ✓  via the handler's type

HOF + param foreach(λ x → set(x, …))     { Modify[denoted(x)] }             ✗  x = the CALLBACK'S param;
                                                                               bound by its arrow → ESCAPES.
                                                                               (there's x, but no xs)

threading   foldLeft(xs, z, λ(a,e)…)     { Modify[denoted(a)],              ✗  a, e are the callback's params
                                            Reads[denoted(e)] }                → escape; not resolved to z / xs
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
> (`(List[A], Function[A,Unit,E]) → Unit ! E` — `E` is opaque); it lives in its
> *body* (`apply(f, elem)`, `elem` from `xs`).

So the form `effect_derive(callee_type, args, ctx)` is **insufficient**: it has
no input from which to eliminate a callback's parameter.

## 4. The input that fixes it

The feed-relationship lives in the callee's body, which anthill already keeps as
a `NodeOccurrence` (`operation_body`, WI-305). So the corrected input adds the
callee's body:

```
effect_derive(callee_type, callee_body, args, ctx)  →  output_row
```

- **`callee_type`** — the callee's arrow type (for a HO parameter, that
  parameter's type). Carries parameter binders and the effect field.
- **`callee_body`** — the callee's **body occurrence** (or `none` for opaque
  callees). The **feed-relationship** is read from it — *how* a callback's
  parameters are bound to the callee's own arguments. This is the input the
  3-arg form lacked.
- **`args`** — `(denotation, type)` per argument; denotations resolve the
  *callee's own* parameters (`denoted(pᵢ) ↦ denoted(argᵢ)`).
- **`ctx`** — the typing environment (provenance, active handlers).

**Output:** a **well-scoped** row (§1) — all callee/callback parameters
eliminated, region-keyed labels resolved to caller-scope regions or abstracted
to a region variable.

### 4.1 Concrete instantiation — the `foreach` call

For `foreach(l, λ x → set(x, get(x) + 1))` with `l : List[Cell[Int]]`, the four
arguments are:

```
effect_derive(

  callee_type =                                          -- foreach's arrow type
     ( xs: List[A], f: Function[A, Unit, E] ) → Unit ! E

  callee_body =                                          -- foreach's body occurrence
     match xs:
        nil        → unit
        cons(h, t) → apply(f, h) ; foreach(t, f)
                          └── feed-relationship: f's param ↦ h,  h ∈ elements(xs)

  args = [
     ( denotation: l ,
       type:       List[Cell[Int]] ),
     ( denotation: λ x → set(x, get(x)+1) ,
       type:       Cell[Int] → Unit ! { Modify[denoted(x)], Reads[denoted(x)] } )
                                              └── x = the lambda's parameter
  ],

  ctx =                                                  -- typing environment
     { l : List[Cell[Int]]  (an input/parameter) ;  no active handlers }
)
```

Deriving:

```
step 1  unify ( List[A], Function[A,Unit,E] ) ~ args' types
        ⇒  A := Cell[Int] ,  E := { Modify[denoted(x)], Reads[denoted(x)] }

naïve   output = E = { Modify[denoted(x)], Reads[denoted(x)] }      ✗ ILL-SCOPED
        (x is the lambda's parameter — there is x, but no l)

correct read callee_body ⇒ feed-relationship  x ↦ elements(l)
        substitute        ⇒ { Modify[denoted(elements of l)], Reads[denoted(elements of l)] }
        abstract to region ⇒ { Modify[ρₗ], Reads[ρₗ] }  (ρₗ = region of l's elements)   ✓ well-scoped
                              └── this read+abstract step is the deferred 046 detail
```

So the *form* is fully determined (the four arguments above), `ctx` says `l` is
an input region (so it is kept, not masked), and only the `callee_body`-read +
region-abstraction is the deferred body.

## 5. What is type vs. what is deferred detail

This document fixes the **input/output types** of `effect_derive` — that is what
makes 045 correct:

- the **4-argument input** (`callee_body` is the missing one), and
- the **well-scoped output** obligation.

For the correct cases (intro/swap/alloc/two-HO/discharge), the *implementation*
is also given — type + unification + own-parameter substitution. For the
incorrect-without-it cases (HOF + callback-parameter), the implementation that
*produces* a well-scoped output — read the feed-relationship from `callee_body`,
substitute the callback parameter, then **abstract** the (unbounded) result into
a region and apply **provenance/masking** — is **deferred in detail** (it needs
region abstraction, escape analysis, and a recursion fixpoint). But its
**interface is now correct**, so the deferred work plugs in without changing the
form.

## 6. Feedback to 045

- Update 045's `effect_derive` signature to the **4-argument** form above; state
  the **well-scoped-output** property as its correctness condition.
- 045 keeps `denoted` and own-parameter substitution (the correct cases) — those
  are *not* moved here.
- 045 marks the HOF+callback-parameter case as: *interface correct, well-scoped
  output required; the body that reads `callee_body` + region abstraction +
  masking is the deferred detail.*

## Open detail (deferred bodies, not types)

1. **Reading the feed-relationship** from `callee_body` (the intensional read),
   and the **recursion fixpoint** (`foldLeft`).
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

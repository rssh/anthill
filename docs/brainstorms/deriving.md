# Deriving — a `derive` clause as a firing site of the `@[simp]` macro engine

## Status: Brainstorming draft (2026-09-18)

Captured from a design session. **Not a proposal**, and almost entirely **READ, NOT
MEASURED**: every claim about current behaviour names the source it was read from, and
*To measure* lists what has to be driven before any of this is distilled into a proposal.
The ONE exception is §3.1's "What is broken today", driven against a freshly built CLI
and filed as **WI-20260918-CKD4J**.

The session started from two clients and gained a third by USER DIRECTION:

- **WI-188** — the entity record-update form, `wi.copy(status: Claimed(…))`.
- **027.4's `Raisable[T]`** — a payload spec whose `tag()` is "DERIVED by default so the
  common case writes nothing" (`027.4-error-effect-reify.md`, §"What travels with a
  raise").
- **`Eq` / `PartialEq` derivation** (WI-664 / WI-1098, `kb/eq_derive.rs`) — USER
  DIRECTION: it should come from the same mechanism rather than stay hardwired.

Where it converged, also by USER DIRECTION and in three steps. The goal is an **extension
mechanism that lets an anthill programmer generate new structures at compile time from a
derive clause** — what Scala's low-level, macro-based derivation gives a library author.
The generator is not a new kind of thing, because **anthill already has `@[simp]`
macros** (043.1): the rule is the trigger, the macro operation is the generator, and
deriving is a new *firing site* of an engine that exists. And **the clause is not needed
per (spec, carrier) pair**: a derivation written in the spec answers for any known
carrier (§5.6), which leaves the clause for derivations that are a choice or take
arguments.

## Relates to

- **[043.1](../proposals/043.1-compile-time-macros.md)** — compile-time macros. The engine
  this rides; its build API (§9 step 5) is a prerequisite for generators written in
  anthill.
- **[056](../proposals/056-variadic-argument-capture.md)** — variadic argument capture.
  What makes `copy` expressible without a grammar change.
- **[058](../proposals/058-modular-instances.md)** — §3.6 (*fill silence, never overwrite
  speech*; a default is a FACT), §3.8 (conditional provisions), §3.10 (the parametric
  `Eq` leg, still proposed).
- **[060](../proposals/060-clause-level-requirements-and-typed-heads.md)** — the derived
  `domain` clause, and "a written `domain` IS the generator".
- **[027.4](../proposals/027.4-error-effect-reify.md)** and **WI-20260911-3MV2C** — the
  tag continuum, and the derived-only-vs-overridable fork for `Raisable`.
- **[055](../proposals/055-types-in-value-position.md)** — a type in value position, which
  is all `tag()`'s body is.
- **WI-20260918-CKD4J** — `eq_derive` derives nothing for a parametric sort; filed from
  this session, measured in §3.1.
- **WI-188** (`copy`), **WI-189** (staging brackets — optional ergonomics, not a
  prerequisite), **WI-664 / WI-1098 / WI-1103** (`eq_derive`), **WI-876** (spec default
  bodies), **WI-1110** (a spec's `provides` derives the floor below), **WI-321** (the
  all-pass-1-then-all-pass-2 invariant), **WI-902** (decline is the engine's outcome).

---

## 1. Anthill already derives — five times, four of them in Rust

| what | output | trigger | lives in | what a written one does |
|---|---|---|---|---|
| `Eq` / `PartialEq` / `NonEq` for a composite (WI-664, WI-1098) | provision ROWS, no bodies — structural `eq` is the builtin | universal | `kb/eq_derive.rs`, one fixpoint pair | the derivation skips a carrier that already provides; a dispatched `eq` is a boundary, neither classified nor overwritten |
| `domain_member` (060) | one CLAUSE per sort with constructors | universal | loader | a written `domain` IS the generator |
| `<Sort>.induction` (`kernel-language.md` §5.2) | a rule | universal | loader | — |
| the floor beneath a spec's `provides` (WI-1110) | a provision row | conditional on the upper row | loader | — |
| `gt` / `lt` / `gte` / `lte` from `compare` (WI-876) | operation BODIES | spec default bodies | **anthill source**, `prelude/ordered.anthill` | the carrier's own member wins (WI-1010) |

Two readings.

**Anthill's practice is universal, opt-out derivation** — Mercury's compiler-generated
unify/compare, not Haskell's opt-in `deriving`. Nobody writes anything to get a `domain`.

**One priority rule has been reinvented at each site: written beats derived.** It is
058's *fill silence, never overwrite speech*, applied at the declaration instead of at
dispatch. A general mechanism should state it once.

The last row is the only derivation written in anthill, and it is exactly Haskell's
default methods — the thing `DeriveAnyClass` rides on.

## 2. Deriving is a ROW and a BODY

Haskell and Scala both factor it this way: the *claim* "`Show[Point]` holds, under these
conditions", and the *evidence*, the operation bodies. Both also hardwire exactly ONE
derivation — the structural description, `Generic` / `Mirror` — and make everything else
library code against it.

Haskell then has to encode structural recursion in instance resolution over `Rep`,
because that is the only type-level logic engine it has. Anthill has a real one, and it
already has the representation: a named tuple IS the product representation, with
`Concat` / `Without` as its type-level algebra, and reflect already answers
`fields(kb, entity)` and `constructors(kb, sort)`. So the mirror is nearly free. What is
missing is a row generator and a body generator.

## 3. The three clients are three different things

### 3.1 `Eq` / `PartialEq` — a row with NO body

Structural `eq` is the builtin, so all the content is in the condition. The move: emit an
ordinary WI-869 conditional provision, generated SYNTACTICALLY from the field types, with
self-references dropped:

```anthill
provides Eq[S] :- Eq[F1], …, Eq[Fn]
```

`eq_derive`'s fixpoint pair then becomes two readings of generated clauses. Its own
header already names them: "Total" is a GREATEST fixpoint — the coinductive reading of
the conjunctive clause above, where a cycle through derived rows succeeds; "Partial" is a
LEAST one — the ordinary inductive reading of one `NonEq[S] :- NonEq[Fi]` clause per
field.

This delivers the parametric leg 058 §3.10 still lists as proposed. `Eq[Pair] :- Eq[A],
Eq[B]` is the same rule with parameters in the field types, which is exactly what
`sort_functor_of_view` cannot see — "a fixpoint over concrete field types has nowhere to
put a condition on a type parameter. A clause does."

It needs two things that do not exist:

- **Tail goals over type EXPRESSIONS in the sort's own parameters.** A field
  `hold(p: Pair[A, B])` needs the goal `Eq[Pair[A, B]]`; the spec admits a "spec
  instantiation over the declaring sort's own parameters" and whether that reaches a
  parameterized argument is unmeasured.
- **A coinductive reading of a cycle through derived rows.** Today a cycle is an
  elimination (058 §3.8: a candidate "eliminated only by cycle detection").

**What is broken today — MEASURED (749c88d4, 2026-09-18), filed as WI-20260918-CKD4J.**
USER DIRECTION: the parametric skip is an ERROR in `eq_derive`, not a scope note. Each
program is `contains(cons(head: X, tail: nil), X)`, which `requires Eq[T]`:

| `X` | result |
|---|---|
| `ibox(v: 1)` — `entity ibox(v: Int64)` | loads, answers 1 — the control, WI-1098's case |
| `box(v: 1)` — `sort Box { sort T = ?  entity box(v: T) }` | LOAD ERROR, "`Box` provides no `Eq`" |
| `holder(o: some(1))` — `entity holder(o: Option[T = Int64])` | LOAD ERROR — a NON-parametric sort, every type concrete |
| `some(1)`, stdlib `Option[T = Int64]` | LOAD ERROR |
| `cons(head: 1, tail: nil)`, stdlib `List[T = Int64]` | LOAD ERROR — a list of lists cannot be searched |
| a `SortedSet[T = Int64, O = Int64]` | LOAD ERROR |

The equality itself works — `eq(box(v: 1), box(v: 1))` and its unequal twin answer 1 and
0 with no provision written — so what is missing is the ROW. And the target form works:
hand-writing `provides Eq[Box] :- Eq[T]` beside its `PartialEq` twin makes the `Box`
program load and answer 1. The gap was quiet until WI-1102's positive use-site discharge
turned "no row" into a refusal.

**The target row is not free — MEASURED (2026-09-19, reverted experiment; details on
CKD4J).** Hand-writing `provides PartialEq[List] :- PartialEq[T]` + `provides Eq[List] :-
Eq[T]` (the same for `Option`) — exactly what the derivation would emit — did two things.
First, `provider_dict_chain` turns every tail goal into a dictionary-chain SLOT, and every
body the carrier owns then sees it as an enclosing `requires`. In `List.nth`, `gt(i, 0)` on
`Int64` was refused as a non-forwarded wildcard (WI-821), and 511 anthill-core tests failed.
Second, `eq` over an `Option`/`List` at an ABSTRACT element became a load error, which is
how `Pair` already behaves. That hits the eight `splitFirst(?s) = some(?p)` stream laws and
any rule like `eq(some(?a), none)`. So one of two things has to happen first: the derived
conditions become check-only (discharged, never slotted), or a provision's tail is scoped
to that provision's own members.

And it has an engineering payoff, which is the argument for generation entering by the
front door. `eq_derive` asserts its rows at TWO points in the pipeline, refreshes the
sort-ops table after the first, and marks the second half's rows
(`mark_unbacked_derived_provision`, WI-1103) so a later phase's coverage walk skips them.
Each is a consequence of asserting rows mid-pipeline.

### 3.2 `Raisable.tag()` — a universal row, a trivial NON-structural body

The signature is fixed and the body is `tag() = T`, the type in value position (055;
027.4 records `tyOf[T](x: T) -> Type = Cell[V = T]` evaluating to `Cell[V = Int64]`).
There is no structural recursion here at all.

This is Haskell's `Typeable`, which GHC stopped deriving in 7.10: every type has it, the
solver supplies it, user instances are forbidden. Haskell's OVERRIDABLE half is
`Exception.fromException`, and it exists to build hierarchies. Anthill already gets
hierarchies from subsumption over the type term — continuum point 3 — so the motive for
the override is gone, and 027.4's hazard with it ("a user-provided match can decline a
payload the typer already discharged").

**Lean: derived-only.** Then there is no instance table: a monomorphic raise site gets a
typer-written constant and a polymorphic one reads the type-argument channel, which is
what 027.4's throw-site table already says. The spec earns its place only as a BOUND —
`Raisable[S]` holds for the nominal fragment — so a closure payload is refused at the
raise site instead of `value_inhabits_type` going loud at the boundary. `Raisable` is a
client of the row half only, with a plain default body on the spec.

### 3.3 `copy` — not deriving at all

Scala synthesizes `copy` per case class because it could not type "any subset of the
fields, by name". Anthill can, since 056:

```anthill
operation copy[R](e: T, ...args: R) -> T
```

with the membership and type check living in a type-constructor reduction the way
`Without`'s does — that reduction already refuses a field that names nothing in `T`, or
mismatches its type.

**WI-188's description predates 056** (created 2026-05-07; 056 delivered 2026-07-17), so
it is stale against the language:

- (a) the grammar change and (b) the `CopyExpr` IR node look unnecessary;
- (c) the typer step becomes a dual of `Without` over a `FieldsOf[T]`-style mirror;
- (d) the lowering is 056's rule-head face:

  ```anthill
  rule copy(?e, ...?args) <=> copy_expand(?e, ?args)   @[simp]
  ```

  expanding to the constructor call with projections. That keeps the ticket's "no new
  runtime concept", and cpp / smt codegen see a plain constructor application.

The spelling is `wi.copy(status: Claimed(…))` — a named argument is `name: value`, where
the ticket wrote `=`. A multi-constructor receiver follows the distributive-projection
rule.

`copy` is structural POLYMORPHISM, not derivation: its admissible arguments depend on the
call site, so no finite set of generated declarations expresses it. It belongs to the same
extension family and needs only the expression-position firing site, which exists.

## 4. Bodies: generate, don't reflect

For a spec with a real structural body — a lexicographic `compare` — there are two routes:
a runtime structural view (Prolog's `=..`; `replace_named_arg` in anthill-todo is this),
or per-carrier generation into ordinary declarations the ordinary typer then checks.

**Generate.** 058 says run time selects no dictionary from runtime data; a value does not
carry its type arguments (3MV2C is that defect); and a reflective body lowers to neither
C++ nor SMT. A generated `Pair.compare` would be what `prelude/pair.anthill` hand-writes
today.

*The output of a derivation is something the author could have typed.* That is the
testable invariant — print the derived declaration and compare — and it is the escape
hatch when someone needs to edit one.

## 5. The mechanism

### 5.1 What 043.1 already gives

Classification by signature (`typing::is_macro` — every parameter and the result an
occurrence, no marker); compile-time evaluation by the scratch interpreter; the purity
gate with `Error` as the REJECTION channel (`check_macro_purity`); fuel and the
ancestor-loop check; `Synthesized{from, by}` provenance; the ambient, phase-adaptive
`kb()`. Two macros ship, `Relation.guarded_of` and `conjoin_of`, both host builtins.

So the fork "is a generator an operation or a relation?" dissolves: it is both halves of
a `@[simp]` macro rule. The RULE is the trigger — its head says which clause it answers —
and the OPERATION is the generator.

### 5.2 The clause needs no grammar

A sort already accepts a trailing `@[…]` and an entity a trailing one too, the keys are
open ("additional keys are project-defined"), and the loader records the block
(`record_declaration_block`). So this parses and loads today, inertly:

```anthill
sort Point
  entity point(x: Int64, y: Int64)
end @[derive: Show]

rule derive(Show, ?carrier) <=> Show.derived(?carrier)   @[simp]
```

The engine synthesizes the redex `derive(<value>, <carrier>)` per entry. The value is a
term, so a generator takes arguments for free — `@[derive: Json(naming: snake)]`.

The carrier argument is a TYPE-REFERENCE occurrence, not a new "declaration occurrence":
043.1 §3.4 already says a macro's context is its arguments' types plus the ambient KB, and
the generator reads structure through `fields(kb(), T)`.

**`derive` must be a LOUD key.** An entry no rule fires on is a load error. Today a
misspelled key is silently project-defined, which is the silent skip the development
principles forbid.

### 5.3 What is new — three pieces

- **Result shape.** `is_macro` demands exactly `NodeOccurrence` / `Expr`. A derive returns
  DECLARATIONS: a reflect `Decl` sort beside `Expr` — an operation, a provision with
  conditions, a rule, a group. The EMPTY group must be legal: since WI-902 a macro cannot
  decline, and "nothing to derive here" is a legitimate answer for any derivation whose
  applicability the engine's fixpoint does not decide for it (§5.6).
- **Splice site.** Mint the new names in the carrier's scope and run the ordinary per-item
  loader path. Generated items are built from resolved `Symbol`s and `Expr` occurrences,
  so they need minting but NO name resolution — hygiene the way 043.1 already has it. A
  generated body is typed by the ordinary typer pass, so there is no re-type step.
- **Firing point.** Not the typer. `derive_total_eq`'s doc comment measured why: "a
  provision only reaches a call site through the typer… Asserted [after it] the fact
  exists and NO call site was ever rewritten to read it." So: after the declarations
  load, BEFORE provider coverage, the sort-ops table, and the typer — where
  `derive_total_eq` sits today, minus its table refresh.

All derive redexes fire against the WRITTEN knowledge base and their output lands
together. That makes expansion order-independent, and it is Rust's rule: a derive sees the
item as written, never another derive's output.

### 5.4 The naming consequence

Path names in operation and rule bodies are resolved during load, which is before derive
fires. So **within the phase that derives it, a derived member is reachable by DISPATCH
and by DOT — both typer-time lookups — and not by qualified path.** A later phase sees an
ordinary name.

For spec derivation this is invisible: nobody names `Point.show`, they call `Show.show(p)`.
For a lens-style generator it is a real restriction, and it must be reported loudly — "
`x_lens` is derived on `Point` in this load phase; reach it through a receiver".

It also answers the scaland worry. Scaland has a resolver and no typer, so it never fires
a `@[simp]` macro; under this rule it also never MEETS a derived name inside the deriving
phase. The residue is a later phase naming a derived member by path.

### 5.5 Staging

A generator written in anthill must come from an EARLIER load phase — Rust's
proc-macro-crate rule. It runs pre-typer, and its own spec-op calls dispatch through
typer-inserted `CallClass` tags, so its body must already be typed. Using a generator
from the phase being loaded is a load error, not a decline.

Host macros are exempt, which gives the first client: re-home the `Eq` / `PartialEq` rows
from `eq_derive.rs` as a host derive macro. They already live at that point in the
pipeline.

Generators written in anthill also wait on the build API. `occurrence_type` is exposed
(`reflect.anthill`); `make_occurrence` and `occurrence_expr` are in 043.1 §9 step 5 and
appear nowhere in the tree. They do NOT wait on WI-189: this is *low-level* derivation,
and 043.1 §8 already says the build API is the primitive quotes would lower to.

### 5.6 Derivation on silence — no clause per (spec, carrier) pair

USER DIRECTION, raised as a question after the first draft: *do we need a derive clause
for each pair? If the derivation lives in `Show`, `Show[T]` can be generated for any
known `T`.* Yes — and it is what `eq_derive` and `domain` already do. The derivation is
written once, in the spec's own body, and the clause of §5.2 survives only where a
derivation is a CHOICE (`Ord`) or takes ARGUMENTS (`Json(naming: snake)`).

**The row/body split applies once more, and it decides who owns what.** The CLAIM is the
same rule for every structural derivation — *every field type has the spec, written or
derived* — so the ENGINE owns it: `eq_derive::classify` generalized over the spec, a
greatest fixpoint over the field-reference graph, its leaves the written provisions. The
spec's macro produces BODIES only, and only for carriers inside the fixpoint.

That ordering — every claim before any body — is what makes a universal derivation
failure-free. It never emits a body that cannot type, so "not derivable" is SILENT and
never a load error, while the explicit clause stays loud. A use site that then finds no
`Show[T]` gets the ordinary missing-provision error, and the fixpoint can say which field
kept `T` out.

**"Any known T" ranges over SORTS, not instantiations.** A parametric sort is materialized
once: the row `provides Show[Pair] :- Show[A], Show[B]`, the body dispatching through the
condition slots — what `prelude/pair.anthill` hand-writes today. So the set is finite.

**When: eagerly, at the LATER of the two declarations.** When a carrier loads, for every
derivable spec visible to it; when a spec carrying a derivation loads, for every carrier
already known. Each pair is materialized exactly once, in the layer of whichever came
later, which is the orphan rule automated: no third package ever derives, so two
packages cannot produce rival copies.

Eager and not on-demand for two reasons. A rule-body or query dispatch picks its
implementation from the RUNTIME carrier (WI-1044), so no static site ever demanded that
pair; and run time performs no typing operations (058 §3.9), so nothing can be generated
then. Defined this way, laziness is a later optimization that cannot change meaning. The
cost — known sorts × derivable specs, bodies typed at every load — is the number to
measure.

**Speech anywhere on a base sort silences the derivation for that sort** — `eq_derive`'s
`spoken_for`. A written ground row beside a derived parametric one is the overlap
`one_default` exists to refuse.

**What the clause was protecting against now needs its own answer.**

- *Silence is sometimes the point.* 058 §3.6 opens: "whether silence may pick is not a
  property of the spec." For a structural derivation the fixpoint computes that per
  carrier, which is fine for `Show`. For `Ord` a derived instance turns field order into
  a semantic commitment, and `SortedSet[T = WorkItem]` being refused is useful. So a spec
  marks whether its derivation answers silence or only a request.
- *The structure is not always the meaning.* A derivation reads a carrier's FIELDS. That
  is right for `Point` and wrong for a carrier whose fields are an implementation detail,
  where a derivation answering silence cannot tell *the author forgot* from *the author
  refused*. Three candidate rules for when it must NOT fire:

  1. `eq_derive`'s BOUNDARY, generalized — a carrier that dispatches its own `eq` is
     outside every structural derivation.
  2. Constructor visibility — constructors marked `internal` are not derivable from
     outside, as a hand-written instance would not be.
  3. An explicit refusal by the author — 058 §3.6 already defers "a per-carrier
     `NoDefault` guard" in the same idiom.

  **NO SHIPPED SORT DEMONSTRATES THE NEED, and two turns of the session claimed one
  wrongly.** `Set` declares no entity, so a field-wise derivation never reaches it.
  `SortedSet` was then offered as an author's refusal, and its file says the opposite:
  "Equality is STRUCTURAL, and how exact that is depends on `O`" — canonical where `O` is
  an `Ord`, finer than the class reading where `O` is coarser, and documented as that. A
  derived `Eq[SortedSet] :- Eq[T]` AGREES with the file. Its absence today is the
  `eq_derive` parametric gap (USER DIRECTION: that is an error in `eq_derive`; §3.1 and
  the ticket it names), not a decision. So the three rules stay candidates.

  The precedent for the whole shape is Rust's auto traits: structural, answering silence,
  opted out of by a negative impl — and Rust admits them for MARKER traits only, keeping
  every trait with methods opt-in.
- *A sort with only operations has no fields to read.* USER DIRECTION: such a sort cannot
  be given `eq` automatically — "maybe the collection knows". It does, and that is a
  third kind of derivation: through an INTERFACE instead of through the representation.
  `Set` already is one — its `eq` is extensional, stated against its own operations. It
  needs no new mechanism: a spec's default body (WI-876) plus a spec's `provides` read as
  a conversion (WI-1110) is how `Ord` already yields the floor below it. WHICH spec knows
  is per collection KIND — mutual `subset` for a set, pairwise for a sequence — so it
  cannot live on a general `Collection`.

### 5.7 Rules of the road

- An explicit `@[derive: G]` beside a hand-written item of the same name is a LOUD
  conflict — two acts of speech. An implicit derivation yields silently to a written one.
- A generator is pure, fuel-bounded, and raises at most `Error`; the raise is a rejection
  reported at the clause's span.
- Every generated item carries its provenance, and a reflect fact says which generator
  made it for which carrier. A diagnostic inside generated code has no source text to
  point into, so it must print the generated item.

## 6. How this lines up with Scala, and where it goes further

Scala's `derives Show` is tiny on the language side: it introduces a `given` with a fixed
name and signature, syntactically, and the `derived` macro fills the body at typer time.
That is §5's split — names and rows early, bodies typed late — arrived at from the other
direction.

Scala's def-macros cannot add MEMBERS, which is why `copy` is compiler-synthesized there
and why macro annotations are still experimental. "Generate new structures" is therefore
more than Scala's deriving: it is Rust's derive, or Lean's deriving handlers.

Three lessons from Scala's low-level derivation carry over:

- **Derive once per carrier, never per use site.** Automatic derivation re-expanding at
  every use is what made it slow. Firing at the declaration is semi-automatic by
  construction, and a universal generator must keep that property.
- **Recursive carriers need no knot-tying here.** A Scala macro must make the instance
  refer to itself lazily; a generated anthill body calls `Show.show(child)` and recursion
  goes through ordinary dispatch.
- **Diagnostics from generated code point at the clause.** `Synthesized{from, by}` and the
  reject path are the answer, and 043.1 §3.5's precision rule applies: attribute each
  built node to the input part it came from.

## 7. Set aside, and why

- **One Rust seam (`Derivation { spec, applies_to, emit }`) before any surface.** The
  first suggestion of the session. Superseded: the seam already exists, and it is macro
  registration.
- **A syntactic declaration face between parse and `scan_definitions`.** The generator
  would read the carrier from parse IR and emit parse-IR items, so every derived name
  exists at pass 1 and WI-321's invariant is untouched. It buys path-visible names in the
  deriving phase. It costs the resolved field types, and a SECOND expression IR —
  reflect's `Expr` is symbol-resolved (`apply(fn: Symbol, …)`) and cannot be used before
  pass 1. Still the fallback if §5.4 is rejected; pass 3 → pass 4 (WI-295) is the
  precedent for a name minted late and an import deferred until it exists.
- **Generators as relations** — each solution of `derived(G, ?carrier, ?item)` one
  generated item, runnable by the resolver both implementations share. Motivated by
  scaland; dissolved by §5.1 and §5.4.
- **A runtime-generic default body over a structural view.** §4.
- **A blanket provision clause with a variable carrier**, written on the spec. It makes
  the dispatch ladder understand a new clause form, where generation emits only the
  WI-869 form the ladder already reads.

## 8. Open decisions

1. **Is the dot-and-dispatch-only rule (§5.4) acceptable?** THE open decision. If derived
   names must be path-visible in the deriving phase, derive fires inside
   `scan_definitions` and reads parse IR (§7).
2. **`Raisable`: derived-only or overridable** — 027.4's own fork. This session's lean is
   derived-only (§3.2).
3. **When a derivation on silence must NOT fire (§5.6).** Three candidate rules — the `eq`
   boundary, constructor visibility, an explicit refusal — not exclusive, and none yet
   demanded by a shipped sort. Separately, how a spec marks "answers silence" against
   "only on request";
   058's `default` modifier is the word already in the language, and whether it is the
   same axis is undecided. USER DIRECTION elsewhere (WI-20260908-9WVT7): anthill and user
   namespaces should not differ, so a namespace privilege is out — the later-of-the-two
   rule needs none.
4. **The `Decl` sort's first forms** — presumably a provision with conditions and an
   operation with a body, since the first two clients need exactly those.
5. **A fresh-binder primitive.** A body for a sum type builds `match` arms, and the arm
   binders are new names the generator invents. A single-constructor entity avoids it by
   projecting.
6. **May a generated item carry its own `@[derive]`?** Rust allows it. It needs the fuel
   bound and nothing else.

## 9. To measure

Nothing below was driven. Each is a claim this document leans on.

- Does a provision's `:- goals` tail admit `Eq[Pair[A, B]]` — a spec instantiation whose
  argument is a parameterized type over the sort's own parameters?
- What does resolution do today with a cycle through two conditional provisions
  (`Eq[A] :- Eq[B]`, `Eq[B] :- Eq[A]`)? §3.1 needs it to succeed for derived rows.
- Does a dot call's method fallback reach a prelude-level `copy` for an arbitrary entity
  receiver? Every capture client so far — `fix`, `rename` — is a member of `Relation`.
- How does an anthill-written EXPRESSION macro get typed before it is first run, when it
  is defined in the batch that uses it? Unasked so far, because both shipped macros are
  host builtins.
- Does `@[derive: Show]` on a sort really load clean today, and where does the recorded
  block surface in reflect?
- What §5.6's eager materialization costs: known sorts × derivable specs, one typed body
  each, at every load. `eq_derive` pays only for rows, so it is no guide.
- Whether `eq_derive::classify` generalizes over the spec as cleanly as §5.6 assumes. Its
  leaves, its boundary predicate and its Partial half are all `Eq`-specific today.

Unexplored, possibly a payoff: a GENERATED field-wise `eq` body for a Partial composite
would replace three implementations that today must agree — the resolver's
`sem_eq_core`, the interpreter's `semantic_equal`, and the C++ `operator==` — and a
generated witness for `NonEq.nonEqRefl` would retire `mark_unbacked_derived_provision`.

## 10. A possible order

One ticket was filed from this session, at the user's request: **WI-20260918-CKD4J**, the
`eq_derive` parametric gap (§3.1). Nothing below is ticketed.

1. **WI-188 as an expression-position host macro**, over 056's rule-head face. No new
   mechanism, and it is the smoke test for "a macro reads an entity's structure and builds
   a constructor call". Its ticket description needs rewriting first (§3.3).
2. **Expose the build API** (043.1 §9 step 5) — the prerequisite for any generator written
   in anthill.
3. **The pre-typer firing site, the `Decl` result and the splice**, with the `Eq` /
   `PartialEq` rows as the first client. Under §5.6 that means generalizing `classify`
   over the spec, not wrapping it in a macro — `Eq` has rows and no body, so it exercises
   the engine-owned half alone. Behaviour-neutral by construction, so its acceptance
   cannot be the existing `wi664` / `wi1098` rows — those pass either way. What it can
   assert is the REMOVAL: no sort-ops table refresh, one assertion point.
4. **The first generator written in anthill** — a `Show`-like spec, exercising a row, a
   generated body, and a recursive carrier.

# Proposal 055: Types in value position — denotation, phases, and profiles

**Status:** Draft (2026-07-13; outcome of the WI-709 follow-up brainstorm)
**Depends on:** WI-311 (grammar `application` merge — the parser does not distinguish type from term application; the loader does), WI-361 (`Type` = opaque, term-backed handle; structure reified on demand by `extract`), WI-206 / WI-707 (sort names and parameterized types as value arguments, accepted where the position expects `Type`), WI-709 / WI-710 (`check_sort_type_args` on all four lowering paths; the depth + bracket-surface instance-claim gates), [022-typing-as-facts](022-typing-as-facts.md) (`TypeOf` judgments as KB facts), proposal 037 (the `Modifiable` marker the first consumer, `is_modifiable`, reads)
**Related:** [052-rules-as-stream-valued-operations](052-rules-as-stream-valued-operations.md) (`Relation[T]` — what makes type-indexed facts first-class composable queries), [053-fact-mutability](053-fact-mutability.md) (`constant` loader-emitted reflection facts), [049-equality-and-unification](049-equality-and-unification.md), WI-302 (`denoted` — the mirror crossing, value into type position), WI-708 (the dead body-side type-arg frame channel — prerequisite for `type_value[T]` in generic bodies), WI-010 (self-hosted type resolver — the largest planned consumer of types-as-values), proposal 029 + WI-089 (profile-keyed codegen mapping facts — the substrate of §5), proposal 039 (`const` — the future compile-time-folding channel of §5.3)
**Affects:** stdlib (move the `Type` cluster `anthill.prelude` → `anthill.reflect`), loader + typer (type-checking reaching lowering paths 3 and 4; qualified-name updates), cpp-gen / rust-gen (the profile fence), `docs/kernel-language.md` (new §4 subsection; §5 fact note), reflect interface (consolidation pass). **Grammar: no changes required** — WI-311 already merged the productions; the parse IR records the `[…]`-vs-`(…)` surface (WI-710); an empirical recheck (end of §2) confirmed every §2 value position parses and documents two pre-existing edges.

## Problem

While delivering WI-709 we noticed that a type expression can stand in an
ordinary value position:

```anthill
is_modifiable(Cell[V = Int64])     -- a parameterized type as a call argument
facts_of(kb(), WorkItem)           -- a bare sort reference as a call argument
```

This was never decided as a language rule — it *emerged*, and the immediate
question was whether to bless it or to forbid it and require an explicit
reification marker (`is_modifiable(type_value[Cell[V = Int64]])`), with the
`fact Modifiable[T = Cell]` clause form re-examined alongside.

The finding, on inspection, is not a grammar leak. It is the planned
convergence of three separately-made decisions:

1. **WI-311** merged `parameterized_type` and `instantiation_term` into one
   grammar `application` node under the stated principle *"don't distinguish
   in the grammar, distinguish in the loader."* The parser accepts
   `Cell[Int64]` anywhere an application may stand; classification is the
   loader's job, by resolution.
2. **WI-361** made `Type` an opaque, **term-backed** handle: a `Type` value IS
   an ordinary term — `Ref(S)` for a bare sort, `Fn{S, named}` for a
   parameterized one — with deep structure reified on demand
   (`extract(t) -> TypeExtractor`), never stored as a shadow ADT.
3. **WI-206 / WI-707** made acceptance turn on the *expected sort*: a sort
   expression in a value position is accepted exactly where that position
   expects `Type` (the `type_slot_arg_hint` chain, gated on
   `kind_of(sym) == Sort`); anywhere else a stray sort name stays a loud
   `UnresolvedName`.

WI-709/WI-710 then closed the checking gaps (undeclared or over-applied type
arguments are now loud on all four lowering paths). What remains is to state
the semantics as a rule of the language rather than an archaeology of commits,
and to answer the two design worries that motivated the "forbid" pole:
*types should be compile-time*, and *some compilation profiles (embedded C)
have no reflect interface at all*.

Runtime type reflection on reflect-capable hosts is a *goal* of this
design, not a leak to plug — so "types should be compile-time" cannot mean
"no type values at runtime". What that intuition is actually owed is
ordinary typing plus two fences: a type expression is simply a value of
sort `Type`, so a non-`Type` position rejects it as an ordinary sort
mismatch (§2); a `Type` *value* never re-enters the typer as a type — the
one restriction with real teeth (§4); and in profiles without reflect
interfaces, `Type` exists only at compile time (§5). The forbid-and-mark
alternative (`is_modifiable(type_value[Cell[V = Int64]])`) is weighed — and
declined — in §"Alternatives considered".

## Decision (summary)

1. **Types in value position are legal, by one uniform rule.** A type
   expression — applied (`Cell[V = Int64]`) or bare (`Cell`) — denotes a
   `Type` value wherever it stands, and ordinary type-checking does the
   rest: a generic `T` instantiates to `Type` exactly as it would to
   `Int64`; a `String`-expecting position fails loudly. There is no
   type-specific placement restriction. (§2)
2. **`Type` moves from `anthill.prelude` to `anthill.reflect`.**
   Types-as-values is reflection; the sort lives with its peers `Term` and
   `Symbol`, and importing it names the dependency. (§3)
3. **Per compilation profile, `Type` is either *full* or *compile-only*.**
   Host/interpreter profiles have runtime reflect, so `Type` is an ordinary
   runtime value. Reflect-less profiles (embedded C) keep `Type` fully usable
   in the specification surface — facts, rules, constraints, `requires`/
   `ensures`, proofs, everything the host toolchain evaluates at load and
   verification time — but no reflect sort may appear in the value signature
   of an operation compiled to the target. (§5)
4. **The value→type direction is unchanged.** Its existing forms — bracket
   type-args, `denoted` (a value persisting as an inert label),
   `ExprCarried` (a value receiver whose statically *synthesized type* is
   projected, the value itself eliminated), `RigidTypeProjection` (a
   type-world subject) — all resolve from static information; none
   evaluates a value. This proposal adds no form; in particular a
   `Type`-sorted *value* never dereferences into the type it names. (§4)
5. **Instance claims stay facts.** `fact Modifiable[T = Cell]` is a top-level
   instance claim under the WI-710 depth gate — a declaration form, not a
   type in value position — and is not touched by this proposal. (§6)

## Design

### §1 One representation, two nominal faces

A type value is term-backed (WI-361) but `Type` is **nominally distinct from
`Term`**, deliberately: `Eq`/`Lattice` instances ride `Type`'s nominal
identity, because keying the type lattice on `Term` would make it the
universal default on every term. The crossings between the faces are explicit
conversions and stay so: `sort_as_term(s: Type) -> Term`,
`term_as_sort(t: Term) -> Option[Type]`. Consequence: a type expression in
value position types as `Type`, not `Term`, and does not leak into
`Term`-expecting slots without the explicit crossing.

### §2 The denotation rule, at all four altitudes

A type expression in value position — applied (`List[T = Int64]`) or bare
(`List`, the same type with its parameter left unbound) — **denotes a `Type`
value**, and ordinary type-checking takes over from there. There is one rule
and no special cases; nothing is decided by markers written at the use site:

> Against `is_modifiable(t: Type)` the expression fits the declared
> parameter; against a generic `idT[T](x: T)` it infers `T = Type` exactly
> as `idT(5)` infers `T = Int64`; against `length(xs: List[…])` it fails
> loudly as `Type` vs `List`. So `idT(5)`, `idT(List[T = Int64])` and
> `idT(List)` are three instances of the same mechanism — the argument
> determines `T` (`Int64`, `Type`, `Type`).

How does the loader know that an expression in a value position is a type
expression at all? There is no marker; the grammar has one application node
(WI-311: don't distinguish in the grammar, distinguish in the loader), and
the loader classifies an expression by **resolving its head name**
(SymbolKind — the WI-313 principle):

- the name resolves to a **sort** → a type expression: bare `List` is a
  type reference, `List[T = Int64]` a type application. A standalone entity
  counts as its sort here (kernel §6.3: a standalone `entity` is a
  single-constructor sort) — these are the same names
  `facts_of(kb(), WorkItem)` accepts today;
- the name resolves to a **parameter, field, or local** → the expression
  denotes that binding's value, as ever;
- the name resolves to an **operation** → a call; `op[A = Int64](…)` is a
  call with call-site type-arguments (WI-269), not a type, although it is
  the same written shape as `List[T = Int64]` — the identical-shape pair
  that shows resolution, not shape, is the decider;
- the name resolves to **nothing** → a loud `UnresolvedName`.

Recorded surface decides exactly one remaining pair: for a *sort-headed*
head, `Leaf[…]` (brackets) is a type application while `Leaf(name: "tip")`
(parentheses) is a constructor call — the parser records which was written
(the WI-710 surface gate), so construction is never confused with
denotation.

Two costs of uniformity, stated honestly. First, a bare `Ref(List)` and an
applied `List[T = ?]` are *semantically* the same type but *structurally*
different terms (`Ref(Cell)` does not unify with `Cell[V = Int64]` — the
WI-206 lesson), so their equivalence is carried by the operation layer
(§7), not by term identity. Second, one diagnostic changes flavor: a stray
sort name in a `String` slot today errors as `UnresolvedName`, under this
rule as `expected String, got Type` — still loud, arguably clearer; the
residual niche where a mistake can now travel (a forgotten-args constructor
name, `register(Leaf)`, flowing into a position that *accepts* `Type`) is
the price of the uniform rule, and work item (c)'s diagnostics must name
the denoted sort so the trail stays short.

This rule is **not** what the implementation does today; closing the gap is
work item (c). As shipped (smoke-tested 2026-07-13), denotation happens
only where the position already expects `Type` (WI-206 wired it for bare
names, WI-707 for applied forms); in every other position both forms are
*rejected* — the applied form with an unhelpful diagnostic
(`type mismatch in Int64.name: expected resolved name, got unresolved`: the
`Type` hint never fires, so the reference is left unresolved rather than
classified), the bare form as `UnresolvedName`. The gap is one-directional —
today's implementation rejects programs the rule accepts, never the
reverse — so adopting the rule is a pure error→accepted widening: no
currently-accepted program changes meaning. (The bare *operation*-name
analogue — a `Function` value only under a function-expecting position, the
`hof_arg_hint` — is deliberately left untouched; unifying that too is a
separate decision, out of scope here.)

Note what this section does **not** contain: any type-specific placement
restriction. Every rejection above is an ordinary sort mismatch, identical
in kind to `length(5)`. The restrictions this proposal does impose live
elsewhere, each with a concrete necessity: §4 — a `Type` value cannot be
used *as a type*, because otherwise typing a program would require running
it; §5 — a compiled operation in a reflect-less profile cannot carry a
`Type` at runtime, because the target has no representation for it; §1 —
`Type` and `Term` stay nominally distinct, because otherwise nothing could
dispatch on type-ness.

A written parameterized type has four lowering paths (the WI-709/WI-710
inventory), and the rule must hold at each:

| # | path | position | placement rule today | type-arg check today |
|---|------|----------|-----------------|----------------------|
| 1 | loader `type_expr_to_child` | type annotations | trivially a type position | ✅ WI-709 |
| 2 | typer sort-application arm | operation-body value position | ✅ `Type`-slot hint (WI-206/707) | ✅ WI-709 |
| 3 | `convert_term` | fact / constraint terms | ⚠️ none — smoke-confirmed silent | ✅ WI-710 |
| 4 | `build_body_atom_occurrence` | rule-body atoms (WI-246 occurrences) | ⚠️ none — smoke-confirmed silent | ✅ WI-710 |

The ⚠️ gap is real, not hypothetical (smoke-tested 2026-07-13): given
`entity Person(name: String, age: Int64)`, both
`fact Person(name: Cell[V = Int64], age: 42)` and the same atom in a rule
body load without complaint — a well-formed type term sits in a
`String`-declared field and will simply never match. Closing the cells is
work item (c): on paths 3 and 4 the nested type term is a `Type` value
(§2), and where the enclosing functor has declared field sorts the value
must type-check against them — `Type` fits; a declared `Term` field accepts
it too (facts are the raw-term substrate: the §1 nominal fence governs the
expression world, and the loader's own reflection facts store type terms in
`Term` fields like `SortProvidesInfo.spec`); any other declared sort is
loud. Where the functor is an undeclared rule-head or derived predicate,
the term flows into WI-603 rule-atom inference as a `Type`-typed value like
any other. Top-level clauses are exempt via the instance-claim depth gate
(§6). The check must stay value-blind (`List[T = ?x]` loads — the WI-710
precedent).

Two shipped classification rules are restated here as spec, not left in
commit messages:

- **Depth gate:** a top-level sort-headed clause is an *instance claim* (its
  argument grammar is richer — operation bindings `pure = optionPure`,
  carrier positionals `NonMonotonicStore[FileStore]`); only *nested*
  sort-headed applications are type terms.
- **Surface gate:** `[…]` marks type/instance arguments, `(…)` marks
  constructor arguments; shape cannot distinguish a sort-headed constructor
  call (`sort Leaf { entity Leaf(…) }`) from a type application — only the
  recorded parse surface can, and the parse IR records it.

**Grammar recheck (empirical, 2026-07-14).** Every value position this
section blesses already parses — checked by loading a battery of smoke
files: call arguments (positional, named, nested
`Map[K = String, V = Cell[V = Int64]]`), bare sort names, fact fields,
rule-body operands of `eq`/`=`/`<=>`, bracket arguments carrying variables
(`List[T = ?x]`, `List[T = ?]`), dot receivers (`Cell[V = Int64].name`),
list-literal elements, row-valued arguments (`Stream[E = {Error}]`), `let`
right-hand sides, `if` conditions, and operation bodies. No grammar change
is needed. The same sweep measured how much narrower the shipped `Type`
hint is than "argument slots": these parse but fail with the
unresolved-classification diagnostic today — an operation body in return
position **even when the operation declares `-> Type`**, an unannotated
`let` right-hand side (annotated `let t: Type = …` works), dot receivers,
list-literal elements even under a `List[T = Type]` return type, and
row-valued arguments (which also lose their span — the error points at
`0..0`). All are one family with the generic-slot case and are work item
(c)'s checklist.

Two pre-existing grammar edges, documented rather than changed here:

- **A bare `[...]` after a bare-name return type is not a meta block.**
  Tree-sitter is whitespace-blind and WI-311's `prec(1)` resolves the
  shift-reduce toward application, so `-> Int64 [Pure]` parses as the type
  application `Int64[Pure]` — which WI-709 now rejects loudly but
  misleadingly ("over-applied") — and `-> Cell [Pure]` silently binds
  `V = Pure`. This is a trap, not a missing capability: WI-087 already
  provides the keyword-introduced **`meta` clause** as the operation-meta
  surface, designed for exactly this collision (its grammar comment names
  it), and both layouts load (smoke-verified):
  `operation m2() -> Int64 meta [Pure, CppName: "m_two"] = 2`. No
  checked-in `.anthill` source uses the postfix form (repo scan), so the
  wart is latent; work item (f) is the diagnostic that redirects to the
  clause. The one syntactic fix that would make the postfix position
  itself work — `token.immediate('[')` on `application`, so tight brackets
  mean application and spaced brackets mean a meta block — would also
  retire the rule-tag parens workaround (`= constant() [simp]`), at the
  price of whitespace-significance plus a corpus + scaland resync; noted
  as an option, not proposed.
- **Call expressions in bracket values do not parse** (`Cell[V = sz()]` is
  a parse error): bracket arguments are `_type | literals` (the WI-302
  literal path; calls were measured and deferred). Value-in-type stays
  names + literals for now; unchanged by this proposal.

### §3 `Type` lives in `anthill.reflect`

The whole co-defined cluster of `stdlib/anthill/prelude/sort.anthill` moves
to a new `stdlib/anthill/reflect/type.anthill` (namespace `anthill.reflect`):

- `sort Type = ?` and its instance facts (`PartialEq`/`Eq`/`Lattice[T = Type]`),
- `TypeExtractor` (the reified deep structure),
- `TypeBinding`, `NamedTupleElement` (extractor payloads),
- `EffectExpression` (co-defined with `Type` by the WI-320 cycle constraint:
  `present`/`absent`/`open` carry a `Type`, `Type`'s `effects_rows` carries an
  `EffectExpression`; they move together or not at all).

Why this is the honest home:

- `Type` is described, in its own doc comment, as "an opaque handle like
  `Term` / `Symbol`" — both of which live in `anthill.reflect`.
- The cluster already reaches into reflect today (`TypeBinding.param :
  anthill.reflect.Symbol`, `.value : anthill.reflect.Term`), so prelude
  currently depends on reflect — the wrong direction. After the move the
  dependency arrow is uniformly reflect → prelude.
- Profile availability (§5) then follows the namespace with **no special
  case**: a profile that excludes the reflect runtime excludes runtime `Type`
  because that is where `Type` lives.

What does **not** move: `Modifiable` (and `Modify`, `ModifyRuntime`) stay in
`anthill.prelude.effects` — they are typing-level effect machinery, and the
instance-claim form `fact Modifiable[T = Cell]` never needs the `Type` sort
(§6). Only the *query* over them (`is_modifiable(t: Type)`) is reflect.

Deliberately **no prelude re-export**: code that manipulates type values
writes `import anthill.reflect.{Type}`, and the import is the visible signal
that the module has a reflection dependency (and hence a profile constraint,
§5). Effect-row *syntax* (`effects Error`, `Stream[E = {…}]`) is unaffected —
rows are engine-lowered; the `EffectExpression` sort is only their reflected
face.

Migration notes (work item (a)): the engine hard-codes the qualified name at
a handful of sites (`typing.rs` `make_sort_ref_by_name("anthill.prelude.Type")`
×5 incl. the `type_slot_arg_hint` resolve, `load.rs` bootstrap `define("Type",
"anthill.prelude.Type", …)`, plus ~66 qualified references across the cluster
in `term.rs`/`term_view.rs`/`mod.rs`/`ir.rs`/`convert.rs`/`print.rs`); exactly
one stdlib import site changes (`reflect/reflect.anthill` drops its
`import anthill.prelude.{Type}` / `{TypeExtractor}`); persisted-image golden
tests and the scaland stdlib mirror need a sweep. Mechanical, but wide enough
to be its own increment.

### §4 The no-dereference fence (why this is not dependent types)

The value→type direction is untouched by this proposal, and it is richer
than one form — the `TypeExtractor` inventory (§3) already has several ways
a value-world thing appears inside a type expression. What they share — the
actual fence — is that **each is resolved from static information alone;
none evaluates a value to obtain a type**:

- **`denoted`** (WI-302, by SymbolKind `Param | Field | Operation`): the
  value stays in the type **as itself** — an inert **label**, compared by
  identity (`Modify[c]` is indexed by *which* `c`, not by anything `c`
  contains). The only form in which value-ness persists at the type level,
  and it persists without ever being read.
- **`ExprCarried`** (WI-376, `s.T`): mentions a value receiver, but only as
  a **path**. The form is *eliminated at the unify boundary* by projecting
  the receiver's statically **synthesized type**; no value identity
  survives into the resulting type and the receiver is never evaluated.
  Despite the surface, what actually crosses here is a type, not a value.
- **`RigidTypeProjection`** (WI-428, `P.Key`): the subject is already
  type-world — a rigid type parameter (a neutral until instantiated) or a
  manifest sort (δ-grounded at the elimination site).
- **Bracket type-args / type parameters**: static, resolved at load.

The one form that would break this shared property is exactly the one §2's
uniform rule might seem to invite: using a `Type`-sorted **value's content**
as a type. Given `t: Type`, the annotation `List[T = t]` is
`List[T = denoted(t)]` — a list indexed *by the value `t`*, the same label
reading every other parameter gets — **not** a list of whatever type `t`
names; and a `Type`-sorted value is never accepted where the typer needs an
actual type (annotations, bounds, `requires` spec views), because typing
would then require running the program. Types flow **out** (reflection)
freely; nothing flows **in** by evaluation. That sentence keeps
types-as-data from becoming dependent types by the back door, and it goes
in the kernel spec verbatim (work item (e)).

### §5 Profiles: full vs compile-only `Type`

A **profile** is already a real thing in codegen: the profile-keyed
`TypeMapping`/`EffectMapping`/`IncludeMapping` fact overlays that cpp-gen
resolves per target (WI-089; e.g. `cpp17-stl`). This proposal specifies, per
profile, one of two `Type` regimes:

- **Full** (interpreter, host profiles with a reflect runtime): `Type` is an
  ordinary runtime value; every reflect operation is available.
- **Compile-only** (embedded C and any profile without reflect interfaces):
  `Type` — and every reflect sort — exists **only during compilation**.

Compile-only, positively stated: the entire *specification surface* keeps
full use of types in value position in every profile — facts
(`fact Modifiable[T = Cell]`), rules and constraints (including ones that
call `is_modifiable`), `requires`/`ensures`, prover obligations, `TypeOf`
queries — because that surface is evaluated by the host toolchain at load
and verification time and is never lowered to the target. The embedded
artifact never sees it.

The fence sits exactly at the compiled surface:

> In a compile-only profile, an operation selected for codegen must not
> mention a reflect-namespace sort in any **value-carrying position** —
> parameter sorts, return sort, fields of entities it constructs or matches —
> and must not call a reflect builtin from its body. Violations are a loud
> codegen-time error naming the sort, the operation, and the profile.

Notes:

- Half of this fence already exists *mechanically*: a sort with no
  `TypeMapping` fact in the active profile fails `extract_type`. Work item
  (b) turns that incidental failure into a specified early check with a
  diagnostic that says *why* (reflect sort in a reflect-less profile), per
  the "loud error over silent skip" principle.
- Type-level apparatus is exempt by construction: effect rows, type
  parameters, and bounds may mention reflect sorts freely (a row is erased
  before the target; `EffectExpression` never becomes target data).
- Engine-implemented reflect builtins are host code; the fence governs
  *user operations compiled to the target*.
- **Future (not v1):** compile-only also opens a door — a ground reflect
  call in a compiled body (`is_modifiable(Cell)`) could be
  **const-folded at load** through the proposal 039 `const`/simp channel,
  letting embedded code *ask* reflection questions whose answers are compiled
  in. Out of scope here; noted so the fence's error message can someday say
  "…unless the call folds".

### §6 Instance claims are not types in value position

`fact Modifiable[T = Cell]` (and `fact Monad[M = Option, pure = optionPure,
…]`, `fact NonMonotonicStore[FileStore]`) are **instance claims**: top-level
sort-headed clauses under the §2 depth gate, with their own argument grammar.
They need no rescue from this proposal and do not depend on the `Type` sort;
they stay facts — which is what keeps them enumerable through the
discrimination tree and, via proposal 052, composable as `Relation[T]`
values. The observed overlap between op-bearing instance claims and
`provides` (both assert "S satisfies C at σ", one without proof obligations)
is real but orthogonal; folding them is explicitly **out of scope** and
deserves its own proposal.

### §7 Matching semantics: structural facts, semantic operations

Type terms in fact arguments unify **structurally**, like every term:
`Modifiable[T = ?t]` binds `?t = Ref(Cell)` from `fact Modifiable[T = Cell]`,
and that `Ref(Cell)` does not unify with `Cell[V = Int64]` — which is
precisely why WI-206's acceptance ("a parameterized instance answers as its
base does") is implemented as head-sort matching *in the operation layer*
(`is_modifiable`), not as a KB query. This proposal fixes that division as
the rule: **facts state structure; operations carry type-semantic matching**
(head-sort projection, lattice walks). The `Eq`/`Lattice[T = Type]` instances
leave the door open to carrier-dispatched semantic matching on `Type` later
(the WI-616 SemEq precedent); the door is noted, not walked through.

The same division answers a question the uniform rule makes pressing: what
do `=` and `<=>` mean on `Type` values? Both stay what they are everywhere
else. `=` dispatches through the carrier's own equality (WI-616;
`fact Eq[T = Type]` rides the type's nominal identity), and `<=>` is the
kernel's **term** unification (proposal 049) applied to the canonical term
backing — no type-aware dispatch. On ground, canonically-constructed types
the two agree and do what a reader expects (`List[T = Int64]` unifies with
`List[T = Int64]`: one hash-consed term — the single-constructor discipline
is what makes this reliable). They deliberately do **not** implement
type-language equivalence: `List <=> List[T = ?x]` fails (`Ref(List)` vs a
`Fn` — the same lesson as `Modifiable`'s `Ref(Cell)` above), and effect
rows unify as stored structure, not as the typer's row normal form. Making
`<=>` type-aware is rejected for a mechanical reason beyond taste: fact
lookup is discrimination-tree indexed on purely structural keys, so a
type-aware unifier would match goals the index has already pruned (and
vice versa), desynchronizing resolution from indexing. Type-language
equivalence — open-parameter matching, row normal forms, lattice
subsumption — is the typer's judgment; when programs need it first-class
(the WI-010 self-hosted resolver will), it arrives as an explicit reflect
operation beside `unify(a: Term, b: Term)` (049's term-level face), not as
new behavior of `<=>`.

### §8 The two interface conventions, and `type_value[T]`

The reflect interface passes types in two ways, and the rule for choosing —
until now folklore — is part of this proposal:

- **Bracket type-arg** (`term_as_entity[E]`, `fresh_var[T]`): the type
  parameterizes the **signature** — the return type depends on it. Static,
  erased/monomorphized, available in **every** profile.
- **`Type`-sorted value parameter** (`is_modifiable(t)`, `operations(kb,
  sort)`, `facts_of(kb, sort)`): the type is **data** inspected by the
  operation. Reflection; runtime only in full profiles, compile-time contexts
  otherwise.

The explicit bridge between them is the one genuinely useful piece of the
rejected "marker" design, added as the canonical static→dynamic reification:

```anthill
operation type_value[T]() -> Type
```

so generic code can reify its own type parameter (`type_value[T]()` inside an
`operation f[T](…)`). Body-side `T` currently lowers through the dead WI-272
frame channel, so this lands **after WI-708** — the dependency is explicit.

### §9 Universes, declined

`fact Eq[T = Type]` already uses `Type` as an instance argument, so
`Type : Type` holds de facto. SLD resolution is first-order over terms — no
impredicative comprehension exists to build a paradox from — so this proposal
records the fact, declares universe stratification out of scope, and moves on.

## Reflect interface consolidation (review items for work item (d))

- One canonical "is this a type" face: today `term_as_sort` (decoder),
  `can_be_sort` (predicate), and `extract → TypeExtractor.Error` (total
  classifier) answer the same question three ways; keep `extract` +
  `term_as_sort`, retire `can_be_sort` into a one-line rule or drop it.
- Document the §8 conventions on the interface itself (doc comments on
  `is_modifiable` / `facts_of` / `term_as_entity` citing this proposal).
- Add `type_value[T]` (post-WI-708).
- The "qualified name not accepted in binding-value position" wart noted in
  the `Type` instance facts' comment — re-examine once the cluster moves,
  since the move changes which short names resolve as siblings.

## Out of scope

- Instance-claim ↔ `provides` unification (§6) — own proposal.
- Lattice-aware / semantic matching of type terms in fact queries (§7) —
  door noted.
- Const-folding reflect calls in compile-only profiles (§5) — proposal 039
  channel, after v1.
- The WI-708 fix itself — tracked separately; `type_value[T]` waits on it.

## Work items (to file on acceptance)

- **(a)** Move the `Type` cluster to `anthill.reflect`
  (`reflect/type.anthill`): stdlib move + engine qualified-name updates
  (`typing.rs` ×5, `load.rs` bootstrap, ~66 cluster references) + golden/test
  sweep + scaland mirror resync. Self-contained, commit-first increment.
- **(b)** Profile fence: specified early check in cpp-gen (and rust-gen where
  applicable) — reflect sort in a value-carrying position of a
  compiled operation, or a reflect-builtin call in its body, is a loud
  per-profile error; supersedes the incidental missing-`TypeMapping` failure
  for this class.
- **(c)** Denotation completion (§2): bare and applied type expressions
  denote outside `Type`-expecting positions too (error→accepted; the
  `expected resolved name, got unresolved` diagnostic replaced by ordinary
  sort mismatches that name the denoted sort). The smoke-found unhinted
  positions are the checklist: unconstrained generic slots, operation
  bodies under a declared `-> Type`, unannotated `let`, dot receivers,
  list-literal elements, row-valued arguments (restoring their lost span);
  declared-field
  type-check for landed `Type` values on paths 3 and 4 (`Type` fits, `Term`
  tolerated as the raw-term substrate, anything else loud); WI-603 inference
  for undeclared heads; instance claims exempt by the depth gate.
- **(d)** Reflect interface consolidation (§8 + the consolidation list),
  including `type_value[T]` gated on WI-708.
- **(e)** Kernel spec (`docs/kernel-language.md`): new §4 "Type expressions
  in term positions" subsection carrying the §2 denotation rule + gates, the
  §4 no-dereference sentence, and the §5 profile regimes; §5 fact section
  gets the instance-claim depth-gate note.
- **(f)** (small, severable) The `-> T [Meta]` swallow (§2 grammar
  recheck): a targeted diagnostic when a bare-name return type's bracket
  application fails the WI-709 check — point at the existing `meta [...]`
  clause (WI-087) — and a kernel-spec note that the postfix position
  belongs to application; the `meta` clause is the operation-meta surface.

## Alternatives considered

- **Forbid + reification marker**
  (`is_modifiable(type_value[Cell[V = Int64]])`; Mercury `type_desc` style):
  runtime type reflection on supported hosts is a goal of this design, so
  the marker was never going to remove runtime type values — the only
  question it decides is whether the *written* crossing is spelled out.
  Rejected on that question: the marker converts nothing (a `Type` value
  already IS the term, WI-361 — where Mercury's `type_desc` genuinely
  bridges two distinct representations); it taxes the designed idiom at
  every reflect call site (`facts_of(kb(), WorkItem)`,
  `is_modifiable(Cell)` — the WI-206 acceptance forms, and the WI-632
  by-reference direction); and the visibility it buys is partial anyway —
  a binding received from a query
  (`rule r(?t) :- type_of(occ: ?, type: ?t)`) carries no marker, and such
  bindings are most of reflection's crossings. What "Type is compile-time"
  legitimately wants is delivered tax-free by §4 and §5. The marker's one
  good part — explicitly reifying a generic body's own type parameter —
  survives as §8's `type_value[T]`.
- **Expectation-gated bare names** (an intermediate draft of this §2:
  applied forms denote anywhere, bare sort names only where the position
  expects `Type`): dropped for uniformity — `List` is the same type
  expression as `List[T = Int64]` with the parameter unbound, construction
  always carries parentheses so a bare name has no competing constructor
  reading, and the traded diagnostic only changes flavor (`UnresolvedName`
  → `expected String, got Type`). Its one legitimate concern — a
  forgotten-args constructor name flowing into a `Type`-accepting position —
  survives as a diagnostics requirement on work item (c), not as a language
  rule.
- **Keep `Type` in prelude + a codegen special case**: rejected — profile
  availability should follow the namespace (§3); reflect is where `Type`'s
  peers live, and the import line is the dependency signal.
- **`fact Modifiable[…]` → `provides`**: deferred, not rejected — real
  overlap, separate concern (§6).

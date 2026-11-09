# 060: Clause-level type declarations compile to generated body goals

**Canonical reference:** [`kernel-language.md` §5.3](../kernel-language.md#53-rule).
The reference records the delivered `require[X]` subset, the directional-rewrite
typed patterns and the typed relational heads (WI-742).

## Status: Draft (2026-08-07). The **language** half of the requirement channel (WI-1040) and of typed relational heads (WI-742). Mechanics — goal encoding, crossings, σ-carrier — are owned by [`../design/requirement-channel.md`](../design/requirement-channel.md); this proposal owns the surface and its rules. The staging invariant is assumed throughout: after the typing pass, run time performs no typing operations (channel doc §2.1).

## Relates to: 058 (§3.3 bracket selection, §3.4 named slots, §3.8 conditional provisions, §3.10 instances are never chosen at run time), 052 (relation column types — the consumer of typed heads), 043 / WI-582 (typed patterns on `@[simp]` heads), WI-300 (the delivered `requires(X)` guard tier), [`../design/constrained-term-substrate.md`](../design/constrained-term-substrate.md) (the desugaring `head(…) :- conforms(typeof(?x), T), body` — meaning this proposal turns into code), 055 (types in value position).

## The rule

> **A type-level declaration written in a rule clause compiles, at typing time, into a
> generated goal in the clause body. At run time the generated goal only reads the
> CARRIED TYPE of a value (`value_type_term`, WI-578) and the `provides`/sort-ops
> tables built at load. It performs no typing operations — no inference, no type
> unification, no instance selection.**

All selection happens in the typing pass; run time reads the value's carried type
— a stored term, nothing is computed or collapsed — and selects from the
load-built tables with it (the head constructor picks the entry, the type
arguments flow to the sub-dictionary fetches). Even a typed head's conformance test
is such a read: sort relations are facts, so conformance at a ground carried
type is lookup over stored relations, not derivation.

Replaced in part by 073 §6.2 (2026-11-09): a requirement no caller passes is refused at
load, not fetched from the carried type.

Three instances, one mechanism:

| written | generated body goal | does |
|---|---|---|
| `requires(X)` — delivered (WI-300) | `find_dictionary(…)`, check-only | **guard**: the clause fires only where X resolves |
| `require[X]` — WI-1040 | `find_dictionary(…, out: ?d)` | guard + **bind**: X's dictionary is in clause scope; covered calls dispatch through it |
| `?x: T` on a relational head — WI-742 | a type test before the body, `SortDomain[T].fill(?x)` after it (§2.3) | guard + **column type** (052's declared column, true by construction) + **generator** where `T` has values to list (§2.2) |

The generated goal is ordinary: it delays on unbound operands, wakes by rotation,
participates in the body like any goal. The engine sees one more goal, never a type
(constrained-term-substrate's M1, satisfied by construction).

## 1. `require[X]` — a dictionary into clause scope

Three spellings, three distinct things, no overload:

```anthill
sort S requires Eq[T] … end                       -- DECLARES a slot (unchanged)

p(?x, ?y) :- requires(Eq[T]), eq(?x, ?y)          -- guard only (delivered)
p(?x, ?y) :- require[Eq[T]], eq(?x, ?y)           -- in scope; eq dispatches through it
p(?x, ?y) :- ?d = require[Eq[T]], f(?x, ?d)       -- named; passed by hand
```

- **No grammar change.** `require[X]` already parses (WI-311 unified application);
  what is added is an interpretation. The **converter owns the name**, as it owns
  `requires` / `unify` / `eq`: both legal spellings are rewritten away there, so a
  kernel-vocabulary entry would be reached only by an illegal one — where it would
  turn a loud error into a name that resolves to nothing and then fails silently.
- **The output variable is the translation's, not the surface's.** For a bare
  `require[X]` the translation synthesizes a fresh output variable and weaves the
  covered calls to dispatch through it; the author names one (`?d = require[X]`)
  only to pass it by hand. A bare `require[X]` nothing consumes degenerates to
  the check-only guard — `out`'s presence in the lowered goal is a translation
  decision (is anything consuming this dictionary?), never a surface obligation.
- **Position is restricted**: a bare body goal, or the RHS of a top-level `=`.
  Nested deeper in a term it is refused loudly — no general lifting.
- **Requirements stay on the right of `:-`.** In a head, `require[X]` would *assert*
  the requirement rather than demand it — refused.
- The bracket names the spec instance being asked for — the input side, exactly
  058 §3.3's `f[Spec = W](…)`. The output `?d` is an ordinary logical variable,
  **not** a type parameter (058 §3.10's rule stands: a value never fills a named slot).

## 2. `?x: T` on a relational head — the WI-742 answer

The WI-582 restriction (`?x: T` only on `@[simp]`/`@[unfold]` heads) is enforcement
coverage, not semantics. Lifted by this rule: on a relational head the annotation
compiles to a type test prepended to the body and the fill of `T`'s `SortDomain`
appended after it (§2.3) — the head itself stays structurally bare, so the
discrimination tree indexes it identically. The fill is called by name for a sort
with no parameters, through the dictionary a ground type builds for a parameterised
one, and through a requirement read — which a citation fills — for a type variable.

**Admission dependency (C666A, delivered 2026-08-24).** An unguarded predicate head
is now refused when it reaches a declared predicate only through a whole-scope
non-enclosing edge (`requires`, conversion-style `provides`, or wildcard import).
That is the unsafe half of this proposal's typeclass-method shape. WI-742 must recognize
the generated type test tied to the contributing carrier and admit that guarded join
at C666A's check; the unguarded refusal remains.

Mode-directed, three-valued, never NAF-decided (WI-067):

| `?x` at the read | outcome |
|---|---|
| bound, carried type conforms to T — and, where T's `SortDomain` has cases, the fill holds (§2.2) | hold — keep the binding |
| bound, refuted | fail this binding (the schema is true by construction) |
| bound, under-determined | suspend |
| unbound, T's `SortDomain` has cases (§2.2) | **enumerate** — a choice point over T's values |
| unbound, T a primitive (its fill is the waiting type check, §2.3) | delay + rotate; re-asked when a later goal binds it |
| still unbound at the end | flounder **loudly** (WI-737 route), never a silent non-check |

052's `relation_clause_columns` already reads the bound first — the typing half is
wired; this gives it the loader path. An **untagged equational** head keeps today's
loud rejection (no body to prepend to, no wakeup site).

### 2.1 The parameter form — no sigil in the defined-predicate head

In the head of the predicate a rule **defines**, `name: Type` introduces a typed
clause variable — no `?`:

```anthill
rule adult(p: Person, age: Int) :- person(p), age_of(p, age), gte(age, 18)
-- ≡ rule adult(?p: Person, ?age: Int) :- person(?p), age_of(?p, ?age), gte(?age, 18)
```

This is the notation the language already uses at its other declaration site:
`operation f(a: Int, b: Int) = a + b` introduces `a`, `b` sigil-free and the body
references them bare. 052 says a rule *is* such an operation (stream-valued, its
head declaring column names and types), so the head parameter list is the same
form, not a new convention. The schema `adult : Relation[(p: Person, age: Int)]`
is then written where it holds.

How it lands, in four steps:

1. **Parsing — unchanged.** `p: Person` already parses as a `named_arg`
   (`grammar.js:1309`). An interpretation, not a production (the 060 pattern).
2. **Classification — by resolved category, never by case.** The loader resolves
   the head functor (WI-896): the rule's own defined predicate → each
   `name: Type` is a typed variable introduction; an **entity-constructor** head
   → named args stay named args (`fact palette(c: red())` untouched — and note
   entities are commonly lowercase, so spelling can never be the discriminator).
   The classification is asked at every head that has one, not only a relational
   clause's head atom: an EQUATION's LHS and a BODY-LESS head reach it too, so
   the two spellings agree on firing and on refusal alike (WI-20260910-7NBZX).
3. **Scope — bare body references, loud typos.** The introduced names are
   clause-scoped, referenced bare like operation parameters; a body typo is an
   unresolved-name error, never a silent fresh variable. Clause-scoped means per
   RULE: a multi-head rule's heads share one body, so one parameter name is one
   variable across all of them (WI-20260909-C7ANM).
4. **Compilation — identical to §2.** Head structurally bare (indexed as today),
   the type test and the fill of §2 generated, bounds read by
   `relation_clause_columns`. A parameter is a **column in the position it is
   written**, so the two spellings agree on order as well as meaning and may be
   interleaved (`rule g(x: Red, ?d)` vs `rule g(?d, x: Red)`). `Term::Fn` files a
   call's arguments into a positional list and a named list, which loses that
   interleaving; the parse store carries the written order across the split
   (WI-20260909-C7ANM).

Bounds of the form:

- **Only the defined-predicate head.** In every other position `name: Type`
  stays a named argument — a sort is a legal argument *value* (055), so
  `f(kind: Int)` passes the type `Int` as data and must keep meaning that.
- **The annotation is the introduction marker.** Untyped bare `p(x, y)` stays a
  loud unresolved-name error — an unresolved bare name is never an implicit
  variable (a typo would become a fresh variable that silently never fails, and
  a rule's meaning would flip when a matching name is later defined).
- **`?` remains** for body-local existentials and untyped variables.
- **Measured** (2026-08-07, textual scan of stdlib/examples/anthill-todo): every
  named-arg `fact`/`rule` head on a lowercase functor in the corpus is an entity
  constructor (`palette`, `parent`) — the reclassified population is empty. The
  loader-verified re-measurement belongs at implementation, at the
  classification site.

### 2.2 The generator arm — a typed head lists its type's values

A typed head is a generator where its type has values to list: the fill (§2.3)
enumerates them when `?x` is unbound and checks membership when it is bound. The
author writes no domain expression — they write a sort, and the loader derives its
`SortDomain` provision (§2.3). A domain wanted as a value is a typed rule cited by
name:

```anthill
sort Colour { entity red  entity green  entity blue }

rule colours(?x: Colour) :- true
colours.takeN(5)          -- 3 rows, every one definite
```

This section was first written over a type-keyed goal, `domain_member(?x, T)`, and a
value face `<Sort>.domain`; §2.3 retired both (2026-09-25, 2026-11-02). The rules
below are the ones that stayed:

- **Derived for any closed ADT**, not only an all-nullary one. A sort with a
  recursive constructor has a fair, lazy, infinite domain: `takeN` is fine, a full
  drain does not return — finiteness decides only whether the stream ENDS. The order
  that makes it fair is §2.3's two rules.
- **Domain-defining, not a generator hint.** Where `T` has cases, both modes read
  them: mode (in) checks conformance and membership, mode (out) enumerates. A mode
  split — generate from a subset but accept anything conforming — would make the
  relation's answers depend on call mode, and is refused. For a derived domain
  membership is conformance, so the common case costs nothing extra.
- **Rule-local narrowing stays an ordinary body goal.** A sort's domain is the sort's
  everywhere; "this rule's `x` ranges over a subset" is written as a goal.
- **A sort that defines its own domain** provides `SortDomain`'s `fill` (§2.3's decided
  item). Not built: today a 1-ary relation `domain(?x)` written in the sort's body is
  read as it, its clauses are not generated from, and a parameterised sort's written
  one is refused.
- **An unwritten parameter is a rule-scoped type variable.** `?x: List` means
  `?x: List[T = ?t]`, recursively and once per occurrence (§8.1's unwritten-slot
  expansion on the rule side); the variable rides the rule's frame and opens fresh per
  firing, so two citations of one rule are two instantiations.
- **A free type is read off the value, not guessed.** With `?x` bound, the value fixes
  its own type (WI-578) and the fill runs at it. With `?x` unbound and the type still
  free, the goal delays and residualizes: there is no one domain to range over, and
  listing every type's would enumerate types.

### 2.3 The domain through the requirement channel — `SortDomain` (WI-20260911-5G28A; designed 2026-09-25)

For a caller's RIGID `X` the type is a name, not a domain, so the domain reaches the clause as a
DICTIONARY, handed in by the citation's caller
([`060-typedomains-implementation.md`](../design/060-typedomains-implementation.md); the build plan
in [`060-implementation.md`](../design/060-implementation.md) §7.3). The dictionary is
`SortDomain`'s:

```anthill
namespace anthill.reflect
  sort SortDomain
    sort T = ?
    provides Fillable[T = T]       -- proposal 067
  end
end
```

- **`SortDomain provides Fillable`** (user, 2026-09-25). `Fillable` is the interface
  ([proposal 067](067-fillable.md)): one rule, `fill(?x)`, which fills `?x` with a value of `T`.
  `SortDomain` is the implementation the loader derives for every sort with constructors, and its
  `fill` IS the sort's domain — what a typed head generates from, and checks against.
- **ONE MECHANISM.** The type-keyed goals this proposal first wrote — `domain(?x, T)` and the
  derived `domain_member(?x, T)` — were built for a type the rule can NAME; `SortDomain` covers
  that case too, so they retired into it rather than stand beside it (060-implementation §7.3, "`SortDomain`
  is the ONLY domain mechanism").

**What a typed head means** (user, 2026-09-25):

```anthill
rule p(?x: T) :- body      ≡      rule p(?x) :- body, SortDomain[T].fill(?x)
```

`SortDomain[T]` is the clause's REQUIREMENT — filled by a citation's caller (S2's channel), or
resolved at the call from what the values pin. The goal goes AFTER the body: a generator ahead of
it enumerates a recursive type forever before the body can prune it — WI-743 measured `word(?w)
:- domain(?w, List[T = Letter]), ?w <=> [?, ?, ?]` not terminating, and the twin with the goal
last answering 27 and stopping.

**Derived per entity.** Each entity has a one-case `SortDomain`, and a sort's is their `combine`
(067 §2):

```
SortDomain[List] = combine(SortDomain[List.nil], SortDomain[List.cons])
```

An entity's case unifies `?x` with the constructor over fresh fields, then fills each field — so
for `List`:

```anthill
List provides SortDomain[T = List[T = T]] :- SortDomain[T = T]      -- derived
  rule fill(?x) :- ?x <=> nil()
                 | ( ?x <=> cons(head: ?h, tail: ?t),
                     fill(?t),                                      -- the tail first
                     SortDomain[T].fill(?h) )                       -- then the head, through its SortDomain
```

**Per field.** Each field's type decides how it is filled and what the provision requires:

| field's type | example | filled by | the provision |
|---|---|---|---|
| the sort itself | `cons`'s `tail: List` | `fill` — the recursion | requires nothing |
| a type parameter | `cons`'s `head: T` | the parameter's `SortDomain` | is CONDITIONAL on it (058 §3.8) |
| a concrete type | `box(c: Colour, n: Int64)` | that type's `Fillable` | holds only if it has one |

So `SortDomain[E]` holds when every field of every entity of `E` can be filled — per FIELD, not per
type parameter. (S3a's rows put one condition on each parameter, so a parameter no field uses —
`SortedSet`'s `O` — was required anyway, a concrete field — `Box`'s `Colour` — never checked, and a
sort whose field cannot be filled — `Delay`'s arrow — got a row it could not honour.) A member of a
conditional provision reads its condition (066); at run time the condition is a sub-dictionary of
the dictionary `fill` was reached through (067 §3).

**The order is semantic — two rules.** `fill` recurses, so it can have infinitely many answers, and
the order of its alternatives decides what is ever reached. WI-743 measured both:
1. **Inside a case, the recursive fields first** — `fill(?t)` before `SortDomain[T].fill(?h)`. Head
   first, a free list descends one spine forever: for `Letter = {a, b}`, `fill(?h)` picks `a` and
   `fill(?t)` then enumerates `[a]`, `[a, a]`, … and never backtracks to `b`. Tail first, the lists
   come out by length: `[]`, `[a]`, `[b]`, `[a, a]`, `[b, a]`, …
2. **The cases with no recursive field first** — `nil` before `cons`: `combine` is ordered
   concatenation (067 §2), and an infinite first operand starves the second.

Fair for ONE recursive field per case, and no further: a tree's `node(l: Tree, r: Tree)` descends
depth-first in the later one — the limit WI-743 pinned; interleaving is WI-20260911-09E6M's.

**A primitive has no cases.** EVERY TYPE HAS A `SortDomain` (user, 2026-09-25, deciding between
this paragraph's first wording — "`Int64` provides `Fillable`, not a `SortDomain`" — and the rest
of this section, which fills a parameter through its `SortDomain` and reads a typed head as
`SortDomain[T].fill`: together they left `List[T = Int64]` and `?x: String` unfillable). A
primitive's `SortDomain` is not DERIVED — it has no constructors — and its `fill` is the waiting type
check: it leaves the variable free with its check waiting, so `List[T = Int64]` fills to skeletons —
`[]` definitely, then `[?a]`, conditional until something binds `?a`, which is what the type-keyed
goal answered before. A hand-written `Fillable` (067 §4's builder) is a `Fillable` and not a
`SortDomain`, so it is accepted where `Fillable` itself is required.

**The loader applies `combine` when deriving:** a sort's `fill` is emitted as the disjunction of its
entities' cases, so `SortDomain[List.cons]` — a nested entity as a TYPE ARGUMENT, which is new
(kernel-language §6.3 makes a nested entity a constructor of its sort, not a sort) — is notation for
the derivation's parts, and nothing at run time needs it.

**Open — both since decided:**
- ~~`<Sort>.domain`, the value face a citation reads (WI-20260911-WT8WG) — the name it keeps for
  `SortDomain`'s `fill` at that sort.~~ **DECIDED (user, 2026-11-02): `<Sort>.domain` is
  SUPERSEDED by `SortDomain[T].fill` and keeps no name as a surface.** It names a SORT, so it
  reaches only a type written at the citation; an abstract `T` — a caller's rigid `X`, a sort's
  parameter — has no name to hang it on, and a value cannot stand in for one: a value carries no
  type, and the one computed from it names only what its constructors name (`[]` is
  `List[T = ?t]`). So the typed head is the surface, and a domain wanted as a value is a typed
  rule cited by name (`rule colours(?x: Colour) :- true`, then `colours.takeN(5)`) — which also
  reaches the domain of a type variable (`rule el(?x: T) :- true` in `sort Wrap[T]`, cited as
  `Wrap[T = X].el` under `requires SortDomain[T = X]`). A sort that defines its own domain
  provides `SortDomain`'s `fill` — `S provides SortDomain[T = S]` with `rule fill(?x) :- …`, the
  form printed above for the derived case — in place of a `domain(?x)` written in its body.
  The per-sort relation stays only as the internal target a `SortDomain` dictionary lands on.
  A hand-written `Fillable` is untouched: it is not a `SortDomain`, and is for fills other than a
  type's domain (067). Retiring the surface is WI-20260911-WT8WG
  ([`060-implementation.md`](../design/060-implementation.md) §7.3, "`<Sort>.domain` is
  superseded").
- ~~A condition that cannot be resolved yet.~~ **DECIDED (user, 2026-09-25): a value whose type
  does not name its element is a `List[?]`, and a condition is resolved when `fill` READS it — a
  read WAITS while its type is unpinned.** `rule elNil(1) :- Wrap.el([])` calls `el(?x: T)` —
  `el(?x) :- SortDomain[T].fill(?x)` — from a rule body, so no citation hands the requirement in,
  and `[]` pins `T` as `List[?]`. The requirement `SortDomain[List[?]]` is `List`'s provision; its
  condition `SortDomain[?]` is resolved only when `fill` reads it. For `[]` it never does —
  `List`'s `fill` takes its `nil` case: `1`, definitely, where `861b3013` answers undecided
  (MEASURED). Where an element exists, the read waits until something pins its type — by the
  delay that makes `Int64`'s check wait on its variable — so the waiting goal carries the tie
  between the type and the value:

  ```anthill
  rule same(?a: T, ?b: T) :- true          -- in sort Wrap[T]
  rule q(?h) :- Wrap.same([?h], [red()])
  ```

  `?a = [?h]`'s element check waits; `?b` pins the element type to `Colour`; the check resumes,
  and `q` answers `red`, `green`. Resolving `SortDomain[?]` to the `Fillable` of ANY value instead —
  this decision's first reading — answers `?h` free and definite, which is wrong: `?b` makes the
  element a `Colour`. (On `861b3013` `q` answers nothing — S3a's `[red()]` defect — MEASURED.) A
  value-dependent TYPE, `List[Unknown[?h]]`, is the type-system form of the same tie
  (WI-20260910-6ARRN), and not a prerequisite. What the resolver owes: `SortDomain[?]` is never
  resolved by a search among providers — the requirement machinery's wildcard rule
  (WI-20260830-X9PB4, `sort_goal_with_wildcards`) matches every candidate and would come back
  ambiguous — and a dictionary holding a condition not yet read is not ground, which
  `dictionary.rs` and WI-860's unification check assume it is.

## 3. The annotation is an ANCHOR — dictionaries and constraints come up together

The two instances meet: a generated goal both **constrains** and **anchors**.

- Every generated `find_dictionary` needs an anchor that grounds the spec's
  parameters at run time — a projection source for the carried types. The
  delivered guard tier admits one anchor: a covered body call (the witness).
- `?x: T` on the head is the second anchor: its type test reads `?x`'s carried
  type, so `T` is grounded by projection from the head argument — and any
  `require[Spec[T]]` in the clause compiles against it.

```anthill
-- T anchored by the head annotation; no witness call needed
p(?x: T, ?y) :- ?d = require[Eq[T]], f(?x, ?y, ?d)
```

So for a spec-constrained `T`, the annotation's generated goals bring up **both**
the constraint (conformance) and the dictionaries (the requirement channel) — one
declaration, one compilation rule, two reads at run time.

**The anchor rule (loud, not silent):** a `require[X]` with *no* anchor — no covered
body call and no typed binding of X's parameters — has nothing to project from and
is **refused at typing** (the guard tier's "cannot be grounded" error, extended),
never left to delay forever.

## 4. Determinism

Instances are never chosen at run time (058 §3.10). The generated goal **fetches**
from the load-built tables what the typing pass selected — narrowing is by one-way
match (only provider variables bind), overlap is refused at typing/load, and a
runtime tie is a defect, not a semantics. A supplied `?d` and a unique local row must **agree** (WI-860):
disagreement is a loud error; a supplied dictionary decides only where the local
row cannot (`Unresolvable`/`Ambiguous`, WI-855 — the 058 §3.3 named-instance case).

## 5. Non-goals

- The dictionary never becomes a head argument (rule arity, indexing, 052 citation).
- No instance *selection* surface in rule bodies (058 §3.3).
- No change to sort/operation-level `requires` declarations or 058 §3.4 named slots.
- The `@[simp]`-tagged equational path (WI-582 match-time bounds) is unchanged.

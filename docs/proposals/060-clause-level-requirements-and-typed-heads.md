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
  drain does not return — finiteness decides only whether the stream ENDS. It is
  generated by size, in rounds, which is what makes it fair; §2.3's two rules order
  the members of one size (WI-20260911-09E6M).
- **Domain-defining, not a generator hint.** Where `T` has cases, both modes read
  them: mode (in) checks conformance and membership, mode (out) enumerates. A mode
  split — generate from a subset but accept anything conforming — would make the
  relation's answers depend on call mode, and is refused. For a derived domain
  membership is conformance, and mode (in) is a CHECK, not a generation: a bound value
  selects the one clause its constructor heads (§2.3, "The head decides the mode"), so no
  case is proposed to it and refuted.
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

An entity's case is ONE CLAUSE: the constructor over fresh fields in its HEAD, and a body that
fills each field — so for `List`:

```anthill
List provides SortDomain[T = List[T = T]] :- SortDomain[T = T]      -- derived
  rule fill(nil)
  rule fill(cons(head: ?h, tail: ?t)) :- fill(?t),                  -- the tail first
                                         SortDomain[T].fill(?h)     -- then the head, through its SortDomain
```

**The head decides the mode** (user, 2026-11-15, WI-20261115-YR3N7). A bound value selects the one
clause whose head its constructor matches, so mode (in) is a check: no case is proposed and
refuted, and none is left to try. An unbound `?x` matches every head, in clause order, so mode
(out) generates — in the order the two rules below give. Nothing else picks the mode: it is how a
goal selects clauses, the index over clause heads. The shape first derived put the cases in ONE
clause's body, `fill(?x) :- ?x <=> nil() | (?x <=> cons(head: ?h, tail: ?t), …)`, which proposes
each constructor to `?x` in turn and so generates even where it checks: MEASURED 2026-11-15, a list
of `Product(id: Int64, price: Int64)` checked through a typed column cost 16 resolution steps per
element and left an untried case per element on the search; the same domain written one clause per
constructor cost 6, and generated the same lists in the same order.

**The dictionary names whose `fill` runs — the value never does** (067 §3). Every fill call runs
the member of the provision its dictionary names, and every sub-domain below that dictionary comes
out of its slots: a recursive field is handed the same dictionary, a field typed by a parameter the
condition's slot, a value of a refining sort a dictionary for its own sort put together from those
slots. A type builds a dictionary only at the top, where no caller hands one — never below one, so
a sub-domain a caller handed for a rigid type is never replaced by the one its type would name:
inside `countAt[X]` below, the asked type is a rigid `X`, a name, and only the dictionary knows its
domain. A relation reached by a sort's name — `<Sort>.domain`, cited or written in the sort's body —
could do none of this: it takes no requirements, so it cannot receive a caller's sub-domain, which
is why it is superseded (the decided item below). **A value of a refining sort** (kernel-language
§8.2) is a case of the DERIVED domain it refines, and the call applies that case: where the
dictionary's `impl` is a derived domain and the value's constructor is not one of that sort's own,
the call runs the `fill` of the value's own sort with a dictionary put together from the handed
one's slots — so `other(7)` under `sort Other requires Base` is filled at `Other` wherever `Base`'s
dictionary is handed, rigid or not, with the sub-domains it carries. A hand-written or primitive
`impl` has no such case: its own clauses decide.
The case is the call's because no clause can hold it: as an indexed clause (`Base.fill(other(n:
?n)) :- …`) its head would match an unbound `?x` and list the refining sorts' values, and with a
variable head it would be tried, and refuted, beside every value of `Base`'s own.

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

**How `fill` is threaded — a rigid variable.** The rigid is the reason `SortDomain` reaches a clause
as a dictionary at all (060-implementation §7.3, "Why the instance must be THREADED — the RIGID
type variable"). The fixture of `wi_5g28a_sort_domain_test` and `wi_shed7_fillable_test`:

```anthill
sort Colour
  entity red
  entity green
  entity blue
end
sort Wrap[T]
  entity wrap(v: T)
  rule el(?x: T) :- true
end
operation countAt[X]() -> Int64 effects {Error} requires SortDomain[T = X] =
  Wrap[T = X].el.takeN(9).length()
operation colours() -> Int64 effects {Error} = countAt[X = Colour]()              -- 3
operation wrapped() -> Int64 effects {Error} = countAt[X = Wrap[T = Colour]]()    -- 3
```

Inside `countAt`, `X` is RIGID: the body is typed once for every instantiation, so no type in it
names `X`'s domain. Only `countAt`'s caller knows `X`, and it hands the domain in as the dictionary
its `requires` slot holds. What the typer compiles and the loader derives, written with the
dictionaries visible — `?d` and `?self` are a clause's dictionary reads, never head arguments
(060-implementation §7.3, "THE HEAD-ARGUMENT ALTERNATIVE STAYS REJECTED"):

```
Wrap.el(?x) :- __domain_guard(?x, T),                                  -- §2's type test, in front
               apply_domain(?d, ?x, T),                                 -- the fill, through ?d
               find_dictionary(SortDomain, SortDomain, ?x, out: ?d)     -- el's IMPLICIT PARAMETER

Colour.fill(red)                                                        -- derived: a clause per constructor
Colour.fill(green)
Colour.fill(blue)
Wrap.fill(wrap(v: ?v)) :- find_dictionary(SortDomain, SortDomain, wrap(v: ?v), out: ?self),
                          apply_domain(__domain_sub(?self, k), ?v)      -- the element: ?self's condition k
```

`k` is the condition's slot in the dictionary's layout, after `SortDomain`'s own chain
(060-implementation §7.3, "DELIVERED 2026-09-25").

`colours()`:
1. The call `countAt[X = Colour]()` knows the instance, so it builds `countAt`'s slot from the
   provisions: `D_Colour = Dictionary(…, impl: Colour)`. A domain involves no choice — a sort has
   one — so the type determines it.
2. In `countAt`'s body the citation `Wrap[T = X].el` can build nothing for the rigid `X`. The typer
   ROUTES `el`'s read `?d` to `countAt`'s slot, and evaluating the citation hands `D_Colour` in with
   the relation value.
3. Opening `el`'s clause binds `?d = D_Colour`. `?x` is unbound, so the guard waits, and
   `apply_domain` lowers through `D_Colour`'s `impl` to `Colour.fill(?x)`.
4. An unbound `?x` matches all three heads, in clause order — `red`, `green`, `blue`: GENERATION.
   Each binding wakes the guard, which checks it. Three rows.

`wrapped()`:
1. The call builds `D = Dictionary(…, D_Colour, impl: Wrap)`: `Wrap`'s provision is conditional on
   its element's `SortDomain`, so `Colour`'s dictionary is `D`'s condition.
2. The same route hands `D` in; opening `el` binds `?d = D`, and `apply_domain` lowers to
   `Wrap.fill(?x)`, handing `D` on to that clause's read.
3. An unbound `?x` matches `Wrap.fill(wrap(v: ?v))`, whose read binds `?self = D`. The element's
   call `apply_domain(__domain_sub(D, k), ?v)` takes `D_Colour` out of `D` and lowers to
   `Colour.fill(?v)`: `wrap(red)`, `wrap(green)`, `wrap(blue)`.

A BOUND value takes the same path, and the heads make it a CHECK. In `operation hasAt[X](v: X) ->
Int64 effects {Error} requires SortDomain[T = X] = Wrap[T = X].el(v).takeN(1).length()`, called as
`hasAt[X = Wrap[T = Colour]](wrap(v: red))`, the same `D` is handed in and `?x` is bound when `el`
opens: the guard reads `T` off the value and holds; `apply_domain(D, wrap(v: red), T)` lowers to
`Wrap.fill(wrap(v: red))`, which selects the one clause `Wrap.fill(wrap(v: ?v))`; the element's call
lowers to `Colour.fill(red)`, which selects the clause `Colour.fill(red)` and no other. No case is
proposed and refuted, and none is left to try. Called as `hasAt[X = Base](other(7))` under `sort
Other requires Base`, the handed dictionary is `Base`'s, a derived domain, and `other` is not one of
`Base`'s constructors, so the call fills `other(7)` at `Other`, at the instance `Base`'s dictionary
describes.

Through every step `X` stays a name: no step reads `X`'s type to choose a `fill`. The dictionary
chooses, the clause heads decide check or generate, and the dictionary goes down the value — whole
to a recursive field (`List`'s `fill(?t)` is `apply_domain(?self, ?t)`), and as a sub-dictionary to
a field typed by a parameter. Built so (WI-20261115-YR3N7): `colours()` and `wrapped()` answer 3, and
the bound rows answer 1 — `hasAt[X = Wrap[T = Colour]](wrap(v: red))`, `hasAt[X = Base](other(7))`,
and `hasAt[X = Wide[W = Colour]](narrow2(q: green))` under `requires Wide[W = Q]`, whose `Q` meets
the `Colour` dictionary the caller handed (`wi_yr3n7_domain_check_test`). The derived relation is
the internal `<Sort>.__fill`; `<Sort>.domain`, while it lasts (WT8WG), is a clause of its own that
hands its dictionary to it — a citation builds its query from its relation's first clause head, and
takes no constructor there. Every fill call dispatches through `apply_domain`, which costs no depth
and no fuel, and an unbound value is tried against the heads in clause order (WI-20260911-SXZ3G:
the index kept no order before).

**Generation is by SIZE; the order is the order inside one size** (WI-20260911-09E6M). `fill`
recurses, so it can have infinitely many answers, and a depth-first search over its alternatives
decides what is ever reached. WI-743 bought fairness with two ordering rules, below, and they make
ONE recursive field per case fair and no more: `node(l: Tree, r: Tree)` descended depth-first in the
later field, `l` stayed `leaf`, and `node(node(leaf, leaf), leaf)` was never reached — no order of
clauses makes a product of two infinite streams fair. So the resolver generates in ROUNDS: an
`apply_domain` outside any round becomes a choice point whose k-th alternative asks the fill with a
budget of k cases with fields, and admits a branch only where it spent all k; a nullary case, a
primitive's waiting check, a tuple and a bound part cost nothing, and every fill below the first
spends the same budget, so the fields of one case, the components of a tuple, the holes of a bound
value and a clause's adjacent typed columns share one round (a fill that waits, its type unpinned,
generates after the round, unfairly against it). The stream ends after a round that cut no member short. Nothing of the
derivation changes — one clause per constructor, the constructor in the head (YR3N7's shape): the
budget is branch state of the search, read only where a case with fields opens over an unbound
value, so a bound value is checked as before, in round 0.

The two rules are no longer needed for fairness, and stand as the order of the members of one size:
1. **Inside a case, the recursive fields first** — `fill(?t)` before `SortDomain[T].fill(?h)`. Tail
   first, the lists of one length come out `[a, a]`, `[b, a]`, `[c, a]`, `[a, b]`, …; head first,
   `[a, a]`, `[a, b]`, …. (Before rounds this rule was what kept a free list fair: head first, a free
   list descended one spine forever.)
2. **The cases with no recursive field first** — `nil` before `cons`, and `one(c: Bit)` before
   `more(next: Seq)` when both are of one size. (Before rounds: `combine` is ordered concatenation,
   067 §2, and an infinite first operand starved the second.)

So `List[T = Letter]` comes out exactly as it did — `[]`, `[a]`, `[b]`, `[c]`, `[a, a]`, `[b, a]`, … —
since a tail-first depth-first search over a list already came out by length, and a free `Tree` comes
out 1, 1, 2, 5, 14 trees of 0 … 4 nodes, each once (`wi_09e6m_fair_domain_test`).

**A primitive has no cases.** EVERY TYPE HAS A `SortDomain` (user, 2026-09-25, deciding between
this paragraph's first wording — "`Int64` provides `Fillable`, not a `SortDomain`" — and the rest
of this section, which fills a parameter through its `SortDomain` and reads a typed head as
`SortDomain[T].fill`: together they left `List[T = Int64]` and `?x: String` unfillable). A
primitive's `SortDomain` is not DERIVED — it has no constructors — and its `fill` is the waiting type
check: it leaves the variable free with its check waiting, so `List[T = Int64]` fills to skeletons —
`[]` definitely, then `[?a]`, conditional until something binds `?a`, which is what the type-keyed
goal answered before. A primitive whose values are finitely many LITERALS — `Bool` — has a derived
case per literal, `fill(true)` and `fill(false)`, not a hand-written domain (WI-20260911-5TK6B; not
built). A hand-written `Fillable` (067 §4's builder) is a `Fillable` and not a
`SortDomain`, so it is accepted where `Fillable` itself is required.

**The loader applies `combine` when deriving:** a sort's `fill` is emitted as its entities' cases,
one clause each, in `combine`'s order, so `SortDomain[List.cons]` — a nested entity as a TYPE ARGUMENT, which is new
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
  provides `SortDomain`'s `fill` — `S provides SortDomain[T = S]` with one `rule fill(<case>) :-
  …` per case, its case in the head, the form printed above for the derived case — in place of a
  `domain(?x)` written in its body.
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

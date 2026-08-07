# 060: Clause-level type declarations compile to generated body goals

## Status: Draft (2026-08-07). The **language** half of the requirement channel (WI-1040) and of typed relational heads (WI-742). Mechanics — goal encoding, crossings, σ-carrier — are owned by [`../design/requirement-channel.md`](../design/requirement-channel.md); this proposal owns the surface and its rules. The staging invariant is assumed throughout: after the typing pass, run time performs no typing operations (channel doc §2.1).

## Relates to: 058 (§3.3 bracket selection, §3.4 named slots, §3.8 conditional provisions, §3.10 instances are never chosen at run time), 052 (relation column types — the consumer of typed heads), 043 / WI-582 (typed patterns on `[simp]` heads), WI-300 (the delivered `requires(X)` guard tier), [`../design/constrained-term-substrate.md`](../design/constrained-term-substrate.md) (the desugaring `head(…) :- conforms(typeof(?x), T), body` — meaning this proposal turns into code), 055 (types in value position).

## The rule

> **A type-level declaration written in a rule clause compiles, at typing time, into a
> generated goal in the clause body. At run time the generated goal only reads the
> CARRIED TYPE of a value (`value_type_term`, WI-578) and the `provides`/sort-ops
> tables built at load. It performs no typing operations — no inference, no type
> unification, no instance selection.**

All selection happens in the typing pass; run time reads the value's carried type
— a stored term, nothing is computed or collapsed — and selects from the
load-built tables with it (the head constructor picks the entry, the type
arguments flow to the sub-dictionary fetches). Even `domain`'s conformance test
is such a read: sort relations are facts, so conformance at a ground carried
type is lookup over stored relations, not derivation.

Three instances, one mechanism:

| written | generated body goal | does |
|---|---|---|
| `requires(X)` — delivered (WI-300) | `find_dictionary(…)`, check-only | **guard**: the clause fires only where X resolves |
| `require[X]` — WI-1040 | `find_dictionary(…, out: ?d)` | guard + **bind**: X's dictionary is in clause scope; covered calls dispatch through it |
| `?x: T` on a relational head — WI-742 | `domain(?x, T)` | guard + **column type** (052's declared column, true by construction) + **generator** where T defines its domain (§2.2, WI-743) |

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

The WI-582 restriction (`?x: T` only on `[simp]`/`[unfold]` heads) is enforcement
coverage, not semantics. Lifted by this rule: on a relational head the annotation
compiles to a prepended `domain(?x, T)` goal — the head itself stays structurally
bare, so the discrimination tree indexes it identically.

Mode-directed, three-valued, never NAF-decided (WI-067):

| `?x` at the read | outcome |
|---|---|
| bound, carried type conforms to T — and, where T defines its `domain`, membership holds (§2.2) | hold — keep the binding |
| bound, refuted | fail this binding (the schema is true by construction) |
| bound, under-determined | suspend |
| unbound, T defines its `domain` (§2.2) | **enumerate** — a choice point over T's domain |
| unbound otherwise | delay + rotate; re-asked when a later goal binds it |
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
3. **Scope — bare body references, loud typos.** The introduced names are
   clause-scoped, referenced bare like operation parameters; a body typo is an
   unresolved-name error, never a silent fresh variable.
4. **Compilation — identical to §2.** Head structurally bare (indexed as today),
   `domain(?p, Person)`-style generated goals, bounds read by
   `relation_clause_columns`.

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

### 2.2 A sort defines its `domain` — the generator arm (WI-743)

Mode (out) does not special-case enums in the resolver: `domain(?x, T)`
dispatches to a **member relation T defines, named `domain`** — the goal is that
member read through the type, which is why they share the name.

- **Derived for an all-nullary closed ADT** (the WI-743 finiteness gate): the
  loader derives `domain(red())`, `domain(green())`, `domain(blue())` from
  `sort Colour`'s variants — declaration order, once each. The 058 §3.9 move
  (derive a row from structure), applied to values.
- **User-definable for any sort** — a hand-written `domain` makes any sort a
  generator. Today's wrapper pattern (`sort Palette` + three `palette(c: …)`
  facts) *is* a hand-written `domain` the language gave no name; this absorbs it
  into the sort.
- **Domain-defining, not a generator hint.** Where T defines its `domain`,
  *both* modes read it: mode (in) checks conformance **and** membership, mode
  (out) enumerates. A mode split — generate from the subset but accept anything
  conforming — would make the relation's answers depend on call mode, and is
  refused. For the derived enum case membership ≡ conformance, so the common
  case costs nothing extra.
- **Rule-local narrowing stays an ordinary body goal.** A sort-level `domain` is
  the sort's domain everywhere; "this rule's `x` ranges over a subset" is
  written as a goal, as today.
- **A sort with no `domain`** keeps §2's behavior unchanged: delay, re-ask on
  binding, flounder loudly at the end — `rule f(?x: String) :- eq(?x, "abe")`
  stays legal and yields its one row.
- **Abstract T dispatches through the requirement channel** (§3's anchor;
  WI-1040); a concrete T is pinned at typing. No tension with 058 §3.10:
  `domain` enumerates **values** by ordinary SLD choice — an instance is never
  chosen.

The payoff, with §2.1's parameter form — map-colouring with no `Palette` sort
and no domain facts:

```anthill
rule colouring(wa: Colour, nt: Colour, sa: Colour, q: Colour, nsw: Colour, v: Colour)
  :- wa != nt, wa != sa, nt != sa, nt != q,
     sa != q,  sa != nsw, sa != v, q != nsw, nsw != v
```

## 3. The annotation is an ANCHOR — dictionaries and constraints come up together

The two instances meet: a generated goal both **constrains** and **anchors**.

- Every generated `find_dictionary` needs an anchor that grounds the spec's
  parameters at run time — a projection source for the carried types. The
  delivered guard tier admits one anchor: a covered body call (the witness).
- `?x: T` on the head is the second anchor: `domain(?x, T)` reads `?x`'s carried
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
- The `[simp]`-tagged equational path (WI-582 match-time bounds) is unchanged.

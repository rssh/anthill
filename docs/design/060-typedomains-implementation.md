# 060 type domains — the domain as a runtime value, through the requirement channel

**STATUS: EXPLORATORY.** No ticket owns this, nothing is scheduled, and nothing here is
built. It is a direction, written down because it dissolves a problem
[`060-implementation.md` §7.3](./060-implementation.md) can only work around, and because
two of the three things it appears to need turn out to already exist.

Companion to [proposal 060](../proposals/060-clause-level-requirements-and-typed-heads.md)
and to [`requirement-channel.md`](./requirement-channel.md), which owns the dictionary
mechanics this reuses wholesale.

## 0. The idea

A sort's domain becomes a **value obtained at resolution time through the requirement
channel**, instead of a relation named at compile time. Declare

```anthill
sort anthill.reflect.SortDomain
  sort T = ?
  rule member(?x: T) :- true          -- the BOUND is the whole content
end
```

**It is a RELATION and not an operation, and the difference is the point.** An operation is
a function: `member(red())` could answer `Bool`, but `member(?x)` with `?x` unbound is not a
call — there is nothing to compute from. A domain is needed in exactly the opposite
direction: `?x` FREE must *enumerate*. Only a relation has that mode, and it is the mode
`domain_member(?x, Colour)` already runs in.

**And `:- true` is not a placeholder.** It is the shape `<Sort>.domain` is already derived
with — `emit_domain_value_face` builds `domain(?x) :- true` and installs the bound
`x: <Self>`, and the typing sweep then appends the member goal that makes it answer
(060-implementation §7.1). Here the bound is `T`, the spec's own parameter, so the one
clause is every sort's domain at once, with the dictionary saying which.

MEASURED 2026-09-12, the three spellings, with the `provides` block written inside
`sort Colour`:

| written in the spec | verdict |
|---|---|
| `rule member(?x)` — untyped declaration | loads clean, 0 clauses (061: a declaration stores none) |
| `rule member(?x: T)` — typed declaration | **REFUSED**: *"the declaration reading, where the annotation is the column's type with nothing to enforce it, is undelivered"* |
| `rule member(?x: T) :- true` — typed clause | loads clean, 1 clause |

So a spec may carry this, and the spelling that works is the one the codebase already
derives. The refused middle row is a real gap and is recorded in §6.

A typed head then compiles to a clause that *fetches* its domain and then *runs* it:

```
rule p(?x: A) :- g

  ⇒   p(?x) :- require[SortDomain[A]] = ?xd,     -- fetch the domain for A
                apply_domain(?xd, ?x),            -- run it on ?x
                g
```

`?xd` is bound during resolution, from the dictionary the caller threaded — so `A` is
whatever the caller actually instantiated, never a compile-time stand-in.

## 1. Why — the problem §7.3 works around

§7.3 threads the citation's type beside the goal and resolves it through
`Frame::type_args` at evaluation. That is correct, and it is a *repair*: the type still
has to be carried from the typer's pin, through eval, to the resolver, with a rule
(“a rigid is left off the channel, eval fills it from the frame”) that exists only because
the typer pinned a rigid in the first place.

The rigid arises because **a type mentioned in a clause is resolved by the pass that types
the clause**. Inside

```anthill
operation g[T]() -> Int64 = List[T = T].domain.takeN(5).length()
```

nothing the typer can write down is the answer; the answer is at `g[Colour]()`. Every
design that resolves the type statically must therefore carry a stand-in and arrange for
someone downstream to replace it.

**A dictionary never has this problem**, and that is the whole argument for this direction.
`find_dictionary` runs *in the resolver*, against the σ of the firing, so the provider it
selects is the one the caller actually supplied. There is no stand-in to replace because
nothing was decided early. The domain becomes the same kind of thing as `Eq`: not a name
the compiler resolves, but evidence the caller supplies.

## 2. What already exists — measured, with sites

Three of the four pieces are in the tree.

| piece | site | state |
|---|---|---|
| **a clause fetching evidence at resolution time** | `require[Eq[T]]` lowers in `parse/convert.rs:3376` to `find_dictionary(Eq, out: ?d)`; the typing sweep rewrites it (`typing.rs record_find_dictionary_grounding`); the resolver reads it at `resolve.rs builtin_find_dictionary` | **delivered** (WI-1040, §1 of 060-implementation) |
| **minting a fresh variable from a domain, in a kernel operation** | `execute.rs`'s `sort_query` arm: it calls `self.fresh_var(...)` and builds `is_entity_of(?_sq, Sort)` as a goal, with the fresh name lexically scoped to the call | **exists** |
| **a goal that accepts an unbound variable and generates** | `domain_member(?x, T)` in mode (out) — §7's whole subject. `?x` unbound is the generating mode, not an error | **delivered** (WI-743) |
| **a runtime-computed goal list pushed as a candidate** | `Candidate::Continuation(body)` — the bounded-quantifier path builds one goal list per element from a value only known at run time, then pushes them as candidates | **exists** |

So both things §0's sketch was unsure about are already done somewhere: **fresh variables
are already minted from a domain by a kernel lowering**, and **a relation applied to an
unbound variable is already the ordinary generating mode.**

## 3. The piece that does not exist — and why it need not be a var-headed goal

Written literally, `?xd(?x)` is a goal whose **functor is a variable**. The resolver
dispatches on `goal.head(kb).functor_sym()`, which answers `None` for a variable head, so
that spelling reaches no clause.

**It does not have to be that spelling.** Make the variable an ARGUMENT of a kernel
relation with a determinate functor:

```
apply_domain(?xd, ?x)
```

a builtin that reads `?xd`'s bound value, lowers it to goals, and pushes them —
`Candidate::Continuation`, the path the bounded quantifier already takes. This is the
ordinary way a metacall is added to a first-order resolver, and it keeps every existing
invariant: one functor, one discrimination key, one arity.

**And the value it reads already has a lowering.** A `Value::Relation { query, columns }`
carries a reified `LogicalQuery`, and `KnowledgeBase::lower_query` turns one into a goal
list — it is the single lowerer shared by `execute_logical_query` and the guard engine. So
`apply_domain` is a small builtin over machinery that exists, not a new engine.

## 4. What the transform would be

```
rule p(?x: A) :- g
  ⇒ p(?x) :- find_dictionary(SortDomain, out: ?xd), apply_domain(?xd, ?x), g
```

with three properties worth stating:

- **It is the same sweep 060 already owns.** §1 established that a typing-pass sweep may
  rewrite a clause body wholesale (`set_rule_body_nodes`), that it runs after
  `type_rule_bodies`, and that a generated goal is an ordinary goal. §2's
  `domain(?x, T)` goal is generated by exactly that sweep today; this replaces what it
  generates, not where.
- **Mode (out) still generates.** With `?x` unbound, `apply_domain` runs the fetched
  domain as a generator — the behaviour `domain_member(?x, T)` has now, with the type
  supplied by evidence instead of by a term.
- **The `[T]`-polymorphic case is the point.** In `g[T]()`, `SortDomain[T]`'s dictionary
  is whatever `g[Colour]()` threaded; there is no rigid anywhere in the clause.

## 5. What it depends on

**The op→rule dictionary channel**, `channel §10 item 3`, owner **WI-20260909-NAR1X**,
status *settled, not built* (`060-implementation.md` §0 and §8.10). A rule reached from an
operation body must receive the caller's dictionary, or `find_dictionary` in the generated
body has nothing to find. This direction is blocked on it, and that is not a detail: it is
the single largest reason this is exploratory rather than a plan.

## 6. What is NOT known

Written as questions, because none of them was measured.

- **The TYPED DECLARATION is refused, and this direction may want it.** §0's measurement:
  `rule member(?x: T)` with no body is refused because "a typed column has exactly one
  enforcer, a rewrite's typed-pattern bound, or — on a relational CLAUSE — the generated
  `domain(?x, T)` goal prepended to its body; a DECLARATION is neither … The declaration
  reading, where the annotation is the column's type with nothing to enforce it, is
  undelivered." `:- true` sidesteps it, and whether sidestepping is right — whether the
  spec should DECLARE a shape providers fill, or CARRY the one clause they parameterise —
  is the first thing to settle, not a detail of spelling.
- **Who provides it.** `provides SortDomain[T = Colour]` would have to be derived for every
  sort that derives a domain (`derive_domain_member_clauses`'s population), the way
  `<Sort>.domain` is derived in §7.1. Measured: the block loads when written inside the
  provider sort's own declaration, and is refused at namespace level ("a `provides` clause
  needs a type at its address"). That is mechanical, but it multiplies the provides facts
  by the number of domain-bearing sorts, and the dispatch cost was not measured.
- **Whether a dictionary can carry a relation at all.** A dictionary is documented as
  *immutable, acyclic and — after typing — GROUND* (`dictionary.rs`), an `(impl symbol,
  ordered children)` tree. That is satisfied by an impl SYMBOL naming the derived domain
  relation; it is not satisfied by a closure. So the dictionary should carry the name and
  `apply_domain` should reach the clauses through it — but this was not checked against
  `Dictionary::from_value`'s whole-tree validation.
- **Termination and cost.** Every typed head gains two goals instead of one, and one of
  them is a dictionary search. §7's measurements are all against a single generated goal.
- **What happens to `domain_member`.** Either it stays as the thing `apply_domain` reaches,
  or it is subsumed. The first is much more likely and much cheaper; nothing here argues
  the second.

## 7. Relation to §7.3

**Not a replacement, and not a competitor to schedule against.** §7.3 closes a silent
acceptance that ships today — `Wrap[T = Colour].dom` and bare `Wrap.dom` are
indistinguishable, and a bracketed citation floats to a flounder at the drain. That is a
defect with users; this is a direction.

If this direction is taken, §7.3's typer work (pinning the bracket per citation) stays —
the bracket still has to be read and validated — and what changes is where the pinned type
GOES: into a dictionary the caller threads, rather than beside the goal to be resolved from
the frame. The right order is therefore §7.3 first, this after NAR1X, with §7.3's
frame-reading step as the thing that would be retired.

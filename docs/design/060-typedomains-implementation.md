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
  rule member(?x)                     -- 061: DECLARES, defines nothing
end

-- derived per domain-bearing sort, inside that sort's own declaration
sort Colour
  entity red  entity green  entity blue
  provides SortDomain[T = Colour]
    rule member(?x) :- anthill.kernel.domain_member(?x, Colour)
  end
end
```

**It is a RELATION and not an operation, and the difference is the point.** An operation is
a function: `member(red())` could answer `Bool`, but `member(?x)` with `?x` unbound is not a
call — there is nothing to compute from. A domain is needed in exactly the opposite
direction: `?x` FREE must *enumerate*. Only a relation has that mode, and it is the mode
`domain_member(?x, Colour)` already runs in.

**THE SPEC'S `member` MUST NOT CARRY A BOUND, and that is a soundness rule rather than a
spelling preference.** The tempting spelling is `rule member(?x: T) :- true` — the shape
`<Sort>.domain` is already derived with (`emit_domain_value_face` builds `domain(?x) :-
true` and installs the bound `x: <Self>`; 060-implementation §7.1), and with `T` the spec's
own parameter it reads as "every sort's domain at once, with the dictionary saying which".
**It is self-recursive.** The typing sweep appends the member goal to every BOUND clause, so
that spelling expands to

```
member(?x) :- domain(?x, T), domain_member(?x, T)
```

which makes `member` itself a typed head — and §4's transform rewrites every typed head's
generated goal into `find_dictionary` + `apply_domain`, this one included. `member` would
fetch a `SortDomain` and apply it, which runs `member`. **The mechanism's definition would
go through the mechanism.**

So `member` is DECLARED untyped in the spec and DEFINED by each provider against the kernel
primitive, which is where the recursion bottoms out: `domain_member(?x, Colour)` reaches
`Colour`'s derived structural clause and nothing fetches a dictionary. This is the
bootstrap rule every such scheme needs, stated once — *the domain of the domain mechanism is
the kernel relation, not another fetch* — and it is the reason the sketch in §0 of the first
draft (`rule member(?x: T) :- true`) is wrong.

MEASURED 2026-09-12, the three spellings, with the `provides` block written inside
`sort Colour`:

| written in the spec | verdict |
|---|---|
| `rule member(?x)` — untyped declaration | loads clean, 0 clauses (061: a declaration stores none) — **the one this design uses** |
| `rule member(?x: T)` — typed declaration | **REFUSED**: *"the declaration reading, where the annotation is the column's type with nothing to enforce it, is undelivered"* |
| `rule member(?x: T) :- true` — typed clause | loads clean, 1 clause — and is the self-recursive one above |

The refused middle row is what the untyped declaration gives up: the spec states no column
type, so nothing checks that a provider's `member` ranges over its own `T`. That is recorded
in §6.

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

a builtin that reads `?xd`'s bound value and pushes the goals it selects —
`Candidate::Continuation`, the path the bounded quantifier already takes for a goal list it
only knows at run time. This is the ordinary way a metacall is added to a first-order
resolver, and it keeps every existing invariant: one functor, one discrimination key, one
arity.

**What it does with `?xd` is DISPATCH, not lowering.** An early draft had it read a
`Value::Relation` and run `KnowledgeBase::lower_query` over the reified `LogicalQuery`. That
is wrong for the case this exists for — see §4.1: the callee's own clause has
sub-requirements, and a lowered goal list carries no channel to satisfy them. `apply_domain`
must instead activate the `member` clauses of `?xd.impl_sort()` **with `?xd` installed as
that activation's `__req_self`**, so the callee's `require[SortDomain[T]]` projects `sub(0)`
exactly as `expand_dispatching_dict` makes it project at an operation dispatch. It is the
SLD-side twin of `dispatch_apply_with_requirements`, which is why §5's dependency is not
merely an enabler but the same mechanism.

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

## 4.1 The `List[X]` example — why any of this exists

A sort with no parameters needs none of this. `Colour.domain` is three constructors and a
compile-time name reaches it. **The whole reason for the machinery is that `List[Colour]`
and `List[Int64]` have DIFFERENT domains while sharing ONE clause**, and that the sharing
has to survive being written inside a polymorphic caller.

Today's derived clause carries the type as an ARGUMENT (060-implementation §7,
`derive_domain_member_clauses`):

```
domain_member(?x, List[T = ?T])
  :- ?x <=> nil()
   | (?x <=> cons(head: ?h, tail: ?t) & domain_member(?t, List[T = ?T])
                                      & domain_member(?h, ?T))
```

The same clause with the type carried as EVIDENCE instead:

```anthill
sort List
  sort T = ?
  entity nil
  entity cons(head: T, tail: List)

  provides SortDomain[T = List[T = T]]
    requires SortDomain[T]                      -- the ELEMENT's domain: one sub-dictionary
    rule member(?x)
      :- ?x <=> nil()
       | ( ?x <=> cons(head: ?y, tail: ?z),
           member(?z),                          -- the TAIL: this same relation, __req_self
           require[SortDomain[T]] = ?ed,        -- the ELEMENT's domain, a SUB-dictionary
           apply_domain(?ed, ?y) )
  end
end
```

**THE DICTIONARY TREE IS THE TYPE TREE.** That is the sentence the whole direction rests on.
A dictionary is `Dictionary(sub₀ … subₙ₋₁, impl: S)` (`dictionary.rs`), so the evidence for
`SortDomain[List[Colour]]` is

```
Dictionary( Dictionary(impl: Colour),   impl: List )
            └─ the element's domain ─┘
```

— and `require[SortDomain[T]]` inside the clause is exactly `dict.sub(0)`, the projection
`expand_dispatching_dict` already performs along a `proj_path`. **Nothing new is invented for
nesting**: `List[List[Colour]]` is one more level of a tree the channel already builds,
projects and validates.

**AND THIS IS WHY THE DICTIONARY IS LOAD-BEARING AND ITS IMPL SYMBOL IS NOT ENOUGH.** It is
tempting to have `apply_domain` take only `?ed.impl_sort()` — the name of the provider — and
look its clauses up. That works for `Colour` and fails for every case the direction exists
for: running `List`'s `member` requires THAT clause's own `require[SortDomain[T]]` to
resolve, and the only thing in the system that says `T = Colour` is `sub(0)` of the
dictionary handed in. Keep the root and drop the tree, and `List[Colour]` and `List[Int64]`
are the same call. **The components' types live in the subtree, so the subtree is what must
cross.**

`provides SortDomain[T = List[T = T]] requires SortDomain[T]` is a CONDITIONAL provision, and
the channel is already built for the unbounded family that implies — `dictionary.rs`, on why
dictionaries are not interned: *"a conditional provision composes over type arguments, so the
distinct-dictionary family follows the carried types that actually occur (no static bound),
while interned terms live for the KB's lifetime."* `List[List[Colour]]` needing a dictionary
no one wrote down is the case that sentence was written for.

**THE TWO RECURSIONS ARE DIFFERENT, and §0's defect is only one of them.**

| | what recurses | base case | verdict |
|---|---|---|---|
| the TAIL, `member(?z)` above | the relation calls itself on a structurally smaller argument | `?x <=> nil()` | **fine** — the ordinary recursion `derive_domain_member_clauses` already emits |
| §0's `rule member(?x: T) :- true` | the relation's own BOUND is enforced by the mechanism that runs the relation | none | **the defect** — the mechanism defined through itself |

They look alike and are not: one is a recursive *definition*, the other a circular
*justification*.

**THE GOAL ORDER IS SEMANTIC, not style.** `derive_domain_member_clauses` states two rules
and this clause must obey both: base constructors first (`nil` ahead of `cons`), and inside a
branch **recursive positions first** — `tail` before `head` — so a free `?x` comes out by
length (`[]`, `[a]`, `[b]`, `[a, a]`, …) instead of descending one spine forever. Hence
`member(?z)` standing before `apply_domain(?ed, ?y)` above. The same limit carries over
too: fair for ONE recursive position per constructor, and `node(l: Tree, r: Tree)` still is
not.

**AND THIS IS WHERE THE RIGID PROBLEM IS ACTUALLY SOLVED.** Write the caller polymorphically:

```anthill
operation g[X]() -> Int64 = List[T = X].domain.takeN(5).length()
```

Under any scheme that resolves the type when the clause is typed, `X` is `g`'s rigid: the
element goal has no constructors to enumerate, and the query delays. Under this one, the
typer resolves nothing — `g[Colour]()` threads `Dictionary(Dictionary(impl: Colour), impl:
List)`, the clause projects `sub(0)` for its element domain, and the generator yields `[]`,
`[red]`, `[green]`, `[blue]`, `[red, red]`, … The parameter never had to be guessed, so it
never had to be a rigid.

## 5. What it depends on

**The op→rule dictionary channel**, `channel §10 item 3`, owner **WI-20260909-NAR1X**,
status *settled, not built* (`060-implementation.md` §0 and §8.10). A rule reached from an
operation body must receive the caller's dictionary, or `find_dictionary` in the generated
body has nothing to find. This direction is blocked on it, and that is not a detail: it is
the single largest reason this is exploratory rather than a plan.

## 6. What is NOT known

Written as questions, because none of them was measured.

- **The spec cannot state what `member` ranges over — KNOWN, and it appears to cost
  nothing.** Kept here so it is not rediscovered as a blocker. The argument of a relational
  head is a COLUMN (WI-714) and a column takes its TYPE from the `?x: T` bound written on
  that head, which is how the derived `<Sort>.domain` gets `x: <Self>`. §0's `rule
  member(?x)` carries no bound, so the spec says only *"there is a relation `member` of one
  argument"*; and neither spelling that would say more is available — `rule member(?x: T)`
  is refused ("the declaration reading, where the annotation is the column's type with
  nothing to enforce it, is **undelivered**") and `rule member(?x: T) :- true` is §0's
  self-recursive one. **Nothing reads that type, which is why it costs nothing.** At run
  time there is no declared type to read: a `Value` carries none, and a value's sort is
  RECOVERED from its constructor (`value_type_term`, WI-578 — the read
  `pin_bound_from_value` already makes). In the transform, `?x` is typed from `p`'s OWN
  bound `A` in `p(?x: A)`, never from `member`'s column; `apply_domain` is a resolver
  builtin and by then everything is `Value`. What the missing type would buy is a STATIC
  check that a provider ranges over its own `T` — MEASURED 2026-09-12: under `provides
  SortDomain[T = Colour]`, a provider defining `member(?x) :- domain_member(?x, Letter)`
  loads clean, exactly as the right one does — and every provider here is derived, so a
  hand-written wrong one is not on the path. It becomes a real question only if providers
  are ever written by hand.
- **Who provides it.** `provides SortDomain[T = Colour]` would have to be derived for every
  sort that derives a domain (`derive_domain_member_clauses`'s population), the way
  `<Sort>.domain` is derived in §7.1. Measured: the block loads when written inside the
  provider sort's own declaration, and is refused at namespace level ("a `provides` clause
  needs a type at its address"). That is mechanical, but it multiplies the provides facts
  by the number of domain-bearing sorts, and the dispatch cost was not measured.
- **Whether the bootstrap really is structural.** With `member` declared untyped it carries
  no bound, so the sweep generates nothing for it and §4's transform never reaches it; and a
  provider's hand-written `domain_member(?x, Colour)` is not a generated goal either, so it
  is not rewritten. That means NO exclusion list — the recursion bottoms out by shape rather
  than by a special case, which is the property worth keeping. It was reasoned from the
  sweep's population (bound clauses only), not driven, because the transform does not exist.
- **Whether a dictionary can carry a relation at all.** A dictionary is documented as
  *immutable, acyclic and — after typing — GROUND* (`dictionary.rs`), an `(impl symbol,
  ordered children)` tree. §4.1 relies on that being satisfied by an impl SYMBOL naming the
  provider, with `apply_domain` reaching the clauses through it — never by a closure, which
  would not be ground. Not checked against `Dictionary::from_value`'s whole-tree validation.
- **How `apply_domain` installs the dictionary on a RULE activation.** It must (§3, §4.1 —
  the impl symbol alone loses the components' types), and a rule activation has no
  requirement channel today: `ResolverFrame` is documented as lacking exactly that, while
  `Frame::requirements` is the operation frame's. So the channel NAR1X adds is the thing
  `apply_domain` writes into, and the two are one piece of work rather than a dependency and
  a consumer. Neither the shape of that channel nor where `apply_domain` would push it was
  worked out.
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

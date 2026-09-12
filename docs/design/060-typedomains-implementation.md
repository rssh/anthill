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
    rule member(?x, ?d)
      :- ?x <=> nil()
       | ( ?x <=> cons(head: ?y, tail: ?z),
           member(?z, ?d),                      -- the TAIL: same relation, same node
           ?ed <=> sub(?d, 0),                  -- the ELEMENT's, PROJECTED out of ?d
           apply_domain(?ed, ?y) )
  end
end
```

**THE DICTIONARY IS AN ARGUMENT AND IS READ BY PROJECTION — one of three reads in the tree,
and the choice is forced by head arity.** There are three ways to get at a requirement here,
and they are not interchangeable:

| read | mechanism | who uses it |
|---|---|---|
| NAMED SLOT | `expand_dispatching_dict` expands the dictionary at frame push into `__req_self` plus one slot per chain entry; the body reads a slot by name | the interpreter's OPERATION frame (`Frame::requirements`) |
| SEARCH | `find_dictionary(spec, op, args…)` DERIVES one from the arguments' carried types | `require[X]` in a rule body today (WI-1040) |
| PROJECTION | `sub(?d, 0)` off a dictionary already in hand | this clause |

Expansion is an OPTIMISATION of projection — `expand_dispatching_dict` projects `slots_for`
out of the dictionary to build the named slots, so the body need not. A rule cannot copy it:
expanding into slots means one head argument per chain entry, and a head's arity is fixed
while a requires chain's length is not. Carrying the ROOT and projecting at each use gives the
same information at arity one. And SEARCH cannot serve the generating mode at all: with `?x`
free there are no carried types to derive from, which is exactly what §5's entry gap is about.

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

## 4.2 Where the new logical variables come from

**Logically, nowhere new.** `apply_domain(?ed, ?y)` is an ordinary relation goal with an
output argument; binding `?y` is unification, which every relation in the system already
does. The provider's own `?y` / `?z` in §4.1 are ordinary clause variables — collected at
the assert, De Bruijn-closed with the head and body, opened fresh per firing by
`with_fresh_vars` — and so are the callee's when `apply_domain` activates the provider's
`member`. There is no "create a variable" primitive to invent.

**One MECHANICAL obligation, and it is about representation, not meaning.** §4's transform
writes `?xd` into a clause that is ALREADY ASSERTED, and an asserted rule's variables are De
Bruijn slots in a fixed frame. A variable the rewrite adds without growing that frame stays
a `Var::Global` shared by every firing of the rule — measured on this feature
(060-implementation §7.2): while a bound's type variable sat outside the frame, `rule
two(?a, ?b) :- my_rule([1, 2], ?a), my_rule(["s"], ?b)` answered NO SOLUTIONS, the first
call's `?t := Int64` refuting the second's.

Two ways out, each with an owner already in the tree:

1. **Mint it before the assert**, which is what `require[X]` does — `rewrite_require_goal`
   lowers it to `find_dictionary(Eq, out: ?<fresh>)` in the CONVERTER, so the variable is in
   the parse tree and is collected like any other body variable. No frame surgery. But the
   transform cannot live there: it keys on the head's BOUND, and at convert time `?x: A` is
   still a `typed_var` marker with `A` an unresolved name.
2. **Mint it in the typing sweep and grow the frame** — `extend_rule_frame_with_bounds`,
   added by 5G28A for `expand_rule_head_bound_type_params`, the other pass that mints
   post-assert. It PREPENDS: a De Bruijn index is `globals.len() - 1 - position`, so
   inserting at the front leaves every existing index where it was, and `arity` moves with
   `globals` so `with_fresh_vars` actually opens the new slot.

Placement 2 is the reachable one. One `?xd` PER TYPED COLUMN, not per clause — §4.4 measures
the case and says what ties them. Still open: `set_rule_body_nodes`'
constraint that fact-ness must not flip — so a body-less clause cannot be given a body this
way (§1, and §5's body-less boundary in 060-implementation).

**And `apply_domain` must not open clauses itself** — it selects the provider's `member` and
lets the ordinary activation open them, the `with_fresh_vars` path `step_choice_point`
already takes. Stated because the alternative is a second clause opener, and two openers is
how a frame invariant comes to hold in only one of them.

## 4.3 What a rule IS at run time, and what that makes `apply_domain`

**There is no `Value` variant for a rule.** The enum carries `OpRef { op, dict, … }` for an
operation and has **no rule twin**. A rule exists only as a `RuleId` — an index into
`kb.rules` — whose `RuleEntry` holds the head `Value`, `body_nodes: Vec<Rc<NodeOccurrence>>`,
`globals: Vec<VarId>`, `arity` and `type_bounds`. That is a KB structure, not a value, and
nothing can be bound to a variable.

**`Value::Relation` is NOT that thing.** Its own doc calls it "a rule cited by name as a
first-class, composable QUERY value": the payload is a `LogicalQuery` (a reified goal tree
built from one specific head) plus the columns it projects. A query, not a handle to
clauses — which is why §3 says `apply_domain` dispatches rather than lowering one.

**So what crosses is a `Value::SymbolRef`, and the dictionary already carries one.**
`Dictionary::build` writes `named: [(impl_key, Value::SymbolRef(impl_sort))]`. The provider
sort IS the handle, and resolving `<impl>.member` from it reaches the clauses:

MEASURED 2026-09-12, on §0's fixture —

| name | clauses |
|---|---|
| `SortDomain.member` — the spec's declaration | **0** (061: a declaration stores none) |
| `Colour.member` — written in `provides SortDomain[T = Colour]` | **1** |

A `provides`-block rule lands in the PROVIDER's scope, which is the same place a spec op's
implementation lands, so `apply_domain` finds its clauses by the route dispatch already uses.

**THE SYMBOL FINDS, THE TREE RUNS**, and that is the sharp form of §3's and §4.1's point.
Naming the clauses needs only `impl_sort()`; RUNNING them needs the whole dictionary,
because `List`'s own `member` reads `require[SortDomain[T]]` for its element and only
`sub(0)` holds it. Hence `apply_domain(?d, ?x)`:

1. resolve `<?d.impl_sort()>.member` — the symbol;
2. select its clauses and let the ORDINARY activation open them (`with_fresh_vars`, the
   `step_choice_point` path), so no second clause opener exists (§4.2);
3. install `?d` as that activation's `__req_self`, so the callee's own `require[…]` projects
   `sub(0)` exactly as `expand_dispatching_dict` makes it project at an operation dispatch.

Step 3 is the one with nowhere to write today — a `ResolverFrame` has no requirement
channel. It was expected to be the same work as NAR1X; MEASURED 2026-09-12, it is not.
NAR1X installed a dictionary in an EVAL frame (`expand_dispatching_dict`, entered through
`call_op_bridged`), and an eval frame is what an operation activation has. A rule activation
still has none, so `apply_domain` must take the other route this document already prefers —
the dictionary as a WRITTEN argument on the provider's `member` (§4.1, §5, and §6's last
bullet, which owns the census that route still needs).

**AND STEP 2 IS FORCED BY HOW THE ENGINE FINDS CLAUSES AT ALL.** A rule is not a path in the
discrimination tree: the tree INDEXES heads, its leaves are `RuleId`s, and a path is a
structural fingerprint of a head that several rules may share. The engine never holds a rule
— it holds a GOAL, and `kb.query_view(&goal_val)` walks the tree BY THE GOAL'S STRUCTURE to
produce the candidate list, each candidate then confirmed by unification ("the
discrimination-tree query *is* the unifier"). Selection is therefore goal-driven from end to
end, so `apply_domain` cannot carry a rule around: it must BUILD the goal
`<impl>.member(?x)` and let the ordinary lookup find the candidates. Two things come free
with that and would have to be rebuilt otherwise — the `GoalKey` query cache, and the Γ
overlay's own candidates (`gamma_candidates_for`).

## 4.4 More than one dictionary per clause — and what ties them

§4.1's `List` clause carries ONE dictionary because it has one receiver instance. A USER's
typed head does not. MEASURED 2026-09-12, this LOADS CLEAN today:

```anthill
rule p[A](?x: List, ?y: Leaf[A = A], ?z: Leaf[A = A]) :- Eq[A], eq(?y, ?z)
```

Three typed columns and a written guard, so the transform needs FOUR dictionaries:

| for | dictionary |
|---|---|
| `?x: List` | `SortDomain[List[T = ?t]]` |
| `?y: Leaf[A = A]` | `SortDomain[Leaf[A = ?a]]` |
| `?z: Leaf[A = A]` | the same one — same type |
| `:- Eq[A]` | `Eq[?a]` — the guard the author wrote, already WI-1040's business |

**THESE ARE INDEPENDENT ROOTS, not nodes of one tree**, which is what separates this from
§4.1. `sub` reaches from `SortDomain[Leaf[A]]` to `SortDomain[A]`; nothing reaches from it to
`Eq[A]`, or to `?x`'s. So a clause gets one fetched variable PER TYPED COLUMN plus the written
requires — answering §4.2's open question ("one `?xd` per clause or one per typed column") with
**per column**.

**AND WHAT CORRELATES THEM IS THE TYPE VARIABLE, which therefore does not go away.** `?y` and
`?z` must draw from the SAME domain and `Eq` must be at the SAME `A` — three facts about one
`A`. A dictionary cannot say that: `find_dictionary` derives each independently from the
arguments' carried types and CHECKS for agreement (WI-860: two derivations of one relation must
agree, disagreement is a loud failure), which is enforcement AFTER the fact and needs carried
types to derive from. In the GENERATING mode this direction exists for, `?y` is free and there
is nothing to carry.

So the fetch is keyed on the clause's own type variable and the tie is ordinary unification:

```
p(?x, ?y, ?z) :- find_dictionary(SortDomain, … Leaf[A = ?a] …, out: ?yd), apply_domain(?yd, ?y),
                 find_dictionary(SortDomain, … Leaf[A = ?a] …, out: ?zd), apply_domain(?zd, ?z),
                 …
```

with `?a` ONE σ variable, so pinning it once decides both fetches.

**CONSEQUENCE, AND IT IS THE STRUCTURAL POINT OF THIS SECTION: this direction sits ON TOP OF
WI-20260911-5G28A's DELIVERED HALF rather than replacing it.** That half made a bound's type
variable an ordinary clause variable — in the frame, De Bruijn-closed, opened fresh per firing
— and taught the resolver to read it off a bound value (`pin_bound_from_value`). That is
exactly the `?a` above. The dictionary does not replace the type machinery; it supplies a
DOMAIN for a type the type machinery has identified. What the dictionary replaces is only the
part that was going to be decided at TYPING time, which is where the rigid came from.

## 5. What it depends on

**THE RECURSION NEEDS NO CHANNEL — the dictionary rides as an ARGUMENT.** Stated first
because an earlier draft of this section argued the opposite and was wrong. `List[List[Colour]]`
has ONE dictionary — a TREE — and different activations hold different NODES of it, which σ
serves directly, exactly as `domain_member(?x, T)` carries the TYPE as an argument today:

```
SortDomain[List[List[Colour]]]  =  D_outer = Dictionary( D_mid,    impl: List )
                                   D_mid   = Dictionary( D_colour, impl: List )   -- = sub(D_outer, 0)
                                   D_colour= Dictionary(           impl: Colour ) -- = sub(D_mid, 0)
```

While the inner `List.member(?y, D_mid)` runs, the outer `List.member(?x, D_outer)` is still on
the stack — so two NODES are in play at once, each held by its own activation as an ordinary
argument. They are not two dictionaries needing two channels; they are one value being
projected as the search descends.

```
List.member(?x, ?d) :- ?x <=> nil()
                     | ( ?x <=> cons(head: ?y, tail: ?z),
                         member(?z, ?d),        -- the tail: the same dictionary
                         ?ed <=> sub(?d, 0),    -- the element's, projected out of it
                         apply_domain(?ed, ?y) )
```

Every dictionary is then a σ binding, and rule→rule dictionary passing ALREADY WORKS —
WI-1040's `a_clause_dictionary_crosses_a_rule_boundary_and_is_checked` drives a caller's `?d`
reaching the callee's `require[…]`. No `ResolverFrame` field, no inheritance rule, no per-push
clone. The dictionary is an ordinary value and needs no more than ordinary values get.

**WHAT IS MISSING IS THE ENTRY, and specifically the GENERATIVE one.** There are two eval→rule
edges:

| edge | site | owner |
|---|---|---|
| the GROUND closed test | `prove_rule_predicate_value` → `kb.prove_rule_predicate(pred, args)` — pred and args, nothing else, from a frame that HOLDS `frame.requirements` | **NOT A GAP** — measured 2026-09-12, see below |
| the GENERATIVE call | `build_relation_value` → `Value::Relation` → `execute_logical_query` | **nobody** |

**THE GROUND EDGE TURNED OUT NOT TO NEED A CHANNEL, and WI-20260909-NAR1X is the measurement.**
That ticket was filed on the reading in the first row — "the crossing DROPS THE SLOT" — and
building it showed the slot is not what is missing: a rule reached as a ground test DERIVES its
own dictionary from the ground operand (the WI-1040 witness / WI-20260909-QMFC5 anchor paths),
so the caller's `frame.requirements` has nothing to add. What failed was one goal LATER, at the
rule→op call, and it was fixed as an ARGUMENT — WI-1040's `Expr::ApplyWithin { requirements:
[?d] }` reaching the eval bridge, which expands it into the callee's frame. No `ResolverFrame`
field was added, which is the same verdict this section reaches above for the recursion.

NAR1X's own boundary rules the GENERATIVE row out in as many words: "`PredicateProof` is Proved /
Refuted / Undecided / Undefined — a CLOSED GROUND TEST. A generative `p(?out)` from an
operation body does not traverse this edge at all, so this ticket delivers the ground call …
NOT generative use." Enumerating a domain IS `member(?x)` with `?x` free, so this direction
still lives entirely on the edge NAR1X excludes, and that edge is still nobody's. It is a gap,
not an impossibility: `build_relation_value` takes `&mut self` and can reach the frame; nothing
reads `Frame::requirements` there today.
[`op-to-rule-requirement-channel.md`](./op-to-rule-requirement-channel.md) §5.1 is where it is
designed (capture in the `Value::Relation`, because a relation outlives the frame that built
it), and its §7 step 4 is what would build it.

## 6. What is NOT known

Written as questions, because none of them was measured.

- **`SortDomain.member` says nothing about what it ranges over, and NOTHING READS IT.**
  Recorded so it is not rediscovered as a blocker. At run time there is no declared type to
  read — a `Value` carries none, and a value's sort is RECOVERED from its constructor
  (`value_type_term`, WI-578, the read `pin_bound_from_value` already makes). In the
  transform, `?x` is typed from `p`'s OWN bound in `p(?x: A)`, never from `member`'s
  argument; `apply_domain` is a resolver builtin and by then everything is `Value`. The only
  thing the missing type would buy is a STATIC check that a provider ranges over its own `T`
  — MEASURED 2026-09-12: under `provides SortDomain[T = Colour]`, a provider defining
  `member(?x) :- domain_member(?x, Letter)` loads clean, exactly as the right one does — and
  every provider here is derived, so a hand-written wrong one is not on the path. It becomes
  a real question only if providers are ever written by hand. (§0 says why `member` cannot
  carry the type even if it wanted to.)
- **WHERE the derivation of `provides SortDomain[T = Colour]` stands — open, and the
  deciding constraint is that it must NAVIGATE TYPES.** The conditional provision for a
  parameterised sort (`provides SortDomain[T = List[T = T]] requires SortDomain[T]`) is not
  a name-level fact: emitting it means reading the sort's parameters and its constructors'
  field types, and deciding which of them recur. Several placements are possible and none
  is settled:

  | placement | what it buys / costs |
  |---|---|
  | a LOAD pass beside `kb/eq_derive.rs`'s `run` | the one existing pass that ASSERTS provisions (derived `NonEq` / `PartialEq` for Float composites), and `derive_domain_member_clauses` already has the constructor field types there. But it runs inside `type_check_sorts`, before the typer has said anything |
  | AFTER the typer | types are fully navigable, which is what the emission needs; but every load check that READS provisions has already run by then |
  | a NORMALIZATION pass after loading, derivations before typing | keeps the typer reading a KB that is already complete, at the cost of a new phase boundary |
  | SPLIT — declaration early, body late | the precedent exists and was FORCED: §7.1 mints `<Sort>.domain`'s NAME in pass 1 and builds its CLAUSE at the drain, because a citation is lowered during the item walk while the clause needs every file's sorts loaded |

  The split is the one with a worked precedent in this very feature, which is a reason to
  look at it first rather than an argument that it wins.

  **Three obligations follow the pass wherever it stands**, all documented at `eq_derive`'s
  call site: drop `provides_index` to `None` FIRST so reads during the loop see the facts
  being asserted, rebuild it after (`build_provides_index`) so the post-derivation checks and
  the persisted runtime index read a complete one, and invalidate the requires-chain cache
  (WI-1110 — `direct_requires` now reads provisions, so every pass asserting a
  `SortProvidesInfo` owes that call).

  MEASURED 2026-09-12: a `provides` block loads when written inside the provider sort's own
  declaration and is refused at namespace level ("a `provides` clause needs a type at its
  address"), so wherever the pass stands it must emit at the sort. And the derivation
  multiplies the provision facts by the number of domain-bearing sorts; the dispatch cost of
  that was not measured.
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
- **The GENERATIVE op→rule entry** (§5) — the largest unknown. `build_relation_value` builds
  a query carrying no dictionary, so a citation inside a polymorphic operation has nothing to
  hand the clause. It CAN reach the frame (`&mut self`); what to read, how to attribute it to
  a spec slot, and what a citation with no enclosing dictionary should do were not worked out.
- **Whether `member` carrying `?d` as an argument disturbs anything** (§5). It is a head-shape
  decision of the same kind the superseded hidden-slot design made for TYPES, and it inherits
  that design's questions — every arity reader, the discrimination key, the printer round trip
  — for the derived clauses only. Not censused.
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

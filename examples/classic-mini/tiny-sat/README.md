# Tiny SAT

Every satisfying assignment of a propositional formula, by generate-and-test
over the domain of assignments. The formula is
`(p ∨ ¬q) ∧ (q ∨ r) ∧ (¬p ∨ ¬r)`, and it has exactly two models.

## The encoding

**An assignment is a `List[Bit]`**, one cell per variable, so the domain is a
recursive type again — and it is the SAME derived domain as in
[`alphabet-words`](../alphabet-words/), over a different element sort. What the
loader derives from `sort Bit` and from the prelude's `List`:

```anthill
domain(?x, Bit)          :- ?x <=> t() | ?x <=> f()
domain(?x, List[T = ?T]) :- ?x <=> nil()
                          | (?x <=> cons(head: ?h, tail: ?t)
                               & domain(?t, List[T = ?T]) & domain(?h, ?T))
```

The `List` clause is not merely identical to the other example's — it IS the
other example's, one derived clause for the one `List` sort. That is what the
type travelling as an argument buys: `List[T = Bit]` and `List[T = Letter]`
reach one clause and differ only in what `?T` binds to.

**The formula is the test.** Negation is two facts; a two-literal clause is a
rule with two **exclusive** cases:

```anthill
fact neg(t(), f())
fact neg(f(), t())
rule or2(?a, ?)  :- ?a <=> t()
rule or2(?a, ?b) :- ?a <=> f(), ?b <=> t()
```

Exclusive matters. A plain `?a <=> t() | ?b <=> t()` is a choice point over
two tests, and an assignment that satisfies both literals would be counted
twice. With the cases exclusive every model is one row.

**The rule binds the spine first**, then tests, and the typed head's domain has
the last word on every cell:

```anthill
rule model(vs: List[T = Bit])
  :- vs <=> [?p, ?q, ?r],
     neg(?p, ?np), neg(?q, ?nq), neg(?r, ?nr),
     or2(?p, ?nq), or2(?q, ?r), or2(?np, ?nr)
```

`vs: List[T = Bit]` is the whole generator. The goal it produces is APPENDED,
after the written body — see `alphabet-words`, where that placement is the
difference between terminating and not.

## What this example used to work around

The bits were `yes` / `no` rather than `t` / `f`, because **an entity named `f`
used to take the identifier `f` away from every operation body in the load**:
the prelude's `List.foldLeft`, `Option.optionMap` and six of their neighbours
each apply a parameter named `f`, and their defining equations were lowered in a
scope where that parameter was invisible, so `f(x)` was read as an application
of the 0-field constructor. `sort Bit { entity t; entity f }` alone — in a file
with no operation of its own — refused the load with five copies of
`constructor 'f' given 1 positional argument(s)`, none of them locatable.

WI-20260911-073GH lowers an operation's defining equation in the operation's own
scope, and gives that lowering the `let` / `lambda` / `match` binder frames the
other one already had — so an applied name is the binder that introduced it,
whether that binder is a declared parameter or a local. The natural names are
back.

The same ticket closed the complementary case, where the name resolves to
nothing at all: an entity registers its field schema under its bare short name
too, and that bare name is what the loader falls back to for a name nothing in
scope answers — so an entity in a file you never imported could silently decide
what your term means. A written functor that resolves to nothing is no longer
read as an entity application.

The `domain` relation used to be hand-written here too, in exactly the shape
above; WI-743 derives it from the sort declarations and the explicit goal went
with it.

## Running

```bash
cd rustland && cargo build -p anthill-cli
./rustland/target/debug/anthill run examples/classic-mini/tiny-sat/
```

Prints `2`. The two models, as a query:

```bash
./rustland/target/debug/anthill query -p examples/classic-mini/tiny-sat \
  --max-results 0 'classic.sat.model(?vs)'
#   ?vs = [f, f, t]
#   ?vs = [t, t, f]
```

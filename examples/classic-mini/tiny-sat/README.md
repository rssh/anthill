# Tiny SAT

Every satisfying assignment of a propositional formula, by generate-and-test
over the domain of assignments. The formula is
`(p ∨ ¬q) ∧ (q ∨ r) ∧ (¬p ∨ ¬r)`, and it has exactly two models.

## The encoding

**An assignment is a `List[Bit]`**, one cell per variable, so the domain is a
recursive type again. The `domain` relation is the one from
[`alphabet-words`](../alphabet-words/), over a different element sort:

```anthill
rule domain(?x, Bit) :- ?x <=> yes() | ?x <=> no()
rule domain(?x, List[T = ?T])
  :- ?x <=> nil()
   | (?x <=> cons(head: ?h, tail: ?t) & domain(?t, List[T = ?T]) & domain(?h, ?T))
```

The `List` clause is byte-identical to the other example's. That is what the
type travelling as an argument buys: `List[T = Bit]` and `List[T = Letter]`
reach one clause and differ only in what `?T` binds to.

**The formula is the test.** Negation is two facts; a two-literal clause is a
rule with two **exclusive** cases:

```anthill
fact neg(yes(), no())
fact neg(no(), yes())
rule or2(?a, ?)  :- ?a <=> yes()
rule or2(?a, ?b) :- ?a <=> no(), ?b <=> yes()
```

Exclusive matters. A plain `?a <=> yes() | ?b <=> yes()` is a choice point over
two tests, and an assignment that satisfies both literals would be counted
twice. With the cases exclusive every model is one row.

**The rule binds the spine first**, then fills it, then tests:

```anthill
rule model(?vs)
  :- ?vs <=> [?p, ?q, ?r], domain(?vs, List[T = Bit]),
     neg(?p, ?np), neg(?q, ?nq), neg(?r, ?nr),
     or2(?p, ?nq), or2(?q, ?r), or2(?np, ?nr)
```

## What is a workaround here

Two things, both said loudly:

- **The `domain` relation is hand-written.** WI-743 derives this shape from the
  sort declarations; then the rule and the explicit goal go, and the head is
  `rule model(vs: List[T = Bit]) :- ...`. See `alphabet-words` for the full
  account.
- **The bits are `yes` / `no`, not `t` / `f`.** An entity named `f` currently
  captures every one-argument call in an operation body — `length(args)` fails
  to load as "constructor 'f' given 1 positional argument(s)" (measured
  2026-09-11 on a minimal file with `entity f` and nothing else). The natural
  names come back when that is fixed.

## Running

```bash
cd rustland && cargo build -p anthill-cli
./rustland/target/debug/anthill run examples/classic-mini/tiny-sat/
```

Prints `2`. The two models, as a query:

```bash
./rustland/target/debug/anthill query -p examples/classic-mini/tiny-sat \
  --max-results 0 'classic.sat.model(?vs)'
#   ?vs = [no, no, yes]
#   ?vs = [yes, yes, no]
```

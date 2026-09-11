# Words over an alphabet

Every three-letter word over `{a, b, c}` — 27 of them — and the 12 with no
letter next to itself. Generate-and-test, like `map-colouring`, with one
difference that is the whole point: the domain is a **recursive type**.

## The problem

A word is a list of letters. "Every word of length three" is a search over
`List[Letter]`, and `x != y` between neighbours is the test.

## The encoding

**A letter is a sort.** `sort Letter { entity a, entity b, entity c }`.

**The domain is a relation over (value, type).** `domain(?x, T)` holds when
`?x` inhabits `T`, and it is written once per sort as a disjunction over the
sort's constructors, with each field's domain conjoined inside the branch:

```anthill
rule domain(?x, Letter) :- ?x <=> a() | ?x <=> b() | ?x <=> c()
rule domain(?x, List[T = ?T])
  :- ?x <=> nil()
   | (?x <=> cons(head: ?h, tail: ?t) & domain(?t, List[T = ?T]) & domain(?h, ?T))
```

That is the inductive definition of a type's inhabitants, read as a generator.
Three things about it carry the example:

- **The type travels as the second argument.** The `List` clause binds `?T`
  from the caller's `List[T = Letter]` by ordinary unification — types are
  terms — and hands it to the element. The same clause serves `tiny-sat`'s
  `List[T = Bit]`.
- **Clause order is enumeration order.** Base constructor first, and in the
  `cons` branch the tail before the head, so a completely free word comes out
  by length: `nil`, `[a]`, `[b]`, `[c]`, `[a, a]`, … — fair, and infinite.
- **Mode does the rest.** Bound, `domain` checks membership (`[a, 7]` is
  refuted). Partly bound — a spine with free cells — it fills the cells.
  Unbound, it enumerates.

**The rule binds the spine first.**

```anthill
rule word(?w) :- ?w <=> [?, ?, ?], domain(?w, List[T = Letter])
```

The `<=>` fixes three cells and the domain goal after it fills them: 27 rows,
then the search ends. Put the domain goal *first* and the program never ends:
it enumerates every word of every length and the `<=>` prunes each one, so
after the 27 matches it keeps producing longer words that never match. That
was measured, and it is the reason a derived domain goal has to sit after the
written body rather than before it.

## What is a workaround here

The `domain` relation is hand-written. **WI-743** derives exactly this shape
from the sort declarations, at which point the rule and the explicit
`domain(...)` goals go away and a typed head carries the domain:

```anthill
rule word(w: List[T = Letter]) :- w <=> [?, ?, ?]
```

Today that typed head loads but returns one *conditional* answer with the
domain goal undischarged — the annotation checks a value's carried type
(WI-742) and does not yet enumerate. This example is the driver for the
change: when the hand-written relation is deleted, the counts must hold.

## Running

```bash
cd rustland && cargo build -p anthill-cli
./rustland/target/debug/anthill run examples/classic-mini/alphabet-words/
```

Prints `27` then `12`. To see the enumeration order of the unbounded domain,
query `any_word` — the domain with nothing binding the spine — under a cap:

```bash
./rustland/target/debug/anthill query -p examples/classic-mini/alphabet-words \
  --max-results 8 'classic.alphabet.any_word(?w)'
#   ?w = nil
#   ?w = [a]
#   ?w = [b]
#   ?w = [c]
#   ?w = [a, a]
#   ...
```

(A query *pattern* naming the type directly, `domain(?w, List[T = Letter])`,
returns nothing from the CLI today although the same goal inside a rule
answers — measured 2026-09-11, cause not chased. Hence the rule.)

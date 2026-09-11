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
`?x` inhabits `T`. It is not written here: the loader DERIVES it, one clause per
sort with constructors, as a disjunction over those constructors with each
field's domain conjoined inside the branch (WI-743). What it derives for the two
sorts this example uses is exactly:

```anthill
domain(?x, Letter)       :- ?x <=> a() | ?x <=> b() | ?x <=> c()
domain(?x, List[T = ?T]) :- ?x <=> nil()
                          | (?x <=> cons(head: ?h, tail: ?t)
                               & domain(?t, List[T = ?T]) & domain(?h, ?T))
```

That is the inductive definition of a type's inhabitants, read as a generator.
Three things about it carry the example:

- **The type travels as the second argument.** The `List` clause binds `?T`
  from the caller's `List[T = Letter]` by ordinary unification — types are
  terms — and hands it to the element. The same clause serves `tiny-sat`'s
  `List[T = Bit]`.
- **Clause order is enumeration order.** Base constructors first, and in the
  `cons` branch the tail before the head, so a completely free word comes out
  by length: `nil`, `[a]`, `[b]`, `[c]`, `[a, a]`, … — fair, and infinite. The
  derivation writes those two orderings deliberately; they are what "fair"
  means here, not a side effect of how the clause happens to be laid out.
  Finiteness is NOT a condition on a sort having a domain — it only decides
  whether the stream ends.
- **Mode does the rest.** Bound, `domain` checks membership (`[a, 7]` is
  refuted). Partly bound — a spine with free cells — it fills the cells.
  Unbound, it enumerates.

**The rule binds the spine first.**

```anthill
rule word(w: List[T = Letter]) :- w <=> [?, ?, ?]
```

`w: List[T = Letter]` is a typed head parameter, and that annotation is the
whole generator. The `<=>` fixes three cells and the domain goal the annotation
generates fills them: 27 rows, then the search ends.

**The generated goal goes AFTER the written body**, and this example is where
that was measured. Put the domain goal *first* and the program never ends: it
enumerates every word of every length and the `<=>` prunes each one, so after
the 27 matches it keeps producing longer words that never match. That is why a
derived domain goal is appended while WI-742's conformance guard is prepended —
the two placements are not interchangeable, and neither is a style choice.

## What this example used to work around

Until WI-743 the `domain` relation above was written out by hand, in this file,
in exactly the shape the loader now derives — and the rule carried an explicit
`domain(?w, List[T = Letter])` goal instead of a typed head. The annotation
loaded, but it only CHECKED a value's carried type (WI-742) and returned one
*conditional* answer with nothing generating. This example was the driver for
the change: the hand-written relation was deleted, and the counts held.

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

(A query *pattern* naming a parameterized type argument directly returns
nothing from the CLI today although the same goal inside a rule answers —
measured 2026-09-11, WI-20260911-7FP1M. Hence the rule.)

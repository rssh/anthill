# Map colouring

Colour each region of a map so that no two regions sharing a border get the same
colour — the textbook constraint-satisfaction problem, and the textbook shape of
**generate-and-test**.

## The problem

The six mainland states and territories of Australia, three colours:

```
        ┌─────────┬─────┬──────┐
        │         │ NT  │      │
        │   WA    ├─────┤  Q   │
        │         │     ├──────┤
        │         │ SA  │ NSW  │
        └─────────┴─────┴───┬──┘
                            │V │
                            └──┘
```

Borders: WA–NT, WA–SA, NT–SA, NT–Q, SA–Q, SA–NSW, SA–V, Q–NSW, NSW–V.

## The encoding

Three pieces, and none of them is an algorithm.

**A colour is a sort, not a string.** `sort Colour { entity red, entity green,
entity blue }` — three variants, so a colour is one of exactly three things and
`colouring` types as `Relation[(wa: Colour, nt: Colour, …)]`. A consumer of a row
gets a colour, not any old text.

**The domain is the sort.** A free colour variable ranges over exactly `red`,
`green` and `blue` because the sort says those are the constructors — nothing
else is written down. There is still no separate notion of "domain" in the
language: a domain *is* a relation, and the one a closed sort defines is derived
from its constructor list (WI-743, proposal 060 §2.2).

And it is a relation you can hold. `Colour.domain` is that same derived relation
under a name, so `main` below counts the colours with `Colour.domain.takeN(9)` —
three rows, and the only place they are written is the three `entity` lines
(WI-20260911-WT8WG). The author writes no domain expression at either face: the
annotation reads it as a goal, the citation reads it as a value.

**The annotation is what does it.** `wa: Colour` in the head is a parameter
(proposal 060 §2.1): it introduces a clause variable named `wa`, typed `Colour`,
and that annotation is read twice — as the column's TYPE, so `colouring` is
`Relation[(wa: Colour, …)]`, and as the DOMAIN `wa` ranges over.

It used to take two more pieces, and this example was where both were measured:

- **The sort was the type, not a generator.** SLD resolves goals against facts
  and rules, and a sort declaration was not something you could call — so a
  `palette` relation had to be written beside `Colour` to enumerate it:
  `fact palette(c: red())` and friends. Dropping those facts and keeping only
  `rule colouring(?wa: Colour, ?nt: Colour) :- ?wa != ?nt` left `?wa` unbound, the
  guard unable to decide, and raised `relation_floundered` rather than
  enumerating. Measured, and that is what WI-743 removed.
- **The entity field was what carried the type.** The palette could have been a
  rule (`rule palette(?c) :- eq(?c, red())`, three clauses, no wrapper sort) — it
  enumerated fine, but the columns came out as `(wa: ?_, nt: ?_)`, *untyped*,
  because a rule subgoal constrains nothing. It was `palette(c: Colour)`'s entity
  field that told the typer a column was a `Colour`. WI-742 moved that job to the
  annotation, which is why the wrapper sort could go.

**The map is a rule.** `colouring(wa: Colour, …)` says: each region takes some
colour of the three there are, and every bordering pair differs. The annotations
generate; the `!=` goals test. Read it as a definition of what a valid colouring
*is* — the search is not written down anywhere.

The generated domain goal is placed AFTER the written body, not before it. For
this example either order works; for a RECURSIVE domain it is the difference
between terminating and not — see `alphabet-words`.

`?a != ?b` is infix sugar: the parser desugars it to `neq(?a, ?b)` via an
ordinary entry in the operator table (`parse/pratt.rs`), alongside `=`, `<`,
`+`, `and`, `|` and the rest. Same operation, same resolver path — it is
spelling, not a separate mechanism.

## Running it

```bash
cd rustland && cargo build -p anthill-cli
./rustland/target/debug/anthill run examples/classic-mini/map-colouring/
```

Prints `6`.

## Why 6

WA, NT and SA border each other, so they form a triangle and must take three
distinct colours: 3! = 6 ways. Everything else is then forced — Q differs from NT
and SA, so Q takes WA's colour; NSW differs from Q and SA, so it takes NT's; V
differs from SA and NSW, so it takes WA's. Six colourings, no more.

## What this example is really testing

`colouring` is queried with **every column free** — mode (out,…,out), the mode
where you don't know the answer and want the search to find it. That is the whole
point of generate-and-test, and until recently anthill got it wrong.

Two bugs sat on exactly this shape and composed:

- **WI-739** — a comparison guard on the rule's own head variables delayed the
  *whole rule* before its body could run, collapsing the enumeration into a single
  floundered residual with unbound columns.
- **WI-737** — that residual was then materialized as though it were a real
  answer.

Run this example against the resolver from before WI-739 and it does not print
`6`: it raises `error: relation_floundered`. That is WI-737 doing its job —
failing loudly rather than printing a row of logic variables — on a bug WI-739
then removed.

The guards here are spelled `?x != ?y`, the natural way — which is `neq(?x, ?y)`
after desugaring. Before WI-739 the only working spelling was `not(eq(?x, ?y))`,
an undiscoverable workaround that happened to take a different path through the
resolver. It is deliberately **not** used here: the whole reason to write these
examples is to find out where the natural spelling doesn't work yet.

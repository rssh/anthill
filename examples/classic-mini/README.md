# classic-mini

Small classic programs, written in anthill, one per subdirectory.

The repository's other examples (`github-todo`, `webots-modelling`) are both
**domain models** — they show anthill describing a world. This collection shows
anthill *as a logic language*: rules, SLD search, and the relational face.

Each example states a problem declaratively — what a solution **is**, never how
to find one — and lets resolution do the rest. There is no search algorithm in
any of these files.

## Examples

| Example | Shows | Status |
|---------|-------|--------|
| [`ancestor/`](ancestor/) | Recursion — transitive closure as two clauses; one relation queried in three modes | Runs |
| [`map-colouring/`](map-colouring/) | Generate-and-test: a domain from facts, `neq` guards, the answer queried free | Runs |

### Not yet here

| Example | Shows | Blocked on |
|---------|-------|------------|
| `eight-queens/` | Proposal 052's own running example | WI-740 |

Further candidates: dining philosophers, zebra puzzle, towers of hanoi, map
colouring over a larger map, send+more=money.

`ancestor` **was** written and then withheld — a recursive rule could not be cited
by name as a relation value, because a column typed only by the rule's own
self-reference came out untyped and the cross-clause lub read that absence as a
conflict. WI-714's schema synthesis now takes such a column's type from the clause
that knows, so the example is here and runs.

## Running

Each example is a program in its own right — driven from anthill source, not a
Rust harness:

```bash
cd rustland && cargo build -p anthill-cli
./rustland/target/debug/anthill run examples/classic-mini/map-colouring/
```

They are also exercised by `classic_mini_test.rs`, so they cannot rot.

## Adding an example

- One self-contained subdirectory: the `.anthill` sources plus a `README.md`
  stating the problem, the encoding, and how to run it.
- Prefer the classic encoding. If you take a workaround because the engine
  cannot yet express the natural form, **say so loudly in the README** — a
  workaround that reads as idiomatic is worse than a missing example.
- Add it to the table above and to `classic_mini_test.rs`.

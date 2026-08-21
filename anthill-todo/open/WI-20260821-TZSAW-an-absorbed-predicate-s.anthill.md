## Attributes

- id: WI-20260821-TZSAW-an-absorbed-predicate-s
- created: 2026-08-21T13:25:37Z

- status: Open
- status_agent: user
- status_at: 2026-08-21T13:25:37Z

- acceptance: cargo-test, scaland-sbt-test

## Description

AN ABSORBED PREDICATE'S QUALIFIED NAME IS DELETED, NOT EMPTIED -- so a third file that
cites it breaks, written by an author who can neither see nor change the file that broke
them.

MEASURED (rustland, WI-980's tree):
  file A  namespace glib { sort S { entity s(n: Int64)  rule p(1) } }
  file C  namespace guser { import glib.S.{p}  rule uses(?x) :- p(?x) }
    -> LOADS. `glib.S.p` = 1 clause.
  ADD file B  namespace glib { rule p(2) }        -- never names `S`
    -> REFUSED: "2:18: unresolved import 'glib.S.p'" and
                "3:20: rule-body goal p names nothing"
  The qualified-citation spelling breaks the same way:
  `namespace guse2 { rule uses(?x) :- glib.S.p(?x) }` -> "rule-body goal 'glib.S.p' names
  nothing". CONTROL (drop B): loads, `glib.S.p` = Some(1).

THE JOIN ITSELF IS DELIBERATE AND IS NOT WHAT THIS TICKET DISPUTES.
kernel-language.md §"Joining is not confined to one file" says a head in a scope you can
see is one you join, whoever wrote it. What that paragraph ALSO says is that the inner
predicate then "holds no clauses" -- which would leave `glib.S.p` resolvable and answering
nothing. The shipped behaviour is different in kind: the inner scope never mints, so the
NAME does not exist, and every `import`/qualified citation of it is a hard load error.

WHY THE DIFFERENCE MATTERS. "Holds no clauses" is a change to what a program COMPUTES, and
the author of file C can see it by reading the predicate. Deletion is a change to what
RESOLVES, and it reaches files that name neither B nor the join -- the diagnostic names
the import site and the goal, never the head that absorbed them, and nothing in C or A is
wrong.

THE DECISION THIS NEEDS. Either the spec sentence is wrong and deletion is intended (then
say so, and say that a qualified citation of an absorbable predicate is not stable), or
the absorbed scope should still get its name, aliased to the owner -- so `glib.S.p`
resolves to `glib.p` and answers its clauses. The second is what the sentence promises and
what keeps a library's published names stable under an edit elsewhere in the library.

WATCH FOR: whatever is chosen must not resurrect the split -- the two must remain ONE
predicate. An alias is a second NAME for one symbol, not a second symbol; `import
glib.S.{p}` resolving to `glib.p` is the shape to aim at, and WI-295's deferred-import
retry is where such a name would have to be registered.

ACCEPTANCE: with B present, file C still loads and `uses(?x)` answers BOTH clauses. The
qualified-citation spelling likewise. Control: dropping B leaves the program unchanged.
Say at the site which rows fail on a back-out. cargo-test green via
rustland/scripts/test.sh.


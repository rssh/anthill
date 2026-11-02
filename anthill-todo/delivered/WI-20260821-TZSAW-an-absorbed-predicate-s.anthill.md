## Attributes

- id: WI-20260821-TZSAW-an-absorbed-predicate-s
- created: 2026-08-21T13:25:37Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-02T12:39:42Z

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

## Changes

### 2026-11-02T12:39:41Z — feedback — claude

DELIVERED — option (a) (user, 2026-11-02): a head that joins an enclosing declaration names nothing at its own scope, and a citation of that name is refused. Re-measured on HEAD first. The ticket wrote its clauses body-less (rule p(1)), which since 061 declares and asserts nothing; written ':- true', the ticket's program (sibling clause undeclared) is now 845G7's visibility refusal at a.anthill:4:5 naming 'glib, glib.S', with nothing reported at the citing file, and the disputed 'holds no clauses' sentence is gone from the spec. What remained: the refusal's own first repair, 'rule p(?x)' at glib in the sibling file, makes S's unchanged head a clause of glib.p, glib.S.p is never minted, and the citing file fails with the ticket's two errors (control without the sibling: 1 answer). Decided intended. kernel-language.md §'A declaration and an explicit path are what join scopes' now says the head declares nothing at Rec and a citation of demo.Rec.p is refused, also when the declaration is in another file; a Rec.p others cite is §WI-896's case (declare it locally, a separate predicate). The visibility refusal's owner arm now says 'no other of those scopes then has a p of its own' (rustland and scaland). Rows: wi_tzsaw_inner_name_after_join_test (3: the join with both citation spellings refused, the undeclared sibling refused at the library head, a declaration in S keeping the name); scaland RuleHeadDeclarationTest 'TZSAW: …'. Back-outs measured: fqc85's pass-1 mint gated off fails 2 of the 3 Rust rows (the undeclared row passes by design); the new message clause removed fails the undeclared row alone in rustland and the TZSAW row alone in scaland. Full workspace 11,492 passed, 0 failed; scaland 51 + 798.


## Attributes

- id: WI-20260908-BN5RA-the-845g7-collision-refusal
- created: 2026-09-08T11:17:30Z

- status: Open
- status_agent: claude
- status_at: 2026-09-08T11:17:30Z

- acceptance: cargo-test, scaland-sbt-test

## Description

THE 845G7 COLLISION REFUSAL ASKS REACH ONLY FROM FILES THAT WRITE A HEAD, SO WHICH FILE AN
`import` WAS TYPED IN DECIDES WHETHER THE PROGRAM LOADS. Present in BOTH implementations,
so it needs ONE decision taken for both.

WI-20260822-845G7's rule is stated over VISIBILITY: two scopes that can see each other may
not both introduce one name. `head_name_collisions` answers "can see" per candidate scope
by asking `head_name_reach` once per file that scope WRITES A HEAD IN — `asked` is built
from `sites` (rustland `kb/load.rs`; scaland `Loader.headNameCollisions`, same set). Per
WI-995 imports are FILE-LOCAL, so a file that re-opens the scope and carries the `import`
but writes NO head is never asked, contributes no edge, and the pair is not refused.

MEASURED, three files, rustland via `anthill load` and scaland via `Loader.loadAll` —
BYTE-IDENTICAL ANSWERS, same message, same head located:

  g1: namespace ns.B   rule p(2) :- true                       end
  g2: namespace ns.A   import ns.B.*   rule reads(?x) :- p(?x)  end
  g3: namespace ns.A   rule p(1) :- true                        end
    -> LOADS CLEAN (rustland: `loaded: 2848 facts, 182 rules`). `ns.A.p` and `ns.B.p` both
       exist, `reads(1)`=1 and `reads(2)`=0 — the `import ns.B.*` one line above the reader
       is SILENTLY SHADOWED, which is verbatim the failure the refusal's own message
       describes.

  the SAME program with that one `import` line moved into g3 (the head-writing file)
    -> REFUSED: "the rule head `p` introduces that name at 2 scopes … ns.A, ns.B".

So the verdict turns on where a line was typed, not on what the program means. `ns.A` is
one scope with one predicate either way.

WHY IT WAS NOT CLOSED IN THE PORT (WI-20260821-SBZ2A): widening scaland's `asked` alone
would make the two loaders disagree about which programs LOAD — the divergence class that
ticket exists to remove. It is recorded at the site in both trees' terms and DRIVEN by
`RuleHeadDeclarationTest`'s "845G7 LIMIT: the reach is asked only from files that WRITE a
head", which asserts the silence including `reads(2)`=0 against a control of 1.

WHAT TO DECIDE:
 1. THE ASKED SET. Every file that OPENS the scope, or every file of the scan? The first is
    the narrow reading of "what this scope can see"; the second is cheaper to state and
    strictly wider. Both change which programs load, so the CENSUS decides: instrument the
    reach loop over stdlib + anthill-stl + examples + anthill-todo + every fixture and
    report how many collisions each reading ADDS. 845G7's own corpus cost was zero; if
    either reading is not also zero, that is the argument against it.
 2. WHETHER THE NAMED OWNER MOVES WITH IT. The owner test is already per (scope, FILE) —
    "reached from EVERY file it writes a head in" — for the reason `/code-review` measured
    on `pwA`: declaring at a scope only SOME of the contributor's files can see leaves the
    others behind. Widening the asked set widens that quantifier too, and the promise the
    message makes must still hold.
 3. THE ORDER OF THE TWO CHANGES. rustland first or scaland first, with the other's port
    ticket filed at the same time — a one-sided landing IS the divergence.

ACCEPTANCE: the three-file program above must give the SAME verdict whichever file the
`import` is typed in, in BOTH implementations, with the clause counts and the `reads`
answers driven rather than the load status alone. The census of item 1 recorded in the
delivery. Every existing 845G7 row keeps its verdict (they are the control that the
widening did not turn the rule into "any two scopes sharing a short name"), notably
`two scopes that cannot see each other keep their own`. cargo-test and sbt test green.


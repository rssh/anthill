## Attributes

- id: WI-20261008-JRV1T-scaland-a-name-qualified
- created: 2026-10-08T10:08:04Z

- status: Open
- status_agent: user
- status_at: 2026-10-08T10:08:04Z

- acceptance: scaland-sbt-test

## Description

SCALAND: A NAME QUALIFIED RELATIVE TO THE SCOPE IT IS WRITTEN IN DOES NOT RESOLVE. The clause is stored under a symbol nothing can name, on a program that loads clean.

THE PROGRAM:

  namespace n
    sort Rec
      entity E(v: Int64)
      rule p(1) :- true
      rule see(?x) :- p(?x)
    end
    fact Rec.p(2)
  end

                                              rustland   scaland
  n.Rec.see(?x)                                   2          1     <- the fact is not a clause of n.Rec.p
  the same with `rule Rec.p(2) :- true`           2          1
  the same with `fact n.Rec.p(2)`                 2          2     <- the fully qualified spelling works

kernel-language.md §2: "A `Name` is resolved relative to where it is written".

MECHANISM. `Loader.lookupWritten` answers a dotted spelling from `byQualifiedName` — the table of ABSOLUTE names — and otherwise hands the WHOLE spelling to `resolveInScope` as one short name. Nothing resolves the first segment by scope and walks the rest, which is what rustland's `resolve_dotted_in_kb` does. A miss falls to `resolveName`'s `kb.intern(name)`, so the clause lands under a symbol spelled `Rec.p`.

MEASURED 2026-10-08 while porting WI-20260821-RDGQC to scaland; that port did not change it. Only the HEAD position was measured. Before scoping the fix, run the body-goal and value positions too — rustland answers 1 for `rule see(?x) :- Rec.p(?x)` written in `n`, and refuses `:- Rec.nosuch(?x)` with "rule-body goal `Rec.nosuch` names nothing".

ACCEPTANCE: drive it. The program above answers 2 through `n.Rec.see`, in the fact spelling and the rule spelling. The fully qualified spelling keeps answering 2 — that row passes before and after and says so. A relative spelling that names nothing gets whatever rustland gives the same program, measured there first. `sbt -batch testFull` green.


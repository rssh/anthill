## Attributes

- id: WI-20261008-G2BXZ-scaland-a-host-provides
- created: 2026-10-08T10:08:05Z

- status: Open
- status_agent: user
- status_at: 2026-10-08T10:08:05Z

- acceptance: scaland-sbt-test

## Description

SCALAND: A HOST `provides … language L … end` BLOCK IS LOADED ONLY FOR `language anthill`, AND IN THE SCOPE IT IS WRITTEN IN. rustland loads every language's block in the scope of the sort the block realizes.

THE PROGRAM:

  namespace n
    sort RecP
      entity P(v: Int64)
      rule see(?x) :- pick(?x)
    end
    sort RecQ
      entity Q(v: Int64)
      rule see(?x) :- pick(?x)
    end
    provides RecP language anthill
      rule pick(1) :- true
    end
    provides RecQ language anthill
      rule pick(2) :- true
    end
  end

                                    rustland              scaland
  n.RecP.see / n.RecQ.see           1 and 1               2 and 2
  where `pick` lives                n.RecP.pick, n.RecQ.pick     n.pick, one predicate with two clauses
  the same with `language rust`     1 and 1               0 and 0 — no clause is loaded, no name exists
  (and `artifact "x.rs"`)

kernel-language.md §10.2 puts a block's clauses in the realized sort's scope, and §"A rule-introduced functor is scoped where it is written" puts its heads there.

MECHANISM. `Loader.loadsProvidesBlockClauses` is the gate (`language == anthill`); `loadProvidesBlock` asserts at the scope it is handed, which is the enclosing one, and `RuleHeadCollectPass` mints there behind the same gate. `loadProvidesBlock`'s `ProvidesClauseI` arm already names "opening the carrier's scope" as the port that remains, and its `OperationMapI` / `ConstMapI` arms wait on the same thing. rustland's side is `load_provides_block` and `RuleHeadCollectPass::collect_provides_block` (WI-20260821-TTHRK, WI-20260827-APXSS, WI-984, and WI-20260924-SNJPR for a block written on an alias).

Before WI-20260821-RDGQC's scaland port the heads were not minted at all and fell to the bare intern; the port scoped them to where scaland lands the clauses, and left where that is alone.

ALSO IN REACH: a body-less `rule p(?x)` inside a block is refused today as "never brought into existence", because pass 1b does not descend into a block.

ACCEPTANCE: drive it. The program above gives 1 and 1 with `n.RecP.pick` and `n.RecQ.pick` both citable, for `language anthill` and for `language rust`. `HeadIntroductionCensusTest`'s block row is rewritten to that — today it pins the written scope, and its `language rust` half pins "no name". A body-less rule inside a block gets rustland's answer for the same program. `sbt -batch testFull` green.


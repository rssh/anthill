## Attributes

- id: WI-20260902-VZC2C-a-nullary-bool-operation-is
- created: 2026-09-02T13:09:51Z

- status: Open
- status_agent: user
- status_at: 2026-09-02T13:09:51Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A NULLARY BOOL OPERATION IS DROPPED AS A GOAL-CONNECTIVE BRANCH (`|` / `&`), IN EVERY SPELLING.

MEASURED BY ME on the WI-20260902-VNWAW tree; one file, both qualifications, both nullary
spellings, and the row that answers beside them:

  namespace zzvc.one
    import anthill.prelude.Bool
    operation onx2() -> Bool = true
    fact pbVc(1)
    rule sAtom(1) :- onx2                -- 1   <- the body ATOM reaches WI-580's view
    rule sOr(1)   :- pbVc(999) | onx2    -- 0   <- silently empty
    rule sOrP(1)  :- pbVc(999) | onx2()  -- 0
    rule sAnd(1)  :- pbVc(1) & onx2      -- 0
  end

and the same four rows, all 0, with the goal written as a DOTTED citation
(`zzvc.inner.onx`) and 0 for its applied spelling too. Exit 0, no diagnostic.

FOUR CONTROLS THAT ANSWER, which is what pins the gap to the OPERATION's reading rather
than to `or`: the same operation as a plain body atom answers 1; `not(onx)` answers 0, so
`kernel.not` DOES reach the relational view from its negand; an arity-1 predicate branch
answers (`pb(999) | pb(1)` -> 1); and an ENTITY branch answers under the same connective
(`pb(999) | ns.acct` -> 1, both dotted spellings), so the connective's slot IS a goal
position and the loader routes it as one.

So WI-580's derived relational view for a Bool operation (`eq(op(args), true)`) is reached
from a rule body's own atom list and from `kernel.not`'s negand, and NOT from
`kernel.or` / `kernel.and`'s branch slots. Same silent-unqueryability class CZJ2N and
8K4RB each closed one position at a time.

SPELLING-INDEPENDENT AND NOT VNWAW'S: all four spellings answer 0 together, before and
after that ticket, which is why VNWAW asserts the two columns are EQUAL there instead of
fixing it. `wi_vnwaw_dotted_goal_readings_test::a_goal_connective_branch_reads_alike_for_every_spelling`
is the standing fixture and is the row that must FLIP when this is closed.

NOT RE-TRACED — I did not find the site; VERIFY BEFORE FIXING. The two ends are the
loader's goal routing (which demonstrably DOES treat the branch as a goal — the entity
control proves it) and the resolver's `resolve_binary_goal_args` ->
`push_choice`/`push_and` continuation, where the branch Value is pushed as a goal without
whatever step a top-level body atom takes to reach `reduce_op_value` / the WI-580 hook.

ACCEPTANCE: `sOr` / `sOrP` / `sAnd` and their four dotted twins answer 1, with a
`false`-bodied control pair (`operation offx() -> Bool = false`) answering 0 under the
same connective so the row measures the VALUE and not mere success. CONTROLS: the ENTITY
branch, the arity-1 predicate branch and `sAtom` must keep answering, `not(onx)` must keep
answering 0, and the `&` rows must be backed out separately from the `|` ones — they are
two connectives and a one-connective repair would leave the other exactly as broken.


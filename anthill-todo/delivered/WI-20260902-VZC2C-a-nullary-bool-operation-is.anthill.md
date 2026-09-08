## Attributes

- id: WI-20260902-VZC2C-a-nullary-bool-operation-is
- created: 2026-09-02T13:09:51Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-08T07:09:45Z

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

## Changes

### 2026-09-08T07:09:44Z — feedback — user

DELIVERED. A nullary Bool operation now takes WI-580's relational view wherever the goal
reaches the resolver, not only where the loader hands over its own occurrence: a `|` / `&`
BRANCH (this ticket's rows), a TOP-LEVEL QUERY, and a CONSTRAINT GUARD.

THE TICKET'S TWO ENDS WERE BOTH INNOCENT, and its own fourth control was the discriminator.
Probed at the hook: the branch DOES arrive as a goal, `resolve_binary_goal_args` DOES push
it, and the WI-580 hook DOES fire on it — it builds `eq(<operand>, true)` with the operand
a bare `Expr::Ref(onx2)`, which `reduce_op_value` hands straight back un-reduced, so the
`eq` fails. The DQD5W paragraph already at that site says exactly this sentence about the
CARRIER; this was the SHAPE.

WHERE THE SHAPE IS LOST, and it is not `or`. The storage canon makes `Fn{f}` and `Ref(f)`
ONE TERM, and `KnowledgeBase::with_fresh_vars` reifies every non-`Term` head-match binding
through `value_to_term`, because the De Bruijn / rename / answer-link walks under it read
`tree_subst` term-only (WI-636). That boundary's own doc calls the `Node` reification
LOSSLESS — and it is, for everything but a nullary call. MEASURED: the `or` goal reaches
`step_init` as `Node(Apply{onx2})` at source span 189..193; the branch, one head match
later, is `Node(Ref(onx2))` with the span zeroed. `kernel.not` has no such rule — it is a
builtin that reads its negand off the goal's own view — which is why `not(onx)` reached the
view when a branch did not.

THREE PRODUCERS, ONE CONSUMER, ONE REPAIR, and two of the three were not in the ticket:
  * the connective BRANCH (head match -> `with_fresh_vars`);
  * a TOP-LEVEL QUERY — `load::nullary_query_canon` builds the transient carrier's
    `Expr::Ref` deliberately, to keep the two carriers' canons one test, so `anthill run`'s
    own query path could never reduce a nullary Bool op: `onq` and `onq()` both answered 0;
  * a CONSTRAINT GUARD — DQD5W's population one shape in, and the only WRONG answer of the
    three: `no ?n: Box(n: ?n) -: flag` could never hold, so the `no` never fired and its
    `forall` transform fired on every row.
The repair is at the consumer they converge on (`resolve.rs::step_init`'s WI-580 hook,
which rebuilds the `Ref` leaf into `Apply{f}` before wrapping it in `eq(…, true)`), and NOT
at any producer: a bare nullary op in an arrow-typed slot is §5.4's unapplied function
value, and no producer — nor `reduce_op_value` — has an expected type to consult, while
reaching the hook already MEANS "the relational view of `f` at its declared arity".
`rebuilt_expr`, so the goal's span/owner/typer pin ride along (WI-1026).

CORPUS CENSUS: ZERO. 55 nullary operations across every `.anthill` in the tree; exactly one
returns Bool — `anthill.kernel.cut` — and it is a resolver BUILTIN and body-less, so
`bare_bodied_bool_relation` excludes it twice. New code only, as VNWAW found for the dotted
spelling.

BACK-OUT (guard disabled present-but-inert, WHOLE WORKSPACE, 30 binaries): EXACTLY 5 TESTS
FAIL, all five written for this ticket — the four in `wi_vzc2c_connective_branch_op_test`
and `wi_vnwaw…::a_goal_connective_branch_reads_alike_for_every_spelling`, the standing
fixture the ticket named, whose six `0` rows are now `1`s. Its `dOrEnt` control and both
VNWAW back-out axes are unchanged. Per-row, paired: the 8 `on` rows go 1->0, the two
`not(on…)` rows go 0->1 (NAF laundering an unrunnable goal into a proof), the nested pair
1->0, the query `on` pair 1->0, the constraint's `ong` pair stops firing.

ONE BACK-OUT FELLS BOTH CONNECTIVES — the ticket asked for `&` to be backed out separately
because a repair written AT a connective would leave the other broken. This one is written
at neither: `push_choice` builds a CONTINUATION candidate in a new frame and `push_and`
SPLICES its conjuncts into the current one, so the two travel different routes to the same
hook, and a repair reaching only one of them still fails the other four rows.

CONTROLS, green either way by design and each stated at its site: the six `false`-bodied
`off` rows (so the moving rows measure the operation's VALUE, not mere success), the ENTITY
branch, the arity-1 predicate branch, `sAtom`/`dAtom`, `not(onx2)` at atom position, and
`not(off…)` inside a branch (so a repair that merely broke NAF fails beside the rows it
would otherwise pass).

SPEC: §5.3 gains the paragraph — the reading holds at every goal position, why it was false
for a nullary operation, and that the value slot's two readings (§5.4) are untouched.

/code-review (high) RAN and found 2, both fixed inline rather than filed:
  * THE OPERAND'S SPELLING. My first form tested for `Expr::Ref`, and `term_view.rs`'s own
    head list names FOUR spellings of a bare nullary name — `Term::Ref(f)`,
    `Value::SymbolRef(f)`, `Expr::Ref(f)` and a stored nullary application — of which only
    the application reduces. The reviewer called `SymbolRef` latent; MEASURED, it is not:
    `resolve`'s front door maps each goal through `as_bind_value`, which unwraps an
    `Expr::Spliced` to the value it carries, so a `Spliced(SymbolRef)` goal — the shape the
    dictionary / `OpRef` mints ride on — arrives at this hook as a bare `Value::SymbolRef`
    and answered nothing. The test now asks the site's own question ("is this already an
    application?") and the `SymbolRef` carrier gets a synthesized occurrence.
    `a_spliced_symbol_ref_goal_takes_the_same_reading` drives it; backing out the WIDENING
    alone (restore the `Expr::Ref` test) fells exactly that one row of 4 276, so the two
    components are separable and each has its own back-out.
  * `wi995_import_file_locality_test`'s `parent_edges == 0` pinned one direction only. A
    new `ImportOrigin` variant falling through the negated `matches!` reds it (twice
    already: `Provision` 0->11, `Requirement` 0->24/28) — but if `import_record_counts`
    stopped counting import edges AT ALL, all six corpus groups still report 0 and the
    audit delivers a verdict while measuring nothing. Pre-existing, from 6BX85/N2865, and
    fixed inline: `wi995_an_import_parent_edge_is_actually_counted` writes the wildcard the
    corpus has none of, with the member-import control beside it. MEASURED: neutralize that
    predicate and EXACTLY ONE row of 4 277 fails — this one.

TESTS: full workspace 6 616 green / 0 failed, 30 binaries. scaland `sbt test` 541/2 failed
— `BootstrapTest` (`WI-1066 CORPUS CONTROL`, `WI-1055`), PRE-EXISTING: verified by stashing
this change and re-running on the clean tree, same 2. Not touched by this ticket (no Scala,
no stdlib, and the scaland resolver has neither the WI-580 hook nor `push_choice`).


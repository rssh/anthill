## Attributes

- id: WI-20261115-DHN42-proposal-010-1-stage-3-docs
- created: 2026-11-15T06:33:13Z

- status: PreOpened
- status_agent: claude
- status_at: 2026-11-15T06:33:21Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261105-CBRD2-proposal-073-stage-4-no-typed

- tags: proposal-010.1

## Description

Proposal 010.1, stage 3 (docs/proposals/010.1-query-interfaces.md §3.3): KB.execute_untyped(kb, q, dictionaries) runs a LogicalQuery no typer reads. The query is a clause with no head (§3.1): each requirement it writes as a goal (Spec[T = ?t]) and each typed variable (?x: ?t, a SortDomain[T] slot, 060 §2.3) is a parameter, filled by a dictionary the caller passes and used as given; a slot given none is an error when the query runs (today's evaluation_failure, 'the requirement anthill.prelude.PartialEq of a clause was passed by no caller'). Its type variables are query variables (?t), not a bracket. PROGRAM: the Pt of 010.1 §2 (its eq compares x alone) and rule sameR[A](?a: A, ?b: A) :- PartialEq[T = A], ?a = ?b. EXPECTED: execute_untyped(kb(), pattern_query(term: make_fn("…sameR", [as_term(pt(1, 2)), as_term(pt(1, 9))])), [Dictionary.instance[PartialEq[T = Pt]]()]) answers one solution through Pt.eq; without the dictionary, an evaluation_failure naming PartialEq; a query that writes no slot answers as KB.execute does. BLOCKED ON TWO DECISIONS (010.1 §4): Q1, how a passed dictionary meets its slot (by spec, one per spec as 058 §3.9's anonymous slot, or by position) and whether it binds ?t as 060.1 binds ?p in Sp[C = Red, P = ?p]; Q2, how a LogicalQuery value writes a slot (make_fn takes a name and terms only, and a goal stored in a fact cannot carry a bracket). Pre-opened until both are decided.


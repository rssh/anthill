## Attributes

- id: WI-20261105-0NFCC-the-narrowing-does-not-read-a
- created: 2026-11-05T17:31:42Z

- status: Open
- status_agent: claude
- status_at: 2026-11-05T17:31:42Z

- acceptance: cargo-test, scaland-sbt-test

- tags: proposal-068

## Description

THE NARROWING DOES NOT READ A RULE'S DATA ARGUMENT AGAINST A CONSTRUCTOR PATTERN: a call whose known argument is a list built in the rule stays conditional where it could narrow (found on WI-20261013-DEY66, 2026-11-05; an incompleteness, never a wrong answer). MEASURED on ab6d7288, the same on fd640523: over operation sel(ys: List[T = Int64], xs: List[T = Int64]) -> Int64 = match ys case cons(g, u) -> (match xs case nil -> g case cons(h, t) -> h) case nil -> 0, rule s1(?r) :- sel([5], ?xs) = 5, ?r <=> ?xs answers one conditional row, residual eq(sel([5], ?_), 5); the same with cons(5, nil) written, and for the tuple spelling selT over match (ys, xs) (both are wanted: ?r = nil and ?r = cons(head: 5, tail: ?t), as firstof(?xs, 9) = 9 answers since DEY66). THE CAUSE (traced in folded_call_match): the argument reaches body_specialize as the rule body's data form, Expr::Apply over the entity cons with named head / tail, and the reducer's constructor readers (occ_head_ctor, ctor_field_occs, used by match_pattern_occ and select_arm) recognise only Expr::Constructor and a bare entity name, so the match on ys is Undecidable and the residual is no match on a flexible variable. ACCEPTANCE (cargo-test via rustland/scripts/test.sh; every row driven, back-out stated at its site): s1 and its cons(5, nil) and tuple twins answer the two definite rows; a known argument that matches no arm still declines or drops as it does at an operation-body constructor; wi_dey66_per_consumer_reductions_test unchanged.


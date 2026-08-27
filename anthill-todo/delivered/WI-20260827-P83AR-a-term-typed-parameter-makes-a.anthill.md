## Attributes

- id: WI-20260827-P83AR-a-term-typed-parameter-makes-a
- created: 2026-08-27T08:32:17Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-27T09:04:03Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A `Term`-TYPED PARAMETER MAKES A RULE-BODY HOST CALL DECIDE FALSE INSTEAD OF SUSPENDING, so `not(...)` over it answers 1 out of a call that never ran. Found finishing WI-880's reflect migration; PRE-EXISTING and untouched by it (measured 0 solutions both before and after that migration, where the flat row went 0 -> 1).

MEASURED, eval and SLD disagreeing on ONE expression:
  operation viaAs(n: Int64) -> Option[T = Int64] = term_as_int(as_term(7))
      -> eval answers some(7).
  rule ras(1) :- term_as_int(as_term(7)) = some(7)
      -> 0 solutions, TOTAL 0 — DECIDED FALSE, not suspended.
  rule bad(1) :- not(term_as_int(as_term(7)) = some(7))
      -> 1 DEFINITE. A positive conclusion from a term the rule never read.

THE SEPARATOR IS THE DECLARED TYPE AND NOTHING ELSE, isolated over three probes because the first two diagnoses were WRONG. Not depth: a nested call ordinarily SUSPENDS (WI-20260826-VPEWK's documented remainder — the argument is sigma-walked, never reduced, so the bridge's ground check declines and the goal residualizes; sound, incomplete). Not genericity: `squish(gid(7)) = 7` with a GENERIC inner suspends like its non-generic twin, and a generic op FLAT reduces. Not the reflect family: the cleanest row uses TWO OF MY OWN operations, both non-generic, both host-mapped to reflect's own host functions, differing only in a type —

  operation mk(n: Int64) -> Term                  mapped "as_term"
  operation tsq(t: Term) -> Option[T = Int64]     mapped "term_as_int"
  operation sq(a: Int64) -> Int64                 mapped "int_abs"
  rule termNest(1) :- tsq(mk(7)) = some(7)   -> total 0  DECIDED FALSE   (eval: some(7))
  rule intNest(1)  :- sq(sq(7)) = 7          -> total 1  suspends, sound

SUSPECTED MECHANISM, stated as a hypothesis because it is not yet traced: AN UN-REDUCED CALL IS A TERM. `reduce_op_value` returns the outer call un-reduced when its argument is itself a call; `is_unreduced_op_call` should then make `eq` DELAY. Where the parameter is `Term`, something upstream accepts the un-reduced inner call as legitimate DATA instead — which is exactly the symbolic-algebra case that predicate's own comment is written around (`Set.insert(Set.empty(), 1)` must stay data), here producing a WRONG ANSWER rather than preserving one. So the fix is not simply widening the delay: the two readings collide precisely on `Term`, and telling them apart is the ticket.

WHY IT MATTERS: this is the WI-738 soundness floor missing for a shape that is now REACHABLE. WI-880 made the reflection accessors reduce in a rule body, so rules over terms are writable for the first time (proposal 008's first consumer, examples/guardians/lib/safety.anthill) — and a `Term` parameter is what every one of those accessors takes. The flat case is sound; composing two of them is not.

ACCEPTANCE: `tsq(mk(7)) = some(7)` and `term_as_int(as_term(7)) = some(7)` answer 1 as rule-body goals, OR suspend — either is sound, deciding FALSE is not; `not(...)` over each answers 0 (or suspends) rather than 1; `sq(sq(7)) = 7`'s suspension is unchanged; `:- Set.insert(Set.empty(), 1) = Set.insert(Set.empty(), 1)` still answers 1 AS DATA (the wi616 five, which is what any widening of the delay must not break); full workspace green via rustland/scripts/test.sh.

REFERENCE: the boundary is pinned in `wi880_reflect_mapping_test::the_two_remaining_boundaries` with both rows and the back-out measurement; docs/kernel-language.md 5.2 states it; `is_unreduced_op_call` / `reduce_op_value` (kb/resolve.rs). NEIGHBOURS, none of which own it: WI-20260826-VPEWK (the rule-body host arm, whose remainder is the SOUND suspension), WI-20260822-F0HHB (what `=` should mean in a rule body — `eq` never binds, so `= ?v` suspends separately), proposal 008 open question 1 (the arity-2 `extract_sort_ref` that succeeds without binding, a different mechanism at tier 3).

## Changes

### 2026-08-27T08:33:18Z — feedback — user

NEIGHBOUR, NOT A DUPLICATE — WI-20260827-XBHX3, filed the same day off /code-review on the VPEWK diff. Read both before touching either; they are two readings of one question and a fix for either could move the other.

DIFFERENT MECHANISM, different symptom. XBHX3 is `unfold_eq_operand`'s `value_has_bodied_op_call` gate on the WI-580 case-split path: the gate reads `HeadCheck::BodiedOpCall`, a host call has no body node, so a host call nested inside OTHER is invisible to it and the per-arm structural `unify` DROPS REAL SOLUTIONS (a completeness loss, unsound under NAF). This ticket is `reduce_op_value` / `is_unreduced_op_call`: no case-split is involved, the outer call COMMITS and the goal is decided FALSE (a wrong answer, not a dropped one).

THE SHARED ROOT, in XBHX3's own words: the gate "cannot currently distinguish 'un-reduced and will STAY un-reduced' from 'not yet reduced but reducible at this position'. Both present as the same `Expr::Apply`." That is this ticket's question one path over — and a `Term`-typed parameter is the case where the two readings genuinely collide, because an un-reduced call IS a term, so "is this data?" has a legitimate YES.

WHAT THIS TICKET CAN LEND IT: XBHX3 records "NOT DRIVEN -- I did not build a fixture with a host call nested inside a data structure in OTHER", and says constructing one is its first step. The three-operation fixture here (`mk`/`tsq`/`sq`, mapped to `as_term`/`term_as_int`/`int_abs`) is a driven nested-host-call shape with its own type-varying control, and is likely the cheapest starting point.

WHAT IT LENDS THIS ONE: XBHX3 MEASURED that the obvious widening (`op_body_node(f).is_some() || is_interpreter_mapped_op(f)`) is sound but costs completeness -- `rule bodiedFirst(?c) :- Colour.isRed(?c) = String.contains(\"abc\", \"b\")` goes 1 DEFINITE to 1 CONDITIONAL. So "just widen the delay" is already refuted on the neighbouring path, and its `bodiedFirst` row belongs in this ticket's control set too.

### 2026-08-27T09:03:55Z — feedback — user

RESOLVED BY WI-880 ITSELF, hours after filing, and the route there is the point: /code-review found that WI-880's reflect migration did not merely leave this gap standing, it MADE THE GAP WORSE — and fixing that regression fixed this ticket.

WHAT I HAD MISSED WHEN FILING. This ticket says the failure is 'pre-existing, measured 0 solutions both before and after'. That was measured on `= some(7)`, which is 0 on BOTH sides and therefore cannot see the change — the un-fired path and the wrong-value path agree there by accident, the same degenerate-witness trap this ticket's own text warns about for `not(... = some(8))`. The COMPLEMENTARY polarity separates: `:- term_as_int(as_term(7)) = none()` went from 0 to 1 DEFINITE, asserting a WRONG VALUE (the true answer is `some(7)`). The host function ran on the un-reduced CALL, found no `Const::Int`, and committed to `none()`.

THE FIX, in `reduce_op_value` (kb/resolve.rs): a HOST callee's ARGUMENTS are now REDUCED before the bridge, not merely sigma-walked. That is the root this ticket was circling — the mechanism paragraph guessed 'something upstream accepts the un-reduced inner call as legitimate DATA', which is right, and the repair is to not hand it one.

MEASURED, this ticket's own four rows, verbatim:
  termNest(1) :- tsq(mk(7)) = some(7)            -> 1 DEFINITE  (was total 0, decided false)
  ras(1)      :- term_as_int(as_term(7)) = some(7) -> 1 DEFINITE  (was total 0)
  bad(1)      :- not(term_as_int(as_term(7)) = some(7)) -> 0      (was 1 DEFINITE, unsound)
  intNest(1)  :- sq(sq(7)) = 7                   -> 1 DEFINITE  (was suspending)

ACCEPTANCE MET, with one clause EXCEEDED and it is worth stating rather than glossing: the acceptance asked that `sq(sq(7)) = 7`'s SUSPENSION be unchanged, as a guard against regressing the sound-but-incomplete case. It does not suspend any more — it reduces to a definite correct answer. That is strictly better and not a regression, but it is not what the clause asked for, so it is recorded as a difference rather than a pass.

BOTH GUARDS HELD, measured across the fix: `:- Set.insert(Set.empty(), 1) = Set.insert(Set.empty(), 1)` still answers 1 AS DATA (the wi616 five — those callees are mapped in no interpreter registry, so the argument recursion bails and leaves them alone), and the bodied-op-split row is unmoved. Full workspace 5597 passed / 0 failed.

SIDE EFFECT WORTH NAMING: this also closes WI-20260826-VPEWK's documented remainder ('a host call in a host call's ARGUMENT is not reduced'). `:- Bool.and(Bool.not(false), true) = true` went 0-with-a-residual to 1 DEFINITE; that file's `nest` rows now carry the flip.

STILL OPEN, and NOT this ticket's: the BINDING case. `term_as_int(7) = ?v` suspends because `eq` never binds — WI-20260822-F0HHB. And WI-20260827-XBHX3's `unfold_eq_operand` gate is untouched by this change; see the cross-link there.


## Attributes

- id: WI-20261105-8412E-a-dot-in-the-right-hand-side
- created: 2026-11-05T13:36:47Z

- status: Open
- status_agent: claude
- status_at: 2026-11-05T13:36:47Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A dot in the right-hand side of a typed-bound @[simp] equation is never dispatched: it reaches the resolver as a dot_apply term and stays data. MEASURED 2026-11-05 (WI-906 review, on 37ab6e68): sort Other { entity other(v: Int64); operation pure_m(o: Other) -> Int64 = 5; operation seven(o: Other) -> Int64 = 7 }; operation t(o: Other) -> Int64 = 0; rule t(?o: Other) <=> ?o.pure_m() @[simp]. The rule loads clean; kb.simplify(t(other(v: 2))) = dot_apply(receiver: other(v: 2), name: pure_m, args: nil) — pure_m never runs. WHY: the TYPER is what dispatches a dot (and what judges the effect of the call a dot reaches, WI-905), and it never fires an equation carrying a typed pattern bound (WI-582: simp_rewrite::try_fire skips bound-carrying rules); the RESOLVER fires it (fire_simp_equation enforces the bound) through instantiate_rhs_verbatim, which neither dispatches a dot nor expands a macro, so the dot is kept as a term. A SECOND SYMPTOM: a dot rule written OUTSIDE a sort, which fires at no dot call (the typer's enclosing-sort guard), rewrites that term — with rule dr: dot_apply(?e, pure_m) <=> Other.seven(?e) @[simp] beside the sort the result is seven(other(v: 2)); written inside the sort it did not fire (not investigated why). This is the row WI-20260926-7D48J recorded from WI-905 (2026-10-22) for @[unfold]; 7D48J was closed on 2026-11-05 reading the @[simp] spelling as refused at load, which holds for an unbounded equation and not for a bounded one. NOT MEASURED: an effectful member there (?o.risky() with effects Error[Boom]) — by the reasoning above the effect gate does not see it either. FIX, as 7D48J's row put it: a dot in an equation the resolver fires is either dispatched (and then held to the effect refusal) or refused at load; never kept as data. ACCEPTANCE: the program above either answers 5 for t(other(v: 2)) or is refused at load naming the dot; the effectful variant is refused by the effect gate; when the path is closed, simp_rewrite::is_typer_fired_dot_rule's doc and kernel-language §5.3's dot-rule sentence (which name this defect as the one dot_apply term the resolver meets) are updated; cargo-test green via scripts/test.sh.


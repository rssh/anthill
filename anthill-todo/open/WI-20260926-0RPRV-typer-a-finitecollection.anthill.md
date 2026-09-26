## Attributes

- id: WI-20260926-0RPRV-typer-a-finitecollection
- created: 2026-09-26T19:06:14Z

- status: Open
- status_agent: user
- status_at: 2026-09-26T19:06:14Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TYPER: a FiniteCollection member called on a carrier that provides NO FiniteCollection at all is refused for the WRONG reason — `FiniteCollection.size(n)` on a bare infinite `Nats` dies on an effect error, not on finiteness.

Found while delivering WI-20260829-H0YCE (whose fix does NOT reach this case). MEASURED on d84cd14, one fixture, `Nats` a hand-written sort that `provides Stream[T = Int64, E = {}]` and nothing else (the carrier `wi590_conditional_finiteness_test` uses), probe `operation probe(m: Nats) -> … = …`:

  FiniteCollection.collect(m)     REFUSED: probe.effects: undeclared effect ?_  AND  FiniteCollection.collect.requires: `requires FiniteCollection[…]` covering …
  FiniteCollection.size(m)        REFUSED: probe.effects: undeclared effect ?_   (ONLY)
  FiniteCollection.foldLeft(m,…)  REFUSED: same, ONLY the effect error
  FiniteCollection.foldRight(m,…) REFUSED: same, ONLY the effect error
  m.size() / m.collect()          REFUSED: no such member (dot dispatch) — correct

So the program is rejected, but by accident: the error names an unresolved access-effect var, and says nothing about `Nats` not being a FiniteCollection. Should the effect row ever get grounded some other way (a declared `effects E`, a future default), the call would LOAD and diverge — the same soundness hole H0YCE closed, one carrier shape over.

WHY, as far as reading goes (NOT TRACED): the defaulted-op arm in apply.rs only reaches its instance checks (`defaulted_call_at_non_instance`, and H0YCE's ground-NoMatch refusal) when a carrier is CLASSIFIED, and the carrier-param classifier recognizes a carrier only through a provision view — a carrier providing NOTHING is never classified. The `unclassified_goal_carrier` route (WI-883) is meant for exactly that, yet evidently does not fire here; possibly because the goal's `E` is the open var the effect error names, so the goal is not ground / the element is dropped. `collect` (body-less) additionally gets the `requires` refusal, the defaulted members do not.

ACCEPTANCE: `FiniteCollection.size` / `foldLeft` / `foldRight` on a bare `Nats` are refused with a diagnostic naming the missing provision (`Nats` does not provide `FiniteCollection`), as `collect` already partly is; the effect error, if it survives at all, is not the only one; a finite hand-written carrier (the `Fin` of wi590) still loads and evaluates under all four; rows in `wi590_conditional_finiteness_test` beside the defaulted_members_* ones, saying at the site which fail when the fix is backed out.


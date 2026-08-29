## Attributes

- id: WI-20260828-N2FHM-typer-a-field-dot-on-an
- created: 2026-08-28T19:52:33Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-29T06:58:40Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

typer: A FIELD DOT ON AN `Iterable.find` CALLBACK PARAMETER TYPE-CHECKS CLEAN AND DIES AT RUN TIME. `find(rows, lambda r -> r.flag)` loads with no diagnostic and then fails `Internal("unhandled Expr variant in eval: Discriminant(10)")` — `Expr::DotApply`, the un-desugared dot. The typer never resolved the projection to a field access, and the evaluator has no arm for the surviving node, so the failure is a HOST-LEVEL internal error rather than a type error at the site that could be repaired.

IT IS THE COMBINATOR, NOT LAMBDAS, and that contrast is what attributes it. MEASURED in `examples/guardians/lib/gate.anthill` (WI-20260824-5XBBQ), twice, at two independent call sites over `List[T = anthill.reflect.LayerSymbol]`:

  find(layer_symbols(l), lambda ls -> and(ls.minted, ls.symbol === s))   -- DIES at eval
  filterElems(layer_symbols(l), lambda ls -> not(is_agent_name(qualified_name(ls.symbol))))  -- CLEAN

Same list, same element sort, same field-dot shape, same lambda position. The difference is how each combinator reaches its element type: `List.filterElems` projects `xs.T` off its own receiver, while `Iterable.find` declares `pred: (x: Element) -> Bool` and a `List` reaches `Iterable` only TRANSITIVELY (`List provides Stream`, `Stream provides Iterable` — WI-495). So the suspicion is that `Element` is not grounded to `LayerSymbol` at the callback's binder, leaving the dot with no receiver type to resolve against.

THE WORKAROUND, and it is what shipped: destructure the parameter instead of dotting it — `lambda ls -> match ls case LayerSymbol(sym, m, _) -> and(m, sym === s)` — which needs no type to bind, and works. So `find` IS usable; only the dot is not. The gate uses `find` throughout and hand-rolls no recursion.

STILL REPRODUCES after WI-20260828-BH1JZ / EKWDC / 36a83f84 (carrier-argument projection through a transitive provision, carrier `requires` at the receiver, `requires` composed across a provider chain) — re-measured on that tree, which is why those three are named here rather than assumed to have covered it.

FIRST TASK IS A MINIMAL STANDALONE REPRO, because the measurement above rides on the reflect sorts and the guardians example, and neither belongs in a typer fixture. The shape to confirm, with no stdlib beyond List/Bool and no reflect at all — NOT YET RUN:

  sort dotfind.Row
    import anthill.prelude.{String, Bool}
    entity row(name: String, flag: Bool)
  end
  namespace dotfind
    import anthill.prelude.{List, Bool, Option}
    import anthill.prelude.Iterable.{find}
    import anthill.prelude.List.{filterElems}
    import dotfind.{Row}
    operation via_find(rows: List[T = Row]) -> Bool =
      match find(rows, lambda r -> r.flag)
        case some(_) -> true
        case none() -> false
    operation via_filter(rows: List[T = Row]) -> List[T = Row] =
      filterElems(rows, lambda r -> r.flag)
  end

If `via_find` dies and `via_filter` answers, the attribution is confirmed with nothing borrowed from the example. If BOTH die, the defect is broader than `find` and the ticket's headline is wrong — report that rather than narrowing the fixture until it agrees.

WHY IT MATTERS BEYOND ONE CALL SITE: `find` is the only search combinator on `Iterable`, `Iterable` is what every collection provides, and a record element is the ordinary case. Every such call site is a program that loads clean and fails when it runs. The repo's own rule is that a loud error beats a silent skip; this is the opposite of both — silent at load, and at run time an `Internal` the caller cannot catch, since it is not a `Raised` payload and no handler sees it.

ACCEPTANCE: the standalone repro above is a fixture in `rustland/anthill-core/tests/include/`, and `via_find` RESOLVES ITS DOT AND ANSWERS — asserting the value, not that it loads. CONTROL, in the same fixture: `via_filter` on the same list, which passes today and must keep passing, so the fixture measures the `find` path and not dots in general. State at the site which assertion fails when the change is backed out. Whether the fix belongs in the element grounding for a transitively-provided `Iterable` or in the dot desugaring is for the implementation to decide and record; if the dot cannot be resolved at that binder, then the honest fix is a LOAD-TIME REFUSAL naming the projection, never a surviving `DotApply` — an unresolved dot must not reach the evaluator either way. Full workspace green via rustland/scripts/test.sh.


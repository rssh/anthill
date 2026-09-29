## Attributes

- id: WI-20260929-0RP29-a-type-projection-nested-in-a
- created: 2026-09-29T20:15:58Z

- status: Open
- status_agent: user
- status_at: 2026-09-29T20:15:58Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A TYPE PROJECTION NESTED IN A RETURN TYPE THAT GROUNDS TO A TYPE HOLDING A VALUE IS REFUSED, AND THE WI-606 FALLBACK MASKS THE REFUSAL. With `xs: List[T = Buf[T = Int64, N = 3]]`: `List.splitFirst(xs)` and `xs.splitFirst()` are refused "type projection resolved to a non-term carrier, which is not yet supported" (typing/projection.rs ~1406-1416, and its rigid twin ~1393-1399), because the grounded element is a `Value::Node` and `rewrite_term_projections` cannot embed one mid-Term-tree; `match Stream.splitFirst(xs) case some(pair(b, _)) -> val(b)` with `val(b: Buf[T = Int64, N = 3])` is refused "expected Buf[T = Int64, N = 3], got xs.T" — `xs` being `List.splitFirst`'s OWN parameter: apply.rs's WI-606 fallback catches the projection error and build.rs `concrete_override_threaded` returns the override's return type with its projections uneliminated. Not stdlib-specific: `unboxOpt(b: Box) -> Option[T = b.T] = some(b.item)` over `x: Box[T = Buf[T = Int64, N = 3]]` is refused with the non-term-carrier error, while the top-level `unbox(b: Box) -> b.T` runs. Every `N = Bool` twin runs. MEASURED identically before and after WI-20260929-WBHTM (the dispatch itself now works: a match that does not use the element runs). FOUND by WI-20260929-WBHTM's /code-review (V8). FIX: at the two projection.rs sites lower the grounded occurrence (`node_occurrence::value_to_term`; minimal, but it interns per-site variables), or make `rewrite_term_projections` return a `Value` and rebuild a parent that receives an occurrence child through `parameterized_value` / `named_tuple_value`; and make the WI-606 fallback eliminate (or refuse) the override's own projections instead of masking the error. ACCEPTANCE: the three stdlib spellings and `unboxOpt` run over the value-in-type element as their `N = Bool` twins do; full workspace green via rustland/scripts/test.sh.


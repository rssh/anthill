## Attributes

- id: WI-20260825-X9RRN-a-qualified-spec-op-reached
- created: 2026-08-25T19:23:39Z

- status: Open
- status_agent: claude
- status_at: 2026-08-25T19:23:39Z

- acceptance: cargo-test

## Description

a QUALIFIED `Spec.op(...)` reached through a `provides` chain is 'unknown functor' — the member IMPORT works and the call does not, so proposal 004's source compatibility holds for only one of the two spellings

## Changes

### 2026-08-25T19:24:08Z — feedback — claude

PRE-EXISTING AND SHIPPED — WI-20260825-1WBZT only WIDENED the population, and the widening is what makes it worth a ticket. Measured on the delivered tree:

  operation same(a: Int64, b: Int64) -> Bool  = Eq.eq(a, b)         -> "type mismatch in Eq.eq.apply:
                                                                       expected known operation or arrow-typed
                                                                       variable, got unknown functor"
  operation q(a: Float, b: Float) -> Float    = Field.div(a, b)     -> same message
  operation plus(a: Int64, b: Int64) -> Int64 = Numeric.add(a, b)   -> same message   <- NEW under 1WBZT
  operation dbl(a: Float) -> Float            = Ring.add(a, a)      -> same message   <- NEW under 1WBZT
  operation dbl(a: Float) -> Float            = Additive.add(a, a)  -> LOADS

The last row is the separator: `add` exists, is backed, and answers — the failure is about the ADDRESS, not the operation. `Eq.eq` has been in this state since WI-1109/WI-1110 moved `eq` onto `PartialEq`, `Field.div` since WI-20260824-VT8CF moved `div` onto `Divisible`; 1WBZT moved `add`/`sub`/`mul`/`neg` onto `Additive`/`Multiplicative` and `Ring`'s five onto the same, so four more addresses joined.

A RULE BODY GIVES THE SAME VERDICT, and twice over — `rule twice(?x, ?y) :- ?y = Numeric.add(?x, ?x)` reports BOTH "rule-body term `Numeric.add` names nothing: no rule, fact, operation, entity, const or builtin is declared under that name" and the typer's "unknown functor".

THE OTHER SPELLING WORKS, which is what makes this a half-kept promise rather than a design. `import anthill.prelude.Numeric.{add, sub, mul, neg}` RESOLVES through the chain and every one of the ~43 corpus sites written that way still loads — measured, that import population is untouched by 1WBZT. `eq.anthill`'s own comment claims the general form: "Filed correctly it brings the scope with it (`Eq.eq` still resolves to the inherited `PartialEq.eq`, which proposal 004 wanted for source compatibility)". Half of that is true. The comment should say which half once this is settled.

AND A THIRD SPELLING WORKS, which localizes the mechanism: `anthill.prelude.algebra.VectorSpace` writes `Ring.sub(Ring.zero, Ring.one)` in a rule body and loads clean — because `VectorSpace` has `requires Ring[F]`, and a `requires` edge brings the target's scope (including what the target reached by `provides`). So the members ARE reachable through the chain; what is not reachable is the qualified `Spec.op` address from a scope that merely IMPORTS `Spec`. `by_qualified_name` has no `anthill.prelude.Numeric.add` entry any more, and the qualified-call path reads that rather than walking the provision.

NOT A SILENT DEFECT and the repair is one word (`Numeric.add` -> `Additive.add`), which is why 1WBZT did not absorb it — VT8CF did not absorb the `Field.div` instance either. WHAT TO DECIDE: whether the qualified form SHOULD walk the chain (then the fix is in the qualified-name path and the ladder doc §8.6 gains a rung), or whether it should not (then the message must stop saying "unknown functor" about a name that is defined, and name the declaring spec instead — the same complaint WI-944's second finding makes about "should be unreachable"). Do not leave it saying a defined name is unknown.

SUBJECT MOVED, RECORDED: `vec3_ops_test::control_ring_now_loads_and_its_residual_failure_is_the_unbacked_provision` was the row pinning `Ring.add`'s "loads, then dies at eval with 'operation has no body'". Under 1WBZT it is refused at LOAD instead, so that row was rewritten to assert the new verdict and to attribute it HERE rather than to WI-944's unbacked `fact Ring[Float]`.

### 2026-08-25T23:56:22Z — feedback — claude

THE CAUSE IS LOCATED, and it says why this is not a small patch — measured rather than predicted, after WI-20260825-N2865's sibling defect turned out to BE one.

`load::dotted_by_head` is a pure STRING JOIN with no scope walk at all:

    kb.symbols.by_qualified_name.get(&format!("{head_qualified}.{tail}")).copied()

So `Mid.b` asks for the literal key `probe.x92.Mid.b`. When `Mid` reaches `b` only through `provides Base[T = T]`, no such key exists and the path MISSES — there is no rung at which the provision chain could be consulted, which is why no narrowing or widening of an existing predicate reaches it.

REPRODUCED ON PURE USER SORTS, so it is not a property of the prelude:

  sort Base { sort T = ?  operation b(x: T) -> T = x }
  sort Mid  { sort T = ?  provides Base[T = T] }                    -- declares nothing
  sort User { operation viaMid(x: T) -> T = Mid.b(x) }
    -> "type mismatch in Mid.b.apply: expected known operation or arrow-typed variable,
        got unknown functor"

…with or without a `requires Mid[T]` on `User`. And the CONTROL that pins the axis: the same file with `Base.b` DECLARED on `Base` and reached as `Base.b(x)` loads clean through BOTH a `requires` and a `provides` — so `Sort.member` works; what fails is `Sort.member` where the member is the PROVISION'S.

WHY IT IS NOT INLINE, in one sentence: the fix is a NEW RUNG on the §8.6 ladder, and which rung is the decision this ticket exists to take. Three questions the patch cannot avoid answering, none of them settled anywhere today:

  * Does the fallback follow `provides` ONLY, or `requires` too? Following `requires` is wrong — `requires` means "I need one", not "I have one to offer under my name", and it is exactly the shadow `Polynom.add` already warns about. Following `provides` only is now MECHANICALLY AVAILABLE for the first time: WI-20260825-N2865 added `ImportOrigin::Provision` and `parent_edge_is_provision_only`, so the two edge kinds are finally distinguishable. That is the one thing this ticket got cheaper.
  * What happens when TWO provision paths reach two same-named members? `dotted_by_head` returns `Option<Symbol>` and has no ambiguity arm; a scope walk has one, and the two callers read the result differently.
  * `dotted_by_head`'s own doc records that head-qualification ALREADY over-hits (WI-751's field case). A scope-walking fallback widens it again, and my memory of this codebase is that narrowing or widening a shared resolver set serves one reader and breaks another (WI-1090, WI-1095, WI-1098).

SO THE CHEAP HALF IS THE OTHER ONE, and it needs no decision: the MESSAGE. "unknown functor" about `Eq.eq` / `Numeric.add` / `Field.div` is false — the operation exists, is backed, and answers under its declaring address. Whoever takes this should either add the rung or make the diagnostic name the declaring spec ("`Eq` reaches `eq` through `provides PartialEq`; write `PartialEq.eq`"), but not leave a defined name reported as unknown.


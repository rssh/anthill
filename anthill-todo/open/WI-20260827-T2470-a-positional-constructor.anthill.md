## Attributes

- id: WI-20260827-T2470-a-positional-constructor
- created: 2026-08-27T14:09:45Z

- status: Open
- status_agent: user
- status_at: 2026-08-27T14:09:45Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A POSITIONAL CONSTRUCTOR ARGUMENT IN AN OPERATION BODY BUILDS A VALUE THAT COMPARES UNEQUAL to the same constructor written anywhere else, so the operation silently answers NOTHING. Equality-independent, pre-existing, and it reaches the prelude: every `some(x)` in the stdlib is this shape.

MEASURED 2026-08-27 on the tree at b09aa9f1, isolated to ONE axis -- POSITIONAL vs NAMED constructor arguments inside an OPERATION BODY. The two rows differ in nothing else:

  enum test.pu3.MyEnum
    sort T = ?
    entity enone
    entity esome(value: T)
  end
  namespace test.pu3
    import anthill.prelude.{Int64, Option}
    import anthill.prelude.Option.{some}
    import test.pu3.MyEnum.{esome}
    sort C
      entity red
      operation ewrap (x: Int64) -> MyEnum[T = Int64] = esome(value: x)   -- NAMED
      operation ewrap2(x: Int64) -> MyEnum[T = Int64] = esome(x)          -- POSITIONAL
      operation owrapn(x: Int64) -> Option[T = Int64] = some(value: x)    -- NAMED
      operation olit  ()         -> Option[T = Int64] = some(1)           -- POSITIONAL
    end
    rule g1() :- C.ewrap(1)  = esome(value: 1)   -> true            NAMED body
    rule g2() :- C.ewrap2(1) = esome(value: 1)   -> no solutions    POSITIONAL body
    rule g4() :- C.owrapn(1) = some(value: 1)    -> true            NAMED body
    rule g5() :- C.olit()    = some(1)           -> no solutions    POSITIONAL body
    rule g6() :- some(1)     = some(1)           -> true            the CONTROL: positional
                                                                    on BOTH sides of a RULE
                                                                    body is fine
  end

`g6` is the control that puts the defect in the OPERATION BODY and not in the positional spelling: written in a rule body, `some(1)` is equal to itself. Only a value BUILT BY AN OPERATION BODY from positional arguments mismatches.

IT IS NOT ABOUT `Option`, NOT ABOUT `enum`, AND NOT ABOUT EQUALITY. Driven across four carriers, with `Int64` payloads and no `eq` override anywhere:
  `sort BoxI  entity boxi(v: Int64)`  named body   -> true
  `sort MyOptP[T] entity psome(value: T)` POSITIONAL body -> no solutions
  `enum MyEnum` (above)               both        -> named true, positional false
  `List` `cons(head: x, tail: nil)`   named body  -> true
So it is every entity constructor with at least one field, whatever the sort's kind or arity.

THE FAILURE IS A REFUTATION, NOT A SUSPENSION, so NAF over it concludes: a caller can prove `not(C.olit() = some(1))`.

ONE PLACE TO LOOK, stated as a hypothesis and NOT as a diagnosis -- I did not trace it. `unify_concrete` (rustland/anthill-core/src/kb/resolve.rs) fails fast on `pa != pb || na != nb`, i.e. a positional/named arity mismatch, before comparing anything. The PATTERN side of the same question already canonicalizes: `fresh_pattern_occ` (same file) says "Build a CANONICAL entity occurrence: positional sub-patterns map to the constructor's declaration field names, all args carried named + sorted (the system's canonical entity form)". The op-body constructor lowering appears not to do that mapping, so the built value stays `Fn{some, pos:[1], named:[]}` where every other producer has `Fn{some, pos:[], named:[value: 1]}`. Verify before fixing.

HOW IT WAS FOUND: while delivering WI-20260827-P1TPE. /code-review reported `C.gopt(?c, ae(k:1,tag:8)) = some(ae(k:1,tag:9))` answering 0 as a gap in that ticket's key; the `Int64` twin answers 0 too, and so does its GROUND twin, which took equality and the WI-580 unfold out of the picture entirely.

WHY NOTHING HAS FOUND IT: the workspace is green because the operation bodies that matter use NAMED arguments. The stdlib's own `Option.optionPure[A](a: A) -> Option[T = A] = some(a)` and `optionMap`'s `some(f(x))` are BOTH the broken spelling -- so `Monad[Option]`'s `pure` builds a value nothing can match. Whether any live path exercises it is the first thing this ticket should census.

ACCEPTANCE: the five rows above driven as a test, with `g2` and `g5` TRUE and `g6` still TRUE as the control; a census of positional constructor applications in operation bodies across stdlib/, examples/ and rustland/ with the count stated (the stdlib's `optionPure` / `optionMap` named explicitly, and whether either is reachable today); the NAF polarity asserted (`not(C.olit() = some(1))` must stop answering 1); the fix stated at the lowering site that owns the canonical entity form, beside `fresh_pattern_occ`'s note that the PATTERN side already does it; full workspace green via rustland/scripts/test.sh.

REFERENCE: `fresh_pattern_occ` and `unify_concrete` (rustland/anthill-core/src/kb/resolve.rs), `anf_flatten`'s `Expr::Constructor` arm, stdlib/anthill/prelude/option.anthill.


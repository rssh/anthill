## Attributes

- id: WI-20261126-GSTYS-a-simp-replacement-fired-by
- created: 2026-11-26T06:16:21Z

- status: Open
- status_agent: user
- status_at: 2026-11-26T06:16:21Z

- acceptance: cargo-test, scaland-sbt-test

## Description

a `@[simp]` replacement fired by the resolver in a rule body binds a const's or a nullary operation's NAME, not its value: over `f(?a) <=> seven @[simp]`, `?v <=> f(1)` binds `seven`, where an operation body's `f(1)` and the rule's own `?v <=> seven` give 7
WHO NEEDS IT. A rule that asks for the value of an operation a `@[simp]` equation defines, where the replacement names a const, a bare nullary operation, or a field read on one. The same rewrite, spliced into an operation body, gives the value.
WHAT HAPPENS. MEASURED 2026-11-26 on d87be1ccc with the anthill CLI, over `sort K { const seven: Int64 = 7; operation one() -> Int64 = 1; entity box(v: Int64); operation mk() -> box = box(v: 3) }` with `import …K.{seven, one, mk}`, `operation f(a: Int64) -> Int64`, `rule r: f(?a) <=> RHS @[simp]` and `operation g() -> Int64 = f(1)`. Columns: `?v <=> g()` | FIRED `?v <=> f(1)` | DIRECT `?v <=> RHS` | `?v <=> f(1) + 0`.
  seven:    7 | seven | 7 | ?_
  K.seven:  7 | seven | 7 | ?_
  one:      1 | one   | 1 | ?_
  mk.v:     3 | ?_    | 3 | ?_
  K.one:    1 | 1     | 1 | 1
  K.mk.v:   3 | 3     | field_access(field_access(K, mk), v) | 3
  K.one(), mk().v: 1 / 3 in every column.
Read, not verified: the resolver fires the stored head's replacement term, which is converted with ConstFold::Off so that an operation body it is spliced into folds the const itself (§5.9: "The subject and replacement of an equation clause head are rewrite sides, matched against and spliced into operation bodies, which keep the symbol"). Fired in a rule body, nothing folds the const, calls the bare nullary operation's name, or reads the field off it. K.one and K.mk.v answer because the resolver reduces a dotted chain.
WHY IT MATTERS. One rewrite gives two answers by where it fires, and the rule-body one is wrong with nothing refused: `f(1) + 0` has no value, and a goal comparing f(1) with 7 fails.
WHAT IS ASKED. A replacement fired by the resolver in a rule body reads its names as the same text in that rule's value slot reads them (the DIRECT column): a const its value, a bare nullary operation its call, a field read on one the field. Then a rule's f(1) and an operation body's f(1) agree. How (folded at fire, or a goal-folded replacement kept beside the stored one) is anthill's, and the stored head keeps the symbol for the splice into operation bodies. A name in a Term field of the replacement is not folded (WI-20261126-VKDX4).
DONE WHEN. Rows driving `?v <=> f(1)` and `?v <=> f(1) + 0` answer 7 / 7 / 1 / 3 for seven, K.seven, one, mk.v, as g() does; K.one, K.one(), K.mk.v and mk().v unmoved (controls); a const in a Term field of a fired replacement still finds the fact holding its name (control); each row's back-out measured at its site.
SEEN BESIDE, not this ticket's: written directly in a rule body, `?v <=> K.mk.v` binds `field_access(field_access(K, mk), v)`, where `K.mk().v` and the one-segment `mk.v` bind 3 (the DIRECT column above).


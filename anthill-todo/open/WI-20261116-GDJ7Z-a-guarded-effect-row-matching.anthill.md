## Attributes

- id: WI-20261116-GDJ7Z-a-guarded-effect-row-matching
- created: 2026-11-16T10:13:03Z

- status: Open
- status_agent: claude
- status_at: 2026-11-16T10:13:03Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A GUARDED EFFECT ROW MATCHING ITS CALLEE'S GUARD IS REFUSED OVER A CARRIER WITH ITS OWN eq. PROGRAM: sort Boom { entity Bang  provides Effect[T = Boom] }, sort Color { entity Red  entity Green  provides PartialEq[T = Color]  provides Eq[T = Color]  operation eq(a: Color, b: Color) -> Bool = true  operation risky(c: Color) -> Int64 effects { Boom :- eq(c, Red) } = 0 }, operation caller(c: Color) -> Int64 effects { Boom :- eq(c, Red) } = Color.risky(c). MEASURED on 7c63d768: refused, 'type mismatch in caller.effects: expected Boom only where eq(c, Red) holds, as the row declares Boom :- eq(c, Red), got the call of risky incurs Boom where nothing shows eq(c, Red)'. The same program with Color's structural equality (no `operation eq`) loads clean. Found in WI-20261105-CBRD2 part 5i; reading the caller's guard as typed did not change it; cause not found. WANTED: the caller's guard covers its callee's identical guard over either equality, as it does over the structural one. ACCEPTANCE: rows over both carriers; full workspace green via rustland/scripts/test.sh.


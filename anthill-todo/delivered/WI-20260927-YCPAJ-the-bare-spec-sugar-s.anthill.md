## Attributes

- id: WI-20260927-YCPAJ-the-bare-spec-sugar-s
- created: 2026-09-27T09:34:42Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-27T10:24:10Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

THE BARE-SPEC SUGAR'S SYNTHESIZED REQUIREMENT IS NOT CHECKED AT A CALL SITE. `operation useB(a: WIS, b: Spec2.B) -> Int64 = 1` records `requires Spec2[B = ?P]` (WI-201), and `useB(wis(n: 4), wis(n: 5))` LOADS CLEAN and runs although nothing provides `Spec2[B = WIS]` (the only provider is `Spec2[A = WIS, B = NoSp]`); with the body `Spec2.both(a, b)` it even answers 9, dispatching to the NoSp provider with a WIS argument. The same through an alias (`b: S2A.B` over `sort S2A = Spec2[A = WIS]`, requiring `Spec2[A = WIS, B = ?P]`). The explicit spelling `[P](b: P) requires Spec2[B = P]` is the control to compare against (WI-20260921-3G1YT says a declared requires is owed by the caller). Found delivering WI-20260924-SNJPR, measured on its tree. ACCEPTANCE: a call whose synthesized requirement no provider meets is refused, as the explicit spelling is; the sugar spelling driven beside the explicit one; full workspace green via rustland/scripts/test.sh.


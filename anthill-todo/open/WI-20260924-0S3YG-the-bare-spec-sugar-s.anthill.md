## Attributes

- id: WI-20260924-0S3YG-the-bare-spec-sugar-s
- created: 2026-09-24T07:50:38Z

- status: Open
- status_agent: user
- status_at: 2026-09-24T07:50:38Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

THE BARE-SPEC SUGAR'S SYNTHESIZED `requires` IS NOT HELD TO THE CALL-SITE CHECK THE EXPLICIT ONE IS: the program loads and dies at run time. `operation usePeek(s: Store.State) -> Bool = Store.peek(s)` (WI-201: a fresh `?P` plus a synthesized `requires Store[State = ?P]`), called as `usePeek(l)` with `l: List[T = NoSp]` where the only provider is `Box provides Store[State = List[T = E]] :- Special[T = E]` and `NoSp` provides no `Special`, LOADS CLEAN, and running it fails `DeferToRequirement: requirement param __req_store not bound in caller frame`. The same program spelled `usePeek[P](s: P) -> Bool requires Store[State = P]` is refused at load: 'requirement Store[State = List[T = NoSp]] cannot be supplied for call to usePeek'. FOUND by WI-20260923-ZBWMC's review (verifier V3, its programs g1/g2/g3); PRE-EXISTING, the same on the 09-20 binary. Where to look: the synthesized clause is rebuilt from `BareSpecSugar::minted` at the drain in `load_operation` (load.rs); whatever the call-site supply check reads for an explicit `requires` has to see that clause the same way. The sugar is WI-201's promise to typecheck IDENTICALLY to the explicit form, so any difference is the bug. ACCEPTANCE: the sugar spelling refused at load exactly as the explicit one, driven by a test with both spellings, plus a control whose caller does supply the requirement and runs; full workspace green via rustland/scripts/test.sh.


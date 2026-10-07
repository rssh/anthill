## Attributes

- id: WI-20261006-GVGSQ-a-member-the-signature-does
- created: 2026-10-06T09:02:46Z

- status: Delivered
- status_agent: codex
- status_at: 2026-10-07T10:16:31Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

A MEMBER THE SIGNATURE DOES NOT NAME IS A FREE VARIABLE IN THE BODY, WHERE §5.4 SAYS IT IS THE INSTANCE'S. `operation f(x: Tagger.C) -> Int64 = Tagger.out(x)`, over `sort Tagger { sort C = ?  sort Out = ?  operation out(self: C) -> Out  operation useOut(self: C, o: Out) -> Int64 }` and `sort B { entity b(n: Int64)  provides Tagger[C = B, Out = String]  operation out(self: B) -> String = "s"  operation useOut(self: B, o: String) -> Int64 = 3 }`: LOADS, and `f(b(n: 1))`, declared `-> Int64`, returns "s" (MEASURED on 149b44b3 and on the tree that delivers WI-20261006-XQGEW; found while delivering it). The signature requires `Tagger[C = P]` and says nothing of `Out`; the call is typed at the spec's own variable for `Out`, which the scope's clause does not bind (`scope_clause_at_carrier` hands a call the bindings the clause writes and nothing for the ones it leaves), and the declared return type then binds it. CONTROL, the member named: `h(x: Tagger.C, o: Tagger.Out) -> Int64 = Tagger.out(x)` is refused "expected Int64, got Tagger.Out". THE SAME VARIABLE IS WHAT AN EFFECT DIAGNOSTIC PRINTS AS `?_`: `both(x: Tagger.C, y: Other.C) -> Int64 effects {Tagger.E} = Tagger.tag(x) + Other.oth(y)` is refused "expected declared: [Tagger.E], got undeclared effect: ?_" — the row's member `Other.E`, not printed as one. That line was WI-20261006-XQGEW's acceptance and is moved here (user, 2026-10-06): naming it at the message alone would be a guess at which instance an unbound variable came from — with a second requirement of the spec in scope (`f[T](x: Tagger.C, y: T) effects {Tagger.E} requires Tagger[C = T]`) the undeclared effect is the other instance's `E`, and would print as the declared one's. EXPECTED: in a body, a member of a spec the scope requires and its clause does not name is an unknown of that clause's instance — the same at every call through the clause, conforming to no other type — and prints as `Spec.Member` where the clause is the signature's own. ACCEPTANCE: `f` is refused at load, "expected Int64, got Tagger.Out"; `k(x: Tagger.C) -> Int64 = Tagger.useOut(x, Tagger.out(x))` loads and `k(b(n: 1))` answers 3, as today; `both` is refused naming `Tagger.E` as declared and `Other.E` as undeclared; the standard library and the examples load, a body that leans on the free reading being found by the full run and repaired or reported; full workspace green via rustland/scripts/test.sh. REFERENCE: kernel-language §5.4 ("A member the signature does not name is that instance's all the same"); `scope_clause_at_carrier` (rustland/anthill-core/src/kb/typing/carrier.rs); WI-20261005-KSSA4; WI-20261006-XQGEW (a parameter printed as `Spec.Member` is one whose NAME was minted by `KnowledgeBase::mint_member_param_name`; a variable carrying such a name prints as the member wherever it is shown, with no other change).

## Changes

### 2026-10-07T10:16:29Z — feedback — codex

Implemented GVGSQ: omitted members of a licensed requirement are rigid unknowns of that instance, cached in the body environment and shared across calls and environment clones. Declared result types cannot choose those members, and different carriers retain distinct identities. Signature-instance diagnostics preserve Spec.Member (including aliases); explicit second instances and requirements over another specs carrier print their own instance. Explicitly written clause bindings retain their existing handling. Added nine regression/control tests and strengthened XQGEW to require Other.E in the undeclared-effect diagnostic. Back-out measurement on the initial eight tests: four regressions fail, four controls pass (named-member refusal and three executing same-instance forms). Removing the final naming guard fails the foreign-carrier regression, reporting Other.Out instead of Tagger[C = Other.C].Out. Full Rust workspace via rustland/scripts/test.sh: 8739 passed, 0 failed, 14 ignored. Scala sbt testFull: 600 passed, 0 failed. Standard library and example integration tests green; no dependent bodies required repair. Manual code review and git diff --check passed; /code-review skill unavailable and not run. No canonical specification changes. Open unblocked queue: 165 after claim.


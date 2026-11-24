## Attributes

- id: WI-20261113-FCMJA-proposal-074-stage-6-x-t-read
- created: 2026-11-13T23:01:52Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-24T19:38:16Z

- acceptance: cargo-test

- depends_on: WI-20261113-2KSAA-proposal-074-stage-1

- tags: proposal-074

## Description

PROPOSAL 074 STAGE 6 — `X.T` READ AS A VALUE IS 065'S DISPATCH (docs/proposals/074-typeclass-instance-is-a-dictionary.md §5, decided with the user 2026-11-13) (§3; T10). In value position `x.T` is `TypeValue.type_value[T = x.T]()`, as a type parameter is: under `requires TypeValue[x.T]`, `tOf(x: Additive) -> Type requires TypeValue[x.T] = x.T` answers `Int64` and `Float`; without the clause it is refused at load, naming the clause to add, as for `X`, over `Num` as well (it loads today). Where `x`'s spec states `requires TypeValue[T = T]`, the clause is supplied from `x`'s dictionary, and the list of T10 answers `[Int64, Float]` (refused today at `map(tOf)`); over `Additive` that `map` is refused. Depends on stage 1, whose spelling its rows write. Spec: §8.2 and proposal 065's rule, which today name a type parameter only. Spec text written with the stage and agreed with the user before it is committed. ACCEPTANCE: each row driven to its value (a load is no evidence); each part backed out by a temporary switch and the failing rows named; full workspace green via rustland/scripts/test.sh; scripts/families.sh green on both carriers; scaland sbt testFull green.

## Changes

### 2026-11-24T19:38:11Z — feedback — user

DECISIONS (2026-11-24, with the user). Measured first: x.T read as a value refused 'the receiver's type leaves it open here, so it is no type value'; the spelled TypeValue.type_value[T = x.T]() answered over Additive; over Num a direct call of tOf under the clause refused since stage 9 as two handed providers (x and the clause), the map refused 'cannot be supplied for tOf used as a function value', and tOf with no clause loaded. Decided: an open member read as a value off a lambda's binder, a let or match binder or a field path is refused, pointing to an operation that takes the value as a parameter and writes the clause (lambda (y: Num) -> TypeValue.type_value[T = y.T]() answered before through y's provider). The kernel-language text is written around a whole program, with positional type arguments where a sort has one parameter; 'a call site supplies nothing' reworded as which providers each call passes (the user).

### 2026-11-24T19:38:13Z — feedback — user

DELIVERED (2026-11-24, abe28d41c): x.T in value position is TypeValue.type_value[T = x.T](), and X where the receiver's type writes a type parameter; a clause at a parameter's own member that its provider holds through its chain is taken from that provider, for any spec (same(o: Ord) requires PartialEq[o.T] answers (true, false)), a named clause excepted; the clause is written, not inferred, refused naming it, over Num too. Acceptance: rows driven (wi_fcmja_member_type_value_test, 17: T10 (Int64, Float) and [Int64, Float], the Additive map refused, the refusals naming the clause, X under Num[X], a fixed member, lambda / let / field-path refusals, kernel-language 8.2's program as written); 3 parts backed out by a temporary switch over all of anthill-core (control 11640 / 0; 11, 6 and 3 rows failing, ledger in the test file; one part-1 run died SIGSEGV once and did not repeat); /code-review (xhigh) 8 findings, 3 fixed (a named clause dropped with its binder left unbound, a let read at its value's type, a doubled call), 5 skipped and recorded in proposal 074. Gate 12724 / 0; families green on both carriers; scaland testFull 811 + 51 (2 skipped) + 1. kernel-language 8.2 and 5.4, proposals 065 and 074, agreed with the user.


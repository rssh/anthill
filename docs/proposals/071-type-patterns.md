# 071: `TypePattern[T]` — a boundary catches by a type pattern, and a raise carries its type

## Status: Draft (2026-10-16). Decided in discussion on WI-20260908-9WVT7's third review: `ErrorTag` is retired; the boundary's evidence is a new spec named `TypePattern`, with one operation `admits(t: Type) -> Bool`; `TypeValue provides TypePattern[T = T]` (a provision, not a refinement); a raise carries the `TypeValue` of its payload's static type. Taken as this proposal's reading, from the same discussion: dispatch is by type pattern, and how a platform computes it is that platform's own (§3); neither spec takes a program-written row. Stage (a) is done (2026-10-17): 065 and 027.4 carry status lines naming what this proposal amends, and WI-20260911-3MV2C a note that stage (d) delivers it. Stage (b) is done (2026-10-20): `TypePattern`, its one row with `admits` in the `where` block, and the test `anthill.reflect.type_admits` (`kb/typing/type_pattern.rs`); a written `provides TypePattern[…]` is refused at load. The row is written on a sort of its own, `anthill.reflect.TypeValuePattern`, and not on `TypeValue` as §1.2 first wrote it (user, 2026-10-20): `TypeValue` is provided by every sort, so a member in a `where` block of its provision was read as an operation every sort has, and the row's condition `TypeValue[T = T]`, naming the sort it is written on, was stored as `TypeValue` with `T` left out. It is still one row over `TypeValue`'s family. With it came three repairs, each to a rule an existing section states: a type argument written `?` in an operation body is left out where the type value is typed; a sort's own operation named `type_value` no longer answers `TypeValue.type_value`; and a call at a type with an open slot is refused at load. Decided with the user for the test (2026-10-20): `anthill.reflect.type_admits` is a public reflect operation; an argument left out on either side admits; a sort that refines the pattern's through `requires` is each instance its clauses give it, its own arguments put for the parameters a clause names; an arrow is compared as the `Function` it is; and the refusal of a call at an open slot is the rule until stage (e) builds pattern evidence there. Stage (c) is done (2026-10-23, WI-20261016-YM8HD): `Error.reify` requires `TypePattern[T = T1]`, and the boundary keeps that dictionary and asks its `admits` of the raised value's head sort (`Interpreter::boundary_admits`); `ErrorTag`, `Error`'s row of it, `is_error_tag_spec` and the gates that read it are gone. Two readings were settled with it. A rule-body call that builds no pattern evidence is refused by the rule-body gate every spec with a member gets (`kernel-language.md` §8.7), and a tuple payload there gets the structural former's refusal, as in an operation body. And the bridge keeps no absence marker for an unpinned slot, §2's last sentence notwithstanding (user, 2026-10-23): that marker was the `ErrorTag` gate's, and without it the slot is unfilled and the boundary refuses to run with no evidence, naming the two routes that hand none — a rule's arguments that do not pin the payload among them — where the marker named the operation whose parameter was not pinned. Either way the call is refused before its thunk runs; only the account differs. A boundary handed a dictionary that is no `TypePattern` instance — the stand-in a host entry seeds for a sort-level `requires` — is refused there too, before its thunk runs. Stage (d) is done (2026-10-24, WI-20261016-5CDN5): `Error.raise` requires `TypeValue[T = T]`, the raised error carries that dictionary (`RaisedType::Evidence`), and the boundary asks its pattern about the type the dictionary names, built at the first boundary that asks — open question 4, answered so with the user — rather than at the raise. Decided with the user for it (2026-10-24), revising §1.3's host-raiser sentence: a raise's type is THREADED, never read off its payload. A raising host operation declares `requires TypeValue[T = X]` for its `Error[X]` and raises with the dictionary its call is handed, a builtin being handed its whole requirement channel; a load rule refuses a `@[host_implemented]` operation whose row raises a written `Error[X]` without the clause, or more than one. A host operation whose row says only `Error` — `Error[T = ?]` — needs none, and what its host function raises carries the unknown type (WI-20260910-6ARRN's): only a boundary whose pattern is `?` catches it, `TypePattern[T = ?]` admitting every type, and every other boundary lets it pass outward. No boundary has that pattern until stage (e) builds pattern evidence at an open slot. A host operation that writes `Error[T = ?]` out was refused at load (user, 2026-10-24): the typer let a boundary at a specific type discharge that label, where it refused the bare `Error` it means, so the host function's raise would have passed a boundary the typer counted on. The difference is gone (2026-10-24, WI-20261024-DK83Q, the user's rule that an identical substitution is not written): a `?` at a slot that declares no default is that slot left out in every written type, an effect label included, so `Error[T = ?]` and `Error[?]` are `Error`, and the refusal went with it. A payload the runtime raises with no operation behind the raise — `MatchFailed`, `RelationFloundered`, `ResolveStreamFailure` at a pull — carries its sort's evidence, a constant the evaluator resolves and checks once at start. With it came one repair of the resolver's fold: a callee that reads a requirement slot is not bridged on an argument still a call (`Result.reflect(Error.reify(…))` in a folded body ran `Result.reflect` on the `reify` term). Stage (e) is not implemented.

## Amends: [055](055-types-in-value-position.md) §2 (`?` in a type in an operation body is an argument left out, so `List[T = ?]` is `List`), §7 (`type_admits` is the reflect operation for type-language matching it anticipated) — recorded on 055's status line; [065](065-type-value-requirement.md) §2 (`TypePattern` has one row, over `TypeValue`'s instances; its rule that every instance is derived now covers both specs), [027.4](027.4-error-effect-reify.md) (the boundary's evidence, and the tag continuum's choice: point 3, a ground type term on the raise and a pattern on the boundary). In `docs/kernel-language.md`: the `ErrorTag` paragraph of §8.7, the sentence of §5.4's structural-former paragraph that names `ErrorTag`, and the data of `stdlib/anthill/prelude/effects.anthill`'s `reify` comment.

## Relates to: [066](066-provision-member-blocks.md) (a provision's `where` block, which is what lets `TypePattern`'s one row read `T` as a value), [070](070-self-and-fresh-bare-sorts.md) (the open slot, `kernel-language.md` §5.4), WI-20260911-3MV2C (a boundary blind to type arguments — delivered by stage (d)), WI-20261015-D2KZ5 (what an unwritten `T1` binds — open question 1), WI-20260921-28TAT (which introduced `ErrorTag`), WI-20260908-9WVT7 (whose review found that a written `ErrorTag` row stops the boundary: finding F1).

## Tracked by: tickets tagged `proposal-071`, one per stage (§4): WI-20261016-Y1EZJ (a), WI-20261016-SQZPQ (b), WI-20261016-YM8HD (c), WI-20261016-5CDN5 (d), WI-20261016-BDVYW (e).

## The problem

`Error.reify` requires `ErrorTag[T = T1]`, and `ErrorTag` declares no operation. The one row that supplies it is `Error provides ErrorTag[T = T] :- TypeValue[T = T]`, and the boundary reads the payload's sort out of that row's condition evidence, by position (`dict.sub(reify_payload_sub).impl_sort()`). It uses no API of the spec it requires. Three things follow, each measured on 2026-10-16:

- **Another provider means nothing to it.** `sort Wrapper … provides ErrorTag[T = Boom]` is more specific than `Error`'s row, so it is selected, and its dictionary has no `TypeValue` inside: every `Error.reify` at `Boom` dies at run time. With a condition, `provides ErrorTag[T = (a: Int64, b: String)] :- TypeValue[T = Other]` puts `Other`'s evidence where the boundary reads the payload, and the tuple's boundary catches `other(n: 7)` (exit 11, where 22 is right).
- **The raised side carries no type.** A raise throws the bare value, and the boundary reads the value's sort off its constructor. A constructor does not record the type arguments it was built at, so a boundary at `Boom[Reason = String]` that declares `Error[Boom[Reason = Int64]]` as escaping still catches `boom(5)`: `narrowR(1)` answers `"inner"` where `"outer"` is right. This is WI-20260911-3MV2C.
- **A catch over type arguments cannot be written.** `caughtWide(n) -> Result[E = Boom, T = Int64] = Error.reify(lambda () -> both(n))` over a thunk raising `Boom[Reason = String]` and `Boom[Reason = Int64]` is refused at load ("undeclared effect: `Error[T = Boom[Reason = Int64]]`"): `T1` binds to one label, and the other is never discharged.

`TypeValue` alone is not the repair. It has no instance at an open slot, and that is correct, since `type_value()` must answer one type: measured, `tyOf(none())` over `tyOf[B](x: B) -> Type requires TypeValue[T = B]` is refused at load, while a ground `tyOf(boom("s"))` answers `Boom(Reason: String)` and a rigid one forwarded by its caller answers `Boom(Reason: Int64)`. A raise always has a type; a boundary may be a pattern.

## 1. The rule

### 1.1 `TypePattern`

```anthill
sort anthill.reflect.TypePattern          -- beside TypeValue
  sort T = ?                              -- a type, which may have open slots
  operation admits(t: Type) -> Bool       -- does `t` fit: is it a subtype of an instance of `T`
end
```

`TypePattern[T = Boom[Reason = ?]]` admits `Boom[Reason = String]` and `Boom[Reason = Int64]`; `TypePattern[T = Boom[Reason = String]]` admits the first alone; a pattern at a sort admits its subsorts (`sort FileNotFound requires IoError`: a pattern at `IoError` admits `FileNotFound`).

### 1.2 Its one row, over `TypeValue`'s family

```anthill
sort anthill.reflect.TypeValuePattern     -- a sort of its own
  sort T = ?
  provides TypePattern[T = T] :- TypeValue[T = T] where
    operation admits(t: Type) -> Bool = type_admits(T, t)   -- `t` is a subtype of `T`, `T` read as a value (§1.5)
  end
end
```

One derived family, as today, and one row over it: a type with no open slot is a pattern that admits its subtypes. The member reads `T` as a value under the row's own condition, which 066's `where` block puts in its scope. Measured on a program-level stand-in (`sort Mark { sort T = ? ; provides Tag[T = T] :- TypeValue[T = T] where operation tag() -> Type = T end }`): a generic caller dispatching through the slot answers `Boom`; the same member outside the block is refused, nothing putting `TypeValue[T = T]` in its scope, and with its own `requires TypeValue[T = T]` it is refused as strengthening the spec's precondition.

The row is not written on `TypeValue` itself (user, 2026-10-20). Every sort provides `TypeValue`, so a member in a `where` block of `TypeValue`'s provision was read as an operation of every sort: measured, `Club.check(1)` over `sort Club { …; operation admits(t: Type) -> Bool = false; operation check(n: Int64) -> Bool = admits[T = Int64](Int64) }` answered `true`, `TypeValue.admits` running in `Club`'s place. And the condition `TypeValue[T = T]`, naming the sort it is written on, is stored as `TypeValue` with `T` left out, so no goal of `TypePattern` resolved until a reader was patched, and a patch in one reader left `f[P, Q](t) requires TypeValue[T = P] = TypeValue.admits[T = Q](t)` answering with `P`'s evidence.

Neither spec takes a program-written row: a written `provides TypeValue[…]` is refused today (065 §2), and a written `provides TypePattern[…]` is refused the same way. A forged `admits` would make a boundary typed at `Boom` deliver an `Other` inside `Result[E = Boom, …]`, or let a `Boom` escape an operation whose row no longer holds `Error[Boom]`.

### 1.3 A raise carries its type

```anthill
operation raise(error: T) -> Nothing effects Error[T] requires TypeValue[T = T] @[host_implemented]
```

The typer knows each raise's payload type: `Error.raise(box(v: "s"))` is `Error[Box[V = String]]`. A monomorphic raise's evidence is resolved statically; a generic raiser states it, `raiseAt[P](p: P) requires TypeValue[T = P] = Error.raise(p)`, as 065 requires of any reader. A host raiser (`division_by_zero`, `match_failed`, `evaluation_failure`, …) builds the payload of a sort it knows and supplies that sort's derived evidence. The raised error travels with the evidence. (Revised in stage (d), with the user, 2026-10-24 — the status line has it: a host OPERATION that raises requires that evidence, threaded by its caller; only a raise with no operation behind it carries a constant; a bare `Error` row's raise carries a type not known.)

A raise at a tuple or an arrow payload, or at a sort holding one among its type arguments, has no `TypeValue` (065 §2: structural formers have no instance yet, and a sort's holds only where each type argument has one) and is refused at load. Census, 2026-10-16: no such `Error[…]` label in `stdlib/`, `rustland/anthill-stl/anthill/`, `examples/` or anthill-todo; seven in three test files, all fixtures of the former refusals themselves: six at a tuple, and one at `Option[T = (a: Int64, b: String)]` (`wi_n31xx_type_value_read_rule_test`, `raisesOpt`).

### 1.4 A boundary catches by its pattern

```anthill
operation reify[Rho, X, T1](body: () -> X @ {Error[T1], Rho}) -> Result[E = T1, T = X]
  effects {Rho} requires TypePattern[T = T1]
```

A raise reaching a boundary is caught when the boundary's `TypePattern[T = T1].admits` answers yes for the raised type — the `type_value()` of the evidence the raise carries. The boundary calls the API of what it requires; it reads no dictionary by position.

### 1.5 One subtype test

`admits` and the typer's discharge of an `Error` label are one predicate over two type terms, so the row and the run cannot disagree: the label `Error[Boom[Reason = Int64]]` is discharged by a boundary at `T1` exactly when `TypePattern[T = T1]` admits `Boom[Reason = Int64]`. Today the two are separate and already differ (`payload_matches` reads `sort_sym_compatible` on head sorts; the discharge reads `labels_match_by_subsumption`, exact on type arguments, with variance from the declared `Covariant` facts). The predicate is carrier-neutral — a `TermView` on both sides, as 3MV2C's 2026-09-18 note asks — and an open slot admits every type.

### 1.6 Pattern evidence at an open slot

`TypePattern`'s one row answers every pattern without an open slot. A pattern with one (`Boom[Reason = ?]`) is built by the typer from `T1`'s term at the call: an open slot is a wildcard, a rigid parameter `P` inside it takes the caller's evidence for `P`, and a sort application takes its derived instance. It is not found by instance search: a goal with an unbound slot matches every instance.

## 2. What does not change

- What `Error.reify` returns, and how a monomorphic call at a ground sort reads: its evidence is resolved statically, as today.
- The rule-body route: a rule-body call whose pattern evidence it cannot build is refused at load, as a rule-body call whose `ErrorTag` slot it could not fill was, and a slot the bridge cannot pin reaches the boundary unfilled, which refuses to run (stage (c) dropped the bridge's absence marker for it; see the status line).
- Covariance: `Error`'s payload stays `Covariant`, and a boundary at a sort catches its subsorts.
- `TypeValue`'s other readers: it still answers one type, without holes.

## 3. How a platform computes it

The semantics is §1: catch by type pattern, with the raised type travelling. A platform may compute it as it likes, provided it agrees. A whole-program translator to C knows every raised type and every boundary's pattern, so `TypeValue` becomes a static tag per type and `admits` a precomputed table — or, over a tree-shaped sort hierarchy numbered depth-first, a range check on the tag — in which a wildcard slot is simply not compared. Such a target may refuse the general `type_value() -> Type`, which needs type terms at run time, and still raise and catch. What a platform chooses is the representation, never which raises a boundary catches.

## 4. Stages

Each stage leaves the whole suite green, and its rows say which back-out fails them.

- **(a)** This proposal; status lines on 065 and 027.4; a note on WI-20260911-3MV2C that stage (d) delivers it.
- **(b)** `TypePattern` and its one row, `TypeValuePattern provides TypePattern[T = T] :- TypeValue[T = T]`, with `admits` over the one predicate of §1.5 (its run-time half). Nothing reads it yet: behaviour-neutral elsewhere.
- **(c)** `reify … requires TypePattern[T = T1]`, and the boundary calls `admits` — with the raised value's head sort as its type until (d), so every verdict is unchanged. `ErrorTag` is retired with it: the spec, `Error`'s row, `is_error_tag_spec` and every gate that reads it, `ErrorLayer`'s positional sub read, and WI-20260908-9WVT7's finding F1.
- **(d)** `raise … requires TypeValue[T = T]`: the raised error carries its type, and the boundary admits by full type. Generic raisers state the clause; host raisers supply their payload sort's evidence; a raise at a former is refused at load, and the three test files' tuple rows move from the reify to the raise. Delivers 3MV2C.
- **(e)** The typer's discharge reads the same predicate, and the typer builds pattern evidence at an open slot (§1.6): `caughtWide` loads and catches both labels.

(b) before (c), (c) before (d); (e) needs (b), and (d) for the run to agree with the row.

## 5. Acceptance

- `admits`: a pattern at `Boom[Reason = ?]` admits both instantiations; a pattern at `Boom[Reason = String]` admits that one alone; a pattern at `IoError` admits `FileNotFound`.
- 3MV2C's rows: nested boundaries at `Box[V = Int64]` (inner) and `Box[V = String]` (outer) answer through the outer one for a `Box[V = String]` raise and the inner one for a `Box[V = Int64]` raise; the two-distinct-sorts row passes either way.
- `narrowR(1)` answers `"outer"` (today `"inner"`); `caughtWide` loads, and catches `boom("s")` and `boom(5)` (today refused).
- A written `provides TypePattern[…]` is refused at load; `ErrorTag` no longer exists.
- A raise at a tuple payload is refused at load, naming the former.
- A host raise is caught as before: `1 / 0` inside a reify at `DivisionByZero`.
- WI-20260908-9WVT7's rule-body reify rows keep their verdicts.
- The full workspace is green via `rustland/scripts/test.sh`, and scaland via `sbt testFull`.

## 6. Considered and not taken

- **`ErrorTag` with `tag() -> Type`.** Any answer other than exactly `T` breaks the result type or the discharge, and a boundary cannot check the answer against `T1`, since `tag()` is how it would learn `T1`.
- **A provider that adopts other payloads into its sort** (Haskell's `fromException`: `timeout(…)` caught as `httpError(504)`). It replaces the payload, and the information with it.
- **`check[B](err: B) -> Option[T] requires TypeValue[T = B]` on `ErrorTag`.** It keeps the dependence on run-time types it was meant to remove, and `Option[T]` admits the adoption above.
- **An injection/projection pair over a platform's representation of an in-flight error.** Kept as §3's reading — how a platform may compute this proposal's semantics — rather than as a surface a program writes.
- **`TypeValue` on both sides.** No catch over type arguments: `TypeValue` has no instance at an open slot (measured above).
- **`TypeValue` with holes.** It would hand a type with holes to readers that assume one type (`facts_of`, the code generators).
- **`TypeValue requires TypePattern[T = T]`** (a refinement). Two derived families where one row over one family does (user, 2026-10-16).
- **Retiring `ErrorTag` for `TypeValue` alone** (raise and reify both requiring `TypeValue`). It loses the open-slot catch, for the reason above.

## 7. Open questions

1. **An unwritten `T1` over several labels** (WI-20261015-D2KZ5). Today it binds the first label that pairs. With patterns it could bind the pattern that admits them all (`Boom[Reason = ?]` over the two `Boom`s), and refuse where no one sort heads them.
2. **An open slot under a covariant parameter.** `kernel-language.md` §5.4 makes `let o = none()` an `Option[T = Nothing]`. A boundary's `T1` is read as a pattern there, admitting every `Option` — to be confirmed against that rule, which is about a bound name's type, not a boundary's.
3. **`Nothing`'s `TypeValue`.** A raise of `none()` typed `Option[T = Nothing]` needs one.
4. **The raised type's representation on the interpreter.** Build the `Type` at the raise (a term per raise, on the error path), or carry the evidence and build it at the first boundary that asks. *Answered in stage (d) (user, 2026-10-24): the evidence is carried, and the `Type` built only where some boundary is on the stack — once per run the raise crosses.*
5. **A catch whose pattern is written at the call** (user, 2026-10-23). `reify`'s pattern is not written: it is `T1`, inferred from the thunk's row, and its evidence is found from `T1`'s type. Where nothing fixes `T1` — a rule body whose thunk raises a rule variable `?p` — no pattern can be found, and the call is refused. Proposed: an operation that takes the pattern as an argument, `Error.catch(pattern, body)`, with sugar later.

   ```anthill
   Error.catch(Boom, lambda () -> raiseEither(?p, ?n))       -- every Boom; Error[Other] stays the caller's
   Error.catch(Boom[Reason = ?], lambda () -> both(n))       -- every Boom, both instantiations
   Error.catch(?, lambda () -> raiseEither(?p, ?n))          -- every payload; no Error label is left
   ```

   The typer computes WHICH LABELS THE CALL DISCHARGES FROM THE WRITTEN PATTERN, by the one predicate the boundary reads (§1.5): every label the pattern admits is discharged, every other one stays in the caller's row. So the row and the run say the same thing whatever the pattern is, and `catch(?, …)` is sound: it catches every payload and leaves no label for an outer boundary to expect. (A catch-all whose row discharges only `P` is not: measured on WI-20260908-9WVT7's second review, `either(7, 7, ?r)` over `{Error[P], Error[Other]}` answered `err(other(n: 7))`, the `Other` its row had left to the caller, inside a `Result[E = P]`.)

   Open in it: (a) the result type — `Result[E = …]` must come from the pattern, so the parameter is typed by it (`catch[T1](pattern: TypePattern[T = T1], body: () -> X @ {Error[T1], Rho})`), the written `Boom` elaborated into that argument, which 055 §2's denotation rule would have to say; a `Type` value, whose content the typer does not read (055 §4), cannot carry it. (b) what `E` is for `catch(?, …)` — the type of everything, or the union of the labels the row discharges. (c) its relation to `reify`, whose pattern can be written today only as a bracket in an operation body (`Error.reify[T1 = Boom](…)`; a rule body refuses the bracket) — `catch` would be the form that works in both, and `reify` its inferred-pattern case. It would subsume the open-slot evidence of §1.6 for a written pattern, which stage (e) builds for an inferred one.

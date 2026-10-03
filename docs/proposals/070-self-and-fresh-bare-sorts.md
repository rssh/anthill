# 070: `Self` — a bare sort is fresh everywhere, and this instance is written

## Status: Draft (2026-10-03). Decided in discussion: the reading of a bare sort, `Self` and `s.Self` (2026-10-01, WI-20261001-80ZV8); keeping a sort's parameters as type parameters of its operations, and refusing an incomplete reference to a sort inside its own definition (2026-10-03). Nothing is implemented; until it is, `kernel-language.md` and `docs/design/type-parameter-scoping.md` describe the code.

## Supersedes: `docs/design/type-parameter-scoping.md` §1's `s.Sort` and its rejection of `s.Self`; §3's first bullet (the implicit self tie), its WI-1082 paragraph and its "Two exceptions"; §4's member-tie enforcement; §5's "The scope is the foreign slots" paragraph. In `docs/kernel-language.md` §8.1, every sentence that makes a reference to the callee's own sort an exception — WI-1059's and WI-1061's self skolem, the "callee's own sort is not existential" paragraph, WI-1082's "The tie is WRITTEN" and the three paragraphs after it (the parameter position, its two consequences, an operation with no parameter naming its own sort), and the self reading and the "enclosing frame for a bare sibling call" of "One principle, two engines" — while WI-1078's sentence on the enclosing sort's parameters keeps its reason and loses its bare `toPair(h: Holder)`, those parameters being the operation's own type parameters (§1.1); in §8.7 the *Interim* sentences of the member rule. WI-20260929-05ZQE's DECIDED (2), "a received bare carrier binding is the receiver's instance".

## Relates to: [042](042-explicit-type-parameters-on-operations.md) (operation type parameters; `s.Sort` in "Type projections"), [058](058-modular-instances.md) (§4.2, what a call's bracket may bind), [059](059-secondary-entries.md) (secondary entries), [066](066-provision-member-blocks.md) (provision blocks), [069](069-parameter-defaults.md) (declared defaults; its "the self tie wins over the default" is `p: Self` in this proposal's terms — §7), WI-374, WI-376, WI-424, WI-1059, WI-1061, WI-1063, WI-1078, WI-1082, WI-20260929-0RP29 (the interim reading of `provides`), WI-20260930-GJW9Z (a same-sort sibling call through the spec).

## Tracked by: WI-20261001-80ZV8.

## The problem

One text means two things, depending on where it is written:

```anthill
sort List
  sort T = ?
  operation append(xs: List, ys: List) -> List = …   -- ONE List[T], three times
end

operation concat(xs: List, ys: List) -> List = xs      -- three unrelated Lists
```

`List.append([1, 2], ["s"])` is refused and `concat([1, 2], ["s"])` loads. Inside a sort's own definition a bare reference to that sort is "this instance" (the scoping doc's §3; WI-374 enforces it at a call, WI-1082 writes it into the signature at load); everywhere else it is the sort with a fresh `?` in each unwritten slot (§4). Nothing in `append`'s text says that its three lists agree. The tie is invisible, so it cannot be checked by reading, and it does not extend to `provides`: WI-20260929-0RP29's reviews 5–7 read `provides Rel[A = Car, B = Car]` three ways in three places of the typer (the declaration rule, the carrier-parameter call, dispatch), and every question of those reviews — received parameters, witnesses, a member narrower than its spec by a tie its text does not show — comes from it.

## 1. The rule

### 1.1 A sort's parameters are type parameters of its operations

Every operation declared in a sort takes that sort's parameters as type parameters. They share one list with the operation's own `[A]`. A call fixes them the way it fixes any type parameter:

- **from a bracket:** `Cell[V = Int64].get(c)` or `Cell.get[V = Int64](c)`;
- **from the arguments:** `Cell.new(5)` fixes `V = Int64` through `new(v: V)`;
- **from the expected type:** `let l : List[T = Int64] = List.empty()`.

Each call fixes them afresh. This includes a call made inside the sort's own operations: `List.mapElems` calls `reverse` at its `Dst`, not at its own `T`. Inside a body, the sort's parameters are rigid. This holds for every sort, whatever it is used for: `T` is a type parameter of `PartialEq.eq` exactly as `V` is a type parameter of `Cell.get`. For a sort used as a spec, the instance a call fixes is also the instance it dispatches on.

This is today's rule (`kernel-language.md` §5.4: a bracket key names "the operation's own, or its enclosing sort's" type parameter, "both scopes, one list", WI-841; and "Which variables the ∀ quantifies" includes "its declaring sort's parameter"), with one change: today a same-sort call inside the sort is pinned to the enclosing instance (WI-424's seeding, §4), and under this rule it is not.

### 1.2 `Self`

Inside a sort's definition, `Self` is that sort applied to its own parameters. In `sort Cell` (with `sort V = ?`) it is `Cell[V = V]`. In a sort without parameters it is just the sort. Because `Self` names the sort's own parameters, every `Self` in one signature is the same instance, the one the call fixes:

```anthill
sort Cell
  sort V = ?
  operation new(v: V) -> Self                    -- the cell holds what was passed
  operation get(c: Self) -> V                    -- returns what this cell holds
  provides Modifiable[T = Self]
end

sort List
  sort T = ?
  entity cons(head: T, tail: Self)
  operation append(xs: Self, ys: Self) -> Self   -- one element type for all three
  operation empty() -> Self                      -- the caller's expected type fixes T
end
```

`Self` is resolved where it is written:

- in a `sort` or `enum` body, and in a secondary entry at the sort's address (§5.1 of the spec: such an entry "is scoped by `X`'s type parameters"), it is that sort;
- in a provision block (066), it is the providing sort, since the block is inside it;
- in a spec it is the spec. It does not become each carrier: what Rust calls a trait's `Self` is, in anthill, the spec's carrier parameter (`PartialEq`'s `T`);
- in a witness it is the witness, not the sort the witness provides for;
- in an entity's fields it is the sort that declares the entity (`cons`'s `tail: Self` is a `List`). A top-level `entity Account(…)` is its own sort (§6.3), so there `Self` is `Account`.

`Self` may be written in operation parameters, returns and bodies, entity fields, `provides` and `requires` bindings, and rule-variable bounds. It takes no bindings — `Self[V = Int64]` is a load error; another instance is written with the sort's name (`Cell[V = Int64]`, or `Cell[V = ?]` for any cell). Outside a sort `Self` is a load error. The name is reserved: no sort, type parameter or member may be called `Self`.

Nothing downstream of name resolution sees `Self`: it is replaced at load by the written form (`Cell[V = V]`), which already loads and runs today (measured 2026-10-01: `provides Rel[A = Car[V], B = Car[V]]` with `mix(a: Car[V], b: Car[V])` runs at one `V` and refuses two).

### 1.3 A bare or partial sort reference

A parametric sort can be written with some parameters left out: bare (`Car`) or partial (`Stream[T = Int64]`). Each slot left out gets a fresh `?`, separately at each occurrence, in every position. So:

- a top-level `mix(a: Car, b: Car)` takes two unrelated `Car`s;
- `sort Garage provides Rel[A = Car, B = Car]` binds two unrelated `Car`s.

In a parameter, the caller instantiates the `?` (∀). In a return, each use opens it (∃) — `kernel-language.md` §8.1, now with no exception for the callee's own sort. A `let` annotation keeps the value's parameters in the slots it leaves out, which is the same `?` bound by the value (scoping doc §4). A sort written as an effect label is compared by identity, not expanded (§8.1), so neither this rule nor §1.4 reaches an `effects` clause.

Where 069 gives a slot a declared default, 069 says what leaving it out means — the default in a negative position, an existential in a return — and this proposal changes nothing about that for a reference to another sort. For a reference to the enclosing sort, see §7.

### 1.4 Inside its own definition, a sort is written in full

Within a parametric sort's definition, a reference to that same sort that leaves a slot out is a load error. This applies at any depth and in every position listed for `Self` in §1.2, for example:

- `get(c: Cell)`
- `tail: Option[T = List]`
- `provides Eq[T = Set]`
- `widen(s: Stream[T = Int64])`
- `let s : Stream = …` inside `sort Stream`

The error message offers two fixes: `Self` for this instance, or the slot written out (`Cell[V = ?]` for any cell).

The rule exists because, under §1.3, a forgotten `Self` silently widens a signature, and a body-less operation has no body check to catch it. `operation get(c: Cell) -> V @[host_implemented]` would accept any cell and let the caller's expected type choose `V`. Measured on today's build with the same signature spelled the only way today allows (`get[W](c: Cell2[V = W]) -> V`): `operation asString(c: Cell2[V = Int64]) -> String = Cell2.get(c)` loads, and reads an `Int64` cell as a `String`; with `get(c: Cell2[V = V])`, the spelling of `Self`, it is refused (`expected String, got Int64`). It is also the one place where the habit of C++, Rust and Swift (inside a type, its bare name is the current instance) meets §1.3, so a reader coming from those languages is told at the declaration rather than surprised at a call.

Three things are not affected:

- a sort without parameters, since nothing is left out;
- a reference to another sort;
- a qualified call such as `List.reverse(xs)`, which names an operation, not a type.

A declared default (069) does not excuse the reference: inside its own definition a left-out slot is refused whether or not it has a default (§7).

### 1.5 `s.Self`

For a value `s`, `s.Self` is its whole parameterized type: `Stream[T = Int64, E = {}]` for a stream of that type. It can be used wherever `s` is in scope, inside a sort or outside one, for example `splitFirst(s: Stream) -> Option[Pair[A = s.T, B = s.Self]]`. It replaces `s.Sort` (WI-376), with no second spelling: after the rename `s.Sort` is an ordinary missing member. One word now names one notion — a sort at its parameters, of the enclosing definition (`Self`) or of a value (`s.Self`). This reverses the scoping doc's §1, which rejected `s.Self` for its "receiver/enclosing-type baggage" when there was no `Self` for it to agree with.

## 2. What does not change

- **§1.1 is today's rule.** The bracket, the ∀, rigid parameters in a body, dispatch on the fixed instance.
- **Foreign references.** A reference to another sort is already fresh per occurrence (scoping doc §3, second bullet).
- **Specs.** `PartialEq.eq(a: T, b: T)` is written and read as today. A spec that receives on itself writes `splitFirst(s: Self)`, and its carrier's member writes its own `Self`; the member rule recognises a self-receiver by its sort (the spec's functor against the carrier's, `kernel-language.md` §8.7), and `Self` keeps the functor.
- **The written form.** `Car[V = V]`, `Car[V = Int64]`, an operation's own `[W]`, projections `c.V`, shared variables `?t` — all mean what they mean today, with one exception: inside the sort, a written `?` at the sort's own slot (`Car[V = ?]`) is this instance today and becomes an independent one (§5, stage c).

## 3. What the typer loses, and what it gains

Gains, all at load and none in unification:

- `Self` resolved by name lookup to the enclosing sort applied to its own parameters, refused outside a sort and with bindings, reserved as a name;
- the refusal of §1.4 — a syntactic check over a parametric sort's own declarations;
- the projection name `.Self`.

Loses — every reading of a bare or part-written reference to the declaring sort as "this instance", on the declaration side and at the call:

- `elaborate_self_ties` with `declares_self_param` and `SlotPosition::fill_self` (`typing/elaborate.rs`; WI-1082, which writes the tie into a signature);
- `enforce_member_tie` (`typing/sort_alias.rs`; WI-374, which enforces it at a call) and its `exempt_rigids`;
- **WI-424's same-sort sibling-call seeding** (`typing/apply.rs`, the block after `seed_receiver_type_args`, and `TypingEnv::enclosing_instance_param_rigids` if nothing else reads it), which pins a sibling call to the enclosing instance. Its comment calls it "exactly the parametricity tie"; it was not in 80ZV8's original list. Measured on a copy of `List.mapElems`: with `rev(xs: MyList) -> MyList[xs.T]` the call `rev(onto(xs, f, seed))` at `Dst` loads; with `rev(xs: MyList[T = T])`, the spelling of `Self`, it is refused (`type mismatch in rev.xs (op-arg): expected MyList[T = ?T], got MyList[T = ?Dst]`); with a let-bound argument (`rev(seed)`, `seed : MyList[T = Dst]`) it is refused in both spellings, while the same call from outside the sort loads;
- the self exception of the foreign-slot expansion — `callee_parent_canon` in `expand_foreign_sort_application_as` and `expand_foreign_sorts_deep` (`typing/sort_alias.rs`; WI-1059, WI-1061, WI-1063);
- the canonical-channel binding of a bare self reference in `unify_parameterized_with_sort_ref` (`typing/unify.rs`);
- the rule side's self reading (§8.1 "One principle, two engines": "Within the sort's own definition the bare self reference is the parametricity tie instead"; the rule half is WI-20260911-5G28A);
- the interim readers of WI-20260929-0RP29: `this_instance_binding_at` and its readers (`self_references_at_own_parameters`, `holds_own_instance`, `binding_at_receiver`), the bare and part-written arms of `is_this_instance` and `holds_carrier`, and `Narrower::Tied` over a bare name (`typing/signature.rs`); the this-instance arms of `bind_spec_params_from_carrier_param` (with `carriers_own_provision_qualifies`) and of `bind_spec_params_from_carrier` (`typing/carrier.rs`).

After §1.4 these see no input they were written for; stage (e) deletes them. Once they are gone, a sort's parameter differs from an operation's `[A]` only in where it is declared, so the two could take one path through the typer. That is a direction to measure, not part of this proposal.

## 4. Stages

Each stage leaves the whole suite green.

- **(a)** This proposal, and a status line on `docs/design/type-parameter-scoping.md` naming what it supersedes.
- **(b)** `Self` (§1.2) and the rename of `s.Sort` to `s.Self` (§1.5). The spec gains `Self` (§5.2) and `s.Self`; 042's "Type projections" and the scoping doc's §1 rename `s.Sort`.
- **(c)** The migration — stdlib, examples, docs and test fixtures write `Self` or the slot — **together with deleting WI-424's seeding**, because a written receiver and the seeding refuse a sibling call at another instance (§3, measured). Every written `Car[V = ?]` inside `sort Car` is checked on the way: today it is this instance, so where an operation relies on that it becomes `Self`. Measured blast radius (2026-10-01): about 90 declarations in 14 stdlib files, at least 321 in 81 files under `rustland/anthill-core/tests` (fixtures assembled from helper strings are not counted), 43 in 14 files under `docs/`; `.Sort` is written once in `stdlib/`, once in `examples/`, 22 times in 8 docs files, 24 in 4 test files and 13 in 6 source files.
- **(d)** The refusal of §1.4. It is what proves (c) complete: a forgotten `Self` is wider, not wrong, so nothing else finds it.
- **(e)** The tie removed (§3). `kernel-language.md` §8.1 loses the sentences listed under *Supersedes*, and §8.7 its *Interim* sentences; the scoping doc's §3–§5 are rewritten to §1; the rows WI-20261001-80ZV8's feedback entries list as asserting the interim reading are flipped or rewritten with `Self`. scaland is checked for parity (a keyword search found no tie there; unverified).

## 5. Acceptance

Each row asserts its control and says which build fails it.

- `mix(a: Self, b: Self)` behind `provides Rel[A = Self, B = Self]` runs at one instance, and `Rel.mix` over two instances is refused at load. With `B = Car[V = ?]` and `mix(a: Self, b: Car[V = ?])`, two instances run.
- A witness's `Rel[A = Tag, B = Tag]` takes two unrelated `Tag`s through the spec call as through the qualified one.
- A bare or partial reference to the enclosing sort — field, parameter, return, body annotation, `provides` or `requires` binding, rule-variable bound, at any depth — is refused, naming `Self` and the written form; a sort without parameters is not.
- `Self` outside a sort, `Self[V = Int64]`, and a sort, type parameter or member named `Self` are refused.
- `Set.eq(a: Self, b: Self)`: `Set.eq(intSet, stringSet)` is refused (today it is refused by the tie: `expected consistent bindings for the sort's shared type parameter (first bound to Int64), got String`). `List.append([1, 2], ["s"])` stays refused, now by the written `Self`.
- `Cell.get(c: Self) -> V`: an `Int64` cell read as a `String` is refused.
- With `reverse(xs: Self)`, `List.mapElems` calls `reverse` at `Dst` and loads; a sibling call with a let-bound argument at another instance loads too.
- `s.Self` reads a value's whole parameterized type wherever `s.Sort` did (the WI-376 rows renamed); `s.Sort` is an ordinary missing member.
- No declaration under `stdlib/` or `examples/` holds a bare self-reference — §1.4 refuses it.
- The full workspace is green via `rustland/scripts/test.sh`, and scaland via `sbt testFull`.

## 6. Considered and not taken

- **The C++ rule** — inside its own definition a sort's bare name is the current instance, in operations and `provides` alike. Sound and terser, but one text keeps two legal meanings, because the bare name outside already means "any" (2026-10-01).
- **"A sort's parameter may be used in an operation only beside `Self`."** It does not see a forgotten `Self` in an operation that never mentions the parameter. `Set.eq(a: Set, b: Set)` and `Set.union(s1: Set, s2: Set) -> Set` are body-less and mention no `T`. Measured with today's spelling of what they will mean (`eq[A, B](a: Set2[T = A], b: Set2[T = B])`): the declaration loads; every call is refused with `missing requires Set2[T = …] on enclosing sort`, the wrong place and the wrong fix; and a caller who adds a bracket (`Set2[T = Int64].eq(intSet, stringSet)`) loads, comparing sets of two element types. Nor does it see a half-forgotten `Self` (`mix(a: Self, b: Car)`). And every spec operation uses its parameters without `Self` (`PartialEq.eq(a: T, b: T)`), so specs would need an exemption, while the language has no spec declaration: a spec's carrier parameter is read off its operations (§5.1, WI-1076: "the first declared type parameter that some declared operation takes as a parameter"), and by that rule `Cell`'s `V` is one too.
- **"Match the parameter to the operation's parameter of the sort automatically, and refuse where it cannot be matched."** That is the tie in a smaller form: the meaning of `V` would depend on how many parameters of the sort an operation has. It has nothing to match in `Set.eq(a: Set, b: Set)` either.
- **A call-side check — refuse a call whose arguments leave a sort's parameter unfixed.** The declaration is still wrong, and a bracket satisfies the check. Measured with `get[W](c: Cell2[V = W]) -> V`: `Cell2[V = String].get(c)` and `Cell2.get[V = String](c)` both load an `Int64` cell as a `String`.
- **A declaration check — refuse a type variable that appears only in the return of a body-less operation.** `Set.empty() -> Self` has exactly that shape and is right; `get(c: Cell[V = ?]) -> V` has it and is wrong. Only the author knows which is meant, which is why §1.4 makes the author say it at the place where the choice is written.
- **`Self` as the carrier in a spec** (Rust's trait `Self`). It needs a declared carrier, which the language does not have, and it reverses §1.2's single lexical meaning.
- **`Self` with bindings** (`Self[T = Int64]`). Another instance is written with the sort's name; `Self` stays one word for one instance.

## 7. Open questions — answered

- **A defaulted slot inside the sort's own definition (069).** ANSWERED (user, 2026-10-03): 069 and this proposal say the same thing in different terms. 069 (Draft) is written in pre-`Self` terms. It fills a left-out slot with its declared default in a negative position only, and makes one exception: *within a sort's own definition, the self tie wins over the default*, because taking the default would change what a member is about —

  ```anthill
  sort AsymmetricPair[T1, T2 = T1]
    entity apair(first: T1, second: T2)
    operation second_of(p: AsymmetricPair) -> T2 = …
    --   tie (069):  p: AsymmetricPair[T1 = T1, T2 = T2]   -- this instance
    --   default:    p: AsymmetricPair[T1, T1]             -- only symmetric pairs; -> T2 no longer matches
  end
  ```

  What 069 writes there means that `p` is `Self`. This proposal removes the tie and writes it: `second_of(p: Self) -> T2`. So §1.4 refuses a left-out slot of the enclosing sort whether or not it has a default — no default gets to change what a member is about, which is 069's own reason — and a reference to another sort keeps 069's rule unchanged. 069 carries the bridge (its §2, "In proposal 070's terms, `p` is `Self`"): before this proposal lands, the tie wins over the default as 069 states; after it, 069's tie paragraph, the parenthesis closing its restatement of WI-1056's four spellings and its sentence "WI-1082's … is unchanged, since a self reference still takes the tie" become a pointer to §1.4, and its acceptance row is written `p: Self`.

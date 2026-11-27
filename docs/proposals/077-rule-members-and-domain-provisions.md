# 077: A spec's rule member is implemented by a provision — a sort's domain is an ordinary `SortDomain` provision

## Status: Draft (2026-11-27), WAITING ON [076](076-goal-scope-in-the-search.md). Written with the user while working WI-20260911-WT8WG: the user's call, "fix the general machinery", over making the per-sort table the one source. Nothing is built. ORDER, decided with the user the same day: 076 first. Programs that lean on domains are not written today because the first attempts were too slow — a typed column generating where it should check (WI-20261115-YR3N7), then checking its whole value again at every call (WI-20261124-YFD7F: 20 s and 7.6 GB at n = 400), then the search itself (076: `2^k` after `k` ground goals, the copied resolvent) — so the machine comes before the reorganisation. 077 is designed after 076's Stage A, together with YFD7F's dictionary channel and the fairness question (open question 2), which 076's branch representation decides. §5's three changes to the requirement machinery are the open part and are measured before anything else (§8, S1). §9 (the type test `anthill.kernel.domain` moved into `SortDomain` as the member `check`, threaded as `fill` is) added with the user the same day; §2 corrected the same day (a provision is an anonymous sort, its rules that sort's — not the providing sort's), with §1's unconditional case and open question 7.

## Amends: [052](052-rules-as-stream-valued-operations.md) (a `Relation` applied in goal position runs its rule in place — open question 6), [060](060-clause-level-requirements-and-typed-heads.md) §2.3 (how `fill` is threaded), [066](066-provision-member-blocks.md) §3 (a `where` block holds operations only), [067](067-fillable.md) §3 (`fill` found "through a map of the rule member's own"); `docs/kernel-language.md` §5.3 (*A closed sort defines its domain*; WI-742's `domain(?x, T)`, and C666A's admission through that guard — §9) and §8.7.

## Relates to: WI-20260911-WT8WG (retires `<Sort>.domain`; its items 3 and 4 are this proposal), [060.1](060.1-written-rule-requirements.md) (a rule declares its requirements), [065](065-type-value-requirement.md) (`TypeValue`, derived for every sort, never written), WI-20260830-X9PB4 (the wildcard rule), WI-860 (a passed dictionary and a local row must agree), WI-20261115-YR3N7 (the head decides the mode), WI-20260911-09E6M (generation by size), WI-20261116-HWD8A (tuple domains), WI-20260911-5TK6B (`Bool`), WI-20261124-YFD7F (the trusted slot, and S4's check-only column — §9).

## The problem

A sort's domain is read through two mechanisms, and they answer differently.

**The per-sort table** (`KnowledgeBase::sort_domains`, one `SortDomainEntry` per sort, written by
`kb::fill_derive`) is what almost everything reads: the resolver's `apply_domain` (which relation
fills a sort), a typed column at a concrete type (its dictionary built from the TYPE at run time,
`domain_evidence_of_type`), a citation's route (`typing::sort_domain_route`), and every sub-domain
inside a fill (`__domain_sub(?self, k)`).

**The `SortDomain` provision rows** (`List provides SortDomain[T = List[T = T]] :- SortDomain[T = T]`)
are read only where a program writes `requires SortDomain[T = X]` on an operation or a sort: the
general requirement machinery resolves the call site's requirement against them. They are derived
FROM the table (`kb::sort_domain_derive`), and only on demand.

MEASURED 2026-11-27 on the delivered tree, each row a probe run and then deleted:

1. **The two disagree where a provision is written.** With `sort W { entity w  provides
   SortDomain[T = Colour]  rule domain(?x) :- ?x <=> red() }`: through a `requires SortDomain[T = X]`
   slot at `X = Colour`, 1 answer (`red`, pinned by `wi_je2mt_provision_at_its_carrier_test`); through
   a typed column `rule typed(?x: Colour) :- true`, 3; through `W`'s own `rule typedW(?x: W) :- true`,
   none — `W`'s entry runs its written relation, which answers a `Colour`.
2. **The general path refuses its own form.** `rule declaredSD[A](?w: List[T = A]) :- SortDomain[T =
   A], ?w <=> [?]` cited as `declaredSD[A = Colour](?w)` from a rule body (060.1's spelling) does not
   load: (a) "no impl provides `anthill.reflect.SortDomain`; declare `provides …` on the carrier",
   because the demand gate (`typing::any_requirement_names_one_of`) counts a sort's and an
   operation's `requires` and not a rule's guard — an unrelated `operation opener[X]() requires
   SortDomain[T = X]` in the file removes this error; (b) then "expected a requirement of
   `SortDomain` the clause declares … A call at a concrete type needs no requirement", a message
   contradicting the call it refuses.
3. **The table copies the requirement layout by hand.** `SortDomainEntry::sub_offset` is the general
   machinery's layout (`SortDomain`'s own chain, the sort's sort-level `requires`, then the
   conditions — `typing::sort_domain_sub_offset`), recorded so a derived clause's `__domain_sub(?self,
   k)` reads the right slot, and checked against the rows only after they exist.
4. **A hand-written domain cannot read its element's domain.** A written domain's reads are handed
   the whole dictionary or `__unrouted` (`resolve::fill_goal`'s `Written` arm), so a parameterised
   written domain is refused at load. Driven with the type passed explicitly, the shape is sound:
   `rule boxCase(?t, box(v: ?v)) :- ?t <=> Box[T = ?e], apply_domain(?e, ?v)` answers 4 at `X =
   Colour`, 2 at `X = One`, 3 at `X = Box[T = One]`, through a rigid `X`.
5. **The table is a one-member `SortOpsTable`.** An operation member is found by `impl` through
   `SortOpsTable.by_impl` (impl sort → operation SHORT name → target). `fill` was first filed there
   and collided with any operation of the provider named `fill` (067 §3), so the rule member got a
   map of its own.

**WHY THE TABLE WAS BUILT** — the recorded reasons, all three from one fact, that a type has exactly
one domain and nothing is chosen:

- **Cost.** Deriving `SortDomain` and `Fillable` rows for every sort cost ~115 ms per load in a debug
  build (`ANTHILL_LOAD_TIMING=1`, 2026-09-25), the typer re-checking a bigger provision relation —
  so rows are derived on demand, and without rows the general machinery answers no typed column.
- **No search.** A column whose type is not pinned at load (`?x: List` is `List[T = ?t]`) would ask
  `SortDomain[T = ?]`, and the wildcard rule (X9PB4, `sort_goal_with_wildcards`) matches every
  provider and comes back ambiguous. The table needs no search: the type's head names the provider.
- **Open conditions.** 060 §2.3 decided that a condition is resolved when `fill` reads it, and a
  read waits while its type is unpinned (`[]`'s `nil` case never reads its element's). The general
  machinery builds a dictionary whole and assumes it ground (`dictionary.rs`, WI-860's check).
  Measured: `rule anylist(?w: List) :- true` answers with residuals reading
  `apply_domain(__domain_sub(Dictionary((), ?_, impl: List), 1), ?_)` — the condition slot holds the
  element's TYPE, unbound, at run time.

So the table is a workaround for three properties of the general machinery, not a second design.
This proposal removes the three properties and the table with them.

## 1. The rule

**A spec may declare a RULE member, and a provision implements it with clauses written in the
provision**, as it implements an operation member. `Fillable.fill` is already declared so
(`rule fill(?x)`, body-less, untyped). A goal at a spec's rule member through a dictionary is
dispatched by the RESOLVER to the provider's clauses — in place, in the current search — handing
the dictionary to the clauses' reads.

A sort's domain is then an ordinary provision. What the loader derives is exactly what an author
could write:

```anthill
sort Colour                                   -- unconditional: a block as well
  entity red
  entity green
  entity blue
  provides SortDomain[T = Colour] where
    rule fill(red) :- true
    rule fill(green) :- true
    rule fill(blue) :- true
  end
end

List provides SortDomain[T = List[T = T]] :- SortDomain[T = T] where      -- conditional: its block
  rule fill(nil) :- true
  rule fill(cons(head: ?h, tail: ?t)) :- fill(?t), SortDomain[T = T].fill(?h)
end
```

- **Inside the block**, `fill(?t)` is the block's own rule (§2), called with the same dictionary
  (the recursive field); `SortDomain[T = T].fill(?h)` calls through the provision's CONDITION (the
  field typed by a parameter). That is 066's rule — a provision's conditions are in scope for the
  members written in its block — extended from operations to rules. It is what `__domain_sub(?self,
  k)` hand-codes today.
- **The cases stay one clause per constructor, the constructor in the head** (YR3N7): a bound value
  selects its one clause, an unbound one matches every head in clause order.
- **The clauses are written in the provision's block, conditional or not** (user, 2026-11-27: "we
  have rule in sort" — a provision is an anonymous sort, and a sort already holds rules; confirmed
  the same day: a provision's rules are not placed in another sort, §2). An unconditional provision
  gets a block as a conditional one does: the grammar already parses `provides X where … end`
  without conditions, and the block admits rules beside operations (§8, S2). An earlier draft of
  this bullet made an unconditional provision's members the providing sort's own rules —
  `sort Colour { … provides SortDomain[T = Colour]  rule fill(red) :- true … }`, the shape the
  je2mt / cxr5b witnesses write today with `domain` for `fill`; those witnesses move into a block.
- **A primitive's provision is written in the stdlib's source**, not in Rust:
  `Int64`'s body gains `provides SortDomain[T = Int64] where rule fill(?x) :- domain(?x, Int64) end`,
  and `Bool`'s block its two cases (`rule fill(true) :- true`, `rule fill(false) :- true`), in place
  of `fill_derive::FINITE_PRIMITIVES`.
- **A sort that defines its own domain writes its provision** — parameterised or not:

  ```anthill
  sort Box[T]
    entity nobox
    entity box(v: T)
    provides SortDomain[T = Box[T = T]] :- SortDomain[T = T] where
      rule fill(nobox) :- true
      rule fill(box(v: ?v)) :- SortDomain[T = T].fill(?v)
    end
  end
  ```

  A written provision REPLACES the derivation for its carrier; a second provision of `SortDomain`
  at one carrier is refused at load (§5.1).

## 2. A provision is an anonymous sort, and its rules are that sort's rules

**DECIDED (user, 2026-11-27): "rules in provision should have exactly the same semantics as rules in
an ordinary sort."** A provision is an anonymous sort — the direction 066 §5 records, "blocks as
anonymous instances — members identified by (carrier, clause, name), dispatch resolving to a
clause" — and a sort already holds rules, so a provision holds them, with nothing new in what they
mean. CONFIRMED the same day: a provision's rules are not placed in another sort — neither in the
providing sort (`List.fill`, which an earlier draft of this section said) nor anywhere else.

- **A rule written in a provision's block is a rule of the block's sort**: written there, scoped
  there. `fill(?t)` inside it names the block's own `fill`, as a rule in a sort names its sibling.
- **A body-less one is a DECLARATION** (061), exactly as in a sort: a case is written `:- true`.
- **The provision's conditions are in scope for the rules of its block, and only for them** — 066's
  rule for operations. They are those rules' declared requirements (060.1), supplied by whoever
  dispatches to them.
- **A block may hold a rule that is no member of the spec**, as a sort holds any rule (§9's
  `checkCase`).
- **It takes no name in the providing sort.** `List` has no `fill` of its own; a rule `fill` written
  in `sort List` is unrelated to the provision's, and nothing collides (open question 7, withdrawn).
- **It is reached through the dictionary**: a goal at the spec's member with a dictionary `D` runs
  the rules of the provision `D` names (§3) — today identified by its providing sort and spec, as 066
  identifies a block (its rule 5 refuses a second block of one spec). A domain wanted as a value
  stays a typed rule cited by name (`rule colours(?x: Colour) :- true`).

So there is no member table for rules. 067 §3's collision came from filing the rule in
`SortOpsTable`, an OPERATION table keyed by short name; a block's rule stays in its block's scope.
The per-sort table's fields become readings of the provision: `fill` the block's rule; `params`,
`conditions` and the layout the provision's own (`dict_layout`); `kind` gone (derived and written
are both provisions); `reads` and `fielded` computed from the block's clauses.

## 3. Dispatch — in the resolver, as `apply_domain` does today

A goal at a spec's rule member with a dictionary `D` lowers, in the step that meets it, to the goal
of the member `D`'s `impl` provides, with `D` handed to each clause's read
(`within_requirements_goal`, as now). It is `apply_domain` generalised from one spec to any. It
starts no search of its own: the goal is replaced in place, in the same frame and substitution,
as `ho_apply` is. A rule member reached from an OPERATION body is an ordinary rule citation, run
as one (052).

## 4. A typed column is a requirement

```anthill
rule p(?x: T) :- body      ≡      rule p(?x) :- body, SortDomain[T = T].fill(?x)
```

060 §2.3 already writes this equation; it now holds literally. The generated goal is the member
call, and its dictionary comes from the ordinary requirement machinery:

- **a concrete `T`**: built at load from the provisions, so nothing builds a dictionary from a type
  at run time (the staging invariant 060 assumes, which `domain_evidence_of_type` breaks today);
- **a `T` mentioning the clause's type parameter or the enclosing sort's**: the clause's implicit
  requirement, routed from the citation's caller as today (5G28A S2) — a rigid `X` from the caller's
  `requires` slot;
- **a `T` not pinned at load** (`?x: List`; superseded by 060.1 §9 if approved, see §5.2): a dictionary with an OPEN condition (§5.2), read off the
  value once something pins it.

A typed column needs no written `requires`: it IS the declaration of its requirement, as it is
today. 060.1's rule (a rule takes no dictionary it does not declare) is unchanged for every other
requirement.

## 5. What the general requirement machinery must learn

The three reasons the table was built, answered in the machinery instead of beside it.

**5.1 No search for a domain.** `SortDomain` is COHERENT BY CARRIER: at most one provision per
carrier, a written one replacing the derived one, a second refused at load. So `SortDomain[T = B]`
is resolved by `B`'s head — a lookup — and never by `sort_goal_with_wildcards`. A witness
(`W provides SortDomain[T = Colour]`) is then an ordinary provision, and the one source for
`Colour` on every path. (Open: a property of `SortDomain` alone, or one a spec declares — `TypeValue`
has it already, being derived-only.)

**5.2 Open conditions.** *SUPERSEDED, if [060.1](060.1-written-rule-requirements.md) §9 (draft,
2026-11-27) is approved: a rule's types are known at load, so no dictionary holds an open condition
and nothing builds one at run time; the `T` not pinned at load of §4's third bullet becomes the
rule's type parameter, fixed at each citation, its `SortDomain[T = T]` passed by it. Kept below as
written.* A dictionary may hold a condition not yet resolved — `SortDomain[T = ?t]` —
resolved when a member reads it, waiting while `?t` is unpinned (060 §2.3, decided). `dictionary.rs`
and WI-860's unification check must accept such a dictionary, or hold the condition as a distinct
pending sub. The table path already builds one at run time (the `anylist` residual above); what is
new is the general machinery building and checking it.

**5.3 Rows for every sort.** With every typed column a requirement, the demand gate opens for
nearly every program, so the rows are derived for every sort with a domain. The 115 ms is a
debug-build figure from before the optimized gate and the provider index (WI-20261010-ANK4X); it is
re-measured first (§8, S1). If it stands, rows are filed lazily per carrier on first lookup —
possible because §5.1 makes the lookup a function of the head.

## 6. What goes

- the per-sort table: `sort_domains`, `SortDomainEntry`, `SortDomainKind`, `fill_relations`,
  `kb::sort_domain_derive` and its demand gate and layout check;
- `fill_derive::FINITE_PRIMITIVES` and the primitives' Rust derivation (§1, stdlib source);
- `__domain_sub` (a call through the condition) and `fill_goal`'s `Written` arm with its
  `__unrouted` reads;
- `typing::sort_domain_route`'s table arm and `domain_evidence_of_type`'s dictionary built from a
  type (§4; the open-condition read of §5.2 stays a run-time read, by decision);
- the written-domain special cases: a 1-ary `domain(?x)` in a sort body, its arity ladder, the
  parameterised refusal, the typer's self-call exclusion (`own_fill_kind`) — a written domain is a
  provision, and its own clauses carry no typed column over its carrier;
- both defects of the problem's row 2, by construction;
- `anthill.kernel.domain` as a name a program writes (§9): a written goal is `SortDomain[T = T].check`,
  and the builtin stays only as the outer-type test inside the primitives' provisions.

## 7. What stays

The derived cases and their order (YR3N7, WI-743's two rules), generation by size (09E6M), the type
guard in front of the body (its form: open question 8) and the fill after it, `Fillable` as the interface (`SortDomain provides
Fillable`), and every answer every row gives today.

## 8. Stages

| stage | what | flips |
|---|---|---|
| **S1** | MEASURE, nothing built: (a) the cost of `SortDomain` rows for every sort, on the optimized build; (b) which of `dictionary.rs`' and WI-860's checks refuse a dictionary with an open condition; (c) a census of short-name collisions in `SortOpsTable` between an operation and a would-be rule member | nothing — decides §5.2's form and §5.3's lazy filing |
| **S2** | rule members in a provision's `where` block, conditional or not (tree-sitter and fastparse), each a rule of the block's own sort (§2); the member table keyed by spec member; dispatch in the resolver (`apply_domain` generalised); the derivation EMITS provisions with members, read into the old table so no answer moves | a written `provides SortDomain[…] where rule fill(…) … end` loads and answers |
| **S3** | §5.1 lookup by head, §5.2 open conditions, §5.3 rows; typed columns resolve through the requirement machinery (§4) | row 1's witness answers one count on every path; row 2's rule loads and answers |
| **S3b** | §9: `check` derived beside `fill` from one walk of the constructors, its waiting clause (`nonvar`, §9); the outer-type test's provisions for the types with no constructors; a written `anthill.kernel.domain` becomes `SortDomain[T = T].check`; a citation at a caller's rigid without `requires SortDomain[T = X]` refused at load; a citation from an operation body trusted where the typer has the argument | §9's row 2 (`isT(true)`) answers 1; row 4's `noDict` is refused at load; row 1's junk list refused by a `check`-only column |
| **S4** | delete the table (§6); primitives in stdlib source; hand-written domains as provisions, parameterised included | row 4's `Box` written as a provision answers 4 / 2 / 3 |
| **S5** | kernel-language §5.3 and §8.7 (with §9's `domain` paragraphs and C666A's admission), 060 §2.3, 066 §3, 067 §3 — the text agreed with the user first | — |

WT8WG's items 1 (`Colour.domain` an ordinary name) and 2 (its citations moved to typed rules) do not
depend on this and can land first; its items 3 and 4 are S4 and S5.

## 9. The type test moves into `SortDomain`: the member `check`

**DIRECTION (user, 2026-11-27):** "fill need to be reengineered with threading, the same as
`anthill.kernel.domain`", and "`anthill.kernel.domain` should be moved to `SortDomain`". Drafted
with the user the same day, after WI-20261124-YFD7F's S4 question (a column that checks and does not
generate) found no check to give it. Nothing is built.

**What `anthill.kernel.domain(?x, T)` is today** (WI-742, kernel-language §5.3). A builtin that asks
whether the value's CARRIED type conforms to `T`. The carried type is read off the value's outer
constructor and the fields that fix a parameter; the value is never walked. It is three-valued:
holds, refuted, or waits while `?x` is unbound or a side is a type variable, and an answer it still
waits in is conditional. At a type mentioning a variable it READS the variable off the value:
`domain([1, 2], List[T = ?t])` binds `?t = Int64`, which is what ties two columns of one head. It is
not the superseded `<Sort>.domain` value face; the two share a word. Its uses:

- the guard `__domain_guard(?x, B)` in front of a typed column's body (the same builtin; a ground
  value whose carried type stays open passes);
- the WHOLE check of a typed column with no fill — a function type, a spec, an abstract sort, a
  bound that states a requirement — and of a typed query variable's;
- an infinite primitive's `fill` (`Int64`, `BigInt`, `Float`, `String`: the waiting check);
- written by a program, qualified or under `import anthill.kernel.*` (seven test files).

**MEASURED 2026-11-27** (release CLI on c9d251abc; each a probe, not kept):

1. **It is shallow.** `domain(cons(head: 5, tail: "junk"), List[T = Int64])` and
   `domain(cons(head: 5, tail: ["s"]), List[T = Int64])` HOLD; `domain(cons(head: "s", tail: [7]),
   List[T = Int64])` is refuted. A written column refuses the junk list only through its FILL, which
   walks a bound value constructor by constructor (the head decides the mode, YR3N7).
2. **It carries no instance.** In `sort Wrap[T]`, `rule isT(?x) :- anthill.kernel.domain(?x, T)` cited
   as `Wrap[T = Bool].isT(true)` answers NOTHING — at a concrete instance, no rigid involved — where
   the typed `rule el(?x: T) :- true` cited the same way answers 1. Through `op[X](v: X)` at
   `X = Bool`, `v = true`: 0. Open (`Wrap[T = X].isT.takeN(9)`): `relation_floundered(domain(Var,
   T))`. The goal's `T` is never replaced by the citation's instance: it is compared as written.
3. **At a rigid it checks nothing against the rigid.** `has[X](v: X) = Wrap[T = X].el(v)…` answers 1
   with and without `requires SortDomain[T = X]`: the guard reads the type off `v`, and compares `v`
   with its own type.
4. **A fill at a rigid without the dictionary loads, and fails when it runs.** `noDict[X]() =
   Wrap[T = X].el.takeN(9).length()` and the nested `rule ll(?w: List[T = List[T = T]]) :- true`
   cited as `Wrap[T = X].ll` load clean and raise `relation_floundered(__domain_guard(Var, Var),
   apply_domain(Var, Var, Var))` at `X = Bool`. With `requires SortDomain[T = X]` they answer 2 and
   7. (kernel-language §5.3 says so: "with neither, the bound keeps §2's ladder"; and its *Not
   reached*: "a bound at the caller's own type parameter `A` is checked only where the caller holds
   `requires SortDomain[T = A]`".)
5. **A check-only column cannot be built from it.** YFD7F's S4 prototype gave a concrete inferred
   column the waiting `domain` check and no fill: `firstX(5, cons(head: 5, tail: "junk"))` still
   answered 1 (row 1), and the bound alone moved 15 anthill-core rows (recorded on the ticket).
6. **A flexible variable is read off the value correctly** — today through the table's run-time
   dictionary, §5.2's open condition: over `rule ll(?w: List[T = List[T = ?t]]) :- true`,
   `ll([[?a], [red()]])` answers `?a = red`, `?a = green`; `ll([[], []])` is definite (no element
   is read); `ll([[?a]])` is conditional, waiting on the element's domain.

**The rule.** `SortDomain` gets a second rule member, `check`, beside `fill`, through the same
dictionary:

```anthill
sort SortDomain
  sort T = ?
  provides Fillable[T = T]
  rule check(?x)                 -- ?x is a T: a bound value is walked, an unbound part waited on
end

List provides SortDomain[T = List[T = T]] :- SortDomain[T = T] where
  rule fill(nil) :- true
  rule fill(cons(head: ?h, tail: ?t)) :- fill(?t), SortDomain[T = T].fill(?h)
  rule check(?x) :- nonvar(?x), checkCase(?x)
  rule checkCase(nil) :- true
  rule checkCase(cons(head: ?h, tail: ?t)) :- check(?t), SortDomain[T = T].check(?h)
end
```

- **The cases are `fill`'s, the constructor in the head** (`checkCase`'s), so a bound value selects
  its one clause and none is proposed to it and refuted. The derivation emits `fill`, `check` and
  `checkCase` from one walk of the constructors (§1). `checkCase` is a rule of the block and no
  member of the spec (§2).
- **`check` WAITS where `fill` GENERATES, by ordinary semantics** (§2: a block's rules mean what a
  sort's do). kernel-language §8.3: a clause whose body asks `nonvar` of an unbound variable of its
  caller does not run while it is unbound; it is asked again after the caller's remaining goals,
  and its answer is conditional if nothing has bound it. `check`'s one clause is such a clause, and
  the recursion goes through `check`, so each level waits on its own open part: at
  `List[T = Bool]`, `check([?a, true])` checks `true` and waits on `?a`; `check(?l)` waits whole.
  MEASURED 2026-11-27, the same shape over a plain list (`rule chk(?x) :- nonvar(?x), cs(?x)`,
  `cs(nil)`, `cs(cons(head: ?, tail: ?t)) :- chk(?t)`): `chk([1, 2])` is true; `chk(?l)` is
  conditional, its residual `nonvar(?l), cs(?l)`; `rule later(?l) :- chk(?l), ?l <=> [1, 2]` is
  definite, `?l = [1, 2]` — the waiting clause ran once the later goal bound it; `rule partial(?l)
  :- chk(?l), ?l <=> cons(head: 1, tail: ?t)` is conditional on the open tail. An earlier draft of
  this section stated the waiting at §3's dispatch instead, which would have given `check` a
  semantics no rule in a sort has.
- **A primitive's `check` is the kernel's outer-type test**, kept as a builtin — the question
  `domain` answers today, which already waits while its value is unbound — and no longer a name a
  program writes: `Int64`'s block reads `rule check(?x) :- <outer-type test>(?x, Int64)`, as its
  `fill` does. `Bool`'s is `List`'s shape, with `checkCase(true) :- true` and
  `checkCase(false) :- true`.
- **Its dictionary is threaded as `fill`'s (§4)**: built at load at a concrete type; the citation's
  instance at a sort's parameter (row 2's `T`); the caller's `requires` slot at a rigid; an open
  condition (§5.2) at a type not pinned at load, read off the value once a part pins it (row 6). A
  value pins only a FLEXIBLE variable — a rule's own. A rigid is never read off a value (row 3's
  mistake).
- **`Fillable` is unchanged.** It is the interface a solver asks for (`fill`); `check` is
  `SortDomain`'s.

**What each use becomes:**

| today | under §9 |
|---|---|
| a written `anthill.kernel.domain(?x, T)` | `SortDomain[T = T].check(?x)`, `T` threaded: row 2's `isT(true)` answers 1 |
| the whole check of a typed column with no fill | that type's `check`: a function type, a spec, an abstract sort and a tuple each get a `SortDomain` provision whose `check` is the outer-type test and whose `fill` waits (open questions 4 and 9) |
| a typed query variable `?x: T` | as a typed column |
| an infinite primitive's `fill` | the same clause, through the provision written in stdlib source (§1); `check` is the same clause |
| the guard `__domain_guard` in front of a body | open question 8 |
| the residual `domain(?_, Int64)` | the waiting clause's body (`nonvar(?_), checkCase(?_)`, as measured above), or a primitive's outer-type test |

**A goal at a rigid is a requirement.** A rigid `X` has no value at run time; what knows its domain
is the dictionary its caller hands. So a `fill` or a `check` at `X` is a requirement on `X` — 065's
rule for `TypeValue`, applied to `SortDomain`: declared on the signature, never inferred, handed in
by the citation. A citation at the caller's rigid `X` whose enclosing signature does not hold
`requires SortDomain[T = X]` is a load error at the citation, naming that clause (row 4 today: a
run-time flounder). This is kernel-language §5.2's refusal of a forwarded rigid, applied to the typed
column's own requirement (§4); today that requirement is not held to it. Two consequences:

- **A value the typer has at `X` needs no check.** An operation parameter `v: X`, a part of one, a
  typed call's result conforms by type preservation, so its column is TRUSTED — WI-20261124-YFD7F's
  `__trusted` slot, extended to a citation from an operation body (that ticket's S2 left it out).
  So `has[X](v)` keeps loading without the requirement, and runs no check. Only a column the call
  leaves OPEN (generation) or hands a value the typer does not have at `X` (a downcast from a wider
  type) needs the dictionary.
- **A generic operation that fills or checks at `X` is callable only at a type with a `SortDomain`.**
  The requirement on its signature says so where it is called.

**The real case** is 067 §4's solver written once over any collection
(`docs/brainstorms/fillable-collection-landscape.md` §4): `sort Sat[C] requires
PersistentCollection[C = C, Element = Bit]` with `rule model(vs: C)`, whose guard and fill are both
at the rigid `C`. Cited at `Sat[C = Bag[T = Bit]]`, the dictionary is built at the citation; cited
from `solveAny[C2]()`, it is `solveAny`'s `requires SortDomain[T = C2]`, or a load error.

**What it gives.** YFD7F's S4 becomes buildable: an inferred concrete column gets `check` and no
`fill`, so a value from a query is checked where it enters (row 1's junk list refused) and nothing
generates — the 33 rows the fill moved stay as they are.

## Open questions

1. ~~A body-less `rule fill(red)` in a `where` block.~~ **SETTLED by §2's decision:** it is a
   declaration, as in a sort, and a case is written `:- true`. (Measured: a probe's body-less
   `rule boxCase(?t, nobox())` answered nothing. 060 §2.3 and 060-implementation print the derived
   cases body-less, and are corrected with S5.)
2. **Rounds.** Generation by size is asked of a `SortDomain` fill. For any spec's rule member, or
   only for `Fillable.fill`? The user's objection (2026-11-27): rounds make the fill a rule with a
   generation of its own, against §2's "same semantics as a rule in a sort". Today the budget is
   spent only by a case of a DERIVED fill (`is_derived_fill_relation`); with the table gone it is
   found through the provision instead. A general fair combinator in goal position (the goal form of
   `LogicalStream.interleave`, and a fair conjunction) would remove the special case, and was set
   aside as too large a change (user, the same day).
   COST, MEASURED 2026-11-27 (the fewest `--max-steps` giving n answers, debug CLI):

   | n answers | `rule nats(?x: Nat) :- true` (rounds) | the same relation written depth-first |
   |---|---|---|
   | 5 | 90 | 28 |
   | 10 | 305 | 58 |
   | 20 | 1 110 | 118 |
   | 40 | 4 220 | 238 |

   Rounds are QUADRATIC where a type has one member per size (`Nat`): round k re-walks every smaller
   member and discards it at the round's end. Plain depth-first is linear. Where members grow
   geometrically with size (`Tree`, `List[T = Letter]`) the last round dominates and the overhead is
   a constant factor (reasoned, not measured). A sort of nullary constructors only opens no round,
   and a bound value is checked in round 0. WI-743's two ordering rules already made ONE recursive
   field per case fair, so rounds buy reachability only where two infinite parts share a value (two
   recursive fields, a tuple of two, adjacent infinite typed columns, two holes at an infinite
   element): opening a round only there would keep `Nat` and a free `List` linear.
3. **Coherence by carrier (§5.1).** `SortDomain`'s alone, or a property a spec declares?
4. **Tuples.** A tuple has no sort to carry a provision (065 §2 step 2 is open), and its domain is
   built from its components' today, with written `SortDomain` at a tuple refused (HWD8A). Which
   provider answers `SortDomain[T = (Colour, Size)]` — a builtin one, or `NamedTuple`'s?
5. **Where a written domain may stand.** On its carrier only, or a witness sort too (`W provides
   SortDomain[T = Colour]`, the je2mt / cxr5b rows)?
6. **The spec's side: a declared rule, or an operation returning a `Relation`?** **DECIDED IN
   PRINCIPLE (user, 2026-11-27): "in theory it should not be difference between rule and operation
   which return relation."** A rule IS an operation returning a `Relation` — 052's title ("rules as
   stream-valued operations"), whose status still lists "operation/relation shared-name syntax" as
   open. The equivalence has two directions: a rule cited by name is a `Relation` value (052,
   delivered); and a `Relation` value in goal position is the rule's goal, run in place with the
   dictionaries its citation carries (MISSING, measured below). So a spec member declared `rule
   fill(?x)` and one declared `operation fill() -> Relation[T = (x: T)]` are one member, and a
   provider implements it in either spelling. The general statement belongs to 052; this proposal
   uses it. The record that led here: the user asked
   (2026-11-27) why `fill` cannot be an operation that returns a relation and works exactly as a
   rule. MEASURED the same day: with `rule apply1(?p, ?x) :- ?p(?x)`, `apply1(colours, ?x)` — the
   rule's NAME passed as a value — answers `red`, `green`, `blue`, run in place (`ho_apply`); but
   `apply1(D.pick(), ?x)`, where `operation pick() -> Relation[T = (x: Colour), E = {Error}] =
   colours`, loads clean and answers NOTHING, with no error: `ho_apply` takes a predicate name, and
   a `Relation` value is quietly no predicate. With one change — a `Relation` applied in goal
   position runs its rule in place, with the dictionaries its citation carries — `SortDomain`'s
   member could be an ordinary operation, dispatched by the ordinary operation machinery, whose
   provider cites its block's rule (§2), and §3's resolver dispatch would not be needed. Unknown:
   whether a citation's dictionaries reach the clauses through an applied `Relation`; the cost of an
   evaluator call per dispatch through a passed dictionary. The silent empty answer is a defect
   either way.
   **SPELLING DECIDED (user, the same day): the declared rule**, "if declared rule is better to
   maintain". It is: `Fillable.fill` is declared so already; the resolver already replaces a fill
   goal in place (§3), so generalising it touches one dispatch site; the operation spelling would
   need the missing direction AND an evaluator call per dispatch through a passed dictionary — an
   eval→SLD crossing on the hottest path a fill has. The equivalence stays the principle, for 052 to
   state; its missing direction is not built here.
7. ~~**A derived member beside an author's rule of the same name.**~~ **WITHDRAWN with §2's
   correction (user, 2026-11-27).** The question came from §2's earlier draft, which made a
   provision's rule a rule of the providing sort, `S.fill`: a derived member and an author's
   unrelated `fill` in `S` would then share one name, and the decision taken on it was a load refusal
   of the author's rule (the `<Sort>.induction` precedent). A provision's rules are its own sort's
   (§2), so `S` has no `fill` of its own, an author's rule `fill` in `S` is unrelated and nothing is
   refused, and a citation `S.fill` does not cite the domain. A domain wanted as a value stays a typed
   rule cited by name (`rule colours(?x: Colour) :- true`).
8. **The guard in front of a body (§9).** `__domain_guard` is shallow today, so a body never runs
   on a value of the wrong type: `add(2.5, 1, ?y)` under `?x: Int64` faulted before the guard
   stood there (WI-742). Under §9 it is either the deep `check` — a walk at entry, which YFD7F's
   trusted slot drops inside the typed program, so a call inside pays nothing — or the outer-type test,
   shallow as today, the deep check left to `fill` after the body. Which?
9. **A type with no constructors (§9).** A function type, a spec, an abstract sort: a `SortDomain`
   provision each, whose `check` is the outer-type test and whose `fill` waits ("EVERY type has one",
   `reflect.anthill`, user 2026-09-25) — or the outer-type test called directly where such a column
   stands, with no dictionary?
10. **The member's name (§9).** `check`, or another (`conforms`, `member`)? `fill` already checks a
    bound value; the new member is the one that never generates. The name collides with no sort's
    own rule (§2): it names a member of `SortDomain`, and `checkCase` a rule of each block.

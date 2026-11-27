# 077: A spec's rule member is implemented by a provision — a sort's domain is an ordinary `SortDomain` provision

## Status: Draft (2026-11-27). Written with the user while working WI-20260911-WT8WG: the user's call, "fix the general machinery", over making the per-sort table the one source. Nothing is built. §5's three changes to the requirement machinery are the open part and are measured before anything else (§8, S1).

## Amends: [052](052-rules-as-stream-valued-operations.md) (a `Relation` applied in goal position runs its rule in place — open question 6), [060](060-clause-level-requirements-and-typed-heads.md) §2.3 (how `fill` is threaded), [066](066-provision-member-blocks.md) §3 (a `where` block holds operations only), [067](067-fillable.md) §3 (`fill` found "through a map of the rule member's own"); `docs/kernel-language.md` §5.3 (*A closed sort defines its domain*) and §8.7.

## Relates to: WI-20260911-WT8WG (retires `<Sort>.domain`; its items 3 and 4 are this proposal), [060.1](060.1-written-rule-requirements.md) (a rule declares its requirements), [065](065-type-value-requirement.md) (`TypeValue`, derived for every sort, never written), WI-20260830-X9PB4 (the wildcard rule), WI-860 (a passed dictionary and a local row must agree), WI-20261115-YR3N7 (the head decides the mode), WI-20260911-09E6M (generation by size), WI-20261116-HWD8A (tuple domains), WI-20260911-5TK6B (`Bool`).

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
sort Colour                                   -- unconditional: the members are the sort's own rules
  entity red
  entity green
  entity blue
  provides SortDomain[T = Colour]
  rule fill(red) :- true
  rule fill(green) :- true
  rule fill(blue) :- true
end

List provides SortDomain[T = List[T = T]] :- SortDomain[T = T] where      -- conditional: its block
  rule fill(nil) :- true
  rule fill(cons(head: ?h, tail: ?t)) :- fill(?t), SortDomain[T = T].fill(?h)
end
```

- **Inside the block**, `fill(?t)` is the provision's own member, called with the same dictionary
  (the recursive field); `SortDomain[T = T].fill(?h)` calls through the provision's CONDITION (the
  field typed by a parameter). That is 066's rule — a provision's conditions are in scope for the
  members written in its block — extended from operations to rules. It is what `__domain_sub(?self,
  k)` hand-codes today.
- **The cases stay one clause per constructor, the constructor in the head** (YR3N7): a bound value
  selects its one clause, an unbound one matches every head in clause order.
- **Where the clauses are written follows the operations' rule** (user, 2026-11-27: "we have rule
  in sort"). A sort body already holds rules, and a sort's own operation already implements a spec
  operation of a provision the sort makes. So an UNCONDITIONAL provision's rule member is the
  carrier's own rule of that name, in its body — `sort Colour { … provides SortDomain[T = Colour]
  rule fill(red) :- true … }`, the shape the je2mt / cxr5b witnesses already write (with `domain`
  for `fill`), and no grammar change. Only a CONDITIONAL provision needs its block, for the reason
  066 gives operations: its conditions are in scope for the members written inside it and nowhere
  else. There the block admits rules beside operations.
- **A primitive's provision is written in the stdlib's source**, not in Rust:
  `Int64`'s body gains `provides SortDomain[T = Int64]` and `rule fill(?x) :- domain(?x, Int64)`, and
  `Bool`'s two cases (`rule fill(true) :- true`, `rule fill(false) :- true`) in place of
  `fill_derive::FINITE_PRIMITIVES`.
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

## 2. A rule in a provision IS a rule of the carrier

**DECIDED (user, 2026-11-27): "rules in provision should have exactly the same semantics as rules in
an ordinary sort."** A rule written in a provision's block is a rule of the carrier, as 066 makes a
block's operation an operation of the carrier (`Pair.eq`). Nothing about it is new:

- it is the carrier's rule `S.fill`, found by name as any sort rule is, and cited as any sort rule is
  (`List[T = Letter].fill.takeN(5)`, through the citation channel 5G28A built);
- a body-less one is a DECLARATION (061), exactly as in a sort — a case is written `:- true`;
- a rule and an operation of one name in a carrier are what they are in a sort;
- the ONE difference is 066's, carried over from operations: the provision's conditions are in scope
  for the rules written inside its block, and only for them. They are those rules' declared
  requirements (060.1), supplied by whoever cites the rule or dispatches to it.

So there is no member table for rules. 067 §3's collision came from filing the rule in
`SortOpsTable`, an OPERATION table keyed by short name; a rule never enters it. The per-sort table's
fields become readings of the carrier and its provision: `fill` the carrier's rule by name;
`params`, `conditions` and the layout the provision's own (`dict_layout`); `kind` gone (derived and
written are both provisions); `reads` and `fielded` computed from the rule's clauses.

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
- **a `T` not pinned at load** (`?x: List`): a dictionary with an OPEN condition (§5.2), read off the
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

**5.2 Open conditions.** A dictionary may hold a condition not yet resolved — `SortDomain[T = ?t]` —
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
- both defects of the problem's row 2, by construction.

## 7. What stays

The derived cases and their order (YR3N7, WI-743's two rules), generation by size (09E6M), the type
guard in front of the body and the fill after it, `Fillable` as the interface (`SortDomain provides
Fillable`), and every answer every row gives today.

## 8. Stages

| stage | what | flips |
|---|---|---|
| **S1** | MEASURE, nothing built: (a) the cost of `SortDomain` rows for every sort, on the optimized build; (b) which of `dictionary.rs`' and WI-860's checks refuse a dictionary with an open condition; (c) a census of short-name collisions in `SortOpsTable` between an operation and a would-be rule member | nothing — decides §5.2's form and §5.3's lazy filing |
| **S2** | a carrier's own rule implements its spec's rule member, as its own operation does; rule members in a CONDITIONAL provision's `where` block (tree-sitter and fastparse); the member table keyed by spec member; dispatch in the resolver (`apply_domain` generalised); the derivation EMITS provisions with members, read into the old table so no answer moves | a written `provides SortDomain[…] where rule fill(…) … end` loads and answers |
| **S3** | §5.1 lookup by head, §5.2 open conditions, §5.3 rows; typed columns resolve through the requirement machinery (§4) | row 1's witness answers one count on every path; row 2's rule loads and answers |
| **S4** | delete the table (§6); primitives in stdlib source; hand-written domains as provisions, parameterised included | row 4's `Box` written as a provision answers 4 / 2 / 3 |
| **S5** | kernel-language §5.3 and §8.7, 060 §2.3, 066 §3, 067 §3 — the text agreed with the user first | — |

WT8WG's items 1 (`Colour.domain` an ordinary name) and 2 (its citations moved to typed rules) do not
depend on this and can land first; its items 3 and 4 are S4 and S5.

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
   provider cites the carrier's rule (§2), and §3's resolver dispatch would not be needed. Unknown:
   whether a citation's dictionaries reach the clauses through an applied `Relation`; the cost of an
   evaluator call per dispatch through a passed dictionary. The silent empty answer is a defect
   either way.
   **SPELLING DECIDED (user, the same day): the declared rule**, "if declared rule is better to
   maintain". It is: `Fillable.fill` is declared so already; the resolver already replaces a fill
   goal in place (§3), so generalising it touches one dispatch site; the operation spelling would
   need the missing direction AND an evaluator call per dispatch through a passed dictionary — an
   eval→SLD crossing on the hottest path a fill has. The equivalence stays the principle, for 052 to
   state; its missing direction is not built here.
7. **A derived member beside an author's rule of the same name.** By §2 a sort's `rule fill` is the
   member only of a `SortDomain` provision the sort writes, as a sort's operation implements a spec
   operation only of a provision it makes. A DERIVED provision's rule must then not take the name
   `S.fill` from a sort that has an unrelated rule `fill`: keep the derived rule under an internal
   name (`S.__fill`, as today) bound to the member, or refuse the unrelated rule?
   **DECIDED (user, 2026-11-27): a load refusal.** In a sort whose domain is DERIVED, a rule the
   author writes under the derived rule's name is refused at load: the name is the domain's. The
   refusal names the two ways out — write `provides SortDomain[T = S]`, and the rule IS the sort's
   domain (nothing is derived), or rename the rule. The precedent is `<Sort>.induction` (kernel-
   language §5.3: "the principle owns its name", an operation or rule written under it refused). So
   the derived rule takes the member's own name, `S.fill`, and no internal name is needed.
   CONSEQUENCE, to confirm with S5's text: `S.fill` is then an ordinary sort rule (§2), so a
   citation of it is a citation of the sort's domain — the value face the 2026-11-02 decision
   retired, under the member's name. Today such a citation is refused anyway: a relation citation
   takes no compound head (`a compound head argument … is not yet supported`, measured on this
   proposal's probe), and the cases have constructor heads. A domain wanted as a value stays a typed
   rule cited by name (`rule colours(?x: Colour) :- true`).

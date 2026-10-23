## Attributes

- id: WI-20261003-QV5W5-implement-proposal-069
- created: 2026-10-03T10:06:09Z

- status: Claimed
- status_agent: claude
- status_at: 2026-10-23T05:46:46Z

- acceptance: cargo-test, scaland-sbt-test

- depends_on: WI-20261001-80ZV8-a-bare-parametric-sort-means, WI-20260821-6WVJB-a-predicate-s-clauses-must-all

- tags: proposal-069

## Description

Implement proposal 069 declaration-site defaults end to end. Add operation value-parameter defaults, entity-constructor field defaults in construction positions only, explicit operation type-parameter defaults, and sort/effect-row parameter defaults in Rust, Scala, and tree-sitter. Type inference must solve without defaults first, install defaults once for omitted still-free parameters in declaration order, then resume solving before validation; explicit ? suppresses a default. Resolve the kernel-language 4.4/8.1 contradiction by declaring Function.E default {}, while Function[A, B, ?] stays open. Preserve full runtime arity, make spec declarations own operation defaults, reflect and persist defaults, replace WI-850 refusal tests with driven controls, and cover dependent defaults, wrong kinds, forward references, constructor expression versus pattern omission, function-value full arity, and Function purity. Acceptance: rustland/scripts/test.sh passes, scaland sbt testFull passes with the expected full test count, and npx tree-sitter test passes.

## Changes

### 2026-10-04T13:54:32Z — feedback — claude

PROPOSAL 069 §2 REWRITTEN for proposal 070 as it stands (user, 2026-10-04: "Update 069 proposal"): inside a sort's own definition a reference to the sort is read as EVERYWHERE — a left-out slot takes its declared default there too, a non-defaulted one is `?` (070 §1.3), and this instance is written `Self`. The paragraph "the self tie wins over the default", the bridge paragraph "In proposal 070's terms", the parenthesis closing the four-spellings restatement, the sentence on WI-1082 and the `AsymmetricPair` acceptance row are rewritten; 070 §7's "to confirm" is settled; the spec's adopted-not-implemented note says the same. TWO OBLIGATIONS THIS ADDS TO THE IMPLEMENTATION, both recorded in 069 §2: (1) until 070's stage (e) the loader writes an anonymous `?` into each slot a reference to the ENCLOSING sort leaves out (`Loader::own_sort_slots_left_out`); an explicit `?` is 069's opt-out, so the fill must leave a DEFAULTED slot out, or the declaring sort is the one place its own default never applies. (2) 070 §1.4's carrier check (`check_sort_parameter_carriers`) reads the stored signature, where a left-out slot of the enclosing sort is that `?`; a slot holding an INSTALLED default is neither the carrier nor open, so `second_of2(p: AsymmetricPair) -> T2` would load — the check must go on reading a defaulted slot the author left out as left out. Acceptance row for both is in 069 §5 (the `AsymmetricPair` row, with its control).

### 2026-10-04T21:39:51Z — feedback — claude

Proposal 070's stage (e) (WI-20261001-80ZV8, 2026-10-04) deleted the loader's `?` fill for a reference to the enclosing sort, so the first of the two obligations recorded for this ticket — the fill must leave a DEFAULTED slot out — is moot: nothing writes a `?` into a slot left out. The second stands and is the one to design for: 070 §1.4's carrier check (check_sort_parameter_carriers, typing/sorts.rs) reads the STORED signature, where a slot the author left out is absent; once a default is installed into such a slot it is neither the carrier nor open, and `second_of2(p: AsymmetricPair) -> T2` would load — the check has to be given what the author wrote. The check also reads an alias as the type it stands for now (alias_expansion), so a default installed through an alias's target needs the same care. Proposal 069's implementation note is updated to say this.

### 2026-10-05T08:45:46Z — feedback — claude

A QUESTION FROM WI-20260925-0RRQP, to decide before plan step 3 (user, 2026-10-05; no dependency edge in either direction). 0RRQP ties a rule clause's variables to its sort's parameter through a constructor's result type: in `rule order(?p, ?c) :- ?p <=> box(a: ?x, b: ?y), …` inside `sort Box`, `?p: Box[T = t]` and `?x: t` share a clause variable `t` that a CITATION binds later, by column unification. Once `Box` declares `T = Int64`, 069 §2 meets `t` from two sides: step 4 installs the default on an omitted slot still unbound at its elaboration boundary, and "a rule under `sort Box[T = Int64]` that omits `T` matches `Box[Int64]`". WHICH HOLDS for a constructor in a PATTERN position whose `T` nothing in the clause fixes: (a) the clause is the boundary — `t` is `Int64`, `order` is a rule about `Box[Int64]`, and a citation at `Box[T = String]` answers nothing or is refused; or (b) the slot is not omitted but open by inference — `t` stays the clause's variable for the citation to bind, and the default reaches only a WRITTEN type that leaves `T` out (`?p: Box`). §1.2 settles a pattern's VALUE defaults (never filled) and says nothing of the type parameter of the constructor's sort. A driven row for the reading chosen, with its control. No program declares a default before this ticket, so 0RRQP cannot meet the case and does not wait on it.
### 2026-10-14T08:35:07Z — feedback — user

A CHECK FOR THIS TICKET (user, 2026-10-14), found by the family e-applied-arrow: under the interim reading an unwritten E accepts any row, so let w: Function[A = Cell[V = Int64], B = Int64] = lambda (z: Cell[V = Int64]) -> put(z, 5) is admitted, and then w(q) in an operation that DECLARES NO EFFECTS runs and writes q (552) — the write is lost at the application. With Function.E default {} the lambda is refused at the annotation; acceptance should drive that program to that refusal. The family lists the program as an exception naming this ticket.

### 2026-10-20T19:31:18Z — feedback — claude

Now depends on WI-20260821-6WVJB (one arity per predicate, unblocked 2026-10-20 when WI-20260821-ZW940 was closed as decided). Once it is delivered, 069's arity check for a declaration that carries a default is the general rule, and needs no gate of its own: implement 069's omission reading on top of it rather than a defaults-only arity check.

### 2026-10-23T05:46:40Z — feedback — claude

SCOPE NARROWED TO STAGE 1 (user, 2026-10-23: five stage tickets). This ticket is now 069's SORT AND EFFECT-ROW PARAMETER DEFAULTS: `sort Box[T = Int64]`, `sort T = ? default Int64`, `effects E = ? default {}` (§1.4); a written type application that leaves a defaulted slot out takes the default, in every position (§2, context-free), dependent defaults (`T2 = T1`) tied to the slot they name, forward references and wrong kinds refused at the default; an explicit `?` keeps the slot open; 070 §1.4's carrier check reads what the author wrote; a constructor call's sort parameter that inference leaves unbound takes the default (§2 steps 4–5); `Function` declares `effects E = ? default {}` and §4.4 / §8.1 are restated (§4, §7 step 6); tree-sitter, Rust, Scala, reflect and persistence of the sort-parameter default. The other surfaces are filed: stage 2 operation type-parameter defaults WI-20261023-GBH5F, stage 3 operation value defaults and `result:` WI-20261023-CX743, stage 4 entity-constructor defaults WI-20261023-FHT5Z, stage 5 rule-column defaults WI-20261023-9XXBW; WI-188 now depends on stages 3 and 4. THE 0RRQP QUESTION (2026-10-05 note) IS DECIDED, reading (b) (user, 2026-10-23): in a rule clause a constructor in a pattern position whose sort parameter nothing in the clause fixes leaves that parameter a clause variable, which a query or citation binds — `rule same(?p) :- ?p <=> box(a: ?x, b: ?x)` under `sort Box[T = Int64]` answers `Box.same(box(a: "s", b: "s"))`; the default reaches only a WRITTEN type that leaves `T` out (`?p: Box`). Acceptance row for this ticket, with its control.


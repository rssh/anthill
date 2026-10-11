## Attributes

- id: WI-20260925-0RRQP-rule-body-typing-does-not-tie
- created: 2026-09-25T14:45:27Z

- status: Open
- status_agent: user
- status_at: 2026-09-25T14:45:27Z

- acceptance: cargo-test, scaland-sbt-test

- tags: typing

## Description

RULE-BODY TYPING DOES NOT TIE A BODY TERM TO ITS ENCLOSING SORT'S PARAMETERS — so a condition inside a rule of a parametric sort cannot be matched to that sort's own `requires`, which rules see (user, 2026-09-25, recorded on WI-20260925-P7VP4).

MEASURED 2026-09-25 (P7VP4's probe):

  sort Box
    sort T = ?
    requires O: WeakOrd[T]
    entity box(a: T, b: T)
    rule order(?p, ?c) :- ?p <=> box(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)
    operation orderOf(p: Box) -> Int64 effects {Error, Error[EmptyStream]} = order(p).head.c
    operation directOf(p: Box) -> Int64 = match p case box(a, b) -> WeakOrd.compare(a, b)
  end

`Box.directOf[T = Int64, O = Descending](box(a: 1, b: 5))` answers 4 — a member operation sees the selection. `Box.orderOf[…same…]` answers -1 (and -1 under `O = Ascending`) — the rule it cites does not. The stamped types of `order`'s clause (`type_rule_bodies` → `collect_rule_var_types`): `?x` and `?y` share ONE per-call placeholder (`compare`'s own `T` instantiated for that call); `?p` is a bare `?T`; `?c` an unresolved logical variable. Nothing says `?x` is at `Box`'s `T`.

WHY — two candidate causes, to MEASURE before choosing: (1) WI-9C2PZ instantiates a callee's type parameters per APPLICATION, and a constructor is a callee, so `box(…)` inside a rule of `Box` gets a fresh `T` like anywhere else (the spec's "within the sort's own definition the bare self reference is the parametricity tie" is about the TYPE `Box`, not a constructor call); (2) `<=>` types its two sides by its own per-call `T`, and the constructor's RESULT type (`Box[T = …]`) never reaches `?p` — with it, `?p: Box[T = t]` and `?x: t` would share `t`, and a citation's column unification would bind it.

WHAT IT BLOCKS: P7VP4's increment 2. `order`'s inferred condition for `compare` — `find_dictionary(WeakOrd, WeakOrd.compare, ?x, ?y, out: ?d)` — is routed at a citation from its witnesses' TYPES, and a witness that is no head column is typed as a fresh variable (`route_requirement_read`), so the route is a wildcard `WeakOrd[T = ?]` against the caller's chain and nothing is routed: the caller's `O = Descending` stops at the rule. Once the witness carries a type tied to the sort's parameter, the router can read its stamped type under the citation's σ (and, if (1) is the cause, the citation's opened parameters — `PendingCitationRoutes` does not carry them yet).

ACCEPTANCE, driven by value: the fixture's `orderOf` answers 4 / -4 under `O = Descending` / `Ascending` through `order`'s condition routed to `orderOf`'s `O` slot; a two-entry sort (`requires OK: WeakOrd[T = K]`, `requires OV: WeakOrd[T = V]`, a rule comparing keys reached through `<=>`) routes each condition to its own slot, not to either by scan order. CONTROLS, stated at their sites: WI-9C2PZ's per-call rows unchanged (`twoeq`, `pair_eq`); a member operation's own dispatch unchanged (`directOf` 4); an uncited rule unchanged (-1, derived from the values); full workspace green via rustland/scripts/test.sh.

## Changes

### 2026-10-05T08:45:28Z — feedback — claude

NO EDGE TO PROPOSAL 069 (user, 2026-10-05: "0RRQP should depends from 069 implementation?" — answered no, then "yes, record both"). 069 supplies nothing this ticket needs: the fixture declares no default (`sort T = ?`); `box(a: ?x, b: ?y)` stands on a side of `<=>`, which 069 §1.2 keeps a pattern, so no field default is filled; and `O: WeakOrd[T]` is a requirement slot, which 069 §9 leaves out (default providers). The one interaction is 069's to answer — what a declared default does to the clause variable this ticket introduces — and is recorded on WI-20261003-QV5W5. READ THE DESCRIPTION AGAINST PROPOSAL 070 (WI-20261001-80ZV8, delivered 2026-10-04 with the tie removed), which it predates. (1) Candidate cause (1) is no longer a defect: it rests on "within the sort's own definition the bare self reference is the parametricity tie", which 070 removes; a fresh `T` at each application of `box(…)` is the rule inside the sort as outside it (070 §1.1). (2) Candidate cause (2) is the route: the constructor's result type reaching `?p` through `<=>`, so that `?p: Box[T = t]` and `?x: t` share one clause variable and a citation's column unification binds it. kernel-language §8.1 states it for a relational clause — "the enclosing sort's parameter is such a variable too — opened per activation and pinned by the value" (the WI-20260911-5G28A paragraph; that ticket is Open, so how much of it the code does is part of the measurement). (3) The fixture's `orderOf(p: Box)` and `directOf(p: Box)` now take ANY box (070 §1.3) where the measurement meant this instance: write `p: Self`. NOT RE-MEASURED: the 2026-09-25 answers (4 / -1) predate 070 and the probe was not re-run for this note — re-run it with `p: Self` before choosing.


## Attributes

- id: WI-20260825-6RRVA-an-equational-law-s-head-and
- created: 2026-08-25T20:14:09Z

- status: Open
- status_agent: claude
- status_at: 2026-08-25T20:14:09Z

- acceptance: cargo-test

## Description

an equational law's HEAD and RHS are UNCHECKED positions: a functor nothing declares loads clean there, so a stale qualified address in a law is indistinguishable from a typo

## Changes

### 2026-08-25T20:14:38Z — feedback — claude

FOUND BY SHIPPING IT. WI-20260825-1WBZT moved `add`/`sub`/`mul`/`zero`/`one` off `algebra.Ring` onto the syntax categories, and `anthill.prelude.algebra.VectorSpace`'s four scalar-side laws went on writing `Ring.sub(Ring.zero, Ring.one)`, `Ring.one`, `Ring.mul(?c, ?d)` and `Ring.add(?c, ?d)` — five addresses that name NOTHING after the move. The full stdlib load stayed clean, both workspaces stayed green, and `/code-review` is what caught it.

THE THREE POSITIONS, DRIVEN SIDE BY SIDE on the built tree, same undeclared name each time:

  rule r: f(?a) <=> Bogus.nope(?a)              inside a sort   -> LOADS CLEAN
  rule r: f(Bogus.nope(?a)) <=> ?a              (law HEAD)      -> LOADS CLEAN
  rule g(?a) :- Bogus.nope(?a, ?a)              (rule-body GOAL)-> "rule-body goal `Bogus.nope` names
                                                                   nothing: no rule, fact, operation,
                                                                   entity, const or builtin is declared
                                                                   under that name, so this goal can
                                                                   NEVER match"
  operation f(x: Float) -> Float = Bogus.nope(x) (op BODY)      -> "expected known operation or
                                                                   arrow-typed variable, got unknown
                                                                   functor"

BOTH SIDES OF THE `<=>` ARE SILENT — head and RHS alike — and the `Ring.sub` spelling loaded byte-identically to the `Bogus.nope` one. So the rule an author reads as "the stdlib loads, therefore the law refers to something" is false, and it is false in the position where a LAW lives.

WI-1034 IS THE SHAPE ONE POSITION OVER, which is the argument that this is a gap rather than a design: that ticket added exactly this check for rule-body GOALS ("so this goal can NEVER match and the rule it is written in can never fire"), with the same reasoning — a term that unifies with nothing is dead, and dying silently is the defect. An equational law whose head or RHS names nothing is dead the same way: no `[simp]` rewrite can ever fire it and no proof layer can ever cite it.

WHAT THE CHECK MUST NOT DO, and this is why it needs a census rather than a one-line copy. `WI-1034`'s own lesson was that "a hypothesis IS a declaration" — the goal check had to learn that `functor_sym` MISSES `Ident`. A law head INTRODUCES its functor by design (kernel-language.md §"A rule head functor is resolved, not declared", WI-896): `rule bound: gte(?x, 3.0) :- gte(?x, 5.0)` is a lemma about an existing name, while a head naming nothing DEFINES a new predicate. So the check cannot simply refuse an unresolvable head — it has to distinguish an unqualified head (which may introduce) from a QUALIFIED one like `Ring.sub` (which cannot introduce anything: `Ring` is a scope that exists and does not hold the member). The RHS has no such escape and is the easier half.

CENSUS TO RUN FIRST: how many law heads / RHS terms across the stdlib, `anthill-stl`, the examples and the fixture suite name something unresolvable today? WI-20260825-1WBZT repaired the five it created (VectorSpace's laws now name `Additive.sub` / `Additive.zero` / `Multiplicative.one` / `Multiplicative.mul` / `Additive.add`) and pinned them through the GUARDED position instead — `wi_1wbzt_syntax_category_test::the_scalar_side_law_addresses_are_live_and_the_ring_ones_are_not` puts each address in a rule-body goal, where the live ones load (`Additive.zero` and `Multiplicative.one` reach "ambiguous dispatch of …", which is proof the name resolved) and every `Ring.*` one is refused as "names nothing". That proxy is what a real check would make unnecessary.

### 2026-08-25T23:55:55Z — feedback — claude

CENSUS RUN, AND THE CORPUS IS CLEAN — but the instrument that says so is incomplete, and that is the finding.

MEASURED on the delivered tree, walking every Term-carried fact whose head functor is `eq` / `unify`, descending BOTH sides' ARGUMENT terms (skipping each side's own top-level functor, which a law head introduces by design):

  190 equational heads scanned
  0   unresolvable dotted functors in law argument positions

So turning the check on would refuse nothing that ships today. That is the number the ticket asked for and it is the green light the body was waiting on.

THE CONTROL SAYS THE WALK IS PARTIAL, which is why this is a note and not a delivery. Restoring the five dead `Ring.*` spellings WI-20260825-1WBZT had left in `algebra.VectorSpace`:

  first cut (descend `Term::Fn` only)     -> 3 hits: Ring.add, Ring.mul, Ring.sub
  plus a `Term::Ident | Term::Ref` arm    -> still MISSES Ring.zero and Ring.one

The two it misses are exactly the NULLARY ones — `vec_scale(Ring.one, ?v) <=> ?v` puts `Ring.one` directly in the LHS's `pos_args`, so the walk visits that slot and does not report it. Adding the `Ident`/`Ref` arm was WI-1034's own lesson re-earned ("`functor_sym` MISSES `Ident`") and it was NOT sufficient: a nullary dotted reference takes some third carrier, or is interned under a name the `contains('.')` test does not see, and I did not establish which.

DO NOT SHIP THE CHECK ON THIS WALK. A refusal built on a descent that silently skips the identities is the same defect one level up: it would report `Ring.mul` and stay quiet about `Ring.zero`, and the quiet half would read as "checked". Establish what carrier a nullary dotted reference takes FIRST — that is the one open question between here and a working check, and it is a much smaller question than the ticket body assumed.

TWO THINGS THE BODY GOT RIGHT AND ONE IT DID NOT. The head/RHS asymmetry is real and both are silent (driven, unchanged). The "census first" instinct was right, and the census came back clean rather than large. But the body says the check "needs its own census rather than a one-line copy" as though the census were the obstacle — it is not; the descent rule is.

### 2026-08-26T05:46:43Z — feedback — user

TWO CORRECTIONS TO THIS TICKET'S BODY, both from delivering WI-20260825-X9RRN, and the second changes what the census would find.

1. THE TEST IT NAMES HAS BEEN RENAMED. `wi_1wbzt_syntax_category_test::the_scalar_side_law_addresses_are_live_and_the_ring_ones_are_not` is now `…::the_scalar_side_law_addresses_are_live_and_a_dead_one_is_still_loud`.

2. THE `Ring.*` HALF OF ITS EVIDENCE IS NO LONGER TRUE, and it was the half this ticket quoted: "every `Ring.*` one is refused as 'names nothing'". Since X9RRN the relative reading has a rung that follows `provides`, so `Ring.add` / `.sub` / `.mul` resolve — to `Additive.add` / `.sub` / `Multiplicative.mul`, the ONE declaration — and `Ring.zero` / `Ring.one` reach "ambiguous dispatch of `anthill.prelude.Additive.zero`" exactly as their `Additive` spellings do.

WHAT THAT COSTS THIS TICKET IS NOTHING, AND WHAT IT COSTS THE CENSUS IS REAL. The gap here is unchanged: an equational law's head and RHS are unchecked positions, `rule r: f(?a) <=> Bogus.nope(?a)` still loads clean, and the five addresses `VectorSpace`'s laws carried after 1WBZT still went unreported for as long as they were wrong. But the CENSUS this ticket asks for — "how many law heads / RHS terms across the tree name something unresolvable today" — must now be run against the POST-X9RRN resolver, because a name reached by conversion is no longer unresolvable. Running it against the old reading would count the whole `Ring.*` family as dead and report a number that is too large.

The renamed row still stands as the proxy this ticket wants replaced, and it is a stronger one than before: it asserts which SYMBOL each address lands on (via the nullary "ambiguous dispatch of …", which spells the target) rather than that the goal loads, and it keeps a `Ring.nope` / `Additive.nope` row that must stay loud — so the proxy cannot be satisfied by a ladder that accepts everything.


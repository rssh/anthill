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


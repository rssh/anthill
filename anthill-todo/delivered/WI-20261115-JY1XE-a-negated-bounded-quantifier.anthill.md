## Attributes

- id: WI-20261115-JY1XE-a-negated-bounded-quantifier
- created: 2026-11-15T15:29:07Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-21T12:19:33Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A NEGATED BOUNDED QUANTIFIER IS NEVER DECIDED: the quantifier's own binder counts as a free variable, so `!(forall ?p in [1, 2]: ?p > 5)` delays as floundering (user, 2026-11-15).

FOUND writing a shop state's invariants in place, one clause each: `rule violation(ShopState(products: ?ps), "product_has_positive_price") :- !(forall ?p in ?ps: ?p.price > 0)`. Every fixture's `violation(?n)` then answered conditionally, all 38 of them. The working spelling routes each negation through a predicate, which costs one wrapper line per invariant (`rule violation(?s, "name") :- !name(?s)`), 34 lines that carry no information.

MEASURED on 53a0d453b (anthill CLI of 2026-11-13):
  1 `rule q :- !(forall ?p in [1, 2]: ?p > 5)`: conditional, residual `not((forall ?_ in [1, 2]: gt(?_, 5)))`. The answer is true.
  2 `!(some ?p in [1, 2]: ?p > 5)`: conditional. The answer is true.
  3 `!(forall ?p in [6, 7]: ?p > 5)`: conditional. The answer is false.
  4 the collection as a rule variable bound to a ground list (`rule r(?xs) :- !(forall ?p in ?xs: ?p > 5)`, asked as `r([1, 2])`): conditional.
  5 Control: the same quantifier behind a predicate, `rule all_big(?xs) :- (forall ?p in ?xs: ?p > 5)` and `!all_big([1, 2])`, answers true.
So the quantifier itself decides; only the negation refuses it.

THE CAUSE. `step_naf`'s groundness gate (kb/resolve.rs, `if open_world_param || !kb.value_is_ground(&inner, &subst)`) delays a negand that holds an unbound variable, since a caller may yet bind it. The negand `forall_in(?p, xs, tuple(body))` holds its binder `?p`, which no caller can bind: the quantifier binds it to each element in turn (§5.3, WI-027). Behind a predicate, the binder sits in the callee's clause and the negand is the ground call, which is why row 5 decides.

PROPOSED: the gate reads a bounded quantifier's binder as bound inside the quantifier. A negand is ground when it is ground apart from the binders of the `forall_in` / `some_in` goals it contains (scoped to their bodies). A free variable of the body other than the binder still delays, so `!(forall ?p in [1, 2]: ?p > ?y)` with `?y` unbound stays conditional. A collection that is not yet ground still delays, as now. Decide with the hereditary-Harrop `(forall(?x), A -: C)` whether its skolemised binder is read the same way.

ACCEPTANCE: rows 1, 2 and 4 answer true, unconditionally. Row 3 answers false. Row 5 is unchanged. `!(forall ?p in [1, 2]: ?p > ?y)` with `?y` unbound stays conditional, and so does `!(forall ?p in ?xs: …)` with `?xs` unbound. Back-out: with the gate as before, rows 1-4 are conditional again.

## Changes

### 2026-11-21T12:19:31Z — feedback — user

Delivered in f3615615d. Decided with the user 2026-11-21: a reused binder is REFUSED at load (not captured, not shadowed), and the hereditary-Harrop discharge's binders read as bound too. The gate (SearchStream::negand_is_ground) instantiates each quantifier's scope as the quantifier does and asks value_is_ground of the instance, so a free body variable and an open collection still delay. Rows: wi_jy1xe_negated_quantifier_test (19); back-outs fail the 7 decided rows (gate), the 7 refusal rows (refusal), and the proof-step row (its reset); 3 controls pass either way. NOT DONE: scaland resolves no bounded quantifier (no gate to change), and its parser does not refuse a reused binder, so rustland refuses a program scaland loads. Follow-up question filed with the user: WI-20261121-9WMZ1 (shadowing).


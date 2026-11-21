## Attributes

- id: WI-20261121-9WMZ1-rule-bodies-have-no-shadowing
- created: 2026-11-21T11:47:20Z

- status: PreOpened
- status_agent: user
- status_at: 2026-11-21T11:47:27Z

- acceptance: cargo-test, scaland-sbt-test

## Description

RULE BODIES HAVE NO SHADOWING, OPERATION BODIES DO: a rule's variables share one clause-wide space, so a bounded-quantifier binder that reuses an enclosing name captures it, while the functional language's let and lambda binders shadow (user, 2026-11-21).

FOUND fixing WI-20261115-JY1XE. §5.3 says a quantifier binder 'is not separately scoped — it shares the enclosing clause's variable space', so reuse captures rather than shadows. MEASURED on c3488633d with the debug CLI: rule c(?p) :- (forall ?p in [1, 2]: ?p > 0) answers c(?z) true for every ?z, yet c(-1) is false; the quantifier ranges when the binder is unbound when it is asked, and reads the captured value when it is bound. JY1XE closes the hole by REFUSING at load a binder that also occurs in the clause outside its own quantifier (sibling quantifiers sharing one binder name stay legal), for forall_in, some_in and the hereditary-Harrop (forall(?x), A -: C) alike (decided with the user 2026-11-21).

THE QUESTION: should a rule-body binder SHADOW, as a let or lambda binder does in an operation body, so one name can be reused at a nested scope without a rename? That would make the refusal a reading: the loader gives each quantifier its own variable (alpha-renaming at conversion), and the two halves of the language agree on what an inner binder means. To decide: whether a rule's ?-variable is a logical variable of the whole clause by nature (a reused name being one variable), or whether a quantifier is a binding construct whose name is local, as in the functional half; and whether the hereditary-Harrop binder follows.

Not started: JY1XE's refusal stands until this is decided.


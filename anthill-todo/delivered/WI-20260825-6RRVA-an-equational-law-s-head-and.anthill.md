## Attributes

- id: WI-20260825-6RRVA-an-equational-law-s-head-and
- created: 2026-08-25T20:14:09Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-06T09:18:26Z

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

WI-1034 IS THE SHAPE ONE POSITION OVER, which is the argument that this is a gap rather than a design: that ticket added exactly this check for rule-body GOALS ("so this goal can NEVER match and the rule it is written in can never fire"), with the same reasoning — a term that unifies with nothing is dead, and dying silently is the defect. An equational law whose head or RHS names nothing is dead the same way: no `@[simp]` rewrite can ever fire it and no proof layer can ever cite it.

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

### 2026-11-06T09:16:22Z — feedback — user

DELIVERED. One check, B8ESG's, widened (decided with the user): an equational law's REPLACEMENT and a PAREN-LESS DOTTED name anywhere in a head are judged by the authority the other positions ask (`symbol_declares_nothing`). `rule r: f(?a) <=> Bogus.nope(?a)` is refused "equation replacement term `Bogus.nope` names nothing" (LoadError::UndefinedEquationReplacement, its own sentence); `vec_scale(Nope.one, ?v) <=> ?v` and `fact holds(Bogus.zero)` "head argument term `Nope.one` names nothing". kernel-language.md §5.3 "Naming one from elsewhere" says so.

THE NULLARY CARRIER THE 2026-08-25 NOTE COULD NOT NAME: a paren-less dotted name parses as a MINTED `field_access` chain, and B8ESG's provenance gate (`!is_minted`) passed over it. It is asked by `Loader::judge_head_dotted_name`: the whole path through `qualified_name_resolves` (the dotted ladder, X9RRN's provision rung included, hidden names counted), judged where resolution FAILS so `Bogus.x.y` is refused once as `Bogus.x`. Not judged, each not a path: a chain rooted at a clause parameter or a local binder, one with a value prefix (rule / const / nullary op), one read through a requirement's name (`R.zero` under `requires R: Ring[F]`, WI-50ZMN's lookup, now shared as `requirement_name_member`). A bare nullary name stays a symbolic constant.

CENSUS, before the check was on: stdlib 104 equation heads and the five examples, zero sites; control — VectorSpace's laws restored with `Nope.sub(Nope.zero, …)` / `Nope.one`, all three refused, HEAD loads them clean. Suites (anthill-core + smt-gen), 9 rows over 5 fixtures: a REAL typo, `anthill.realization.Pending` for `ObligationStatus.Pending` in wi_s8cyd's fixture (fixed); `dbl` (wi_n20ez) and `bar` (equational_attr) never declared (declared); the guarded `bar(?a) = bar(?a)` of wi627 (now exempt, below); `vv.H` over a `let` binder in qk77s (the binding gate). Also found by a probe: `anthill.prelude.Bool.true` written inside a namespace is a relative path since WI-1075 and named nothing, silently.

FROM /code-review, 11 findings, all done:
  * `fact Bogus.zero` + `fact holds(Bogus.zero)` was refused: a paren-less fact is an arity-0 proposition only the discrimination tree holds. A paren-less site now gets the goal walk's backstop.
  * `rule r: Foo.Bar.c <=> 0` judged the subject's inner `Foo.Bar`: a dotted subject's span is one name (EquationHead::subject_name).
  * `R.zero` / `R.add(?a, ?a)` under `requires R: Ring[F]` were refused; MEASURED with the replacement exempt, `R.add` in a `@[simp]` right-hand side type-checks where it fires. Exempt in both checks.
  * `fact holds(Vault.secret)` over an `internal` member loaded silently while `Vault.secret2(1)` was refused: now refused as the forbidden access (`hidden_dotted_internal`).
  * a guarded `bar(?a) = bar(?a) :- g` was refused while `baz(?a) = 0 :- g` loaded: the subject's own functor repeated in its replacement is exempt (EquationHead::subject_functor); wi627's fixture is back as it was.
  * PROPOSED AND DECLINED, MEASURED: exempting a call through a sigil-free parameter (`app(f: (x: Int64) -> Int64, x: Int64) <=> f(x) @[simp]`). `f` stays a bare name in the stored term; with the replacement exempt `app(inc, 4)` died OperationBodyMissing, typed by the arrow or by a sort alias of it. The refusal is true and is pinned (`a_call_through_a_parameter_names_nothing`).
  * stale ClauseHead doc, test gaps (a dotted fact-head row, a control that reaches the check — `K.seven` folds before it), half-done rename (field `head_name_sites`, `check_undefined_head_names`), rustfmt in the changed hunks.

TEST: wi_6rrva_law_names_nothing_test, 15 rows. Back-out table MEASURED over 114 rows (this file plus the suites it touches), ten parts each backed out alone, each failing its own rows (table in the file's module doc); the restored tree 114/114. Families green, no verdict moved. Full workspace 11,729 passed, 0 failed (36 binaries).

LEFT, NOT FILED (to discuss):
  1. The same dotted blind spot in a RULE-BODY data slot: `rule q :- p(Bogus.zero)` loads clean — unresolved, the chain is an application of `field_access` over two bare names, and WI-1058's typer-side check asks only whether `field_access` names something. Not folded in: WI-1058 judges occurrences, where the chain has lost the parse provenance this check reads, and a loader-side copy would be a second mechanism for WI-1058's question.
  2. A dotted sort member written paren-less in a `@[simp]` right-hand side — `f(?a) <=> K.seven @[simp]` (const) or `K.one` (nullary op) — dies in the typer where it fires with "expected a type value recorded where the sort is written … a defect in the walk that built this occurrence"; `K.one()` runs. Pre-existing, loud.
  3. A guarded equation's SUBJECT naming nothing is still not judged: `baz(?a) = 0 :- g` with nothing declaring `baz` loads, and no redex can ever be written.

### 2026-11-06T09:26:07Z — feedback — user

The three LEFT items above are filed with the user: (1) WI-20261106-ES95W, the rule-body data slot; (2) WI-20261106-BYJ0X, a paren-less dotted sort member in a `@[simp]` right-hand side; (3) WI-20261106-9G5K2, a guarded equation's subject naming nothing.


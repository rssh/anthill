## Attributes

- id: WI-20260908-PW9A0-bug-diagnostic-feature-a-rule
- created: 2026-09-08T10:45:39Z

- status: Delivered
- status_agent: claude
- status_at: 2026-09-08T15:56:19Z

- acceptance: cargo-test

## Description

BUG (diagnostic) + FEATURE: a rule-head TYPE-VARIABLE INTRODUCER may only be used BARE as a bound, and using it inside a COMPOUND bound reports 'unresolved name' about a variable the same head introduced. Two scopes; (1) is the floor and must land even if (2) waits.

MEASURED 2026-09-08, three rows over one program (sort Summable with 'sort T = ?'; 'fact Summable[T = Int64]'; 'fact src(1, 7)'):
  CONTROL, LOADS:  rule g[A](?a: A, ?b: Int64) :- src(?a, ?b), Summable[A]
  FAILS:           rule g[A](?a: List[T = A], ?b: Int64) :- src(?a, ?b), Summable[A]   -> unresolved name 'A'
  FAILS the same:  the SIGIL-FREE spelling of that second row (proposal 060 sec 2.1)
The control is what makes this a report rather than a guess: A IS registered as an introducer and IS bounded by the body guard, so the failing row's message is wrong about its own program -- it names A unresolved at a site three tokens from where the head introduced it, and its advice ('import the name you meant' / declare it) is the WRONG REPAIR.

NOT A WI-582 REGRESSION, checked rather than assumed -- do not re-open that ticket. WI-582's description scopes the introducer to exactly the bare form (its own example is 'rule add[T](?x: T, 0) = ?x :- Numeric[T]') and states the desugaring as 'conforms(typeof(?x), T)' with conforms = subsort (sort bound) / provides (spec bound); every example in it is a bare NOMINAL bound. The loader matches that scope literally. NOT A SOUNDNESS BUG either: it is loud, not silent. What it is, is a capability gap whose only surface is a misdirecting diagnostic -- and it had NO TICKET AND NO OWNER (searched the whole store: nothing mentions the introducer machinery, and the only open item citing WI-582 is WI-743, which uses it as background).

LOCUS. kb/load.rs ~20141, the typed_var strip's introducer arm: the substitution of a head-introduced type-var for its guard-given bound fires ONLY for 'Some(TypeExpr::Simple(n)) if n.segments.len() == 1 && rule_tvar_bounds.contains_key(..)'. A PARAMETERIZED bound is 'TypeExpr::Parameterized', so it falls through to the ordinary 'Some(ty_expr) => type_expr_to_value(..)' arm, where A has no symbol. rule_tvar_bounds is populated by load_rule from collect_rule_tvar_names + try_body_tvar_guard.

SCOPE (1) -- THE DIAGNOSTIC FLOOR. When a name that fails to resolve inside a rule-head bound IS a key of rule_tvar_bounds, say that: the head introduced it, it is bounded, and it may currently be used only as the WHOLE bound. Never 'unresolved name', whose repair is wrong. This is cheap and makes the gap honest.

SCOPE (2) -- THE CAPABILITY. Let an introduced type variable appear INSIDE a compound bound: '?x: List[T = A]' meaning 'x is a List whose element type is the bounded A'. That is the natural use and the one a user reached for. It means the introducer substitution must WALK a TypeExpr (Parameterized, and decide about Tuple / Arrow / nested) rather than matching only Simple at the top. Decide and STATE which TypeExpr shapes are admitted; a shape left out must take scope (1)'s located refusal, never the unresolved-name message.

BOTH SPELLINGS, ONE ANSWER. proposal 060 sec 2.1's sigil-free parameter form lowers to the same internal binding, so whatever (2) admits must be admitted for 'a: List[T = A]' too, and whatever (1) refuses must be refused there identically. WI-742 already had to make the sigil-free head DECLINE a ParseAux-bearing head to keep the two in step (it PANICKED on convert_term's unreachable! before that) -- see convert_rule_head_with_params' ParseAux gate and docs/design/060-implementation.md sec 6; that decline is what would be lifted here.

ACCEPTANCE. The CONTROL row above still loads (it must pass either way BY DESIGN -- say so at its test site). Under (1): the parameterized row is refused with a message NAMING the introducer and the restriction, and the SIGIL-FREE row is refused identically. Under (2): both rows LOAD and are DRIVEN -- the clause answers, and a value whose element type is not the bounded A is FILTERED, asserted by value rather than by a clean load. Say at the test sites which rows fail when the introducer walk is backed out. cargo-test green via scripts/test.sh.

## Changes

### 2026-09-08T15:56:11Z — feedback — user

DELIVERED via SCOPE (2), which makes SCOPE (1) vacuous rather than skipped. The two are alternatives ("(1) is the floor and must land even if (2) waits"), and (2) landed, so no bounded introducer ever fails to resolve inside a bound and (1)'s refusal has no population. Commit b4d80829.

THE DECISION THIS TICKET ASKED FOR — "STATE which TypeExpr shapes are admitted": ALL OF THEM, and no shape takes (1)'s refusal, because the substitution is NOT a walk over shapes. It happens at the RESOLUTION (`Loader::rule_head_bound_alias`): inside a rule-head bound, a head-introduced type variable DENOTES the sort its `:- Spec[A]` guard bounds it with, which is a fact about what the NAME means. So `List[T = A]`, `Set[E = List[T = A]]`, `A[T = Int64]`, a tuple element and an arrow parameter all substitute alike, and a bound reaches a name through four doors that each consult one owner. Stated at the site and in kernel-language.md 5.3.

Whether the RESULTING bound then DECIDES is a separate question about bound SHAPES, and it is answered identically for a substituted variable and for a concrete type written in the same place. It also moved while this ticket was open, but by its own commit (7def5556, `domain` RESTRICTS) — the verdict predicate suspended on any non-NOMINAL bound, which is wider than "not determined"; an arrow or tuple bound now decides.

A REFUSAL DID LAND, but for a fault this ticket did not anticipate: an introducer whose NAME ALREADY RESOLVES in scope is refused. Since the variable now shadows at EVERY depth, `g[Bool](?a: List[T = Bool], ...)` could be read as the bounded variable or as the sort `Bool`; measured, it kept opposite rows under the two readings and LOADED CLEAN under both. Corpus cost measured at ZERO across the whole anthill-core suite, stdlib included, with the check shown firing on the colliding rows and silent on three controls.

TWO DEFECTS FOUND THAT WERE NOT IN THE TICKET. (a) The 060 sec 2.1 reclassifier DECLINED any ParseAux-bearing head, so `rule g[A](a: A, ...) :- one(a, ...), Summable[A]` kept `a: A` a named argument and its body's `a` a constant: it LOADED CLEAN and answered 0 where its sigil twin answered 1 — a dead clause with no diagnostic. Lifted to a filter sharing the generic walk's own predicate. (b) An unbounded introducer reported TWO errors, the second being the same misdirecting unresolved-name message; now one.

WHAT WAS TRIED AND REVERTED, recorded so it is not re-attempted: lifting the typed-pattern refusal for GUARDED equations, so `anthill.prelude.Stream`'s six laws could carry `?s: Stream`. The bound installs and the typer prepends its `domain` goal — both observable — but the goal is INERT: nothing evaluates a matched equation's body (WI-20260820-8RJK8, which now carries a note recording typed patterns as a downstream consumer). Driven with an UNSATISFIABLE bound, `kb.simplify` is byte-identical to no annotation at all. Reverted; `a_guarded_equation_keeps_its_refusal` pins BOTH guarded spellings refused and carries that measurement as the reason. Separately worth knowing before 8RJK8 decides anything: annotating those six pays nothing even after it lands, since each operation already declares `s: Stream` — a typed pattern earns its place only where it NARROWS below the signature.

TESTS: wi_pw9a0_rule_tvar_in_bound_test, 10 rows at this commit, stating FOUR separable back-out axes with the row counts each produces, measured by mutating each site rather than predicted, plus the two yardsticks that pass under all four BY DESIGN. wi742's decline row rewritten to the behaviour that replaced it. Full workspace green via scripts/test.sh (6664).


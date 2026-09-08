## Attributes

- id: WI-20260908-PW9A0-bug-diagnostic-feature-a-rule
- created: 2026-09-08T10:45:39Z

- status: Claimed
- status_agent: claude
- status_at: 2026-09-08T12:03:38Z

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


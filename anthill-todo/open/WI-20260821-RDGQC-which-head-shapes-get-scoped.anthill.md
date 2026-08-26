## Attributes

- id: WI-20260821-RDGQC-which-head-shapes-get-scoped
- created: 2026-08-21T10:29:37Z

- status: Open
- status_agent: user
- status_at: 2026-08-21T10:29:37Z

- acceptance: cargo-test, scaland-sbt-test

## Description

WHICH HEAD SHAPES GET SCOPED IS AN INCOMPLETE ENUMERATION, and the four that fall
through share one consequence: the head reaches `remap_name_str`'s bare `intern(name)`
fallback -- ONE GLOBAL NAME -- so two scopes writing it silently share one uncitable
predicate. That is WI-894's defect class, still live in four shapes.

MEASURED, each with a `rule`-shaped CONTROL that scopes correctly:
 * A FACT HEAD. `namespace zzA { fact pfact(1)  rule seeA(?x) :- pfact(?x) }` beside the
   same in zzB with `pfact(2)`: `zzA.pfact` = `zzB.pfact` = `pfact` = NO SYMBOL, and each
   namespace's rule reads the OTHER namespace's fact. CONTROL with `rule` in place of
   `fact`: `zzC.prule` and `zzD.prule` both exist, one clause each. The spec says a fact
   IS a rule with an empty body (kernel-language.md "Facts are rules"), so §"A
   rule-introduced functor is scoped where it is written" governs it.
 * A MULTI-HEAD RULE's functors. `rule lawE: pm(1), rm(9) :- base(0)` in zzE beside the
   same shape in zzF: `zzE.pm` = `zzF.pm` = `pm` = NO SYMBOL.
 * A PAREN-LESS NULLARY head -- WI-20260821-P85Z7, filed, with its own decision (the
   predicate case and the equation case want opposite answers from one function).
 * A head inside a `provides ... language ... end` BLOCK -- WI-20260821-TTHRK, filed,
   with its own decision (the scope is `scope_id(spec_domain)`, which the LOAD phase
   resolves from the block's TypeExpr).

MECHANISM, one enumeration in two places. `RuleHeadCollectPass::at_item` (kb/load.rs,
sub-pass 3) matches `Item::Rule` and `Item::RuleBlock` and drops everything else through
`_ => {}`; `rule_introduced_functor_name` then refuses a multi-head rule
(`r.heads.len() != 1`) and a non-`Term::Fn` subject. Between them they decide which head
shapes are scoped at all, and NEITHER states the enumeration as a decision -- the shapes
that fall through do so silently.

PRE-EXISTING, not introduced by WI-980: the old `RuleHeadPass` matched the same two
`Item` variants and `rule_introduced_functor_name` is untouched by that change. WI-980
rewrote the pass around them, which is why the gap is now visible.

THIS TICKET IS THE ENUMERATION, not the four fixes. Two of the four already have tickets
because each needs a decision longer than its patch. What has no owner is the QUESTION --
which head shapes introduce a name, stated once, in one place, with the fall-through made
loud instead of silent. Decide that first; the two filed tickets then become instances of
it rather than separate policies, and facts and multi-head rules may need no policy of
their own at all.

WATCH FOR: a fact head and a rule head of one name in one scope are two clauses of one
predicate and must stay so; and `rule lawE: pm(1), rm(9)` introduces TWO names, so the
"one introduced functor per rule" shape that `rule_introduced_functor_name`'s signature
assumes has to widen or the multi-head case has to be refused explicitly.

ACCEPTANCE: drive it. Two scopes each writing the same head name in each admitted shape
must give TWO predicates, each answering its own clause and neither the other's -- the
control is that today the goal answers BOTH. Assert the qualified names resolve. For any
shape deliberately left out, the fall-through must be a located diagnostic, not silence.
cargo-test green via rustland/scripts/test.sh.

## Changes

### 2026-08-25T16:57:15Z — feedback — claude

A SECOND CONSEQUENCE OF BULLET 1 (the FACT HEAD), measured while delivering
WI-20260823-VM3YB, and it is worth stating because it is not the one the ticket
describes. Bullet 1 records that two scopes writing one fact name SHARE one uncitable
predicate. The same bare intern also means a fact head that names NOTHING AT ALL is
admitted in silence -- there is no resolution to fail:

  fact NoSuchSortXyz[T = Reg]     loads clean
  fact noSuchPred(a: 1)           loads clean
  fact noSuchNullary              loads clean
  fact noSuchNullary()            loads clean
  fact ..absolute.NoSuchAbs[T=Reg]  loads clean
  rule r(?x) :- noSuchGoal(?x)    REFUSED (WI-1034, the body-goal twin)

The last row is the control: the same question asked one construct over is already loud,
which is what makes the fact side read as an omission rather than a policy.

WHY IT MATTERS BEYOND TIDINESS, with a live witness. `fact Effect[T = K]` is the effect-kind
registration (kernel §5.5). Written with `Effect` MISSING from the import list, the head
mints a bare global `Effect` that is not `anthill.prelude.Effect`, so
`maybe_emit_fact_provides_info`'s `kind_of(functor) == Sort` gate returns early, no
provision is emitted, and the line registers nothing while reading as though it did.
`wi698_row_param_refinement_test` shipped exactly that through a whole review cycle with
its suite green. Any `fact Spec[...]` claim is exposed the same way -- the emission's early
return is silent for every non-sort functor.

NOT ARGUING FOR A BLANKET REFUSAL. §6.1 and `undefined_functor`'s doc both say a
fact-only predicate legitimately keeps an unresolved functor -- `fact parent("a","b")` is
how such a predicate is introduced -- so "names nothing" cannot simply become an error
here. That is precisely why it belongs to THIS ticket rather than to a patch: the
enumeration this ticket owes has to say which fact-head shapes DECLARE and which merely
REFERENCE, and only then can the fall-through be loud. `remap_name_str_inner`'s NotFound
arm already anticipates the answer -- "the refusal belongs where a bare intern is the FINAL
answer, which for the shapes the marker adds is `scan_rule_goal` (a rule head) and
`load_fact` (a fact head)".

VM3YB closed only the effects-side consequence: an effect row naming an unregistered kind
is now refused, so the un-imported-`Effect` spelling above fails loudly at the LABEL even
though the fact itself is still admitted in silence.


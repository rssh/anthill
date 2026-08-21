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


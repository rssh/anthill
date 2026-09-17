## Attributes

- id: WI-20260821-RDGQC-which-head-shapes-get-scoped
- created: 2026-08-21T10:29:37Z

- status: Claimed
- status_agent: user
- status_at: 2026-09-17T09:42:30Z

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

### 2026-09-17T10:16:50Z — feedback — user

THE ENUMERATION SHIPPED; THE LOUD FALL-THROUGH DID NOT. Scope chosen with the user
(2026-09-17): the enumeration only, the three live shapes left as they are.

FIRST, TWO CORRECTIONS TO THIS TICKET'S OWN DESCRIPTION, both measured before acting.

 1. BULLET 3 IS DELIVERED. A paren-less nullary head scopes today (P85Z7 + CZJ2N).
    Driven with a DISCRIMINATING fixture, because the obvious one proves nothing — with
    both clauses TRUE both readers answer 1 either way. Top-level `shared_pl :- bfalse(999)`
    beside `nsx.shared_pl :- btrue(1)`: `nsx.seeX` = 1, `seeTop` = 0. Scoped.
 2. THE MECHANISM CLAIM IS STALE. This ticket says `RuleHeadCollectPass::at_item` "drops
    everything else through `_ => {}`". That catch-all is GONE — WI-1001 / APXSS made it
    an explicit arm per `Item` variant, with a comment saying a catch-all was the bug. So
    the enumeration this ticket asks for ALREADY EXISTS for the CLAUSE census. What had
    no owner was the same explicitness for the MINT, scattered over five sites:
    `head_subject_name`'s `is_minted` guard and its `_ => None` shape arm,
    `subject_introduces`' two conditions, `at_item`'s `Item::Fact` arm, and
    `collect_provides_block`. Each returned a bare `None`.

THE LEDGER, RE-MEASURED ON THIS TREE. Every row is the INVERTED PAIR (P85Z7's idiom):
two sibling scopes, one head name, one clause FALSE and one TRUE, each scope reading
through a unary rule of its own — so a merge is a WRONG ANSWER and not an extra one.

  shape                          scoped?  measured        control
  rule p(1) :- ...  applied      YES      0 / 1           --
  rule p :- ...     paren-less   YES      0 / 1           applied row, unmoved
  rule f(?x) <=> .. equation     YES      two symbols     --
  fact p(1)         fact head    no       2 / 2           same as `rule`: 1 / 1
  rule l: p(1), q(9) multi-head  no       2 / 2           single-head:    1 / 1
  head in provides ... language  no       2 / 2           same, in-sort:  1 / 1

WHAT SHIPPED.

 A. `NoIntroduction` — ONE type, one variant per reason a RULE head introduces no name:
    SeveralHeads(n) / DenialHead / DesugaredSubject / NotAnApplication /
    QualifiedSpelling(name). `head_subject_name`, `subject_introduces` and
    `rule_introduced_functor_name` return `Result<_, NoIntroduction>`.
 B. AND IT DELETED A DUPLICATE WALK, which is the part worth having.
    `bodyless_declares_nothing_detail` was a SECOND walk re-deriving the same shape
    questions in the same order to choose the author's sentence; its own doc said "the
    message and the verdict cannot describe different rules" and its fall-through was a
    `debug_assert!(false)` for when they had stopped doing so — an invariant held by
    hand, asserted only in debug, on a diagnostic path, AFTER the wrong sentence was
    chosen. It is now a `match` on the verdict. The drift it guarded against is real and
    this file records it happening once already (`rule ..nosuchxyz` got "not a functor
    application" while `rule ..nosuchxyz()` got the QUALIFIED sentence).
 C. THE HEAD COUNT MOVED FIRST in `rule_introduced_functor_name`, to the order the
    detail walk already used. No rule changes reading — every count but 1 refused before
    and refuses now.
 D. `wi_rdgqc_head_introduction_census_test` — 8 rows: the three ADMITTED shapes driven,
    the three LEFT-OUT ones PINNED WITH THEIR CONTROLS, and every `NoIntroduction`
    variant driven from source through its sentence with a dedup assertion.
 E. `docs/kernel-language.md` §"A rule-introduced functor is scoped where it is written"
    listed THREE shapes that introduce nothing; it now states all five plus the two
    constructs that never ask, and names the census as where the list is complete.

BACK-OUTS, RUN NOT ASSUMED — my first draft of the ledger was WRONG and the run corrected it.
 * Drop `head_subject_name`'s `Term::Ident` arm: I wrote "1 row fails". THREE do. The
   extra two are `both_spellings_of_a_qualified_head_get_one_reason` and the
   QualifiedSpelling row of the variant census, because `rule ..nosuchxyz` then reaches
   NotAnApplication while `..nosuchxyz()` still reaches QualifiedSpelling — the ORIGINAL
   drift reappearing. That says those rows guard it rather than merely describe it. The
   applied-head row is unmoved.
 * Give `NotAnApplication` the `DenialHead` sentence: EXACTLY 1 row fails, on its dedup
   assertion. That is the drift-catcher the merge buys — before it, the same swap had
   two homes and only one was under test.

AND THE HONEST LIMIT ON PART C: the change is behaviour-preserving, so the five
sentences pass against the PRE-merge code too. Measured byte-identical before and after
(all five, via a stashed build). Those rows are the ledger the merge had to preserve,
not evidence that it happened; their teeth are the second back-out. Said at the site.

/code-review (high) ON MY OWN DIFF FOUND THREE, all fixed before commit, none a
correctness bug: three doc blocks still promising `Some`/`None` (including the comment
that justifies `scan_rule_goal`'s `expect` by naming an Option contract — a reader
auditing that panic would check the wrong invariant); `subject_introduces` cloning the
Cow to build a refusal about the ONE subject shape that is `Owned`, now taken by value
so it moves; and `Clone`/`PartialEq`/`Eq` derives with no reader, reduced to `Debug`
with a note that `expect` renders it.

SUITE: full `rustland/scripts/test.sh`, 0 failures in every binary (wi_tests 4736).

STILL OPEN HERE — the ACCEPTANCE's second half: "for any shape deliberately left out,
the fall-through must be a LOCATED DIAGNOSTIC, not silence". It is not, and it cannot be
until the question this ticket's own feedback poses is answered: WHICH fact-head shapes
DECLARE and which merely REFERENCE. §6.1 and `undefined_functor`'s doc both make
`fact parent("a","b")` a legitimate way to introduce a fact-only predicate, so a blanket
refusal would flood every existing program. The three live shapes are each pinned in the
census with the ticket that owns them (NE0E4 for multi-head, TTHRK for the provides
block, this ticket for the fact head).

### 2026-09-17T14:08:55Z — feedback — user

THE ACCEPTANCE'S THIRD CLAUSE IS DELIVERED, BY A ROUTE THIS TICKET DID NOT ANTICIPATE —
and the route is the user's, not mine. Commits 355b70e9 and be2cb2ef.

WHAT I GOT WRONG FIRST, because it shaped everything after. I reported clause 3 ("for any
shape deliberately left out, the fall-through must be a located diagnostic, not silence")
as BLOCKED, on the reading that a fact head's silence is §6.1's intended behaviour and so
had nothing to diagnose. I proposed a report keyed on the clause census instead. The user
answered: `fact p(x,y)` MEANS `rule p(x,y) :- true`. That dissolves the blocker — there is
no "fact rule" to follow, only one rule and one spelling escaping it. MEASURED on the
shipped tree before changing anything:

  namespace zzA  fact pp(1)  rule see(?x) :- pp(?x)  end   |  2 answers, zzA.pp resolves to NOTHING
  namespace zzB  fact pp(2)  rule see(?x) :- pp(?x)  end   |  2 answers
  the same program written `rule pp(1) :- true`            |  1 each, its own; both resolve

One clause, two spellings, two programs. So the shape was never "left out" — it was
escaping, and clause 3 is satisfied by removing the escape rather than by reporting it.

THE CENSUS I RAN TO SIZE THE FIX WAS THE WRONG POPULATION, and I recommended it. It asked
"will shipped programs break" — no, and that held exactly: 7 fact-head names newly mint
corpus-wide, every reader of all 7 in the scope that writes it, corpus load byte-identical.
What it did not ask is what the language's OWN SUITE encodes, which was 36 rows. Running
the suite would have been the cheaper and truer census. Recorded because the mistake is
reusable: for a change to a language rule, the suite IS the corpus.

EVERY ONE OF THE 36 ASSERTED THE DIVERGENCE, NOT A DESIGN. The decisive one: wi_apxss
recorded "a fact head is UNSCOPED, so one written in a nested `sort` resolves UP to the
enclosing type's predicate" — and the `rule` spelling of that same clause was refused
HERE, TODAY, with nothing applied. §1234's sentence for it is deleted.

TWO PRE-EXISTING DEFECTS CLOSED ON THE WAY, both silent-failure class:
 * A DEFERRED SELECTIVE IMPORT DID NOT REACH THE MINT GUARD (355b70e9, its own commit
   with its own test). `namespace Side { import X.Rec.{freshp}  rule freshp(2) :- true }`
   minted `Side.freshp` and left the import DEAD. It also hid an ownership fault: the
   clause never reached the type's predicate, so 059 R3 had no assembly to refuse. The
   `fact` spelling dodged it only because a fact head declared nothing, which is how R3
   came to look like the thing policing this shape.
 * THE GUARDIANS GATE COULD NOT SEE A FACT. `naming_violations` has always said "a
   generated program may declare only under `guardians.agent.`"; a fact head minted
   nothing, so the rule could never apply to one. It does now.

AND THE wi_apxss LEDGER, RE-MEASURED RATHER THAN INHERITED (the user asked for this
explicitly, and it was worth it): TWO OF SEVEN AXES HAD STOPPED MEASURING ANYTHING. B and
F are about R3's ATTRIBUTION, which a bare head no longer reaches — backing either out
fell ZERO rows against claimed 2 and 1. Restored with three rows reaching R3 through a
QUALIFIED head. Axis A keeps its count of 4 and changed its SET. 74 -> 77 rows.

ACCEPTANCE, CLAUSE BY CLAUSE:
 1. two scopes, same head name, each admitted shape -> TWO predicates  — DONE
 2. assert the qualified names resolve                                 — DONE (51268158)
 3. the fall-through is not silence                                    — DONE, by removing
    the fall-through for the fact head. The two shapes still left out are NE0E4's
    (multi-head functors) and TTHRK's (a head in a `provides … language … end` block),
    each pinned in the census with its owner named.
 4. cargo-test green                                                   — 7127 passed, 0 failed

scaland-sbt-test: NOT RUN. `sbt`, `scala` and `java` are all absent from this machine, so
the criterion cannot be discharged here. The change is rustland-only and touches no
scaland file. SCALAND HAS THE SAME DIVERGENCE — its `ruleIntroducedFunctor` refuses a fact
head identically — and porting it is not in these commits.

STILL OPEN AND NOT IMPLIED FIXED: a bracketed provision claim. `fact Spec[T = K]` whose
functor is not a declared sort loads clean and emits no provision — measured on the
delivered tree (`fact NoSuchSpecXyz[T = Carrier]`). The head now mints a local `Goal`, so
`maybe_emit_fact_provides_info`'s `kind_of == Sort` gate still returns early. No worse than
before; not fixed. It is the second half of the split-by-shape reading the user chose, and
it needs the parse IR to carry whether the head was written with brackets — the CST tells
`application` from a call, the converted term does not. The live witness is on record:
`wi698_row_param_refinement_test` shipped an un-imported `Effect` through a whole review
cycle, registering nothing while reading as though it did.

### 2026-09-17T14:43:50Z — feedback — user

CORRECTION TO THE OPEN ITEM ABOVE — I STATED IT TOO NARROWLY AND PROPOSED THE WRONG FIX.
The user asked about the BRACKETLESS form, which I had not measured. Measuring it moves
the item.

WHAT I SAID: "a bracketed provision claim (`fact Spec[T = K]`) whose functor is not a
declared sort loads clean … it needs the parse IR to carry whether the head was written
with brackets — the CST tells `application` from a call, the converted term does not."

BOTH HALVES ARE WRONG.

1. THE BRACKETLESS FORM HAS THE IDENTICAL DEFECT, so "bracketed" is not the population.
   Measured, all inside a `sort` body:

     fact anthill.prelude.Eq        (functor IS a Sort)   provision emitted + DEPRECATION warning
     fact NoSuchSpecB               (not a Sort)          SILENT — loads clean, emits nothing
     fact NoSuchSpecD[T = Carrier]  (not a Sort)          SILENT

   THE PRECISE STATEMENT is not about brackets at all: the only diagnostic that exists is
   gated on the SAME `kind_of(functor) == Sort` test the emission is, so when the functor
   is not a sort the provision AND its deprecation warning vanish TOGETHER. That is why
   the `Effect` case cleared a whole review — there was nothing to see.

2. THE BRACKET FLAG CANNOT WORK. `fact Box` and `fact somePredicate` are the same shape at
   every level, CST included. There is nothing to key on, so the parse-IR change I
   proposed would have fixed at most half the population and I would have found that out
   while writing it.

AND THE TWO READINGS ARE GENUINELY UNDECIDABLE FROM THE TEXT, which is the real finding.
Inside a sort body BOTH of these are legitimate and correct today:

   sort Rec { fact helper(1) }            an ordinary fact-only predicate, scoped to Rec
                                          (driven: `Rec.see(?x) :- helper(?x)` answers 1)
   sort Rec { fact SomeSpec[T = …] }      a PROVISION

They are told apart ONLY by whether the functor resolves to a Sort — which is exactly the
thing that fails when the spec is not imported. So `fact Effect[T = K]` with `Effect`
unimported is textually indistinguishable from an ordinary fact-only predicate named
`Effect` with a named argument `T`. No diagnostic can separate them.

THE FIX IS SOMEBODY ELSE'S, AND IT ALREADY EXISTS AS A PLAN: finish 058 §4's retirement of
the `fact` spelling of a provision. The deprecation is live and says so at every remaining
site — "the DEPRECATED spelling of a provision (058 §4). Write `provides Spec[…]` …
retiring the `fact` one removes the language's only construct whose meaning depended on
its container". Once `provides` is the only spelling, the ambiguity is gone: a `fact`
inside a sort is unambiguously an ordinary fact-only predicate, §6.1 governs it, and
nothing is silent. AND THE LOUD CHANNEL IS ALREADY THERE — measured:

   provides NoSuchSpecXyz[T = Carrier]   ->  error: unresolved name 'NoSuchSpecXyz' in scope
   fact     NoSuchSpecXyz[T = Carrier]   ->  loads clean

So the author who means a provision already gets the refusal, in the spelling 058 wants
them to use. Nothing new has to be invented; the retirement has to finish.

TWO THINGS TO KNOW BEFORE TAKING IT:
 * OUTSIDE a sort, `fact Spec[…]` was NEVER a provision — measured, a namespace-level
   `fact anthill.prelude.Eq[T = Carrier]` emits NO `SortProvidesInfo` at all and warns
   nothing. That is the "meaning depended on its container" the warning names, so the
   retirement's surface is the IN-SORT spelling only.
 * THE SWAP IS NOT MECHANICAL, and the warning says so: `fact Spec[Carrier]`'s carrier is
   positional and derived, while `provides Spec[…]` inside a sort takes the ENCLOSING SORT
   as provider and the bindings say what the spec is instantiated at. An author who swaps
   the keyword and keeps a bare positional carrier gets a DIFFERENT provision.

NOT FILED AS A TICKET — this is 058's work and I have not been asked to open one.

### 2026-09-17T15:00:20Z — feedback — user

CORRECTION TO MY CORRECTION — the previous note's claim about the NAMESPACE-LEVEL form is
FALSE, and I should not have stated it. Filed as WI-20260917-S8JYF with the real numbers.

I wrote: "OUTSIDE a sort, `fact Spec[…]` was NEVER a provision — measured, a
namespace-level `fact anthill.prelude.Eq[T = Carrier]` emits NO `SortProvidesInfo` at all".
The measurement was wrong: I grepped the `SortProvidesInfo` listing for the NAMESPACE name
`zzT`, and those rows print SHORT names (`sort_ref: Carrier, spec: SortView(Eq, T: Carrier)`),
so the grep could never have matched whatever the answer was. Re-measured by the short
name, BOTH namespace-level spellings emit the provision:

  namespace zz { fact anthill.prelude.Eq[Carrier] }      -> SortProvidesInfo(sort_ref: Carrier, …)
  namespace zz { fact anthill.prelude.Eq[T = Carrier] }  -> SortProvidesInfo(sort_ref: Carrier, …)

WHAT THAT CHANGES. I concluded "the retirement's surface is the IN-SORT spelling only" and
that finishing 058 §4 would dissolve the problem. The census says the opposite: the in-sort
spelling has ZERO users corpus-wide (the deprecation warning fires 0 times over stdlib +
every example + anthill-stl + anthill-todo), while the NAMESPACE-LEVEL spelling has 20
sites across 9 files including stdlib itself and anthill-stl. So the deprecation as scoped
would retire the half nobody uses and leave the 20 real users untouched — the reverse of
what I said.

The defect itself stands and is unchanged: at BOTH levels, a `fact`-spelled provision whose
functor is not a declared Sort loads clean and emits nothing, because the early return and
the only diagnostic share the `kind_of == Sort` gate. S8JYF carries it with the corrected
census, the undecidability argument (an ordinary fact-only predicate in a sort body is
legitimate and textually identical), and the note that `fact Effect[T = K]` at namespace
level is ALSO §5.5's effect-kind registration, so the two levels may not be one question.

TWICE WRONG ON THIS ITEM, both times from a measurement I did not check: first the
population ("bracketed", when the bracketless form has the identical defect), then the
scope. Recorded because the pattern is the reusable part — I was reading greps for absence,
and an absence needs a positive control before it means anything.


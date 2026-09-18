## Attributes

- id: WI-20260917-S8JYF-a-fact-spelled-provision-whose
- created: 2026-09-17T14:59:44Z

- status: Delivered
- status_agent: user
- status_at: 2026-09-17T19:34:43Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A `fact`-SPELLED PROVISION WHOSE SPEC IS NOT A DECLARED SORT DROPS IN SILENCE — and the 058 §4 deprecation that would retire the spelling covers only HALF the population.

THE DEFECT, measured on the delivered tree (be2cb2ef):

  provides NoSuchSpecXyz[T = Carrier]   ->  error: unresolved name 'NoSuchSpecXyz' in scope
  fact     NoSuchSpecXyz[T = Carrier]   ->  LOADS CLEAN, emits nothing, warns nothing

`maybe_emit_fact_provides_info` returns early on `kind_of(functor) != Sort`, and the ONLY
diagnostic on that path — the 058 §4 deprecation warning — is gated on the SAME test. So
when the functor is not a sort, the provision AND its warning vanish TOGETHER. That is why
the live witness cleared a whole review cycle: `wi698_row_param_refinement_test` shipped
`fact Effect[T = K]` with `Effect` MISSING from the import list, which mints a bare
`Effect` that is not `anthill.prelude.Effect`, registers nothing, and reads as though it
did. Any `fact Spec[…]` claim is exposed the same way.

IT HAPPENS AT BOTH LEVELS, and both were measured:
  * INSIDE a sort body  — `sort Carrier { fact NoSuchSpecB }` and
    `sort Carrier { fact NoSuchSpecD[T = Carrier] }`: silent, bracketed or not.
  * AT NAMESPACE LEVEL  — `namespace zz { fact NoSuchSpecXyz[T = Carrier] }`: silent.

THE TWO READINGS ARE UNDECIDABLE FROM THE TEXT, which is why no diagnostic can simply be
added. Both of these are legitimate and correct today:

  sort Rec { fact helper(1) }         an ordinary fact-only predicate scoped to Rec
                                      (driven: `rule see(?x) :- helper(?x)` answers 1)
  sort Rec { fact SomeSpec[T = …] }   a PROVISION

They are told apart ONLY by whether the functor resolves to a Sort — exactly the thing
that fails when the spec is not imported. So `fact Effect[T = K]` with `Effect` unimported
is textually indistinguishable from an ordinary fact-only predicate named `Effect` with a
named argument `T`. A parse-shape test cannot separate them either: `fact Box` and
`fact somePredicate` are the same shape at every level, CST included.

THE DIRECTION, AND WHY IT IS BIGGER THAN IT LOOKS. 058 §4 already deprecates the `fact`
spelling of a provision, with a warning at every remaining site: "Write `provides Spec[…]`
— … retiring the `fact` one removes the language's only construct whose meaning depended
on its container". Finish that and the ambiguity dissolves: a `fact` is then unambiguously
an ordinary fact-only predicate (§6.1 governs it), the author who means a provision writes
`provides`, and `provides` ALREADY refuses an unresolved spec loudly. Nothing new has to
be invented.

BUT THE DEPRECATION'S SCOPE IS ONLY THE IN-SORT SPELLING, and that is the wrong half.
CENSUSED over stdlib + all examples + anthill-stl + anthill-todo:

  in-sort `fact Spec[…]`        0 sites   (the deprecation warning fires 0 times, corpus-wide)
  namespace-level `fact Spec[…]`  20 sites across 9 files, INCLUDING stdlib and anthill-stl:
      stdlib/anthill/prelude/{sort,permission,external,effects}.anthill
      stdlib/anthill/persistence/filesystem.anthill
      rustland/anthill-stl/anthill/{persistence,geometry}.anthill
      rustland/anthill-todo/anthill/coordination_rust.anthill
      examples/guardians/lib/vocabulary.anthill

So the retirement as currently scoped would change nothing (0 users) while the 20 real
users sit on the undeprecated spelling. Deciding what the namespace-level `fact Spec[…]`
becomes is the substance of this ticket; `fact Effect[T = K]` there is ALSO §5.5's
effect-kind registration, so it is not obviously the same question as the in-sort one.

WATCH FOR: the swap is NOT mechanical, and the warning says so — `fact Spec[Carrier]`'s
carrier is POSITIONAL and derived, while `provides Spec[…]` inside a sort takes the
ENCLOSING SORT as the provider and the bindings say what the spec is instantiated at. An
author (or a migration) that swaps the keyword and keeps a bare positional carrier records
a DIFFERENT provision. Both spellings were driven here: at namespace level
`fact Eq[Carrier]` and `fact Eq[T = Carrier]` both emit
`SortProvidesInfo(sort_ref: Carrier, spec: SortView(Eq, T: Carrier))`.

ACCEPTANCE: drive it. A `fact`-spelled provision naming a spec that does not resolve must
not load in silence — at BOTH levels — and the existing 20 namespace-level sites must keep
recording the provisions they record today, asserted by reading `SortProvidesInfo` back
rather than by the absence of a load error. If the fix is the retirement, the in-sort and
namespace-level spellings must be decided together and the spec section that governs each
updated in the same change.

FOUND: while delivering WI-20260821-RDGQC (be2cb2ef), which made a fact head declare its
predicate. That change does NOT affect this defect — the head now mints a local `Goal`
instead of a bare global, so `kind_of != Sort` still holds and the early return still
fires. No worse, not fixed.

## Changes

### 2026-09-17T15:33:51Z — feedback — user

RESTATED AS PROPOSAL 055'S WORK, AND THE FIX NEEDS NO NEW MACHINERY. The user asked whether
this is 055's "cannot distinguish a type from a value after `fact`" problem, and whether
055's plan enumerates the other places. Both yes.

055 ALREADY STATES THE RULE THIS VIOLATES. §2's classification list ends "the name resolves
to NOTHING -> a loud `UnresolvedName`", and the implementation design §8 repeats it as a
requirement, with the fallback named and forbidden:

    "unresolved head: `UnresolvedName` at the name … Do not retain a fallback that retries
     a failed value resolution as a type (or the reverse). Resolve the symbol once and
     classify loudly."

A `fact` head that names nothing does exactly the forbidden thing: it falls to the WI-476
bare intern, which SILENTLY reclassifies the claim from a provision to an ordinary fact.

WHY IT ESCAPED: §6 carves instance claims out — "`fact Modifiable[T = Cell]` … They need no
rescue from this proposal and do not depend on the `Type` sort … not touched by this
proposal." That is right about DENOTATION (an instance claim is not a type in value
position) but it also carried the claims out of reach of §8's diagnostic rule. The silence
lives in that gap, not in a missing decision.

THE ENUMERATION IS design/055-implementation.md §7 — four lowering paths — AND I DROVE ALL
OF THE REACHABLE ONES. A bracketed sort-headed application whose head resolves to NOTHING:

  rule-body goal    `rule r(1) :- NoSuchSpecQ[T = Carrier]`   LOUD  ("names nothing")
  fact DATA slot    `fact p(NoSuchTypeQ[T = Carrier])`        LOUD  ("names nothing")
  fact HEAD         `fact NoSuchSpecXyz[T = Carrier]`         SILENT   <- the defect

POSITIVE CONTROLS, so the LOUD rows are about resolution and not about the bracketed form
being unsupported: `rule r(1) :- Modifiable[T = Cell]` (imported) loads clean, and
`fact p(Cell[V = Int64])` loads clean.

So the fact HEAD is the ONLY position in 055's own enumeration where this is silent. Its
three siblings already do what §8 requires. That is the whole ticket, and it makes the
change a NARROWING of one outlier to a rule the codebase already keeps everywhere else —
not a new policy.

AND THE MECHANISM IS ALREADY SHIPPED — I was wrong that this needs a parse-IR change.
WI-710 records the surface: `SimpleTermStore::is_type_application(id)` — "was this
`Term::Fn` written as a bracketed type application? The loader checks type ARGUMENTS only
on these — a `(…)` call with a sort-named functor is a data constructor". 055 lists it as a
shipped gate ("surface: `Sort[…]` is type/instance application, while `Sort(…)` is
construction"). `load_fact` holds the parse `TermId` (`f.term`) and can ask it today.

SO THE FIX IS: in `load_fact`, a head for which `is_type_application(f.term)` holds and
whose functor does not resolve to a declared Sort is REFUSED, with the message naming the
likely cause (the spec is not imported). It does not touch the bare/unbracketed head, does
not need the 058 retirement decided, and reuses the gate the loader already consults for
type ARGUMENTS on the very same nodes.

STILL OUT OF ITS REACH, and unchanged from the note above: the BARE in-sort claim
(`sort X { fact Box }`, WI-365's effect-row-only spec, which has no bindings to write).
`fact Box` is textually identical to an ordinary nullary fact, so no surface gate separates
them. Smaller and separate; the 20 corpus sites are all bracketed.

WHERE THIS BELONGS: 055 work item (c) names "carry it through raw rule/fact lowering" as
part of denotation completion. This is the fact-HEAD half of that, severable and much
smaller than (c) as a whole, because the other three paths are already right.

### 2026-09-17T16:01:07Z — feedback — user

DIRECTION DECIDED BY THE USER (2026-09-17): `fact` IS ALWAYS AN ORDINARY FACT; A SPEC CLAIM
IS `provides`, ONLY — including `fact Effect[T = K]`. Retire the `fact` spelling of a
provision at BOTH levels rather than teach the loader to tell the two readings apart.

WHY THIS IS BETTER THAN THE NARROW FIX ABOVE, and not merely bigger. The narrow fix
(consult WI-710's `is_type_application` in `load_fact`) teaches the loader to distinguish
two readings of one keyword. The retirement REMOVES THE SECOND READING, so:
  * the missing-import silence is gone — `fact Spec[T = C]` is then just a fact, and an
    author who means a provision writes `provides`, which ALREADY refuses an unresolved
    spec loudly (`error: unresolved name 'NoSuchSpecXyz' in scope`);
  * THE MIRROR DEFECT IS GONE TOO — see the note above: `fact MySpec(T: 1)`, written with
    PARENTHESES, currently banks `SortProvidesInfo(sort_ref: Carrier, spec: SortView(MySpec,
    T: 1))`, binding a spec parameter to the LITERAL 1. No `fact` can be a provision after
    the retirement, so no parenthesised head can be read as one;
  * `is_type_application` stops being load-bearing for classification altogether — there is
    nothing left to classify.

IT NEEDS NO NEW LANGUAGE SURFACE. I had said the namespace-level form has no `provides`
replacement because `provides` names its subject by WHERE it is written. A 059 SECONDARY
ENTRY supplies exactly that. MEASURED:

    sort Carrier … end
    namespace Carrier
      provides HasOp[T = Carrier]
    end
  ->  SortProvidesInfo(sort_ref: Carrier, spec: SortView(HasOp, T: Carrier))

byte-identical to what `fact HasOp[Carrier]` produces.

THE EFFECT-KIND REGISTRATION MIGRATES, AND THE CAPABILITY WAS DRIVEN, not inferred from the
fact row — this was the case I had flagged as possibly a different construct sharing the
spelling. It is not:

    namespace MyEff  provides Effect[T = MyEff]  end
    operation act(x: Int64) -> Int64  effects {MyEff}      -> LOADS CLEAN
    CONTROL, registration removed                          -> "declares effect `MyEff`, but
        `zzEU.MyEff` is not a REGISTERED effect kind — nothing in the knowledge base says
        that sort is an effect"

So §5.5's registration IS the provision emission, and `provides` performs it.

OBLIGATIONS ARE THE SAME, at least the one I compared — so this is a rename and not a
weakening. A carrier that backs nothing is refused IDENTICALLY either way:
    fact HasOp[Carrier]          -> "'zzOF.Carrier' provides 'zzOF.HasOp' but backs no
    provides HasOp[T = Carrier]      operation 'zzOF.HasOp.doit' …"
STATED AS A LIMIT: I compared the MEMBER-BACKING obligation only. 055 §6 describes the
overlap as "both assert 'S satisfies C at σ', one without proof obligations", so the
remaining obligations must be compared before the retirement is called total.

MIGRATION: 20 sites, all BRACKETED and so mechanically identifiable —
    stdlib/anthill/prelude/{sort,permission,external,effects}.anthill
    stdlib/anthill/persistence/filesystem.anthill
    rustland/anthill-stl/anthill/{persistence,geometry}.anthill
    rustland/anthill-todo/anthill/coordination_rust.anthill
    examples/guardians/lib/vocabulary.anthill
The in-sort spelling has ZERO corpus sites, so 058 §4's existing deprecation covers the
half nobody uses; this direction covers the half everybody does.

THE SWAP IS NOT BLIND, and the deprecation warning already says why: `fact Spec[Carrier]`'s
carrier is POSITIONAL and derived, while `provides` takes its carrier from the ADDRESS. The
secondary-entry form is what supplies the address, which is why the migration target is
`namespace <Carrier> { provides Spec[…] }` and not a bare keyword swap in place.

FALLBACK, IF THE RETIREMENT IS NOT TAKEN: the narrow fix stands on its own — in `load_fact`,
a head for which `is_type_application(f.term)` holds and whose functor does not resolve to a
declared Sort is REFUSED. It closes the silent drop and (extended to the parens direction)
the mirror defect, without deciding the retirement. It leaves the BARE in-sort claim
(`sort X { fact Box }`, WI-365) ambiguous, which the retirement would also close.

PRIOR ART: 055 parked exactly this question rather than settling it — §6 ("the observed
overlap between op-bearing instance claims and `provides` … folding them is explicitly out
of scope and deserves its own proposal"), Out of scope ("Instance-claim ↔ `provides`
unification — own proposal"), and Alternatives ("`fact Modifiable[…]` → `provides`:
deferred, not rejected — real overlap, separate concern"). This ticket is now the answer to
that deferral, with the feasibility measured rather than assumed.

### 2026-09-17T19:34:28Z — feedback — user

DELIVERED — `provides` IS THE ONLY SPELLING OF A PROVISION, AT BOTH LEVELS.

WHAT SHIPPED:
  * `maybe_emit_fact_provides_info` and its two helpers are GONE from `load_fact`. No
    `fact` emits `SortProvidesInfo` — neither the in-sort reading (provider from the
    enclosing type) nor the namespace-level one (carrier DERIVED from a binding value).
  * Three diagnostics retired with the derivation that raised them:
    `CarrierlessProvisionFact` + `CarrierlessProvisionReason` (WI-933),
    `UnresolvableInstanceCarrier` (WI-431 (E)), and the `ProvisionFactSpelling`
    deprecation warning (WI-862). Each could only fire on a carrier derivation, and
    there is no longer one.
  * READERS keyed on the `fact` spelling dropped that leg, which is the retirement and
    not a cleanup: `region.rs`'s `modifiable_claim_heads` reads the provision relation
    ONLY (a `fact Modifiable[T = X]` claims nothing now); Rust codegen lost its
    `Item::Fact` supertrait arm, its proximity-based namespace-level arm and
    `emit_namespace_fact`, and gained `emit_secondary_entry_provisions` — an entry at a
    trait-lowered address folds into that sort's supertraits, one at an entity's address
    renders `// impl Spec for X`.
  * §5.5's effect-kind registration migrated with everything else and is DRIVEN, not
    inferred: `provides Effect[T = MyEff]` registers, a `fact` does not.

CORPUS MIGRATION — 20 sites + the two the census missed (`anthill-testcases/ring-polynom`,
`docs/measurements/guardians/d3_frame.anthill`). Written in the carrier's own body where
it has one (`sort Modify { provides Effect[T = Modify[?]] }`), in a `namespace <Carrier>`
SECONDARY ENTRY where it does not (`sort Type = ?`, the free-standing `entity FileStore`
family, `Vec3`, both forges, `anthill.prelude.Int64` for the ring testcase). MEASURED: a
cross-FILE entry works — `anthill-todo`'s and `wi931`'s both claim for a sort declared in
another file.

THE GATE WAS BUILT AND REMOVED, and that is the one place the ticket's plan changed.
055-implementation §7 lists the fact HEAD beside three positions where a bracketed
application over an unresolved name already reports, and it reads as the fourth. It is
not: those three are REFERENCE positions and a clause head is a DECLARATION
(WI-20260821-RDGQC). `fact myrel[T = Red]` is a rule-introduced predicate carrying a type
argument — byte-identical to `fact NoSuchSpec[T = C]` except that one name is capitalized,
which §2.3 gives no meaning. MEASURED: the refusal took
`wi_c7anm_head_parameter_column_test::a_bracketed_head_binds_a_type_argument_not_a_parameter`
with it. So what closes the silence is the retirement itself — with one reading left, a
missing import demotes nothing — exactly as the 16:01 direction note argued.

TEST MIGRATION — ~374 fixture sites across ~95 modules, scripted over the raw-string
fixtures and hand-applied to the plain-string ones. 362 tests failed with the emission off
before the migration; 0 after. `wi933_carrierless_provision_test` is DELETED (its subject
is gone) and succeeded by `wi_s8jyf_provision_spelling_test`, which drives: a `fact`
records no provision at either level, a secondary entry records what the fact used to, the
provision DISPATCHES and the fact falls to the spec's default, the parens mirror defect
(`fact MySpec(T: 1)` banking a spec parameter bound to the literal 1) is gone, effect
registration works through `provides` only, and the deliberately-absent head gate. wi862's
four deprecation rows are deleted; wi1069's fact/provides agreement pair is one row;
wi431's two carrier-derivation refusals are replaced by rows that read the provision
relation back rather than asserting a clean load.

SPEC + PROPOSALS, in the same change: `kernel-language.md` §4.4, §5.1, §5.5, §6.3, §8.7,
059's R3 table row; 058 §4 (which SAID the namespace-level population was untouched — that
scoping was measured wrong: the in-sort half had 0 corpus sites, the namespace-level half
had 20); 055 §6's deferred overlap, now answered; 055-implementation §7/§8;
`rust-forward-mapping.md` §2.13; a status note on 013.

WHAT IT COSTS, stated rather than discovered later:
  * A provision is NOT a clause, so the goal `Spec(T: ?q)` no longer answers from one.
    Where a rule resolves the spec as a goal, keep the fact BESIDE the provision —
    §5.1 says so and `wi1069::the_two_spellings_diverge_outside_the_provision` drives it.
  * A PARAMETERIZED provision still renders no Rust supertrait (WI-1108). The retired
    `fact` arm rendered it bare — dropping every binding, which is wrong Rust — and
    widening the `provides` arm was measured to break the anthill-stl build. Pinned with
    its control by `codegen_test::a_parameterized_provision_renders_no_supertrait_yet`.
  * The `LoadWarning` span/`Located` channel now has no producer. Kept and documented at
    `LoadWarning::span` so the next span-bearing advisory plugs in rather than rebuilding.

ACCEPTANCE: `rustland/scripts/test.sh` — 7121 passed, 0 failed. `/code-review` run at
`high`; its two findings were mine and both are fixed in the same change (a secondary
entry that also declares an operation rendered its provision twice in codegen; a stray
blank line). scaland-sbt-test NOT RUN — sbt is not installed in this environment. scaland
is untouched by the change (no `SortProvidesInfo` there); its tests do parse the repo's
`stdlib/anthill` sources, and the migrated spellings are all existing grammar its one
`declaration` production already admits (`providesDecl` and `namespaceDecl` are both in
it), but that is reasoning and not a measurement.


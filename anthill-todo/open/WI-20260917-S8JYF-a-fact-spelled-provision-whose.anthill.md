## Attributes

- id: WI-20260917-S8JYF-a-fact-spelled-provision-whose
- created: 2026-09-17T14:59:44Z

- status: Open
- status_agent: user
- status_at: 2026-09-17T14:59:44Z

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


## Attributes

- id: WI-20260821-M460D-adding-an-entity-to-a-spec
- created: 2026-08-21T11:23:18Z

- status: Open
- status_agent: user
- status_at: 2026-08-21T11:23:18Z

- acceptance: cargo-test, scaland-sbt-test

## Description

ADDING AN `entity` TO A SPEC HIDES ITS OPERATIONS FROM EVERY `requires` CALLER. The
`exposed` (variant-exposure) filter is applied to `requires` edges, so whether a bare
member name crosses one depends on whether the target happens to declare variants.

MEASURED, one line apart:
  sort Spec { operation f(x: Int64) -> Int64 = x }
  sort User { requires tt.Spec  entity u(n: Int64)  operation g(y) = f(y) }   -> LOADS
  add `entity marker(n: Int64)` to Spec, change nothing else                  -> REFUSED
      "`f` is a member of sort Spec, not in scope as a bare name here; call it
       qualified as `Spec.f(...)` or via a receiver"
So a spec that acquires an unrelated constructor silently breaks every caller that
reached its operations bare through `requires`.

THE SPEC CONTRADICTS ITSELF ABOUT IT, in two paragraphs of one section:
  * kernel-language.md §resolution step 3(c): "A *non-enclosing* parent is skipped when
    the name is ... absent from a non-empty **exposed** set of that parent (variant
    exposure)". A `requires` link IS a non-enclosing parent, so (c) applies to it.
  * kernel-language.md §"Variant exposure": "the sort's *operations* never leak as bare
    names (they are reached via `Sort.op`, `requires`, or wildcard)" -- which says
    `requires` DOES reach them.
Both cannot hold for a variant-bearing spec. The code implements the first
(`intern.rs`, the `!parent.exposed.is_empty() && !parent.exposed.contains(name)` arm).

INVISIBLE TODAY BY ACCIDENT: the stdlib's specs (`PartialEq`, `Ord`, `Numeric`, ...)
declare no variants, so `exposed` is empty and the filter never fires. The coupling
bites the first time somebody gives a spec a constructor.

THE DECISION THIS NEEDS: one behaviour, not two. The user's reading (2026-08-21) is
that a `requires` target's members should be VISIBLE, uniformly -- `exposed` is about
what leaks OUTWARD to an enclosing scope (proposal 044 job 2: bare `Open` for
`WorkStatus.Open`), which is a different question from what a `requires` clause reaches
INWARD. If that is the answer, the filter stops applying to `requires` edges and step
3(c) narrows to the exposure link alone; the alternative is to keep the filter and
delete the "reached via `requires`" clause, which makes `requires` useless for bare
member access and is not what the stdlib relies on.

WATCH FOR: 059 R4's capture rule deliberately stops at the exposure link
(kernel-language.md, "the leak is ..."), and WI-999's own doc records measuring that.
Whatever changes here must not widen what a DECLARATION captures.

ACCEPTANCE: the two programs above must agree -- adding an unrelated `entity` to a spec
does not change whether a `requires` caller reaches its operations bare. Drive the call,
assert the value, both with and without the variant. Keep a control pinning that variant
exposure still leaks constructor names to the ENCLOSING scope and still does not reach
sibling types' members (§8.7). cargo-test green via rustland/scripts/test.sh.


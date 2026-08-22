## Attributes

- id: WI-20260821-M460D-adding-an-entity-to-a-spec
- created: 2026-08-21T11:23:18Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-22T21:16:50Z

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

## Changes

### 2026-08-22T21:16:47Z — feedback — claude

DELIVERED as the user's reading: `exposed` filters the VARIANT-EXPOSURE link and no
other. The two programs now agree; the whole change is that a parent link carries the
CLAUSE THAT WROTE IT, so a filter decision is taken per link kind instead of per far
scope.

Rust: `ImportOrigin::Exposure` + `SymbolTable::add_exposure_parent` (one producer,
`scan_items_pass1`'s SortWithBody arm) + `parent_edge_is_exposure_only`. The kind rides
on the ORIGIN LIST, not on `ScopeInclusion`: that struct is the dedup key, so a kind
field would split `sort Outer { sort Inner { entity V }  requires Inner }` into two
entries for one link and let push order decide the filter. Scaland: the same
`ImportOrigin.Exposure`, tested per INCLUSION (its `parents` is an append-only list,
so the two writers are two records and the reaching one admits the name).

WI-999's capture skip was re-keyed onto the same predicate. It used to read
`exposed.contains(name) && !parent_edge_is_imported` — `exposed` as a stand-in for
"this is the exposure hop", which could not see the `requires` writer at all. Its
documented back-out is unchanged in effect: exactly one row,
`wildcard_import_of_a_variant_bearing_sort_is_a_capture`.

THE TICKET'S "WATCH FOR" DID NOT MATERIALISE, and the reason is worth recording. The
capture walk now follows a `requires` hop it used to skip, which is strictly MORE
names — but `capture_is_excused` excuses anything reached over the requiring sort's own
requires/provides chain by construction, so no program gains a refusal. Probed
directly: `sort User { requires Colour  operation Red(…) }` over `entity Red` loads,
as does the sibling-sort control. The spec now says this as a rule rather than leaving
"an import spends the exemption" to imply a `requires` does too.

FOUND BY /code-review, NOT BY THE NINE ROWS: `parent_edge_is_exposure_only` answered
over the RAW origin list, so a wildcard import written IN the declaring namespace
lifted the `exposed` filter for EVERY file at that address — a third file with no
import loaded clean, and was refused again when the importing file was dropped. That is
WI-995's rule inverted (a foreign import GRANTING a name). Fixed by answering over the
VISIBLE origins, with `vis` threaded so the WI-995 audit's counterfactual stays
faithful; pinned by `a_sibling_files_wildcard_import_does_not_lift_the_filter_for_
another_file` in both ports. My own nine rows could not reach it: the wildcard row puts
its import in a DIFFERENT namespace, the one arrangement where the pair carries no
exposure origin.

WHAT NOTHING DRIVES: the `provides` link (`wire_provides_scope_parent`) has the same
shape and carried the same defect, and is unreachable by construction — a `provides`
whose target declares constructors is already refused as a DATA sort. Fixed by the same
re-keying, driven by nothing, and said so at the test file's head.

Measured. rustland 36 binaries / 5542 passed / 0 failed; scaland 514/514. Back-outs,
each isolated (the two arms share one binding, and widening the binding moves both):
ARM 1 (`exposed` on every non-enclosing link) -> 4 rows, all in the new file; ARM 2
(capture skip keyed on the name) -> 1 row, wi999's; ARM 3 (raw origins instead of
visible) -> 1 row, the file-locality one. Deleting the filter instead of re-keying it
-> 2251 rows, because the stdlib itself goes ambiguous; recorded so that control is
not credited with a measurement it cannot make.

Spec: §8.6 step 3(c) narrowed to the exposure link, the scope glossary now says a
parent link carries its writing clause, *Variant exposure* gained the outward/inward
paragraph, and the capture-exemption paragraph states the `requires` case explicitly.


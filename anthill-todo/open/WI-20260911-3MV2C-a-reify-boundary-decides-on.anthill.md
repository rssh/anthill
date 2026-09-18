## Attributes

- id: WI-20260911-3MV2C-a-reify-boundary-decides-on
- created: 2026-09-11T06:05:45Z

- status: Open
- status_agent: user
- status_at: 2026-09-11T06:05:45Z

- acceptance: cargo-test

- tags: effects

## Description

A REIFY BOUNDARY DECIDES ON THE PAYLOAD'S SORT, NOT ITS TYPE ARGUMENTS — so a boundary
typed at `Box[V = Int64]` catches a raised `Box[V = String]`, and the value arrives inside
a `Result[E = Box[V = Int64]]` a caller is about to destructure at the wrong type.

THE TYPER DOES DISTINGUISH THEM. Measured: a boundary at `Box[V = String]` around a body
raising `Error[Box[V = Int64]]` is REFUSED — "expected declared: [], got undeclared effect:
Error[T = Box[V = Int64]]". `labels_match_by_subsumption` holds a parameterized payload to
exact argument match; its own comment says so ("`Error[List[T = X]]` against
`Error[List[T = Y]]` falls back to the exact-match leg above, even where `X` refines `Y`").

THE RUNTIME CANNOT. `enter_reify_boundary` narrows `T1` to a `Symbol` (`payload_sort_of`
takes the `Fn` head), and `runtime_carrier_sort` can only ever answer a bare sort — a value
carries its constructor, not the type arguments it was built at. So the comparison in
`payload_matches` is head-against-head by construction.

DRIVEN by /code-review on the working tree: nested boundaries at `Box[V=Int64]` (inner) and
`Box[V=String]` (outer) around a raise of the STRING box answered "inner-caught", and so did
the mirror image. The control with two distinct payload SORTS answered "outer-caught", so
only the type-argument axis is blind. The corruption is observable — a `Box[V=String]`
delivered inside a `Result[E = Box[V = Int64]]` — and a caller that then uses the field at
its declared `Int64` type answers `no solutions`, the confusion degrading into a silent
failure.

NOT A REGRESSION, AND THAT IS WHY IT IS FILED RATHER THAN FIXED IN PLACE. Before proposal
027.4's narrowing no boundary judged the payload at all, so every boundary caught every
raise; this axis is the part the narrowing did not reach, not a part it broke. The
`Boom`-vs-`Other` case it DID close is the same defect class one type-argument shallower.

WHAT CLOSING IT NEEDS. The raised value's type ARGUMENTS at run time, which the interpreter
does not reconstruct. Three directions, none obviously right:
 * RECONSTRUCT from the value — read the constructor's field values' carrier sorts and match
   them against the sort's declared field types. Total for a fully-applied constructor,
   silent for a phantom parameter no field mentions.
 * CARRY the arguments on the value — a constructor records what it was built at. Changes
   the value representation, which is the expensive option.
 * REFUSE at install — `payload_sort_of` answers `None` for a PARAMETERIZED head, so such a
   boundary catches wide as it did before. Cheapest and honest, and it gives up the
   narrowing exactly where the typer is sharpest.

ACCEPTANCE: a nested pair of boundaries at `Box[V=Int64]` / `Box[V=String]` answers through
the OUTER one for a `Box[V=String]` raise and the INNER one for a `Box[V=Int64]` raise, with
the two-distinct-sorts row as the control that passes either way.

## Changes

### 2026-09-18T07:42:57Z — feedback — user

THE THREE DIRECTIONS ARE RECLASSIFIED, AND THE DECISION IS NOW WRITTEN DOWN AS A
CONTINUUM RATHER THAN A MENU. See `docs/proposals/027.4-error-effect-reify.md` §"What
travels with a raise — the tag continuum" (NOT BUILT; it fixes vocabulary, it does not
decide).

WHAT REFRAMED IT. USER DIRECTION: during typing nothing is erased, and the typed tree
carries no information loss. If that holds, a tag is not something the runtime
reconstructs from a value — it is something the TYPER writes into the raise. So "throw
the value alone or with a tag" is really "may the typed tree write into the raise", and
the premise answers yes. That splits cleanly: a MONOMORPHIC throw site bakes the tag as a
CONSTANT (no channel, no dictionary, no lookup), a POLYMORPHIC one takes it from the
caller through a channel anthill already has — the type-argument channel (ground since
`collect_closed_type_args`) or the requirement dictionary (WI-562).

THIS TICKET'S OWN DIRECTIONS, RE-JUDGED.
 * RECONSTRUCT from the value is the FALLBACK, not the mechanism — right where no typed
   tree wrote a tag (host raisers, bridged entry, an empty frame channel), wrong as the
   primary rule. And its recorded objection is milder than stated: an unwitnessed
   parameter is not silently WRONG, it is UNCONSTRAINED. `entity none` inhabits
   `Option[Int64]` and `Option[String]` alike, so the residue is a control-flow
   imprecision over values well-typed either way, not a corruption. The witnessing case
   — `InvalidParameter[T](t: T)`, the shape real error vocabulary takes — is recoverable
   from `entity_field_types`: the field whose declared type IS the sort parameter.
   The fallback shrinks further if host raisers carry their own tags (`raise_match_failed`
   knows it raises `Error[MatchFailed]`), which closes the off-channel-payload question
   by construction rather than by declining.
 * CARRY on the value is continuum point 4 — C#, reified generics — and its price is
   global: every allocation pays for a discrimination only the error path needs.
 * REFUSE at install was measured WRONG as written: `None` catches WIDE, so the same
   `Box[V=String]` still lands in a `Result[E = Box[V=Int64]]`. It removes the pretense
   of judging, not the defect. A blanket LOAD-time refusal was considered and withdrawn —
   it would forbid `InvalidParameter[T]`, which is the normal vocabulary (Java's
   escape, JLS §8.1.2, and not available to us).

THE SURVEY, WHICH IS THE PART WORTH KEEPING. Five designs, and none routes an exception
on a type argument without reified generics: ML forbids a polymorphic exception
constructor; Java forbids the declaration; TypeScript types the catch binding `unknown`;
Rust's `downcast` is exact and its widening is `From` inserted statically at `?`; Scala
permits the declaration, warns "non-variable type argument ... is unchecked since it is
eliminated by erasure", and gets it wrong at run time. ANTHILL TODAY IS SCALA'S BEHAVIOUR
MINUS THE WARNING — that is the honest statement of this defect. Haskell is the one that
discriminates on arguments, via the `Typeable` dictionary, and pays by giving up
covariance (`cast` is exact). C# has both and pays globally.

WHAT ANTHILL'S OWN COMMITMENTS ALREADY DECIDE. Covariance is committed and driven, which
makes a minted-token design EXPENSIVE (identity cannot subsume; the boundary would need
the typer to enumerate its discharge SET) and a ground-type-term design CHEAP (the
subsuming predicate is the one already in use). Anthill already evaluates type terms at
run time — `tyOf[T](x: T) -> Type = Cell[V = T]` gives `Cell[V = Int64]` — so a term-shaped
tag is not a new kind of thing here, and a bare-sort tag degenerates to a token's cost.

THE COMPARISON IS ONE PREDICATE AND IT IS NOT ERROR-SPECIFIC. `payload_matches`'s
`declared: Symbol` becomes a two-view relation beside `views_structurally_equal`:
`value_inhabits_type<V: TermView, T: TermView>`. `TermView` and NOT `TermId` on either
side — USER DIRECTION, and the reason is CLAUDE.md's representation note: a type term
grounded per dispatch is a TRANSIENT and interned terms live for the KB's lifetime.
(`ground_type_params` takes and returns a `TermId` today, so the install path already
interns a freshly-grounded term per dispatch — pre-existing, one layer down, and a
view-shaped comparison is what would let it be fixed rather than extended.)

WHAT IS STILL OPEN, AND IT IS A DECISION NOT A MEASUREMENT:
 * continuum point 2 (minted token, exact, needs an enumerated discharge set to keep
   covariance) vs point 3 (ground type term, subsuming, reuses the existing predicate);
 * if the tag is typeclass-supplied — `Raisable[T]` with a derived-by-default `tag()`,
   which is Haskell's `Exception`/`fromException` riding anthill's existing dictionary
   threading — whether a USER-WRITTEN match may override the derived one. It is the
   per-sort policy knob and it has a hazard: an overriding match can decline a payload
   the typer already discharged, and then the raise escapes an operation certified
   effect-free. Derived-only keeps the discharge a GUARANTEE; overridable makes it a
   CLAIM.

THE ACCEPTANCE AS WRITTEN SURVIVES point 3 and does NOT survive a catch-wide fallback:
nested boundaries at `Box[V=Int64]` / `Box[V=String]` route correctly only where the tag
carries the argument.


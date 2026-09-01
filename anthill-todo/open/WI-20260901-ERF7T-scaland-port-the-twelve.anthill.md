## Attributes

- id: WI-20260901-ERF7T-scaland-port-the-twelve
- created: 2026-09-01T15:47:17Z

- status: Open
- status_agent: user
- status_at: 2026-09-01T15:47:17Z

- acceptance: cargo-test, scaland-sbt-test

## Description

SCALAND: PORT THE TWELVE DESUGAR-TARGET ADDRESSES (5W3RJ / S66VH), so a minted functor names
its target absolutely. Split out of WI-20260824-6RXGD, whose `scaland-sbt-test` acceptance this
carries; 6RXGD's rustland half is delivered without it.

WHY IT IS NO LONGER 6RXGD'S ONE-LINE PORT. 6RXGD was filed (2026-08-24) as "mint the `x.f`
accessor absolutely". In rustland that grew into a whole mechanism: `parse::desugar_target`
now holds TWELVE absolute addresses (`..anthill.reflect.field_access`, the four `Expr` forms,
the three literal carriers, `ho_apply`, `dot_apply`, plus the two KERNEL CONTROL targets
`..anthill.kernel.cut` / `..anthill.kernel.find_dictionary`), a `qualified` / `short` / `is`
reader API with a documented per-carrier contract, and an `is_kernel_control` partition that
`is` refuses to answer for. Porting `field_access` alone would reproduce the divergence one
name at a time.

SCALAND'S STATE — READ FROM SOURCE, NOT DRIVEN (no sbt run was made for this ticket; the
first step is to drive each claim below):
  - `AnthillParser.scala:1019` `private lazy val fieldAccessSym = intern("field_access")`, and
    `:1245` `Term.Fn(intern("field_access"), …)` — the mint is BARE.
  - `load/Prelude.scala:224` registers `(reflect, "field_access", BuiltinTag.FieldAccess)`, so
    the SHORT name resolves through prelude registration. Rustland deleted that rung: its
    `KERNEL_VOCAB_QUALIFIED` table of 28 reflect addresses is gone, and
    `load::implicit_qualified` now covers the USER-facing prelude only.
  - `parse/ExprMarker.scala` carries a DIFFERENT mechanism for the ten `match_expr` /
    `pattern_*` forms — parse-time provenance markers (`allocMarkerAt` / `markerOf`, WI-1009)
    — and its own doc says `field_access` / `dot_apply` / `ho_apply` / `unify` / the collection
    literals are deliberately NOT markers because "the loader is MEANT to resolve" them. So
    scaland has two mechanisms where rustland now has one, and the port has to decide whether
    `ExprMarker` is subsumed by addresses or stays beside them.
  - No `desugar_target` equivalent, no absolute-path-marker handling on this path.

THE MEASURED DIVERGENCE (rustland side driven this session, scaland side read):
  - rustland: `KnowledgeBase::resolve_name_in_global("field_access")` answers NotFound, as do
    `dot_apply` and `ListLiteral`; `SortInfo` and `cons` answer Found. Both QUALIFIED spellings
    of the accessor answer Found. So a host-supplied name (an extent mount owner, a
    `reflect.lookup_symbol` call) must spell the accessor qualified.
  - scaland: the prelude registration above means the bare short name is expected to resolve.
    DRIVE THIS FIRST — the whole ticket rests on it.

ACCEPTANCE: scaland mints each of the twelve targets at its absolute address; a bare
`field_access` / `dot_apply` resolves the same way in both implementations (drive the
host-name position, not only the load); the kernel CONTROL pair is excluded from any
short-spelling admission, as `desugar_target::is`'s assert requires; `sbt test` green.
Say at each ported site which scaland test fails when the port is backed out.


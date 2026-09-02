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

## Changes

### 2026-09-02T07:58:40Z — feedback — user

WI-909 ADDED TWO MORE ADDRESSES TO PORT, and they are not among this ticket's twelve.
`parse::pratt::UNIFY_FUNCTOR` / `STRUCT_EQ_FUNCTOR` are now `..anthill.kernel.unify` /
`..anthill.kernel.struct_eq` (they were short names on `kb::load::PRELUDE_QUALIFIED`),
so rustland parses `<=>` / `===` to an address while scaland still parses them to
`unify` / `struct_eq`. That is the divergence `Pratt.scala`'s own KD9SW doc says the
mirror exists to prevent — "the same source would parse to `add(a, b)` here and to
`..anthill.prelude.Additive.add(a, b)` there, so the two implementations would disagree
about what a program IS".

THREE MINT SITES, not two. `Pratt.scala:83` (`"<=>"`) and `:88` (`"==="`), plus
`AnthillParser.scala:869`, where a goal-position `let ?v = e` calls `intern("unify")`
directly. Rustland had that identical split — `convert_let_binding` held its own
`"unify"` literal — and WI-909 walked into it: the `let` lowering stopped agreeing with
the operator, while `parse_let_binding_desugars_to_unify` stayed GREEN because it
compared that site's spelling against a literal of its own. Scaland's
`ParseTest.scala:902/910/919` and `LoaderTest.scala:319` have the same shape, so they
will not catch it either. The rustland fix was to assert the two lowerings against EACH
OTHER rather than against literals.

ONE READER IS REAL WORK, and it is the only one — the other two I first cited were
wrong, so they are named here as NOT the problem to save the next reader the walk:
  - REAL: `kb/KnowledgeBase.scala:531` `isEquation` matches `name == "eq" || name ==
    "unify"` on `symbols.name(fn.functor)`. Per `Pratt.scala`'s own comment scaland has
    no resolver-side builtin and the functor "just round-trips", and `Prelude.scala:242`
    confirms `anthill.kernel` is deliberately NOT a `<global>` parent — so a minted
    connective is never resolved and `symbols.name` yields whatever was interned. Give
    it an address and this reader sees `..anthill.kernel.unify`, not `unify`.
  - NOT: `Loader.scala:821` `nonDefiningConnectiveHead` is purely parse-layer and goes
    through `parseConnectiveHead`, which compares against the pratt constants — it
    follows an address automatically.
  - NOT: `Prelude.scala:224` is `field_access`; `:243-244` is a doc line. Neither
    registers `unify` / `struct_eq`. The only kernel builtin registered is
    `(kernel, "not", BuiltinTag.Not)` at `:218`.

AND SCALAND HAS NO `..`-MARKER HANDLING: `ABSOLUTE_PATH_MARKER` / `stripPrefix("..")`
over `scaland/core/src/main/scala` finds one mention, a comment in `Symbol.scala`. The
twelve `SPEC_OP_FUNCTORS` addresses already in `Pratt.scala` get away with that because
nothing classifies on them; a connective that IS classified cannot.

NOT DRIVEN — read from source, same standing as this ticket's own state section. No sbt
run was made.


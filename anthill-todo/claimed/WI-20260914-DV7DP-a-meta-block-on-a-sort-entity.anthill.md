## Attributes

- id: WI-20260914-DV7DP-a-meta-block-on-a-sort-entity
- created: 2026-09-14T05:50:24Z

- status: Claimed
- status_agent: user
- status_at: 2026-09-14T06:30:50Z

- acceptance: cargo-test, scaland-sbt-test

- tags: reflect

## Description

A META BLOCK ON A SORT, ENTITY, CONST OR CONSTRAINT IS PARSED AND SILENTLY DROPPED — the grammar admits `[Marker, Key: value]` after those declarations and the parse IR carries it, but the loader never reads it, so the program loads clean and the metadata reaches nothing.

MEASURED FROM THE CODE (2026-09-14; not yet driven — acceptance row 1 is the drive). `parse/ir.rs` gives `meta: Option<MetaBlock>` to `AbstractSort`, `SortWithBody`, `Rule`, `Operation`, `Const`, `Entity`, `Fact` and `Constraint`, and tree-sitter-anthill/grammar.js accepts a trailing `meta_block` on sort, enum, effects, entity and const declarations. `kb/load.rs` reads it at exactly four sites: facts (`f.meta`), rules (`r.meta`, plus the destructured `meta` read by `meta_has_flag(…, "simp" / "unfold")`), the unlabeled-rule refusal, and operations (`o.meta` into `OperationInfo.meta`, §5.8). Nothing reads it for the other four kinds.

WHY IT MATTERS NOW. WI-20260914-Z73FX decided (with the user) that `internal` becomes a meta FLAG — `internal entity text(…)` shorthand for `entity text(…) [internal]` — carried as the clause metadata of the declaration's own reflect row (`SortInfo` / `MemberInfo`), with no new schema field. That spelling cannot exist while a declaration's block is discarded. Independently of Z73FX it is the silent-skip this repo's rules forbid: a `[Marker]` a codegen handler would read, written on an entity, does nothing and says nothing.

SHAPE. The block lowers through the existing `load_meta_block` to the same `meta(key: value, …)` term operations and rules use, and rides as the CLAUSE META of the reflect row the loader already emits for the declaration — `SortInfo` for a sort / enum / abstract sort, `MemberInfo(kind: Constructor)` for an entity constructor, the const's own row for a const, the constraint's labeled rule for a constraint. One reader for all of them is Z73FX's `KB.meta_of(kb, s: Symbol) -> Term`; this ticket only has to put the block where that reader will find it, and may ship its own minimal read path for the acceptance rows if Z73FX has not landed.

WHAT MUST STAY TRUE: a declaration with NO block keeps an empty `meta()` (the operations' convention, "no attributes"); §5.8's `OperationInfo.meta` is unchanged; a block's contents are not interpreted by the loader except where a key already has kernel meaning (none of these four kinds has one yet — `internal` is Z73FX's); an UNLABELED constraint with a block is refused the way an unlabeled rule's tag already is ("A `[…]` tag on it has no clause to govern"), not dropped.

ACCEPTANCE: (1) a sort, an enum, an entity constructor, a const and a labeled constraint each carrying `[Marker, Key: 7]` — the block is readable from the KB afterwards with `Marker` present and `Key` = 7, driven through a reader rather than asserted from the load succeeding; CONTROL: the same declarations without a block read as empty meta; (2) an unlabeled constraint with a block is refused, with the rule's message shape; (3) nothing that loads today changes its verdict — full workspace green via rustland/scripts/test.sh.


### Review decision (2026-09-14)

The review found that the proposed symbol-keyed host table was not queryable from
Anthill. The user requested a standard KB relation instead of a parallel table.
The implementation now publishes `anthill.reflect.DeclarationMeta(name: Term,
meta: Term)` facts, read by ordinary Anthill rules and SLD resolution. This replaces
the original SHAPE above: no host table, no one-block-per-symbol conflict rule, and
no new clause-metadata query primitive. Each declaration contributes its block, or
empty `meta()` when absent; declarations sharing a name retain separate rows.
`OperationInfo.meta` and rule/fact clause metadata keep their existing meaning.

### Naming decision (2026-09-15)

MEASURED: a rule body cannot write a sort, operation or constraint label in
`DeclarationMeta(name: …)` — `Ref(MySort)`, the bare name and the dotted name are all
refused ("expected resolved name, got unresolved"; an operation as "op-as-fn-value"),
exactly as `SortInfo(name: Tagged)` and `OperationInfo(name: twice)` are today (WI-206
gates the sort rung on a `Type` slot; WI-40KSW is the message). Only constructors and
consts, which have a value reading, loaded.

DECIDED with the user: keep `name` as the declaration's symbol reference — the shape
`SortInfo.name` has, so `SortInfo(name: ?s), DeclarationMeta(name: ?s, meta: ?m)` joins —
and do not widen what a `Term` slot admits in a rule body. A reader binds the name by a
join, or passes a particular name in through a `Term`-typed fact. No string key. The
tests drive every kind that way; the spec and `reflect.anthill` no longer show the
rule-body `Ref(MySort)` spelling.

### Kind decision (2026-09-15)

REVIEW FOUND: rows were filed under `current_domain()` — the sort / operation ITSELF
inside its scope — and a fact dedups on (head, clause kind, domain). So
`sort Point  entity Point [M]  end [M]` was ONE row (both in `Point`'s domain); filed
under the enclosing domain, as `DescriptionInfo` is, it became two IDENTICAL rows. The
row count was an accident of placement.

DECIDED with the user: `DeclarationMeta(name: Term, kind: MemberKind, meta: Term)`.
`kind` reuses `MemberInfo`'s vocabulary (`Sort`, `Enum`, `Constructor`, `Const`,
`Operation`) plus a new `MemberKind.Constraint`; a rule names it (`kind: Sort`), which a
Symbol-typed kind (`SortInfo.kind`) cannot be — measured, neither `kind: enum` nor
`kind: "enum"` loads. Rows are filed under the enclosing domain with `ClauseKind::Fact`
(was `Member`, `MemberInfo`'s kind). A const's block is lowered under the const's
ownership. scaland is untouched: it emits no reflect facts and loads no `constraint`
(WI-1007), so neither the rows nor the unlabeled-constraint refusal have a site there.

### Second review (2026-09-15)

FIXED: a type parameter declared in `sort Box[T]` and written again as `sort T = ? [M]`
(or HK `sort Spec[F[E]]` + `sort F … end [M]`) answered both `meta()` and `meta(M)`.
An absent block's empty row is now queued and emitted at the end of the file only for a
(name, kind) no declaration gave a block (control: eager emission fails
`redeclared_parameter_keeps_only_its_written_block`). Kinds are a Rust `MemberKind`
enum shared by `MemberInfo` and `DeclarationMeta` and the symbol registration, so a
misspelt kind no longer compiles. The spec's joins are driven by a test; the spec no
longer claims a type-argument bracket is always refused — `sort Ids = List [Int64]`
LOADS as `List[Int64]` (measured), a grammar ambiguity older than this ticket.

NOT TAKEN: one exhaustive emission seam (the six sites are exactly
`emit_own_descriptions`'s, which shares the risk); emitting a refused constraint's row
after validation (the load fails, and its `DescriptionInfo` has the same order); caching
per-row symbol lookups (WI-1031 measured the same per-member cost for `MemberInfo` as
noise).

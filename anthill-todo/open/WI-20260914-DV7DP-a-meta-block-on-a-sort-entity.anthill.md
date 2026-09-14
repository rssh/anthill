## Attributes

- id: WI-20260914-DV7DP-a-meta-block-on-a-sort-entity
- created: 2026-09-14T05:50:24Z

- status: Open
- status_agent: user
- status_at: 2026-09-14T05:50:24Z

- acceptance: cargo-test, scaland-sbt-test

- tags: reflect

## Description

A META BLOCK ON A SORT, ENTITY, CONST OR CONSTRAINT IS PARSED AND SILENTLY DROPPED — the grammar admits `[Marker, Key: value]` after those declarations and the parse IR carries it, but the loader never reads it, so the program loads clean and the metadata reaches nothing.

MEASURED FROM THE CODE (2026-09-14; not yet driven — acceptance row 1 is the drive). `parse/ir.rs` gives `meta: Option<MetaBlock>` to `AbstractSort`, `SortWithBody`, `Rule`, `Operation`, `Const`, `Entity`, `Fact` and `Constraint`, and tree-sitter-anthill/grammar.js accepts a trailing `meta_block` on sort, enum, effects, entity and const declarations. `kb/load.rs` reads it at exactly four sites: facts (`f.meta`), rules (`r.meta`, plus the destructured `meta` read by `meta_has_flag(…, "simp" / "unfold")`), the unlabeled-rule refusal, and operations (`o.meta` into `OperationInfo.meta`, §5.8). Nothing reads it for the other four kinds.

WHY IT MATTERS NOW. WI-20260914-Z73FX decided (with the user) that `internal` becomes a meta FLAG — `internal entity text(…)` shorthand for `entity text(…) [internal]` — carried as the clause metadata of the declaration's own reflect row (`SortInfo` / `MemberInfo`), with no new schema field. That spelling cannot exist while a declaration's block is discarded. Independently of Z73FX it is the silent-skip this repo's rules forbid: a `[Marker]` a codegen handler would read, written on an entity, does nothing and says nothing.

SHAPE. The block lowers through the existing `load_meta_block` to the same `meta(key: value, …)` term operations and rules use, and rides as the CLAUSE META of the reflect row the loader already emits for the declaration — `SortInfo` for a sort / enum / abstract sort, `MemberInfo(kind: Constructor)` for an entity constructor, the const's own row for a const, the constraint's labeled rule for a constraint. One reader for all of them is Z73FX's `KB.meta_of(kb, s: Symbol) -> Term`; this ticket only has to put the block where that reader will find it, and may ship its own minimal read path for the acceptance rows if Z73FX has not landed.

WHAT MUST STAY TRUE: a declaration with NO block keeps an empty `meta()` (the operations' convention, "no attributes"); §5.8's `OperationInfo.meta` is unchanged; a block's contents are not interpreted by the loader except where a key already has kernel meaning (none of these four kinds has one yet — `internal` is Z73FX's); an UNLABELED constraint with a block is refused the way an unlabeled rule's tag already is ("A `[…]` tag on it has no clause to govern"), not dropped.

ACCEPTANCE: (1) a sort, an enum, an entity constructor, a const and a labeled constraint each carrying `[Marker, Key: 7]` — the block is readable from the KB afterwards with `Marker` present and `Key` = 7, driven through a reader rather than asserted from the load succeeding; CONTROL: the same declarations without a block read as empty meta; (2) an unlabeled constraint with a block is refused, with the rule's message shape; (3) nothing that loads today changes its verdict — full workspace green via rustland/scripts/test.sh.


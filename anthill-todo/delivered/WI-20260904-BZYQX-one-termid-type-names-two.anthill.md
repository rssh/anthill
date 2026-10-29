## Attributes

- id: WI-20260904-BZYQX-one-termid-type-names-two
- created: 2026-09-04T10:39:12Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-29T04:45:26Z

- acceptance: cargo-test, scaland-sbt-test

## Description

ONE `TermId` TYPE NAMES TWO STORES — a parse-node index and a hash-consed KB term — so passing the wrong one COMPILES.

`parse/ir.rs` reuses `kb::term::TermId` as the index into `SimpleTermStore` ("a plain term store for parse time — no hash-consing or refcounting", a `Vec<ParseTermEntry>` with a span per entry). `kb::term::TermStore` is the other one: hash-consed, refcounted, structurally identical terms share an id. Nothing in the type system separates them.

THE TWO ARE NOT INTERCHANGEABLE, and the difference is exactly what several passes depend on. `Loader::compound_expression_occurrence`, `entity_slot_origin`, `binder_syms`, `parse_span_table` and `parse_dot_chain_table` all key on the PARSE id ON PURPOSE — `entity_slot_origin`'s own doc states the rule: "a KB `TermId` denotes a STRUCTURE (hash-consed, so a minted `ns.rel` and a hand-written `field_access(ns, rel)` share one), while every question the occurrence builder asks — which span, is this a dot the author wrote, was this bracket consumed — is about a PLACE." `binder_sym(name, pattern_var_parse_id)` is the sharpest case: hash-consing would collapse `let x = 0` and `let x = 1` into ONE binder site and defeat the alpha-renaming.

WHAT IT COSTS TODAY. A KB id passed where a parse id is expected type-checks and silently indexes the wrong `Vec` — an out-of-range panic if you are lucky, a wrong node if you are not. The only guard is a NAMING convention (`parse_id` / `kb_id`), which the loader follows at 284 and 114 sites respectively and which nothing enforces. WI-20260903-FC2X4 hit the confusion from the other side: `convert_expr_term(parse_id: TermId) -> (TermId, Rc<NodeOccurrence>)` had `TermId` in BOTH meanings, parse in and KB out. (That return was narrowed to the occurrence alone in FC2X4 — all three call sites discarded the handle — so the signature is unambiguous now, but only there.)

MEASURED SURFACE: 2 431 `TermId` mentions across the workspace. The PARSE population is small and localized — `parse/convert.rs` 85, `parse/ir.rs` 54, `parse/pratt.rs` 11, plus the loader's parse-facing half. `kb/typing.rs` (733), `kb/mod.rs` (285), `kb/node_occurrence.rs` (140) are KB-only and would not move.

THE ONE REAL OBSTACLE, and it must be settled first: `TermSource` (`kb/term.rs`) is a READ trait implemented by BOTH `KnowledgeBase` and `ParsedFile`, with `fn term(&self, id: TermId) -> &Term`. That shared signature is what lets `TermPrinter` render either side without duplicating the printing logic — and it REQUIRES the two stores to index alike. A newtype splits it. Options:

  (a) `TermSource` grows an associated id: `type Id; fn term(&self, id: Self::Id) -> &Term`. CHEAPER THAN IT LOOKS — `TermPrinter<'a, V: TermSource + ?Sized>` is ALREADY generic over the source, so its body swaps `TermId` for `V::Id` (24 mentions in `persistence/print.rs`). The `impl<'a> TermPrinter<'a, KnowledgeBase>` block pins `Id = TermId` and is unaffected.
  (b) Newtype at the loader/converter boundary only, unwrapping at the `TermSource` impl. Cheaper, and leaves the hole exactly where the trait erases the distinction.
  (c) Convention only: no newtype, just make the `parse_id` / `kb_id` naming a stated rule with a doc at both stores. Buys nothing the compiler checks.

END STATE the ticket should reach for: a `ParseTermId` for the parse side, after which the bare `TermId` denotes the KB store UNAMBIGUOUSLY — and consider renaming it (`KbTermId`) so no site is reading an id whose store it has to infer from the surrounding code. That rename is the expensive half (the 2 431 figure is its scope) and should be a separate pass from introducing the newtype, so the cheap safety lands first.

ACCEPTANCE. `ParseTermId` exists and the parse store indexes by it; passing a KB id to `SimpleTermStore` (or the reverse) is a COMPILE error, demonstrated by a doc-test or a `compile_fail` row — "it type-checks today" is the whole defect, so a row that only exercises the happy path measures nothing. `TermPrinter` still renders both sides through one body. Say which option was taken and what the other two would have cost.

## Changes

### 2026-10-28T21:27:53Z — feedback — claude

ROUTE TAKEN (user, 2026-10-28): (A) — `Term` is generic over its child id, `Term<I = TermId>`, and the parse store holds `Term<ParseTermId>`. A newtype on `SimpleTermStore::alloc`/`get` alone, which the Description asks for, checks only an expression's top term: `Term::Fn` holds its children as `TermId` (`pos_args`, `named_args`), so every child read off a parse term (`self.parsed.terms.get(pos_args[1])`) would come out a bare `TermId` and be wrapped back by hand — option (b)'s hole at every child read. The printer obstacle the Description names is mostly gone since it was written: `TermPrinter` is generic over `PrintView`, which already has `type Item` (`ParsedFile`'s is `TermId`). Also in scope: the eight `SimpleTermStore` side tables keyed by `TermId` (a wrong id there answers `false`, it does not panic) and the loader's `entity_slot_origin` / `binder_syms`, keyed by raw `u32`. DROPPED: the `KbTermId` rename (now 3 083 `TermId` mentions) — the KB side is moving to carrier-neutral values (WI-20261026-T51MG is one step), so the rename spends effort on the older approach. A possible second step, not part of this one: take the parse-only `Term::ParseAux` out of the KB's `Term`, where at least six arms exist only to reject it.

### 2026-10-29T04:45:25Z — feedback — claude

DELIVERED (user, 2026-10-29), route (A) in both implementations. rustland: `Term<I = TermId>`, parse store holds `ParseTerm = Term<ParseTermId>`; `ParseTermId` has no public constructor or `raw()`; `TermId::from_raw` is test-only; `TermSource`/`PrintView` take the source's own id, so `TermPrinter` still renders both sides through one body; parse side tables, loader parse sets and the seven `.raw()`-keyed loader maps are keyed by their id type. Rows: three `compile_fail` doc-tests on `ParseTermId` plus one that compiles — each refusal, compiled as an ordinary test, fails with one E0308 at the id argument (stable rustdoc does not check the code), and the first compiles at the parent commit. scaland: `TermOf[+I]` with `type Term = TermOf[TermId]`, opaque `ParseTermId`, store-typed `Term.Fn` patterns; `ParseTermIdTest` matches each refusal on Found/Required, and with `ParseTermId` aliased to `TermId` under `core/clean` the three refusals fail and the positive case passes. Options not taken: (b) newtype at the boundary only — checks an expression's top term, every child read would be re-wrapped by hand; (c) convention only — nothing checked. Not done: the `KbTermId` rename, and moving `Term::ParseAux` out of the KB's `Term`. Gates: cargo 11 079 passed / 0 failed; scaland testFull 818 passed / 0 failed.


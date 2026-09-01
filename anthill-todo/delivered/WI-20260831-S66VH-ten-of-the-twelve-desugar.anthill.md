## Attributes

- id: WI-20260831-S66VH-ten-of-the-twelve-desugar
- created: 2026-08-31T18:13:34Z

- status: Delivered
- status_agent: codex
- status_at: 2026-09-01T09:28:33Z

- acceptance: cargo-test

## Description

TEN OF THE TWELVE DESUGAR TARGET ADDRESSES ARE STILL HAND-SYNCED ACROSS THE TREE, so `desugar_target` owns the address for two of its members and merely declares it for the other ten. WI-909's group-3 pass added `desugar_target::qualified()` and routed `register_builtin_tags` plus the two typer sites through the constants for `CUT` / `FIND_DICTIONARY`; that mechanism was never applied to the reflect ten, and the duplication it removes is much larger there.

MEASURED on the tree at feb4b25d (the WI-909 group-3 commit), over `anthill-core`, `anthill-stl`, `anthill-cpp-gen` and `anthill-smt-gen` `src/`, excluding `desugar_target.rs` itself and whole-line comments: **78 textual occurrences of the ten addresses across 14 files in 4 crates**, of which **54 sit inside a `resolve_symbol` / `try_resolve_symbol` / `intern` call or a `==` / `!=` string comparison** — i.e. real coupling, not prose. Distribution: typing.rs 19, load.rs 17, term_view.rs 8, eval/mod.rs 8, node_occurrence.rs 6, cpp-gen 4, typing/tests.rs 4, resolve.rs 4, kb/mod.rs 3, and one each in stl/reflect/builtins.rs, smt-gen, simp_rewrite.rs, body_specialize.rs, eval/builtins.rs. THE 78/54 SPLIT IS NOT FULLY SEPARATED — the grep drops whole-line comments but not trailing ones, so the first step is to partition it rather than trust either number as the site count.

THE NAMED ONES, because each fails differently and silently:
  `kb/load.rs:5004`      `CAPTURE_RECORD_CONSTRUCTOR = "anthill.reflect.TupleLiteral"` — a SECOND named constant for `dt::TUPLE_LITERAL`, the exact shape `qualified()` exists to retire.
  `eval/mod.rs:161-187`  the `ExprSyms` table — twenty addresses re-resolved by literal, `list_literal` / `tuple_literal` / `set_literal` among them.
  `body_specialize.rs:898` and its mirror `anthill-smt-gen/src/lib.rs:1684` — the dual-spelling `qn != "anthill.reflect.field_access" && qn != "field_access"` arms.
  `node_occurrence.rs:3567/3621/3630/3659`, `term_view.rs`, `cpp-gen/src/lib.rs:3246/3321-3323`.

WHY IT MATTERS: rename `ListLiteral` or `Expr.if_expr` in `stdlib/anthill/reflect/reflect.anthill` and `wi040_reserved_vocab_test::every_desugar_target_is_declared_by_the_standard_load` catches the `desugar_target` side while NONE of these are caught. The bracket lowering then returns `None` for every literal, `ExprSyms` resolves a phantom symbol, and the program LOADS CLEAN with the lowering silently disabled. That watchdog is also vacuous for every builtin-tagged name (16 of the 27 it walks — stated at its site), so `field_access` and `ho_apply` have no orphan coverage at all.

THE VEHICLE EXISTS AND IS ONE LINE PER SITE: `desugar_target::qualified(dt::LIST_LITERAL)` yields the plain qualified name, delegating to `intern::absolute_path_target` so the marker keeps a single reader. `kb/typing::REQUIREMENT_OUT_LABEL` is the established precedent for a cross-module shared name constant.

NOT A MECHANICAL SWEEP, and that is why this is a ticket rather than an inline edit. `body_specialize.rs:898`'s dual-spelling arm is the one WI-20260825-5W3RJ's history records as subtle: keying it wrong made the parse-side print of `[1, 2]` stop rendering as a bracket, the content-addressed retract key stop matching, and a retracted fact stay on disk with NO error anywhere — caught only by `wi1099_list_literal_twin_test::a_persisted_literal_is_still_retractable`. Its smt-gen mirror has no such row. Any site gated on `is_minted` may compare to the constant directly; a site that must admit a hand-written short spelling needs `dt::is`, which must NEVER be used for `CUT` / `FIND_DICTIONARY` (it asserts against that).

CONTROL: rename one target in `reflect.anthill` (say `ListLiteral` -> `ListLiteralX`) and the suite must FAIL, naming the address, in place of today's silent lowering. Back the sweep out and that rename must return to loading clean — that inversion is the measurement, not the mere presence of a passing test. Keep `wi1099`'s retractability row green throughout; it is the only one that measures the parse-view/KB-view split.

ACCEPTANCE: no `.rs` file outside `desugar_target` writes one of the twelve addresses as a literal where the constant would serve; the rename control above fails loudly; `wi1099_list_literal_twin_test` and the cpp-gen / smt-gen accessor recognizers stay green; full workspace green via rustland/scripts/test.sh. REFERENCE: WI-909 (which introduced `qualified()` for two of the twelve), WI-20260825-5W3RJ (which created the constants and records the print.rs landmine), WI-20260824-6RXGD (the `field_access` attempt and its five findings).


## Attributes

- id: WI-20261106-BYJ0X-a-dotted-sort-member-written
- created: 2026-11-06T09:25:19Z

- status: Delivered
- status_agent: claude
- status_at: 2026-11-26T06:08:18Z

- acceptance: cargo-test, scaland-sbt-test

## Description

a dotted sort member written without parentheses in a `@[simp]` right-hand side (`f(?a) <=> K.seven @[simp]` over a const, `K.one` over a nullary operation) dies in the typer where the rewrite fires with an internal-defect message; `K.one()` runs

## Changes

### 2026-11-06T09:25:49Z — feedback — user

FOUND BESIDE WI-20260825-6RRVA (bd8eebdf) while looking for a positive row. MEASURED on bd8eebdf, each with `operation f(a: Int64) -> Int64`, `rule r: f(?a) <=> RHS @[simp]` and `operation g(x: Int64) -> Int64 = f(x)`, over `sort K { const seven: Int64 = 7; operation one() -> Int64 = 1; entity box(v: Int64) }`: RHS `K.seven` and `K.one` refuse at g's splice with "type mismatch in p6r.pos.K.reference: expected a type value recorded where the sort is written (proposal 055 §1), got a plain reference to the sort — a defect in the walk that built this occurrence, not an error in the program" plus "seven.name / one.name: expected resolved name, got unresolved"; `K.one()` loads and runs; the same with `K.mk.v` (a field read off a nullary op). LIKELY CAUSE, not verified: an equation head converts with ConstFold::Off, so the data-slot const fold and the dotted rungs leave the replacement's chain as `field_access(Ref(K), seven)`, and the spliced replacement reaches the typer as a field access whose receiver is a plain sort Ref with no recorded type value. Loud today (load error), so not silent — but the message blames the loader's walk, and the spelling is one §5.3 now tells authors is a path.

### 2026-11-26T06:08:16Z — feedback — user

Implemented 2026-11-26 (63eb28d9e). A paren-less dotted name in a @[simp] replacement is built by the walk that reads it in an operation body (Loader::replacement_dotted_name_occurrence -> convert_expr_term, its try_qualified_*_ref ladder and DotFieldPass), sharing compound_expression_occurrence's memo; the stored head term is not moved. CAUSE (the ticket's guess, confirmed): the replacement converts with ConstFold::Off, so the rule-body walk's data-slot readers of a dotted name (data_slot_dotted_const and siblings) declined and the chain stood as field_access(K, seven), K a plain sort reference, which the typer refused where the rule fired.
GATED: only a name rooted at no binding whose whole name is a rule, const, sort, constructor or operation, or a prefix of it a value; a name naming nothing, a member hidden by internal, and a namespace keep their refusals (counts unchanged). Not in a quoted reflect Term field: entity_ctor_children now sets in_quoted_term for the occurrence walk's re-walk (MEASURED with that gate out: Q(pattern: K.seven) fired as Q(pattern: seven), loaded clean and found no fact, a silent miss). No spec change: kernel-language.md §5.3 already reads a qualified name as a path.
DONE: tests/include/wi_byj0x_simp_rhs_dotted_member_test.rs (wi_tests), 7 rows. Spliced into an operation body K.seven, byja.K.seven, K.In.eight, K.one, K.mk.v run to 7/7/8/1/3 as their twins (seven, eight, K.one(), K.mk().v) do; id(K.seven), ob(v: K.seven), ob(v: some(K.one)) likewise; K.In and byja.K.In are the type value In is; fired in a rule body K.seven answers what seven answers (before: refused). Controls: K.one, K.one(), K.mk.v fired in a rule body unchanged (1/1/3); K.zz, K.zz.deep, Vault.secret (internal), byjb.lib (namespace) refused with the same messages and counts; the quoted-field row never loads clean and misses. Back-outs: whole change out, the 4 headline rows fail and the 3 controls pass; only the in_quoted_term gate out, only the quoted-field row fails.
/code-review xhigh: fixed, exact refusal counts, the quoted control anchored at the replacement's line with a sound twin, nested rows, the doc's measured list. Left, pre-existing, not filed: a dotted name in a quoted Term field of a replacement is still refused with the internal-defect message where it fires; a replacement fired by the resolver in a rule body binds a const's or operation's name, not its value (<=> seven gives seven), and mk.v leaves a residual; a hidden member in a replacement is refused twice at one place; Box.rel cited in an operation body for a rule declared in a sort is refused as an unresolved name.
Gate: workspace 12790 passed, 0 failed; scripts/families.sh green, no verdicts moved; scaland sbt testFull 811 + 51 (2 skipped) + 1 passed, 0 failed (no Scala touched).


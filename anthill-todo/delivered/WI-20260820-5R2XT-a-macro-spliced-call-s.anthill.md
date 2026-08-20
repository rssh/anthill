## Attributes

- id: WI-20260820-5R2XT-a-macro-spliced-call-s
- created: 2026-08-20T05:33:44Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-20T07:34:57Z

- acceptance: cargo-test, scaland-sbt-test

## Description

A MACRO-SPLICED CALL'S DIAGNOSTIC NAMES THE SYNTHESIZED OPERATION, NOT THE SURFACE CALL. Split out of WI-20260819-33H3P (delivered), which repaired the other half of the same symptom — the LOCATION — and deliberately stopped there.

THE SYMPTOM, measured on the current tree. `p.join(q, lambda (c, d) -> eq(c.id, d.owner))` where both relations carry a `name` column now reports:
  21:13: type mismatch in join_run.return (op-return): expected a well-formed type projection, got `concat` operands share the field name `name` ...
The location is right (it is the author's `p.join(...)`, which is what 33H3P fixed). `join_run` is not: it is the RUNTIME back-end the `conjoin_of` macro splices, and the author wrote `join`. The same holds for `where` / `where_run`.

WHY IT IS NOT A ONE-LINER, which is why 33H3P did not do it inline. The label comes from `TypeErrorContext::OperationReturn { op_name }` (kb/typing.rs), built at 16 sites from the CALLEE symbol of whatever call is being checked. For the spliced call that symbol IS `join_run` — the context is not wrong, it is merely internal. Naming `join` needs a PROVENANCE channel the occurrence does not carry today: `splice_query_runner` (eval/builtins.rs) stamps the synthesized nodes with the pass `anthill.kb.passes.macro_expand`, which says a macro made them but not WHICH SURFACE MEMBER it was expanding — and the builtin itself knows it is `conjoin_of`, not `join`, since the `[simp]` rule `join(?r1, ?r2, ?cond) <=> conjoin_of(...)` is what got there.

DECIDE FIRST, then implement:
  * WHAT THE READER SHOULD SEE — `join.return`? `join (expanded to join_run).return`? The second keeps the internal name findable, which matters when the failure really is in the runner's own signature rather than in the author's operands.
  * WHERE THE NAME COMES FROM — the `[simp]` redex's own functor is the honest source (`join`, the thing that was rewritten), not anything the macro builtin knows about itself. That suggests carrying it on the occurrence at the REWRITE, not at the splice.
  * WHETHER IT IS A SEPARATE FIELD OR A RENAME — a `surface_name: Option<Symbol>` beside `op_name` keeps every existing site compiling and unchanged; keying the typer on the callee's identity is forbidden here (the typer stays universal).

SCOPE. Every macro-spliced call, not `join` alone: `where_run` has the same face, and any later `[simp]`-backed combinator will inherit it. Do not special-case `join_run` by name.

ACCEPTANCE: the un-renamed `join` column collision names `join` (in whatever spelling is decided) rather than `join_run` alone, at the location WI-20260819-33H3P already pins; the same for a `where` refusal; the five arms of `wi_33h3p_dot_call_receiver_span_test` stay green (they assert the LOCATION and the refusal text, so they must not need editing for a naming change — if they do, say why); no typer site keys on an operation's identity; cargo-test green via scripts/test.sh.


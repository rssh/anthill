```anthill
fact WorkItem(id: "WI-20260819-33H3P-a-dot-call-receiver-s", created: "2026-08-19T04:52:29Z", acceptance: [ToolPasses(tool: "cargo-test"), ToolPasses(tool: "scaland-sbt-test")], depends_on: some(value: nil), status: Open)
```

## description

A DOT-CALL RECEIVER'S OCCURRENCE CARRIES NO SPAN, so every diagnostic anchored on it reports at 1:1 and blames a synthesized operation the author never wrote. Split out of WI-731 (delivered), which measured the cause and found it is NOT where WI-1128 pointed.

THE SYMPTOM, measured on the current tree. `p.join(q, lambda (c, d) -> eq(c.id, d.owner))` where both relations have a `name` column reports:
  1:1: type mismatch in join_run.return (op-return): expected a well-formed type projection, got `concat` operands share the field name `name` ...
`join_run` is synthesized by the `conjoin_of` macro; the author wrote `join`. `fix` reports the analogous `Without` refusal at a REAL location ("15:5: type mismatch in fix.return"), so the contrast is the macro path, not the reduction.

WHERE IT IS NOT (this is what WI-1128 and WI-731's own feedback had, and it is wrong). WI-1128 recorded "the anchor occurrence ALREADY carries a zero span, so the span is NOT lost by the macro" and directed the next reader at the `[simp]` rewrite `join(?r1, ?r2, ?cond) <=> conjoin_of(...)` and at `substitute_to_occurrence`. MEASURED (temporary eprintln at `instantiate_rhs`, since removed): the `from` occurrence handed to the rewrite has a REAL span -- `SourceSpan { source: SourceId(76), span: Span { start: 554, end: 599 } }`, exactly the written `p.join(q, ...)`. So the rewrite receives a located redex and the loss is not there.

WHERE IT IS. Probed at `splice_query_runner` (eval/builtins.rs): the two relation operands do NOT agree.
  anchor (?r1, the dot RECEIVER `p`) = SourceSpan { source: SourceId(0), span: Span { start: 0, end: 0 } }
  the second (?r2, the written argument `q`) = SourceSpan { source: SourceId(76), span: Span { start: 561, end: 562 } }
So the written argument keeps its location and the RECEIVER has none. Probed one level further, at the `TypeBuildFrame::DotApply` arm (kb/typing.rs): for member `join`, `occ.span` is the real 554..599 while the RAW receiver occurrence -- `Expr::DotApply { receiver }`, an ordinary `Expr::VarRef` -- is already `SourceId(0) 0..0`, and `recv.node` is the same `Rc`. The receiver occurrence is therefore span-less BEFORE any typing, macro or rewrite runs.

CONTRAST WORTH KEEPING, because it says the loss is not universal: in `r.rename(who: r.name)` the receiver of the inner `r.name` carries 404..410 -- which is the span of the WHOLE `r.name`, not of the one-character `r`. So on that path a receiver occurrence INHERITS its parent's span, and on the dot-call path it gets none at all. Both `push_field_access` and the method-call builder push the identical `WorkOp::Visit(WorkKind::Term, receiver)` (parse/convert.rs), so the divergence is downstream of the converter -- in how a receiver TERM's span is recorded or read when the occurrence is built (`build_expr_leaf` / the `var_ref` arm take `span` as a parameter; the question is what the caller passes for a dot receiver).

WHY IT WAS NOT FIXED IN WI-731. That ticket listed it as "ALSO IN SCOPE, inline (small)". It is not small: the fix is either in term->occurrence span propagation (a leaf's span is not a rename concern and has other readers) or in choosing a different anchor at the splice. The latter is reachable but is a heuristic -- "anchor on an operand that happens to have a location" -- and picking it without knowing why the receiver has none would be guessing. WI-731 shipped the half that was genuinely inline: the message now names the `rename` operator as the repair instead of saying "rename one" with no spelling behind it.

SCOPE. Decide first whether the receiver occurrence SHOULD carry a span (and which -- its own, or its parent dot node's, as the field-access path effectively does), then fix it there; the splice anchor then needs no rule of its own. Check the other consumers of a receiver occurrence's span before changing it -- `projection_type_error` sites, `macro_rejection_error`, and the WI-757 guard at kb/typing.rs that PANICS when a macro rejection's span comes from a different file than the redex (a zero span is `SourceId(0)`, so making it real could start tripping that guard where it currently does not).

ACCEPTANCE: the un-renamed `join` column-collision reports at the written `p.join(...)`, naming a location in the user's file rather than 1:1; a macro rejection and a `where`/`join` type error each still report where they do today (name the tests); the WI-757 cross-file span guard does not fire on the corpus; `wi714_join` / `wi714_where` / `wi731_rename` green; cargo-test green via scripts/test.sh.


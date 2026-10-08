## Attributes

- id: WI-20261008-T290W-scaland-the-parser-has-no-name
- created: 2026-10-08T10:08:06Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-08T14:18:24Z

- acceptance: scaland-sbt-test

## Description

SCALAND: THE PARSER HAS NO `..name` SPELLING. An absolute name is a parse error.

THE PROGRAM:

  namespace n
    rule ..nosuchxyz()
  end

  rustland   parses; "unresolved name '..nosuchxyz' in scope 'n'", and the body-less rule is refused with
             "`..nosuchxyz` is a QUALIFIED name, and a qualified name references an existing predicate"
  scaland    probe.anthill:2:8: parse error: found "..nosuchxy"

kernel-language.md §2: "A `Name` is resolved relative to where it is written; `..` asks for the" root.

MEASURED 2026-10-08 while porting WI-20260821-RDGQC to scaland: rustland's census drives the qualified-spelling reason with `rule ..nosuchxyz`, and scaland's `HeadIntroductionCensusTest` had to use `rule nosuch.xyz` instead. Only the rule-head position was measured; `grep '"\.\."'` over `AnthillParser.scala` finds nothing, so the spelling is likely absent everywhere a name is read.

ACCEPTANCE: drive it. `..a.b` parses wherever rustland's grammar admits it and resolves from the root: a goal `:- ..n.p(?x)` written in another namespace answers from `n.p`, and the control is the same goal spelled `n.p(?x)`. `HeadIntroductionCensusTest`'s two qualified rows gain the `..` spelling. `sbt -batch testFull` green.

## Changes

### 2026-10-08T14:18:23Z — feedback — claude

DELIVERED — scaland parses `..a.b` in the reference positions rustland's grammar gives it and resolves it from the root (user, 2026-10-08).

PARSER. `Tokens.absoluteHeadToken` puts the marker on the head segment's text, as rustland's `_absolute_head` does; `refName` is taken by a term atom, a call and application head, `Ref(…)`, a type, a proof target and a mapping source. A declaration still takes `name`. `describe` is not parsed by scaland at all, so that position has nothing to take the spelling.

LOADER. `lookupWritten` answers a marked name from `byQualifiedName` alone, with no scope walk; `anthill.intern.absolutePathTarget` is the marker's one reader. A marked name that names nothing is `unresolved name`, in a term and in a proof target. `Ref(a.b)` carries the whole path where it carried its last segment.

THIS IS ALSO THE RUNG WI-20260902-373AW ASKS FOR — the shared Pratt table mints fourteen operators with their address. So the written `not` / `!` is NAF; `reallocTerm` reads `not`'s negand as a goal (`KnowledgeBase.goalArgSlots`), so `not(ns.flag)` negates the predicate; and an operator in a KB without the stdlib is a load error. Three fixtures moved onto the stdlib; four rows that pinned the dead `not` are re-pinned.

EMITTER. `TypeScope.placePath` places `..a.b.T` by the package it spells; a one-segment `..T` is refused, Scala having no qualified spelling for an empty-package member. Before: `my.app...Top[X]` was emitted. docs/scala-forward-mapping.md §2.1b states the rule.

PINNED, NOT FIXED. `not(true)` answers 1 (WI-20260908-NARC7). `Ref(Rec.E)`, a relative path, resolves to nothing as the call `Rec.E(…)` does (WI-20261008-JRV1T); it resolved by its last segment before. An effect row `{..E, E}` merges into one effect, as `{a.E, b.E}` already did (not filed). NOT DONE: kernel-language.md §8.6 still says scaland implements neither reading; the sentence waits on the user.

`AbsoluteNameTest` (14 rows) and the negand row in `DottedParenLessCitationTest`; their headers state the back-outs, measured over the core suite. /code-review: 12 findings, 8 fixed. One fix made the smt-gen fixture read load errors and found a stale `import anthill.prelude.{Int}` in `CommDelayTest`. scaland: sbt testFull, 628 + 35 + 1 passed. rustland untouched and not run.

### 2026-10-08T14:36:35Z — feedback — claude

ADDENDUM, 2026-10-08 — one position was missed, found answering the user's question about an effect row. A TYPE WRITTEN INSIDE A TERM read its path's last segment (`AnthillParser.typeExprToRef`), so `fact viaAbs(Box[T = ..zzAbs.tn.C])`, written in a namespace with its own `C`, bound that namespace's `C`: the marker was dropped with the qualification. The unmarked `zzAbs.tn.C` had the same defect before this ticket. Both bind `zzAbs.tn.C` now; `Ref(…)` and a lowered type carry a path through one function, `writtenSymbol`.

THE EFFECT ROW. `{a.E, b.E}` on an arrow type kept one label, `Ref(E)` — the same lowering, not the de-duplication, which my delivery note blamed. Only the one-segment `..E` kept its text and was then dropped by the short-name key. The row is ordered by short name and told apart by the name written, so `{a.E, b.E}`, `{..a.E, a.E}` and `{E, ..E}` keep two labels and `{E, E}` one. Two spellings of one symbol stay two atoms: the parser resolves nothing, where rustland de-duplicates after resolution.

A relative path in a type inside a term (`Box[T = Rec.E]`) resolves to nothing, as `Ref(Rec.E)` and `Rec.E(…)` do (WI-20261008-JRV1T); the three are pinned as one in `AbsoluteNameTest`. Rows: `a type written inside a term is the path it writes` there, and `a canonical row tells effects apart by the name written, not by its last segment` in `ParseTest`; back-outs measured. kernel-language.md §8.6 and proposal 044 now say scaland implements the absolute reading only (user, 2026-10-08). scaland: sbt testFull, 630 + 35 + 1 passed.


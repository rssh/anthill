## Attributes

- id: WI-20261008-T290W-scaland-the-parser-has-no-name
- created: 2026-10-08T10:08:06Z

- status: Open
- status_agent: user
- status_at: 2026-10-08T10:08:06Z

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


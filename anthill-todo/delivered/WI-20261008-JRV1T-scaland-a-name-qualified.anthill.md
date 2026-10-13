## Attributes

- id: WI-20261008-JRV1T-scaland-a-name-qualified
- created: 2026-10-08T10:08:04Z

- status: Delivered
- status_agent: codex
- status_at: 2026-10-13T17:52:47Z

- acceptance: scaland-sbt-test

## Description

SCALAND: A NAME QUALIFIED RELATIVE TO THE SCOPE IT IS WRITTEN IN DOES NOT RESOLVE. The clause is stored under a symbol nothing can name, on a program that loads clean.

THE PROGRAM:

  namespace n
    sort Rec
      entity E(v: Int64)
      rule p(1) :- true
      rule see(?x) :- p(?x)
    end
    fact Rec.p(2)
  end

                                              rustland   scaland
  n.Rec.see(?x)                                   2          1     <- the fact is not a clause of n.Rec.p
  the same with `rule Rec.p(2) :- true`           2          1
  the same with `fact n.Rec.p(2)`                 2          2     <- the fully qualified spelling works

kernel-language.md §2: "A `Name` is resolved relative to where it is written".

MECHANISM. `Loader.lookupWritten` answers a dotted spelling from `byQualifiedName` — the table of ABSOLUTE names — and otherwise hands the WHOLE spelling to `resolveInScope` as one short name. Nothing resolves the first segment by scope and walks the rest, which is what rustland's `resolve_dotted_in_kb` does. A miss falls to `resolveName`'s `kb.intern(name)`, so the clause lands under a symbol spelled `Rec.p`.

MEASURED 2026-10-08 while porting WI-20260821-RDGQC to scaland; that port did not change it. Only the HEAD position was measured. Before scoping the fix, run the body-goal and value positions too — rustland answers 1 for `rule see(?x) :- Rec.p(?x)` written in `n`, and refuses `:- Rec.nosuch(?x)` with "rule-body goal `Rec.nosuch` names nothing".

ACCEPTANCE: drive it. The program above answers 2 through `n.Rec.see`, in the fact spelling and the rule spelling. The fully qualified spelling keeps answering 2 — that row passes before and after and says so. A relative spelling that names nothing gets whatever rustland gives the same program, measured there first. `sbt -batch testFull` green.

## Changes

### 2026-10-08T14:18:37Z — feedback — claude

ONE MORE SPELLING IN THIS TICKET'S POPULATION since WI-20261008-T290W, 2026-10-08: `Ref(Rec.E)`. `Ref(…)` used to read its last segment, so this resolved through the sort's variant exposure; it carries the whole path now, as a call functor does, and resolves to nothing exactly as `Rec.E(…)` does. `AbsoluteNameTest`, row `a RELATIVE path in Ref resolves as the call spelling of it does — not yet`, pins the pair at (`Rec.E`, unresolved) with the logical answer named. It must flip when the relative reading lands.

### 2026-10-08T14:36:36Z — feedback — claude

A THIRD CARRIER, 2026-10-08 (WI-20261008-T290W's addendum): a type written inside a term. `fact typeRel(Box[T = Rec.E])` binds a bare symbol spelled `Rec.E`, as `Ref(Rec.E)` and `Rec.E(…)` do; it read its last segment before and so resolved through the sort's variant exposure. The same `AbsoluteNameTest` row pins all three as one answer.

### 2026-10-13T17:52:38Z — feedback — codex

Implemented scoped dotted lookup in Loader.lookupWritten: resolve the head where written, then walk members with enclosing links stopped. Ambiguity ends the path; no root fallback after a missing member. Shared lookup covers heads, body goals, constructor calls, Ref and term type bindings. Dotted reference misses now produce located UnresolvedName diagnostics. Measured with the existing rustland CLI: relative fact and rule heads and the fully qualified control each answer 2; the relative body goal answers 1. Unresolved qualified fact/rule heads load in rustland, so Scala preserves that control; unresolved body/data/Ref/type paths are refused. Structural bracket fixtures now load their stdlib constructor declarations, and the old dotted-body silent-miss pin now expects refusal. Regression tests drive resolution, shadowing, imported nested paths and all three term carriers. Back-outs: old lookup causes 6 of 20 AbsoluteNameTest rows to fail (14 controls pass); removing only the dotted diagnostic causes 3 of 26 rows across AbsoluteNameTest and DottedParenLessCitationTest to fail (23 pass). Full sbt -batch testFull: 668 core + 40 SMT + 1 Scala generator tests passed. git diff --check passed. Direct diff review completed; /code-review skill unavailable in this session, not run. No specification changes and no commit.


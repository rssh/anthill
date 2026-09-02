## Attributes

- id: WI-20260902-373AW-scaland-s-loader-cannot
- created: 2026-09-02T06:15:10Z

- status: Open
- status_agent: user
- status_at: 2026-09-02T06:15:10Z

- acceptance: scaland-sbt-test

## Description

SCALAND'S LOADER CANNOT RESOLVE A `..` ABSOLUTE PATH AT ALL, so every operator the SHARED
Pratt table addresses absolutely is bare-interned -- and `not` / `or` are DEAD in a rule
body, silently, on a stdlib that loads with ZERO errors.

MEASURED (scaland, WI-20260901-719FJ's tree), with the FULL stdlib loaded (60 files,
0 parse errors, 0 load errors) and the fixture loaded beside it (0 load errors):
  rule pz(?n) :- bz(?n)          -- HOLDS for 1
  rule emptyz(?n) :- bz(9)       -- EMPTY
  rule nafEmpty(1)  :- not(emptyz(1))          -> 0     NAF would answer 1
  rule nafFull(1)   :- not(pz(1))              -> 0     right by accident
  rule orFirst(1)   :- pz(1) or emptyz(1)      -> 0     the first disjunct HOLDS
  rule orNeither(1) :- emptyz(1) or emptyz(2)  -> 0     right by accident
  rule commaCtl(1)  :- pz(1), bz(1)            -> 1     CONTROL: the goal machinery works
So the comma conjunction resolves and the three WRITTEN connectives resolve to nothing.
`!q(1)` measures the same as `not(q(1))` -> 0, and `p and p` with BOTH conjuncts true -> 0.

AND THE TARGETS EXIST: with the same KB, `anthill.kernel.not` = symbol 59,
`anthill.kernel.or` = 1110, `anthill.kernel.and` = 1111. `Prelude.registerBuiltinTags`
puts `BuiltinTag.Not` on 59 and `SearchStream` (line ~167) dispatches `stepNaf` on that
tag. Nothing about NAF is missing; the goal just never reaches the tagged symbol.

MECHANISM, CONFIRMED FROM SOURCE AND DRIVEN. `Pratt.scala` -- the layer scaland and
rustland SHARE by design -- addresses FOURTEEN operators absolutely: the eleven spec ops
(`+ - neg * / mod = != < <= > >=`, WI-20260825-1WBZT) and the three connectives
(`or` / `and` / `not`|`!`, WI-20260825-P9Y67). A goal `not(q(1))` therefore loads with the
functor NAME `..anthill.kernel.not`. `Loader.lookupWritten` is:
    if name.contains('.') then byQualifiedName.get(name) orElse resolveInScope(name, scope)
    else resolveInScope(name, scope)
Neither rung strips the `..`, so both miss, and `Loader.resolveName` ends
`case NotFound => kb.intern(name)` -- the WI-476 bare intern. MEASURED: the goal's functor
is symbol 1130 named literally `..anthill.kernel.not` while the real one is 59, and
`kb.getBuiltin(goal)` answers `None`. There is no `absolutePathTarget` in scaland at all
(rustland has `intern::absolute_path_target` + `resolve_dotted_in_kb`'s `dotted_absolute`
rung, WI-1075).

THE CENSUS, which is how loud this is: after a full stdlib load PLUS that fixture, exactly
THREE symbols in the KB have a name beginning with `..` --
`..anthill.kernel.not`, `..anthill.kernel.or`, `..anthill.prelude.PartialEq.eq` -- every
one a bare intern nothing declared, on a load reporting zero errors. The stdlib alone
mints two of them (`stdlib/anthill/reflect/typing.anthill:270` writes `:- not(...)`, so
scaland's OWN stdlib rule is dead). The other eleven addresses surface the moment a
program writes those operators in goal position.

`=` IS IN THE CENSUS BUT IS NOT SEPARABLE HERE, and that is stated so the ticket is not
read as claiming more than it drove: `anthill.prelude.PartialEq.eq` has no clauses in a
scaland KB, so `?x = 1` and the short-spelled `eq(1, 1)` both answer 0 and the address
makes no difference yet. It will the moment `eq` gains a clause or a builtin.

WHY IT IS SILENT AND NOT LOUD, which is the second half of this ticket. scaland has no
typer and no WI-1034 `undefined_rule_body_goals` backstop, so a goal naming nothing simply
fails. WI-20260820-MH90F's own review recorded exactly this failure mode for `not` ("a
lost `not` mints an untagged same-named symbol and NAF just stops firing") and guarded the
IMPORT path with a `PreludeScopesTest` row -- but that row resolves the SHORT name `not`
from `anthill.reflect.typing` and asserts the tag, and NO SOURCE SPELLING REACHES IT: the
Pratt prefix table rewrites every written `not`/`!` to the address, so
`Prelude.registerBuiltinTags`' `addImport(globalScope, "not", sym)` has no user. The guard
is intact and guards a path programs do not take.

RELATION TO WI-20260901-ERF7T, which is the same missing mechanism from the other side:
ERF7T is "scaland MINTS BARE where rustland mints absolute" (the twelve desugar targets);
this is "scaland ALREADY MINTS ABSOLUTE -- from the shared Pratt table -- and cannot
RESOLVE it". Whichever lands first should build the `..` rung; the other then only has to
move mints onto it. Not filed as a dependency because which order is cheaper is undriven.

ACCEPTANCE: drive it. `rule r(1) :- not(empty(1))` answers 1 when `empty` is empty and 0
when it holds; `p or q` answers when EITHER disjunct holds and not when neither does;
`p and q` answers only when both do. The CONTROL is the comma conjunction, which answers
either way -- without it a fix that broke goal resolution outright would pass. Assert the
CENSUS too: a full stdlib load holds ZERO symbols whose name starts with `..`, which is
the assertion a fourteenth address cannot slip past. Decide and drive the LOUD half: a
`..` path naming nothing is REFUSED in rustland (WI-1075) and bare-interned here, so say
what scaland does with one -- if the rung lands without a refusal the next mis-addressed
target is silent again. Say at each site which scaland test fails when it is backed out.
`sbt test` green.


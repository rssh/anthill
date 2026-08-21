## Attributes

- id: WI-20260821-ZW940-arity-should-distinguish
- created: 2026-08-21T15:24:24Z

- status: Open
- status_agent: user
- status_at: 2026-08-21T15:24:24Z

- acceptance: cargo-test, scaland-sbt-test

## Description

ARITY SHOULD DISTINGUISH OPERATIONS, and today it is refused -- while PREDICATES already
overload by arity and it works. The language is inconsistent with itself, and the refusal's
own message says the reason is representational rather than semantic.

USER POSITION (2026-08-21): `operation f(x)` beside `operation f(x, y)` in one scope
should NOT be refused. Arity is part of what identifies an operation.

MEASURED, the same shape in both halves of the language:
  namespace ar
    sort S { entity s(n: Int64)
             operation f(x: Int64) -> Int64 = x
             operation f(x: Int64, y: Int64) -> Int64 = x }
  -> REFUSED: "operation 'ar.S.f' is declared more than once in its scope (2 declarations)"
  namespace ar2 { rule p(1)   rule p(1, 2) }
  -> LOADS, `ar2.p` = 2 clauses.
And the predicate half is not merely accepted, it DISPATCHES. Driven over
`{ rule p(1)  rule p(1, 2)  rule p(7) }`:
    p(1) -> 1    p(7) -> 1    p(1,2) -> 1    p(9) -> 0    p(1,9) -> 0
Each arity answers its own clauses and neither reaches the other's.

THE REFUSAL'S STATED REASON IS A REPRESENTATION LIMIT (kb/load.rs, the duplicate-operation
message): "Anthill has no signature-keyed overloading. A scope maps a name to one symbol,
so the second `operation` did not introduce a second operation: it MERGED into the first,
and the kernel kept N signature records under that one name -- so which signature it
reports came down to WHICH WAS WRITTEN FIRST. Rename one." So the refusal exists to convert
a silent, order-dependent merge into a loud error. That is the right response to the
limit; it is not an argument that the limit is right. WI-1049 delivered the refusal, 059 R1
the type-declaration half.

WHY IT MATTERS BEYOND TIDINESS:
 * The predicate side proves the kernel can key on arity -- clauses of one symbol are
   selected by arity at resolution, correctly, today. So "one name, one symbol" does not
   force "one name, one arity"; it is the OPERATION path that collapses them.
 * It blocks ordinary shapes. An operation with an optional extra argument, or a curried
   and an uncurried spelling, must be renamed rather than overloaded, and the diagnostic's
   own advice is "Rename one."
 * It bears on proposal 061 (rule declarations), open question 2 -- "does a declaration fix
   ARITY?". If arity distinguishes, `rule p/2` becomes the natural declaration form and the
   question answers itself; if it does not, a declaration has to say which arity it means
   for a predicate whose clauses already differ.

WHAT THIS TICKET HAS TO DECIDE, and it is a language change, not a diagnostic one:
 1. Is the IDENTITY of an operation `(scope, name)` or `(scope, name, arity)`? Everything
    keyed on the symbol follows -- dispatch, the requirement dictionary (WI-857), the
    `provides` operation map, 059 R4's capture rule, and `SymbolTable::define`'s merge.
 2. If arity distinguishes, WI-1049's refusal narrows to a genuine duplicate (same name AND
    same arity) rather than disappearing -- the silent merge it was written against is
    still a silent merge.
 3. Named arguments and 056's variadic capture (`...args: R`) make "arity" less than
    obvious as a key; say what it means for a declaration carrying named slots or a
    capture before keying anything on it.

WATCH FOR: same-named operations on DIFFERENT sorts are already fine and are chosen by
carrier -- that is not overloading and must not be disturbed. And a `rule` whose head names
an operation is not a second DECLARATION (the message says so); WI-939 item 4 owns the
body-plus-clause pair.

ACCEPTANCE: `operation f(x)` beside `operation f(x, y)` in one scope loads, and BOTH
dispatch -- drive each and assert its value, with a control showing a genuine duplicate
(same name, same arity) is still refused naming both sites. The predicate rows above stay
green as the control that arity-keyed selection already works. cargo-test green via
rustland/scripts/test.sh.

## Changes

### 2026-08-21T15:35:34Z — feedback — user

THE DECIDING FACT IS THE VALUE POSITION, not the refusal — and it reframes what this
ticket has to settle.

MEASURED: a bare operation name IS a value. `operation apply1(f: (Int64) -> Int64, v:
Int64) -> Int64 = f(v)` called as `apply1(twice, 3)` LOADS, with `twice` alone denoting
the function. 052 OQ2 wants the same for rules — bare `Queen.find` citable as a
`Relation[T]`.

So arity is visible in CALL position and invisible in VALUE position:
    f(x, y)          -- the call site says which arity
    apply1(f, 3)     -- nothing here says which `f`
With `f/1` and `f/2` both declared, the second line has nothing to pick by. That is what
the duplicate-operation refusal means by "a scope maps a name to one symbol": the language
wants a name to denote ONE thing so it can be passed as one.

SO THE FIX IS NOT "ALLOW ARITY OVERLOADING". Allowing it requires one of:
 * TYPE-DIRECTED RESOLUTION in value position — the resolver consults the expected arrow
   type to pick among same-named operations. That is a substantial addition and is exactly
   what "no signature-keyed overloading" says the language does not do; or
 * AN EXPLICIT CITATION FORM — some `f/2`-like spelling at USE sites, not just at
   declarations, so a value position can say which one it means.
Either is bigger than the refusal it would lift, and both should be priced before the
refusal is called a bug.

THE THIRD OPTION IS TO GO THE OTHER WAY: make rules agree with operations rather than the
reverse. Measured cost: of 41 multi-clause predicates over stdlib + anthill-stl +
github-todo, exactly ONE has mixed arity — `Constraint [1, 2]`, the kernel's own
bookkeeping, not user code. And it would make proposal 052's schema coherent: a
`Relation[T]`'s schema IS its row type, the full named tuple of its columns, so a
mixed-arity predicate has NO single schema and cannot be a relation value. That is a live
incoherence today.

AGAINST THAT DIRECTION, honestly: it is worse than Prolog, where `p/1` and `p/2` are simply
different predicates. Here you would have to rename — which is the same "Rename one"
complaint that opened this ticket, now applied to rules as well.

ONE MORE COLLISION EITHER WAY: WI-938's derived relational view of `operation f(x) -> y`
sits at arity 2. So the language ALREADY has one name at two arities as a feature, and
WI-939 item 4 refuses a hand-written clause in that slot for exactly that reason. Any
arity-keyed identity needs a rule saying which `f/2` is meant. And 056's variadic capture
(`...args: R`) plus named arguments mean "arity" needs defining before it can be a key.

CONSEQUENCE FOR PROPOSAL 061 (WI-20260821-FQC85), recorded there: since arity is not part
of identity, the `rule p/2` declaration spelling is dead — it would write down a number
that identifies nothing — and so is the type-ascription spelling, which 060 §2 has already
given a different meaning (a `domain` goal that ENUMERATES over T). What is left is a
keyword or a modifier.


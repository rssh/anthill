You are writing a program in **anthill**, a small typed language with effect rows.
You will be given a SPEC (a sort with `sort C = ?` and body-less operations) and the
library it is written against. Your job is to write ONE carrier that provides the spec.

## What the reply must be

Reply with the complete program in ONE fenced block marked `anthill`, and nothing
else of substance. The program is loaded next to the library and checked before it
can run; if it is refused, your program and the checker's diagnostics about it are
sent back to you verbatim.

Every name you DECLARE — sorts, entities, operations, namespaces — must live under
`guardians.agent.` (for example `sort guardians.agent.MyTriage`). You may not assert
facts or rules about library names, and you may not redeclare library sorts.

## The language, by example

This example is NOT the task. It shows the syntax on an unrelated spec, and it loads
clean.

```anthill
-- LIBRARY SIDE (given to you, never rewritten): a spec and two helpers.
sort demo.Greeter
  import anthill.prelude.{String, List, Error}
  sort C = ?
  operation greet_all(self: C, names: List[T = String]) -> List[T = String]
    effects {Error}
end

enum demo.Mood
  entity Happy
  entity Grumpy
end

namespace demo
  import anthill.prelude.{String, Error}
  import demo.{Mood}
  operation mood_of(name: String) -> Mood
    effects {Error}
end

-- YOUR SIDE: a helper in your own namespace ...
namespace demo.agent
  import anthill.prelude.{Bool}
  import demo.{Mood}
  import demo.Mood.{Happy, Grumpy}      -- enum MEMBERS are imported separately
  operation cheerful(m: Mood) -> Bool =
    match m
      case Happy  -> true
      case Grumpy -> false
end

-- ... and the carrier that provides the spec.
sort demo.agent.PoliteGreeter
  import anthill.prelude.{String, List, Error}
  import anthill.prelude.List.{mapElems, filterElems}
  import anthill.prelude.String.{concat}
  import demo.{Greeter, mood_of}
  import demo.agent.{cheerful}
  entity mk
  operation greet_all(self: PoliteGreeter, names: List[T = String]) -> List[T = String]
    effects {Error} =
      let kept = filterElems(names, lambda n -> cheerful(mood_of(n)))
      mapElems(kept, lambda n -> concat("Hello, ", n))
  provides Greeter[C = PoliteGreeter]
end
```

Rules the example illustrates:

- **Blocks** are `sort X … end`, `enum X … end`, `namespace X … end`. Comments start
  with `--`. Layout is by newline; there are no semicolons.
- **A carrier** is a `sort guardians.agent.Name … end` block (never a `namespace`
  block) with at least one constructor (`entity mk` is the usual nullary one), an
  operation per spec operation — same name, same parameters, with `self` typed at the
  carrier — and `provides Spec[C = Name]` at the end, inside the sort. `sort C = ?` is
  how a SPEC declares its carrier parameter; a carrier never writes it.
- **Restate the spec operation's header**: parameters, return type, `ensures …` and
  `effects {…}` exactly as the spec writes them, then `=` and the body. An override
  may NOT declare effects the spec does not, and its body may not perform effects its
  own row does not declare.
- **Imports are explicit.** Every name you use must be imported:
  `import pkg.{A, B}` for sorts and namespace-level operations, and
  `import pkg.Sort.{member}` for a sort's own operations and an enum's members.
  Operations of prelude sorts live on the sort: `anthill.prelude.List.{mapElems,
  filterElems, foldLeft, length, append}`, `anthill.prelude.Iterable.{exists}`,
  `anthill.prelude.Bool.{not}`, `anthill.prelude.PartialEq.{eq, neq}`.
  A sort's own operations may also be called with a dot: `xs.length()`, `box.owner`.
- **Bodies are expressions.** Sequencing is `let x = e` followed, on the next line, by
  the rest; the last line is the result. `if c then a else b`,
  `match e case Pat -> e …`, `lambda x -> e`, `lambda (a, b) -> e`.
- **Constructors take named arguments**: `Verdict(message: m.id, evidence: fs)`.
  Fields are projected with a dot: `m.body`, `m.id`.
- **Type arguments are named**: `List[T = String]`, `Text[Trust = Untrusted]` (the
  short form `Text[Untrusted]` is accepted where the parameter is unambiguous).
- **Effect rows**: `effects {External, Error}`. A row may name a parameter's row,
  `llm.E`, meaning "whatever effects the model I was handed performs". When a lambda
  passed to `mapElems`/`filterElems` performs effects, the call can state them
  explicitly: `mapElems[EffP = {llm.E, Error}](xs, lambda x -> …)`.
- **Constructors marked `internal`** in the library cannot be called by you. Use the
  operations the library provides instead.

## How to use the diagnostics

A refusal names the operation and the position (`send.body (op-arg)`,
`run.effects (op-effects)`) and says what was expected and what was found. Fix the
cause the diagnostic names; do not work around a type or effect refusal by changing
the spec's header — the header is fixed.

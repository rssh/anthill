## Attributes

- id: WI-20260822-T70A2-a-sort-s-type-parameter-cannot
- created: 2026-08-22T14:33:36Z

- status: Open
- status_agent: user
- status_at: 2026-08-22T14:33:36Z

- acceptance: cargo-test

## Description

A SORT'S TYPE PARAMETER CANNOT BE RESTRICTED TO A SET OF ADMISSIBLE TYPES, so every `S[T]` accepts every `T` and a parameter's declared name is documentation rather than a constraint.

MEASURED. Given

  enum Text
    sort Trust = ?
    entity text(raw: String)
  end

this loads clean:

  operation nonsense(t: Text[Int64]) -> Unit

`Int64` is not a trust level and never could be, but `sort Trust = ?` is unconstrained and admits it. The slot's NAME carries the intent and nothing enforces it.

A `requires` CLAUSE DOES NOT HELP, also measured. Declaring a marker spec and requiring it on the sort --

  sort IsLevel      sort T = ? end
  fact IsLevel[T = Untrusted]
  fact IsLevel[T = Public]

  enum Text
    sort Trust = ?
    requires IsLevel[T = Trust]
    entity text(raw: String)
  end

-- still admits `Text[Int64]`. So the obvious spelling for "this parameter ranges over these types" does not bind.

WHY IT MATTERS, AND WHY IT IS NOT A SECURITY HOLE. examples/guardians puts an information-flow label in a type parameter: `Text[Public]` and `Text[Untrusted]` are different types, and `send_email(body: Text[Public])` is what refuses the article's exfiltration. That works, because a sink demands a LITERAL label and `Text[Int64]` cannot reach it. What does NOT work is the claim one level up -- that the parameter ranges over a LATTICE. It ranges over everything. The lattice is a convention held up by the particular pairings the author happened to write, and a typo (`Text[Publik]`, a sort that exists for another reason) is a fresh type rather than an error.

RELATED, AND NOT THE SAME THING: variance IS declarable (`fact Covariant(sort, param)`, stdlib/anthill/reflect/typing.anthill) and `type_compatible` has a `provides` arm, so ORDERING between labels is expressible today -- a provides-chain of level sorts plus a covariant parameter gives widening in one direction and refuses the other (measured). Ordering the admissible values and CONSTRAINING WHICH VALUES ARE ADMISSIBLE are different questions; this ticket is the second.

WHAT DEPENDS ON IT. examples/guardians/lib/vocabulary.anthill declares `sort Trust = ?` on `Text` and on `Message`, and `lib/llm.anthill` on `Prompt`. The parameter itself is not a workaround -- it is the only way an inner label becomes visible to a signature, and removing it removes the ability to write `Text[Public]` at all. What is a workaround is the `= ?`: those declarations want a BOUNDED parameter and settle for an open one. When this is fixed they should read as the bounded form, and the comment at that declaration cites this ticket so the change is not forgotten.

ACCEPTANCE: `Text[Int64]` against a parameter declared to range over the level sorts is a load error naming the parameter, the offending argument, and what was admissible. CONTROLS: `Text[Public]` and `Text[Untrusted]` still load; the guardians suite still passes, in particular fixtures/agent/rejected/leak.anthill still refused (the label must still be ENFORCED, not merely constrained); and an unbounded `sort T = ?` elsewhere -- List, Option, every prelude sort -- keeps admitting any argument, since the bound must be opt-in.


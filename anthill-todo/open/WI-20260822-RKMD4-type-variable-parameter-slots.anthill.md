## Attributes

- id: WI-20260822-RKMD4-type-variable-parameter-slots
- created: 2026-08-22T09:29:00Z

- status: Open
- status_agent: user
- status_at: 2026-08-22T09:29:00Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TYPE-VARIABLE PARAMETER SLOTS DO NOT REJECT A WRONG-SORT ARGUMENT -- and the silent pass LAUNDERS the variable. An argument whose SORT differs from a parameter type CONTAINING A TYPE VARIABLE is accepted with no diagnostic, and the variable is left UNBOUND rather than the call being rejected.

MEASURED (docs/measurements/guardians/nest4.anthill, and nest3 for the container case):

  operation fetch_one() -> Message[Trust = Untrusted]
  operation sum_flat(m: Text[Trust = ?t]) -> Text[Trust = ?t]
  operation sink(body: Text[Trust = Public]) -> Unit
  operation leak() -> Unit = sink(sum_flat(fetch_one()))

LOADS CLEAN. `Message` where `Text` is expected raises nothing; `?t` is never bound; it then binds to `Public` at the sink and the call is accepted.

TWO CONTROLS PIN IT, and they are what make this a narrow claim rather than 'the typer does not check arguments'. (a) GROUND-vs-GROUND IS checked: `send_email(to: 42)` gives `type mismatch in send_email.to (op-arg): expected Address, got Int64`, and the same shape catches `Text[Trust=Untrusted]` against `Text[Trust=Public]`. (b) NESTING IS NOT THE CAUSE: `List[T = Text[Trust = Untrusted]]` passed into `List[T = Text[Trust = ?t]]` propagates correctly and the sink refuses it (nest2). The variable is the cause.

WHY THIS IS WORSE THAN A TYPICAL MISSED ERROR. A free variable is not a neutral outcome -- it is the MAXIMALLY PERMISSIVE one, because the consumer instantiates it to whatever it wants. So the failure mode is not 'a wrong program is accepted', it is 'the constraint the variable was carrying is discarded'. Where the variable carries an information-flow label (examples/guardians: `Text[Trust = ?t]`), that is LAUNDERING, and it silently defeats the property the signature exists to enforce.

HOW IT WAS FOUND, AND WHY NO EXISTING TEST SEES IT. examples/guardians/vocabulary.anthill was written out to answer 'where are these definitions?'. The first agent written against it -- `send_email(body: summarize(fetch_mail(box)))`, the OBVIOUS spelling -- loaded clean and exfiltrated. The measurement suite had never caught it because every probe used ONE sort throughout: a vocabulary of one sort cannot exercise a sort mismatch. Any test written the same way is blind to this.

MITIGATION IN PLACE, NOT A FIX. examples/guardians works around it with an explicit `bodies_of(List[Message[?t]]) -> List[Text[?t]]` projection, so every label-polymorphic operation is reachable only through arguments of exactly its declared sort. That is discipline in the TRUSTED declarations; the typer should reject the mismatch.

WHERE. The op-arg conformance check in rustland/anthill-core/src/kb/typing.rs -- the site that emits `type mismatch in <op>.<param> (op-arg): expected .., got ..`. Expected shape of the fix: a parameter type containing a variable must still require the argument's HEAD CONSTRUCTOR to match; only the variable-occupied slots are free. Whether the current code skips the whole comparison or fails to propagate the mismatch outward is the first thing to establish.

ACCEPTANCE: nest3/nest4 above are refused, with the two controls still passing -- ground-vs-ground still refused, and the nest2 container case still PROPAGATING (not newly refused). Recorded as C7 in examples/guardians/docs/design/measured.md.


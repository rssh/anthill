## Attributes

- id: WI-20260829-4MHED-parse-parity-scaland-refuses
- created: 2026-08-29T23:57:55Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T23:57:55Z

- acceptance: cargo-test, scaland-sbt-test

## Description

PARSE PARITY: scaland REFUSES the companion-receiver type-arg bracket that rustland accepts, and kernel-language.md now states the rustland behaviour as the rule.

FILED BECAUSE A SPEC RULE HAS ONE CONFORMING IMPLEMENTATION AND ONE REFUSING ONE, recorded until now only in a source comment (found by /code-review on WI-20260829-BAD3V).

WI-20260829-BAD3V made `Map[K = String, V = Int64].empty[T = Int64]()` parse and read the
outer bracket as the call's type arguments, and kernel-language.md §"the bracket is read in
exactly two positions" now says it "means what `Map.empty[T = Int64]()` means". Scaland's
`refuseDotTypeArgs` rejects it.

WHY, and it is NOT the refusal that is wrong: rustland's CST distinguishes a `field_access`
whose object is an `application` (a QUALIFIED companion receiver) from one whose object is a
value, so `push_fn_term` can route the two differently. Scaland collapses a call and an
instantiation to the same `Term.Fn` shape, so `isValueReceiver` reads `Name[B].field` as a
VALUE — a divergence its own doc comment has recorded since WI-278 as affecting "only that
edge form, which no loaded stdlib uses". BAD3V is what makes it load-bearing: one side now
has a capability across it.

MEASURED at the time of filing: 0 occurrences of the companion-with-bracket spelling in
stdlib/ and examples/, so nothing is broken today. The exposure is a `.anthill` file that
adopts the new spelling and then fails to parse under scaland.

THE FIX IS IN `NameSuffix`, NOT IN THE REFUSAL: scaland must be able to tell an
instantiation `Fn` from a call `Fn` — `fnOrInstOrIdent` builds both through
`terms.allocAt(Term.Fn(...))` and keeps nothing that separates them. Options are a distinct
term shape for an instantiation, or a side-table of instantiation-built TermIds that
`isValueReceiver` consults. Note this ALSO closes the older WI-278 divergence, which is the
argument for doing it properly rather than special-casing the bracket.

ACCEPTANCE: `Map[K = String, V = Int64].empty[T = Int64]()` parses in scaland and produces
the same functor + `type_args` shape rustland's
`a_companion_receiver_call_reads_its_bracket_as_type_arguments` asserts; the bracket-less
`Map[K = …].empty()` keeps working (control, passes either way); `isValueReceiver`'s WI-278
note is updated or deleted depending on whether the divergence it describes survives; and a
shared parser-parity corpus case is added under testdata/parser-parity/wi777/accept, which
is the mechanism that would have caught this.


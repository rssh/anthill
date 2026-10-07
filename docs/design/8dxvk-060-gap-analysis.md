# 8DXVK: implementation gaps against proposal 060

Investigation and implementation, 2026-10-07. No replacement proposal.

Proposal 060 §3 already gives a typed-head anchor for `require[Spec[T]]`,
including a named dictionary. The existing QMFC5 suite executes a
multi-parameter requirement and consumes its dictionary in a nullary operation,
returning the provider-specific value 7. The instance-bearing dictionary channel
works; rejection of a WI-582 introducer spelling does not establish otherwise.

## Repaired gaps

The introducer recognizer accepted only `Spec[A]` and stored only the spec
symbol. It now normalizes positional and named arguments against the declaration
and retains the written instance. The annotated value supplies the carrier;
sibling bindings and alias-fixed bindings remain in its requirement. Applying
that introduced bound preserves those bindings too. Invalid labels, excess
arguments, non-carrier members and overwriting an alias binding are load errors.

Both head-annotation spellings accept `IntTagger.C` through
`sort IntTagger = Tagger[Out = Int64]`, retaining `Out = Int64` rather than
refusing the alias or dropping its restriction. Executable tests distinguish
providers at different `Out` values and consume the selected dictionary through
060's existing `require[...]` channel and a nullary operation.

Source query `domain` now applies the same type-position validation as a rule
or constraint. A parameter-carried spec is diagnosed even with an unbound value
or under negation. Qualified sort operands are converted to sort values, so a
dotted spelling cannot evade that check. Generated annotation guards keep their
provider-requirement interpretation.

## Retained boundaries

No new carrier-classification rule is introduced. A sole parameter is not
necessarily the carrier: existing member-free `DataProvider[K]` binds `K` to
`String` while its values are `DataProvider` values. Inferring the carrier from
parameter count broke existing tests and was withdrawn. The user agreed to
retain existing classification while fixing the implementation gaps.

The stored requirement now carries the instance, but existing nominal-bound
readers and `spec_as_its_providers` remain. This change does not claim to replace
that internal representation or implement independent unbounded rule type
variables. Design 060-implementation §8.7 already records that the polymorphic
anchor example needs a bounding guard. Removing that dependence is separate
from preserving the instance through the supported guard and dictionary path.

## Verification

`wi_8dxvk_rule_requirements_test` executes provider filtering, alias members,
application of introduced bounds, dictionary-selected operations and query
validation. Its operation-free Marker case is a compatibility control. The
updated WI-582 alias-member test executes the previously refused spelling.
Final test and back-out counts are recorded in the work item's feedback.

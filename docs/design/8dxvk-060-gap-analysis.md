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
dotted spelling cannot evade that check. Generated annotation guards read actual
carrier type variables; provider requirements are separate dictionary reads.

## Retained boundaries

No new carrier-classification rule is introduced. A sole parameter is not
necessarily the carrier: existing member-free `DataProvider[K]` binds `K` to
`String` while its values are `DataProvider` values. Inferring the carrier from
parameter count broke existing tests and was withdrawn. The user agreed to
retain existing classification while fixing the implementation gaps.

## Carrier and dictionary representation

Following the agreed representation change, `RuleEntry.type_bounds` stores the
actual carrier type expression. An introduced `A` is one real clause variable,
shared across its annotated columns. Member sugar introduces an anonymous carrier
for each annotation. Neither stores the spec instance as the value's nominal type.

`RuleProviderRequirement` separately records the carrier type slot, complete spec
instance, and dictionary slot. All three channels close against the same clause
frame. Companion type variables and dictionary variables belong to that frame
from assertion, so activations and citations open them together.

Relational clauses receive generated type-based `find_dictionary` reads. Covered
calls carry the dictionary slot. A rigid caller's citation instantiates the clause's
type slots from its columns and routes the full instance through the existing
requirement channel. The caller's rigid type is never rebound. Written dictionary
calls retain their explicit selection.

A directional rewrite keeps an empty body. Its match-time check extends the match
with carrier types and dictionary values before instantiating the woven RHS.
Both occurrence and term redexes preserve that dictionary call; the term form uses
the existing reflect encoding of `apply_within`. Evaluation accepts the ordinary,
structurally validated dictionary Value spliced into the RHS.

Rule-bound and citation comparisons use ordinary type compatibility, with explicit
obligations attached to the carrier variable. Their `spec_as_its_providers` mode
was removed. Uses of that mode for permission/effect capabilities are independent
and remain. Independent unbounded rule type introducers are still outside this
change; design 060-implementation §8.7 requires a bounding guard.

## Verification

`wi_8dxvk_rule_requirements_test` executes provider filtering, alias members,
application of introduced bounds, dictionary-selected operations and query
validation. Its operation-free Marker case is a compatibility control. The
updated WI-582 alias-member test executes the previously refused spelling.
Final test and back-out counts are recorded in the work item's feedback.

The representation suite drives shared carrier identity, independent anonymous
carriers, dictionary dispatch without an authored `require`, a rigid caller's
selected rival, and rewrite RHS execution on both carriers. The focused suite and
back-out measurement are recorded below after validation.

Measured on 2026-10-07: the temporary focused binary passed all 74 tests with the
change (`test-run-20261007-211637.log`). Against ef6a3b09 it passed 69 and failed
5 (`test-run-20261007-211718.log`): shared carrier identity admitted the mixed
row; automatic dispatch and rewrite RHS used default 1; the rigid caller was
refused; the WI-582 inspection still found a nominal spec bound. The independent
member control passed in both runs. The new suite is registered in `wi_tests`;
the temporary binary was removed before the workspace gate.

The expanded focused suite passed all 128 tests on 2026-10-08
(`test-run-20261008-061623.log`). Its rigid-caller test covers both a fully
specified callee requirement and a partial one, including a selected provider
whose omitted companion differs from the carrier's default provider. Citation
conformance retains the original carrier obligation after type substitution;
written composed carrier restrictions compare the actual type constructor.
Authored requirement brackets refer to the actual carrier variable. The expanded
temporary binary was removed before the final workspace gate.

Final gate: `rustland/scripts/test.sh` exited 0 with 8,762 passed, 0 failed,
14 ignored across 36 targets (`test-run-20261008-061804.log`). Scala
`sbt testFull` passed all 600 tests. Manual diff review completed; the
`/code-review` skill was unavailable.

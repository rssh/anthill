## Attributes

- id: WI-20260829-XZMGC-typing-a-composed-provision
- created: 2026-08-29T22:44:19Z

- status: Delivered
- status_agent: claude
- status_at: 2026-08-30T08:47:47Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TYPING: a COMPOSED provision view keeps the intermediate's SELF-REFERENCE as the spec's carrier param, so a transitively-provided carrier is refused at a spec view that names its own carrier.

SPLIT OUT OF WI-20260829-GNPG7, which settled the design question and closed the transitivity half. GNPG7's fix routed both subtype sites through `transitive_provider_spec_view_bindings`, so a 2-hop carrier now composes its provider view. Four of that ticket's five rows moved. THIS is the fifth.

MEASURED (arg `rs: List[T = Row]`, all after GNPG7):

  operation ti(c: Iterable[Element = Row])           LOADS   -- Element composes
  operation ti(c: Iterable[Element = Row, E = {}])   LOADS   -- E composes too
  operation ti(c: Iterable[C = List[T = Row],
                           Element = Row, E = {}])   REFUSED -- only C fails

  refusal: type mismatch in ti.c (op-arg): expected Iterable[C = List[T = Row],
           Element = Row, E = {empty_row}], got List[T = Row]

  CONTROL, one hop: `MutableStack[T = Row]` against
  `Iterable[C = MutableStack[T = Row], Element = Row, E = {}]` LOADS -- a DIRECT
  provision binds C to its own carrier, so the fully-bound view is admissible when no
  composition is involved. Both are in
  `typer_capability_matrix_test::a_spec_typed_parameter_and_its_carrier`.

THE MECHANISM. `Stream provides Iterable[C = Stream, Element = T, E = E]` binds C to
STREAM ITSELF. `compose_provision_views` substitutes values that are type-param refs OF
THE INTERMEDIATE (`Stream.T` -> `List.T`, `Stream.E` -> `{}`) and keeps everything else
verbatim -- its own doc names this exact case: "a value not referencing an intermediate
param (the carrier application `C |-> Stream`) is kept verbatim". So the composed view for
`List` says `C = Stream` where it should say `C = List`. `Iterable.C` declares no variance,
so the check is INVARIANT and `Stream` vs `List[T = Row]` fails both directions.

WHY `C = List` IS THE RIGHT ANSWER, not just the one that makes the row load: `C` is the
carrier `Iterable.iterator(c: C)` receives, and `iterator` on a List receives the LIST.
`C = Stream` is an artifact of the intermediate's self-naming, not a claim anyone makes.
Note the bare form suffices -- `C = List` against an expected `C = List[T = Row]` is the
(sort_ref, parameterized) arm on one base, which is compatible both directions.

WHY IT WAS NOT DONE INLINE IN GNPG7 -- two routes, neither a small edit:

  (a) SUBSTITUTE IN THE COMPOSER. `compose_provision_views` would emit a bare `Ref` to the
      carrier, which needs `kb.alloc` and therefore `&mut KnowledgeBase`. It and both its
      walkers (`transitive_provider_spec_view_bindings`, `transitive_provision_view`) take
      `&KnowledgeBase`, and TWO of the three call sites are themselves immutable --
      `carrier_param_receiver` and `bind_spec_params_from_carrier` (`bare_spec_arg_provision_projection`
      is the only `&mut` one). So this is a mutability cascade through the typer's read
      paths, reaching three consumers that do NOT read `C` and for which the verbatim
      value is currently correct.
  (b) SUBSTITUTE AT THE SUBTYPE SITE, where `&mut kb` is already in hand
      (`parameterized_compatible_view` allocs `actual_base_ty` two lines up). It would have
      to RECOGNIZE the self-reference without the composer's help -- e.g. "an actual-side
      value that is a bare ref to a sort the actual provides" -- which has a stated misfire:
      a provision that legitimately binds a param to a spec sort the carrier also provides
      (`X provides S[P = Iterable]` where X provides Iterable) would be rewritten wrongly.
      Not shipped without a way to tell the two apart.

WHETHER THE COMPOSER SHOULD CHANGE AT ALL IS THE REAL QUESTION, and it is why this is a
ticket rather than a patch: the verbatim behaviour is DOCUMENTED as deliberate and is
correct for the three consumers that ground spec params off a receiver. Only the subtype
relation compares `C`. So the choice is between changing the shared composer for everyone
(and re-justifying its doc) or giving the subtype relation its own composition. Deciding
that needs the WI-380 deep-compound follow-up in view too -- the same function already
defers compound substitution (`Element = Pair[A = Stream.T]` is kept verbatim and surfaces
a loud `?_`), and a self-reference rule and a compound rule are plausibly one increment.

ACCEPTANCE: `Iterable[C = List[T = Row], Element = Row, E = {}]` admits a `List[T = Row]`;
the MutableStack one-hop rows and the `Element`/`E` rows stay green (they pass either way --
say so at the site); the three non-subtype consumers of `compose_provision_views` are named
with what each does with a `C` binding, and whichever route is taken says why the other was
not. Update `a_spec_typed_parameter_and_its_carrier`'s row and its doc, which names this
ticket.

## Changes

### 2026-08-30T08:47:42Z — feedback — user

DELIVERED. The carrier parameter of a COMPOSED provision view is now the ACTUAL, not the
intermediate -- and the ticket's defect had a SECOND HALF nothing had named.

BOTH SIGNS WERE LIVE. The filed half: `ti(c: Iterable[C = List[T = Row], ...])` REFUSED a
`List[T = Row]`. The other half, found by asking the same question from the accepting side:
`ti(c: Iterable[C = Stream])` ACCEPTED that same `List`, because the composed view literally
said its carrier was a `Stream`. A silent accept, at BOTH subtype sites. Measured:

  Iterable[C = List[T = Row], Element = Row, E = {}]   REFUSED -> LOADS   (the ticket's row)
  Iterable[C = List[T = Row]]                          REFUSED -> LOADS
  Iterable[C = List]                                   REFUSED -> LOADS
  Iterable[C = Stream]                                 LOADS   -> REFUSED (the silent half)
  Iterable[C = List[T = Bool]]                         REFUSED -> REFUSED (strength control)
  Element / E rows, every MutableStack row              unchanged

THE CENSUS THE TICKET ASKED FOR SETTLES ITS QUESTION. `compose_provision_views` is
UNCHANGED, because not one of its three consumers reads the composed `C`:

  * bind_spec_params_from_carrier (WI-357/714) -- DROPS it. `Stream` is a ref shape naming
    no parameter of `List`, so `concrete` is None. A correct `List` would be dropped too.
  * carrier_param_receiver -> bind_spec_params_from_carrier_param (WI-424/593) -- SKIPS it
    by VarId, by design: `C` binds by argument unification, not by the provision.
  * bare_spec_arg_provision_projection (WI-20260828-BH1JZ) -- SKIPS it by VarId and
    substitutes THE RECEIVER'S OWN TYPE. Its comment is a MEASUREMENT of this same artifact
    escaping into `MappedStream[Source = Stream, ...]`, and its conclusion -- "the spec's
    CARRIER parameter is the receiver's own type, by definition, and must not be read off
    the provision" -- is the rule applied here at the fourth consumer.

So route (a) would be a mutability cascade through paths that discard the value. Route (b)
was declined for the reason the ticket gives: recognizing the artifact from the composed
view alone ("a bare ref to a sort the actual provides") cannot tell it from a legitimate
binding. A THIRD route needs no such recognition: split on the BRANCH. `subtype_provider_view`
-- the subtype relation's own entry point, which WI-20260829-GNPG7 created for exactly this
reason -- excludes the carrier param from a COMPOSED view and reports that it did; each of
its two callers supplies the actual it holds. The DIRECT branch is untouched.

WHY THE ACTUAL AND NOT A BARE `Ref(carrier)`, which `subtype_provider_view` could have
emitted with no caller change: MEASURED, that opens a hole one hop does not have.
`MutableStack[T = Row]` is REFUSED at `Iterable[C = MutableStack[T = Bool]]`; a bare
`C |-> List` would ACCEPT `Iterable[C = List[T = Bool]]` for a `List[T = Row]`, since
(sort_ref, parameterized) on one base is compatible both directions. That variant reddens
exactly ONE test, which is why that test exists.

TWO /code-review PASSES, THREE FINDINGS, ALL REPRODUCED, AND THE HIGH ONE WAS A REAL
REGRESSION I SHIPPED TWICE -- the same gate, too wide, in two different ways:

  * CUT 1 keyed the exclusion on `spec_carrier_param` ALONE. That predicate answers "the
    first declared type parameter some declared operation TAKES", which by the language's
    own rule (WI-1077) reads an ACCEPTED ARGUMENT as the carrier: `touch(c: Spec, x: P)`
    files at `P`, the ELEMENT. So a correct composed `P` was dropped and the actual's whole
    type substituted -- `Carrier[T = Int64]` REFUSED at `Spec[P = Int64]`, a program that
    loads on main. I had DESIGNED a second gate on the value and then not implemented it.
  * CUT 2 added "the value's sort self-provides the spec at this param" -- still too wide,
    because that is true of ANY self-providing sort (`Int64 provides Combiner[T = Int64]` is
    the ordinary shape). DRIVEN, both signs: with `Elem provides Spec[P = Elem]`,
    `Spec[P = Elem]` was REFUSED for a 2-hop `Carrier` and `Spec[P = Carrier]` ACCEPTED,
    while the ONE-HOP `Mid` answered the opposite to both. The composed path contradicting
    the direct path -- this ticket's own defect, relocated onto element parameters.
    Cut 1's fixture stayed GREEN through this, because its `P` is `Int64`, which provides no
    `Spec`. Two fixtures, two review passes, and neither could have found the other's rung.
  * THE GATE IS NOW IDENTITY against the chain's OWN self-naming sort, resolved once by
    `transitive_carrier_for_param` -- the walk that already answers "who owns this spec's
    implementation on this chain". Both element fixtures are kept, and the back-out ladder
    is recorded at the test: absent gate reddens both, wide gate reddens only the second.
  * LOW, and the code was right while the comment was not: at the bare site the value is
    `Ref(carrier)` -- where the entity->parent climb STOPPED -- not `Ref(actual_sym)`.
    `Iterable.C` declares no variance so the check is INVARIANT and no one value satisfies
    both spellings; the DIRECT provision decides, and it accepts a `boxed` at
    `Iterable[C = DBox]` and refuses `Iterable[C = DBox.boxed]`. An earlier draft claimed
    the two SITES agree there; they do not -- `parameterized_compatible_view` has no
    entity->parent climb, so it refuses every carrier spelling for a parameterized entity
    actual, with this change and with it backed out. Pre-existing, and said so.

SPEC: kernel-language.md carried "a spec type carrying BINDINGS is a distinct view", which
is the reading GNPG7 refuted and this ticket extends past. Corrected: that sentence is the
SCOPE of N01PY's witness widening, not a claim about spec views, and two paragraphs now
state what the language does -- a bound spec view is admissible wherever the provision
supplies it, reached through a chain or not, and in a composed view the carrier parameter is
the value's own type.

CONTROLS, said plainly: every MutableStack row and every one-hop row is GREEN EITHER WAY, by
design -- a direct provision never reaches the composed branch. That is what makes the
`List` rows attributable to composition rather than to the carrier parameter having been
given a new meaning everywhere.

TESTS: rustland 36 binaries / 6161 passed / 0 failed (doc-tests included); scaland 524 / 0.
New file `wi_xzmgc_composed_carrier_param_test.rs` (9 tests). Capability-matrix cell flipped
and given the `C = Stream` and wrong-argument rows plus a one-hop strength control;
`wi_gnpg7`'s boundary marker flipped to LOADS and kept, so backing GNPG7 out still reddens it.


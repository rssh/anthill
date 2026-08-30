## Attributes

- id: WI-20260829-XZMGC-typing-a-composed-provision
- created: 2026-08-29T22:44:19Z

- status: Open
- status_agent: user
- status_at: 2026-08-29T22:44:19Z

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


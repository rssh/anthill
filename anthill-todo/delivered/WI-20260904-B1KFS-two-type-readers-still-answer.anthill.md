## Attributes

- id: WI-20260904-B1KFS-two-type-readers-still-answer
- created: 2026-09-04T03:17:36Z

- status: Delivered
- status_agent: user
- status_at: 2026-09-04T05:57:32Z

- acceptance: cargo-test, scaland-sbt-test

## Description

TWO TYPE READERS STILL ANSWER ONE TYPE DIFFERENTLY ON A `Value::Entity` THAN ON ITS `Term` TWIN.

THE INVARIANT: carrier-neutral means `Fn{Map, K = Bool}` and its `Value::Entity` twin cannot
have different outputs. `KnowledgeBase::fn_value` builds the Entity for ANY application with
a non-leaf child, so a type carrying an occurrence child IS an Entity -- which is exactly what
`KnowledgeBase::reify` hands back for such a type. This is not exotic: it is the shape
WI-20260903-H054K's natural repair produced, and it reported ZERO errors on a wrong program
because of it.

ALREADY FIXED, and the pattern to copy: `resolved_type_is_ground_g` had `_ => false` for every
non-Term/non-Node carrier, which at its callers means SKIP THE CHECK. It now reads every
carrier but `Value::Node` through ONE `TermView` walk (`type_view_is_ground_g`), and
`type_value_is_ground_g` is a thin delegate to it, so the TermId and Value readings cannot
drift again. The `Value::Node` arm is deliberately kept: three of its judgments are
type-specific rather than structural (a `denoted`'s CLOSEDNESS per WI-470, a `PolyType` being a
schema per WI-1083, a guarded effect atom whose GUARD is not read per WI-478).

STILL DISAGREEING, both MEASURED:

 1. `typing::type_display_name_value`. `Map[K = Bool]` renders `"Map[K = Bool]"` on the Term
    carrier and `"Map"` on the Entity carrier -- the bindings SILENTLY DROPPED from a
    user-facing type error, which is the shape of message that sends an author to the wrong
    place. The file already STATES the agreement contract, on its own `Value::Node` arm:
    "render a `Value::Node` label to the SAME string `type_display_name` produces for the
    equivalent term ... the two must agree". The Entity arm exempts itself from the rule its
    neighbour is written to.

 2. `typing::walk_type_deep_value_g`'s `other => other.clone()`. An Entity-carried type's inner
    vars are NEVER sigma-resolved. The WI-441 comment one line above it records this EXACT
    mistake having been made and fixed for `Value::Node` -- "the old `Nodes carry Refs, not
    type-param vars` assumption left those un-walked, so the rigidify pass missed them (the
    body then unified/leaked the raw Global)". The Entity carrier is the un-fixed twin of a
    bug this codebase has already paid for once.

WHY A TICKET AND NOT INLINE. (1) is not an arm: it is merging `type_display_name` (~180 lines,
nine special meta-ctor arms -- Arrow, TypeVar, NamedTuple, Nothing, ExprCarried,
RigidTypeProjection, Denoted, EffectsRows) with its hand-kept twin `type_display_name_occ` into
one `TermView` walk. That function produces EVERY type-error string in the system, so the blast
radius is the message corpus and it needs its own measurement pass. A partial fix is worse than
none here: making the generic application agree while Arrow-as-an-Entity still renders "Arrow"
leaves a disagreement that is harder to see than the current one.

LATENT, NOT LIVE, AND SAY SO. Censused with a probe the test harness cannot capture (an
`eprintln` at these sites reads ZERO because libtest swallows a test's stderr): **0**
`Value::Entity`s reach the groundness gate across 36 binaries and 6 376 tests. So no existing
row moves and no `.anthill` fixture can drive either site today. The driver is the
carrier-agreement PROPERTY itself, asserted directly -- see
`typing::tests::groundness_gate_carrier_agreement_test`, which builds one type on both carriers
and asserts one answer, with a ground/non-ground control pair so the agreement cannot be bought
by the predicate answering the same thing to everything.

ACCEPTANCE. The same type built on both carriers renders to the same string and sigma-walks to
the same result, with the ground/non-ground control pair. Say which rows fail when the change is
backed out, and which pass either way by design.

## Changes

DONE. Both readers go through ONE `TermView` walk, so a type has one name and one
σ-answer on whatever carrier it rides.

WHAT LANDED.

 1. `typing::type_display_name_view` — the merged walk. `type_display_name` (the nine
    meta-ctor arms), `type_display_name_value` and `type_display_name_occ` are thin faces
    on it, and `type_child_display_name` routes through the same pair. The TERM carrier
    gained the occurrence renderer's arms it never had (effect atoms and the ROW they
    fold into, `dot_apply` as `r.n`, `Term::Ident` as its name instead of
    `format!("{:?}")`'s `TermId(8960)`); the generic arm shows POSITIONAL args, which the
    term renderer silently dropped. `denoted_value_display` and `extract_ref_field` are
    gone — the walk subsumes both — and `effect_atom_display` is now the display itself.

 2. `walk_type_deep_value_g` — `Value::Entity`, `Value::Tuple` and a `Value::Var` child
    all resolve. Was `other => other.clone()`.

 3. `typing::effect_atom_order_key`, forced by (1): `type_display_name` was ALSO
    `build_canonical_effects_rows`' canonical SORT KEY, and once an atom displays as its
    label two distinct atoms can share a string. `sort_by_cached_key` is stable, so a
    shared key leaves order to INPUT order and two rows written in opposite orders stop
    hash-consing to one term. One name had become two questions.

TWO ARMS KEYED ON THE QUALIFIED NAME, not the local one: `EffectExpression.*` and
`dot_apply`. `guarded`, `merge` and `open` each name a SECOND, unrelated stdlib
constructor (`LogicalQuery.guarded`, `SortedSet.merge`), and local keying would render
those `"?"`. The capitalized `TypeExtractor` arms keep local keying — no homonym, and
that was already their rule.

ONE OCCURRENCE-ONLY ARM KEPT, for the reason part 1 kept its own: a `Parameterized` whose
head the shared view answers `Opaque` for (`parameterized_base_functor` finds no symbol —
a `TypeChild::Node` base OR a `Ground` base that is not a bare `Ref`/`Ident`) would render
`?`, dropping base and bindings. It fires on the HEAD, not on a spelling of the base.

MEASUREMENT — SIX AXES, SIX SEPARATE BACK-OUTS, each failing only its own rows.

 * display fallback (`other => resolved_functor_name`) → `type_reader_carrier_agreement_test::`
   `a_generic_application_shows_its_bindings_on_either_carrier` (entity renders `"Map"`)
   and `::an_arrow_is_an_arrow_on_either_carrier` (renders `"Arrow"` — the case the ticket
   names).
 * σ-walk Entity/Tuple arms → `::an_entity_carried_types_inner_var_is_resolved`.
 * σ-walk `Value::Var` arm → `::a_value_var_child_of_an_entity_is_resolved` ONLY; the row
   above passes, because its var rides as `Value::term(Term::Var(..))`. Two spellings of
   "a variable in a child slot", and the first repair reached one.
 * sort key ← `type_display_name` → `typing_test::two_atoms_sharing_a_display_still_canonicalize_to_one_row`.
 * `absent` without its `-` → `typing_test::a_canonical_effect_row_renders_as_a_row`'s
   absence assertion.
 * `merge` joining unconditionally → the same test's trailing-separator assertion.

PASS EITHER WAY BY DESIGN, and each is why its neighbour measures something:
`::a_bare_sort_reference_agrees_either_way` (no bindings to drop), `::a_ground_type_walks_to_itself_on_either_carrier`
(no var to resolve), `typing_test::arrow_effects_canonical_form_hash_cons_stable` (two
atoms with DISTINCT labels never shared a key), and the `{}` assertion in the row test (an
empty row has no atom to lose — which is exactly why the five refusal assertions this
ticket updated, ALL of them on `E = {}`, caught neither row defect).

THE σ-WALK ROWS ASSERT STRUCTURALLY (`views_structurally_equal`), NOT THROUGH THE DISPLAY.
Reading their verdict off `type_display_name_value` made them fail under the DISPLAY
back-out — one fixture measuring its neighbour's defect, and two axes that could no longer
be told apart. Caught by running the back-out, not by inspection.

`/code-review high` FOUND SEVEN, and five were real and are fixed above: the row rendering
(it printed `{External, }` for BOTH `{External}` and `{-External}`, tripping the
identical-rendering backstop for the one difference the message exists to show), the
`Value::Var` child, the too-narrow occurrence guard, `NamedTuple` silently dropping a
malformed field (now `?: ?`, as the term renderer had it), and the local-name collisions.
Its finding 3 was right that "byte-for-byte the old key" was FALSE — children render
through the new walk — and the doc now claims only what the sort needs: injective and
deterministic. Its finding 5 (a `Term::ParseAux` panicking in a diagnostic) is NOT
reachable: the loader strips `ParseAux` before allocation (`kb/term.rs`), so no KB term
can carry it.

REGRESSION CAUGHT BY THE SUITE, not by review: moving `dot_apply` to qualified keying
dropped its arm, and `Modify[T = c.contents]` printed
`Modify[T = dot_apply[receiver = c, name = contents, args = nil]]`.
`parse_test::compound_value_path_undeclared_effect_is_named` and
`wi400_body_projection_test::abstract_projection_distinct_receivers_rejected` are that
arm's control — both fail without it.

CORPUS. 5 refusal assertions moved, all one rendering: an empty effect row prints the
surface `{}` instead of leaking the ctor name `{empty_row}` (WI-1059 ×2, WI-1061 ×2,
WI-1063; plus a comment in WI-1076). The occurrence carrier already printed `{}`. Nothing
else moved.

RUST: 36 binaries, 6393 passed, 0 failed (baseline 6385 + the 8 rows above).
SCALA: 539 passed, 0 failed — untouched; scaland has no typing package, so there is
nothing here to port.

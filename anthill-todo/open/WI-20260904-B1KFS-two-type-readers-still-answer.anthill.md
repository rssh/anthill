## Attributes

- id: WI-20260904-B1KFS-two-type-readers-still-answer
- created: 2026-09-04T03:17:36Z

- status: Open
- status_agent: user
- status_at: 2026-09-04T03:17:36Z

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


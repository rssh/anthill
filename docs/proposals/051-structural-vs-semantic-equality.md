# Proposal 051: Structural vs. semantic equality — un-parking `===`

**Status:** Draft
**Depends on:** [049-equality-and-unification](049-equality-and-unification.md)
**Related:** WI-300 (rule-body requirement goals), [043-simp-rewrite](043-simp-rewrite.md), [design/requirement-dictionaries](../design/requirement-dictionaries.md)
**Affects:** `rustland/anthill-core/src/kb/{resolve,load,mod}.rs`, `tree-sitter-anthill/grammar.js`, `scaland/.../parse`, `stdlib/anthill/prelude/*`, `docs/kernel-language.md`

## Motivation

Proposal 049 drew the equality concept map on two axes — **structural** (compare raw
structure) vs **semantic** (dispatch to a carrier), and **test** vs **bind** — and named
four cells:

|                | test (no binding)  | bind (unify) |
|----------------|--------------------|--------------|
| **structural** | `===` *(parked)*   | `<=>` unify  |
| **semantic**   | `=` / `eq`         | E-unification *(engine)* |

049 delivered `<=>` (unify) and kept `=` a pure test, but **parked** `===` and left the
resolver's structural shortcut in place, under an explicit Invariant:

> `=` is semantic and may someday dispatch (today a structural shortcut, valid **while
> every carrier's equality is structural**).

with a stated trigger for revisiting: *"the first semantic-equality carrier."* 049 judged
that *"None exists."*

**One now exists — and it is in the prelude.** `Set` is a non-structural-equality carrier:
`set.anthill:25` makes insertion commutative,

```anthill
rule insert(insert(?s, ?x), ?y) <=> insert(insert(?s, ?y), ?x)   -- commutative (NOT [simp]: would loop)
```

so `insert(insert(empty, 1), 2)` and `insert(insert(empty, 2), 1)` denote the **same set**
but are **structurally distinct terms**. Any `Eq[Set]` (or `Eq[Map]`) is therefore
membership-based, *not* structural — the moment a program compares two sets for equality
via `=`/`eq`, the resolver's structural shortcut (`builtin_eq` → `views_structurally_equal`,
wired at `mod.rs:4171`) returns the **wrong answer**. The shortcut is a latent soundness
gap, exactly as 049 predicted its expiry.

Two further pressures make the split worth surfacing now rather than at first-bug:

- **WI-300 makes the conflation visible.** A rule-body `requires(Eq[T]), eq(?x, ?y)`
  guard (WI-300) asserts "T has an `Eq` instance," but under the structural shortcut the
  body `eq` runs structurally **regardless of whether the instance exists or what it
  says** — the guard is operationally vacuous and, for a custom instance, actively
  dishonest. WI-300's guard tier lands independently, but its *semantics* are only honest
  once `eq` genuinely means the instance's equality.
- **Users want custom equality.** Case-insensitive `String`, normalized rationals,
  eq-mod-n — all are `Eq` instances that differ from structure. There is today **no way to
  express "compare these two values *structurally*, ignoring any instance,"** which is a
  distinct and legitimate need (reflection, term/symbol identity, debugging).

This proposal un-parks `===` and sets `=`/`eq` on the path to genuine dispatch.

## Design

### `===` ≜ structural identity test (un-parked)

`===` is a resolver builtin: the carrier-agnostic, always-available structural comparison
that `builtin_eq` **already is** today (`views_structurally_equal`, WI-486 — the one
structural `Value` comparator; opaque carriers `Cell`/`Requirement`/closures compare by
handle identity). It needs **no `Eq` instance**, dispatches nothing, and is defined for
every value. It is the honest name for "are these two values literally the same structure."

```anthill
namespace anthill.kernel
  operation ===(a: T, b: T) -> Bool   -- structural identity; resolver-implemented; never dispatches
end
```

Implementation is a **relabel, not new behaviour**: register the `===` symbol to the
existing `BuiltinTag::Eq` / `builtin_eq`. `===` is a *test* (never binds), so — like `=`
— it carries no NAF hazard.

### `=` / `eq` become genuinely dispatched (Phase 2)

`=`/`eq` are the semantic `Eq.eq` operation: dispatched through the carrier's `Eq`
instance. For a concrete argument the carrier pins the impl (`Int → IntEq.eq`, still an
`i64` compare, so **every current ground use keeps its answer**); for an abstract argument
the requirement dictionary supplies it (WI-300 Tier B). A `Set` carrier's `Eq` is
membership-based, and `=`/`eq` finally honor it. This **replaces** the structural shortcut
with real dispatch — the change 049 deferred.

This half is **gated on spec-op dispatch at SLD**, which does not yet exist: a rule-body
`eq(1,1)` works today *only because* it is `builtin_eq`; unbinding it needs the resolver to
dispatch `Int → IntEq.eq` at resolution (carrier-based for concrete args, dict-based for
abstract), i.e. the same SLD→eval bridge that gates WI-300 Tier B (the WI-483/487 line).
So the flip is Phase 2, sequenced behind that bridge.

### The migration is an audit, not a rename

The expensive part of Phase 2 is that **today's `=`/`eq` sites carry mixed intent** and
must be split:

- **structural intent → `===`**: reflect/internal comparisons of `Term`s, `Symbol`s, and
  reflected structure *mean* structural identity and must not suddenly require an `Eq`
  instance. These migrate to `===`.
- **semantic intent → `=`**: value comparisons over data whose equality is (or may become)
  the carrier's — these stay `=` and gain real dispatch.

`neq` (`neq(a,b) <=> not(eq(a,b))`) pairs with semantic `=`; structural inequality is
`not(a === b)` (a `!==` sugar is possible but not required). Doing the `===` **surface +
the structural-intent migration first** (Phase 1) means that when `=` flips (Phase 2), the
structural sites are already off `=` and cannot break.

### Interaction with WI-300

Orthogonal to WI-300's guard tier (`requires(X) → find_dictionary → provides/suspend`),
which lands unchanged. `===` gives rule bodies a structural test that needs **no** `Eq`
instance (so a rule that just wants term identity carries no `requires`), while `eq`/`=`
under a `requires(Eq[T])` guard become the honest "dispatched equality, so `T` must have
`Eq`." The two together make WI-300's worked example mean what it says.

### Invariant

> `===` is structural-only and never dispatches; it is total (defined for every value,
> no `Eq` instance). `=` / `eq` are semantic and dispatch through the carrier's `Eq`
> instance (Phase 2; a structural shortcut until then). `<=>` is structural unify (049).

This supersedes 049's Invariant by *acting on* its "may someday dispatch" clause — the
someday is scheduled.

## Lexing

`===` is a single token, lexed **greedy-longest** before `==` (were it to exist) and `=`.
`a = b` is the semantic test; `a === b` is structural. Applies to both
`tree-sitter-anthill/grammar.js` and the scaland fastparse grammar (scaland mirrors
grammar + loader only, no typer).

## Build order

1. **`===` operator (Phase 1)** — grammar token (tree-sitter + scaland, greedy lex) +
   loader mapping `===` → `BuiltinTag::Eq` / `builtin_eq` (the existing structural
   comparator) + migrate the obvious structural-intent internal/reflect comparison sites
   from `=`/`eq` to `===`. `=`/`eq` stay the structural shortcut (backward-compatible).
   Decision-free, independent of the SLD bridge. **Lands first.** *(the filed WI)*
2. **Dispatched `=` (Phase 2)** — flip `=`/`eq` from the structural shortcut to genuine
   carrier dispatch (concrete = carrier-pinned per WI-350; abstract = requirement dict per
   WI-300 Tier B); add the first non-structural `Eq` carriers (`Set`/`Map` membership
   equality); complete the intent audit across prelude/stdlib. **Gated on** the SLD→eval
   spec-op dispatch bridge (WI-483/487 / WI-300 Tier B). Its own follow-on WI, filed when
   that bridge is scoped.
3. **Docs** — `kernel-language.md` equality section + this concept map; 049 cross-link.

## Non-goals

- E-unification / AC-matching (still 049's non-goal; a future engine capability).
- Building the SLD→eval spec-op dispatch bridge itself (a prerequisite for Phase 2,
  tracked separately as WI-300 Tier B / WI-483/487).
- A `!==` structural-inequality glyph (`not(a === b)` suffices; revisit if ergonomics
  demand).

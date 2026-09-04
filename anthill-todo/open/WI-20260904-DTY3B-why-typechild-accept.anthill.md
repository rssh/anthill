## Attributes

- id: WI-20260904-DTY3B-why-typechild-accept
- created: 2026-09-04T14:54:14Z

- status: Open
- status_agent: user
- status_at: 2026-09-04T14:54:14Z

- acceptance: cargo-test, scaland-sbt-test

## Description

why TypeChild accept hash-consed TermId, what is the reason to have no Occurrence and not
accept Value

ANSWERED IN PART 2026-09-04, and the answer turns into a proposal. Sibling of
WI-20260904-RB0Z5 ("why can't we create a Var in the Value itself") — ONE question from
two sides.

WHAT THE TWO CARRIERS BUY (WI-342's minimal-`Value`-spine principle: only the path from a
container down to a `denoted` is `Value`-carried, everything else stays interned):

  * O(1) STRUCTURAL EQUALITY. `Interned(a) == Interned(b)` is `a == b`. As occurrences two
    structurally identical types are distinct `Rc`s — identity-bearing and span-carrying —
    so every comparison becomes a deep walk, and this crate compares types constantly.
  * DEDUP. Every `Int64` across every signature is ONE `TermId`; one per SITE as an
    occurrence.

That is exactly what CLAUDE.md's representation note reserves interning FOR — "persistent,
heavily-shared structure". So DROPPING the `TermId` arm de-optimizes the overwhelmingly
common case to fix a rare one, and is the wrong direction.

WHY IT IS NOT ACCEPTING `Value` EITHER. `TypeChild` is a NARROWED `Value` — the two
carriers a type may legally take. The narrowing is what makes "a scalar / `Var` / `Entity`
here is a typer bug" unrepresentable rather than a runtime check, which is CLAUDE.md's
"make illegal state unrepresentable". Widening it to `Value` would give that up.

THE REAL GAP IS A THIRD CARRIER, not a different set of two. A TRANSIENT INFERENCE
VARIABLE is precisely what the same note says must NOT be interned — "specifically
inappropriate for binders … whose scope and alpha-equivalence don't fit a global dedup
store" — and today it has no other way to exist in a type slot: `TypeChild::Interned`
holds a `TermId`, so `Value::term(type_param_var_term(kb, Var::Global(vid)))` is forced.
MEASURED (WI-20260904-50B2K): passing `Value::Var(..)` instead fails every row with
"WI-342: non-type Value in a TypeChild slot: Var(Global(..))".

    enum TypeChild {
        Interned(TermId),          // shared persistent structure — O(1) equality
        Node(Rc<NodeOccurrence>),  // denoted-poisoned spine
        Var(VarId),                // a transient inference variable — never interned
    }

IT ALSO RETIRES A NAME COLLISION RATHER THAN PAPERING IT. The variant was `Ground` and was
renamed to `Interned` on 2026-09-04 because the word meant two things in one crate: this
arm asks HASH-CONSABILITY (its opposite is POISONED), while `resolved_type_is_ground` /
`GroundCheck::Ground` / `BuiltinTag::Ground` ask the LOGICAL property. They disagree on
exactly ONE shape — a `Term::Var` in a type slot, which is interned and is not ground —
and under a third arm that shape has its own carrier, so the two readings stop overlapping
at all. `value_to_type_child` would map `Value::Var -> TypeChild::Var` instead of
`debug_assert!`-ing it a typer bug.

THE ARM'S POPULATION, CENSUSED (load.rs's type lowering, 2026-09-04) — evidence for the
claim above rather than an assertion of it:

    make_sort_ref                                     7   a bare sort ref — DOMINANT
    Interned(t) pass-throughs                        10   already interned upstream
    proj / make_expr_carried                          3   `s.T` projections
    effect forms (canonical rows / absent / guarded)   3
    make_named_tuple_type                             2
    make_parameterized_type, make_arrow_type          2
    Interned(var)                                     1   <- a VARIABLE

So the arm is dominated by NOMINAL SORT REFERENCES and structural type forms — persistent,
heavily shared, which is what the interning justification needs. A variable is not the
arm's purpose; it is a MINORITY INHABITANT RIDING A CARRIER BUILT FOR SOMETHING ELSE. One
carrier, two populations — the same shape as `type_var` serving two questions
(WI-20260904-50B2K), one layer down. `resolve.rs:15149` already carries a comment
explaining that a caller var "lives in a `TypeChild::Interned(Var)` binding"; that note
stops being needed once `Var` has its own arm.

WHY A VAR NEEDS A `TermId` AT ALL — IT DOES NOT. Hash-consing buys DEDUP and O(1)
structural equality for REPEATED STRUCTURE. A `VarId` is already a copyable value with O(1)
equality, so interning a variable buys nothing it does not already have, while costing a
permanently refcounted store entry per fresh var. The only reason is the SLOT'S SHAPE:
`TypeChild::Interned` holds a `TermId`, so a variable must become one to fit. An artifact,
not a benefit.

AND IT IS NOT ONLY THE VAR — EVERY CONTAINER BUILT OVER ONE IS INTERNED TOO. `load.rs`'s
named-tuple lowering (2 sites) reads:

    if any {                                   // some child is a Node (denoted-poisoned)
        TypeChild::Node(make_named_tuple_occ(..))
    } else {
        let ground: Vec<(Symbol, TermId)> = ..  // <- the local is named `ground`
        TypeChild::Interned(make_named_tuple_type(&ground))
    }

The predicate is `!any_node` — NO CHILD IS DENOTED-POISONED. It says nothing about
variables, so `(a: ?T, b: Int64)` takes the INTERNED branch, variables and all. Since `?T`
is unique per site, that tuple term is shareable with nothing: one store entry per site,
for a container whose whole point was the transient variable inside it. The interning
justification (persistent, heavily-shared structure) is FALSE for exactly this population
and the code cannot currently tell it apart.

(The local named `ground` is the same word-collision a THIRD time — after
`TypeChild::Ground` itself and the `TypeNode` doc's "always ground" list. Its predicate is
the INTERNED sense; renaming it is part of this ticket's work, not a drive-by.)

THE THIRD ARM FIXES THE CONTAINER CASE FOR FREE, and that is the shape's best argument.
Every container's lowering already asks "is any child NOT interned?" — spelled `any` /
`any_node` today because `Node` was the only non-interned answer. With a `Var` arm the
predicate becomes "are ALL children `Interned`?", so a `Var` child pushes its container
onto the occurrence carrier by the SAME rule that a `denoted` child does. `(a: ?T, b:
Int64)` stops being interned without anyone writing a special case for it. The change is
therefore not "add a variant and patch N sites" — it is "the existing predicate was
binary and should have been a question about the carrier".

THE TWO CARRIERS ARE A CHOICE, NOT A CONSTRAINT — checked, not assumed. `make_sort_ref`
COULD build an occurrence: `span: SourceSpan` and `owner: Option<Symbol>` are threaded
through every lowering function that reaches these sites (`load.rs` 24539, 24609, 24753,
24821, 24894, 25059, …), which is the same context `make_named_tuple_occ` already uses on
the other branch. So the answer to "why can't a sort ref be an occurrence" is not that it
cannot; it is that a sort ref is the ONE thing interning genuinely pays for — `Int64`
across 500 signatures is one `TermId` against 500 identity-bearing `Rc`s and a deep
equality.

WHICH EXPOSES THE ACTUAL RULE THE CODE APPLIES, and it is the wrong one. Today a subtree is
interned UNLESS A `denoted` SITS BENEATH IT. That is not "interned when it PAYS", it is
"interned when it CAN BE". A transient `?T` can be, so it is; the `(a: ?T, b: Int64)` built
over it can be, so it is — and `?T` is unique per site, so that term is shareable with
nothing at all.

    THE RULE THIS TICKET IS REALLY PROPOSING:
    the carrier is chosen by whether a subtree is WORTH SHARING,
    not by whether it is CAPABLE of being shared.

The `Var` arm is what makes that decidable — a per-site-unique variable is never worth
sharing — and the existing container predicate then propagates the verdict outward for
free (see the paragraph above). Stated this way the change is a CORRECTION to a rule, not
an addition to an enum, which is also what says where its risk lives: not in the arm, but
in every site whose `_ =>` assumed the old binary.

WHAT TO MEASURE BEFORE BELIEVING IT IS CHEAP. ~110 `TypeChild` match sites gain an arm,
and the ones that decide the outcome are the CATCH-ALLS: a `_ =>` that treats a `Var` as
interned is where this goes wrong SILENTLY. Census the `_` arms first, not the explicit
ones — a new variant's real population is the arms that do not name it.


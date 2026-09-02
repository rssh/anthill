## Attributes

- id: WI-20260902-JB6RS-czj2n-s-sort-exemption-is
- created: 2026-09-02T13:44:21Z

- status: Open
- status_agent: user
- status_at: 2026-09-02T13:44:21Z

- acceptance: cargo-test, scaland-sbt-test

## Description

CZJ2N'S SORT EXEMPTION IS TERMID-ONLY: structurally `Ref(S)` and `Fn{S,[],[]}` are ONE, so every matching consumer widened.

MEASURED BY ME (found by /code-review during WI-20260902-VNWAW; re-measured on the same
tree, one file plus four direct reads):

  namespace zzf34
    sort Shape
      entity Circle(r: Int64)
    end
    fact holdsS(Shape)
    rule viaBare(1)    :- holdsS(Shape)    -- 1
    rule viaApplied(1) :- holdsS(Shape())  -- 1   <- could not match before CZJ2N
  end

  ref_tid == fn_tid                 -> false      <- the exemption, as intended
  head(Ref(Shape))                  -> Functor { Shape, pos 0, named 0 }
  head(Fn{Shape,[],[]})             -> Functor { Shape, pos 0, named 0 }   <- IDENTICAL
  views_structurally_equal(r, f)    -> true
  MapKey::try_from_value  of each   -> Ref(Shape) / Ref(Shape)             <- ONE key

So the exemption survives exactly where CZJ2N put it — the hash-consed store — and NOWHERE
a consumer actually decides: `functor_view_head` is now unconditional, so the
discrimination tree, `views_structurally_equal`, the resolver's structural unify and the
map-key reader all see ONE head. §8.3 / WI-391 / WI-387 make `Ref(S)` the dispatch
WILDCARD and a nullary `Fn{S}` the CONCRETE spec identity; that distinction is what the
exemption exists to preserve, and it is preserved only for a reader that compares TermIds.

TWO FACES, ONE MECHANISM:
 (a) BEHAVIOUR. A match that could not happen before now can. CZJ2N's own
     `nullary_head_tests` module claims "every consumer that must keep them apart
     therefore reads the TERM", and the evidence offered for it is that the stdlib loads —
     which cannot rank whether a dispatch decision taken by MATCHING has widened. Nobody
     has driven a wildcard-vs-concrete binding THROUGH THE DISCRIM TREE; the coverage that
     exists goes through `impl_param_ref`.
 (b) A STALE INVARIANT COMMENT, corrected inline by VNWAW's commit rather than left:
     `eval/map_arena.rs`'s `MapKey::try_from_value` said "THE CANON IS GATED ON
     `is_constructor_symbol`, AND THAT GATE IS THE POINT … so
     `resolve_qualified_name_term("…Color")` (a sort) keeps its own key by design". Both
     halves are false now — the gate is type-hood at `alloc`, and the sort does NOT keep
     its own key (measured above). A new CZJ2N paragraph had been inserted ABOVE the stale
     one instead of replacing it.

NOT VNWAW'S — that ticket's change is `at_goal`-gated in the rule-body goal walk and moves
none of these numbers; measured with it backed out, every row above is identical.

ACCEPTANCE: decide which reading is right and make ONE of them true everywhere. Either the
Sort exemption is real, in which case a consumer that decides by MATCHING must see two
heads and `holdsS(Shape())` must stop matching `fact holdsS(Shape)`; or it is not, in
which case `alloc`'s gate is dead weight and the 792-symbol stdlib measurement that
motivated it has to be re-taken to find what actually depends on the TermId split.
CONTROLS, whichever way it goes: `FiniteCollection` must keep covering its own `requires`
(the measurement that put the gate there), a CONSTRUCTOR's two spellings must stay ONE key
(`map_arena`'s `a_non_canonicalized_nullary_constructor_keys_as_its_name`), and the
decisive new row must go through the DISCRIMINATION TREE — a `provides Spec[T = T]`
wildcard beside a concrete `Fn{S}` instance, retrieved by a ground goal — because that is
the reader the existing coverage does not use.


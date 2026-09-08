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

## Changes

### 2026-09-08T19:39:47Z — feedback — user

TWO MORE CONSUMERS, MEASURED — inherited from WI-20260902-EQG4F items 1 and 5, which are
this ticket's question asked twice and are dropped there. Neither changes the decision;
both widen the population it has to cover, and one of them is a SCALAND face this ticket
did not have.

A. SCALAND CONTRADICTS ITSELF, where rustland merely widens. rustland's readers agree with
   each other (`views_structurally_equal(Ref(S), Fn{S})` is TRUE, per this ticket's own
   table). Scaland's do NOT: `discrim/SubstTree.insertWalk` keys `Term.Ref(sym)` as
   `Functor(sym)/Arity(0)` — byte-identical to `Fn(sym,[],[])`'s key — while
   `subst/Substitution.unifyMatch` refuses the pair outright ("Head-kind mismatch (incl.
   Const-vs-Ref etc.) has no shared structure"). And `kb/KnowledgeBase.alloc` keeps the
   same `SymbolKind.Sort` exemption rustland has. So whichever way this ticket decides,
   scaland needs BOTH sites moved, and today its tree retrieves a candidate its unifier
   then rejects. Confirmed by reading all three sites; the decisive row this ticket already
   demands (a wildcard beside a concrete instance, retrieved by a ground goal THROUGH the
   tree) is the row that would tell whether the rejection saves it.

B. THE REIFY ROUND TRIP IS A CONSUMER THAT DECIDES, and it loses the exemption. Measured on
   the delivered tree, `test.eqg4f5.Shape` a `SymbolKind::Sort`:

     Fn{Shape,[],[]}  = TermId(14)        <- canon-EXEMPT, as intended
     Ref(Shape)       = TermId(24)
     reify(TermId(14)) = RefRepr(Shape)
     reflect(RefRepr)  = TermId(24)       <- the concrete spec identity became the wildcard

   CONTROLS: an entity constructor (`Shape.Circle`) and a rule predicate (`plain`) are
   canonicalized, so `Fn` and `Ref` are ONE TermId for them and their round trips are
   STABLE. The loss is at exactly the one shape the exemption exists to protect.
   WHERE IT IS: `reader::reflect_walk`'s `ReflectShape::Ref(sym) => CoreTerm::Ref(sym)`,
   reached from BOTH realizations (`KbBridge::reflect` and the interpreter's `kb_reflect`).
   NOT persistence — `persistence::print` reads the raw `Term::Fn` and never routes through
   `reify_walk`, exactly as CZJ2N's comment says. That comment censused the repr's READERS
   (`gate.anthill`) and the printer, and its "the move is invisible to it" holds for both;
   what it did not census is the INVERSE walk, which is where a `RefRepr` becomes a term
   again. Nothing in the corpus calls `KB.reflect` yet, so this is latent — but it is a
   published surface operation on both realizations, not dead code.

SO THE ACCEPTANCE GROWS BY TWO ROWS, whichever reading wins: if the exemption is real, the
reify round trip must PRESERVE `Fn{S,[],[]}` and scaland's tree must stop keying it as
`Ref(S)`; if it is not, `alloc`'s gate goes in BOTH implementations and `unifyMatch` must
stop refusing the pair — otherwise scaland keeps a retrieval its unifier undoes.


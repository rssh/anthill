## Attributes

- id: WI-20260902-JB6RS-czj2n-s-sort-exemption-is
- created: 2026-09-02T13:44:21Z

- status: Delivered
- status_agent: claude
- status_at: 2026-10-20T13:57:57Z

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

### 2026-10-17T18:38:48Z — feedback — user

DECIDED (user, 2026-10-17): reading A, with a different justification. The spec text is committed with this note: kernel §4.4 "A name has a reading in each context, and the context's own comes first", §6 (the exception paragraph), §5.6 Modify, §8.3, the grammar; 055 §2 amended twice.

MEASURED FIRST, on 67fee9e0. With the `SymbolKind::Sort` gate in `nullary_name_canons_to_ref` dropped, the stdlib loads, so the 792-symbol / FiniteCollection failure no longer reproduces. anthill-core (opt 2) had 43 failures in three groups:
  - rows asserting the split itself: ~10 lib rows;
  - test helpers matching a raw `Term::Fn`: wi210 x9, wi221 x3, wi224 x6, wi452 x4, wi943, wi954 x2, wi366, wi031;
  - REAL changes: `()` typed `Type (TupleLiteral)` (wi_3hn0n x3), `role: Alpha831()` no longer refused (wi830), and ListLiteral() (wi1099 x2).
So the split is load-bearing, but as VALUE vs TYPE for a name that is both a sort and a constructor, not as wildcard vs concrete: the wildcard is read by role (7QVD5).

THE RULE. In a TYPE context (an annotation, a bracket binding, a requires/provides spec) a name is read as a type first, and as a value only if it has no type reading. In a DATA context (clause positions, data slots, operation bodies) it is read as data first, and as a type value (055) only if it has no data reading. Every constructor has both readings (§6.3), so:
  - `Foo` = `Foo()`, the instance, in a data context. Choice (i): this holds for fielded constructors too, so bare `account` is the all-fields-fresh application.
  - A constructor's type as data is `Foo[]` (grammar: zero bindings).
  - A sort with no constructor of its name (`Int64`, `Cell`) stays a bare type value.
  - Only a BARE name falls back. `S(…)` needs something applicable (`Shape()`, `Eq(T: ?q)` are load errors), and `S[…]` is always a type.
  - NO EXCEPTIONS: `Modify[counter]` over a nullary constructor (WI-4GBQV, the ambient resource) is retired. It is the constructor's type, refused like `Modify[Cell]`. Parameters, result, field paths and zero-arg operations are unchanged.
  - A type written as data and an instance are never one term. Measured on HEAD, both of these are wrong: `fact held(Foo[X = Int64])` is found by `:- held(Foo(X: ?v))`, and `fact Tag[T = Int64]` is found by `:- Tag(T: ?q)`.

ALSO IN THIS TICKET (user: fix inline). `Foo[Int64, String]` and `Foo[X = Int64, Y = String]` are the same type by §5.1, but they are two terms in a data slot and do not match either way (measured).

FOUND, NOT IN SCOPE (raised with the user, undecided): the spec's position vocabulary is inconsistent. "data slot" (§5.9, matched not evaluated) and "value slot" (§5.3, evaluated) claim the same goal arguments, and line 945 ("a rule data position is not evaluated") contradicts line 4305 ("a compound expression … is evaluated wherever it is written, even inside a clause").

ACCEPTANCE GROWS. The rows the ticket already demands, plus:
  - `p(Foo)` and `p(Foo())` are one term; `p(Foo[])` is another;
  - `facts_of(kb(), WorkItem[])` (27 corpus calls move);
  - `Modify[counter]` refused (wi4gbqv rewritten);
  - positional = named bracket;
  - the type-value/instance pair is disjoint through the discrimination tree, unify, MapKey and reify/reflect, in rustland AND scaland.

### 2026-10-17T19:06:25Z — feedback — user

REPRESENTATION DECIDED (user, 2026-10-17): R-C, separate symbols. Every constructor c, nested or standalone, gets a TYPE symbol c† distinct from its CONSTRUCTOR symbol c. A type is Ref(c†) / Fn{c†; params}; an instance is Ref(c) / Fn{c; fields}. They are disjoint by functor at every arity, so the alloc Sort gate, a label rule and a kind-dependent view head are all unnecessary, and CZJ2N's merged head becomes correct. The reading rule is name resolution: a type context resolves to c†, a data context to c. The printer writes c[…] / c[] for c† in a data slot. Rejected: R-A (Ref = type, Fn{c} = instance). It is smaller in the typer but diffuse: ~250 Term::Ref sites outside it, Ref(c) left meaning name/type/instance (an experiment flipping Ref(c) -> Fn{c} broke var_ref(name: Ref(c)) decoding, so the stdlib panicked at load), and a symbol-kind lookup back on every head() of a Ref (the hot path). Rough estimate for R-C, from grep upper bounds: ~90 typer hits and ~130 other KB hits where one symbol is both constructor and sort, each to get an explicit c <-> c† map; typer +0.3-0.5% lines; no hot-path cost.

### 2026-10-20T05:30:21Z — feedback — user

DECIDED (user, 2026-10-20): DROP AMBIENT PLACES — every resource is threaded as a parameter, and the place is the parameter. Both ambient spellings are refused: a nullary constructor in a Modify bracket (WI-20260823-4GBQV's Modify[counter]) is the constructor's TYPE, as in every bracket, and a zero-argument operation's result (WI-313's Modify[slot]) is refused as an AMBIENT place (PlaceType::Ambient in modify_place_type), because no call can write it — a call is no place to re-key onto. At a call, set(counter) and set(counter()) are no place either, and both are told as the constant they are. Repair: a parameter, or a let-bound local where a caller starts from the constant. Raised before deciding: 037 §3.2's pool rows (Modify[file_storage] over a pool sort's constant) depend on the ambient reading. 037 and 037-implementation.md carry dated amendment notes; how a row says "may change the file storage" is left to WI-20261017-J4WGC. Not redesigned here. Also found: origin's cef5913b (WI-9WVT7, 'a clause's type application is one term per type') already makes Foo[Int64] and Foo[X = Int64] one term in a clause (measured on the merged tree), so the positional = named item is closed by it, not by this ticket.

### 2026-10-20T13:57:27Z — feedback — user

DELIVERED in seven gated commits on main (not yet pushed): 142bf20d step 0, the Symbol type-face bit; a1ea1fce step 1, declaration tables keyed by intern::Decl; 5c6ac1d0 step 2, the predicates read a face as a type; d3701834 step 3, nested constructors' faces, no ambient places (user, 2026-10-20); dec23aaa step 4, every constructor's face; 4b93777d step 5, the reading rule — a bare constructor in a data context is its instance, its type `Foo[]`, with the migration of facts_of/covers, the JSON store's types and kind by face (decisions 1–4); a6615e1d step 6, one term for every name's nullary application but the three collection-literal reflect forms, `S(…)` over a sort refused, the printer bracketing a type written as data. Last gate 10,134 passed, 0 failed; scaland's suite green as it stands (694 + 45 + 1). Spec: kernel-language.md §4.2, §4.4, §5.6, §6, §8.3 and the grammar; proposal 055's two amendments; 037's pools left to WI-20261017-J4WGC. The scaland port is WI-20261020-80VNX (user, 2026-10-20).


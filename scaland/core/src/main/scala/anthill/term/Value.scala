package anthill.term

import anthill.intern.TermSymbol

/** A term carrier that is **not** hash-consed.
  *
  * [[TermStore]] interns persistent, heavily-shared structure — asserted facts,
  * rule heads, nominal sort identities — so structurally-identical terms share
  * one [[TermId]]. That is a storage *optimization*, not a property of term-hood:
  * transient structure (a query pattern, a constructed-but-not-yet-asserted
  * entity, an in-flight scalar) pays the intern cost for nothing and, in the
  * case of binders, must not be globally deduplicated at all.
  *
  * `Value` is the carrier for exactly that structure. It holds its children
  * inline rather than as `TermId`s, and it never enters [[TermStore]] unless it
  * crosses a KB boundary (fact assertion), at which point it is promoted to a
  * `Term`/`TermId`. `Value.Term` is the bridge: an already-interned subterm
  * riding inside a non-interned parent.
  *
  * Mirrors rustland `eval::value::Value` (proposal 026 §Values). Reading a
  * `Value` structurally — head, positional/named children — goes through
  * `anthill.kb.TermView`, which reads a `TermId` and a `Value` identically, so
  * the two carriers unify and index alike.
  *
  * ==Equality==
  * The derived `==` is **carrier-blind**: `Value.Term(id)` never equals a
  * structurally-identical `Value.Entity`, because they are different cases. It
  * is a useful within-carrier compare and nothing more. The structural,
  * cross-carrier comparator is `anthill.kb.viewsStructurallyEqual` — reach for
  * that whenever the question is "do these two denote the same term?".
  * (Rustland enforces this by not deriving `PartialEq` on `Value` at all; Scala
  * enum cases always carry one, hence this warning. Payloads are `IndexedSeq`,
  * not `IArray`, so the derived `==` is at least deep rather than referential.)
  *
  * ==Not yet ported==
  * Deliberately absent, each awaiting the thing that would produce it:
  *   - `Node(NodeOccurrence)` — the span-carrying occurrence carrier, and with
  *     it `ViewHead.Opaque`. Arrives with operation-body loading (WI-294).
  *   - the per-instance carried static type (rustland's `ty` field). Scaland has
  *     no typer to stamp it. It would ride here, on the per-instance `Value`,
  *     never on the interned `TermId` — one `TermId` spans every environment.
  *   - the evaluator's runtime handles (closure, stream, map, cell). Scaland has
  *     no evaluator.
  */
enum Value:
  // Scalars — inline, no `TermStore` allocation. The `*Val` suffix avoids
  // colliding with the payload types (`case BigInt(v: BigInt)` would be
  // self-referential) and mirrors `Literal`'s `*Lit`.
  case IntVal(v: Long)
  case BigIntVal(v: BigInt)
  case FloatVal(v: Double)
  case BoolVal(v: Boolean)
  case StrVal(v: String)
  case UnitVal

  /** Anonymous aggregate — no functor. Views as a functor-less application. */
  case Tuple(pos: IndexedSeq[Value], named: IndexedSeq[(TermSymbol, Value)])

  /** Constructed entity: a functor applied to inline children.
    *
    * TWO INVARIANTS, both ASSUMED and neither ENFORCED — nothing constructs an
    * `Entity` yet, so the first producer is where they must be established:
    *
    *  1. `named` carries no duplicate key. `anthill.kb.viewsStructurallyEqual`
    *     returns a false positive without this.
    *  2. `named` is in the same order as the `Term.Fn.namedArgs` of the term
    *     this entity would intern to. `viewsStructurallyEqual` looks named
    *     children up by key and does not depend on it, but the discrimination
    *     tree walks named positions in order — a differently-ordered `Entity`
    *     would key differently from its `Term.Fn` twin, and a cross-carrier
    *     discrim miss is a wrong answer, not a slow one.
    *
    * Rustland enforces both at `finish_constructor`, canonicalizing to declared
    * field order via `canonicalize_record_named_args` so that its Value- and
    * Term-side builders agree. Scaland has no such canonicalization pass on
    * either side today: the loader stores named args in construction order. That
    * is self-consistent while only `Term.Fn` exists, and becomes load-bearing
    * the moment a `Value` and a `Term` must key alike.
    */
  case Entity(functor: TermSymbol, pos: IndexedSeq[Value], named: IndexedSeq[(TermSymbol, Value)])

  /** An interned subterm riding inside a non-interned carrier. */
  case Term(id: TermId)

  /** A logic variable of any kind — views identically to `Term.Var`. */
  case Var(v: anthill.term.Var)

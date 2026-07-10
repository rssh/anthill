package anthill.kb

import anthill.intern.TermSymbol
import anthill.term.{Literal, OrderedDouble, Term, TermId, Value}

/** A carrier-neutral read API over terms.
  *
  * A term reaches a consumer riding on one of several carriers: a hash-consed
  * [[TermId]] out of the KB's `TermStore`, or a non-interned [[Value]] built in
  * flight. `TermView` is the read-only shape that makes them indistinguishable
  * to a consumer that only wants structure — a head, positional children, named
  * children. Once the unifier and the discrimination tree read through it, a
  * fact stored under one carrier will match a query in the other; a
  * cross-carrier miss is a wrong answer, not a slow one.
  *
  * NOTHING READS THROUGH THIS YET. `Substitution`, `SubstTree` and the SLD
  * resolver still walk `TermId` directly, and no scaland code constructs a
  * `Value`. Until those are migrated, the [[functorViewHead]] canonicalization
  * below is inert and the cross-carrier guarantee above is a promise, not a
  * property. This file is the substrate that migration lands on.
  *
  * Mirrors rustland `kb::term_view` (proposal 026.1 Q2). Rust needs a trait to
  * accept `TermId | Value` without boxing; here it is the same thing spelled as
  * a Scala 3 typeclass. Rust additionally has a `ViewItem` child type, whose
  * three cases distinguish *borrowed* from *owned* children; Scala children are
  * always owned references, so children are plain [[Value]]s and that type has
  * no counterpart here (a `TermId` child surfaces as `Value.Term`).
  *
  * Deliberately not yet ported, each awaiting its producer:
  *   - the `NodeOccurrence` carrier (`Value.Node`) and its `ViewHead.Opaque`
  *     head, which control-flow expression forms read. Arrives with
  *     operation-body loading (WI-294). Every `match` over `Value` below is
  *     exhaustive *without* a wildcard, so adding that case raises an E029
  *     exhaustivity warning at each of the four `valueView` methods (and a
  *     `MatchError` if one is missed) rather than silently reading a Node as a
  *     childless leaf. The build does not set `-Xfatal-warnings`, so these are
  *     warnings, not errors; making them errors would be a strict improvement.
  *   - `as_bind_value`, which captures a matched view into a discrimination-tree
  *     variable edge. `BindValue` cannot carry a `Value` yet, and nothing puts a
  *     `Value` into the tree. It lands when the substitution and discrim walkers
  *     are themselves carrier-neutralized.
  */
trait TermView[A]:
  def head(a: A, kb: KnowledgeBase): ViewHead

  /** The `i`th positional child, or `None` when this carrier has no such child
    * (a leaf, or an out-of-range index).
    */
  def posArg(a: A, kb: KnowledgeBase, i: Int): Option[Value]

  /** The named child under `sym`, or `None` when this carrier has no such key. */
  def namedArg(a: A, kb: KnowledgeBase, sym: TermSymbol): Option[Value]

  /** The keys of all named args, in the carrier's own order. */
  def namedKeys(a: A, kb: KnowledgeBase): IndexedSeq[TermSymbol]

  /** The logic variable at this view's head, of *any* kind — flex `Global`,
    * bound `DeBruijn`, or `Rigid` skolem. `None` for a non-variable head, which
    * then keys on [[head]].
    *
    * In rustland this is what lets the discrimination tree route a var by KIND:
    * `Global`/`DeBruijn` become a wildcard var-edge, while a `Rigid` skolem
    * becomes a CONSTANT (`DiscrimKey::RigidVar(VarId)`) that matches only the
    * same skolem. Scaland's `SubstTree` has no `RigidVar` key — `Var.varId`
    * collapses every kind to a `VarId` and every var becomes a wildcard var-edge
    * — so a `Rigid` there would over-match a concrete fact and two distinct
    * skolems would conflate. That gap is currently unreachable (nothing in
    * scaland mints a `Rigid`; see `Var.Rigid`'s "ADT scaffolding for parity"
    * note, WI-637) and must be closed before one does.
    *
    * Note that [[viewsStructurallyEqual]] already treats a `Rigid` as a constant
    * — it compares var heads by full `Var` identity — so the comparator and the
    * discrimination tree currently disagree about rigids. Only the comparator is
    * right.
    *
    * Every carrier surfaces its var kind through `head` as [[ViewHead.Var]], so
    * this default is exact and no instance overrides it.
    */
  def indexVar(a: A, kb: KnowledgeBase): Option[anthill.term.Var] =
    head(a, kb) match
      case ViewHead.Var(v) => Some(v)
      case _               => None

/** The outermost shape of a term, enough to drive unification dispatch.
  * Structure beneath the head is fetched through [[TermView.posArg]] /
  * [[TermView.namedArg]].
  */
enum ViewHead:
  /** A logic variable of any kind — see [[TermView.indexVar]]. */
  case Var(v: anthill.term.Var)
  case Const(lit: Literal)

  /** A functor application. `functor` is `None` for a functor-less aggregate
    * (`Value.Tuple`, `Value.UnitVal`), which is why `unit` and the empty tuple
    * read — and compare — as the same head.
    */
  case Functor(functor: Option[TermSymbol], posArity: Int, namedArity: Int)
  case Ref(sym: TermSymbol)
  case Ident(sym: TermSymbol)
  case Bottom

  /** The head's functor symbol, reading a bare [[ViewHead.Ref]] as the 0-ary
    * application it denotes (`Ref(c) ≡ Fn{c}`) — see [[functorViewHead]]. A
    * reader that identifies a head by its *symbol* must accept either spelling.
    * `None` for a functor-less aggregate, a var, a const, `Bottom`.
    */
  def functorSym: Option[TermSymbol] = this match
    case ViewHead.Functor(f, _, _) => f
    case ViewHead.Ref(s)           => Some(s)
    case _                         => None

/** Canonicalize a functor-application head: a **0-ary application of a
  * registered constructor** reads as the bare [[ViewHead.Ref]].
  *
  * A 0-ary constructor `c` has two indistinguishable spellings — bare `Ref(c)`
  * and the nullary application `Fn{c}` / `Entity{c}` — that print identically
  * (`c`), and only the bare `Ref` survives a print/parse round-trip. Reading
  * every carrier's 0-ary constructor *through* `Ref` closes the divergence where
  * a fact stored as `Fn{c}` is invisible to a rule spelled `Ref(c)`.
  *
  * The `isConstructorSymbol` gate keeps this kind-isolated: a concrete sort
  * (`Fn{Int64}`) or a type parameter is not a constructor, so the
  * wildcard-vs-concrete distinction those rely on is untouched.
  *
  * LOAD-ORDER SENSITIVE: `isConstructorSymbol` reads `constructorSymbols_`,
  * which `registerEntityOf` fills incrementally during loading. The same term
  * `Fn{c}` therefore heads as `Functor(c,0,0)` before `c` is registered and as
  * `Ref(c)` after. A consumer that keys, caches, or compares 0-ary constructors
  * mid-load can straddle that boundary and get two different answers. Rustland
  * `kb::term_view::functor_view_head` (WI-436) has the same property.
  */
private[kb] def functorViewHead(
  kb: KnowledgeBase,
  functor: TermSymbol,
  posArity: Int,
  namedArity: Int
): ViewHead =
  if posArity == 0 && namedArity == 0 && kb.isConstructorSymbol(functor) then ViewHead.Ref(functor)
  else ViewHead.Functor(Some(functor), posArity, namedArity)

/** Symbol equality on the raw handle. `TermSymbol` is an opaque `Int`, so `==`
  * would also be correct, but it boxes; this is the module-wide idiom and the
  * view API is on the resolver's hot path.
  */
private[kb] inline def symEq(x: TermSymbol, y: TermSymbol): Boolean =
  TermSymbol.raw(x) == TermSymbol.raw(y)

private[kb] def posAt(pos: IndexedSeq[Value], i: Int): Option[Value] =
  if i >= 0 && i < pos.length then Some(pos(i)) else None

/** First child under `sym`. A hand-rolled loop rather than `collectFirst`, which
  * would allocate a partial function per call on the hot path.
  */
private[kb] def namedAt(named: IndexedSeq[(TermSymbol, Value)], sym: TermSymbol): Option[Value] =
  var i = 0
  while i < named.length do
    val (s, v) = named(i)
    if symEq(s, sym) then return Some(v)
    i += 1
  None

object TermView:
  /** Summoner: `TermView[TermId].head(tid, kb)`. */
  def apply[A](using tv: TermView[A]): TermView[A] = tv

  /** The hash-consed carrier. Every other instance bottoms out here whenever it
    * meets an interned subterm; its children surface as `Value.Term`.
    */
  given termIdView: TermView[TermId] with
    def head(a: TermId, kb: KnowledgeBase): ViewHead = kb.getTerm(a) match
      case Term.Var(v)     => ViewHead.Var(v)
      case Term.Const(lit) => ViewHead.Const(lit)
      case fn: Term.Fn     => functorViewHead(kb, fn.functor, fn.posArgs.length, fn.namedArgs.length)
      case Term.Ref(s)     => ViewHead.Ref(s)
      case Term.Ident(s)   => ViewHead.Ident(s)
      case Term.Bottom     => ViewHead.Bottom

    def posArg(a: TermId, kb: KnowledgeBase, i: Int): Option[Value] = kb.getTerm(a) match
      case fn: Term.Fn =>
        if i >= 0 && i < fn.posArgs.length then Some(Value.Term(fn.posArgs(i))) else None
      case Term.Const(_) | Term.Var(_) | Term.Ref(_) | Term.Ident(_) | Term.Bottom => None

    def namedArg(a: TermId, kb: KnowledgeBase, sym: TermSymbol): Option[Value] =
      kb.getTerm(a) match
        case fn: Term.Fn =>
          var i = 0
          var found: Option[Value] = None
          while i < fn.namedArgs.length && found.isEmpty do
            val (s, t) = fn.namedArgs(i)
            if symEq(s, sym) then found = Some(Value.Term(t))
            i += 1
          found
        case Term.Const(_) | Term.Var(_) | Term.Ref(_) | Term.Ident(_) | Term.Bottom => None

    def namedKeys(a: TermId, kb: KnowledgeBase): IndexedSeq[TermSymbol] = kb.getTerm(a) match
      case fn: Term.Fn => Vector.tabulate(fn.namedArgs.length)(i => fn.namedArgs(i)._1)
      case Term.Const(_) | Term.Var(_) | Term.Ref(_) | Term.Ident(_) | Term.Bottom => Vector.empty

  /** The non-interned carrier. A `Value.Term` delegates to [[termIdView]]; the
    * inline carriers read their own children.
    *
    * Each match enumerates every case rather than ending in `case _`, so adding
    * a `Value.Node` carrier flags HERE — at the child accessors, which under a
    * wildcard would instead report a Node as childless and silently mis-key it.
    */
  given valueView: TermView[Value] with
    def head(a: Value, kb: KnowledgeBase): ViewHead = a match
      case Value.Term(id)              => termIdView.head(id, kb)
      case Value.IntVal(n)             => ViewHead.Const(Literal.IntLit(n))
      case Value.BigIntVal(n)          => ViewHead.Const(Literal.BigIntLit(n))
      case Value.FloatVal(f)           => ViewHead.Const(Literal.FloatLit(OrderedDouble(f)))
      case Value.BoolVal(b)            => ViewHead.Const(Literal.BoolLit(b))
      case Value.StrVal(s)             => ViewHead.Const(Literal.StringLit(s))
      case Value.UnitVal               => ViewHead.Functor(None, 0, 0)
      case Value.Tuple(pos, named)     => ViewHead.Functor(None, pos.length, named.length)
      case Value.Entity(f, pos, named) => functorViewHead(kb, f, pos.length, named.length)
      case Value.Var(v)                => ViewHead.Var(v)

    def posArg(a: Value, kb: KnowledgeBase, i: Int): Option[Value] = a match
      case Value.Term(id)          => termIdView.posArg(id, kb, i)
      case Value.Tuple(pos, _)     => posAt(pos, i)
      case Value.Entity(_, pos, _) => posAt(pos, i)
      case Value.IntVal(_) | Value.BigIntVal(_) | Value.FloatVal(_) | Value.BoolVal(_) |
          Value.StrVal(_) | Value.UnitVal | Value.Var(_) => None

    def namedArg(a: Value, kb: KnowledgeBase, sym: TermSymbol): Option[Value] = a match
      case Value.Term(id)            => termIdView.namedArg(id, kb, sym)
      case Value.Tuple(_, named)     => namedAt(named, sym)
      case Value.Entity(_, _, named) => namedAt(named, sym)
      case Value.IntVal(_) | Value.BigIntVal(_) | Value.FloatVal(_) | Value.BoolVal(_) |
          Value.StrVal(_) | Value.UnitVal | Value.Var(_) => None

    def namedKeys(a: Value, kb: KnowledgeBase): IndexedSeq[TermSymbol] = a match
      case Value.Term(id)            => termIdView.namedKeys(id, kb)
      case Value.Tuple(_, named)     => named.map(_._1)
      case Value.Entity(_, _, named) => named.map(_._1)
      case Value.IntVal(_) | Value.BigIntVal(_) | Value.FloatVal(_) | Value.BoolVal(_) |
          Value.StrVal(_) | Value.UnitVal | Value.Var(_) => Vector.empty

/** Representation-independent structural equality between two term views.
  *
  * Two views are equal iff their heads match and every child recurses equal,
  * regardless of which carrier either side rides on — children are themselves
  * [[Value]]s, hence views, so the recursion is carrier-blind. This is the
  * comparator to reach for instead of `TermId.raw ==` (true only while both
  * sides are interned, and silently false the moment a `Value` enters) or
  * rendered names (two distinct terms can print the same string, and one term
  * can print two ways across carriers).
  *
  * Variables compare by full `Var` identity, so a `Global` and a `Rigid` sharing
  * a `VarId` are unequal and two distinct skolems never conflate. Head-kind
  * mismatches are unequal: there is no shared structure to compare.
  *
  * It resolves neither a substitution nor a sort alias — a caller that needs two
  * differently-encoded-but-equal forms to agree canonicalizes first, then
  * compares. It is NOT, however, a pure function of the two terms: heads come
  * from [[functorViewHead]], which consults the KB's constructor registry, so
  * whether `Fn{c}` equals `Ref(c)` depends on `c` having been registered (see
  * that function's load-order note).
  *
  * ASSUMED, NOT ENFORCED: named keys are duplicate-free on both sides. Equal
  * `namedArity` plus every one of `a`'s keys found-and-equal in `b` implies
  * identical key sets only under that assumption; with a duplicated key on one
  * side (`[(x,1),(x,2)]` vs `[(x,1),(y,9)]`) this returns a false positive.
  * Nothing constructs a `Value.Entity` yet, so the first producer is where the
  * invariant must be established. Rustland `views_structurally_equal` (WI-486)
  * makes the same assumption, enforced there at `finish_constructor`.
  */
def viewsStructurallyEqual[A, B](kb: KnowledgeBase, a: A, b: B)(using
  va: TermView[A],
  vb: TermView[B]
): Boolean =
  (va.head(a, kb), vb.head(b, kb)) match
    case (ViewHead.Var(x), ViewHead.Var(y))     => x == y
    case (ViewHead.Const(x), ViewHead.Const(y)) => x == y
    case (ViewHead.Ref(x), ViewHead.Ref(y))     => symEq(x, y)
    case (ViewHead.Ident(x), ViewHead.Ident(y)) => symEq(x, y)
    case (ViewHead.Bottom, ViewHead.Bottom)     => true
    case (ViewHead.Functor(fa, pa, na), ViewHead.Functor(fb, pb, nb)) =>
      fa == fb && pa == pb && na == nb &&
      (0 until pa).forall { i =>
        (va.posArg(a, kb, i), vb.posArg(b, kb, i)) match
          case (Some(ca), Some(cb)) => viewsStructurallyEqual(kb, ca, cb)
          case _                    => false
      } &&
      // Keyed lookup, so the carriers' named-arg ORDER is not relied on here.
      // The discrimination tree, which walks named positions in order, is where
      // the canonical-order invariant on `Value.Entity` will matter.
      va.namedKeys(a, kb).forall { key =>
        (va.namedArg(a, kb, key), vb.namedArg(b, kb, key)) match
          case (Some(ca), Some(cb)) => viewsStructurallyEqual(kb, ca, cb)
          case _                    => false
      }
    case _ => false

package anthill.discrim

import anthill.intern.TermSymbol
import anthill.subst.Substitution
import anthill.term.{Term, TermId, TermStore, VarId}

/** Describes where in a fact term to extract a variable's binding value: a
  * chain of [[ArgPos]] steps descending from the head, root-to-leaf. The empty
  * chain (`Root`) addresses the whole head — a bare-variable query binds it. A
  * single step addresses a top-level argument; multiple steps address a variable
  * nested inside a compound argument (`f(g(?y))` records `?y` at
  * `[Positional(0), Positional(0)]`). The discrimination-tree query records the
  * chain as it descends the query structure; [[extractAtPath]] replays it
  * against the matched fact head (WI-671, rust parity: `VarPath` /
  * `extract_at_path`, WI-373 gap 3 — nested binding extraction). */
final case class VarPath(steps: Vector[ArgPos]):
  /** A new path with `step` appended (descend one level). */
  def appended(step: ArgPos): VarPath = VarPath(steps :+ step)

object VarPath:
  /** The root path (empty chain) — addresses the whole head. */
  val Root: VarPath = VarPath(Vector.empty)

enum ArgPos:
  case Positional(n: Int)
  case Named(sym: TermSymbol)

/** A binding value: either an already-resolved TermId or a deferred path. */
enum BindValue:
  case TermVal(id: TermId)
  case Path(path: VarPath)

/** Extract a subterm TermId from a fact term following a VarPath, descending one
  * [[ArgPos]] step at a time. The root path returns the whole term; a multi-step
  * path walks into nested `Fn` args (WI-671). A step that fails to descend (a
  * non-`Fn` term, or a missing arg) is a discrim/path desync — falls back to the
  * whole fact term, mirroring rust's `extract_at_path`. */
def extractAtPath(terms: TermStore, factTerm: TermId, path: VarPath): TermId =
  val steps = path.steps
  var cur = factTerm
  var i = 0
  while i < steps.length do
    terms.get(cur) match
      case fn: Term.Fn =>
        val next: Option[TermId] = steps(i) match
          case ArgPos.Positional(n) =>
            if n < fn.posArgs.length then Some(fn.posArgs(n)) else None
          case ArgPos.Named(sym) =>
            var j = 0
            var found: Option[TermId] = None
            while j < fn.namedArgs.length && found.isEmpty do
              val (s, id) = fn.namedArgs(j)
              if TermSymbol.raw(s) == TermSymbol.raw(sym) then found = Some(id)
              j += 1
            found
        next match
          case Some(id) => cur = id; i += 1
          case None      => return factTerm // path/fact desync (missing arg)
      case _ => return factTerm             // path step into a non-Fn term
  cur

/** SmallSubst — immutable cons-list for O(1) clone/branch during tree traversal. */
class SmallSubst private (private val bindings: List[(VarId, BindValue)]):

  def withBinding(v: VarId, value: BindValue): SmallSubst =
    new SmallSubst((v, value) :: bindings)

  /** Materialize the deferred leaf bindings into a real [[Substitution]].
    * `unifyRebind` (WI-637) selects how a var bound TWICE (a nonlinear pattern
    * position) reconciles: `true` — the RESOLUTION path (SLD head selection) —
    * UNIFIES the two values; `false` — the MATCHING path — demands structural
    * identity. See [[Substitution.bindLeaf]]. */
  def resolveLeaf(terms: TermStore, factTerm: TermId, unifyRebind: Boolean): Substitution =
    val s = Substitution()
    for (vid, bv) <- bindings do
      val tid = bv match
        case BindValue.TermVal(id) => id
        case BindValue.Path(path) => extractAtPath(terms, factTerm, path)
      s.bindLeaf(terms, vid, tid, unifyRebind)
    s

  /** No-op — immutable, structural sharing means clone is free. */
  def copy(): SmallSubst = this

object SmallSubst:
  def apply(): SmallSubst = new SmallSubst(Nil)

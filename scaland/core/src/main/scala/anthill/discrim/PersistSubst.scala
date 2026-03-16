package anthill.discrim

import anthill.intern.TermSymbol
import anthill.subst.Substitution
import anthill.term.{Term, TermId, TermStore, VarId}

/** Describes where in a fact term to extract a variable's binding value. */
enum VarPath:
  case Root
  case Arg(pos: ArgPos)

enum ArgPos:
  case Positional(n: Int)
  case Named(sym: TermSymbol)

/** A binding value: either an already-resolved TermId or a deferred path. */
enum BindValue:
  case TermVal(id: TermId)
  case Path(path: VarPath)

/** Extract a subterm TermId from a fact term following a VarPath. */
def extractAtPath(terms: TermStore, factTerm: TermId, path: VarPath): TermId =
  path match
    case VarPath.Root => factTerm
    case VarPath.Arg(argPos) =>
      terms.get(factTerm) match
        case fn: Term.Fn =>
          argPos match
            case ArgPos.Positional(n) =>
              if n < fn.posArgs.length then fn.posArgs(n) else factTerm
            case ArgPos.Named(sym) =>
              var i = 0
              while i < fn.namedArgs.length do
                val (s, id) = fn.namedArgs(i)
                if TermSymbol.raw(s) == TermSymbol.raw(sym) then return id
                i += 1
              factTerm
        case _ => factTerm

/** SmallSubst — immutable cons-list for O(1) clone/branch during tree traversal. */
class SmallSubst private (private val bindings: List[(VarId, BindValue)]):

  def withBinding(v: VarId, value: BindValue): SmallSubst =
    new SmallSubst((v, value) :: bindings)

  def resolveLeaf(terms: TermStore, factTerm: TermId): Substitution =
    val s = Substitution()
    for (vid, bv) <- bindings do
      val tid = bv match
        case BindValue.TermVal(id) => id
        case BindValue.Path(path) => extractAtPath(terms, factTerm, path)
      s.bind(vid, tid)
    s

  /** No-op — immutable, structural sharing means clone is free. */
  def copy(): SmallSubst = this

object SmallSubst:
  def apply(): SmallSubst = new SmallSubst(Nil)

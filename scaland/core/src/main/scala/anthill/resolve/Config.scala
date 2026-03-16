package anthill.resolve

import anthill.term.TermId
import anthill.subst.Substitution

/** Configuration for SLD resolution. */
case class ResolveConfig(
  maxDepth: Int = 100,
  maxSolutions: Int = 0,  // 0 = unlimited
  simplify: Boolean = false
)

/** A successful resolution result. */
case class Solution(
  subst: Substitution,
  residual: IndexedSeq[TermId]
)

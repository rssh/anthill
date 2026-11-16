package anthill.resolve

import anthill.term.TermId
import anthill.subst.Substitution

/** Configuration for SLD resolution.
  *
  * `maxDepth` is the deepest a goal may be NESTED: a goal opened from a clause's body is one
  * deeper than the goal the clause answered (WI-20261115-0WT09). `maxSteps` is the FUEL: the
  * most steps the whole search may take, a negation's sub-search included. */
case class ResolveConfig(
  maxDepth: Int = 100,
  maxSolutions: Int = 0,  // 0 = unlimited
  simplify: Boolean = false,
  maxSteps: Long = ResolveConfig.DefaultMaxSteps
)

object ResolveConfig:
  /** The default fuel, rustland's `DEFAULT_MAX_STEPS`. */
  val DefaultMaxSteps: Long = 10_000_000L

/** A successful resolution result. */
case class Solution(
  subst: Substitution,
  residual: IndexedSeq[TermId]
)

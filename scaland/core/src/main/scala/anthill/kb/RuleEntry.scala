package anthill.kb

import anthill.term.TermId

// ── Rule handle ─────────────────────────────────────────────────

opaque type RuleId = Int

object RuleId:
  def fromIndex(idx: Int): RuleId = idx

  extension (id: RuleId)
    def index: Int = id

// ── Sort kind ───────────────────────────────────────────────────

enum SortKind:
  case Abstract, Defined, Constructor

// ── Rule entry (internal) ──────────────────────────────────────

private[kb] class RuleEntry(
  val head: TermId,
  val body: IndexedSeq[TermId],
  val sort: TermId,
  val domain: TermId,
  val meta: Option[TermId],
  // Number of distinct DeBruijn vars closed over head+body (WI-637). 0 for a
  // truly ground fact — those take the resolver's raw-bind fast path; arity>0
  // rules (incl. bodyless facts with vars) open through `withFreshVars`.
  val arity: Int = 0,
  var retracted: Boolean = false
)

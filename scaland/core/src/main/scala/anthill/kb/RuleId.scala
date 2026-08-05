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

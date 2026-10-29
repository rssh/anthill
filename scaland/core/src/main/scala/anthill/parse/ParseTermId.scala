package anthill.parse

import anthill.term.TermOf

/** The id of a term in a [[SimpleTermStore]]. It names a PLACE in the file: two terms
  * written alike are two ids. A knowledge-base [[anthill.term.TermId]] names a
  * STRUCTURE — its store is hash-consed, so terms built alike share one — and indexes
  * the other store. The two are separate types, so an id handed to the wrong store, or
  * to a table keyed by the other's ids, does not compile (`ParseTermIdTest`). */
opaque type ParseTermId = Int

object ParseTermId:
  /** Only the parse store issues one. */
  private[parse] def fromRaw(raw: Int): ParseTermId = raw

  extension (id: ParseTermId) private[parse] def index: Int = id

/** A term of the parse store: its children are [[ParseTermId]]s. */
type ParseTerm = TermOf[ParseTermId]

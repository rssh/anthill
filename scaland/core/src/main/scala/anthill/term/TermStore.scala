package anthill.term

import scala.collection.mutable.{ArrayBuffer, HashMap}

/** Hash-consed term store. Structurally identical terms share the same TermId.
  *
  * Unlike the Rust implementation, we skip reference counting — JVM GC handles it.
  * We still maintain the hash index for deduplication.
  */
class TermStore:
  private val terms = ArrayBuffer.empty[Term]
  private val hashIndex = HashMap.empty[Term, TermId]

  /** Allocate a term, deduplicating via hash-consing.
    * If an identical term already exists, returns the existing TermId.
    */
  def alloc(term: Term): TermId =
    hashIndex.getOrElseUpdate(term, {
      val id = TermId.fromRaw(terms.length)
      terms += term
      id
    })

  /** Get the term at the given id. */
  def get(id: TermId): Term = terms(id.index)

  /** Number of unique terms in the store. */
  def size: Int = terms.length

  def isEmpty: Boolean = terms.isEmpty

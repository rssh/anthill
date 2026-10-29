package anthill.parse

import scala.compiletime.testing.typeCheckErrors

/** WI-20260904-BZYQX — a parse id and a knowledge-base id are separate types.
  *
  * The parse store ([[SimpleTermStore]], one id per written node) and the hash-consed
  * [[anthill.term.TermStore]] (one id per structure) used to share `TermId`, so an id
  * handed to the wrong store compiled and indexed the wrong buffer. A term's children
  * are typed by the store too ([[anthill.term.TermOf]]), so a child read off a parse
  * term is a parse id as well.
  *
  * Each refusal is matched on its `Found` / `Required` pair, so a snippet that fails
  * for another reason does not pass; the positive case keeps the three from passing on
  * a typo in the snippet's names.
  *
  * BACK-OUT, measured under `core/clean` (`typeCheckErrors` runs at this file's compile
  * time, and zinc does not track what a snippet names), by aliasing `ParseTermId` back
  * to `anthill.term.TermId` — one id type for both stores, the state before the
  * ticket: the three refusal cases fail, each with `got List()`, and the positive case
  * passes. The first refusal names no new type, so it is also the state at the parent
  * commit, where `SimpleTermStore.get` took a `TermId`.
  */
class ParseTermIdTest extends munit.FunSuite:

  test("a knowledge-base id does not index the parse store") {
    val errors = typeCheckErrors(
      """(store: anthill.parse.SimpleTermStore, id: anthill.term.TermId) => store.get(id)""")
    assert(
      errors.exists(e =>
        e.message.contains("anthill.term.TermId") &&
          e.message.contains("Required: anthill.parse.ParseTermId")),
      s"a TermId must not index the parse store; got $errors")
  }

  test("a parse id does not index the knowledge base's store") {
    val errors = typeCheckErrors(
      """(kb: anthill.kb.KnowledgeBase, id: anthill.parse.ParseTermId) => kb.getTerm(id)""")
    assert(
      errors.exists(e =>
        e.message.contains("anthill.parse.ParseTermId") &&
          e.message.contains("Required: anthill.term.TermId")),
      s"a ParseTermId must not index the knowledge base; got $errors")
  }

  test("a child read off a parse term is a parse id") {
    val errors = typeCheckErrors(
      """(fn: anthill.term.Term.Fn[anthill.parse.ParseTermId]) =>
           val child: anthill.term.TermId = fn.posArgs(0)
           child""")
    assert(
      errors.exists(e =>
        e.message.contains("anthill.parse.ParseTermId") &&
          e.message.contains("Required: anthill.term.TermId")),
      s"a parse child must not read as a TermId; got $errors")
  }

  test("each store is read by its own id") {
    assertEquals(
      typeCheckErrors(
        """(store: anthill.parse.SimpleTermStore, id: anthill.parse.ParseTermId,
            kb: anthill.kb.KnowledgeBase, kid: anthill.term.TermId) =>
             (store.get(id), kb.getTerm(kid))"""),
      Nil)
  }

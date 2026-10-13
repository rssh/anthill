package anthill.load

import anthill.span.Span
import scala.collection.mutable.HashMap

/** Per-KB load history; never shared between independently loaded programs. */
private[anthill] class LoadBoundaryState:
  val declarations = HashMap.empty[String, Span]
  val sealedDeclarations = HashMap.empty[String, Span]
  val equality = HashMap.empty[String, Set[String]]
  val rows = HashMap.empty[String, HashMap[String, Span]]
  val providers = scala.collection.mutable.HashSet.empty[(String, String)]
  val operations = HashMap.empty[(String, String), HashMap[String, Span]]
  val parameters = HashMap.empty[String, IndexedSeq[String]]

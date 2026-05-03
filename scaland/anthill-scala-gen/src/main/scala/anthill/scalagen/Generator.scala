package anthill.scalagen

import anthill.codegen.scala.GeneratedFile
import anthill.kb.KnowledgeBase

/** Anthill → Scala KB-driven codegen (proposal 034 §`anthill-scala-gen`).
  *
  * Skeleton; body lands in a follow-up WI gated on a real consumer
  * (proposal 034 §5).
  */
object Generator:

  def generate(kb: KnowledgeBase): IndexedSeq[GeneratedFile] =
    IndexedSeq.empty

end Generator

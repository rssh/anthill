package anthill.codegen.scala

import anthill.intern.SymbolTable
import anthill.parse.{Rule, Constraint, Name}

/** Rules + constraints → ScalaCheck property file.
  *
  * v1 emits property *stubs* — the property body invokes the rule's
  * label (or a synthesized id) and uses `???` for the underlying
  * arbitrary, leaving body generation to the KB-driven gen. Tests
  * compile but the user must supply the arbitrary or skip the test.
  */
object LawsGen:

  def render(
    sortName: String, typeParams: IndexedSeq[String],
    rules: IndexedSeq[Rule], constraints: IndexedSeq[Constraint],
    packagePath: String, sym: SymbolTable
  ): String =
    val sb = StringBuilder()
    if packagePath.nonEmpty then sb ++= s"package $packagePath\n\n"
    sb ++= "import org.scalacheck.Properties\n"
    sb ++= "import org.scalacheck.Prop.forAll\n\n"
    sb ++= s"object ${sortName}Laws extends Properties(\"$sortName\"):\n"
    rules.zipWithIndex.foreach { case (r, i) =>
      val label = r.label.map(n => Names.scalaMethodName(sym.name(n.last))).getOrElse(s"rule_$i")
      sb ++= s"  property(\"$label\") = forAll { (_: Unit) => ??? : Boolean }\n"
    }
    constraints.zipWithIndex.foreach { case (c, i) =>
      val label = c.label.map(n => Names.scalaMethodName(sym.name(n.last))).getOrElse(s"constraint_$i")
      sb ++= s"  property(\"$label\") = forAll { (_: Unit) => ??? : Boolean }\n"
    }
    sb.toString

end LawsGen

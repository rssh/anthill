package anthill.codegen.scala

import anthill.intern.SymbolTable
import anthill.parse.{Rule, Constraint, Name}

/** Rules + constraints → ScalaCheck property file.
  *
  * v1 emits property *placeholders* — `Prop.passed` so the test
  * compiles and passes. Real bodies (rule term → boolean expression)
  * are KB-driven and land with `anthill-scala-gen`. Per
  * `docs/scala-forward-mapping.md` §1, `???` must never appear in
  * generated output.
  */
object LawsGen:

  def render(
    sortName: String, typeParams: IndexedSeq[String],
    rules: IndexedSeq[Rule], constraints: IndexedSeq[Constraint],
    packagePath: String, sym: SymbolTable
  ): String =
    val sb = StringBuilder()
    if packagePath.nonEmpty then sb ++= s"package $packagePath\n\n"
    sb ++= "import org.scalacheck.{Prop, Properties}\n\n"
    sb ++= s"object ${sortName}Laws extends Properties(\"$sortName\"):\n"
    val labelled =
      rules.zipWithIndex.map((r, i) => labelOf(r.label, "rule", i, sym)) ++
      constraints.zipWithIndex.map((c, i) => labelOf(c.label, "constraint", i, sym))
    labelled.foreach(label => sb ++= s"  property(\"$label\") = Prop.passed\n")
    sb.toString

  private def labelOf(label: Option[Name], fallback: String, idx: Int, sym: SymbolTable): String =
    label.map(n => Names.scalaMethodName(sym.name(n.last))).getOrElse(s"${fallback}_$idx")

end LawsGen

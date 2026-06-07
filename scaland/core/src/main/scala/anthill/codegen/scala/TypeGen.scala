package anthill.codegen.scala

import anthill.intern.SymbolTable
import anthill.parse.{TypeExpr, SortBinding}

/** TypeExpr → Scala type string. Uses the default `scala_std` type
  * mapping per `docs/scala-forward-mapping.md` table in §2 + §1.1.
  */
object TypeGen:

  def render(sym: SymbolTable, te: TypeExpr): String = te match
    case TypeExpr.Simple(n) =>
      mapPrelude(n.segments.map(sym.name).mkString("."))
    case TypeExpr.Parameterized(n, bindings) =>
      val base = mapPrelude(n.segments.map(sym.name).mkString("."))
      val args = bindings.map { sb => render(sym, sb.bound) }.mkString("[", ", ", "]")
      s"$base$args"
    case TypeExpr.Variable(_, _) =>
      // Anonymous type variable (e.g. `?A`) — unusual at type position;
      // fall back to a wildcard. The KB-driven gen will resolve these.
      "?"
    case TypeExpr.TupleType(fields) =>
      if fields.isEmpty then "Unit"
      else fields.map { case (_, ty) => render(sym, ty) }.mkString("(", ", ", ")")
    case TypeExpr.Arrow(params, ret, _) =>
      // Pure arrow in scala_std (effects shape result type for cc only).
      val ps = if params.isEmpty then "()" else params.map(render(sym, _)).mkString("(", ", ", ")")
      s"$ps => ${render(sym, ret)}"

  /** Map prelude type names to their Scala stdlib counterparts.
    * Mirrors the type_map facts in `stdlib/anthill/realization/scala_std.anthill`.
    * Unknown names pass through (project-defined sorts).
    */
  private def mapPrelude(qualName: String): String =
    val short = qualName.split('.').last
    short match
      case "Int64" => "Int"
      case "BigInt" => "BigInt"
      case "Float" => "Double"
      case "Bool" => "Boolean"
      case "String" => "String"
      case "Unit" => "Unit"
      case "Nothing" => "Nothing"
      case "List" => "List"
      case "Option" => "Option"
      case "Pair" => "Tuple2"
      case "Set" => "Set"
      case "Map" => "Map"
      case "Stream" => "LazyList"
      case _ => Names.scalaTypeName(short)

end TypeGen

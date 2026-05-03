package anthill.codegen.scala

/** Identifier conversion per `docs/scala-forward-mapping.md` §5. */
object Names:

  /** Anthill snake_case → Scala lowerCamelCase. Identifiers without
    * `_` pass through unchanged (already camelCase or single-word).
    * Reserved-word collisions get backticked.
    */
  def scalaMethodName(s: String): String =
    val converted = toCamel(s, firstLower = true)
    if isReserved(converted) then s"`$converted`" else converted

  /** Field names follow the same rule as method names — Scala field
    * naming convention is lowerCamelCase. */
  def scalaFieldName(s: String): String = scalaMethodName(s)

  /** Type / sort / entity names: target PascalCase. Anthill stdlib
    * usually writes entity names in lowercase (`some`, `none`, `pair`),
    * but Scala convention requires PascalCase for `enum` cases and
    * `case class` names. Single underscore-free identifiers are
    * upper-cased on the first letter; snake_case identifiers go
    * through `toCamel(firstLower = false)`. Reserved words get
    * backticked.
    */
  def scalaTypeName(s: String): String =
    val converted =
      if s.contains('_') then toCamel(s, firstLower = false)
      else if s.isEmpty || s.charAt(0).isUpper then s
      else s.charAt(0).toUpper + s.substring(1)
    if isReserved(converted) then s"`$converted`" else converted

  /** Split on `_`, lowercase the first segment, PascalCase each
    * subsequent segment. Identifiers without `_` returned unchanged. */
  def toCamel(s: String, firstLower: Boolean): String =
    if !s.contains('_') then s
    else
      val parts = s.split('_').filter(_.nonEmpty)
      if parts.isEmpty then s
      else
        val sb = StringBuilder()
        sb ++= (if firstLower then parts.head.toLowerCase else capitalize(parts.head))
        parts.tail.foreach(p => sb ++= capitalize(p))
        sb.toString

  private def capitalize(s: String): String =
    if s.isEmpty then s else s.charAt(0).toUpper + s.substring(1).toLowerCase

  /** Scala 3 reserved words that would collide with anthill identifiers. */
  private val reserved = Set(
    "abstract", "case", "catch", "class", "def", "do", "else", "enum",
    "export", "extends", "false", "final", "finally", "for", "given",
    "if", "implicit", "import", "lazy", "match", "new", "null", "object",
    "override", "package", "private", "protected", "return", "sealed",
    "super", "then", "this", "throw", "trait", "true", "try", "type",
    "using", "val", "var", "while", "with", "yield"
  )

  private def isReserved(s: String): Boolean = reserved(s)

end Names

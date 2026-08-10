package anthill.codegen.scala

/** Identifier conversion per `docs/scala-forward-mapping.md` §5. */
object Names:

  /** The hyphen rule (§5, WI-1054), applied FIRST at every entry point below.
    *
    * An anthill identifier is `[a-zA-Z_][a-zA-Z0-9_-]*` (`Tokens.identToken`), so `-`
    * is the ONE character it admits that Scala does not — and it is not a character
    * Scala merely dislikes: `def zero-val(): T` parses as `zero` applied to an
    * operator, i.e. the emitter produced text that is not the language. numeric.anthill
    * writes `zero-val` and its emission failed to PARSE under dotc (WI-1020's harness).
    *
    * `-` IS TREATED AS `_` RATHER THAN GETTING ITS OWN CONVENTION, so `zero-val` and
    * `zero_val` reach Scala as the same name. That is what lets §5's per-kind table stay
    * the single authority on what an identifier becomes: normalize, then convert by
    * kind. An operation is camelCased (`zeroVal`), a sort PascalCased (`ZeroVal`), a
    * package segment left as it stands (`zero_val`) — and the underscore §1.1 promises
    * is what survives in exactly the position §1.1 is written about.
    *
    * ONE PRIVATE SITE, and [[toCamel]] is private for the same reason: a caller that
    * reached a conversion without passing through here would re-open the defect for
    * whichever identifier kind it handles.
    */
  private def normalize(s: String): String = s.replace('-', '_')

  /** Anthill snake_case → Scala lowerCamelCase. Identifiers with neither
    * `_` nor `-` pass through unchanged (already camelCase or single-word).
    * Reserved-word collisions get backticked.
    */
  def scalaMethodName(s: String): String =
    val converted = toCamel(normalize(s), firstLower = true)
    if isReserved(converted) then s"`$converted`" else converted

  /** Field names follow the same rule as method names — Scala field
    * naming convention is lowerCamelCase. */
  def scalaFieldName(s: String): String = scalaMethodName(s)

  /** Type / sort / entity names: target PascalCase. Anthill stdlib
    * usually writes entity names in lowercase (`some`, `none`, `pair`),
    * but Scala convention requires PascalCase for `enum` cases and
    * `case class` names. Single-word identifiers are upper-cased on the
    * first letter; anything the hyphen rule leaves with a `_` goes
    * through `toCamel(firstLower = false)`. Reserved words get
    * backticked.
    */
  def scalaTypeName(raw: String): String =
    val s = normalize(raw)
    val converted =
      if s.contains('_') then toCamel(s, firstLower = false)
      else if s.isEmpty || s.charAt(0).isUpper then s
      else s"${s.charAt(0).toUpper}${s.substring(1)}"
    if isReserved(converted) then s"`$converted`" else converted

  /** A `namespace` segment, as it appears in a `package` clause and in the
    * `src/main/scala/…` directory the file is written to (§1.1, §2.1).
    *
    * THE HYPHEN RULE IS THE WHOLE CONVERSION here, and that is §5's table rather than
    * an omission: a namespace segment is already lowercase and already idiomatic for a
    * Scala package (`prelude`, `realization`), so `my-ns` becomes `my_ns` and NOT
    * `myNs` — camelCasing it would rename every package in the tree for no reason and
    * split `my_ns` from `my-ns`, which anthill treats as two spellings of one thing
    * everywhere else.
    *
    * NO RESERVED-WORD BACKTICKING, unlike the two above: a package segment is also a
    * DIRECTORY name (`pathToDir`), and a backticked `` `type` `` would put backticks in
    * the emitted path. `namespace type` is already broken output today, unchanged by
    * this rule; refusing it needs a span this function does not have, so it is a
    * separate rule with its own case to make. `docs/scala-forward-mapping.md` §5 records
    * the exception next to the backticking rule it is an exception to.
    */
  def scalaPackageSegment(s: String): String = normalize(s)

  /** A whole package PATH, from the segments a `Name` carries.
    *
    * THE JOIN LIVES HERE and not at each caller (WI-1054 review): `namespacePath`,
    * `splitPath` and `importedNames` each build a package string from segments, and
    * three copies of `map(scalaPackageSegment).mkString(".")` is three chances for a
    * fourth caller to forget the `map` and hand a hyphen back to the emitter. The
    * segment-level entry point stays for [[Bootstrap]]'s namespace arithmetic, which
    * splits parent from leaf and so needs the segments individually.
    */
  def scalaPackagePath(segments: Seq[String]): String =
    segments.map(scalaPackageSegment).mkString(".")

  /** The same rule for a path a caller already holds JOINED — `ScalaTypes`'
    * `autoImportPackage`, which arrives as one dotted string.
    *
    * SAFE ON A DOTTED STRING because the rule is character-wise and `.` is not the
    * character it rewrites, so this and [[scalaPackagePath]] agree by construction
    * rather than by two implementations happening to match. It exists because the
    * alternative at the call site is `split('.')`, which turns a total function into
    * one with an empty-string edge case.
    */
  def scalaPackagePathOf(dotted: String): String = normalize(dotted)

  /** Split on `_`, lowercase the first segment, PascalCase each
    * subsequent segment. Identifiers without `_` returned unchanged.
    *
    * PRIVATE: every conversion must enter through one of the entry points above, which
    * apply [[normalize]] first. A caller reaching this directly would see a `-` fall
    * through as an ordinary character and emit it verbatim.
    */
  private def toCamel(s: String, firstLower: Boolean): String =
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
    if s.isEmpty then s else s"${s.charAt(0).toUpper}${s.substring(1).toLowerCase}"

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

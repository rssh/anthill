package anthill.codegen.scala

import anthill.kb.KnowledgeBase
import anthill.parse.ParsedFile

/** The two tables a written PRELUDE name is placed against, resolved from outside the
  * emitter (WI-1060).
  *
  * A prelude name has exactly two ways to have a Scala counterpart at all, and WI-1021
  * decided which is which by asking whether anthill can BUILD a value of the sort: a
  * scalar cannot (`Int64` declares no `entity` and nothing but a literal makes one), so
  * the host type IS the carrier; every other prelude sort has anthill constructors or a
  * provider-chosen carrier, and Bootstrap emits a Scala declaration for it which is then
  * what a written occurrence denotes. `docs/scala-forward-mapping.md` §2.1a.
  *
  * TWO FIELDS AND NOT ONE MAP, because they are consulted at DIFFERENT points of
  * [[TypeScope.place]] — [[hostScalar]] above the enclosing sort, [[preludeSort]] below it
  * and below the file's own types — and a single combined lookup cannot express that.
  * `int64.anthill`'s `operation compare(a: Int64, b: Int64) -> Int64` is over the CARRIER,
  * not over the `trait Int64` that same file emits. Where a name is in both — every
  * scalar is, since the prelude declares it — the scalar wins, by [[preludeSorts]]
  * rather than by luck of lookup order.
  *
  * THE TWO HALVES COME FROM DIFFERENT SOURCES, and that is the content of WI-1060 rather
  * than an accident of plumbing:
  *
  *  - `hostScalars` is a PROFILE decision and comes from the KB
  *    ([[ScalaProfile.typeMap]]). `Int64 -> Long` is scala_std's choice — rust_std says
  *    `i64`, cpp_std `int64_t` — and a profile is entitled to another one.
  *  - `autoImportedTypes` is a FACT ABOUT THE PRELUDE'S OWN FILES and is derived by
  *    parsing them ([[Bootstrap.emittedTypes]]). That `List` takes one type parameter is
  *    not something a profile could disagree with; it is what `list.anthill` declares. The
  *    hand-written table this replaced was a copy of `Bootstrap.sortTypeParams`' own
  *    answer with nothing cross-checking it — give a sort a new parameter and every
  *    consumer was refused with a message reading as if the DECLARATION were wrong.
  *
  * WHAT THE FACT SCHEMA COULD NOT SAY, which is the design question the ticket left open:
  * `TypeMapping(anthill_type, host_type)` has no arity column and no host name to put in
  * the one it has, so the prelude-sort half has no counterpart there. Growing the schema
  * was the alternative; deriving is better because the derivation cannot drift from the
  * declaration it copies, and because it answers the MEMBERSHIP question for free — every
  * sort the prelude emits is in the table, not the six that happened to have had a host
  * entry, so `Eq`, `Iterable` and the rest stop falling through to [[Placement.Ambient]]
  * (which qualifies with the DECLARING file's package: right for a prelude file, a guess
  * for a project consumer).
  */
case class ScalaTypes(
  /** Anthill leaf name → the fully-qualified host type its values ARE. No arity column,
    * because a scalar has no parameters to have an arity of. */
  hostScalars: Map[String, String],
  /** The anthill package a bare name reaches WITHOUT an import — `anthill.prelude`.
    *
    * A FIELD and not a constant, because two different questions read it and both must
    * get the same answer: which of the passed files' declarations enter
    * [[autoImportedTypes]] ([[Bootstrap.emittedTypes]] filters on it), and whether an
    * explicit `import` in a consumer file NAMES this same package or another one
    * ([[TypeScope.place]]). Split, a caller could resolve a table for one package and
    * have imports judged against another. */
  autoImportPackage: String,
  /** Anthill leaf name → the type the auto-imported files EMIT for it, with the
    * parameters that declaration writes. `_root_`-anchored, for the same reason the
    * scalars are: a relative `anthill.prelude.Option` is capturable by a project that
    * emits into a package with an `anthill` member of its own.
    *
    * EVERY emitted type, scalars included — this is what the files say, before any
    * question of what a written name should denote. [[preludeSorts]] is the answer to
    * the second question. */
  autoImportedTypes: Map[String, Placement.Known],
  /** Names the auto-imported files DECLARE and Bootstrap emits no Scala type for — a
    * namespace-level `sort Type = ?`, whose Scala spelling would be an `opaque type`
    * needing an enclosing object rather than a package.
    *
    * The cross-file half of WI-1055 B1, which had no carrier before this table existed:
    * inside sort.anthill a bare `Type` was already refused (the file's own
    * `FileTypes.declaredNotEmitted`), while the same name from ANY other file fell to
    * [[Placement.Ambient]] and emitted `<consumer pkg>.Type` — a bare identifier naming
    * nothing in the tree, which is the defect B1 was filed for. */
  autoImportedNotEmitted: Set[String]
):

  // A `type_map` entry may only name a sort with NO parameters, and this is the check
  // that says so rather than a comment hoping for it. `preludeSorts` subtracts the
  // scalars, so an entry naming a parameterized sort DELETES that sort's arity from the
  // table and re-adds it as a 0-parameter host type: every `List[T = X]` in the corpus is
  // then refused with "`List` maps to Scala `scala.List` and declares 0 type
  // parameter(s), but 1 were written" — a message blaming the USE SITE for a bad fact
  // entry, which is the reading WI-1060 exists to remove. `List -> Vec`/`List -> List` is
  // not a hypothetical: rust_std.anthill carries it today and scala_std did until WI-1021.
  private val parameterizedScalars: Vector[String] =
    hostScalars.keys.toVector.sorted.flatMap(leaf =>
      autoImportedTypes.get(leaf).filter(_.kinds.written > 0)
        .map(k => s"`$leaf` -> `${hostScalars(leaf)}`, but the auto-imported files " +
                  s"declare it with ${k.kinds.written} type parameter(s)"))
  if parameterizedScalars.nonEmpty then
    throw IllegalArgumentException(
      "the profile's type_map names a PARAMETERIZED sort as a host scalar: " +
      parameterizedScalars.mkString("; ") +
      ". A scalar is a sort anthill can build no value of, so it has no parameters to " +
      "carry; an entry for a parameterized sort would replace the declared arity with " +
      "zero and refuse every written occurrence of it (WI-1021)")

  /** What a written name is actually placed by: [[autoImportedTypes]] MINUS the
    * scalars.
    *
    * The subtraction is the whole of WI-1021's inversion, stated once and structurally
    * instead of relying on a lookup ORDER to hide the loser. `int64.anthill` really does
    * declare `sort Int64` and Bootstrap really does emit a `trait Int64` for it — but no
    * value inhabits that trait, every consumer of the anthill name means `Long`, and an
    * entry pointing at it could only ever be the wrong of two answers. The hand-written
    * table this replaced kept the two disjoint by having six entries somebody chose; a
    * DERIVED table has the scalars in it, so the exclusion has to be said.
    *
    * `place`'s ordering is still load-bearing and this does not replace it: the scalar
    * has to beat the ENCLOSING sort and the file's own types too, which are the same
    * declaration reached by two other routes. */
  private val preludeSorts: Map[String, Placement.Known] =
    autoImportedTypes -- hostScalars.keySet

  /** The scalar half. Consulted ABOVE the enclosing sort: read the other way round,
    * `int64.anthill` emitted `def compare(a: Int64, b: Int64): Int64` against a trait no
    * value inhabits, while every consumer of the same anthill name got `Long` — one name
    * denoting two unrelated Scala types, surviving inside the five files that declare a
    * scalar. */
  def hostScalar(anthillLeaf: String): Option[Placement.Known] =
    hostScalars.get(anthillLeaf).map(Placement.Known(_, ParamKinds.none))

  /** The prelude-sort half. Consulted BELOW the enclosing sort and the file's own types —
    * a file that declares the name emits it, and its own spelling is the one to use. */
  def preludeSort(anthillLeaf: String): Option[Placement.Known] =
    preludeSorts.get(anthillLeaf)

  /** The refusal half of the same table: an auto-imported file declares the name and
    * emits nothing for it, so no spelling reaches it from anywhere. */
  def preludeNotEmitted(anthillLeaf: String): Option[Placement] =
    if autoImportedNotEmitted.contains(anthillLeaf) then
      Some(Placement.Unplaceable(
        s"`$anthillLeaf` is declared by the auto-imported `$autoImportPackage` in a " +
        "position Bootstrap emits no Scala type for (an abstract sort has no " +
        "declaration in the output), so the name is not in the emitted tree"))
    else None

object ScalaTypes:

  /** Resolve both tables: the scalars from a loaded profile, the prelude sorts from the
    * prelude's own parsed files.
    *
    * `autoImported` is the file set whose declarations a consumer reaches WITHOUT writing
    * an import. Only the declarations emitted into `autoImportPackage` itself are taken
    * from it — a nested `namespace anthill.prelude.algebra` is a package a bare name does
    * not reach, and entering its `Ring` here would place a project's own `Ring` against
    * it. Passing files that emit somewhere else entirely is therefore harmless rather
    * than silently wrong; what they declare is skipped.
    *
    * THROWS where [[ScalaProfile.typeMap]] returns a value, and the asymmetry is the same
    * one `languageVersion` draws: "does cobol have a scala profile?" is a fair question
    * with `no` for an answer, but a caller asking for the TABLES has already decided it
    * is emitting this profile, and no table this returned would be true.
    */
  def resolve(
    kb: KnowledgeBase, autoImported: Iterable[ParsedFile],
    autoImportPackage: String = "anthill.prelude",
    language: String = "scala", profile: String = "std"
  ): ScalaTypes =
    val scalars = ScalaProfile.typeMap(kb, language, profile) match
      case HostTypeMap.Declared(entries) => entries
      case other => throw IllegalStateException(
        s"no usable type_map for language `$language`, profile `$profile`: $other")
    val reachable = Bootstrap.emittedTypes(autoImported, autoImportPackage)
    ScalaTypes(scalars, autoImportPackage, reachable.types, reachable.declaredNotEmitted)

end ScalaTypes

package anthill.codegen.scala

import anthill.kb.KnowledgeBase
import anthill.parse.ParsedFile

/** The tables the emitter reads but must not derive itself (proposal 034), resolved
  * from outside it: the two a written PRELUDE name is placed against (WI-1060), and
  * the member table the `requires` → `extends` shadow check reads (WI-1065,
  * [[specMembers]] — not a placement table, a peer resolved one).
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
  *  - `packageTypes` is a FACT ABOUT THE PROJECT/PRELUDE FILES and is derived by parsing
  *    them ([[Bootstrap.emittedTypes]]). That `List` takes one type parameter is not
  *    something a profile could disagree with; it is what `list.anthill` declares. The
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
    * get the same answer: which package table supplies the fallback bare-name scope,
    * and whether an explicit `import` in a consumer file NAMES this same package or
    * another one ([[TypeScope.place]]). Split, a caller could resolve one fallback and
    * have imports judged against another.
    *
    * HELD IN CONVERTED (SCALA) FORM, normalized by [[resolve]] (WI-1054): both readers
    * compare it against a package string the emitter produced, and those are converted.
    * A raw `my-lib` here matches neither, so a hyphenated auto-import package would
    * empty the table AND turn every self-import into a false `Unplaceable`. */
  autoImportPackage: String,
  /** Scala package → the types the supplied files PROMISE to emit there, plus names
    * declared there for which Bootstrap emits no type. Every spelling is `_root_`
    * anchored. The map includes both the auto-imported files and the caller's complete
    * project file set, so a declaration's own/dotted-ancestor package can answer
    * before the auto-import package (WI-1067).
    *
    * PROMISE is precise: deriving this table cannot call `Bootstrap.generate`, because
    * generation itself needs the table. The caller must generate the same closure it
    * supplied to [[resolve]]; the mandatory Scala compilation of that closure catches a
    * refused declaring file as a missing `_root_` type. */
  packageTypes: Map[String, Bootstrap.PackageTypes],
  /** Anthill sort leaf → the member METHOD names its emitted trait would lend a
    * subtype, transitive over `requires` edges ([[Bootstrap.specMemberNames]],
    * WI-1065). Read by the `requires` → `extends` decision: a requirement whose
    * spec's members the declaring sort redeclares is a SHADOW (kernel §8.7, distinct
    * operations), and the supertrait that would merge the two into one Scala
    * override group is demoted to evidence. Derived from the same parsed closure as
    * [[packageTypes]], for the same reason: the collision is cross-file knowledge
    * proposal 034 keeps out of the emitter itself. */
  specMembers: Map[String, Set[String]]
):

  private val autoImported: Bootstrap.PackageTypes =
    packageTypes.getOrElse(autoImportPackage, Bootstrap.PackageTypes(Map.empty, Set.empty))

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
      autoImported.types.get(leaf).filter(_.kinds.written > 0)
        .map(k => s"`$leaf` -> `${hostScalars(leaf)}`, but the auto-imported files " +
                  s"declare it with ${k.kinds.written} type parameter(s)"))
  if parameterizedScalars.nonEmpty then
    throw IllegalArgumentException(
      "the profile's type_map names a PARAMETERIZED sort as a host scalar: " +
      parameterizedScalars.mkString("; ") +
      ". A scalar is a sort anthill can build no value of, so it has no parameters to " +
      "carry; an entry for a parameterized sort would replace the declared arity with " +
      "zero and refuse every written occurrence of it (WI-1021)")

  /** What an auto-imported written name is actually placed by: its package table MINUS the
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
    autoImported.types -- hostScalars.keySet

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

  /** The nearest declaration in the mentioning Anthill package or a dotted ancestor.
    *
    * The empty package is deliberately absent from a named package's parent chain:
    * Scala 3 does not make default-package members visible from named packages. The
    * spelling of an emitted type remains fully qualified because a generated top-level
    * `package a.b` clause does NOT make `a.Foo` bare-visible. Qualification makes the
    * selected declaration explicit and capture-free across both files and packages.
    *
    * POSITIVE AND NEGATIVE ENTRIES SHARE THIS WALK. Looking for an emitted type first
    * and a not-emitted declaration second would let an ancestor's concrete `Foo` jump
    * over a nearer abstract `Foo`, silently defeating normal shadowing.
    */
  def packagePlacement(pkg: String, anthillLeaf: String): Option[Placement] =
    PackageNesting.from(pkg).iterator.flatMap(exactPlacement(_, anthillLeaf)).nextOption()

  /** What ONE package says about a leaf, with no walk at all — what a QUALIFIED
    * occurrence asks (WI-1081), and the single rung [[packagePlacement]]'s chain is
    * built from, so a bare name and a written prefix cannot come to disagree about
    * what one package holds. */
  def exactPlacement(owner: String, anthillLeaf: String): Option[Placement] =
    packageTypes.get(owner).flatMap { table =>
      table.types.get(anthillLeaf).map(k => k: Placement).orElse {
        Option.when(table.declaredNotEmitted.contains(anthillLeaf)) {
          Placement.Unplaceable(
            s"`$anthillLeaf` is declared in package `$owner` by the supplied project " +
            "files in a position Bootstrap emits no Scala type for (an abstract sort " +
            "has no declaration in the output), so the name is not in the emitted tree")
        }
      }
    }

  /** Does the supplied closure put any declaration in this package or below it? — the
    * "does this namespace exist" question a written path's HEAD segment asks
    * ([[TypeScope.placeQualified]], WI-1081). Prefix-closed: `anthill` is a real package
    * whenever `anthill.prelude` holds a declaration, though nothing is declared in
    * `anthill` itself. */
  def packageExists(owner: String): Boolean =
    packageTypes.keysIterator.exists(p => p == owner || p.startsWith(s"$owner."))

  /** The refusal half of the same table: an auto-imported file declares the name and
    * emits nothing for it, so no spelling reaches it from anywhere. */
  def preludeNotEmitted(anthillLeaf: String): Option[Placement] =
    if autoImported.declaredNotEmitted.contains(anthillLeaf) then
      Some(Placement.Unplaceable(
        s"`$anthillLeaf` is declared by the auto-imported `$autoImportPackage` in a " +
        "position Bootstrap emits no Scala type for (an abstract sort has no " +
        "declaration in the output), so the name is not in the emitted tree"))
    else None

object ScalaTypes:

  /** Resolve the tables: the scalars from a loaded profile, the prelude sorts and the
    * spec member sets from the prelude's own parsed files.
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
    projectFiles: Iterable[ParsedFile] = Iterable.empty,
    autoImportPackage: String = "anthill.prelude",
    language: String = "scala", profile: String = "std"
  ): ScalaTypes =
    val scalars = ScalaProfile.typeMap(kb, language, profile) match
      case HostTypeMap.Declared(entries) => entries
      case other => throw IllegalStateException(
        s"no usable type_map for language `$language`, profile `$profile`: $other")
    // Both sets enter ONE package-keyed inventory. If a caller includes the prelude in
    // `projectFiles` too, identical spans make that repetition idempotent; two distinct
    // declarations at one (package, leaf) remain a located refusal. ONE closure value
    // for both derivations — the type table and the member table are only sound over
    // the SAME file set, so the shared input is structural, not coincidental.
    val closure = autoImported ++ projectFiles
    val reachable = Bootstrap.emittedTypes(closure)
    ScalaTypes(scalars, Names.scalaPackagePathOf(autoImportPackage),
      reachable.packages,
      Bootstrap.specMemberNames(closure))

end ScalaTypes

/** Anthill's dotted package lookup chain, nearest first (WI-1067).
  *
  * Named packages never include the empty package in the chain. For example `a.b.c`
  * selects among `a.b.c`, `a.b`, and `a`; the empty package sees only itself. This is
  * NOT a claim that a top-level Scala `package a.b.c` clause imports ancestor members:
  * cross-package selections are emitted fully qualified.
  */
private[codegen] object PackageNesting:
  def from(pkg: String): IndexedSeq[String] =
    if pkg.isEmpty then IndexedSeq("")
    else
      val segments = pkg.split('.').toIndexedSeq
      (segments.length to 1 by -1).map(n => segments.take(n).mkString("."))

package anthill.codegen.scala

import anthill.intern.SymbolTable
import anthill.parse.*
import anthill.span.Span

import scala.collection.mutable.ArrayBuffer

/** A single Scala source file emitted by the bootstrap codegen. */
case class GeneratedFile(relPath: String, contents: String)

/** What the scala-gen emitter raises. Two kinds, and the SPLIT IS THE SCOPE OF THE
  * FAULT (WI-1080) — which is what decides whether the run can continue.
  *
  * `(message, span)` and `render = span.render(message)`, the shape
  * [[anthill.parse.ParseError]] and [[anthill.load.LoadError]] already have: the
  * ONE located renderer, so which STAGE found a fault cannot change how its
  * location reads (WI-947). `render` is also `getMessage`/`toString`, for the
  * reason it is on those two — nothing in this tree calls a renderer by name, so
  * one reachable only by name is a seam with no user.
  */
sealed abstract class GenError(message: String, span: Span) extends RuntimeException:
  def render: String = span.render(message)
  override def getMessage: String = render
  override def toString: String = render

/** A DECLARATION Bootstrap refuses, because no Scala spelling of it would mean what
  * the anthill declaration means (WI-940).
  *
  * COLLECTED, not fatal (WI-1080): the fault is about this declaration, so its
  * siblings are unaffected and `generate` records it in [[Bootstrap.Generated]].
  * What matters is that the case stays loud — emitting the nearest legal Scala
  * instead is exactly the silent-wrong-output the refusals exist to remove.
  */
case class BootstrapError(message: String, span: Span) extends GenError(message, span)

/** The PROFILE is broken, which is not a fact about any declaration (WI-1080 review).
  *
  * `scala_std.anthill`'s `type_map` dropping the `Unit` entry breaks a rendering path
  * for every declaration that reaches it, and there is no source the user could fix at
  * the span it points to. FATAL — [[Bootstrap.attempt]] catches `BootstrapError` and
  * this is deliberately not one, so it escapes `generate` and no partial tree is built
  * against a profile already known to be broken. Recording it per declaration instead
  * would report one configuration fault N times and return output regardless, which is
  * the "emit anyway" this backend refuses everywhere else.
  */
case class ProfileError(message: String, span: Span) extends GenError(message, span)

/** Anthill → Scala bootstrap codegen (parse-IR-driven, no KB).
  *
  * v1 of the scala-gen pipeline per proposal 034. Walks a [[ParsedFile]]
  * and emits an sbt-shaped output tree:
  *
  *   src/main/scala/<package-path>/<Sort>.scala
  *   src/test/scala/<package-path>/<Sort>Laws.scala
  *
  * Mapping rules per `docs/scala-forward-mapping.md` §2; default
  * `scala_std` profile. Generated traits / enums / case classes
  * compile as-is with no method bodies (Scala traits accept abstract
  * members). Concrete companion objects with bodies are deferred to
  * the KB-driven `anthill-scala-gen` (proposal 034 §anthill-scala-gen).
  *
  * Out of scope for v1: KB-driven decisions, `Quoted` body inlining,
  * `scala_caps` / `scala_cats_effect` / `scala_zio` profiles,
  * `@anthillName` round-trip annotations, ScalaCheck arbitrary
  * derivation. Tests under `<Sort>Laws.scala` compile but invoke
  * `???` in their `Arbitrary` slot — opt out via `--skip-laws`.
  */
object Bootstrap:

  /** What one file's emission produced: the declarations that EMITTED, and the ones
    * that were REFUSED (WI-1080).
    *
    * BOTH HALVES ARE RETURNED because a refusal is scoped to ONE DECLARATION, and a
    * throw can carry only one of them. This deliberately revisits WI-1055's
    * abort-the-file choice, which was right about LOUDNESS and wrong about BLAST
    * RADIUS: `effects.anthill` declares eleven sorts in one namespace and exactly two
    * of them name `anthill.reflect`, so refusing at the file took the other nine with
    * them. `Modifiable` was among the nine, which left `MutableCollection`'s emitted
    * supertrait naming a type no file in the tree declared — a cascade into a file with
    * nothing wrong with it, and the last error in the whole-prelude closure.
    *
    * The failure MODE is unchanged and only its scope narrows. A refused declaration
    * emits nothing; [[emittedTypes]] still promises it (that walk renders no types, so
    * it cannot see the refusal); and the promise breaks at the consumer's mandatory
    * Scala compile — now naming the one missing `_root_` type instead of every type the
    * refused declaration's FILE happened to declare. Dropping `refusals` on the floor
    * is the one way to make this quiet, and nothing here does that for a caller.
    */
  case class Generated(
    files: IndexedSeq[GeneratedFile], refusals: IndexedSeq[BootstrapError])

  /** Generate Scala files from one parsed `.anthill` file. The package
    * path and per-file output is determined by the file's top-level
    * namespace (or sort/entity name when no namespace is present).
    *
    * `types` is a PARAMETER and has no default (WI-1060), for the reason
    * [[buildSbt]]'s `scalaVersion` has none: the scalar half of it is a decision
    * `scala_std.anthill` makes and the emitter has no business making a second
    * time. A default here would be that second answer, silently winning wherever a
    * caller forgot to ask — which is exactly how the hardcoded table this replaced
    * came to disagree with the fact for two releases. [[ScalaTypes.resolve]] is the
    * one way to build it; Bootstrap still reads no KB (proposal 034).
    *
    * STILL THROWS, for the two faults that are not about a declaration. `fileTypes`
    * refuses a leaf this file declares twice in one Scala package — a file whose own
    * name table contradicts itself can place nothing, so no declaration of it could
    * emit anyway — and a [[ProfileError]] says the profile is broken for every
    * declaration at once. Everything a DECLARATION does wrong rides in
    * [[Generated.refusals]].
    */
  def generate(pf: ParsedFile, types: ScalaTypes): Generated =
    val files = ArrayBuffer.empty[GeneratedFile]
    val refusals = ArrayBuffer.empty[BootstrapError]
    // The shadow table gets the same same-file complement `decls` gives the type
    // table: a required spec declared in THIS file is not in the resolved closure's
    // `specMembers` unless the caller listed the file there, and the rendering half
    // would see it while the shadow half did not — one emission's two halves
    // disagreeing about what the file declares (WI-1065 review).
    val env = FileEnv(fileTypes(pf.symbols, pf.items, ""), types,
      specMemberNames(Seq(pf), base = types.specMembers))
    emitItems(pf.symbols, pf.items, "", env, Map.empty, files, refusals)
    // SEQUENCED, not inlined into the constructor call: `refuseColliding` APPENDS to
    // `refusals`, so building `Generated` from both in one expression would be correct
    // only under left-to-right argument evaluation. Swapping the two arguments — or
    // reordering `Generated`'s fields — would drop every collision refusal from the
    // result with nothing to compile-fail on.
    val survivors = refuseColliding(files, refusals)
    Generated(survivors, refusals.toIndexedSeq)

  /** The declaration walk, shared by the file top level and every `namespace` body.
    *
    * ONE WALK because [[fileTypes]] mirrors these arms to record where each emitted type
    * lands, and it could only ever mirror one of them — held apart, the top-level loop
    * and the namespace loop were the same three cases written twice, and the type table
    * was hand-coupled to whichever copy a reader found first.
    */
  private def emitItems(
    sym: SymbolTable, items: Iterable[Item], packagePath: String, env: FileEnv,
    imports: Map[String, String], out: ArrayBuffer[GeneratedFile],
    refusals: ArrayBuffer[BootstrapError]
  ): Unit =
    items.foreach {
      case Item.NamespaceItem(ns) =>
        // NOT wrapped: a namespace is a CONTAINER, not a declaration. Its members each
        // stage their own emission through this same walk, and its `<Ns>Ops` trait
        // stages separately — wrapping the whole thing would discard members that
        // already emitted, which is the file-scoped bug one level down.
        emitNamespace(sym, ns, packagePath, env, imports, out, refusals)
      case Item.SortWithBodyItem(s) =>
        attempt(out, refusals)(emitSort(sym, s, packagePath, env, imports, _))
      case Item.EntityItem(e) =>
        attempt(out, refusals)(emitStandaloneEntity(sym, e, packagePath, env, imports, _))
      case _ => // facts/rules — TODO in KB-driven gen
    }

  /** Emit ONE declaration, or record its refusal and leave its siblings alone (WI-1080).
    *
    * STAGED rather than emitted straight into `out`, so that "refused" and "emitted
    * nothing" are the same state by construction. NO EMITTER NEEDS THIS TODAY — every
    * one of them appends its single `GeneratedFile` after the last thing that can
    * refuse, so a staged and an unstaged commit agree, and no test drives the
    * difference. It is here because the invariant is what a caller reads (`files` are
    * complete declarations) and the alternative failure is silent: an emitter that
    * grows a second `out +=` before its refusal would ship a half-emitted declaration,
    * which is worse than a refused one because it looks complete.
    *
    * `BootstrapError` ALONE and not `NonFatal`, nor its [[GenError]] parent: a refusal
    * is the emitter saying it cannot spell THIS CONSTRUCT, which is a fact about one
    * declaration. A [[ProfileError]] is a fact about the profile and stays fatal, and
    * any other throwable is a defect in the emitter — both must take the whole run
    * down rather than be recorded as if the source had asked for something impossible.
    *
    * The `refusals` ELEMENT TYPE is what enforces that, not this `catch`: widening the
    * catch to `GenError` on its own does not compile, so the distinction cannot be
    * eroded one site at a time.
    */
  private def attempt(
    out: ArrayBuffer[GeneratedFile], refusals: ArrayBuffer[BootstrapError]
  )(emit: ArrayBuffer[GeneratedFile] => Unit): Unit =
    val staged = ArrayBuffer.empty[GeneratedFile]
    try
      emit(staged)
      out ++= staged
    catch case e: BootstrapError => refusals += e

  /** Two emissions at ONE path is a refusal, not a last-writer-wins (WI-1054 review).
    *
    * `Names.scalaTypeName` is MANY-TO-ONE — `foo_bar` and `fooBar` already shared an
    * image, and normalizing `-` to `_` (§5) adds `foo-bar` to that class — so two
    * distinct anthill sorts can now want one `FooBar.scala`. Nothing downstream can see
    * it: `emittedTypes`' duplicate check is keyed on the ANTHILL leaf, so two different
    * leaves never collide there, and whatever writes the tree to disk keeps whichever
    * file it wrote last. The result is a silently missing declaration in a tree that
    * compiled green.
    *
    * ON THE OUTPUT and not on the name table, because the path is what actually
    * collides and every emission route reaches it — a sort, a standalone entity, and a
    * namespace's `<Ns>Ops` trait each build their own `relPath`, and a check on any one
    * of them would miss the other two.
    *
    * OVER THE SURVIVORS and BOTH SIDES DROPPED (WI-1080): it runs on what actually
    * emitted, so a declaration whose colliding twin was refused for its own reason no
    * longer collides with anything and ships. When the collision is real, neither side
    * ships — the emitter cannot choose between them, and keeping one would be the
    * last-writer-wins this exists to prevent, merely decided earlier.
    *
    * `Span.empty` AND NOT A BORROWED ONE, which is what that value is for ("a
    * diagnostic that genuinely has nowhere to point"): the fault is a RELATION between
    * two declarations, so neither of them is where a reader should be sent, and
    * pointing at one would say the wrong thing more confidently than saying nothing.
    * The path it names is what identifies both.
    */
  private def refuseColliding(
    files: ArrayBuffer[GeneratedFile], refusals: ArrayBuffer[BootstrapError]
  ): IndexedSeq[GeneratedFile] =
    val collisions = files.groupBy(_.relPath).filter(_._2.length > 1).keys.toVector.sorted
    collisions.foreach { path =>
      refusals += BootstrapError(
        s"two declarations emit to one path ($path). Scala " +
        "names are converted many-to-one (§5: `-` normalizes to `_`, then snake_case " +
        "camelCases), so distinct anthill names can converge — rename one of them",
        Span.empty)
    }
    files.filterNot(f => collisions.contains(f.relPath)).toIndexedSeq

  /** What one Scala package is promised by a parsed file set (WI-1067).
    *
    * `types` is keyed by the Anthill leaf a declaration writes; every Scala spelling is
    * `_root_`-anchored so the same table can serve a consumer in any package. The
    * negative set is the namespace-level abstract sorts Bootstrap deliberately emits no
    * declaration for.
    */
  case class PackageTypes(
    types: Map[String, Placement.Known], declaredNotEmitted: Set[String]
  )

  /** The package-keyed declaration promises made by a whole parsed file set. */
  case class EmittedTypes(packages: Map[String, PackageTypes]):
    def in(pkg: String): PackageTypes =
      packages.getOrElse(pkg, PackageTypes(Map.empty, Set.empty))

  /** Every type a set of files promises to emit, keyed first by Scala package and then
    * by Anthill leaf name (WI-1060/WI-1067).
    *
    * This is where [[ScalaTypes]]'s prelude half comes from, and the point is that it is
    * the SAME walk `generate` places a file's own names with — so the parameters a
    * consumer is checked against are the ones the declaring file actually emits, not a
    * hand-copy of them. The table this replaced was that copy, with nothing
    * cross-checking it and only three of its six entries pinned by a compile.
    *
    * `_root_`-ANCHORED, which qualification alone does not achieve: `anthill.prelude.Option`
    * is a RELATIVE path, so a project emitting into `myco` alongside a `myco.anthill`
    * namespace captures it. See [[ScalaTypes]].
    *
    * PACKAGE-KEYED rather than filtered to the auto-import package: `ScalaTypes` needs
    * the exact package for two distinct lookups. A declaration's own package (or its
    * nearest dotted Anthill ancestor package) answers first; only then does the designated
    * auto-import package answer. Thus a project's sibling-file `Pair` can beat the
    * prelude's without making `anthill.prelude.algebra.Ring` visible from `my.app`.
    *
    * A LEAF DECLARED TWICE in ONE package is a refusal rather than last-wins. The same
    * leaf in two packages is legal because the package lookup selects which declaration
    * a mentioning scope can reach. Listing the exact same parsed file twice is
    * idempotent: its declaration has the same source span, so it is one input repeated,
    * not two declarations.
    *
    * THIS IS A PROMISE, not a second emission pass. Building the table by calling
    * `generate` would be circular (`generate` needs this table), so a caller must emit
    * the same parsed closure it supplies here. A REFUSED DECLARATION then breaks its own
    * promise loudly: it reaches no output closure, and a consumer's mandatory Scala
    * compilation reports that one missing `_root_` type. Since WI-1080 the break is
    * exactly that narrow — the refused declaration's siblings emit, so a file is no
    * longer promised whole and delivered empty. The refusal-set test names every refused
    * declaration; this table does not pretend it successfully emitted them.
    */
  def emittedTypes(files: Iterable[ParsedFile]): EmittedTypes =
    val all = files.foldLeft(FileTypes.empty) { (acc, pf) =>
      acc.merge(fileTypes(pf.symbols, pf.items, ""))
    }
    val packageNames =
      (all.types.keysIterator.map(_._1) ++ all.declaredNotEmitted.keysIterator.map(_._1)).toSet
    EmittedTypes(packageNames.iterator.map { pkg =>
      val types = all.types.collect { case ((owner, leaf), t) if owner == pkg =>
        val known: Placement.Known = Placement.Known(t.qualified, t.kinds)
        leaf -> known
      }
      val missing = all.declaredNotEmitted.collect {
        case ((owner, leaf), _) if owner == pkg => leaf
      }.toSet
      pkg -> PackageTypes(types, missing)
    }.toMap)

  /** The operations an item list declares, block entries flattened — the ONE reading
    * shared by the emission sites and the shadow table, so an Item kind that starts
    * carrying operations cannot be taught to one and missed by the other (the drift
    * the table exists to prevent). */
  private def declaredOps(items: Iterable[Item]): IndexedSeq[Operation] =
    items.iterator.flatMap {
      case Item.OperationItem(op) => Iterator.single(op)
      case Item.OperationBlockItem(b) => b.entries.iterator
      case _ => Iterator.empty
    }.toIndexedSeq

  /** Every sort's member METHOD names, transitive over its `requires` edges — the
    * table [[requiresMapping]] reads to keep a shadowed requirement out of the
    * `extends` clause (WI-1065).
    *
    * WHY A TABLE AT ALL: whether `FiniteCollection.map` collides with a member of the
    * `Iterable` it requires is a fact about ANOTHER file, and proposal 034 gives
    * `generate` one `ParsedFile` and no KB. Like [[emittedTypes]], the answer is
    * derived by the caller from the same parsed closure and supplied as a value
    * ([[ScalaTypes.specMembers]]), so it cannot drift from the declarations it copies.
    * `base` is that supplied table when THIS call derives a single file's complement
    * on top of it (`generate`): edges resolve against the merged view, and the result
    * carries both — the same same-file complement `FileEnv.decls` gives the type
    * table. `base` entries are already transitively closed, so they seed the fixpoint
    * and pass through unchanged.
    *
    * EMITTED METHOD NAMES, not anthill spellings: the override group Scala forms is
    * over what [[Names.scalaMethodName]] produces, so `zero-val` and `zero_val` are
    * one name here exactly as they are in the output (WI-1054).
    *
    * TWO STATED OVER-APPROXIMATIONS, both in the demotion-safe direction — each can
    * only ever DROP an `extends` that might have stayed, and a demoted requirement is
    * still recorded, as evidence (the third safe over-approximation, name-keying, is
    * [[requiresMapping]]'s and stated there):
    *  - keyed by LEAF name, so a leaf declared in two packages merges its member
    *    sets ([[emittedTypes]] can afford per-package keys because a USE site names
    *    one package; a `requires` head is resolved per-file by `TypeScope`, which
    *    this walk deliberately does not replicate);
    *  - transitive over EVERY `requires` edge, although an edge that is itself
    *    demoted (or is evidence over a non-carrier parameter) lends no members to
    *    the emitted trait.
    *
    * ONE BLIND SPOT IN THE OTHER DIRECTION, stated rather than filed under the safe
    * ones: a required spec NO supplied file declares (an Ambient name — a
    * hand-written or carrier-bound trait outside the generated closure) contributes
    * an EMPTY member set, so a shadow against it is missed and the `extends` is
    * KEPT. That errs toward the compile error this table exists to prevent, and it
    * is the same blind spot every Ambient name has: Bootstrap has not read the
    * declaration, so nothing per-file can know its members. A SAME-FILE spec is not
    * in this class — `generate`'s per-file complement covers it.
    */
  def specMemberNames(
    files: Iterable[ParsedFile], base: Map[String, Set[String]] = Map.empty
  ): Map[String, Set[String]] =
    case class Direct(ops: Set[String], requires: Set[String])
    val direct = scala.collection.mutable.Map.empty[String, Direct]
    def visit(sym: SymbolTable, items: Iterable[Item]): Unit =
      items.foreach {
        case Item.NamespaceItem(ns) => visit(sym, ns.items)
        case Item.SortWithBodyItem(s) if !s.isTypeParam =>
          val ops = declaredOps(s.items)
            .map(o => Names.scalaMethodName(sym.name(o.name.last))).toSet
          val reqs = s.items
            .collect { case Item.RequiresDeclItem(r) => headName(sym, r.typeExpr) }
            .flatten.toSet
          val leaf = sym.name(s.name.last)
          val prev = direct.getOrElse(leaf, Direct(Set.empty, Set.empty))
          direct(leaf) = Direct(prev.ops ++ ops, prev.requires ++ reqs)
          visit(sym, s.items) // nested sorts declare members of their own
        case _ => ()
      }
    files.foreach(pf => visit(pf.symbols, pf.items))
    // Fixpoint rather than a memoized descent: a `requires` cycle would hand the
    // descent a partial set to cache, and the table is ~50 keys of depth ≤ 4.
    var closed: Map[String, Set[String]] = direct.view.mapValues(_.ops).toMap
    var changed = true
    while changed do
      changed = false
      direct.foreach { case (leaf, d) =>
        val grown = closed(leaf) ++ d.requires.flatMap(r =>
          closed.getOrElse(r, Set.empty) ++ base.getOrElse(r, Set.empty))
        if grown.size > closed(leaf).size then
          closed = closed.updated(leaf, grown)
          changed = true
      }
    // Union per key, not replacement: a leaf in both (the file is itself in the
    // caller's closure, or shares its leaf with another package's sort) must stay
    // monotone — dropping a base member would flip a demotion back to a kept clause.
    base ++ closed.map((leaf, ms) => leaf -> (ms ++ base.getOrElse(leaf, Set.empty)))

  /** One type a file EMITS: where it goes, what Scala calls it, how it is parameterized,
    * and where it was written (which is what a cross-file refusal points at). */
  private case class EmittedType(pkg: String, scalaName: String, kinds: ParamKinds,
                                 span: Span):
    /** The spelling an outsider must write. */
    def qualified: String = if pkg.isEmpty then s"_root_.$scalaName" else s"_root_.$pkg.$scalaName"

  /** What Bootstrap knows about a whole parsed FILE, before any one declaration:
    * which types it EMITS (with their arity), and which names it declares and
    * emits nothing for. The second is not the complement of the first — it is the
    * set Bootstrap can point at and say "the emitted tree has no such type"
    * (WI-1055 B1).
    */
  private case class FileTypes(
    types: Map[(String, String), EmittedType],
    declaredNotEmitted: Map[(String, String), Span]
  ):
    def addEmitted(leaf: String, t: EmittedType): FileTypes =
      val key = t.pkg -> leaf
      existingSpan(key) match
        case Some(first) if first != t.span => FileTypes.refuseDuplicate(leaf, t.pkg, first, t.span)
        case _ => copy(types = types + (key -> t))

    def addNotEmitted(leaf: String, pkg: String, span: Span): FileTypes =
      val key = pkg -> leaf
      existingSpan(key) match
        case Some(first) if first != span => FileTypes.refuseDuplicate(leaf, pkg, first, span)
        case _ => copy(declaredNotEmitted = declaredNotEmitted + (key -> span))

    def merge(other: FileTypes): FileTypes =
      val withTypes = other.types.foldLeft(this) { case (acc, ((_, leaf), t)) =>
        acc.addEmitted(leaf, t)
      }
      other.declaredNotEmitted.foldLeft(withTypes) { case (acc, ((pkg, leaf), span)) =>
        acc.addNotEmitted(leaf, pkg, span)
      }

    private def existingSpan(key: (String, String)): Option[Span] =
      types.get(key).map(_.span).orElse(declaredNotEmitted.get(key))

  private object FileTypes:
    val empty: FileTypes = FileTypes(Map.empty, Map.empty)

    private def location(span: Span): String =
      if !span.hasLocation then "an unknown location"
      else if span.file.isEmpty then span.formatStart
      else s"${span.file}:${span.formatStart}"

    def refuseDuplicate(leaf: String, pkg: String, first: Span, second: Span): Nothing =
      val shownPkg = if pkg.isEmpty then "<empty>" else pkg
      throw BootstrapError(
        s"`$leaf` is declared twice in Scala package `$shownPkg`: the first declaration " +
        s"is at ${location(first)}, and this second declaration cannot be emitted to the " +
        "same package and name",
        second)

  /** One file's own names, plus the project-wide tables every file is rendered against. */
  private case class FileEnv(
    decls: FileTypes, scalaTypes: ScalaTypes,
    /** [[ScalaTypes.specMembers]] plus this file's own sorts ([[specMemberNames]]'
      * `base` merge) — the view [[requiresMapping]]'s shadow check reads, complete
      * for same-file required specs the resolved closure never saw. */
    specMembers: Map[String, Set[String]]
  ):

    private val fileTypePlacements: Map[(String, String), Placement.Known] =
      decls.types.view.mapValues { t =>
        val known: Placement.Known = Placement.Known(t.qualified, t.kinds)
        known
      }.toMap

    /** A [[TypeScope]] for one declaration, with the file-wide and project-wide fields
      * filled in. A factory rather than three call sites spelling them out — those are
      * the file's answer and never the declaration's, so a call site that could vary
      * them would be a way for one emission to disagree with the rest of its file. */
    def scopeAt(
      decl: String, declSpan: Span, pkg: String, imports: Map[String, String],
      enclosing: Option[EnclosingSort] = None,
      params: Map[String, ParamBinding] = Map.empty
    ): TypeScope =
      TypeScope(decl, declSpan, pkg, enclosing, params, fileTypePlacements, imports,
        decls.declaredNotEmitted.keySet, scalaTypes)

  /** The name environment of one parsed file, in ONE walk.
    *
    * `types` is keyed on what is EMITTED and not on what is declared, which is the
    * whole point: `declaredNotEmitted` holds the names this file declares and
    * Bootstrap emits nothing for, so a member typed by one is refused rather than
    * shipped naming a type that is not in the tree.
    *
    * An `AbstractSortItem` at NAMESPACE level is that second case — `sort Type = ?`
    * in sort.anthill, an opaque handle whose Scala spelling would be an `opaque
    * type`, which needs an enclosing object rather than a package. (Inside a SORT
    * the same item is a type PARAMETER, which is why only the namespace walk
    * collects it.)
    *
    * THE DECLARATION IS STILL DROPPED SILENTLY, and only its USES are loud. That
    * asymmetry is deliberate but is a debt, not a design: refusing the whole file
    * on an un-emittable declaration would take sort.anthill and effects.anthill out
    * of the tree even when nothing refers to the name, and the measured trade for
    * the analogous choice ([[Placement.Ambient]]) was thirteen files. An abstract
    * sort nothing references therefore produces no output and no diagnostic.
    *
    * IT TRACKS AND KEYS BY PACKAGE (WI-1060/WI-1067) because [[emittedTypes]] reads the same walk from
    * OUTSIDE the file, where the bare leaf is not a spelling that reaches anything. The
    * two package derivations — a nested namespace's, a dotted declaration's — are
    * [[namespacePath]] and [[splitPath]], the same two `emitNamespace` and `emitSort`
    * use, so the table names the package the emitter writes to and cannot drift from it.
    * `splitPath` shares that package with the emitter and recognizes a dotted
    * declaration whose prefix already names its enclosing namespace (`namespace
    * anthill.prelude { sort anthill.prelude.Concat … }`), so the path is not appended
    * twice. A same-package duplicate is rejected while two packages may carry the same
    * leaf; no namespace merge can silently overwrite either.
    *
    * COUPLED TO THE EMIT WALK BY HAND: the three arms here are the three [[emitItems]]
    * dispatches on, and the `case _` means `-Wconf:id=E029` cannot catch them drifting.
    * An `Item` kind that gains an emission without being taught here would fall through
    * to `Placement.Ambient`, which performs no arity check — quietly losing the
    * guarantee WI-1055 exists for, on exactly the type it should cover. (One walk to
    * mirror rather than two since WI-1080; before that the emitter dispatched in
    * `generate` AND in `emitNamespace`, and this comment could only name one of them.)
    */
  private def fileTypes(
    sym: SymbolTable, items: Iterable[Item], packagePath: String
  ): FileTypes =
    items.foldLeft(FileTypes.empty) {
      case (acc, Item.NamespaceItem(ns)) =>
        val inner = fileTypes(sym, ns.items, namespacePath(sym, ns, packagePath).childPath)
        acc.merge(inner)
      case (acc, Item.SortWithBodyItem(s)) if !s.isTypeParam =>
        val (pkg, scalaName) = splitPath(sym, s.name, packagePath)
        acc.addEmitted(sym.name(s.name.last),
          EmittedType(pkg, scalaName, paramKinds(sortTypeParams(sym, s)), s.name.span))
      case (acc, Item.EntityItem(e)) =>
        val (pkg, scalaName) = splitPath(sym, e.name, packagePath)
        acc.addEmitted(sym.name(e.name.last),
          EmittedType(pkg, scalaName, ParamKinds.none, e.name.span))
      case (acc, Item.AbstractSortItem(s)) =>
        // The PACKAGE is tracked for the same reason the emitted types' is: read from
        // outside the file, "which names are unreachable" is a question about one
        // package, and a nested namespace's abstract sort is not in it.
        acc.addNotEmitted(sym.name(s.name.last),
          splitPath(sym, s.name, packagePath)._1, s.name.span)
      case (acc, _) => acc
    }

  /** Anthill leaf name → the package an `import` brings it from, accumulated
    * down the nesting: a sort's imports add to its namespace's.
    *
    * THE KEY STAYS AS ANTHILL WROTE IT and only the VALUE is converted (WI-1054): the
    * key is looked up by [[TypeScope.place]] against a written occurrence, which is the
    * anthill name, while the value is compared against the emitted `pkg` — a
    * package-converted string. Converting one and not the other is what makes the
    * comparison meaningful: leave the value raw and a hyphenated namespace importing
    * from itself reads as an import from ELSEWHERE, and every name it brings in is
    * refused as unreachable.
    */
  private def importedNames(
    sym: SymbolTable, imports: IndexedSeq[Import], outer: Map[String, String]
  ): Map[String, String] =
    imports.foldLeft(outer) { (acc, imp) =>
      val path = imp.path.segments.map(sym.name)
      imp.kind match
        case ImportKind.Selective(names) =>
          val from = Names.scalaPackagePath(path)
          acc ++ names.map(n => sym.name(n.last) -> from)
        case ImportKind.Plain if path.length > 1 =>
          acc + (path.last -> Names.scalaPackagePath(path.dropRight(1)))
        // A wildcard names nothing in particular, and a single-segment plain
        // import names a package rather than a member; neither places a name.
        case _ => acc
    }

  /** A sort's type parameters, in declaration order — ALL of them, effect
    * parameters included.
    *
    * BOTH desugarings of a head parameter, which is WI-1055 A2: the parser turns
    * a SIMPLE parameter `V` into an `AbstractSort` (`sort V = ?`) and a
    * HIGHER-KINDED one `M[T]` into a `SortWithBody` MARKED `isTypeParam`
    * (`AnthillParser.desugarSortTypeParam`, mirroring rustland). Only the first
    * was collected, so `sort anthill.prelude.Monad[M[T]]` emitted `trait Monad:`
    * with no parameters at all and every member mentioning `M` was unbound.
    *
    * A nested `sort F { … }` that is NOT marked stays a concrete nested sort and
    * is not a parameter — the same distinction the loader draws.
    *
    * IT KEEPS THE ERASED ONES (WI-1062) rather than filtering them out here, and
    * that is load-bearing: an `effects E = ?` parameter is absent from the emitted
    * type but PRESENT in every written occurrence of the sort, so a use site is
    * checked and erased against this list while the emission is built from
    * `paramKinds(...).keepTypeArgs(...)`. Filtering at the source would leave
    * nothing able to say that `Stream[Element, E]` is a correct two-argument
    * application.
    *
    * A NAMED REQUIREMENT SLOT IS ONE OF THEM (WI-1022, proposal 058 §4.7): `requires
    * O: Ord[T]` declares a type parameter whose value is a chosen WITNESS, which is
    * how the comparator enters the type — `SortedSet[T = String, O = ByLength]` and
    * `SortedSet[T = String, O = Alphabetical]` are DIFFERENT types, and that
    * distinction is the whole point of naming the slot. It is collected HERE rather
    * than beside the `requires` handling because the question this list answers is
    * "which parameters does the emitted type have", and the answer must be the same
    * one [[fileTypes]] records for a consumer in another file: a slot counted inside
    * the sort and not outside it would make every sibling's `SortedSet[T, O]` an
    * arity refusal. `sort.items` is in SOURCE order and the written occurrences bind
    * positionally, so the binder list and `SortedSet[T = T, O = O]` agree by
    * construction rather than by a sort key chosen here.
    *
    * THE BOUND IS NOT HERE, and cannot be: it is the requirement's spec RENDERED,
    * which needs the `TypeScope` this list is used to build. [[emitSort]] renders it
    * and hands it back through [[TypeParamDecl.declWith]].
    */
  private def sortTypeParams(sym: SymbolTable, sort: SortWithBody): IndexedSeq[TypeParamDecl] =
    sort.items.collect {
      case Item.AbstractSortItem(s) =>
        TypeParamDecl(
          sym.name(s.name.last), s.name.span, IndexedSeq.empty, isEffect = s.isEffectRow)
      case Item.SortWithBodyItem(s) if s.isTypeParam =>
        TypeParamDecl(sym.name(s.name.last), s.name.span, sortTypeParams(sym, s))
      case Item.RequiresDeclItem(RequiresDecl(Some(binder), _, _)) =>
        TypeParamDecl(sym.name(binder.last), binder.span, IndexedSeq.empty)
    }

  /** Two binders of one name is a refusal, not a last-wins (WI-1022 review).
    *
    * THE SOURCES CAN NOW COLLIDE, which is what makes this reachable: a parameter
    * arrives either as a `sort T = ?` or as a named requirement slot ([[sortTypeParams]]),
    * and nothing relates the two spellings. `requires O: Ord[T]` beside a `sort O = ?`,
    * or two slots both named `O`, emit `enum X[T, O <: …, O <: …]` — not Scala at all —
    * and the BOUND of the first is silently lost besides, because `emitSort` keys the
    * bounds by anthill name and the later entry wins. A refusal at the second binder
    * costs the declaration; shipping it costs the reader a diagnostic about generated
    * text and drops a requirement with no diagnostic at all.
    *
    * AT THE SECOND BINDER and not at the sort header: both spellings carry their own
    * span, and the one a reader must edit is the repeat.
    */
  private def refuseDuplicateParams(
    sortLeaf: String, params: IndexedSeq[TypeParamDecl]
  ): Unit =
    params.foldLeft(Set.empty[String]) { (seen, p) =>
      if seen.contains(p.anthillName) then
        throw BootstrapError(
          s"sort `$sortLeaf` binds the type parameter `${p.anthillName}` twice — a " +
          "`sort` parameter and a named requirement slot are both binders (§2.7b), and " +
          "Scala admits one of a name, so the second would silently take the first's " +
          "bound",
          p.span)
      seen + p.anthillName
    }

  private def paramKinds(params: IndexedSeq[TypeParamDecl]): ParamKinds =
    ParamKinds(params.map(p => if p.isEffect then ParamKind.Effect else ParamKind.Type))

  /** One type parameter, as anthill wrote it and as Scala binds it.
    *
    * The BINDING form and the USE form differ for a higher-kinded parameter:
    * `M[T]` binds as `M[_]` and is used as `M`. Scala needs the kind at the
    * binder and forbids it at every mention.
    *
    * `isEffect` is the parse-IR mark `effects E = ?` carries (WI-1062). A
    * higher-kinded parameter is never one: `sort S[M[T, E]]` writes its members
    * with the binder grammar, which has no `effects` spelling — so `E` there is an
    * ordinary `sort E = ?`, which is exactly what makes delay.anthill's graded
    * monad refusable rather than silently erased.
    */
  private case class TypeParamDecl(
    anthillName: String, span: Span, members: IndexedSeq[TypeParamDecl],
    isEffect: Boolean = false
  ):
    val scalaName: String = Names.scalaTypeName(anthillName)
    /** `T`, `M[_]`, `F[_[_]]` — what goes between the sort's brackets. */
    def decl: String = scalaName + kindSuffix
    /** The binder with a NAMED requirement slot's upper bound attached (WI-1022):
      * `O <: _root_.anthill.prelude.Ord[T]`. The map is keyed on the ANTHILL name, as
      * every other parameter lookup is, because `Names.scalaTypeName` is many-to-one.
      * A parameter with no entry is an ordinary one and binds as it did. */
    def declWith(bounds: Map[String, String]): String =
      decl + bounds.get(anthillName).fold("")(b => s" <: $b")
    /** The same kind with the name erased, for a nested binder position. */
    private def anonymousKind: String = "_" + kindSuffix
    private def kindSuffix: String =
      // No `emitted` filter, and that is the claim above rather than an omission:
      // a member cannot be an effect parameter, because the binder grammar has no
      // `effects` spelling to mark one with.
      if members.isEmpty then ""
      else members.map(_.anonymousKind).mkString("[", ", ", "]")

  /** Project-level `build.sbt` for an output tree. Bootstrap is per-file, so
    * callers fold many `generate()` results into one tree and call this once
    * to write the project-global file — avoids the per-file last-write-wins
    * footgun.
    *
    * `scalaVersion` is a PARAMETER and has no default on purpose. Its source of truth is
    * the `scala_std` `LanguageMapping`'s `language_version`, read by
    * [[ScalaProfile.languageVersion]] — and a default here would be a second answer to a
    * question the profile already answers, silently winning whenever a caller forgot to
    * ask. This is not the same question as `build.sbt`'s `scala3Version`, which is what
    * scaland itself is COMPILED WITH; they agree today but are free not to.
    *
    * `Bootstrap` still reads no KB (proposal 034) — the caller resolves the profile and
    * passes the value in, which is what keeps this a pure function of its inputs.
    */
  def buildSbt(scalaVersion: String): GeneratedFile =
    GeneratedFile("build.sbt", s"scalaVersion := \"$scalaVersion\"\n")

  // ── Namespace ───────────────────────────────────────────────────

  /** Where one `namespace` header puts things: the package its own OPS trait is
    * emitted into, its leaf name, and the package path its members inherit.
    *
    * Extracted (WI-1060) because [[fileTypes]] walks the same nesting to record where
    * each emitted type lands, and a second copy of this arithmetic is how a derived
    * table comes to name a package the emitter never writes to.
    */
  private case class NamespacePath(parentPkg: String, leaf: String, anthillLeaf: String):
    def childPath: String = if parentPkg.isEmpty then leaf else s"$parentPkg.$leaf"

  private def namespacePath(
    sym: SymbolTable, ns: Namespace, packagePath: String
  ): NamespacePath =
    val written = ns.name.segments.map(sym.name)
    // WI-1054: every segment is a PACKAGE segment, so `my-ns` reaches the `package`
    // clause — and the directory `pathToDir` derives from it — as `my_ns`.
    //
    // [[NamespacePath.anthillLeaf]] is for the DIAGNOSTIC LABEL ALONE, and that is the
    // whole of it: a located refusal must quote the namespace as the source spells it.
    // It is NOT what the `<Ns>Ops` trait name is read from — `Names.scalaTypeName`
    // normalizes for itself and normalization is idempotent, so both leaves give the
    // same identifier. (An earlier comment here claimed otherwise; a third field with a
    // false rationale is what a later call site would pick the wrong leaf from.)
    val segs = written.map(Names.scalaPackageSegment)
    if segs.length == 1 then NamespacePath(packagePath, segs.head, written.head)
    else
      // `packagePath` is an ENCLOSING path, already converted by whichever call
      // produced it; only the segments this header writes are converted here.
      val parent = Names.scalaPackagePath(written.dropRight(1))
      NamespacePath(
        if packagePath.isEmpty then parent else s"$packagePath.$parent",
        segs.last, written.last)

  /** A namespace emits its members and, if it declares operations, ONE `<Ns>Ops` trait.
    *
    * The prologue is deliberately outside [[attempt]]'s reach: `namespacePath` and
    * `importedNames` are `Names` conversions and symbol lookups, and neither has a
    * refusal to raise. Nothing here can fail in a way that should cost the file, so
    * every failing path below is inside a staged unit and this function does not throw.
    */
  private def emitNamespace(
    sym: SymbolTable, ns: Namespace, packagePath: String, env: FileEnv,
    outerImports: Map[String, String], out: ArrayBuffer[GeneratedFile],
    refusals: ArrayBuffer[BootstrapError]
  ): Unit =
    val here = namespacePath(sym, ns, packagePath)
    val nsParentPkg = here.parentPkg
    val imports = importedNames(sym, ns.imports, outerImports)
    emitItems(sym, ns.items, here.childPath, env, imports, out, refusals)
    // Top-level operations inside a namespace land in a <NsName>Ops trait. ONE staged
    // unit for the lot of them, because they emit as one file: an operation Bootstrap
    // cannot render costs the whole trait (delay.anthill's `pure`, WI-1055) but not,
    // since WI-1080, the sorts declared beside it.
    val nsOps = declaredOps(ns.items)
    if nsOps.nonEmpty then attempt(out, refusals) { staged =>
      val typeName = Names.scalaTypeName(here.leaf) + "Ops"
      val scope = env.scopeAt(
        s"namespace `${here.anthillLeaf}`", ns.name.span, nsParentPkg, imports)
      val sb = StringBuilder()
      if nsParentPkg.nonEmpty then sb ++= s"package $nsParentPkg\n\n"
      sb ++= s"trait $typeName:\n"
      // NO EVIDENCE: a `requires` belongs to a sort, whose carrier it conditions
      // (kernel §8.7), and a namespace declares no carrier — so there is nothing here
      // for a `using` clause to carry (WI-1022).
      nsOps.foreach(op =>
        sb ++= s"  ${OpGen.renderAbstract(op, IndexedSeq.empty, scope, sym)}\n")
      staged += GeneratedFile(
        relPath = s"src/main/scala/${pathToDir(nsParentPkg)}$typeName.scala",
        contents = sb.toString)
    }

  // ── Sort (trait or enum) ────────────────────────────────────────

  private def emitSort(
    sym: SymbolTable, sort: SortWithBody, packagePath: String, env: FileEnv,
    outerImports: Map[String, String], out: ArrayBuffer[GeneratedFile]
  ): Unit =
    // Multi-segment top-level decl like `enum anthill.prelude.Option`:
    // treat the prefix as the package path and the last segment as the type.
    val (effectivePkg, sortName) = splitPath(sym, sort.name, packagePath)
    val written = sortTypeParams(sym, sort)
    refuseDuplicateParams(sym.name(sort.name.last), written)
    // WI-1062: the sort's own `effects E = ?` parameters are erased (§2.8a). They
    // are dropped from every EMITTED list — the binders and the `EnclosingSort`
    // arguments — and kept as `kinds`, which is what a written occurrence of this
    // sort is checked and erased against. ONE reading of "which slots survive"
    // (`keepTypeArgs`) serves both, so the binder list and a use site's argument
    // list cannot drift out of positional sync.
    val kinds = paramKinds(written)
    val typeParams = kinds.keepTypeArgs(written)
    val scope = env.scopeAt(
      s"sort `${sym.name(sort.name.last)}`", sort.name.span, effectivePkg,
      importedNames(sym, sort.imports, outerImports),
      enclosing = Some(EnclosingSort(
        sym.name(sort.name.last), sortName, written.map(_.scalaName), kinds)),
      params = written.map(p =>
        p.anthillName ->
          (if p.isEffect then ParamBinding.Effect
           else ParamBinding.Scala(p.scalaName, p.members.length))).toMap)
    val requires = sort.items.collect {
      case Item.RequiresDeclItem(r) =>
        SortRequirement(r,
          TypeGen.render(sym, r.typeExpr, scope.at(s"$sortName's `requires`", r.span)))
    }
    // WI-1022: a named slot's requirement is its parameter's UPPER BOUND, so the
    // binder list can only be built once the requirements are rendered — which needs
    // `scope`, which needs the parameter NAMES. The two-step is that dependency and
    // not an ordering preference: `sortTypeParams` answers "which parameters", this
    // answers "bounded by what". A slot binding a parameter that is not in the list
    // cannot happen — both readings collect the same `RequiresDeclItem`s.
    val bounds = requires.collect {
      case SortRequirement(RequiresDecl(Some(binder), _, _), rendered) =>
        sym.name(binder.last) -> rendered
    }.toMap
    val tpStr =
      if typeParams.isEmpty then ""
      else typeParams.map(_.declWith(bounds)).mkString("[", ", ", "]")
    val ops = declaredOps(sort.items)
    val shape = shapeOf(sym, sort.name, sort.items.collect { case Item.EntityItem(e) => e })
    // `typeParams` and not `written`: the carrier is chosen from the parameters that
    // SURVIVE erasure, through the one reading of which those are (`keepTypeArgs`).
    // Reading `written` and filtering it again here would be a second answer to that
    // question, and a parameter kind that erases for some new reason would make the
    // two disagree — the carrier would name a binder the emitted type does not have.
    val req = requiresMapping(
      sym, sym.name(sort.name.last), shape, typeParams, ops, requires, scope,
      env.specMembers)

    // Rules + constraints are NOT emitted from bootstrap. Their bodies
    // are semantic (rule term → ScalaCheck Boolean expression); the
    // parse-IR-only path can't render them, and emitting a placeholder
    // (Prop.passed / ???) is either vacuously green or a spec violation
    // (see docs/scala-forward-mapping.md §1, §2.9). Laws emission is
    // owned by the KB-driven anthill-scala-gen.
    val mainSrc = renderMainSort(sortName, tpStr, typeParams, req, ops, shape,
      effectivePkg, scope, sym)
    out += GeneratedFile(
      relPath = s"src/main/scala/${pathToDir(effectivePkg)}$sortName.scala",
      contents = mainSrc)

  // ── Standalone entity → case class ──────────────────────────────

  private def emitStandaloneEntity(
    sym: SymbolTable, e: Entity, packagePath: String, env: FileEnv,
    imports: Map[String, String], out: ArrayBuffer[GeneratedFile]
  ): Unit =
    val (effectivePkg, typeName) = splitPath(sym, e.name, packagePath)
    val pkg = if effectivePkg.isEmpty then "" else s"package $effectivePkg\n\n"
    val scope = env.scopeAt(
      s"entity `${sym.name(e.name.last)}`", e.name.span, effectivePkg, imports)
    val src = pkg +
      renderCaseClass(sym, typeName, tpStr = "", e.fields, extendsClause = "", scope)
    out += GeneratedFile(
      relPath = s"src/main/scala/${pathToDir(effectivePkg)}$typeName.scala",
      contents = src)

  // ── Sort shape (§6.3) ───────────────────────────────────────────

  /** Which ONE Scala declaration a sort body maps to.
    *
    * The three are DISJOINT by construction — a sort picks exactly one, and each
    * carries what its renderer needs — which is what keeps an eponymous sort
    * from reaching Scala as a data type AND a nested case of itself. cpp-gen
    * states the same contract over its three emission bands (WI-931,
    * `classify_namespace`); this is the same rule in the other backend.
    */
  private enum SortShape:
    /** `sort V { entity V(…) }` — the constructor IS the sort (§6.3 / WI-926),
      * so ONE `case class V(…)` and no `V.V`. */
    case Record(ctor: Entity)
    /** Constructors named differently from the sort → `enum S: case C1 …`. */
    case Sum(ctors: IndexedSeq[Entity])
    /** No constructors → `trait S` carrying the abstract operations. */
    case Algebra

  /** Classify a sort body per §6.3.
    *
    * Eponymy is keyed on the ANTHILL name, which is what §6.3 says ("keyed on
    * the name matching") and not on the emitted one: `Names.scalaTypeName` is
    * many-to-one — `foo_bar` and `fooBar` share an image — so two anthill names
    * that merely converge in Scala are not one symbol.
    */
  private def shapeOf(
    sym: SymbolTable, sortName: Name, ctors: IndexedSeq[Entity]
  ): SortShape =
    val sortLeaf = sym.name(sortName.last)
    val hasEponymous = ctors.exists(c => sym.name(c.name.last) == sortLeaf)
    if ctors.isEmpty then SortShape.Algebra
    else if !hasEponymous then SortShape.Sum(ctors)
    else if ctors.length == 1 then SortShape.Record(ctors.head)
    else
      // §6.3 admits an eponymous variant ALONGSIDE siblings ("an eponymous
      // variant is a sibling of the other variants of its sort", WI-946), and
      // Scala has no spelling for it: the sum and one of its cases would have to
      // be one name in one scope. `enum S: case S` does NOT say that — it
      // declares the nested `S.S` that §6.3 rules out, which is the very defect
      // this classification exists to remove. Refused loudly rather than emitted
      // wrong. The tree ships no sort of this shape (measured across stdlib).
      throw BootstrapError(
        s"sort '$sortLeaf' has a constructor of its own name alongside " +
        s"${ctors.length - 1} other constructor(s). §6.3 makes those ONE symbol, " +
        "which Scala cannot spell as both a sum and one of its cases",
        sortName.span)

  /** One `requires` declaration of a sort, as written and as rendered. Both halves
    * are needed and neither derives the other: the rendered string is what an
    * `extends` clause or a field-type comparison uses, and the written `TypeExpr` is
    * what the carrier question below is asked of — a Scala string has lost which of
    * its arguments the anthill declaration bound where. */
  private case class SortRequirement(decl: RequiresDecl, rendered: String):
    def span: Span = decl.span

  /** What a sort's `requires` declarations become in the emitted declaration: the
    * `extends` clause, the note recording why a requirement is not in it, and the
    * evidence every operation of the sort takes as a `using` clause (WI-1022).
    *
    * `ext` AND `evidence` PARTITION the requirements — a requirement is a supertrait
    * or it is evidence, never both and never neither. That is what makes the omitted
    * `extends` a mapping rather than a loss: an implementor of the emitted trait is
    * asked for exactly the dictionaries kernel §8.7 says the sort's bodies have.
    *
    * THE PARTITION IS OVER THE EMITTED SIGNATURES, so a sort with NO operations is
    * where it stops meaning anything: `evidence` is computed and there is no `def` to
    * put it on ([[renderMainSort]]'s `ops.isEmpty` arm). Nothing is lost that the
    * emission ever carried — no operation, no body, no evidence to supply — and the
    * note says so in its own words rather than promising a clause ([[carriedByNothing]]). */
  private case class RequiresMapping(
    ext: String, note: String, evidence: IndexedSeq[String])

  /** Map a sort's `requires` declarations onto its emitted declaration (§2.7a).
    *
    * A SORT-LEVEL `requires` IS NOT AN IS-A CLAIM. Kernel spec §8.7: it "conditions
    * every provision, and supplies every body's evidence" — it is the requirement
    * DICTIONARY. The is-a claim is `provides`. So `requires` → `extends` is right
    * only where the two coincide, namely where the required spec's carrier slot is
    * bound to the declaring sort's OWN carrier (`sort Ord { sort T = ?; requires
    * Eq[T] }` — ops take `a: T`, so `T` is Ord's carrier, and `trait Ord[T] extends
    * Eq[T]` says what the declaration says).
    *
    * ON A SORT WITH CONSTRUCTORS IT NEVER COINCIDES (WI-1064): the sort IS the
    * carrier, so a requirement can only be over some other parameter.
    * `finite_combinators.anthill` writes `requires FiniteCollection[C = SrcC, …]`
    * over its SOURCE parameter, while its claim about itself is the `provides
    * FiniteCollection[C = FiniteMappedStream, …]` three lines below. The `extends`
    * was built from the first, because `emitSort` reads `RequiresDeclItem` and
    * NOTHING reads `ProvidesClauseItem` — the is-a claim falls through a `case _`.
    * Measured symptom: `class Fmapped needs to be abstract, since it has 9
    * unimplemented members`. The two data shapes therefore answer the carrier
    * question from the SHAPE and never consult [[carrierOf]]; that is exact, not an
    * approximation, and this ticket does not reopen it.
    *
    * WITHOUT CONSTRUCTORS THE CARRIER MUST BE READ (WI-1066), and until it was, the
    * shape stood in for it: every algebra sort got the supertrait unconditionally.
    * That is right wherever the requirement is over the carrier (`trait Ord[T]
    * extends Eq[T]`) and wrong wherever it is over an ELEMENT, a KEY or a SCALAR —
    * three measured emissions, `trait Set[T] extends Eq[T]` (set.anthill:13, whose
    * real claim is the `provides Eq[T = Set]` eleven lines below), `trait Map[K, V]
    * extends Eq[K]` (map.anthill:16) and `trait VectorSpace[V, F] extends Ring[F]`
    * (algebra.anthill:65). All three COMPILE — a trait tolerates unimplemented
    * members — so neither `ScalaCompile` nor the refusal-set test could see them;
    * what ships is an obligation on every implementor that `sort Set` never
    * declared, sitting beside Set's own `eq(a: Set, b: Set)` as an overload.
    *
    * OVER THE CARRIER IS STILL NOT ENOUGH (WI-1065). A requirement whose spec the
    * sort REDECLARES a member of is a SHADOW: kernel §8.7 rules the two same-named
    * operations DISTINCT, not one operation refined — `FiniteCollection.map` returns
    * a `FiniteCollection` where `Iterable.map` returns a `Stream`, the spec's own
    * worked example. Scala's `extends` reads the same two declarations the other
    * way: matching members (same name, same parameter types — the return type is
    * not part of matching) form ONE override group, and RefChecks refuses the
    * incompatible return (E164, `error overriding method map in trait Iterable`).
    * The emitted clause would therefore assert exactly the relation the kernel
    * denies, so a shadowed requirement is demoted to EVIDENCE, recorded with the
    * members that shadow it ([[shadowNote]]). The collision is read from
    * [[FileEnv.specMembers]] — cross-file knowledge proposal 034 keeps out of
    * Bootstrap, supplied like every other resolved table (WI-1060), plus the
    * file's own sorts — and is keyed on emitted METHOD NAMES, an
    * over-approximation in the demotion-safe direction ([[specMemberNames]] holds
    * the other two): a same-name-different-params member would be a legal
    * overload, but dropping to evidence never breaks a compile and keeping the
    * clause can. The demotion guards ONE dimension — the sort's own members
    * against each requirement, which is the shadow relation kernel §8.7 names.
    * Two KEPT supertraits whose specs declare same-named members against EACH
    * OTHER are not compared: name sets cannot tell that apart from the legal
    * diamond (`Ord`'s `Eq[T]` and `PartialOrd[T]` both reach `PartialEq`'s
    * `eq`/`neq`, one inherited declaration and fine), and no corpus file writes
    * the conflicting shape. A sort that hits it gets Scala's own conflicting-
    * members error at the closure compile, named at the declaration.
    *
    * NOT A SILENT DROP, in any direction: a supertrait is the `extends` clause,
    * everything else is `using` EVIDENCE on every operation (WI-1022), and an
    * algebra sort's demotion is additionally RECORDED in the emitted source
    * ([[evidenceNote]], [[shadowNote]]) so the reader is told which of the two a
    * requirement became and why. A data sort's anonymous requirement is the one case
    * with no `using` of its own: it reaches Scala as the declared type of the
    * constructor field typed by it, and one that rides nowhere is refused
    * ([[checkDischarged]]).
    *
    * A NAMED SLOT IS NEITHER QUESTION (WI-1022, proposal 058 §4.7). `requires O:
    * Ord[T]` declares a type PARAMETER whose value is the chosen witness, so it is
    * carried by that parameter's upper bound ([[TypeParamDecl.declWith]]) in EVERY
    * shape — the carrier reading below is not consulted and cannot be, since the
    * requirement is over a parameter the author introduced for it. The bound is a
    * type and a body needs a value, so the witness is also `using O`: the evidence is
    * the slot itself, which is what keeps two orderings of one element type from
    * sharing an implementation as well as from sharing a type. This is also the data
    * shape's second discharge route — the bound is on the emitted declaration, so
    * `checkDischarged` is asked only about the anonymous ones.
    */
  private def requiresMapping(
    sym: SymbolTable, sortLeaf: String, shape: SortShape,
    typeParams: IndexedSeq[TypeParamDecl], ops: IndexedSeq[Operation],
    requires: IndexedSeq[SortRequirement], scope: TypeScope,
    specMembers: Map[String, Set[String]]
  ): RequiresMapping =
    if requires.isEmpty then RequiresMapping("", "", IndexedSeq.empty)
    else
      val anonymous = requires.filter(_.decl.binder.isEmpty)
      // Per shape: the supertraits, the note explaining every demotion, and which
      // ANONYMOUS requirements need a `using` dictionary of their own. The data
      // shapes need none — theirs is carried by the constructor FIELD typed by it,
      // which is a stronger position than a context parameter (it constrains the
      // VALUE and not only the bodies), and `checkDischarged` is what says so.
      val (supertraits, note, evidence) = shape match
        case SortShape.Algebra =>
          // A WITNESS SLOT IS NOT A CARRIER CANDIDATE (WI-1022), and the parameter
          // list has to be filtered before [[carrierOf]] reads its head: a named slot
          // is a parameter the AUTHOR introduced to hold a chosen provider (058
          // §4.7), never the thing the sort's operations are an algebra over. Written
          // before the sort's own `sort T = ?` it would otherwise BE the head, and
          // every anonymous requirement of that sort would then be judged against the
          // wrong carrier — silently, since both answers emit. No corpus sort writes
          // the shape; a fixture drives it.
          val witnesses = requires.flatMap(_.decl.binder).map(b => sym.name(b.last)).toSet
          val carrier = carrierOf(
            sym, sortLeaf, typeParams.filterNot(p => witnesses.contains(p.anthillName)), ops)
          val (overCarrier, notOverCarrier) =
            anonymous.partition(r => isOverCarrier(sym, r, carrier))
          val (shadowed, kept) = overCarrier.partitionMap { r =>
            val members = shadowedMemberNames(sym, r, ops, specMembers)
            if members.nonEmpty then Left((r, members)) else Right(r)
          }
          // "EVERYTHING THE `extends` CLAUSE DID NOT TAKE", by subtraction rather
          // than by re-deriving the two demotion reasons: a third reason to demote
          // would otherwise emit no clause AND no dictionary, which is the silent
          // loss the notes exist to prevent.
          (kept,
            shadowed.map((r, members) => shadowNote(r.rendered, members)).mkString +
              notOverCarrier.map(r =>
                evidenceNote(r.rendered, carrier, hasOps = ops.nonEmpty)).mkString,
            anonymous.toSet -- kept)
        case SortShape.Record(ctor) =>
          checkDischarged(sym, sortLeaf, IndexedSeq(ctor), anonymous, scope)
          (IndexedSeq.empty, "", Set.empty)
        case SortShape.Sum(ctors) =>
          checkDischarged(sym, sortLeaf, ctors, anonymous, scope)
          (IndexedSeq.empty, "", Set.empty)
      // Walking `requires` keeps SOURCE order, so the `using` clause lists the
      // dictionaries in the order the sort declares them.
      RequiresMapping(
        if supertraits.isEmpty then ""
        else s" extends ${supertraits.map(_.rendered).mkString(", ")}",
        note,
        requires.flatMap { r =>
          r.decl.binder match
            case Some(binder) => Some(Names.scalaTypeName(sym.name(binder.last)))
            case None => Option.when(evidence.contains(r))(r.rendered)
        })

  /** What an algebra sort's operations are an algebra OVER. */
  private enum Carrier:
    /** Self-representing (`Set`, `Map`): the operations take the SORT, and its type
      * parameters are content — element, key, value. */
    case TheSort(leaf: String)
    /** The sort's own carrier parameter (`FiniteCollection`'s `C`, `Ord`'s `T`). */
    case Param(param: String)

    /** The anthill name a requirement's argument must mention to be over it. */
    def mentionName: String = this match
      case TheSort(leaf) => leaf
      case Param(name) => name

    def describe: String = this match
      case TheSort(leaf) => s"`$leaf` itself (self-representing)"
      case Param(name) => s"its parameter `$name`"

  /** The carrier of a sort that declares no constructors.
    *
    * THIS IS RUSTLAND'S RULE, not a second one invented here:
    * `requires_edge_is_carrier_preserving` / `spec_is_self_representing`
    * (`kb/typing.rs`, WI-614) decide the identical question for member lending, and
    * the two halves below are theirs — "does ANY declared operation take the sort
    * ITSELF as a self-receiver parameter … a self-representing spec's carrier is the
    * spec, not a type-param", otherwise the carrier is "its first type-param — the
    * `provision_carrier_sort` convention, shared with the provides resolver".
    *
    * ANY operation, not the first: `set.anthill` declares `empty() -> Set` before
    * `insert(s: Set, x: T)`, and a RETURN of the sort is not a receiver. Reading only
    * the first operation would classify `Set` as carried by `T`.
    *
    * THE FIRST TYPE PARAMETER, not the one the operations happen to receive, and the
    * difference is what makes the no-operation sorts answerable rather than a special
    * case: `sort Eq` (eq.anthill:35) declares NO operations at all — it adds only the
    * reflexivity law — so it has no receiver to read, and `sort NonEq` /
    * `BoundedLattice` declare only nullary ones (`nonEqRefl() -> T`, `top() -> T`).
    * All three are carried by their sole parameter under this rule with nothing
    * special said about them, and all three keep the supertrait they had.
    *
    * THE PARAMETERS ARE THE EMITTED ONES, which is how an `effects E = ?` is skipped:
    * a carrier is a sort and an effect row is not one, and it does not survive to the
    * emitted type anyway (§2.8a). The caller passes the list `keepTypeArgs` already
    * built rather than the written one — see the note at the call site. No corpus sort
    * declares an effect parameter first, so this is a statement rather than a fix.
    *
    * IDENTITY IS BY LEAF NAME, as `shapeOf`'s eponymy test and `namesIn` also are, and
    * that is the anthill question rather than the Scala one: inside a sort body a bare
    * mention of the sort's own name means the sort (WI-1055 A3). It would misread a
    * parameter typed by a DIFFERENT sort of the same leaf name — which needs that other
    * sort to share the enclosing sort's own name, a shape no corpus file writes and one
    * anthill's own scoping resolves the other way. `TypeScope.place` is what draws the
    * distinction for rendering, and it cannot be borrowed here: it answers about the
    * EMISSION, so `sort String`'s `s: String` places as a host scalar although the
    * operation plainly receives the sort.
    *
    * NO TYPE PARAMETERS AT ALL ⇒ the sort itself, because there is nothing else it
    * could be. `sort Hello { requires anthill.cli.Main; operation main(…) }`
    * (rustland's CLI fixtures) is that shape. Rustland's function answers `false`
    * here — but it is asking whether the required spec lends its MEMBERS to this
    * receiver, and a marker spec has none to lend; the question here is whether the
    * emitted Scala type is a subtype, which for a marker is exactly what is meant.
    * See [[isOverCarrier]].
    */
  private def carrierOf(
    sym: SymbolTable, sortLeaf: String,
    typeParams: IndexedSeq[TypeParamDecl], ops: IndexedSeq[Operation]
  ): Carrier =
    val selfReceiver = ops.exists(_.params.exists(p => headName(sym, p.ty).contains(sortLeaf)))
    if selfReceiver then Carrier.TheSort(sortLeaf)
    else
      typeParams.headOption match
        case Some(p) => Carrier.Param(p.anthillName)
        case None => Carrier.TheSort(sortLeaf)

  /** The sort a written type APPLIES, or `None` where it names no sort at all (an
    * arrow, a tuple). Deliberately blind to the arguments — `s: Set` and a
    * hypothetical `s: Set[T = X]` are both a receiver of `Set`. */
  private def headName(sym: SymbolTable, te: TypeExpr): Option[String] = te match
    case TypeExpr.Simple(n) => Some(sym.name(n.last))
    case TypeExpr.Parameterized(n, _) => Some(sym.name(n.last))
    case _ => None

  /** Is this requirement over the declaring sort's own carrier — i.e. do the
    * requirement and the is-a claim coincide, so `extends` says what the declaration
    * says?
    *
    * A WEAKER TEST THAN THE REAL QUESTION, stated rather than hidden. The real
    * question is whether the required spec's CARRIER SLOT is bound to `carrier`, and
    * answering it means knowing which of `Ring[…]`'s parameters is its carrier — its
    * first, by the convention [[carrierOf]] quotes — which lives in the file that
    * declares `Ring`. Proposal 034 gives Bootstrap one `ParsedFile` and no KB; the
    * resolved type table (WI-1060) carries each prelude sort's parameter COUNT and
    * kinds, not their names, so it cannot say which named binding is the carrier
    * one. What is asked instead is whether the carrier is mentioned among the
    * requirement's arguments AT ALL.
    *
    * WHERE THE TWO DIFFER: a requirement naming the carrier in a NON-carrier slot
    * (`sort Foo { sort C = ?; sort E = ?; requires Bar[X = E, Y = C] }` where `Bar`'s
    * carrier is `X`) qualifies here and should not. No corpus file writes one, and
    * the weaker test is exact on every file that does: `Iterable[C = C, …]` mentions
    * `C`; `Ring[F]` does not mention `V`; `Eq[T]` inside `Set` does not mention
    * `Set`; `Eq[T = K]` inside `Map` does not mention `Map`.
    *
    * A REQUIREMENT WITH NO ARGUMENTS is over the carrier: it has no slot to be over
    * anything else. `requires anthill.cli.Main` is that shape — a marker with no
    * parameters and no members, whose whole content is the tag, and `trait Hello
    * extends Main` carries exactly the tag and nothing else. This is sound only
    * because a spec that DOES declare parameters cannot reach here written bare:
    * `TypeGen` refuses a partial application ("declares N type parameter(s), but 0
    * were written") before this runs. The one gap is a [[Placement.Ambient]] name,
    * whose declaration Bootstrap has not read and whose arity therefore goes
    * unchecked — the same blind spot every ambient name has.
    */
  private def isOverCarrier(
    sym: SymbolTable, req: SortRequirement, carrier: Carrier
  ): Boolean =
    val args = writtenArguments(req)
    args.isEmpty ||
      args.foldLeft(Set.empty[String])((acc, a) => acc ++ namesIn(sym, a))
        .contains(carrier.mentionName)

  /** The arguments a `requires` writes, or none where it writes a bare name.
    *
    * The two argument-less spellings answer as ONE — a `Simple` name is what the
    * parser mints for `requires Main`, and an empty binding list is what a
    * `Parameterized` would carry for the same thing — so the marker rule above cannot
    * depend on which node the grammar happened to build. (`parameterizedType` is a
    * `rep(1, …)`, so only the first occurs today; a guard admitting the other and then
    * refusing it would advertise a case it handles wrong.)
    */
  private def writtenArguments(req: SortRequirement): IndexedSeq[TypeExpr] =
    req.decl.typeExpr match
      case TypeExpr.Simple(_) => IndexedSeq.empty
      case TypeExpr.Parameterized(_, bindings) => bindings.map(_.bound)
      case _ =>
        // The grammar takes a full `typeExpr` after `requires`, so an arrow or a
        // tuple parses. Neither names a sort, so neither has a carrier slot and the
        // question above has no answer for it. Treating one as a marker emits `trait
        // Weird[T] extends (T) => T:`, which MEASURED does not even parse ("end of
        // toplevel definition expected but '=>' found") — so what the refusal buys is
        // not a rescued compile but a diagnostic AT the `requires` instead of a syntax
        // error in generated text, the same trade WI-1055 made everywhere else.
        throw BootstrapError(
          s"a `requires` must name a sort, and `${req.rendered}` does not, so it has " +
          "no carrier slot to compare against the declaring sort's carrier (§2.7a)",
          req.span)

  /** The comment an algebra sort's non-supertrait `requires` becomes — one frame for
    * both demotion reasons: the `requires` header, the reason lines, and the shared
    * tail naming what carries it instead. `reason` ends mid-sentence, flowing into the
    * tail's "What carries…".
    *
    * WHY A COMMENT AT ALL, once the requirement is no longer dropped. The `using`
    * clause says WHAT the operation needs and nothing about WHY the type does not say
    * it — and a reader of `trait Set[T]` who knows set.anthill writes `requires Eq[T]`
    * is owed the difference between "this is not a subtype of Eq" and "the emitter
    * lost a clause". The note is that difference: it names the carrier the requirement
    * is not over (§2.7a), or the members that shadow it (WI-1065), which is precisely
    * the reasoning no signature can carry.
    *
    * THE TAIL LIVES ONCE because it is a claim about what Bootstrap emits — WI-1022
    * landed the `using` emission by changing this one site, and both notes followed.
    *
    * ABOVE the declaration and not inside it: Scala's indentation syntax requires a
    * block opened with `:` to contain a definition, so a comment inside the body of
    * an operation-less sort is `indented definitions expected, eof found` — the same
    * trap [[renderMainSort]]'s `ops.isEmpty` arm exists for.
    */
  private def requirementNote(rendered: String, reason: String, carriedBy: String): String =
    // The requirement gets its own line: it is the only part of this whose length
    // varies, so wrapping the rest by hand stays honest as the name grows.
    s"// `requires $rendered`\n" + reason + "What carries\n" + carriedBy

  private val carriedByUsing =
    "//   it is §2.7's `using` context parameter, which every operation below takes.\n"

  /** The tail for a sort that declares NO operation (WI-1022 review).
    *
    * THE PARTITION IS OVER THE EMITTED SIGNATURES, and a sort with none has nowhere to
    * put a dictionary: [[renderMainSort]]'s `ops.isEmpty` arm emits a bare `trait S[…]`
    * with no member to hang a `using` clause on. Claiming "every operation below takes
    * it" there is vacuous and reads as a promise, which is worse than the silence it
    * describes.
    *
    * NOT A REFUSAL, and the reason is that nothing is LOST that the emission ever
    * carried: with no operation there is no body for the evidence to reach, and what
    * the requirement does condition — this sort's `provides` clauses and its laws — has
    * no bootstrap emission at all (§2.7a's closing note). So the honest report is that
    * the requirement reaches Scala nowhere, which is what this says.
    */
  private val carriedByNothing =
    "//   it is NOTHING here: this sort declares no operation, so the emission has no\n" +
    "//   signature for the dictionary to ride. What the requirement conditions — this\n" +
    "//   sort's `provides` and its laws — has no bootstrap emission either (§2.7a).\n"

  private def evidenceNote(rendered: String, carrier: Carrier, hasOps: Boolean): String =
    requirementNote(rendered,
      "//   is EVIDENCE, not a supertype claim (§2.7a, kernel §8.7). This sort's carrier is\n" +
      s"//   ${carrier.describe}, and the requirement is not over it. ",
      if hasOps then carriedByUsing else carriedByNothing)

  /** The sort's own operations that SHADOW a member of the required spec — the
    * declaring sort's spelling, in declaration order, empty when the requirement is
    * a clean supertrait. Compared as EMITTED method names on both sides, because
    * the override group Scala would form is over those (WI-1054). */
  private def shadowedMemberNames(
    sym: SymbolTable, req: SortRequirement, ops: IndexedSeq[Operation],
    specMembers: Map[String, Set[String]]
  ): IndexedSeq[String] =
    headName(sym, req.decl.typeExpr) match
      case Some(specLeaf) =>
        val inherited = specMembers.getOrElse(specLeaf, Set.empty)
        ops.map(o => sym.name(o.name.last))
          .distinctBy(Names.scalaMethodName) // one entry per EMITTED name (WI-1054)
          .filter(n => inherited.contains(Names.scalaMethodName(n)))
      // Unreachable for a requirement that passed [[isOverCarrier]] — an arrow or
      // tuple already threw in [[writtenArguments]] — kept total rather than partial.
      case None => IndexedSeq.empty

  /** The comment a SHADOWED requirement becomes (WI-1065): over the carrier, so it
    * would have been the supertrait, and demoted because the sort redeclares members
    * of the required spec — distinct operations per kernel §8.7, which one Scala
    * override group cannot hold. Same frame as [[evidenceNote]], and above the
    * declaration for the same indentation-syntax reason.
    *
    * ALWAYS [[carriedByUsing]], where [[evidenceNote]] has to be told: a shadow IS a
    * redeclared member, so this note cannot exist for a sort with no operations. */
  private def shadowNote(rendered: String, members: IndexedSeq[String]): String =
    val names = members.map(m => s"`$m`").mkString(", ")
    requirementNote(rendered,
      "//   is EVIDENCE here, not a supertrait (§2.7a, kernel §8.7): this sort redeclares\n" +
      s"//   $names, and a redeclared member of a merely-required spec is a DISTINCT\n" +
      "//   operation shadowing it, not an override — a relation one Scala override\n" +
      "//   group cannot hold (WI-1065). ",
      carriedByUsing)

  /** Refuse a data sort's ANONYMOUS `requires` that the emitted tree would not carry.
    *
    * ANONYMOUS, because a named slot has its own home and reaches here already
    * discharged (WI-1022): it is a type PARAMETER, so the requirement rides in that
    * parameter's upper bound on the emitted declaration — `enum SortedSet[T, O <:
    * Ord[T]]` states it where no field could. [[requiresMapping]] does the filtering,
    * so this function is never asked a question it would answer wrongly.
    *
    * The question is asked of the EMISSION and not of the source, which is what
    * makes it the right question: the requirement survives when a constructor field
    * is TYPED BY it, so the evidence reaches Scala as that field's type. Both
    * corpus instances are exactly that — `requires FiniteCollection[C = SrcC,
    * Element = Src, E = ES]` beside `entity fmapped(source: FiniteCollection[C =
    * SrcC, Element = Src, E = ES], …)` — and there the omitted `extends` costs the
    * emitted tree nothing. Rendering through the SAME `scope` the field list uses
    * (`at` varies only the diagnostic label) is what makes the two comparable.
    *
    * PER CONSTRUCTOR, not per sort. Over the flattened field list of a sum, one
    * constructor carrying the requirement would discharge it for its siblings, and
    * a sibling that carries it nowhere is the silent drop this exists to prevent.
    *
    * CONTAINMENT, not equality, and bounded on the left so `MyWalk[T]` cannot
    * discharge `Walk[T]`. A field is often the requirement NESTED — `sources:
    * List[T = Walk[…]]` renders `_root_.anthill.prelude.List[Walk[SrcC, Src]]` —
    * and whole-string equality refused those, which aborts `generate` and takes
    * every other sort in the file with it.
    *
    * TWO LIMITS, both real and neither reached by the corpus. Effect arguments
    * erase before rendering (§2.8a), so a field carrying a DIFFERENT row compares
    * equal to the requirement — the check is blind in exactly that slot.
    * `Names.scalaTypeName` is many-to-one, so `requires foo_bar[T]` is discharged
    * by a field `x: fooBar[T]`. Both are the price of asking the question of the
    * rendered output; asking it of the parse IR instead would be asking about a
    * type the emission may not carry.
    */
  private def checkDischarged(
    sym: SymbolTable, sortLeaf: String, ctors: IndexedSeq[Entity],
    requires: IndexedSeq[SortRequirement], scope: TypeScope
  ): Unit =
    requires.foreach { req =>
      val rendered = req.rendered
      val occurrence = java.util.regex.Pattern.compile(
        s"(?<![\\w.])${java.util.regex.Pattern.quote(rendered)}")
      ctors.foreach { ctor =>
        val carried = ctor.fields.exists(f =>
          occurrence.matcher(TypeGen.render(sym, f.ty, scope)).find())
        if !carried then
          throw BootstrapError(
            s"sort `$sortLeaf` has constructors, so its `requires $rendered` is " +
            "evidence supplied to bodies (kernel §8.7) and not a claim about the " +
            s"type — and constructor `${sym.name(ctor.name.last)}` has no field " +
            "typed by it, so the emitted declaration would carry the requirement " +
            "nowhere — and a data sort's requirement constrains the constructed " +
            "VALUE, which a `using` clause on its operations does not reach. NAME " +
            "the slot and it becomes a type parameter bounded by the spec (§2.7), " +
            "which the declaration itself carries",
            req.span)
      }
    }

  // ── Helpers ─────────────────────────────────────────────────────

  /** Split a multi-segment name into (packagePath, leafTypeName). For
    * `anthill.prelude.Option` returns ("anthill.prelude", "Option"); for
    * a single-segment name the enclosing `packagePath` is used instead.
    *
    * BOTH HALVES ARE CONVERTED, by their own rule (WI-1054): the prefix segments name
    * a PACKAGE and take [[Names.scalaPackageSegment]], the leaf names a TYPE and takes
    * `scalaTypeName`. A raw prefix would put a hyphen in a `package` clause and in the
    * `src/main/scala/…` path derived from it.
    */
  private def splitPath(
    sym: SymbolTable, name: anthill.parse.Name, packagePath: String
  ): (String, String) =
    if name.segments.length > 1 then
      val prefix = Names.scalaPackagePath(name.segments.dropRight(1).map(sym.name))
      val leaf = Names.scalaTypeName(sym.name(name.last))
      // A dotted declaration may repeat the namespace it is written in
      // (`namespace anthill.prelude { sort anthill.prelude.Concat ... }`). Its
      // prefix is then already an absolute spelling of this lexical package; appending
      // the enclosing path again produced `anthill.prelude.anthill.prelude`. A genuinely
      // relative dotted prefix still extends the package (`namespace a { sort b.T }`).
      val alreadyRooted =
        prefix == packagePath || (packagePath.nonEmpty && prefix.startsWith(s"$packagePath."))
      val pkg =
        if packagePath.isEmpty || alreadyRooted then prefix else s"$packagePath.$prefix"
      (pkg, leaf)
    else
      (packagePath, Names.scalaTypeName(sym.name(name.last)))

  private def pathToDir(packagePath: String): String =
    if packagePath.isEmpty then "" else s"${packagePath.replace('.', '/')}/"

  // ── Render: main sort source ────────────────────────────────────

  private def renderMainSort(
    sortName: String, tpStr: String, typeParams: IndexedSeq[TypeParamDecl],
    req: RequiresMapping, ops: IndexedSeq[Operation], shape: SortShape,
    packagePath: String, scope: TypeScope, sym: SymbolTable
  ): String =
    val sb = StringBuilder()
    if packagePath.nonEmpty then sb ++= s"package $packagePath\n\n"
    // The `requires` mapping arrives ALREADY DECIDED ([[requiresMapping]]), rather
    // than being derived from `requires` here: the three branches below share one
    // answer, and while they shared one DERIVATION the algebra sort's reading was
    // applied to the two data shapes as well (WI-1064).
    val ext = req.ext
    sb ++= req.note
    // The sort's parameters as ARGUMENTS (`[T]`), against `tpStr`'s BINDERS
    // (`[M[_]]`) — an enum case that has to name its parent needs both forms.
    val tpArgs =
      if typeParams.isEmpty then "" else typeParams.map(_.scalaName).mkString("[", ", ", "]")
    shape match
      case SortShape.Record(ctor) =>
        // case class Sort[T](fields) — ONE declaration (§6.3 / WI-926 / WI-940).
        sb ++= renderCaseClass(sym, sortName, tpStr, ctor.fields, ext, scope)
        sb ++= renderOpsTrait(sortName, tpStr, ops, req.evidence, scope, sym)
      case SortShape.Sum(ctors) =>
        // enum Sort[T] { case C1(...); case C2 }
        sb ++= s"enum $sortName$tpStr$ext:\n"
        ctors.foreach { c =>
          val cName = Names.scalaTypeName(sym.name(c.name.last))
          val fields = renderFieldList(sym, c.fields, scope)
          // An UNPARAMETERIZED enum's nullary case takes no parameter list at all —
          // `case Red`, not `case Red()`. The record branch has neither form: a
          // `case class` always needs its `()`.
          if c.fields.isEmpty && typeParams.isEmpty then sb ++= s"  case $cName\n"
          else
            val uncovered = uncoveredParams(sym, c, typeParams)
            if uncovered.isEmpty then sb ++= s"  case $cName($fields)\n"
            else
              val parent = enumParent(cName, sortName, packagePath, c.name.span)
              sb ++= s"  case $cName$tpStr($fields) extends $parent$tpArgs\n"
        }
        sb ++= renderOpsTrait(sortName, tpStr, ops, req.evidence, scope, sym)
      case SortShape.Algebra =>
        // trait Sort[T] { abstract ops }
        //
        // A sort declaring NO operations takes no body at all — not a `:` with a comment
        // under it. Scala's indentation syntax requires a block opened with `:` to
        // contain at least one definition, so `trait Eq[T] extends PartialEq[T]:` over a
        // lone comment is `indented definitions expected, eof found`. stdlib's `Eq` is
        // exactly that shape (it adds only a law), and it shipped uncompilable behind a
        // green substring test until WI-1020's harness compiled the output.
        if ops.isEmpty then sb ++= s"trait $sortName$tpStr$ext\n"
        else
          sb ++= s"trait $sortName$tpStr$ext:\n"
          ops.foreach(op =>
            sb ++= s"  ${OpGen.renderAbstract(op, req.evidence, scope, sym)}\n")
    sb.toString

  /** How an enum CASE names the enum it extends.
    *
    * ITS OWN NAME SHADOWS THE ENUM'S inside the enum body, and two anthill names that
    * §5 converts to one is a shape this backend already knows it must handle
    * ([[refuseColliding]] for the file path): `sortedset.anthill` declares `sort
    * SortedSet` with the constructor `sorted_set`, which are two symbols in anthill —
    * so [[shapeOf]]'s eponymy test, keyed on the ANTHILL name deliberately, correctly
    * classifies the sort as a SUM — and `Names.scalaTypeName` sends both to
    * `SortedSet`. MEASURED under dotc: `case SortedSet[…](…) extends SortedSet[T, O]`
    * is `Cyclic inheritance: class SortedSet extends itself`, followed by `enum case
    * does not extend its enum class`.
    *
    * QUALIFYING THE PARENT is the whole fix, and it is available because every
    * emitted declaration is in a named package. Only the REPARAMETERIZED form needs
    * it: a case whose fields cover every parameter writes no `extends` at all, which
    * is why `enum Pair: case Pair(…)` compiles (measured, `ScalaCompile`'s doc) and
    * this does not.
    *
    * QUALIFIED ONLY WHERE IT SHADOWS, rather than always: `extends List[T]` is what
    * the emitted tree reads today and what its tests pin, and a qualification with no
    * shadow to escape would be noise the reader has to rule out. The condition is
    * exact — a case shadows the enum iff their EMITTED names are equal — so there is
    * no shape where the plain form is chosen and wrong.
    *
    * NO PACKAGE ⇒ NO SPELLING, so it is refused. A top-level type in the empty
    * package is not a member of `_root_` (measured: `type RootSet is not a member of
    * <root>`), so there is nothing to qualify with and the emission would be the
    * cyclic-inheritance error above. Every stdlib file declares a namespace; the
    * shape is reachable only from a fixture.
    */
  private def enumParent(
    caseName: String, sortName: String, packagePath: String, span: Span
  ): String =
    if caseName != sortName then sortName
    else if packagePath.nonEmpty then s"_root_.$packagePath.$sortName"
    else
      throw BootstrapError(
        s"constructor `$caseName` and its sort emit the same Scala name (§5 converts " +
        "many anthill names to one), so the enum case shadows the enum it extends — " +
        "and in the empty package there is no qualified spelling of the enum to " +
        "escape it with. Declare the sort inside a namespace, or rename one of them",
        span)

  /** The enum parameters a case's FIELD TYPES do not mention.
    *
    * Scala infers an enum case's parent arguments from its fields, so a case that
    * leaves a parameter unmentioned is `cannot determine type argument for enum
    * parent class List, type parameter type T is invariant`. `List.scala` and
    * `Option.scala` both shipped that way, through their nullary `nil` / `none`.
    *
    * THE RULE IS COVERAGE, NOT ARITY. Keying on "the case has no fields" would be a
    * proxy: `entity left(v: L)` in a two-parameter `sort Either[L, R]` has a field
    * and still leaves `R` uninferable. No prelude sort has that shape today, which
    * is exactly why the proxy would have looked right.
    *
    * A case that needs it is REPARAMETERIZED — `case Nil[T]() extends List[T]` —
    * rather than pinned to the covariant idiom `extends List[Nothing]`: anthill's
    * `nil` IS polymorphic (a `List[T]` for every `T`) and an anthill sort declares
    * no variance, so `List[Nothing]` would be a value no `List[Int]` context could
    * take. A higher-kinded parameter needs no special case — `case Nil[M[_]]()
    * extends Foo[M]` is the same shape, which is why the binder list is `tpStr`,
    * the sort's own.
    */
  private def uncoveredParams(
    sym: SymbolTable, ctor: Entity, typeParams: IndexedSeq[TypeParamDecl]
  ): Set[String] =
    val mentioned = ctor.fields.foldLeft(Set.empty[String])((acc, f) =>
      acc ++ namesIn(sym, f.ty))
    typeParams.map(_.anthillName).toSet -- mentioned

  /** Every type name written anywhere inside a type expression. Over-approximates
    * on purpose — a name that is not a parameter simply never matches. */
  private def namesIn(sym: SymbolTable, te: TypeExpr): Set[String] = te match
    case TypeExpr.Simple(n) => Set(sym.name(n.last))
    case TypeExpr.Parameterized(n, bindings) =>
      bindings.foldLeft(Set(sym.name(n.last)))((acc, b) => acc ++ namesIn(sym, b.bound))
    case TypeExpr.TupleType(fields) =>
      fields.foldLeft(Set.empty[String])((acc, f) => acc ++ namesIn(sym, f._2))
    case TypeExpr.Arrow(params, ret, effects) =>
      (params ++ effects :+ ret).foldLeft(Set.empty[String])((acc, t) => acc ++ namesIn(sym, t))
    case TypeExpr.EffectRow(effects) =>
      effects.foldLeft(Set.empty[String])((acc, t) => acc ++ namesIn(sym, t))
    case TypeExpr.EffectGuarded(label, _) => namesIn(sym, label)
    // A logical variable and a value-in-type name no type. Both are refused by
    // `TypeGen` before an emission gets this far, so neither can hide a mention.
    case TypeExpr.Variable(_, _) | TypeExpr.Denoted(_) => Set.empty

  /** The `case class` a SINGLE-CONSTRUCTOR sort maps to — the one declaration
    * BOTH of §6.3's spellings produce.
    *
    * Shared by the standalone-`entity` sugar and by the eponymous long form so
    * that equivalence ("the sugar and the long form denote the same thing")
    * holds BY CONSTRUCTION, rather than by two renderers happening to agree —
    * which they did not: the long form emitted `enum Vec3: case Vec3(…)`, the
    * nested `Vec3.Vec3` §6.3 rules out (WI-940).
    */
  private def renderCaseClass(
    sym: SymbolTable, typeName: String, tpStr: String,
    fields: IndexedSeq[FieldDecl], extendsClause: String, scope: TypeScope
  ): String =
    s"case class $typeName$tpStr(${renderFieldList(sym, fields, scope)})$extendsClause\n"

  /** A constructor's fields as a Scala parameter list, without the parentheses —
    * one rendering for the `case class` and the `enum case`, which declare the
    * same schema and must not drift on how a field name or type reaches Scala. */
  private def renderFieldList(
    sym: SymbolTable, fields: IndexedSeq[FieldDecl], scope: TypeScope
  ): String =
    fields.map { f =>
      s"${Names.scalaFieldName(sym.name(f.name))}: ${TypeGen.render(sym, f.ty, scope)}"
    }.mkString(", ")

  /** The abstract operation contract of a sort that has constructors, or "" when
    * it declares none.
    *
    * It stays a SEPARATE `trait <Sort>Ops` — not members of the `case class` /
    * `enum` — and that is a Scala limit, not a reading of §6.3: bootstrap emits
    * signatures only (bodies are the KB-driven gen's, proposal 034), and Scala
    * has no abstract member in an instantiable `case class`. cpp-gen puts an
    * eponymous sort's operations inside the same `struct` (WI-931) because a C++
    * member declaration needs no definition; that collapse has no analogue here.
    * What §6.3 buys in Scala is therefore that the TYPE is one declaration —
    * there is no `Vec3.Vec3` — while the contract an implementation satisfies
    * keeps the `<Sort>Ops` name it already has for a sum sort
    * (docs/scala-forward-mapping.md §2.3).
    */
  private def renderOpsTrait(
    sortName: String, tpStr: String, ops: IndexedSeq[Operation],
    evidence: IndexedSeq[String], scope: TypeScope, sym: SymbolTable
  ): String =
    if ops.isEmpty then ""
    else
      val sb = StringBuilder()
      sb ++= s"\ntrait ${sortName}Ops$tpStr:\n"
      ops.foreach(op => sb ++= s"  ${OpGen.renderAbstract(op, evidence, scope, sym)}\n")
      sb.toString

end Bootstrap

package anthill.codegen.scala

import anthill.intern.SymbolTable
import anthill.parse.{Name, TypeExpr}

/** TypeExpr → Scala type string. Uses the default `scala_std` type
  * mapping per `docs/scala-forward-mapping.md` table in §2 + §1.1.
  *
  * EVERY NAME IS PLACED (WI-1055). Rendering takes a [[TypeScope]] and asks it
  * where each written name goes; a name it cannot place, and a construct with no
  * Scala type form at all, are [[BootstrapError]]s rather than a nearest-legal
  * spelling. The placeholders this replaced — `?` for a type variable, `Any` for
  * a denoted value or an effect row — were not types Bootstrap believed in; they
  * were text that let a file reach the output looking emitted. Measured: 27 of 44
  * prelude files did not compile and every one of them emitted quietly.
  */
object TypeGen:

  def render(sym: SymbolTable, te: TypeExpr, scope: TypeScope): String = te match
    case TypeExpr.Simple(n) =>
      named(sym, n, IndexedSeq.empty, scope)
    case TypeExpr.Parameterized(n, bindings) =>
      named(sym, n, bindings.map(b => render(sym, b.bound, scope)), scope)
    case TypeExpr.TupleType(fields) =>
      // The empty tuple goes through [[hostScalars]] rather than a literal "Unit":
      // one answer to "what is anthill's Unit in Scala", so the two cannot drift
      // (they had — this arm emitted a bare `Unit` after the table was `_root_`-
      // anchored). `get` and not a fallback: an absent entry is a table edit that
      // broke a rendering path, and a silent bare `Unit` is how it would hide.
      if fields.isEmpty then hostScalars("Unit")
      else fields.map { case (_, ty) => render(sym, ty, scope) }.mkString("(", ", ", ")")
    case TypeExpr.Arrow(params, ret, _) =>
      // Pure arrow in scala_std (effects shape result type for cc only).
      val ps =
        if params.isEmpty then "()"
        else params.map(render(sym, _, scope)).mkString("(", ", ", ")")
      s"$ps => ${render(sym, ret, scope)}"
    case TypeExpr.Variable(_, _) =>
      // WI-1055 B2. `?A` in a type position denotes a logical variable, which
      // Scala has no term for — this rendered as the literal `?`, which is not
      // even a Scala type, so the emitted file could not parse. Resolving what
      // the variable stands for is a typer question and scaland has no typer.
      throw BootstrapError(
        s"${scope.decl}: a type VARIABLE in a type position has no Scala form. " +
        "What it stands for is a typer question, and Bootstrap runs on the parse " +
        "IR alone (proposal 034)",
        scope.declSpan)
    case TypeExpr.Denoted(_) =>
      // WI-1055 B2. Value-in-type (`Vector[Int64, 3]`, WI-302) — Scala has no
      // dependent type slot to put the literal in. Emitted as `Any`, which
      // compiles and means something else entirely.
      throw BootstrapError(
        s"${scope.decl}: a value in a type-argument slot (value-in-type, WI-302) " +
        "has no Scala form; `Any` would compile and mean something else",
        scope.declSpan)
    case TypeExpr.EffectRow(_) | TypeExpr.EffectGuarded(_, _) =>
      // WI-1055 B2. scala_std ERASES effects (§2.8), so a written effect row in a
      // type-argument slot has nothing to erase TO: the slot still needs a type.
      // `Any` was emitted here, which is a silent widening of whatever the row
      // constrained.
      //
      // THE OPEN QUESTION UNDER IT is not the row but the PARAMETER it fills:
      // `Stream`'s second parameter IS an effect row (`effects E = ?`), so the
      // coherent answer may be that an effect parameter is erased from the emitted
      // type entirely and the argument dropped rather than rendered. That needs the
      // parse IR to mark effect parameters (it does not) and a use site to know a
      // FOREIGN sort's parameter kinds (proposal 034 says it cannot) — WI-1062.
      // Until then this is the refusal that keeps eight prelude files, and through
      // `Iterable` their dependents, out of the tree.
      throw BootstrapError(
        s"${scope.decl}: a written effect row in a type-argument slot has no Scala " +
        "form — scala_std erases effects (§2.8), but the argument slot still needs " +
        "a type",
        scope.declSpan)

  /** One written name, with its already-rendered arguments. */
  private def named(
    sym: SymbolTable, n: Name, args: IndexedSeq[String], scope: TypeScope
  ): String =
    val leaf = sym.name(n.last)
    scope.place(leaf) match
      // The two placements of UNKNOWN arity, and the only ones whose arguments
      // pass through unchecked. A type parameter's kind is not carried here (a
      // higher-kinded `M[A]` takes arguments, a proper `V` does not) and an ambient
      // name's arity lives in a file Bootstrap has not read. Over-application is
      // therefore left to the Scala compiler ("V does not take type parameters"),
      // which is a clear diagnostic and a shape no stdlib file writes — unlike the
      // map-entry mismatch below, whose point is that the ENTRY is wrong, not the
      // use, and which no compiler message would attribute correctly.
      case Placement.TypeParam(name) => name + brackets(args)
      case Placement.Ambient(name) => name + brackets(args)
      case Placement.Enclosing(self) =>
        // WI-1055 A3: a BARE mention of the enclosing sort means "with my own
        // parameters" in anthill, and Scala has no bare spelling for that. This is
        // also what stops the sort's own name being rewritten through the prelude
        // map — pair.anthill's `operation fst(p: Pair) -> A` emitted `Tuple2`, a
        // DIFFERENT type from the `enum Pair[A, B]` three lines up (WI-1021).
        if args.isEmpty then self.scalaName + brackets(self.params)
        else if args.length != self.params.length then
          throw BootstrapError(
            s"${scope.decl}: `$leaf` is the enclosing sort, which is emitted with " +
            s"${self.params.length} type parameter(s), but ${args.length} argument(s) " +
            "were written. The parameters Bootstrap emits and the ones the " +
            "declaration writes have diverged",
            n.span)
        else self.scalaName + brackets(args)
      case Placement.Known(scalaName, arity) =>
        if args.length != arity then
          // WI-1055 B3. The written occurrence is PARTIAL — `Pair` where
          // `Pair[A, B]` is needed, which is what an operation's `p: Pair` is once
          // it is read from OUTSIDE the sort that declares it. In anthill the
          // parameters are in scope and need no writing; Scala has no bare type
          // constructor in this position, and the arguments to re-attach exist only
          // for the ENCLOSING sort (the arm above).
          //
          // IT ALSO CAUGHT AN ARITY-INCOMPATIBLE MAP ENTRY, and that is now a shape
          // the table cannot express: `Stream[Element, E]` was checked against
          // `LazyList`'s ONE parameter, because the entry claimed an effect-carrying
          // anthill collection was a Scala one. WI-1021 settled that it is not —
          // see [[hostScalar]] / [[preludeSort]] — so every entry's arity is now that of the
          // type it names.
          throw BootstrapError(
            s"${scope.decl}: `$leaf` maps to Scala `$scalaName`, which takes $arity " +
            s"type argument(s), but ${args.length} were written. anthill leaves a " +
            "sort's parameters implicit where they are in scope and allows a PARTIAL " +
            "named binding; Scala has no bare type constructor in this position, so " +
            "there is no spelling to emit",
            n.span)
        else scalaName + brackets(args)
      case Placement.Unplaceable(reason) =>
        // WI-1055 B1. The name would reach the output as a bare identifier naming
        // nothing in the emitted tree. This is how `Term`, `NodeOccurrence` and
        // `Type` shipped: not as a typo Bootstrap could not rule out, but as a
        // reference Bootstrap could already show unreachable and emitted anyway.
        throw BootstrapError(s"${scope.decl}: cannot emit the type `$leaf` — $reason", n.span)

  private def brackets(args: IndexedSeq[String]): String =
    if args.isEmpty then "" else args.mkString("[", ", ", "]")

  // ── Prelude names: host type or anthill type (WI-1021) ────────────────────
  //
  // Two accessors and two tables, because a prelude name has exactly two ways to
  // have a Scala counterpart at all and they are consulted at DIFFERENT points of
  // `TypeScope.place` — [[hostScalar]] above the enclosing sort, [[preludeSort]]
  // below it and below the file's own types. A single combined lookup was the shape
  // this replaced, and it could not express that.

  /** The decision, and the enforcement site for `docs/scala-forward-mapping.md`
    * §2.1a.
    *
    * WI-1021 DECIDED WHICH IS WHICH, and the test is whether anthill can build a
    * value of the sort. A scalar cannot be built in anthill — `Int64` declares no
    * `entity` and there is no way to make one but a literal, so the host type IS
    * the carrier and nothing else could be. Every other prelude sort either has
    * anthill CONSTRUCTORS (`List`'s `nil`/`cons`, `Option`'s `none`/`some`,
    * `Pair`'s `pair`) or is representation-defined with the carrier chosen by a
    * provider (`Set`, `Map`, `Stream`) — and in both cases Bootstrap EMITS a Scala
    * declaration for it, which is then what a written occurrence denotes.
    *
    * WHAT THE HOST REWRITE DID, measured on the emitted prelude: `pair.anthill`
    * emitted `enum Pair[A, B]` into `anthill.prelude` and `list.anthill`, four
    * lines of output away, emitted `Option[Tuple2[T, List[T]]]` — the SAME anthill
    * name denoting two unrelated Scala types in one tree, one of them structural
    * where anthill's has named fields, its own `eq`, and four conditioned
    * `provides` clauses no `Tuple2` can carry. `Stream` showed it as an outright
    * arity conflict (`Stream[Element, E]` against a one-parameter `LazyList`),
    * which is the same defect where the shapes happened not to line up.
    *
    * AND IT CAPTURED, IN BOTH DIRECTIONS. Every entry emitted a BARE name, and a
    * bare name in `package anthill.prelude` resolves against that package's own
    * members before Scala's root imports. So `Option -> Option` bound
    * `anthill.prelude.Option` when the sibling file was in the compilation and
    * `scala.Option` when it was not — the emission MEANT different things depending
    * on what else was compiled with it. The scalars had the mirror image, and it is
    * the sharper one because the prelude declares `trait String`, `trait BigInt`
    * and `trait Nothing`: MEASURED, `Duration(5, "m")` against the emitted
    * `case class Duration(amount: Int, unit: String)` is `Found: ("m" : String),
    * Required: anthill.prelude.String` with string.anthill present and compiles
    * without it — an ALGEBRA trait silently standing in for the carrier.
    *
    * BOTH TABLES THEREFORE EMIT `_root_`-ANCHORED NAMES. Qualification alone is not
    * enough: `anthill.prelude.Option` is a RELATIVE path, so a project emitting into
    * `myco` alongside a `myco.anthill` namespace captures it the same way. `_root_.`
    * is what cannot be captured, and it costs only verbosity in generated source.
    * This is the `Numeric` / `scala.math.Numeric` hazard [[Placement.Ambient]]
    * exists to close, and it was reachable through a table entry.
    *
    * THE ALTERNATIVE, AND WHY IT WAS REFUSED. WI-1021 also offered simply DELETING
    * the offending entries, which is what "these are not host types" says on its
    * own. Deleting drops the name to [[Placement.Ambient]], and Ambient qualifies
    * with the DECLARATION'S package — right inside the prelude, wrong for every
    * project consumer, which would reach `Option` through the auto-import and be
    * emitted `my.app.Option`. It also gives up the arity check on exactly the
    * names WI-1055 B3 added it for. Re-pointing keeps both: the same `Known`
    * placement, with the package the prelude actually emits into.
    *
    * NOT A NEW ARITY CLAIM: this table already stated an arity per entry and every
    * one of them was already the anthill sort's own, `Stream` excepted — where the
    * `1` was `LazyList`'s and the anthill sort has two parameters. What changed is
    * the NAME each arity belongs to.
    *
    * `Map` NAMES A TYPE NOTHING EMITS TODAY, and that is deliberate rather than an
    * oversight: map.anthill is in the refusal set (a written effect row, WI-1062),
    * so a consumer's `Map[K = A, V = B]` reaches `_root_.anthill.prelude.Map` and
    * fails naming exactly the declaration that is missing. The alternative was
    * `scala.Map`, which compiles and is a different type with a different contract —
    * the same trade [[Placement.Ambient]] made when it chose a loud missing sibling
    * over a silent capture.
    *
    * WHAT A RE-POINT COSTS A PROJECT THAT HAS ITS OWN `Option`: the old bare
    * emission bound to a same-package sibling when there was one, so a project
    * declaring `enum Option` in another file of its own package got ITS type. It now
    * gets `_root_.anthill.prelude.Option`. That is a real narrowing and not a pure
    * gain — the table answers before `fileTypes` can see a sibling FILE (Bootstrap
    * is per-file), and shadowing is not checked at all (below). `Pair` alone
    * regressed nothing, because its old answer was `Tuple2` either way.
    *
    * An unknown name gets NO entry — the pass-through this replaced
    * (`Names.scalaTypeName(short)`) is precisely how an unresolvable name reached
    * the output looking like a project-defined sort. `Numeric` was the sharpest
    * case: it passed through and bound to `scala.math.Numeric`, so `field.anthill`
    * COMPILED against a type from a different library.
    *
    * A NON-SCALAR NAME IS NOT CHECKED FOR SHADOWING, unchanged by this and worth
    * saying out loud now that the target is a package rather than a host type: a
    * project declaring its OWN `Pair` in a sibling FILE, or importing one, still
    * reaches [[preludeSorts]] (`TypeScope.place` consults it after `fileTypes`,
    * which is per-file, and before `importedFrom`), so the emission says
    * `anthill.prelude.Pair` for a name the source meant locally. No corpus file has
    * the shape. Fixing it means consulting the import table first, which is a
    * `place` reordering with its own justification to make.
    *
    * A SECOND SOURCE OF TRUTH, AND NOTHING ENFORCES THE AGREEMENT.
    * `stdlib/anthill/realization/scala_std.anthill` declares a `type_map` and says
    * of itself "Codegen reads this from the KB; changing it changes generated code
    * without touching the codegen implementation" — nothing reads it. WI-1021 made
    * the two AGREE where they can: the fact's `type_map` is now exactly
    * [[hostScalars]], entry for entry, including `Int64 -> Long` (the fact said
    * `Int64 -> Int64`, a WI-068 rename artifact, and THIS table said `Int` — which
    * is 32-bit and was the older error of the two) and minus the `Duration` /
    * `Timestamp` entries, which name sorts `primitives.anthill` declares WITH
    * constructors and Bootstrap emits. `scala_caps.anthill`, the other
    * `language: "scala"` profile, carries the same corrected table.
    *
    * [[preludeSorts]] has NO counterpart in the fact: `TypeMapping(anthill_type,
    * host_type)` has no arity column and no host name to put in the one it has.
    * (`realization.anthill`'s `TypeMapping` does carry `lang`/`key`, so a schema
    * that could say this is reachable — it is not the shape today.) That, and making
    * the emitter read either table at all, is WI-1060; the shape is the one
    * `buildSbt` already has, with the caller resolving the profile and passing the
    * table in (Bootstrap reads no KB by design, proposal 034). Until then the
    * agreement above is a fact about today, held by nothing but this comment.
    */
  /** The scalar half. Consulted ABOVE the enclosing sort:
    * `int64.anthill`'s `operation compare(a: Int64, b: Int64) -> Int64` is over the
    * CARRIER, not over the `trait Int64` that file emits. Read the other way round
    * it emitted `def compare(a: Int64, b: Int64): Int64` against a trait no value
    * inhabits, while every consumer of the same anthill name got `Long` — the
    * two-types-for-one-name defect this whole ticket removes, surviving inside the
    * five files that declare a scalar. */
  def hostScalar(anthillLeaf: String): Option[Placement.Known] =
    hostScalars.get(anthillLeaf).map(Placement.Known(_, arity = 0))

  /** The prelude-sort half. Consulted BELOW the enclosing sort and the file's own
    * types — a file that declares the name emits it, and its own spelling is the
    * one to use. */
  def preludeSort(anthillLeaf: String): Option[Placement.Known] =
    preludeSorts.get(anthillLeaf).map(arity =>
      Placement.Known(s"_root_.anthill.prelude.${Names.scalaTypeName(anthillLeaf)}", arity))

  /** The sorts whose values ARE host values. No arity column, because a scalar has
    * no parameters to have an arity of — the shape is what keeps a parameterized
    * sort from being entered here.
    *
    * `Int64` IS `Long`, not `Int`. anthill's `Int64` is a 64-bit integer — the WI-068
    * rename says so, `rust_std` maps it to `i64` and `cpp_std` to `int64_t` — and
    * Scala's `Int` is 32-bit, so every value above 2^31-1 would truncate silently.
    *
    * `_root_`-ANCHORED, and the reason is measured: `string.anthill` emits
    * `trait String` into `anthill.prelude`, so a bare `String` in a sibling emission
    * binds THAT and not `java.lang.String`. See the note on [[hostScalar]]. */
  private val hostScalars: Map[String, String] = Map(
    "Int64" -> "_root_.scala.Long",
    "BigInt" -> "_root_.scala.math.BigInt",
    "Float" -> "_root_.scala.Double",
    "Bool" -> "_root_.scala.Boolean",
    "String" -> "_root_.java.lang.String",
    "Unit" -> "_root_.scala.Unit",
    "Nothing" -> "_root_.scala.Nothing",
  )

  /** Prelude sorts Bootstrap emits, by the arity it emits them with. No Scala NAME
    * column, because there is no choice to make: the type is the one the prelude's
    * own file emits, in `anthill.prelude`. The shape is what keeps a host type from
    * being entered here.
    *
    * NOT EVERY PRELUDE SORT — these six are the ones that HAD a host entry, and
    * WI-1021 decided where those entries point, not which names belong in a table.
    * `Eq`, `Iterable`, `Duration` and the rest still reach [[Placement.Ambient]],
    * which qualifies with the DECLARING file's package: right for the prelude's own
    * files, a guess for a project consumer reaching one through the auto-import.
    * Closing that means a table of every auto-imported prelude sort, which is the
    * read-it-from-the-profile job (WI-1060) and not a list to grow by hand here.
    *
    * THE ARITIES ARE A HAND-COPY of what `Bootstrap.sortTypeParams` computes from
    * the declaring file, and nothing cross-checks them — Bootstrap is per-file and
    * never parses `set.anthill` while emitting a consumer. Give a sort here a new
    * parameter and every consumer is refused with a message that reads as if the
    * DECLARATION were wrong. WI-1060's profile-supplied table is where that stops
    * being a copy. Only `Option`, `Pair` and `Stream` are pinned by a compile
    * today. */
  private val preludeSorts: Map[String, Int] = Map(
    "List" -> 1,
    "Option" -> 1,
    "Pair" -> 2,
    "Set" -> 1,
    "Map" -> 2,
    "Stream" -> 2,
  )

  // The two tables answer different questions and a name belongs to exactly one.
  // Checked rather than made unrepresentable because the SHAPES only constrain the
  // value columns: nothing stops a name being a key in both, and `place`
  // would then let the scalar win silently — so a later fix that added `"String" ->
  // 0` to `preludeSorts` (the obvious wrong move, since `String` is already a
  // capture hazard) would be dead code with no signal.
  require((hostScalars.keySet & preludeSorts.keySet).isEmpty,
    "a prelude name is either a host scalar or a sort Bootstrap emits, not both: " +
    (hostScalars.keySet & preludeSorts.keySet).mkString(", "))

end TypeGen

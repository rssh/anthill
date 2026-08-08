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
      if fields.isEmpty then "Unit"
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
          // WI-1055 B3. Either the written occurrence is partial (`List` where
          // `List[T]` is needed — Scala has no bare type constructor in a value
          // position) or the scala_std map entry is not arity-compatible at all:
          // anthill `Stream[Element, E]` maps to `LazyList`, which takes ONE
          // parameter, so `Iterable` emitted `LazyList[Element, E]`. Whether the
          // entry is wrong or the mapping is unrepresentable is WI-1021's question;
          // until it is settled a refusal beats an emission.
          throw BootstrapError(
            s"${scope.decl}: `$leaf` maps to Scala `$scalaName`, which takes $arity " +
            s"type argument(s), but ${args.length} were written. A partial " +
            "application has no Scala spelling here, and an arity-incompatible " +
            "scala_std map entry is not a name swap",
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

  /** The `scala_std` type map, as (Scala name, Scala ARITY).
    *
    * The arity is the SCALA side's, and it is what makes an unrepresentable entry
    * detectable instead of emitted: anthill's `Stream` has two parameters and
    * `LazyList` has one, so every occurrence is an error rather than a rename.
    *
    * An unknown name gets NO entry — the pass-through this replaced
    * (`Names.scalaTypeName(short)`) is precisely how an unresolvable name reached
    * the output looking like a project-defined sort. `Numeric` was the sharpest
    * case: it passed through and bound to `scala.math.Numeric`, so `field.anthill`
    * COMPILED against a type from a different library.
    *
    * A SECOND SOURCE OF TRUTH, AND IT HAS DRIFTED. `stdlib/anthill/realization/
    * scala_std.anthill` declares this same table as `type_map` facts and says of
    * itself "Codegen reads this from the KB; changing it changes generated code
    * without touching the codegen implementation" — nothing reads it. Measured
    * disagreements today: the fact says `Int64 -> Int64` (a WI-068 rename artifact;
    * rust_std says `Int64 -> i64`, and Scala has no `Int64`), the fact carries
    * `Duration` and `Timestamp` entries this table does not, and this table carries
    * `Unit` and `Nothing` the fact does not. The `arity` column has no counterpart
    * in the `TypeMapping` schema at all, so it cannot be cross-checked even in
    * principle. Bootstrap reads no KB by design (proposal 034), so the fix is the
    * shape `buildSbt` already has — the caller resolves the profile and passes the
    * table in — and it needs the arity schema question settled first: WI-1060. Do
    * not add entries here to "catch up" with the fact, because whether an anthill
    * sort should map to a host type AT ALL is WI-1021's open question and
    * `Duration` is one of the sorts it covers (primitives.anthill declares it as a
    * sort, and Bootstrap emits that).
    */
  def preludeMapping(anthillLeaf: String): Option[Placement.Known] =
    anthillLeaf match
      case "Int64" => known("Int", 0)
      case "BigInt" => known("BigInt", 0)
      case "Float" => known("Double", 0)
      case "Bool" => known("Boolean", 0)
      case "String" => known("String", 0)
      case "Unit" => known("Unit", 0)
      case "Nothing" => known("Nothing", 0)
      case "List" => known("List", 1)
      case "Option" => known("Option", 1)
      case "Pair" => known("Tuple2", 2)
      case "Set" => known("Set", 1)
      case "Map" => known("Map", 2)
      case "Stream" => known("LazyList", 1)
      case _ => None

  private def known(scalaName: String, arity: Int): Option[Placement.Known] =
    Some(Placement.Known(scalaName, arity))

end TypeGen

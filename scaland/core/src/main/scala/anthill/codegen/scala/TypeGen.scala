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
      // The arguments ride in UNRENDERED (WI-1062). An argument in an erased
      // effect slot is dropped, and rendering it first would refuse on the very
      // construct — a written row, an effect parameter's name — that erasure
      // exists to remove. So the head is placed first, and only the surviving
      // arguments are rendered.
      named(sym, n, bindings.map(_.bound), scope)
    case TypeExpr.TupleType(fields) =>
      // The empty tuple goes through the profile's scalar table rather than a literal
      // "Unit": one answer to "what is anthill's Unit in Scala", so the two cannot
      // drift (they had — this arm emitted a bare `Unit` after the table was `_root_`-
      // anchored). `required` and not a fallback: an absent entry is a profile edit
      // that broke a rendering path, and a silent bare `Unit` is how it would hide.
      if fields.isEmpty then scope.requiredScalar("Unit", "the empty tuple type `()`")
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
      // WI-1055 B2, ANSWERED BY WI-1062 for the case that made it eight prelude
      // files — and this is what is LEFT of it.
      //
      // The question was never what a row erases to; it is what the SLOT is. Where
      // the slot is an effect PARAMETER (`Stream`'s `effects E = ?`), the parameter
      // itself is erased from the emitted type (§2.8a) and the argument goes with
      // the slot — dropped in `named` before it can reach here. Reaching here means
      // the opposite: the declaration says this slot is an ordinary `sort X = ?`,
      // so the row is a type-level VALUE, not an erasable annotation.
      //
      // delay.anthill IS THAT CASE and is why this arm survives rather than
      // becoming unreachable. Its graded monad (proposal 047) holds the captured
      // effect set in an ordinary parameter deliberately — `pure` returns
      // `M[T = A, E = {}]` and `delay` returns `M[T = A, E = EffP]`, and those two
      // are DIFFERENT types. Erasing `E` would make them one, which is the whole
      // content of the grading. `Any` — what this emitted before WI-1055 — does the
      // same collapse while compiling.
      throw BootstrapError(
        s"${scope.decl}: a written effect row stands in an ORDINARY type-parameter " +
        "slot, so it is a type-level value and not an erasable effect annotation. " +
        "scala_std erases effects (§2.8) and drops an effect PARAMETER with its " +
        "argument (§2.8a), but this slot is declared `sort X = ?` — a graded monad's " +
        "captured-effect index (proposal 047), which Scala has no term for and which " +
        "erasure would collapse",
        scope.declSpan)

  /** One written name, with its arguments still unrendered.
    *
    * ERASURE HAPPENS HERE, and which END decides is the whole of WI-1062's rule
    * (`docs/scala-forward-mapping.md` §2.8a). Where Bootstrap can see the target's
    * DECLARATION — the enclosing sort, a type this file emits, a prelude-sort table
    * entry, a higher-kinded parameter's members — the declaration says which slots
    * are `effects E = ?` and those arguments are dropped whatever was written in
    * them, including a plain name (`Stream[Element, E]`) that nothing else marks.
    * Where it cannot — an [[Placement.Ambient]] name, whose parameters live in a
    * file Bootstrap has not read — the ARGUMENT decides, via
    * [[TypeScope.isEffectArgument]].
    *
    * The two agree wherever both could run, and the declaration answering first is
    * what makes delay.anthill's graded monad a refusal rather than a silent
    * collapse: a row in an ordinary `sort E = ?` slot is a type-level value.
    */
  private def named(
    sym: SymbolTable, n: Name, args: IndexedSeq[TypeExpr], scope: TypeScope
  ): String =
    val leaf = sym.name(n.last)
    def rendered(as: IndexedSeq[TypeExpr]): IndexedSeq[String] = as.map(render(sym, _, scope))
    // The argument-side rule. Reached only where nothing declares the slots.
    def erasedByArgument: IndexedSeq[TypeExpr] = args.filterNot(scope.isEffectArgument(sym, _))
    scope.place(leaf) match
      // The two placements whose argument COUNT passes through unchecked. A proper
      // type parameter has no arity to check against (a higher-kinded `M[A]` takes
      // arguments, a proper `V` does not) and an ambient name's lives in a file
      // Bootstrap has not read. Over-application is therefore left to the Scala
      // compiler ("V does not take type parameters"), which is a clear diagnostic
      // and a shape no stdlib file writes — unlike the map-entry mismatch below,
      // whose point is that the ENTRY is wrong, not the use, and which no compiler
      // message would attribute correctly.
      case Placement.TypeParam(name, memberArity) =>
        // A higher-kinded parameter DOES declare its members, and none of them can
        // be an effect slot (the binder grammar has no `effects` spelling), so a
        // matching application erases NOTHING — which is what refuses
        // delay.anthill's `M[T = A, E = {}]` rather than collapsing it. A proper
        // parameter declares nothing (arity 0) and a bare mention writes nothing,
        // so both take the argument rule, where they are no-ops.
        //
        // AN APPLICATION THAT DOES NOT MATCH falls to the argument rule too, and
        // that is the one place a row could be dropped where a declaration says it
        // should not. It takes an already-malformed application to reach — `M[A]`
        // or `M[A, {}, X]` against `M[T, E]` — which the Scala compiler refuses
        // whichever way this goes, and no corpus file writes one.
        val keep = if memberArity == args.length then args else erasedByArgument
        name + brackets(rendered(keep))
      case Placement.Ambient(name) => name + brackets(rendered(erasedByArgument))
      case Placement.Enclosing(self) =>
        // WI-1055 A3: a BARE mention of the enclosing sort means "with my own
        // parameters" in anthill, and Scala has no bare spelling for that. This is
        // also what stops the sort's own name being rewritten through the prelude
        // map — pair.anthill's `operation fst(p: Pair) -> A` emitted `Tuple2`, a
        // DIFFERENT type from the `enum Pair[A, B]` three lines up (WI-1021).
        //
        // The bare form re-attaches what the sort EMITS (`self.params`, already
        // effect-free); an explicit application is checked against what it WRITES
        // (`self.kinds.written`), because that is what the anthill declaration says
        // and what a sibling occurrence spells.
        if args.isEmpty then self.scalaName + brackets(self.params)
        else if args.length != self.kinds.written then
          throw BootstrapError(
            s"${scope.decl}: `$leaf` is the enclosing sort, which declares " +
            s"${self.kinds.written} type parameter(s)${erasureNote(self.kinds)}, but " +
            s"${args.length} argument(s) were written. The parameters Bootstrap emits " +
            "and the ones the declaration writes have diverged",
            n.span)
        else self.scalaName + brackets(rendered(self.kinds.keepTypeArgs(args)))
      case Placement.Known(scalaName, kinds) =>
        if args.length != kinds.written then
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
          // see [[ScalaTypes]] — so every entry's arity is now that of the type it
          // names, and since WI-1060 it is the declaring file's own count rather
          // than a hand-copy of it.
          throw BootstrapError(
            s"${scope.decl}: `$leaf` maps to Scala `$scalaName` and declares " +
            s"${kinds.written} type parameter(s)${erasureNote(kinds)}, but " +
            s"${args.length} were written. anthill leaves a " +
            "sort's parameters implicit where they are in scope and allows a PARTIAL " +
            "named binding; Scala has no bare type constructor in this position, so " +
            "there is no spelling to emit",
            n.span)
        else scalaName + brackets(rendered(kinds.keepTypeArgs(args)))
      case Placement.ErasedEffect(name) =>
        // WI-1062. The name denotes an effect ROW — a sort's `effects E = ?`
        // parameter, or an operation type parameter its signature only ever uses in
        // an effect position. An erased slot is dropped WITH its argument before
        // anything renders it, so getting here means the row was written where the
        // declaration says a type belongs.
        throw BootstrapError(
          s"${scope.decl}: `$name` is an effect row, not a type. scala_std erases " +
          "effects (§2.8), so it has no Scala form; it is emittable only in a slot " +
          "that erases with it, and this slot is declared to hold a type",
          n.span)
      case Placement.Unplaceable(reason) =>
        // WI-1055 B1. The name would reach the output as a bare identifier naming
        // nothing in the emitted tree. This is how `Term`, `NodeOccurrence` and
        // `Type` shipped: not as a typo Bootstrap could not rule out, but as a
        // reference Bootstrap could already show unreachable and emitted anyway.
        throw BootstrapError(s"${scope.decl}: cannot emit the type `$leaf` — $reason", n.span)

  private def brackets(args: IndexedSeq[String]): String =
    if args.isEmpty then "" else args.mkString("[", ", ", "]")

  /** The clause an arity refusal needs once erasure exists (WI-1062): a reader
    * counting the parameters of the EMITTED Scala type would otherwise get a
    * different number from the one the message states, and conclude the message
    * was wrong. Empty when nothing erases, so the common refusal reads as before. */
  private def erasureNote(kinds: ParamKinds): String =
    val erased = kinds.written - kinds.emitted
    if erased == 0 then ""
    else s" (${kinds.emitted} emitted; $erased erased as effect row(s))"

  // ── Prelude names: host type or anthill type ──────────────────────────────
  //
  // The tables themselves are [[ScalaTypes]], resolved by the CALLER (WI-1060) and
  // reached through `scope.types`: the scalars from the profile fact, the prelude
  // sorts from the prelude's own parsed files. What used to live here was a
  // hardcoded copy of both, and `scala_std.anthill`'s claim about itself — "codegen
  // reads this from the KB; changing it changes generated code without touching the
  // codegen implementation" — was false for as long as it did.
  //
  // WI-1021 DECIDED WHICH NAME GOES IN WHICH TABLE and that decision is unchanged;
  // its reasoning, and the defects it measured, are on [[ScalaTypes]].
  //
  // AN IMPORTED NAME SHADOWS THE TABLE and a SIBLING-FILE one does not, which is the
  // line the derived table forced. `TypeScope.shadowsThePrelude` runs before the
  // prelude lookup, so a project writing `import my.lib.{Numeric}` is refused rather
  // than emitted as `_root_.anthill.prelude.Numeric` — a different library's type,
  // which is what it did while the lookup came first. What is still NOT checked is a
  // name a project declares in a sibling FILE with no import: `fileTypes` is per-file
  // and the caller's auto-import set is the prelude, so a project's own `Pair`
  // reaches the prelude's. Closing that means resolving a project's whole file set
  // the way `ScalaTypes.resolve` resolves the prelude's — the same package-keyed
  // table `FileTypes` needs one scope down, which is why WI-1067 owns both.

end TypeGen

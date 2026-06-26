package anthill.parse

import anthill.intern.{TermSymbol, SymbolTable}
import anthill.term.{Term, TermId, VarId, Literal, OrderedDouble}
import anthill.span.Span
import fastparse.*
import scala.collection.mutable.{ArrayBuffer, HashMap}

object AnthillParser:

  def parse(source: String, fileName: String = "<input>"): Either[IndexedSeq[ParseError], ParsedFile] =
    val symbols = SymbolTable()
    val terms = SimpleTermStore()
    val errors = ArrayBuffer.empty[ParseError]
    val parser = new AnthillParserImpl(source, fileName, symbols, terms, errors)
    fastparse.parse(source, parser.sourceFile(using _)) match
      case Parsed.Success(items, _) =>
        if errors.nonEmpty then Left(errors.toIndexedSeq)
        else Right(ParsedFile(ArrayBuffer.from(items), symbols, terms))
      case f: Parsed.Failure =>
        val idx = f.index
        errors += ParseError(s"Parse error at $idx: ${f.msg}", Span(fileName, idx, idx, 0, 0, 0, 0))
        Left(errors.toIndexedSeq)

end AnthillParser

// Token-level parsers — no whitespace between characters
private object Tokens:
  import fastparse.NoWhitespace.*

  def identToken[$: P]: P[String] =
    P(CharIn("a-zA-Z_") ~ CharsWhileIn("a-zA-Z0-9_\\-", 0)).!

  def variableToken[$: P]: P[String] =
    P("?" ~ (CharIn("a-zA-Z_") ~ CharsWhileIn("a-zA-Z0-9_\\-", 0)).?.!)

  def stringToken[$: P]: P[String] =
    P("\"" ~ CharsWhile(_ != '"', 0).! ~ "\"")

  def floatToken[$: P]: P[String] =
    P(("-".? ~ CharsWhileIn("0-9", 1) ~ "." ~ CharsWhileIn("0-9", 1)).!)

  def intToken[$: P]: P[String] =
    P(("-".? ~ CharsWhileIn("0-9", 1)).!)

  def boolToken[$: P]: P[String] =
    P(identToken.filter(s => s == "true" || s == "false"))

  def opToken[$: P]: P[String] =
    P(CharsWhileIn("+\\-*/%^|&=<>~", 1).!)

end Tokens


private class AnthillParserImpl(
  source: String,
  fileName: String,
  symbols: SymbolTable,
  terms: SimpleTermStore,
  errors: ArrayBuffer[ParseError]
):

  // ── Variable scoping ─────────────────────────────────────────

  private var nextVar: Int = 0
  private val varScope: HashMap[TermSymbol, VarId] = HashMap.empty

  private def resetVarScope(): Unit = varScope.clear()

  private def getOrCreateVar(sym: TermSymbol): VarId =
    varScope.getOrElseUpdate(sym, {
      val id = nextVar; nextVar += 1; VarId(id, sym)
    })

  private def freshAnonymousVar(): VarId =
    val anonSym = symbols.intern("?")
    val id = nextVar; nextVar += 1; VarId(id, anonSym)

  /** A fresh anonymous type variable — the `?` an unspecified `sort X = ?`
    * carries. Mirrors rustland's shared `fresh_anon_type_var` (convert.rs),
    * reused by `variableType`'s anonymous branch and the WI-451 type-param
    * desugar so the `?`-var IR cannot drift (the loader's `sort T = ?`
    * type-param arm matches on exactly this `TypeExpr.Variable` shape). */
  private def freshAnonTypeVar(): TypeExpr.Variable =
    TypeExpr.Variable(terms.alloc(Term.Var(freshAnonymousVar())), IndexedSeq.empty)

  // ── Helpers ──────────────────────────────────────────────────

  private def mkSpan(s: Int, e: Int): Span = Span(fileName, s, e, 0, 0, 0, 0)
  private def intern(s: String): TermSymbol = symbols.intern(s)

  // ── Custom whitespace ────────────────────────────────────────

  given ws: Whitespace with
    def apply(ctx: P[?]): P[Unit] =
      var index = ctx.index
      val input = ctx.input
      val length = input.length
      var continue = true
      while continue && index < length do
        val c = input(index)
        if c == ' ' || c == '\t' || c == '\n' || c == '\r' then
          index += 1
        else if index + 1 < length && c == '-' && input(index + 1) == '-' then
          index += 2
          while index < length && input(index) != '\n' do index += 1
        else if index + 1 < length && c == '{' && input(index + 1) == '-' then
          index += 2
          var depth = 1
          while index + 1 < length && depth > 0 do
            if input(index) == '{' && input(index + 1) == '-' then
              depth += 1; index += 2
            else if input(index) == '-' && input(index + 1) == '}' then
              depth -= 1; index += 2
            else index += 1
        else if index + 1 < length && c == '{' && input(index + 1) == '<' then
          // Doc-comment block: `{< ... >}` (used by stdlib sort.anthill).
          index += 2
          while index + 1 < length &&
              !(input(index) == '>' && input(index + 1) == '}') do
            index += 1
          if index + 1 < length then index += 2
        else
          continue = false
      ctx.freshSuccessUnit(index)

  // ── Lexical ──────────────────────────────────────────────────

  private def ident[$: P]: P[TermSymbol] = P(Tokens.identToken).map(intern)

  private def keyword[$: P](kw: String): P[Unit] =
    P(Tokens.identToken.filter(_ == kw)).map(_ => ())

  private def name[$: P]: P[Name] =
    P(Index ~ ident ~ ("." ~ ident).rep ~ Index).map { case (s, first, rest, e) =>
      Name(first +: rest.toIndexedSeq, mkSpan(s, e))
    }

  private def simpleName[$: P]: P[Name] =
    P(Index ~ ident ~ Index).map { case (s, sym, e) => Name.simple(sym, mkSpan(s, e)) }

  // ── Literals ─────────────────────────────────────────────────

  private def stringLiteral[$: P]: P[TermId] =
    P(Tokens.stringToken).map(s => terms.alloc(Term.Const(Literal.StringLit(s))))

  private def floatLiteral[$: P]: P[TermId] =
    P(Tokens.floatToken).map(s => terms.alloc(Term.Const(Literal.FloatLit(OrderedDouble(s.toDouble)))))

  private def integerLiteral[$: P]: P[TermId] =
    P(Tokens.intToken).map(s => terms.alloc(Term.Const(Literal.IntLit(s.toLong))))

  private def boolLiteral[$: P]: P[TermId] =
    P(Tokens.boolToken).map(s => terms.alloc(Term.Const(Literal.BoolLit(s == "true"))))

  private def literal[$: P]: P[TermId] =
    P(stringLiteral | floatLiteral | integerLiteral | boolLiteral)

  // ── Variables ────────────────────────────────────────────────

  private def variable[$: P]: P[TermId] =
    P(Tokens.variableToken ~ fnArgsList.?).map { case (varName, args) =>
      val varTid =
        if varName.isEmpty then terms.alloc(Term.Var(freshAnonymousVar()))
        else terms.alloc(Term.Var(getOrCreateVar(intern(varName))))
      args match
        case None => varTid
        case Some(rawArgs) =>
          // Higher-order predicate call `?P(a, b)` → `ho_apply(?P, a, b)`.
          // Mirrors rustland/anthill-core/src/parse/convert.rs:437.
          val posArgs = ArrayBuffer(varTid)
          val namedArgs = ArrayBuffer.empty[(TermSymbol, TermId)]
          rawArgs.foreach {
            case Left(tid) => posArgs += tid
            case Right((k, v)) => namedArgs += ((k, v))
          }
          terms.alloc(Term.Fn(intern("ho_apply"), IArray.from(posArgs), IArray.from(namedArgs)))
    }

  // ── Types ────────────────────────────────────────────────────

  private def typeExpr[$: P]: P[TypeExpr] = P(arrowType | nonArrowType)

  private def nonArrowType[$: P]: P[TypeExpr] =
    P(parameterizedType | tupleType | variableType | simpleType)

  private def simpleType[$: P]: P[TypeExpr] = P(name).map(TypeExpr.Simple(_))

  private def parameterizedType[$: P]: P[TypeExpr] =
    P(name ~ "[" ~ sortBinding.rep(1, sep = ",") ~ "]").map { case (n, bs) =>
      TypeExpr.Parameterized(n, bs.toIndexedSeq)
    }

  private def sortBinding[$: P]: P[SortBinding] =
    P(
      (name ~ "=" ~ commonTypeExpr).map { case (n, t) => SortBinding(Some(n), t) } |
      commonTypeExpr.map(t => SortBinding(None, t))
    )

  /** The value slot of a sort binding — what may appear as a type argument.
    * Mirrors rustland's `_common_type_expr`: a type, a literal value-in-type
    * (`Denoted`, WI-302), or a written effect-row (`EffectRow`, WI-375).
    * Effect-row and literal are tried before `typeExpr`: a `{`-prefixed row is
    * disjoint from every type form, and a literal would otherwise be misread
    * (`true`/`false` as a `simple_type` name). A projection like `l.T` needs no
    * special form — it parses through `typeExpr` as a dotted name. */
  private def commonTypeExpr[$: P]: P[TypeExpr] =
    P(effectRowType | denotedLiteral | typeExpr)

  /** WI-302: a literal in a type-argument slot (`Vector[Int64, 3]`, `Fin[n = 8]`). */
  private def denotedLiteral[$: P]: P[TypeExpr] =
    P(literal).map(TypeExpr.Denoted(_))

  /** WI-375: a written effect-row `{ e1, e2, … }` (or empty `{}`) in a
    * type-argument value slot. Mirrors rustland's `effect_row` node
    * (`{ commaSep(_effect_type) }`). The cut after `{` commits — a `{` in a
    * binding value is always a row, never a set literal (this retired the old
    * `setType` rule, whose only use — `Collection[Effect = {}]` — lands here). */
  private def effectRowType[$: P]: P[TypeExpr] =
    P("{" ~/ effectType.rep(sep = ",") ~ "}").map(es => TypeExpr.EffectRow(es.toIndexedSeq))

  private def variableType[$: P]: P[TypeExpr] =
    P(Tokens.variableToken).map { varName =>
      if varName.isEmpty then freshAnonTypeVar()
      else TypeExpr.Variable(terms.alloc(Term.Var(getOrCreateVar(intern(varName)))), IndexedSeq.empty)
    }

  private def arrowType[$: P]: P[TypeExpr] =
    P(arrowParams ~ "->" ~ typeExpr ~ ("@" ~ effectSet).?).map {
      case (params, ret, effs) => TypeExpr.Arrow(params, ret, effs.getOrElse(IndexedSeq.empty))
    }

  /** Effect set, shared by arrow `@` and operation `effects`. Mirrors
    * rustland's `_effect_set` (`commaSep`, WI-440):
    *   - single:  `E`            → `IndexedSeq(E)`
    *   - braced:  `{E1, E2, …}`  → `IndexedSeq(E1, E2, …)`
    *   - empty:   `{}`           → `IndexedSeq.empty` (explicit closed-empty row)
    *
    * The braced form allows ZERO elements (WI-440: `@ {}` / `effects {}`
    * is the explicit pure/closed-empty row). The cut after `{` commits to
    * the braced branch so `{}` is never rescued as a `setType`. */
  private def effectSet[$: P]: P[IndexedSeq[TypeExpr]] =
    P(
      ("{" ~/ effectType.rep(sep = ",") ~ "}").map(_.toIndexedSeq) |
      effectType.map(IndexedSeq(_))
    )

  /** Single effect type. Mirrors rustland's `_effect_type` (WI-092 +
    * WI-327): the base `simple_type | parameterized_type | variable_term`
    * (`simpleEffect`) plus the proposal-045 surface algebra — explicit
    * `+E` presence and `-E` absence (lacks-constraint). `merge(...)` union
    * sugar is not yet used by any loaded file, so it is omitted here.
    * Tuple and arrow types are deliberately rejected — neither is
    * meaningful as an effect, and accepting a leading `(` would let a typo
    * like `effects (Modify self)` consume the `(` as an arrow/tuple type. */
  private def effectType[$: P]: P[TypeExpr] =
    P(parenGuardedEffect | effectPresence | effectAbsence | guardedEffect | simpleEffect)

  /** `_simple_effect` (WI-327): a bare effect with no composite prefix —
    * what `+`/`-`/`:- guard` attach to. */
  private def simpleEffect[$: P]: P[TypeExpr] =
    P(parameterizedType | variableType | simpleType)

  /** WI-478 (proposal 048): a bare guarded effect-row element `E :- guard`. The
    * `:- guard` binds the SINGLE preceding effect, per-element — the row `,`
    * stays the OUTER separator, so the guard is a single `_term`, not a
    * conjunction (a conjunctive guard uses the parenthesized form). Tried before
    * `simpleEffect` and backtracks cleanly when no `:-` follows (no cut before
    * `:-`). Mirrors rustland's `guarded_effect`. */
  private def guardedEffect[$: P]: P[TypeExpr] =
    P(simpleEffect ~ ":-" ~/ term).map { case (label, g) =>
      TypeExpr.EffectGuarded(label, IndexedSeq(g))
    }

  /** WI-478: the parenthesized guarded form `( E :- g1, g2 )` — the `:-` body is
    * a full Horn `rule_body` delimited by `)`, so a conjunctive guard is
    * expressible. The mandatory `:-` preserves the `(`-typo protection (a bare
    * `( E )` is still not an admissible effect). Mirrors rustland's
    * `paren_guarded_effect`. */
  private def parenGuardedEffect[$: P]: P[TypeExpr] =
    P("(" ~ simpleEffect ~ ":-" ~/ term.rep(1, sep = ",") ~ ")").map { case (label, gs) =>
      TypeExpr.EffectGuarded(label, gs.toIndexedSeq)
    }

  /** `+E` explicit presence → `present(E)`; `-E` absence/lacks → `absent(E)`
    * (mirrors rustland's `effect_presence`/`effect_absence` lowering). scaland
    * has no typer, so these lower to plain functor terms that round-trip
    * through `typeExprToRef`; the lacks-semantics live only in the rust typer. */
  private def effectPresence[$: P]: P[TypeExpr] =
    P("+" ~/ simpleEffect).map(wrapEffectOp("present"))

  private def effectAbsence[$: P]: P[TypeExpr] =
    P("-" ~/ simpleEffect).map(wrapEffectOp("absent"))

  private def wrapEffectOp(op: String)(e: TypeExpr): TypeExpr =
    val inner = typeExprToRef(e)
    TypeExpr.Variable(terms.alloc(Term.Fn(intern(op), IArray(inner), IArray.empty)), IndexedSeq.empty)

  private def arrowParams[$: P]: P[IndexedSeq[TypeExpr]] =
    P("(" ~ arrowParam.rep(sep = ",") ~ ")").map(_.toIndexedSeq)

  /** An arrow parameter may carry an optional binder NAME — `(x: Elem) -> Bool`
    * — so a dependent-absence row `-Modify[x]` can reference it (WI-441).
    * scaland has no typer, so the binder name is dropped and only the type is
    * kept (matching scaland's single-param arrow lowering, which never
    * captured binder names). NO cut after `:`, so a NAMED TUPLE type
    * `(a: T, b: U)` — for which arrow's `->` is absent — still backtracks
    * cleanly to `tupleType`. */
  private def arrowParam[$: P]: P[TypeExpr] =
    P((ident ~ ":" ~ typeExpr).map { case (_, t) => t } | typeExpr)

  case class TupleField(name: TermSymbol, ty: TypeExpr)

  private def tupleType[$: P]: P[TypeExpr] =
    P(
      ("(" ~ ")").map(_ => TypeExpr.TupleType(IndexedSeq.empty)) |
      ("(" ~ tupleTypeArg ~ ("," ~/ tupleTypeArg).rep(1) ~ ")").map { case (first, rest) =>
        TypeExpr.TupleType((first +: rest.toIndexedSeq).map(f => (f.name, f.ty)))
      }
    )

  private def tupleTypeArg[$: P]: P[TupleField] =
    P(
      (ident ~ ":" ~ typeExpr).map { case (n, t) => TupleField(n, t) } |
      typeExpr.map(t => TupleField(intern("_"), t))
    )

  // ── Terms ────────────────────────────────────────────────────

  private def term[$: P]: P[TermId] =
    P(atomWithFieldAccess ~ (infixOp ~ atomWithFieldAccess).rep).map { case (first, pairs) =>
      buildInfix(first, pairs)
    }

  /** A `_term` for an operation's `requires` / `ensures` clause body. Identical
    * to `term` except a bare `=` is treated as the operation-body separator
    * (`= <body>`) rather than an equality goal ONLY when it introduces an
    * expr-body-only form — see `clauseInfixOp`. So `requires Eq[T] = match l …`
    * gives the op the `match` body, while `ensures result = x` keeps
    * `result = x` as the postcondition eq goal — both matching rustland's GLR. */
  private def clauseTerm[$: P]: P[TermId] =
    P(atomWithFieldAccess ~ (clauseInfixOp ~ atomWithFieldAccess).rep).map { case (first, pairs) =>
      buildInfix(first, pairs)
    }

  private def buildInfix(first: TermId, pairs: Seq[(TermSymbol, TermId)]): TermId =
    if pairs.isEmpty then first
    else
      val operands = ArrayBuffer(first)
      val opSymbols = ArrayBuffer.empty[TermSymbol]
      pairs.foreach { case (op, operand) => opSymbols += op; operands += operand }
      Pratt.desugar(operands.toIndexedSeq, opSymbols.toIndexedSeq, symbols.name, terms.alloc, symbols.intern)

  /** A rule-body goal: the cut control primitive `!` (WI-568), a goal-position
    * `let ?v = expr` binding (WI-522), or a regular `_term`. Mirrors rustland's
    * `_goal` (`choice($.cut, $.let_binding, $._term)`). `letGoal` precedes `term`
    * (so the `let` keyword is not eaten as an `Ident`); `cutGoal` follows `term`
    * (so `! atom` stays prefix negation `not(atom)` — only a bare `!`, where
    * `term` fails for lack of an operand, becomes the cut). */
  private def goalTerm[$: P]: P[TermId] =
    P(letGoal | term | cutGoal)

  /** Goal-position `let ?v = expr` (proposal 049) → `unify(?v, expr)`, the same
    * IR `<=>` builds. Distinct from the expression-position `let_chain` (which
    * carries a continuation body). The cut after `let` is safe — no goal is the
    * bare word `let`, and a longer identifier (`lettuce`) never matches the
    * keyword (maximal-munch lexing). */
  private def letGoal[$: P]: P[TermId] =
    P(keyword("let") ~/ variable ~ "=" ~/ term).map { case (v, e) =>
      terms.alloc(Term.Fn(intern("unify"), IArray(v, e), IArray.empty))
    }

  /** Cut (`!`) — kernel control primitive (proposal 033.1 / WI-568): a nullary
    * `cut` goal that commits to the current rule invocation. scaland has no
    * resolver-side cut semantics; the goal just round-trips as a `cut()` term. */
  private def cutGoal[$: P]: P[TermId] =
    P("!").map(_ => terms.alloc(Term.Fn(intern("cut"), IArray.empty, IArray.empty)))

  /** A base atom followed by a dotted access/call chain. WI-278: a chain
    * segment over a *value* receiver (`?x`, a call result, a literal, …)
    * becomes `dot_apply(receiver, name, ...args)`; a *name* receiver keeps
    * the `field_access` builtin. `Foo.bar` never reaches here — `name`
    * greedily consumes consecutive `.ident`, so the only bases carrying
    * trailing dots are values. A method call `?x.m(args)` is one segment
    * with `(args)`; a plain field `?x.f` is one segment with no args. */
  private def atomWithFieldAccess[$: P]: P[TermId] =
    P(atomBase ~ dotSegment.rep).map { case (base, segs) =>
      segs.foldLeft(base) { (obj, seg) =>
        val (field, callArgs) = seg
        // A name receiver carrying call args (`Foo.bar(args)`) is consumed by
        // `name`/`nameSuffix` and never reaches here, so a name receiver always
        // has `callArgs == None`; route any value receiver — incl. the
        // call/instantiation `Fn` shapes — through `dot_apply` so args are never
        // dropped.
        if isValueReceiver(obj) || callArgs.isDefined then buildDotApply(obj, field, callArgs)
        else
          val fieldRef = terms.alloc(Term.Ref(field))
          terms.alloc(Term.Fn(fieldAccessSym, IArray(obj, fieldRef), IArray.empty))
      }
    }

  /** One `.name` access, optionally a call `.name(args)` (WI-278). */
  private def dotSegment[$: P]: P[(TermSymbol, Option[IndexedSeq[Either[TermId, (TermSymbol, TermId)]]])] =
    P("." ~ ident ~ fnArgsList.?)

  private lazy val fieldAccessSym = intern("field_access")
  private lazy val dotApplySym = intern("dot_apply")

  /** WI-278: whether `tid` denotes a runtime *value* (→ `dot_apply`) rather
    * than a sort/namespace *name* (→ `field_access`). Walks the `field_access`
    * chain to its root atom: a `Ref`/`Ident` root is a name; anything else (a
    * `Var`, a call/instantiation `Fn`, a literal, a collection) is a value.
    * Mirrors rustland's `is_value_receiver` CST walk. (Scaland collapses a
    * call and an instantiation to the same `Fn` shape, so `Name[B].field` —
    * a name receiver in rustland — reads as a value here; this affects only
    * that edge form, which no loaded stdlib uses.) */
  private def isValueReceiver(tid: TermId): Boolean =
    terms.get(tid) match
      case Term.Ident(_) => false
      case Term.Ref(_)   => false
      case Term.Fn(f, posArgs, _) if f == fieldAccessSym && posArgs.nonEmpty =>
        isValueReceiver(posArgs(0))
      case _ => true

  /** WI-278: build `dot_apply(receiver, Ident(name), ...positional, named...)`,
    * matching rustland's `BuildFrame::DotApply` drain layout. */
  private def buildDotApply(
    receiver: TermId,
    field: TermSymbol,
    callArgs: Option[IndexedSeq[Either[TermId, (TermSymbol, TermId)]]]
  ): TermId =
    val nameTerm = terms.alloc(Term.Ident(field))
    val posArgs = ArrayBuffer(receiver, nameTerm)
    val namedArgs = ArrayBuffer.empty[(TermSymbol, TermId)]
    callArgs.foreach(_.foreach {
      case Left(tid)     => posArgs += tid
      case Right((k, v)) => namedArgs += ((k, v))
    })
    terms.alloc(Term.Fn(dotApplySym, IArray.from(posArgs), IArray.from(namedArgs)))

  private def atomBase[$: P]: P[TermId] =
    P(
      literal |
      variable |
      refTerm |
      prefixTerm |
      fnOrInstOrIdent |
      collectionLiteral |
      setLiteral |
      boundedQuantification |
      tupleLiteralOrParenExpr
    )

  /** WI-027: bounded quantification over a collection's elements, a rule-body
    * goal — `(forall ?x in xs: P(?x))` → `forall_in(?x, xs, tuple(P(?x)))` and
    * `(some ?x in xs: …)` → `some_in(…)`. Parenthesised, tried before the plain
    * `(` paren/tuple forms; it backtracks cleanly when the leading token after
    * `(` is not `forall`/`some` followed by a `?`-binder and `in` (no cut until
    * after `in`), so the nested-implication `( forall (?h, ?rest), … )` form and
    * ordinary paren exprs still parse. Mirrors rustland's
    * `convert_bounded_quantification`. */
  private def boundedQuantification[$: P]: P[TermId] =
    P("(" ~ (keyword("forall").map(_ => "forall_in") | keyword("some").map(_ => "some_in"))
      ~ boundedBinderVar ~ keyword("in") ~/ term ~ ":" ~ goalTerm.rep(1, sep = ",") ~ ")").map {
      case (functor, binder, collection, body) =>
        val bodyTuple = terms.alloc(Term.Fn(intern("tuple"), IArray.from(body), IArray.empty))
        terms.alloc(Term.Fn(intern(functor), IArray(binder, collection, bodyTuple), IArray.empty))
    }

  /** The binder of a bounded quantifier MUST be a named variable (`?x`), not the
    * anonymous `?` — an anon binder never flows into the body, so the quantifier
    * would bind nothing. Rejecting the empty name (which fails the alternative,
    * leaving the `(`-dispatch to error out) mirrors rustland's loud rejection
    * (`convert_bounded_quantification`) over silently iterating an unbound body.
    * Shares the binder's `VarId` with its body uses via `getOrCreateVar`. */
  private def boundedBinderVar[$: P]: P[TermId] =
    P(Tokens.variableToken.filter(_.nonEmpty))
      .map(n => terms.alloc(Term.Var(getOrCreateVar(intern(n)))))

  // ── Name suffix ADT ──────────────────────────────────────────

  private enum NameSuffix:
    case FnArgs(args: IndexedSeq[Either[TermId, (TermSymbol, TermId)]])
    case InstArgs(bindings: IndexedSeq[SortBinding])
    // WI-269: `Name[bindings](args)` — an instantiation term used as a
    // call callee. The bindings are call-site type arguments, the args
    // the actual call arguments.
    case InstThenFn(
      bindings: IndexedSeq[SortBinding],
      args: IndexedSeq[Either[TermId, (TermSymbol, TermId)]]
    )
    case Bare

  private def fnOrInstOrIdent[$: P]: P[TermId] =
    P(name ~ nameSuffix).map { case (n, suffix) =>
      suffix match
        case NameSuffix.FnArgs(args) =>
          val posArgs = ArrayBuffer.empty[TermId]
          val namedArgs = ArrayBuffer.empty[(TermSymbol, TermId)]
          args.foreach {
            case Left(tid) => posArgs += tid
            case Right((k, v)) => namedArgs += ((k, v))
          }
          val funcStr = n.segments.map(symbols.name).mkString(".")
          terms.alloc(Term.Fn(intern(funcStr), IArray.from(posArgs), IArray.from(namedArgs)))

        case NameSuffix.InstArgs(bindings) =>
          val funcStr = n.segments.map(symbols.name).mkString(".")
          val posArgs = ArrayBuffer.empty[TermId]
          val namedArgs = ArrayBuffer.empty[(TermSymbol, TermId)]
          bindings.foreach { sb =>
            val bt = typeExprToRef(sb.bound)
            sb.param match
              case Some(p) => namedArgs += ((p.last, bt))
              case None => posArgs += bt
          }
          terms.alloc(Term.Fn(intern(funcStr), IArray.from(posArgs), IArray.from(namedArgs)))

        case NameSuffix.InstThenFn(bindings, args) =>
          val funcStr = n.segments.map(symbols.name).mkString(".")
          val posArgs = ArrayBuffer.empty[TermId]
          val namedArgs = ArrayBuffer.empty[(TermSymbol, TermId)]
          args.foreach {
            case Left(tid) => posArgs += tid
            case Right((k, v)) => namedArgs += ((k, v))
          }
          // Carry the `[A = Int, …]` call-site bindings as a `type_args`
          // named-arg child, mirroring rustland's ParseAux(SortBindings).
          // Positional bindings stay positional, `p = T` stays named,
          // matching the InstArgs lowering above.
          if bindings.nonEmpty then
            val bPos = ArrayBuffer.empty[TermId]
            val bNamed = ArrayBuffer.empty[(TermSymbol, TermId)]
            bindings.foreach { sb =>
              val bt = typeExprToRef(sb.bound)
              sb.param match
                case Some(p) => bNamed += ((p.last, bt))
                case None => bPos += bt
            }
            val aux = terms.alloc(Term.Fn(intern("type_args"), IArray.from(bPos), IArray.from(bNamed)))
            namedArgs += ((intern("type_args"), aux))
          terms.alloc(Term.Fn(intern(funcStr), IArray.from(posArgs), IArray.from(namedArgs)))

        case NameSuffix.Bare =>
          if n.isSimple then terms.alloc(Term.Ident(n.last))
          else
            var result = terms.alloc(Term.Ident(n.segments.head))
            for seg <- n.segments.tail do
              val fieldRef = terms.alloc(Term.Ref(seg))
              result = terms.alloc(Term.Fn(intern("field_access"), IArray(result, fieldRef), IArray.empty))
            result
    }

  private def nameSuffix[$: P]: P[NameSuffix] =
    P(
      fnArgsList.map(NameSuffix.FnArgs(_)) |
      // WI-269: an instantiation `[bindings]` may be followed by a call
      // `(args)`. The trailing-token after `]` disambiguates: `(` → typed
      // call (InstThenFn), otherwise a bare instantiation term (InstArgs).
      (instArgsList ~ fnArgsList.?).map {
        case (bindings, Some(args)) => NameSuffix.InstThenFn(bindings, args)
        case (bindings, None)       => NameSuffix.InstArgs(bindings)
      } |
      Pass(NameSuffix.Bare)
    )

  private def fnArgsList[$: P]: P[IndexedSeq[Either[TermId, (TermSymbol, TermId)]]] =
    P("(" ~ fnArg.rep(sep = ",") ~ ")").map(_.toIndexedSeq)

  private def fnArg[$: P]: P[Either[TermId, (TermSymbol, TermId)]] =
    // The unnamed value is an `exprBody`, not a bare `term`, so a call
    // argument may itself be a `lambda`/`match`/`if`/`let` expression
    // (e.g. `find(specs, lambda s -> match s case ...)`, stdlib cli/parse).
    // `exprBody` falls through to `term`, so ordinary args are unchanged.
    P(
      // A lambda is admissible as a named-arg value too (not just positional) —
      // `f(k: lambda x -> g(x), j: 2)` — mirroring rustland's `named_arg`
      // `value: choice($._term, $.lambda_expr)`. Its `_expr_body` cannot consume
      // the argument-separating comma, so the call stays unambiguous.
      (ident ~ ":" ~/ (lambdaExpr | term)).map { case (k, v) => Right((k, v)) } |
      exprBody.map(Left(_))
    )

  private def instArgsList[$: P]: P[IndexedSeq[SortBinding]] =
    P("[" ~ sortBinding.rep(1, sep = ",") ~ "]").map(_.toIndexedSeq)

  private def typeExprToRef(te: TypeExpr): TermId = te match
    case TypeExpr.Simple(n) => terms.alloc(Term.Ref(n.last))
    case TypeExpr.Parameterized(n, bindings) =>
      val posArgs = ArrayBuffer.empty[TermId]
      val namedArgs = ArrayBuffer.empty[(TermSymbol, TermId)]
      bindings.foreach { sb =>
        val bt = typeExprToRef(sb.bound)
        sb.param match
          case Some(p) => namedArgs += ((p.last, bt))
          case None => posArgs += bt
      }
      terms.alloc(Term.Fn(n.last, IArray.from(posArgs), IArray.from(namedArgs)))
    case TypeExpr.Variable(tid, _) => tid
    // WI-288 / WI-361: arrow and tuple types lower to the structural
    // `TypeExtractor` entities (`anthill.prelude.TypeExtractor.Arrow` /
    // `NamedTuple`), mirroring rustland's `type_expr_to_term`. Previously both
    // fell through to a `Ref("_")` sentinel, silently discarding the structure.
    case TypeExpr.Arrow(params, ret, effects) =>
      // Single param stays bare; a multi-param list collapses to a
      // positional named-tuple `_0, _1, …`, exactly as rustland does.
      val paramTerm =
        if params.length == 1 then typeExprToRef(params.head)
        else namedTupleTypeTerm(params.zipWithIndex.map((p, i) => (intern(s"_$i"), p)))
      val resultTerm = typeExprToRef(ret)
      val effectsList = typeListTerm(effects.map(typeExprToRef))
      // Named args in canonical (alphabetical) order: effects, param, result.
      terms.alloc(Term.Fn(intern("anthill.prelude.TypeExtractor.Arrow"), IArray.empty,
        IArray((intern("effects"), effectsList), (intern("param"), paramTerm),
               (intern("result"), resultTerm))))
    case TypeExpr.TupleType(fields) =>
      namedTupleTypeTerm(fields)
    // WI-302: a denoted value-in-type rides as the raw literal term (rustland
    // retired the `make_denoted` wrapper in WI-366 — the value rides as a Node).
    case TypeExpr.Denoted(value) => value
    // WI-375: a written effect-row lowers to an opaque `effects_rows(e1, …)`
    // term (rustland builds an EffectExpression; scaland has no effect
    // machinery, so the row rides as a plain functor term — this also subsumes
    // the retired `setType`'s `SetLiteral` lowering for binding-value `{}`).
    case TypeExpr.EffectRow(effects) =>
      terms.alloc(Term.Fn(intern("effects_rows"),
        IArray.from(effects.map(typeExprToRef)), IArray.empty))
    // WI-478: a guarded effect `E :- guard` lowers to an opaque
    // `guarded(label, guardList)` term — rustland builds an
    // `EffectExpression.guarded(label, guard: List[reflect.Term])`; scaland has
    // no effect machinery, so the element rides as a plain functor with the
    // guard goals as a prelude cons-list (carrier-faithful round-trip only).
    case TypeExpr.EffectGuarded(label, guard) =>
      terms.alloc(Term.Fn(intern("guarded"),
        IArray(typeExprToRef(label), typeListTerm(guard)), IArray.empty))

  /** Build `anthill.prelude.TypeExtractor.NamedTuple(fields: List[NamedTupleElement])`
    * from `(name, type)` field pairs. Shared by tuple types and multi-parameter
    * arrow parameter lists. Mirrors rustland's `make_named_tuple_type`. */
  private def namedTupleTypeTerm(fields: IndexedSeq[(TermSymbol, TypeExpr)]): TermId =
    val fieldTerms = fields.map { (nameSym, ty) =>
      val nameRef = terms.alloc(Term.Ref(nameSym))
      val typeTerm = typeExprToRef(ty)
      terms.alloc(Term.Fn(intern("anthill.prelude.NamedTupleElement"), IArray.empty,
        IArray((intern("name"), nameRef), (intern("type"), typeTerm))))
    }
    terms.alloc(Term.Fn(intern("anthill.prelude.TypeExtractor.NamedTuple"), IArray.empty,
      IArray((intern("fields"), typeListTerm(fieldTerms)))))

  /** Build a prelude cons-list term (`anthill.prelude.List.cons`/`nil`) from
    * element TermIds, in order. */
  private def typeListTerm(elems: IndexedSeq[TermId]): TermId =
    val nilTerm = terms.alloc(Term.Fn(intern("anthill.prelude.List.nil"), IArray.empty, IArray.empty))
    elems.foldRight(nilTerm)((h, t) =>
      terms.alloc(Term.Fn(intern("anthill.prelude.List.cons"), IArray(h, t), IArray.empty)))

  private def refTerm[$: P]: P[TermId] =
    P(keyword("Ref") ~ "(" ~/ name ~ ")").map(n => terms.alloc(Term.Ref(n.last)))

  private def prefixTerm[$: P]: P[TermId] =
    P(prefixOp ~ atomWithFieldAccess).map { case (op, operand) =>
      val opString = symbols.name(op)
      val entry = Pratt.lookupPrefix(opString)
      val functorSym = entry.map(e => intern(e.functor)).getOrElse(op)
      terms.alloc(Term.Fn(functorSym, IArray(operand), IArray.empty))
    }

  private def prefixOp[$: P]: P[TermSymbol] =
    P(
      "!".!.map(_ => intern("!")) |
      keyword("not").map(_ => intern("not")) |
      "-".!.map(_ => intern("-"))
    )

  private def collectionLiteral[$: P]: P[TermId] =
    // Head-tail `[h | t]` removed (WI-560): it was an unused, parse-only
    // surface; list destructuring uses the explicit `cons(?h, ?t)` constructor.
    P("[" ~/ (
      "]".map(_ => terms.alloc(Term.Fn(intern("ListLiteral"), IArray.empty, IArray.empty))) |
      (term.rep(1, sep = ",") ~ "]").map { elems =>
        terms.alloc(Term.Fn(intern("ListLiteral"), IArray.from(elems), IArray.empty))
      }
    ))

  private def setLiteral[$: P]: P[TermId] =
    P("{" ~ term.rep(sep = ",") ~ "}").map { elems =>
      terms.alloc(Term.Fn(intern("SetLiteral"), IArray.from(elems), IArray.empty))
    }

  /** Parse `(...)` as one of:
    *   - empty tuple `()`,
    *   - nested-implication `(t1, … -: u1, …)` (induction-style body —
    *     used by stdlib int.anthill, encoded as
    *     `forall_impl(tuple(antecedents), tuple(consequents))`),
    *   - single-arg paren expr `(x)` (returned as-is),
    *   - tuple literal `(x, y, …)` with positional or named args.
    *
    * One dispatcher avoids the backtracking trap: alternatives that
    * pre-consumed input then failed under `~/` couldn't reach the
    * fallback (this bit `not(not(?a))` and would also bite the nested-
    * impl form if it lived in a separate alternative).
    */
  private def tupleLiteralOrParenExpr[$: P]: P[TermId] =
    P("(" ~/ (
      ")".map(_ => terms.alloc(Term.Fn(intern("TupleLiteral"), IArray.empty, IArray.empty))) |
      (fnArg ~ ("," ~/ fnArg).rep ~ ",".? ~ ("-:" ~/ term.rep(1, sep = ",")).? ~ ")").map {
        case (first, rest, Some(consequents)) =>
          val antecedents = (first +: rest).collect { case Left(t) => t }
          val antTuple = terms.alloc(Term.Fn(intern("tuple"),
            IArray.from(antecedents), IArray.empty))
          val conTuple = terms.alloc(Term.Fn(intern("tuple"),
            IArray.from(consequents), IArray.empty))
          terms.alloc(Term.Fn(intern("forall_impl"),
            IArray(antTuple, conTuple), IArray.empty))
        case (first, rest, None) =>
          if rest.isEmpty then first match
            case Left(tid) => tid
            case Right((k, v)) =>
              terms.alloc(Term.Fn(intern("TupleLiteral"), IArray.empty, IArray((k, v))))
          else
            val all = first +: rest
            val posArgs = ArrayBuffer.empty[TermId]
            val namedArgs = ArrayBuffer.empty[(TermSymbol, TermId)]
            all.foreach {
              case Left(tid) => posArgs += tid
              case Right((k, v)) => namedArgs += ((k, v))
            }
            terms.alloc(Term.Fn(intern("TupleLiteral"),
              IArray.from(posArgs), IArray.from(namedArgs)))
      }
    ))

  private def infixOp[$: P]: P[TermSymbol] =
    P(
      "!=".!.map(_ => intern("!=")) |
      keyword("or").map(_ => intern("or")) |
      keyword("and").map(_ => intern("and")) |
      keyword("mod").map(_ => intern("mod")) |
      keyword("div").map(_ => intern("div")) |
      Tokens.opToken.map(intern)
    )

  /** `infixOp` for a `requires` / `ensures` clause term (see `clauseTerm`). A
    * bare `=` is the equality goal EXCEPT when it introduces the operation body —
    * i.e. when it is followed by an expr-body-only keyword (`match`/`if`/`let`/
    * `lambda`/`proof`), which cannot be a `_term` and so can only be the
    * `= <body>` separator. This mirrors rustland's GLR (the infix `Eq[T] = match`
    * parse is impossible, so `= match` is the body; `result = x` stays an eq
    * goal). Every other operator (`<=`, `>=`, `==`, `!=`, `<=>`, …) is a distinct
    * maximal-munch token and always an infix op. Derived from `infixOp` so the
    * two operator sets can't drift. */
  private def clauseInfixOp[$: P]: P[TermSymbol] =
    P(
      (Tokens.opToken.filter(_ == "=") ~ !exprBodyKeyword).map(_ => intern("=")) |
      infixOp.filter(sym => symbols.name(sym) != "=")
    )

  /** The keywords that introduce an expr-body-only form (`_expr_body` minus the
    * `_term` fall-through). A lookahead over these distinguishes a clause `= goal`
    * from the operation-body `= <body>` separator. */
  private def exprBodyKeyword[$: P]: P[Unit] =
    P(keyword("match") | keyword("if") | keyword("let") | keyword("lambda") | keyword("proof"))

  // ── Expression bodies ────────────────────────────────────────

  private def exprBody[$: P]: P[TermId] =
    P(matchExpr | ifExpr | letExpr | lambdaExpr | proofStatement | term)

  /** WI-538: an in-body / control-flow proof — `proof TARGET [using …] [by …]
    * [conclude term] end BODY`. The existing proof clauses in statement
    * position, followed by a continuation `exprBody` (the `let x = v <body>`
    * sequencing precedent). scaland has no proof discharge, so the `using` / `by`
    * clauses are parsed-and-dropped and the form lowers to an inert
    * `proof_stmt(body, target: "<qn>" [, conclude])` term that carries the
    * continuation; mirrors rustland's `proof_statement` shape (which rides the
    * proof metadata as a `ParseAux::ProofStmt`). */
  private def proofStatement[$: P]: P[TermId] =
    P(keyword("proof") ~/ name ~ (keyword("using") ~/ proofUsingList).? ~
      (keyword("by") ~/ proofStrategy).? ~ (keyword("conclude") ~/ term).? ~
      keyword("end") ~ exprBody).map {
      case (target, _using, _strategy, conclude, body) =>
        val targetStr = terms.alloc(Term.Const(
          Literal.StringLit(target.segments.map(symbols.name).mkString("."))))
        val named = ArrayBuffer((intern("target"), targetStr))
        conclude.foreach(c => named += ((intern("conclude"), c)))
        terms.alloc(Term.Fn(intern("proof_stmt"), IArray(body), IArray.from(named)))
    }

  private def matchExpr[$: P]: P[TermId] =
    // Mirrors rustland's tree-sitter grammar: `match scrut repeat1(branch)`,
    // no `end`. `matchBranch.rep(1)` self-terminates at the first non-`case`.
    P(keyword("match") ~/ term ~ matchBranch.rep(1)).map { case (scrutinee, branches) =>
      terms.alloc(Term.Fn(intern("match_expr"), IArray(scrutinee) ++ IArray.from(branches), IArray.empty))
    }

  private def matchBranch[$: P]: P[TermId] =
    P(keyword("case") ~/ pattern ~ "->" ~ exprBody).map { case (pat, body) =>
      terms.alloc(Term.Fn(intern("match_branch"), IArray(pat, body), IArray.empty))
    }

  private def ifExpr[$: P]: P[TermId] =
    P(keyword("if") ~/ term ~ keyword("then") ~ exprBody ~ keyword("else") ~ exprBody).map {
      case (cond, thenB, elseB) =>
        terms.alloc(Term.Fn(intern("if_expr"), IArray(cond, thenB, elseB), IArray.empty))
    }

  /** `let pat [: T] = value [in] body`. The `in` keyword is OPTIONAL:
    * rustland's canonical form is block-style (`let x = value \n body`, no
    * `in` — see grammar `let_chain`); the `in` form is also accepted for
    * back-compat. The optional `: T` annotation (proposal 035 form (1),
    * WI-185) supplies an expected-type hint for the value position. Mirrors
    * rustland: encoded as a `type_name` named-arg child holding the type
    * lowered to a term; positional args stay `(pattern, value, body)`. */
  private def letExpr[$: P]: P[TermId] =
    P(keyword("let") ~/ pattern ~ (":" ~ typeExpr).? ~ "=" ~ exprBody ~ keyword("in").? ~ exprBody).map {
      case (pat, tyAnno, value, body) =>
        val named = tyAnno match
          case Some(ty) => IArray((intern("type_name"), typeExprToRef(ty)))
          case None     => IArray.empty[(TermSymbol, TermId)]
        terms.alloc(Term.Fn(intern("let_expr"), IArray(pat, value, body), named))
    }

  private def lambdaExpr[$: P]: P[TermId] =
    P(keyword("lambda") ~/ pattern ~ "->" ~ exprBody).map { case (param, body) =>
      terms.alloc(Term.Fn(intern("lambda_expr"), IArray(param, body), IArray.empty))
    }

  // ── Patterns ─────────────────────────────────────────────────

  private def pattern[$: P]: P[TermId] =
    P(patternConstructor | patternTyped | patternTuple | patternLiteral | patternWildcard | patternVar)

  /** WI-517: a type-annotated binder `name: Type`. Lowers to the SAME
    * `pattern_var` functor as a bare binder but carries the declared type as a
    * `type` named arg (rustland rides it as a `ParseAux::TypeExpr`; scaland
    * lowers the type to a term via `typeExprToRef`). Cut-free so a non-typed
    * tuple element backtracks cleanly. */
  private def typedBinder[$: P]: P[TermId] =
    P(ident ~ ":" ~ typeExpr).map { case (nameSym, ty) =>
      val idTerm = terms.alloc(Term.Ident(nameSym))
      terms.alloc(Term.Fn(intern("pattern_var"), IArray(idTerm),
        IArray((intern("type"), typeExprToRef(ty)))))
    }

  /** WI-517: a parenthesized single typed binder `(x: T)` (e.g.
    * `lambda (x: Int64) -> x`). NOT a 1-tuple — it lowers to the inner typed
    * `pattern_var`. */
  private def patternTyped[$: P]: P[TermId] =
    P("(" ~ typedBinder ~ ")")

  /** A tuple-pattern element: a typed binder (`a: A`) or a plain pattern (WI-517,
    * `lambda (acc: A, elem: B) -> …`). */
  private def patternTupleElem[$: P]: P[TermId] =
    P(typedBinder | pattern)

  private def patternWildcard[$: P]: P[TermId] =
    P("_").map(_ => terms.alloc(Term.Fn(intern("pattern_wildcard"), IArray.empty, IArray.empty)))

  private def patternVar[$: P]: P[TermId] =
    P(ident).map { sym =>
      val idTerm = terms.alloc(Term.Ident(sym))
      terms.alloc(Term.Fn(intern("pattern_var"), IArray(idTerm), IArray.empty))
    }

  private def patternLiteral[$: P]: P[TermId] =
    P(literal).map { tid =>
      terms.alloc(Term.Fn(intern("pattern_literal"), IArray(tid), IArray.empty))
    }

  private def patternConstructor[$: P]: P[TermId] =
    P(name ~ "(" ~ pattern.rep(sep = ",") ~ ")").map { case (n, pats) =>
      val nameTerm = terms.alloc(Term.Ident(n.last))
      terms.alloc(Term.Fn(intern("pattern_constructor"), IArray(nameTerm) ++ IArray.from(pats), IArray.empty))
    }

  private def patternTuple[$: P]: P[TermId] =
    P(
      ("(" ~ ")").map(_ => terms.alloc(Term.Fn(intern("pattern_tuple"), IArray.empty, IArray.empty))) |
      ("(" ~ patternTupleElem ~ "," ~ patternTupleElem.rep(1, sep = ",") ~ ")").map { case (first, rest) =>
        terms.alloc(Term.Fn(intern("pattern_tuple"), IArray.from(first +: rest), IArray.empty))
      }
    )

  // ── Field declarations & params ──────────────────────────────

  private def fieldDecl[$: P]: P[FieldDecl] =
    P(ident ~ ":" ~ typeExpr).map { case (n, t) => FieldDecl(n, t) }

  private def param[$: P]: P[Param] =
    P(ident ~ ":" ~ typeExpr).map { case (n, t) => Param(n, t) }

  // ── Visibility ───────────────────────────────────────────────

  private def visibility[$: P]: P[Visibility] =
    P(
      keyword("internal").map(_ => Visibility.Internal) |
      keyword("public").map(_ => Visibility.Public)
    )

  // ── Import ───────────────────────────────────────────────────

  private def importClause[$: P]: P[Import] =
    P(keyword("import") ~/ importPath)

  private def importPath[$: P]: P[Import] =
    P(Index ~ ident ~ ("." ~ importSegment).rep ~ Index).map { case (s, first, rest, e) =>
      val allSegments = ArrayBuffer(first)
      var kind: ImportKind = ImportKind.Plain
      for seg <- rest do
        seg match
          case Left(sym) => allSegments += sym
          case Right(ik) => kind = ik
      Import(Name(allSegments.toIndexedSeq, mkSpan(s, e)), kind)
    }

  private def importSegment[$: P]: P[Either[TermSymbol, ImportKind]] =
    P(
      selectiveImport.map(Right(_)) |
      wildcardImport.map(Right(_)) |
      ident.map(Left(_))
    )

  private def selectiveImport[$: P]: P[ImportKind] =
    P("{" ~/ simpleName.rep(1, sep = ",") ~ "}").map(ns => ImportKind.Selective(ns.toIndexedSeq))

  private def wildcardImport[$: P]: P[ImportKind] =
    P("*").map(_ => ImportKind.Wildcard)

  // ── Meta block ───────────────────────────────────────────────

  private def metaBlock[$: P]: P[MetaBlock] =
    P("[" ~/ metaEntry.rep(1, sep = ",") ~ "]").map(es => MetaBlock(es.toIndexedSeq))

  /** Open-keyed entry: `key: value` for ordinary metadata, or bare `key`
    * for the WI-140 flag form (`[simp]` ≡ `[simp: true]`). The bare form
    * stores `Term.Bottom` as a sentinel — flag-presence checks (landing
    * with WI-157) inspect only the key, so the two forms are equivalent. */
  private def metaEntry[$: P]: P[MetaEntry] =
    P(name ~ (":" ~/ term).?).map {
      case (k, Some(v)) => MetaEntry(k, v)
      case (k, None) => MetaEntry(k, terms.alloc(Term.Bottom))
    }

  // ── Body content (shared by namespace and sort) ──────────────

  private type BodyContent = Either[Import, Item]

  private def bodyContent[$: P]: P[BodyContent] =
    P(
      importClause.map(Left(_)) |
      declaration.map(Right(_))
    )

  private def processContent(
    content: Seq[BodyContent]
  ): (IndexedSeq[Import], IndexedSeq[Item]) =
    val imports = ArrayBuffer.empty[Import]
    val items = ArrayBuffer.empty[Item]
    content.foreach {
      case Left(imp) => imports += imp
      case Right(item) => items += item
    }
    (imports.toIndexedSeq, items.toIndexedSeq)

  private def bracedBody[$: P]: P[(IndexedSeq[Import], IndexedSeq[Item])] =
    P("{" ~/ bodyContent.rep ~ "}").map(cs => processContent(cs))

  private def endBody[$: P]: P[(IndexedSeq[Import], IndexedSeq[Item])] =
    P(bodyContent.rep ~ keyword("end")).map(cs => processContent(cs))

  private def body[$: P]: P[(IndexedSeq[Import], IndexedSeq[Item])] =
    P(bracedBody | endBody)

  // ── Declarations ─────────────────────────────────────────────

  private def namespaceDecl[$: P]: P[Item] =
    P(keyword("namespace") ~/ name ~ body).map { case (n, (imports, items)) =>
      Item.NamespaceItem(Namespace(n, imports, items, mkSpan(0, 0)))
    }

  /** `sort …` — three shapes, disambiguated by the token after `sort`:
    *   - a plain `name` → `abstract_sort` (`= type`) or `sort_with_body`;
    *   - a `?X` marker → `sort_var_binder` (WI-454);
    *   - a leading `[` → `sort_bracket_binder` (WI-454).
    * The binder forms (`sort ?X` / `sort [X]`, optionally `{ sort ?T … }`) are
    * per-statement synonyms of a WI-451 enclosing type-param; they desugar to
    * the SAME IR (`desugarSortTypeParam`). The branches return a
    * `vis => Item` so the `visibility.?` parsed before `sort` is applied once;
    * the binder forms drop both the visibility and any trailing meta block —
    * a type-param binder carries neither (the desugar has no slot for them), so
    * `public sort ?X [simp]` parses but silently ignores `public`/`[simp]`. */
  private def sortDecl[$: P]: P[Item] =
    P(visibility.? ~ keyword("sort") ~/ (sortVarBinderDecl | sortBracketBinderDecl | sortNamedDecl)).map {
      case (vis, mk) => mk(vis)
    }

  private def sortNamedDecl[$: P]: P[Option[Visibility] => Item] =
    P(name ~ (abstractSortRest | sortWithBodyRest)).map {
      case (n, Left((defn, meta))) =>
        (vis: Option[Visibility]) =>
          Item.AbstractSortItem(AbstractSort(vis, n, defn, IndexedSeq.empty, meta, mkSpan(0, 0)))
      case (n, Right((imports, items, meta))) =>
        (vis: Option[Visibility]) =>
          Item.SortWithBodyItem(SortWithBody(vis, n, IndexedSeq.empty, imports, items, meta, mkSpan(0, 0), SortDeclKind.Sort))
    }

  /** WI-454: `sort ?X [ { sort ?T … } ]` — `?X` reuses the logical-var marker as
    * the binder name. Desugars to the SAME IR the enclosing-list form produces. */
  private def sortVarBinderDecl[$: P]: P[Option[Visibility] => Item] =
    P(Tokens.variableToken ~ sortBinderBody.? ~ metaBlock.?).map {
      case (nm, members, _) =>
        val item = desugarSortTypeParam(SortTypeParam(intern(nm), members))
        (_: Option[Visibility]) => item
    }

  /** WI-454: `sort [X] [ { sort [T] … } ]` — the standalone bracket binder. */
  private def sortBracketBinderDecl[$: P]: P[Option[Visibility] => Item] =
    P("[" ~/ ident ~ "]" ~ sortBinderBody.? ~ metaBlock.?).map {
      case (nameSym, members, _) =>
        val item = desugarSortTypeParam(SortTypeParam(nameSym, members))
        (_: Option[Visibility]) => item
    }

  /** A structured binder's brace body — members are themselves type-variable
    * binders ONLY (`sort ?T` / `sort [T]`, possibly nested HK), `repeat1` so an
    * empty `sort [F] {}` is a loud error rather than a degenerate carrier. */
  private def sortBinderBody[$: P]: P[IndexedSeq[SortTypeParam]] =
    P("{" ~/ sortBinderMember.rep(1) ~ "}").map(_.toIndexedSeq)

  private def sortBinderMember[$: P]: P[SortTypeParam] =
    P(keyword("sort") ~/ (
      (Tokens.variableToken ~ sortBinderBody.?).map { case (nm, ms) => SortTypeParam(intern(nm), ms) } |
      ("[" ~/ ident ~ "]" ~ sortBinderBody.?).map { case (nm, ms) => SortTypeParam(nm, ms) }
    ))

  /** `effects E = ?` (or `= X`) at sort-item position (WI-320 / proposal
    * 045). Rustland (`effects_sort_item`) desugars this to the pair
    * `sort E = ? + requires EffectsRuntime[Effects = E]`. scaland keeps the
    * `sort E = ?` half as an `AbstractSort` and OMITS the
    * `requires EffectsRuntime` anchor: that anchor exists solely to give the
    * row variable a kind reachable at typing time, and scaland has no typer,
    * so it would be inert load. The mandatory `=` disambiguates from the
    * operation-clause `effects E` (which never appears at body level). */
  private def effectsSortItem[$: P]: P[Item] =
    P(visibility.? ~ keyword("effects") ~ name ~ "=" ~/ typeExpr ~ metaBlock.?).map {
      case (vis, n, defn, meta) =>
        Item.AbstractSortItem(AbstractSort(vis, n, defn, IndexedSeq.empty, meta, mkSpan(0, 0)))
    }

  /** `enum NAME ... end` — same body shape as `sort NAME ... end` but the
    * declaration kind is recorded as `Enum` (proposal 025). */
  private def enumDecl[$: P]: P[Item] =
    P(visibility.? ~ keyword("enum") ~/ name ~ body ~ metaBlock.?).map {
      case (vis, n, (imports, items), meta) =>
        Item.SortWithBodyItem(SortWithBody(vis, n, IndexedSeq.empty, imports, items, meta, mkSpan(0, 0), SortDeclKind.Enum))
    }

  private def abstractSortRest[$: P]: P[Left[(TypeExpr, Option[MetaBlock]), Nothing]] =
    P("=" ~/ typeExpr ~ metaBlock.?).map { case (te, mb) => Left((te, mb)) }

  private def sortWithBodyRest[$: P]: P[Right[Nothing, (IndexedSeq[Import], IndexedSeq[Item], Option[MetaBlock])]] =
    P(sortTypeParamList.? ~ body ~ metaBlock.?).map { case (paramsOpt, (imports, items), meta) =>
      // WI-451 (§5.4): an enclosing type-param list desugars into body items
      // PREPENDED so the params precede the members that reference them. The list
      // lives only in this body branch (not `abstractSortRest`), so `sort X[A] = T`
      // — a param list with no body — is a loud parse error, mirroring rustland
      // (`sort_type_param_list` belongs to `sort_with_body`, not `abstract_sort`).
      val paramItems = paramsOpt.getOrElse(IndexedSeq.empty).map(desugarSortTypeParam)
      Right((imports, paramItems ++ items, meta))
    }

  // WI-451 (§5.4): an enclosing operation-style type-param list after a sort name
  // — `sort CpsMonad[F[T], A, B]`. Each param is a NON-RIGID type variable; a
  // higher-kinded param carries its own bracketed member list (`F[T]`, the one
  // shape the flat parameterized-type binding cannot express). Mirrors rustland's
  // `sort_type_param_list` / `desugar_sort_type_param`.
  private case class SortTypeParam(name: TermSymbol, members: Option[IndexedSeq[SortTypeParam]])

  private def sortTypeParamList[$: P]: P[IndexedSeq[SortTypeParam]] =
    P("[" ~ sortTypeParam.rep(1, sep = ",") ~ "]").map(_.toIndexedSeq)

  private def sortTypeParam[$: P]: P[SortTypeParam] =
    P(ident ~ sortTypeParamList.?).map { case (n, members) => SortTypeParam(n, members) }

  /** Desugar one enclosing type-param binder to the SAME IR rustland's
    * `desugar_sort_type_param` produces, so the surface form and the body form
    * cannot drift: a SIMPLE param `A` → `sort A = ?` (an `AbstractSort` with a
    * fresh anonymous `?` — picked up by the loader's `sort T = ?` type-param arm);
    * a HIGHER-KINDED param `F[T]` → a `SortWithBody` MARKED `isTypeParam` whose
    * body holds the recursively-desugared members (the loader mints F as a type
    * param of the enclosing sort). No `= default` form (sort-param defaults are
    * undefined by §5.4). */
  private def desugarSortTypeParam(p: SortTypeParam): Item =
    val nm = Name.simple(p.name, mkSpan(0, 0))
    p.members match
      case Some(members) =>
        Item.SortWithBodyItem(SortWithBody(
          None, nm, IndexedSeq.empty, IndexedSeq.empty,
          members.map(desugarSortTypeParam), None, mkSpan(0, 0),
          SortDeclKind.Sort, isTypeParam = true))
      case None =>
        Item.AbstractSortItem(AbstractSort(None, nm, freshAnonTypeVar(), IndexedSeq.empty, None, mkSpan(0, 0)))

  private def ruleDecl[$: P]: P[Item] =
    P(keyword("rule") ~/ (
      bracedRuleBlock |
      singleRule
    ))

  private def bracedRuleBlock[$: P]: P[Item] =
    P("{" ~/ ruleEntry.rep ~ "}").map { entries =>
      Item.RuleBlockItem(RuleBlock(entries.toIndexedSeq, mkSpan(0, 0)))
    }

  private def singleRule[$: P]: P[Item] =
    P((simpleName ~ ":").? ~ ruleArrowChoice ~ metaBlock.?).map {
      case (label, (heads, body), meta) =>
        resetVarScope()
        Item.RuleItem(Rule(label, heads, body, meta, mkSpan(0, 0)))
    }

  private def ruleEntry[$: P]: P[Rule] =
    P((simpleName ~ ":").? ~ ruleArrowChoice ~ metaBlock.?).map {
      case (label, (heads, body), meta) =>
        resetVarScope()
        Rule(label, heads, body, meta, mkSpan(0, 0))
    }

  /** Proposal 032: choice over (heads :- body | body -: heads | heads).
    * `:-` and `-:` are mirror surface forms of the same implication arrow;
    * exactly one (or neither, for a bare-head fact) appears per rule.
    *
    * We parse heads first then look for `:-` body or `-:` heads, rather than
    * the literal alternation `(heads :- body | body -: heads | heads)`, because
    * the literal form can't backtrack out of a Pratt-parsed equational head
    * like `?a * (?b + ?c) = ?a * ?b + ?a * ?c`. The reversed `-:` form is rare,
    * so probing for it only after the heads parse cleanly stays cheap. */
  private def ruleArrowChoice[$: P]: P[(IndexedSeq[RuleHead], Option[IndexedSeq[TermId]])] =
    P(
      (ruleHeads ~ (":-" ~/ goalTerm.rep(1, sep = ",")).?).flatMap { case (hs, body) =>
        body match
          case Some(_) =>
            Pass.map(_ => (hs, body.map(_.toIndexedSeq)))
          case None =>
            ("-:" ~/ ruleHeads).?.map {
              case Some(reversedHeads) =>
                // What we parsed as `heads` was actually the body of `body -: heads`.
                val bodyTerms = hs.collect { case RuleHead.TermHead(t) => t }
                (reversedHeads, Some(bodyTerms))
              case None =>
                (hs, None)
            }
      }
    )

  private def ruleHeads[$: P]: P[IndexedSeq[RuleHead]] =
    P(
      "\u22A5".!.map(_ => IndexedSeq[RuleHead](RuleHead.Bottom)) |
      term.rep(1, sep = ",").map(_.map(RuleHead.TermHead(_)).toIndexedSeq)
    )

  private def operationDecl[$: P]: P[Item] =
    P(keyword("operation") ~/ (
      bracedOperationBlock |
      singleOperation
    ))

  private def bracedOperationBlock[$: P]: P[Item] =
    P("{" ~/ operationEntry.rep ~ "}").map { entries =>
      Item.OperationBlockItem(OperationBlock(entries.toIndexedSeq, mkSpan(0, 0)))
    }

  private def singleOperation[$: P]: P[Item] =
    P(visibility.? ~ simpleName ~ operationTypeParamList.? ~ "(" ~ param.rep(sep = ",") ~ ")" ~ "->" ~ typeExpr ~
      operationClauses ~ ("=" ~/ exprBody).? ~ metaBlock.?
    ).map { case (vis, n, tps, params, retType, (reqs, enss, effs, clauseMeta), opBody, trailingMeta) =>
      Item.OperationItem(Operation(vis, n, tps.getOrElse(IndexedSeq.empty), params.toIndexedSeq, retType,
        reqs, enss, effs, opBody, combineMeta(clauseMeta, trailingMeta), mkSpan(0, 0)))
    }

  private def operationEntry[$: P]: P[Operation] =
    P(visibility.? ~ simpleName ~ operationTypeParamList.? ~ "(" ~ param.rep(sep = ",") ~ ")" ~ "->" ~ typeExpr ~
      operationClauses ~ ("=" ~/ exprBody).? ~ metaBlock.?
    ).map { case (vis, n, tps, params, retType, (reqs, enss, effs, clauseMeta), opBody, trailingMeta) =>
      Operation(vis, n, tps.getOrElse(IndexedSeq.empty), params.toIndexedSeq, retType,
        reqs, enss, effs, opBody, combineMeta(clauseMeta, trailingMeta), mkSpan(0, 0))
    }

  /** Operation type-parameter list `[T, U = Int]` (WI-269). A distinct
    * production from `sortBinding`/instantiation even though the tokens
    * coincide: this declares operation-local logical variables, not
    * bindings of sort parameters at an instantiation site. Mirrors
    * rustland's `operation_type_param_list`. */
  private def operationTypeParamList[$: P]: P[IndexedSeq[TypeParam]] =
    P("[" ~ operationTypeParam.rep(1, sep = ",") ~ "]").map(_.toIndexedSeq)

  private def operationTypeParam[$: P]: P[TypeParam] =
    P(ident ~ ("=" ~/ typeExpr).?).map { case (n, default) =>
      TypeParam(n, default, mkSpan(0, 0))
    }

  private def operationClauses[$: P]: P[(IndexedSeq[IndexedSeq[TermId]], IndexedSeq[IndexedSeq[TermId]], IndexedSeq[Effect], IndexedSeq[MetaEntry])] =
    P(operationClause.rep).map { clauses =>
      val reqs = ArrayBuffer.empty[IndexedSeq[TermId]]
      val enss = ArrayBuffer.empty[IndexedSeq[TermId]]
      val effs = ArrayBuffer.empty[Effect]
      val metas = ArrayBuffer.empty[MetaEntry]
      clauses.foreach {
        case (0, terms: IndexedSeq[TermId] @unchecked) => reqs += terms
        case (1, terms: IndexedSeq[TermId] @unchecked) => enss += terms
        case (2, effects: IndexedSeq[Effect] @unchecked) => effs ++= effects
        // WI-087: `meta [...]` clause entries accumulate (matching effects/
        // requires/ensures — no silent last-wins drop), merged with a trailing
        // bare meta_block by `combineMeta`.
        case (3, entries: IndexedSeq[MetaEntry] @unchecked) => metas ++= entries
        case _ =>
      }
      (reqs.toIndexedSeq, enss.toIndexedSeq, effs.toIndexedSeq, metas.toIndexedSeq)
    }

  /** WI-087: merge `meta [...]` operation-clause entries with a trailing
    * `[...]` meta block (clause entries first, then trailing). `None` when
    * both are empty, so clauseless ops keep `meta = None`. */
  private def combineMeta(clauseEntries: IndexedSeq[MetaEntry], trailing: Option[MetaBlock]): Option[MetaBlock] =
    val all = clauseEntries ++ trailing.map(_.entries).getOrElse(IndexedSeq.empty)
    if all.isEmpty then None else Some(MetaBlock(all))

  private def operationClause[$: P]: P[(Int, IndexedSeq[?])] =
    P(
      // `clauseTerm` (not `term`): a trailing `= <expr-body>` after the clause
      // is the operation-body separator, not an equality goal (WI-562:
      // `requires Eq[T] = match l …`). See `clauseTerm`.
      (keyword("requires") ~/ clauseTerm.rep(1, sep = ",")).map(ts => (0, ts.toIndexedSeq)) |
      (keyword("ensures") ~/ clauseTerm.rep(1, sep = ",")).map(ts => (1, ts.toIndexedSeq)) |
      // Mirrors rustland's `_effect_set` shared between operation
      // `effects` and arrow-type `@`: bare single type or braced list
      // (possibly with trailing comma).
      (keyword("effects") ~/ effectSet).map(ts => (2, ts.map(Effect(_)).toIndexedSeq)) |
      // WI-087: operation attributes — a keyword-introduced `meta [...]`
      // clause carrying the existing meta_block. The `meta` keyword
      // disambiguates from return-type application args (`-> Vec3[...]`).
      // (Unblocks the C++ mapping codegen, which reads operation meta.)
      (keyword("meta") ~/ metaBlock).map(mb => (3, mb.entries))
    )

  /** `const NAME : T [= value]` (proposal 039 / WI-084). Monomorphic +
    * carrier-independent — no params / type-params / clauses. The declared
    * type is MANDATORY; the body OPTIONAL (absent for host-supplied constants
    * such as float `infinity` / `nan`). Mirrors rustland's `convert_const`
    * (modeled on the operation's description / visibility / optional-body
    * shape). scaland defines only the symbol (load.rs `Item::Const` arm); the
    * value body is not lowered (scaland has no typer/eval to consume it). */
  private def constDecl[$: P]: P[Item] =
    P(visibility.? ~ keyword("const") ~/ name ~ ":" ~ typeExpr ~ ("=" ~/ exprBody).? ~ metaBlock.?).map {
      case (vis, n, ty, value, meta) =>
        Item.ConstItem(Const(vis, n, ty, value, meta, mkSpan(0, 0)))
    }

  private def requiresDeclItem[$: P]: P[Item] =
    P(keyword("requires") ~/ typeExpr).map { te =>
      Item.RequiresDeclItem(RequiresDecl(te, mkSpan(0, 0)))
    }

  private def entityDecl[$: P]: P[Item] =
    // `name` (not `simpleName`): rustland allows a qualified entity name
    // (`entity anthill.prelude.TypeBinding(...)`, stdlib sort.anthill).
    P(visibility.? ~ keyword("entity") ~/ name ~ ("(" ~ fieldDecl.rep(1, sep = ",") ~ ")").? ~ metaBlock.?
    ).map { case (vis, n, fields, meta) =>
      Item.EntityItem(Entity(vis, n, fields.map(_.toIndexedSeq).getOrElse(IndexedSeq.empty), meta, mkSpan(0, 0)))
    }

  private def factDeclInner[$: P]: P[Fact] =
    P(keyword("fact") ~/ term ~ metaBlock.?).map { case (t, meta) =>
      Fact(t, meta, mkSpan(0, 0))
    }

  private def factDecl[$: P]: P[Item] = factDeclInner.map(Item.FactItem(_))

  private def constraintDecl[$: P]: P[Item] =
    P(keyword("constraint") ~/ (simpleName ~ ":").? ~ term.rep(1, sep = ",") ~
      (":-" ~/ term.rep(1, sep = ",")).? ~ metaBlock.?
    ).map { case (label, head, guard, meta) =>
      resetVarScope()
      Item.ConstraintItem(Constraint(label, head.toIndexedSeq, guard.map(_.toIndexedSeq), meta, mkSpan(0, 0)))
    }

  // describe is not needed for test cases — omitted from declaration dispatch

  // ── Proof / Provides (proposal 025 + 031) ────────────────────

  // Hot interns for the synthetic `named_arg(name: "k", value: v)`
  // shape used by `proofStrategy` (mirrors rustland's `convert_named_arg`).
  private lazy val namedArgFunctorSym = intern("named_arg")
  private lazy val namedArgNameSym = intern("name")
  private lazy val namedArgValueSym = intern("value")

  /** Allocate a synthetic `named_arg(name: "k", value: v)` term so a
    * `key: value` shape survives parse-IR round-tripping alongside the
    * raw values (mirrors rustland's `convert_named_arg`). */
  private def allocNamedArg(k: TermSymbol, v: TermId): TermId =
    val keyStr = terms.alloc(Term.Const(Literal.StringLit(symbols.name(k))))
    terms.alloc(Term.Fn(namedArgFunctorSym, IArray.empty,
      IArray((namedArgNameSym, keyStr), (namedArgValueSym, v))))

  /** `proof TARGET ... end`. Two body shapes (proposal 031):
    *
    *   * Single-tactic — optional `using ...`, optional `by <strategy>`,
    *     optional inner body (`:- hints` or `query "..."`).
    *   * Structured — one or more `rule h_i: ... by t_i` step rules
    *     followed by an optional concluding `[using ...] by <tactic>`.
    *
    * Disambiguated by lookahead: a structured body must start with a
    * `rule` step (proof_step), so we try the structured form first and
    * fall back to the single-tactic form on rep(1) failure. */
  private def proofDeclInner[$: P]: P[ProofDecl] =
    // The grammar allows an optional trailing `end <name>`, dropped here:
    // `name.?` after `end` would greedily consume an outer scope's `end`
    // keyword (parsed as an ident). The trailing name is decorative.
    P(keyword("proof") ~/ name ~ proofBodyForm ~ keyword("end")).map {
      case (target, (using0, strategy, body)) =>
        resetVarScope()
        ProofDecl(target, strategy, body, using0, mkSpan(0, 0))
    }

  private def proofDecl[$: P]: P[Item] = proofDeclInner.map(Item.ProofItem(_))

  private def proofBodyForm[$: P]: P[(IndexedSeq[Name], Option[ProofStrategy], Option[ProofBody])] =
    P(structuredProofForm | singleTacticProofForm)

  private def structuredProofForm[$: P]: P[(IndexedSeq[Name], Option[ProofStrategy], Option[ProofBody])] =
    P(proofStepEntry.rep(1) ~ proofConcludingClause.?).map { case (steps, conclude) =>
      val structured = ProofBody.Structured(steps.toIndexedSeq, conclude)
      (IndexedSeq.empty, None, Some(structured))
    }

  private def singleTacticProofForm[$: P]: P[(IndexedSeq[Name], Option[ProofStrategy], Option[ProofBody])] =
    P((keyword("using") ~/ proofUsingList).? ~ (keyword("by") ~/ proofStrategy).? ~ proofBody.?).map {
      case (using0, strategy, body) =>
        (using0.getOrElse(IndexedSeq.empty), strategy, body)
    }

  private def proofUsingList[$: P]: P[IndexedSeq[Name]] =
    P(name.rep(1, sep = ",")).map(_.toIndexedSeq)

  private def proofStrategy[$: P]: P[ProofStrategy] =
    P(Index ~ ident ~ ("(" ~/ fnArg.rep(1, sep = ",") ~ ")").? ~ Index).map {
      case (s, n, args, e) =>
        val rawArgs: IndexedSeq[TermId] = args.getOrElse(Seq.empty).toIndexedSeq.map {
          case Left(tid) => tid
          case Right((k, v)) => allocNamedArg(k, v)
        }
        ProofStrategy(n, rawArgs, mkSpan(s, e))
    }

  private def stringText[$: P]: P[String] = P(Tokens.stringToken)

  private def proofBody[$: P]: P[ProofBody] =
    P(
      (":-" ~/ term.rep(1, sep = ",")).map(hs => ProofBody.Hints(hs.toIndexedSeq)) |
      (keyword("query") ~/ stringText ~ (keyword("mapping") ~/ mappingBlock).?).map {
        case (text, mapping) => ProofBody.Query(text, mapping)
      }
    )

  private def mappingBlock[$: P]: P[MappingBlock] =
    P("{" ~/ mappingEntry.rep(1, sep = ",") ~ ",".? ~ "}").map(es => MappingBlock(es.toIndexedSeq))

  private def mappingEntry[$: P]: P[MappingEntry] =
    P(name ~ "->" ~/ (stringText | name.map(n => n.segments.map(symbols.name).mkString(".")))).map {
      case (src, target) => MappingEntry(src, target)
    }

  private def proofStep[$: P]: P[ProofStep] =
    P((simpleName ~ ":").? ~ ruleArrowChoice ~ metaBlock.? ~ (keyword("using") ~/ proofUsingList).? ~ keyword("by") ~/ proofStrategy)
      .map { case (label, (heads, bodyTerms), meta, using0, strat) =>
        val rule = Rule(label, heads, bodyTerms, meta, mkSpan(0, 0))
        resetVarScope()
        ProofStep(rule, using0.getOrElse(IndexedSeq.empty), strat, mkSpan(0, 0))
      }

  /** `rule <step>` — strips the `rule` keyword before delegating to
    * `proofStep` so the structured-form parser composes cleanly with
    * `rep(1)`. */
  private def proofStepEntry[$: P]: P[ProofStep] =
    P(keyword("rule") ~/ proofStep)

  private def proofConcludingClause[$: P]: P[ConcludeClause] =
    P((keyword("using") ~/ proofUsingList).? ~ keyword("by") ~/ proofStrategy).map {
      case (using0, strat) =>
        ConcludeClause(using0.getOrElse(IndexedSeq.empty), strat, mkSpan(0, 0))
    }

  /** `provides Spec` (clause) or `provides Spec language X ... end` (block).
    * Disambiguated by checking for the `language` keyword after the spec. */
  private def providesDecl[$: P]: P[Item] =
    P(keyword("provides") ~/ typeExpr ~ providesRest).map {
      case (spec, Left(())) =>
        Item.ProvidesClauseItem(ProvidesClause(spec, mkSpan(0, 0)))
      case (spec, Right((lang, items))) =>
        Item.ProvidesBlockItem(ProvidesBlock(spec, lang, items, mkSpan(0, 0)))
    }

  private def providesRest[$: P]: P[Either[Unit, (TermSymbol, IndexedSeq[ProvidesItem])]] =
    P(
      (keyword("language") ~/ ident ~ providesContent.rep ~ keyword("end"))
        .map { case (lang, items) => Right((lang, items.toIndexedSeq)) } |
      Pass.map(_ => Left(()))
    )

  private def providesContent[$: P]: P[ProvidesItem] =
    P(
      providesArtifact |
      providesCarrier |
      providesNamespaceMap |
      providesProof |
      providesRule |
      providesFact
    )

  private def providesArtifact[$: P]: P[ProvidesItem] =
    P(keyword("artifact") ~/ stringText).map(p => ProvidesItem.ArtifactI(p))

  private def providesCarrier[$: P]: P[ProvidesItem] =
    P(keyword("carrier") ~/ providesBindings).map { bs =>
      ProvidesItem.CarrierI(bs.map { case (k, v) => CarrierBinding(k, v) })
    }

  private def providesNamespaceMap[$: P]: P[ProvidesItem] =
    P(keyword("namespace_map") ~/ providesBindings).map { bs =>
      ProvidesItem.NamespaceMapI(bs.map { case (k, v) => NamespaceMapEntry(k, v) })
    }

  private def providesBindings[$: P]: P[IndexedSeq[(TermSymbol, TermId)]] =
    P("{" ~/ providesBinding.rep(1, sep = ",") ~ ",".? ~ "}").map(_.toIndexedSeq)

  private def providesBinding[$: P]: P[(TermSymbol, TermId)] =
    P(ident ~ ":" ~/ term)

  private def providesProof[$: P]: P[ProvidesItem] =
    proofDeclInner.map(ProvidesItem.ProofI(_))

  /** Inside a `provides` block, `rule { ... }` desugars to a block-of-
    * rules and a bare `rule h :- b` to a single rule — `ruleDecl`
    * already returns the `Item.RuleItem` / `Item.RuleBlockItem` union,
    * so the partial match here mirrors that existing union. */
  private def providesRule[$: P]: P[ProvidesItem] =
    ruleDecl.map {
      case Item.RuleItem(r) => ProvidesItem.RuleI(r)
      case Item.RuleBlockItem(rb) => ProvidesItem.RuleBlockI(rb)
      case other => sys.error(s"ruleDecl returned unexpected $other")
    }

  private def providesFact[$: P]: P[ProvidesItem] =
    factDeclInner.map(ProvidesItem.FactI(_))

  // ── Declaration dispatch ─────────────────────────────────────

  private def declaration[$: P]: P[Item] =
    P(
      namespaceDecl |
      sortDecl |
      effectsSortItem |
      enumDecl |
      ruleDecl |
      operationDecl |
      constDecl |
      requiresDeclItem |
      entityDecl |
      factDecl |
      constraintDecl |
      proofDecl |
      providesDecl
    )

  // ── Top-level ────────────────────────────────────────────────

  def sourceFile[$: P]: P[Seq[Item]] =
    P(Start ~ declaration.rep ~ End)

end AnthillParserImpl

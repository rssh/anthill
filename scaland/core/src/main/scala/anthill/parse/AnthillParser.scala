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
    P(parameterizedType | tupleType | setType | variableType | simpleType)

  /** Type-positioned set literal: `{e1, e2, …}` (or empty `{}`). Used in
    * fact bindings like `fact Collection[Effect = {}]` (proposal 020 effect
    * sets). Stored as a `Variable` wrapping a SetLiteral term so it round-
    * trips through the existing `typeExprToRef` lowering. */
  private def setType[$: P]: P[TypeExpr] =
    P("{" ~ typeExpr.rep(sep = ",") ~ "}").map { elems =>
      val elemTerms = elems.map(typeExprToRef).toIndexedSeq
      val setTerm = terms.alloc(Term.Fn(intern("SetLiteral"), IArray.from(elemTerms), IArray.empty))
      TypeExpr.Variable(setTerm, IndexedSeq.empty)
    }

  private def simpleType[$: P]: P[TypeExpr] = P(name).map(TypeExpr.Simple(_))

  private def parameterizedType[$: P]: P[TypeExpr] =
    P(name ~ "[" ~ sortBinding.rep(1, sep = ",") ~ "]").map { case (n, bs) =>
      TypeExpr.Parameterized(n, bs.toIndexedSeq)
    }

  private def sortBinding[$: P]: P[SortBinding] =
    P(
      (name ~ "=" ~ typeExpr).map { case (n, t) => SortBinding(Some(n), t) } |
      typeExpr.map(t => SortBinding(None, t))
    )

  private def variableType[$: P]: P[TypeExpr] =
    P(Tokens.variableToken).map { varName =>
      val vid = if varName.isEmpty then freshAnonymousVar()
                else getOrCreateVar(intern(varName))
      TypeExpr.Variable(terms.alloc(Term.Var(vid)), IndexedSeq.empty)
    }

  private def arrowType[$: P]: P[TypeExpr] =
    P(arrowParams ~ "->" ~ typeExpr ~ ("@" ~ effectSet).?).map {
      case (params, ret, effs) => TypeExpr.Arrow(params, ret, effs.getOrElse(IndexedSeq.empty))
    }

  /** Effect set, shared by arrow `@` and operation `effects`. Mirrors
    * rustland's `_effect_set` (`commaSep1`):
    *   - single:  `E`            → `IndexedSeq(E)`
    *   - braced:  `{E1, E2, …}`  → `IndexedSeq(E1, E2, …)`
    *
    * The braced form requires at least one element and no trailing
    * comma, matching the rust grammar exactly. The cut after `{`
    * prevents the bare branch from rescuing `{}` via `setType`. */
  private def effectSet[$: P]: P[IndexedSeq[TypeExpr]] =
    P(
      ("{" ~/ effectType.rep(1, sep = ",") ~ "}").map(_.toIndexedSeq) |
      effectType.map(IndexedSeq(_))
    )

  /** Single effect type. Mirrors rustland's `_effect_type` (WI-092):
    * `simple_type | parameterized_type | variable_term` only. Tuple and
    * arrow types are deliberately rejected — neither is meaningful as an
    * effect, and accepting a leading `(` would let a typo like
    * `effects (Modify self)` consume the `(` as an arrow/tuple type and
    * cascade error recovery across the enclosing body. With `(` rejected
    * up front the parser fails at the bad token and resyncs at the next
    * clause keyword. */
  private def effectType[$: P]: P[TypeExpr] =
    P(parameterizedType | variableType | simpleType)

  private def arrowParams[$: P]: P[IndexedSeq[TypeExpr]] =
    P("(" ~ typeExpr.rep(sep = ",") ~ ")").map(_.toIndexedSeq)

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
      if pairs.isEmpty then first
      else
        val operands = ArrayBuffer(first)
        val opSymbols = ArrayBuffer.empty[TermSymbol]
        pairs.foreach { case (op, operand) => opSymbols += op; operands += operand }
        Pratt.desugar(operands.toIndexedSeq, opSymbols.toIndexedSeq, symbols.name, terms.alloc, symbols.intern)
    }

  private def atomWithFieldAccess[$: P]: P[TermId] =
    P(atomBase ~ ("." ~ ident).rep).map { case (base, fields) =>
      fields.foldLeft(base) { (obj, field) =>
        val fieldRef = terms.alloc(Term.Ref(field))
        terms.alloc(Term.Fn(intern("field_access"), IArray(obj, fieldRef), IArray.empty))
      }
    }

  private def atomBase[$: P]: P[TermId] =
    P(
      literal |
      variable |
      refTerm |
      prefixTerm |
      fnOrInstOrIdent |
      collectionLiteral |
      setLiteral |
      tupleLiteralOrParenExpr
    )

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
    P(
      (ident ~ ":" ~/ term).map { case (k, v) => Right((k, v)) } |
      term.map(Left(_))
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
    // WI-288: arrow and tuple types lower to the reflect `Type` entities
    // (`anthill.prelude.Type.arrow` / `named_tuple`), mirroring rustland's
    // `type_expr_to_term`. Previously both fell through to a `Ref("_")`
    // sentinel, silently discarding the structure.
    case TypeExpr.Arrow(params, ret, effects) =>
      // Single param stays bare; a multi-param list collapses to a
      // positional named-tuple `_0, _1, …`, exactly as rustland does.
      val paramTerm =
        if params.length == 1 then typeExprToRef(params.head)
        else namedTupleTypeTerm(params.zipWithIndex.map((p, i) => (intern(s"_$i"), p)))
      val resultTerm = typeExprToRef(ret)
      val effectsList = typeListTerm(effects.map(typeExprToRef))
      // Named args in canonical (alphabetical) order: effects, param, result.
      terms.alloc(Term.Fn(intern("anthill.prelude.Type.arrow"), IArray.empty,
        IArray((intern("effects"), effectsList), (intern("param"), paramTerm),
               (intern("result"), resultTerm))))
    case TypeExpr.TupleType(fields) =>
      namedTupleTypeTerm(fields)

  /** Build `anthill.prelude.Type.named_tuple(fields: List[TypeField])` from
    * `(name, type)` field pairs. Shared by tuple types and multi-parameter
    * arrow parameter lists. Mirrors rustland's `make_named_tuple_type`. */
  private def namedTupleTypeTerm(fields: IndexedSeq[(TermSymbol, TypeExpr)]): TermId =
    val fieldTerms = fields.map { (nameSym, ty) =>
      val nameRef = terms.alloc(Term.Ref(nameSym))
      val typeTerm = typeExprToRef(ty)
      terms.alloc(Term.Fn(intern("anthill.prelude.Type.TypeField"), IArray.empty,
        IArray((intern("name"), nameRef), (intern("type"), typeTerm))))
    }
    terms.alloc(Term.Fn(intern("anthill.prelude.Type.named_tuple"), IArray.empty,
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
    P("[" ~/ (
      "]".map(_ => terms.alloc(Term.Fn(intern("ListLiteral"), IArray.empty, IArray.empty))) |
      (term.rep(1, sep = ",") ~ ("|" ~/ term).? ~ "]").map { case (elems, tail) =>
        val all = ArrayBuffer.from(elems)
        tail.foreach(all += _)
        terms.alloc(Term.Fn(intern("ListLiteral"), IArray.from(all), IArray.empty))
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

  // ── Expression bodies ────────────────────────────────────────

  private def exprBody[$: P]: P[TermId] =
    P(matchExpr | ifExpr | letExpr | lambdaExpr | term)

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

  /** `let pat [: T] = value in body`. The optional `: T` annotation
    * (proposal 035 form (1), WI-185) supplies an expected-type hint to the
    * typer for the value position. Mirrors rustland: encoded as a
    * `type_name` named-arg child holding the type lowered to a term; the
    * positional args stay `(pattern, value, body)` so the bare form is
    * unchanged. */
  private def letExpr[$: P]: P[TermId] =
    P(keyword("let") ~/ pattern ~ (":" ~ typeExpr).? ~ "=" ~ exprBody ~ keyword("in") ~ exprBody).map {
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
    P(patternConstructor | patternTuple | patternLiteral | patternWildcard | patternVar)

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
      ("(" ~ pattern ~ "," ~ pattern.rep(1, sep = ",") ~ ")").map { case (first, rest) =>
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
      keyword("export").map(_ => Visibility.Export) |
      keyword("public").map(_ => Visibility.Public)
    )

  // ── Import / Export ──────────────────────────────────────────

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

  private def exportClause[$: P]: P[IndexedSeq[Name]] =
    P(keyword("export") ~/ name.rep(1, sep = ",")).map(_.toIndexedSeq)

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

  private type BodyContent = Either[Either[Import, IndexedSeq[Name]], Item]

  private def bodyContent[$: P]: P[BodyContent] =
    P(
      importClause.map(i => Left(Left(i))) |
      exportClause.map(e => Left(Right(e))) |
      declaration.map(Right(_))
    )

  private def processContent(
    content: Seq[BodyContent]
  ): (IndexedSeq[Import], IndexedSeq[Name], IndexedSeq[Item]) =
    val imports = ArrayBuffer.empty[Import]
    val exports = ArrayBuffer.empty[Name]
    val items = ArrayBuffer.empty[Item]
    content.foreach {
      case Left(Left(imp)) => imports += imp
      case Left(Right(exps)) => exports ++= exps
      case Right(item) => items += item
    }
    (imports.toIndexedSeq, exports.toIndexedSeq, items.toIndexedSeq)

  private def bracedBody[$: P]: P[(IndexedSeq[Import], IndexedSeq[Name], IndexedSeq[Item])] =
    P("{" ~/ bodyContent.rep ~ "}").map(cs => processContent(cs))

  private def endBody[$: P]: P[(IndexedSeq[Import], IndexedSeq[Name], IndexedSeq[Item])] =
    P(bodyContent.rep ~ keyword("end")).map(cs => processContent(cs))

  private def body[$: P]: P[(IndexedSeq[Import], IndexedSeq[Name], IndexedSeq[Item])] =
    P(bracedBody | endBody)

  // ── Declarations ─────────────────────────────────────────────

  private def namespaceDecl[$: P]: P[Item] =
    P(keyword("namespace") ~/ name ~ body).map { case (n, (imports, exports, items)) =>
      Item.NamespaceItem(Namespace(n, imports, exports, items, mkSpan(0, 0)))
    }

  private def sortDecl[$: P]: P[Item] =
    P(visibility.? ~ keyword("sort") ~/ name ~ (abstractSortRest | sortWithBodyRest)).map {
      case (vis, n, Left((defn, meta))) =>
        Item.AbstractSortItem(AbstractSort(vis, n, defn, IndexedSeq.empty, meta, mkSpan(0, 0)))
      case (vis, n, Right((imports, exports, items, meta))) =>
        Item.SortWithBodyItem(SortWithBody(vis, n, IndexedSeq.empty, imports, exports, items, meta, mkSpan(0, 0), SortDeclKind.Sort))
    }

  /** `enum NAME ... end` — same body shape as `sort NAME ... end` but the
    * declaration kind is recorded as `Enum` (proposal 025). */
  private def enumDecl[$: P]: P[Item] =
    P(visibility.? ~ keyword("enum") ~/ name ~ body ~ metaBlock.?).map {
      case (vis, n, (imports, exports, items), meta) =>
        Item.SortWithBodyItem(SortWithBody(vis, n, IndexedSeq.empty, imports, exports, items, meta, mkSpan(0, 0), SortDeclKind.Enum))
    }

  private def abstractSortRest[$: P]: P[Left[(TypeExpr, Option[MetaBlock]), Nothing]] =
    P("=" ~/ typeExpr ~ metaBlock.?).map { case (te, mb) => Left((te, mb)) }

  private def sortWithBodyRest[$: P]: P[Right[Nothing, (IndexedSeq[Import], IndexedSeq[Name], IndexedSeq[Item], Option[MetaBlock])]] =
    P(body ~ metaBlock.?).map { tup =>
      // fastparse flattens: (imports, exports, items, meta)
      val imports = tup._1
      val exports = tup._2
      val items = tup._3
      val meta = tup._4
      Right((imports, exports, items, meta))
    }

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
      (ruleHeads ~ (":-" ~/ term.rep(1, sep = ",")).?).flatMap { case (hs, body) =>
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
    ).map { case (vis, n, tps, params, retType, (reqs, enss, effs), opBody, meta) =>
      Item.OperationItem(Operation(vis, n, tps.getOrElse(IndexedSeq.empty), params.toIndexedSeq, retType,
        reqs, enss, effs, opBody, meta, mkSpan(0, 0)))
    }

  private def operationEntry[$: P]: P[Operation] =
    P(visibility.? ~ simpleName ~ operationTypeParamList.? ~ "(" ~ param.rep(sep = ",") ~ ")" ~ "->" ~ typeExpr ~
      operationClauses ~ ("=" ~/ exprBody).? ~ metaBlock.?
    ).map { case (vis, n, tps, params, retType, (reqs, enss, effs), opBody, meta) =>
      Operation(vis, n, tps.getOrElse(IndexedSeq.empty), params.toIndexedSeq, retType,
        reqs, enss, effs, opBody, meta, mkSpan(0, 0))
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

  private def operationClauses[$: P]: P[(IndexedSeq[IndexedSeq[TermId]], IndexedSeq[IndexedSeq[TermId]], IndexedSeq[Effect])] =
    P(operationClause.rep).map { clauses =>
      val reqs = ArrayBuffer.empty[IndexedSeq[TermId]]
      val enss = ArrayBuffer.empty[IndexedSeq[TermId]]
      val effs = ArrayBuffer.empty[Effect]
      clauses.foreach {
        case (0, terms: IndexedSeq[TermId] @unchecked) => reqs += terms
        case (1, terms: IndexedSeq[TermId] @unchecked) => enss += terms
        case (2, effects: IndexedSeq[Effect] @unchecked) => effs ++= effects
        case _ =>
      }
      (reqs.toIndexedSeq, enss.toIndexedSeq, effs.toIndexedSeq)
    }

  private def operationClause[$: P]: P[(Int, IndexedSeq[?])] =
    P(
      (keyword("requires") ~/ term.rep(1, sep = ",")).map(ts => (0, ts.toIndexedSeq)) |
      (keyword("ensures") ~/ term.rep(1, sep = ",")).map(ts => (1, ts.toIndexedSeq)) |
      // Mirrors rustland's `_effect_set` shared between operation
      // `effects` and arrow-type `@`: bare single type or braced list
      // (possibly with trailing comma).
      (keyword("effects") ~/ effectSet).map(ts => (2, ts.map(Effect(_)).toIndexedSeq))
    )

  private def requiresDeclItem[$: P]: P[Item] =
    P(keyword("requires") ~/ typeExpr).map { te =>
      Item.RequiresDeclItem(RequiresDecl(te, mkSpan(0, 0)))
    }

  private def entityDecl[$: P]: P[Item] =
    P(visibility.? ~ keyword("entity") ~/ simpleName ~ ("(" ~ fieldDecl.rep(1, sep = ",") ~ ")").? ~ metaBlock.?
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
      enumDecl |
      ruleDecl |
      operationDecl |
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

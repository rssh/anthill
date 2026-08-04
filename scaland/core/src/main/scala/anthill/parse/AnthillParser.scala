package anthill.parse

import anthill.intern.{TermSymbol, SymbolTable}
import anthill.term.{Term, TermId, Var, VarId, Literal, OrderedDouble}
import anthill.span.{LineIndex, Span}
import fastparse.*
import scala.collection.mutable.{ArrayBuffer, HashMap}

object AnthillParser:

  def parse(source: String, fileName: String = "<input>"): Either[IndexedSeq[ParseError], ParsedFile] =
    val symbols = SymbolTable()
    val terms = SimpleTermStore()
    val errors = ArrayBuffer.empty[ParseError]
    // WI-947: ONE index per source, built here and threaded into the parser, so
    // every span this parse produces resolves its `line:col` against the same
    // O(len) scan instead of one scan per span.
    val lines = LineIndex(source)
    val parser = new AnthillParserImpl(source, fileName, lines, symbols, terms, errors)
    val result = fastparse.parse(source, parser.sourceFile(using _))
    // WI-952: the trivia skipper has no error channel of its own. It runs inside
    // productions that backtrack, so a refusal it pushed into `errors` could be
    // dropped by the WI-950 scoping — it records the OPENER of an unterminated
    // block comment on the parser instead, and it is reported from here, ahead of
    // any other error: the unterminated comment is the root cause of whatever the
    // parse then made of the text it swallowed, and it is reported whether or not
    // the parse failed (a comment left open at the last line swallows to `End` and
    // the file parses "clean" without this).
    val unterminated = parser.unterminatedComment.toList
    result match
      case Parsed.Success(items, _) =>
        if unterminated.isEmpty && errors.isEmpty then Right(ParsedFile(ArrayBuffer.from(items), symbols, terms))
        else Left((unterminated ++ errors).toIndexedSeq)
      case f: Parsed.Failure =>
        // WI-947: the POSITION rides on the span, and is rendered by the one
        // located renderer every diagnostic family shares. `Parsed.Failure.msg`
        // is not used: it spells its own `Position row:col` INSIDE the message
        // text, so a user got fastparse's numbering here and nothing at all from a
        // load error — the two families now render the same way by construction.
        // No "expected …" half: fastparse populates `Failure.label` only under
        // `verboseFailures = true`, which the `fastparse.parse` above does not pass,
        // so it is ALWAYS empty here — a branch on it would be dead code. `f.msg`
        // carried no expectation set either (it is `Position …, found …`), so nothing
        // is lost; recovering one means `f.trace()`, which re-runs the whole parse.
        // WI-970: a ZERO-WIDTH span, and deliberately so — the only one left in the
        // file. Every other was a construct reported at less than its own width; here
        // the parse FAILED, so there is no construct to bracket and `idx` is a POINT
        // ("the input stops making sense here"). `formatTrailing` is a display string
        // — quoted, escaped and truncated — so its length is not a source length and
        // cannot supply an end. See [[Span]] on why this is not an exception to the
        // tight-end invariant.
        val idx = f.index
        val found = Parsed.Failure.formatTrailing(f.extra.input, idx)
        errors += ParseError(s"parse error: found $found", Span.at(fileName, lines, idx, idx))
        Left((unterminated ++ errors).toIndexedSeq)

end AnthillParser

// Token-level parsers — no whitespace between characters
private object Tokens:
  import fastparse.NoWhitespace.*

  def identToken[$: P]: P[String] =
    P(CharIn("a-zA-Z_") ~ CharsWhileIn("a-zA-Z0-9_\\-", 0)).!

  def variableToken[$: P]: P[String] =
    P("?" ~ (CharIn("a-zA-Z_") ~ CharsWhileIn("a-zA-Z0-9_\\-", 0)).?.!)

  /** A string literal, ESCAPE-AWARE. Mirrors rustland's token regex
    * `/"([^"\\]|\\.)*"/`: a `\` consumes the next character whatever it is, so an
    * embedded `\"` does not close the literal. Without this a C++ include mapping
    * (`"#include \"anthill_runtime.hpp\""`, stdlib `realization/cpp_std.anthill`)
    * ended at the first inner quote and the rest of the line was a syntax error. */
  def stringToken[$: P]: P[String] =
    P("\"" ~ (CharsWhile(c => c != '"' && c != '\\', 1) | ("\\" ~ AnyChar)).rep.! ~ "\"")
      .map(decodeStringEscapes)

  /** Decode the `\.`-style escapes the token above accepts. Mirrors rustland's
    * `decode_string_escapes`, down to its two fall-through rules: an UNKNOWN escape
    * passes the trailing char through, and a lone trailing `\` is kept literal. The
    * matching encoder is `persistence::print`'s String case (\" \\ \n \r \t). */
  private def decodeStringEscapes(raw: String): String =
    if !raw.contains('\\') then raw
    else
      val out = new StringBuilder(raw.length)
      var i = 0
      while i < raw.length do
        val c = raw.charAt(i)
        if c == '\\' && i + 1 < raw.length then
          raw.charAt(i + 1) match
            case '"'  => out += '"'
            case '\\' => out += '\\'
            case 'n'  => out += '\n'
            case 'r'  => out += '\r'
            case 't'  => out += '\t'
            case other => out += other
          i += 2
        else
          out += c
          i += 1
      out.toString

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
  lines: LineIndex,
  symbols: SymbolTable,
  terms: SimpleTermStore,
  errors: ArrayBuffer[ParseError]
):

  // ── Refusal scoping (WI-950) ─────────────────────────────────

  /** `P`, SHADOWING `fastparse.P` for every production in this class: a production
    * that FAILS drops the refusals recorded under it, along with the rest of its
    * output.
    *
    * Three productions refuse from inside a `.map` — the WI-639 projection-label
    * checks, the braced-`operation`-block visibility refusal, the WI-850 type-param
    * default. A `.map` runs when ITS production succeeds, which is not the same as
    * the enclosing parse accepting that text: fastparse may backtrack out of the
    * alternative afterwards. In a flat shared buffer the refusal outlived the
    * backtrack, and since `AnthillParser.parse` returns `Left` whenever the buffer
    * is non-empty, a discarded production could both add noise to an unrelated
    * failure and — given one more backtrackable alternative over any refusal site —
    * REFUSE AN OTHERWISE-GOOD PARSE.
    *
    * WHERE A REFUSAL LANDS, exactly: a `.map` is applied to the value this wrapper
    * already returned, so a refusal is recorded into the scope of the INNERMOST
    * ENCLOSING wrapped production, not the mapped one's own. That is enough, because
    * discarding a production's output is always the failure of something that
    * encloses it, and the whole grammar is written as `def x[$: P] = P(…)` — so
    * there is a wrapped production between every backtrack point and every refusal.
    * Keep new productions in that shape: this is a convention the compiler does not
    * check, and a production written as a bare `inner.map(…)` at an outer position
    * would establish no scope of its own.
    *
    * `sourceFile` is the deliberate exception — see the comment there. The `Tokens`
    * object is a separate scope and keeps `fastparse.P`; it records nothing. */
  private inline def P[T](inline t: fastparse.P[T])(using
    name: sourcecode.Name, ctx: fastparse.P[?]
  ): fastparse.P[T] =
    val mark = errors.length
    val run = fastparse.P[T](t)(using name, ctx)
    // Production failure is the ordinary control flow of a backtracking parser, and
    // almost none of it records anything — so test before calling.
    if !run.isSuccess && errors.length > mark then errors.dropRightInPlace(errors.length - mark)
    run

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
    TypeExpr.Variable(terms.alloc(Term.Var(Var.Global(freshAnonymousVar()))), IndexedSeq.empty)

  // ── Helpers ──────────────────────────────────────────────────

  /** The span of `[s, e)` in this file, `line:col` resolved through the file's ONE
    * [[LineIndex]] (WI-947). Every span in the parse comes from here — `Span`'s
    * constructor is package-private precisely so a caller cannot hand-build one
    * with a placeholder row, which is what all seven fields were before. */
  private def mkSpan(s: Int, e: Int): Span = Span.at(fileName, lines, s, e)
  private def intern(s: String): TermSymbol = symbols.intern(s)

  /** [[mkSpan]] with the end held at [[contentEnd]] — the WI-972 repair, and the only
    * difference between what the two combinators below bracket and the index pair they
    * were handed.
    *
    * WHAT IT REPAIRS, root cause first: fastparse rewinds the trivia a `~` skipped when
    * the right-hand side then matches nothing —
    * `if (!rhsMadeProgress && input.isReachable(postRhsIndex)) postLhsIndex`
    * (`internal.MacroInlineImpls.parsedSequence0`, 3.1.1) — and `isReachable(i)` is
    * `i < length`. AT END OF INPUT THE REWIND DOES NOT HAPPEN, so a production whose
    * last element matched nothing — an optional (`metaBlock.?`) or an empty `rep` — keeps
    * the trivia its own `~` had skipped past it. The file's LAST top-level declaration is
    * the one construct that can be in that position, and it spanned every trailing
    * newline, blank line and COMMENT after it. Nothing about the `~`-vs-`~~` decision the
    * combinators own is wrong at any of those sites, which is why neither the WI-970
    * sweep nor the WI-971 [[Index]] shadow could see this: it is not a spelling.
    *
    * A BAD END IS ALWAYS EXACTLY `source.length`, by that same code — the rewind is
    * skipped only when `postRhsIndex == length`, so the index the construct carries away
    * is the end of input itself, never some interior point of the trivia. A `min` with
    * the end of content is therefore the whole repair; it cannot move a span that was
    * already tight, because no construct ends inside the trailing trivia.
    *
    * NOT A BACKWARD SCAN. Trimming whitespace off the end (the obvious move) is
    * insufficient — `fact p(x: 1)\n-- done\n` ends its span on the `\n` AFTER a comment,
    * and a scan that steps back over the newline stops on `e`. Re-deriving where the
    * comment began means running the trivia grammar backwards, which is a second
    * implementation of [[ws]] and would have to agree with it forever. The skipper
    * instead reports the one position it already knows.
    *
    * `max(s, …)`: a zero-width capture at end of input (`located` around a production
    * that matched empty there) must stay zero-width rather than invert. */
  private def mkSpanToContent(s: Int, e: Int): Span =
    mkSpan(s, math.max(s, math.min(e, contentEnd)))

  /** The span of the ONE token `p` matches, discarding its value — what a
    * keyword-led production wants (`spanOfToken(keyword("if"))`, `spanOfToken("[")`).
    *
    * WI-965: this and [[located]] replace the open-coded `Index ~ p ~~ Index` +
    * `mkSpan(s, e)` that had accreted at ~30 productions, each spelling the same
    * three-step bracket-and-resolve by hand and each free to get the `~~` wrong.
    *
    * NO PRODUCTION STAYS HAND-WRITTEN — WI-971 finished the conversion the two earlier
    * WIs each thought had a remainder, and [[Index]] below now makes the hand-written
    * spelling a compile error. Both remainders were misreadings, and the shape of each
    * is worth keeping, because the next production to look unconvertible will look
    * unconvertible in one of these two ways:
    *
    *   * WI-965 said "multi-token"; WI-970 disproved it by conversion. [[located]] is
    *     generic in its payload, so a dotted `name` or a `.(…)` projection rides it at
    *     the cost of one nesting level in the destructuring.
    *   * WI-970 then said "its start is not an `Index` at its own entry", and named six.
    *     Every one of them WAS bracketable — the start was simply being carried in a
    *     shape other than a `Span`. The four `sort` shapes read a start handed down from
    *     `sortDecl` as an `Int`, and now take a `Span` from a `located` around the
    *     dispatcher; `sortTypeParam` recovered its start from `nameSpan.start`, and
    *     `proofStep` took two ends off one start — both are [[located]] NESTED inside
    *     [[located]], the inner bracket closing early.
    *
    * `~~` for the trailing `Index`, always: fastparse's plain `~` skips the trivia
    * after the token FIRST, which stretches the span over it — the [[Span]] invariant,
    * and what WI-970 measured wrong at five productions (the census is at [[Index]],
    * stated once). Having two places that spell it is the point — the trailing `~` was
    * a per-site decision at every one of the ~30.
    *
    * TWO and not one, deliberately: `spanOfToken(p) = located(p).map(_._2)` does
    * compile (checked, not assumed — a `P[Unit]` rides `located` as `A = Unit`), and
    * it was rejected because it allocates a throwaway `(Unit, Span)` per token on the
    * parser's hottest path and hands fastparse's failure stack the wrong production
    * name. One line of duplication buys both back.
    *
    * THAT REJECTION IS ABOUT PER-TOKEN COST, and does not forbid what WI-970 did — the
    * productions it routed through [[located]] are per-DECLARATION. Counted over the
    * 105-file corpus: the token-level sites this combinator serves face ~46 000 open
    * brackets and ~2 900 `?`-variables, where `simpleName` sees ~2 500 declarations and
    * `operationTypeParam` 83. Two orders of magnitude, so the extra pair is real at one
    * and noise at the other.
    *
    * The `Span` rides as ONE slot through further `~` composition, because fastparse
    * flattens `scala.TupleN`s and `Span` is a nominal case class — `spanOfToken(…) ~/
    * x` is `(Span, X)`, where a raw `(start, end)` pair would dissolve into two loose
    * `Int`s for the call site to re-pair by position. Same reason [[OpToken]] /
    * [[ProjectionMember]] are case classes.
    *
    * CONTROL — WI-965 adds NO test, because it changes no behaviour, so the honest
    * question is which EXISTING ones would catch a mis-conversion. Measured by
    * breaking each combinator in turn against the 311-test suite:
    *
    *   * make `located` hand back [[Span.empty]] and 6 fail — `ParseSpanCoverageTest`
    *     (both cases), `DiagnosticLocationTest`'s infix / dot-member / synthesized-
    *     marker cases, and `DeclarationSpanTest`'s type-param-name case;
    *   * make `spanOfToken` hand back [[Span.empty]] and 3 fail — both
    *     `ParseSpanCoverageTest` cases and the synthesized-marker one (the `let` and
    *     the bracket literals go through this one).
    *
    * WI-970 CLOSED THE HOLE IN THAT CONTROL. When WI-965 wrote it, swapping the `~~`
    * below back to a whitespace-skipping `~` — the exact mistake these two exist to
    * make unrepeatable — failed NOTHING, because no test read `end`. It failed EIGHT
    * after WI-970 and FIFTEEN after WI-971 (measured, 327 tests): ten in `SpanEndTest`,
    * three in `DeclarationSpanTest`, two in `ParseSpanCoverageTest`. The jump is not the
    * six new tests — it is that the whole declaration family rides this one `~~` now
    * that WI-971 removed the per-site copies, so a single mistake here is no longer a
    * single production's mistake. */
  private def spanOfToken[$: P](p: => P[Unit]): P[Span] =
    P(fastparse.Index ~ p ~~ fastparse.Index).map { case (s, e) => mkSpanToContent(s, e) }

  /** [[spanOfToken]] for a token that CARRIES a value: `located(ident)` is
    * `(TermSymbol, Span)`. The pair flattens into the enclosing sequence, so a caller
    * destructures it as two adjacent slots — `case (sym, span, …)`. */
  private def located[A, $: P](p: => P[A]): P[(A, Span)] =
    P(fastparse.Index ~ p ~~ fastparse.Index).map { case (s, a, e) => (a, mkSpanToContent(s, e)) }

  /** THE TYPE IS THE ERROR MESSAGE. A hand-written bracket reports either `value ~ is
    * not a member of … BracketSpansWithLocatedOrSpanOfToken` (a LEADING `Index`) or
    * that type against `ParsingRun` (a TRAILING one) — so the rule reaches the author in
    * the compiler output, not only in the doc on [[Index]] below.
    *
    * The name carries the message because nothing else could. Both idiomatic spellings
    * were tried and neither reports: `@compileTimeOnly` loses to the type error it
    * exists to explain, and `inline def Index: Nothing = compiletime.error(…)` fires
    * NOTHING — `Nothing` conforms to `ParsingRun`, so the hand-written bracket
    * type-checks and the message never surfaces from inside fastparse's `P` macro. A
    * type mismatch is the one signal that survives, which makes the type's NAME the
    * only place a sentence fits. */
  private class BracketSpansWithLocatedOrSpanOfToken

  /** `Index`, SHADOWING `fastparse.Index` for every production in this class: a
    * hand-written span bracket is a COMPILE error, so [[spanOfToken]] and [[located]]
    * above are the only way to capture one.
    *
    * WI-971, and the reason it is a shadow rather than a convention: WI-965 introduced
    * the two combinators and left ~30 productions still spelling the bracket by hand,
    * and WI-970 then measured EIGHT of them wrong. THE CENSUS, stated once and here
    * because this is the enforcement site: five stretched over trailing trivia (a
    * whitespace-skipping `~` before the trailing `Index`), two captured zero width, and
    * one — the `flatMap` case below — had no `Index` at all. Repairing the sites someone
    * happened to grep leaves the next author free to write the ninth. Removing the
    * spelling from the vocabulary this file is written in does not.
    *
    * THE ESCAPE IS `fastparse.Index`, written out — the same shape `sourceFile` uses to
    * opt out of the `P` shadow above, and greppable for exactly that reason. Only the
    * two combinators use it today: every declaration production, INCLUDING the `sort`
    * shapes whose start used to be handed down from `sortDecl` as a bare `Int`, now
    * brackets itself through [[located]]. A production that genuinely cannot must write
    * the qualified name and say why, rather than reach for a short alias that would read
    * like ordinary vocabulary again.
    *
    * SCOPE, since the `P` shadow above names its own exception: this covers the class,
    * not the file — `object Tokens` keeps `fastparse.Index`. That is not a hole, because
    * `Tokens` cannot produce a span whatever it captures: [[mkSpan]] and both combinators
    * are private members of this class, and `Tokens` returns `String`s.
    *
    * WHAT THIS DOES NOT CATCH, so it is not mistaken for a total guard: the eighth site
    * had no `Index` of its own at all — `ruleArrowChoice` leaked trivia into every `:-`
    * rule's span through fastparse's `flatMap`, which runs the whitespace skipper before
    * its continuation (`flatMapX` does not). No lint over this name would have seen it.
    * Guarding the NAME is one mechanism; the property that no span ends on whitespace is
    * the other, and it is checked over the corpus by `ParseSpanCoverageTest` — the same
    * two-mechanism split WI-961 documents there, for the same reason. */
  private val Index = new BracketSpansWithLocatedOrSpanOfToken

  // ── Custom whitespace ────────────────────────────────────────

  /** WI-952: an unterminated `{- … ` / `{< … ` block, named by its OPENING position
    * — the opener is what the author has to fix, and the position where the scan
    * gave up is the far end of text they meant as a comment.
    *
    * NOT the `errors` buffer: the skipper runs inside productions that backtrack,
    * and WI-950 scoping drops what a discarded production recorded. This field is
    * outside that scoping, which is sound because the fact is about the SOURCE, not
    * about any production: a `{-` reached at a trivia position with no `-}` after it
    * is unterminated whichever alternative was being tried. Backtracking can reach
    * the same defect by several routes, so keep the EARLIEST opener seen — for a
    * nested `{- {- `, that is the outer one. */
  private var unterminated: Option[ParseError] = None

  def unterminatedComment: Option[ParseError] = unterminated

  /** WI-972: where this file's CONTENT stops and its trailing trivia begins — the end
    * every span is held to by [[mkSpanToContent]], which is where the defect and the
    * `min` are argued.
    *
    * MEASURED FORWARD, NOT SCANNED BACKWARD, and by the skipper itself because it is the
    * one thing that knows what trivia is. Every position the skipper is entered at is a
    * TOKEN BOUNDARY (a string literal's insides are parsed under `NoWhitespace`, so no
    * entry lands inside one), and it consumes to end of input from exactly those
    * boundaries that have nothing but trivia after them. The EARLIEST such boundary is
    * the end of content: a boundary before it has content after it by definition, and
    * the boundary that ends the last token is one the grammar always enters the skipper
    * at — that entry is what swallows the trailing trivia in the first place, so the
    * position is recorded strictly before any span that needs it is built.
    *
    * OUTSIDE THE WI-950 REFUSAL SCOPING, like [[unterminated]] above and for the same
    * reason: it is a fact about the SOURCE, not about any production. Backtracking can
    * enter the skipper at the same boundary by several routes and reach the same answer,
    * and an alternative that is discarded does not make the text after it stop being
    * trivia — so `min`, never a reset.
    *
    * The initial value is the file's own end: a file with NO trailing trivia has its
    * content run to there, and the `min` in [[mkSpanToContent]] is then a no-op. */
  private var contentEnd: Int = source.length

  private def noteUnterminatedComment(open: Int, opener: String, closer: String): Unit =
    if unterminated.forall(_.span.start > open) then
      // WI-947: the message no longer spells `opened at $open`. The span carries the
      // opener's position and renders it as `line:col`; a raw UTF-16 offset beside it
      // is a second encoding of the same point, in the unit this WI exists to retire.
      unterminated = Some(ParseError(
        s"Unterminated block comment: `$opener` is never closed by `$closer`",
        mkSpan(open, open + opener.length)))

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
          val open = index
          index += 2
          var depth = 1
          while index + 1 < length && depth > 0 do
            if input(index) == '{' && input(index + 1) == '-' then
              depth += 1; index += 2
            else if input(index) == '-' && input(index + 1) == '}' then
              depth -= 1; index += 2
            else index += 1
          // Input exhausted with the comment still open (WI-952). Swallow the rest —
          // it is comment text by intent — and let `parse` report the opener, rather
          // than resuming a declaration on the comment's last character.
          if depth > 0 then
            noteUnterminatedComment(open, "{-", "-}")
            index = length
        else if index + 1 < length && c == '{' && input(index + 1) == '<' then
          // Doc-comment block: `{< ... >}` (used by stdlib sort.anthill).
          val open = index
          index += 2
          while index + 1 < length &&
              !(input(index) == '>' && input(index + 1) == '}') do
            index += 1
          // Loop exits either ON the `>}` or on exhausted input — `index + 1 < length`
          // separates the two, and the second is the WI-952 unterminated case.
          if index + 1 < length then index += 2
          else
            noteUnterminatedComment(open, "{<", ">}")
            index = length
        else
          continue = false
      // WI-972: nothing but trivia from here to end of input — see [[contentEnd]].
      if index >= length && ctx.index < contentEnd then contentEnd = ctx.index
      ctx.freshSuccessUnit(index)

  // ── Lexical ──────────────────────────────────────────────────

  private def ident[$: P]: P[TermSymbol] = P(Tokens.identToken).map(intern)

  private def keyword[$: P](kw: String): P[Unit] =
    P(Tokens.identToken.filter(_ == kw)).map(_ => ())

  // WI-970: [[located]] is generic in its payload, so a MULTI-TOKEN production rides it
  // too — the cost is one nesting level in the destructuring (`case ((first, rest),
  // span)`), which is cheaper than a per-site `~~` decision, since getting that decision
  // wrong at four such sites is what WI-970 exists to repair.
  private def name[$: P]: P[Name] =
    P(located(ident ~ ("." ~ ident).rep)).map { case ((first, rest), span) =>
      Name(first +: rest.toIndexedSeq, span)
    }

  private def simpleName[$: P]: P[Name] =
    P(located(ident)).map { case (sym, span) => Name.simple(sym, span) }

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
    P(located(Tokens.variableToken) ~ fnArgsList.?).map { case (varName, span, args) =>
      val varTid =
        if varName.isEmpty then terms.alloc(Term.Var(Var.Global(freshAnonymousVar())))
        else terms.alloc(Term.Var(Var.Global(getOrCreateVar(intern(varName)))))
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
          // WI-957: `ho_apply` is a name the loader RESOLVES, so it is located — at
          // the applied variable, the text that produced the application.
          terms.allocAt(
            Term.Fn(intern("ho_apply"), IArray.from(posArgs), IArray.from(namedArgs)),
            span)
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
      else TypeExpr.Variable(terms.alloc(Term.Var(Var.Global(getOrCreateVar(intern(varName))))), IndexedSeq.empty)
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
    P(spanOfToken("+") ~/ simpleEffect).map { case (span, te) =>
      wrapEffectOp("present", span)(te) }

  private def effectAbsence[$: P]: P[TypeExpr] =
    P(spanOfToken("-") ~/ simpleEffect).map { case (span, te) =>
      wrapEffectOp("absent", span)(te) }

  /** WI-961: located at the `+` / `-`, the token that chose the wrapper — the
    * `present`/`absent` functor is written nowhere, exactly as `add` is not. */
  private def wrapEffectOp(op: String, span: Span)(e: TypeExpr): TypeExpr =
    val inner = typeExprToRef(e)
    TypeExpr.Variable(
      terms.allocAt(Term.Fn(intern(op), IArray(inner), IArray.empty), span), IndexedSeq.empty)

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

  /** A component of a tuple type. WI-763 adds the DENOTED component `person:
    * "name"` — a named component whose value is a CONSTANT standing in type
    * position. Its motivating case is a projection's keep spec (`Project[T = …,
    * Keep = (person: "name", years: "age")]`), which maps each result key to its
    * source column's NAME, and a name reaches type position only as a denoted
    * (there are no singleton types). The denoted arm is tried FIRST for the same
    * reason `commonTypeExpr` orders it first: `true` / `false` would otherwise be
    * read as a `simple_type` name. */
  private def tupleTypeArg[$: P]: P[TupleField] =
    P(
      (ident ~ ":" ~ denotedLiteral).map { case (n, t) => TupleField(n, t) } |
      (ident ~ ":" ~ typeExpr).map { case (n, t) => TupleField(n, t) } |
      typeExpr.map(t => TupleField(intern("_"), t))
    )

  // ── Terms ────────────────────────────────────────────────────

  /** An operator token and ITS OWN SPAN (WI-957) — what a diagnostic about the
    * functor the desugar mints (`add` for `+`) has to point at, since that functor
    * appears nowhere in the source.
    *
    * A CASE CLASS, not a pair: fastparse FLATTENS tuple results across `~`, so a
    * `P[(TermSymbol, Span)]` would dissolve into the enclosing sequence's tuple and
    * the operator list and the span list would be built by two separate positional
    * drains — one rename away from mislocating every operator in a chain. */
  private case class OpToken(sym: TermSymbol, span: Span)

  private def term[$: P]: P[TermId] =
    P(atomWithFieldAccess ~ (infixOp ~ atomWithFieldAccess).rep).map { case (first, pairs) =>
      buildInfix(first, pairs)
    }

  /** A `_term` for an operation's `requires` / `ensures` clause goal. Like
    * `term`, but `=` (equality) is NON-ASSOCIATIVE: a clause goal carries at
    * most one. A leading chain of non-`=` infix ops, then an optional single
    * `= rhs` (guarded by `!exprBodyKeyword` so `= match …` stays the operation
    * body), then a trailing non-`=` chain. The whole ordered op list still goes
    * through one `buildInfix`/Pratt pass, so precedence vs `or`/`and`/… is
    * unchanged — only a SECOND `=` is left unconsumed. That second `=` is the
    * `= <body>` separator, so e.g. `ensures result = f(x) = g(x)` keeps
    * `result = f(x)` as the postcondition AND `= g(x)` as the body, rather than
    * silently swallowing the body into a chained eq (WI-562 follow-up). Mirrors
    * rustland's non-assoc `=` under GLR: `requires Eq[T] = match l …` gives the
    * op the `match` body, while `ensures result = x` keeps the eq goal. */
  /** One item of an op-scoped `requires` list: its goal, and the NAMED requirement
    * slot's binder when the item was written `<name>: Spec[…]` (WI-840, proposal 058
    * §4.7). The op-scoped list is OVERLOADED — it carries both spec requirements
    * (WI-448) and VALUE preconditions (`requires neq(b, 0)`, WI-539) — and a binder
    * attaches only to the type flavor while coexisting with predicates in the same
    * comma list, so it is admissible at ANY position of it. */
  // WI-947: the binder carries its own TOKEN span, because a named slot becomes an
  // operation type parameter and `TypeParam` has a span of its own to fill. The span
  // rides INSIDE the `Option` rather than beside it: a binder always has a position and
  // an absent binder has nothing to position, so the two nonsense pairings — a `None`
  // with a real span, a `Some` with a filler one — are not representable.
  private case class RequiresItem(goal: TermId, binder: Option[(TermSymbol, Span)])

  /** A `requires` item, binder form first. The binder alternative backtracks cleanly
    * when no `:` follows, so an ordinary goal (which may begin with the same
    * identifier token) still parses. */
  private def requiresItem[$: P]: P[RequiresItem] =
    P((located(ident) ~ ":" ~ clauseTerm).map {
        case (b, span, t) => RequiresItem(t, Some((b, span))) } |
      clauseTerm.map(RequiresItem(_, None)))

  private def clauseTerm[$: P]: P[TermId] =
    P(
      atomWithFieldAccess ~ (nonEqInfixOp ~ atomWithFieldAccess).rep ~
        (eqClauseOp ~ atomWithFieldAccess ~ (nonEqInfixOp ~ atomWithFieldAccess).rep).?
    ).map { case (first, leading, eqTail) =>
      val pairs = ArrayBuffer.from(leading)
      eqTail.foreach { case (eqSym, eqRhs, trailing) =>
        pairs += ((eqSym, eqRhs))
        pairs ++= trailing
      }
      buildInfix(first, pairs.toSeq)
    }

  private def buildInfix(first: TermId, pairs: Seq[(OpToken, TermId)]): TermId =
    if pairs.isEmpty then first
    else
      val operands = ArrayBuffer(first)
      val ops = ArrayBuffer.empty[(TermSymbol, Span)]
      pairs.foreach { case (op, operand) =>
        ops += ((op.sym, op.span)); operands += operand }
      // WI-618: every node the infix desugar builds is parse-MINTED — `?a + ?b`
      // yields `add(?a, ?b)` whose functor is the desugar's, not the source's.
      // WI-957: which is exactly why the span it is allocated at is the OPERATOR's
      // — `add` appears nowhere in the source, so a diagnostic about that name
      // points at the `+` that denotes it.
      Pratt.desugar(operands.toIndexedSeq, ops.toIndexedSeq,
                    symbols.name, terms.allocMintedAt, symbols.intern)

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
    P(spanOfToken(keyword("let")) ~/ variable ~ "=" ~/ term).map { case (span, v, rhs) =>
      // WI-957: `unify` is resolved like any other functor, so it is located — at the
      // `let` that produced it.
      terms.allocAt(Term.Fn(intern("unify"), IArray(v, rhs), IArray.empty), span)
    }

  /** Cut (`!`) — kernel control primitive (proposal 033.1 / WI-568): a nullary
    * `cut` goal that commits to the current rule invocation. scaland has no
    * resolver-side cut semantics; the goal just round-trips as a `cut()` term. */
  private def cutGoal[$: P]: P[TermId] =
    P(spanOfToken("!")).map { span =>
      // WI-957: located at the `!`, for the same reason `unify` is located at `let`.
      terms.allocAt(Term.Fn(intern("cut"), IArray.empty, IArray.empty), span)
    }

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
        seg match
          case DotSeg.Field(field, fieldSpan, callArgs) =>
            buildFieldAccess(obj, field, fieldSpan, isValueReceiver(obj), callArgs)
          case DotSeg.Projection(members, span) =>
            buildDistributiveProjection(obj, members, span)
      }
    }

  /** Build the accessor a single `obj.member` produces: a value receiver (or any
    * call `.member(args)`) routes through `dot_apply` so args are never dropped;
    * a name receiver keeps the `field_access` builtin. Shared by the plain
    * dot-chain fold (WI-278) and the WI-639 distributive projection, so `x.(m)`
    * builds byte-identically to `x.m`. `valueRecv` is passed in (not recomputed)
    * so the projection can decide the receiver kind once for all its members.
    * A name receiver carrying call args never reaches here — `name`/`nameSuffix`
    * consumes `Foo.bar(args)` — so a name receiver always has `callArgs == None`.
    * `memberSpan` is the member TOKEN's own span (WI-957): the accessor's `Ref` /
    * `Ident` child is the symbol the loader resolves, so a name error about it
    * belongs on the `.f`, not on the whole receiver chain. */
  private def buildFieldAccess(
    obj: TermId, member: TermSymbol, memberSpan: Span, valueRecv: Boolean,
    callArgs: Option[IndexedSeq[Either[TermId, (TermSymbol, TermId)]]]
  ): TermId =
    if valueRecv || callArgs.isDefined then buildDotApply(obj, member, memberSpan, callArgs)
    else
      val fieldRef = terms.allocAt(Term.Ref(member), memberSpan)
      // WI-618: accessor provenance, as for the dotted-name build.
      terms.allocMintedAt(Term.Fn(fieldAccessSym, IArray(obj, fieldRef), IArray.empty), memberSpan)

  /** One dotted access after an atom: a field/method `.name` / `.name(args)`
    * (WI-278) or a distributive projection `.(m1, …, mn)` (WI-639). */
  private enum DotSeg:
    case Field(
      name: TermSymbol, span: Span,
      callArgs: Option[IndexedSeq[Either[TermId, (TermSymbol, TermId)]]])
    case Projection(members: IndexedSeq[ProjectionMember], span: Span)

  /** One member of a distributive projection. A bare member auto-labels
    * (`label == member`); `a: f` renames. `span` is the MEMBER token's — the
    * member is the name that gets resolved, the label only keys the result tuple
    * (WI-957). */
  private case class ProjectionMember(label: TermSymbol, member: TermSymbol, span: Span)

  private def dotSegment[$: P]: P[DotSeg] =
    // The projection opener `.(` diverges from a `.name` field access on the
    // token after `.` (`(` vs an identifier), so it is tried first and
    // backtracks cleanly to the field form. Mirrors rustland's fused `.(` token.
    P(distributiveProjectionSeg | fieldSeg)

  /** A field access `.name`, optionally a call `.name(args)` (WI-278). */
  private def fieldSeg[$: P]: P[DotSeg] =
    P("." ~ located(ident) ~ fnArgsList.?).map {
      case (name, span, args) => DotSeg.Field(name, span, args)
    }

  /** WI-639: a distributive projection segment `.(m1, …, mn)`. The `.(` opener
    * is unambiguous (no other construct follows `x.` with a `(`), so it cuts
    * after `(` — a malformed member list (`x.()`, `x.(1)`, `x.(a + b)`) is a
    * loud parse error rather than silently backtracking to leave the tail
    * unconsumed. The `.` alone stays cut-free (the alternation must fall back to
    * `fieldSeg` when the token after `.` is an identifier, not `(`). */
  private def distributiveProjectionSeg[$: P]: P[DotSeg] =
    P(located("." ~ "(" ~/ projectionMember.rep(1, sep = ",") ~ ",".? ~ ")")).map {
      case (members, span) => DotSeg.Projection(members.toIndexedSeq, span)
    }

  /** One member of a distributive projection: a bare member `f` auto-labels
    * (`label == member == f`), or `a: f` renames (label `a`, member `f`).
    * Members are plain identifiers — expression/call members are deferred
    * (proposal 052 OQ3), mirroring rustland's `projection_member`. */
  private def projectionMember[$: P]: P[ProjectionMember] =
    P(located(ident) ~ (":" ~ located(ident)).?).map {
      case (label, _, Some((member, memberSpan))) => ProjectionMember(label, member, memberSpan)
      case (member, span, None)                   => ProjectionMember(member, member, span)
    }

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
    fieldSpan: Span,
    callArgs: Option[IndexedSeq[Either[TermId, (TermSymbol, TermId)]]]
  ): TermId =
    val nameTerm = terms.allocAt(Term.Ident(field), fieldSpan)
    val posArgs = ArrayBuffer(receiver, nameTerm)
    val namedArgs = ArrayBuffer.empty[(TermSymbol, TermId)]
    callArgs.foreach(_.foreach {
      case Left(tid)     => posArgs += tid
      case Right((k, v)) => namedArgs += ((k, v))
    })
    // WI-618: accessor provenance, as for `field_access`.
    terms.allocMintedAt(Term.Fn(dotApplySym, IArray.from(posArgs), IArray.from(namedArgs)), fieldSpan)

  /** WI-639: build `x.(m1, …, mn)` — distribute the receiver `x` over the
    * member list. Each member desugars to the SAME accessor a single `x.m`
    * builds (`dot_apply(x, Ident(m))` for a value receiver, `field_access(x,
    * Ref(m))` for a name receiver, chosen once by `isValueReceiver`), then each
    * is keyed by its result label into a named `TupleLiteral`. A single member
    * 1-collapses to the scalar accessor (`x.(f)` ≡ `x.f`, whether bare or
    * renamed), so the tuple key only matters for a multi-column result. Mirrors
    * rustland's `push_distributive_projection` build + `is_value_receiver`. */
  private def buildDistributiveProjection(
    obj: TermId, members: IndexedSeq[ProjectionMember], span: Span
  ): TermId =
    // Validate result keys BEFORE building a multi-column tuple (a single member
    // 1-collapses to a scalar — no tuple, nothing to key). Each check turns an
    // otherwise-silent wrong result into a loud parse error (WI-639 review).
    if members.length > 1 then validateProjectionLabels(members, span)
    val valueRecv = isValueReceiver(obj)
    val accessors = members.map { m =>
      (m.label, buildFieldAccess(obj, m.member, m.span, valueRecv, None))
    }
    if accessors.length == 1 then accessors.head._2
    else terms.allocAt(Term.Fn(intern("TupleLiteral"), IArray.empty, IArray.from(accessors)), span)

  /** Reject the two ill-formed key shapes a multi-member projection could emit
    * into its result tuple, each a silent-corruption footgun (WI-639 review):
    *   - a `_`-prefixed label collides with the positional-tuple convention
    *     (`_1`/`_2` are re-slotted positionally, discarding the label);
    *   - a DUPLICATE label builds a duplicate-key named tuple whose later
    *     columns are silently dropped (first-match-wins downstream).
    * Mirrors rustland's `validate_projection_labels`. */
  private def validateProjectionLabels(
    members: IndexedSeq[ProjectionMember], span: Span
  ): Unit =
    val seen = scala.collection.mutable.HashSet.empty[TermSymbol]
    for label <- members.map(_.label) do
      val nm = symbols.name(label)
      if nm.startsWith("_") then
        errors += ParseError(
          s"distributive projection key `$nm` is `_`-prefixed, colliding with the " +
          s"positional-tuple convention; projection is named-only — write a positional " +
          s"tuple `(x.f1, x.f2)` explicitly, or rename (`x.(name: $nm)`)", span)
      if !seen.add(label) then
        errors += ParseError(
          s"duplicate distributive projection key `$nm`; each projected member must " +
          s"yield a distinct result key (rename a collision, e.g. `x.(a: $nm, b: …)`)", span)

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
    P("(" ~ located(keyword("forall").map(_ => "forall_in") | keyword("some").map(_ => "some_in"))
      ~ boundedBinderVar ~ keyword("in") ~/ term ~ ":" ~ goalTerm.rep(1, sep = ",") ~ ")").map {
      case (functor, span, binder, collection, body) =>
        val bodyTuple = terms.allocAt(Term.Fn(intern("tuple"), IArray.from(body), IArray.empty), span)
        terms.allocAt(
          Term.Fn(intern(functor), IArray(binder, collection, bodyTuple), IArray.empty), span)
    }

  /** The binder of a bounded quantifier MUST be a named variable (`?x`), not the
    * anonymous `?` — an anon binder never flows into the body, so the quantifier
    * would bind nothing. Rejecting the empty name (which fails the alternative,
    * leaving the `(`-dispatch to error out) mirrors rustland's loud rejection
    * (`convert_bounded_quantification`) over silently iterating an unbound body.
    * Shares the binder's `VarId` with its body uses via `getOrCreateVar`. */
  private def boundedBinderVar[$: P]: P[TermId] =
    P(Tokens.variableToken.filter(_.nonEmpty))
      .map(n => terms.alloc(Term.Var(Var.Global(getOrCreateVar(intern(n))))))

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

  /** WI-957: EVERY term this production builds is allocated at `n.span` — the
    * written name is the whole reason the node exists, and it is the symbol the
    * loader later resolves. The dotted arms use the WHOLE name's span rather than
    * the failing segment's: a `Name` carries one span for `a.b.c`, and pointing at
    * the dotted name is truthful where inventing a per-segment offset would not be. */
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
          terms.allocAt(Term.Fn(intern(funcStr), IArray.from(posArgs), IArray.from(namedArgs)), n.span)

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
          terms.allocAt(Term.Fn(intern(funcStr), IArray.from(posArgs), IArray.from(namedArgs)), n.span)

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
            val aux = terms.allocAt(
              Term.Fn(intern("type_args"), IArray.from(bPos), IArray.from(bNamed)), n.span)
            namedArgs += ((intern("type_args"), aux))
          terms.allocAt(Term.Fn(intern(funcStr), IArray.from(posArgs), IArray.from(namedArgs)), n.span)

        case NameSuffix.Bare =>
          if n.isSimple then terms.allocAt(Term.Ident(n.last), n.span)
          else
            var result = terms.allocAt(Term.Ident(n.segments.head), n.span)
            for seg <- n.segments.tail do
              val fieldRef = terms.allocAt(Term.Ref(seg), n.span)
              // WI-618: accessor provenance — a dotted name's segments are built
              // here, they are not written as a `field_access(…)` call.
              result = terms.allocMintedAt(
                Term.Fn(intern("field_access"), IArray(result, fieldRef), IArray.empty), n.span)
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
      typedVarArg.map(Left(_)) |
      exprBody.map(Left(_))
    )

  /** WI-582: a type-annotated variable argument `?x: T` in a rule LHS (e.g.
    * `rule [simp] add(?x: Numeric, 0) = ?x`). Lowers to a `typed_var(?x, type: T)`
    * marker; the loader (`reallocTerm`) STRIPS it back to the bare `?x`, keeping
    * the head structurally identical to the untyped form so the discrimination
    * tree indexes it the same (carrier-neutral — the bound rides off the
    * structural key). scaland has no typer, so the type bound is DROPPED, not
    * enforced (rustland installs it as a per-DeBruijn `Type` bound and checks it
    * at simp-firing). Mirrors `typedBinder`'s `pattern_var` type-carrying shape,
    * but the binder is a `?var`, not a plain identifier.
    *
    * A bare `?var` (`variableToken`, never an application), and `:` is not an
    * infix operator here, so `?x` followed by `:` is unambiguously a typed arg.
    * Placed after the `ident:` named-arg alt (whose key is a plain identifier,
    * never a `?var`) and before `exprBody` (which would parse `?x` and stop,
    * leaving `: T` dangling). The cut is AFTER `:`, so a plain `?x` argument
    * (no colon) fails this alt cleanly and falls through to `exprBody`. */
  private def typedVarArg[$: P]: P[TermId] =
    P(located(Tokens.variableToken) ~ ":" ~/ typeExpr).map { case (varName, span, ty) =>
      val varTid =
        if varName.isEmpty then terms.alloc(Term.Var(Var.Global(freshAnonymousVar())))
        else terms.alloc(Term.Var(Var.Global(getOrCreateVar(intern(varName)))))
      terms.allocAt(Term.Fn(intern("typed_var"), IArray(varTid),
        IArray((intern("type"), typeExprToRef(ty)))), span)
    }

  private def instArgsList[$: P]: P[IndexedSeq[SortBinding]] =
    P("[" ~ sortBinding.rep(1, sep = ",") ~ "]").map(_.toIndexedSeq)

  private def firstLocated(spans: Iterable[Span]): Span =
    spans.find(_.hasLocation).getOrElse(Span.empty)

  /** The two-span case: `own` if it has a position, else the enclosing `fallback`.
    *
    * Not sugar for `firstLocated(Seq(own, fallback))` — it is the SAME function.
    * [[Span.empty]] is the only unlocated span (`Span.render`'s "TWO cases, not four"),
    * so an unlocated `fallback` IS the `getOrElse(Span.empty)` the general form ends in.
    * Worth its own name because it is the shape every "a built node inherits its
    * parent's position" site wants, and it allocates neither the `Seq` nor the `Option`
    * — `typeListTerm` runs it once per list element. */
  private def firstLocated(own: Span, fallback: Span): Span =
    if own.hasLocation then own else fallback

  /** Lower a written type to a term.
    *
    * THE SPAN OF A LOWERED NODE (WI-961). A structural lowering —
    * `TypeExtractor.Arrow`, `NamedTuple`, an `EffectExpression` chain — has no token
    * of its own: it stands for the whole written type, so it takes the first position
    * that type can offer, recursively, because an arrow's leftmost leaf is what a
    * reader looks at first. DERIVED, and that is honest: the node covers text the
    * reader can see. What it must never be is [[Span.empty]] while the term carries a
    * resolvable name — see `SimpleTermStore.alloc` and `ParseSpanCoverageTest`.
    *
    * READ BACK, NOT RE-DERIVED (WI-964). Every arm below allocates its node AT the
    * span it derived, so `terms.spanOf(childTerm)` IS the span a walk of the child's
    * `TypeExpr` would produce — by induction over these same arms, and available in
    * O(1). Each arm therefore BUILDS its children first and reads their spans back,
    * instead of walking the raw `TypeExpr` for a span and then walking it again to
    * build. The walking form (a recursive `typeExprSpan`) re-derived its answer at
    * every level, costing O(n) + O(n-1) + … down a curried `(A) -> (B) -> (C) -> D`;
    * `ParseSpanGrowthTest` pins the difference, which is invisible in the RESULT —
    * both forms produce identical spans.
    *
    * READ BACK rather than RETURNED — i.e. this stays `TypeExpr => TermId` and does not
    * become `TypeExpr => (TermId, Span)`, which would also kill the quadratic. A
    * returned span is a SECOND copy of a node's position, free to disagree with the one
    * in the store; the store is where a node's position lives, so reading it back is the
    * form in which the two CANNOT disagree. It is also what the neighbouring builders
    * already do (`typeListTerm`, `effectExpression*`), for the same reason. */
  private def typeExprToRef(te: TypeExpr): TermId = te match
    // WI-957: a WRITTEN type name locates at the name it was written as; the
    // structural lowerings below (arrow, tuple, effect row) mint `TypeExtractor`
    // functors that appear nowhere in the source and stay locationless.
    case TypeExpr.Simple(n) => terms.allocAt(Term.Ref(n.last), n.span)
    case TypeExpr.Parameterized(n, bindings) =>
      val posArgs = ArrayBuffer.empty[TermId]
      val namedArgs = ArrayBuffer.empty[(TermSymbol, TermId)]
      bindings.foreach { sb =>
        val bt = typeExprToRef(sb.bound)
        sb.param match
          case Some(p) => namedArgs += ((p.last, bt))
          case None => posArgs += bt
      }
      terms.allocAt(Term.Fn(n.last, IArray.from(posArgs), IArray.from(namedArgs)), n.span)
    case TypeExpr.Variable(tid, _) => tid
    // WI-288 / WI-361: arrow and tuple types lower to the structural
    // `TypeExtractor` entities (`anthill.prelude.TypeExtractor.Arrow` /
    // `NamedTuple`), mirroring rustland's `type_expr_to_term`. Previously both
    // fell through to a `Ref("_")` sentinel, silently discarding the structure.
    case TypeExpr.Arrow(params, ret, effects) =>
      val paramTerms = params.map(typeExprToRef)
      val resultTerm = typeExprToRef(ret)
      // WI-340: the arrow's `effects` field is the canonical
      // `effects_rows(EffectExpression)` row — a right-folded `merge` chain —
      // NOT a prelude cons-list (the pre-WI-340 shape). This matches rustland's
      // post-WI-307/WI-331 loader (`KnowledgeBase::build_canonical_effects_rows`)
      // and the stdlib schema. See `buildCanonicalEffectsRows`.
      val effectTerms = effects.map(typeExprToRef)
      // Source order — params, result, effects — so the arrow reports at the
      // leftmost position it was written at.
      val span = firstLocated(((paramTerms :+ resultTerm) ++ effectTerms).map(terms.spanOf))
      // Single param stays bare; a multi-param list collapses to a
      // positional named-tuple `_0, _1, …`, exactly as rustland does.
      val paramTerm =
        if paramTerms.length == 1 then paramTerms.head
        else namedTupleTypeTerm(paramTerms.zipWithIndex.map((p, i) => (intern(s"_$i"), p)), span)
      val effectsRows = buildCanonicalEffectsRows(effectTerms, span)
      // Named args in canonical (alphabetical) order: effects, param, result.
      terms.allocAt(Term.Fn(intern("anthill.prelude.TypeExtractor.Arrow"), IArray.empty,
        IArray((intern("effects"), effectsRows), (intern("param"), paramTerm),
               (intern("result"), resultTerm))), span)
    case TypeExpr.TupleType(fields) =>
      val fieldTerms = fields.map((n, ty) => (n, typeExprToRef(ty)))
      namedTupleTypeTerm(fieldTerms, firstLocated(fieldTerms.map((_, t) => terms.spanOf(t))))
    // WI-302: a denoted value-in-type rides as the raw literal term (rustland
    // retired the `make_denoted` wrapper in WI-366 — the value rides as a Node).
    case TypeExpr.Denoted(value) => value
    // WI-375: a written effect-row lowers to an opaque `effects_rows(e1, …)`
    // term (rustland builds an EffectExpression; scaland has no effect
    // machinery, so the row rides as a plain functor term — this also subsumes
    // the retired `setType`'s `SetLiteral` lowering for binding-value `{}`).
    case TypeExpr.EffectRow(effects) =>
      val effectTerms = effects.map(typeExprToRef)
      terms.allocAt(Term.Fn(intern("effects_rows"),
        IArray.from(effectTerms), IArray.empty), firstLocated(effectTerms.map(terms.spanOf)))
    // WI-478: a guarded effect `E :- guard` lowers to an opaque
    // `guarded(label, guardList)` term — rustland builds an
    // `EffectExpression.guarded(label, guard: List[reflect.Term])`; scaland has
    // no effect machinery, so the element rides as a plain functor with the
    // guard goals as a prelude cons-list (carrier-faithful round-trip only).
    case TypeExpr.EffectGuarded(label, guard) =>
      val labelTerm = typeExprToRef(label)
      val span = terms.spanOf(labelTerm)
      terms.allocAt(Term.Fn(intern("guarded"),
        IArray(labelTerm, typeListTerm(guard, span)), IArray.empty), span)

  /** Build `anthill.prelude.TypeExtractor.NamedTuple(fields: List[NamedTupleElement])`
    * from ALREADY-LOWERED `(name, type)` field pairs. Shared by tuple types and
    * multi-parameter arrow parameter lists. Mirrors rustland's
    * `make_named_tuple_type`.
    *
    * WI-964: takes the field TYPES as BUILT terms — both callers lower them anyway to
    * derive their own `span`, and the built term answers "where is this field" in O(1). */
  private def namedTupleTypeTerm(fields: IndexedSeq[(TermSymbol, TermId)], span: Span): TermId =
    val fieldTerms = fields.map { (nameSym, typeTerm) =>
      // The label rides at its own field's position where the field has one.
      val fieldSpan = firstLocated(terms.spanOf(typeTerm), span)
      val nameRef = terms.allocAt(Term.Ref(nameSym), fieldSpan)
      terms.allocAt(Term.Fn(intern("anthill.prelude.NamedTupleElement"), IArray.empty,
        IArray((intern("name"), nameRef), (intern("type"), typeTerm))), fieldSpan)
    }
    terms.allocAt(Term.Fn(intern("anthill.prelude.TypeExtractor.NamedTuple"), IArray.empty,
      IArray((intern("fields"), typeListTerm(fieldTerms, span)))), span)

  /** Build a prelude cons-list term (`anthill.prelude.List.cons`/`nil`) from
    * element TermIds, in order. */
  private def typeListTerm(elems: IndexedSeq[TermId], span: Span): TermId =
    val nilTerm = terms.allocAt(
      Term.Fn(intern("anthill.prelude.List.nil"), IArray.empty, IArray.empty), span)
    elems.foldRight(nilTerm)((h, t) =>
      terms.allocAt(Term.Fn(intern("anthill.prelude.List.cons"), IArray(h, t), IArray.empty),
        firstLocated(terms.spanOf(h), span)))

  // ── EffectExpression / EffectsRows builders (WI-340) ──────────────
  // The Scala port of rustland's `make_effect_expression_*` /
  // `make_effects_rows_type` (kb/mod.rs). Fully-qualified functor symbols so
  // the built term is structurally identical to the Rust loader's, sitting
  // naturally alongside the sibling `TypeExtractor.Arrow` / `.NamedTuple`.

  /** `EffectExpression.empty_row` — the closed empty row `{}` (pure). */
  private def effectExpressionEmptyRow(span: Span): TermId =
    terms.allocAt(Term.Fn(intern("anthill.prelude.EffectExpression.empty_row"),
      IArray.empty, IArray.empty), span)

  /** `EffectExpression.present(label: Type)` — a single present effect. */
  private def effectExpressionPresent(label: TermId, span: Span): TermId =
    terms.allocAt(Term.Fn(intern("anthill.prelude.EffectExpression.present"),
      IArray.empty, IArray((intern("label"), label))), firstLocated(terms.spanOf(label), span))

  /** `EffectExpression.open(tail: Type)` — a row-variable tail. */
  private def effectExpressionOpen(tail: TermId, span: Span): TermId =
    terms.allocAt(Term.Fn(intern("anthill.prelude.EffectExpression.open"),
      IArray.empty, IArray((intern("tail"), tail))), firstLocated(terms.spanOf(tail), span))

  /** `EffectExpression.merge(left, right)` — union of two expressions. */
  private def effectExpressionMerge(left: TermId, right: TermId, span: Span): TermId =
    terms.allocAt(Term.Fn(intern("anthill.prelude.EffectExpression.merge"),
      IArray.empty, IArray((intern("left"), left), (intern("right"), right))),
      firstLocated(terms.spanOf(left), span))

  /** Wrap an EffectExpression in the `TypeExtractor.EffectsRows(effects_expr: …)`
    * Type entity — the bridge from EffectExpression to Type position. */
  private def effectsRowsType(expr: TermId, span: Span): TermId =
    terms.allocAt(Term.Fn(intern("anthill.prelude.TypeExtractor.EffectsRows"),
      IArray.empty, IArray((intern("effects_expr"), expr))), span)

  /** Scala port of rustland's `KnowledgeBase::build_canonical_effects_rows`
    * (kb/mod.rs). Builds the canonical `effects_rows(EffectExpression)` Type an
    * arrow's `effects` field carries. Each bare effect label is wrapped in
    * `present(label)`; a bare type-variable effect becomes the row tail
    * `open(tail)`; already-built `present`/`absent`/`guarded` atoms (from the
    * `+E` / `-E` / `E :- g` surface) are kept as-is. Atoms are ordered and
    * de-duplicated by `canonicalAtomKey`, then right-folded into
    * `merge(a1, merge(a2, …, tail))` and wrapped in `EffectsRows`.
    *
    * scaland has no typer, so — unlike rustland's `row_tail_var_of`, which also
    * resolves a `Ref(S.E)` sort-alias tail — only a bare `Term.Var` is treated
    * as a row tail (there is no SortAlias table here). */
  private def buildCanonicalEffectsRows(effects: IndexedSeq[TermId], span: Span): TermId =
    val atoms = ArrayBuffer.empty[TermId]
    val tailVars = ArrayBuffer.empty[TermId]
    effects.foreach { e =>
      terms.get(e) match
        case v: Term.Var =>
          if !tailVars.exists(t => terms.get(t) == v) then tailVars += e
        case fn: Term.Fn if isEffectAtom(fn.functor) =>
          atoms += e   // pre-built present/absent/guarded — keep as-is
        case _ =>
          atoms += effectExpressionPresent(e, span)   // bare label → present(label)
    }
    // Canonical ordering: sort by structural key, then drop true duplicates.
    // The key is fully structural (see `canonicalAtomKey`) so this drops only
    // genuinely-identical atoms — matching rustland's hash-consed-TermId
    // `atoms.dedup()`, NOT collapsing distinct effects that share a base.
    // WI-964, the same principle one function up: `canonicalAtomKey` is a full
    // structural walk, so it is derived ONCE PER ATOM and carried. `sortBy(f)` is
    // `sorted(Ordering.by(f))` — it re-ran the walk per COMPARISON, and the dedup then
    // re-ran it twice more per element.
    // The two steps are INDEPENDENT, and neither implies the other: `distinctBy` is a
    // GLOBAL first-wins dedup over a `HashSet`, so it would drop the same atoms unsorted.
    // `sortBy` is here for CANONICAL ORDER — rustland's `build_canonical_effects_rows`
    // parity, pinned by `ParseTest`'s row-order assertion — and dropping it as "implied
    // by the dedup" would leave every dedup assertion green while the row silently
    // stopped being canonical.
    val deduped = atoms.map(a => (canonicalAtomKey(a), a)).sortBy(_._1).distinctBy(_._1).map(_._2)
    // Seed: innermost tail — `open(?ρ)` when a row var was present, else the
    // closed `empty_row`; any extra tails fold in as `open(…)` merges. Then
    // right-fold `merge(atom, …)` back through the sorted atoms.
    var acc = tailVars.headOption
      .map(effectExpressionOpen(_, span)).getOrElse(effectExpressionEmptyRow(span))
    tailVars.drop(1).foreach(extra =>
      acc = effectExpressionMerge(effectExpressionOpen(extra, span), acc, span))
    deduped.reverseIterator.foreach(atom => acc = effectExpressionMerge(atom, acc, span))
    effectsRowsType(acc, span)

  /** Recognizes an already-built EffectExpression atom in the effects input — a
    * `present`/`absent`/`guarded` produced by the `+E` / `-E` / `E :- g` surface
    * lowering (`effectPresence`/`effectAbsence`/`guardedEffect`, which intern the
    * UNqualified functors). Such an atom is kept as-is rather than re-wrapped in
    * `present`, mirroring rustland. Matched by EXACT functor name — not short
    * name — so a user label like `Foo.present` is not misclassified (rustland
    * likewise matches only the exact EffectExpression constructor symbols). */
  private def isEffectAtom(functor: TermSymbol): Boolean =
    symbols.name(functor) match
      case "present" | "absent" | "guarded" => true
      case _ => false

  /** The last `.`-separated segment of a symbol's name — its short name.
    * (Parse-time symbols are unresolved, so `symbols.name` returns the full
    * interned string; this recovers the short name rustland's `resolve_sym`
    * yields.) */
  private def shortName(sym: TermSymbol): String =
    val n = symbols.name(sym)
    val i = n.lastIndexOf('.')
    if i >= 0 then n.substring(i + 1) else n

  /** Fully-structural canonical key for an effect atom — the row's ORDER and its
    * de-duplication both key on this. Renders the functor short name plus a
    * recursive `[arg, …]` over BOTH positional and named args; a `Ref`/`Ident`
    * renders its short name, a `Var` renders `?name`.
    *
    * Unlike rustland's `type_display_name` (kb/typing.rs), which drops positional
    * args, this keeps them. rustland de-duplicates by hash-consed `TermId`
    * (`atoms.dedup()`), so its sort key may be lossy; scaland's parse-time store
    * is NOT hash-consed and stores a parameterized effect's bindings positionally
    * (`Modify[c]` → `Fn(Modify, pos = [c])`, and the `+E`/`-E`/`E :- g` atoms
    * carry a positional label too), so a lossy key would collapse genuinely-
    * distinct effects — `{Modify[c1], Modify[c2]}`, `{+A, +B}` — into one. A
    * fully-structural key makes the dedup drop only true duplicates, matching
    * rustland's TermId-based dedup. */
  private def canonicalAtomKey(tid: TermId): String =
    terms.get(tid) match
      case Term.Ref(sym)   => shortName(sym)
      case Term.Ident(sym) => shortName(sym)
      case Term.Var(v)     => "?" + shortName(v.varId.name)
      case fn: Term.Fn =>
        val args = fn.posArgs.map(canonicalAtomKey) ++
          fn.namedArgs.map((k, v) => s"${shortName(k)} = ${canonicalAtomKey(v)}")
        if args.isEmpty then shortName(fn.functor)
        else shortName(fn.functor) + "[" + args.mkString(", ") + "]"
      case other => other.toString

  private def refTerm[$: P]: P[TermId] =
    P(keyword("Ref") ~ "(" ~/ name ~ ")").map(n => terms.allocAt(Term.Ref(n.last), n.span))

  private def prefixTerm[$: P]: P[TermId] =
    P(prefixOp ~ atomWithFieldAccess).map { case (op, operand) =>
      val opString = symbols.name(op.sym)
      val entry = Pratt.lookupPrefix(opString)
      val functorSym = entry.map(e => intern(e.functor)).getOrElse(op.sym)
      // WI-618: prefix desugar, as for infix above.
      // WI-957: located at the OPERATOR, as for infix above.
      terms.allocMintedAt(Term.Fn(functorSym, IArray(operand), IArray.empty), op.span)
    }

  private def prefixOp[$: P]: P[OpToken] =
    P(located(
      "!".!.map(_ => intern("!")) |
      keyword("not").map(_ => intern("not")) |
      "-".!.map(_ => intern("-"))
    )).map { case (sym, span) => OpToken(sym, span) }

  // WI-957: `ListLiteral` / `SetLiteral` / `TupleLiteral` / `forall_impl` are names
  // the loader RESOLVES (they are not in `convertExprTerm`'s by-name dispatch, so they
  // reach `resolveName` like a written call), which means each must be located. The
  // span is the OPENING BRACKET — the token that decided which literal this is.
  private def collectionLiteral[$: P]: P[TermId] =
    // Head-tail `[h | t]` removed (WI-560): it was an unused, parse-only
    // surface; list destructuring uses the explicit `cons(?h, ?t)` constructor.
    P(spanOfToken("[") ~/ (
      "]".map(_ => None) |
      (term.rep(1, sep = ",") ~ "]").map(Some(_))
    )).map { case (span, elems) =>
      terms.allocAt(
        Term.Fn(intern("ListLiteral"), IArray.from(elems.getOrElse(Seq.empty)), IArray.empty),
        span)
    }

  private def setLiteral[$: P]: P[TermId] =
    P(spanOfToken("{") ~ term.rep(sep = ",") ~ "}").map { case (span, elems) =>
      terms.allocAt(Term.Fn(intern("SetLiteral"), IArray.from(elems), IArray.empty), span)
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
    // WI-957: the span is the opening `(` — see `collectionLiteral`.
    P(spanOfToken("(") ~/ (
      ")".map(_ => None) |
      (fnArg ~ ("," ~/ fnArg).rep ~ ",".? ~ ("-:" ~/ term.rep(1, sep = ",")).? ~ ")").map(Some(_))
    )).map { case (span, body) =>
      body match
        case None =>
          terms.allocAt(Term.Fn(intern("TupleLiteral"), IArray.empty, IArray.empty), span)
        case Some((first, rest, Some(consequents))) =>
          val antecedents = (first +: rest).collect { case Left(t) => t }
          val antTuple = terms.allocAt(Term.Fn(intern("tuple"),
            IArray.from(antecedents), IArray.empty), span)
          val conTuple = terms.allocAt(Term.Fn(intern("tuple"),
            IArray.from(consequents), IArray.empty), span)
          terms.allocAt(Term.Fn(intern("forall_impl"),
            IArray(antTuple, conTuple), IArray.empty), span)
        case Some((first, rest, None)) =>
          if rest.isEmpty then first match
            case Left(tid) => tid
            case Right((k, v)) =>
              terms.allocAt(Term.Fn(intern("TupleLiteral"), IArray.empty, IArray((k, v))), span)
          else
            val all = first +: rest
            val posArgs = ArrayBuffer.empty[TermId]
            val namedArgs = ArrayBuffer.empty[(TermSymbol, TermId)]
            all.foreach {
              case Left(tid) => posArgs += tid
              case Right((k, v)) => namedArgs += ((k, v))
            }
            terms.allocAt(Term.Fn(intern("TupleLiteral"),
              IArray.from(posArgs), IArray.from(namedArgs)), span)
    }

  /** An infix operator and ITS OWN TOKEN SPAN (WI-957). The span rides with the
    * symbol rather than beside it because the desugar consumes them together:
    * `Pratt.desugar` pairs op `i` with span `i`, and a pairing built by two
    * separately-collected lists is one off-by-one from silently mislocating every
    * diagnostic in the chain. */
  private def infixOp[$: P]: P[OpToken] =
    P(located(
      "!=".!.map(_ => intern("!=")) |
      keyword("or").map(_ => intern("or")) |
      keyword("and").map(_ => intern("and")) |
      keyword("mod").map(_ => intern("mod")) |
      keyword("div").map(_ => intern("div")) |
      Tokens.opToken.map(intern)
    )).map { case (sym, span) => OpToken(sym, span) }

  /** A non-`=` clause-term infix op: every operator in `infixOp` except `=`.
    * `=` is handled separately by `eqClauseOp` (at most one per clause goal), so
    * a second `=` is left for the `= <body>` separator. Derived from `infixOp`
    * so the two operator sets can't drift. (`<=`/`>=`/`!=`/`<=>`/… are distinct
    * maximal-munch tokens, never `=`, so they remain ordinary chaining ops.) */
  private def nonEqInfixOp[$: P]: P[OpToken] =
    P(infixOp.filter(op => symbols.name(op.sym) != "="))

  /** The single clause `=` (equality goal), consumed EXCEPT when it introduces
    * the operation body — i.e. when followed by an expr-body-only keyword
    * (`match`/`if`/`let`/`lambda`/`proof`), which cannot be a `_term` and so can
    * only be the `= <body>` separator. Mirrors rustland's GLR (the infix
    * `Eq[T] = match` parse is impossible, so `= match` is the body). */
  private def eqClauseOp[$: P]: P[OpToken] =
    P((located(Tokens.opToken.filter(_ == "=")) ~ !exprBodyKeyword)
      .map { case (_, span) => OpToken(intern("="), span) })

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
    P(spanOfToken(keyword("proof")) ~/ name ~ (keyword("using") ~/ proofUsingList).? ~
      (keyword("by") ~/ proofStrategy).? ~ (keyword("conclude") ~/ term).? ~
      keyword("end") ~ exprBody).map {
      case (kwSpan, target, _using, _strategy, conclude, body) =>
        val targetStr = terms.alloc(Term.Const(
          Literal.StringLit(target.segments.map(symbols.name).mkString("."))))
        val named = ArrayBuffer((intern("target"), targetStr))
        conclude.foreach(c => named += ((intern("conclude"), c)))
        terms.allocAt(Term.Fn(intern("proof_stmt"), IArray(body), IArray.from(named)), kwSpan)
    }

  private def matchExpr[$: P]: P[TermId] =
    // Mirrors rustland's tree-sitter grammar: `match scrut repeat1(branch)`,
    // no `end`. `matchBranch.rep(1)` self-terminates at the first non-`case`.
    P(spanOfToken(keyword("match")) ~/ term ~ matchBranch.rep(1)).map {
      case (span, scrutinee, branches) =>
        terms.allocAt(
          Term.Fn(intern("match_expr"), IArray(scrutinee) ++ IArray.from(branches), IArray.empty),
          span)
    }

  private def matchBranch[$: P]: P[TermId] =
    P(spanOfToken(keyword("case")) ~/ pattern ~ "->" ~ exprBody).map { case (span, pat, body) =>
      // WI-618: binder-form provenance, as for the accessor builds.
      terms.allocMintedAt(Term.Fn(intern("match_branch"), IArray(pat, body), IArray.empty), span)
    }

  private def ifExpr[$: P]: P[TermId] =
    P(spanOfToken(keyword("if")) ~/ term ~ keyword("then") ~ exprBody ~ keyword("else") ~ exprBody).map {
      case (span, cond, thenB, elseB) =>
        terms.allocAt(Term.Fn(intern("if_expr"), IArray(cond, thenB, elseB), IArray.empty), span)
    }

  /** `let pat [: T] = value [in] body`. The `in` keyword is OPTIONAL:
    * rustland's canonical form is block-style (`let x = value \n body`, no
    * `in` — see grammar `let_chain`); the `in` form is also accepted for
    * back-compat. The optional `: T` annotation (proposal 035 form (1),
    * WI-185) supplies an expected-type hint for the value position. Mirrors
    * rustland: encoded as a `type_name` named-arg child holding the type
    * lowered to a term; positional args stay `(pattern, value, body)`. */
  private def letExpr[$: P]: P[TermId] =
    P(spanOfToken(keyword("let")) ~/ pattern ~ (":" ~ typeExpr).? ~ "=" ~ exprBody ~
      keyword("in").? ~ exprBody).map {
      case (span, pat, tyAnno, value, body) =>
        val named = tyAnno match
          case Some(ty) => IArray((intern("type_name"), typeExprToRef(ty)))
          case None     => IArray.empty[(TermSymbol, TermId)]
        // WI-618: binder-form provenance.
        terms.allocMintedAt(Term.Fn(intern("let_expr"), IArray(pat, value, body), named), span)
    }

  private def lambdaExpr[$: P]: P[TermId] =
    P(spanOfToken(keyword("lambda")) ~/ pattern ~ "->" ~ exprBody).map { case (span, param, body) =>
      // WI-618: binder-form provenance.
      terms.allocMintedAt(Term.Fn(intern("lambda_expr"), IArray(param, body), IArray.empty), span)
    }

  // ── Patterns ─────────────────────────────────────────────────

  private def pattern[$: P]: P[TermId] =
    P(patternConstructor | patternTyped | patternTuple | patternParen | patternLiteral | patternWildcard | patternVar)

  /** WI-620: a parenthesized pattern is pure grouping — `(p)` ≡ `p`. A single
    * parenthesized element is NOT a 1-tuple, so `lambda (x) -> body` binds one
    * variable (the WI-517 tuple/typed forms already parsed `()` / `(a, b)` /
    * `(x: T)`; only the single unannotated `(x)` was a syntax error). Unwraps
    * to the inner pattern, so grouping is transparent in EVERY pattern position
    * (lambda param, match case, let). Tried AFTER `patternTyped` (`(x: T)`) and
    * `patternTuple` (`()` / `(a, b, …)`) so those specific paren forms win —
    * only a single non-typed element reaches here. Mirrors rustland's
    * `pattern_paren` (converter unwraps via the `pattern` field). */
  private def patternParen[$: P]: P[TermId] =
    P("(" ~ pattern ~ ")")

  /** WI-517: a type-annotated binder `name: Type`. Lowers to the SAME
    * `pattern_var` functor as a bare binder but carries the declared type as a
    * `type` named arg (rustland rides it as a `ParseAux::TypeExpr`; scaland
    * lowers the type to a term via `typeExprToRef`). Cut-free so a non-typed
    * tuple element backtracks cleanly. */
  private def typedBinder[$: P]: P[TermId] =
    P(located(ident) ~ ":" ~ typeExpr).map { case (nameSym, span, ty) =>
      val idTerm = terms.allocAt(Term.Ident(nameSym), span)
      terms.allocAt(Term.Fn(intern("pattern_var"), IArray(idTerm),
        IArray((intern("type"), typeExprToRef(ty)))), span)
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
    P(spanOfToken("_")).map { span =>
      terms.allocAt(Term.Fn(intern("pattern_wildcard"), IArray.empty, IArray.empty), span)
    }

  private def patternVar[$: P]: P[TermId] =
    P(located(ident)).map { case (sym, span) =>
      val idTerm = terms.allocAt(Term.Ident(sym), span)
      terms.allocAt(Term.Fn(intern("pattern_var"), IArray(idTerm), IArray.empty), span)
    }

  private def patternLiteral[$: P]: P[TermId] =
    P(located(literal)).map { case (tid, span) =>
      terms.allocAt(Term.Fn(intern("pattern_literal"), IArray(tid), IArray.empty), span)
    }

  private def patternConstructor[$: P]: P[TermId] =
    P(name ~ "(" ~ pattern.rep(sep = ",") ~ ")").map { case (n, pats) =>
      // WI-957: the constructor name is resolved by `loadPatternConstructor`, so it
      // carries the span a `case nosuchctor(…)` diagnostic points at.
      val nameTerm = terms.allocAt(Term.Ident(n.last), n.span)
      terms.allocAt(Term.Fn(intern("pattern_constructor"),
        IArray(nameTerm) ++ IArray.from(pats), IArray.empty), n.span)
    }

  private def patternTuple[$: P]: P[TermId] =
    P(
      (spanOfToken("(") ~ ")").map { span =>
        terms.allocAt(Term.Fn(intern("pattern_tuple"), IArray.empty, IArray.empty), span) } |
      (spanOfToken("(") ~ patternTupleElem ~ "," ~ patternTupleElem.rep(1, sep = ",") ~ ")").map {
        case (span, first, rest) =>
          terms.allocAt(Term.Fn(intern("pattern_tuple"), IArray.from(first +: rest), IArray.empty),
            span)
      }
    )

  // ── Field declarations & params ──────────────────────────────

  private def fieldDecl[$: P]: P[FieldDecl] =
    P(ident ~ ":" ~ typeExpr).map { case (n, t) => FieldDecl(n, t) }

  /** WI-727 (proposal 056): an optional leading `...` marks a VARIADIC CAPTURE
    * parameter — a trailing param collecting every named argument not matched to a
    * declared parameter into one named-tuple record (`fix[R](p: Relation, ...args:
    * R)`, stdlib `prelude/relation.anthill`). "At most one, trailing" is enforced in
    * the loader, not here, matching rustland — the diagnostic quotes the qualified
    * operation name, which only the loader has. */
  private def param[$: P]: P[Param] =
    // WI-947: the span starts at the `...` when there is one — the marker IS what the
    // loader's placement refusal is about, so it is what the diagnostic must point at.
    P(located("...".!.? ~ ident ~ ":" ~ typeExpr)).map {
      case ((rest, n, t), span) => Param(n, t, rest.isDefined, span)
    }

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
    P(located(ident ~ ("." ~ importSegment).rep)).map { case ((first, rest), span) =>
      val allSegments = ArrayBuffer(first)
      var kind: ImportKind = ImportKind.Plain
      for seg <- rest do
        seg match
          case Left(sym) => allSegments += sym
          case Right(ik) => kind = ik
      Import(Name(allSegments.toIndexedSeq, span), kind)
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

  // WI-947: every declaration production brackets itself with [[located]], so its IR
  // node carries the range it was written over instead of the `mkSpan(0, 0)` the whole
  // family used to pass. `located`'s leading `Index` is read before any input is
  // consumed, and a production is always entered at a non-trivia position (the caller's
  // `~` did the skipping), so it lands on the first token — measured for WI-850's
  // refusal across three whitespace shapes.
  //
  // WI-971: `located` and NOT a hand-written `Index ~ … ~~ Index`, which is now a
  // compile error (see [[Index]]) — the trailing `~~` is the whole difference between a
  // span that stops at the construct and one that runs into the next declaration, and
  // it was decided per-site at ~30 productions until WI-970 measured a census of them
  // wrong (stated once, at [[Index]]).
  //
  // A declaration's span begins at its OWN first token — the `visibility` if written,
  // otherwise the keyword — for every shape, WITH NO EXCEPTIONS. The alternative — let
  // the dispatched shapes start at their name — was written first and rejected on
  // review: the same operation then reported a different column depending on whether it
  // was spelled singly or inside a braced block, which is exactly the kind of difference
  // a reader would read as meaning something. `sort`, `rule` and `operation` are the
  // shapes that cost something for it, because a dispatching production consumes their
  // keyword before the branch that builds the node runs: each wraps its dispatcher in
  // `located` and hands the finished span down (`ruleDecl` / `operationDecl` re-stamp
  // the node they were handed, `sortDecl` passes the span to a builder function).
  //
  // `DeclarationSpanTest` pins one span per shape, and is where a new declaration
  // production adds its case. That is deliberate: the spans here reach a user only
  // through whichever diagnostic happens to cite them, so testing them THROUGH
  // diagnostics leaves most of the family unpinned (it did, until review said so).
  private def namespaceDecl[$: P]: P[Item] =
    P(located(keyword("namespace") ~/ name ~ body)).map { case ((n, (imports, items)), span) =>
      Item.NamespaceItem(Namespace(n, imports, items, span))
    }

  /** `sort …` — three shapes, disambiguated by the token after `sort`:
    *   - a plain `name` → `abstract_sort` (`= type`) or `sort_with_body`;
    *   - a `?X` marker or a leading `[` → a type-param binder (WI-454), the two
    *     spellings of one `binderName`.
    * The binder forms (`sort ?X` / `sort [X]`, optionally `{ sort ?T … }`) are
    * per-statement synonyms of a WI-451 enclosing type-param; they desugar to
    * the SAME IR (`desugarSortTypeParam`). The branches return a `(vis, span) => Item`
    * so the `visibility.?` parsed before `sort` is applied once and the WI-947 span can
    * begin at the declaration's own first token, which this production has already
    * consumed by the time a branch runs; the binder forms drop both the visibility and
    * any trailing meta block — a type-param binder carries neither (the desugar has no
    * slot for them), so `public sort ?X [simp]` parses but silently ignores
    * `public`/`[simp]`.
    *
    * WI-971: a `Span` is handed down, not the raw start offset it used to be. The four
    * shapes were the reason this family looked unable to use [[located]] — each branch
    * captured its own trailing `Index` and paired it with an `Int` from the dispatcher.
    * But a branch is the LAST thing in the dispatcher's sequence, so the dispatcher's
    * own trailing capture lands on exactly the offset the branch was reading: one
    * `located` here spans all three, and the branches now bracket nothing at all. */
  private type SortDeclBuilder = (Option[Visibility], Span) => Item

  private def sortDecl[$: P]: P[Item] =
    P(located(visibility.? ~ keyword("sort") ~/ (sortBinderDecl | sortNamedDecl))).map {
      case ((vis, mk), span) => mk(vis, span)
    }

  private def sortNamedDecl[$: P]: P[SortDeclBuilder] =
    P(name ~ (abstractSortRest | sortWithBodyRest)).map { case (n, rest) =>
      (vis, span) => rest match
        case Left((defn, meta)) =>
          Item.AbstractSortItem(AbstractSort(vis, n, defn, IndexedSeq.empty, meta, span))
        case Right((imports, items, meta)) =>
          Item.SortWithBodyItem(SortWithBody(vis, n, IndexedSeq.empty, imports, items, meta, span, SortDeclKind.Sort))
    }

  /** WI-454: the binder NAME, in either spelling — `?X` reuses the logical-var marker,
    * `[X]` brackets a plain identifier. The two are alternatives of ONE production
    * because both positions that accept a binder accept both spellings: the standalone
    * declaration (`sortBinderDecl`) and the structured-body member
    * (`sortBinderMember`). Written out per position, that is the same two-branch
    * grammar four times — and WI-971 is what exposed it, by deleting the per-branch
    * span capture that had been the only difference between two of the four. */
  private def binderName[$: P]: P[(TermSymbol, Span)] =
    P(
      located(Tokens.variableToken).map { case (nm, span) => (intern(nm), span) } |
      ("[" ~/ located(ident) ~ "]")
    )

  /** WI-454: `sort ?X { sort ?T … }` / `sort [X] { … }` as a DECLARATION. Desugars to
    * the SAME IR the enclosing-list form produces. */
  private def sortBinderDecl[$: P]: P[SortDeclBuilder] =
    P(binderName ~ sortBinderBody.? ~ metaBlock.?).map { case (nm, nameSpan, members, _) =>
      (_, span) => desugarSortTypeParam(SortTypeParam(nm, members, nameSpan, span))
    }

  /** A structured binder's brace body — members are themselves type-variable
    * binders ONLY (`sort ?T` / `sort [T]`, possibly nested HK), `repeat1` so an
    * empty `sort [F] {}` is a loud error rather than a degenerate carrier. */
  private def sortBinderBody[$: P]: P[IndexedSeq[SortTypeParam]] =
    P("{" ~/ sortBinderMember.rep(1) ~ "}").map(_.toIndexedSeq)

  private def sortBinderMember[$: P]: P[SortTypeParam] =
    P(located(keyword("sort") ~/ binderName ~ sortBinderBody.?)).map {
      case ((nm, nameSpan, ms), span) => SortTypeParam(nm, ms, nameSpan, span)
    }

  /** `effects E = ?` (or `= X`) at sort-item position (WI-320 / proposal
    * 045). Rustland (`effects_sort_item`) desugars this to the pair
    * `sort E = ? + requires EffectsRuntime[Effects = E]`. scaland keeps the
    * `sort E = ?` half as an `AbstractSort` and OMITS the
    * `requires EffectsRuntime` anchor: that anchor exists solely to give the
    * row variable a kind reachable at typing time, and scaland has no typer,
    * so it would be inert load. The mandatory `=` disambiguates from the
    * operation-clause `effects E` (which never appears at body level). */
  private def effectsSortItem[$: P]: P[Item] =
    P(located(visibility.? ~ keyword("effects") ~ name ~ "=" ~/ typeExpr ~ metaBlock.?)).map {
      case ((vis, n, defn, meta), span) =>
        Item.AbstractSortItem(AbstractSort(vis, n, defn, IndexedSeq.empty, meta, span))
    }

  /** `enum NAME ... end` — same body shape as `sort NAME ... end` but the
    * declaration kind is recorded as `Enum` (proposal 025). */
  private def enumDecl[$: P]: P[Item] =
    P(located(visibility.? ~ keyword("enum") ~/ name ~ body ~ metaBlock.?)).map {
      case ((vis, n, (imports, items), meta), span) =>
        Item.SortWithBodyItem(SortWithBody(vis, n, IndexedSeq.empty, imports, items, meta, span, SortDeclKind.Enum))
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
  // WI-947: BOTH spans ride here, because `desugarSortTypeParam` is a PURE function
  // over this record — it runs after the parse, with no `Index` in reach — and the
  // items it mints are ordinary sort declarations a load error can name. TWO of them
  // and not one: `nameSpan` is the identifier token, `span` the whole binder including
  // any nested member list, and the desugar needs each in its own slot. Stamping the
  // declaration's range onto the `Name` (which is what `lookupScope` reports through)
  // would make a name that spans `?F { sort ?T sort ?U }` — a plausible-looking range
  // that is wrong, which is worse than the `mkSpan(0, 0)` it replaced.
  private case class SortTypeParam(
    name: TermSymbol, members: Option[IndexedSeq[SortTypeParam]], nameSpan: Span, span: Span)

  private def sortTypeParamList[$: P]: P[IndexedSeq[SortTypeParam]] =
    P("[" ~ sortTypeParam.rep(1, sep = ",") ~ "]").map(_.toIndexedSeq)

  private def sortTypeParam[$: P]: P[SortTypeParam] =
    // TWO spans, nested: the inner [[located]] brackets the NAME, the outer one the
    // whole binder including any member list. They start at the same offset — a
    // production is entered at a non-trivia position, and the name is its first token —
    // which is why this used to reconstruct the declaration's start by reading
    // `nameSpan.start` back out. That was the one site in the parser that recovered an
    // offset from a span rather than capturing it, and it depended on [[Span.at]]
    // storing `start` verbatim; WI-971 removed the dependency along with the
    // hand-written bracket.
    P(located(located(ident) ~ sortTypeParamList.?)).map {
      case ((n, nameSpan, members), span) =>
        SortTypeParam(n, members, nameSpan, span)
    }

  /** Desugar one enclosing type-param binder to the SAME IR rustland's
    * `desugar_sort_type_param` produces, so the surface form and the body form
    * cannot drift: a SIMPLE param `A` → `sort A = ?` (an `AbstractSort` with a
    * fresh anonymous `?` — picked up by the loader's `sort T = ?` type-param arm);
    * a HIGHER-KINDED param `F[T]` → a `SortWithBody` MARKED `isTypeParam` whose
    * body holds the recursively-desugared members (the loader mints F as a type
    * param of the enclosing sort). No `= default` form (sort-param defaults are
    * undefined by §5.4). */
  private def desugarSortTypeParam(p: SortTypeParam): Item =
    // `nameSpan` for the NAME and `span` for the declaration — every other `Name` in
    // this parser spans exactly its identifier token, and this one must too.
    val nm = Name.simple(p.name, p.nameSpan)
    p.members match
      case Some(members) =>
        Item.SortWithBodyItem(SortWithBody(
          None, nm, IndexedSeq.empty, IndexedSeq.empty,
          members.map(desugarSortTypeParam), None, p.span,
          SortDeclKind.Sort, isTypeParam = true))
      case None =>
        Item.AbstractSortItem(AbstractSort(None, nm, freshAnonTypeVar(), IndexedSeq.empty, None, p.span))

  // Same shape as `operationDecl`: the dispatcher consumed the `rule` keyword, so it
  // is the one that can span from it (WI-947).
  private def ruleDecl[$: P]: P[Item] =
    P(located(keyword("rule") ~/ (
      bracedRuleBlock.map(Left(_)) |
      ruleEntry.map(Right(_))
    ))).map {
      case (Right(rule), span) => Item.RuleItem(rule.copy(span = span))
      case (Left(entries), span) => Item.RuleBlockItem(RuleBlock(entries, span))
    }

  private def bracedRuleBlock[$: P]: P[IndexedSeq[Rule]] =
    P("{" ~/ ruleEntry.rep ~ "}").map(_.toIndexedSeq)

  /** One rule, spanning its own text — WITHOUT closing the variable scope, because a
    * rule is not always the whole construct its `?x`s belong to: a `proofStep` carries
    * the same scope on into its `using …/by …` tail. The two callers each say where
    * their scope ends by calling `resetVarScope` themselves. */
  private def ruleWithSpan[$: P]: P[Rule] =
    P(located((simpleName ~ ":").? ~ ruleArrowChoice ~ metaBlock.?)).map {
      case ((label, (heads, body), meta), span) => Rule(label, heads, body, meta, span)
    }

  private def ruleEntry[$: P]: P[Rule] =
    P(ruleWithSpan).map { rule => resetVarScope(); rule }

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
      // WI-970: `flatMapX`, not `flatMap`. fastparse's `flatMap` runs the whitespace
      // skipper between the first parser and the continuation — and the continuation
      // for a rule that HAS a `:-` body is `Pass`, which consumes nothing, so the parse
      // index was left sitting past the rule's own text. `ruleEntry` and `ruleDecl`
      // both take their `located` end from there, so every `:-` rule's declaration span
      // ran to the start of whatever followed it. `flatMapX` is the no-whitespace twin;
      // the `-:` branch below, which genuinely needs the trivia skipped, asks for it.
      (ruleHeads ~ (":-" ~/ goalTerm.rep(1, sep = ",")).?).flatMapX { case (hs, body) =>
        body match
          case Some(_) =>
            Pass.map(_ => (hs, body.map(_.toIndexedSeq)))
          case None =>
            // `Pass ~` is the request: `~` skips trivia before its RIGHT operand, so
            // this is how the reversed form still matches `heads\n  -: body` (the
            // spelling stdlib `prelude/int64.anthill` uses).
            (Pass ~ "-:" ~/ ruleHeads).?.map {
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
    // Visibility precedes the `operation` keyword — `internal operation foo`
    // (WI-369), mirroring rustland's `operation_declaration` (`visibility?
    // 'operation' …`) and the other decls (`sort`/`const`/`enum`), which all
    // take `visibility.? ~ keyword(...)`. Thread the leading visibility onto a
    // single operation (a braced block takes none). `singleOperation` still
    // tolerates a post-`operation` visibility as a no-op fallback, so `orElse`
    // keeps whichever is present.
    // WI-947: the two shapes come back UNWRAPPED (an `Either`, not a built `Item`), so
    // this production — the one that knows where the declaration started — builds each
    // node's span itself. Wrapping first and re-stamping afterwards needs a match over
    // all of `Item` for two reachable shapes, whose third arm could only be a silent
    // pass-through.
    // WI-970: the visibility is [[located]] for the refusal below — it was reported at
    // `mkSpan(s, s)`, the declaration's start, which is the right column (the modifier
    // IS the first token when present) but zero characters wide. The modifier is what
    // the message is about, so it is what the span brackets.
    P(located(located(visibility).? ~ keyword("operation") ~/ (
      bracedOperationBlock.map(Left(_)) |
      operationEntry.map(Right(_))
    ))).map {
      case ((vis, Right(op)), span) =>
        Item.OperationItem(op.copy(visibility = op.visibility.orElse(vis.map(_._1)), span = span))
      case ((vis, Left(entries)), span) =>
        // A leading visibility on a braced `operation { … }` block has no meaning
        // (rustland has no such form — visibility is per-entry). Reject it loudly
        // rather than silently dropping it (CLAUDE.md: loud error over silent skip).
        for (_, visSpan) <- vis do
          errors += ParseError(
            "a visibility modifier cannot precede a braced `operation { … }` block; " +
            "put the visibility on each entry", visSpan)
        Item.OperationBlockItem(OperationBlock(entries, span))
    }

  private def bracedOperationBlock[$: P]: P[IndexedSeq[Operation]] =
    P("{" ~/ operationEntry.rep ~ "}").map(_.toIndexedSeq)

  /** One operation, spanning its OWN text — which inside a braced block starts at the
    * entry's `visibility.?`, and for the single spelling is re-stamped by
    * `operationDecl` to start at the `operation` keyword it consumed. The two differ
    * by exactly the text the two surface forms differ by. */
  private def operationEntry[$: P]: P[Operation] =
    P(located(visibility.? ~ simpleName ~ operationTypeParamList.? ~ "(" ~ param.rep(sep = ",") ~ ")" ~ "->" ~ typeExpr ~
      operationClauses ~ ("=" ~/ exprBody).? ~ metaBlock.?
    )).map { case ((vis, n, tps, params, retType, clauses, opBody, trailingMeta), span) =>
      Operation(vis, n,
        refuseTypeParamDefaults(n, tps.getOrElse(IndexedSeq.empty)) ++ clauses.slotBinders,
        params.toIndexedSeq, retType, clauses.requires, clauses.ensures, clauses.effects,
        opBody, combineMeta(clauses.meta, trailingMeta), span)
    }

  /** Operation type-parameter list `[T, U = Int]` (WI-269). A distinct
    * production from `sortBinding`/instantiation even though the tokens
    * coincide: this declares operation-local logical variables, not
    * bindings of sort parameters at an instantiation site. Mirrors
    * rustland's `operation_type_param_list`. */
  private def operationTypeParamList[$: P]: P[IndexedSeq[WrittenTypeParam]] =
    P("[" ~ operationTypeParam.rep(1, sep = ",") ~ "]").map(_.toIndexedSeq)

  /** A type parameter plus the DEFAULT as written, if any. The default is carried
    * only as far as `refuseTypeParamDefaults`, which reports it and drops it —
    * `TypeParam` has no field to store it in (WI-850). */
  private case class WrittenTypeParam(param: TypeParam, writtenDefault: Option[TypeExpr])

  private def operationTypeParam[$: P]: P[WrittenTypeParam] =
    // The default is carried as the parsed `TypeExpr`, NOT as a `.!` source capture:
    // the refusal quotes it back to the author, and a capture spans whatever trivia
    // was written inside the type — a comment, a line break, or (because an anthill
    // identifier may contain `-`) a `my--type` whose `--` reads as a line comment to
    // anything that re-lexes the slice. `renderTypeExpr` reads the tree instead, so
    // there is nothing to re-lex (WI-950).
    // WI-970: this was `mkSpan(idx, idx)` — a zero-WIDTH span at the parameter's first
    // character, so the WI-850 refusal below pointed at a position with nothing to
    // underline. [[located]] spans the identifier TOKEN, which is what the refusal is
    // about. The START is unchanged (both capture `Index` before the ident), so the
    // refusal renders at the same `line:col` as before — only the end moved.
    P(located(ident) ~ ("=" ~/ typeExpr).?).map { case (n, span, default) =>
      WrittenTypeParam(TypeParam(n, span), default)
    }

  /** WI-850: a declared type-param DEFAULT (`operation foo[T = Int64](…)`) is
    * REFUSED. The production above parses it so the refusal can name the operation
    * and the parameter, instead of failing as an unexpected `=` pointing at a token.
    *
    * It has no semantics anywhere: the loader mints a fresh var per parameter from
    * its NAME alone, so `[T = Int64]` loaded EXACTLY as `[T]` and the default was
    * dropped in silence. The kernel spec's production is `TypeParam ::= Name` (§5.4).
    * Refused HERE rather than in the loader because the verdict is decidable from the
    * surface form alone, and this is the one point both declaration spellings
    * (`singleOperation` and a braced block's `operationEntry`) reach — mirroring
    * rustland, which refuses in the converter for the same reason. */
  private def refuseTypeParamDefaults(op: Name, tps: IndexedSeq[WrittenTypeParam]): IndexedSeq[TypeParam] =
    for wtp <- tps; writtenType <- wtp.writtenDefault do
      val opName = op.segments.map(symbols.name).mkString(".")
      val pName = symbols.name(wtp.param.name)
      val written = renderTypeExpr(writtenType)
      errors += ParseError(
        s"operation `$opName`: type parameter `$pName` carries a default " +
        s"(`$pName = $written`), which nothing reads — the declaration means exactly " +
        s"`$pName`, and the default would be dropped in silence. Declare it bare and " +
        s"let the call bind it, either from the arguments or explicitly " +
        s"(`$opName[$pName = $written](…)`)", wtp.param.span)
    tps.map(_.param)

  /** Render a parsed `TypeExpr` back as anthill surface syntax, for the refusal
    * above — the ONE diagnostic that has to show the author a type they wrote.
    *
    * Rendering the TREE rather than normalising a `.!` source capture is what keeps
    * this honest (WI-950): a capture spans the trivia written inside the type, and
    * anything that strips that trivia has to re-lex the slice — which needs the whole
    * token model, not just the comment forms (an anthill identifier may contain `-`,
    * so `my--type` is ONE token whose `--` is not a line comment). These matches are
    * exhaustive over sealed types, so a new `TypeExpr` / `Term` / `Literal` case is a
    * COMPILE error here rather than a silently mis-rendered diagnostic.
    *
    * The spelling is canonical, not verbatim: interior trivia is gone (the point),
    * and a term written infix inside an effect guard renders as the functor call it
    * desugared to. Both are what the author's declaration MEANS, which is what the
    * message is about. */
  private def renderTypeExpr(te: TypeExpr): String = te match
    case TypeExpr.Simple(n)              => renderName(n)
    case TypeExpr.Parameterized(n, bs)   => s"${renderName(n)}[${bs.map(renderSortBinding).mkString(", ")}]"
    // The `descriptions` a `{< … >}` doc block attaches are trivia by nature — the
    // very thing this rendering exists to leave out.
    case TypeExpr.Variable(tid, _)       => renderTerm(tid)
    case TypeExpr.TupleType(fields)      =>
      // `tupleTypeArg` labels an unnamed component `_`; render those bare.
      s"(${fields.map((n, t) =>
        if symbols.name(n) == "_" then renderTypeExpr(t)
        else s"${symbols.name(n)}: ${renderTypeExpr(t)}").mkString(", ")})"
    case TypeExpr.Arrow(ps, ret, effs)   =>
      val base = s"(${ps.map(renderTypeExpr).mkString(", ")}) -> ${renderTypeExpr(ret)}"
      if effs.isEmpty then base else s"$base @ {${effs.map(renderTypeExpr).mkString(", ")}}"
    case TypeExpr.Denoted(v)             => renderTerm(v)
    case TypeExpr.EffectRow(effs)        => s"{${effs.map(renderTypeExpr).mkString(", ")}}"
    case TypeExpr.EffectGuarded(l, g)    =>
      s"${renderTypeExpr(l)} :- ${g.map(renderTerm).mkString(", ")}"

  private def renderName(n: Name): String = n.segments.map(symbols.name).mkString(".")

  private def renderSortBinding(b: SortBinding): String = b.param match
    case Some(p) => s"${renderName(p)} = ${renderTypeExpr(b.bound)}"
    case None    => renderTypeExpr(b.bound)

  /** Render a parse-time term as surface syntax. Reached from `renderTypeExpr` only,
    * for a value-in-type (`Vector[Int64, 3]`) or an effect guard's goals. */
  private def renderTerm(tid: TermId): String = terms.get(tid) match
    case Term.Const(lit)  => renderLiteral(lit)
    case Term.Var(v)      => v match
      // The parser only ever builds `Global`; `DeBruijn` is the loader's canonical
      // form for a STORED rule and `Rigid` is resolution's, so neither can reach here.
      case Var.Global(id)   => s"?${symbols.name(id.name)}"
      case Var.Rigid(id)    => s"?${symbols.name(id.name)}"
      case Var.DeBruijn(i)  => s"?_$i"
    case Term.Bottom      => "⊥"
    case Term.Ref(s)      => symbols.name(s)
    case Term.Ident(s)    => symbols.name(s)
    case fn: Term.Fn      =>
      val pos = fn.posArgs.map(renderTerm)
      val named = fn.namedArgs.map((k, v) => s"${symbols.name(k)}: ${renderTerm(v)}")
      s"${symbols.name(fn.functor)}(${(pos ++ named).mkString(", ")})"

  private def renderLiteral(lit: Literal): String = lit match
    // Re-encode the escapes `Tokens.decodeStringEscapes` decoded, so the quoted
    // default is anthill source the author could paste back.
    case Literal.StringLit(s) =>
      val out = new StringBuilder(s.length + 2)
      out += '"'
      s.foreach {
        case '"'  => out ++= "\\\""
        case '\\' => out ++= "\\\\"
        case '\n' => out ++= "\\n"
        case '\r' => out ++= "\\r"
        case '\t' => out ++= "\\t"
        case c    => out += c
      }
      out += '"'
      out.toString
    case Literal.IntLit(v)    => v.toString
    case Literal.BigIntLit(v) => v.toString
    case Literal.FloatLit(v)  => v.value.toString
    case Literal.BoolLit(v)   => v.toString

  /** The accumulated operation clauses. `slotBinders` (WI-840) are the NAMED
    * requirement slots found in the `requires` lists — each becomes an operation type
    * parameter, appended to the ones written in the `[…]` bracket. */
  private case class OperationClauses(
    requires: IndexedSeq[IndexedSeq[TermId]],
    ensures: IndexedSeq[IndexedSeq[TermId]],
    effects: IndexedSeq[Effect],
    meta: IndexedSeq[MetaEntry],
    slotBinders: IndexedSeq[TypeParam]
  )

  private def operationClauses[$: P]: P[OperationClauses] =
    P(operationClause.rep).map { clauses =>
      val reqs = ArrayBuffer.empty[IndexedSeq[TermId]]
      val enss = ArrayBuffer.empty[IndexedSeq[TermId]]
      val effs = ArrayBuffer.empty[Effect]
      val metas = ArrayBuffer.empty[MetaEntry]
      val binders = ArrayBuffer.empty[TypeParam]
      clauses.foreach {
        // WI-840: `slotBase` is the number of requirement goals earlier clauses
        // already contributed, so a binder's recorded position indexes the
        // operation's WHOLE requirement list rather than one clause of it (an
        // operation may carry several `requires` clauses; they accumulate here
        // rather than last-wins).
        case (0, items: IndexedSeq[RequiresItem] @unchecked) =>
          val slotBase = reqs.map(_.length).sum
          reqs += items.map(_.goal)
          items.zipWithIndex.foreach {
            case (RequiresItem(_, Some((binder, binderSpan))), i) =>
              binders += TypeParam(binder, binderSpan, Some(slotBase + i))
            case _ => ()
          }
        case (1, terms: IndexedSeq[TermId] @unchecked) => enss += terms
        case (2, effects: IndexedSeq[Effect] @unchecked) => effs ++= effects
        // WI-087: `meta [...]` clause entries accumulate (matching effects/
        // requires/ensures — no silent last-wins drop), merged with a trailing
        // bare meta_block by `combineMeta`.
        case (3, entries: IndexedSeq[MetaEntry] @unchecked) => metas ++= entries
        case _ =>
      }
      OperationClauses(reqs.toIndexedSeq, enss.toIndexedSeq, effs.toIndexedSeq,
        metas.toIndexedSeq, binders.toIndexedSeq)
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
      (keyword("requires") ~/ requiresItem.rep(1, sep = ",")).map(ts => (0, ts.toIndexedSeq)) |
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
    P(located(visibility.? ~ keyword("const") ~/ name ~ ":" ~ typeExpr ~ ("=" ~/ exprBody).? ~ metaBlock.?)).map {
      case ((vis, n, ty, value, meta), span) =>
        Item.ConstItem(Const(vis, n, ty, value, meta, span))
    }

  /** `requires [<name> :] <type>` at sort / namespace level.
    *
    * WI-840 (proposal 058 §4.7): the optional binder names the requirement SLOT,
    * making it a type parameter of the enclosing sort. `ident ~ ":"` is tried first
    * and backtracks cleanly on the anonymous form, whose `<type>` may itself begin
    * with a (dotted) name — the two are decided on the `:` lookahead, which is also
    * how rustland's grammar decides them. The binder is a single `ident`, not a
    * `name`: it DECLARES a parameter rather than referencing one, so a dotted
    * spelling would have no meaning. */
  private def requiresDeclItem[$: P]: P[Item] =
    P(located(keyword("requires") ~/ (located(ident) ~ ":").? ~ typeExpr)).map {
      case ((binder, te), span) =>
        val binderName = binder.map { case (b, bSpan) => Name(IndexedSeq(b), bSpan) }
        Item.RequiresDeclItem(RequiresDecl(binderName, te, span))
    }

  private def entityDecl[$: P]: P[Item] =
    // `name` (not `simpleName`): rustland allows a qualified entity name
    // (`entity anthill.prelude.TypeBinding(...)`, stdlib sort.anthill).
    P(located(visibility.? ~ keyword("entity") ~/ name ~ ("(" ~ fieldDecl.rep(1, sep = ",") ~ ")").? ~ metaBlock.?)
    ).map { case ((vis, n, fields, meta), span) =>
      Item.EntityItem(Entity(vis, n, fields.map(_.toIndexedSeq).getOrElse(IndexedSeq.empty), meta, span))
    }

  private def factDeclInner[$: P]: P[Fact] =
    P(located(keyword("fact") ~/ term ~ metaBlock.?)).map { case ((t, meta), span) =>
      Fact(t, meta, span)
    }

  private def factDecl[$: P]: P[Item] = P(factDeclInner).map(Item.FactItem(_))

  private def constraintDecl[$: P]: P[Item] =
    P(located(keyword("constraint") ~/ (simpleName ~ ":").? ~ term.rep(1, sep = ",") ~
      (":-" ~/ term.rep(1, sep = ",")).? ~ metaBlock.?)
    ).map { case ((label, head, guard, meta), span) =>
      resetVarScope()
      Item.ConstraintItem(Constraint(label, head.toIndexedSeq, guard.map(_.toIndexedSeq), meta, span))
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
    // WI-961: the marker stands for the `key: value` pair, so it rides at the value's
    // position — the key is a bare `TermSymbol` here and carries none of its own.
    terms.allocAt(Term.Fn(namedArgFunctorSym, IArray.empty,
      IArray((namedArgNameSym, keyStr), (namedArgValueSym, v))), terms.spanOf(v))

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
    P(located(keyword("proof") ~/ name ~ proofBodyForm ~ keyword("end"))).map {
      case ((target, (using0, strategy, body)), span) =>
        resetVarScope()
        ProofDecl(target, strategy, body, using0, span)
    }

  private def proofDecl[$: P]: P[Item] = P(proofDeclInner).map(Item.ProofItem(_))

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
    P(located(ident ~ ("(" ~/ fnArg.rep(1, sep = ",") ~ ")").?)).map {
      case ((n, args), span) =>
        val rawArgs: IndexedSeq[TermId] = args.getOrElse(Seq.empty).toIndexedSeq.map {
          case Left(tid) => tid
          case Right((k, v)) => allocNamedArg(k, v)
        }
        ProofStrategy(n, rawArgs, span)
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
    // The step's rule spans only its rule text; the STEP spans that plus its
    // `using …/by …` tail, so a diagnostic about either points at the right half.
    // TWO ends off one start, which is why this reads as [[located]] NESTED inside
    // [[located]] rather than one bracket with a second `Index` in the middle: the
    // inner one — [[ruleWithSpan]], the same production `ruleEntry` wraps — closes on
    // the rule, the outer one on the step, and both open at the same offset because no
    // input is consumed before the inner one (WI-971).
    P(located(ruleWithSpan ~ (keyword("using") ~/ proofUsingList).? ~
      keyword("by") ~/ proofStrategy))
      .map { case ((rule, using0, strat), stepSpan) =>
        resetVarScope()
        ProofStep(rule, using0.getOrElse(IndexedSeq.empty), strat, stepSpan)
      }

  /** `rule <step>` — strips the `rule` keyword before delegating to
    * `proofStep` so the structured-form parser composes cleanly with
    * `rep(1)`. */
  private def proofStepEntry[$: P]: P[ProofStep] =
    P(keyword("rule") ~/ proofStep)

  private def proofConcludingClause[$: P]: P[ConcludeClause] =
    P(located((keyword("using") ~/ proofUsingList).? ~ keyword("by") ~/ proofStrategy)).map {
      case ((using0, strat), span) =>
        ConcludeClause(using0.getOrElse(IndexedSeq.empty), strat, span)
    }

  /** `provides Spec` (clause) or `provides Spec language X ... end` (block).
    * Disambiguated by checking for the `language` keyword after the spec. */
  private def providesDecl[$: P]: P[Item] =
    P(located(keyword("provides") ~/ typeExpr ~ providesRest)).map {
      case ((spec, Left(())), span) =>
        Item.ProvidesClauseItem(ProvidesClause(spec, span))
      case ((spec, Right((lang, items))), span) =>
        Item.ProvidesBlockItem(ProvidesBlock(spec, lang, items, span))
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
      providesOperationMap |
      providesConstMap |
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

  /** WI-876: `operation_map { compare: "ordered_compare" }` — the operation-level
    * peer of `carrier`. Mirrors rustland's `operation_map_clause`.
    */
  private def providesOperationMap[$: P]: P[ProvidesItem] =
    P(keyword("operation_map") ~/ providesBindings).map { bs =>
      ProvidesItem.OperationMapI(bs.map { case (k, v) => OperationMapEntry(k, v) })
    }

  /** WI-889: `const_map { infinity: "f64::INFINITY" }` — the const-level peer of
    * `operation_map`. Mirrors rustland's `const_map_clause`.
    */
  private def providesConstMap[$: P]: P[ProvidesItem] =
    P(keyword("const_map") ~/ providesBindings).map { bs =>
      ProvidesItem.ConstMapI(bs.map { case (k, v) => ConstMapEntry(k, v) })
    }

  private def providesBindings[$: P]: P[IndexedSeq[(TermSymbol, TermId)]] =
    P("{" ~/ providesBinding.rep(1, sep = ",") ~ ",".? ~ "}").map(_.toIndexedSeq)

  private def providesBinding[$: P]: P[(TermSymbol, TermId)] =
    P(ident ~ ":" ~/ term)

  private def providesProof[$: P]: P[ProvidesItem] =
    P(proofDeclInner).map(ProvidesItem.ProofI(_))

  /** Inside a `provides` block, `rule { ... }` desugars to a block-of-
    * rules and a bare `rule h :- b` to a single rule — `ruleDecl`
    * already returns the `Item.RuleItem` / `Item.RuleBlockItem` union,
    * so the partial match here mirrors that existing union. */
  private def providesRule[$: P]: P[ProvidesItem] =
    P(ruleDecl).map {
      case Item.RuleItem(r) => ProvidesItem.RuleI(r)
      case Item.RuleBlockItem(rb) => ProvidesItem.RuleBlockI(rb)
      case other => sys.error(s"ruleDecl returned unexpected $other")
    }

  private def providesFact[$: P]: P[ProvidesItem] =
    P(factDeclInner).map(ProvidesItem.FactI(_))

  // ── Declaration dispatch ─────────────────────────────────────

  private def declaration[$: P]: P[Item] =
    P(
      // WI-853: a file's top level admits an `import`, as a namespace / sort body
      // already did — the top level IS a scope (`_global`), and an import is how
      // names enter one. First in the choice because `import` is its own keyword,
      // shared with no other declaration.
      importClause.map(Item.ImportItem(_)) |
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

  /** The one production that deliberately does NOT scope refusals — note the
    * explicit `fastparse.P`, not this class's shadowing one.
    *
    * Its scope would be the whole file, so a syntax error anywhere (`End` failing on
    * trailing garbage, say) would drop every refusal in the buffer — including ones
    * recorded by declarations `declaration.rep` had ACCEPTED. Those refusals are
    * live: that declaration parsed, and the author should see it in the same run as
    * the syntax error rather than discovering it only after fixing the typo. A
    * declaration that fails still drops its own, one level down (WI-950). */
  def sourceFile[$: P]: P[Seq[Item]] =
    fastparse.P(Start ~ declaration.rep ~ End)

end AnthillParserImpl

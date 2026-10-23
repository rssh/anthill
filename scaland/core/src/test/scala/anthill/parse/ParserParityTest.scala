package anthill.parse

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters.*

/** WI-777 — Scaland's half of the shared Rust/Scala parser corpus.
  *
  * The Rust test `wi777_parser_parity_corpus_test.rs` consumes the exact same root.
  * Expected verdicts come from the `accept` / `reject` directory, so neither test can
  * quietly edit a private expectation table to bless a divergence.
  */
class ParserParityTest extends munit.FunSuite:

  private val corpusRoot: Path =
    sys.env.get("ANTHILL_PARSER_PARITY_CORPUS")
      .map(Paths.get(_))
      .getOrElse(Paths.get(System.getProperty("user.dir"), "..", "testdata",
        "parser-parity", "wi777"))
      .toAbsolutePath.normalize

  private def cases(verdict: String): IndexedSeq[Path] =
    val dir = corpusRoot.resolve(verdict)
    val stream = Files.list(dir)
    val paths = try
      stream.iterator.asScala
        .filter(path => path.getFileName.toString.endsWith(".anthill"))
        .toIndexedSeq.sortBy(_.getFileName.toString)
    finally stream.close()
    assert(paths.nonEmpty, s"$verdict parity corpus must not be empty: $dir")
    paths

  private def parsePath(path: Path): Either[IndexedSeq[ParseError], ParsedFile] =
    Parser.parse(Files.readString(path, StandardCharsets.UTF_8), path.toString)

  test("WI-777: Scaland agrees with Rust's shared parser corpus") {
    for path <- cases("accept") do
      parsePath(path) match
        case Right(_) => ()
        case Left(errors) =>
          fail(s"Scaland rejected shared accept case $path: ${errors.map(_.message).mkString("; ")}")

    for path <- cases("reject") do
      assert(parsePath(path).isLeft, s"Scaland accepted shared reject case $path")

    // BACK-OUT: restoring tupleType's `.rep(1)` makes this test fail on both
    // one-component tuple files. The arrow, two-component tuple, and negative cases
    // pass either way by design; they are the controls around the changed capability.
  }
  test("WI-777: shared one-component forms keep their distinct IR shapes") {
    val named = parsePath(corpusRoot.resolve("accept/one_named_tuple_type.anthill"))
      .toOption.getOrElse(fail("named one-component parity case did not parse"))
    named.items.collectFirst { case Item.NamespaceItem(ns) => ns }.get
      .items.collectFirst { case Item.OperationItem(op) => op.returnType }.get match
      case TypeExpr.TupleType(IndexedSeq((label, TypeExpr.Simple(component)))) =>
        assertEquals(named.symbols.name(label), "a")
        assertEquals(named.symbols.name(component.last), "A")
      case other => fail(s"`(a: A)` must remain a one-field TupleType, got $other")

    val arrow = parsePath(corpusRoot.resolve("accept/one_positional_arrow.anthill"))
      .toOption.getOrElse(fail("one-parameter arrow parity case did not parse"))
    val arrowType = arrow.items.collectFirst { case Item.NamespaceItem(ns) => ns }.get
      .items.collectFirst { case Item.OperationItem(op) => op.params.head.ty }.get
    arrowType match
      case TypeExpr.Arrow(IndexedSeq(TypeExpr.Simple(param)), TypeExpr.Simple(result), _) =>
        assertEquals(arrow.symbols.name(param.last), "A")
        assertEquals(arrow.symbols.name(result.last), "B")
      case other => fail(s"`(A) -> B` must remain a one-parameter Arrow, got $other")

    val bareErrors = parsePath(corpusRoot.resolve("reject/bare_parenthesized_type.anthill"))
      .left.getOrElse(fail("bare `(A)` unexpectedly parsed"))
    assert(bareErrors.exists(_.message.contains("single parenthesized type is not a type")),
      s"bare `(A)` must fail for the type-reading reason, got: ${bareErrors.map(_.message)}")
  }

  /** A lambda after an infix operator is the lambda (kernel-language §4.8), the same
    * term its parenthesized spelling builds; its body is the rest of the chain; and
    * after a `requires` clause `=` still opens the body. BACK-OUT: `term`'s operand
    * back at `atomWithFieldAccess` fails the accept case (`lambda ()` is a call there
    * and `lambda x` no term at all); measured 2026-10-23. */
  test("a lambda after an infix operator is the lambda, bare as parenthesized") {
    val file = parsePath(corpusRoot.resolve("accept/lambda_as_infix_operand.anthill"))
      .toOption.getOrElse(fail("the lambda-operand parity case did not parse"))
    val items = file.items.collectFirst { case Item.NamespaceItem(ns) => ns }.get.items
    def render(tid: anthill.term.TermId): String = file.terms.get(tid) match
      case anthill.term.Term.Const(lit) => Parser.renderLiteral(lit)
      case anthill.term.Term.Var(anthill.term.Var.Global(id)) => s"?${file.symbols.name(id.name)}"
      case anthill.term.Term.Var(v) => v.toString
      case anthill.term.Term.Bottom => "⊥"
      case anthill.term.Term.Ref(s) => file.symbols.name(s)
      case anthill.term.Term.Ident(s) => file.symbols.name(s)
      case fn: anthill.term.Term.Fn =>
        val args = fn.posArgs.map(render) ++
          fn.namedArgs.map((k, v) => s"${file.symbols.name(k)}: ${render(v)}")
        s"${file.symbols.name(fn.functor)}(${args.mkString(", ")})"
    def body(name: String): IndexedSeq[String] =
      items.collectFirst {
        case Item.RuleItem(rule) if rule.heads.exists {
          case RuleHead.TermHead(h) => render(h).startsWith(s"$name(")
          case RuleHead.Bottom => false
        } => rule.body.get.map(render)
      }.getOrElse(fail(s"no rule `$name`"))

    assertEquals(body("bare"), body("paren"))
    assert(body("bare").head.contains("lambda_expr("), s"a lambda: ${body("bare")}")
    assert(body("binder").head.matches(""".*lambda_expr\(.*add\(x, 1\)\)\)"""),
      s"the body is the rest of the chain: ${body("binder")}")
    val op = items.collectFirst { case Item.OperationItem(o) if file.symbols.name(o.name.last) == "body" => o }.get
    assert(op.body.exists(b => render(b).contains("lambda_expr(")), s"the body is the lambda: $op")
  }


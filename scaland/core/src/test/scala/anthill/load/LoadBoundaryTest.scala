package anthill.load

import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.resolve.SearchStream

/** S723J controls: refusal rows fail without the boundary checks; the accepted
  * controls pass either way. Resolve an actual later clause to drive multi-load KBs. */
class LoadBoundaryTest extends munit.FunSuite:
  private def parsed(s: String) = LoadFixture.parsed(s, "boundary.anthill")
  private val base = """
namespace demo
  sort Point
    entity point
  end
  sort Handle
  end
end
"""
  private val specs = """
namespace anthill.prelude
  sort PartialEq
    sort T = ?
  end
  sort Eq
    sort T = ?
  end
  sort NonEq
    sort T = ?
  end
end
"""
  private def fresh(): KnowledgeBase =
    val kb = KnowledgeBase()
    Prelude.register(kb)
    kb
  private def load(kb: KnowledgeBase, s: String) = Loader.loadAll(kb, IndexedSeq(parsed(s)))
  private def initial(): KnowledgeBase =
    val kb = fresh()
    assert(load(kb, specs + base).isEmpty)
    kb
  private def witness(carrier: String, condition: String = "") = s"""
namespace demo
  import anthill.prelude.{PartialEq, Eq}
  sort Witness
    provides PartialEq[T = $carrier] $condition
  end
end
"""

  test("later witness equality is refused; same-load witness is accepted") {
    val kb = initial()
    val errs = load(kb, witness("Point"))
    assert(errs.exists(_.render.contains("the equality of 'demo.Point' is closed")), errs.toString)
    val together = fresh()
    assert(load(together, specs + base + witness("Point")).isEmpty)
    assert(load(kb, "namespace unrelated\n entity untouched\nend").exists(_.render.contains("is closed")))
  }

  test("own member eq in a secondary entry is refused") {
    val kb = initial()
    val errs = load(kb, "namespace demo.Point\n operation eq(a: Point, b: Point) -> Point\nend")
    assert(errs.exists(_.render.contains("is closed")), errs.toString)
  }

  test("an unrelated free eq helper does not supply the earlier carrier's equality") {
    val kb = initial()
    assert(load(kb, "namespace demo\n operation eq(a: Point, b: Point) -> Point\nend").isEmpty)
    assert(load(kb, "namespace demo.Helper\n operation eq(a: Point, b: Point) -> Point\nend").isEmpty)
    assert(load(kb, "namespace demo.Generic\n operation eq[A](a: A, b: A) -> Point\nend").isEmpty)
  }

  test("a witness's later eq member is refused even when its provision was earlier") {
    val kb = fresh()
    assert(load(kb, specs + base + witness("Point")).isEmpty)
    assert(load(kb, "namespace demo.Witness\n operation eq(a: Point, b: Point) -> Point\nend").exists(_.isInstanceOf[LoadError.EqualityOfEarlierSort]))
  }

  test("a new instantiation of an earlier witness's provision is refused") {
    val kb = fresh()
    val crate = "namespace demo\n sort Crate\n sort A = ?\n entity crate(a: A)\nend\nend"
    assert(load(kb, specs + base + crate + witness("Crate[A = Point]")).isEmpty)
    assert(load(kb, "namespace demo.Witness\n import anthill.prelude.PartialEq\n provides PartialEq[T = Crate[A = Handle]]\nend").exists(_.isInstanceOf[LoadError.EqualityOfEarlierSort]))
  }

  test("abstract carrier equality remains open") {
    val kb = initial()
    assert(load(kb, witness("Handle")).isEmpty)
  }

  test("later provisions of each equality spec are refused, including conditions") {
    for spec <- Seq("PartialEq", "Eq", "NonEq") do
      val kb = initial()
      val src = s"namespace demo.Point\n import anthill.prelude.{$spec, Eq}\n provides $spec[T = Point] :- Eq[T = Handle]\nend"
      assert(load(kb, src).exists(_.render.contains("is closed")), spec)
  }

  test("unchanged equality source can be presented again without a seal") {
    val kb = fresh()
    assert(load(kb, specs + base + witness("Point")).isEmpty)
    assert(load(kb, witness("Point")).isEmpty)
    assert(load(kb, witness("Point").replace("[T = Point]", "[Point]")).isEmpty)
  }

  test("later load adds a runnable clause and retains the earlier constructors") {
    val kb = initial()
    assert(load(kb, "namespace demo\n rule alive(point) :- true\nend").isEmpty)
    val head = kb.alloc(anthill.term.Term.Fn(kb.resolveSymbol("demo.alive"),
      IArray(kb.makeNameTermFromSym(kb.resolveSymbol("demo.Point.point"))), IArray.empty))
    assertEquals(SearchStream.resolve(kb, head).allSolutions(kb).length, 1)
  }

  for declaration <- Seq("sort S\nend", "enum S\n entity one\nend", "operation op() -> S", "sort T = ?", "entity item", "const value: S") do
    test(s"duplicate declaration is refused in one load and across a seal: $declaration") {
      val src = "namespace lib\n" + declaration + "\nend"
      val one = fresh()
      assert(Loader.loadAll(one, IndexedSeq(parsed(src), parsed(src))).exists(_.render.contains("made again")))
      val kb = fresh()
      assert(load(kb, src).isEmpty)
      Loader.sealDeclarations(kb)
      assert(load(kb, src).exists(_.render.contains("made again")))
    }

  test("unsealed declarations may repeat, while a sealed scope admits a new name") {
    val kb = initial()
    assert(load(kb, base).isEmpty)
    Loader.sealDeclarations(kb)
    assert(load(kb, "namespace demo\n entity newName\nend").isEmpty)
  }

  test("a named requirement declares a type protected by the seal") {
    val kb = fresh()
    val src = "namespace demo.Point\n import anthill.prelude.Eq\n requires O: Eq[T = Point]\nend"
    assert(load(kb, specs + base + src).isEmpty)
    Loader.sealDeclarations(kb)
    val errs = load(kb, src)
    assert(errs.exists {
      case LoadError.SealedDeclarations("demo.Point.O", _, _) => true
      case _ => false
    }, errs.toString)
  }

  test("loadProgram seals between library and program; empty library seals nothing") {
    val src = parsed(base)
    val kb = fresh()
    assert(Loader.loadProgram(kb, IndexedSeq(src), IndexedSeq(src)).exists(_.render.contains("made again")))
    val noLib = fresh()
    assert(Loader.loadProgram(noLib, IndexedSeq.empty, IndexedSeq(src)).isEmpty)
    assert(load(noLib, base).isEmpty)
    val noProgram = fresh()
    assert(Loader.loadProgram(noProgram, IndexedSeq(src), IndexedSeq.empty).isEmpty)
    assert(load(noProgram, base).exists(_.render.contains("made again")))
  }

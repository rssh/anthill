package anthill.load

import anthill.kb.KnowledgeBase
import anthill.parse.{ParsedFile, Parser}

/** WI-20261004-2HJW8 — a type alias whose definition reaches its own name is refused
  * where it is declared, naming the chain.
  *
  * THE RULE. An alias is the type it is defined as, so one that names itself — directly
  * (`sort S = S`), through a chain of aliases (`sort A = B`, `sort B = A`), or inside an
  * applied link (`sort Loop = List[T = Loop]`) — would be an infinite type. A recursive
  * type is written through a sort with a constructor.
  *
  * BEFORE. Every such declaration loaded, with no message. Scaland reads no alias
  * through, so nothing else went wrong here; the refusal is the declaration's, the same
  * on both implementations (rustland: `wi_2hjw8_recursive_alias_test`).
  *
  * WHICH TESTS FAIL WHEN THE CHECK IS BACKED OUT ([[Loader.scanDefinitions]] not calling
  * `reportRecursiveAliases`) — measured:
  *
  *   `an alias that names itself is refused where it is declared`
  *   `a chain of aliases that comes back is refused at each link`
  *   `an alias that names a chain without being on it is not refused`
  *
  * `an alias that reaches no name of its own loads` PASSES EITHER WAY, by design: it is
  * the fence, what must keep loading.
  */
class RecursiveAliasTest extends munit.FunSuite:

  private def parsed(src: String)(using munit.Location): ParsedFile =
    Parser.parse(src, "t.anthill") match
      case Right(p)   => p
      case Left(errs) => fail(s"parse failed: ${errs.map(_.render).mkString("; ")}")

  /** The load errors of `body` inside a namespace `t`. */
  private def loadErrors(body: String)(using munit.Location): Seq[String] =
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val src = s"namespace t\n$body\nend\n"
    Loader.loadAll(kb, IndexedSeq(parsed(src))).map(_.toString).toSeq

  /** The one refusal of `alias`, at `line:col`, naming `chain`. */
  private def assertRefused(errs: Seq[String], alias: String, at: String, chain: String)(
    using munit.Location
  ): Unit =
    val hits = errs.filter(_.contains(s"type alias `t.$alias` reaches its own name"))
    assertEquals(hits.size, 1, s"one refusal of `$alias`: $errs")
    assert(hits.head.contains(s":$at: "), s"at the declaration: ${hits.head}")
    assert(hits.head.contains(s"($chain)"), s"naming the chain: ${hits.head}")

  test("an alias that names itself is refused where it is declared") {
    val self = loadErrors("  sort S = S")
    assertRefused(self, "S", "2:3", "S -> S")
    assertEquals(self.size, 1, self.toString)

    val inside = loadErrors("  sort List\n    sort T = ?\n  end\n  sort Loop = List[T = Loop]")
    assertRefused(inside, "Loop", "5:3", "Loop -> Loop")
    assertEquals(inside.size, 1, inside.toString)

    val nested = loadErrors(
      "  sort List\n    sort T = ?\n  end\n  sort Host\n    sort HA = List[T = HA]\n    entity h\n  end")
    assertRefused(nested, "Host.HA", "6:5", "HA -> HA")
  }

  test("a chain of aliases that comes back is refused at each link") {
    val bare = loadErrors("  sort A = B\n  sort B = A")
    assertRefused(bare, "A", "2:3", "A -> B -> A")
    assertRefused(bare, "B", "3:3", "B -> A -> B")
    assertEquals(bare.size, 2, bare.toString)

    val applied = loadErrors(
      "  sort List\n    sort T = ?\n  end\n  sort Opt\n    sort T = ?\n  end\n" +
      "  sort A = List[T = B]\n  sort B = Opt[T = A]")
    assertRefused(applied, "A", "8:3", "A -> B -> A")
    assertRefused(applied, "B", "9:3", "B -> A -> B")
    assertEquals(applied.size, 2, applied.toString)
  }

  test("an alias that names a chain without being on it is not refused") {
    val errs = loadErrors(
      "  sort List\n    sort T = ?\n  end\n" +
      "  sort A = B\n  sort B = C\n  sort C = List[T = A]\n  sort D = List[T = A]")
    assertRefused(errs, "A", "5:3", "A -> B -> C -> A")
    assertRefused(errs, "B", "6:3", "B -> C -> A -> B")
    assertRefused(errs, "C", "7:3", "C -> A -> B -> C")
    assert(!errs.exists(_.contains("`t.D` reaches")), s"`D` is on no chain: $errs")
  }

  test("an alias that reaches no name of its own loads") {
    // A chain that ends; an alias naming one declared below it; recursion through a
    // constructor, where `Kids` names the sort and not itself; an alias that shares its
    // short name with the sort it stands for.
    val errs = loadErrors(
      "  sort List\n    sort T = ?\n  end\n" +
      "  sort Top = Mid\n  sort Mid = List[T = Leaf]\n  sort Leaf\n    entity leaf\n  end\n" +
      "  sort Y = Later\n  sort Later = Leaf\n" +
      "  sort Tree\n    entity node(kids: Kids)\n  end\n  sort Kids = List[T = Tree]\n" +
      "  namespace inner\n    sort Box2\n      entity b2\n    end\n  end\n  sort Box2 = inner.Box2")
    assertEquals(errs, Seq.empty[String])
  }

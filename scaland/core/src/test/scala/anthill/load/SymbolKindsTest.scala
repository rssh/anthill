package anthill.load

import anthill.intern.{SymbolKind}
import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.term.Term

/** N3WGM: membership drives behavior even when the required role was added last.
  * Measured with define's addKind(existing, kind) removed: 3 of 40 focused rows fail.
  * The first two rows here fail; RuleHeadDeclarationTest's construct-collision row
  * fails in its rule-first arm. The remaining 37 rows are controls, including the
  * entity-sugar row (explicit addKind) and the completed-ladder row below. */
class SymbolKindsTest extends munit.FunSuite:
  test("define accumulates roles in both orders and preserves symbol identity") {
    for roles <- Seq(Vector(SymbolKind.Goal, SymbolKind.Operation),
                     Vector(SymbolKind.Operation, SymbolKind.Goal)) do
      val kb = KnowledgeBase()
      val first = kb.symbols.define("p", "p", roles.head, kb.globalScope)
      val again = kb.symbols.define("p", "p", roles.last, kb.globalScope)
      assertEquals(first, again)
      kb.symbols.define("p", "p", roles.head, kb.globalScope)
      assertEquals(kb.symbols.get(first).kindsSet, roles.toSet)
      assertEquals(kb.symbols.get(first).exclusiveKind, None)
      assertEquals(kb.symbols.get(first).primaryKind, Some(roles.head))
  }

  test("a sort role added after Entity keeps the one symbol and its one nullary term") {
    // It asserted the two nullary forms until the canon stopped exempting a sort
    // (WI-20261020-80VNX): the role set is what accumulates, and `E()` is `E`.
    val kb = KnowledgeBase()
    val sym = kb.symbols.define("E", "E", SymbolKind.Entity, kb.globalScope)
    assertEquals(kb.symbols.define("E", "E", SymbolKind.Sort, kb.globalScope), sym)
    assertEquals(kb.symbols.get(sym).kindsSet, Set(SymbolKind.Entity, SymbolKind.Sort))
    assertEquals(kb.alloc(Term.Ref(sym)), kb.alloc(Term.Fn(sym, IArray.empty, IArray.empty)))
    // CONTROL: constructor-only names still have a single nullary form.
    val variant = kb.symbols.define("V", "V", SymbolKind.Entity, kb.globalScope)
    assertEquals(kb.alloc(Term.Ref(variant)), kb.alloc(Term.Fn(variant, IArray.empty, IArray.empty)))
  }

  /** §6.3 (WI-926): the two spellings of one declaration are ONE symbol with both roles —
    * `entity Short` and the long form `sort Long … entity Long … end` alike — and the long
    * form defines no nested `Long.Long`. A constructor named otherwise keeps its own nested
    * symbol, a constructor and nothing else. */
  test("a free-standing and an eponymous entity are one symbol with both roles") {
    val kb = LoadFixture.loaded("""namespace n3
      |  entity Short
      |  sort Long
      |    entity Long
      |  end
      |  sort Other
      |    entity variant
      |  end
      |end""".stripMargin, "entity-kinds.anthill")
    val short = kb.symbols.byQualifiedName("n3.Short")
    val long = kb.symbols.byQualifiedName("n3.Long")
    val nested = kb.symbols.byQualifiedName("n3.Other.variant")
    for sym <- Seq(short, long) do
      assertEquals(kb.symbols.get(sym).kindsSet, Set(SymbolKind.Entity, SymbolKind.Sort))
      assertEquals(kb.alloc(Term.Ref(sym)), kb.alloc(Term.Fn(sym, IArray.empty, IArray.empty)))
    assert(!kb.symbols.byQualifiedName.contains("n3.Long.Long"), "no nested `Long.Long`")
    assertEquals(kb.symbols.get(nested).exclusiveKind, Some(SymbolKind.Entity))
    assertEquals(kb.alloc(Term.Ref(nested)), kb.alloc(Term.Fn(nested, IArray.empty, IArray.empty)))
  }

  test("a later enclosing operation cannot be shadowed by a predicate declaration") {
    for files <- Seq(
      IndexedSeq("namespace n3.outer\n sort Inner\n rule p(?x)\n end\nend",
                 "namespace n3.outer\n operation p(x: Int64) -> Bool\nend"),
      IndexedSeq("namespace n3.outer\n operation p(x: Int64) -> Bool\nend",
                 "namespace n3.outer\n sort Inner\n rule p(?x)\n end\nend")) do
      val kb = KnowledgeBase()
      Prelude.register(kb)
      val parsed = files.zipWithIndex.map((src, i) => LoadFixture.parsed(src, s"n3-$i.anthill"))
      val errors = Loader.loadAll(kb, parsed)
      assert(errors.exists(_.toString.contains("declaration would shadow")), errors.toString)
  }

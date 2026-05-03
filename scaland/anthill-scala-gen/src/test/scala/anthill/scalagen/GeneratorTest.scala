package anthill.scalagen

import anthill.kb.KnowledgeBase

class GeneratorTest extends munit.FunSuite:

  test("Generator.generate on an empty KB returns no files") {
    val kb = KnowledgeBase()
    val files = Generator.generate(kb)
    assertEquals(files.size, 0)
  }

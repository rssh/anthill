package anthill.load

import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.resolve.SearchStream
import anthill.term.{Literal, Term}

/** WI-20261029-50361 — a rule head named like a namespace it reaches introduces its own
  * predicate, as its declaration does, and a clause is never stored under a namespace
  * (kernel-language.md §5.3). The scaland port of rustland's
  * `wi_50361_namespace_named_head_test`.
  *
  * Inside `namespace probe.zed` a bare `zed` reaches the namespace through the enclosing
  * `probe`, and a head introduces only when its name resolves to nothing, so `rule zed :- …`
  * introduced nothing and its clause was stored under the namespace. Where no predicate of
  * its own can be introduced — the head is written in the scope that declares the
  * namespace, or spelled qualified — the clause is refused.
  *
  * NOT PORTED: rustland's ambiguity row (scaland's recovery interns the written name, so it
  * never stands on a namespace) and its one-arity, two-scope and path rows, whose refusals
  * scaland does not raise.
  *
  * ── THE BACK-OUT, applied and run ───────────────────────────────────────────
  *
  * Each part edited out alone, over this suite and `GlobalDeclarationHeadTest`:
  *   * the namespace arm of `Loader.ruleHeadLadderAnswer` → the nullary, unary and
  *     deeper-and-imported rows (the clause goes back on the namespace, or the import of
  *     `zed` is unresolved);
  *   * `Loader.refuseHeadNamingNamespace` answering `false` → the refusal row and the
  *     multi-head row;
  *   * the multi-head rule's other heads asserted beside a refused one → the multi-head
  *     row;
  *   * the namespace exclusion in `refuseDeclarationThatCannotStand` → the declared
  *     predicate's row;
  *   * the declaration's repair advising `:- true` again → the advice row.
  * The declared entity passes either way by design, as do `GlobalDeclarationHeadTest`'s
  * seven. */
class NamespaceNamedHeadTest extends munit.FunSuite:

  private def errorsOf(files: (String, String)*): IndexedSeq[String] =
    val kb = KnowledgeBase()
    Prelude.register(kb)
    Loader.loadAll(kb, files.map((l, s) => LoadFixture.parsed(s, l)).toIndexedSeq).map(_.render).toIndexedSeq

  private def loaded(files: (String, String)*)(using munit.Location): KnowledgeBase =
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val errs = Loader.loadAll(kb, files.map((l, s) => LoadFixture.parsed(s, l)).toIndexedSeq)
    assert(errs.isEmpty, s"load errors: ${errs.map(_.render)}")
    kb

  /** Definite answers of `qn(args…)`; `qn` must resolve. */
  private def answers(kb: KnowledgeBase, qn: String, args: Int*)(using munit.Location): Int =
    val sym = kb.tryResolveSymbol(qn).getOrElse(fail(s"`$qn` must resolve"))
    val goal =
      if args.isEmpty then kb.alloc(Term.Ref(sym))
      else kb.alloc(Term.Fn(sym,
        IArray.from(args.map(a => kb.alloc(Term.Const(Literal.IntLit(a.toLong))))), IArray.empty))
    SearchStream.resolve(kb, goal).allSolutions(kb).length

  private def clauses(kb: KnowledgeBase, qn: String): Int =
    kb.tryResolveSymbol(qn).map(sym => kb.byFunctor(sym).length).getOrElse(-1)

  test("a nullary head introduces its own predicate, and is imported by name") {
    for clause <- Seq("rule zed :- Link(from: 1, to: 2)", "fact zed") do
      val kb = loaded("a.anthill" ->
        ("namespace n50361a.zed\n  entity Link(from: Int64, to: Int64)\n  fact Link(from: 1, " +
          s"to: 2)\n  $clause\nend\nnamespace n50361a.use\n  import n50361a.zed.{zed}\n  rule " +
          "seen :- zed\nend\n"))
      assertEquals(answers(kb, "n50361a.zed.zed"), 1, clause)
      assertEquals(answers(kb, "n50361a.use.seen"), 1, clause)
  }

  test("a unary head answers under its own name, and the namespace holds nothing") {
    val kb = loaded("b.anthill" -> "namespace n50361b.zed\n  rule zed(3) :- true\nend\n")
    assertEquals(answers(kb, "n50361b.zed.zed", 3), 1)
    assertEquals(answers(kb, "n50361b.zed", 3), 0)
  }

  test("reached deeper and through an import, the head introduces where it is written") {
    val kb = loaded("f.anthill" ->
      ("namespace n50361f.zed.inner\n  rule zed(1) :- true\nend\n" +
        "namespace n50361f.sib\n  import n50361f.zed\n  rule zed(2) :- true\nend\n"))
    assertEquals(answers(kb, "n50361f.zed.inner.zed", 1), 1)
    assertEquals(answers(kb, "n50361f.sib.zed", 2), 1)
  }

  test("CONTROL: a declared entity of the name was already its own") {
    val kb = loaded("d.anthill" ->
      "namespace n50361d.zed\n  entity zed(x: Int64)\n  fact zed(x: 1)\nend\n")
    assert(clauses(kb, "n50361d.zed.zed") > 0)
  }

  test("the declared predicate stands beside the namespace it reaches") {
    // Scaland refused it until now ("would shadow it for the whole scope"), where rustland
    // loaded it; the undeclared head introduces there, so its declaration does too.
    val kb = loaded("e.anthill" -> "namespace n50361e.zed\n  rule zed(?x)\n  rule zed(1) :- true\nend\n")
    assertEquals(answers(kb, "n50361e.zed.zed", 1), 1)
  }

  test("a clause that would land on a namespace is refused") {
    val child = "namespace n50361i.zed\n  entity X(v: Int64)\nend\n"
    for (label, src, ns) <- Seq(
      ("rule in the parent", s"namespace n50361i\n  rule zed(1) :- true\nend\n$child", "n50361i.zed"),
      ("fact in the parent", s"namespace n50361i\n  fact zed(1)\nend\n$child", "n50361i.zed"),
      ("qualified head", s"namespace n50361j\n  rule n50361i.zed(1) :- true\nend\n$child", "n50361i.zed"),
    ) do
      val errs = errorsOf("i.anthill" -> src)
      assert(errs.exists(e => e.contains(s"head names the namespace `$ns`") &&
        e.contains("a namespace is not a relation and holds no clauses")), s"$label: $errs")
  }

  test("the declaration in the parent does not advise a clause") {
    val errs = errorsOf("k.anthill" ->
      "namespace n50361k\n  rule zed(?x)\nend\nnamespace n50361k.zed\n  entity X(v: Int64)\nend\n")
    assert(errs.exists(_.contains("no clause can be written of it")), s"$errs")
    assert(!errs.exists(_.contains("write `:- true`")), s"$errs")
  }

  test("a multi-head rule with a head on a namespace stores none of its heads") {
    val kb = KnowledgeBase()
    Prelude.register(kb)
    val errs = Loader.loadAll(kb, IndexedSeq(LoadFixture.parsed(
      "namespace n50361p.zed\n  entity X(v: Int64)\nend\nnamespace n50361q\n  rule both: " +
        "n50361p.zed(1), other(1) :- true\nend\n", "p.anthill"))).map(_.render)
    assert(errs.exists(_.contains("head names the namespace `n50361p.zed`")), s"$errs")
    assert(clauses(kb, "n50361q.other") <= 0, "the rule's other head is not stored")
  }

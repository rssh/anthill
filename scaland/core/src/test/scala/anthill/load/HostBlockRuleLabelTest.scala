package anthill.load

import anthill.kb.{KnowledgeBase, LoadFixture}
import anthill.kb.LoadFixture.{refusal, unaryAnswers as answers}

/** WI-20261024-RMZQZ (rustland's twin: `wi_rmzqz_host_block_rule_label_test`) — A RULE
  * LABEL IN A HOST `provides … language … end` BLOCK IS DEFINED AT THE BLOCK'S TARGET
  * SORT, the scope the block's clauses load in (§10.2). Pass 1 cannot define it there:
  * the target is known only after imports, so the block's deferred work does, beside the
  * predicate a body-less rule there declares. Before this ticket the label was defined
  * nowhere, and neither name could be imported: the deferred work ran after pass 2 had
  * deferred the import, and the head census refused it.
  *
  * scaland stores no label on a clause (citation is not ported), so a row asks where the
  * label is DEFINED; which clauses it cites is rustland's row.
  *
  * ── WHICH ROWS FAIL WHEN WHAT IS BACKED OUT — each applied in `Loader` and run ──
  *
  *  * **NO LABEL IN THE DEFERRED BLOCK** — `defineRuleLabel` not called there (the state
  *    before this ticket). **6 OF 8 FAIL**: every label row, and the import row, which
  *    imports `law`. Every program still loads, scaland never looking a label up.
  *  * **NO IMPORT RETRY** — `wireImportsOfHostBlockNames` not called. **1 FAILS**: the
  *    import row, each of its three forms refused.
  *  * **THE SCAN REPORTS AN UNRESOLVED TARGET** — the deferred block and the head census
  *    passing `errors` to `providesBlockScope` again. **1 FAILS**: the unresolved-target
  *    row, with three errors.
  *
  * PASS EITHER WAY, BY DESIGN: the declaration row. scaland declared at the target before
  * this ticket; the row is the twin of rustland's, which did not.
  *
  * Measured 2026-10-30.
  */
class HostBlockRuleLabelTest extends munit.FunSuite:

  private def loaded(src: String)(using munit.Location): KnowledgeBase =
    LoadFixture.loaded(src, "hostlabel.anthill")

  test("a labeled rule in a host block has its label at the target sort") {
    val kb = loaded("""namespace zzRMZ.one
      |  sort RecP
      |    entity P(v: Int64)
      |    rule see(?x) :- pick(?x)
      |  end
      |  provides RecP language rust
      |    artifact "x.rs"
      |    rule law: pick(1) :- true
      |  end
      |end""".stripMargin)
    assertEquals(answers(kb, "zzRMZ.one.RecP.see"), 1)
    assert(kb.hasQualifiedName("zzRMZ.one.RecP.law"), "the label is the target sort's")
    assert(!kb.hasQualifiedName("zzRMZ.one.law"), "not the scope the block is written in")
  }

  test("two carriers' blocks writing one label do not collide") {
    val kb = loaded("""namespace zzRMZ.two
      |  sort RecP
      |    entity P(v: Int64)
      |    rule see(?x) :- pick(?x)
      |  end
      |  sort RecQ
      |    entity Q(v: Int64)
      |    rule see(?x) :- pick(?x)
      |  end
      |  provides RecP language rust
      |    artifact "x.rs"
      |    rule law: pick(1) :- true
      |  end
      |  provides RecQ language rust
      |    artifact "y.rs"
      |    rule law: pick(2), pick(3) :- true
      |  end
      |end""".stripMargin)
    assertEquals((answers(kb, "zzRMZ.two.RecP.see"), answers(kb, "zzRMZ.two.RecQ.see")), (1, 2))
    val (p, q) = (kb.tryResolveSymbol("zzRMZ.two.RecP.law"), kb.tryResolveSymbol("zzRMZ.two.RecQ.law"))
    assert(p.isDefined && q.isDefined && p != q, s"each carrier's label is its own: $p / $q")
  }

  test("the enclosing namespace's label is not the host block's") {
    val kb = loaded("""namespace zzRMZ.ns
      |  rule law: other(1) :- true
      |  sort RecP
      |    entity P(v: Int64)
      |    rule see(?x) :- pick(?x)
      |  end
      |  provides RecP language rust
      |    artifact "x.rs"
      |    rule law: pick(1) :- true
      |  end
      |end""".stripMargin)
    val (ns, rec) = (kb.tryResolveSymbol("zzRMZ.ns.law"), kb.tryResolveSymbol("zzRMZ.ns.RecP.law"))
    assert(ns.isDefined && rec.isDefined && ns != rec, s"two labels: $ns / $rec")
  }

  test("a rule block in a host block labels each entry at the target sort") {
    val kb = loaded("""namespace zzRMZ.blk
      |  sort RecP
      |    entity P(v: Int64)
      |    rule see(?x) :- pick(?x)
      |  end
      |  provides RecP language rust
      |    artifact "x.rs"
      |    rule {
      |      law: pick(1) :- true
      |      law2: pick(2), pock(1) :- true
      |    }
      |  end
      |end""".stripMargin)
    assertEquals(answers(kb, "zzRMZ.blk.RecP.see"), 2)
    assert(kb.hasQualifiedName("zzRMZ.blk.RecP.law") && kb.hasQualifiedName("zzRMZ.blk.RecP.law2"))
  }

  test("the label lands where the clauses land however the target is written") {
    // rustland's row also writes the target as an alias; scaland reads no alias through,
    // so a block at an alias loads its clauses at the alias.
    for (label, decl, target) <- Seq(
        ("imported", "", "Rec"),
        ("applied", "", "Rec[T = Int64]"))
    do
      val kb = loaded(s"""namespace zzRMZ.lib
        |  sort Rec[T]
        |    entity E(v: T)
        |    rule see(?x) :- pick(?x)
        |  end
        |end
        |namespace zzRMZ.side_$label
        |  import zzRMZ.lib.{Rec}
        |$decl  provides $target language rust
        |    artifact "x.rs"
        |    rule law: pick(1) :- true
        |  end
        |end""".stripMargin)
      assertEquals(answers(kb, "zzRMZ.lib.Rec.see"), 1, label)
      assert(kb.hasQualifiedName("zzRMZ.lib.Rec.law"), s"$label: the label is the target sort's")
  }

  test("a declaration in a host block declares its predicate for every file") {
    // A predicate with clauses in two files must be declared (proposal 061). Written in a
    // host block, the declaration is the target sort's, as the block's clauses are.
    val kb = LoadFixture.tryLoad(
      "a.anthill" -> """namespace zzRMZ.d2
        |  sort RecP
        |    entity P(v: Int64)
        |    rule see(?x) :- pick(?x)
        |  end
        |  provides RecP language rust
        |    artifact "x.rs"
        |    rule pick(?x)
        |    rule pick(1) :- true
        |  end
        |end""".stripMargin,
      "b.anthill" -> """namespace zzRMZ.d2
        |  provides RecP language cpp
        |    artifact "x.cpp"
        |    rule pick(2) :- true
        |  end
        |end""".stripMargin).fold(e => fail(e.toString), identity)
    assertEquals(answers(kb, "zzRMZ.d2.RecP.see"), 2, "both files' clauses answer")
  }

  test("a host block name is imported as a sort body's is") {
    val lib = """namespace zzRMZ.imp
      |  sort RecP
      |    entity P(v: Int64)
      |  end
      |  provides RecP language rust
      |    artifact "x.rs"
      |    rule law: pick(1) :- true
      |    rule pock(?x)
      |    rule pock(5) :- true
      |  end
      |end
      |""".stripMargin
    for (label, imports) <- Seq(
        ("plain", "import zzRMZ.imp.RecP.pock\n  import zzRMZ.imp.RecP.law"),
        ("selective", "import zzRMZ.imp.RecP.{pock, law}"),
        ("one scope below", "import zzRMZ.imp.{pock, law}"))
    do
      val kb = LoadFixture.tryLoad("imp.anthill" ->
        (lib + s"namespace zzRMZ.use\n  $imports\n  rule see(?x) :- pock(?x)\nend\n"))
        .fold(e => fail(s"$label: $e"), identity)
      assertEquals(answers(kb, "zzRMZ.use.see"), 1, s"$label: the import reaches `pock`")
    // The control: a name the block does not define is still refused.
    val errors = refusal("imp.anthill" -> (lib + "namespace zzRMZ.use\n  import zzRMZ.imp.RecP.{nosuch}\nend\n"))
    assert(errors.exists(_.contains("nosuch")), errors.toString)
  }

  test("a block whose target names nothing is refused once") {
    val errors = refusal("miss.anthill" -> """namespace zzRMZ.miss
      |  provides Missing language rust
      |    artifact "x.rs"
      |    rule law: pick(1) :- true
      |  end
      |end""".stripMargin)
    assertEquals(errors.length, 1, errors.toString)
    assert(errors.head.contains("Missing"), errors.toString)
  }

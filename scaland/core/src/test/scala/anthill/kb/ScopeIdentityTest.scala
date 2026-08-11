package anthill.kb

import anthill.intern.{SymbolDef, SymbolTable}
import anthill.resolve.SearchStream
import anthill.term.{Term, TermId, Var}

import scala.compiletime.testing.typeCheckErrors

/** WI-976 — SCOPE-HOOD IS A TYPE, NOT A CLAIM EACH CALLER RE-MAKES. The type and its
  * history live in [[anthill.intern.SymbolTable.ScopeId]]; this file is what holds it true.
  *
  * CONTROL — two mechanisms, because they fail differently:
  *
  *   1. THE TYPE, asserted rather than described. The first case below type-checks the
  *      two call shapes that were legal before this WI — `scopeDisplayName` on a bare
  *      `TermId`, and `resolveInScope` on a bare `Int` — and asserts both are rejected.
  *      It is an assertion and not a comment because the guarantee is the kind that
  *      rots quietly: it can be undone with every runtime test still green.
  *
  *      Measured on the two ways that could happen. A widening `Conversion[TermId,
  *      ScopeId]` in scope: this ONE case fails (`a bare TermId must not be a scope; got
  *      List()`) and the three below pass, which is the report you want — the type went,
  *      the behaviour did not. A `scopeDisplayName(TermId)` OVERLOAD turns out not to be
  *      reachable at all: `ScopeId` and `TermId` both erase to `int`, so the compiler
  *      refuses it as a double definition. That is a stronger guarantee than this case
  *      needs, and it is the erasure's doing, not the assertion's.
  *   2. THE RUNTIME CASES, for what the type cannot state. `scopeTerm` is the one
  *      scope→term direction and reflect's `scope` builtin is its only runtime reader —
  *      a site that previously reconstructed the term as `TermId.fromRaw(scopeRaw)`,
  *      correct ONLY because the scope key happened to be a term id. Measured:
  *      transcribe that old line under the new storage —
  *      `TermId.fromRaw(TermSymbol.raw(kb.symbols.symbolOf(scope)))` — and exactly ONE case fails, the
  *      builtin one, binding term 66 where `demo.S` is term 18. The other two pass
  *      either way BY DESIGN: they never reach the builtin.
  *
  * All of it is NEW coverage rather than re-assertion — nothing in the tree drove the
  * `scope` builtin at all before this WI, which is why its read-back could lean on a
  * coincidence unnoticed.
  *
  * WI-983 CARRIED THE SAME TYPE ACROSS THE KB's WRITE BOUNDARY — a clause's `domain`.
  * The last two cases are its, and they split the same way.
  *
  * The TYPE case is the discriminator, measured by the same `Conversion[TermId,
  * ScopeId]` above: it fails (`a scope's term form must not be a domain; got List()`)
  * alongside the WI-976 case and nothing else, 335 of 337 still passing. What it rejects
  * is the loader's own former spelling, `assertFact(…, kb.scopeTerm(scope))`, at all six
  * assert sites.
  *
  * The RUNTIME case passes EITHER WAY, by design, and that too is measured rather than
  * assumed: run it with `val a: ScopeId = kb.makeNameTerm("a")` — the pre-WI-983 domain,
  * a term, widened by that same conversion — and it is green. WI-983 changes what the
  * slot is spelled as and nothing about what it does; both spellings are one key per
  * scope. The case earns its place as COVERAGE, not discrimination: `byDomain`,
  * `ruleDomain` and `assertFact`'s dedup had no reader anywhere in this tree, so a
  * mis-keyed index or a domain equality that answered the same for every scope would
  * have gone unnoticed either side of this WI.
  *
  * WI-990 SAID WHICH TABLE AT THE MINT SITE, which the type alone could not. `ScopeId.of`
  * was total over `TermSymbol`, and a `TermSymbol` indexes ONE `SymbolTable`'s `defs`
  * while the loader threads two. Its two cases split the usual way — the mint's LOCATION
  * is a compile error, its RANGE a runtime refusal.
  *
  * WI-1004 MADE THE TABLE PART OF THE TYPE — `ScopeId` is a member of the table that
  * issues it. Why that, and what it does and does not reach, is stated once at
  * [[anthill.intern.SymbolTable.ScopeId]]. What this file adds is the assertions, and the
  * limit WI-990 recorded splits in two across them:
  *   - a scope minted by one table and USED at another is a compile error (`Found:
  *     a.ScopeId  Required: b.ScopeId`), at `resolveInScope` and at the KB's `domain` slot;
  *   - a foreign symbol handed to the RIGHT table's MINT still compiles. That half stays
  *     open, and the `mint refuses` case asserts it rather than implying it is closed.
  *
  * MEASURE A TYPE-LEVEL CONTROL WITH `core/clean`. `typeCheckErrors` runs the typer at
  * THIS file's compile time, and zinc does not treat the snippet's subject as a
  * dependency: changing the subject and re-running `testOnly` leaves the stale class file
  * in place and reports green.
  *
  * MEASURED for WI-1004 under `core/clean`, by aliasing the member back to ONE top-level
  * opaque type (`type ScopeId = anthill.intern.SharedScopeId`) — the pre-WI-1004 semantics
  * in the post-WI-1004 spelling, so the tree still compiles and only the type-level
  * assertions can move: 2 of these 9 cases fail, "belongs to the table that minted it" and
  * the inverted third assertion of "the mint refuses", both with `got List()` — the
  * snippet compiled clean, which is exactly the state this WI closed. Its two rejections
  * were measured ONE AT A TIME (munit stops a case at its first failed assert): each fails
  * on its own, so the `domain` half is not riding on the `resolveInScope` half. The other
  * 354 tests pass either way, by design — they are WI-976/983/990's, and this WI changes
  * what the type SAYS, not what any of it does.
  */
class ScopeIdentityTest extends munit.FunSuite:

  private def loaded(src: String): KnowledgeBase = LoadFixture.loaded(src, "<scope>")

  private val src =
    """namespace demo
      |  sort S
      |    operation f(x: S) -> S
      |  end
      |end""".stripMargin

  test("WI-976: a term and an integer are no longer scopes") {
    // Both snippets COMPILED before this WI. `typeCheckErrors` runs the typer over them
    // at THIS file's compile time and hands back the diagnostics, so the assertion is on
    // the rejection itself rather than on a comment claiming one.
    //
    // Matched on `Required: <table>.ScopeId` since WI-1004: the type is a MEMBER now, so
    // its rendering names the path as well as the type, and a match on the pair asserts
    // both halves at once — that a scope is what was wanted, and whose.
    val termAsScope = typeCheckErrors(
      """val kb = anthill.kb.KnowledgeBase()
         kb.scopeDisplayName(kb.makeNameTerm("Foo"))""")
    assert(
      termAsScope.exists(_.message.contains("Required: kb.ScopeId")),
      s"a bare TermId must not be a scope; got $termAsScope")

    // Through a `val`, so the table has a NAME to render: an unstable prefix
    // (`SymbolTable().resolveInScope(…)`) is rejected just the same, but the message reads
    // `Required: ?1.ScopeId`, which pins nothing a reader can check. Both spellings
    // compiled before WI-976.
    val intAsScope = typeCheckErrors(
      """val st = anthill.intern.SymbolTable()
         st.resolveInScope("x", 100)""")
    assert(
      intAsScope.exists(_.message.contains("Required: st.ScopeId")),
      s"a bare Int must not be a scope; got $intAsScope")

    // POSITIVE control, so the two rejections cannot pass vacuously: the same snippet
    // shape with a real scope type-checks clean. Without this, a typo inside a snippet
    // string would produce errors of its own and both assertions would still hold.
    assertEquals(
      typeCheckErrors(
        """val kb = anthill.kb.KnowledgeBase()
           kb.scopeDisplayName(kb.globalScope)"""),
      Nil)
  }

  test("WI-976: a declared scope displays as its qualified name; `_global` as its spelling") {
    val kb = loaded(src)
    assertEquals(kb.scopeDisplayName(kb.symbols.scopeOf(kb.resolveSymbol("demo.S"))), "demo.S")
    // The scope with NO qualified name — `_global` is interned, never declared, so its
    // `SymbolDef` is `Unresolved`. This is the input the old `scopeFunctor` /
    // `IllegalStateException` pair looked like it was guarding against and never was:
    // it is a perfectly good scope, and `qualifiedNameOf` already falls back to the
    // interned spelling.
    assertEquals(kb.scopeDisplayName(kb.globalScope), "_global")
  }

  test("WI-990: a scope is minted THROUGH the table whose symbol it is") {
    // `ScopeId.of(sym)` compiled from anywhere before this WI, for a symbol from ANY
    // table — and the loader threads two, `kb.symbols` and the parse-time `fileSym`. The
    // snippet is that call on a foreign table's symbol, which is the shape
    // `ScopeId.of(imp.path.last)` would have had at any of `Loader`'s import sites.
    val companionMint = typeCheckErrors(
      """val fileSym = anthill.intern.SymbolTable()
         anthill.intern.ScopeId.of(fileSym.intern("Widget"))""")
    // WI-990 made this an ACCESS refusal (`ScopeId.of` went `private[intern]`); WI-1004
    // moved the type itself INTO the table, so there is no `anthill.intern.ScopeId` left
    // to reach — a mint outside a table is now unspellable rather than inaccessible. The
    // assertion follows the message, and still discriminates the same thing: re-introduce
    // a top-level `ScopeId` with a companion mint and it fails. Matched on the NAME as
    // well as the wording — "is not a member of" alone would be satisfied by any typo in
    // the snippet, which is the trap the previous spelling of this assertion named.
    assert(
      companionMint.exists(m =>
        m.message.contains("ScopeId is not a member of anthill.intern")),
      s"a scope must not be mintable outside a `SymbolTable`; got $companionMint")

    // POSITIVE control: the same mint through the table type-checks clean, so the
    // rejection above is about WHERE the mint lives and not about the snippet.
    assertEquals(
      typeCheckErrors(
        """val st = anthill.intern.SymbolTable()
           st.scopeOf(st.intern("Widget"))"""),
      Nil)
  }

  test("WI-990: the mint refuses a symbol its table never issued") {
    val kb = KnowledgeBase()
    // A second table, grown past `kb.symbols` (a bare KB holds only `_global`), so its
    // last symbol indexes off the end of the KB's `defs` — the direction the ticket
    // MEASURED: `kb.scopeDisplayName(ScopeId.of(foreign))` used to throw
    // `IndexOutOfBoundsException` from inside `qualifiedNameOf`, a display path, with
    // nothing naming the actual mistake.
    val other = SymbolTable()
    val foreign = IndexedSeq("a", "b", "c", "d", "e").map(other.intern).last
    // Discriminating for the range check alone: delete it and `intercept` finds no throw.
    val refused = intercept[IllegalArgumentException](kb.symbols.scopeOf(foreign))
    assert(refused.getMessage.contains("past this symbol table's 1 entries"),
      s"the refusal should say what it observed; got ${refused.getMessage}")

    // The bound is the TABLE's, not a global one: `other` issued it, so `other` mints it.
    assertEquals(other.scopeOf(foreign), other.scopeOf(other.intern("e")))

    // INVERTED BY WI-1004, which is what this pair of assertions used to record as a hole.
    // The direction that mattered — `other` issues the symbol, so `other` mints the scope,
    // and the KB is then handed something that means nothing to it — is a compile error:
    // the table is in the TYPE, so no index is ever looked at.
    val inRange = other.intern("a")
    assertEquals(other.name(inRange), "a")
    val handedOver = typeCheckErrors(
      """val kb = anthill.kb.KnowledgeBase()
         val other = anthill.intern.SymbolTable()
         other.intern("a")
         kb.scopeDisplayName(other.scopeOf(other.intern("a")))""")
    assert(
      handedOver.exists(m =>
        m.message.contains("Found:    other.ScopeId") &&
        m.message.contains("Required: kb.ScopeId")),
      s"another table's scope must not be one of the KB's; got $handedOver")

    // WHAT IS STILL OPEN, asserted so the limit stays a measured fact rather than a hope:
    // the MINT takes a bare `TermSymbol`, so a foreign symbol handed to the KB's OWN mint
    // is in range and silently names another scope — `other`'s "a" is index 0, which in
    // the KB is `_global`. Why it is not closed is at `SymbolTable.ScopeId`; what this
    // line does is make the non-guarantee executable, so a later change that closes it
    // fails here rather than leaving a comment claiming a limit that is gone.
    assertEquals(kb.scopeDisplayName(kb.symbols.scopeOf(inRange)), "_global")
  }

  test("WI-1004: a scope belongs to the table that minted it") {
    // THE cross-table hand-off, which is the direction `scopeOf`'s range check cannot see
    // (`fileSym` small, `kb.symbols` large — a parse-time symbol is always in range for
    // the KB's table). Before WI-1004 `ScopeId` was ONE top-level opaque type, so every
    // table's scopes had the same type and this snippet compiled.
    val crossTable = typeCheckErrors(
      """val a = anthill.intern.SymbolTable()
         val b = anthill.intern.SymbolTable()
         a.intern("x")
         b.resolveInScope("x", a.scopeOf(a.intern("x")))""")
    assert(
      crossTable.exists(m =>
        m.message.contains("Found:    a.ScopeId") &&
        m.message.contains("Required: b.ScopeId")),
      s"a scope of `a` must not resolve in `b`; got $crossTable")

    // The SAME rejection across the KB's write boundary — `RuleEntry.domain` (WI-983).
    // It is a separate assertion because it is what the ticket's first question settled:
    // `RuleEntry` takes a type parameter and `KnowledgeBase` pins it at its own table's
    // `ScopeId`, rather than each clause carrying a table of its own. Instantiate it at
    // anything else and this stops being a compile error.
    val foreignDomain = typeCheckErrors(
      """val kb = anthill.kb.KnowledgeBase()
         val other = anthill.intern.SymbolTable()
         other.intern("a")
         kb.assertFact(kb.makeNameTerm("f"), kb.makeNameTerm("S"),
                       other.scopeOf(other.intern("a")))""")
    assert(
      foreignDomain.exists(m =>
        m.message.contains("Found:    other.ScopeId") &&
        m.message.contains("Required: kb.ScopeId")),
      s"another table's scope must not be a clause domain; got $foreignDomain")

    // POSITIVE controls, one per rejection, so neither can pass on some unrelated error in
    // its snippet: the same two calls with the SAME table's scope type-check clean.
    assertEquals(
      typeCheckErrors(
        """val a = anthill.intern.SymbolTable()
           a.intern("x")
           a.resolveInScope("x", a.scopeOf(a.intern("x")))"""),
      Nil)
    assertEquals(
      typeCheckErrors(
        """val kb = anthill.kb.KnowledgeBase()
           kb.assertFact(kb.makeNameTerm("f"), kb.makeNameTerm("S"), kb.globalScope)"""),
      Nil)
  }

  test("WI-976: `scopeTerm` is the inverse of the scope a symbol was defined in") {
    val kb = loaded(src)
    val stored = kb.symbols.get(kb.resolveSymbol("demo.S.f")) match
      case SymbolDef.Resolved(_, _, _, scope) => scope
      case other => fail(s"expected a resolved symbol, got $other")
    assertEquals(kb.scopeDisplayName(stored), "demo.S")
    assertEquals(
      TermId.raw(kb.scopeTerm(stored)),
      TermId.raw(kb.makeNameTermFromSym(kb.resolveSymbol("demo.S"))))
  }

  test("WI-976: reflect's `scope` builtin answers with the scope's name term") {
    val kb = loaded(src)
    val fTerm = kb.makeNameTermFromSym(kb.resolveSymbol("demo.S.f"))
    val vid = kb.freshVar(kb.intern("s"))
    val goal = kb.alloc(Term.Fn(
      kb.resolveSymbol("anthill.reflect.scope"),
      IArray(fTerm, kb.alloc(Term.Var(Var.Global(vid)))),
      IArray.empty))

    val solutions = SearchStream.resolve(kb, goal).allSolutions(kb)
    assertEquals(solutions.length, 1, "`scope(demo.S.f, ?s)` should have one solution")
    val bound = solutions.head.subst.resolve(vid).getOrElse(fail("`?s` was left unbound"))
    // The ANSWER, not just "something came back". Naming the term is enough to pin it:
    // `TermStore` hash-conses, so equal ids mean the structurally identical term.
    assertEquals(
      TermId.raw(bound),
      TermId.raw(kb.makeNameTermFromSym(kb.resolveSymbol("demo.S"))),
      s"expected the name term of demo.S, got ${kb.getTerm(bound)}")
  }

  test("WI-983: a clause's domain is a scope, and a scope's term form is not one") {
    // The snippet is the loader's own former spelling — `kb.scopeTerm(scope)` handed to
    // the domain slot, six times over. It compiled before WI-983 and must not now.
    val termAsDomain = typeCheckErrors(
      """val kb = anthill.kb.KnowledgeBase()
         val scope = kb.globalScope
         kb.assertFact(kb.makeNameTerm("f"), kb.makeNameTerm("S"), kb.scopeTerm(scope))""")
    assert(
      termAsDomain.exists(_.message.contains("Required: kb.ScopeId")),
      s"a scope's term form must not be a domain; got $termAsDomain")

    // POSITIVE control: the same call with the scope itself type-checks clean, so the
    // rejection above cannot be some unrelated error in the snippet.
    assertEquals(
      typeCheckErrors(
        """val kb = anthill.kb.KnowledgeBase()
           kb.assertFact(kb.makeNameTerm("f"), kb.makeNameTerm("S"), kb.globalScope)"""),
      Nil)
  }

  test("WI-983: the domain index and `assertFact`'s dedup discriminate by scope") {
    val kb = KnowledgeBase()
    val sort = kb.makeNameTerm("S")
    val fact = kb.makeNameTerm("f")
    val a = kb.symbols.scopeOf(kb.intern("a"))
    val b = kb.symbols.scopeOf(kb.intern("b"))

    val inA = kb.assertFact(fact, sort, a)
    assertEquals(kb.assertFact(fact, sort, a), inA,
      "the same fact in the same scope is the same clause")
    val inB = kb.assertFact(fact, sort, b)
    assertNotEquals(inB, inA, "the same fact in another scope is another clause")

    assertEquals(kb.ruleDomain(inA), a)
    assertEquals(kb.byDomain(a).toSeq, Seq(inA))
    assertEquals(kb.byDomain(b).toSeq, Seq(inB))

    // What `retract` does to the index is NOT observable here — `byDomain` filters on
    // the retracted flag regardless — so this pins the answer, not the bookkeeping: a
    // retracted clause is gone from its own domain and the other domain is untouched.
    kb.retract(inA)
    assertEquals(kb.byDomain(a).toSeq, Seq.empty)
    assertEquals(kb.byDomain(b).toSeq, Seq(inB))
  }

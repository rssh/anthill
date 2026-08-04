package anthill.load

import anthill.intern.{ResolveResult, SymbolDef, SymbolKind}
import anthill.kb.{BuiltinTag, KnowledgeBase}

import scala.compiletime.testing.typeCheckErrors

/** WI-990 — THE STDLIB SPINE IS A VALUE, SO A STEP CANNOT RUN BEFORE IT EXISTS.
  *
  * `Prelude.register`'s later steps used to re-derive `anthill.prelude` / `anthill.reflect`
  * from the KB by qualified name, through `KnowledgeBase.scopeByQualifiedName` — which
  * THREW on a miss, into four private `Unit`-returning steps with no error channel, so a
  * miss aborted KB bootstrap with a stack trace instead of a diagnostic. Nothing but the
  * statement ORDER inside `register` kept that unreachable, and no test named that order
  * load-bearing. Eight lines away `registerBuiltinTags` met the identical condition —
  * "the stdlib namespace is not registered" — and DEGRADED, interning the whole qualified
  * name as one symbol in no scope: two opposite policies for one condition in one file.
  *
  * The policy now is that the condition is UNREPRESENTABLE. `registerStdlibScopes`
  * returns a `StdlibScopes` and every later step takes one, so the ordering dependence is
  * a data dependence.
  *
  * CONTROL, per case, MEASURED by restoring both old shapes — `scopeByQualifiedName` on
  * the KB, and a `registerPrimitiveSorts(kb)` that reads the scopes back through it — and
  * rebuilding from `core/clean` (see below): 2 of these 3 fail.
  *   - "cannot be called without the spine" is THE discriminator, and it is the reordering
  *     the ticket asked for said as a compile error: there is no order to get wrong when
  *     the argument IS the earlier step's result. Fails with `got List()`.
  *   - "`scopeByQualifiedName` is gone" is the same shape for the second half — the KB
  *     exposed TWO scope mints over DISJOINT name universes (symbols, and qualified
  *     names), and neither could name every scope: `scopeByQualifiedName("_global")` threw,
  *     because `_global` is interned and never defined. One mint remains and it is total.
  *     Fails with `got List()`.
  *   - "every builtin tag is defined in a scope" passes EITHER WAY, by design: the degrade
  *     arm was unreachable in fact, so removing it moves nothing. It earns its place as
  *     COVERAGE — nothing in this tree asserted that a builtin is reachable by the name a
  *     rule body writes, and under the degrade arm none of them would be.
  *
  * A `typeCheckErrors` CONTROL NEEDS `core/clean`. The typer runs at this file's compile
  * time and zinc does not treat the snippet's subject as a dependency, so a plain
  * `testOnly` after backing the change out re-uses the stale class file and reports green.
  */
class PreludeScopesTest extends munit.FunSuite:

  test("WI-990: a register step cannot be called before the spine that feeds it") {
    val withoutSpine = typeCheckErrors(
      """anthill.load.Prelude.registerPrimitiveSorts(anthill.kb.KnowledgeBase())""")
    assert(
      withoutSpine.nonEmpty,
      "a step must not be callable with only a KnowledgeBase — that is the ordering " +
        s"dependence this WI removed; got $withoutSpine")

    // POSITIVE control, so the rejection cannot pass on some unrelated error in the
    // snippet: the same call fed by the step that produces the spine type-checks clean.
    assertEquals(
      typeCheckErrors(
        """val kb = anthill.kb.KnowledgeBase()
           anthill.load.Prelude.registerPrimitiveSorts(
             kb, anthill.load.Prelude.registerStdlibScopes(kb))"""),
      Nil)
  }

  test("WI-990: the KB has ONE scope mint, and it names `_global` too") {
    val gone = typeCheckErrors(
      """anthill.kb.KnowledgeBase().scopeByQualifiedName("anthill.prelude")""")
    assert(gone.nonEmpty, s"the qualified-name mint must be gone; got $gone")

    // The remaining mint is total over its table's symbols, so it reaches the scope the
    // deleted one could not name at all. (What `_global` DISPLAYS as is `ScopeIdentityTest`'s
    // to assert; what this case adds is that the mint gets there.)
    val kb = KnowledgeBase()
    assertEquals(kb.symbols.scopeOf(kb.intern("_global")), kb.globalScope)
  }

  test("WI-990: every builtin tag is an operation defined in the scope its name says") {
    val kb = KnowledgeBase()
    Prelude.register(kb)

    // Written as (namespace, short) pairs — the shape `Prelude.builtinDefs` now has, and
    // an INDEPENDENT pin on the wire names, which stdlib `.anthill` sources also spell.
    // Deriving the list from production would assert nothing about those names.
    val builtins = IndexedSeq(
      ("anthill.reflect", "nonvar"), ("anthill.reflect", "ground"),
      ("anthill.reflect", "qualified_name"), ("anthill.reflect", "short_name"),
      ("anthill.reflect", "lookup_symbol"), ("anthill.reflect", "not"),
      ("anthill.reflect.typing", "is_entity_of"),
      ("anthill.reflect.typing", "extract_sort_ref"),
      ("anthill.reflect", "resolve_sort_instantiation_param"),
      ("anthill.reflect", "scope"), ("anthill.reflect", "kind"),
      ("anthill.reflect", "field_access"))

    // …so a 13th builtin has to be added here too, rather than going silently unchecked.
    assertEquals(builtins.length, BuiltinTag.values.length,
      "every BuiltinTag should be listed here")

    for (nsPrefix, short) <- builtins do
      val qualName = s"$nsPrefix.$short"
      // The degrade arm interned the WHOLE spelling as one symbol, and `intern` never
      // writes `byQualifiedName` — so under it this lookup answers `None`.
      val sym = kb.tryResolveSymbol(qualName)
        .getOrElse(fail(s"`$qualName` should be a defined symbol"))
      val scope = kb.symbols.get(sym) match
        case SymbolDef.Resolved(gotShort, gotQual, kind, sc) =>
          assertEquals(gotShort, short)
          assertEquals(gotQual, qualName)
          assertEquals(kind, SymbolKind.Operation)
          sc
        case other => fail(s"`$qualName` should be resolved, got $other")
      assertEquals(kb.scopeDisplayName(scope), nsPrefix)
      // Reachable by the SHORT name from inside its namespace, which is what the scope
      // is for — a builtin in no scope is a builtin no rule body can name.
      kb.symbols.resolveInScope(short, scope) match
        case ResolveResult.Found(found) => assertEquals(found, sym)
        case other => fail(s"`$short` should resolve inside `$nsPrefix`, got $other")
  }

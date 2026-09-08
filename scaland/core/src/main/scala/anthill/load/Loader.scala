package anthill.load

import anthill.kb.{KnowledgeBase, SortKind}
import anthill.intern.{TermSymbol, SymbolTable, SymbolKind, SymbolDef, ResolveResult, ImportOrigin, FileId}
import anthill.term.{Term, TermId, Var, VarId, Literal}
import anthill.parse.*
import anthill.span.Span

import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet, LinkedHashMap}

/** Load errors.
  *
  * EVERY variant carries a span (WI-947). `Other` did not, which meant the
  * diagnostics that use it — the WI-727 variadic-capture refusals, the multi-head
  * rule refusals, the WI-949 missing-scope report — could not point anywhere even
  * in principle. A span may still be [[Span.empty]], but that is now a CLAIM the
  * raise site makes ("this has nowhere to point"), not the absence of a field.
  *
  * `scopeName` (on the two name-resolution variants) has ONE meaning, stated here because
  * three raise sites fill it and for a while they disagreed (WI-962): it is the scope the
  * name was RESOLVED AGAINST — what the reader must inspect to fix the error. All three
  * now derive it from a SYMBOL, via [[anthill.kb.KnowledgeBase.scopeDisplayName]] or
  * `qualifiedNameOf`; none composes it from a spelling, and none writes a literal. The one
  * reading a reader could misjudge, so said out loud: for a selective `import P.{n}` it is
  * `P`, the scope searched INTO, and not the importing scope, because `n` IS resolved
  * against `P` ([[Loader.resolveSelectiveImport]]) — a distinct scope, not a distinct
  * meaning. The third site filled it with the literal string `"requires"`, which named no
  * scope at all. A `String` field cannot enforce any of this, and WI-976 deliberately did
  * NOT type it: an opaque `ScopeName` would have accepted the right KIND of name computed
  * from the wrong scope — the likelier next drift — so what got typed is the SCOPE
  * ([[anthill.intern.SymbolTable.ScopeId]]), which is what every filler now derives its name
  * from. */
enum LoadError:
  case UnresolvedName(name: String, span: Span, scopeName: String)
  case UnresolvedImport(path: String, span: Span)
  case AmbiguousSymbol(name: String, candidates: IndexedSeq[String], span: Span, scopeName: String)
  /** WI-1009: an expression or pattern form reached a position the loader lowers to a KB
    * TERM (a rule head or body goal, a fact, a constraint). Scaland loads declarations
    * only — it has no expression→reflect translation — so the form cannot be lowered, and
    * this refusal is what the alternatives were: the marker's functor either CAPTURED the
    * reflect entity of the same spelling or LEAKED as an undeclared predicate, decided by
    * nothing but whether the two vocabularies happened to agree. See [[ExprMarker]]. */
  case ExpressionInTermPosition(marker: ExprMarker, span: Span)
  case Other(message: String, span: Span)

  /** WI-947: `file:line:col: message`, through the ONE located renderer that
    * [[anthill.parse.ParseError.render]] also uses — so a load error and a parse
    * error at the same character render identically by construction, not by
    * convention. A locationless variant degrades to the bare message;
    * [[Span.render]] owns that rule.
    *
    * IT IS ALSO `toString` (below), which is how it reaches consumers: scaland has
    * no CLI or driver, so nothing in this tree calls `Loader.loadAll` outside tests,
    * and a `render` reachable only by name would have been a seam with no user. As
    * `toString` it is what every `s"$errs"` and `mkString` already prints, in this
    * tree and in a downstream one. Mirrors rustland, where `LoadError` puts the same
    * rendering behind `Display`. */
  def render: String = this match
    case UnresolvedName(name, span, scopeName) =>
      span.render(s"unresolved name '$name' in scope '$scopeName'")
    case UnresolvedImport(path, span) =>
      span.render(s"unresolved import '$path'")
    case AmbiguousSymbol(name, candidates, span, scopeName) =>
      span.render(s"ambiguous symbol '$name' in scope '$scopeName': candidates ${candidates.mkString(", ")}")
    case ExpressionInTermPosition(marker, span) =>
      span.render(
        s"${marker.description} cannot be loaded as a term — scaland loads declarations " +
        s"only and does not translate expressions into the reflect encoding " +
        s"(parse marker '${marker.functorName}')")
    case Other(message, span) =>
      span.render(message)

  override def toString: String = render

/** IR → KB loading.
  *
  * Converts parsed files into KnowledgeBase terms and facts.
  * Two phases: scanDefinitions (define all names) then load (fill KB).
  */
object Loader:

  /** Scan all parsed files to define symbols and build scope chain. */
  def scanDefinitions(kb: KnowledgeBase, files: IndexedSeq[ParsedFile]): ArrayBuffer[LoadError] =
    val errors = ArrayBuffer.empty[LoadError]

    // WI-1074 — one FileId per file, minted ahead of every pass so the scan and the
    // load phase (which re-asks [[SymbolTable.fileIdOf]] on the same instance) share
    // one id per file. Every per-file loop below says whose text it resolves on
    // behalf of; the scan clears the cursor on the way out.
    val fileIds = files.map(kb.symbols.fileIdOf)

    // Pass 1: Define all names
    for (file, fid) <- files.zip(fileIds) do
      kb.symbols.setAskingFile(Some(fid))
      walkScopes(DefinePass(kb, file.symbols), file.items)

    // Pass 1b (proposal 061): the PREDICATES body-less rules declare. A separate walk,
    // after every other name in every file exists — see [[DeclarePredicatePass]] for why
    // scaland cannot interleave it the way rustland does.
    for (file, fid) <- files.zip(fileIds) do
      kb.symbols.setAskingFile(Some(fid))
      walkScopes(DeclarePredicatePass(kb, file.symbols, file.terms, errors), file.items)

    // Pass 2: Process requires and imports (all sorts exist now). A Selective
    // import of an AUTO-DECLARED predicate cannot resolve here — its head-functor symbol
    // is not registered until pass 3 — so such names are deferred into `pending` and
    // retried below (WI-295). A predicate a body-less rule DECLARES is not one of those
    // since proposal 061: pass 1b minted it above, so it resolves here like any other
    // declared name.
    val pending = ArrayBuffer.empty[PendingImport[kb.ScopeId]]
    for (file, fid) <- files.zip(fileIds) do
      kb.symbols.setAskingFile(Some(fid))
      walkScopes(ImportPass(kb, file.symbols, errors, pending, ImportOrigin.File(fid)), file.items)

    // Post-pass: auto-import prelude sort contents into global scope. BEFORE pass 3,
    // and that ordering is load-bearing: pass 3's mint guard asks whether a head's
    // name ALREADY denotes, so every name a declaration provides must be visible
    // first. Otherwise `rule eq_refl: eq(?a, ?a) <=> true` (stdlib `eq.anthill`,
    // where `eq` is PartialEq's declared operation reached through the requires
    // chain) mints a SECOND `eq` and makes the real one ambiguous. rustland reaches
    // the same state by registering the prelude before `scan_definitions` runs.
    autoImportPrelude(kb)

    // Pass 3: register the functors that RULE HEADS introduce (WI-894/896/898), in
    // THREE phases — collect, freeze, mint. WI-20260821-SBZ2A ports WI-980 / 059 R6 and
    // WI-20260822-845G7 from rustland; `docs/kernel-language.md` §"A rule head functor
    // is resolved, not declared" states the rule for both implementations.
    //
    // WHY THE PASS IS SPLIT. Deciding a head is ASKING THE LADDER, and this is the only
    // pass whose own work changes what the ladder answers — so a single walk that minted
    // as it went asked its question against a half-built table: `namespace demo { rule
    // p(1) :- true  sort Rec { rule p(2) :- true } }` loaded as ONE predicate with two
    // clauses when the namespace-level rule came first and as TWO when it came second,
    // and the same pair across two files split on whichever file was reached first. Both
    // loaded clean, and the split silently decided whether a rule EXTENDS someone else's
    // predicate. Nothing is decided now until every head is in hand.
    //
    // AND THERE IS NO OWNERSHIP DECISION LEFT TO TAKE (845G7). A head that does not
    // already DENOTE declares its predicate at the scope it is WRITTEN IN, full stop —
    // so no order can enter, and order-freedom is a property of the rule rather than a
    // result computed over the finished program. What replaced the decision is a
    // REFUSAL: two scopes that can see each other may not both introduce one name
    // ([[headNameCollisions]]), because a second scope's same-named head is a SHADOW
    // rather than a clause and inventing one silently is the defect.
    //
    // Runs after pass 2 because a head that ALREADY DENOTES references what it resolves
    // to and introduces nothing — the ladder must see every import and every `requires`
    // first.
    val heads = ArrayBuffer.empty[RuleHeadSite[kb.ScopeId]]
    for ((file, fid), fileIdx) <- files.zip(fileIds).zipWithIndex do
      kb.symbols.setAskingFile(Some(fid))
      walkScopes(RuleHeadCollectPass(kb, file.symbols, file.terms, fileIdx, heads, errors), file.items)

    // PHASE 2 — every ladder answer read off the PRE-MINT table, in full, before phase 3
    // starts. That is what makes them order-free. WI-995: imports are file-local, so
    // each is asked on behalf of the file the HEAD is written in.
    val headSites = heads.toIndexedSeq
    val denotes: IndexedSeq[Boolean] = headSites.map { h =>
      kb.symbols.setAskingFile(Some(fileIds(h.fileIdx)))
      kb.symbols.resolveInScope(h.name, h.scope).denotes
    }

    // PHASE 3 — DECIDE, then mint. Deciding reads the table and minting writes it, so
    // they cannot interleave: [[headNameCollisions]] sees a scope through a per-scope
    // SENTINEL symbol, and no mint has happened when any of its answers is taken.
    val collided = reportHeadNameCollisions(kb, headSites, denotes, fileIds, errors)
    reportPredicateHeadsSpanningFiles(kb, headSites, denotes, collided, errors)
    for (head, denoted) <- headSites.zip(denotes) if !denoted do
      kb.symbols.setAskingFile(Some(fileIds(head.fileIdx)))
      scanRuleGoal(kb, head)

    // Pass 4 (WI-295): retry the deferred predicate imports. Pass 3's head-functor
    // symbols are in `byQualifiedName` now, so a cross-namespace rule-predicate
    // import resolves like any declared name — erroring only if it is still unbound.
    // WI-1074: the retry runs outside the per-file loop, so each pending import
    // carries its own provenance and re-asks as the file that wrote it.
    for p <- pending do
      kb.symbols.setAskingFile(Some(p.origin.id))
      resolveSelectiveImport(kb, p.target, p.path, p.short) match
        case Some(sym) => kb.symbols.addImport(p.scope, p.short, sym, p.origin)
        // WI-962: the scope name comes off the SYMBOL, like the other two raise sites, and
        // not off `p.path` — the written import spelling. The two agree (a `define` writes
        // one qualified name into both the `byQualifiedName` key and the `SymbolDef`, and
        // that lookup is where `target` came from), but agreeing is not deriving: with the
        // spelling the field had a second source that could drift, which is the whole
        // failure this WI is about. `path` is a resolution INPUT here, nothing else.
        case None =>
          errors += LoadError.UnresolvedName(p.short, p.span, kb.qualifiedNameOf(p.target))

    // WI-1074 — the scan is over; nothing after it asks on one file's behalf until the
    // load phase sets the cursor again.
    kb.symbols.setAskingFile(None)
    errors

  /** Load a parsed file into the KB (Phase 2 — after scanDefinitions).
    *
    * WI-1074 — sets the asking file and LEAVES it set: the shipped shape is
    * load-then-resolve on that file's behalf (a test loads a fixture and then asks the
    * KB about the names its text imported), so clearing here would make every import
    * the file itself wrote invisible to the resolution that follows — a name imported
    * one line earlier answering `NotFound`, with nothing to distinguish "not yours"
    * from "no such name". Mirrors rustland's `scan_definitions`, which leaves the
    * cursor on its last source for the query path.
    *
    * THE COROLLARY, stated because a caller can only see it by tracing this method:
    * after [[loadAll]] the cursor is the LAST file's, so a post-load `resolveInScope`
    * answers as that file — which is what the load-a-fixture-then-ask tests mean, and
    * an ORDER ARTIFACT for any other caller. A caller resolving on a different file's
    * behalf (or on none) sets the cursor itself via
    * [[anthill.intern.SymbolTable.setAskingFile]]. */
  def load(kb: KnowledgeBase, file: ParsedFile): ArrayBuffer[LoadError] =
    val errors = ArrayBuffer.empty[LoadError]
    kb.symbols.setAskingFile(Some(kb.symbols.fileIdOf(file)))
    walkScopes(LoadPass(kb, file.symbols, file.terms, errors), file.items)
    errors

  /** Load multiple files: scan first, then load all. */
  def loadAll(kb: KnowledgeBase, files: IndexedSeq[ParsedFile]): ArrayBuffer[LoadError] =
    val errors = scanDefinitions(kb, files)
    for file <- files do
      errors ++= load(kb, file)
    errors

  // ── The scope spine ──────────────────────────────────────────

  /** A declaration that OPENS a child scope. Both carry a name, an import list and a
    * body, which is all the walk needs; only the pass that DEFINES a scope has to tell
    * the two apart, so `ScopeDecl` keeps that distinction available without making
    * every pass re-derive it from `Item`. */
  private enum ScopeDecl(
    val name: Name, val imports: IndexedSeq[Import], val items: IndexedSeq[Item]
  ):
    case Ns(ns: Namespace) extends ScopeDecl(ns.name, ns.imports, ns.items)
    case SortBody(sort: SortWithBody) extends ScopeDecl(sort.name, sort.imports, sort.items)

  /** One pass over the scope spine.
    *
    * `walkScopes` owns the descent — qualify the short name against the enclosing
    * prefix, obtain the child scope, recurse with the new (scope, prefix) pair — so a
    * pass supplies only what it does AT a scope (`enterScope`, which yields the scope to
    * recurse into) and at every other item (`atItem`, in the scope that encloses it).
    *
    * WI-949: ONE walker, not one per pass. The four scan passes and the loader each
    * re-spelled this recursion, which is how the WI-853 top-level-import arm and the
    * WI-295 `pending` buffer had to be threaded through separate copies in lockstep —
    * and how the copies came to disagree about a scope that is missing (see
    * `lookupScope`, which is now the single answer). */
  private trait ScopePass:
    /** The KB being loaded into, and a `val` so `kb.ScopeId` is a type (WI-1004): a scope
      * identity belongs to the table that issued it, so every scope this pass sees is one
      * of THIS KB's — which is what the walk's `pass.kb.ScopeId` says, and what the two
      * tables a pass holds (`kb.symbols` and [[fileSym]]) can no longer be confused over. */
    val kb: KnowledgeBase

    /** The parse-time symbol table of the file being walked — names are file-local. */
    def fileSym: SymbolTable

    /** The child scope to recurse into, or `None` to abandon the subtree (only ever
      * because the scope could not be found, which `lookupScope` has already reported).
      *
      * `writtenName` is the name AS WRITTEN, which is the short name only when it has no
      * dot; `prefix` is the enclosing scope's qualified path, the same one `atItem` gets.
      * Only [[DefinePass]] reads either — a WRITTEN name may be DOTTED, and then the segments
      * before the last are namespaces the declaration goes INTO ([[ensureNamespacePath]],
      * WI-992), each qualified against this prefix in turn. The three lookup passes need
      * only `qualName`, which is where that walk ends up either way. */
    def enterScope(
      decl: ScopeDecl, writtenName: String, qualName: String, prefix: String,
      enclosing: kb.ScopeId
    ): Option[kb.ScopeId]

    /** Every item that does not open a scope, with the scope and prefix enclosing it.
      *
      * WI-1007: [[LoadPass]]'s implementation is EXHAUSTIVE and the other three end in a
      * catch-all, which is a decision and not drift. `LoadPass` is the pass whose job is
      * "everything that reaches the KB reaches it here", so an `Item` kind it does not
      * name is data loss — that is how `ConstraintItem` was found being dropped in
      * silence. The other three are narrow scans (`DefinePass` defines names,
      * `ImportPass` handles imports, `DeclarePredicatePass` and `RuleHeadCollectPass`
      * handle 2 of 23 kinds each), where a
      * catch-all says "not my job" honestly and enumerating would be 18 arms of noise. */
    def atItem(item: Item, scope: kb.ScopeId, prefix: String): Unit

  /** Walk a whole file for one pass, from the scope its top-level declarations land in.
    *
    * The PASS comes first and the starting scope is not a parameter at all (WI-1004). Both
    * follow from the scope type: it is `pass.kb.ScopeId`, so `pass` has to be named before
    * the walk's scope can be typed. All four call sites passed `kb.globalScope` and `""`,
    * so the start lives here rather than four times over — one fewer thing a pass can
    * start differently from the others. */
  private def walkScopes(pass: ScopePass, topItems: Iterable[Item]): Unit =
    // Nested, so the recursion closes over `pass` instead of re-threading it — and so the
    // scope type is written once.
    def walk(items: Iterable[Item], scope: pass.kb.ScopeId, prefix: String): Unit =
      for item <- items do
        val opened = item match
          case Item.NamespaceItem(ns) => Some(ScopeDecl.Ns(ns))
          case Item.SortWithBodyItem(sort) => Some(ScopeDecl.SortBody(sort))
          case _ => None
        opened match
          case Some(decl) =>
            val writtenName = joinSegments(pass.fileSym, decl.name.segments)
            val qualName = makeQualified(prefix, writtenName)
            pass.enterScope(decl, writtenName, qualName, prefix, scope).foreach { child =>
              walk(decl.items, child, qualName)
            }
          case None => pass.atItem(item, scope, prefix)

    walk(topItems, pass.kb.globalScope, "")

  /** The symbol `qualName` names, which `DefinePass` defined before any later pass ran.
    * A MISS is therefore a broken invariant, not a shape a pass may skip — and this is
    * the ONE place that answers it, for every pass and every kind of name: report, and
    * say what the miss costs. Skipping instead would drop the work with no diagnostic at
    * all, which is exactly the silent skip the project forbids. Before WI-949 the copies
    * disagreed: pass 2 and the loader skipped, pass 3 reported. */
  private def lookupDefined(
    kb: KnowledgeBase, qualName: String, span: Span, consequence: String, errors: ArrayBuffer[LoadError]
  ): Option[TermSymbol] =
    // A `match` and not `.orElse { errors += … ; None }`: the combinator form is correct
    // only because `orElse`'s parameter is by-name, so the raise lives one strict-argument
    // refactor away from firing on EVERY successful lookup — once per declaration, in the
    // one helper four passes share.
    kb.symbols.byQualifiedName.get(qualName) match
      case some @ Some(_) => some
      case None =>
        // WI-947: the DECLARATION's span, not the missing name's — the name is missing
        // from the symbol table, so there is nothing to point at on that side; what the
        // reader needs is the declaration whose contents were dropped.
        errors += LoadError.Other(
          s"internal: '$qualName' was not defined in pass 1, so $consequence", span)
        None

  /** The scope `qualName` names — the descent's use of [[lookupDefined]]. A miss here
    * abandons the whole subtree: its imports unwired, its rule heads unregistered, its
    * facts and rules never loaded. */
  private def lookupScope(
    kb: KnowledgeBase, qualName: String, span: Span, errors: ArrayBuffer[LoadError]
  ): Option[kb.ScopeId] =
    lookupDefined(kb, qualName, span, "the declarations inside it cannot be loaded", errors)
      .map(kb.symbols.scopeOf)

  // ── Pass 1: Define names ─────────────────────────────────────

  /** Pass 1 — DEFINE every name. The pass that creates the scopes the others look up,
    * so its `enterScope` defines rather than resolving, and can never miss.
    *
    * A PREDICATE IS NOT DEFINED HERE, and that is a scaland-specific ordering rather than
    * a difference of rule — see [[DeclarePredicatePass]], the sub-pass that follows this
    * one. */
  private final class DefinePass(val kb: KnowledgeBase, val fileSym: SymbolTable) extends ScopePass:

    def enterScope(
      decl: ScopeDecl, writtenName: String, qualName: String, prefix: String, enclosing: kb.ScopeId
    ): Option[kb.ScopeId] =
      // WI-992: a DOTTED name declares into the namespace it names, not into `enclosing`
      // under its whole spelling. `enclosing` stays the scope the TYPE-PARAM marker is
      // added to below — that is a property of the syntactic nesting, not of the name.
      val (short, target) = ensureNamespacePath(kb, writtenName, enclosing, prefix)
      decl match
        case ScopeDecl.Ns(_) =>
          val sym = kb.symbols.define(short, qualName, SymbolKind.Namespace, target)
          val nsScope = kb.symbols.scopeOf(sym)
          // Enclosing scope. (Model C / proposal 044: names visible by default;
          // the `export` statement was removed in WI-291.)
          kb.symbols.addParent(nsScope, target, isEnclosing = true)
          Some(nsScope)

        case ScopeDecl.SortBody(sort) =>
          val sym = kb.symbols.define(short, qualName, SymbolKind.Sort, target)
          val sortScope = kb.symbols.scopeOf(sym)
          kb.registerSort(kb.makeNameTermFromSym(sym), SortKind.Defined)
          kb.symbols.addParent(sortScope, target, isEnclosing = true)
          // Variant exposure (proposal 044 job 2): a sort exposes ONLY its
          // entity-variant names to the enclosing scope, linked as a
          // non-enclosing parent — so bare `Open` resolves to `WorkStatus.Open`
          // while operations never leak as bare names. (Names are visible by
          // default; the `export` statement was removed in WI-291.)
          val variants = sort.items.collect {
            case Item.EntityItem(e) => joinSegments(fileSym, e.name.segments)
          }
          for v <- variants do kb.symbols.addExposed(sortScope, v)
          // WI-M460D — `addExposureParent`, so the link carries the clause that wrote
          // it. Before it, this link and a `requires` one were one shape
          // (`isEnclosing = false`) and the resolver told them apart by whether the far
          // scope happened to declare variants.
          if variants.nonEmpty then
            kb.symbols.addExposureParent(target, sortScope)
          // WI-452 (§5.4): a MARKED structured param (`sort [F] { … }`, the
          // higher-kinded carrier of `sort Spec[F[T]]`) is a NON-RIGID type
          // parameter of the enclosing sort — register it like the `sort T = ?`
          // abstract-sort arm below. An UNMARKED `sort F { … }` stays a concrete
          // nested sort. (scaland emits no `SortAlias` backing-var fact — it has
          // no typer; the type-param marker is what the resolver and codegen read.)
          if sort.isTypeParam && isSortScope(kb, enclosing) then
            kb.symbols.addTypeParam(enclosing, short)
          Some(sortScope)

    def atItem(item: Item, scope: kb.ScopeId, prefix: String): Unit =
      item match
        case Item.AbstractSortItem(sort) =>
          // `sort T = ?` inside a SortWithBody (or enum) declares a type
          // parameter local to the enclosing sort; `sort T = Concrete` is an
          // ordinary abstract sort. Only the variable form is a parameter.
          val isParam = sort.definition.isInstanceOf[TypeExpr.Variable]
          defineAbstractSort(kb, fileSym, prefix, scope, sort.name.segments, isParam)

        case Item.EntityItem(entity) =>
          val (shortName, qualName, target) = declSite(kb, fileSym, entity.name.segments, prefix, scope)
          val sym = kb.symbols.define(shortName, qualName, SymbolKind.Entity, target)
          val entityTerm = kb.makeNameTermFromSym(sym)
          kb.registerSort(entityTerm, SortKind.Constructor)
          // WI-985: the entity→parent edge is a SORT-BODY edge and ONLY that. This used
          // to record the enclosing scope whatever it was, so an `entity` written
          // directly under a namespace — which §4 of the spec permits — got that
          // NAMESPACE as its parent sort, and `is_entity_of` then answered true of a
          // namespace. The stdlib depends on the opposite: `reflect/typing.anthill`'s
          // `entity_of` rule guards `scope(?x, ?sort)` with the `is_entity_of` builtin
          // precisely so a namespace-level entity yields NO parent, and rustland
          // registers the edge only from inside its sort-body loop (`kb/load.rs`) —
          // `load_entity` emits the metadata fact and no edge. An entity outside a sort
          // body is still an entity and still a constructor; it just has no parent sort
          // to name, so nothing is recorded rather than something false.
          if isSortScope(kb, scope) then
            kb.registerEntityOf(entityTerm, kb.scopeTerm(scope))
          // Register entity fields
          val fields = entity.fields.map(f => fileSym.name(f.name)).map(kb.intern)
          kb.registerEntityFields(sym, fields)

        case Item.OperationItem(op) =>
          val (shortName, qualName, target) = declSite(kb, fileSym, op.name.segments, prefix, scope)
          defineSymbolOnce(kb, shortName, qualName, SymbolKind.Operation, target)

        // A BLOCK entry takes no `declSite` — its name is a simple one by construction
        // (`operation { eq(a, b) -> Bool, … }` names members of the sort the block is
        // written in), and rustland's pass 1 leaves this arm flat for the same reason.
        case Item.OperationBlockItem(block) =>
          for op <- block.entries do
            val shortName = joinSegments(fileSym, op.name.segments)
            val qualName = makeQualified(prefix, shortName)
            defineSymbolOnce(kb, shortName, qualName, SymbolKind.Operation, scope)

        case Item.ConstItem(c) =>
          // Proposal 039 / WI-084: define the constant's symbol (pass 1, like
          // operations). Monomorphic + carrier-independent — no params or
          // type-params to scan. The symbol is ALL that is recorded; why the declared
          // type and the value are not is stated once, at the seam they would enter —
          // `LoadPass.atItem`'s WI-1007 arm.
          val (shortName, qualName, target) = declSite(kb, fileSym, c.name.segments, prefix, scope)
          defineSymbolOnce(kb, shortName, qualName, SymbolKind.Const, target)

        // The LABEL only. A rule's label is a citation handle (`using X`) and exists
        // whatever the rule reads as; the PREDICATE a body-less rule declares is minted
        // one sub-pass later ([[DeclarePredicatePass]]).
        case Item.RuleItem(rule) => defineRuleLabel(rule, scope, prefix)

        case Item.RuleBlockItem(block) =>
          for rule <- block.entries do defineRuleLabel(rule, scope, prefix)

        // WI-840 (proposal 058 §4.7): a NAMED requirement slot — `requires O: Ord[T]`
        // — declares a type PARAMETER of the enclosing sort, which is what lets the
        // chosen witness enter the type (`SortedSet[T = String, O = ByLength]`); an
        // ANONYMOUS slot stays a constraint and defines nothing. rustland reaches the
        // same state by desugaring the named form into `sort O = ?` at convert time;
        // scaland's `declaration` yields one `Item` per production, so the binder
        // rides on the item and this arm does what the `AbstractSortItem` arm would
        // have. Outside a sort scope the binder has nothing to parameterize, so it
        // defines no symbol (rustland raises there; scaland has no operation-level
        // diagnostics to sit beside it).
        case Item.RequiresDeclItem(req) =>
          // A NAMED slot IS `sort O = ?`, so it goes through the SAME registration —
          // one implementation of "an abstract sort that is a type parameter of its
          // enclosing sort", not two. rustland reaches this state by desugaring the
          // binder into an `AbstractSort` item at CONVERT time; scaland's
          // `declaration` yields one `Item` per production, so the binder rides on
          // the item and the shared helper is applied here instead.
          req.binder.foreach { binder =>
            defineAbstractSort(kb, fileSym, prefix, scope, binder.segments, isParam = true)
          }

        case _ => // Other items don't define symbols in pass 1

    private def defineRuleLabel(rule: Rule, scope: kb.ScopeId, prefix: String): Unit =
      rule.label.foreach { label =>
        val shortName = joinSegments(fileSym, label.segments)
        kb.symbols.define(shortName, makeQualified(prefix, shortName), SymbolKind.Rule, scope)
      }

  /** Pass 1b (proposal 061, WI-20260821-SBZ2A) — DEFINE THE PREDICATES BODY-LESS RULES
    * DECLARE. A predicate was the only name in the language created as a side effect of
    * USING it, so the pass that decided its binding was the pass that created it; every
    * other name kind is immune because pass 1 defines all of them across every file
    * before anything resolves anything (WI-321). A declaration gives the head something
    * to land on, put there like every other name, so WHEN pass 3's ladder is asked stops
    * mattering.
    *
    * A SEPARATE WALK, AND THAT IS SCALAND-SPECIFIC. rustland mints a declaration inside
    * pass 1 itself, which is safe there because a symbol carries a kind SET —
    * `SymbolDef::Resolved.kinds: SmallVec<[SymbolKind; 2]>` with `add_kind`, so a
    * repeated `(name, scope)` ACCUMULATES roles. Here [[anthill.intern.SymbolDef]] has a
    * single `kind` field and no merge: `define` returns the existing symbol and keeps
    * whichever kind got there first. (scaland records a name's OTHER roles in separate
    * registries instead — `SortKind` per sort TERM, `constructorSymbols_`,
    * `entityParent_` — one role each, never a set on the symbol.)
    *
    * SO AN INTERLEAVED WALK LET THE TEXT ORDER DECIDE THE KIND: MEASURED,
    * `operation has(x) -> Bool` beside `rule has(?x)` was refused with the operation
    * written first and LOADED CLEAN with the rule written first, stamping `has` a `Goal`
    * and silently swallowing the no-op line. Deferring every declaration until every
    * other name in every file exists restores the WI-321 invariant for this kind too:
    * whatever else declares the name, it is already there.
    *
    * THE OTHER FIX WOULD BE A KIND SET, and it is worth naming rather than leaving as an
    * unstated road not taken: give scaland's `SymbolDef` rustland's `kinds` and this pass
    * folds back into pass 1. That is a change to every one of the ~20 sites that
    * pattern-match `SymbolDef.Resolved` by kind, so it is a ticket of its own, not this
    * one's to take.
    *
    * BEFORE PASS 2, so a selective `import P.{p}` of a DECLARED predicate resolves like
    * any other declared name rather than through pass 4's deferred retry. */
  private final class DeclarePredicatePass(
    val kb: KnowledgeBase,
    val fileSym: SymbolTable,
    fileTerms: SimpleTermStore,
    errors: ArrayBuffer[LoadError]
  ) extends ScopePass:

    def enterScope(
      decl: ScopeDecl, writtenName: String, qualName: String, prefix: String, enclosing: kb.ScopeId
    ): Option[kb.ScopeId] =
      lookupScope(kb, qualName, decl.name.span, errors)

    def atItem(item: Item, scope: kb.ScopeId, prefix: String): Unit =
      item match
        case Item.RuleItem(rule) => declare(rule, scope, prefix)
        case Item.RuleBlockItem(block) => for rule <- block.entries do declare(rule, scope, prefix)
        case _ =>

    /** [[defineSymbolOnce]], like every other declaration mint in this loader. Its gate
      * is `define`'s UNCONDITIONAL `byQualifiedName` write, reached "by any route to a
      * colliding qualified name" (see its doc) — and this pass is a new such route, so
      * exempting it would reopen exactly what that gate is for. rustland's `scan_rule`
      * writes a plain `define` here; it can, because its `SymbolTable::define` merges a
      * kind SET onto a repeated `(name, scope)` and scaland's keeps the first kind.
      *
      * IT COSTS NOTHING THE DECLARATION NEEDS. Two declarations of one predicate at one
      * scope stay idempotent (the second finds the qualified name registered), and
      * another construct's kind is still left in place for
      * [[refuseDeclarationThatCannotStand]] to find (the operation's mint got there
      * first). What changes is only the unreachable case the gate exists for, and it
      * changes it from a silent remapping to that method's loud
      * "was never brought into existence". */
    private def declare(rule: Rule, scope: kb.ScopeId, prefix: String): Unit =
      if ruleReading(rule, fileSym, fileTerms) == RuleReading.Declaration then
        // A `Declaration` reading is reached only through the `Some((_, Goal))` arm of
        // that very call, so a `None` here would mean the two disagree — which is the
        // defect this pairing exists to make impossible. Raised rather than skipped.
        ruleIntroducedFunctor(rule, fileSym, fileTerms) match
          case Some((name, kind)) =>
            defineSymbolOnce(kb, name, makeQualified(prefix, name), kind, scope)
          case None =>
            throw AssertionError(
              "internal: a Declaration reading must name the predicate it declares")

  /** Define an ABSTRACT sort in `scope` and, when `isParam` and the scope is a
    * sort body, register it as one of that sort's TYPE PARAMETERS — the marker the
    * resolver uses to keep `T` from leaking into ambient name-resolution from sibling
    * sorts that share the canonical parameter name.
    *
    * Shared by the two surfaces that declare one (WI-840): `sort T = ?`, and a NAMED
    * requirement slot `requires O: Ord[T]` (proposal 058 §4.7), which IS a type
    * parameter of the sort that declares it. Outside a sort scope neither is a
    * parameter — a namespace has none to add to — so the symbol is defined and the
    * marker is not.
    */
  private def defineAbstractSort(
    kb: KnowledgeBase,
    fileSym: SymbolTable,
    prefix: String,
    scope: kb.ScopeId,
    segments: IndexedSeq[TermSymbol],
    isParam: Boolean
  ): Unit =
    val (shortName, qualName, target) = declSite(kb, fileSym, segments, prefix, scope)
    val sym = kb.symbols.define(shortName, qualName, SymbolKind.Sort, target)
    kb.registerSort(kb.makeNameTermFromSym(sym), SortKind.Abstract)
    // The marker goes on the SYNTACTICALLY enclosing sort — being a type parameter is a
    // property of where the declaration is written, not of where its name puts it.
    if isParam && isSortScope(kb, scope) then
      kb.symbols.addTypeParam(scope, shortName)

  /** Where a WRITTEN declaration name puts its symbol: the SHORT name it is defined
    * under, the QUALIFIED name it is registered by, and the SCOPE it lands in. The three
    * differ only for a DOTTED name, and then by [[ensureNamespacePath]] — which this may
    * therefore create namespaces as a side effect of asking. Shared by the pass-1 arms
    * whose rustland counterparts call `ensure_intermediate_namespaces` (sort, namespace,
    * abstract sort, entity, operation, const). */
  private def declSite(
    kb: KnowledgeBase,
    fileSym: SymbolTable,
    segments: IndexedSeq[TermSymbol],
    prefix: String,
    scope: kb.ScopeId
  ): (String, String, kb.ScopeId) =
    val written = joinSegments(fileSym, segments)
    val (short, target) = ensureNamespacePath(kb, written, scope, prefix)
    (short, makeQualified(prefix, written), target)

  /** The scope a DOTTED declaration name declares INTO, and the short name it declares
    * there — `sort anthill.prelude.Eq` at a file's top level declares `Eq` in the
    * namespace `anthill.prelude`. An UNDOTTED name is returned unchanged, with the scope
    * it was already going into.
    *
    * WI-992 — before this, the whole dotted spelling WAS the short name and it was
    * defined in `<global>`; nothing ever linked it to a scope called `anthill.prelude`. So
    * from inside `sort anthill.prelude.Eq` the name `PartialEq` resolved to nothing, even
    * though `sort anthill.prelude.PartialEq` sits eleven lines above it in the same file
    * — and since a `requires` here LINKS A PARENT SCOPE and is the whole of what a
    * requirement does in scaland, the requires-chain inheritance the stdlib documents
    * (WI-614: `Eq` inherits `eq`/`neq` from `PartialEq`) had never worked for any stdlib
    * spec. Two workarounds grew on the import side around the same hole; one of them
    * (`resolveSelectiveImport`'s fully-qualified rung) is gone with this.
    *
    * The intermediate namespaces are SYNTHESIZED when the source never wrote them, and
    * reused when it did — including by the next dotted declaration naming the same one,
    * which is what puts a file's sorts in ONE `anthill.prelude` rather than one each.
    * `Prelude` writes `anthill` / `anthill.prelude` / `anthill.reflect` before any file is
    * scanned, so the stdlib's dotted declarations land in exactly those.
    *
    * Settled against rustland, where `scan_items_pass1` has called
    * `ensure_intermediate_namespaces` all along: this is a scaland gap, not a language
    * question, and the answer is the one already in the other implementation. */
  private def ensureNamespacePath(
    kb: KnowledgeBase, written: String, outerScope: kb.ScopeId, prefix: String
  ): (String, kb.ScopeId) =
    val segments = written.split('.')
    if segments.length <= 1 then (written, outerScope)
    else
      val innermost = segments.init.zipWithIndex.foldLeft(outerScope) { case (scope, (short, i)) =>
        // Reuse whatever this scope already has under that short name — the same merge
        // `define` performs for a re-opened namespace. Reusing by SHORT NAME IN SCOPE and
        // not by qualified name is what makes `anthill` the one Prelude defined rather
        // than a second symbol sharing its spelling.
        kb.symbols.scope(scope).flatMap(_.locals.get(short)) match
          case Some(sym) => kb.symbols.scopeOf(sym)
          case None =>
            val qualPath = makeQualified(prefix, segments.take(i + 1).mkString("."))
            val ns = kb.symbols.scopeOf(
              kb.symbols.define(short, qualPath, SymbolKind.Namespace, scope))
            kb.symbols.addParent(ns, scope, isEnclosing = true)
            ns
      }
      (segments.last, innermost)

  /** Define a symbol of `kind` unless its qualified name is already
    * registered — mirrors rustland's `is_new` reuse gate (load.rs:1110, the
    * entity arm). Shared by operations and consts. A kernel operation such as
    * `anthill.kernel.not` is FIRST registered as a builtin by
    * `Prelude.registerBuiltinTags` (into the prelude's `anthill.kernel` scope); the
    * stdlib then ALSO declares `operation not(...)` in kernel.anthill, and minting a
    * SECOND `anthill.kernel.not` makes a bare rule-body use (`:- not(...)` in
    * typing.anthill) collect both through `resolveInScope` and report `AmbiguousSymbol`
    * (WI-212).
    *
    * WI-992 closed that case UPSTREAM: a re-opened namespace no longer scans into a fresh
    * scope, because `ensureNamespacePath` reuses the one `Prelude` already defined — so
    * `define`'s own short-name-in-scope merge now returns the builtin's symbol and mints
    * nothing. MEASURED: removing this gate moves no test. It stays because what it guards
    * is `define`'s UNCONDITIONAL `byQualifiedName` write — which happens whenever the
    * short name is new in the target scope, by any route to a colliding qualified name,
    * not only the one WI-212 hit. */
  private def defineSymbolOnce(
    kb: KnowledgeBase,
    shortName: String,
    qualName: String,
    kind: SymbolKind,
    scope: kb.ScopeId
  ): Unit =
    if !kb.symbols.byQualifiedName.contains(qualName) then
      kb.symbols.define(shortName, qualName, kind, scope)

  // ── Pass 2: Process requires/imports ─────────────────────────

  /** Pass 2 — wire the parent-scope chain: a scope's own `import` list, and the
    * `requires` declarations inside it. Runs after every name exists (pass 1), so an
    * import can name any declaration in any file. */
  private final class ImportPass(
    val kb: KnowledgeBase,
    val fileSym: SymbolTable,
    errors: ArrayBuffer[LoadError],
    pending: ArrayBuffer[PendingImport[kb.ScopeId]],
    /** WI-1074 — who this file's imports belong to. `ImportOrigin.File`, not the full
      * enum: a written import always has a writing file, and the narrower type is what
      * lets the pass-4 retry read `origin.id` with no dead arm for origins no producer
      * builds. */
    origin: ImportOrigin.File
  ) extends ScopePass:

    // The import list attached to a `namespace` and to a `sort … end` body go through
    // the SAME `processImports`; only the scope differs, and the walk already carries it.
    def enterScope(
      decl: ScopeDecl, writtenName: String, qualName: String, prefix: String, enclosing: kb.ScopeId
    ): Option[kb.ScopeId] =
      lookupScope(kb, qualName, decl.name.span, errors).map { scope =>
        processImports(kb, decl.imports, fileSym, scope, errors, pending, origin)
        scope
      }

    def atItem(item: Item, scope: kb.ScopeId, prefix: String): Unit =
      item match
        case Item.RequiresDeclItem(req) =>
          processRequires(kb, req, fileSym, scope, errors)

        // WI-869: a provision's conditions are linked HERE, in the same scan pass and
        // by the same resolution as `requires` — not at the phase-2 load, where the
        // first cut put them. A `requires` links a parent scope, that IS what a
        // requirement does in scaland, and a condition is written in the same
        // vocabulary. Measured: moving `pair.anthill`'s two `requires PartialEq`
        // clauses into conditions removed two parent links from scaland's `Pair` scope
        // until this arm existed.
        case Item.ProvidesClauseItem(pc) =>
          processProvidesConditions(kb, pc, fileSym, scope, errors)
          processProvidesHead(kb, pc, fileSym, scope, errors)

        // WI-727 (proposal 056): "at most one variadic capture parameter, and
        // trailing" is checked HERE and not in the parser — the diagnostic quotes the
        // QUALIFIED operation name, which only the loader has. Mirrors rustland's
        // `load.rs` check. Both spellings reach it: a free operation and one written
        // inside a braced `operation { … }` block.
        case Item.OperationItem(op) =>
          checkVariadicCapture(fileSym, prefix, op, errors)

        case Item.OperationBlockItem(block) =>
          for op <- block.entries do checkVariadicCapture(fileSym, prefix, op, errors)

        // WI-853: a TOP-LEVEL import feeds `<global>` — the scope a file's top-level
        // declarations are defined in. Same `processImports` the namespace-attached
        // and sort-attached lists go through; only the scope differs, and it is
        // already the one this walk carries.
        //
        // Only ever the top level: inside a namespace / sort body the parser's
        // `bodyContent` consumes an `import` before `declaration` is tried, so it
        // lands in that body's `imports` list and never reaches this arm as an Item.
        //
        // WI-1074 — `<global>` is ONE address every file writes, which made a top-level
        // import the widest reach a file had into text it never saw. It carries the
        // same file origin as any other import now: global in PLACE, local in WHO SEES
        // IT. (Rustland's wi853 test was inverted by WI-995 the same way.)
        case Item.ImportItem(imp) =>
          processImports(kb, Seq(imp), fileSym, scope, errors, pending, origin)

        case _ =>

  /** WI-727: a variadic capture (`...args: R`) must be the operation's LAST
    * parameter, and there may be at most one. Messages mirror rustland's, which
    * names the operation the same way. */
  private def checkVariadicCapture(
    fileSym: SymbolTable, prefix: String, op: Operation, errors: ArrayBuffer[LoadError]
  ): Unit =
    val captures = op.params.filter(_.rest)
    val opQualified = makeQualified(prefix, joinSegments(fileSym, op.name.segments))
    // WI-947: each refusal points at the OFFENDING capture — the second one for the
    // count, the misplaced one for the position — not at the operation as a whole.
    if captures.length > 1 then
      errors += LoadError.Other(
        s"operation '$opQualified': at most one variadic capture parameter (`...`) is allowed",
        captures(1).span)
    else if captures.length == 1 && !op.params.last.rest then
      errors += LoadError.Other(
        s"operation '$opQualified': a variadic capture parameter (`...`) must be the LAST parameter",
        captures.head.span)

  // ── Pass 3: rule-introduced functors ─────────────────────────

  /** ONE RULE HEAD, its introduced name already read off the head, waiting for the
    * decision — sub-pass 3's unit of work since the pass was split in three
    * (WI-20260821-SBZ2A). The split exists because deciding a head is *asking the
    * ladder*, and this is the only pass whose own work changes what the ladder answers.
    *
    * PARAMETERIZED BY THE SCOPE TYPE for the reason [[PendingImport]] is (WI-1004): a
    * scope identity belongs to the table that issued it, and this record is held outside
    * [[anthill.intern.SymbolTable]].
    *
    * `fileIdx` indexes `scanDefinitions`' own `files`/`fileIds` — the file this head is
    * WRITTEN in, so the decision can be taken on that file's behalf (imports are
    * file-local, WI-995) and the 061 file rule can count files. `span` is the RULE's own
    * span, which carries the file name a refusal prints. */
  private case class RuleHeadSite[S](
    fileIdx: Int, scope: S, prefix: String, name: String, kind: SymbolKind, span: Span
  )

  /** Sub-pass 3, PHASE 1 — read each rule head's introduced name and remember WHERE it
    * is written. Takes no decision and mints nothing, so nothing it does depends on the
    * order it runs in; [[scanRuleGoal]] is the mint.
    *
    * WI-894/896/898 is what the mint is FOR. `ite` is the motivating case —
    * `bool.anthill` declares no `ite` operation; its two `[simp]` equations ARE its
    * definition, and `int64.anthill` / `ordered.anthill` reach it by `import
    * anthill.prelude.Bool.{ite}`. Without the mint that import resolves to nothing,
    * which is how the whole stdlib failed to load. */
  private final class RuleHeadCollectPass(
    val kb: KnowledgeBase,
    val fileSym: SymbolTable,
    fileTerms: SimpleTermStore,
    fileIdx: Int,
    sites: ArrayBuffer[RuleHeadSite[kb.ScopeId]],
    errors: ArrayBuffer[LoadError]
  ) extends ScopePass:

    def enterScope(
      decl: ScopeDecl, writtenName: String, qualName: String, prefix: String, enclosing: kb.ScopeId
    ): Option[kb.ScopeId] =
      lookupScope(kb, qualName, decl.name.span, errors)

    def atItem(item: Item, scope: kb.ScopeId, prefix: String): Unit =
      item match
        case Item.RuleItem(rule) => collect(rule, scope, prefix)
        case Item.RuleBlockItem(block) => for rule <- block.entries do collect(rule, scope, prefix)
        case _ =>

    private def collect(rule: Rule, scope: kb.ScopeId, prefix: String): Unit =
      for (name, kind) <- ruleIntroducedFunctor(rule, fileSym, fileTerms) do
        sites += RuleHeadSite(fileIdx, scope, prefix, name, kind, rule.span)

  /** Sub-pass 3, PHASE 3 — the MINT, and no longer the DECISION.
    *
    * WI-894 — A RULE DOES NOT TRAVEL TO THE GLOBAL NAMESPACE FROM ITS PLACE. A name a
    * rule introduces belongs to the scope the rule is WRITTEN IN: the sort when written
    * inside a sort, the namespace when written at namespace level — the same rule every
    * other member (`operation`, `entity`, `const`) follows. A functor with no scoped
    * symbol falls to the bare `intern(name)` fallback, which is ONE GLOBAL NAME: two
    * sorts defining the same short name then share one definition and the loser's own
    * laws are ignored INSIDE ITS OWN SORT, on a program that loads clean.
    *
    * WI-898 — WHICH KIND the fresh symbol gets travelled with the name from the same
    * head walk that picked it ([[ruleIntroducedFunctor]]), so no second walk can
    * disagree.
    *
    * `defineSymbolOnce`, not `define`: `define` writes `byQualifiedName` for the
    * qualified name UNCONDITIONALLY whenever the SHORT name is new in the target scope,
    * so a rule head in a re-opened namespace could replace a builtin's mapping (the case
    * that gate was written for — see its doc).
    *
    * NO RE-CHECK OF THE LADDER HERE. The caller passes only heads whose frozen phase-2
    * answer was `NotFound`; re-asking would put the question back against the table THIS
    * LOOP IS FILLING, which is the defect the split removes. Two heads of one name at one
    * scope are two clauses of one predicate, and `defineSymbolOnce` is already idempotent
    * for them. */
  private def scanRuleGoal(kb: KnowledgeBase, site: RuleHeadSite[kb.ScopeId]): Unit =
    defineSymbolOnce(kb, site.name, makeQualified(site.prefix, site.name), site.kind, site.scope)

  /** How many scope names a collision message prints before it says "… and N more".
    * Mirrors rustland's `COLLISION_SCOPES_SHOWN`. */
  private val CollisionScopesShown = 6

  /** ONE NAME INTRODUCED AT TWO SCOPES THAT CAN SEE EACH OTHER — the whole of what
    * rustland's deleted `Ownership` fixpoint used to DECIDE, now a report.
    *
    * `owner` is the scope a declaration belongs at when one place collects every head:
    * the member that EVERY other member reaches FROM EVERY FILE it writes a head in.
    * `None` where no member does — a chain (a wildcard import is not re-exported) or two
    * siblings a third scope imports — and the message then prescribes a per-scope
    * declaration instead. */
  private case class HeadNameCollision[S](
    name: String, scopes: IndexedSeq[S], owner: Option[S], sites: IndexedSeq[Int]
  )

  /** Mint one sentinel per scope that writes a rule head — a symbol standing for "a head
    * is written here", so the resolver can be told about names that are not symbols yet.
    *
    * PER SCOPE, not one shared sentinel: the walk deduplicates its matches by symbol, so
    * one sentinel for every scope would collapse two distinct owners into a single
    * `Found` and the group would lose a member. The spelling is unspellable by any
    * identifier token, like [[anthill.intern.GLOBAL_SCOPE_NAME]], so it can never be a
    * name a program writes. */
  private def mintHeadSentinels(
    kb: KnowledgeBase, sites: Seq[RuleHeadSite[kb.ScopeId]]
  ): Map[kb.ScopeId, TermSymbol] =
    sites.map(_.scope).distinct
      .sortBy(sc => TermSymbol.raw(kb.symbols.symbolOf(sc)))
      .zipWithIndex
      .map((sc, i) => sc -> kb.intern(s"<head-present:$i>"))
      .toMap

  /** WHAT A HEAD NAMED `name`, WRITTEN AT `scope` IN `file`, CAN SEE among the scopes
    * that introduce that name — with every candidate overlaid as though its head were
    * already a symbol.
    *
    * `<global>` DOES NOT APPEAR HERE, and that is deliberate rather than an omission:
    * [[headNameCollisions]] leaves it out of the CANDIDATE SET, so `!candidates.contains`
    * already answers for it. */
  private def headNameReach(
    kb: KnowledgeBase,
    name: String,
    scope: kb.ScopeId,
    file: FileId,
    candidates: Set[kb.ScopeId],
    sentinels: Map[kb.ScopeId, TermSymbol],
    ofSymbol: Map[TermSymbol, kb.ScopeId]
  ): Set[kb.ScopeId] =
    val previous = kb.symbols.setAskingFile(Some(file))
    val found = kb.symbols.resolveWithOverlay(name, scope,
      sc => if sc == scope || !candidates.contains(sc) then None else sentinels.get(sc))
    kb.symbols.setAskingFile(previous)
    found match
      // NOTHING, or an ordinary DECLARATION. Neither is a collision: a name that resolves
      // to a real declaration makes the head DENOTE, so it never became a candidate.
      case ResolveResult.NotFound         => Set.empty
      case ResolveResult.Found(sym)       => ofSymbol.get(sym).toSet
      // AMBIGUOUS IS STILL RESOLVING (§"the same ladder, to the rung", WI-900): every
      // candidate among the alternatives is a scope that introduces the name and is
      // visible from here, so all of them collide.
      case ResolveResult.Ambiguous(cands) => cands.flatMap(ofSymbol.get).toSet

  /** Every name introduced at two or more mutually-reachable scopes (845G7).
    *
    * ONE RESOLVER CALL PER `(candidate scope, file)`, and no iteration around it. The
    * fixpoint this replaced existed to decide WHO WINS, which is a non-monotone question
    * — the more scopes own a name the more heads yield, so the fewer own it — and had to
    * be settled in rounds inside one strongly-connected component at a time. Nobody wins
    * any more: each scope keeps its own, so the only question left is whether two of them
    * can see each other, which each scope answers for itself and nothing can change. */
  private def headNameCollisions(
    kb: KnowledgeBase,
    heads: IndexedSeq[RuleHeadSite[kb.ScopeId]],
    denotes: IndexedSeq[Boolean],
    fileIds: IndexedSeq[FileId],
    sentinels: Map[kb.ScopeId, TermSymbol]
  ): IndexedSeq[HeadNameCollision[kb.ScopeId]] =
    // The sentinel map inverted ONCE, not once per resolver call: `headNameReach` runs
    // per (candidate scope, file) and reads it on every answer.
    val ofSymbol: Map[TermSymbol, kb.ScopeId] = sentinels.map((k, v) => v -> k)
    // CANDIDATES PER NAME — EVERY head shape, INCLUDING AN EQUATION'S SUBJECT. 061 puts
    // equations outside the DECLARATION rule (their clauses index under the connective,
    // so the subject owns none), but not outside this one: exempting them silently splits
    // `zeq { rule f(true) <=> 1  sort Rec { rule f(false) <=> 2 } }` into two symbols
    // where it had been one, which is the exact hazard this refusal exists for, permitted
    // for half the head shapes.
    //
    // `<global>` IS NOT A PARTY IN EITHER DIRECTION, and it is excluded from the
    // CANDIDATE SET rather than only from the overlay. Excluding it from the overlay
    // alone stops a namespace head from seeing it, but the group is built on the
    // UNDIRECTED closure of reach — so a namespace-less file that writes `import ns.*`
    // and a head would still pull `ns` into a group with `<global>`, and the repair such
    // a refusal names DELETES the `<global>` head's predicate. THE COST IS A NAMED
    // SILENCE: a namespace-less file importing a namespace and writing its head name
    // shadows it, and nothing says so. That is the one scope where the language has
    // always taken that trade — nobody opts into `<global>`.
    val byName = LinkedHashMap.empty[String, LinkedHashMap[kb.ScopeId, ArrayBuffer[Int]]]
    for (head, idx) <- heads.zipWithIndex if !denotes(idx) && head.scope != kb.globalScope do
      byName.getOrElseUpdate(head.name, LinkedHashMap.empty)
        .getOrElseUpdate(head.scope, ArrayBuffer.empty) += idx

    val out = IndexedSeq.newBuilder[HeadNameCollision[kb.ScopeId]]
    for (name, scopes) <- byName if scopes.size >= 2 do
      val candidates: Set[kb.ScopeId] = scopes.keySet.toSet
      // WHAT EACH CANDIDATE SEES, asked once per FILE it writes a head in — imports are
      // file-local (WI-995), so a sibling head at the same scope in a file without the
      // import gets a different answer, and seeing it from ANY of them is seeing it.
      //
      // KEPT PER FILE, not only unioned per scope: the two readers below want different
      // answers. The GROUP asks whether any file of a scope reaches another (seeing it
      // once is enough to make them one group), while the named OWNER must be seen from
      // EVERY file, because the message promises that declaring there collects every
      // head.
      //
      // AND THE ASKED SET IS THE HEAD-WRITING FILES, WHICH IS A LIMIT. A file that
      // re-opens the scope and writes the `import` but NO head is never asked, so it
      // contributes no edge and the pair is not refused — while the same program with
      // that import line moved into the head-writing file IS. Whether it loads depends on
      // which file the import was typed in. rustland answers identically (its `asked` is
      // the same set), MEASURED through `anthill load` on the same three files, so this
      // is a limit of the shipped rule and not a port gap; closing it needs one decision
      // taken for both trees. Driven by the test row named "845G7 LIMIT: the reach is
      // asked only from files that WRITE a head".
      val perFile = HashMap.empty[(kb.ScopeId, FileId), Set[kb.ScopeId]]
      val edges = HashMap.empty[kb.ScopeId, Set[kb.ScopeId]]
      for (scope, sites) <- scopes do
        var seen = Set.empty[kb.ScopeId]
        for file <- sites.map(i => fileIds(heads(i).fileIdx)).distinct do
          val r = headNameReach(kb, name, scope, file, candidates, sentinels, ofSymbol)
          seen ++= r
          perFile((scope, file)) = r
        edges(scope) = seen

      // THE GROUPS ARE THE WEAKLY-CONNECTED COMPONENTS of that relation. Two scopes
      // neither of which can reach the other are two unrelated predicates that happen to
      // share a short name — the overwhelmingly common case, and not a collision.
      val undirected = HashMap.empty[kb.ScopeId, Set[kb.ScopeId]]
      for (s0, targets) <- edges; t <- targets do
        undirected(s0) = undirected.getOrElse(s0, Set.empty) + t
        undirected(t) = undirected.getOrElse(t, Set.empty) + s0
      val assigned = HashSet.empty[kb.ScopeId]
      // A DETERMINISTIC group order and a deterministic seed, so nothing below depends on
      // a hash map's iteration.
      for seed <- candidates.toIndexedSeq.sortBy(kb.scopeDisplayName)
          if !assigned.contains(seed) && undirected.contains(seed) do
        val group = ArrayBuffer.empty[kb.ScopeId]
        val stack = scala.collection.mutable.Stack(seed)
        while stack.nonEmpty do
          val n = stack.pop()
          if assigned.add(n) then
            group += n
            for t <- undirected.getOrElse(n, Set.empty) do stack.push(t)
        if group.size >= 2 then
          val ordered = group.toIndexedSeq.sortBy(kb.scopeDisplayName)
          // WHERE THE DECLARATION BELONGS — AND ONLY WHEN IT REALLY COLLECTS EVERY HEAD.
          // The message that names a scope promises that declaring there makes every
          // other member's head a clause of it, so the test is not "reaches nothing" but
          // "IS REACHED BY EVERY OTHER MEMBER". The two differ exactly where reach is NOT
          // transitive, which is the common case: a wildcard import is not re-exported,
          // so in a chain `a -> b -> c` the SINK is `c` and `a` cannot see it — declaring
          // at the sink would leave `a`'s head a separate predicate with no error at all,
          // a promise the repair does not keep.
          //
          // MORE THAN ONE MEMBER CAN QUALIFY, and naming the first is right rather than a
          // coin toss: in a mutual cycle every member is reached by every other, so
          // declaring at ANY of them collects the whole group. `ordered` is sorted by
          // display name, so which one is named is deterministic.
          val owner = ordered.find { cand =>
            ordered.forall { other =>
              other == cand || scopes(other).forall { i =>
                perFile((other, fileIds(heads(i).fileIdx))).contains(cand)
              }
            }
          }
          out += HeadNameCollision(
            name, ordered, owner, ordered.flatMap(sc => scopes(sc)).sorted)
    // A DETERMINISTIC report order across names.
    out.result().sortBy(c => (c.name, c.scopes.map(kb.scopeDisplayName).mkString(",")))

  /** Push one refusal per collision, and answer with the `(scope, name)` pairs a
    * declaration is already being asked for — which is what keeps the 061 FILE rule from
    * printing a second message about the same missing declaration. */
  private def reportHeadNameCollisions(
    kb: KnowledgeBase,
    heads: IndexedSeq[RuleHeadSite[kb.ScopeId]],
    denotes: IndexedSeq[Boolean],
    fileIds: IndexedSeq[FileId],
    errors: ArrayBuffer[LoadError]
  ): Set[(kb.ScopeId, String)] =
    val sentinels = mintHeadSentinels(kb, heads)
    val collisions = headNameCollisions(kb, heads, denotes, fileIds, sentinels)
    var collided = Set.empty[(kb.ScopeId, String)]
    for c <- collisions do
      for sc <- c.scopes do collided += ((sc, c.name))
      val first = c.sites.minBy(i => (heads(i).fileIdx, heads(i).span.start))
      val names = c.scopes.map(kb.scopeDisplayName)
      val named =
        if names.length <= CollisionScopesShown then names.mkString(", ")
        else s"${names.take(CollisionScopesShown).mkString(", ")}, … and " +
          s"${names.length - CollisionScopesShown} more"
      // WI-898 — a body-less `rule` in the named owner does NOT collect an EQUATION's
      // subject written elsewhere: an equation's clauses index under the connective, so
      // it is not a clause of a predicate. Asked per SITE, not per group — where every
      // subject in the group sits AT the owner, the ordinary text is still true.
      val equationElsewhere = c.sites.exists(i =>
        heads(i).kind == SymbolKind.EquationFunctor && !c.owner.contains(heads(i).scope))
      val repair = c.owner match
        case Some(o) if equationElsewhere =>
          s"One of those heads is an EQUATION's subject, which a body-less `rule` does " +
          s"not collect — an equation is not a clause of a predicate (WI-898). Declare " +
          s"what the equations define: an `operation ${c.name}(…) -> R` in " +
          s"'${kb.scopeDisplayName(o)}' makes every one of those heads its own, or a " +
          s"body-less `rule ${c.name}(…)` in EACH scope says they are separate."
        case Some(o) =>
          s"Declare it (proposal 061): a body-less `rule ${c.name}(…)` in " +
          s"'${kb.scopeDisplayName(o)}', with a named import of that predicate in each " +
          s"non-enclosing contributor, makes every one of those heads a clause of it. " +
          s"Alternatively, one declaration in EACH scope says they are separate predicates."
        case None =>
          // NO SCOPE IS REACHED BY ALL THE OTHERS — which a cycle produces, and so does a
          // chain, and so does a pair of siblings a third scope imports. The text says
          // only what is true of every shape that produces it: NOT "they reach each
          // other", which is false for the last two.
          s"No one of them is reachable from all the others, so nothing in the program " +
          s"says which should own it. Declare it (proposal 061): a body-less `rule " +
          s"${c.name}(…)` in each scope that should own one says they are separate " +
          s"predicates, and one in a scope the others can all reach, with named imports " +
          s"in its non-enclosing contributors, makes their heads its clauses" +
          (if equationElsewhere then
            " — except an EQUATION's subject, which a body-less `rule` does not collect " +
            "(WI-898); an `operation` there does."
          else ".")
      errors += LoadError.Other(
        s"the rule head `${c.name}` introduces that name at ${c.scopes.length} scopes, " +
        s"each of which reaches or is reached by another of them — $named — and none of " +
        s"them declares it. Each scope's own name beats what it imports or inherits, so " +
        s"a bare `${c.name}` written in any of them would silently reach only that " +
        s"scope's half, with no ambiguity reported. $repair",
        heads(first).span)
    collided

  /** PROPOSAL 061 — AUTO-DECLARATION STOPS AT THE FILE BOUNDARY.
    *
    * A predicate whose heads are all in ONE file is auto-declared by them, at the scope
    * they are written in. One with heads in MORE THAN ONE file is a predicate assembled
    * by two parties that never agreed on it (059 §Definitions), and must be DECLARED — a
    * body-less rule, minted in pass 1b — or the load is refused naming the files.
    *
    * KEYED ON THE SCOPE, which since 845G7 is the same thing as the predicate: a head
    * never lands anywhere but where it is written, so the group is `(scope, name)` and
    * the cross-SCOPE half of what this used to report is [[reportHeadNameCollisions]].
    *
    * A DECLARED predicate never reaches here: its heads all denote (pass 1b minted the
    * name), so they are excluded — which is what makes "declare it" a remedy the message
    * can name.
    *
    * "THE PROGRAM" IS THE FILES OF ONE SCAN, exactly as everything else in this pass is.
    * A predicate assembled across two `loadAll` batches is therefore not caught: the
    * earlier batch's heads are already minted, so the later batch's denote. */
  private def reportPredicateHeadsSpanningFiles(
    kb: KnowledgeBase,
    heads: IndexedSeq[RuleHeadSite[kb.ScopeId]],
    denotes: IndexedSeq[Boolean],
    collided: Set[(kb.ScopeId, String)],
    errors: ArrayBuffer[LoadError]
  ): Unit =
    val byPredicate =
      LinkedHashMap.empty[(kb.ScopeId, String), ArrayBuffer[Int]]
    for (head, idx) <- heads.zipWithIndex
        // An EQUATION is out of scope (061 §"Equational rules are NOT this construct"):
        // its clauses index under the connective, so its subject owns none and there is
        // no predicate to declare.
        if !denotes(idx) && head.kind == SymbolKind.Goal do
      byPredicate.getOrElseUpdate((head.scope, head.name), ArrayBuffer.empty) += idx
    // A DETERMINISTIC report order, so a program with two such predicates does not print
    // them in hash order.
    for ((owner, name), sites) <- byPredicate.toIndexedSeq
        .sortBy((k, _) => (kb.scopeDisplayName(k._1), k._2)) do
      val fileIdxs = sites.map(i => heads(i).fileIdx).distinct.sorted
      // ONE MISSING DECLARATION IS ONE MESSAGE. A scope already named by the visibility
      // refusal is repaired by the declaration THAT message asks for, so reporting both
      // prints one fault twice and prescribes two owners for it.
      if fileIdxs.length >= 2 && !collided.contains((owner, name)) then
        // ONE error per predicate, located at its FIRST head — not one per head. The
        // defect is the predicate, and a report per clause would print it N times.
        val first = sites.minBy(i => (heads(i).fileIdx, heads(i).span.start))
        // THE FILE NAMES COME OFF THE SPANS, which is where a scaland diagnostic's file
        // always comes from — `ParsedFile` carries no path, and the span's `file` is the
        // label the parse was given. One source, not two.
        val names = fileIdxs.map(f => sites.find(i => heads(i).fileIdx == f)
          .map(i => heads(i).span.file).getOrElse("<unknown>"))
        errors += LoadError.Other(
          s"the predicate `$name` has rule heads in ${fileIdxs.length} files — " +
          s"${names.mkString(", ")} — and no declaration. A predicate whose clauses are " +
          s"all in ONE file is declared by them; one assembled from several must be " +
          s"declared once, in the scope that owns it, by a rule with no body: write " +
          s"`rule $name(…)` in '${kb.scopeDisplayName(owner)}' (proposal 061).",
          heads(first).span)

  /** §6.1 — a TOP-LEVEL body goal spelling `true` is erased at load, so the body stays
    * EMPTY.
    *
    * THIS IS A BODY-SHAPE DEVICE, NOT THE MEANING OF `true`, and the distinction is
    * WI-20260822-J38JE's. 061 introduced this strip under the reading "`true` IS the
    * empty conjunction"; J38JE then settled the meaning elsewhere and one rung lower —
    * **a boolean constant in GOAL position is a SEARCH: `true` succeeds, `false` fails**,
    * at EVERY goal position, which is where §6.6 already puts the boolean OPERATORS. The
    * strip cannot be that reading: it walks the body's top-level goal list, so by
    * construction it never reaches a `true` nested under `not` or `|`.
    *
    * WHAT THE STRIP IS STILL FOR is the one thing the resolver arm cannot do: keep the
    * body EMPTY. Only an empty body makes `fact H` and `rule H :- true` ONE clause rather
    * than two with equal answers — [[anthill.kb.KnowledgeBase.isEquation]] reads
    * body-emptiness, and so does every reader that asks whether a rule is a fact. 061
    * item 5, settled by keeping BOTH readings.
    *
    * SCALAND HAS ONLY THIS HALF. J38JE's resolver arm is not ported, so a boolean
    * constant the strip cannot see gets no reading at all — MEASURED here:
    * `:- not(false)` answers 0 where logic says 1, `:- base(9) | true` answers 0 where
    * logic says 1, and a NON-Bool constant goal (`:- 42`) loads clean and silently never
    * matches (J38JE item 4, refused in rustland). `:- false` answers 0 for the WRONG
    * REASON — a constant names no name, so it resolves to no clause and no builtin, and
    * WI-1034's "names nothing" refusal cannot reach it. Recorded rather than discovered:
    * the row "J38JE GAP: a boolean constant goal has no reading below the top level"
    * drives every one of those answers.
    *
    * THE COROLLARY FOR THIS FILE'S BACK-OUTS: removing the strip fells rows HERE that it
    * fells none of in rustland, because there the arm answers what the strip stops
    * seeing. That number measures the missing arm, not the strip. */
  private def isEmptyConjunctionGoal(fileTerms: SimpleTermStore, tid: TermId): Boolean =
    fileTerms.get(tid) match
      case Term.Const(Literal.BoolLit(true)) => true
      case _                                 => false

  /** Does this rule's body add NOTHING to its head — no body at all, or a body of
    * nothing but erased `true`s? Asked by [[ruleIntroducedFunctor]], for which an
    * equation is BODYLESS (§8.3), and by [[loadRuleHeads]]'s non-defining-connective
    * refusal, whose subject is the same emptiness.
    *
    * NOT the same question as "is this a DECLARATION", which is [[ruleReading]]'s and is
    * keyed on the SYNTACTIC absence of a body. That is 061's split point: `rule p(?x)`
    * declares and `rule p(?x) :- true` asserts, so the two must never be fused. */
  private def ruleBodyIsEmptyConjunction(rule: Rule, fileTerms: SimpleTermStore): Boolean =
    rule.body.forall(_.forall(isEmptyConjunctionGoal(fileTerms, _)))

  /** PROPOSAL 061 — HOW A RULE READS: **no body ⇒ DECLARES, a body ⇒ asserts.**
    *
    * A rule with no body declares its head's predicate and asserts nothing; `fact` is
    * how a body-less assertion is written, and it desugars to an explicit `:- true`.
    * This removes `rule`'s exception — `operation f(…) -> R` declares and `= body`
    * defines, `const N: T` declares and `= expr` defines, and `rule` was the sole
    * construct whose body-less form ASSERTED, only because §6.1's desugaring had spent
    * that form on `fact`.
    *
    * THE SPLIT POINT ALREADY EXISTED and this does not newly overload it: the loader
    * already reads a body-less head two ways, and [[parseConnectiveHead]] is where. */
  private enum RuleReading:
    /** A body-less plain head: it DECLARES its predicate and asserts nothing. The name
      * is minted in PASS 1b by [[DeclarePredicatePass]], like every other declared name
      * (WI-321),
      * which is what makes a head's binding independent of the order a pass walks in.
      *
      * A SECOND DECLARATION OF ONE PREDICATE AT ONE SCOPE IS IDEMPOTENT, and admitted:
      * a predicate declaration carries no signature, no arity claim and no clause, so
      * two of them name the same symbol and lose nothing. */
    case Declaration
    /** Anything with a body — and the shapes 061 leaves alone, which are the
      * equality-family connective heads: `<=>` DEFINES (its clauses index under the
      * connective, so its subject owns none and there is no predicate to declare —
      * WI-898), while `=` and `===` are refused at a body-less head where they cannot
      * define (WI-888 / WI-1090), and that refusal must keep firing rather than be
      * swallowed by a declaration reading. */
    case Clause
    /** A body-less head that can declare NOTHING: a `⊥` denial (which names no
      * predicate), several heads at once (a declaration declares ONE name), or a head
      * whose functor introduces no name at all — a QUALIFIED head, which references
      * rather than introduces, or a desugared one (`?x.m(?y)` carries the converter's
      * `dot_apply`). Under 061 such a rule asserts nothing and declares nothing, so it
      * is refused rather than dropped in silence. */
    case DeclaresNothing

  /** [[RuleReading]] for one rule — the single decider, asked by pass 1's mint
    * ([[DeclarePredicatePass]]) and by [[loadRuleHeads]]. Both must give the same answer:
    * the mint puts in exactly the names the load then declines to assert. Mirrors
    * rustland's `rule_reading`. */
  private def ruleReading(
    rule: Rule, fileSym: SymbolTable, fileTerms: SimpleTermStore
  ): RuleReading =
    if rule.body.isDefined then RuleReading.Clause
    // The equality family, WHOLE — not [[parseEquationLhs]]'s defining subset. A
    // body-less `===` / `=` head has its own refusal in [[loadRuleHeads]], and reading
    // it as a declaration here would return before that refusal ever ran.
    else if rule.heads.length == 1 && (rule.heads.head match
        case RuleHead.TermHead(t) => parseConnectiveHead(fileSym, fileTerms, t).isDefined
        case RuleHead.Bottom      => false)
    then RuleReading.Clause
    else ruleIntroducedFunctor(rule, fileSym, fileTerms) match
      case Some((_, SymbolKind.Goal)) => RuleReading.Declaration
      // An EQUATION reaches here only through a head this function already sent to
      // `Clause`; the arm is stated rather than fused so a future head shape cannot
      // acquire a declaration reading by accident. `SymbolKind.EquationFunctor` is the
      // introduction kind [[ruleIntroducedFunctor]] stamps for it — WI-898's split, and
      // this is its first reader in scaland.
      case Some((_, _)) => RuleReading.Clause
      case None         => RuleReading.DeclaresNothing

  /** The kinds a body-less rule's own mint can produce, and therefore the ones a
    * DECLARATION may find already sitting at its scope without having declared nothing:
    * [[SymbolKind.Goal]] (its own), [[SymbolKind.EquationFunctor]] (a sibling equation
    * about the same subject) and [[SymbolKind.Rule]] (a LABEL of that spelling, which
    * [[DefinePass.defineRuleLabel]] defines one pass earlier). Anything else is another
    * construct's declaration that pass 1's `define` merged into. */
  private val DeclarableByARule: Set[SymbolKind] =
    Set(SymbolKind.Goal, SymbolKind.EquationFunctor, SymbolKind.Rule)

  /** WHY a [[RuleReading.DeclaresNothing]] rule declares nothing, in the author's terms.
    * Asks the SAME shape questions [[ruleIntroducedFunctor]] asks, in its order, so the
    * message and the verdict cannot describe different rules. Mirrors rustland's
    * `bodyless_declares_nothing_detail`. */
  private def bodylessDeclaresNothingDetail(
    rule: Rule, fileSym: SymbolTable, fileTerms: SimpleTermStore
  ): String =
    val prefix = "a body-less rule DECLARES its predicate (proposal 061, §5.3), but this " +
      "one declares nothing: "
    if rule.heads.length != 1 then
      return prefix + s"it writes ${rule.heads.length} heads at once, and a declaration " +
        "declares ONE predicate"
    val tid = rule.heads.head match
      case RuleHead.TermHead(t) => t
      case RuleHead.Bottom =>
        return prefix + "a `⊥` denial names no predicate, so there is nothing for it to declare"
    // A DOTTED PAREN-LESS HEAD IS MINTED AND STILL NAMES SOMETHING (WI-20260901-719FJ),
    // so it is asked ahead of the desugaring sentence — the same order
    // [[ruleIntroducedFunctor]] takes, because the two walks must describe one rule.
    val chain = dottedCitationName(fileSym, fileTerms, tid)
    if chain.isEmpty && fileTerms.isMinted(tid) then
      return prefix + "its head functor is the DESUGARING's (`?x.m(?y)` carries " +
        "`dot_apply`, `?a + ?b` carries `add`), not a name the rule introduces"
    // A BARE NAME DOES NOT REACH THE FALLTHROUGH (WI-20260821-P85Z7):
    // [[ruleIntroducedFunctor]] reads a `Term.Ident` head as an application of arity 0,
    // so it carries a name and the qualified test below must run for it — this walk has
    // to agree or the two describe different rules. What still reaches the fallthrough
    // is a bare VARIABLE head (`rule ?x`).
    val name = chain.orElse(fileTerms.get(tid) match
      case fn: Term.Fn    => Some(fileSym.name(fn.functor))
      case id: Term.Ident => Some(fileSym.name(id.sym))
      case _              => None)
    name match
      case None =>
        prefix + "its head is not a functor application, so it names no predicate"
      case Some(n) if n.contains('.') =>
        prefix + s"`$n` is a QUALIFIED name, and a qualified name references an " +
          "existing predicate — it never introduces one"
      case Some(n) =>
        // Every shape [[ruleIntroducedFunctor]] refuses has been named above, so
        // reaching here means the two walks have diverged. Said rather than left as a
        // plausible-looking sentence — and NOT thrown: this is a DIAGNOSTIC path, and
        // aborting while rendering an error would replace a message with a crash.
        prefix + s"the loader's two readings of `$n` disagree — please report this"

  /** Proposal 061 — the two ways a DECLARATION can be written and still stand for
    * nothing, refused rather than dropped in silence. Mirrors rustland's
    * `declaration_clause_carrier` plus the `local` lookup in its `Declaration` arm.
    *
    * ONE CARRIER SCALAND CANNOT ASK ABOUT: rustland also refuses a `[t]` type-variable
    * INTRODUCER on the head, whose only possible bound is a body's `:- Spec[t]` guard
    * (WI-582). scaland's `Rule` has no head type-parameter field — WI-582's fold is not
    * ported — so there is nothing here to read, and the arm is absent rather than
    * guessed at. */
  private def refuseDeclarationThatCannotStand(
    kb: KnowledgeBase,
    rule: Rule,
    fileSym: SymbolTable,
    fileTerms: SimpleTermStore,
    scope: kb.ScopeId,
    errors: ArrayBuffer[LoadError]
  ): Unit =
    val name = ruleIntroducedFunctor(rule, fileSym, fileTerms).map(_._1).getOrElse("")
    // A declaration stores no clause, so there is nothing for a citation handle or a
    // `[…]` tag to attach to. Refused rather than dropped: a label on a declaration
    // defines a `Rule` symbol that `using` then finds nothing under, and both carriers
    // were silently lost the moment this arm stopped asserting.
    val carrier: Option[String] =
      if rule.label.isDefined then Some("A citation label on it has nothing to cite.")
      else if rule.meta.isDefined then Some("A `[…]` tag on it has no clause to govern.")
      else rule.heads.headOption.flatMap {
        case RuleHead.TermHead(t) if headCarriesTypedColumn(fileSym, fileTerms, t) =>
          Some("A typed column `?x: T` has exactly one enforcer, a rewrite's " +
            "typed-pattern bound (WI-903), which a predicate declaration is not.")
        case _ => None
      }
    carrier match
      case Some(why) =>
        errors += LoadError.Other(
          s"the body-less rule `$name` DECLARES a predicate and stores no clause. $why",
          rule.span)
      case None =>
        // WHAT PASS 1 ACTUALLY PUT AT THIS SCOPE — the scope's OWN locals, not the
        // ladder. Two silent no-ops hide here, and only this question separates them
        // from a working declaration. The LADDER is the wrong instrument: it answers YES
        // for any name the scope can SEE, so a declaration whose name the prelude
        // already provides would pass it and still introduce nothing.
        kb.symbols.scope(scope).flatMap(_.locals.get(name)) match
          // NOTHING WAS MINTED HERE. One shape reaches this: the interior of a
          // `provides … language … end` block, which [[walkScopes]] hands to `atItem`
          // and no scan pass descends into — so the declaration would introduce nothing
          // AND assert nothing.
          case None =>
            errors += LoadError.Other(
              s"`$name` was never brought into existence: the defining pass does not " +
              "descend into this position (a `provides … language … end` block's " +
              "interior is the one such place), so the declaration would introduce " +
              "nothing and assert nothing",
              rule.span)
          case Some(sym) =>
            // SOMETHING ELSE ALREADY DECLARED THE NAME HERE, and pass 1b's mint left it
            // alone rather than minting anything — `operation has(x) -> Bool` beside
            // `rule has(?x)`, or `sort Foo` beside `rule Foo(?x)`. The declaration then
            // declares nothing new and asserts nothing: a no-op line, which 059 R4
            // clause 3 refuses for every other pair of declarations at one address. NOT
            // refused at the mint: whichever construct the walk reached first would
            // decide it, which is the order dependence 061 exists to remove.
            //
            // A `DeclarableByARule` KIND IS NOT REFUSED, and one shape makes that a
            // decision rather than an omission: a body-less rule inside a `provides …
            // language anthill … end` block whose name the ENCLOSING scope already
            // declares. The block opens no scope, so it IS that scope, and the rule is
            // 061's admitted SECOND DECLARATION of one predicate at one address —
            // idempotent, and naming a predicate that really exists. Only the `None` arm
            // above is the silent no-op, and it is the one that speaks.
            val kind = kb.symbols.get(sym) match
              case SymbolDef.Resolved(_, _, k, _) => Some(k)
              case SymbolDef.Unresolved(_)        => None
            kind.filterNot(DeclarableByARule.contains).foreach { k =>
              errors += LoadError.Other(
                s"`$name` is already declared in this scope (kind: $k), so a body-less " +
                "rule adds nothing to it — write `:- true` to make this a CLAUSE of it, " +
                "or delete the line",
                rule.span)
            }

  /** Does this head carry a `?x: T` ascription in its ARGUMENTS? The parser lowers one
    * to a `typed_var` MARKER node (WI-582), so the question is asked of that shape
    * rather than of a node kind — and through [[isTypedVarMarker]], which pairs the name
    * with the marker's exact shape, because `typed_var` is also an ordinary identifier a
    * user may write (WI-948's *a name, not a verdict*).
    *
    * THE HEAD'S OWN FUNCTOR IS NOT ASKED: the grammar puts a typed column only in an
    * ARGUMENT position, so a marker can never be the head. */
  private def headCarriesTypedColumn(
    fileSym: SymbolTable, fileTerms: SimpleTermStore, tid: TermId
  ): Boolean =
    fileTerms.get(tid) match
      case fn: Term.Fn =>
        (fn.posArgs.iterator ++ fn.namedArgs.iterator.map(_._2)).exists { a =>
          fileTerms.get(a) match
            case af: Term.Fn => isTypedVarMarker(af, fileSym)
            case _           => false
        }
      case _ => false

  /** The functor a rule introduces, and which kind of introduction it is — or `None`
    * when the rule introduces nothing. Mirrors rustland's
    * `rule_introduced_functor_name`, including its three refusals:
    *
    *  - a MULTI-head rule, or a denial head, introduces nothing;
    *  - a MINTED subject introduces nothing (WI-618) — the desugar's functor is the
    *    desugar's name, not the rule's, so `rule ?x.m(?y) :- p(?x)` must not mint
    *    `dot_apply` and shadow reserved kernel vocab for the whole scope;
    *  - a QUALIFIED (dotted) head REFERENCES an existing symbol and never introduces
    *    one — otherwise `rule String.isEmpty(?s) <=> true` defines a symbol whose
    *    SHORT name is literally `String.isEmpty`.
    *
    * A BARE NAME IS AN APPLICATION OF ARITY 0 on the PREDICATE path (P85Z7): `rule
    * holds :- base(1)` introduces `holds`, scoped where it is written, exactly as
    * `rule holds()` does. On the EQUATION path it introduces nothing, deliberately —
    * a `[simp]` head is an application, so a bare subject matches no redex.
    *
    * The SUBJECT is the node the rule is about: for an equation (`ite(true, ?t, ?_) =
    * ?t`) that is the LHS; for a predicate head it is the head itself. This is the one
    * place the two part ways, and the answer travels with the name so a second walk
    * cannot disagree (WI-898). The rule's LABEL is deliberately never read. */
  private def ruleIntroducedFunctor(
    rule: Rule, fileSym: SymbolTable, fileTerms: SimpleTermStore
  ): Option[(String, SymbolKind)] =
    if rule.heads.length != 1 then return None
    val headId = rule.heads.head match
      case RuleHead.TermHead(t) => t
      case RuleHead.Bottom => return None
    // Only a BODY-LESS rule can be an equation (a `:-` rule with an `=` head is an
    // ordinary predicate whose head happens to be an equality goal).
    //
    // §8.3 — an equation is BODYLESS, which is a property of the RULE, so the question
    // goes through the ONE owner of it ([[ruleBodyIsEmptyConjunction]]) rather than off
    // `body.isDefined` directly: since 061 `rule f(?x) <=> ?x :- true` is the explicit
    // spelling of the same empty body, and it must read as the equation it is HERE and
    // at [[loadRuleHeads]] alike.
    val equationLhs =
      if ruleBodyIsEmptyConjunction(rule, fileTerms) then parseEquationLhs(fileSym, fileTerms, headId)
      else None
    val (subject, kind) = equationLhs match
      case Some(lhs) => (lhs, SymbolKind.EquationFunctor)
      case None      => (headId, SymbolKind.Goal)
    if fileTerms.isMinted(subject) then return None
    fileTerms.get(subject) match
      case fn: Term.Fn =>
        val name = fileSym.name(fn.functor)
        if name.contains('.') then None else Some((name, kind))
      // A PAREN-LESS NULLARY PREDICATE HEAD is an application of arity 0 (rustland
      // WI-20260821-P85Z7). The parser gives a bare name a `Term.Ident`, not a
      // zero-argument `Term.Fn`, so reading only the `Fn` shape made the two spellings
      // of one nullary predicate opposite programs: `rule holds()` scoped where it was
      // written, `rule holds` introduced NOTHING ANYWHERE and fell to the bare intern —
      // one global name two scopes' same-spelled heads then share, WI-894's defect
      // class.
      //
      // WI-20260902-CZJ2N — THE EQUATION PATH MINTS TOO, and the `kind == Goal` guard
      // that stood here is what it deletes. P85Z7 admitted only the PREDICATE path, on
      // the reading that a `[simp]` head is an APPLICATION which a bare name is not — so
      // `rule tau <=> …` matched no redex and minting `tau` would have stamped it
      // `EquationFunctor` for a law that can never run. CZJ2N makes the two spellings
      // ONE TERM, so the bare law DOES define and refusing to mint its subject would be
      // a new spelling-dependent rule: refusing at arity 0 only, on the equation path
      // only. `docs/kernel-language.md` §5.3 now says so, and rustland's
      // `load::head_subject_name` deleted the same guard — the two loaders must agree on
      // what a rule introduced, which is why `SymbolKind.EquationFunctor` exists here at
      // all with no reader yet.
      //
      // A dotted paren-less head never reaches here — the converter folds a
      // multi-segment name into a MINTED `field_access` chain, refused above.
      case id: Term.Ident =>
        val name = fileSym.name(id.sym)
        if name.contains('.') then None else Some((name, kind))
      case _ => None

  /** THE SHAPE: a head the infix desugar wrote with an equality-family connective —
    * its functor spelling and its LHS operand — or `None` when `head` is not one. The
    * connective sits at the head with its operands at 0 and 1; arity 2 is load-bearing
    * — a 2-ary head is told from a connective head by the FUNCTOR
    * (`Pratt.isEqualityFamilyFunctor`, one source of truth with the desugar's table),
    * never by arity alone.
    *
    * `isMinted` FIRST, and it is not redundant with the name test: only a node the
    * infix desugar built is a written connective. Without it the decision would be
    * re-derived from a name blocklist — the thing `SimpleTermStore.minted` exists to
    * replace — and a legitimate 2-ary predicate head spelled as an ordinary call
    * (`rule eq(?a, ?b)`) would be read as an equation whose "LHS" is a variable,
    * introducing nothing at all. (WI-948 ported this guard to rustland's
    * `parse_equation_lhs`; the two implementations agree.) */
  private def parseConnectiveHead(
    fileSym: SymbolTable, fileTerms: SimpleTermStore, head: TermId
  ): Option[(String, TermId)] =
    if !fileTerms.isMinted(head) then None
    else fileTerms.get(head) match
      case fn: Term.Fn if fn.posArgs.length == 2 && fn.namedArgs.isEmpty =>
        val name = fileSym.name(fn.functor)
        Option.when(Pratt.isEqualityFamilyFunctor(name))((name, fn.posArgs(0)))
      case _ => None

  /** The LHS operand of a parse-layer DEFINING EQUATION head (`lhs <=> rhs`), or
    * `None` when `head` is not one — [[parseConnectiveHead]] narrowed to the ONE
    * connective that DEFINES. Neither `===` (WI-1090) nor `=` (WI-888) is one: both are
    * the spec's TEST column, their subjects define nothing, and a bodyless head on
    * either is refused by [[nonDefiningConnectiveHead]] instead of being stamped.
    *
    * Two questions, kept apart deliberately — "where do the operands sit" is the shape
    * above and answers the same for every family member, while "does this head DEFINE"
    * is this one. Collapsing them cost rustland a bodied `g[T](?x) === ?x :- p(?x)`,
    * whose `[T]` introducer rides on the LHS like every connective head's. */
  private def parseEquationLhs(
    fileSym: SymbolTable, fileTerms: SimpleTermStore, head: TermId
  ): Option[TermId] =
    parseConnectiveHead(fileSym, fileTerms, head)
      .filter((name, _) => Pratt.isEquationFunctor(name))
      .map((_, lhs) => lhs)

  /** WI-1090 / WI-888 — a head written with an equality-family connective that does NOT
    * define, as `(connective spelling, subject or None)`. `None` only for the ONE
    * defining connective, `<=>`.
    *
    * It reads TWO connectives now (`===`, then `=`), and they arrived by the same rule
    * rather than by two judgements — the spec's equality table puts both in the TEST
    * column. What differs is what the refusal REPLACES, so the MESSAGE branches
    * ([[nonDefiningConnectiveMessage]]) while this reader does not.
    *
    * Purely parse-layer: `isMinted` already proves the desugar wrote the node, so the
    * connective's identity needs no symbol resolution — a user's own `struct_eq`
    * operation can never be minted (WI-948), which is why that guard exists. */
  private def nonDefiningConnectiveHead(
    fileSym: SymbolTable, fileTerms: SimpleTermStore, head: TermId
  ): Option[(String, Option[String])] =
    parseConnectiveHead(fileSym, fileTerms, head)
      .filterNot((name, _) => Pratt.isEquationFunctor(name))
      .map { (name, lhs) =>
        val subject = fileTerms.get(lhs) match
          case fn: Term.Fn => Some(fileSym.name(fn.functor))
          case Term.Ref(s) => Some(fileSym.name(s))
          case _           => None
        (name, subject)
      }

  /** WI-1090 / WI-888 — THE CONNECTIVE-DEFINES-NOTHING SENTENCE. A test connective
    * compares, it does not define, and `<=>` is the connective that does; the author who
    * wrote this believes otherwise, so the message has to say which and name the
    * substitute. Mirrors rustland's `non_defining_connective_head_message`, branch for
    * branch.
    *
    * IT BRANCHES ON THE CONNECTIVE because the two refusals replace different beliefs.
    * For `===` nothing worked, so the author is told what went wrong. For `=` the rule
    * FIRED, so a message about silent uselessness would be false — and `===`'s second
    * remedy must be WITHHELD there, since "give it a body goal" turns an `=` equation
    * into a guarded one, which no firing site reads. */
  private def nonDefiningConnectiveMessage(connective: String, subject: Option[String]): String =
    if connective == Pratt.eqFunctor then
      val remedy = subject match
        case Some(s) => s"Write `$s(…) <=> …` to define `$s` by equations"
        case None    => "Write `<=>` to define by equations"
      val what = subject match
        case Some(s) => s"so `$s(…) = …` is not an equation about `$s`"
        case None    => "so a `lhs = rhs` rule with no body goals is not an equation"
      s"`=` is the semantic equality TEST (`PartialEq.eq`): it dispatches to the " +
      s"carrier's own equality and never binds, whereas an equational rule head " +
      s"UNIFIES the redex with its left-hand side and derives the right — $what. " +
      s"`<=>` is the connective that binds, and it is the only one admitted at a " +
      s"bodyless head (proposal 049; the `=` spelling was accepted while that " +
      s"migration was in flight and no longer is). $remedy. Adding a body goal is NOT " +
      s"the alternative here: `lhs = rhs :- guard` is a guarded equation, which no " +
      s"firing site reads."
    else
      val op = if connective == Pratt.structEqFunctor then "===" else connective
      val what = subject match
        case Some(s) => s"the rule `$s(…) $op …` defines nothing, and `$s` is left naming no callable"
        case None    => s"a `lhs $op rhs` rule with no body goals defines nothing"
      val remedy = subject match
        case Some(s) => s"Write `<=>` to define `$s` by equations"
        case None    => "Write `<=>` to define by equations"
      s"`$op` is the structural identity TEST, not a defining connective, so $what: " +
      s"`$op` is a resolver builtin that answers every goal itself, so no clause of it is " +
      s"ever consulted, and a `[simp]` tag on it never fires (the normalizer reads only " +
      s"the `<=>` equations). $remedy, or give the rule a BODY GOAL to state it " +
      s"as an ordinary law about `$op`."

  /** WI-1090 — push the refusal for a bodyless head written with a non-defining
    * connective, reporting whether it fired. One helper for the two callers a bodyless
    * head has: a `rule` with no body, and a `fact` (which §6.1 defines as exactly
    * that). Rustland shipped the rule side alone and its review found the `fact`
    * spelling loading clean one keyword away. */
  private def refuseNonDefiningConnectiveHead(
    fileSym: SymbolTable, fileTerms: SimpleTermStore, head: TermId,
    span: Span, errors: ArrayBuffer[LoadError]
  ): Boolean =
    nonDefiningConnectiveHead(fileSym, fileTerms, head) match
      case Some((connective, subject)) =>
        errors += LoadError.Other(nonDefiningConnectiveMessage(connective, subject), span)
        true
      case None => false

  /** WI-295: a `Selective` import name that did not resolve in pass 2. The
    * head-functor symbol of a rule-introduced predicate is not registered until pass
    * 3, so such names are deferred and retried after it.
    *
    * `path` is the import's written spelling, and it is a RESOLUTION INPUT only (WI-962):
    * [[resolveSelectiveImport]]'s nested-scope rung builds lookup keys out of it. It used
    * to double as the retry's diagnostic scope name, which is a second source for a field
    * [[LoadError]] says is derived from a scope; the retry now reads that off `target`
    * instead. */
  private case class PendingImport[S](
    scope: S, short: String, target: TermSymbol, span: Span, path: String,
    /** WI-1074 — whose import this is; the pass-4 retry runs outside the per-file loop,
      * so the provenance rides with the deferral. */
    origin: ImportOrigin.File)

  /** Resolve one name of a `Selective` import against the imported symbol `target`
    * (whose qualified name is `pathStr`). THE one resolution both pass 2 and the
    * pass-4 retry use — the retry differs only in WHEN it runs, never in which rungs
    * it tries, so a name that pass 3 has since registered resolves through exactly the
    * ladder that first missed it. */
  private def resolveSelectiveImport(
    kb: KnowledgeBase, target: TermSymbol, pathStr: String, name: String
  ): Option[TermSymbol] =
    // WI-20260826-NB88H — `resolveBelowImport`, not `resolveInScope`: this call IS the
    // import edge, so the walk starts with the enclosing chain already stopped. Without
    // it a path naming a sort answered out of the namespace around it — see that
    // method's doc for the two measured over-hits.
    kb.symbols.resolveBelowImport(name, kb.symbols.scopeOf(target)) match
      case ResolveResult.Found(s) => Some(s)
      // Last resort: an entity exported by the namespace but defined one scope
      // deeper, e.g. `execution_platform` declared inside `sort ExecutionPlatform`
      // of namespace `anthill.realization.platform`. Mirrors rustland's
      // `find_in_nested_scope`.
      //
      // WI-992 retired the rung that used to sit ABOVE this one — a direct
      // `byQualifiedName("$pathStr.$name")` lookup, there because a top-level dotted
      // declaration such as `enum anthill.prelude.Pair` was registered at global under
      // its whole spelling and never attached to the `anthill.prelude` namespace. It is
      // attached now ([[ensureNamespacePath]]), so `resolveInScope` above answers those
      // names, and the rung was measured dead: removing it moves no test. This one is
      // NOT dead — removing it fails `WI-295: a deferred import resolves through the
      // nested-scope rung too`, because the name there is a scope deeper than the path
      // names, which is a different gap and the one rustland also still fills.
      case _ => findInNestedScope(kb, pathStr, name)

  private def processImports(
    kb: KnowledgeBase,
    imports: Iterable[Import],
    fileSym: SymbolTable,
    scope: kb.ScopeId,
    errors: ArrayBuffer[LoadError],
    pending: ArrayBuffer[PendingImport[kb.ScopeId]],
    origin: ImportOrigin.File
  ): Unit =
    for imp <- imports do
      val pathStr = joinSegments(fileSym, imp.path.segments)
      kb.symbols.byQualifiedName.get(pathStr) match
        case Some(sym) =>
          imp.kind match
            case ImportKind.Plain =>
              val short = fileSym.name(imp.path.last)
              kb.symbols.addImport(scope, short, sym, origin)
            case ImportKind.Selective(names) =>
              for n <- names do
                val name = joinSegments(fileSym, n.segments)
                resolveSelectiveImport(kb, sym, pathStr, name) match
                  case Some(s) => kb.symbols.addImport(scope, name, s, origin)
                  // WI-295: a RULE-INTRODUCED predicate's head-functor symbol is not
                  // registered until pass 3, which runs AFTER imports — so a selective
                  // import of one (`import anthill.prelude.Bool.{ite}`, stdlib
                  // int64/ordered) cannot resolve here. Defer instead of erroring; the
                  // post-pass-3 retry re-resolves it and errors only if still unbound.
                  case None =>
                    pending += PendingImport(scope, name, sym, n.span, pathStr, origin)
            case ImportKind.Wildcard =>
              // WI-988: a wildcard brings a scope's CONTENTS in, so the path has to name
              // something with contents — a namespace, or a sort (§5.1 names both).
              // WI-1074: through [[SymbolTable.addImportParent]] — this link is one
              // file's import, not a property of the address.
              parentScopeOf(kb, sym, Set(SymbolKind.Namespace, SymbolKind.Sort),
                s"the wildcard import `$pathStr.*`", imp.path.span, errors)
                .foreach(p => kb.symbols.addImportParent(scope, p, isEnclosing = false, origin))
        case None =>
          errors += LoadError.UnresolvedImport(pathStr, imp.path.span)

  /** Resolve a selectively-imported name that lives one scope level below
    * the imported namespace — e.g. an entity declared inside a `sort`/`enum`
    * within the namespace. Without this, `import anthill.realization.platform.{
    * execution_platform}` fails because the entity's qualified name is
    * `…platform.ExecutionPlatform.execution_platform` (one intermediate
    * segment), not `…platform.execution_platform`. Mirrors rustland's
    * `find_in_nested_scope`: requires exactly one intermediate segment and a
    * unique match (ambiguity → None). */
  private def findInNestedScope(
    kb: KnowledgeBase, basePath: String, short: String
  ): Option[TermSymbol] =
    val prefix = s"$basePath."
    val suffix = s".$short"
    val matches = kb.symbols.byQualifiedName.iterator.collect {
      case (qname, sym)
        // The length guard rules out an overlapping prefix/suffix (e.g.
        // base="a", short="b", qname="a.b"), which would make the substring
        // bounds invalid; such a qname is the exact `base.short` already
        // handled by the direct lookup, so it has no intermediate segment.
        if qname.startsWith(prefix) && qname.endsWith(suffix) &&
           qname.length >= prefix.length + suffix.length &&
           {
             val middle = qname.substring(prefix.length, qname.length - suffix.length)
             middle.nonEmpty && !middle.contains('.')
           } => sym
    }.toSet
    if matches.size == 1 then Some(matches.head) else None

  /** The scope a symbol names, when its KIND is one that has contents (WI-988).
    *
    * `scopeOf` is total over its table's symbols, deliberately — the scope graph is open,
    * so a symbol's KIND is nothing the mint can require (its own refusal is about which
    * table, WI-990). That leaves "can this name hold contents at all" to the sites that
    * link a parent, and both of them used to skip it. An `import X.*` or a
    * `requires X` naming an OPERATION minted a scope that no `define` had ever filled;
    * `addParent` created the importing side's record and never the parent's, and
    * `resolveRecursive` then treated the missing parent as eligible and answered
    * `NotFound`. The user's import contributed nothing, and said nothing.
    *
    * Reports rather than degrading, and names the kind it got — "did nothing" is not a
    * diagnosis a reader can act on. */
  private def parentScopeOf(
    kb: KnowledgeBase, sym: TermSymbol, allowed: Set[SymbolKind],
    clause: String, span: Span, errors: ArrayBuffer[LoadError]
  ): Option[kb.ScopeId] =
    val actual = kb.symbols.get(sym) match
      case SymbolDef.Resolved(_, _, kind, _) => Some(kind)
      case SymbolDef.Unresolved(_) => None
    if actual.exists(allowed.contains) then Some(kb.symbols.scopeOf(sym))
    else
      val got = actual
        .map(k => s"names a ${k.toString.toLowerCase}")
        .getOrElse("names nothing declared")
      val wanted = allowed.toIndexedSeq.map(_.toString.toLowerCase).sorted.mkString(" or a ")
      errors += LoadError.Other(
        s"$clause $got, '${kb.qualifiedNameOf(sym)}' — only a $wanted has contents to " +
        "bring into scope, so this would resolve nothing", span)
      None

  private def processRequires(
    kb: KnowledgeBase,
    req: RequiresDecl,
    fileSym: SymbolTable,
    scope: kb.ScopeId,
    errors: ArrayBuffer[LoadError]
  ): Unit =
    // A requirement is resolved by its BASE NAME, whether or not bindings follow it:
    // `requires Ord[T]` requires `Ord`, and the bindings say which instance — which
    // scaland, having no typer, records nowhere (rustland builds an instantiation term
    // from them). WI-988 had to drop the parameterized form — 24 of the stdlib's 26
    // requirements — because routing it through this resolution failed 8 tests, every one
    // a base name that did not resolve from inside a top-level DOTTED declaration. That
    // was WI-992's gap in the scope graph, fixed at [[ensureNamespacePath]], and the arm
    // now goes through the same one rung order as the bare form.
    linkSpecScope(kb, req.typeExpr, req.span, "requires", fileSym, scope, errors,
      ImportOrigin.Requirement)

  /** WI-869 (058 §3.8) — a provision's `:- goals` tail, linked exactly as a `requires`
    * is. A condition is a spec instantiation over the declaring sort's parameters, and
    * "link the spec's scope as a parent" is [[processRequires]]'s whole effect in
    * scaland, so the two share it rather than one silently doing less. */
  private def processProvidesConditions(
    kb: KnowledgeBase,
    pc: anthill.parse.ProvidesClause,
    fileSym: SymbolTable,
    scope: kb.ScopeId,
    errors: ArrayBuffer[LoadError]
  ): Unit =
    pc.conditions.foreach(c =>
      linkSpecScope(kb, c, pc.span, "provides … :-", fileSym, scope, errors,
        ImportOrigin.Declaration))

  /** WI-1110 — a SPEC's `provides` is a CONVERSION, and a conversion lends its names
    * exactly as a `requires` does: both put a dictionary in the declaring sort's hands,
    * so both make the target's members resolvable inside it. `Ord`'s whole content is
    * `provides WeakOrd[T = T]`, so without this link `import anthill.prelude.Ord.{gte}`
    * stops resolving — `gte` lives two floors down and is reached through the chain.
    *
    * GATED ON THE CLAUSE SPEAKING ONLY OF THE SORT'S OWN PARAMETERS, mirroring
    * rustland's `provides_speaks_only_of_own_params` (kb/load.rs), and for the reason
    * measured there: `provides` is written far more often than `requires` and by
    * CARRIERS, and splicing each target's scope in re-enters that target's enclosing
    * namespace, so a carrier declaring its own `Cell` beside `provides Eq[Cell]` starts
    * reporting `ambiguous symbol 'Cell'`. A clause binding only the sort's parameters is
    * a claim about an abstract thing; one naming a concrete carrier is a claim about a
    * value and brings nothing new into scope.
    *
    * A MISS IS SILENT here, unlike the `requires` arm: an unresolvable provision spec is
    * already reported where the provision is loaded, and a second diagnostic would
    * double every one of them. */
  private def processProvidesHead(
    kb: KnowledgeBase,
    pc: anthill.parse.ProvidesClause,
    fileSym: SymbolTable,
    scope: kb.ScopeId,
    errors: ArrayBuffer[LoadError]
  ): Unit =
    // The `effects E = ?` desugar's synthetic anchor, skipped for the reason the
    // `requires` arm gives at length: wiring it splices the whole prelude namespace in as
    // a resolution parent of every effects-bearing sort (WI-703). Rustland's twin
    // (`wire_provides_scope_parent`, kb/load.rs) carries the same exemption, and the two
    // loaders differing about which clauses they wire is the drift this prevents.
    if type_expr_base_name_is_effects_runtime(fileSym, pc.spec) then return
    val speaksOnlyOfOwnParams = pc.spec match
      case TypeExpr.Parameterized(_, bindings) if bindings.nonEmpty =>
        bindings.forall(_.bound match
          case TypeExpr.Simple(n) =>
            kb.symbols.isTypeParam(scope, joinSegments(fileSym, n.segments))
          case _ => false)
      case _ => false
    if speaksOnlyOfOwnParams then
      // SILENCED SELECTIVELY, not wholesale. The load phase already reports an
      // unresolvable provision spec, so a `UnresolvedName` here would double every one of
      // them — but an AMBIGUITY is reported by nobody else, and swallowing it loses the
      // target's names with no diagnostic at all (§8.6: an ambiguity ends the ladder, it
      // is not a miss). So the miss is dropped and the ambiguity is kept.
      val silenced = ArrayBuffer.empty[LoadError]
      linkSpecScope(kb, pc.spec, pc.span, "provides", fileSym, scope, silenced,
        ImportOrigin.Declaration)
      errors ++= silenced.collect { case e: LoadError.AmbiguousSymbol => e }

  /** The `effects E = ?` desugar's `anthill.prelude.EffectsRuntime` anchor — a synthetic
    * kind-marker and not a spec whose scope anything should resolve names against. */
  private def type_expr_base_name_is_effects_runtime(
    fileSym: SymbolTable, typeExpr: TypeExpr
  ): Boolean =
    (typeExpr match
      case TypeExpr.Simple(name) => Some(name)
      case TypeExpr.Parameterized(name, _) => Some(name)
      case _ => None
    ).exists(n => joinSegments(fileSym, n.segments) == "anthill.prelude.EffectsRuntime")

  /** Resolve a spec instantiation by its BASE NAME and link the spec's scope as a
    * parent of `scope`. Shared by `requires` and by a provision's `:- goals`;
    * `clause` names the writer for the diagnostic.
    *
    * `origin` says WHICH clause wrote the link, and the walk reads it: a `requires`
    * files [[ImportOrigin.Requirement]] and stops the target's ENCLOSING chain
    * (WI-20260906-6BX85), a `provides` files [[ImportOrigin.Declaration]] and does not.
    * That asymmetry is not a decision taken here — rustland stops the `provides` edge
    * too (WI-20260825-N2865) and scaland has not ported it; the origin is the seam that
    * port lands on. */
  private def linkSpecScope(
    kb: KnowledgeBase,
    typeExpr: TypeExpr,
    span: Span,
    clause: String,
    fileSym: SymbolTable,
    scope: kb.ScopeId,
    errors: ArrayBuffer[LoadError],
    origin: ImportOrigin
  ): Unit =
    (typeExpr match
      case TypeExpr.Simple(name) => Some(name)
      case TypeExpr.Parameterized(name, _) => Some(name)
      case _ => None
    ) match
      case Some(name) =>
        val nameStr = joinSegments(fileSym, name.segments)
        // WI-986: through [[lookupWritten]], the ONE rung order — so the scope this
        // reports is the scope it SEARCHED, and `LoadError`'s "resolved against" is
        // literally that rather than a stand-in for it. This site used to ask
        // `byQualifiedName` alone, which a short name is never answered by, and a
        // requirement naming an imported spec (§5.1: an import makes a name visible in
        // the current scope as a local alias) was then refused with a message asserting
        // it did not resolve in a scope where it did.
        lookupWritten(kb, nameStr, scope) match
          case ResolveResult.Found(sym) =>
            // A requirement names an algebraic SPEC (§5.2), and a spec is a sort.
            parentScopeOf(kb, sym, Set(SymbolKind.Sort),
              s"`$clause $nameStr`", name.span, errors)
              .foreach(p =>
                origin match
                  case ImportOrigin.Requirement => kb.symbols.addRequiresParent(scope, p)
                  case ImportOrigin.Declaration => kb.symbols.addParent(scope, p, isEnclosing = false)
                  case other =>
                    // No default arm and no silent fallback: a new clause kind routed
                    // through here is a decision about the enclosing stop, and one that
                    // quietly took `Declaration`'s reach is the defect
                    // WI-20260906-6BX85 spent a census on.
                    sys.error(s"linkSpecScope: `$clause` may not link a parent as $other"))
          case ResolveResult.Ambiguous(candidates) =>
            errors += LoadError.AmbiguousSymbol(
              nameStr, candidates.map(kb.qualifiedNameOf).toIndexedSeq,
              name.span, kb.scopeDisplayName(scope))
          case ResolveResult.NotFound =>
            errors += LoadError.UnresolvedName(nameStr, name.span, kb.scopeDisplayName(scope))
      case None =>
        // Every other `TypeExpr` — an arrow, a tuple, a bare `?T` — is a type and not a
        // spec. Unreachable from `requires`, whose production refuses them; REACHABLE
        // from a provision's `:- goals`, where this parser takes the full `typeExpr`
        // while tree-sitter narrows to a spec instantiation. Parse-permissive,
        // convert-strict (WI-763): a located refusal beats a bare syntax error.
        errors += LoadError.Other(
          s"`$clause …` names a type and not a spec, so it can resolve no instance",
          span)

  // ── Phase 2: Load items into KB ─────────────────────────────

  /** Phase 2 — fill the KB. Walks the SAME scope spine the scan passes do (WI-949): it
    * looks a scope up exactly as they do, so a namespace whose imports pass 2 wired
    * cannot be a namespace whose facts this phase silently drops. */
  private final class LoadPass(
    val kb: KnowledgeBase,
    val fileSym: SymbolTable,
    fileTerms: SimpleTermStore,
    errors: ArrayBuffer[LoadError]
  ) extends ScopePass:

    def enterScope(
      decl: ScopeDecl, writtenName: String, qualName: String, prefix: String, enclosing: kb.ScopeId
    ): Option[kb.ScopeId] =
      lookupScope(kb, qualName, decl.name.span, errors)

    def atItem(item: Item, scope: kb.ScopeId, prefix: String): Unit =
      item match
        case Item.FactItem(fact) =>
          // WI-1090: a fact IS a bodyless rule (§6.1), so `fact lhs === rhs` is the same
          // dead clause the rule arm refuses — refused BEFORE the assert, so no consumer
          // that collects errors without failing the load sees the pre-fix KB.
          if !refuseNonDefiningConnectiveHead(
            fileSym, fileTerms, fact.term, fileTerms.spanOf(fact.term), errors) then
            // WI-20260901-719FJ: a fact head is a LOGICAL SUBJECT too — `fact ns.tgt`
            // is the same reference `fact ns.tgt()` is.
            val kbTerm = reallocTerm(kb, fileTerms, fileSym, fact.term, scope, errors, atGoal = true)
            val sortSort = findSortTerm(kb, "anthill.reflect.Fact")
            kb.assertFact(kbTerm, sortSort, scope)

        case Item.RuleItem(rule) =>
          val sortSort = findSortTerm(kb, "anthill.reflect.Rule")
          loadRuleHeads(kb, rule, fileTerms, fileSym, scope, sortSort, errors)

        case Item.RuleBlockItem(block) =>
          val sortSort = findSortTerm(kb, "anthill.reflect.Rule")
          for rule <- block.entries do
            loadRuleHeads(kb, rule, fileTerms, fileSym, scope, sortSort, errors)

        case Item.EntityItem(entity) =>
          val shortName = joinSegments(fileSym, entity.name.segments)
          val qualName = makeQualified(prefix, shortName)
          // Same invariant as a scope descent, so the same answer (WI-949): `DefinePass`
          // defines every entity, and a name that is not there drops this `EntityOf`
          // fact — silently, before the miss got a diagnostic.
          val defined = lookupDefined(
            kb, qualName, entity.name.span, "its `entity_of` fact cannot be asserted", errors)
          // Gated exactly as the parent EDGE is in pass 1 (WI-985), and for the same
          // reason: the fact makes the same claim in the other spelling, so an ungated
          // fact would be the second source that outlives the fix — `entity_of(Foo,
          // demo)` naming a namespace, with the index correctly saying Foo has no
          // parent. The lookup above stays UNGATED: "pass 1 defined every entity" is an
          // invariant of every entity, not only of the ones that get a fact.
          if isSortScope(kb, scope) then defined.foreach { sym =>
            val entityTerm = kb.makeNameTermFromSym(sym)
            val entityOfSort = findSortTerm(kb, "anthill.reflect.EntityOf")
            val entityOfSym = kb.intern("entity_of")
            // The scope appears twice here in two DIFFERENT roles, which is why only one
            // of them changed in WI-983: as the fact's second ARGUMENT it is a term the
            // fact is about, and as the domain it is the scope the fact was declared in.
            val entityOfFact = kb.alloc(
              Term.Fn(entityOfSym, IArray(entityTerm, kb.scopeTerm(scope)), IArray.empty))
            kb.assertFact(entityOfFact, entityOfSort, scope)
          }

        case Item.ProofItem(p) =>
          loadProof(kb, p, fileSym, scope)

        case Item.ProvidesClauseItem(pc) =>
          loadProvidesClause(kb, pc, fileSym, scope)

        case Item.ProvidesBlockItem(pb) =>
          loadProvidesBlock(kb, pb, fileTerms, fileSym, scope, errors)

        // WI-1007: THE seam an operation BODY / const VALUE would enter the KB at.
        // Both are parsed (`Operation.body`, `Const.value`) and both are deliberately
        // dropped: scaland has no typer and no evaluator to consume them, and the KB has
        // no slot to hold them — rustland stores the body as an occurrence
        // (`set_op_body_node`, called from its `convert_expr_term`) and scaland has no
        // peer for either side. Pass 1 already took what IS loaded: the symbol.
        //
        // Dropped, NOT refused. A refusal here is what this arm would otherwise be — the
        // repo prefers a loud error to a silent skip — but it cannot be one: 72 of the
        // stdlib's 319 operations carry a body, so an error would stop scaland loading
        // its own stdlib. (Counted through the PARSER, not by grep — `Operation.body
        // .isDefined` over every `Item` of every `EmbeddedStdlib.stdlibPaths` file,
        // braced `operation { … }` entries included; `list.anthill` alone has 18.) The
        // limitation is whole-implementation, not per-site, so it is pinned by a test
        // that DRIVES it (`LoaderTest`, "WI-1007": the symbol is defined, and a goal
        // calling the operation has no clause) rather than reported per declaration.
        //
        // WI-1007 deleted the ~250-line Expr/Pattern conversion cluster that hung off
        // this decision: ported ahead of any consumer in 03415ce1 and never once called,
        // because the caller it was written for is this arm and this arm never grew one.
        // Wire bodies in HERE, and restore the conversion from that commit, when scaland
        // grows something that reads them.
        case Item.OperationItem(_) | Item.OperationBlockItem(_) | Item.ConstItem(_) =>

        // WI-1007: `constraint` is PARSED and dropped, and unlike the body above that is
        // not a decision anyone has made — it fell through the `case _` this arm's
        // enumeration replaced. `Item.ConstraintItem` has exactly one mention in the main
        // tree, the parser production that builds it: no pass reads it, so an integrity
        // guard a user writes is accepted and vanishes. Named here so the gap is visible
        // rather than silent; loading it is its own work.
        case Item.ConstraintItem(_) =>

        // Consumed by an EARLIER pass, so phase 2 has nothing left to do with them:
        // `AbstractSortItem` and `RequiresDeclItem` by `DefinePass`, `ImportItem` by
        // `ImportPass`. Listed rather than defaulted so "already handled" and "not
        // handled at all" stay different answers.
        case Item.AbstractSortItem(_) | Item.RequiresDeclItem(_) | Item.ImportItem(_) =>

        // The todo-domain IR (`anthill-todo`'s work items, tools, feedback). scaland's
        // parser has NO production for any of these — they are `Item` shapes ported ahead
        // of the parser that would build them, so nothing can reach this arm today.
        case Item.DescribeItem(_) | Item.ProjectItem(_) | Item.ToolItem(_)
           | Item.WorkItemItem(_) | Item.FeedbackItem(_) | Item.ImportToolsItem(_) =>

        // Unreachable BY CONSTRUCTION: `walkScopes` routes the two scope-opening shapes
        // to `enterScope` and only everything else to `atItem`. Loud rather than silent,
        // because reaching it means that routing changed and a whole subtree is being
        // loaded as a leaf.
        case Item.NamespaceItem(_) | Item.SortWithBodyItem(_) =>
          errors += LoadError.Other(
            "internal: a scope-opening item reached LoadPass.atItem; walkScopes routes " +
            "those to enterScope", Span.empty)

  /** Load a rule under the proposal-032 grammar. `rule.heads` may be a single
    * positive head, multiple positive heads (conjunctive sugar), or a single
    * `Bottom` (denial). Mixing `Bottom` with positive heads is rejected.
    *
    * Translation:
    *   - single positive head            → one horn rule, head IS the KB head
    *   - labeled multi-head (positive)   → N horn rules, one per head, sharing body
    *   - unlabeled multi-head (positive) → error: needs a label for citation handle
    *   - single `Bottom` (denial)        → one rule with `Term.Bottom` as head
    *
    * (Scaland's KB has no `conclusion` field, so the rust transitional
    * translation that synthesizes a 0-arg label-functor as the KB head with
    * user heads moved to conclusion is collapsed into the literal conjunctive
    * expansion above. Citation infrastructure is not yet ported.)
    */
  private def loadRuleHeads(
    kb: KnowledgeBase,
    rule: Rule,
    fileTerms: SimpleTermStore,
    fileSym: SymbolTable,
    scope: kb.ScopeId,
    sortSort: TermId,
    errors: ArrayBuffer[LoadError]
  ): Unit =
    val vm = HashMap.empty[Int, VarId] // shared across heads + body
    val hasBottom = rule.heads.exists { case RuleHead.Bottom => true; case _ => false }
    val positiveHeads = rule.heads.collect { case RuleHead.TermHead(t) => t }

    if hasBottom && rule.heads.length > 1 then
      errors += LoadError.Other(
        "denial heads (`⊥`) cannot be combined with positive heads in a multi-head rule",
        rule.span)
      return

    if positiveHeads.length > 1 && rule.label.isEmpty then
      errors += LoadError.Other(
        "multi-head rule requires a label so the rule has a unique citation handle " +
        "(e.g. `rule my_law: H1, H2 :- B`)",
        rule.span)
      return

    // WI-1090: a BODYLESS head written with a connective that does not DEFINE
    // (`lhs === rhs`) is a definition that cannot define — refused before any clause is
    // asserted. A rule with a body is untouched: it is not an equation at all (§8.3) but
    // an ordinary law about the operator, which `totalfloat.anthill` writes.
    //
    // 061 WIDENS "BODYLESS" HERE, and only here among this method's three readings of
    // it: the emptiness this refusal is about is the one every equation reader uses
    // ([[ruleBodyIsEmptyConjunction]]), so `rule a === b :- true` — the explicit
    // spelling of the same empty body — is refused exactly as the arrow-less form is.
    // [[ruleReading]]'s question stays SYNTACTIC (`body.isDefined`), which is 061's own
    // split point; the two must not be fused.
    if ruleBodyIsEmptyConjunction(rule, fileTerms) then
      val refused = positiveHeads.exists(h =>
        refuseNonDefiningConnectiveHead(fileSym, fileTerms, h, fileTerms.spanOf(h), errors))
      if refused then return

    // PROPOSAL 061 — NO BODY ⇒ DECLARES. A body-less plain head brought its predicate
    // into existence in PASS 1b ([[DeclarePredicatePass]]) and asserts NOTHING here;
    // asserting it is what `fact` and the explicit `:- true` are for. The reading is
    // taken from the ONE decider both passes share, so the name pass 1 minted and the
    // clause this pass declines to store cannot disagree.
    ruleReading(rule, fileSym, fileTerms) match
      case RuleReading.Clause => ()
      case RuleReading.Declaration =>
        refuseDeclarationThatCannotStand(kb, rule, fileSym, fileTerms, scope, errors)
        return
      case RuleReading.DeclaresNothing =>
        errors += LoadError.Other(bodylessDeclaresNothingDetail(rule, fileSym, fileTerms), rule.span)
        return

    // WI-20260901-719FJ: a top-level body atom IS a goal, so a dotted paren-less
    // citation written there is the NAME. Only the top level, and that is a
    // MEASUREMENT rather than an omission — see `reallocTerm`'s `Term.Fn` arm, and
    // the row `negation in a rule body does not reach NAF, for any spelling`.
    // §6.1 — a top-level `true` is ERASED, so the body stays EMPTY. That is what makes
    // `rule H :- true` the exact spelling of `fact H`: the same clause, with the same
    // empty body, reached by the two syntaxes §6.1 says mean one thing. It is NOT what
    // `true` MEANS — that is J38JE's "a boolean constant in goal position is a SEARCH",
    // which belongs in the resolver and is not ported here. See
    // [[isEmptyConjunctionGoal]] for the split and for what scaland is missing.
    val kbBody = rule.body.map(_.filterNot(isEmptyConjunctionGoal(fileTerms, _)).map(b =>
      reallocTerm(kb, fileTerms, fileSym, b, scope, errors, vm, atGoal = true))).getOrElse(IndexedSeq.empty)

    if hasBottom then
      val botTerm = kb.alloc(Term.Bottom)
      kb.assertRule(botTerm, kbBody, sortSort, scope)
    else
      // One horn rule per head, sharing body (and shared var scope via vm).
      for headId <- positiveHeads do
        // WI-20260901-719FJ: a rule head is a LOGICAL SUBJECT.
        val kbHead = reallocTerm(kb, fileTerms, fileSym, headId, scope, errors, vm, atGoal = true)
        kb.assertRule(kbHead, kbBody, sortSort, scope)

  // ── Proof / Provides loaders (proposal 025 + 031) ────────────

  private def loadProof(
    kb: KnowledgeBase,
    p: anthill.parse.ProofDecl,
    fileSym: SymbolTable,
    scope: kb.ScopeId
  ): Unit =
    val targetStr = joinSegments(fileSym, p.target.segments)
    val targetTerm = kb.alloc(Term.Const(Literal.StringLit(targetStr)))
    val strategyStr = p.strategy.map(s => fileSym.name(s.name)).getOrElse("derivation")
    val strategyTerm = kb.alloc(Term.Const(Literal.StringLit(strategyStr)))
    val proofSym = kb.intern("proof_decl")
    val proofTerm = kb.alloc(Term.Fn(proofSym, IArray.empty,
      IArray(
        (kb.intern("target"), targetTerm),
        (kb.intern("strategy"), strategyTerm))))
    val proofSort = kb.makeNameTerm("ProofRecord")
    kb.assertFact(proofTerm, proofSort, scope)

  private def loadProvidesClause(
    kb: KnowledgeBase,
    pc: anthill.parse.ProvidesClause,
    fileSym: SymbolTable,
    scope: kb.ScopeId
  ): Unit =
    // Lossy: parameterized bindings (e.g. `Stack[T = Int]` vs `Stack[T = String]`)
    // collapse to the bare spec name. The witness pipeline (WI-157) replaces
    // this with a structured term that preserves bindings.
    // WI-869 (058 §3.8) — `pc.conditions` is consumed in SCAN PASS 2, by
    // `processProvidesConditions`, which links each condition's spec scope exactly as a
    // `requires` does. Nothing more is recorded HERE because scaland records no
    // requirement BINDINGS for any requirement — `processRequires` resolves the base
    // name and links the parent, and that is the whole of what a requirement does in
    // this implementation. The DICTIONARY half (one slot set per sort, strictness per
    // provision) has no peer at all: scaland has no `DictLayout` and no dispatch
    // resolution. See rustland's `typing::provider_dict_chain` for the rule, and wire it
    // in when scaland grows something that reads a dictionary.
    val specStr = specName(fileSym, pc.spec)
    val specTerm = kb.alloc(Term.Const(Literal.StringLit(specStr)))
    val provSym = kb.intern("provides_clause")
    // `sort_ref` is the scope AS A TERM — the sort the clause is about, read back by a
    // consumer of the fact. The domain beside it is the same scope in the other role
    // (WI-983), and only that one stopped being a term.
    val provTerm = kb.alloc(Term.Fn(provSym, IArray.empty,
      IArray(
        (kb.intern("sort_ref"), kb.scopeTerm(scope)),
        (kb.intern("spec"), specTerm))))
    val provSort = kb.makeNameTerm("Requirement")
    kb.assertFact(provTerm, provSort, scope)

  private def loadProvidesBlock(
    kb: KnowledgeBase,
    pb: anthill.parse.ProvidesBlock,
    fileTerms: SimpleTermStore,
    fileSym: SymbolTable,
    scope: kb.ScopeId,
    errors: ArrayBuffer[LoadError]
  ): Unit =
    if fileSym.name(pb.language) != "anthill" then return
    val ruleSort = findSortTerm(kb, "anthill.reflect.Rule")
    val factSort = findSortTerm(kb, "anthill.reflect.Fact")
    for item <- pb.items do item match
      case ProvidesItem.RuleI(r) =>
        loadRuleHeads(kb, r, fileTerms, fileSym, scope, ruleSort, errors)
      case ProvidesItem.RuleBlockI(rb) =>
        for r <- rb.entries do
          loadRuleHeads(kb, r, fileTerms, fileSym, scope, ruleSort, errors)
      case ProvidesItem.FactI(f) =>
        // WI-20260901-719FJ: the same head position, inside a `provides … language
        // anthill` block.
        val kbTerm = reallocTerm(kb, fileTerms, fileSym, f.term, scope, errors, atGoal = true)
        kb.assertFact(kbTerm, factSort, scope)
      case ProvidesItem.ProofI(p) =>
        loadProof(kb, p, fileSym, scope)
      // WI-862 (058 §4): PARSED, and deliberately not filed — the one thing this arm
      // must not do is call `loadProvidesClause`. That helper files the provision at
      // `scope`, and `scope` here is the ENCLOSING namespace, not the carrier: a
      // binding block opens the CARRIER's scope in rustland, and scaland's loader never
      // opens one. Reusing the helper would therefore assert `provides_clause(sort_ref:
      // <namespace>, spec: …)` — a provision filed against the wrong owner, silently.
      // Two other things make the omission cost nothing today: the guard above returns
      // for every language but `anthill`, and every block in the tree is `language
      // rust`; and scaland has no reader of provisions at all. Opening the carrier's
      // scope is the port that remains, and it is the same one `OperationMapI` below
      // is waiting on.
      case ProvidesItem.ProvidesClauseI(_)
         | ProvidesItem.ArtifactI(_)
         | ProvidesItem.CarrierI(_)
         | ProvidesItem.NamespaceMapI(_)
         // WI-876: parsed so scaland can READ a binding file that uses the clause;
         // scaland emits no `Implementation` fact either, so it emits no
         // `OperationMapping` — the fact-emitting half is rustland's (see
         // `emit_operation_mapping_facts`) and is the port that remains.
         | ProvidesItem.OperationMapI(_)
         // WI-889: same standing as `OperationMapI` — parsed so a binding file
         // using it can be read; no `ConstMapping` fact, for the same reason.
         | ProvidesItem.ConstMapI(_) =>

  private def specName(fileSym: SymbolTable, te: TypeExpr): String = te match
    case TypeExpr.Simple(n) => joinSegments(fileSym, n.segments)
    case TypeExpr.Parameterized(n, _) => joinSegments(fileSym, n.segments)
    case _ => "<spec>"

  // ── Term reallocation ─────────────────────────────────────────

  /** WI-582: whether `fn` is the parser-emitted typed-pattern marker
    * `typed_var(?x, type: T)` — matched by functor name AND its exact shape
    * (exactly one positional arg plus a `type` named arg). Mirrors rustland's
    * three-condition guard (`load.rs`): matching by name ALONE would crash on a
    * user functor `typed_var()` (`posArgs(0)` out of bounds) and silently strip
    * `typed_var(a, b)` to `a`. A non-marker `typed_var` falls through to normal
    * loading. */
  private def isTypedVarMarker(fn: Term.Fn, fileSym: SymbolTable): Boolean =
    fileSym.name(fn.functor) == "typed_var" &&
      fn.posArgs.length == 1 &&
      fn.namedArgs.exists { case (k, _) => fileSym.name(k) == "type" }

  /** WI-20260901-719FJ (rustland's twin, same ticket) — the dotted NAME a PAREN-LESS
    * citation spells, or `None` when this node is not one.
    *
    * A multi-segment name written without a trailing `(…)` has no application to hang a
    * functor on, so the parser folds it into a MINTED `field_access(object, Ref(field))`
    * chain (§6.7: a name with no application is dot projection). The chain is what the
    * spelling lowers to in EVERY position; what it MEANS is the position's to say — see
    * [[reallocTerm]]'s `atGoal` parameter.
    *
    * THREE GATES, mirroring rustland's `dotted_citation_name`: PROVENANCE and not
    * spelling (a hand-written `field_access(a, b)` is a call to whatever that name
    * denotes, so only `allocMinted` nodes are read); no named arguments (the parser emits
    * none on either of its two `field_access` paths); and NAME-ROOTED (a chain rooted in
    * a variable is `?x.f`, a projection on a value, with no name to be). */
  private def dottedCitationName(
    fileSym: SymbolTable, fileTerms: SimpleTermStore, termId: TermId
  ): Option[String] =
    if !fileTerms.isMinted(termId) then return None
    fileTerms.get(termId) match
      case fn: Term.Fn
        if fn.namedArgs.isEmpty && fileSym.name(fn.functor) == "field_access" => ()
      case _ => return None
    val segments = ArrayBuffer.empty[String]
    var cur = termId
    var done = false
    while !done do
      fileTerms.get(cur) match
        case id: Term.Ident =>
          segments += fileSym.name(id.sym)
          done = true
        case fn: Term.Fn
          if fileSym.name(fn.functor) == "field_access"
            && fn.posArgs.length == 2 && fn.namedArgs.isEmpty =>
          fileTerms.get(fn.posArgs(1)) match
            case r: Term.Ref =>
              segments += fileSym.name(r.sym)
              cur = fn.posArgs(0)
            case _ => return None
        case _ => return None
    Some(segments.reverse.mkString("."))

  /** Re-allocate a parse-time term into the KB's hash-consed store.
    * Uses varMap to share VarIds within a rule scope (same parse-time VarId → same KB VarId).
    *
    * WI-20260901-719FJ — AND IT DECIDES ONE THING BY POSITION: `atGoal` says whether this
    * node is a LOGICAL SUBJECT (a rule head, a `fact` head, a rule-body goal), which is
    * where a dotted PAREN-LESS citation is the NAME it spells rather than a `field_access`
    * chain. MEASURED BEFORE IT, and scaland's symptom was the LOUDER one: `field_access`
    * is a builtin whose tag is `BuiltinResult.Delay`, so a dotted paren-less GOAL
    * SUSPENDED and its residual counted as a solution — `rule r(1) :- zz.nope.tgt`, naming
    * a namespace that does not exist, loaded clean and ANSWERED. In head position the
    * clause landed under `field_access` and the rule was dropped: `rule ns.tgt :- b(1)`
    * answered nothing where `rule ns.tgt() :- b(1)` answered.
    */
  private def reallocTerm(
    kb: KnowledgeBase,
    fileTerms: SimpleTermStore,
    fileSym: SymbolTable,
    termId: TermId,
    scope: kb.ScopeId,
    errors: ArrayBuffer[LoadError],
    varMap: HashMap[Int, VarId] = HashMap.empty,
    /** WI-20260901-719FJ — is this node a LOGICAL SUBJECT: a rule head, a `fact` head or
      * a rule-body goal? See the collapse below for what it decides, and
      * [[dottedCitationName]] for what a dotted paren-less citation is. `false` for a
      * DATA slot, which keeps the chain: a fact's argument and the pattern that searches
      * for it must build ONE term. It is NOT propagated to any child — see the `Term.Fn`
      * arm for the measurement that says scaland has no goal-carrying argument yet. */
    atGoal: Boolean = false
  ): TermId =
    // WI-1009: refuse a PARSE-TIME MARKER before anything below reads its functor name.
    // Asked of the term's PROVENANCE and not its spelling, which is the whole fix: four
    // marker spellings are also `anthill.reflect.Expr` entity names, so the `Term.Fn` arm
    // below RESOLVED those four (the marker captured the entity symbol, and the KB gained
    // an Entity applied positionally to a shape that entity does not declare) while every
    // other marker fell through its `NotFound` rung and leaked as an undeclared predicate
    // with no diagnostic. One condition, one answer, and neither turns on a name.
    //
    // The subterms are deliberately NOT walked: one form, one diagnostic — a walk would
    // report the `pattern_var` under a `lambda` as a second, derived failure.
    //
    // `Bottom` stands in for the term that could not be built. It is the one carrier with
    // neither a name nor structure, so nothing downstream can read a resolution out of it,
    // and the load has already failed by the time anything looks. It does NOT collide with
    // `Bottom`'s other meaning — a `⊥` denial head — because a marker can never BE a head
    // or a fact term: both parse a `term`, and only `fnArg` admits a full `exprBody`, so a
    // marker reaches this loader nested as an ARGUMENT and never as the subject.
    fileTerms.markerOf(termId) match
      case Some(marker) =>
        errors += LoadError.ExpressionInTermPosition(marker, fileTerms.spanOf(termId))
        return kb.alloc(Term.Bottom)
      case None => ()

    // WI-20260901-719FJ — A LOGICAL SUBJECT'S DOTTED PAREN-LESS CITATION IS THE NAME IT
    // SPELLS. `rule ns.tgt :- b(1)` joins the predicate `ns.tgt`, `:- ns.tgt` runs it and
    // `fact ns.tgt` asserts it, exactly as the applied spelling `ns.tgt(…)` does — a
    // proposition has no projection reading, so the chain is the qualified name. The
    // result is BYTE-IDENTICAL to the `Term.Ident` arm below: a paren-less citation is
    // the same node whether its name has one segment or five — INCLUDING the promotion
    // of a resolved name to `Term.Ref` (WI-20260902-CZJ2N, which brought scaland's arm
    // into line with rustland's). Dropping the promotion here would re-open the split
    // one spelling over: `ns.tgt` would stay `Ident` while `ns.tgt()` canonicalized to
    // `Ref`, which is the very thing 719FJ closed for the dotted case.
    if atGoal then
      dottedCitationName(fileSym, fileTerms, termId) match
        case Some(name) =>
          val sym = resolveName(kb, name, scope, errors, fileTerms.spanOf(termId))
          return
            if kb.symbols.isResolved(sym) then kb.alloc(Term.Ref(sym))
            else kb.alloc(Term.Ident(sym))
        case None => ()

    fileTerms.get(termId) match
      case Term.Const(lit) => kb.alloc(Term.Const(lit))
      case Term.Var(v) =>
        // Map parse-time VarId to a fresh KB VarId (preserves sharing within
        // scope). Parse terms carry only `Global` vars; `assertRule`/`assertFact`
        // later close them to DeBruijn (WI-637). A DeBruijn/Rigid here is a bug
        // upstream — fail loudly rather than mis-map it.
        val vid = v match
          case Var.Global(g) => g
          case other =>
            throw new IllegalStateException(
              s"reallocTerm: parse term carries a non-Global var ($other); the parser emits only Global")
        val kbVid = varMap.getOrElseUpdate(vid.id, {
          val name = fileSym.name(vid.name)
          val kbSym = kb.intern(name)
          kb.freshVar(kbSym)
        })
        kb.alloc(Term.Var(Var.Global(kbVid)))
      case fn: Term.Fn if isTypedVarMarker(fn, fileSym) =>
        // WI-582: strip the typed-pattern marker `typed_var(?x, type: T)` back to
        // the bare `?x`. The parser wraps a `?x: T` rule-LHS arg as this marker;
        // rustland installs T as a per-DeBruijn `Type` bound and keeps the head
        // structurally bare so the discrimination tree indexes it identically to
        // an untyped head. scaland has no typer to enforce the bound, so we DROP
        // the type and keep only the bare variable — sound-conservative (the head
        // still matches the untyped form). Mirrors rustland's strip minus the
        // bound install.
        reallocTerm(kb, fileTerms, fileSym, fn.posArgs(0), scope, errors, varMap)
      // The three name-bearing carriers, and the only arms that resolve anything:
      // each hands `resolveName` the span its OWN parse term was allocated at
      // (WI-957), so a diagnostic lands on the occurrence, not on the enclosing
      // declaration and not nowhere.
      case fn: Term.Fn =>
        val name = fileSym.name(fn.functor)
        val kbFunctor = mintedConnectiveSymbol(kb, fileTerms, name, termId)
          .getOrElse(resolveName(kb, name, scope, errors, fileTerms.spanOf(termId)))
        // WI-20260901-719FJ — NO GOAL DESCENT, and that is a MEASUREMENT rather than an
        // omission. rustland routes `not`'s negand as a goal of its own
        // (`goal_arg_slots`); the twin here would be keyed on the resolved functor's
        // builtin tag, and it could never fire: `kb.getBuiltin` answers `None` for a
        // loaded rule-body `not(…)`, so scaland's NAF is not reached from a rule body at
        // all. Driven — `rule r(1) :- not(un(999))` over an EMPTY `un` answers 0, as does
        // `not(un(1))` over a provable one, and as does every nullary spelling, dotted or
        // not. There is no negand POSITION here to route yet; a branch nothing can drive
        // is not a fix. When `not` reaches NAF in a rule body, this is the line that has
        // to grow the descent, and the dotted spelling will be wrong there until it does.
        // Every argument is therefore DATA, which keeps a fact's slot and the pattern
        // that searches for it spelling one term.
        val kbPos = IArray.from(fn.posArgs.map(id =>
          reallocTerm(kb, fileTerms, fileSym, id, scope, errors, varMap)))
        val kbNamed = IArray.from(fn.namedArgs.map { (sym, id) =>
          val kbKeySym = kb.intern(fileSym.name(sym))
          (kbKeySym, reallocTerm(kb, fileTerms, fileSym, id, scope, errors, varMap))
        })
        kb.alloc(Term.Fn(kbFunctor, kbPos, kbNamed))
      case Term.Ref(sym) =>
        val name = fileSym.name(sym)
        val kbSym = resolveName(kb, name, scope, errors, fileTerms.spanOf(termId))
        kb.alloc(Term.Ref(kbSym))
      case Term.Ident(sym) =>
        val name = fileSym.name(sym)
        val kbSym = resolveName(kb, name, scope, errors, fileTerms.spanOf(termId))
        // WI-20260902-CZJ2N — PROMOTE A RESOLVED BARE NAME TO `Ref`, which is what
        // rustland's `convert_term_inner` has always done and scaland did not. Without
        // it the store still held two nullary forms: `tgtA` stayed `Term.Ident` while
        // `tgtA()` canonicalized to `Term.Ref`, so `rule ab(1) :- tgtA()` answered 0
        // against `rule tgtA :- …`. `Term.Ident` now means exactly one thing here — a
        // name nothing in scope answers.
        if kb.symbols.isResolved(kbSym) then kb.alloc(Term.Ref(kbSym))
        else kb.alloc(Term.Ident(kbSym))
      case Term.Bottom => kb.alloc(Term.Bottom)

  /** WI-888 — A MINTED CARRIER-AGNOSTIC CONNECTIVE DENOTES ITS KERNEL PRIMITIVE,
    * whatever a same-named symbol in scope holds. `None` for every ordinary functor.
    * Mirrors rustland's `minted_connective_symbol`.
    *
    * THE DEFECT, measured on the stdlib the moment WI-888 made `<=>` the only equational
    * spelling: `reflect.anthill` declares its own `unify(a: Term, b: Term, kb: KB)`
    * (proposal 049's term-level face), so the three `rule fact_monotonicity(…) <=>
    * constant() [simp]` rules written in that same namespace resolve their MINTED
    * connective through the ordinary ladder onto `anthill.reflect.unify` and file three
    * clauses under a 3-ary reflect operation. They load clean and fire nothing. The `=`
    * spelling had worked only because `anthill.reflect` happens to declare no `eq`.
    * scaland loads `reflect.anthill`, so it had the identical defect — found by review
    * after the rustland half shipped alone.
    *
    * WHY THE LINE IS AT *CARRIER-AGNOSTIC*, and why `eq` is deliberately NOT here: the
    * spec's Invariant (proposal 049) says `<=>` is structural-only and NEVER dispatches,
    * and §"`===` — the structural identity *test*" says the same of `===` — so no carrier
    * can mean something else by them, and a same-named symbol in scope is a collision
    * rather than an override. `=` is the opposite: it is semantic and DOES dispatch
    * through a carrier's own `eq` (WI-350/WI-444/WI-627, `Set.eq` / `Map.eq`), so the
    * ladder answering for it is the feature.
    *
    * `isMinted` is the whole gate (WI-948): a user's own `unify(a, b, kb)` CALL is never
    * minted and keeps the ordinary ladder, so `reflect.anthill`'s operation stays
    * callable by name from inside its own namespace.
    *
    * Both targets live in `anthill.kernel`, which is what makes the qualified name one
    * concatenation rather than a table; an unloaded target answers `None` and falls to
    * the ladder, the same defined answer rustland gives for the same reason (a KB with
    * no kernel has no kernel primitive for the operator to mean). */
  private def mintedConnectiveSymbol(
    kb: KnowledgeBase, fileTerms: SimpleTermStore, name: String, termId: TermId
  ): Option[TermSymbol] =
    if !fileTerms.isMinted(termId) then None
    else if !Pratt.isEqualityFamilyFunctor(name) || name == Pratt.eqFunctor then None
    else kb.tryResolveSymbol(s"anthill.kernel.$name")

  /** THE rung order a WRITTEN name resolves in, and the one place it is spelled.
    *
    * The `byQualifiedName` rung fires only for a DOTTED spelling — a name with no dot
    * is a SHORT name, and a short name is answered by scope, never by the global
    * qualified-name table. Before pass 3 the distinction did not bite, because only
    * dotted or namespaced declarations reached that table; pass 3 registers an
    * UNQUALIFIED entry for every top-level rule head, and taking that rung for a short
    * name then let a top-level `rule p(?y) :- q(?y)` capture an unrelated `sort S`'s
    * own `rule p(?x) :- q(?x)` — S's law was indexed under the global `p` and `S.p`
    * got no clauses at all, with no diagnostic.
    *
    * Callers differ ONLY in what they make of a miss, which is why the order lives here
    * and in neither of them: [[resolveName]] interns and carries on, [[processRequires]]
    * reports. WI-986 — `processRequires` used to ask `byQualifiedName` ALONE, the rung a
    * short name is never answered by, and then render `in scope '<the declaring scope>'`:
    * a claim about a search it had not performed, and false whenever the name really did
    * resolve there (an imported spec). One order is one thing to keep true; rustland has
    * had one (`resolve_name_in_kb`) all along. */
  private def lookupWritten(kb: KnowledgeBase, name: String, scope: kb.ScopeId): ResolveResult =
    if name.contains('.') then
      kb.symbols.byQualifiedName.get(name) match
        case Some(sym) => ResolveResult.Found(sym)
        case None => kb.symbols.resolveInScope(name, scope)
    else kb.symbols.resolveInScope(name, scope)

  /** Resolve a name in scope, falling back to intern for user-defined predicates.
    *
    * The rung order is [[lookupWritten]]'s; the mint guard in `scanRuleGoal` asks
    * `resolveInScope` directly, which is what keeps those two answering alike.
    *
    * WI-957: `span` is the OCCURRENCE's — the parse term this name was lifted out of,
    * carried by [[anthill.parse.SimpleTermStore.spanOf]]. It is a parameter and not a
    * lookup done here because the caller is the only one that knows WHICH term it took
    * the name from: `reallocTerm`'s `Term.Fn` arm resolves the functor, and its
    * arguments are separate terms with spans of their own. */
  private def resolveName(
    kb: KnowledgeBase, name: String, scope: kb.ScopeId,
    errors: ArrayBuffer[LoadError], span: Span
  ): TermSymbol =
    lookupWritten(kb, name, scope) match
      case ResolveResult.Found(sym) => sym
      case ResolveResult.Ambiguous(candidates) =>
        val qualNames = candidates.map(kb.qualifiedNameOf).toIndexedSeq
        // WI-957: the last locationless load diagnostic, closed. `scopeName` was
        // `""` for the same reason the span was empty — nothing was threaded here
        // — and it is the scope this very resolution was attempted in, so it is
        // read off `scope` rather than passed down a second channel that could
        // disagree with the scope actually searched.
        errors += LoadError.AmbiguousSymbol(
          name, qualNames, span, kb.scopeDisplayName(scope))
        kb.intern(name)
      case ResolveResult.NotFound =>
        kb.intern(name)

  /** Auto-import prelude sort contents into global scope.
    * Adds each sort defined directly under anthill.prelude as a parent of <global>,
    * making their exported operations (add, sub, mul, etc.) globally visible.
    *
    * Skips the primitive type sorts (Bool/Int/Float/BigInt/String) — their
    * operations conflict with the kernel builtins (`anthill.kernel.not`,
    * etc.) that Prelude.registerBuiltinTags already imports at global.
    * Mirrors rustland's `register_prelude`, which only imports explicit
    * global aliases instead of bulk-parenting every prelude sort.
    */
  private def autoImportPrelude(kb: KnowledgeBase): Unit =
    val globalScope = kb.globalScope
    val preludePrefix = "anthill.prelude."
    // Skip primitive type sorts (their ops collide with kernel builtins)
    // AND typeclass sorts whose generic ops collide with each other —
    // Iteration/Collection/IndexedSeq/Set/Map/LogicalStream all expose
    // `empty` / `insert` / `Effect`, and `Monad` exposes the very common
    // `map` / `flatMap` / `pure`. These should be reached via explicit
    // `import` clauses (as `option.anthill` imports `Monad`), mirroring
    // rustland's explicit-only global aliases.
    val skip = Set(
      "Bool", "Int64", "Float", "BigInt", "String",
      "Iteration", "Collection", "IndexedSeq", "Set", "Map", "LogicalStream",
      "Monad")
    for (qualName, sym) <- kb.symbols.byQualifiedName do
      if qualName.startsWith(preludePrefix) then
        val afterPrelude = qualName.substring(preludePrefix.length)
        if !afterPrelude.contains('.') && !skip.contains(afterPrelude) then
          // WI-M460D — `addExposureParent`, and this is the classification rather than
          // a default. What this bulk link is FOR is making the prelude's entity
          // variants (`some`, `nil`, …) writable bare at global scope; the `skip` set
          // above is the evidence, since it lists exactly the sorts whose OPERATIONS
          // collide when they arrive too. So it is filtered by `exposed` for the same
          // reason §8.6's link is, and stamping it `Declaration` — which reaches the
          // target whole — would deliver every prelude sort's members to the global
          // scope and re-create the collisions `skip` exists to avoid.
          kb.symbols.addExposureParent(globalScope, kb.symbols.scopeOf(sym))

  private def findSortTerm(kb: KnowledgeBase, qualName: String): TermId =
    kb.symbols.byQualifiedName.get(qualName) match
      case Some(sym) => kb.makeNameTermFromSym(sym)
      case None => kb.makeNameTerm(qualName)

  // ── Helpers ─────────────────────────────────────────────────

  private def joinSegments(symbols: SymbolTable, segments: IndexedSeq[TermSymbol]): String =
    segments.map(symbols.name).mkString(".")

  /** Is this scope a SORT body — i.e. does it have type parameters to add one to? Pass 1
    * asks it of an `enclosing` that may be `<global>`, which is a scope like any other but
    * whose symbol was never declared, so the answer there is `false` (WI-976: `false`
    * because `<global>` is Unresolved, not because the term failed a scope-shape test —
    * that test, and the `Option` it used to return, are gone). */
  private def isSortScope(kb: KnowledgeBase, scope: kb.ScopeId): Boolean =
    kb.symbols.get(kb.symbols.symbolOf(scope)) match
      case SymbolDef.Resolved(_, _, SymbolKind.Sort, _) => true
      case _ => false

  // `private[load]` so `Prelude.defineIn` joins by the SAME rule (WI-990) rather than
  // re-spelling it — including the empty-prefix arm, which a bare `s"$prefix.$name"`
  // would turn into a leading dot.
  private[load] def makeQualified(prefix: String, name: String): String =
    if prefix.isEmpty then name else s"$prefix.$name"

package anthill.load

import anthill.kb.{KnowledgeBase, SortKind}
import anthill.intern.{TermSymbol, SymbolTable, SymbolKind, SymbolDef, ResolveResult, ImportOrigin}
import anthill.term.{Term, TermId, Var, VarId, Literal}
import anthill.parse.*
import anthill.span.Span

import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}

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

    // Pass 2: Process requires and imports (all sorts exist now). A Selective
    // import of a RULE-INTRODUCED predicate cannot resolve here — its head-functor
    // symbol is not registered until pass 3 — so such names are deferred into
    // `pending` and retried below (WI-295).
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

    // Pass 3: register the functors that RULE HEADS introduce (WI-894/896/898).
    //
    // DIVERGES FROM RUSTLAND — WI-980 / 059 R6 IS NOT PORTED HERE, and the absence is a
    // gap, not a shape scaland lacks. OWNED BY WI-20260821-SBZ2A, which carries the
    // algorithm and the acceptance rows. `scanRuleGoal`'s guard below asks whether the name
    // ALREADY DENOTES, and this loop mints as it walks, so the table it reads is the one
    // it is filling: `namespace demo { rule p(1); sort Rec { rule p(2) } }` is ONE
    // predicate with two clauses, and moving `rule p(1)` below the sort makes it TWO.
    // Rustland now decides it on a question the pass cannot move — does some scope this
    // one can SEE already INTRODUCE the name — answered by `Ownership` over
    // `SymbolTable.resolve_captured_name_with_overlay`, which runs the resolver's OWN
    // walk over an overlay of the program's rule heads (a second traversal built from
    // the parent-eligibility filter alone refused three programs that load clean).
    //
    // A ROUND-BASED FIXPOINT, not a recursion: the relation is non-monotone (the more
    // scopes own a name, the more heads yield, so the fewer own it), so a demand-driven
    // recursion has to break cycles provisionally, and caching anything computed under
    // such a break reintroduced the very order dependence — measured, six permutations
    // of three files gave two different programs. Three rules instead: a scope that can
    // see nothing even optimistically OWNS; a scope that sees a settled owner from every
    // file YIELDS; and a remaining tie is broken inside ONE strongly-connected
    // component, by real enclosing edges, never across the whole undecided set.
    // `<global>` may own what is written at it and is never yielded to.
    //
    // docs/kernel-language.md §"A rule head functor is resolved, not declared" states
    // the rule for BOTH implementations; this one does not yet meet it.
    for (file, fid) <- files.zip(fileIds) do
      kb.symbols.setAskingFile(Some(fid))
      walkScopes(RuleHeadPass(kb, file.symbols, file.terms, errors), file.items)

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
    * WI-949: ONE walker, not one per pass. The three scan passes and the loader each
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
      * `ImportPass` handles imports, `RuleHeadPass` handles 2 of 23 kinds), where a
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
    * so its `enterScope` defines rather than resolving, and can never miss. */
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

        case Item.RuleItem(rule) =>
          rule.label.foreach { label =>
            val shortName = joinSegments(fileSym, label.segments)
            val qualName = makeQualified(prefix, shortName)
            kb.symbols.define(shortName, qualName, SymbolKind.Rule, scope)
          }

        case Item.RuleBlockItem(block) =>
          for rule <- block.entries do
            rule.label.foreach { label =>
              val shortName = joinSegments(fileSym, label.segments)
              val qualName = makeQualified(prefix, shortName)
              kb.symbols.define(shortName, qualName, SymbolKind.Rule, scope)
            }

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

  /** Pass 3 — WI-894/896/898: register the functor a RULE HEAD introduces. `ite` is the
    * motivating case — `bool.anthill` declares no `ite` operation; its two `[simp]`
    * equations ARE its definition, and `int64.anthill` / `ordered.anthill` reach it by
    * `import anthill.prelude.Bool.{ite}`. Without this pass that import resolves to
    * nothing, which is how the whole stdlib failed to load.
    *
    * Runs after pass 2 because it must see whether the name ALREADY denotes: a head
    * naming a declared operation references it, and introduces nothing. */
  private final class RuleHeadPass(
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
        case Item.RuleItem(rule) => scanRuleGoal(kb, rule, fileSym, fileTerms, scope, prefix)
        case Item.RuleBlockItem(block) =>
          for rule <- block.entries do
            scanRuleGoal(kb, rule, fileSym, fileTerms, scope, prefix)

        case _ =>

  private def scanRuleGoal(
    kb: KnowledgeBase,
    rule: Rule,
    fileSym: SymbolTable,
    fileTerms: SimpleTermStore,
    scope: kb.ScopeId,
    prefix: String
  ): Unit =
    for (name, kind) <- ruleIntroducedFunctor(rule, fileSym, fileTerms) do
      // Already denotes something in this scope ⇒ the head REFERENCES it, and a
      // second definition would shadow the real target for the whole scope.
      // `defineSymbolOnce`, not `define`: `define` writes `byQualifiedName` for the
      // qualified name UNCONDITIONALLY whenever the SHORT name is new in the target
      // scope, so a rule head in a re-opened namespace could replace a builtin's
      // mapping (the case that gate was written for — see its doc).
      if !kb.symbols.resolveInScope(name, scope).denotes then
        defineSymbolOnce(kb, name, makeQualified(prefix, name), kind, scope)

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
    val equationLhs = if rule.body.isDefined then None else parseEquationLhs(fileSym, fileTerms, headId)
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
    linkSpecScope(kb, req.typeExpr, req.span, "requires", fileSym, scope, errors)

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
      linkSpecScope(kb, c, pc.span, "provides … :-", fileSym, scope, errors))

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
      linkSpecScope(kb, pc.spec, pc.span, "provides", fileSym, scope, silenced)
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
    * `clause` names the writer for the diagnostic. */
  private def linkSpecScope(
    kb: KnowledgeBase,
    typeExpr: TypeExpr,
    span: Span,
    clause: String,
    fileSym: SymbolTable,
    scope: kb.ScopeId,
    errors: ArrayBuffer[LoadError]
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
              .foreach(p => kb.symbols.addParent(scope, p, isEnclosing = false))
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
    if rule.body.isEmpty then
      val refused = positiveHeads.exists(h =>
        refuseNonDefiningConnectiveHead(fileSym, fileTerms, h, fileTerms.spanOf(h), errors))
      if refused then return

    // WI-20260901-719FJ: a top-level body atom IS a goal, so a dotted paren-less
    // citation written there is the NAME. Only the top level, and that is a
    // MEASUREMENT rather than an omission — see `reallocTerm`'s `Term.Fn` arm, and
    // the row `negation in a rule body does not reach NAF, for any spelling`.
    val kbBody = rule.body.map(_.map(b =>
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

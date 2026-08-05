package anthill.load

import anthill.kb.{KnowledgeBase, SortKind}
import anthill.intern.{TermSymbol, SymbolTable, SymbolKind, SymbolDef, ResolveResult}
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

    // Pass 1: Define all names
    for file <- files do
      walkScopes(DefinePass(kb, file.symbols), file.items)

    // Pass 2: Process requires and imports (all sorts exist now). A Selective
    // import of a RULE-INTRODUCED predicate cannot resolve here — its head-functor
    // symbol is not registered until pass 3 — so such names are deferred into
    // `pending` and retried below (WI-295).
    val pending = ArrayBuffer.empty[PendingImport[kb.ScopeId]]
    for file <- files do
      walkScopes(ImportPass(kb, file.symbols, errors, pending), file.items)

    // Post-pass: auto-import prelude sort contents into global scope. BEFORE pass 3,
    // and that ordering is load-bearing: pass 3's mint guard asks whether a head's
    // name ALREADY denotes, so every name a declaration provides must be visible
    // first. Otherwise `rule eq_refl: eq(?a, ?a) <=> true` (stdlib `eq.anthill`,
    // where `eq` is PartialEq's declared operation reached through the requires
    // chain) mints a SECOND `eq` and makes the real one ambiguous. rustland reaches
    // the same state by registering the prelude before `scan_definitions` runs.
    autoImportPrelude(kb)

    // Pass 3: register the functors that RULE HEADS introduce (WI-894/896/898).
    for file <- files do
      walkScopes(RuleHeadPass(kb, file.symbols, file.terms, errors), file.items)

    // Pass 4 (WI-295): retry the deferred predicate imports. Pass 3's head-functor
    // symbols are in `byQualifiedName` now, so a cross-namespace rule-predicate
    // import resolves like any declared name — erroring only if it is still unbound.
    for p <- pending do
      resolveSelectiveImport(kb, p.target, p.path, p.short) match
        case Some(sym) => kb.symbols.addImport(p.scope, p.short, sym)
        // WI-962: the scope name comes off the SYMBOL, like the other two raise sites, and
        // not off `p.path` — the written import spelling. The two agree (a `define` writes
        // one qualified name into both the `byQualifiedName` key and the `SymbolDef`, and
        // that lookup is where `target` came from), but agreeing is not deriving: with the
        // spelling the field had a second source that could drift, which is the whole
        // failure this WI is about. `path` is a resolution INPUT here, nothing else.
        case None =>
          errors += LoadError.UnresolvedName(p.short, p.span, kb.qualifiedNameOf(p.target))

    errors

  /** Load a parsed file into the KB (Phase 2 — after scanDefinitions). */
  def load(kb: KnowledgeBase, file: ParsedFile): ArrayBuffer[LoadError] =
    val errors = ArrayBuffer.empty[LoadError]
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

    /** Every item that does not open a scope, with the scope and prefix enclosing it. */
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
          if variants.nonEmpty then
            kb.symbols.addParent(target, sortScope, isEnclosing = false)
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
          // type-params to scan. scaland records only the symbol; the declared
          // type + optional body are not loaded (no typer/eval to consume them),
          // mirroring how operation bodies/effects are left inert here.
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
    * defined in `_global`; nothing ever linked it to a scope called `anthill.prelude`. So
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
    * `anthill.reflect.not` is FIRST registered as a builtin by
    * `Prelude.registerBuiltinTags` (into the prelude's `anthill.reflect` scope); the
    * stdlib then ALSO declares `operation not(...)` in reflect.anthill, and minting a
    * SECOND `anthill.reflect.not` makes a bare rule-body use (`:- not(...)` in
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
    pending: ArrayBuffer[PendingImport[kb.ScopeId]]
  ) extends ScopePass:

    // The import list attached to a `namespace` and to a `sort … end` body go through
    // the SAME `processImports`; only the scope differs, and the walk already carries it.
    def enterScope(
      decl: ScopeDecl, writtenName: String, qualName: String, prefix: String, enclosing: kb.ScopeId
    ): Option[kb.ScopeId] =
      lookupScope(kb, qualName, decl.name.span, errors).map { scope =>
        processImports(kb, decl.imports, fileSym, scope, errors, pending)
        scope
      }

    def atItem(item: Item, scope: kb.ScopeId, prefix: String): Unit =
      item match
        case Item.RequiresDeclItem(req) =>
          processRequires(kb, req, fileSym, scope, errors)

        // WI-727 (proposal 056): "at most one variadic capture parameter, and
        // trailing" is checked HERE and not in the parser — the diagnostic quotes the
        // QUALIFIED operation name, which only the loader has. Mirrors rustland's
        // `load.rs` check. Both spellings reach it: a free operation and one written
        // inside a braced `operation { … }` block.
        case Item.OperationItem(op) =>
          checkVariadicCapture(fileSym, prefix, op, errors)

        case Item.OperationBlockItem(block) =>
          for op <- block.entries do checkVariadicCapture(fileSym, prefix, op, errors)

        // WI-853: a TOP-LEVEL import feeds `_global` — the scope a file's top-level
        // declarations are defined in. Same `processImports` the namespace-attached
        // and sort-attached lists go through; only the scope differs, and it is
        // already the one this walk carries.
        //
        // Only ever the top level: inside a namespace / sort body the parser's
        // `bodyContent` consumes an `import` before `declaration` is tried, so it
        // lands in that body's `imports` list and never reaches this arm as an Item.
        case Item.ImportItem(imp) =>
          processImports(kb, Seq(imp), fileSym, scope, errors, pending)

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
      case _ => None

  /** The LHS operand of a parse-layer EQUATION head (`lhs = rhs` / `<=>` / `===`), or
    * `None` when `head` is not one. The connective sits at the head with its subject
    * at position 0; arity 2 is load-bearing — a 2-ary head is told from an equation by
    * the CONNECTIVE (`Pratt.isEquationFunctor`, the one source of truth for the
    * functors the infix desugar mints), never by arity alone. */
  private def parseEquationLhs(
    fileSym: SymbolTable, fileTerms: SimpleTermStore, head: TermId
  ): Option[TermId] =
    // `isMinted` FIRST, and it is not redundant with the name test: only a node the
    // infix desugar built is a written connective. Without it the decision would be
    // re-derived from a name blocklist — the thing `SimpleTermStore.minted` exists to
    // replace — and a legitimate 2-ary predicate head spelled as an ordinary call
    // (`rule eq(?a, ?b)`) would be read as an equation whose "LHS" is a variable,
    // introducing nothing at all. (rustland's `parse_equation_lhs` still tests the
    // name alone; this is a deliberate divergence, and the fix belongs there too.)
    if !fileTerms.isMinted(head) then None
    else fileTerms.get(head) match
      case fn: Term.Fn
        if fn.posArgs.length == 2 && fn.namedArgs.isEmpty
        && Pratt.isEquationFunctor(fileSym.name(fn.functor)) => Some(fn.posArgs(0))
      case _ => None

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
    scope: S, short: String, target: TermSymbol, span: Span, path: String)

  /** Resolve one name of a `Selective` import against the imported symbol `target`
    * (whose qualified name is `pathStr`). THE one resolution both pass 2 and the
    * pass-4 retry use — the retry differs only in WHEN it runs, never in which rungs
    * it tries, so a name that pass 3 has since registered resolves through exactly the
    * ladder that first missed it. */
  private def resolveSelectiveImport(
    kb: KnowledgeBase, target: TermSymbol, pathStr: String, name: String
  ): Option[TermSymbol] =
    kb.symbols.resolveInScope(name, kb.symbols.scopeOf(target)) match
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
    pending: ArrayBuffer[PendingImport[kb.ScopeId]]
  ): Unit =
    for imp <- imports do
      val pathStr = joinSegments(fileSym, imp.path.segments)
      kb.symbols.byQualifiedName.get(pathStr) match
        case Some(sym) =>
          imp.kind match
            case ImportKind.Plain =>
              val short = fileSym.name(imp.path.last)
              kb.symbols.addImport(scope, short, sym)
            case ImportKind.Selective(names) =>
              for n <- names do
                val name = joinSegments(fileSym, n.segments)
                resolveSelectiveImport(kb, sym, pathStr, name) match
                  case Some(s) => kb.symbols.addImport(scope, name, s)
                  // WI-295: a RULE-INTRODUCED predicate's head-functor symbol is not
                  // registered until pass 3, which runs AFTER imports — so a selective
                  // import of one (`import anthill.prelude.Bool.{ite}`, stdlib
                  // int64/ordered) cannot resolve here. Defer instead of erroring; the
                  // post-pass-3 retry re-resolves it and errors only if still unbound.
                  case None =>
                    pending += PendingImport(scope, name, sym, n.span, pathStr)
            case ImportKind.Wildcard =>
              // WI-988: a wildcard brings a scope's CONTENTS in, so the path has to name
              // something with contents — a namespace, or a sort (§5.1 names both).
              parentScopeOf(kb, sym, Set(SymbolKind.Namespace, SymbolKind.Sort),
                s"the wildcard import `$pathStr.*`", imp.path.span, errors)
                .foreach(p => kb.symbols.addParent(scope, p, isEnclosing = false))
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
    (req.typeExpr match
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
              s"`requires $nameStr`", name.span, errors)
              .foreach(p => kb.symbols.addParent(scope, p, isEnclosing = false))
          case ResolveResult.Ambiguous(candidates) =>
            errors += LoadError.AmbiguousSymbol(
              nameStr, candidates.map(kb.qualifiedNameOf).toIndexedSeq,
              name.span, kb.scopeDisplayName(scope))
          case ResolveResult.NotFound =>
            errors += LoadError.UnresolvedName(nameStr, name.span, kb.scopeDisplayName(scope))
      case None => // Every other `TypeExpr` — an arrow, a tuple, a bare `?T` — is a type
                   // and not a spec; those are refused by the parser's `requires`
                   // production, so there is no reachable arm here to raise from.

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
          val kbTerm = reallocTerm(kb, fileTerms, fileSym, fact.term, scope, errors)
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

        case _ => // Other items

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

    val kbBody = rule.body.map(_.map(b =>
      reallocTerm(kb, fileTerms, fileSym, b, scope, errors, vm))).getOrElse(IndexedSeq.empty)

    if hasBottom then
      val botTerm = kb.alloc(Term.Bottom)
      kb.assertRule(botTerm, kbBody, sortSort, scope)
    else
      // One horn rule per head, sharing body (and shared var scope via vm).
      for headId <- positiveHeads do
        val kbHead = reallocTerm(kb, fileTerms, fileSym, headId, scope, errors, vm)
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
        val kbTerm = reallocTerm(kb, fileTerms, fileSym, f.term, scope, errors)
        kb.assertFact(kbTerm, factSort, scope)
      case ProvidesItem.ProofI(p) =>
        loadProof(kb, p, fileSym, scope)
      case ProvidesItem.ArtifactI(_)
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

  /** Re-allocate a parse-time term into the KB's hash-consed store.
    * Uses varMap to share VarIds within a rule scope (same parse-time VarId → same KB VarId).
    */
  private def reallocTerm(
    kb: KnowledgeBase,
    fileTerms: SimpleTermStore,
    fileSym: SymbolTable,
    termId: TermId,
    scope: kb.ScopeId,
    errors: ArrayBuffer[LoadError],
    varMap: HashMap[Int, VarId] = HashMap.empty
  ): TermId =
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
        val kbFunctor = resolveName(kb, name, scope, errors, fileTerms.spanOf(termId))
        val kbPos = IArray.from(fn.posArgs.map(id => reallocTerm(kb, fileTerms, fileSym, id, scope, errors, varMap)))
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
        kb.alloc(Term.Ident(kbSym))
      case Term.Bottom => kb.alloc(Term.Bottom)

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
    * Adds each sort defined directly under anthill.prelude as a parent of _global,
    * making their exported operations (add, sub, mul, etc.) globally visible.
    *
    * Skips the primitive type sorts (Bool/Int/Float/BigInt/String) — their
    * operations conflict with the kernel builtins (`anthill.reflect.not`,
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
          kb.symbols.addParent(globalScope, kb.symbols.scopeOf(sym), isEnclosing = false)

  private def findSortTerm(kb: KnowledgeBase, qualName: String): TermId =
    kb.symbols.byQualifiedName.get(qualName) match
      case Some(sym) => kb.makeNameTermFromSym(sym)
      case None => kb.makeNameTerm(qualName)

  // ── Helpers ─────────────────────────────────────────────────

  private def joinSegments(symbols: SymbolTable, segments: IndexedSeq[TermSymbol]): String =
    segments.map(symbols.name).mkString(".")

  /** Is this scope a SORT body — i.e. does it have type parameters to add one to? Pass 1
    * asks it of an `enclosing` that may be `_global`, which is a scope like any other but
    * whose symbol was never declared, so the answer there is `false` (WI-976: `false`
    * because `_global` is Unresolved, not because the term failed a scope-shape test —
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

  // ── List / Option builders ────────────────────────────────────

  private def buildList(kb: KnowledgeBase, items: IndexedSeq[TermId]): TermId =
    val nilSym = kb.tryResolveSymbol("anthill.prelude.List.nil").getOrElse(kb.intern("nil"))
    val consSym = kb.tryResolveSymbol("anthill.prelude.List.cons").getOrElse(kb.intern("cons"))
    val headKey = kb.intern("head")
    val tailKey = kb.intern("tail")
    var list = kb.alloc(Term.Fn(nilSym, IArray.empty, IArray.empty))
    var i = items.length - 1
    while i >= 0 do
      list = kb.alloc(Term.Fn(consSym, IArray.empty, IArray((headKey, items(i)), (tailKey, list))))
      i -= 1
    list

  private def buildNone(kb: KnowledgeBase): TermId =
    val noneSym = kb.tryResolveSymbol("anthill.prelude.Option.none").getOrElse(kb.intern("none"))
    kb.alloc(Term.Fn(noneSym, IArray.empty, IArray.empty))

  private def buildSome(kb: KnowledgeBase, value: TermId): TermId =
    val someSym = kb.tryResolveSymbol("anthill.prelude.Option.some").getOrElse(kb.intern("some"))
    val valueKey = kb.intern("value")
    kb.alloc(Term.Fn(someSym, IArray.empty, IArray((valueKey, value))))

  // ── Expression conversion ─────────────────────────────────────

  /** Convert a parse-time expression term into the KB's Expr representation.
    * Dispatches on functor name to restructure positional args into named args.
    */
  private def convertExprTerm(
    kb: KnowledgeBase, fileTerms: SimpleTermStore, fileSym: SymbolTable,
    parseId: TermId, scope: kb.ScopeId, errors: ArrayBuffer[LoadError],
    varMap: HashMap[Int, VarId]
  ): TermId =
    fileTerms.get(parseId) match
      case fn: Term.Fn =>
        val name = fileSym.name(fn.functor)
        name match
          case "match_expr" => loadMatchExpr(kb, fileTerms, fileSym, fn.posArgs, scope, errors, varMap)
          case "match_branch" => loadMatchBranch(kb, fileTerms, fileSym, fn.posArgs, scope, errors, varMap)
          case "if_expr" => loadIfExpr(kb, fileTerms, fileSym, fn.posArgs, scope, errors, varMap)
          case "let_expr" => loadLetExpr(kb, fileTerms, fileSym, fn.posArgs, scope, errors, varMap)
          case "lambda_expr" => loadLambdaExpr(kb, fileTerms, fileSym, fn.posArgs, scope, errors, varMap)
          case "pattern_var" => loadPatternVar(kb, fileTerms, fileSym, fn.posArgs, scope, errors, varMap)
          case "pattern_wildcard" => loadPatternWildcard(kb)
          case "pattern_literal" => loadPatternLiteral(kb, fileTerms, fileSym, fn.posArgs, scope, errors, varMap)
          case "pattern_constructor" => loadPatternConstructor(kb, fileTerms, fileSym, fn.posArgs, scope, errors, varMap)
          case "pattern_tuple" => loadPatternTuple(kb, fileTerms, fileSym, fn.posArgs, scope, errors, varMap)
          // WI-582: strip a `typed_var(?x, type: T)` marker back to the bare `?x`
          // here too (a typed arg in an expression body), matching `reallocTerm`.
          // Guarded on the exact marker shape (name + 1 pos + `type` named) — a
          // non-marker `typed_var` falls through to `loadApplyOrConstructor`.
          case "typed_var" if isTypedVarMarker(fn, fileSym) =>
            exprRec(Ctx(kb, fileTerms, fileSym, scope, errors, varMap), fn.posArgs(0))
          case _ => loadApplyOrConstructor(kb, fileTerms, fileSym, fn.functor, fileTerms.spanOf(parseId),
                                           fn.posArgs, fn.namedArgs, scope, errors, varMap)
      case Term.Const(_) => loadLiteralExpr(kb, fileTerms, fileSym, parseId, scope, errors, varMap)
      case Term.Ident(_) => loadVarRef(kb, fileTerms, fileSym, parseId, scope, errors, varMap)
      case _ => reallocTerm(kb, fileTerms, fileSym, parseId, scope, errors, varMap)

  /** Shorthand for the recursive call's parameters.
    *
    * A CLASS and not the 6-tuple it was (WI-1004): `scope` is a `kb.ScopeId`, which is a
    * type only where `kb` is a stable identifier, and a tuple's components have no names
    * for the others to depend on. One parameter list, not two: a class parameter is
    * already a stable identifier for the parameters that FOLLOW it in the same list. */
  private final class Ctx(
    val kb: KnowledgeBase, val fileTerms: SimpleTermStore, val fileSym: SymbolTable,
    val scope: kb.ScopeId, val errors: ArrayBuffer[LoadError], val vm: HashMap[Int, VarId])

  private def exprRec(ctx: Ctx, parseId: TermId): TermId =
    convertExprTerm(ctx.kb, ctx.fileTerms, ctx.fileSym, parseId, ctx.scope, ctx.errors, ctx.vm)

  private def loadMatchExpr(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    posArgs: IArray[TermId], scope: kb.ScopeId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val ctx = Ctx(kb, ft, fs, scope, errors, vm)
    val scrutinee = exprRec(ctx, posArgs(0))
    val branches = IArray.tabulate(posArgs.length - 1)(i => exprRec(ctx, posArgs(i + 1)))
    val branchList = buildList(kb, branches.toIndexedSeq)
    val matchSym = kb.resolveSymbol("anthill.reflect.Expr.match_expr")
    kb.alloc(Term.Fn(matchSym, IArray.empty,
      IArray((kb.intern("scrutinee"), scrutinee), (kb.intern("branches"), branchList))))

  private def loadMatchBranch(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    posArgs: IArray[TermId], scope: kb.ScopeId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val ctx = Ctx(kb, ft, fs, scope, errors, vm)
    val pattern = exprRec(ctx, posArgs(0))
    val body = exprRec(ctx, posArgs(1))
    val guard = buildNone(kb)
    val branchSym = kb.resolveSymbol("anthill.reflect.MatchBranch")
    kb.alloc(Term.Fn(branchSym, IArray.empty,
      IArray((kb.intern("pattern"), pattern), (kb.intern("guard"), guard), (kb.intern("body"), body))))

  private def loadIfExpr(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    posArgs: IArray[TermId], scope: kb.ScopeId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val ctx = Ctx(kb, ft, fs, scope, errors, vm)
    val cond = exprRec(ctx, posArgs(0))
    val thenBranch = exprRec(ctx, posArgs(1))
    val elseBranch = exprRec(ctx, posArgs(2))
    val ifSym = kb.resolveSymbol("anthill.reflect.Expr.if_expr")
    kb.alloc(Term.Fn(ifSym, IArray.empty,
      IArray((kb.intern("cond"), cond), (kb.intern("then_branch"), thenBranch), (kb.intern("else_branch"), elseBranch))))

  private def loadLetExpr(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    posArgs: IArray[TermId], scope: kb.ScopeId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val ctx = Ctx(kb, ft, fs, scope, errors, vm)
    val pattern = exprRec(ctx, posArgs(0))
    val value = exprRec(ctx, posArgs(1))
    val body = exprRec(ctx, posArgs(2))
    val letSym = kb.resolveSymbol("anthill.reflect.Expr.let_expr")
    kb.alloc(Term.Fn(letSym, IArray.empty,
      IArray((kb.intern("pattern"), pattern), (kb.intern("value"), value), (kb.intern("body"), body))))

  private def loadLambdaExpr(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    posArgs: IArray[TermId], scope: kb.ScopeId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val ctx = Ctx(kb, ft, fs, scope, errors, vm)
    val param = exprRec(ctx, posArgs(0))
    val body = exprRec(ctx, posArgs(1))
    val lambdaSym = kb.resolveSymbol("anthill.reflect.Expr.lambda_expr")
    kb.alloc(Term.Fn(lambdaSym, IArray.empty,
      IArray((kb.intern("param"), param), (kb.intern("body"), body))))

  private def loadVarRef(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    parseId: TermId, scope: kb.ScopeId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val nameRef = ft.get(parseId) match
      case Term.Ident(sym) =>
        val kbSym = kb.intern(fs.name(sym))
        kb.alloc(Term.Ref(kbSym))
      case _ => reallocTerm(kb, ft, fs, parseId, scope, errors, vm)
    val varRefSym = kb.resolveSymbol("anthill.reflect.Expr.var_ref")
    kb.alloc(Term.Fn(varRefSym, IArray.empty, IArray((kb.intern("name"), nameRef))))

  private def loadLiteralExpr(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    parseId: TermId, scope: kb.ScopeId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    ft.get(parseId) match
      case Term.Const(lit) =>
        val (entityName, valueTerm) = lit match
          case Literal.IntLit(n) => ("anthill.reflect.Expr.int_lit", kb.alloc(Term.Const(Literal.IntLit(n))))
          case Literal.BigIntLit(n) => ("anthill.reflect.Expr.bigint_lit", kb.alloc(Term.Const(Literal.BigIntLit(n))))
          case Literal.FloatLit(f) => ("anthill.reflect.Expr.float_lit", kb.alloc(Term.Const(Literal.FloatLit(f))))
          case Literal.StringLit(s) => ("anthill.reflect.Expr.string_lit", kb.alloc(Term.Const(Literal.StringLit(s))))
          case Literal.BoolLit(b) => ("anthill.reflect.Expr.bool_lit", kb.alloc(Term.Const(Literal.BoolLit(b))))
        val entitySym = kb.resolveSymbol(entityName)
        kb.alloc(Term.Fn(entitySym, IArray.empty, IArray((kb.intern("value"), valueTerm))))
      case _ => reallocTerm(kb, ft, fs, parseId, scope, errors, vm)

  private def loadApplyOrConstructor(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    parseFunctor: TermSymbol, functorSpan: Span,
    posArgs: IArray[TermId], namedArgs: IArray[(TermSymbol, TermId)],
    scope: kb.ScopeId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val ctx = Ctx(kb, ft, fs, scope, errors, vm)
    val kbFunctor = resolveName(kb, fs.name(parseFunctor), scope, errors, functorSpan)
    val isEntity = kb.symbols.get(kbFunctor) match
      case SymbolDef.Resolved(_, _, SymbolKind.Entity, _) => true
      case _ => false

    val applyArgSym = kb.resolveSymbol("anthill.reflect.ApplyArg")
    val argNameKey = kb.intern("name")
    val argValueKey = kb.intern("value")

    val argTerms = scala.collection.mutable.ArrayBuffer.empty[TermId]
    for tid <- posArgs do
      val value = exprRec(ctx, tid)
      val none = buildNone(kb)
      argTerms += kb.alloc(Term.Fn(applyArgSym, IArray.empty,
        IArray((argNameKey, none), (argValueKey, value))))
    for (sym, tid) <- namedArgs do
      val value = exprRec(ctx, tid)
      val nameRef = kb.alloc(Term.Ref(kb.intern(fs.name(sym))))
      val someName = buildSome(kb, nameRef)
      argTerms += kb.alloc(Term.Fn(applyArgSym, IArray.empty,
        IArray((argNameKey, someName), (argValueKey, value))))
    val argsList = buildList(kb, argTerms.toIndexedSeq)
    val nameRef = kb.alloc(Term.Ref(kbFunctor))

    if isEntity then
      val ctorSym = kb.resolveSymbol("anthill.reflect.Expr.constructor")
      kb.alloc(Term.Fn(ctorSym, IArray.empty,
        IArray((kb.intern("name"), nameRef), (kb.intern("args"), argsList))))
    else
      val applySym = kb.resolveSymbol("anthill.reflect.Expr.apply")
      kb.alloc(Term.Fn(applySym, IArray.empty,
        IArray((kb.intern("fn"), nameRef), (kb.intern("args"), argsList))))

  // ── Pattern conversion ───────────────────────────────────────

  private def loadPatternVar(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    posArgs: IArray[TermId], scope: kb.ScopeId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val nameRef = ft.get(posArgs(0)) match
      case Term.Ident(sym) =>
        val kbSym = kb.intern(fs.name(sym))
        kb.alloc(Term.Ref(kbSym))
      case _ => reallocTerm(kb, ft, fs, posArgs(0), scope, errors, vm)
    val typeAnn = buildNone(kb)
    val varPatternSym = kb.resolveSymbol("anthill.reflect.Pattern.var_pattern")
    kb.alloc(Term.Fn(varPatternSym, IArray.empty,
      IArray((kb.intern("name"), nameRef), (kb.intern("type_ann"), typeAnn))))

  private def loadPatternWildcard(kb: KnowledgeBase): TermId =
    val wildcardSym = kb.resolveSymbol("anthill.reflect.Pattern.wildcard")
    kb.alloc(Term.Fn(wildcardSym, IArray.empty, IArray.empty))

  private def loadPatternLiteral(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    posArgs: IArray[TermId], scope: kb.ScopeId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val value = reallocTerm(kb, ft, fs, posArgs(0), scope, errors, vm)
    val litPatternSym = kb.resolveSymbol("anthill.reflect.Pattern.literal_pattern")
    kb.alloc(Term.Fn(litPatternSym, IArray.empty, IArray((kb.intern("value"), value))))

  private def loadPatternConstructor(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    posArgs: IArray[TermId], scope: kb.ScopeId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val ctx = Ctx(kb, ft, fs, scope, errors, vm)
    val nameRef = ft.get(posArgs(0)) match
      case Term.Ident(sym) =>
        val kbSym = resolveName(kb, fs.name(sym), scope, errors, ft.spanOf(posArgs(0)))
        kb.alloc(Term.Ref(kbSym))
      case _ => reallocTerm(kb, ft, fs, posArgs(0), scope, errors, vm)
    val subPatterns = IArray.tabulate(posArgs.length - 1)(i => exprRec(ctx, posArgs(i + 1)))
    val argsList = buildList(kb, subPatterns.toIndexedSeq)
    val ctorPatternSym = kb.resolveSymbol("anthill.reflect.Pattern.constructor_pattern")
    kb.alloc(Term.Fn(ctorPatternSym, IArray.empty,
      IArray((kb.intern("name"), nameRef), (kb.intern("args"), argsList))))

  private def loadPatternTuple(
    kb: KnowledgeBase, ft: SimpleTermStore, fs: SymbolTable,
    posArgs: IArray[TermId], scope: kb.ScopeId, errors: ArrayBuffer[LoadError], vm: HashMap[Int, VarId]
  ): TermId =
    val ctx = Ctx(kb, ft, fs, scope, errors, vm)
    val elements = IArray.tabulate(posArgs.length)(i => exprRec(ctx, posArgs(i)))
    val elementsList = buildList(kb, elements.toIndexedSeq)
    val tuplePatternSym = kb.resolveSymbol("anthill.reflect.Pattern.tuple_pattern")
    kb.alloc(Term.Fn(tuplePatternSym, IArray.empty, IArray((kb.intern("elements"), elementsList))))

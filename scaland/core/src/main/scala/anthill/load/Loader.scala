package anthill.load

import anthill.kb.{KnowledgeBase, SortKind}
import anthill.intern.{TermSymbol, SymbolTable, SymbolKind, SymbolDef, ResolveResult, ImportOrigin, FileId, absolutePathTarget}
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
  case DuplicateDeclaration(name: String, first: Span, span: Span)
  case SealedDeclarations(name: String, first: Span, span: Span)
  case EqualityOfEarlierSort(name: String, span: Span)
  case ConstantInGoalPosition(literal: String, span: Span)
  /** WI-20261020-80VNX (rustland's `SortAppliedAsData`, WI-20260902-JB6RS step 6) — `S(…)`
    * WRITTEN in a clause where `S` names only a type ([[KnowledgeBase.namesOnlyAType]]).
    * Only a BARE name falls back to another reading (kernel-language.md §4.4); an
    * application needs a constructor, predicate or operation to apply, and the sort's type
    * is written `S[…]`. It used to BE the type in silence: `Eq(T: ?q)` answered from
    * `fact Eq[T = Int64]`, the two surfaces building one term. */
  case SortAppliedAsData(sort: String, span: Span)
  /** WI-20261029-50361 (rustland's `ClauseHeadNamesNoRelation` for a namespace) — a `fact`
    * or a `rule` clause whose head names a namespace, which holds no clauses. A head
    * reaches one only where a predicate of its own would take the namespace's name: in the
    * scope that declares it, or spelled qualified. It used to be stored under it. */
  case ClauseHeadNamesNamespace(kind: String, name: String, span: Span)
  /** WI-20261029-50361 (rustland's `NamespaceAsGoal`) — a goal naming a namespace, which
    * is not a relation. It answered `true`, through the clause a namespace declaration
    * files under its own name. Scaland judges a rule's and a constraint's body. */
  case NamespaceAsGoal(position: String, namespace: String, span: Span)
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
    case DuplicateDeclaration(name, first, span) =>
      span.render(s"declaration '$name' is made again; first declaration: ${first.render(name)}")
    case SealedDeclarations(name, first, span) =>
      span.render(s"sealed declaration '$name' is made again; first declaration: ${first.render(name)}")
    case EqualityOfEarlierSort(name, span) =>
      span.render(s"the equality of '$name' is closed by the load that defined it")
    case ConstantInGoalPosition(literal, span) =>
      span.render(s"constant `$literal` in a GOAL position names no predicate. " +
        "Only `true` and `false` read as goals (kernel-language.md §5.3); " +
        s"put data in an argument (`p($literal)`) or comparison (`?x = $literal`), " +
        "or write `false` for a goal that always fails.")
    // Rustland's `sort_applied_as_data_message`, word for word.
    case SortAppliedAsData(sort, span) =>
      span.render(s"`$sort(…)` is an application, and `$sort` names no constructor, predicate or " +
        s"operation to apply — it is a sort, and its type is written `$sort[…]` " +
        "(kernel-language.md §4.4)")
    case NamespaceAsGoal(position, namespace, span) =>
      span.render(s"the $position `$namespace` names a namespace, and a namespace is not a " +
        "goal: it is not a relation and holds no clauses (kernel-language.md §5.3)")
    case ClauseHeadNamesNamespace(kind, name, span) =>
      span.render(s"this $kind's head names the namespace `$name`: a namespace is not a " +
        "relation and holds no clauses (kernel-language.md §5.3). Give the relation a name " +
        "of its own.")
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

    // Blocks name a realized sort through imports; collect their work during pass 1
    // and run it after imports, without another scope walk (G2BXZ).
    val deferredBlocks = ArrayBuffer.empty[() => Unit]
    // Pass 1: Define all names
    for (file, fid) <- files.zip(fileIds) do
      kb.symbols.setAskingFile(Some(fid))
      walkScopes(DefinePass(kb, file.symbols, file.terms, errors, deferredBlocks, fid), file.items)

    // Before user imports, so explicit imports retain precedence over the prelude.
    autoImportPrelude(kb)

    // Pass 2: Process requires and imports (all sorts exist now). An import, selective
    // or plain (WI-20261022-JBHQC), of an AUTO-DECLARED predicate cannot resolve here —
    // its head-functor symbol is not registered until pass 3 — so such names are
    // deferred into `pending` and retried below (WI-295). A predicate a body-less rule
    // DECLARES is not one of those since proposal 061: pass 1 minted it above, so it
    // resolves here like any other declared name.
    val pending = ArrayBuffer.empty[PendingImport[kb.ScopeId]]
    for (file, fid) <- files.zip(fileIds) do
      kb.symbols.setAskingFile(Some(fid))
      walkScopes(ImportPass(kb, file.symbols, errors, pending, ImportOrigin.File(fid)), file.items)

    deferredBlocks.foreach(_())

    // A type alias whose definition reaches its own name is refused where it is declared
    // ([[reportRecursiveAliases]]). After pass 2, because a definition names what its
    // scope sees, imports included.
    val aliasSites = ArrayBuffer.empty[AliasSite[kb.ScopeId]]
    for ((file, fid), fileIdx) <- files.zip(fileIds).zipWithIndex do
      kb.symbols.setAskingFile(Some(fid))
      walkScopes(AliasCollectPass(kb, file.symbols, fileIdx, aliasSites, errors), file.items)
    reportRecursiveAliases(kb, aliasSites.toIndexedSeq, files, fileIds, errors)

    // The entity fields that hold a QUOTED term — after pass 2, because a field's type is
    // resolved where the entity is written, imports included; before any clause loads.
    // A KB that declares no `anthill.reflect.Term` has no field to quote.
    for reflectTerm <- kb.tryResolveSymbol("anthill.reflect.Term") do
      val quoting = QuotingTypes(reflectTerm,
        kb.tryResolveSymbol("anthill.prelude.List"), kb.tryResolveSymbol("anthill.prelude.Option"))
      for (file, fid) <- files.zip(fileIds) do
        kb.symbols.setAskingFile(Some(fid))
        walkScopes(QuotedFieldPass(kb, file.symbols, quoting, errors), file.items)

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

    // PHASE 1b — WIRE THE DEFERRED IMPORTS (WI-20261022-JBHQC; rustland's
    // `wire_deferred_imports`). The head census says which qualified names this scan's
    // heads will mint; an import waiting for one is wired to the symbol reserved for it
    // before any head is decided, so the ladder below reads it as any import — from the
    // importing scope and every scope it encloses, behind whatever a nearer scope holds,
    // for the file that wrote it. One whose target no head mints is refused here. Until
    // this ticket a deferred import was retried in pass 4, AFTER the mint, and the mint
    // guard alone was told of it, for the head's own scope alone.
    val headSites = heads.toIndexedSeq
    val wiring = wireDeferredImports(kb, headSites, pending.toIndexedSeq, errors)

    // PHASE 2 — every ladder answer read off the PRE-MINT table, in full, before phase 3
    // starts. That is what makes them order-free. WI-995: imports are file-local, so
    // each is asked on behalf of the file the HEAD is written in.
    val answers: Array[ResolveResult] = headSites.map { h =>
      kb.symbols.setAskingFile(Some(fileIds(h.fileIdx)))
      ruleHeadLadderAnswer(kb, h.name, h.scope)
    }.toArray
    // The imports that wait for these answers, then every reservation no head mints
    // withdrawn, and the heads that read it asked again.
    wireLate(kb, wiring, headSites, answers, fileIds, errors)
    settleWiring(kb, wiring, headSites, answers, fileIds, errors)
    // A head whose answer is the symbol reserved for ITS OWN mint introduces it: it is
    // the predicate's definer, reached through an import of the predicate it defines.
    val denotes: IndexedSeq[Boolean] = headSites.indices.map { i =>
      answers(i).denotes && !wiring.isOwnReservation(headSites(i), answers(i))
    }

    // PHASE 3 — DECIDE, then mint. Deciding reads the table and minting writes it, so
    // they cannot interleave: [[headNameCollisions]] sees a scope through a per-scope
    // SENTINEL symbol, and no mint has happened when any of its answers is taken.
    val captured = reportRuleHeadImportCaptures(kb, headSites, denotes, errors)
    val collided = captured ++ reportHeadNameCollisions(kb, headSites, denotes, fileIds, errors)
    for (head, denoted) <- headSites.zip(denotes) if !denoted do
      kb.symbols.setAskingFile(Some(fileIds(head.fileIdx)))
      scanRuleGoal(kb, head, wiring)
    // A local the mint put ahead of what a denoting head read, at another address than
    // the head's own ([[reportPostMintCaptures]]) — before 061's report, which stays quiet
    // on it as on the one-address capture.
    val enclosing = reportPostMintCaptures(kb, headSites, denotes, answers, captured, fileIds, errors)
    reportPredicateHeadsSpanningFiles(kb, headSites, denotes, collided ++ enclosing, errors)

    // Pass 4 (WI-295) — NOTHING LEFT TO RETRY (WI-20261022-JBHQC): a deferred import was
    // wired in phase 1b to the symbol its definer has just minted, or refused there.
    reportUnminted(kb, wiring, errors)

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
    refuseVisibilityFlags(file.symbols, file.terms, file.items, errors)
    walkScopes(LoadPass(kb, file.symbols, file.terms, errors), file.items)
    errors

  /** WI-20260914-Z73FX — `@[internal]` is the `internal` MODIFIER's other spelling, so
    * `internal entity text(…)` and `entity text(…) @[internal]` are one statement. This
    * is the refusal half, which is all scaland can mirror: rustland decides visibility
    * from either spelling at parse, and scaland implements no §8.6 hiding at all (it
    * parses `visibility` and no pass reads it), so there is nothing here for the flag to
    * set — but a spelling this port ACCEPTS while rustland refuses it is a divergence
    * that would be found by a program, not by a test.
    *
    * Three refusals, all rustland's `convert_declaration_attributes` /
    * `convert_clause_meta_block`, message for message: a modifier contradicted by a flag,
    * a flag with a value (`meta_has_flag` reads any value as present, so
    * `@[internal: false]` would HIDE), and a flag on a CLAUSE, which admits no modifier.
    *
    * Its OWN walk rather than a `LoadPass` arm: a `SortWithBody` opens a scope, so the
    * spine routes it to `enterScope` and `atItem` never sees the declaration whose block
    * this reads. */
  private def refuseVisibilityFlags(
    fileSym: SymbolTable, fileTerms: SimpleTermStore, items: Iterable[Item], errors: ArrayBuffer[LoadError]
  ): Unit =
    def word(v: Visibility): String = v match
      case Visibility.Internal => "internal"
      case Visibility.Public => "public"

    /** The `internal` / `public` entries of a block, keyed as a reader keys one: by the
      * key's LAST segment, which is what the meta term carries. */
    def flags(meta: Option[MetaBlock]): IndexedSeq[(Visibility, MetaEntry)] =
      meta.toIndexedSeq.flatMap(_.entries).flatMap { e =>
        fileSym.name(e.key.last) match
          case "internal" => Some((Visibility.Internal, e))
          case "public" => Some((Visibility.Public, e))
          case _ => None
      }

    def declaration(vis: Option[Visibility], meta: Option[MetaBlock]): Unit =
      var decided = vis
      var spelling = vis.map(v => s"`${word(v)}`")
      for (flag, entry) <- flags(meta) do
        val flagSpelling = s"`@[${word(flag)}]`"
        // WRITTEN-VALUE TEST, and it differs from rustland's by a case neither port can
        // spell today: rustland reads the parse NODE (`@[internal:` with anything after
        // it), scaland reads the lowered term, and the parser writes `Term.Bottom` both
        // for a missing value and for a written `⊥`. So `@[internal: ⊥]` alone loads here
        // and is refused there (/code-review). Closing it needs the IR to distinguish the
        // two, which is a change to `MetaEntry`, not to this refusal.
        if fileTerms.get(entry.value) != Term.Bottom then
          errors += LoadError.Other(
            s"$flagSpelling takes no value: `${word(flag)}` is a visibility flag — " +
            s"write `@[${word(flag)}]`", entry.key.span)
        (decided, spelling) match
          case (Some(v), Some(by)) if v != flag =>
            errors += LoadError.Other(
              s"$by and $flagSpelling contradict: a declaration is `internal` or " +
              "`public`, not both — keep one", entry.key.span)
          case _ =>
            decided = Some(flag)
            spelling = Some(flagSpelling)

    def clause(what: String, meta: Option[MetaBlock]): Unit =
      for (flag, entry) <- flags(meta) do
        errors += LoadError.Other(
          s"`@[${word(flag)}]` on $what: the flag is the `${word(flag)}` modifier's other " +
          "spelling, admitted exactly where the modifier is — on a sort, enum, effects " +
          "sort, type parameter, entity, operation or const", entry.key.span)

    def proof(p: ProofDecl): Unit = p.body match
      case Some(ProofBody.Structured(steps, _)) =>
        steps.foreach(step => clause("a proof step", step.rule.meta))
      case _ => ()

    // A `provides … language … end` block holds CLAUSES of its own, and rustland routes
    // each through the same `convert_fact` / `convert_rule` the top level uses — so the
    // refusal reaches them there. This arm is what a `case _ => ()` catch-all was
    // silently skipping (/code-review): the block loaded clean here and was refused
    // there, which is the divergence this whole function exists to prevent.
    def providesItem(pi: ProvidesItem): Unit = pi match
      case ProvidesItem.RuleI(r) => clause("a rule", r.meta)
      case ProvidesItem.RuleBlockI(b) => b.entries.foreach(r => clause("a rule entry", r.meta))
      case ProvidesItem.FactI(f) => clause("a fact", f.meta)
      case ProvidesItem.ProofI(p) => proof(p)
      case ProvidesItem.ArtifactI(_) | ProvidesItem.CarrierI(_) | ProvidesItem.NamespaceMapI(_)
         | ProvidesItem.OperationMapI(_) | ProvidesItem.ConstMapI(_)
         | ProvidesItem.ProvidesClauseI(_) => ()

    // EXHAUSTIVE over `Item`, deliberately: a catch-all is how the `provides` arm above
    // went missing, and it is the failure WI-1007 made `LoadPass.atItem` exhaustive to
    // stop — a new declaration kind must decide here rather than inherit silence.
    def walk(items: Iterable[Item]): Unit =
      for item <- items do item match
        case Item.NamespaceItem(ns) => walk(ns.items)
        case Item.SortWithBodyItem(sort) =>
          declaration(sort.visibility, sort.meta); walk(sort.items)
        case Item.AbstractSortItem(sort) => declaration(sort.visibility, sort.meta)
        case Item.EntityItem(e) => declaration(e.visibility, e.meta)
        case Item.OperationItem(op) => declaration(op.visibility, op.meta)
        case Item.OperationBlockItem(b) => b.entries.foreach(op => declaration(op.visibility, op.meta))
        case Item.ConstItem(c) => declaration(c.visibility, c.meta)
        case Item.RuleItem(r) => clause("a rule", r.meta)
        case Item.RuleBlockItem(b) => b.entries.foreach(r => clause("a rule entry", r.meta))
        case Item.FactItem(f) => clause("a fact", f.meta)
        case Item.ConstraintItem(c) => clause("a constraint", c.meta)
        case Item.ProofItem(p) => proof(p)
        case Item.ProvidesBlockItem(pb) => pb.items.foreach(providesItem)
        // No block, and nothing nested that has one.
        case Item.RequiresDeclItem(_) | Item.DescribeItem(_) | Item.ProjectItem(_)
           | Item.ToolItem(_) | Item.WorkItemItem(_) | Item.FeedbackItem(_)
           | Item.ImportToolsItem(_) | Item.ProvidesClauseItem(_) | Item.ImportItem(_) => ()

    walk(items)

  /** Load multiple files: scan first, then load all. */
  def loadAll(kb: KnowledgeBase, files: IndexedSeq[ParsedFile]): ArrayBuffer[LoadError] =
    val errors = checkDeclarations(kb, files)
    if errors.nonEmpty then return errors
    errors ++= scanDefinitions(kb, files)
    for file <- files do
      errors ++= load(kb, file)
    recordEquality(kb, files, errors)
    errors

  /** An explicit seal: unsealed repeated loads retain their existing behavior. */
  def sealDeclarations(kb: KnowledgeBase): Unit =
    kb.loadBoundary.sealedDeclarations ++= kb.loadBoundary.declarations

  /** Product entry point. An empty library is one unsealed program load. */
  def loadProgram(
    kb: KnowledgeBase, library: IndexedSeq[ParsedFile], program: IndexedSeq[ParsedFile]
  ): ArrayBuffer[LoadError] =
    if library.isEmpty then loadAll(kb, program)
    else
      val errors = loadAll(kb, library)
      if errors.isEmpty then
        sealDeclarations(kb)
        if program.nonEmpty then errors ++= loadAll(kb, program)
      errors

  /** Check before defining names: a refused redeclaration must not overwrite the
    * earlier symbol's kind or source. Namespaces are secondary entries, not declarations. */
  private def checkDeclarations(kb: KnowledgeBase, files: IndexedSeq[ParsedFile]): ArrayBuffer[LoadError] =
    val errors = ArrayBuffer.empty[LoadError]
    val current = HashMap.empty[String, Span]
    val parameters = HashMap.empty[String, IndexedSeq[String]]
    def declare(name: String, span: Span): Unit =
      kb.loadBoundary.sealedDeclarations.get(name) match
        case Some(first) => errors += LoadError.SealedDeclarations(name, first, span)
        case None => current.get(name) match
          case Some(first) => errors += LoadError.DuplicateDeclaration(name, first, span)
          case None => current(name) = span
    for file <- files do
      def name(n: Name, prefix: String): String = makeQualified(prefix, joinSegments(file.symbols, n.segments))
      def walk(items: Iterable[Item], prefix: String): Unit = items.foreach {
        case Item.NamespaceItem(ns) => walk(ns.items, name(ns.name, prefix))
        case Item.SortWithBodyItem(sort) =>
          val q = name(sort.name, prefix)
          declare(q, sort.span)
          parameters(q) = sort.items.flatMap {
            case Item.AbstractSortItem(p) if p.definition.isInstanceOf[TypeExpr.Variable] => Some(joinSegments(file.symbols, p.name.segments))
            case Item.SortWithBodyItem(p) if p.isTypeParam => Some(joinSegments(file.symbols, p.name.segments))
            case Item.RequiresDeclItem(r) => r.binder.map(b => joinSegments(file.symbols, b.segments))
            case _ => None
          }
          walk(sort.items, q)
        case Item.AbstractSortItem(sort) => declare(name(sort.name, prefix), sort.span)
        case Item.EntityItem(entity) => declare(name(entity.name, prefix), entity.span)
        case Item.OperationItem(op) => declare(name(op.name, prefix), op.span)
        case Item.OperationBlockItem(block) => block.entries.foreach(op => declare(name(op.name, prefix), op.span))
        case Item.ConstItem(c) => declare(name(c.name, prefix), c.span)
        case Item.RequiresDeclItem(r) => r.binder.foreach(b => declare(name(b, prefix), r.span))
        case _ => () // Only declaration-bearing items; clauses add no declaration.
      }
      walk(file.items, "")
    if errors.isEmpty then
      kb.loadBoundary.declarations ++= current
      kb.loadBoundary.parameters ++= parameters
    errors

  /** S723J: equality is closed at the load defining a composite, even without a
    * typer. Keep resolved provision bindings/conditions here: the legacy KB metadata
    * stores only the spec's spelling and cannot distinguish its instantiations.
    * Failed additions remain in the candidate signature, so retries stay refused. */
  private def recordEquality(
    kb: KnowledgeBase, files: IndexedSeq[ParsedFile], errors: ArrayBuffer[LoadError]
  ): Unit =
    val state = kb.loadBoundary
    val old = state.equality.toMap
    val newComposites = HashSet.empty[String]
    for file <- files do
      kb.symbols.setAskingFile(Some(kb.symbols.fileIdOf(file)))
      val targetKB = kb
      val pass = new ScopePass:
        val kb: KnowledgeBase = targetKB
        val fileSym: SymbolTable = file.symbols
        var operationParams = Set.empty[String]
        var operationOwner = ""
        def resolved(n: Name, scope: kb.ScopeId): String =
          val written = joinSegments(fileSym, n.segments)
          if written == "Self" then return kb.scopeDisplayName(scope)
          if operationParams.contains(written) then return operationOwner + "." + written
          lookupWritten(kb, written, scope) match
            case ResolveResult.Found(sym) => kb.qualifiedNameOf(sym)
            case ResolveResult.NotFound =>
              errors += LoadError.UnresolvedName(written, n.span, kb.scopeDisplayName(scope))
              written
            case ResolveResult.Ambiguous(cs) =>
              errors += LoadError.AmbiguousSymbol(written, cs.map(kb.qualifiedNameOf).toIndexedSeq, n.span, kb.scopeDisplayName(scope))
              written
        def ty(t: TypeExpr, scope: kb.ScopeId): String = t match
          case TypeExpr.Simple(n) => resolved(n, scope)
          case TypeExpr.Parameterized(n, bs) =>
            val head = resolved(n, scope)
            val params = state.parameters.getOrElse(head, IndexedSeq.empty)
            var position = 0
            val bindings = bs.map { b =>
              val label = b.param match
                case Some(p) => joinSegments(fileSym, p.segments)
                case None =>
                  val label = params.lift(position).getOrElse(s"pos:$position")
                  position += 1
                  label
              label + "=" + ty(b.bound, scope)
            }
            head + bindings.sorted.mkString("[", ",", "]")
          case TypeExpr.Variable(_, _) => "?"
          case TypeExpr.TupleType(fs) => fs.map((n, t) => fileSym.name(n) + ":" + ty(t, scope)).mkString("(", ",", ")")
          case TypeExpr.Arrow(ps, r, es) => ps.map(ty(_, scope)).mkString("(", ",", ")") + "->" + ty(r, scope) + es.map(ty(_, scope)).mkString("@", ",", "")
          case TypeExpr.Denoted(v) => term(v)
          case TypeExpr.EffectRow(es) => es.map(ty(_, scope)).mkString("{", ",", "}")
          case TypeExpr.EffectGuarded(t, gs) => ty(t, scope) + gs.map(term).mkString(":-", ",", "")
        def term(id: ParseTermId): String = file.terms.get(id) match
          case Term.Fn(f, ps, ns) => fileSym.name(f) + ps.map(term).mkString("(", ",", ")") + ns.map((n, v) => fileSym.name(n) + ":" + term(v)).sorted.mkString("{", ",", "}")
          case Term.Ref(s) => fileSym.name(s)
          case Term.Ident(s) => fileSym.name(s)
          case t => t.toString
        def add(carrier: String, row: String, span: Span): Unit =
          state.rows.getOrElseUpdate(carrier, HashMap.empty)(row) = span
        def base(t: TypeExpr, scope: kb.ScopeId): Option[String] = t match
          case TypeExpr.Simple(n) => Some(resolved(n, scope))
          case TypeExpr.Parameterized(n, _) => Some(resolved(n, scope))
          case _ => None
        def operation(op: Operation, scope: kb.ScopeId, prefix: String): Unit =
          val written = joinSegments(fileSym, op.name.segments)
          if written.split('.').last == "eq" then
            operationOwner = makeQualified(prefix, written)
            operationParams = op.typeParams.map(p => fileSym.name(p.name)).toSet
            val carriers = op.params.flatMap(p => base(p.ty, scope)).distinct
            if op.params.size == 2 && carriers.size == 1 && op.params.map(p => ty(p.ty, scope)).distinct.size == 1 then
              val qualified = makeQualified(prefix, written)
              val owner = qualified.stripSuffix(".eq")
              state.operations.getOrElseUpdate((carriers.head, owner), HashMap.empty)("eq:" + qualified) = op.span
            operationParams = Set.empty
        def enterScope(decl: ScopeDecl, written: String, q: String, prefix: String, enclosing: kb.ScopeId): Option[kb.ScopeId] =
          decl match
            case ScopeDecl.SortBody(sort) if sort.items.exists(_.isInstanceOf[Item.EntityItem]) => newComposites += q
            case _ => ()
          lookupScope(kb, q, decl.name.span, errors)
        def atItem(item: Item, scope: kb.ScopeId, prefix: String): Unit = item match
          case Item.EntityItem(e) if !isSortScope(kb, scope) => newComposites += makeQualified(prefix, joinSegments(fileSym, e.name.segments))
          case Item.OperationItem(op) => operation(op, scope, prefix)
          case Item.OperationBlockItem(b) => b.entries.foreach(operation(_, scope, prefix))
          case Item.ProvidesClauseItem(pc) =>
            pc.spec match
              case TypeExpr.Parameterized(n, bindings) if Set("anthill.prelude.PartialEq", "anthill.prelude.Eq", "anthill.prelude.NonEq").contains(resolved(n, scope)) =>
                bindings.find(b => b.param.exists(p => joinSegments(fileSym, p.segments) == "T")).orElse(bindings.headOption).foreach { b =>
                  base(b.bound, scope).foreach { c =>
                    state.providers += ((c, prefix))
                    add(c, prefix + ":" + ty(pc.spec, scope) + pc.conditions.map(ty(_, scope)).sorted.mkString(":-", ",", ""), pc.span)
                  }
                }
              case _ => ()
          case _ => () // Only equality suppliers/provisions and constructor declarations.
      walkScopes(pass, file.items)
    for ((carrier, owner), rows) <- state.operations if owner == carrier || state.providers.contains((carrier, owner)) do
      state.rows.getOrElseUpdate(carrier, HashMap.empty) ++= rows
    for (carrier, signature) <- old do
      val now = state.rows.get(carrier).map(_.keySet.toSet).getOrElse(Set.empty[String])
      if now != signature then
        val span = state.rows(carrier).find((row, _) => !signature.contains(row)).map(_._2).getOrElse(Span.empty)
        errors += LoadError.EqualityOfEarlierSort(carrier, span)
    // Preserve the last accepted signature for an earlier composite, even on failure.
    for carrier <- newComposites if !state.equality.contains(carrier) do
      state.equality(carrier) = state.rows.get(carrier).map(_.keySet.toSet).getOrElse(Set.empty)

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
      * WI-1007: [[LoadPass]]'s implementation is EXHAUSTIVE and the definition/import scans end in a
      * catch-all, which is a decision and not drift. `LoadPass` is the pass whose job is
      * "everything that reaches the KB reaches it here", so an `Item` kind it does not
      * name is data loss — that is how `ConstraintItem` was found being dropped in
      * silence. `DefinePass` (defines names), `ImportPass` (handles imports) and
      * `declarePredicate` (2 of 23 kinds) are narrow scans, where a catch-all says
      * "not my job" honestly and enumerating would be 18 arms of noise.
      *
      * [[RuleHeadCollectPass]] IS EXHAUSTIVE TOO (WI-20260821-RDGQC), for `LoadPass`'s
      * reason: it must see every item that lands a clause head, and one it does not see
      * loses its name without a word — a `fact` sat under its catch-all, and its head
      * took the bare intern. */
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

  /** Define every declared name, accumulating all roles at the same address. */
  private final class DefinePass(
    val kb: KnowledgeBase, val fileSym: SymbolTable, fileTerms: SimpleTermStore,
    errors: ArrayBuffer[LoadError], deferredBlocks: ArrayBuffer[() => Unit], fileId: FileId
  ) extends ScopePass:

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
          val fields = entity.fields.map(f => fileSym.name(f.name)).map(kb.intern)
          eponymousSortSymbol(kb, fileSym, entity.name.segments, scope) match
            case Some(sortSym) =>
              // §6.3 (WI-926): `sort Foo … entity Foo(…) … end` writes `Foo` ONCE and
              // defines ONE symbol — the sort's, now playing `Entity` too, which is what
              // a free-standing `entity Foo(…)` is from the other spelling. No nested
              // `Foo.Foo` is defined, so no parent edge and no `entity_of` fact: it is
              // not a constructor OF a sort, it is the sort (rustland's
              // `eponymous_sort_symbol`, which marks no constructor either).
              kb.symbols.addKind(sortSym, SymbolKind.Entity)
              kb.registerEntityFields(sortSym, fields)
            case None => defineEntity(entity, fields, scope, prefix)

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
          defineRuleLabel(rule, scope, prefix)
          declarePredicate(kb, fileSym, fileTerms, rule, scope, prefix)

        case Item.RuleBlockItem(block) =>
          for rule <- block.entries do
            defineRuleLabel(rule, scope, prefix)
            declarePredicate(kb, fileSym, fileTerms, rule, scope, prefix)

        case Item.ProvidesBlockItem(pb) =>
          val askingFile = Some(fileId)
          deferredBlocks += (() => {
            kb.symbols.setAskingFile(askingFile)
            for target <- providesBlockScope(kb, fileSym, pb, scope, errors) do
              val targetPrefix = kb.scopeDisplayName(target)
              for inner <- pb.items do inner match
                case ProvidesItem.RuleI(rule) =>
                  declarePredicate(kb, fileSym, fileTerms, rule, target, targetPrefix)
                case ProvidesItem.RuleBlockI(block) =>
                  for rule <- block.entries do
                    declarePredicate(kb, fileSym, fileTerms, rule, target, targetPrefix)
                case ProvidesItem.ProvidesClauseI(pc) =>
                  processProvidesConditions(kb, pc, fileSym, target, errors)
                  processProvidesHead(kb, pc, fileSym, target, errors)
                case _ => ()
          })

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

    /** An entity that is not its sort's own name: a sort-nested constructor, or a
      * free-standing entity. */
    private def defineEntity(
      entity: Entity, fields: IndexedSeq[TermSymbol], scope: kb.ScopeId, prefix: String
    ): Unit =
      val (shortName, qualName, target) = declSite(kb, fileSym, entity.name.segments, prefix, scope)
      val sym = kb.symbols.define(shortName, qualName, SymbolKind.Entity, target)
      // §6.3: a free-standing entity also names its type, like `sort E { entity E }`.
      // Nested variants keep their constructor-only reading and their own identity.
      if !isSortScope(kb, scope) then kb.symbols.addKind(sym, SymbolKind.Sort)
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
      kb.registerEntityFields(sym, fields)

    private def defineRuleLabel(rule: Rule, scope: kb.ScopeId, prefix: String): Unit =
      rule.label.foreach { label =>
        val shortName = joinSegments(fileSym, label.segments)
        kb.symbols.define(shortName, makeQualified(prefix, shortName), SymbolKind.Rule, scope)
      }

  /** Mint during pass 1; validate against the complete role set at load time. */
  private def declarePredicate(
    kb: KnowledgeBase, fileSym: SymbolTable, fileTerms: SimpleTermStore,
    rule: Rule, scope: kb.ScopeId, prefix: String
  ): Unit =
    ruleReading(rule, fileSym, fileTerms) match
      case RuleReading.Declaration(name) =>
        defineSymbolOnce(kb, name, makeQualified(prefix, name), SymbolKind.Goal, scope)
      case RuleReading.Clause | RuleReading.DeclaresNothing(_) => ()

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

  /** Merge a role into an existing local, or define a new local only when its
    * qualified name is free. The existing-local arm is essential for N3WGM: a rule
    * declaration and an operation must accumulate both roles in either text order.
    * Shared by operations, consts and rule functors. A kernel operation such as
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
    if kb.symbols.scope(scope).exists(_.locals.contains(shortName)) ||
        !kb.symbols.byQualifiedName.contains(qualName) then
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

  // ── Recursive type aliases ───────────────────────────────────

  /** One type alias — `sort X = T`, `T` no variable — where it is written. */
  private case class AliasSite[S](
    sym: TermSymbol, scope: S, fileIdx: Int, definition: TypeExpr, span: Span
  )

  /** Reads every type alias of a file and where it is written. Takes no decision. */
  private final class AliasCollectPass(
    val kb: KnowledgeBase,
    val fileSym: SymbolTable,
    fileIdx: Int,
    sites: ArrayBuffer[AliasSite[kb.ScopeId]],
    errors: ArrayBuffer[LoadError]
  ) extends ScopePass:

    def enterScope(
      decl: ScopeDecl, writtenName: String, qualName: String, prefix: String, enclosing: kb.ScopeId
    ): Option[kb.ScopeId] =
      lookupScope(kb, qualName, decl.name.span, errors)

    def atItem(item: Item, scope: kb.ScopeId, prefix: String): Unit =
      item match
        case Item.AbstractSortItem(sort) if !sort.definition.isInstanceOf[TypeExpr.Variable] =>
          val (_, qualName, _) = declSite(kb, fileSym, sort.name.segments, prefix, scope)
          for sym <- kb.symbols.byQualifiedName.get(qualName) do
            sites += AliasSite(sym, scope, fileIdx, sort.definition, sort.span)
        case _ => ()

  /** The declarations a QUOTING field type is written in, resolved once per load:
    * `anthill.reflect.Term`, and the two containers whose element a quoted field may hold. */
  private case class QuotingTypes(term: TermSymbol, list: Option[TermSymbol], option: Option[TermSymbol])

  /** WI-20261020-80VNX — record each entity field whose declared type QUOTES
    * ([[KnowledgeBase.isQuotedField]]): `anthill.reflect.Term`, or a `List` or `Option` of
    * a quoting type, as rustland reads a list's elements and an option's payload at
    * their element type (`convert_arg_value`'s `is_reflect_term_type`, through
    * `elem_expected` / `some_payload_hint`). Such a field holds a QUOTED pattern (§4.2;
    * §6.3, "a field declared `anthill.reflect.Term` holds a QUOTED term"), so a clause's
    * argument there is judged as written and not read: `fact holdsQ(pattern: Eq(T: 1))`
    * holds the pattern, and `Eq(…)`'s refusal as an application of a sort
    * ([[LoadError.SortAppliedAsData]]) does not reach inside it. Scaland, with no typer,
    * records it for itself: the declared type is resolved here, where the entity is
    * written. Any other field type is a verdict — not quoted — and not a skip. */
  private final class QuotedFieldPass(
    val kb: KnowledgeBase,
    val fileSym: SymbolTable,
    quoting: QuotingTypes,
    errors: ArrayBuffer[LoadError]
  ) extends ScopePass:

    // A scope that does not resolve is reported by the passes that load it; this one has
    // nothing to add to that, so it follows the descent silently rather than reporting
    // the miss a third time.
    def enterScope(
      decl: ScopeDecl, writtenName: String, qualName: String, prefix: String, enclosing: kb.ScopeId
    ): Option[kb.ScopeId] =
      kb.symbols.byQualifiedName.get(qualName).map(kb.symbols.scopeOf)

    private def quotes(ty: TypeExpr, scope: kb.ScopeId): Boolean =
      def names(n: Name): TermSymbol => Boolean = target =>
        lookupWritten(kb, joinSegments(fileSym, n.segments), scope) == ResolveResult.Found(target)
      ty match
        case TypeExpr.Simple(n) => names(n)(quoting.term)
        case TypeExpr.Parameterized(n, IndexedSeq(binding))
            if quoting.list.exists(names(n)) || quoting.option.exists(names(n)) =>
          quotes(binding.bound, scope)
        case _ => false

    def atItem(item: Item, scope: kb.ScopeId, prefix: String): Unit =
      item match
        case Item.EntityItem(entity) =>
          val entitySym = eponymousSortSymbol(kb, fileSym, entity.name.segments, scope).orElse {
            val (_, qualName, _) = declSite(kb, fileSym, entity.name.segments, prefix, scope)
            lookupDefined(kb, qualName, entity.name.span, "its quoted fields cannot be recorded", errors)
          }
          for sym <- entitySym; field <- entity.fields if quotes(field.ty, scope) do
            kb.registerQuotedField(sym, kb.intern(fileSym.name(field.name)))
        case _ => ()

  /** Every leading part of every name written in `ty` — `WisStore` and `WisStore.State`
    * of `WisStore.State` — so a name that reaches an alias by a qualified path is seen as
    * naming it. Mirrors rustland's `collect_type_expr_heads`. */
  private def typeExprHeads(fileSym: SymbolTable, ty: TypeExpr): IndexedSeq[String] =
    def prefixes(name: Name): IndexedSeq[String] =
      (1 to name.segments.length).map(n => joinSegments(fileSym, name.segments.take(n)))
    ty match
      case TypeExpr.Simple(name) => prefixes(name)
      case TypeExpr.Parameterized(name, bindings) =>
        prefixes(name) ++ bindings.flatMap(b => typeExprHeads(fileSym, b.bound))
      case TypeExpr.TupleType(fields) => fields.flatMap((_, t) => typeExprHeads(fileSym, t))
      case TypeExpr.Arrow(params, returnType, effects) =>
        (params :+ returnType).flatMap(typeExprHeads(fileSym, _)) ++
          effects.flatMap(typeExprHeads(fileSym, _))
      case TypeExpr.EffectRow(effects) => effects.flatMap(typeExprHeads(fileSym, _))
      case TypeExpr.EffectGuarded(label, _) => typeExprHeads(fileSym, label)
      case TypeExpr.Variable(_, _) | TypeExpr.Denoted(_) => IndexedSeq.empty

  /** WI-20261004-2HJW8 — a type alias whose definition reaches its own name is refused
    * where it is declared, naming the chain: `sort S = S`, `sort A = B` with `sort B = A`,
    * `sort Loop = List[T = Loop]`. An alias is the type it is defined as, so such a one
    * would be an infinite type; a recursive type is written through a sort with a
    * constructor. An alias that only NAMES one on a chain is on none, and is not refused.
    *
    * Scaland reads no alias through — it has no typer — so nothing here went wrong with
    * such a declaration; the refusal is the declaration's, the same on both
    * implementations (rustland's `AliasDeclarePass::refuse_alias_reaching_itself`). */
  private def reportRecursiveAliases(
    kb: KnowledgeBase,
    sites: IndexedSeq[AliasSite[kb.ScopeId]],
    files: IndexedSeq[ParsedFile],
    fileIds: IndexedSeq[FileId],
    errors: ArrayBuffer[LoadError]
  ): Unit =
    val aliases = sites.map(_.sym).toSet
    val names: Map[TermSymbol, IndexedSeq[TermSymbol]] = sites.map { site =>
      kb.symbols.setAskingFile(Some(fileIds(site.fileIdx)))
      val named = typeExprHeads(files(site.fileIdx).symbols, site.definition).flatMap { head =>
        lookupWritten(kb, head, site.scope) match
          case ResolveResult.Found(sym) if aliases(sym) => Some(sym)
          case _ => None
      }.distinct
      site.sym -> named
    }.toMap
    def shortName(sym: TermSymbol): String = kb.qualifiedNameOf(sym).split('.').last
    for site <- sites do
      for chain <- chainBackTo(site.sym, names) do
        errors += LoadError.Other(
          s"type alias `${kb.qualifiedNameOf(site.sym)}` reaches its own name through its " +
          s"definition (${chain.map(shortName).mkString(" -> ")}), so it stands for no type. " +
          "An alias is the type it is defined as; write a recursive type as a sort with a " +
          "constructor (`sort Loop  entity loop(items: List[T = Self])  end`)",
          site.span)

  /** The chain from `alias` back to itself through the aliases each definition names —
    * `A, B, A` for `sort A = B`, `sort B = A` — or `None` when `alias` is on none.
    * Breadth-first, so the chain named is a shortest one. */
  private def chainBackTo(
    alias: TermSymbol, names: Map[TermSymbol, IndexedSeq[TermSymbol]]
  ): Option[IndexedSeq[TermSymbol]] =
    val reached = HashMap.empty[TermSymbol, TermSymbol]
    val queue = scala.collection.mutable.Queue(alias)
    var found: Option[IndexedSeq[TermSymbol]] = None
    while found.isEmpty && queue.nonEmpty do
      val at = queue.dequeue()
      val named = names.getOrElse(at, IndexedSeq.empty)
      if named.contains(alias) then
        var chain = List(at, alias)
        var back = at
        while back != alias do
          back = reached(back)
          chain = back :: chain
        found = Some(chain.toIndexedSeq)
      else
        for next <- named if !reached.contains(next) do
          reached(next) = at
          queue.enqueue(next)
    found

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
    * span — or the FACT's, a fact head being a site like any other — which carries the
    * file name a refusal prints. */
  private case class RuleHeadSite[S](
    fileIdx: Int, scope: S, prefix: String, name: String, kind: SymbolKind, span: Span
  )

  /** Sub-pass 3, PHASE 1 — read the name each clause head introduces and remember WHERE
    * it belongs: a rule's head, a fact's, and those inside a host `provides` block.
    * Takes no decision and mints nothing, so nothing it does depends on
    * the order it runs in; [[scanRuleGoal]] is the mint.
    *
    * WI-894/896/898 is what the mint is FOR. `ite` is the motivating case —
    * `bool.anthill` declares no `ite` operation; its two `@[simp]` equations ARE its
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
        // WI-20260821-RDGQC — A FACT HEAD INTRODUCES ITS NAME WHERE IT IS WRITTEN, as the
        // `rule H :- true` spelling of the same clause does (§6.1: they are one clause).
        // MEASURED before this arm: `namespace a { fact p(1)  rule see(?x) :- p(?x) }`
        // beside the same in `b` with `p(2)` gave 2 answers in EACH namespace and
        // neither `a.p` nor `b.p` resolved — one uncitable global held both clauses —
        // while the `rule` spelling gave 1 each, its own. Mirrors rustland's
        // `RuleHeadCollectPass::collect_fact`.
        case Item.FactItem(fact) => collectFact(fact, scope, prefix)
        // G2BXZ: every language's clauses belong to the realized sort, as at load.
        case Item.ProvidesBlockItem(pb) =>
          for target <- providesBlockScope(kb, fileSym, pb, scope, errors) do
            val targetPrefix = kb.scopeDisplayName(target)
            for inner <- pb.items do inner match
              case ProvidesItem.RuleI(rule) => collect(rule, target, targetPrefix)
              case ProvidesItem.RuleBlockI(block) =>
                for rule <- block.entries do collect(rule, target, targetPrefix)
              case ProvidesItem.FactI(fact) => collectFact(fact, target, targetPrefix)
              // No clause of a predicate: a verdict, a provision, and the realization
              // bindings themselves.
              case ProvidesItem.ProofI(_) | ProvidesItem.ProvidesClauseI(_)
                 | ProvidesItem.ArtifactI(_) | ProvidesItem.CarrierI(_)
                 | ProvidesItem.NamespaceMapI(_) | ProvidesItem.OperationMapI(_)
                 | ProvidesItem.ConstMapI(_) =>

        // ENUMERATED, not swept up by `case _`: which head shapes introduce a name is
        // this pass's whole question, and a shape that falls through does so silently —
        // its head takes the bare intern, one global name every scope shares. A new
        // `Item` kind must fail to compile here (E029 is an error in this build) and be
        // classified. None of these writes a clause head: a `constraint` has no head,
        // and the rest declare, import, or record a verdict or a provision.
        case Item.AbstractSortItem(_) | Item.EntityItem(_) | Item.OperationItem(_)
           | Item.OperationBlockItem(_) | Item.ConstItem(_) | Item.ConstraintItem(_)
           | Item.RequiresDeclItem(_) | Item.ImportItem(_) | Item.ProofItem(_)
           | Item.ProvidesClauseItem(_) | Item.DescribeItem(_) | Item.ProjectItem(_)
           | Item.ToolItem(_) | Item.WorkItemItem(_) | Item.FeedbackItem(_)
           | Item.ImportToolsItem(_) =>
        // Never reach `atItem`: [[walkScopes]] descends into the two scope openers.
        case Item.NamespaceItem(_) | Item.SortWithBodyItem(_) =>

    private def collect(rule: Rule, scope: kb.ScopeId, prefix: String): Unit =
      for (name, kind) <- headIntroductions(rule, fileSym, fileTerms) do
        sites += RuleHeadSite(fileIdx, scope, prefix, name, kind, rule.span)

    /** A fact is the one-head PREDICATE rule, so it is asked [[introducedName]]'s
      * questions and nothing else: there is no equation reading to make (a `<=>` head is
      * the desugar's node, which introduces nothing), and a QUALIFIED fact head
      * references — `fact Rec.p(2)` lands its clause on `Rec.p`. */
    private def collectFact(fact: Fact, scope: kb.ScopeId, prefix: String): Unit =
      for name <- introducedName(fileSym, fileTerms, fact.term) do
        sites += RuleHeadSite(fileIdx, scope, prefix, name, SymbolKind.Goal, fact.span)

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
    * head walk that picked it ([[headIntroduces]], asked per head by
    * [[headIntroductions]]; WI-20260908-NE0E4), so no second walk can disagree.
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
  private def scanRuleGoal(
    kb: KnowledgeBase, site: RuleHeadSite[kb.ScopeId], wiring: DeferredWiring[kb.ScopeId]
  ): Unit =
    val qualified = makeQualified(site.prefix, site.name)
    // WI-20261022-JBHQC — a name a deferred import waits for is the symbol reserved for
    // it in phase 1b: the first head to mint the name adopts it.
    adoptReservation(kb, wiring, qualified, site.kind)
    defineSymbolOnce(kb, site.name, qualified, site.kind, site.scope)

  /** THE refusal of a capture (WI-20260821-JR7BB): the local the `introducing` heads would
    * mint at `scope` takes the `importing` heads, which denote through an import. One
    * builder for both askers — the one address before the mint, every other after it. */
  private def captureRefusal(
    kb: KnowledgeBase, heads: IndexedSeq[RuleHeadSite[kb.ScopeId]],
    scope: kb.ScopeId, name: String, importing: IndexedSeq[Int], introducing: IndexedSeq[Int]
  ): LoadError =
    val importingFiles = importing.map(i => heads(i).span.file).distinct.sorted
    val introducingFiles = introducing.map(i => heads(i).span.file).distinct.sorted
    val first = introducing.minBy(i => (heads(i).fileIdx, heads(i).span.start))
    LoadError.Other(
      s"the local rule-head name `$name` in '${kb.scopeDisplayName(scope)}' would " +
      s"capture the same head as resolved through an import in " +
      s"${importingFiles.mkString(", ")}. Imports belong only to the files that write " +
      s"them, but the local declaration requested by ${introducingFiles.mkString(", ")} " +
      s"would belong to every file at this scope and outrank those imports, silently " +
      s"retargeting an unchanged clause. Qualify the imported head, import it by name " +
      s"in every contributing file, or declare the local predicate explicitly and " +
      s"qualify the foreign contribution.",
      heads(first).span)

  /** WI-20260821-JR7BB — refuse a scope-local rule-head declaration that would capture
    * a sibling file's imported head.
    *
    * Imports are FILE-local (WI-1074/WI-995); declarations are SCOPE-wide. Therefore a
    * mixed frozen answer for one `(scope, name)` — one head DENOTES while another would
    * INTRODUCE — means the latter's local would precede the former's import and silently
    * retarget an unchanged clause. Ask before the mint, while the distinction still
    * exists. Carrying the imported answer only into head placement was rejected: then a
    * bare name in one rule's head and body would resolve two ways. */
  private def reportRuleHeadImportCaptures(
    kb: KnowledgeBase,
    heads: IndexedSeq[RuleHeadSite[kb.ScopeId]],
    denotes: IndexedSeq[Boolean],
    errors: ArrayBuffer[LoadError]
  ): Set[(kb.ScopeId, String)] =
    val groups = LinkedHashMap.empty[(kb.ScopeId, String), (ArrayBuffer[Int], ArrayBuffer[Int])]
    for (head, idx) <- heads.zipWithIndex do
      val (imported, introducing) = groups.getOrElseUpdate(
        (head.scope, head.name), (ArrayBuffer.empty, ArrayBuffer.empty))
      if denotes(idx) then imported += idx else introducing += idx

    var refused = Set.empty[(kb.ScopeId, String)]
    for ((scope, name), (imported, introducing)) <- groups.toIndexedSeq
        .sortBy((key, _) => (kb.scopeDisplayName(key._1), key._2))
        if imported.nonEmpty && introducing.nonEmpty do
      errors += captureRefusal(kb, heads, scope, name, imported.toIndexedSeq, introducing.toIndexedSeq)
      refused += ((scope, name))
    refused

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

  /** The ladder a rule head reads — the ordinary one, save that a head written inside a
    * namespace never resolves to a name whose only home is `<global>` (WI-20260821-HSG31,
    * kernel-language.md §5.3 "`<global>` is not a party to any of it"). Such a head
    * declares at its own scope instead, and once minted that local is what every reference
    * in the namespace reads.
    *
    * RE-ASKED ONLY WHEN THE ORDINARY ANSWER IS A `<global>` DECLARATION: `NotFound` means
    * `<global>` declares nothing by this name, and a `Found` elsewhere never reached it.
    * An `Ambiguous` answer is kept even with a `<global>` candidate among it — the
    * namespace's own references are ambiguous too, and WI-900 reports that at the
    * reference. Rustland's twin is `load::rule_head_ladder_answer`.
    *
    * WI-20261029-50361 — A NAMESPACE IS NO ANSWER, unless its own scope is the head's. A
    * namespace holds no clauses ([[isNamespaceOnly]]), so a head whose name reaches one —
    * `rule zed :- …` inside `namespace probe.zed`, through the enclosing `probe`, or
    * through an `import probe.zed` — introduces its predicate where it is written, exactly
    * as its declaration `rule zed(?x)` does there. Where the head is written in the scope
    * that declares the namespace, introducing would mint the namespace's own qualified
    * name, so the answer stands and the clause is refused at its head
    * ([[refuseHeadNamingNamespace]]). */
  private def ruleHeadLadderAnswer(kb: KnowledgeBase, name: String, scope: kb.ScopeId): ResolveResult =
    val answer = kb.symbols.resolveInScope(name, scope) match
      case ResolveResult.Found(sym)
          if homeOf(kb, sym).contains(kb.globalScope) && kb.symbols.isInsideNamespace(scope) =>
        kb.symbols.resolveRuleHeadInsideNamespace(name, scope)
      case other => other
    answer match
      case ResolveResult.Found(sym) if isNamespaceOnly(kb, sym) && !homeOf(kb, sym).contains(scope) =>
        ResolveResult.NotFound
      case other => other

  /** The scope `sym` is declared in, if it is a resolved symbol. */
  private def homeOf(kb: KnowledgeBase, sym: TermSymbol): Option[kb.ScopeId] =
    kb.symbols.get(sym) match
      case SymbolDef.Resolved(_, _, _, home) => Some(home)
      case _                                 => None

  /** Is `sym` a namespace and nothing else? A namespace denotes no value and no type, and
    * holds no clauses. A `namespace X` beside `sort X` is one symbol that IS a type (059
    * R2's secondary entry), so the value and type kinds are named. Rustland's twin is
    * `load::is_namespace_only`. */
  private def isNamespaceOnly(kb: KnowledgeBase, sym: TermSymbol): Boolean =
    val d = kb.symbols.get(sym)
    d.hasKind(SymbolKind.Namespace) &&
      !Seq(SymbolKind.Sort, SymbolKind.Entity, SymbolKind.Operation, SymbolKind.Const).exists(d.hasKind)

  /** WI-20261029-50361 — refuse a goal that names a namespace, where a body writes it: any
    * goal slot, since a namespace's goal never fails. Rustland's twin is the rule-body goal
    * reading's `NamespaceAsGoal`. */
  private def refuseNamespaceGoal(
    kb: KnowledgeBase, sym: TermSymbol, span: Span, errors: ArrayBuffer[LoadError]
  ): Unit =
    if isNamespaceOnly(kb, sym) then
      errors += LoadError.NamespaceAsGoal("rule-body goal", kb.qualifiedNameOf(sym), span)

  /** WI-20261029-50361 — refuse a clause whose head names a namespace, and answer `true` so
    * the caller stores none. A head reaches one only where a predicate of its own would
    * take the namespace's name: in the scope that declares it, or spelled qualified.
    * Rustland's twin is `Loader::refuse_if_head_names_no_relation`, which refuses a const
    * head too; scaland has no const refusal. */
  private def refuseHeadNamingNamespace(
    kb: KnowledgeBase, head: TermId, kind: String, span: Span, errors: ArrayBuffer[LoadError]
  ): Boolean =
    kb.headFunctorOf(head).filter(isNamespaceOnly(kb, _)) match
      case Some(ns) =>
        errors += LoadError.ClauseHeadNamesNamespace(kind, kb.qualifiedNameOf(ns), span)
        true
      case None => false

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
    * body-less rule, minted in pass 1 — or the load is refused naming the files.
    *
    * KEYED ON THE SCOPE, which since 845G7 is the same thing as the predicate: a head
    * never lands anywhere but where it is written, so the group is `(scope, name)` and
    * the cross-SCOPE half of what this used to report is [[reportHeadNameCollisions]].
    *
    * A DECLARED predicate never reaches here: its heads all denote (pass 1 minted the
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
    * NARC7 ports the resolver reading and refuses non-boolean constants in goal slots.
    * Measured strip back-out: every search answer in RuleHeadDeclarationTest stays
    * correct. The empty-body identity and unconditional-denial refusal fail, because
    * those depend on body shape rather than the operational reading of `true`. */
  private def isEmptyConjunctionGoal(fileTerms: SimpleTermStore, tid: ParseTermId): Boolean =
    fileTerms.get(tid) match
      case Term.Const(Literal.BoolLit(true)) => true
      case _                                 => false

  /** Does this rule's body add NOTHING to its head — no body at all, or a body of
    * nothing but erased `true`s? Asked by [[headIntroduces]], for which an equation is
    * BODYLESS (§8.3), and by [[loadRuleHeads]]'s non-defining-connective refusal, whose
    * subject is the same emptiness.
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
      * is minted in PASS 1 by [[declarePredicate]], like every other declared name
      * (WI-321),
      * which is what makes a head's binding independent of the order a pass walks in.
      *
      * A SECOND DECLARATION OF ONE PREDICATE AT ONE SCOPE IS IDEMPOTENT, and admitted:
      * a predicate declaration carries no signature, no arity claim and no clause, so
      * two of them name the same symbol and lose nothing.
      *
      * `name` is the predicate it declares — carried, so pass 1's mint and the load's
      * refusals read the one answer instead of walking the head again. */
    case Declaration(name: String)
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
      * is refused rather than dropped in silence — with `why`, the one reason both the
      * verdict and the author's sentence read. */
    case DeclaresNothing(why: NoIntroduction)

  /** [[RuleReading]] for one rule — the single decider, asked by pass 1's mint
    * ([[declarePredicate]]) and by [[loadRuleHeads]]. Both must give the same answer:
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
      case Right((name, SymbolKind.Goal)) => RuleReading.Declaration(name)
      // An EQUATION reaches here only through a head this function already sent to
      // `Clause`; the arm is stated rather than fused so a future head shape cannot
      // acquire a declaration reading by accident. `SymbolKind.EquationFunctor` is the
      // introduction kind [[ruleIntroducedFunctor]] stamps for it — WI-898's split, and
      // this is its first reader in scaland.
      case Right(_)  => RuleReading.Clause
      case Left(why) => RuleReading.DeclaresNothing(why)

  /** The kinds a body-less rule's own mint can produce, and therefore the ones a
    * DECLARATION may find already sitting at its scope without having declared nothing:
    * [[SymbolKind.Goal]] (its own), [[SymbolKind.EquationFunctor]] (a sibling equation
    * about the same subject) and [[SymbolKind.Rule]] (a LABEL of that spelling, which
    * [[DefinePass.defineRuleLabel]] defines in the same pass). Anything else is another
    * construct's declaration that pass 1's `define` merged into. */
  private val DeclarableByARule: Set[SymbolKind] =
    Set(SymbolKind.Goal, SymbolKind.EquationFunctor, SymbolKind.Rule)

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
    name: String,
    fileSym: SymbolTable,
    fileTerms: SimpleTermStore,
    scope: kb.ScopeId,
    errors: ArrayBuffer[LoadError]
  ): Unit =
    // Membership on the completed ladder, excluding the predicate minted in pass 1.
    // This also catches an enclosing operation declared later or in another file.
    val reached = if kb.symbols.isInsideNamespace(scope) then
      kb.symbols.resolveRuleHeadInsideNamespace(name, scope, ownLocalsVisible = false)
    else kb.symbols.resolveWithOverlay(name, scope, _ => None)
    // WI-20261029-50361 — a namespace reached is no answer, as on the head's ladder
    // ([[ruleHeadLadderAnswer]]): the undeclared head introduces there, so its declaration
    // does too. One the scope itself declares is the `local` collision below.
    reached match
      case ResolveResult.Found(sym) if !isNamespaceOnly(kb, sym) =>
        kb.symbols.get(sym).kindsSet.diff(DeclarableByARule).toSeq.sortBy(_.ordinal).foreach { k =>
          errors += LoadError.Other(
            s"the body-less rule `$name` DECLARES a predicate, but `$name` already " +
              s"names something this scope reaches (kind: $k), which a rule cannot " +
              "declare — the declaration would shadow it for the whole scope. " +
              "Rename the predicate, or drop the line if the head meant to cite it", rule.span)
        }
      case _ => ()

    // A declaration stores no clause, so there is nothing for a citation handle or a
    // `@[…]` tag to attach to. Refused rather than dropped: a label on a declaration
    // defines a `Rule` symbol that `using` then finds nothing under, and both carriers
    // were silently lost the moment this arm stopped asserting.
    val carrier: Option[String] =
      if rule.label.isDefined then Some("A citation label on it has nothing to cite.")
      else if rule.meta.isDefined then Some("A `@[…]` tag on it has no clause to govern.")
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
          // A declaration must have been minted by the defining pass at this scope.
          case None =>
            errors += LoadError.Other(
              s"`$name` was never brought into existence: the defining pass does not " +
              "descend into this position, so the declaration would introduce " +
              "nothing and assert nothing",
              rule.span)
          case Some(sym) =>
            // SOMETHING ELSE ALSO DECLARED THE NAME HERE; pass 1 merged both roles:
            // `operation has(x) -> Bool` beside
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
            // Membership: ANY non-rule role makes this declaration a collision.
            // WI-20261029-50361 — not `:- true` where no clause can stand: that advice led
            // a namespace's name to the clause [[refuseHeadNamingNamespace]] now refuses.
            val repair =
              if isNamespaceOnly(kb, sym) then
                "and no clause can be written of it — give the predicate a name of its own"
              else "— write `:- true` to make this a CLAUSE of it, or delete the line"
            kb.symbols.get(sym).kindsSet.diff(DeclarableByARule).toSeq.sortBy(_.ordinal).foreach { k =>
              errors += LoadError.Other(
                s"`$name` is already declared in this scope (kind: $k), so a body-less " +
                s"rule adds nothing to it $repair",
                rule.span)
            }

  /** Does this head carry a `?x: T` ascription in its ARGUMENTS? The parser lowers one
    * to a `typed_var` MARKER node (WI-582), so the question is asked of that shape
    * rather than of a node kind — and through [[isTypedVarMarker]], which pairs the name
    * with the marker's exact shape, because `typed_var` is also an ordinary identifier a
    * user may write (WI-948's *a name, not a verdict*).
    *
    * THE HEAD'S OWN FUNCTOR IS NOT ASKED: the grammar puts a typed column only in an
    * ARGUMENT position, so a marker can never be the head.
    *
    * RECURSIVE, mirroring rustland's `declaration_clause_carrier`, which walks the
    * whole head rather than its top row. A direct-arguments-only walk accepted `rule
    * p(f(?x: T))` — the same ascription one level down — where rustland refuses it, so
    * the two loaders disagreed about a program neither should admit. The nesting is
    * reachable: the grammar allows a typed column in any argument position, not only a
    * top-level one. */
  private def headCarriesTypedColumn(
    fileSym: SymbolTable, fileTerms: SimpleTermStore, tid: ParseTermId
  ): Boolean =
    fileTerms.get(tid) match
      case fn: Term.Fn[ParseTermId] =>
        (fn.posArgs.iterator ++ fn.namedArgs.iterator.map(_._2)).exists { a =>
          isTypedVarMarker(fileTerms, a, fileSym) ||
            headCarriesTypedColumn(fileSym, fileTerms, a)
        }
      case _ => false

  /** WI-20260821-RDGQC — THE ENUMERATION: every reason a head introduces no name of its
    * own, stated ONCE so that the VERDICT and the author's SENTENCE cannot describe
    * different rules. Mirrors rustland's `load::NoIntroduction`.
    *
    * The verdict was a bare `None` from [[ruleIntroducedFunctor]], and the sentence came
    * from a SECOND walk that re-asked the same shape questions in the same order and
    * ended in "the loader's two readings disagree — please report this" for the case
    * where they had stopped agreeing. The reason now IS the refusal, and [[detail]] is a
    * `match` on it with no shape question of its own.
    *
    * A FACT head needs no variant: it is the one-head predicate rule (§6.1) and gets
    * these answers through [[introducedName]]. Nor does a MULTI-head rule with a body:
    * each of its heads asks [[headIntroduces]] on its own ([[headIntroductions]],
    * WI-20260908-NE0E4). */
  private enum NoIntroduction:
    /** SEVERAL HEADS on a BODY-LESS rule, which DECLARES and so names one predicate.
      * Carries the count the sentence quotes. A multi-head rule with a body is N clauses,
      * and each head introduces on its own ([[headIntroductions]], WI-20260908-NE0E4). */
    case SeveralHeads(count: Int)
    /** A `⊥` denial, which names no predicate. */
    case DenialHead
    /** The subject carries the DESUGAR's functor, not the rule's (WI-618): `?x.m(?y)`
      * is `dot_apply`, `?a + ?b` is `add`. Minting it would shadow reserved kernel
      * vocabulary for the whole scope. */
    case DesugaredSubject
    /** The subject is neither an application nor a bare name — a bare VARIABLE head
      * (`rule ?x`) is the shape that reaches this; a bare LITERAL is refused earlier
      * with its own sentence. */
    case NotAnApplication
    /** A QUALIFIED spelling REFERENCES an existing predicate and never introduces one —
      * a rule about the SPELLING, so a dotted head that resolves to nothing still
      * introduces nothing. Otherwise `rule String.isEmpty(?s) <=> true` defines a symbol
      * whose SHORT name is literally `String.isEmpty`. */
    case QualifiedSpelling(name: String)

    /** WHY this head introduces nothing, in the author's terms. */
    def detail: String = this match
      case SeveralHeads(count) =>
        s"it writes $count heads at once, and a declaration declares ONE predicate"
      case DenialHead =>
        "a `⊥` denial names no predicate, so there is nothing for it to declare"
      case DesugaredSubject =>
        "its head functor is the DESUGARING's (`?x.m(?y)` carries `dot_apply`, " +
          "`?a + ?b` carries `add`), not a name the rule introduces"
      case NotAnApplication =>
        "its head is not a functor application, so it names no predicate"
      case QualifiedSpelling(name) =>
        s"`$name` is a QUALIFIED name, and a qualified name references an existing " +
          "predicate — it never introduces one"

  /** The name the SUBJECT node `subject` introduces — the shape questions, asked in one
    * order of a rule's subject and of a fact's head alike.
    *
    * A DOTTED PAREN-LESS subject is asked ahead of the minted test (WI-20260901-719FJ):
    * the parser folds `ns.tgt` into a minted `field_access` chain, whose functor really
    * is the desugar's but which SPELLS A NAME — a qualified one, so it references.
    *
    * A BARE NAME IS AN APPLICATION OF ARITY 0 (WI-20260821-P85Z7): the parser gives it a
    * `Term.Ident`, not a zero-argument `Term.Fn`, and reading only the `Fn` shape made
    * `rule holds()` scoped where it was written while `rule holds` fell to the bare
    * intern. On BOTH paths since WI-20260902-CZJ2N — the two spellings are one term, so
    * a bare `rule tau <=> …` defines exactly as `rule tau() <=> …` does. */
  private def introducedName(
    fileSym: SymbolTable, fileTerms: SimpleTermStore, subject: ParseTermId
  ): Either[NoIntroduction, String] =
    def unqualified(name: String) =
      if name.contains('.') then Left(NoIntroduction.QualifiedSpelling(name)) else Right(name)
    dottedCitationName(fileSym, fileTerms, subject) match
      case Some(chain) => Left(NoIntroduction.QualifiedSpelling(chain))
      case None if fileTerms.isMinted(subject) => Left(NoIntroduction.DesugaredSubject)
      case None => fileTerms.get(subject) match
        case fn: Term.Fn[ParseTermId]    => unqualified(fileSym.name(fn.functor))
        case id: Term.Ident => unqualified(fileSym.name(id.sym))
        case _              => Left(NoIntroduction.NotAnApplication)

  /** The functor a rule introduces and which kind of introduction it is, or the
    * [[NoIntroduction]] reason it introduces nothing. Mirrors rustland's
    * `rule_introduced_functor_name`.
    *
    * THE HEAD COUNT IS ASKED FIRST: a multi-head rule whose first head is also malformed
    * is told it writes several heads, not that its first one is unreadable.
    *
    * The ONE-NAME question, which is the DECLARATION reader's ([[ruleReading]]): a
    * declaration declares one predicate, so several heads answer
    * [[NoIntroduction.SeveralHeads]] here. The clause path asks [[headIntroductions]],
    * which takes a multi-head rule with a body head by head (WI-20260908-NE0E4). */
  private def ruleIntroducedFunctor(
    rule: Rule, fileSym: SymbolTable, fileTerms: SimpleTermStore
  ): Either[NoIntroduction, (String, SymbolKind)] =
    rule.heads match
      case IndexedSeq(RuleHead.Bottom)           => Left(NoIntroduction.DenialHead)
      case IndexedSeq(RuleHead.TermHead(headId)) =>
        headIntroduces(ruleBodyIsEmptyConjunction(rule, fileTerms), headId, fileSym, fileTerms)
      case heads                                 => Left(NoIntroduction.SeveralHeads(heads.length))

  /** What ONE head of `rule` introduces. The SUBJECT is the node the head is about: for
    * an equation (`ite(true, ?t, ?_) <=> ?t`) that is the LHS; for a predicate head it is
    * the head itself. This is the one place the two part ways, and the kind travels with
    * the name so a second walk cannot disagree (WI-898). The rule's LABEL is deliberately
    * never read. */
  private def headIntroduces(
    bodyless: Boolean, headId: ParseTermId, fileSym: SymbolTable, fileTerms: SimpleTermStore
  ): Either[NoIntroduction, (String, SymbolKind)] =
    // Only a BODY-LESS rule can be an equation (a `:-` rule with an `=` head is an
    // ordinary predicate whose head happens to be an equality goal).
    //
    // §8.3 — an equation is BODYLESS, which is a property of the RULE, so the caller
    // asks the ONE owner of it ([[ruleBodyIsEmptyConjunction]]) once per rule, as
    // rustland's `head_subject_name` is handed it, rather than off `body.isDefined`
    // directly: since 061 `rule f(?x) <=> ?x :- true` is the explicit spelling of the
    // same empty body, and it must read as the equation it is HERE and at
    // [[loadRuleHeads]] alike.
    val equationLhs =
      if bodyless then parseEquationLhs(fileSym, fileTerms, headId)
      else None
    val (subject, kind) = equationLhs match
      case Some(lhs) => (lhs, SymbolKind.EquationFunctor)
      case None      => (headId, SymbolKind.Goal)
    introducedName(fileSym, fileTerms, subject).map((_, kind))

  /** WI-20260908-NE0E4 — every name a rule's HEADS introduce, for the clause path's mint.
    *
    * A multi-head rule WITH A BODY is N clauses sharing one body (§5.3, "conjunctive
    * sugar"), so each head introduces exactly what the single-head rule `Hᵢ :- B` would:
    * at the scope it is written in, unless its name already denotes. It used to introduce
    * nothing — [[ruleIntroducedFunctor]] answers `SeveralHeads` — and each head then took
    * the bare intern, ONE global name: `rule lawP: aa, bb :- …` in sort P and `rule lawQ:
    * aa, cc :- …` in sort Q shared `aa`, and P's reader answered from Q's clause.
    *
    * A MULTI-HEAD RULE THAT STORES NOTHING introduces nothing — a body-less one (a
    * declaration declares ONE predicate), an unlabeled one, one with `⊥` among its heads.
    * The load refuses each ([[severalHeadsRefusal]], the one decider), so minting its
    * heads would put names in the table for a rule that stores nothing, and the refused
    * line drew a second error ("introduces that name at 2 scopes", "declare it"). Mirrors
    * rustland's `RuleHeadCollectPass::collect`. */
  private def headIntroductions(
    rule: Rule, fileSym: SymbolTable, fileTerms: SimpleTermStore
  ): IndexedSeq[(String, SymbolKind)] =
    if severalHeadsRefusal(rule).isDefined then IndexedSeq.empty
    else
      val bodyless = ruleBodyIsEmptyConjunction(rule, fileTerms)
      rule.heads.flatMap:
        case RuleHead.TermHead(headId) => headIntroduces(bodyless, headId, fileSym, fileTerms).toOption
        // A `⊥` denial names no predicate.
        case RuleHead.Bottom           => None

  /** WHY A RULE WITH SEVERAL HEADS STORES NO CLAUSE AT ALL — `None` for every rule that
    * stores one per head (a labeled rule with a body and no `⊥` among its heads) and for
    * every one-head rule. ONE DECIDER, read by the load that refuses such a rule
    * ([[loadRuleHeads]]; the body-less arm through [[ruleReading]]'s `DeclaresNothing`)
    * and by the clause path's mint ([[headIntroductions]]). Mirrors rustland's
    * `several_heads_refusal`, arm for arm and in its order: the body first, then `⊥`,
    * then the label. */
  private def severalHeadsRefusal(rule: Rule): Option[SeveralHeadsRefusal] =
    if rule.heads.length < 2 then None
    else if rule.body.isEmpty then Some(SeveralHeadsRefusal.Declaration)
    else if rule.heads.contains(RuleHead.Bottom) then Some(SeveralHeadsRefusal.DenialAmongHeads)
    else if rule.label.isEmpty then Some(SeveralHeadsRefusal.Unlabeled)
    else None

  private enum SeveralHeadsRefusal:
    /** No body: the rule reads as a DECLARATION, which declares one predicate. */
    case Declaration
    /** A `⊥` denial beside other heads. NO SOURCE REACHES IT: the grammar writes `⊥`
      * only as a rule's sole head; the IR can still hold the shape. */
    case DenialAmongHeads
    /** No label: N clauses with no citation handle. */
    case Unlabeled

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
    fileSym: SymbolTable, fileTerms: SimpleTermStore, head: ParseTermId
  ): Option[(String, ParseTermId)] =
    if !fileTerms.isMinted(head) then None
    else fileTerms.get(head) match
      case fn: Term.Fn[ParseTermId] if fn.posArgs.length == 2 && fn.namedArgs.isEmpty =>
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
    fileSym: SymbolTable, fileTerms: SimpleTermStore, head: ParseTermId
  ): Option[ParseTermId] =
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
    fileSym: SymbolTable, fileTerms: SimpleTermStore, head: ParseTermId
  ): Option[(String, Option[String])] =
    parseConnectiveHead(fileSym, fileTerms, head)
      .filterNot((name, _) => Pratt.isEquationFunctor(name))
      .map { (name, lhs) =>
        val subject = fileTerms.get(lhs) match
          case fn: Term.Fn[ParseTermId] => Some(fileSym.name(fn.functor))
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
      s"ever consulted, and a `@[simp]` tag on it never fires (the normalizer reads only " +
      s"the `<=>` equations). $remedy, or give the rule a BODY GOAL to state it " +
      s"as an ordinary law about `$op`."


  /** A conclusion is never a bare literal — rustland's `convert_rule_heads` refusal (WI-893,
    * spec §"A head is an atom"), which scaland lacked: a retired `q(?a) [simp]` inside
    * `rule { … }` loaded silently as an untagged law beside a junk entry headed by the list.
    * WI-20260915-G9EA9 made that the retired spelling's landing shape, so a list of bare
    * names also names the one-token block. At LOAD, where rustland's converter refuses it:
    * the parser's term-shape tests write literal facts (`fact (a: 1)`) on purpose. */
  private def refuseBareLiteralConclusion(
    fileSym: SymbolTable,
    fileTerms: SimpleTermStore,
    t: ParseTermId,
    what: String,
    errors: ArrayBuffer[LoadError]
  ): Boolean =
    val span = fileTerms.spanOf(t)
    def bareName(id: ParseTermId): Option[String] = fileTerms.get(id) match
      case Term.Ref(sym) => Some(fileSym.name(sym))
      case Term.Ident(sym) => Some(fileSym.name(sym))
      case Term.Fn(f, pos, named) if pos.isEmpty && named.isEmpty => Some(fileSym.name(f))
      case _ => None
    def atom() = errors += LoadError.Other(
      s"a $what must be an atom, not a bare literal (a value is not a proposition)", span)
    fileTerms.get(t) match
      case Term.Fn(f, pos, _) if Seq(DesugarTarget.ListLiteral,
        DesugarTarget.SetLiteral, DesugarTarget.TupleLiteral)
        .exists(DesugarTarget.is(fileSym.name(f), _)) =>
        atom()
        val names = pos.toSeq.map(bareName)
        if DesugarTarget.is(fileSym.name(f), DesugarTarget.ListLiteral) && names.nonEmpty && names.forall(_.isDefined) then
          val block = names.flatten.mkString("[", ", ", "]")
          errors += LoadError.Other(s"`$block` is a meta block in the retired spelling: write `@$block`", span)
        true
      case Term.Const(_) =>
        atom(); true
      case _ => false

  /** WI-1090 — push the refusal for a bodyless head written with a non-defining
    * connective, reporting whether it fired. One helper for the two callers a bodyless
    * head has: a `rule` with no body, and a `fact` (which §6.1 defines as exactly
    * that). Rustland shipped the rule side alone and its review found the `fact`
    * spelling loading clean one keyword away. */
  private def refuseNonDefiningConnectiveHead(
    fileSym: SymbolTable, fileTerms: SimpleTermStore, head: ParseTermId,
    span: Span, errors: ArrayBuffer[LoadError]
  ): Boolean =
    nonDefiningConnectiveHead(fileSym, fileTerms, head) match
      case Some((connective, subject)) =>
        errors += LoadError.Other(nonDefiningConnectiveMessage(connective, subject), span)
        true
      case None => false

  /** WI-295: an imported name that did not resolve in pass 2. The head-functor symbol
    * of a rule-introduced predicate is not registered until pass 3, so such names wait
    * for pass 3's head census, which wires them ([[wireDeferredImports]]) — a `Selective`
    * import's name, and since WI-20261022-JBHQC a `Plain` import's whole path: §5.3
    * names both forms as ways to name a rule-introduced functor, and the plain form
    * refused in pass 2 could name one only when an EARLIER load had minted it. The
    * `form` says what each may land on — each form as pass 2 would have. */
  private case class PendingImport[S](
    scope: S, short: String, span: Span, form: PendingForm,
    /** WI-1074 — whose import this is; the pass-4 retry runs outside the per-file loop,
      * so the provenance rides with the deferral. */
    origin: ImportOrigin.File,
    /** The import's PLACE among the writes of its name, held from pass 2
      * ([[SymbolTable.addDeferredImport]]): wired, the import takes it, so a write the
      * text makes after it still outranks it, whatever order the wiring runs in. */
    placeholder: TermSymbol)

  private enum PendingForm:
    /** `import <path>.{short}`, resolved below `target` ([[resolveSelectiveImport]]).
      *
      * `path` is the import's written spelling, and it is a RESOLUTION INPUT only
      * (WI-962): [[resolveSelectiveImport]]'s nested-scope rung builds lookup keys out
      * of it. It used to double as the retry's diagnostic scope name, which is a second
      * source for a field [[LoadError]] says is derived from a scope; the retry now reads
      * that off `target` instead. */
    case Selective(target: TermSymbol, path: String, existingBelow: Boolean)
    /** `import <path>`, whose whole spelling is the qualified name it binds. */
    case Plain(path: String)

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

  /** Is `qname` exactly ONE scope below `base`, with the short name `short` —
    * `base.<segment>.short`? The shape of the nested-scope rung ([[findInNestedScope]]),
    * asked of what exists at pass 2 and of what the head census will mint. */
  private def isOneScopeBelow(qname: String, base: String, short: String): Boolean =
    val prefix = s"$base."
    val suffix = s".$short"
    qname.length > prefix.length + suffix.length && qname.startsWith(prefix) &&
      qname.endsWith(suffix) &&
      !qname.substring(prefix.length, qname.length - suffix.length).contains('.')

  /** One qualified name a deferred import waits for (WI-20261022-JBHQC): the symbol
    * reserved for it, the heads that would mint it (its DEFINERS), and the imports wired
    * to it, to take back if no definer mints it. */
  private final class Reservation[S](
    val sym: TermSymbol,
    val definers: IndexedSeq[Int],
    val imports: ArrayBuffer[(PendingImport[S], String)],
    var minted: Boolean)

  /** A selective import that can only land one scope below its base, wired after phase 2
    * ([[wireLate]]). */
  private final case class LateImport[S](p: PendingImport[S], base: String, existingBelow: Boolean)

  /** WI-20261022-JBHQC — the deferred imports of one scan, wired to symbols reserved for
    * the names its rule heads will mint. Rustland's twin is `DeferredWiring`. */
  private final class DeferredWiring[S](
    val byName: LinkedHashMap[String, Reservation[S]],
    /** Qualified mint name → the heads that would mint it, for the names an import
      * waits for only. */
    val census: LinkedHashMap[String, ArrayBuffer[Int]],
    val late: ArrayBuffer[LateImport[S]]):

    /** Is `answer` the symbol reserved for the name `head` would mint — the head reached
      * through an import of the predicate it DEFINES? Then it introduces it. */
    def isOwnReservation(head: RuleHeadSite[S], answer: ResolveResult): Boolean =
      byName.nonEmpty && (answer match
        case ResolveResult.Found(sym) =>
          byName.get(makeQualified(head.prefix, head.name)).exists(_.sym == sym)
        case _ => false)

    /** Does head `i` INTRODUCE its name, by its answer? */
    def introduces(heads: IndexedSeq[RuleHeadSite[S]], answers: Array[ResolveResult], i: Int): Boolean =
      !answers(i).denotes || isOwnReservation(heads(i), answers(i))

    /** The ONE name a head INTRODUCES exactly one scope below `base`, by the answers,
      * beside none that exists: the nested-scope rung, asked of what the scan mints. */
    def oneScopeBelow(
      heads: IndexedSeq[RuleHeadSite[S]], answers: Array[ResolveResult],
      base: String, short: String, existingBelow: Boolean
    ): Option[String] =
      if existingBelow then None
      else
        val minted = census.collect {
          case (q, definers) if isOneScopeBelow(q, base, short) && definers.exists(introduces(heads, answers, _)) => q
        }.toIndexedSeq
        Option.when(minted.size == 1)(minted.head)

  /** Does `answer` read one of `syms`? */
  private def readsAny(answer: ResolveResult, syms: collection.Set[TermSymbol]): Boolean = answer match
    case ResolveResult.Found(sym)       => syms.contains(sym)
    case ResolveResult.Ambiguous(cands) => cands.exists(syms.contains)
    case ResolveResult.NotFound         => false

  /** The symbol reserved for `target`, reserved now if no import waited for it yet. */
  private def reservation(
    kb: KnowledgeBase, wiring: DeferredWiring[kb.ScopeId],
    heads: IndexedSeq[RuleHeadSite[kb.ScopeId]], target: String
  ): Reservation[kb.ScopeId] =
    wiring.byName.getOrElseUpdate(target, {
      val definers = wiring.census(target).toIndexedSeq
      val first = heads(definers.head)
      Reservation[kb.ScopeId](
        kb.symbols.reserve(first.name, target, first.kind, first.scope),
        definers, ArrayBuffer.empty, minted = false)
    })

  /** Wire the import `p` to the symbol reserved for `target`, at the place it holds. */
  private def wireImport(
    kb: KnowledgeBase,
    wiring: DeferredWiring[kb.ScopeId],
    heads: IndexedSeq[RuleHeadSite[kb.ScopeId]],
    target: String,
    p: PendingImport[kb.ScopeId],
    written: String
  ): Unit =
    val r = reservation(kb, wiring, heads, target)
    kb.symbols.wireDeferredImport(p.scope, p.short, p.placeholder, r.sym, p.origin)
    r.imports += ((p, written))

  /** THE SELECTIVE IMPORTS THAT WAIT FOR PHASE 2'S ANSWERS: one that can only land one
    * scope below its base lands on [[DeferredWiring.oneScopeBelow]]. Each wired here has
    * every head of its short name asked again; one that lands nowhere names nothing. */
  private def wireLate(
    kb: KnowledgeBase,
    wiring: DeferredWiring[kb.ScopeId],
    heads: IndexedSeq[RuleHeadSite[kb.ScopeId]],
    answers: Array[ResolveResult],
    fileIds: IndexedSeq[FileId],
    errors: ArrayBuffer[LoadError]
  ): Unit =
    for LateImport(p, base, existingBelow) <- wiring.late.toIndexedSeq do
      wiring.oneScopeBelow(heads, answers, base, p.short, existingBelow) match
        case Some(target) =>
          wireImport(kb, wiring, heads, target, p, s"$base.${p.short}")
          for (h, i) <- heads.zipWithIndex if h.name == p.short do
            kb.symbols.setAskingFile(Some(fileIds(h.fileIdx)))
            answers(i) = ruleHeadLadderAnswer(kb, h.name, h.scope)
        case None =>
          kb.symbols.dropDeferredImport(p.scope, p.short, p.placeholder)
          errors += unresolvedDeferred(kb, p, s"$base.${p.short}")
    wiring.late.clear()

  /** WITHDRAW THE RESERVATIONS NO DEFINER MINTS, and ask the ladder again for every head
    * that read one. Each import wired to it is taken back: a selective one re-pointed, at
    * its place, to the one name a head introduces one scope below its base (a load in two
    * steps resolves it so — found by `/code-review`), any other refused. ONLY those whose
    * definers read no other idle reservation, each round: one that does may mint once
    * that one is withdrawn. Where every idle one reads another (a cycle), they go
    * together. A round withdraws one at least, and a re-pointed import lands on a name a
    * head introduces, which is not idle; so this ends. */
  private def settleWiring(
    kb: KnowledgeBase,
    wiring: DeferredWiring[kb.ScopeId],
    heads: IndexedSeq[RuleHeadSite[kb.ScopeId]],
    answers: Array[ResolveResult],
    fileIds: IndexedSeq[FileId],
    errors: ArrayBuffer[LoadError]
  ): Unit =
    var done = false
    while !done do
      val idle = wiring.byName.values
        .filter(r => r.definers.forall(i => !wiring.introduces(heads, answers, i)))
        .map(_.sym).toSet
      if idle.isEmpty then done = true
      else
        val ready = wiring.byName.collect {
          case (_, r) if idle.contains(r.sym) && r.definers.forall(i => !readsAny(answers(i), idle)) => r.sym
        }.toSet
        val batch = if ready.isEmpty then idle else ready
        for q <- wiring.byName.collect { case (q, r) if batch.contains(r.sym) => q }.toIndexedSeq.sorted do
          val r = wiring.byName.remove(q).get
          for (p, path) <- r.imports do takeBack(kb, wiring, heads, answers, r.sym, p, path, errors)
          kb.symbols.withdrawReserved(r.sym)
        for (h, i) <- heads.zipWithIndex if readsAny(answers(i), batch) do
          kb.symbols.setAskingFile(Some(fileIds(h.fileIdx)))
          answers(i) = ruleHeadLadderAnswer(kb, h.name, h.scope)

  /** Take back `p`, wired to the withdrawn `sym` ([[settleWiring]] says what that is). */
  private def takeBack(
    kb: KnowledgeBase,
    wiring: DeferredWiring[kb.ScopeId],
    heads: IndexedSeq[RuleHeadSite[kb.ScopeId]],
    answers: Array[ResolveResult],
    sym: TermSymbol,
    p: PendingImport[kb.ScopeId],
    path: String,
    errors: ArrayBuffer[LoadError]
  ): Unit =
    val repointed = p.form match
      case PendingForm.Selective(_, base, existingBelow) =>
        wiring.oneScopeBelow(heads, answers, base, p.short, existingBelow)
      case PendingForm.Plain(_) => None
    repointed match
      case Some(target) =>
        val r = reservation(kb, wiring, heads, target)
        kb.symbols.rewireImport(p.scope, p.short, sym, r.sym, p.origin)
        r.imports += ((p, path))
      case None =>
        kb.symbols.removeImport(p.scope, p.short, sym, p.origin)
        errors += unresolvedDeferred(kb, p, path)

  /** The first head to mint `qualified` adopts the symbol reserved for it. */
  private def adoptReservation(
    kb: KnowledgeBase, wiring: DeferredWiring[kb.ScopeId], qualified: String, kind: SymbolKind
  ): Unit =
    wiring.byName.get(qualified).filter(!_.minted).foreach { r =>
      kb.symbols.adoptReserved(r.sym, kind)
      r.minted = true
    }

  /** Every reservation [[settleWiring]] kept has a definer that mints it. One that was not
    * minted is a loader invariant failing, REPORTED as that — not as an import naming
    * nothing, which would hide a broken [[settleWiring]] behind an ordinary refusal
    * (found by `/code-review`). */
  private def reportUnminted(
    kb: KnowledgeBase, wiring: DeferredWiring[kb.ScopeId], errors: ArrayBuffer[LoadError]
  ): Unit =
    for q <- wiring.byName.collect { case (q, r) if !r.minted => q }.toIndexedSeq.sorted
        (p, path) <- wiring.byName(q).imports do
      errors += LoadError.Other(
        s"the import of `$path` was wired to the predicate a rule head of this load would " +
        s"mint, and no head minted it. This is a loader invariant failing rather than a " +
        s"fault in the program; please report it.", p.span)

  /** The refusal of a deferred import that names nothing: the selective form's names its
    * base's scope, as pass 2's would; the plain form's its path. */
  private def unresolvedDeferred(
    kb: KnowledgeBase, p: PendingImport[kb.ScopeId], path: String
  ): LoadError = p.form match
    case PendingForm.Selective(target, _, _) =>
      LoadError.UnresolvedName(p.short, p.span, kb.qualifiedNameOf(target))
    case PendingForm.Plain(_) => LoadError.UnresolvedImport(path, p.span)

  /** WI-20261022-JBHQC — WIRE THE DEFERRED IMPORTS OF A SCAN before its heads are decided.
    * The head census says which qualified names the scan's heads would mint; an import
    * whose qualified name is among them is wired to a symbol reserved for it, at the place
    * it holds, and the first of its definers adopts it at the mint. A selective import that
    * can only land one scope below its base waits for phase 2's answers ([[wireLate]]). One
    * whose name no head could mint names nothing, and is refused now, before any head
    * reads it. */
  private def wireDeferredImports(
    kb: KnowledgeBase,
    heads: IndexedSeq[RuleHeadSite[kb.ScopeId]],
    pending: IndexedSeq[PendingImport[kb.ScopeId]],
    errors: ArrayBuffer[LoadError]
  ): DeferredWiring[kb.ScopeId] =
    val wiring = DeferredWiring[kb.ScopeId](LinkedHashMap.empty, LinkedHashMap.empty, ArrayBuffer.empty)
    if pending.isEmpty then return wiring
    val shorts = pending.map(_.short).toSet
    for (h, i) <- heads.zipWithIndex if shorts.contains(h.name) do
      wiring.census.getOrElseUpdate(makeQualified(h.prefix, h.name), ArrayBuffer.empty) += i
    for p <- pending do
      p.form match
        case PendingForm.Plain(path) =>
          if wiring.census.contains(path) then wireImport(kb, wiring, heads, path, p, path)
          else
            kb.symbols.dropDeferredImport(p.scope, p.short, p.placeholder)
            errors += unresolvedDeferred(kb, p, path)
        case PendingForm.Selective(_, path, existingBelow) =>
          val direct = s"$path.${p.short}"
          if wiring.census.contains(direct) then wireImport(kb, wiring, heads, direct, p, direct)
          else if wiring.census.keys.exists(isOneScopeBelow(_, path, p.short)) then
            wiring.late += LateImport(p, path, existingBelow)
          else
            kb.symbols.dropDeferredImport(p.scope, p.short, p.placeholder)
            errors += unresolvedDeferred(kb, p, direct)
    wiring

  /** WI-20261022-JBHQC — A LOCAL THE MINT PUT AHEAD OF WHAT A HEAD DENOTED, at any address
    * (rustland's `report_post_mint_captures` says why): the frozen answer of each
    * denoting head, whose name the scan minted somewhere, against what its ladder says
    * now. A group the one-address check refused is not refused twice. */
  private def reportPostMintCaptures(
    kb: KnowledgeBase,
    heads: IndexedSeq[RuleHeadSite[kb.ScopeId]],
    denotes: IndexedSeq[Boolean],
    answers: Array[ResolveResult],
    refused: Set[(kb.ScopeId, String)],
    fileIds: IndexedSeq[FileId],
    errors: ArrayBuffer[LoadError]
  ): Set[(kb.ScopeId, String)] =
    val minted = heads.indices.filter(!denotes(_)).map(heads(_).name).toSet
    val groups = LinkedHashMap.empty[(kb.ScopeId, String), ArrayBuffer[Int]]
    for (h, i) <- heads.zipWithIndex
        if denotes(i) && minted.contains(h.name) && !refused.contains((h.scope, h.name)) do
      answers(i) match
        case ResolveResult.Found(frozen) =>
          kb.symbols.setAskingFile(Some(fileIds(h.fileIdx)))
          ruleHeadLadderAnswer(kb, h.name, h.scope) match
            case ResolveResult.Found(now) if now != frozen =>
              // Only a mint moves an answer, and a mint is a head of this scan introducing
              // its name at its scope; an answer that moved to anything else is reported as
              // the loader invariant it is, not skipped.
              val capturing = kb.symbols.get(now) match
                case SymbolDef.Resolved(_, _, _, scope) =>
                  Option.when(heads.indices.exists(j =>
                    !denotes(j) && heads(j).scope == scope && heads(j).name == h.name))(scope)
                case SymbolDef.Unresolved(_) => None
              capturing match
                case Some(scope) => groups.getOrElseUpdate((scope, h.name), ArrayBuffer.empty) += i
                case None =>
                  errors += LoadError.Other(
                    s"the rule head `${h.name}` written in '${kb.scopeDisplayName(h.scope)}' resolved " +
                    s"to '${kb.qualifiedNameOf(frozen)}' when its predicate was decided and to " +
                    s"'${kb.qualifiedNameOf(now)}' once the load's heads were minted, and no head of " +
                    s"this load introduced the second. This is a loader invariant failing rather " +
                    s"than a fault in the program; please report it.", h.span)
            case _ =>
        case _ =>
    var out = Set.empty[(kb.ScopeId, String)]
    for ((scope, name), captured) <- groups.toIndexedSeq.sortBy((k, _) => (kb.scopeDisplayName(k._1), k._2)) do
      val introducing = heads.indices.filter(i => !denotes(i) && heads(i).scope == scope && heads(i).name == name)
      errors += captureRefusal(kb, heads, scope, name, captured.toIndexedSeq, introducing)
      out += ((scope, name))
    out

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
                    val placeholder = kb.symbols.placeholder()
                    kb.symbols.addDeferredImport(scope, name, placeholder)
                    pending += PendingImport(
                      scope, name, n.span,
                      PendingForm.Selective(sym, pathStr, nestedScopeMatches(kb, pathStr, name).nonEmpty),
                      origin, placeholder)
            case ImportKind.Wildcard =>
              // WI-988: a wildcard brings a scope's CONTENTS in, so the path has to name
              // something with contents — a namespace, or a sort (§5.1 names both).
              // WI-1074: through [[SymbolTable.addImportParent]] — this link is one
              // file's import, not a property of the address.
              parentScopeOf(kb, sym, Set(SymbolKind.Namespace, SymbolKind.Sort),
                s"the wildcard import `$pathStr.*`", imp.path.span, errors)
                .foreach(p => kb.symbols.addImportParent(scope, p, isEnclosing = false, origin))
        // WI-20261022-JBHQC — a plain import of a name pass 3 has yet to mint waits for
        // the head census, as the selective form's names do (WI-295), which asks the
        // same question pass 2 does: the qualified name. Every miss waits: the census
        // refuses one no head mints before any head is decided ([[wireDeferredImports]]).
        case None if imp.kind == ImportKind.Plain =>
          val short = fileSym.name(imp.path.last)
          val placeholder = kb.symbols.placeholder()
          kb.symbols.addDeferredImport(scope, short, placeholder)
          pending += PendingImport(scope, short, imp.path.span, PendingForm.Plain(pathStr), origin,
            placeholder)
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
    val matches = nestedScopeMatches(kb, basePath, short)
    if matches.size == 1 then Some(matches.head) else None

  /** Every name exactly one scope below `basePath` with the short name `short` — the
    * nested-scope rung's matches; a deferred import keeps whether there was any. */
  private def nestedScopeMatches(
    kb: KnowledgeBase, basePath: String, short: String
  ): Set[TermSymbol] =
    kb.symbols.byQualifiedName.iterator.collect {
      case (qname, sym) if isOneScopeBelow(qname, basePath, short) => sym
    }.toSet

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
    // Membership: any role with contents admits this parent edge.
    val actual = kb.symbols.get(sym).kindsSet
    if actual.exists(allowed.contains) then Some(kb.symbols.scopeOf(sym))
    else
      val got = if actual.isEmpty then "names nothing declared"
        else s"names a ${actual.toSeq.sortBy(_.ordinal).map(_.toString.toLowerCase).mkString("/")}"
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
    ).exists { n =>
      // Either spelling of the one sort: unmarked, the dotted rung reads it as its own
      // qualified name, which is what the marker says outright.
      val written = joinSegments(fileSym, n.segments)
      absolutePathTarget(written).getOrElse(written) == "anthill.prelude.EffectsRuntime"
    }

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

    private def refuseBareLiteralHeads(rule: Rule): Boolean =
      rule.heads.map {
        case RuleHead.TermHead(t) => refuseBareLiteralConclusion(fileSym, fileTerms, t, "rule head", errors)
        case RuleHead.Bottom => false
      }.contains(true)

    def atItem(item: Item, scope: kb.ScopeId, prefix: String): Unit =
      item match
        case Item.FactItem(fact) =>
          // WI-1090: a fact IS a bodyless rule (§6.1), so `fact lhs === rhs` is the same
          // dead clause the rule arm refuses — refused BEFORE the assert, so no consumer
          // that collects errors without failing the load sees the pre-fix KB.
          if !refuseBareLiteralConclusion(fileSym, fileTerms, fact.term, "fact", errors)
            && !refuseNonDefiningConnectiveHead(
            fileSym, fileTerms, fact.term, fileTerms.spanOf(fact.term), errors) then
            // WI-20260901-719FJ: a fact head is a LOGICAL SUBJECT too — `fact ns.tgt`
            // is the same reference `fact ns.tgt()` is.
            val kbTerm = reallocTerm(kb, fileTerms, fileSym, fact.term, scope, errors, atGoal = true, atHead = true)
            if !refuseHeadNamingNamespace(kb, kbTerm, "fact", fileTerms.spanOf(fact.term), errors) then
              val sortSort = findSortTerm(kb, "anthill.reflect.Fact")
              kb.assertFact(kbTerm, sortSort, scope)

        case Item.RuleItem(rule) =>
          val sortSort = findSortTerm(kb, "anthill.reflect.Rule")
          if !refuseBareLiteralHeads(rule) then
            loadRuleHeads(kb, rule, fileTerms, fileSym, scope, sortSort, errors)

        case Item.RuleBlockItem(block) =>
          val sortSort = findSortTerm(kb, "anthill.reflect.Rule")
          for rule <- block.entries do
            if !refuseBareLiteralHeads(rule) then
              loadRuleHeads(kb, rule, fileTerms, fileSym, scope, sortSort, errors)

        // An eponymous constructor IS its sort (§6.3): no parent, so no `entity_of` fact,
        // exactly as pass 1 records no parent edge for it.
        case Item.EntityItem(entity) if eponymousSortSymbol(kb, fileSym, entity.name.segments, scope).isDefined =>

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
          loadProof(kb, p, fileSym, scope, errors)

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

    // The rule's SHAPE refusal ([[severalHeadsRefusal]], the one decider the clause
    // path's mint reads too — [[headIntroductions]] — so a rule refused here mints
    // nothing), read at the places below it is reported from. THE REFUSALS RUN IN
    // RUSTLAND'S ORDER (`load_rule`): the reading, `⊥`, WI-1090's connective, the label —
    // so one program gets one diagnostic in both implementations (found by
    // `/code-review`: an unlabeled `rule f(1) === 2, g(1) :- true` was told about its
    // label here and about its `===` there).
    val severalHeads = severalHeadsRefusal(rule)

    // PROPOSAL 061 — NO BODY ⇒ DECLARES. A body-less plain head brought its predicate
    // into existence in PASS 1 ([[declarePredicate]]) and asserts NOTHING here;
    // asserting it is what `fact` and the explicit `:- true` are for. The reading is
    // taken from the ONE decider both passes share, so the name pass 1 minted and the
    // clause this pass declines to store cannot disagree.
    //
    // ASKED BEFORE WI-1090's CONNECTIVE REFUSAL, in rustland's order (`load_rule` reads
    // `rule_reading` first): a body-less multi-head rule with a `===` head is refused for
    // what it is — several heads where a declaration declares one — in both
    // implementations. A one-head connective rule reads `Clause` here and reaches the
    // refusal below unchanged.
    ruleReading(rule, fileSym, fileTerms) match
      case RuleReading.Clause => ()
      case RuleReading.Declaration(name) =>
        refuseDeclarationThatCannotStand(kb, rule, name, fileSym, fileTerms, scope, errors)
        return
      case RuleReading.DeclaresNothing(why) =>
        errors += LoadError.Other(
          "a body-less rule DECLARES its predicate (proposal 061, §5.3), but this one " +
          s"declares nothing: ${why.detail}",
          rule.span)
        return

    if severalHeads.contains(SeveralHeadsRefusal.DenialAmongHeads) then
      errors += LoadError.Other(
        "denial heads (`⊥`) cannot be combined with positive heads in a multi-head rule",
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

    if severalHeads.contains(SeveralHeadsRefusal.Unlabeled) then
      errors += LoadError.Other(
        "multi-head rule requires a label so the rule has a unique citation handle " +
        "(e.g. `rule my_law: H1, H2 :- B`)",
        rule.span)
      return

    // WI-20260901-719FJ: a top-level body atom IS a goal, so a dotted paren-less
    // citation written there is the NAME. Below the top level a goal is found by
    // `reallocTerm`'s `Term.Fn` arm, in the slots the resolver proves.
    // §6.1 — a top-level `true` is ERASED, so the body stays EMPTY. That is what makes
    // `rule H :- true` the exact spelling of `fact H`: the same clause, with the same
    // empty body, reached by the two syntaxes §6.1 says mean one thing. It is NOT what
    // `true` MEANS — that is J38JE's "a boolean constant in goal position is a SEARCH",
    // which belongs in the resolver (NARC7). See [[isEmptyConjunctionGoal]] for the split.
    val kbBody = rule.body.map(_.filterNot(isEmptyConjunctionGoal(fileTerms, _)).map(b =>
      reallocTerm(kb, fileTerms, fileSym, b, scope, errors, vm, atGoal = true))).getOrElse(IndexedSeq.empty)

    if hasBottom then
      // A DENIAL WITH AN EMPTY BODY IS AN UNCONDITIONAL CONTRADICTION, and 061's `true`
      // strip is what newly makes one reachable: before it, `rule ⊥ :- true` kept an
      // unresolvable `true` goal and the clause was dead, so nothing said anything and
      // nothing fired. Stripped, the body is `IndexedSeq.empty` and the clause asserts
      // "false", unconditionally — a program that says nothing can be true, loaded in
      // silence. It is also miscounted downstream: every reader that reads body-
      // emptiness as fact-ness (`KnowledgeBase.factCount`, the fact-first sort) counts
      // this denial among the facts.
      //
      // REFUSED, MATCHING THE BODY-LESS SPELLING. `rule ⊥` is already refused
      // ([[NoIntroduction.DenialHead]]), and §6.1 makes `:- true` the SAME empty
      // body — so admitting one spelling and refusing the other is the disagreement
      // this delivery exists to remove. The strip's purpose is `fact H` / `rule H :-
      // true` equivalence for POSITIVE heads; a denial has no `fact` spelling to be
      // equivalent to.
      if kbBody.isEmpty then
        errors += LoadError.Other(
          "a `⊥` denial with an empty body is an unconditional contradiction: it asserts " +
            "that nothing can be true. `:- true` is the empty body (§6.1), so this is the " +
            "same rule as the body-less `rule ⊥`, which is refused too. Give the denial " +
            "the goals it should fire on, or delete the line",
          rule.span)
        return
      val botTerm = kb.alloc(Term.Bottom)
      kb.assertRule(botTerm, kbBody, sortSort, scope)
    else
      // One horn rule per head, sharing body (and shared var scope via vm).
      // WI-20261029-50361: a head that names a namespace refuses the whole rule, none of
      // its heads stored, as rustland's `load_rule` returns at it.
      val kbHeads = positiveHeads.map { headId =>
        // WI-20260901-719FJ: a rule head is a LOGICAL SUBJECT.
        headId -> reallocTerm(kb, fileTerms, fileSym, headId, scope, errors, vm, atGoal = true, atHead = true)
      }
      val refused = kbHeads.exists((headId, kbHead) =>
        refuseHeadNamingNamespace(kb, kbHead, "rule", fileTerms.spanOf(headId), errors))
      if !refused then
        for (_, kbHead) <- kbHeads do kb.assertRule(kbHead, kbBody, sortSort, scope)

  // ── Proof / Provides loaders (proposal 025 + 031) ────────────

  private def loadProof(
    kb: KnowledgeBase,
    p: anthill.parse.ProofDecl,
    fileSym: SymbolTable,
    scope: kb.ScopeId,
    errors: ArrayBuffer[LoadError]
  ): Unit =
    val targetStr = joinSegments(fileSym, p.target.segments)
    // The target is recorded AS WRITTEN and not resolved — scaland discharges no proof.
    // An ABSOLUTE one is still asked whether it names anything: it claims a symbol by
    // its own qualified name, so a miss is the same loud miss [[resolveName]] gives a
    // marked name in a term, and not a string that happens to be recorded.
    if absolutePathTarget(targetStr).isDefined
      && lookupWritten(kb, targetStr, scope) == ResolveResult.NotFound then
      errors += LoadError.UnresolvedName(targetStr, p.target.span, kb.scopeDisplayName(scope))
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

  /** G2BXZ: declaration, head collection and loading must use ONE scope decision.
    * The base sort owns clauses in every host language, including parameterized specs.
    * Resolve before entering that scope, so the name uses the block's written context. */
  private def providesBlockScope(
    kb: KnowledgeBase, fileSym: SymbolTable, pb: anthill.parse.ProvidesBlock,
    writtenScope: kb.ScopeId, errors: ArrayBuffer[LoadError]
  ): Option[kb.ScopeId] =
    def resolve(name: Name): Option[kb.ScopeId] =
      val text = joinSegments(fileSym, name.segments)
      lookupWritten(kb, text, writtenScope) match
        case ResolveResult.Found(sym) =>
          parentScopeOf(kb, sym, Set(SymbolKind.Sort), s"provides $text", name.span, errors)
        case ResolveResult.Ambiguous(candidates) =>
          errors += LoadError.AmbiguousSymbol(text, candidates.map(kb.qualifiedNameOf).toIndexedSeq,
            name.span, kb.scopeDisplayName(writtenScope))
          None
        case ResolveResult.NotFound =>
          errors += LoadError.UnresolvedName(text, name.span, kb.scopeDisplayName(writtenScope))
          None

    pb.spec match
      case TypeExpr.Simple(name) => resolve(name)
      case TypeExpr.Parameterized(name, _) => resolve(name)
      case _ =>
        errors += LoadError.Other("a host provides block must name a sort", pb.span)
        None

  private def loadProvidesBlock(
    kb: KnowledgeBase,
    pb: anthill.parse.ProvidesBlock,
    fileTerms: SimpleTermStore,
    fileSym: SymbolTable,
    writtenScope: kb.ScopeId,
    errors: ArrayBuffer[LoadError]
  ): Unit =
    val scope = providesBlockScope(kb, fileSym, pb, writtenScope, errors) match
      case Some(target) => target
      case None => return
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
        val kbTerm = reallocTerm(kb, fileTerms, fileSym, f.term, scope, errors, atGoal = true, atHead = true)
        if !refuseHeadNamingNamespace(kb, kbTerm, "fact", fileTerms.spanOf(f.term), errors) then
          kb.assertFact(kbTerm, factSort, scope)
      case ProvidesItem.ProofI(p) =>
        loadProof(kb, p, fileSym, scope, errors)
      case ProvidesItem.ProvidesClauseI(pc) =>
        loadProvidesClause(kb, pc, fileSym, scope)
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

  /** WI-582: whether the node at `tid` is the parser-emitted typed-pattern marker
    * `typed_var(?x, type: T)`.
    *
    * PROVENANCE FIRST, and it is not redundant with the name and shape tests below —
    * the same pairing [[dottedCitationName]] states at its own gate. `type` is an
    * ordinary identifier in scaland's grammar (nothing reserves it; the parser interns
    * it only as a named-arg key), so a hand-written `rule p(typed_var(?x, type: Foo))`
    * satisfies the name AND the exact shape. Keyed on those alone, the loader read a
    * user's own functor as this desugar: [[headCarriesTypedColumn]] then refused the
    * program naming a typed column the source does not contain, and [[reallocTerm]]
    * stripped the node to its first argument. `allocMintedAt` in `typedVarArg` is the
    * provenance this asks; rustland's `is_typed_column` asks `parse_terms.is_minted`
    * for the same measured reason.
    *
    * The name and shape tests stay, because minted-ness alone does not say WHICH
    * desugar wrote the node, and `posArgs(0)` below would be out of bounds for another.
    * A non-marker `typed_var` falls through to normal loading. */
  private def isTypedVarMarker(fileTerms: SimpleTermStore, tid: ParseTermId, fileSym: SymbolTable): Boolean =
    fileTerms.isMinted(tid) && (fileTerms.get(tid) match
      case fn: Term.Fn[ParseTermId] =>
        fileSym.name(fn.functor) == "typed_var" &&
          fn.posArgs.length == 1 &&
          fn.namedArgs.exists { case (k, _) => fileSym.name(k) == "type" }
      case _ => false)

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
    fileSym: SymbolTable, fileTerms: SimpleTermStore, termId: ParseTermId
  ): Option[String] =
    if !fileTerms.isMinted(termId) then return None
    fileTerms.get(termId) match
      case fn: Term.Fn[ParseTermId]
        if fn.namedArgs.isEmpty && DesugarTarget.is(fileSym.name(fn.functor), DesugarTarget.FieldAccess) => ()
      case _ => return None
    val segments = ArrayBuffer.empty[String]
    var cur = termId
    var done = false
    while !done do
      fileTerms.get(cur) match
        case id: Term.Ident =>
          segments += fileSym.name(id.sym)
          done = true
        case fn: Term.Fn[ParseTermId]
          if DesugarTarget.is(fileSym.name(fn.functor), DesugarTarget.FieldAccess)
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
    termId: ParseTermId,
    scope: kb.ScopeId,
    errors: ArrayBuffer[LoadError],
    varMap: HashMap[Int, VarId] = HashMap.empty,
    /** WI-20260901-719FJ — is this node a LOGICAL SUBJECT: a rule head, a `fact` head or
      * a rule-body goal? See the collapse below for what it decides, and
      * [[dottedCitationName]] for what a dotted paren-less citation is. `false` for a
      * DATA slot, which keeps the chain: a fact's argument and the pattern that searches
      * for it must build ONE term. It reaches a child only through a GOAL SLOT of this
      * node — see the `Term.Fn` arm. */
    atGoal: Boolean = false,
    // Rustland admits an unresolved qualified subject, but not its data slots.
    atHead: Boolean = false,
    /** WI-20261020-80VNX — is this node inside a field DECLARED `anthill.reflect.Term`
      * ([[KnowledgeBase.isQuotedField]])? Such a field holds a quoted pattern, judged as
      * written: `S(…)` is not refused there. Reaches every node below the field. */
    quoted: Boolean = false
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
          val sym = resolveName(kb, name, scope, errors, fileTerms.spanOf(termId), allowQualifiedMiss = atHead)
          if !atHead then refuseNamespaceGoal(kb, sym, fileTerms.spanOf(termId), errors)
          return
            if kb.symbols.isResolved(sym) then kb.alloc(Term.Ref(sym))
            else kb.alloc(Term.Ident(sym))
        case None => ()
    // A CONSTRUCTOR'S QUALIFIED NAME IS THE REFERENCE ITS ONE-SEGMENT NAME IS, in a data slot
    // too (§6.7): `fact holds(Colour.red)` holds `red`'s symbol, as `fact plain(red)` does, so
    // a goal writing either spelling finds either fact; and so is a sort's (`fact
    // holds(Outer.Inner)` holds `Inner`'s). Any other dotted chain in a data slot keeps its
    // spelling. Mirrors rustland's `data_slot_dotted_ctor` and `data_slot_dotted_type`, which
    // also reads an alias through, as scaland reads none.
    else
      dottedCitationName(fileSym, fileTerms, termId).map(lookupWritten(kb, _, scope)) match
        case Some(ResolveResult.Found(sym)) if kb.isConstructorSymbol(sym) || kb.namesOnlyAType(sym) =>
          return kb.alloc(Term.Ref(sym))
        case _ => ()

    fileTerms.get(termId) match
      case Term.Const(lit) =>
        // NARC7: goal slots descend through this same path. Literal arguments of
        // ordinary predicates remain data; only Bool has a constant-goal reading.
        if atGoal && !atHead then
          lit match
            case Literal.BoolLit(_) => ()
            case other => errors += LoadError.ConstantInGoalPosition(
              Parser.renderLiteral(other), fileTerms.spanOf(termId))
        kb.alloc(Term.Const(lit))
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
      case fn: Term.Fn[ParseTermId] if isTypedVarMarker(fileTerms, termId, fileSym) =>
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
      case fn: Term.Fn[ParseTermId] =>
        val name = fileSym.name(fn.functor)
        // ERF7T replaces the connective-only override with ordinary absolute lookup.
        // A missing target fails loudly; a same-spelled local operation cannot answer.
        val resolved = resolveName(kb, name, scope, errors, fileTerms.spanOf(termId), allowQualifiedMiss = atHead)
        // WI-20261020-80VNX — A WRITTEN BRACKET IS A TYPE, in a clause as in a signature
        // (§4.4; rustland's `Loader::convert_term_inner`, JB6RS steps 3–4): `Foo[X = Int64]`
        // and `red[]` are headed by the constructor's TYPE FACE, so a type written as data
        // and an instance are never one term — `fact held(red[])` is not found by
        // `:- held(red)` — and a name its bindings write is read in a type context, which
        // the parser records on the name (`isTypeName`, the `Term.Ref` arm).
        val isTypeApp = fileTerms.isTypeApplication(termId)
        val kbFunctor = if isTypeApp then kb.typeFaceOf(resolved) else resolved
        // WI-20261020-80VNX — AND ONLY A BARE NAME FALLS BACK (§4.4): `S(…)` written over a
        // name that is only a type applies nothing, where it used to be the type in silence
        // (`Eq(T: ?q)` answered from `fact Eq[T = Int64]`). A bracket is the type. Rustland's
        // `refuse_sort_applied_as_data` also exempts a node its converter MINTED; no node
        // scaland's parser mints is headed by a sort (measured: the gate failed no row).
        if !quoted && !isTypeApp && kb.namesOnlyAType(kbFunctor) then
          errors += LoadError.SortAppliedAsData(kb.resolveSym(kbFunctor), fileTerms.spanOf(termId))
        // A GOAL SLOT IS A GOAL: `not`'s negand is proved, not matched, so it is read
        // as a logical subject like the body goal it sits in — `not(ns.flag)` negates
        // the predicate `ns.flag`, where a data reading would negate a `field_access`
        // chain. The slots are [[KnowledgeBase.goalArgSlots]]'s, keyed by the tag the
        // resolver dispatches on and asked of the RESOLVED functor, and only under a
        // node that is itself a goal: `holds(not(a.b))` stores data. Every other
        // argument is DATA, which keeps a fact's slot and the pattern that searches for
        // it spelling one term. Mirrors rustland's `goal_arg_slots` descent.
        if atGoal && !atHead then refuseNamespaceGoal(kb, kbFunctor, fileTerms.spanOf(termId), errors)
        val goalSlots =
          if atGoal then kb.goalArgSlots(kbFunctor, fn.posArgs.length) else Set.empty[Int]
        // A field declared `Term` holds what is written in it, quoted — named, or by
        // position against the declared field order.
        def quotedField(field: Option[TermSymbol]): Boolean =
          quoted || field.exists(kb.isQuotedField(kbFunctor, _))
        val declaredFields = kb.entityFieldNames(kbFunctor)
        val kbPos = IArray.from(fn.posArgs.zipWithIndex.map((id, i) =>
          reallocTerm(kb, fileTerms, fileSym, id, scope, errors, varMap, atGoal = goalSlots(i),
            quoted = quotedField(declaredFields.flatMap(_.lift(i))))))
        val kbNamed = IArray.from(fn.namedArgs.map { (sym, id) =>
          val kbKeySym = kb.intern(fileSym.name(sym))
          (kbKeySym, reallocTerm(kb, fileTerms, fileSym, id, scope, errors, varMap,
            quoted = quotedField(Some(kbKeySym))))
        })
        kb.alloc(Term.Fn(kbFunctor, kbPos, kbNamed))
      case Term.Ref(sym) =>
        val name = fileSym.name(sym)
        val kbSym = resolveName(kb, name, scope, errors, fileTerms.spanOf(termId), allowQualifiedMiss = atHead)
        if atGoal && !atHead then refuseNamespaceGoal(kb, kbSym, fileTerms.spanOf(termId), errors)
        // A name written in a TYPE position (§4.4; rustland's `type_context_binding` and
        // its type lowerings, JB6RS steps 3–5) — a bracket's binding (`Box[V = red]` is
        // `Box[V = red[]]`), an arrow's or tuple's component — is the TYPE: a constructor
        // there is named by its type face, where in a data slot it is its instance.
        kb.alloc(Term.Ref(if fileTerms.isTypeName(termId) then kb.typeFaceOf(kbSym) else kbSym))
      case Term.Ident(sym) =>
        val name = fileSym.name(sym)
        val kbSym = resolveName(kb, name, scope, errors, fileTerms.spanOf(termId), allowQualifiedMiss = atHead)
        if atGoal && !atHead then refuseNamespaceGoal(kb, kbSym, fileTerms.spanOf(termId), errors)
        // WI-20260902-CZJ2N — PROMOTE A RESOLVED BARE NAME TO `Ref`, which is what
        // rustland's `convert_term_inner` has always done and scaland did not. Without
        // it the store still held two nullary forms: `tgtA` stayed `Term.Ident` while
        // `tgtA()` canonicalized to `Term.Ref`, so `rule ab(1) :- tgtA()` answered 0
        // against `rule tgtA :- …`. `Term.Ident` now means exactly one thing here — a
        // name nothing in scope answers.
        //
        // A bare constructor is its INSTANCE here, in a data slot and a logical position
        // alike (§4.4, §8.3). A name in a type position never reaches this arm: the parser
        // lowers it to `Term.Ref` (`typeExprToRef`), whose arm reads it as the type.
        if kb.symbols.isResolved(kbSym) then kb.alloc(Term.Ref(kbSym))
        else kb.alloc(Term.Ident(kbSym))
      case Term.Bottom => kb.alloc(Term.Bottom)

  /** THE rung order a WRITTEN name resolves in, and the one place it is spelled.
    *
    * Short names resolve in scope. JRV1T: a dotted name resolves its first segment
    * in that same scope, then reads each member below an enclosing-link boundary.
    * This keeps imported aliases and lexical shadowing on the path's head, while
    * preventing a missing member from being supplied by the owner's container.
    * A contested segment ends the path rather than falling back to a root lookup.
    *
    * AN ABSOLUTE PATH (`..a.b.c`) HAS ONE RUNG AND NO SCOPE: the symbol whose own
    * qualified name is `a.b.c`, or nothing (§8.6). Asked ahead of the dot test because
    * `..top` asks the same question `..top.f` does — it is the one spelling by which a
    * SHORT name reaches the qualified-name table, as an exact lookup of the name written.
    * A miss does not fall to the scope walk: that walk is what the marker opts out of. */
  private def lookupWritten(kb: KnowledgeBase, name: String, scope: kb.ScopeId): ResolveResult =
    absolutePathTarget(name) match
      case Some(path) =>
        kb.symbols.byQualifiedName.get(path).fold(ResolveResult.NotFound)(ResolveResult.Found(_))
      case None if name.contains('.') =>
        // JRV1T: the first segment is a name at the writing scope, not an
        // absolute address. A contested head ends the search; a missing member
        // must not restart it at an unrelated root namespace.
        val segments = name.split('.').toList
        segments.tail.foldLeft(kb.symbols.resolveInScope(segments.head, scope)) {
          case (ResolveResult.Found(owner), member) =>
            kb.symbols.resolveBelowImport(member, kb.symbols.scopeOf(owner))
          case (result, _) => result
        }
      case None => kb.symbols.resolveInScope(name, scope)

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
    errors: ArrayBuffer[LoadError], span: Span, allowQualifiedMiss: Boolean = false
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
        // A dotted reference must name something. Qualified heads are the one
        // exception measured in rustland: they introduce nothing but load even
        // when unresolved. Absolute misses are refused in every position.
        if absolutePathTarget(name).isDefined || (name.contains('.') && !allowQualifiedMiss) then
          errors += LoadError.UnresolvedName(name, span, kb.scopeDisplayName(scope))
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
    // Membership: a sort body remains a sort when the symbol acquires other roles.
    kb.symbols.get(kb.symbols.symbolOf(scope)).hasKind(SymbolKind.Sort)

  /** §6.3 (WI-926) — the SORT an entity written as `segments` directly inside the body of
    * `scope` IS, when it carries that sort's own name: `sort Foo … entity Foo(…) … end`
    * writes `Foo` once and defines one symbol, so there is no nested `Foo.Foo`. `None` for
    * every other entity — a variant named otherwise, a dotted name (filed at its prefix's
    * address, WI-929 item 8), an entity outside a sort body. Mirrors rustland's
    * `eponymous_sort_symbol`; asked by both passes that read an `entity`, so they cannot
    * disagree about which symbol it is. */
  private def eponymousSortSymbol(
    kb: KnowledgeBase, fileSym: SymbolTable, segments: IndexedSeq[TermSymbol], scope: kb.ScopeId
  ): Option[TermSymbol] =
    if segments.length != 1 || !isSortScope(kb, scope) then None
    else
      val owner = kb.symbols.symbolOf(scope)
      kb.symbols.get(owner) match
        case SymbolDef.Resolved(short, _, _, _) if short == fileSym.name(segments.head) => Some(owner)
        case _ => None

  // `private[load]` so `Prelude.defineIn` joins by the SAME rule (WI-990) rather than
  // re-spelling it — including the empty-prefix arm, which a bare `s"$prefix.$name"`
  // would turn into a leading dot.
  private[load] def makeQualified(prefix: String, name: String): String =
    if prefix.isEmpty then name else s"$prefix.$name"

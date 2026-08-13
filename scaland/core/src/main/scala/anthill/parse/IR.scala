package anthill.parse

import anthill.intern.{TermSymbol, SymbolTable}
import anthill.term.{Term, TermId, TermStore, VarId}
import anthill.span.Span
import scala.collection.mutable.{ArrayBuffer, HashMap}

// ── Simple term store (parse-time only, no hash-consing) ────────

/** OPEN for ONE override, [[SimpleTermStore.spanOf]] — see its doc (WI-991). Everything
  * else is `final` on purpose: [[SimpleTermStore.allocAt]] is the store's single append
  * point, which is what keeps `terms` and `spans` parallel and therefore what
  * [[SimpleTermStore.nameBearingWithoutSpan]] and
  * [[SimpleTermStore.spansEndingInWhitespace]] read. A subclass overriding an allocator
  * without calling `super` desynchronizes the two silently, and the obvious next
  * instrumenting store is an alloc counter. `open` also states the intent the compiler
  * otherwise only mentions under `-source:future` (`adhocExtensions`). */
open class SimpleTermStore:
  private val terms = ArrayBuffer.empty[Term]
  /** WI-618: the `Term.Fn` nodes the parse pipeline MINTED — infix/prefix operator
    * desugars (`?a + ?b` → `add`) and accessor builds (`?x.f` → `field_access`,
    * `?x.m(…)` → `dot_apply`) — as opposed to nodes written as a call. Provenance,
    * carried rather than re-derived from a name blocklist: a user may legitimately
    * write a functor called `add`, and only this set tells the two apart. Read by
    * the loader's rule-introduced-functor scan, which must not mint a symbol for a
    * desugar's own functor name. */
  private val minted = scala.collection.mutable.HashSet.empty[TermId]
  /** WI-1009: which nodes are PARSE-TIME MARKERS, and which marker each one is — the
    * expression and pattern forms scaland has no translation for (see [[ExprMarker]]).
    *
    * The same provenance argument as `minted` one field up, for a sharper reason: four
    * marker spellings are ALSO reflect entity names, so a loader that recognized markers
    * by spelling would refuse a user's legitimate `lambda_expr(?x)` — and a loader that
    * did not recognize them at all let the marker capture that entity's symbol, which is
    * the defect WI-1009 names. Carried, so neither can happen.
    *
    * SPARSE, hence a `HashMap` and not a parallel buffer: markers are a handful of nodes
    * per file where `spans` below is total. */
  private val markers = HashMap.empty[TermId, ExprMarker]
  /** WI-957: the source text each term was built from, parallel to `terms`.
    *
    * A parse-time term is the ONE IR shape with no node of its own to carry a span
    * — the loader is handed a bare `TermId` and lifts a NAME out of it
    * ([[anthill.load.Loader.reallocTerm]]), so a diagnostic about that name had
    * nowhere to point. This is what WI-947 could not reach, and why
    * `AmbiguousSymbol` was the last locationless load error in the tree.
    *
    * PARALLEL BUFFER, not a `HashMap` like `descriptions`: [[allocAt]] is the single
    * append point (`alloc` delegates to it), so an entry exists for every id BY
    * CONSTRUCTION — a key that can be missing is a key that can drift, and the reader
    * would then have to invent a default indistinguishable from a real [[Span.empty]].
    * `descriptions` is genuinely sparse — only the `{< … >}` doc-comment production
    * writes it — where this is total, so the array is also the cheaper store.
    *
    * [[Span.empty]] is the CLAIM the allocation site makes: "no source text stands
    * behind this node". It is NOT a placeholder for a position nobody captured.
    *
    * A name-bearing term cannot make that claim by accident — [[alloc]] does not
    * accept one, and its doc carries the argument for why the exception set is empty.
    * A structural lowering with no token of its own (a `TypeExtractor.*` chain) takes
    * a DERIVED span — see `AnthillParser.typeExprToRef`. Derived is honest; empty is
    * what is forbidden, and [[nameBearingWithoutSpan]] is the audit for it. */
  private val spans = ArrayBuffer.empty[Span]
  val descriptions: HashMap[TermId, ArrayBuffer[String]] = HashMap.empty

  /** Allocate a term with NO NAME to resolve — a `Const`, a `Var`, `Bottom`.
    *
    * NAMELESS IS NOT THE SAME AS SPANLESS (WI-989). This is the entry point for a node
    * that stands behind NO SOURCE TEXT, and the parser is down to one such node: the
    * `Bottom` a valueless meta entry carries, where the absent value is the point. A
    * written `?var` or literal is nameless and this looks like its entry point, which is
    * how they went spanless for years — and their spans turned out to be load-bearing,
    * because [[nameBearingWithoutSpan]]'s derived-span readers read them. Ask whether the
    * node HAS source text, not whether it has a name.
    *
    * THE SIGNATURE IS THE ENFORCEMENT (WI-961). `Loader.reallocTerm` resolves the
    * functor / symbol of every `Fn` / `Ref` / `Ident` it walks, so one of those
    * arriving without a span is precisely the WI-947/957 defect: a diagnostic about
    * that name renders with no position. Before this, `alloc` and [[allocAt]] were
    * equally reachable and equally neutral-looking, so the next production to mint a
    * resolvable functor would compile clean, pass every test, and silently reopen the
    * bug. [[anthill.term.Term.Nameless]] makes that a TYPE error instead — the repo
    * prefers an unrepresentable illegal state over a check, and a check here would
    * only have fired in whatever test happened to exercise the new production.
    *
    * THERE IS NO EXEMPTION LIST, and there cannot be a useful one. An earlier attempt
    * enumerated the "synthesized markers that never resolve" and was wrong on its own
    * examples — `unify`, `ho_apply`, `ListLiteral`, `SetLiteral` and `TupleLiteral`
    * all DO reach `resolveName` (measured, WI-957) — and could never have been
    * complete anyway, because a pattern binder puts an arbitrary user identifier in
    * the same position. Locating everything leaves nothing to keep in sync.
    *
    * A name-bearing term genuinely built from no source — a hand-assembled test
    * fixture — says so at the site: `allocAt(term, Span.empty)`. */
  final def alloc(term: Term.Nameless): TermId = allocAt(term, Span.empty)

  /** Allocate a term built from the source text at `span` (WI-957). Use this wherever
    * the term's own functor / ref / ident symbol comes from written text: that symbol
    * is what the loader resolves, so `span` is where a name error about it belongs.
    * THE single append point — keep it that way. */
  final def allocAt(term: Term, span: Span): TermId =
    val id = TermId.fromRaw(terms.length)
    terms += term
    spans += span
    id

  /** Allocate and mark as parse-minted, in one step — the two must not drift apart.
    *
    * There is no spanless `allocMinted` twin: everything the parse pipeline MINTS is a
    * `Term.Fn` (an operator desugar, an accessor build), so such a twin could only be
    * called with a name-bearing term and [[alloc]] no longer accepts one. The span is
    * the token the desugar came FROM — `?a + ?b` mints `add(?a, ?b)`, whose functor is
    * written nowhere, so it rides at the `+`. */
  final def allocMintedAt(term: Term, span: Span): TermId =
    val id = allocAt(term, span)
    minted += id
    id

  /** Allocate a PARSE-TIME MARKER (WI-1009) — a marker is minted by definition, so this
    * records both provenances in one step, as [[allocMintedAt]] does for its one.
    *
    * THE RESIDUAL, said out loud: this store holds no symbol table, so it cannot check
    * that `term`'s functor is `marker.functorName` — and that pairing is the whole point.
    * It is enforced one level up instead, at `AnthillParser.markerFn`, which derives the
    * functor FROM the marker and is this method's only caller. Closing it here would mean
    * taking an `intern` function as a parameter and threading it through twelve
    * productions, which trades a one-site convention for a twelve-site one. */
  final def allocMarkerAt(marker: ExprMarker, term: Term.Fn, span: Span): TermId =
    val id = allocMintedAt(term, span)
    markers(id) = marker
    id

  def isMinted(id: TermId): Boolean = minted.contains(id)

  /** Which parse-time marker `id` is, or `None` for an ordinary term (WI-1009). THE
    * question `Loader.reallocTerm` asks before it resolves a functor by name. */
  def markerOf(id: TermId): Option[ExprMarker] = markers.get(id)

  /** The source span of `id` — [[Span.empty]] for a synthesized node (WI-957).
    *
    * OVERRIDABLE ON PURPOSE, and the ONLY override this class admits (WI-991). How the
    * type lowerings DERIVE a span is observable only as WORK — see
    * `AnthillParser.parseInto`, which owns that argument and the seam that follows from
    * it. WI-964 counted the reads with a counter HERE instead, summed over the store's
    * whole life; a count is now taken per PARSE, by a subclass, in the test tree. */
  def spanOf(id: TermId): Span =
    spans(id.index)

  /** WI-961: the name-bearing terms in this store that carry NO location.
    *
    * The audit `alloc`'s refusal cannot perform. That refusal catches the slip of
    * calling the spanless entry point; it cannot catch a span that was supplied but came
    * out EMPTY — which a DERIVED span can do, because a builder that takes its position
    * from its children has no answer when no child has one.
    *
    * WI-989 closed both ways that could happen — an enclosing-span fallback in the
    * derivers, and located `?var`/literal leaves for them to read (see
    * `AnthillParser.firstLocated`). THIS AUDIT STAYS, because neither repair is a TYPE:
    * a new builder is free to derive a span from nothing again, and it would fail here
    * rather than at a diagnostic.
    *
    * EMPTY for every parser-built store, pinned over the whole stdlib AND over a grammar
    * tour by `ParseSpanCoverageTest` — the tour is the half that matters, since the
    * stdlib exercises no type lowering at all. A HAND-BUILT store is expected to be
    * non-empty — the fixture declared `Span.empty` on purpose — which is why this
    * reports rather than throws: only the caller knows which kind of store it holds. */
  def nameBearingWithoutSpan: IndexedSeq[TermId] =
    (0 until terms.length).view
      .map(TermId.fromRaw)
      .filter(id => !spans(id.index).hasLocation)
      .filter(id => terms(id.index) match
        case _: Term.Fn | _: Term.Ref | _: Term.Ident => true
        case _                                        => false)
      .toIndexedSeq

  /** WI-971: the located terms in this store whose span ENDS on whitespace, paired with
    * the text each brackets — every one is a span that ran past its own construct.
    *
    * The audit the [[AnthillParserImpl.Index]] shadow cannot perform. That shadow bans a
    * SPELLING (`Index ~ p ~~ Index`); this checks a PROPERTY, so it is blind to how the
    * offsets were obtained. WI-970's eighth defect is why the difference matters: it
    * came from fastparse's `flatMap` running the whitespace skipper before a `Pass`
    * continuation, mentioned no `Index`, and survived three greps — but it would have
    * failed this on the first stdlib file, because the span it produced ended in the
    * newline before the next declaration.
    *
    * A ZERO-WIDTH span passes: `Span.empty` and the deliberate point diagnostics
    * (`Span`'s doc lists them) bracket no text, so they have no last character to be
    * wrong about. `source` is the text the store was built from — a hand-built store has
    * none, which is why this takes it rather than holding it. */
  def spansEndingInWhitespace(source: String): IndexedSeq[(TermId, String)] =
    (0 until terms.length).view
      .map(TermId.fromRaw)
      .map(id => (id, spans(id.index)))
      .filter((_, sp) => sp.hasLocation && sp.end > sp.start && sp.end <= source.length)
      .filter((_, sp) => source.charAt(sp.end - 1).isWhitespace)
      .map((id, sp) => (id, source.slice(sp.start, sp.end)))
      .toIndexedSeq

  def get(id: TermId): Term = terms(id.index)
  def size: Int = terms.length
  def isEmpty: Boolean = terms.isEmpty

// ── ParsedFile (root) ─────────────────────────────────────────

case class ParsedFile(
  items: ArrayBuffer[Item],
  symbols: SymbolTable,
  terms: SimpleTermStore
)

// ── Name ─────────────────────────────────────────────────────

case class Name(segments: IndexedSeq[TermSymbol], span: Span):
  def last: TermSymbol = segments.last
  def isSimple: Boolean = segments.length == 1

object Name:
  def simple(sym: TermSymbol, span: Span): Name = Name(IndexedSeq(sym), span)

// ── TypeExpr ────────────────────────────────────────────────────

enum TypeExpr:
  case Simple(name: Name)
  case Parameterized(name: Name, bindings: IndexedSeq[SortBinding])
  case Variable(termId: TermId, descriptions: IndexedSeq[String])
  case TupleType(fields: IndexedSeq[(TermSymbol, TypeExpr)])
  /** Arrow type: `(A) -> B`, `(A, B) -> C @ E`, or `(A) -> B @ {E1, E2}`.
    * Its parameter surface is parsed by the same parenthesized type-list production
    * as `TupleType` (WI-777 / rust WI-766); names are intentionally discarded because
    * scaland has no dependent typer, preserving the existing IR contract.
    * Empty `effects` means no `@` annotation — the braced surface form
    * may itself be empty (`@ {}`), so emptiness also denotes an explicitly closed
    * pure row. Mirrors `rustland` `TypeExpr::Arrow`. */
  case Arrow(params: IndexedSeq[TypeExpr], returnType: TypeExpr, effects: IndexedSeq[TypeExpr])
  /** WI-302: a literal value standing in a type-argument slot — value-in-type,
    * e.g. `Vector[Int64, 3]` / `Fin[n = 8]`. The loader/typer (rust-only)
    * classifies it; scaland lowers it to the raw literal term. Mirrors
    * rustland's `TypeExpr::Denoted`. */
  case Denoted(value: TermId)
  /** WI-375: a written effect-row in a type-argument value slot, e.g.
    * `Stream[E = {}]` / `Stream[E = {Modify[c]}]`. A distinct node (not a set
    * literal) per rustland's named-`effect_row` decision — `{X}` is a
    * one-effect row, not the type `X`. Mirrors rustland's `TypeExpr::EffectRow`. */
  case EffectRow(effects: IndexedSeq[TypeExpr])
  /** WI-478 (proposal 048): a guarded effect-row element `E :- guard` — present
    * iff its guard is not refuted (discharge is rust-only / WI-067; scaland just
    * parses + lowers it). `label` is the guarded effect (the `_simple_effect`);
    * `guard` is the guard's Horn body — a conjunction of goal terms (a bare
    * `E :- p` stores `[p]`, a paren `( E :- p, q )` stores `[p, q]`). Only
    * meaningful in an effect-clause / effect-row position. Mirrors rustland's
    * `TypeExpr::EffectGuarded`. */
  case EffectGuarded(label: TypeExpr, guard: IndexedSeq[TermId])

case class SortBinding(param: Option[Name], bound: TypeExpr)

// ── Literal (parse-time) ────────────────────────────────────────

enum ParseLiteral:
  case StringLit(value: String)
  case IntLit(value: Long)
  case FloatLit(value: Double)
  case BoolLit(value: Boolean)

// ── Visibility ──────────────────────────────────────────────────

enum Visibility:
  case Internal, Public

// ── Items ───────────────────────────────────────────────────────

enum Item:
  case NamespaceItem(ns: Namespace)
  case AbstractSortItem(sort: AbstractSort)
  case SortWithBodyItem(sort: SortWithBody)
  case RuleItem(rule: Rule)
  case OperationItem(op: Operation)
  case ConstItem(c: Const)
  case RequiresDeclItem(req: RequiresDecl)
  case EntityItem(entity: Entity)
  case FactItem(fact: Fact)
  case ConstraintItem(c: Constraint)
  case OperationBlockItem(block: OperationBlock)
  case RuleBlockItem(block: RuleBlock)
  case DescribeItem(desc: Describe)
  case ProjectItem(proj: Project)
  case ToolItem(tool: Tool)
  case WorkItemItem(wi: WorkItem)
  case FeedbackItem(fb: Feedback)
  case ImportToolsItem(it: ImportTools)
  case ProofItem(proof: ProofDecl)
  case ProvidesClauseItem(pc: ProvidesClause)
  case ProvidesBlockItem(pb: ProvidesBlock)
  // WI-853: a file's TOP LEVEL admits an `import`, as a namespace / sort body
  // already did. The top level is a scope — the `_global` one every top-level
  // `sort` / `fact` / `rule` is defined in — and an import is how names enter a
  // scope. Rides as its own `Item` (rather than a file-level `imports` list)
  // because scaland's `declaration` yields one `Item` per production.
  case ImportItem(imp: Import)

// ── Namespace ───────────────────────────────────────────────────

case class Namespace(
  name: Name,
  imports: IndexedSeq[Import],
  items: IndexedSeq[Item],
  span: Span
)

case class Import(path: Name, kind: ImportKind)

enum ImportKind:
  case Plain
  case Selective(names: IndexedSeq[Name])
  case Wildcard

// ── Sort ────────────────────────────────────────────────────────

case class AbstractSort(
  visibility: Option[Visibility],
  name: Name,
  definition: TypeExpr,
  descriptions: IndexedSeq[String],
  meta: Option[MetaBlock],
  span: Span,
  /** WI-1062: set when this abstract sort came from `effects E = ?` rather than
    * `sort E = ?` — the parameter holds an effect ROW, not a type.
    *
    * The two desugar to the same declaration ON PURPOSE (`effectsSortItem`),
    * because the `requires EffectsRuntime` anchor that would distinguish them is
    * inert without a typer. This flag is the provenance the desugar was otherwise
    * throwing away: it says WHICH surface form was written, and nothing about what
    * the declaration means. The loader ignores it — a backend that erases effects
    * (`scala_std`, §2.8a) reads it to know which of a sort's own parameters it
    * must drop. Same shape as [[SortWithBody.isTypeParam]], for the same reason:
    * an `Item` kind of its own would have to be spelled "identical to
    * `AbstractSortItem`" at every exhaustive match over `Item`.
    *
    * THE TWO IMPLEMENTATIONS MARK THIS DIFFERENTLY and nothing cross-checks them.
    * rustland's marker is SEMANTIC — `convert_effects_sort_item` emits the
    * `requires anthill.prelude.EffectsRuntime[Effects = E]` anchor alongside the
    * abstract sort — where scaland drops the anchor and carries this flag. Neither
    * can be derived from the other by reading one tree.
    *
    * NO DEFAULT, deliberately: a future desugar that mints an effect parameter
    * would silently get `false` and its sort would emit a parameter that should
    * have been erased. Spelled at all three construction sites instead. */
  isEffectRow: Boolean
)

/** Sort or enum declaration kind. Enums are sorts whose subterms are
  * understood as a closed disjoint sum of constructors (proposal 025). */
enum SortDeclKind:
  case Sort, Enum

case class SortWithBody(
  visibility: Option[Visibility],
  name: Name,
  descriptions: IndexedSeq[String],
  imports: IndexedSeq[Import],
  items: IndexedSeq[Item],
  meta: Option[MetaBlock],
  span: Span,
  kind: SortDeclKind = SortDeclKind.Sort,
  /** WI-451 (§5.4): set when this `SortWithBody` is the higher-kinded carrier of
    * an enclosing sort type-param (`F` in `sort Spec[F[T]]`, or the structured
    * binder `sort [F] { sort [T] }`) — a NON-RIGID type variable, not a concrete
    * nested sort. The loader reads this to register the carrier as a type param
    * of the enclosing sort (mirrors the `sort T = ?` abstract-sort arm). An
    * UNMARKED `sort F { … }` stays a concrete nested sort. */
  isTypeParam: Boolean = false
)

case class FieldDecl(name: TermSymbol, ty: TypeExpr)

// ── Rule ────────────────────────────────────────────────────────

case class Rule(
  label: Option[Name],
  /** One or more positive heads, or a single `RuleHead.Bottom` for denial.
    * Mixing `Bottom` with positive heads is rejected at load time.
    * Multi-head desugars conjunctively (proposal 032).
    */
  heads: IndexedSeq[RuleHead],
  body: Option[IndexedSeq[TermId]],
  meta: Option[MetaBlock],
  span: Span
)

enum RuleHead:
  case TermHead(termId: TermId)
  case Bottom

// ── Operation ───────────────────────────────────────────────────

case class Operation(
  visibility: Option[Visibility],
  name: Name,
  typeParams: IndexedSeq[TypeParam],
  params: IndexedSeq[Param],
  returnType: TypeExpr,
  requires: IndexedSeq[IndexedSeq[TermId]],
  ensures: IndexedSeq[IndexedSeq[TermId]],
  effects: IndexedSeq[Effect],
  body: Option[TermId],
  meta: Option[MetaBlock],
  span: Span
)

/** An operation parameter. `rest` is WI-727 (proposal 056): `true` for a
  * VARIADIC CAPTURE parameter — one written `...name: R`, which collects every
  * named argument not matched to a declared parameter into a single named-tuple
  * record. At most one, and trailing; enforced in the loader (which knows the
  * qualified operation name the diagnostic quotes), as rustland does — and WI-947
  * added `span` so that refusal can also point AT the offending parameter, which is
  * the driving case for giving `LoadError.Other` a location at all. */
case class Param(name: TermSymbol, ty: TypeExpr, rest: Boolean, span: Span)

/** Operation-local type parameter (WI-269): `[T]`.
  * Mirrors rustland's `TypeParam`. These declare operation-local logical
  * variables, distinct from sort-parameter bindings at an instantiation
  * site.
  *
  * WI-850: there is no `default` field. A written `[T = Int64]` still PARSES —
  * so the refusal can name the operation and the parameter instead of failing as
  * an unexpected `=` — and is then refused, never stored. The kernel spec's
  * production is `TypeParam ::= Name` (§5.4), and a stored default had no reader:
  * the loader mints a fresh var per parameter from its NAME alone.
  *
  * WI-840 (proposal 058 §4.7): `requirementSlot` is `Some(k)` when the parameter was
  * declared as a NAMED requirement slot in the operation's `requires` clause list
  * (`requires plus: Monoid[T]`) rather than in its `[…]` bracket; `k` is the slot's
  * position among the operation's requirement GOALS in source order. A POSITION and
  * not the spec, because a slot's identity is positional and the spec would not
  * discriminate the motivating case: the two slots of
  * `requires plus: Monoid[T], times: Monoid[T]` are the same type. */
case class TypeParam(
  name: TermSymbol,
  span: Span,
  requirementSlot: Option[Int] = None
)

// ── Const (proposal 039 / WI-084) ───────────────────────────────

/** A term-level named constant: `const NAME: T [= EXPR]`. Monomorphic and
  * carrier-independent by design — no params, type-params, or effects. The
  * declared type `ty` is MANDATORY (part of the name's contract); the `value`
  * body is OPTIONAL — absent for a host-supplied constant (e.g. float `infinity`
  * / `nan`). Mirrors rustland's `Const`. */
case class Const(
  visibility: Option[Visibility],
  name: Name,
  ty: TypeExpr,
  value: Option[TermId],
  meta: Option[MetaBlock],
  span: Span
)

// ── Requires declaration ────────────────────────────────────────

/** A `requires` declaration at sort / namespace level.
  *
  * WI-840 (proposal 058 §4.7): `binder` is the NAMED slot's name — `Some(O)` for
  * `requires O: Ord[T]`, `None` for the anonymous `requires Ord[T]`. A NAMED slot is
  * a type PARAMETER of the enclosing sort (which is how a chosen witness enters a
  * type, `SortedSet[T = String, O = ByLength]`); an ANONYMOUS one is a constraint —
  * solved, not recorded. rustland desugars the named form into `sort O = ?` + the
  * requirement at CONVERT time; scaland has no such fan-out in `declaration`
  * (`P[Item]`, one item per production), so the binder rides here and the loader's
  * `DefinePass` registers the type parameter directly — same effect, one production
  * earlier. */
case class RequiresDecl(binder: Option[Name], typeExpr: TypeExpr, span: Span)

// ── Sugar ───────────────────────────────────────────────────────

case class Entity(
  visibility: Option[Visibility],
  name: Name,
  fields: IndexedSeq[FieldDecl],
  meta: Option[MetaBlock],
  span: Span
)

case class Fact(term: TermId, meta: Option[MetaBlock], span: Span)

case class Constraint(
  label: Option[Name],
  head: IndexedSeq[TermId],
  guard: Option[IndexedSeq[TermId]],
  meta: Option[MetaBlock],
  span: Span
)

case class OperationBlock(entries: IndexedSeq[Operation], span: Span)

case class RuleBlock(entries: IndexedSeq[Rule], span: Span)

case class Describe(target: Name, contents: IndexedSeq[String], span: Span)

// ── Common ──────────────────────────────────────────────────────

case class Effect(typeExpr: TypeExpr)

case class MetaBlock(entries: IndexedSeq[MetaEntry])

case class MetaEntry(key: Name, value: TermId)

// ── Stage 0 ─────────────────────────────────────────────────────

case class Project(
  name: Name,
  structure: ProjectStructure,
  importTools: IndexedSeq[ImportTools],
  tools: IndexedSeq[Name],
  domains: IndexedSeq[Name],
  meta: Option[MetaBlock],
  span: Span
)

enum ProjectStructure:
  case Simple(fields: SimpleProjectFields)
  case Modules(modules: IndexedSeq[ModuleDecl])
  case ToolsOnly

case class SimpleProjectFields(
  language: String,
  build: Option[String],
  sources: IndexedSeq[SourceRoot]
)

case class ModuleDecl(
  name: Name,
  root: String,
  language: String,
  build: Option[String],
  sources: IndexedSeq[SourceRoot],
  meta: Option[MetaBlock],
  span: Span
)

case class SourceRoot(path: String, language: Option[String], scope: SourceScope)

enum SourceScope:
  case Main, Test, Generated, Docs

case class ImportTools(names: IndexedSeq[Name], span: Span)

case class Tool(
  name: Name,
  command: String,
  args: IndexedSeq[String],
  workingDir: Option[String],
  timeout: Option[String],
  success: SuccessCriterion,
  meta: Option[MetaBlock],
  span: Span
)

enum SuccessCriterion:
  case ExitZero
  case ExitCode(code: Long)
  case OutputMatches(pattern: String)
  case Custom(termId: TermId)

case class WorkItem(
  id: Name,
  description: Option[TermId],
  context: IndexedSeq[ContextRef],
  acceptance: IndexedSeq[AcceptanceCriterion],
  dependsOn: IndexedSeq[Name],
  generates: IndexedSeq[TermId],
  requiresCapability: IndexedSeq[Capability],
  status: WorkStatus,
  meta: Option[MetaBlock],
  span: Span
)

enum ContextRef:
  case FileRef(path: String, lines: Option[(Long, Long)])
  case FactRef(name: Name, term: TermId)
  case WorkItemRef(name: Name)

enum AcceptanceCriterion:
  case ToolPasses(tool: Name, bindings: Option[IndexedSeq[(String, TermId)]])
  case FactHolds(name: Name, term: TermId)
  case Compiles(target: CompileTarget)
  case ConstraintCrit(termId: TermId)

enum CompileTarget:
  case SourceRootTarget(root: SourceRoot)
  case ModuleTarget(name: Name)

enum Capability:
  case Code(languages: IndexedSeq[String])
  case Test, Refine, Review, Decompose, Architect, HumanJudgment

enum WorkStatus:
  case Draft, Open
  case Claimed(agent: String, since: String)
  case Delivered(agent: String, at: String)
  case Verified(at: String)
  case Rejected(reason: String, at: String)
  case ProposalRejected(reason: String, at: String)
  case Stale(reason: String, since: String)

case class Feedback(
  workitem: Name,
  author: String,
  content: TermId,
  at: String,
  meta: Option[MetaBlock],
  span: Span
)

// ── Proof construct (proposal 025 / 031) ────────────────────────

/** A `proof <target> ... end` declaration. The `body` field carries the
  * single-tactic hints, an explicit query, or a structured body of
  * inner step rules + concluding clause (proposal 031). Witness
  * checking and discharge are deferred (WI-157). */
case class ProofDecl(
  target: Name,
  strategy: Option[ProofStrategy],
  body: Option[ProofBody],
  usingNames: IndexedSeq[Name],
  span: Span
)

/** `by <name>(arg, k: v, ...)`. Args are stored as parse-side terms;
  * the typed Tactic IR (proposal 025.1 phase 2) is not yet ported. */
case class ProofStrategy(
  name: TermSymbol,
  args: IndexedSeq[TermId],
  span: Span
)

enum ProofBody:
  /** `:- hint1, hint2` — guided-derivation hints. */
  case Hints(hints: IndexedSeq[TermId])
  /** `query "..."` (+ optional mapping). */
  case Query(text: String, mapping: Option[MappingBlock])
  /** Structured body: a sequence of inner step rules each with its own
    * `by <tactic>` discharge, plus an optional concluding clause that
    * discharges the enclosing target under accumulated step hypotheses. */
  case Structured(steps: IndexedSeq[ProofStep], conclude: Option[ConcludeClause])

case class ProofStep(
  rule: Rule,
  usingNames: IndexedSeq[Name],
  strategy: ProofStrategy,
  span: Span
)

case class ConcludeClause(
  usingNames: IndexedSeq[Name],
  strategy: ProofStrategy,
  span: Span
)

case class MappingBlock(entries: IndexedSeq[MappingEntry])
case class MappingEntry(source: Name, target: String)

// ── Provides construct (proposal 025) ────────────────────────────

/** `provides Spec[T = X]` inside a sort/enum body — declares the
  * enclosing sort satisfies the spec.
  *
  * WI-869 (058 §3.8): `conditions` is the `:- goals` tail, scoping the provision's
  * conditions to THAT provision instead of to the whole sort. Empty for the
  * unconditioned form. */
case class ProvidesClause(
  spec: TypeExpr,
  conditions: IndexedSeq[TypeExpr],
  span: Span
)

/** Standalone `provides Spec language <lang> ... end` block. */
case class ProvidesBlock(
  spec: TypeExpr,
  language: TermSymbol,
  items: IndexedSeq[ProvidesItem],
  span: Span
)

enum ProvidesItem:
  case RuleI(rule: Rule)
  case RuleBlockI(block: RuleBlock)
  case FactI(fact: Fact)
  case ProofI(proof: ProofDecl)
  case ArtifactI(path: String)
  case CarrierI(bindings: IndexedSeq[CarrierBinding])
  case NamespaceMapI(entries: IndexedSeq[NamespaceMapEntry])
  // WI-876: `operation_map { compare: "ordered_compare" }` — which host FUNCTION
  // realizes one of the carrier's operations. The operation-level peer of
  // `CarrierI`, which says which host TYPE realizes a sort.
  case OperationMapI(entries: IndexedSeq[OperationMapEntry])
  // WI-889: `const_map { infinity: "f64::INFINITY" }` — the CONST-level peer of
  // `operation_map`, saying which host EXPRESSION realizes a carrier's body-less
  // `const`. A const is not an operation, so it has no place in `operation_map`,
  // whose reader refuses a non-operation by design.
  case ConstMapI(entries: IndexedSeq[ConstMapEntry])

case class CarrierBinding(anthillParam: TermSymbol, hostType: TermId)
case class NamespaceMapEntry(anthillNamespace: TermSymbol, hostModule: TermId)
case class OperationMapEntry(operation: TermSymbol, hostFn: TermId)
case class ConstMapEntry(constName: TermSymbol, hostExpr: TermId)

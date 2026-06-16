package anthill.parse

import anthill.intern.{TermSymbol, SymbolTable}
import anthill.term.{Term, TermId, TermStore, VarId}
import anthill.span.Span
import scala.collection.mutable.{ArrayBuffer, HashMap}

// ── Simple term store (parse-time only, no hash-consing) ────────

class SimpleTermStore:
  private val terms = ArrayBuffer.empty[Term]
  val descriptions: HashMap[TermId, ArrayBuffer[String]] = HashMap.empty

  def alloc(term: Term): TermId =
    val id = TermId.fromRaw(terms.length)
    terms += term
    id

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
    * Empty `effects` means no `@` annotation — the braced surface form
    * requires at least one element (`commaSep1`), so emptiness can only
    * come from a missing annotation. Mirrors `rustland` `TypeExpr::Arrow`. */
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
  span: Span
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
  kind: SortDeclKind = SortDeclKind.Sort
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

case class Param(name: TermSymbol, ty: TypeExpr)

/** Operation-local type parameter (WI-269): `[T]` or `[T = Default]`.
  * Mirrors rustland's `TypeParam`. These declare operation-local logical
  * variables, distinct from sort-parameter bindings at an instantiation
  * site. `default` carries the optional `= Type` right-hand side. */
case class TypeParam(name: TermSymbol, default: Option[TypeExpr], span: Span)

// ── Requires declaration ────────────────────────────────────────

case class RequiresDecl(typeExpr: TypeExpr, span: Span)

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
  * enclosing sort satisfies the spec. */
case class ProvidesClause(spec: TypeExpr, span: Span)

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

case class CarrierBinding(anthillParam: TermSymbol, hostType: TermId)
case class NamespaceMapEntry(anthillNamespace: TermSymbol, hostModule: TermId)

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
  case Arrow(params: IndexedSeq[TypeExpr], returnType: TypeExpr, effect: Option[TypeExpr])

case class SortBinding(param: Option[Name], bound: TypeExpr)

// ── Literal (parse-time) ────────────────────────────────────────

enum ParseLiteral:
  case StringLit(value: String)
  case IntLit(value: Long)
  case FloatLit(value: Double)
  case BoolLit(value: Boolean)

// ── Visibility ──────────────────────────────────────────────────

enum Visibility:
  case Internal, Export, Public

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

// ── Namespace ───────────────────────────────────────────────────

case class Namespace(
  name: Name,
  imports: IndexedSeq[Import],
  exports: IndexedSeq[Name],
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

case class SortWithBody(
  visibility: Option[Visibility],
  name: Name,
  descriptions: IndexedSeq[String],
  imports: IndexedSeq[Import],
  exports: IndexedSeq[Name],
  items: IndexedSeq[Item],
  meta: Option[MetaBlock],
  span: Span
)

case class FieldDecl(name: TermSymbol, ty: TypeExpr)

// ── Rule ────────────────────────────────────────────────────────

case class Rule(
  label: Option[Name],
  head: RuleHead,
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

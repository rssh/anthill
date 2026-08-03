package anthill.parse

import anthill.intern.{TermSymbol, SymbolTable}
import anthill.term.{Term, TermId, TermStore, VarId}
import anthill.span.Span
import scala.collection.mutable.{ArrayBuffer, HashMap}

// ── Simple term store (parse-time only, no hash-consing) ────────

class SimpleTermStore:
  private val terms = ArrayBuffer.empty[Term]
  /** WI-618: the `Term.Fn` nodes the parse pipeline MINTED — infix/prefix operator
    * desugars (`?a + ?b` → `add`) and accessor builds (`?x.f` → `field_access`,
    * `?x.m(…)` → `dot_apply`) — as opposed to nodes written as a call. Provenance,
    * carried rather than re-derived from a name blocklist: a user may legitimately
    * write a functor called `add`, and only this set tells the two apart. Read by
    * the loader's rule-introduced-functor scan, which must not mint a symbol for a
    * desugar's own functor name. */
  private val minted = scala.collection.mutable.HashSet.empty[TermId]
  val descriptions: HashMap[TermId, ArrayBuffer[String]] = HashMap.empty

  def alloc(term: Term): TermId =
    val id = TermId.fromRaw(terms.length)
    terms += term
    id

  /** Allocate and mark as parse-minted, in one step — the two must not drift apart. */
  def allocMinted(term: Term): TermId =
    val id = alloc(term)
    minted += id
    id

  def isMinted(id: TermId): Boolean = minted.contains(id)

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

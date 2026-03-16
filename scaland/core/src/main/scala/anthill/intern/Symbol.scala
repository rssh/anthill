package anthill.intern

// ── Symbol handle ───────────────────────────────────────────────

opaque type TermSymbol = Int

object TermSymbol:
  def fromRaw(raw: Int): TermSymbol = raw

  extension (s: TermSymbol)
    def raw: Int = s

// ── Symbol metadata ─────────────────────────────────────────────

enum SymbolKind:
  case Sort, Entity, Operation, Namespace, Fact, Rule, Constraint, Param, Field, Goal

enum SymbolDef:
  case Unresolved(name: String)
  case Resolved(shortName: String, qualifiedName: String, kind: SymbolKind, scopeRaw: Int)

// ── Scope ───────────────────────────────────────────────────────

case class ScopeInclusion(
  parentScopeRaw: Int,
  instantiationTermRaw: Int,
  isEnclosing: Boolean
)

enum ResolveResult:
  case Found(sym: TermSymbol)
  case Ambiguous(candidates: Vector[TermSymbol])
  case NotFound

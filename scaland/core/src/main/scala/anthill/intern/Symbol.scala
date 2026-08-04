package anthill.intern

// ── Symbol handle ───────────────────────────────────────────────

opaque type TermSymbol = Int

object TermSymbol:
  def fromRaw(raw: Int): TermSymbol = raw

  extension (s: TermSymbol)
    def raw: Int = s

// ── Symbol metadata ─────────────────────────────────────────────

enum SymbolKind:
  // WI-898: `Goal` and `EquationFunctor` are both RULE-INTRODUCED — a functor no
  // declaration names, brought into being by a rule head. They are distinct because
  // the two introductions are: a PREDICATE head introduces a relation (`Goal`), an
  // equational head introduces a function symbol its equations define
  // (`EquationFunctor`) — and an equation-introduced functor is not a relation.
  //
  // `EquationFunctor` has NO reader in scaland yet, deliberately: rustland's readers
  // are its typer (`UnreducedEquationFunctor`) and the simp machinery, neither of
  // which scaland has. It is recorded now so the two loaders agree on what a rule
  // introduced — recovering it later would mean re-walking every rule head.
  case Sort, Entity, Operation, Const, Namespace, Fact, Rule, Constraint, Param, Field,
       Goal, EquationFunctor

enum SymbolDef:
  case Unresolved(name: String)
  case Resolved(shortName: String, qualifiedName: String, kind: SymbolKind, scope: ScopeId)

// ── Scope ───────────────────────────────────────────────────────

/** A parent link in the scope graph (WI-976: `parent` is a [[ScopeId]], not the raw
  * `Int` a caller had to promise was one).
  *
  * The record used to carry a third field, `instantiationTermRaw: Int` — a raw term id,
  * written by every producer and read by NONE, here and in rustland alike (`kb/load.rs`
  * says so at its own writers). WI-976 dropped it rather than retype it: parity was the
  * only argument for keeping it, and this same change already moved `parent` from a
  * TermId raw to a symbol, so the two records had stopped agreeing regardless. What was
  * left was an untyped term id inside the record whose untypedness this ticket exists to
  * remove. The rustland twin is WI-984. */
case class ScopeInclusion(
  parent: ScopeId,
  isEnclosing: Boolean
)

enum ResolveResult:
  case Found(sym: TermSymbol)
  case Ambiguous(candidates: Vector[TermSymbol])
  case NotFound

  /** Does this answer denote ANYTHING — a unique symbol or a contested set? Asked by
    * the positions that need the verdict and not the symbol, notably the rule-head
    * mint guard: an AMBIGUOUS name already denotes, so minting a third meaning for it
    * would deepen the ambiguity rather than fill a hole. Mirrors rustland's
    * `ResolveResult::denotes`. */
  def denotes: Boolean = this match
    case ResolveResult.NotFound => false
    case _ => true

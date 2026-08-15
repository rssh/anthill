package anthill.intern

/** The name of the SYNTHETIC TOP-LEVEL SCOPE — the one a file's top-level declarations
  * land in, minted by [[anthill.kb.KnowledgeBase.globalScope]].
  *
  * UNSPELLABLE BY THE IDENTIFIER TOKEN (WI-987). It used to be `_global`, which both
  * grammars admit (`Tokens.identToken` here, `_identifier_token` in
  * `tree-sitter-anthill/grammar.js`) — and a scope is minted from a SYMBOL, so
  * `namespace _global` simply declared a second one: [[SymbolTable.define]] writes
  * `byQualifiedName("_global")` without consulting the intern map, and
  * `KnowledgeBase.scopeDisplayName` then rendered both scopes `_global`, so a WI-962
  * diagnostic could not say which it meant. `<` starts no identifier, so the second
  * scope is now UNREPRESENTABLE rather than merely unlikely — which is why nothing
  * checks for it. Angle brackets are also this tree's existing spelling for a name no
  * source text can write (`Parser.parse`'s `"<input>"`).
  *
  * RUSTLAND HOLDS THE SAME SPELLING, at `intern::GLOBAL_SCOPE_NAME`, where it sits
  * beside `ABSOLUTE_PATH_MARKER` — the same argument, for the same reason. The two
  * trees must agree: neither reads the other, so a one-sided change diverges their
  * diagnostics in silence.
  *
  * THE GUARANTEE IS EXACTLY AS WIDE AS THE IDENTIFIER TOKEN. `kernel-language.md` §2.3
  * also lists a QUOTED identifier (`"my weird name"`), which admits arbitrary text and
  * would readmit the collision. Neither implementation parses one today — which is why
  * this is a fact and not a hope — but whichever adds one must exclude this name from it
  * or move the sentinel out of its reach. Stated at §8.6 *The top-level scope* as well,
  * since a grammar change starts there. */
val GLOBAL_SCOPE_NAME: String = "<global>"

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

/** A symbol's metadata, PARAMETERIZED by the scope type (WI-1004).
  *
  * `Resolved.scope` used to be a top-level `ScopeId`, which is exactly why the type could
  * not say WHICH table's scope it was: `SymbolDef` lives outside [[SymbolTable]], and a
  * scope identity is now that class's own member ([[SymbolTable.ScopeId]]). The parameter
  * is how a record held outside the class still names the one table it belongs to — a
  * table's `defs` are `SymbolDef[ScopeId]`, so `st.get(sym)` hands back a scope only `st`
  * accepts. Nothing else varies over `S`; it is never instantiated at anything but some
  * table's `ScopeId`.
  *
  * COVARIANT so `Unresolved` — which has no scope to name — is a `SymbolDef` of every
  * table at once, rather than needing a cast into each table's `defs`.
  *
  * A PARAMETER and not a move inside [[SymbolTable]], unlike the other three records that
  * hold a scope (`Scope`, `ScopeInclusion`, `KnowledgeBase.RuleEntry`): this enum is
  * pattern-matched by unqualified name at ~20 sites across `kb`, `resolve`, `load` and
  * the tests, and a member enum would make every one of them
  * `kb.symbols.SymbolDef.Resolved(…)`. The parameter's price is that `scope` erases to
  * `Object` where the others are back to `int` — ~960 boxed ints per loaded stdlib, plus a
  * discarded unbox at the seven sites that destructure and ignore the field. Measured and
  * accepted: 15 KB against a load phase that allocates ~15 MB. */
enum SymbolDef[+S]:
  case Unresolved(name: String) extends SymbolDef[Nothing]
  case Resolved(shortName: String, qualifiedName: String, kind: SymbolKind, scope: S)

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

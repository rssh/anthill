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

/** The marker an ABSOLUTE path carries: `..a.b.c` names the symbol whose OWN qualified
  * name is `a.b.c`, looked up directly — the channel `import` uses — so nothing in scope
  * can shadow it. An unmarked `a.b.c` is read where it is written.
  *
  * IT RIDES ON THE HEAD SEGMENT'S TEXT (`Tokens.absoluteHeadToken` is one token), so a
  * marked path is one string wherever a name is joined — a call functor, a `Name`'s
  * segments — and one that resolves to nothing is interned and reported under the text
  * the author wrote. `Tokens.identToken` admits only `[a-zA-Z_][a-zA-Z0-9_-]*`, so no
  * identifier contains it and a marked head collides with no user symbol.
  *
  * RUSTLAND HOLDS THE SAME SPELLING AND THE SAME CARRIER, at
  * `intern::ABSOLUTE_PATH_MARKER`; its doc says why the marker is the separator doubled. */
val ABSOLUTE_PATH_MARKER: String = ".."

/** The qualified name `name` asks for ABSOLUTELY, or `None` for an ordinary name. The
  * SOLE reader of [[ABSOLUTE_PATH_MARKER]], so "is this path absolute" has one spelling
  * whoever wrote the path: `Tokens.absoluteHeadToken` for a path in source, and
  * `Pratt`'s operator addresses (`..anthill.kernel.not`), which are marked names the
  * desugar mints. Mirrors rustland's `absolute_path_target`.
  *
  * A single segment counts: `..top` asks for the top-level `top` by the rule `..top.f`
  * asks for `top.f` — an exact lookup of the name written, not a search for a short one. */
def absolutePathTarget(name: String): Option[String] =
  Option.when(name.startsWith(ABSOLUTE_PATH_MARKER))(name.substring(ABSOLUTE_PATH_MARKER.length))

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
  // WI-20260821-SBZ2A GAVE `EquationFunctor` ITS FIRST READERS HERE, and they are all
  // in the loader: proposal 061's `ruleReading` (an equation head is a CLAUSE, never a
  // declaration), 061's file rule (an equation subject owns no predicate, so it is
  // exempt) and 845G7's collision message (a body-less `rule` does not collect an
  // equation's subject — WI-898). The kind was recorded before any of them existed,
  // deliberately, so the two loaders would agree on what a rule introduced; recovering
  // it later would have meant re-walking every rule head.
  //
  // RUSTLAND'S OTHER READERS ARE STILL ABSENT: its typer
  // (`UnreducedEquationFunctor` at a VALUE citation, and since WI-20260902-8K4RB
  // `EquationSubjectInGoalPosition` at a GOAL one) and the simp machinery, neither of
  // which scaland has — the goal-position refusal in particular is raised by the
  // rule-body goal-READING pass, and scaland has no typer to run it.
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

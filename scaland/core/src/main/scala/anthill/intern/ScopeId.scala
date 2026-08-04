package anthill.intern

/** THE IDENTITY OF A SCOPE — the thing a name is resolved against.
  *
  * WI-976: scope-hood used to be UNTYPED. A scope was a bare `Int` in nine
  * [[SymbolTable]] methods, in [[SymbolDef.Resolved]] and in [[ScopeInclusion]], and a
  * bare `anthill.term.TermId` at every `KnowledgeBase` and loader entry point — so a
  * scope, an arbitrary term and an arbitrary integer were ONE type, and "this TermId is
  * a scope" was a claim every caller re-made at runtime. `KnowledgeBase.scopeFunctor`
  * re-derived scope-hood structurally and answered `None`; `scopeDisplayName` THREW on
  * that answer. Neither arm was reachable in fact — the nullary name term was the only
  * shape any producer built — which is the definition of a runtime check standing in
  * for a type.
  *
  * A SCOPE IS A SYMBOL. [[SymbolTable.scopeOf]] is the sole mint and it is total over its
  * table's symbols, so [[symbol]] is a projection, not a query: no `Option`, no term
  * store, nothing to refuse, and so nothing for a caller to re-decide.
  *
  * TOTAL OVER A TABLE'S SYMBOLS IS THE POINT, not a weakening of it. The scope graph is
  * OPEN — [[SymbolTable]] creates a scope's entry lazily, so every symbol of that table
  * is a potential scope and its KIND is nothing the mint could require. What this type
  * carries is a ROLE, not a capability: it says the value came from a symbol rather than
  * from an integer or an arbitrary term, which is the whole of what was being promised by
  * hand before. The mint's one refusal is about the OTHER question, which table (WI-990,
  * below).
  *
  * The scope's TERM form — `Term.Fn(symbol, [], [])`, what an `entity_of` fact and a
  * rule's domain carry — is recovered by `KnowledgeBase.scopeTerm`, which goes through
  * the one name-term producer (`makeNameTermFromSym`, WI-962). Scope → term is a
  * function; this type is what makes the other direction unnecessary.
  *
  * A SYMBOL MEANS SOMETHING ONLY RELATIVE TO ONE TABLE, so the mint is
  * [[SymbolTable.scopeOf]] and not a companion method here (WI-990). A `TermSymbol` is
  * an index into one [[SymbolTable]]'s `defs`, and the loader threads TWO tables side by
  * side — `kb.symbols` and the parse-time `fileSym` — through nearly every signature;
  * `ScopeId.of(imp.path.last)` used to type-check and mint a scope in the wrong universe.
  * Naming the table at the mint is what this type could not say on its own —
  * `ScopeIdentityTest` holds it, and `SymbolTable.scopeOf` says what it does not reach.
  */
opaque type ScopeId = TermSymbol

object ScopeId:
  /** The mint's implementation, `private[intern]` so [[SymbolTable.scopeOf]] is the only
    * way in from outside — see the note on tables above, and `scopeOf`'s own comment for
    * what naming the table does and does not close. */
  private[intern] def of(sym: TermSymbol): ScopeId = sym

  extension (s: ScopeId)
    /** The symbol that names this scope. Total by construction — see
      * [[SymbolTable.scopeOf]]. Named for the SYMBOL layer, not the term layer (`functor`
      * would be the word if a scope were a term, which is exactly what this type denies). */
    def symbol: TermSymbol = s

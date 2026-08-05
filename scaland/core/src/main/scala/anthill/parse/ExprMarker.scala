package anthill.parse

/** A PARSE-TIME EXPRESSION OR PATTERN MARKER: the functor the parser mints for a source
  * form that is not a call, and that the loader has no translation for (WI-1009).
  *
  * TWO LAYERS, DELIBERATELY NAMED DIFFERENTLY. The parser mints these markers; the
  * REFLECT ENTITIES they would translate INTO are a different vocabulary
  * (`stdlib/anthill/reflect/reflect.anthill` declares `var_pattern` / `wildcard` /
  * `MatchBranch` where the parser writes `pattern_var` / `pattern_wildcard` /
  * `match_branch`), and rustland's `convert_expr_term` is the translation between them.
  * Scaland's copy of that translation was ported ahead of any consumer, never acquired
  * one, and WI-1007 deleted it — so in this tree a marker has no target to become.
  *
  * FOUR SPELLINGS THE TWO LAYERS SHARE, and that is what this type exists to defuse.
  * `match_expr` / `if_expr` / `let_expr` / `lambda_expr` are BOTH a marker here and an
  * `anthill.reflect.Expr` entity ([[anthill.load.Prelude]] registers them, and
  * `reflect.anthill` declares them). `Loader.reallocTerm` resolves the functor of every
  * `Term.Fn` by NAME, so before WI-1009 a marker in a rule body was decided by a spelling
  * coincidence: where the two layers agreed the marker CAPTURED the entity symbol and the
  * KB gained an `Entity` applied positionally to a shape that entity does not declare;
  * where they did not, the marker LEAKED as an undeclared predicate with no diagnostic.
  * Measured on `rule r(?x) :- p(lambda s -> s)`, load errors EMPTY:
  * {{{
  * Fn p                                   [bare intern]
  *   Fn anthill.reflect.Expr.lambda_expr  [RESOLVED  <- the marker, captured]
  *     Fn pattern_var                     [bare intern — no entity of that spelling]
  * }}}
  *
  * SO THE ANSWER IS PROVENANCE, NOT A NAME BLOCKLIST. The marker set travels with the
  * TERM ([[SimpleTermStore.allocMarkerAt]] / [[SimpleTermStore.markerOf]]), which is the
  * same argument `SimpleTermStore.minted` already makes for operator desugars: a user may
  * legitimately write a functor called `lambda_expr` — reflect.anthill's own entity is
  * reachable by that name — and only the provenance tells the two apart. A blocklist
  * keyed on the spelling would refuse the user's `lambda_expr(?x)` and, being a second
  * copy of this list, would drift from it.
  *
  * WHAT A MARKER IS NOT, since the parser mints plenty of functors and only these ten are
  * listed. `field_access` / `dot_apply` / `ho_apply` / `unify` / the collection literals
  * are names the loader is MEANT to resolve (see `SimpleTermStore.alloc`'s WI-957 note,
  * which measured exactly that). `proof_stmt` is the near miss and belongs with THEM: the
  * `AnthillParserImpl.proofStatement` doc states its lowering — an inert term carrying the
  * continuation — so it has one, and a bare intern is how scaland already represents the
  * rest of that family (`Loader.loadProof` mints `proof_decl` the same way). A marker is a
  * form with NO lowering; that, and not "the parser made it up", is the membership test.
  *
  * `description` is how a diagnostic names the form the USER WROTE — the functor name is
  * an internal spelling and belongs in a diagnostic only as a parenthetical. */
enum ExprMarker(val functorName: String, val description: String):
  case MatchExpr extends ExprMarker("match_expr", "a `match` expression")
  case MatchBranch extends ExprMarker("match_branch", "a `case` branch")
  case IfExpr extends ExprMarker("if_expr", "an `if` expression")
  case LetExpr extends ExprMarker("let_expr", "a `let` expression")
  case LambdaExpr extends ExprMarker("lambda_expr", "a `lambda` expression")
  case PatternVar extends ExprMarker("pattern_var", "a binder pattern")
  case PatternWildcard extends ExprMarker("pattern_wildcard", "a `_` wildcard pattern")
  case PatternLiteral extends ExprMarker("pattern_literal", "a literal pattern")
  case PatternConstructor extends ExprMarker("pattern_constructor", "a constructor pattern")
  case PatternTuple extends ExprMarker("pattern_tuple", "a tuple pattern")

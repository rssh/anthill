package anthill.resolve

import anthill.kb.{KnowledgeBase, BuiltinTag}
import anthill.term.{Term, TermId, VarId, Literal}
import anthill.intern.{TermSymbol, SymbolDef, SymbolKind}
import anthill.subst.Substitution

/** Result of executing a builtin. */
enum BuiltinResult:
  case Success
  case SuccessWithBindings(extra: Substitution)
  case Delay
  case Failure

/** Groundness check result. */
enum GroundCheck:
  case Ground, HasVar

object Builtins:

  def execute(kb: KnowledgeBase, tag: BuiltinTag, goal: TermId, subst: Substitution): BuiltinResult =
    tag match
      case BuiltinTag.NonVar => executeNonVar(kb, goal, subst)
      case BuiltinTag.Ground => executeGround(kb, goal, subst)
      case BuiltinTag.QualifiedName => executeSymbolName(kb, goal, subst, qualifiedName = true)
      case BuiltinTag.ShortName => executeSymbolName(kb, goal, subst, qualifiedName = false)
      case BuiltinTag.LookupSymbol => executeLookupSymbol(kb, goal, subst)
      case BuiltinTag.IsEntityOf => executeIsEntityOf(kb, goal, subst)
      case BuiltinTag.ExtractSort => executeExtractSort(kb, goal, subst)
      case BuiltinTag.Not => BuiltinResult.Delay // NAF handled specially
      case BuiltinTag.ResolveSortInstParam => BuiltinResult.Delay // TODO
      case BuiltinTag.Scope => executeScope(kb, goal, subst)
      case BuiltinTag.Kind => executeKind(kb, goal, subst)
      case BuiltinTag.FieldAccess => BuiltinResult.Delay // TODO

  /** The symbol a NAME-shaped argument denotes, in either spelling.
    *
    * WI-20260902-CZJ2N — the four reflection builtins below each read `case inner:
    * Term.Fn` to get the symbol out of their first argument, and a name term is a
    * `Term.Ref` now (`KnowledgeBase.alloc`'s nullary canon). Read as "not a name" it made
    * every one of them `Delay`, so `qualified_name`, `short_name`, `scope`, `kind` and
    * `extract_sort` answered a SUSPENSION on the very shape they exist for. `Term.Ident`
    * is admitted too — an unresolved name still names something to report.
    */
  private def nameArgSymbol(kb: KnowledgeBase, arg: TermId): Option[TermSymbol] =
    kb.getTerm(arg) match
      case Term.Fn(functor, _, _) => Some(functor)
      case Term.Ref(sym)          => Some(sym)
      case Term.Ident(sym)        => Some(sym)
      case _                      => None

  /** The first POSITIONAL argument of a 1-ary builtin goal, or `None` when the goal has
    * no positional argument at all.
    *
    * "NO POSITIONAL ARGUMENT" IS WIDER THAN "NULLARY", and deliberately: a goal carrying
    * only NAMED arguments (`ground(x: ?y)`) answers `None` here too, so `nonvar`/`ground`
    * FAIL where the old fallback walked the whole goal and answered `Delay`. That is
    * rustland's answer as well — its `pos_arg` reads `pos_args` alone, so the same shape
    * reaches `builtin_ground`'s `None => BuiltinResult::Failure`. These builtins are
    * positional; a named-arg spelling of one names no argument they can read.
    *
    * WI-20260902-EQG4F item 2 — IT USED TO FALL BACK TO THE GOAL ITSELF, and that made a
    * NULLARY `not` goal recurse forever. WI-20260902-CZJ2N stores a nullary goal as
    * `Term.Ref`, and [[KnowledgeBase.getBuiltin]] reads it through `headFunctorOf`, so
    * `rule r(1) :- not` (and its dotted spelling `:- anthill.kernel.not`) now REACHES
    * [[SearchStream.stepNaf]]. With the old fallback the negand WAS the `not` goal, the
    * sub-stream re-entered `stepNaf` on it at depth 0 — so `maxDepth` never bit — and
    * BOTH spellings died `StackOverflowError`. Measured; the applied spelling
    * `anthill.kernel.not(un(999))` answered 1 either way and is the control.
    *
    * `None` IS THE ANSWER RUSTLAND GIVES, at all three of this function's readers:
    * `builtin_nonvar` / `builtin_ground` return `BuiltinResult::Failure` on a missing
    * `pos_arg(0)` and `step_naf` pops the frame. An argument-less builtin goal is
    * malformed, and neither implementation refuses it at LOAD — it fails at resolve, in
    * both, which is a shared limit rather than a scaland one. */
  def firstArg(kb: KnowledgeBase, goal: TermId): Option[TermId] =
    kb.getTerm(goal) match
      case fn: Term.Fn if fn.posArgs.length >= 1 => Some(fn.posArgs(0))
      case _ => None

  def isGround(kb: KnowledgeBase, term: TermId, subst: Substitution): GroundCheck =
    val walked = kb.walk(term, subst)
    kb.getTerm(walked) match
      case Term.Var(_) => GroundCheck.HasVar
      case fn: Term.Fn =>
        var i = 0
        while i < fn.posArgs.length do
          if isGround(kb, fn.posArgs(i), subst) == GroundCheck.HasVar then
            return GroundCheck.HasVar
          i += 1
        i = 0
        while i < fn.namedArgs.length do
          if isGround(kb, fn.namedArgs(i)._2, subst) == GroundCheck.HasVar then
            return GroundCheck.HasVar
          i += 1
        GroundCheck.Ground
      case _ => GroundCheck.Ground

  /** Extract 2 positional args from a goal, walking the first through subst.
    * Returns (walked_arg0, raw_arg1) or None.
    */
  private def extract2Args(kb: KnowledgeBase, goal: TermId, subst: Substitution): Option[(TermId, TermId)] =
    kb.getTerm(goal) match
      case fn: Term.Fn if fn.posArgs.length >= 2 =>
        Some((kb.walk(fn.posArgs(0), subst), fn.posArgs(1)))
      case _ => None

  /** Bind a result term to the result arg (second positional), handling Var or check-equality. */
  private def bindResult(kb: KnowledgeBase, resultArg: TermId, resultTerm: TermId, subst: Substitution): BuiltinResult =
    kb.getTerm(resultArg) match
      case Term.Var(v) =>
        val extra = Substitution()
        extra.bind(v.varId, resultTerm)
        BuiltinResult.SuccessWithBindings(extra)
      case _ =>
        if TermId.raw(kb.walk(resultArg, subst)) == TermId.raw(resultTerm) then
          BuiltinResult.Success
        else BuiltinResult.Failure

  private def executeNonVar(kb: KnowledgeBase, goal: TermId, subst: Substitution): BuiltinResult =
    firstArg(kb, goal) match
      case None => BuiltinResult.Failure // arity-less goal — rustland's `builtin_nonvar`
      case Some(arg) =>
        kb.getTerm(kb.walk(arg, subst)) match
          case Term.Var(_) => BuiltinResult.Delay
          case _ => BuiltinResult.Success

  private def executeGround(kb: KnowledgeBase, goal: TermId, subst: Substitution): BuiltinResult =
    firstArg(kb, goal) match
      case None => BuiltinResult.Failure // arity-less goal — rustland's `builtin_ground`
      case Some(arg) =>
        isGround(kb, arg, subst) match
          case GroundCheck.Ground => BuiltinResult.Success
          case GroundCheck.HasVar => BuiltinResult.Delay

  /** Unified handler for qualified_name and short_name builtins. */
  private def executeSymbolName(kb: KnowledgeBase, goal: TermId, subst: Substitution, qualifiedName: Boolean): BuiltinResult =
    extract2Args(kb, goal, subst) match
      case Some((symArg, resultArg)) =>
        nameArgSymbol(kb, symArg) match
          case Some(functor) =>
            val name = kb.symbols.get(functor) match
              case SymbolDef.Resolved(shortName, qn, _, _) => if qualifiedName then qn else shortName
              case SymbolDef.Unresolved(n) => n
            val strTerm = kb.alloc(Term.Const(Literal.StringLit(name)))
            bindResult(kb, resultArg, strTerm, subst)
          case _ => BuiltinResult.Delay
      case None => BuiltinResult.Failure

  private def executeLookupSymbol(kb: KnowledgeBase, goal: TermId, subst: Substitution): BuiltinResult =
    extract2Args(kb, goal, subst) match
      case Some((nameArg, resultArg)) =>
        kb.getTerm(nameArg) match
          case Term.Const(Literal.StringLit(name)) =>
            kb.tryResolveSymbol(name) match
              case Some(sym) =>
                bindResult(kb, resultArg, kb.makeNameTermFromSym(sym), subst)
              case None => BuiltinResult.Failure
          case _ => BuiltinResult.Delay
      case None => BuiltinResult.Failure

  private def executeIsEntityOf(kb: KnowledgeBase, goal: TermId, subst: Substitution): BuiltinResult =
    extract2Args(kb, goal, subst) match
      case Some((sub, sup)) =>
        val supWalked = kb.walk(sup, subst)
        if kb.isEntityOf(sub, supWalked) then BuiltinResult.Success
        else BuiltinResult.Failure
      case None => BuiltinResult.Failure

  private def executeExtractSort(kb: KnowledgeBase, goal: TermId, subst: Substitution): BuiltinResult =
    extract2Args(kb, goal, subst) match
      case Some((instArg, resultArg)) =>
        nameArgSymbol(kb, instArg) match
          case Some(functor) =>
            // The canonical NAME shape, whichever spelling it arrived in — the form the
            // loader uses for sort references (e.g. `SortRequiresInfo` facts hold
            // `sort_ref`). Pre-WI-172 the eager applySubst-each + bindCompressed silently
            // overwrote the `Term.Ref` form when later discrim-tree matches re-bound the
            // same var; lazy walking surfaces the inconsistency.
            bindResult(kb, resultArg, kb.makeNameTermFromSym(functor), subst)
          case _ => BuiltinResult.Delay
      case None => BuiltinResult.Failure

  private def executeScope(kb: KnowledgeBase, goal: TermId, subst: Substitution): BuiltinResult =
    extract2Args(kb, goal, subst) match
      case Some((symArg, resultArg)) =>
        nameArgSymbol(kb, symArg) match
          case Some(functor) =>
            kb.symbols.get(functor) match
              // WI-976: THE reader of the scope→term direction, and it goes through
              // `scopeTerm`. It used to be `TermId.fromRaw(scopeRaw)` — see
              // `anthill.intern.SymbolTable.ScopeId` for why that was right only by coincidence.
              case SymbolDef.Resolved(_, _, _, scope) =>
                bindResult(kb, resultArg, kb.scopeTerm(scope), subst)
              case _ => BuiltinResult.Delay
          case _ => BuiltinResult.Delay
      case None => BuiltinResult.Failure

  private def executeKind(kb: KnowledgeBase, goal: TermId, subst: Substitution): BuiltinResult =
    extract2Args(kb, goal, subst) match
      case Some((symArg, resultArg)) =>
        nameArgSymbol(kb, symArg) match
          case Some(functor) =>
            kb.symbols.get(functor) match
              case SymbolDef.Resolved(_, _, kind, _) =>
                val strTerm = kb.alloc(Term.Const(Literal.StringLit(kind.toString.toLowerCase)))
                bindResult(kb, resultArg, strTerm, subst)
              case _ => BuiltinResult.Delay
          case _ => BuiltinResult.Delay
      case None => BuiltinResult.Failure

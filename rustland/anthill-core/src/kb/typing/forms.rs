//! Expression-form helpers around application: named-argument matching, field access
//! synthesis, variadic capture, and the walk's inference state (`WalkSolutions`).

use super::*;

// ── Expression form checkers ───────────────────────────────────

/// WI-426: resolve a named-argument label to the callee parameter it names.
/// A named arg binds by LABEL NAME, not symbol identity: the label is interned
/// at parse as a use-site (unresolved) symbol, distinct from the callee's
/// scoped, resolved param symbol even when both short-print the same name. So a
/// symbol-identity `find` silently dropped every named operation argument.
/// Match by short name and return the param's `(symbol, declared-type)` so the
/// caller keys the per-call maps (`param_to_arg_type` / `param_to_arg_sym`) and
/// the validation context by the PARAM symbol — consistent with the positional
/// loop and with what the projection eliminator / WI-385 validation look up.
pub(super) fn match_named_arg_param<'a>(
    kb: &KnowledgeBase,
    params: &'a [(Symbol, Value)],
    arg_name: Symbol,
) -> Option<&'a (Symbol, Value)> {
    // `same_label` relates a written use-site label to a resolved param by SHORT
    // name — a bare source label matched against the param's (possibly-qualified)
    // registered name — the same name resolution the dot-call named-arg path uses.
    params.iter().find(|(s, _)| same_label(kb, *s, arg_name))
}

/// apply(fn, args): type-check with type parameter instantiation.
/// 1. fn is a known operation → unify arg types with param types, resolve return type
/// 2. fn is a variable with arrow type → extract return type and effects
/// Non-recursive Apply checker. Identical to the legacy `check_apply`
/// but reads per-arg `TypeResult`s from `pos_results` / `named_results`
/// (pre-computed by the iterative typer's Build phase) instead of
/// calling `type_check_node` itself. This is the function the iterative
/// `Build::Apply` arm calls.
/// WI-759 — the `field_access(receiver, "name")` call a dot projection rewrites to, with
/// the projected NAME supplied TWICE, once per channel:
///
///  - as the VALUE argument `field`, a `String` constant — the form eval, SLD resolution
///    and both code generators already read (`field_access_parts`' P2 shape). Unchanged, so
///    none of them are touched by this rewrite;
///  - as the TYPE argument `Name`, a `denoted` value-in-type — which is what lets the
///    node's DECLARED return type `FieldOf[T = R, Name = Name]` state the projection's
///    result, making a re-type of the stored node re-derive the member's type instead of
///    widening to `field_access`'s nominal `-> Term`.
///
/// The second channel is needed because there are no singleton types: the `String` constant
/// in value position types as plain `String` and has LOST the name by the time the return
/// type is assembled. The denoted type-argument channel is the only route that carries a
/// compile-time name into type position.
///
/// Keyed by the callee's OWN `Name` type-param symbol, read off the declaration rather than
/// re-interned here — `seed_op_type_args` matches type-argument labels by symbol IDENTITY,
/// and an op-scoped param symbol is not the bare intern of its short name (WI-708).
///
/// Two failure modes, deliberately distinguished (CLAUDE.md: a case that cannot be handled
/// is an explicit diagnostic, not a silent skip):
///  - `Err(None)` — reflect is not loaded, so this desugaring does not exist. Quiet; the
///    caller continues to its remaining dot-dispatch modes, as it did before WI-759 when the
///    `field_access` symbol itself was missing.
///  - `Err(Some(e))` — reflect IS loaded but `field_access` does not declare the `Name` type
///    parameter this rewrite needs. LOUD: falling through would report `no such member` for
///    every field projection in every program, naming the user's own code instead of the
///    malformed declaration.
pub(super) fn synthesize_field_access(
    kb: &mut KnowledgeBase,
    receiver_node: &Rc<NodeOccurrence>,
    field_name: &str,
    occ: &Rc<NodeOccurrence>,
) -> Result<Rc<NodeOccurrence>, Option<TypeError>> {
    let Some(fa_sym) = kb.try_resolve_symbol(dt::qualified(dt::FIELD_ACCESS)) else {
        return Err(None);
    };
    let name_param = lookup_operation_info_full(kb, fa_sym)
        .and_then(|op| {
            op.type_params
                .iter()
                .find(|(n, _)| short_name_of(kb.local_name_of(*n)) == FIELD_OF_NAME_OPERAND)
                .map(|(n, _)| *n)
        })
        .ok_or_else(|| {
            Some(projection_type_error(
                &TypeErrorContext::OperationReturn {
                    op_name: fa_sym,
                    surface: None,
                },
                Some(occ.span.span),
                &format!(
                    "`{}` must declare a `{}` type parameter — the channel a field \
                     projection's name travels to type position through",
                    dt::qualified(dt::FIELD_ACCESS),
                    FIELD_OF_NAME_OPERAND,
                ),
            ))
        })?;
    let field_name_node = NodeOccurrence::new_expr(
        Expr::Const(Literal::String(field_name.to_string())),
        occ.span,
        occ.owner,
    );
    // GROUND (hash-consed) rather than occurrence-carried. A denoted normally rides as a
    // `Value::Node` because it can carry poison — a value occurrence referring to a
    // parameter (`Modify[c]`). A field NAME carries none: it is a closed string constant,
    // which is exactly the persistent, heavily-shared structure hash-consing is for (every
    // projection of the same field shares one term). It also has to be ground to be usable:
    // the return type is term-backed, so the type param binding is resolved by the
    // `TermId` deep σ-walk, which STOPS at a non-`Term` binding (WI-394) and would leave
    // `Name` an unresolved var — reducing `FieldOf` to a residual on every projection.
    let name_term = kb.alloc(Term::Const(Literal::String(field_name.to_string())));
    let name_denoted = Value::term(kb.make_denoted(name_term));
    let pass = crate::kb::simp_rewrite::simp_pass(kb);
    Ok(NodeOccurrence::synthesized_expr(
        Expr::Apply {
            recv_type: None,
            functor: fa_sym,
            pos_args: vec![Rc::clone(receiver_node), field_name_node],
            named_args: Vec::new(),
            type_args: vec![(Some(name_param), name_denoted)],
        },
        Rc::clone(occ),
        pass,
        occ.owner,
    ))
}

/// WI-369: whether projecting a field of `ctor` is forbidden from `from` — true when
/// `ctor` is declared `internal` and `from` cannot see it (kernel-language.md §8.6).
/// A projection inside the declaring sort's own ops (`s.rep` in `MutableStack.push`)
/// is visible, because an operation's scope reaches its sort through the
/// `is_enclosing` link `scan_operation_params` installs; one from another sort is not.
///
/// WI-984 retired the derivation this doc used to describe (the scope as a
/// hash-consed `Fn{sort}` term raw): a [`ScopeId`] carries its owner, and for a sort
/// with an eponymous constructor the term form canonicalizes to `Term::Ref`, so the
/// term-keyed lookup found a scope holding nothing and every `internal` field of such
/// a sort read as VISIBLE.
///
/// WI-977 — TAKES THE SCOPE ALREADY RESOLVED, and there is no permissive arm left.
/// This doc used to end "with no enclosing sort (a free op / top-level), there is no
/// lexical scope to test against, so enforcement is skipped (permissive)", and that
/// was a measured hole rather than a design: a projection written at a file's top
/// level, or in ANY rule body, was never checked. [`hidden_field_owner`] now resolves
/// every context to a real scope — the operation's, the rule's `domain`, or the
/// global scope — so the question is always asked. See [`TypingEnv::referencing_scope`].
///
/// WI-759: takes a scope rather than the whole `TypingEnv` — that is all it ever
/// read, and it is what a `FieldOf` reduction can carry to its site
/// ([`CtorReduceSite::scope`]) without reaching for an ambient env.
pub(super) fn internal_field_hidden_from(
    kb: &mut KnowledgeBase,
    from: ScopeId,
    ctor: Symbol,
) -> bool {
    if !kb.symbols.is_internal(ctor) {
        return false;
    }
    // WI-984: the enclosing sort's scope, straight off its symbol. Was an
    // `alloc(Fn{s}).raw()`, which for a sort with an eponymous constructor
    // canonicalizes to `Term::Ref` (WI-511) and so keyed a scope that holds
    // nothing — every `internal` field of such a sort read as visible.
    //
    // WI-977: takes the scope ALREADY RESOLVED, so the "no enclosing sort" case
    // cannot be answered here by skipping the check. It used to arrive as an
    // `Option` whose `None` arm returned `false` — permissive, and a measured hole
    // for top-level code. [`hidden_field_owner`] resolves it to the global scope.
    !kb.symbols.internal_visible_from(ctor, from)
}

/// WI-727 (proposal 056) — the rewritten call a variadic capture produces: the SAME
/// operation call with its leftover named arguments folded into one named-tuple record
/// bound to the `...args: R` capture parameter. All three are rewritten CONSISTENTLY (the
/// node's named LABELS, the argument list, and the typed results) so the ordinary
/// argument-matching that follows — `R` inference, the `Without` reduction, and the node
/// reorder for eval — runs UNCHANGED on `fix(p, args: (x: 1, z: 2))`.
pub(super) struct CaptureRewrite {
    pub(super) occ: Rc<NodeOccurrence>,
    pub(super) named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
    pub(super) named_results: Vec<Result<TypeResult, TypeError>>,
}

/// WI-727 — clone a typed argument result (`TypeResult` does not derive `Clone`, though all
/// its fields do). Used to carry a matched named argument's already-computed result into the
/// rewritten result list when a capture op mixes declared-named args with captured ones.
fn clone_arg_result(r: &Result<TypeResult, TypeError>) -> Result<TypeResult, TypeError> {
    match r {
        Ok(t) => Ok(TypeResult {
            ty: t.ty.clone(),
            env: t.env.clone(),
            effects: t.effects.clone(),
            node: Rc::clone(&t.node),
        }),
        Err(e) => Err(e.clone()),
    }
}

/// WI-727 (proposal 056) — if `fn_sym` declares a variadic capture parameter (`...args:
/// R`) and this call does NOT already carry that record explicitly, fold every named
/// argument that matches no DECLARED (non-capture) parameter into a single named-tuple
/// occurrence bound to the capture parameter, and return the rewritten call. Returns
/// `None` for the >99% of ops with no capture parameter, and for an already-normalized
/// call (a named argument that names the capture parameter directly) — which then types
/// through the ordinary path (`args` matches the capture parameter, `R` inferred from the
/// tuple, the `Without` reduction narrows the schema). Every arg is `Ok` here
/// (`check_apply_iter`'s `collect_arg_errors` returned early on any failure), so the
/// leftover results are read directly.
///
/// WI-1130 — AND FOR A CALL WHOSE CAPTURE SLOT A POSITIONAL ARGUMENT ALREADY FILLS.
/// Nothing is deferred here: the capture parameter occupies a position like any other, so
/// a positional leftover binds it DIRECTLY (`R` that argument's own type), which is what
/// spec §5.4 says. This function used to fold anyway and append its own synthesized
/// `rest: ()` on top of that binding — one parameter, two bindings, and a load error in
/// every positional arrangement. Both guards below ask the same question of their own
/// channel: is the capture slot already spoken for? The named channel answers by label,
/// the positional one by count. A call that fills it BOTH ways is refused rather than
/// declined, naming the named argument the author wrote (§5.4's exclusivity rule).
pub(super) fn normalize_variadic_capture(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    fn_sym: Symbol,
    // WI-1100: read by the CALLER (`kb.op_capture_param`), which needs it to count this
    // call as the source text writes it, and handed on rather than looked up twice.
    capture_param: Option<Symbol>,
    params: &[(Symbol, Value)],
    occ: &Rc<NodeOccurrence>,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    named_results: &[Result<TypeResult, TypeError>],
) -> Result<Option<CaptureRewrite>, TypeError> {
    let capture_sym = match capture_param {
        Some(s) => s,
        None => return Ok(None),
    };
    // Already-normalized / explicit-record guard: a named argument that names the capture
    // parameter directly (a re-typed rewrite, or a caller passing the record explicitly)
    // is left to ordinary typing. Without this the fold would re-fire every re-type.
    if named_args
        .iter()
        .any(|(label, _)| same_label(kb, capture_sym, *label))
    {
        return Ok(None);
    }
    // WI-1130 (proposal 056 §5.4) — THE CAPTURE SLOT IS A POSITION TOO, and a positional
    // argument may fill it directly, `R` binding that argument's own type. The parameter
    // is declared last (`load.rs` refuses a non-trailing or second `...`, and records no
    // capture entry for a malformed one) and positional arguments fill parameters from
    // index 0, so the slot is taken positionally exactly when the call writes more
    // positional arguments than there are parameters before it.
    //
    // WITHOUT THIS CLAUSE THE FOLD FIRED ANYWAY and appended its OWN synthesized
    // `rest: ()`, giving one parameter two bindings. Measured, before it:
    //   operation cap[R](...rest: R) -> R = rest
    //   operation drive() -> Int64 = cap(5)
    //     type mismatch in cap.rest (op-arg): expected Int64, got ()
    //     type mismatch in cap.rest (op-arg): expected a named argument matching a distinct
    //       unbound parameter, got named argument 'rest' binds a parameter already given
    // Read `expected Int64`: `R` had ALREADY been inferred from the positional argument —
    // the direct binding the spec describes was happening, and the fold then clobbered it.
    // The guard above asks only whether a NAMED argument names the capture parameter; this
    // one asks the same question of the POSITIONAL channel. Two channels, one question
    // (`cap(rest: 5)` and `cap(5)` now agree, both `5`).
    //
    // Not an `Option` fallthrough: a capture symbol absent from the very parameter list it
    // was recorded from is an internal inconsistency, and skipping it would silently
    // restore the double-bind this clause exists to remove. Loud, and unreachable by
    // construction — `record_op_capture_param` (load.rs) keys both from the same `o.params`.
    let capture_index = match params.iter().position(|(s, _)| *s == capture_sym) {
        Some(i) => i,
        None => {
            return Err(TypeError::Other {
                site: std::panic::Location::caller(),
                span: Some(occ.span.span),
                context: TypeErrorContext::OperationArgument {
                    op_name: fn_sym,
                    param: capture_sym,
                },
                expected: "the recorded `...` capture parameter to be one of the \
                           operation's declared parameters"
                    .to_string(),
                actual: "it is not — the capture registry and the parameter list disagree"
                    .to_string(),
            });
        }
    };
    if pos_args.len() > capture_index {
        // A NAMED leftover has nowhere left to go: the record it would be folded into
        // is the very slot the positional argument took, and the two cannot both be
        // `rest`. Refused HERE, naming the argument THE AUTHOR WROTE — the WI-757
        // class. Letting it fall through to ordinary typing reported the synthesized
        // record instead (`expected Int64, got (a: Int64)` for `cap(1, 2, a: 3)`),
        // describing the rewrite rather than the source text.
        let leftovers: Vec<String> = named_args
            .iter()
            .filter(|(label, _)| {
                !params
                    .iter()
                    .any(|(s, _)| *s != capture_sym && same_label(kb, *s, *label))
            })
            .map(|(label, _)| format!("'{}'", short_name_of(kb.local_name_of(*label))))
            .collect();
        if !leftovers.is_empty() {
            let capture_name = short_name_of(kb.local_name_of(capture_sym)).to_string();
            let plural = if leftovers.len() == 1 { "" } else { "s" };
            // The record alternative is offered ONLY for two or more leftovers. A
            // ONE-field named tuple has NO SPELLING — `cap(1, rest: (a: 3))` is
            // `syntax error near \`a: 3\``, measured — so suggesting it for the
            // single-leftover case, which is the commonest way to reach this error,
            // would send the author at a repair they cannot write. WI-1131 owns that
            // gap; when it lands, this condition can go and the clause become
            // unconditional. Found by a `/code-review` pass, which measured the parse.
            let alternative = if leftovers.len() >= 2 {
                format!(", or pass the whole record as `{capture_name}: (…)`")
            } else {
                String::new()
            };
            return Err(TypeError::Other {
                site: std::panic::Location::caller(),
                span: Some(occ.span.span),
                context: TypeErrorContext::OperationArgument {
                    op_name: fn_sym,
                    param: capture_sym,
                },
                expected: format!(
                    "the `...{capture_name}` capture filled ONE way — either by a \
                     positional argument or by named arguments, never both"
                ),
                actual: format!(
                    "named argument{plural} {} cannot be captured: a positional \
                     argument already fills `{capture_name}`; drop that positional \
                     argument{alternative}",
                    leftovers.join(", "),
                ),
            });
        }
        // No named leftover: the positional binding IS the capture. Decline to fold and
        // let the ordinary path bind it — including the surplus case (`cap(1, 2, 3)`),
        // whose WI-1100 arity error is then the ONLY error the call reports.
        return Ok(None);
    }
    // Partition the named arguments: those matching a DECLARED, NON-capture parameter are
    // kept in place; the leftovers (a column name no fixed parameter names) are captured.
    // The capture parameter is excluded from matching by symbol identity, so a leftover
    // never lands in the capture slot via a name coincidence.
    let mut kept_args: Vec<(Symbol, Rc<NodeOccurrence>)> = Vec::new();
    let mut kept_results: Vec<Result<TypeResult, TypeError>> = Vec::new();
    let mut captured: Vec<(Symbol, Rc<NodeOccurrence>)> = Vec::new();
    let mut captured_fields: Vec<(Symbol, Value)> = Vec::new();
    let mut captured_effects: Vec<Value> = Vec::new();
    for (i, (label, arg_occ)) in named_args.iter().enumerate() {
        let matches_declared = params
            .iter()
            .any(|(s, _)| *s != capture_sym && same_label(kb, *s, *label));
        if matches_declared {
            kept_args.push((*label, Rc::clone(arg_occ)));
            kept_results.push(clone_arg_result(&named_results[i]));
            continue;
        }
        // A leftover: a field of the captured record, keyed by its use-site label and typed
        // field-by-field FROM the call (the capture is unconstrained — §2.2). Every arg is
        // `Ok` here (`check_apply_iter`'s `collect_arg_errors` returned early on any failure),
        // so an `Err` leftover is unreachable — but decline to normalize rather than silently
        // drop it (loud over silent), leaving the ordinary path to surface the error.
        let r = match &named_results[i] {
            Ok(r) => r,
            Err(_) => return Ok(None),
        };
        // WI-805 §4.5: the captured record is a NAMED TUPLE, and its component names
        // must be distinct. It is built from a call's NAMED ARGUMENTS, which is why the
        // tuple-literal and tuple-type guards did not cover it when this was written.
        // WI-809 has since made the whole named-argument LIST subject to the same rule at
        // parse, which covers this case too — see the note below on what that leaves.
        //
        // Measured before this check, on a clean load:
        //   operation cap[R](x: Int64, ...rest: R) -> R = rest
        //   operation drive() -> Int64 = cap(1, a: 2, a: "ess").a   -- returned Int(2)
        // building `(a: Int64, a: String)` — the exact type the parse guard forbids
        // writing — with the `a: String` column reachable by neither its name nor its
        // position and its type never checked. A `let (p, q) = cap(1, a: 2, a: 3)` over
        // it reached `match_tuple_pattern` with two IDENTICAL labels and raised
        // `MatchFailed` from the WI-445 double-cover guard, i.e. the defect was live at
        // run time too.
        //
        // Refused rather than declined (`return Ok(None)`): falling back to ordinary
        // typing would report that the label names no parameter, which is true of every
        // captured field and so says nothing about the actual fault.
        //
        // NO LONGER THE FIRST LINE OF DEFENCE, and NOT KNOWN TO BE REACHABLE. WI-809 made
        // "one argument list may not repeat a label" a SYNTACTIC rule
        // (`check_label_unique`, parse/convert.rs), which catches every source-written
        // spelling before the typer runs — including the fixture this check was added for.
        //
        // An earlier version of this comment justified keeping it by claiming a WI-722
        // compile-time macro could synthesize an `Expr::Apply` carrying named args and so
        // bypass the parser. That was FALSE WHEN WRITTEN, and a /code-review pass caught
        // it: both occurrence builders hardcode an empty list (`reflect_make_apply` /
        // `reflect_make_fn`, eval/builtins.rs) and `try_expand_macro` (kb/simp_rewrite.rs)
        // DECLINES any template carrying named args. `substitute_to_occurrence` does carry
        // them, but copies its keys from a source-parsed `Term::Fn` — already checked by
        // the syntactic rule.
        //
        // WI-1127 ADDED A SYNTHESIZER THAT DOES BYPASS THE PARSER, and the guard is still
        // unreachable through it: `splice_query_runner` (eval/builtins.rs) splices
        // `where_run`/`join_run` with the row condition's captured operands as named args,
        // whose labels it MINTS from a running counter (`__anthill_row_param_N__`) — one
        // per hole, so they cannot repeat. That is the property to check of the next such
        // synthesizer: not whether it went through the parser, but whether its labels come
        // from a source the author can make collide.
        if captured_fields
            .iter()
            .any(|(prev, _)| same_label(kb, *prev, *label))
        {
            let name = short_name_of(kb.local_name_of(*label)).to_string();
            return Err(TypeError::Other {
                site: std::panic::Location::caller(),
                span: Some(occ.span.span),
                context: TypeErrorContext::OperationArgument {
                    op_name: fn_sym,
                    param: *label,
                },
                expected: "distinct labels among the captured named arguments".to_string(),
                actual: format!(
                    "named argument '{name}' is captured twice into the `...` record; a named \
                     tuple's component names must be distinct (spec §4.5) — the later '{name}' \
                     would be reachable by neither its name nor its position"
                ),
            });
        }
        captured.push((*label, Rc::clone(&r.node)));
        captured_fields.push((*label, r.ty.clone()));
        merge_effects_into(kb, &mut captured_effects, &r.effects);
    }
    // The captured record's TYPE — a named tuple, NOT 1-collapsed (a single captured
    // field keeps its name so `Without` can drop that column). Empty (`r.fix()`) is a
    // legitimate empty record → `R = ()` → the `Without` identity (OQ #6).
    let record_type = named_tuple_value(kb, &captured_fields, occ.span, occ.owner);
    // The captured record's runtime VALUE occurrence: an ordinary named-tuple literal the
    // back-end evaluates to a `Value::Tuple` (no `where`/`project` compile-time spec-splice
    // — §2.1). Stamp its type so the arg-matching reads it without re-typing the children.
    let tuple_occ = synthesize_named_tuple_literal(kb, occ, captured, record_type.clone());
    let pass = crate::kb::simp_rewrite::simp_pass(kb);
    let tuple_result = Ok(TypeResult {
        ty: record_type,
        env: env.clone(),
        effects: captured_effects,
        node: Rc::clone(&tuple_occ),
    });
    // Bind the record as the capture parameter's argument (kept named args first, the
    // record last), keyed by the capture parameter's short name so ordinary named-arg
    // matching binds it to `...args: R`.
    let capture_short = short_name_of(kb.local_name_of(capture_sym)).to_string();
    let capture_label = kb.intern(&capture_short);
    kept_args.push((capture_label, Rc::clone(&tuple_occ)));
    kept_results.push(tuple_result);
    // The rewritten call node — the type_args carry over from the original apply (a
    // `fix[R]`'s `R` is inferred, so there are none in practice). `reorder_named_args_in_-
    // apply` later rebuilds it from the typed results, so the pos/named children here are
    // scaffolding; only the functor, named LABELS, and type_args are read from it.
    let type_args = match occ.as_expr() {
        Some(Expr::Apply { type_args, .. }) => type_args.clone(),
        _ => Vec::new(),
    };
    // WI-20260829-W6JH0: and the receiver's type claim, on the same grounds as the
    // sentence above — the capture rewrite reshapes this call's ARGUMENTS, not what it
    // returns.
    let recv_type = match occ.as_expr() {
        Some(Expr::Apply { recv_type, .. }) => recv_type.clone(),
        _ => None,
    };
    let new_occ = NodeOccurrence::synthesized_expr(
        Expr::Apply {
            recv_type,
            functor: fn_sym,
            pos_args: pos_args.to_vec(),
            named_args: kept_args.clone(),
            type_args,
        },
        Rc::clone(occ),
        pass,
        occ.owner,
    );
    Ok(Some(CaptureRewrite {
        occ: new_occ,
        named_args: kept_args,
        named_results: kept_results,
    }))
}

/// WI-20260820-5R2XT — the name the author wrote at this call site, when a MACRO lowered
/// it into a call to `fn_sym`. `None` for every call that was not macro-expanded.
///
/// The same-name suppression compares what is RENDERED, not the two symbols. Comparing
/// symbols is the more precise question and the WRONG one here: `entity_name` renders both
/// through `local_name_of`, so two distinct symbols sharing a short name produce
/// `x (expanded to x)` — measured, before the macro gate existed, on an ordinary dot call
/// whose `DotApply` member symbol is not the operation symbol it resolves to.
pub(super) fn surface_of(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    fn_sym: Symbol,
) -> Option<Symbol> {
    let pass = crate::kb::occurrence::macro_expand_pass(kb);
    surface_of_with(kb, pass, occ, fn_sym)
}

/// [`surface_of`] with the `PassId` already in hand — for a caller in a LOOP, where
/// re-interning the pass name per iteration is pure waste (review). The walk itself is
/// three to five links and runs on the success path too, since the context is built before
/// the elimination that may fail.
pub(super) fn surface_of_with(
    kb: &KnowledgeBase,
    macro_pass: crate::kb::occurrence::PassId,
    occ: &Rc<NodeOccurrence>,
    fn_sym: Symbol,
) -> Option<Symbol> {
    occ.surface_call_name(macro_pass)
        .filter(|s| kb.local_name_of(*s) != kb.local_name_of(fn_sym))
}

/// WI-20260904-50B2K part (c) — ONE WALK'S INFERENCE STATE, threaded through the
/// iterative typer beside its work stack.
///
/// It holds the two things a walk learns that outlive the call that learned them, and
/// they are ONE struct rather than two parameters because they are read TOGETHER: the
/// deferred requirements below are discharged against the solutions above, and a walk
/// that reports no solution can license nothing.
///
/// LIFETIME IS THE WALK, WHICH IS NOT WHERE THIS BELONGS. Solutions travelling WITH the
/// result would scope to the body that produced them and make [`Self::watermark`]
/// unnecessary rather than merely correct — `check_apply_iter` already returns
/// `env: env.clone()` at fifteen of its return points, so the channel exists and is inert
/// (user, 2026-09-05; WI-502's `σ → (σ, residual C)` shape). Naming the state here is the
/// step that makes that move a change of OWNER rather than a re-plumbing.
pub(crate) struct WalkSolutions {
    /// What this walk's calls have SOLVED — see [`report_call_solutions`], which is the
    /// one writer, and `TypeBuildFrame::LambdaBody`, which is the one reader.
    pub(super) solved: Substitution,
    /// The walk's variable WATERMARK: [`KnowledgeBase::var_watermark`] as it stood when
    /// the walk began, so `raw() >= watermark` IS "minted during this walk". Read by
    /// [`report_call_solutions`]' scoping gate and by [`walk_minted_carriers`].
    pub(super) watermark: u32,
    /// Abstract spec-op dispatches this walk DEFERRED rather than refused — see
    /// [`WalkSolutions::defer_abstract_dispatch`].
    pub(super) deferred: Vec<DeferredSpecRequirement>,
}

/// WI-20260904-50B2K part (c) — an abstract spec-op dispatch whose carrier is a LAMBDA
/// BINDER, held until the walk ends so the binder's own uses can answer it.
///
/// The refusal it replaces demands a `requires` clause "on enclosing sort", and for this
/// carrier there is NO SITE THE AUTHOR COULD WRITE ONE: a lambda binder is not a type
/// parameter of anything. That is what makes deferral the right answer rather than a
/// weakening — the question is not "did the author forget a declaration" but "does the
/// evidence exist yet", and for a binder it arrives at the USE.
pub(super) struct DeferredSpecRequirement {
    /// The call occurrence to classify if the discharge fails.
    pub(super) occ: Rc<NodeOccurrence>,
    /// The walk-minted variables this call's carrier arguments are typed at — the binders
    /// the requirement falls on. EVERY one must be answered for the call to be licensed.
    pub(super) carriers: SmallVec<[VarId; 2]>,
    /// The spec each carrier must provide.
    pub(super) spec_sort: Symbol,
    /// The classification to raise if the discharge fails — built at the call site, where
    /// the per-call σ that derived `abstract_params` is still in scope, and carried rather
    /// than re-derived (the σ is gone by the time this is read).
    pub(super) class: CallClass,
    /// `(binder, concrete carrier)` for every use of these binders this walk has seen.
    ///
    /// **PER BINDER, NOT A FLAT SET.** The discharge's question is asked of EACH carrier
    /// separately — "was this binder answered, and was every answer an instance?" — and a
    /// flat list cannot state it: with `a` seen at `Int64` and `b` seen at nothing, a flat
    /// `[Int64]` is non-empty and all-providing, and would license a call half of whose
    /// carriers have no evidence at all.
    ///
    /// **NOT `solved` ALONE, AND THE DIFFERENCE IS A FAIL-OPEN.** [`report_call_solutions`]
    /// is FIRST-WINS — a variable already bound is left alone, because the rest of the walk
    /// has been typed against the first answer. Discharging against that one binding would
    /// license `let g = lambda x -> x + x  let a = g(2)  g(bad)` on the strength of `g(2)`
    /// alone. Observations are appended at the same site BEFORE that filter, so a second
    /// use at a second carrier is seen even though it never becomes a solution.
    observed: Vec<(VarId, Symbol)>,
    /// WI-20260904-50B2K part (c), step 2 — has this requirement MOVED INTO A TYPE?
    ///
    /// Set when [`WalkSolutions::generalize_for_arrow`] puts it in a lambda arrow's
    /// `PolyType` context. It stays in this list rather than being removed, and that is
    /// deliberate: the OCCURRENCE and the `CallClass` here are what produce the diagnostic,
    /// and a second error channel for the same failure would be a second owner of the
    /// message. What changes is WHICH variables the discharge asks about — see
    /// [`Self::instances`].
    generalized: bool,
    /// The per-use ∀-ELIMINATIONS of [`Self::carriers`], one set of fresh variables per
    /// reference to the generalized value ([`WalkSolutions::note_instantiation`]).
    ///
    /// Once generalized, the discharge asks its question of THESE and not of the binders:
    /// the binders are quantified, so they are answerable by nothing and are not supposed
    /// to be. An EMPTY list is therefore the licence a polymorphic value earns by being
    /// polymorphic — nothing used it, so nothing owes anything, and the constraint travels
    /// in the type to whoever eventually does.
    instances: SmallVec<[VarId; 2]>,
}

impl WalkSolutions {
    pub(super) fn new(kb: &KnowledgeBase) -> Self {
        Self {
            solved: Substitution::new(),
            watermark: kb.var_watermark(),
            deferred: Vec::new(),
        }
    }

    /// Hold an abstract dispatch instead of refusing it. See [`DeferredSpecRequirement`].
    pub(super) fn defer_abstract_dispatch(
        &mut self,
        occ: &Rc<NodeOccurrence>,
        carriers: SmallVec<[VarId; 2]>,
        spec_sort: Symbol,
        class: CallClass,
    ) {
        self.deferred.push(DeferredSpecRequirement {
            occ: Rc::clone(occ),
            carriers,
            spec_sort,
            class,
            observed: Vec::new(),
            generalized: false,
            instances: SmallVec::new(),
        });
    }

    /// WI-20260904-50B2K part (c) — every variable the enclosing environment still reaches,
    /// σ-RESOLVED as the subjects of the two generalization side conditions are.
    ///
    /// ONE OWNER because both producers ask the identical question, and a side condition
    /// computed two ways is one that can come to disagree with itself.
    fn env_free_vars(&self, kb: &mut KnowledgeBase, outer_env: &TypingEnv) -> Vec<VarId> {
        let mut out: Vec<VarId> = Vec::new();
        let mut seen = HashSet::new();
        let bound: Vec<Value> = outer_env.bound_types().cloned().collect();
        for t in bound {
            let r = resolve_type_deep_value(kb, &self.solved, &t);
            collect_value_type_and_bare_vars(kb, &r, &mut out, &mut seen);
        }
        out
    }

    /// WI-20260904-50B2K part (c), step 3 — RE-GENERALIZE AT THE `let`, which is the half of
    /// the standard rule step 2 shipped without: instantiate freely at every reference, then
    /// quantify again at the binding.
    ///
    /// **THE WART THIS REMOVES WAS MEASURED AND SHIPPED DELIBERATELY.**
    /// `let g = lambda x -> x + x  let h = g  1` was REFUSED while the same program without
    /// the unused alias LOADED — because [`check_bare_ref`] instantiates at every reference,
    /// so the alias minted a carrier and an obligation on it and nothing then pinned that
    /// carrier. Adding an unused alias broke a working program. The narrower repair (only
    /// instantiate where something expects a type) was also measured, and it ACCEPTS a
    /// function value into a `Bool` slot — so the rule had to be this one.
    ///
    /// **ADDITIVE, NOT A MUTATION, and that is what keeps the three existing guards intact.**
    /// A requirement whose instance moves back into a type does not have its own identity
    /// rewritten: the moved instances become a NEW entry whose `carriers` are exactly the
    /// variables the new ∀ binds, and the old entry simply loses them from `instances`. So
    /// `note_instantiation`'s whole-carrier-set gate, the `contradicted` test and the
    /// discharge all read the same shapes they were written for, and the old entry — now
    /// with nothing outstanding — is licensed for the reason it always was: a constraint
    /// that lives in a type is owed by whoever eventually uses it.
    ///
    /// The side condition is [`Self::generalize_for_arrow`]'s, for its reason: an instance
    /// still free in the enclosing environment is not this binding's to quantify.
    pub(super) fn generalize_at_binding(
        &mut self,
        kb: &mut KnowledgeBase,
        bound: &Value,
        outer_env: &TypingEnv,
        span: crate::span::SourceSpan,
        owner: Option<Symbol>,
    ) -> Option<(Vec<VarId>, Vec<Value>)> {
        if self
            .deferred
            .iter()
            .all(|d| d.generalized && d.instances.is_empty())
        {
            return None;
        }
        // FREE IN THE *RESOLVED* TYPE, which is the premise [`Self::generalize_for_arrow`]
        // gets for nothing and this frame has to ask for. That function's free-var test
        // doubles as an UNSOLVED test only because the arrow reaching it was already resolved
        // through `solved`; a `let`'s bound type is not, so a carrier this walk has already
        // pinned still LOOKS free here.
        //
        // MEASURED, and it is the wrong accept review finding 20 fixed coming back by another
        // door: `let g = lambda x -> (x + x, lambda y -> x)  let r = g(true)  1` LOADED again,
        // because `g(true)`'s instance is pinned to `Bool` AND occurs in the result tuple, so
        // it was quantified here and the requirement's instance list emptied — a licence
        // reached by discarding evidence, exactly what the `contradicted` guard exists to
        // refuse one level up.
        let resolved = resolve_type_deep_value(kb, &self.solved, bound);
        let mut free: Vec<VarId> = Vec::new();
        let mut seen = HashSet::new();
        collect_value_type_and_bare_vars(kb, &resolved, &mut free, &mut seen);
        let env_free = self.env_free_vars(kb, outer_env);
        let mut binders: Vec<VarId> = Vec::new();
        let mut context: Vec<Value> = Vec::new();
        let mut spawned: Vec<DeferredSpecRequirement> = Vec::new();
        // NOT-YET-GENERALIZED REQUIREMENTS FIRST — the carriers themselves, which is what the
        // `LambdaBody` frame used to do. Every carrier must be free in the resolved bound type
        // (at once the UNSOLVED test and the EXPRESSIBILITY one — quantifying a variable the
        // type does not mention gives an obligation no instantiation can reach) and none may
        // be free in the enclosing environment.
        for i in 0..self.deferred.len() {
            if self.deferred[i].generalized
                || !self.deferred[i].carriers.iter().all(|v| free.contains(v))
                || self.deferred[i]
                    .carriers
                    .iter()
                    .any(|v| env_free.contains(v))
            {
                continue;
            }
            let spec_sort = self.deferred[i].spec_sort;
            let Some(param) = spec_carrier_param_or_sole(kb, spec_sort) else {
                continue;
            };
            let base = kb.make_sort_ref(spec_sort);
            let carriers = self.deferred[i].carriers.clone();
            for v in &carriers {
                let carrier_ty = Value::term(type_param_var_term(kb, Var::Global(*v)));
                context.push(parameterized_value(
                    kb,
                    base,
                    &[(param, carrier_ty)],
                    span,
                    owner,
                ));
                if !binders.contains(v) {
                    binders.push(*v);
                }
            }
            self.deferred[i].generalized = true;
        }
        // THEN the already-generalized ones, whose per-use INSTANCES a rebinding puts back
        // into a type — `let h = g`, the alias case.
        for d in &mut self.deferred {
            if !d.generalized {
                continue;
            }
            let moved: SmallVec<[VarId; 2]> = d
                .instances
                .iter()
                .copied()
                // AND NOT ALREADY ANSWERED. The resolved-type test above catches an instance
                // this walk has BOUND; this catches one it has merely OBSERVED, which is the
                // same evidence in the channel the discharge actually reads. Two tests for
                // one property is deliberate here: the guard whose absence produced a wrong
                // accept twice in this ticket is the one that gets the belt and the braces.
                .filter(|v| !d.observed.iter().any(|(w, _)| w == v))
                .filter(|v| free.contains(v) && !env_free.contains(v))
                .collect();
            if moved.is_empty() {
                continue;
            }
            let Some(param) = spec_carrier_param_or_sole(kb, d.spec_sort) else {
                continue;
            };
            let base = kb.make_sort_ref(d.spec_sort);
            for v in &moved {
                let carrier_ty = Value::term(type_param_var_term(kb, Var::Global(*v)));
                context.push(parameterized_value(
                    kb,
                    base,
                    &[(param, carrier_ty)],
                    span,
                    owner,
                ));
                if !binders.contains(v) {
                    binders.push(*v);
                }
            }
            d.instances.retain(|v| !moved.contains(v));
            spawned.push(DeferredSpecRequirement {
                occ: Rc::clone(&d.occ),
                carriers: moved,
                spec_sort: d.spec_sort,
                class: d.class.clone(),
                observed: Vec::new(),
                generalized: true,
                instances: SmallVec::new(),
            });
        }
        self.deferred.extend(spawned);
        if binders.is_empty() {
            return None;
        }
        binders.sort_by_key(|v| v.raw());
        Some((binders, context))
    }

    /// WI-20260904-50B2K part (c), step 2 — record one ∀-ELIMINATION of a generalized
    /// requirement, so the discharge asks its question of the fresh variables the USE will
    /// pin rather than of the binders, which are quantified and answerable by nothing.
    ///
    /// Keyed on the binder map rather than on the obligations, because the map is what
    /// says WHICH ∀ this is: a requirement generalized over `?a` is instantiated by
    /// exactly the elimination that freshened `?a`, and two different values' contexts
    /// can name the same spec.
    ///
    /// ANSWERS HOW MANY REQUIREMENTS CLAIMED A BINDER, so a caller can tell that a context
    /// it just eliminated found NO owner — which would mean the constraint has been
    /// dropped. Unreachable while [`Self::generalize_for_arrow`] is the only producer (it
    /// leaves its entry in this list), and read anyway: the next producer this design plans
    /// — let-generalization at the `Let` frame — would otherwise lose its constraints here
    /// in silence.
    pub(super) fn note_instantiation(&mut self, binder_map: &[(VarId, VarId)]) -> usize {
        let mut matched = 0usize;
        for d in &mut self.deferred {
            if !d.generalized {
                continue;
            }
            // THIS ∀ MUST BIND THE REQUIREMENT'S WHOLE CARRIER SET, not merely one of its
            // carriers. `generalize_for_arrow` quantifies a requirement only when EVERY
            // carrier qualifies at that frame, so the ∀ it produced binds all of them —
            // and a ∀ binding only some is therefore a DIFFERENT one, whose elimination
            // would otherwise be credited here as evidence for this requirement. Two
            // requirements sharing a carrier and generalizing at different frames is the
            // shape (not constructible on today's single-carrier prelude specs, which is
            // why this is a precision fix rather than a measured defect — /code-review).
            if !d
                .carriers
                .iter()
                .all(|c| binder_map.iter().any(|(o, _)| o == c))
            {
                continue;
            }
            let mut claimed_here = false;
            for (old, new) in binder_map {
                if d.carriers.contains(old) {
                    claimed_here = true;
                    if !d.instances.contains(new) {
                        d.instances.push(*new);
                    }
                }
            }
            // ONE PER REQUIREMENT, which is what the name and the doc say. The first cut
            // incremented per matching (binder, carrier) PAIR, so a two-carrier requirement
            // answered 2 — inert while both callers only test `== 0`, and a name/value
            // disagreement the next reader would take at its word. /code-review found it.
            if claimed_here {
                matched += 1;
            }
        }
        matched
    }

    /// Record every concrete carrier this call's σ gives a deferred requirement's binders.
    /// Runs BEFORE [`report_call_solutions`]' first-wins filter — see the `observed` doc.
    fn observe_deferred_carriers(
        &mut self,
        kb: &KnowledgeBase,
        before: &Substitution,
        subst: &Substitution,
    ) {
        for d in &mut self.deferred {
            // THE INSTANCES ARE OBSERVED TOO, and they are what the discharge asks about
            // once the requirement has moved into a type (step 2). A generalized
            // requirement's own carriers are quantified — no σ can pin them — so observing
            // only those would leave every use unanswered and refuse every polymorphic
            // application.
            let watched: SmallVec<[VarId; 4]> = d
                .carriers
                .iter()
                .chain(d.instances.iter())
                .copied()
                .collect();
            for v in &watched {
                // ATTRIBUTABLE TO THIS UNIFY OR NOT OBSERVED. A carrier already resolved in
                // `before` was decided by an earlier argument, whose own unify may have
                // FAILED after binding it — `unify_types` never rolls back. See
                // [`report_walk_solutions`].
                if resolved_carrier_sort(kb, before, *v).is_some() {
                    continue;
                }
                let Some(c) = resolved_carrier_sort(kb, subst, *v) else {
                    continue;
                };
                if !d.observed.contains(&(*v, c)) {
                    d.observed.push((*v, c));
                }
            }
        }
    }

    /// THE DISCHARGE, run once when the walk ends: a deferred requirement whose binders
    /// were all seen at carriers that provide the spec is LICENSED — left as the spec op
    /// for value-directed eval, exactly as WI-562's and WI-590's licences leave theirs.
    /// Anything else is classified now, so the walk's refusal is the one it would have
    /// raised at the call.
    ///
    /// **A REQUIREMENT WITH NO OBSERVATION IS REFUSED, NOT LICENSED.** A lambda nothing in
    /// this walk applies (`operation mk() -> … = lambda x -> x + x`) has no evidence, and
    /// the answer it wants is a `PolyType` CONTEXT that outlives the walk — part (c)'s
    /// remaining half. Until that exists, the conservative verdict is today's refusal.
    pub(super) fn discharge(self, kb: &mut KnowledgeBase) {
        for d in self.deferred {
            // WI-20260904-50B2K part (c), step 2 — ONCE THE REQUIREMENT IS IN A TYPE, THE
            // QUESTION IS ASKED OF THE USES, NOT OF THE BINDERS. A quantified variable is
            // answerable by nothing, so asking about it would refuse every generalized
            // lambda; the instantiations are what a use actually pins.
            //
            // AND AN EMPTY INSTANCE LIST IS A LICENCE HERE WHERE AN EMPTY OBSERVATION LIST
            // IS A REFUSAL, which looks like the same fail-open and is its opposite. Not
            // generalized means the constraint has NOWHERE to live but this walk, so no
            // evidence is a gap; generalized means it lives in the arrow's `PolyType`
            // context, so no use is not missing evidence — there is nothing yet to
            // discharge, and whoever eventually applies the value will be asked then.
            let targets: &[VarId] = if d.generalized {
                &d.instances
            } else {
                &d.carriers
            };
            // AND AN OBSERVATION OF A BINDER IS STILL EVIDENCE AFTER GENERALIZATION,
            // WHICH THE FIRST CUT THREW AWAY. Switching `targets` to the instances made an
            // empty instance list license unconditionally — including a walk that had
            // WATCHED the binder itself and seen a carrier providing nothing, since
            // `observe_deferred_carriers` records `carriers ∪ instances`. /code-review
            // raised it as defence-in-depth beside the capture defect above, and it is
            // worth having on its own terms: a licence must never be reached by DISCARDING
            // evidence, whatever route left the instances empty.
            let contradicted = d.observed.iter().any(|(v, c)| {
                d.carriers.contains(v) && !carrier_provides_spec(kb, *c, d.spec_sort)
            });
            // EVERY binder answered, and EVERY answer an instance. Both halves are the
            // licence: a binder with no observation has no evidence, and an observation
            // that provides nothing is the requirement failing rather than deferring.
            let licensed = !contradicted
                && targets.iter().all(|v| {
                    let mut answered = false;
                    for (_, c) in d.observed.iter().filter(|(w, _)| w == v) {
                        answered = true;
                        if !carrier_provides_spec(kb, *c, d.spec_sort) {
                            return false;
                        }
                    }
                    answered
                });
            if !licensed {
                classify(kb, &d.occ, d.class);
            }
        }
    }
}

/// WI-20260904-50B2K part (c) — the CONCRETE sort `var` stands for under `subst`, or
/// `None` while it stands for nothing concrete.
///
/// [`Substitution::resolve_as_value`] is ONE HOP (plus the parent chain), and a call's σ
/// routinely binds one variable to another before either reaches a type — `?param :=
/// ?T_callee`, `?T_callee := Int64`. Asking one hop would read that as "not concrete" and
/// the walk would refuse a call its own evidence answers, so the chain is followed. Bounded
/// and visited-guarded because a σ is not guaranteed acyclic here: `bind_value` raw-inserts
/// on the unbound path (see [`report_call_solutions`], which performs its own occurs-check
/// for the same reason).
fn resolved_carrier_sort(kb: &KnowledgeBase, subst: &Substitution, var: VarId) -> Option<Symbol> {
    let mut cur = var;
    let mut seen: SmallVec<[VarId; 4]> = SmallVec::new();
    loop {
        if seen.contains(&cur) {
            return None;
        }
        seen.push(cur);
        let val = subst.resolve_as_value(cur)?;
        // BOTH CARRIERS, and the first cut read only `Value::Var` — which is the carrier a
        // type variable is LEAST likely to arrive on here. A variable in type position is
        // interned by construction, and `bind_resolved` routes a `Value::Term` binding to
        // `bind_term`, so the very chain this loop's doc names (`?param := ?T_callee`,
        // `?T_callee := Int64`) is stored as `Value::Term(Term::Var(…))` and fell straight
        // to the `other` arm, where `sort_functor_of_view` answers `None` for a variable
        // term. The chase was therefore a no-op on its own motivating case, and the
        // consequence is the refusal it was written to prevent — the walk declining a call
        // whose evidence it holds. `resolved_var` is the file's owner of "read a VarId off
        // either carrier"; asking it is what makes the two spellings one question.
        // /code-review found it.
        //
        // AND THE REPAIR IS WHAT MAKES AN ESCAPED CLOSURE WORK — WI-817's original question,
        // answered here rather than by the ∀ beside it. `Applier.ap(g, leaf())` with
        // `ap[X](fn: Function[A = X, B = Int64], a: X)` binds the closure's carrier to `X`
        // and `X` to `Leaf`, a two-hop chain this loop could not follow. It now answers
        // `Leaf`, `Desc[Leaf]` holds, and the call is licensed: 1 at `Leaf`, 12 at
        // `Wrap[Leaf]`, 1012 for both through ONE closure. MEASURED WITH THE
        // GENERALIZATION BACKED OUT, which is what attributes it here and not to step 2.
        match resolved_var(kb, val) {
            Some(next) => cur = next,
            None => return sort_functor_of_view(kb, val),
        }
    }
}

/// WI-20260904-50B2K part (c) — does `carrier` supply `spec`? The discharge's question,
/// asked through BOTH channels the abstract-dispatch guard itself reads: a sort's own
/// out-edges ([`sort_provides`]) and a provision another sort declares FOR it
/// ([`carrier_provided_by_witness`], WI-1043). Asking only the first would refuse a
/// witness-supplied carrier the call can actually dispatch — the exact wrong answer that
/// ticket was opened on.
pub(super) fn carrier_provides_spec(kb: &KnowledgeBase, carrier: Symbol, spec: Symbol) -> bool {
    sort_provides(kb, carrier, spec) || carrier_provided_by_witness(kb, spec, carrier)
}

/// WI-20260904-50B2K part (c) — the variables minted DURING this walk that a call's
/// argument types are stated at.
///
/// A non-empty answer is what says "this call's carrier is a LAMBDA BINDER": a declared
/// type parameter's variable is minted once, at the declaration, and so is older than
/// every walk. MEASURED over `wi_tests` — 79,414 abstract-dispatch classifications, of
/// which **3** have a walk-minted carrier, and all three are the fixtures this ticket
/// added. The predicate is therefore narrow by measurement, not by argument.
///
/// The bare `Value::Var` arm is written HERE and not left to `collect_value_type`, for the
/// reason [`value_vars_all_walk_local`] states at length: that collector has no
/// `Value::Var` arm and a `_ => {}`, so a carrier that IS a variable — which is this
/// function's whole population — would collect nothing and read as empty.
///
/// **EVERY ARGUMENT POSITION, NOT THE CARRIER POSITIONS**, and the imprecision is stated
/// because it is a deliberate approximation rather than an oversight. A spec op whose
/// NON-carrier parameter is also typed at a binder would have that binder demanded of the
/// discharge too. That direction can only OVER-REFUSE — the discharge requires every listed
/// variable to be answered AND to provide, so a SUPERSET of the carriers is a stricter
/// licence — and the whole measured population is `Additive.add`, where both parameters ARE
/// the carrier. Narrowing to the declared carrier slots would be machinery with no witness.
///
/// **THE CONVERSE IS NOT SYMMETRIC, AND MY FIRST DOC CLAIMED IT WAS.** A SUBSET is a LOOSER
/// licence: a carrier this list omits is never demanded of the discharge, so the call is
/// licensed on the other binders' evidence alone — the exact half-evidence case
/// [`DeferredSpecRequirement::observed`] is per-binder to prevent. Raised by /code-review
/// against the collector, and the reason this reads
/// [`collect_value_type_and_bare_vars`] rather than the shared collector, whose missing
/// `Value::Var` arm produces precisely that subset.
pub(super) fn walk_minted_carriers(
    kb: &KnowledgeBase,
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
    watermark: u32,
) -> SmallVec<[VarId; 2]> {
    let mut out: SmallVec<[VarId; 2]> = SmallVec::new();
    for r in pos_results.iter().chain(named_results.iter()).flatten() {
        let mut vars: Vec<VarId> = Vec::new();
        let mut seen = HashSet::new();
        collect_value_type_and_bare_vars(kb, &r.ty, &mut vars, &mut seen);
        for v in vars {
            if v.raw() >= watermark && !out.contains(&v) {
                out.push(v);
            }
        }
    }
    out
}

/// WI-20260904-50B2K part (c) — the one call an argument-unification site makes: OBSERVE
/// what this σ gives a deferred requirement's binders, then REPORT what it solved.
///
/// The order is load-bearing. [`report_call_solutions`] is first-wins, and observation
/// must see a second use's carrier even where the solving does not — see
/// [`DeferredSpecRequirement::observed`].
///
/// **`unified` GATES BOTH HALVES.** `unify_types` binds as it DESCENDS and never rolls
/// back, so a pair that agrees partway and then disagrees — `Function[A = Int64, B = String]`
/// against `?p -> ?p` binds `?p := Int64` before failing on `B` — leaves real bindings behind
/// on a unification that did NOT hold. For the observation half the consequence is a LICENCE:
/// [`WalkSolutions::discharge`] drops a requirement on the strength of what was observed, so
/// an observation drawn from a failed unify would license a call on evidence the typer is
/// elsewhere careful to say is not evidence.
///
/// THE FIRST CUT GATED ONLY THAT HALF, and the argument it gave for the gate applies WORD FOR
/// WORD to the solutions half — which /code-review said, and it is right. A failed unify's
/// bindings reach `w.solved`, where FIRST-WINS makes them permanent for the whole walk and
/// the `LambdaBody` frame resolves the lambda's arrow through them; and the boolean is
/// DISCARDED at this site (WI-20260904-60143's census), so a false one does not by itself end
/// the call. Withholding is the safe direction either way: an unpinned binder is a REFUSAL,
/// while a binding taken from a failed unify is a wrong type accepted quietly.
///
/// NO CORPUS PROGRAM SEPARATES THE TWO GATINGS — measured, the suite is green with the
/// solutions half gated and ungated — so this is a class removed rather than a defect fixed,
/// and it is recorded as such. What would drive it is a call whose argument unify fails
/// PARTWAY, binds a walk-minted binder on the way down, and whose enclosing call still types;
/// the discarded boolean is what makes that shape constructible at all.
///
/// WI-20260904-60143 CLOSED THAT CENSUS AND WIDENED THE SHAPE RATHER THAN REMOVING IT. The
/// relation still does not roll back — deliberately; see [`unify_types`]' "what survives a
/// `false`" note — and an author-ordered slot list now contributes EVERY agreeing slot
/// instead of the prefix before the first disagreement. Strictly more can reach `w.solved`
/// from a `false`, which is an argument for this gate and not against it. Whether the widened
/// shape gives the two gatings a SEPARATING program was not re-measured there — the gate was
/// left in place, so nothing depended on the answer, and it is recorded as unmeasured rather
/// than assumed unchanged.
///
/// **AND THE GATE IS PER-BINDING, NOT PER-CALL, WHICH TOOK THREE CUTS TO GET RIGHT.** `subst`
/// is ACCUMULATED across a call's whole argument loop, so the boolean alone gates only the
/// FAILING argument: arg[0] binds something and fails, arg[1] unifies cleanly, and the shared
/// σ is read as though the failed unify had never happened. `before` — the σ AS IT STOOD
/// BEFORE THIS ARGUMENT'S UNIFY — is what makes the question per-binding, and BOTH halves
/// take it. The first cut gave it to neither, the second to the observation half only (and
/// said in this very doc that both were covered), and /code-review found each in turn.
pub(super) fn report_walk_solutions(
    kb: &KnowledgeBase,
    solving: Option<&mut WalkSolutions>,
    before: &Substitution,
    subst: &Substitution,
    unified: bool,
) {
    let Some(w) = solving else { return };
    if !unified {
        return;
    }
    w.observe_deferred_carriers(kb, before, subst);
    report_call_solutions(kb, Some(&mut w.solved), before, subst, w.watermark);
}

/// WI-20260904-50B2K part (c) — copy a finished call's bindings into the walk's
/// [`Substitution`], so a frame that minted a type before the call ran can see what the
/// call decided.
///
/// THE CHANNEL THAT DID NOT EXIST. A call's σ is minted in `check_apply_iter` and dropped
/// with the call, so the lambda whose binder a body pinned never saw the pinning —
/// measured on `let f = lambda v -> twice(v)`, where `?param` IS bound to `Int64` by the
/// body's own call and the binding went nowhere.
///
/// **WALK-LOCAL ONLY, DECIDED BY ALLOCATION ORDER.** `watermark` is
/// [`KnowledgeBase::var_watermark`] taken when this walk began, so a variable minted
/// DURING the walk has `raw() >= watermark` and everything older does not.
///
/// THE FIRST CUT HAD NO SUCH GATE, on the reasoning that "`VarId`s are unique, so a
/// callee's variable can never be mistaken for a caller's". /code-review falsified that,
/// and three rounds of driving found three separate populations — which is what says
/// ENUMERATING was the wrong method:
///
///   1. A DECLARED TYPE PARAMETER'S VARIABLE IS SHARED.
///      [`KnowledgeBase::record_type_param_var`] publishes exactly ONE `Var::Global` per
///      type-parameter SYMBOL, so a callee's `T` is the SAME variable at every call site.
///      `check_apply_iter`'s WI-374 note says what kept that sound — the parametricity tie
///      rides "the canonical channel AND THE PER-CALL SUBST" — and this copies out of that
///      σ. Measured in one walk: `var 1372 kept=String dropped=Int64`.
///   2. THE RANGE LEAKS WHERE THE DOMAIN DOES NOT. `?param := ?T_callee` puts a
///      callee-owned variable INTO the arrow, and filtering the VARIABLE says nothing
///      about the VALUE. Measured as an arrow leaving the walk reading `?_`.
///   3. A CALL'S σ IS NOT TYPE-ONLY. It carries dispatch's value-level bindings —
///      `Name := "x" / "y" / "z"` collided within one walk, and riding as `Value::Term`
///      over literal terms they escaped a carrier filter too.
///
/// ONE QUESTION RETIRES THE LIST. None of the three is minted during the walk that takes
/// the watermark: a type parameter's canonical variable and a fact pattern's variables are
/// allocated at LOAD. BOTH SIDES are asked, because (2) is a RANGE defect — the variable
/// must be walk-local AND its value must mention no variable that is not.
///
/// MEASURED, AND THE ZERO IS THE POINT: with the gate, a consistency check over the whole
/// `wi_tests` binary sees NO variable bound twice to disagreeing values (4131 rows). The
/// ungated version disagreed on 19 rows of 19 in one file.
///
/// AN OCCURS-CHECK IS PERFORMED HERE, because `bind_value` does not do one — /code-review,
/// and the first cut's doc claimed it did. That function compares structurally when the
/// variable is ALREADY bound and does a raw insert otherwise, and this call is filtered to
/// the unbound case, so it always takes the insert path. Two calls can then contribute
/// `?a := f(?b)` and `?b := g(?a)`, each acyclic and walk-local on its own, and leave
/// `body_solutions` CYCLIC for `resolve_type_deep_value` to walk. An ALREADY-BOUND variable
/// is left alone: the rest of the walk has already been typed against the first answer.
///
/// TWO THINGS THIS DOES NOT DO, named because they are unmeasured rather than absent:
///
///   * NO ROLLBACK. A report happens when an argument's unification finishes, which is
///     BEFORE the CALL is known to type: [`report_walk_solutions`] withholds a FAILED
///     argument unify's bindings, but a call whose arguments all unify and which then
///     returns `Err` for another reason still leaves its bindings behind. Combined with
///     first-wins, a speculative binding could outrank a later well-typed one. No corpus
///     program shows it; the scoped container below is what would remove the possibility.
///   * THE PROJECTION-DEFERRED PATH DOES NOT REPORT. The report sits inside the
///     `!(op_has_projection && value_contains_projection(..))` arm, and WI-398's deferred
///     elimination unify afterwards has no report of its own. A binder pinned only through
///     a projection-typed parameter keeps the pre-change behaviour.
///
/// AND THE CONTAINER IS STILL WALK-LIFETIME, WHICH IS NOT WHERE THIS BELONGS. Solutions
/// travelling WITH the result would scope to the body that produced them and make the gate
/// above unnecessary rather than merely correct — `check_apply_iter` already returns
/// `env: env.clone()` at fifteen of its return points, so the channel exists and is inert
/// (user, 2026-09-05; WI-502's `σ → (σ, residual C)` shape).
pub(super) fn report_call_solutions(
    kb: &KnowledgeBase,
    solved: Option<&mut Substitution>,
    before: &Substitution,
    subst: &Substitution,
    watermark: u32,
) {
    let Some(out) = solved else { return };
    // WI-20260904-50B2K part (c) — THE OCCURS-CHECK RUNS AGAINST THE `out` EACH CANDIDATE
    // ACTUALLY LANDS IN, which the first cut did not do: it filtered the WHOLE batch against
    // `out` as it stood before any of the batch was bound, so two candidates could jointly
    // close a cycle that neither closes alone. With `out` holding `?c := (?a,)`, a σ carrying
    // `?a := (?b,)` and `?b := (?c,)` passes both tests — `?b` is unbound when `?a` is
    // checked and `?a` is unbound when `?b` is checked — and the pair is cyclic once both
    // land. That is the same hazard the transitive check was added for, one level up, with
    // the same consequence: a stack overflow in `resolve_type_deep_value`, not a wrong type.
    // Only the WALK-LOCAL and watermark filters can be batched, because neither reads `out`.
    // /code-review found it.
    let mut candidates: Vec<(VarId, Value)> = subst
        .iter()
        .filter(|(v, val)| v.raw() >= watermark && value_vars_all_walk_local(kb, val, watermark))
        .map(|(v, val)| (*v, val.clone()))
        .collect();
    // ORDERED, BECAUSE A SEQUENTIAL DECISION MAKES THE ORDER PART OF THE ANSWER. `subst` is
    // an `imbl` HashMap over `RandomState` (kb/subst.rs) — HAMT iteration order varies with
    // a per-process seed. The batch filter this replaced could not see that, every candidate
    // being tested against a frozen `out`; testing against a GROWING one means WHICH member
    // of a cycle survives would otherwise differ run to run, and `w.solved` is what the
    // `LambdaBody` frame resolves the lambda's arrow through. Mint order is the tie-break:
    // the earlier variable wins, which is the same first-wins rule this function already
    // applies across calls. /code-review found it.
    candidates.sort_by_key(|(v, _)| v.raw());
    for (v, val) in candidates {
        // ALREADY BOUND BEFORE THIS ARGUMENT'S UNIFY ⇒ NOT THIS ARGUMENT'S TO REPORT, and
        // this is the half the first two cuts left open. `subst` is ACCUMULATED across the
        // argument loop, so `if !unified { return }` suppresses only the FAILING argument's
        // report: the next argument that unifies cleanly hands the whole σ over, leftovers
        // and all. Concretely, `take(f: (x: Int64) -> String, n: Int64)` applied as
        // `take(lambda v -> v, 3)` binds `?p := Int64` descending into the param slot, fails
        // on the result slot, and reports nothing — then `3` unifies and carries `?p := Int64`
        // into `solved`, where first-wins makes it permanent for the walk. The filter costs
        // NOTHING on the good path: a variable bound by an earlier SUCCESSFUL argument was
        // already offered at that argument's own site, and first-wins means re-offering it
        // is a no-op. Its candidacy cannot have improved in between either — a bound var
        // keeps its value, and the walk-local test reads only the value and the watermark.
        // /code-review found it, on the pass after the doc claimed both halves were gated.
        if before.resolve_as_value(v).is_some() {
            continue;
        }
        if out.resolve_as_value(v).is_some() {
            continue;
        }
        if value_reaches_var(kb, out, &val, v) {
            continue;
        }
        out.bind_value(kb, v, val);
    }
}

/// WI-20260904-50B2K part (c) — [`collect_value_type`]'s walk PLUS THE ARM IT LACKS: a
/// bare `Value::Var`, at EVERY depth.
///
/// **THE SHARED COLLECTOR CANNOT ANSWER THIS QUESTION, AND ANSWERING IT WRONG IS SILENT.**
/// `collect_value_type` has arms for `Value::Term`, `Value::Node` and `Value::Entity` /
/// `Value::Tuple`, then `_ => {}` — a bare `Value::Var` contributes NOTHING. Its three
/// callers here all ask "which variables does this value mention?", and for all three an
/// under-collecting answer fails in the UNSAFE direction: a walk-local gate answers `true`
/// on an empty list, an occurs-check answers "no cycle", and a carrier list omits a binder
/// the discharge would otherwise have demanded evidence for.
///
/// THE FIRST CUT HANDLED THE TOP LEVEL ONLY, in each of the three, and /code-review found
/// all three: `Value::Tuple { … Value::Var(?a) … }` walks straight past the special case
/// into the shared collector, which recurses into the children WITH ITSELF and drops the
/// var. So the special case covered exactly the depth-0 shape and nothing under it.
///
/// **NOT FIXED IN `collect_value_type` ITSELF, AND THAT IS THE SAME DECISION AS BEFORE.**
/// That collector feeds [`signature_bound_vars`], the ONE OWNER of a signature's binder set
/// (WI-1083) — widening it changes which variables a `∀` quantifies. It is measurably green
/// either way and the shape occurs ZERO times on this corpus, so the wider change still has
/// no witness. This one is LOCAL to the three functions part (c) owns, has no other reader,
/// and can only TIGHTEN; the under-collection in the shared collector is real, is NOT this
/// ticket's, and is recorded at its site.
fn collect_value_type_and_bare_vars(
    kb: &KnowledgeBase,
    v: &Value,
    vars: &mut Vec<VarId>,
    seen: &mut HashSet<u32>,
) {
    match v {
        Value::Var(Var::Global(vid)) => {
            if !vars.contains(vid) {
                vars.push(*vid);
            }
        }
        // Recurse with THIS function, not the shared one: the shared one recurses into a
        // carrier's children with ITSELF, which is exactly where the bare var is lost.
        Value::Entity { pos, named, .. } | Value::Tuple { pos, named, .. } => {
            for c in pos.iter() {
                collect_value_type_and_bare_vars(kb, c, vars, seen);
            }
            for (_, c) in named.iter() {
                collect_value_type_and_bare_vars(kb, c, vars, seen);
            }
        }
        other => crate::kb::node_occurrence::collect_value_type(kb, other, vars, seen),
    }
}

/// WI-20260904-50B2K part (c) — can `var` be reached FROM `v`, following the bindings
/// already recorded in `out`? The occurs-check [`report_call_solutions`] performs itself.
///
/// **THE DIRECT TEST IS NOT ENOUGH, AND THE DOC THAT DEMANDED THIS CHECK SAID SO.** It names
/// the hazard as "two calls can contribute `?a := f(?b)` and `?b := g(?a)`, each acyclic and
/// walk-local ON ITS OWN" — and a direct `value_mentions_var` passes each of them, because
/// neither value mentions its OWN variable. So the first cut implemented the check the doc
/// argued against. The cycle then reaches `resolve_type_deep_value`, whose `map_fn_children`
/// recursion has no visited set: a STACK OVERFLOW, not a wrong type. /code-review found it.
///
/// Following `out` is what makes the test transitive: a candidate is rejected when `var` is
/// reachable from its value through bindings THIS walk has already committed.
pub(super) fn value_reaches_var(
    kb: &KnowledgeBase,
    out: &Substitution,
    v: &Value,
    var: VarId,
) -> bool {
    let mut stack: Vec<Value> = vec![v.clone()];
    let mut seen_vars: HashSet<u32> = HashSet::new();
    while let Some(cur) = stack.pop() {
        let mut vars: Vec<VarId> = Vec::new();
        let mut seen = HashSet::new();
        collect_value_type_and_bare_vars(kb, &cur, &mut vars, &mut seen);
        for w in vars {
            if w == var {
                return true;
            }
            if !seen_vars.insert(w.raw()) {
                continue;
            }
            if let Some(bound) = out.resolve_as_value(w) {
                stack.push(bound.clone());
            }
        }
    }
    false
}

/// WI-20260904-50B2K part (c) — is every variable inside `v` walk-local? The RANGE half of
/// [`report_call_solutions`]' gate; the measurement that made it necessary is there.
///
/// **IT READS [`collect_value_type_and_bare_vars`], AND THE REASON IS THIS GATE'S OWN
/// HISTORY.** The first cut asked `collect_value_type`, which has no `Value::Var` arm, so
/// a binding `?param := Value::Var(T_canonical)` — the shape `unify_types`' var arm mints
/// when it binds one variable to another's WALKED value — collected ZERO variables and
/// `all()` answered `true` on an empty list, admitting exactly the leak the gate exists to
/// stop. The repair then handled the TOP LEVEL only, which /code-review found in turn: the
/// same value one carrier deep (`Value::Tuple { … Value::Var(?T) … }`) walks past the
/// special case and is dropped by the shared collector's own recursion. A GATE IS ONLY AS
/// EXHAUSTIVE AS THE READER IT ASKS, and asking it at one depth is asking it at one depth.
pub(super) fn value_vars_all_walk_local(kb: &KnowledgeBase, v: &Value, watermark: u32) -> bool {
    let mut vars: Vec<VarId> = Vec::new();
    let mut seen = HashSet::new();
    collect_value_type_and_bare_vars(kb, v, &mut vars, &mut seen);
    vars.iter().all(|vid| vid.raw() >= watermark)
}

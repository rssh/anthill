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
    // (The `Value`-level walk the apply resolves a return type through now SPLICES such a
    // binding back — `splice_non_term_bindings` — so that stop no longer strands it; ground
    // is kept for the sharing reason above, and dropping it is unmeasured.)
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
/// level, or in ANY rule body, was never checked. [`written_scope`] now resolves
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
    // for top-level code. [`written_scope`] resolves it to the global scope.
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
pub(super) fn clone_arg_result(r: &Result<TypeResult, TypeError>) -> Result<TypeResult, TypeError> {
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
    /// [`WalkSolutions::defer_binder_dispatch`].
    pub(super) deferred: Vec<DeferredSpecRequirement>,
    /// The tuple patterns this walk bound over a type it had not decided — see [`TupleShape`].
    pub(super) shapes: Vec<TupleShape>,
    /// The labels each such pattern reads by, as the first use that labelled its tuple gave
    /// them ([`WalkSolutions::close_under_shapes`]) — one list per pattern, for every shape of
    /// it: an instance a use's ∀-elimination copied shares its pattern.
    agreed_labels: Vec<(Rc<NodeOccurrence>, Rc<[Symbol]>)>,
    /// The operations taken as function values at a slot that holds a variable — see
    /// [`HeldFunctionValue`].
    held_values: Vec<HeldFunctionValue>,
}

/// An operation taken as a function value at a slot whose type holds a variable where the
/// reference is typed: `useS` in `app(useS, leaf)` over `app[X](f: (x: X) -> Int64, x: X)`
/// meets `(x: X) -> Int64` before `leaf` fixes `X`. The value is the lambda that calls the
/// operation, typed at the instance the value is used at (kernel-language §5.4), so its
/// dictionaries are built where that instance is known: by the call or the construction whose
/// argument it is, once its σ is complete and closes the slot ([`attach_held_arguments`]),
/// and otherwise where the walk ends, at the slot as far as it was read
/// ([`WalkSolutions::attach_held_values`]).
pub(super) struct HeldFunctionValue {
    /// The reference, stamped `EtaOpRef` with no dictionary until it is decided.
    pub(super) occ: Rc<NodeOccurrence>,
    pub(super) op: Symbol,
    /// The operation's own type, the ∀ the dictionary pin reads ([`attach_eta_dispatch_dict`]).
    pub(super) fn_ty: Value,
    /// The slot as the reference met it, read through the σ of each call or construction that
    /// left it open.
    pub(super) expected: Value,
    pub(super) env: TypingEnv,
}

/// WI-20260904-34J8Z — A TUPLE PATTERN BOUND OVER A TYPE THE WALK HAD NOT DECIDED: a tuple nested
/// in a lambda's binder list (`lambda ((a, b), c)`), or a `let` or `match` that takes apart an
/// un-annotated binder (`lambda p -> let (a, b) = p …`). Its value's type is a variable, and the
/// pattern says what it must be — a tuple of as many components as it has binders, component `i`
/// meeting binder `i` — but not its labels: a pattern spells none (kernel-language §6.7), so the
/// pattern cannot be the type, and binding the variable to a positional tuple would refuse every
/// named value handed to it (§4.5). So it is held here, and each call whose σ decides the
/// variable is held to it there ([`WalkSolutions::close_under_shapes`]): a value of another
/// width, or no tuple, is refused at that call, and a component meets its binder there, which
/// binds an un-annotated binder's variable in that call's σ as the top-level binder list's own
/// tuple binds its components (kernel-language §4.7). Each call its own σ, so each use its own
/// types, as for a binder of the list itself.
///
/// Before it, each component was a variable nothing tied to the parent's, so a use's tuple
/// reached no binder: `lambda ((a: Int64, b: Int64), c)` applied to `(("x", true), 3)` loaded
/// and stopped at run time, and `lambda ((a, b), c) -> a + b` was refused for want of an
/// `Additive` its use supplies.
///
/// A shape names the walk's own variables, so where a `let` generalizes the lambda and a use
/// eliminates the ∀, the use's instance of a quantified variable is not the one the shape names:
/// each elimination copies the shapes that mention one, at the instance
/// ([`WalkSolutions::note_instantiation`]).
pub(super) struct TupleShape {
    /// The pattern as the walk returned it — the occurrence the labels the uses give are written
    /// onto ([`WalkSolutions::agreed_labels`]).
    pub(super) pattern: Rc<NodeOccurrence>,
    /// The variable the value taken apart is typed at.
    pub(super) parent: VarId,
    /// What each component's binder is typed at: its annotation, the type a literal or a
    /// constructor written there states, else the variable the pattern minted for it.
    pub(super) components: Vec<Value>,
    /// The name each component binds, where it is a binder, for the refusal.
    pub(super) binders: Vec<Option<Symbol>>,
    /// The components as the body of the lambda the pattern is in solved them, read once where
    /// that body ends ([`WalkSolutions::freeze_shapes`]). A use read after that point reads
    /// these and not the walk's solutions, which by then hold what OTHER uses gave, first wins.
    frozen: bool,
    /// A `match` arm's pattern: a tuple of another width does not match it and the next arm is
    /// tried (WI-20261012-80259), so such a use holds it to nothing. Any other is irrefutable,
    /// and the use is refused.
    refutable: bool,
}

impl TupleShape {
    pub(super) fn new(
        pattern: Rc<NodeOccurrence>,
        parent: VarId,
        components: Vec<Value>,
        binders: Vec<Option<Symbol>>,
        refutable: bool,
    ) -> Self {
        TupleShape {
            pattern,
            parent,
            components,
            binders,
            frozen: false,
            refutable,
        }
    }
}

/// WI-20260904-50B2K part (c) — an abstract spec-op dispatch whose carrier is a LAMBDA
/// BINDER, held until the walk ends so the binder's own uses can answer it — and
/// (WI-20260929-6NMGQ) a deferral to the enclosing declaration's `requires` that covered
/// such a call only because the binder was not solved yet. [`WalkSolutions::discharge`]
/// decides both the same way ([`DeferredCall`]).
///
/// The refusal it replaces demands a `requires` clause "on enclosing sort", and for this
/// carrier there is NO SITE THE AUTHOR COULD WRITE ONE: a lambda binder is not a type
/// parameter of anything. That is what makes deferral the right answer rather than a
/// weakening — the question is not "did the author forget a declaration" but "does the
/// evidence exist yet", and for a binder it arrives at the USE.
pub(super) struct DeferredSpecRequirement {
    /// The call occurrence the discharge classifies.
    pub(super) occ: Rc<NodeOccurrence>,
    /// The walk-minted variables this call's carrier arguments are typed at — the binders
    /// the requirement falls on. EVERY one must be answered for the call to be licensed.
    pub(super) carriers: SmallVec<[VarId; 2]>,
    /// The classification the call keeps where no use gives its carriers a type — the
    /// refusal of the dispatch, or for a held deferral the deferral itself ([`DeferredCall::held`]).
    /// Built at the call site, where the per-call σ that derived it is still in scope, and
    /// carried rather than re-derived.
    pub(super) class: CallClass,
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
    /// WI-20260929-6NMGQ — the call as it was typed, which the dictionaries its uses hand
    /// it are built from.
    call: Rc<DeferredCall>,
    /// For each variable this entry watches, the variable of the call's σ a use's type is
    /// bound to when its dictionary is built: a carrier's root in that σ
    /// ([`walk_minted_elements`]), an instance's carrier's.
    origin: SmallVec<[(VarId, VarId); 2]>,
    /// The type each use gave a watched variable, PER VARIABLE: with `a` given `Int64` and
    /// `b` nothing, a flat list of types would answer for a call half of whose carriers have
    /// no evidence. Not [`WalkSolutions::solved`] alone, which is first-wins: `let g = lambda x -> x
    /// + x  let a = g(2)  g(bad)` would be answered on `g(2)` alone. A use at the enclosing
    /// declaration's own type parameter is recorded too, and is the use its `requires`
    /// answers.
    uses: Vec<(VarId, Value)>,
    /// Each ∀-elimination of this entry's carriers: an instance, and the application of
    /// the lambda that hands it the dictionary at the instance's type.
    sites: Vec<(VarId, Rc<NodeOccurrence>)>,
    /// The instances a rebinding put back into a quantified type
    /// ([`WalkSolutions::generalize_at_binding`] spawns their entry): an application at one
    /// forwards the slot the enclosing lambda is handed.
    moved: SmallVec<[VarId; 2]>,
}

/// WI-20260929-6NMGQ — a spec-op call whose element is a lambda's unannotated parameter,
/// as it was typed. The parameter is solved by the lambda's uses, after the call: where
/// the walk generalized the lambda, each application hands it the dictionary at the type
/// that application gives the parameter, under [`Self::slot`] (its quantified type's
/// context is the lambda's requirement, kernel-language §4.4), and the call reads it;
/// where the parameter has one type, the call reads the dictionary at it. Either is built
/// as a call builds an operation's `requires` ([`lambda_requirement_dict`]): the enclosing
/// declaration's own dictionary where its `requires` covers the type, a construction where
/// a provider answers it, and a refusal otherwise.
pub(super) struct DeferredCall {
    /// The environment and σ the call was typed in.
    pub(super) env: TypingEnv,
    pub(super) subst: Substitution,
    pub(super) fn_sym: Symbol,
    pub(super) op_short_sym: Symbol,
    pub(super) spec_sort: Symbol,
    pub(super) span: Option<Span>,
    /// The slot an application of the generalized lambda hands the dictionary under: one
    /// per held call, so two calls on one parameter at two bindings read two.
    pub(super) slot: Symbol,
    /// The call deferred to the enclosing declaration's `requires` where it was typed,
    /// covered only because its element was not solved yet — the classification it keeps
    /// where no use gives the parameter a type, generalized or not.
    pub(super) held: bool,
}

impl DeferredCall {
    /// The call typed at `subst` in `env`, the `serial`-th this walk deferred; `held` where
    /// it was a deferral to the enclosing declaration's `requires`. The slot is named by
    /// its first carrier — a variable minted in this walk, so no other walk's — and the
    /// serial.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        kb: &mut KnowledgeBase,
        env: &TypingEnv,
        subst: &Substitution,
        fn_sym: Symbol,
        spec_sort: Symbol,
        span: Option<Span>,
        carriers: &[VarId],
        serial: usize,
        held: bool,
    ) -> Self {
        let op_short = short_name_of(kb.qualified_name_of(fn_sym)).to_string();
        let op_short_sym = kb.intern(&op_short);
        let slot = kb.intern(&format!(
            "__ctx_{}_{}_{serial}",
            short_name_of(kb.qualified_name_of(spec_sort)).to_lowercase(),
            carriers[0].raw(),
        ));
        DeferredCall {
            env: env.clone(),
            subst: subst.clone(),
            fn_sym,
            op_short_sym,
            spec_sort,
            span,
            slot,
            held,
        }
    }
}

impl WalkSolutions {
    pub(super) fn new(kb: &KnowledgeBase) -> Self {
        Self {
            solved: Substitution::new(),
            watermark: kb.var_watermark(),
            deferred: Vec::new(),
            shapes: Vec::new(),
            agreed_labels: Vec::new(),
            held_values: Vec::new(),
        }
    }

    /// Hold `value` until its instance is known ([`HeldFunctionValue`]). A reference typed
    /// again replaces what it held before.
    pub(super) fn hold_function_value(&mut self, value: HeldFunctionValue) {
        self.held_values.retain(|h| !Rc::ptr_eq(&h.occ, &value.occ));
        self.held_values.push(value);
    }

    /// Does this walk hold a function value no call has decided yet?
    pub(super) fn holds_function_values(&self) -> bool {
        !self.held_values.is_empty()
    }

    /// The function value `occ` holds, taken out to be decided by the call it is an argument
    /// of; `None` where it holds none.
    pub(super) fn take_held_value(&mut self, occ: &Rc<NodeOccurrence>) -> Option<HeldFunctionValue> {
        let at = self.held_values.iter().position(|h| Rc::ptr_eq(&h.occ, occ))?;
        Some(self.held_values.swap_remove(at))
    }

    /// Where the walk ends, every function value no call decided is given its dictionaries at
    /// its slot as far as it was read. The first refusal is the walk's. A call that types
    /// decides its arguments, so what reaches here is a value whose call was refused before it
    /// could (traced over `wi_tests`: nine references, each in a refused program).
    pub(super) fn attach_held_values(&mut self, kb: &mut KnowledgeBase) -> Result<(), TypeError> {
        let mut refusal: Option<TypeError> = None;
        for h in std::mem::take(&mut self.held_values) {
            let labels = h.occ.eta_slot_labels().flatten();
            if let Err(e) = attach_eta_dispatch_dict(kb, &h.env, h.op, &h.occ, &h.fn_ty, &h.expected, labels) {
                refusal.get_or_insert(e);
            }
        }
        refusal.map_or(Ok(()), Err)
    }

    /// WI-20260904-34J8Z — where the body of a lambda ends, the components of the shapes its
    /// patterns recorded since `mark` are read through what the body solved, and kept so: a use
    /// after the body reads them and not [`Self::solved`], where a use reports what it gave,
    /// first wins — read live, the second of `g((1, 2), 3)` and `g(("s", true), 3)` was refused
    /// for the first's types. The same reading the frame gives the lambda's arrow.
    pub(super) fn freeze_shapes(&mut self, kb: &mut KnowledgeBase, mark: usize) {
        for shape in self.shapes.iter_mut().skip(mark).filter(|s| !s.frozen) {
            for c in shape.components.iter_mut() {
                *c = resolve_type_deep_value(kb, &self.solved, c);
            }
            shape.frozen = true;
        }
    }

    /// WI-20260904-34J8Z — the type a tuple pattern takes apart, as far as this walk has decided
    /// it: a variable an EARLIER call of the body solved is that call's type, so a `let` or a
    /// `match` written after it is bound against it rather than recorded as a shape no later call
    /// decides — `let w = h(p)  let (a, b) = p  a` left `a` unsolved, and an operation declared
    /// `-> String` returned `1`, where the two `let`s the other way round were refused. Anything
    /// else is as it was.
    pub(super) fn decided_for_pattern(&self, kb: &mut KnowledgeBase, ty: Value) -> Value {
        if inference_hole_var(kb, &ty).is_some() {
            resolve_type_deep_value(kb, &self.solved, &ty)
        } else {
            ty
        }
    }

    /// WI-20260904-34J8Z — THE LABELS EACH SHAPE'S PATTERN READS BY, once the walk has seen every
    /// use: the real labels the first use that labelled its tuple gave ([`Self::close_under_shapes`]
    /// holds every later one to them). The run time then fetches by them, as it does for a pattern
    /// whose type was known (kernel-language §6.7, "Destructuring binds by LABEL"). Read by slot, a
    /// value permuted against its type handed binder `i` another component than the one it was
    /// typed from: `g(f(), 3)` over `lambda ((a, b), c) -> a`, `f() -> (x: Int64, y: String) = (y:
    /// "s", x: 1)`, answered `"s"` from an operation declared `-> Int64` (WI-788's wrong value, one
    /// level down). A positional use says no labels, and a positional value is read by slot
    /// whatever the pattern holds.
    pub(super) fn agreed_labels(&self) -> &[(Rc<NodeOccurrence>, Rc<[Symbol]>)] {
        &self.agreed_labels
    }

    /// WI-20260904-34J8Z — HOLD A CALL'S σ TO THE SHAPES IT DECIDES, after one of its arguments
    /// met its parameter ([`report_walk_solutions`]). For each [`TupleShape`] whose variable this
    /// argument's unify decided — not `before`, whose bindings an earlier argument's unify made
    /// and may have made failing, as [`report_call_solutions`] reads them: the type must be a tuple
    /// of the pattern's width, and each component meets its binder — checked as an argument meets
    /// its parameter, and unified so that a binder's variable takes the component's type in this
    /// σ, which is what the call's result and the dispatches on that binder then read. To a fixed
    /// point, because a component that is itself a shape's variable is decided by the step before.
    ///
    /// A component meets the binder the pattern's LABELS place it at: the first use that labels the
    /// tuple fixes them ([`Self::agreed_labels`]), and a later one carrying the same labels in
    /// another order is met by name, as the run time reads it. One carrying other labels is
    /// refused (user, 2026-11-05): the pattern is the lambda's, and reads one set for every use.
    /// A positional tuple is met by position.
    ///
    /// `Err` is the call's refusal, at the call: a value of another width or no tuple where the
    /// pattern stands, a component its binder does not admit, or a tuple labelled otherwise than
    /// an earlier use labelled it.
    fn close_under_shapes(
        &mut self,
        kb: &mut KnowledgeBase,
        before: &Substitution,
        subst: &mut Substitution,
        site: ShapeSite,
    ) -> Result<(), TypeError> {
        if self.shapes.is_empty() {
            return Ok(());
        }
        let mut applied: Vec<bool> = self
            .shapes
            .iter()
            .map(|s| decided_type(kb, before, s.parent).is_some())
            .collect();
        loop {
            let mut progressed = false;
            for (k, shape) in self.shapes.iter().enumerate() {
                if applied[k] {
                    continue;
                }
                let Some(given) = decided_type(kb, subst, shape.parent) else {
                    continue;
                };
                applied[k] = true;
                progressed = true;
                let width = shape.components.len();
                let fields = named_tuple_field_pairs(kb, &given);
                if shape.refutable && fields.as_ref().is_some_and(|f| f.len() != width) {
                    continue;
                }
                let Some(fields) = fields.filter(|f| f.len() == width) else {
                    return Err(TypeError::TypeMismatch {
                        site: TypeError::here(),
                        span: site.span,
                        context: TypeErrorContext::PatternPosition {
                            pattern: WrittenPattern::Tuple,
                        },
                        expected: unsaid_tuple_of(kb, width),
                        quoted: None,
                        actual: given,
                    });
                };
                let labels: Vec<Symbol> = fields.iter().map(|(l, _)| *l).collect();
                // `at[i]`: the component binder `i` meets.
                let at: Vec<usize> =
                    if crate::eval::value::TupleComponents::labels_are_positional(kb, &labels) {
                        (0..width).collect()
                    } else {
                        let agreed = self
                            .agreed_labels
                            .iter()
                            .find(|(p, _)| Rc::ptr_eq(p, &shape.pattern))
                            .map(|(_, l)| Rc::clone(l));
                        match agreed {
                            None => {
                                self.agreed_labels
                                    .push((Rc::clone(&shape.pattern), labels.clone().into()));
                                (0..width).collect()
                            }
                            Some(agreed) => match agreed
                                .iter()
                                .map(|l| labels.iter().position(|m| m == l))
                                .collect::<Option<Vec<usize>>>()
                            {
                                Some(at) => at,
                                None => {
                                    let shown = |ls: &[Symbol]| {
                                        ls.iter()
                                            .map(|l| short_name_of(kb.local_name_of(*l)))
                                            .collect::<Vec<_>>()
                                            .join(", ")
                                    };
                                    return Err(TypeError::Other {
                                        site: TypeError::here(),
                                        span: site.span,
                                        context: TypeErrorContext::PatternPosition {
                                            pattern: WrittenPattern::Tuple,
                                        },
                                        expected: format!(
                                            "a tuple labelled `({})`, as another use hands this \
                                             pattern — a pattern reads one set of labels",
                                            shown(&agreed)
                                        ),
                                        actual: format!("a tuple labelled `({})`", shown(&labels)),
                                    });
                                }
                            },
                        }
                    };
                for (i, &c) in at.iter().enumerate() {
                    let (label, given_ty) = &fields[c];
                    let binder_ty = if shape.frozen {
                        shape.components[i].clone()
                    } else {
                        resolve_type_deep_value(kb, &self.solved, &shape.components[i])
                    };
                    let param = site.param.or(shape.binders[i]).unwrap_or(*label);
                    let context = TypeErrorContext::OperationArgument {
                        op_name: site.fn_sym,
                        param,
                    };
                    match validate_arg_against_param(
                        kb,
                        subst,
                        given_ty,
                        &binder_ty,
                        site.span,
                        context.clone(),
                        None,
                    ) {
                        ArgValidation::Ok => {}
                        ArgValidation::Fail(err) => return Err(err),
                        // A coercion inserts a `some(…)` around an ARGUMENT; a component of a
                        // value taken apart has no expression to wrap, so it is refused
                        // (kernel-language §6.7).
                        ArgValidation::WrapSome { .. } => {
                            return Err(TypeError::TypeMismatch {
                                site: TypeError::here(),
                                span: site.span,
                                context,
                                expected: binder_ty,
                                quoted: None,
                                actual: given_ty.clone(),
                            });
                        }
                    }
                    // The check above decided whether the component is admitted — by subtyping
                    // and the conversions, which equality would over-refuse (see
                    // [`validate_arg_against_param`]); this only BINDS, so its boolean says
                    // nothing more: a ground binder has nothing to bind, and a variable one is
                    // bound unless the occurs check refuses a component that holds the binder
                    // itself, which no value can be.
                    unify_types(kb, subst, given_ty, &binder_ty);
                }
            }
            if !progressed {
                return Ok(());
            }
        }
    }

    /// Hold a dispatch whose carrier is a lambda binder instead of deciding it — see
    /// [`DeferredSpecRequirement`] and [`DeferredCall`]. `class` is raised where no use
    /// gives the binder a type; `origin` maps each carrier to the variable of the call's
    /// σ its type is bound to.
    pub(super) fn defer_binder_dispatch(
        &mut self,
        occ: &Rc<NodeOccurrence>,
        carriers: SmallVec<[VarId; 2]>,
        origin: SmallVec<[(VarId, VarId); 2]>,
        class: CallClass,
        call: DeferredCall,
    ) {
        self.deferred.push(DeferredSpecRequirement {
            occ: Rc::clone(occ),
            carriers,
            class,
            generalized: false,
            instances: SmallVec::new(),
            call: Rc::new(call),
            origin,
            uses: Vec::new(),
            sites: Vec::new(),
            moved: SmallVec::new(),
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
            let spec_sort = self.deferred[i].call.spec_sort;
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
                // this walk has BOUND; this catches one a use has merely given a type, which
                // is the same evidence in the channel the discharge actually reads. Two tests
                // for one property is deliberate here: the guard whose absence produced a
                // wrong accept twice in this ticket is the one that gets the belt and the
                // braces.
                .filter(|v| !d.uses.iter().any(|(w, _)| w == v))
                .filter(|v| free.contains(v) && !env_free.contains(v))
                .collect();
            if moved.is_empty() {
                continue;
            }
            let Some(param) = spec_carrier_param_or_sole(kb, d.call.spec_sort) else {
                continue;
            };
            let base = kb.make_sort_ref(d.call.spec_sort);
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
            d.moved.extend(moved.iter().copied());
            let origin = moved.iter().map(|v| (*v, d.origin_of(*v))).collect();
            spawned.push(DeferredSpecRequirement {
                occ: Rc::clone(&d.occ),
                carriers: moved,
                class: d.class.clone(),
                generalized: true,
                instances: SmallVec::new(),
                call: Rc::clone(&d.call),
                origin,
                uses: Vec::new(),
                sites: Vec::new(),
                moved: SmallVec::new(),
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
    ///
    /// WI-20260904-34J8Z: AND COPIES THE TUPLE SHAPES the ∀ reaches — each that names one of its
    /// variables, as its parent or in a component — at the instance, so the use's σ, which
    /// decides the instance and not the quantified variable, is held to the pattern as an
    /// unquantified use is ([`TupleShape`]). Without it, `lambda p -> (let (a, b) = p  …
    /// Weigh.weigh(p) …)`, whose `p` the dispatch generalizes, was held to nothing at its use.
    pub(super) fn note_instantiation(
        &mut self,
        kb: &mut KnowledgeBase,
        binder_map: &[(VarId, VarId)],
        // WI-20260929-6NMGQ: the application that hands the lambda its dictionary at this
        // instance — the application itself, or the wrapper's for a reference handed on.
        site: &Rc<NodeOccurrence>,
    ) -> usize {
        self.instantiate_shapes(kb, binder_map);
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
                        let origin = d.origin_of(*old);
                        d.origin.push((*new, origin));
                        d.sites.push((*new, Rc::clone(site)));
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

    /// The shapes [`Self::note_instantiation`] copies at one ∀-elimination.
    fn instantiate_shapes(&mut self, kb: &mut KnowledgeBase, binder_map: &[(VarId, VarId)]) {
        if self.shapes.is_empty() || binder_map.is_empty() {
            return;
        }
        let mut at_instance = Substitution::new();
        for (old, new) in binder_map {
            at_instance.bind_value(kb, *old, Value::Var(Var::Global(*new)));
        }
        let quantified = |v: VarId| binder_map.iter().any(|(old, _)| *old == v);
        let mut copies: Vec<TupleShape> = Vec::new();
        for shape in &self.shapes {
            let mut named: Vec<VarId> = vec![shape.parent];
            let mut seen = HashSet::new();
            for c in &shape.components {
                collect_value_type_and_bare_vars(kb, c, &mut named, &mut seen);
            }
            if !named.into_iter().any(quantified) {
                continue;
            }
            let parent = binder_map
                .iter()
                .find(|(old, _)| *old == shape.parent)
                .map_or(shape.parent, |(_, new)| *new);
            copies.push(TupleShape {
                pattern: Rc::clone(&shape.pattern),
                parent,
                components: shape
                    .components
                    .iter()
                    .map(|c| walk_type_deep_value(kb, &at_instance, c))
                    .collect(),
                binders: shape.binders.clone(),
                frozen: shape.frozen,
                refutable: shape.refutable,
            });
        }
        self.shapes.extend(copies);
    }

    /// Record the type this call's σ gives each variable a deferred requirement watches
    /// ([`record_uses`]). Runs BEFORE [`report_call_solutions`]' first-wins filter, so a
    /// second use at a second type is seen though it never becomes a solution.
    fn observe_deferred_carriers(
        &mut self,
        kb: &mut KnowledgeBase,
        before: &Substitution,
        subst: &Substitution,
    ) {
        for d in &mut self.deferred {
            record_uses(kb, d, before, subst);
        }
    }

    /// THE DISCHARGE, run once when the walk ends: each call held on a lambda binder is
    /// decided by the types the walk's uses gave the binder (WI-20260929-6NMGQ,
    /// [`DeferredCall`]).
    ///
    ///  * The lambda was generalized: the call reads the slot of the lambda's requirement,
    ///    and each application hands the dictionary at the type it gives the parameter —
    ///    or forwards the slot an enclosing lambda is handed, where a rebinding put the
    ///    instance back into a quantified type.
    ///  * The parameter has one type: the call reads the dictionary at that type.
    ///  * No use gave the parameter a type: a call that covered a `requires` of the
    ///    enclosing declaration keeps that deferral; any other is refused as the dispatch
    ///    it is, unless the lambda was generalized and nothing applies it — its constraint
    ///    lives in its type, and whoever applies the value is asked then.
    ///
    /// A dictionary no route builds is the walk's refusal, raised where the call is.
    pub(super) fn discharge(self, kb: &mut KnowledgeBase) -> Result<(), TypeError> {
        let mut refusal: Option<TypeError> = None;
        let mut decided: Vec<*const NodeOccurrence> = Vec::new();
        for d in &self.deferred {
            let key = Rc::as_ptr(&d.occ);
            if decided.contains(&key) {
                continue;
            }
            decided.push(key);
            // The entries the call's binders spread to: a rebinding spawns one.
            let group: Vec<&DeferredSpecRequirement> = self
                .deferred
                .iter()
                .filter(|e| Rc::as_ptr(&e.occ) == key)
                .collect();
            if let Err(e) = self.decide_call(kb, &group) {
                refusal.get_or_insert(e);
            }
        }
        refusal.map_or(Ok(()), Err)
    }

    /// One held call, from the entries its binders spread to — the first is the call's own.
    fn decide_call(
        &self,
        kb: &mut KnowledgeBase,
        group: &[&DeferredSpecRequirement],
    ) -> Result<(), TypeError> {
        let own = group[0];
        let call = &own.call;
        let frame = DeferredFrame::of(kb, call)?;
        // Not generalized, or generalized and applied nowhere: the call is decided at the
        // types its carriers were given — evidence the walk saw is never discarded.
        if !own.generalized || group.iter().all(|d| d.sites.is_empty()) {
            let mut at: SmallVec<[(VarId, Value); 2]> = SmallVec::new();
            for c in &own.carriers {
                match self.one_type_of(kb, own, *c)? {
                    Some(ty) => at.push((own.origin_of(*c), ty)),
                    None => {
                        self.unanswered(kb, own);
                        return Ok(());
                    }
                }
            }
            let dict = lambda_requirement_dict(kb, call, &frame, &at, call.span)?;
            classify(kb, &own.occ, call.reads(dict));
            return Ok(());
        }
        let forward = build_req_var_ref(kb, &frame.syms, call.slot);
        for d in group {
            // One application instantiates every carrier of the entry at once.
            let mut sites: Vec<(Rc<NodeOccurrence>, SmallVec<[VarId; 2]>)> = Vec::new();
            for (v, site) in &d.sites {
                match sites.iter_mut().find(|(s, _)| Rc::ptr_eq(s, site)) {
                    Some((_, vars)) => vars.push(*v),
                    None => sites.push((Rc::clone(site), SmallVec::from_elem(*v, 1))),
                }
            }
            for (site, vars) in sites {
                if vars.iter().any(|v| d.moved.contains(v)) {
                    site.hand_closure_dict(call.slot, forward);
                    continue;
                }
                // An application that leaves the parameter open is asked at the open type:
                // one provider at every type answers it, and otherwise the refusal names the
                // open element. Reported at the application, whose type it is.
                let mut at: SmallVec<[(VarId, Value); 2]> = SmallVec::new();
                for v in &vars {
                    if let Some(ty) = self.one_type_of(kb, d, *v)? {
                        at.push((d.origin_of(*v), ty));
                    }
                }
                let dict = lambda_requirement_dict(kb, call, &frame, &at, Some(site.span.span))?;
                site.hand_closure_dict(call.slot, dict);
            }
        }
        classify(kb, &own.occ, call.reads(forward));
        Ok(())
    }

    /// A held call no use gave a type: its deferral to the enclosing declaration's
    /// `requires` where it had one; else, unless the lambda was generalized, the refusal
    /// of the dispatch — no evidence was seen, and nothing outside this walk can supply it.
    fn unanswered(&self, kb: &mut KnowledgeBase, d: &DeferredSpecRequirement) {
        if d.call.held || !d.generalized {
            classify(kb, &d.occ, d.class.clone());
        }
    }

    /// The type the walk's uses gave `var`, through what it solved since: `None` while none
    /// did, and a refusal where two uses gave it two ground types — one call cannot read
    /// two dictionaries. A type recorded while a part of it was still open yields to the
    /// ground one the part was solved to.
    fn one_type_of(
        &self,
        kb: &mut KnowledgeBase,
        d: &DeferredSpecRequirement,
        var: VarId,
    ) -> Result<Option<Value>, TypeError> {
        let mut found: Option<Value> = None;
        for (_, ty) in d.uses.iter().filter(|(w, _)| *w == var) {
            let ty = resolve_type_deep_value(kb, &self.solved, ty);
            match &found {
                None => found = Some(ty),
                Some(first) if views_structurally_equal(kb, first, &ty) => {}
                Some(first) => match (type_is_ground(kb, first), type_is_ground(kb, &ty)) {
                    (false, true) => found = Some(ty),
                    (true, true) => {
                        let first = type_display_name_value(kb, first);
                        let second = type_display_name_value(kb, &ty);
                        return Err(d.call.refusal(
                            d.call.span,
                            "one type for the lambda's parameter",
                            &format!(
                                "`{first}` at one use and `{second}` at another, and the call \
                                 reads one dictionary — write a lambda for each"
                            ),
                        ));
                    }
                    _ => {}
                },
            }
        }
        Ok(match found {
            Some(ty) => Some(ty),
            None => decided_type(kb, &self.solved, var),
        })
    }
}

impl DeferredCall {
    /// The call read through `dict`.
    fn reads(&self, dict: TermId) -> CallClass {
        CallClass::DeferToDictionary {
            spec_op_sym: self.fn_sym,
            op_short_sym: self.op_short_sym,
            dict,
        }
    }

    /// A refusal of the call, reported at `span`.
    pub(super) fn refusal(&self, span: Option<Span>, expected: &str, actual: &str) -> TypeError {
        TypeError::Other {
            site: TypeError::here(),
            span,
            context: TypeErrorContext::OperationAsFunctionValue {
                op_name: self.fn_sym,
            },
            expected: expected.to_string(),
            actual: actual.to_string(),
        }
    }
}

/// WI-20260929-6NMGQ — record `class`, a body call's deferral to a requirement of its
/// frame, or hold it where the call's element is a lambda's unannotated parameter not
/// solved yet ([`walk_minted_elements`]): an unsolved element matches every binding, so the
/// requirement covered it for nothing, and the call is decided by the parameter's uses
/// ([`DeferredCall`]).
#[allow(clippy::too_many_arguments)]
pub(super) fn classify_or_hold_deferral(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    occ: &Rc<NodeOccurrence>,
    subst: &Substitution,
    spec_sort: Symbol,
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
    class: CallClass,
    span: Option<Span>,
    solving: Option<&mut WalkSolutions>,
) {
    let Some(w) = solving else {
        return classify(kb, occ, class);
    };
    let held = walk_minted_elements(
        kb,
        subst,
        spec_sort,
        pos_results,
        named_results,
        w.watermark,
    );
    if held.is_empty() {
        return classify(kb, occ, class);
    }
    let CallClass::DeferToRequirement {
        spec_op_sym: fn_sym,
        ..
    } = class
    else {
        unreachable!("only a deferral to a requirement is held");
    };
    let mut carriers: SmallVec<[VarId; 2]> = SmallVec::new();
    let mut origin: SmallVec<[(VarId, VarId); 2]> = SmallVec::new();
    for (carrier, root) in &held {
        if !carriers.contains(carrier) {
            carriers.push(*carrier);
            origin.push((*carrier, *root));
        }
    }
    let serial = w.deferred.len();
    let call = DeferredCall::new(
        kb, env, subst, fn_sym, spec_sort, span, &carriers, serial, true,
    );
    w.defer_binder_dispatch(occ, carriers, origin, class, call);
}

impl DeferredSpecRequirement {
    /// The variable of the held call's σ `var` stands for ([`Self::origin`]).
    fn origin_of(&self, var: VarId) -> VarId {
        self.origin
            .iter()
            .find(|(w, _)| *w == var)
            .map_or(var, |(_, o)| *o)
    }
}

/// WI-20260929-6NMGQ — record the type this call's σ gives each variable an entry
/// watches: its carriers, and the instances that answer for them once the requirement has
/// moved into a type (a quantified carrier no σ can pin). ATTRIBUTABLE TO THIS UNIFY OR NOT
/// RECORDED: a variable `before` already decided was decided by an earlier argument, whose
/// own unify may have FAILED after binding it — `unify_types` never rolls back (see
/// [`report_walk_solutions`]). A variable the chain leaves unbound has no type yet.
fn record_uses(
    kb: &mut KnowledgeBase,
    d: &mut DeferredSpecRequirement,
    before: &Substitution,
    subst: &Substitution,
) {
    let watched: SmallVec<[VarId; 4]> = d
        .carriers
        .iter()
        .chain(d.instances.iter())
        .copied()
        .collect();
    for v in watched {
        if decided_type(kb, before, v).is_some() {
            continue;
        }
        let Some(ty) = decided_type(kb, subst, v) else {
            continue;
        };
        if !d
            .uses
            .iter()
            .any(|(w, t)| *w == v && views_structurally_equal(kb, t, &ty))
        {
            d.uses.push((v, ty));
        }
    }
}

/// The type `var` stands for under `subst`, or `None` while the chain ends at an unbound
/// variable. Read at the END of σ's chain of links ([`sigma_chain_end`]) and resolved through
/// it: a call's σ binds one variable to another before either reaches a type — `?param :=
/// ?T_callee`, `?T_callee := Int64` — and `Applier.ap(g, leaf())`, with `ap[X](fn:
/// Function[A = X, B = Int64], a: X)`, gives the closure's carrier `X` and `X` `Leaf`, two
/// links (WI-817).
fn decided_type(kb: &mut KnowledgeBase, subst: &Substitution, var: VarId) -> Option<Value> {
    let end = sigma_chain_end(kb, subst, var)?.clone();
    if kb.value_global_var(&end).is_some() {
        return None;
    }
    Some(walk_type_deep_value(kb, subst, &end))
}

/// WI-20260904-50B2K part (c) — does `carrier` supply `spec`? Asked through BOTH channels the
/// abstract-dispatch guard itself reads: a sort's own
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
/// [`DeferredSpecRequirement::uses`] is per-variable to prevent. Raised by /code-review
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

/// WI-20260929-6NMGQ — the variables this walk minted that a call's element stands at — a
/// lambda's unannotated parameter, solved by the lambda's uses and not yet where the call
/// is typed — each with the root of its class in σ, the variable a use's type is bound to
/// when the call's dictionary is built.
///
/// THE LINK RUNS EITHER WAY. Unifying the argument's type with the parameter's binds the
/// argument's variable to the spec parameter's (`?x := Store.State`) as readily as the
/// reverse, so a parameter σ leaves unbound is asked about too: the walk-minted variables
/// the call's argument types are stated at ([`walk_minted_carriers`]) whose chain ends at
/// it. A part of an element (`Buf[T = ?x]`) is not one: the element's sort is known, and a
/// provision at it fixes the part.
pub(super) fn walk_minted_elements(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
    watermark: u32,
) -> SmallVec<[(VarId, VarId); 2]> {
    let minted = walk_minted_carriers(kb, pos_results, named_results, watermark);
    let mut out: SmallVec<[(VarId, VarId); 2]> = SmallVec::new();
    for (_, vid) in spec_param_vars(kb, spec_sort) {
        let Some(root) = sigma_root(kb, subst, vid) else {
            continue;
        };
        if root.raw() >= watermark {
            out.push((root, root));
        }
        for m in &minted {
            if *m != root && sigma_root(kb, subst, *m) == Some(root) {
                out.push((*m, root));
            }
        }
    }
    out
}

/// The variable `var`'s chain of links in σ ends at — `var` itself when σ leaves it
/// unbound — or `None` when the chain ends at a type.
pub(super) fn sigma_root(kb: &KnowledgeBase, subst: &Substitution, var: VarId) -> Option<VarId> {
    match sigma_chain_end(kb, subst, var) {
        None => Some(var),
        Some(end) => kb.value_global_var(end),
    }
}

/// WI-20260904-50B2K part (c) — the one call an argument-unification site makes: OBSERVE
/// what this σ gives a deferred requirement's binders, then REPORT what it solved.
///
/// The order is load-bearing. [`report_call_solutions`] is first-wins, and observation
/// must see a second use's carrier even where the solving does not — see
/// [`DeferredSpecRequirement::uses`].
///
/// **`unified` GATES BOTH HALVES.** `unify_types` binds as it DESCENDS and never rolls
/// back, so a pair that agrees partway and then disagrees — `Function[A = Int64, B = String]`
/// against `?p -> ?p` binds `?p := Int64` before failing on `B` — leaves real bindings behind
/// on a unification that did NOT hold. For the observation half the consequence is a WRONG
/// DICTIONARY: [`WalkSolutions::discharge`] builds a call's dictionary at the type a use was
/// recorded at, so a type drawn from a failed unify would choose it on evidence the typer is
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
///
/// WI-20260904-34J8Z: AND FIRST THE σ IS HELD TO THE WALK'S TUPLE SHAPES
/// ([`WalkSolutions::close_under_shapes`]), so what a shape's binders take from this argument is
/// in σ before either half reads it — `Err` is the call's refusal, raised by the caller at the
/// call.
pub(super) fn report_walk_solutions(
    kb: &mut KnowledgeBase,
    solving: Option<&mut WalkSolutions>,
    before: &Substitution,
    subst: &mut Substitution,
    unified: bool,
    site: ShapeSite,
) -> Result<(), TypeError> {
    let Some(w) = solving else { return Ok(()) };
    if !unified {
        return Ok(());
    }
    root_callee_links_at_walk_vars(kb, before, subst, w.watermark);
    w.close_under_shapes(kb, before, subst, site)?;
    w.observe_deferred_carriers(kb, before, subst);
    report_call_solutions(kb, Some(&mut w.solved), before, subst, w.watermark);
    Ok(())
}

/// WI-20261105-MHF0B — where this argument's unify linked a walk variable to the callee's own
/// type variable, the link is turned round: `?x := ?T` becomes `?T := ?x`, so the class is rooted
/// at the walk's variable. The class is the same; what changes is the variable a later reading
/// of the call's σ lands on. `x * 10` binds `?x := ?T` at `x`; with `?T` the root, `10` then binds
/// `?T := Int64` and `?x` stays a link to a variable the walk may not keep (the callee's `T` is one
/// variable at every call site, [`report_call_solutions`]' first population), so the lambda's
/// arrow kept `?x` and `g("a")` loaded. With `?x` the root, `10` binds `?x := Int64`, which the
/// walk keeps. And a call whose result is the callee's variable — `a + b` over two binders —
/// answers `?a`, where it answered `?T` and each use of the lambda bound `?T` again in its own σ.
///
/// Only an unbound canonical type parameter's variable is turned round
/// ([`KnowledgeBase::is_canonical_type_param_var`]): any other variable older than the walk
/// — a rule variable's type, a fact pattern's — means the same thing outside the call, and a link
/// to it stays as unify made it. Only a link this argument made: one `before` holds was an earlier
/// argument's.
fn root_callee_links_at_walk_vars(
    kb: &mut KnowledgeBase,
    before: &Substitution,
    subst: &mut Substitution,
    watermark: u32,
) {
    let mut linked: Vec<VarId> = subst
        .iter()
        .filter(|(v, val)| {
            v.raw() >= watermark
                && kb.value_global_var(val).is_some()
                && before.resolve_as_value(**v).is_none()
        })
        .map(|(v, _)| *v)
        .collect();
    if linked.is_empty() {
        return;
    }
    // Mint order, as [`report_call_solutions`] reads its candidates: the first variable of a class
    // becomes its root, and the next one's chain then ends at it.
    linked.sort_by_key(|v| v.raw());
    for v in linked {
        let Some(root) = sigma_chain_end(kb, subst, v).and_then(|end| kb.value_global_var(end))
        else {
            continue;
        };
        // A chain that came back to a variable it passed ends at a bound one.
        if root.raw() >= watermark
            || !kb.is_canonical_type_param_var(root)
            || subst.resolve_as_value(root).is_some()
        {
            continue;
        }
        subst
            .take_own_binding(v)
            .expect("a binding read off this layer's own iterator");
        // A bare `Value::Var`: it interns nothing ([`KnowledgeBase::type_var_child`]), and a
        // reader of σ follows it on to what `v` is bound to.
        subst.bind_value(kb, root, Value::Var(Var::Global(v)));
    }
}

/// A positional tuple of `width` components nothing says, as a refusal shows the tuple a
/// pattern takes apart.
pub(super) fn unsaid_tuple_of(kb: &mut KnowledgeBase, width: usize) -> Value {
    let unsaid = kb.intern("?_");
    let shown: Vec<(Symbol, TermId)> = (0..width)
        .map(|i| (kb.intern(&positional_label(i)), kb.make_type_var(unsaid)))
        .collect();
    Value::term(kb.make_named_tuple_type(&shown))
}

/// WI-20260904-34J8Z — the call a [`report_walk_solutions`] reports for, which a refusal of a
/// tuple shape is raised at.
#[derive(Clone, Copy)]
pub(super) struct ShapeSite {
    pub(super) fn_sym: Symbol,
    /// The parameter the argument met, at a call of an operation by its name: a refusal there
    /// names it, as one of a lambda written at that slot does. `None` where a function value is
    /// applied, whose refusal names the binder of its pattern (`g.a`), as one of a binder of
    /// its list does.
    pub(super) param: Option<Symbol>,
    pub(super) span: Option<Span>,
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
///      `check_apply_iter`'s WI-374 note said what kept that sound — the parametricity tie
///      rode "the canonical channel AND THE PER-CALL SUBST" (the tie is gone since proposal
///      070's stage (e); the per-call σ still holds that variable) — and this copies out of
///      that σ. Measured in one walk: `var 1372 kept=String dropped=Int64`.
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
/// ONE THING THIS DOES NOT DO, named because it is unmeasured rather than absent:
///
///   * NO ROLLBACK. A report happens when an argument's unification finishes, which is
///     BEFORE the CALL is known to type: [`report_walk_solutions`] withholds a FAILED
///     argument unify's bindings, but a call whose arguments all unify and which then
///     returns `Err` for another reason still leaves its bindings behind. Combined with
///     first-wins, a speculative binding could outrank a later well-typed one. No corpus
///     program shows it; the scoped container below is what would remove the possibility.
///
/// AND THE CONTAINER IS STILL WALK-LIFETIME, WHICH IS NOT WHERE THIS BELONGS. Solutions
/// travelling WITH the result would scope to the body that produced them and make the gate
/// above unnecessary rather than merely correct — `check_apply_iter` already returns
/// `env: env.clone()` at fifteen of its return points, so the channel exists and is inert
/// (user, 2026-09-05; WI-502's `σ → (σ, residual C)` shape).
///
/// WI-20261105-MHF0B: A VALUE IS READ THROUGH THE CALL'S σ where it is not the walk's as it stands.
/// One unify can bind `?x := ?T` and `?T := Int64` both — an argument `(a: x, b: 10)` at a
/// parameter `(a: T, b: T)` — and the link was dropped with the callee's variable in it, where the type it
/// stands for is the walk's. Read through σ it is `Int64`, and kept; a reading that still names a
/// variable older than the walk is dropped as before. A link to the callee's variable that a LATER
/// argument decides is turned round before it is read ([`root_callee_links_at_walk_vars`]).
pub(super) fn report_call_solutions(
    kb: &mut KnowledgeBase,
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
    // Only the filters that do not read `out` can be batched: the watermark, `before` below, and
    // the walk-local reading. /code-review found it.
    //
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
    // is a no-op. A link to an older variable that a later argument decides does improve
    // in between, read through σ, and is still not reported: a link to a callee's variable
    // was turned round before it could be one ([`root_callee_links_at_walk_vars`]), and a
    // link to any other older variable is not the walk's to keep. Asked before a value is
    // read through σ, so nothing is resolved only to be skipped. /code-review found it, on
    // the pass after the doc claimed both halves were gated.
    let bound: Vec<(VarId, Value)> = subst
        .iter()
        .filter(|(v, _)| v.raw() >= watermark && before.resolve_as_value(**v).is_none())
        .map(|(v, val)| (*v, val.clone()))
        .collect();
    let mut candidates: Vec<(VarId, Value)> = Vec::with_capacity(bound.len());
    for (v, val) in bound {
        if value_vars_all_walk_local(kb, &val, watermark) {
            candidates.push((v, val));
            continue;
        }
        let read = resolve_type_deep_value(kb, subst, &val);
        if value_vars_all_walk_local(kb, &read, watermark) {
            candidates.push((v, read));
        }
    }
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
        if out.resolve_as_value(v).is_some() {
            continue;
        }
        // Two calls can contribute `?a := f(?b)` and `?b := g(?a)`, each acyclic and
        // walk-local on its own: the check follows what `out` has committed.
        if occurs_through(kb, out, v, &val) {
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

/// WI-20261105-MHF0B — does `ty` name a declared type parameter's own variable, at any depth
/// ([`KnowledgeBase::is_canonical_type_param_var`])? The variable is one at every call site, so a
/// type naming it is a callee's parameter type, read before a call's σ instantiates it.
pub(super) fn names_a_type_parameter_variable(kb: &KnowledgeBase, ty: &Value) -> bool {
    let mut vars: Vec<VarId> = Vec::new();
    let mut seen = HashSet::new();
    collect_value_type_and_bare_vars(kb, ty, &mut vars, &mut seen);
    vars.iter().any(|v| kb.is_canonical_type_param_var(*v))
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

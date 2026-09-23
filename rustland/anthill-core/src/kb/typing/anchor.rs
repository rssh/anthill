//! Rewriting `find_dictionary` goals and anchor grounding.

use super::*;

/// WI-1040 — one rewritten requirement goal plus the call it was grounded on.
pub(super) struct GroundedRequirement {
    /// The rewritten `find_dictionary(spec_base, op, args…[, out: ?d])` goal, or `None`
    /// when the requirement was RESOLVED AT LOAD and no goal is left to run —
    /// WI-20260909-QMFC5's check tier under a typed-head anchor. Dropping it rather than
    /// emitting an inert one matters: an anchor goal SUSPENDS while its carrier is
    /// unbound, so keeping it would make a clause DELAY on a question already answered.
    pub(super) goal: Option<Rc<NodeOccurrence>>,
    /// EVERY call this dictionary covers — each call to an operation of the spec
    /// itself, whose dispatch the dictionary decides. A `Vec`, not the witness
    /// alone: a clause may call the spec op more than once, and weaving only the
    /// one the witness scan happened to reach left the others folding the SPEC'S
    /// DEFAULT — a silent wrong answer in a clause that explicitly asked for the
    /// dictionary (`rule via(?x,?a,?b) :- require[Desc[T]], Desc.describe(?x,?a),
    /// Desc.describe(?x,?b)` answered `1` then `7`).
    ///
    /// Empty for the transitive / inherited witnesses, which ground the requirement
    /// through a DIFFERENT spec's carrier and so name no call this dictionary can be
    /// threaded into (see [`weave_covered_call`]).
    pub(super) covered_calls: Vec<(Rc<NodeOccurrence>, Symbol)>,
    /// WI-20260909-96ZTM, widened by WI-20260917-HRFR5 — did the WRITTEN BRACKET choose
    /// this grounding?
    ///
    /// Two `require`s on one spec are admitted ONLY where every one of them was, because
    /// otherwise nothing says which dictionary is which and they would bind whatever the
    /// scan reached first.
    ///
    /// IT USED TO BE SPELLED `anchored`, and that spelling was a PROXY that has stopped
    /// being exact. The anchor path was once the only place the bracket was read — it is
    /// what chose the head binding — so "did an anchor ground it" answered "did the
    /// bracket choose it" by coincidence of there being one such path. HRFR5 gives the
    /// DIRECT WITNESS scan the same ability: where the bracket names a carrier and
    /// exactly one candidate call's carrier argument statically names it, the bracket
    /// chose that witness as surely as it chooses a binding. Asking the proxy would now
    /// refuse a pair that IS attributed.
    pub(super) bracket_attributed: bool,
}

/// Rewrite one `find_dictionary(X)` goal (see [`record_find_dictionary_grounding`]).
pub(super) fn rewrite_find_dictionary_goal(
    kb: &KnowledgeBase,
    goal: &Rc<NodeOccurrence>,
    body_nodes: &[Rc<NodeOccurrence>],
    fd_sym: Symbol,
    rule_sym: Option<Symbol>,
    bounds: &[(u32, TermId)],
) -> Result<GroundedRequirement, TypeError> {
    let span = goal.span;
    let owner = goal.owner;
    let err = |expected: String, actual: String| TypeError::Other {
        site: TypeError::here(),
        span: Some(span.span),
        context: TypeErrorContext::Rule {
            name: rule_sym.unwrap_or(fd_sym),
            field: RuleField::Body,
        },
        expected,
        actual,
    };

    // The single argument X is the spec instance (`Eq[T]`); read its base sort.
    // WI-1040: `out` — the clause variable the dictionary BINDS to — rides as a
    // presence-optional NAMED arg, carried through this rewrite untouched. Present
    // iff the author wrote `require[X]` (the converter mints or takes the variable);
    // absent for `requires(X)`, which is the same relation read check-only.
    let (spec_arg, out_arg) = match goal.as_expr() {
        Some(Expr::Apply {
            pos_args,
            named_args,
            ..
        }) if pos_args.len() == 1 => (
            &pos_args[0],
            named_args
                .iter()
                .find(|(n, _)| kb.local_name_of(*n) == REQUIREMENT_OUT_LABEL)
                .map(|(n, v)| (*n, Rc::clone(v))),
        ),
        _ => {
            return Err(err(
                "find_dictionary(SpecInstance)".into(),
                "malformed guard goal".into(),
            ))
        }
    };
    let Some(spec_base) = occ_head_symbol(spec_arg) else {
        return Err(err(
            "a spec instance as the `requires` argument".into(),
            "an argument with no nominal spec head".into(),
        ));
    };
    let spec_canon = kb.canonical_sort_sym(spec_base);

    // A PROJECTED BRACKET TAKES THE ANCHOR PATH, AND TAKES IT FIRST.
    // See [`spec_arg_has_projection`] for the two defects this ordering closes. The
    // witness scans below cannot honour a projection — they ground from a covered call's
    // arguments, which name a different value entirely — so a bracket that writes one
    // either anchors or is refused, and never silently grounds somewhere else.
    if spec_arg_has_projection(kb, spec_arg) {
        return match anchor_grounding(
            kb, spec_arg, spec_base, spec_canon, bounds, span, owner, fd_sym, &out_arg, body_nodes,
            &err,
        ) {
            Some(result) => result,
            // No typed head binding at all: the projection's root cannot be a head
            // parameter of this clause, so there is nothing for it to project off.
            None => Err(err(
                format!(
                    "a TYPED head binding for the receiver this `{}` bracket projects off",
                    kb.local_name_of(spec_base),
                ),
                "this clause annotates no head parameter, so the projection has \
                 no receiver whose type could be read"
                    .into(),
            )),
        };
    }

    // Emit the rewritten guard `find_dictionary(spec_base, witness_op, arg…)` for a
    // chosen witness `functor` (`None` if the call is partial — some parameter
    // unprovided — so its arguments can't be positionalized the way the fire-time
    // carrier decision [`simp_guard_holds_core`] indexes them). Shared by both the
    // direct and the transitive witness scans below.
    let make_witness = |kb: &KnowledgeBase,
                        functor: Symbol,
                        pos_args: &[Rc<NodeOccurrence>],
                        named_args: &[(Symbol, Rc<NodeOccurrence>)]|
     -> Option<Rc<NodeOccurrence>> {
        let rec = crate::kb::op_info::lookup_operation_info(kb, functor)?;
        let args_in_order = align_call_args_to_params(kb, &rec.params, pos_args, named_args)?;
        let mut new_pos: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(2 + args_in_order.len());
        // WI-20260909-51W18 — THE SPEC INSTANCE RIDES WHOLE, not re-minted as a bare
        // `Expr::Ref(spec_base)`. Retaining the bracket at convert (§8.6) buys nothing if
        // the rewrite erases it one phase later: `require[Desc[T = Leaf]]` and
        // `require[Desc]` would still produce identical stored goals, which is exactly
        // the information loss this work exists to undo.
        //
        // TRANSPARENT TO EVERY READER OF THIS SLOT, because all of them ask for the HEAD
        // and an `Apply` answers it: `occ_head_symbol` (used by
        // `collect_find_dictionary_bases` and by this function's own caller) matches the
        // `Apply` arm, and the resolver's `builtin_find_dictionary` walks the argument and
        // takes `ViewHead::Functor { functor: Some(_) }`. A bare `require[Desc]` still
        // arrives here as the `Ref` it always was.
        new_pos.push(Rc::clone(spec_arg));
        new_pos.push(NodeOccurrence::new_expr(Expr::Ref(functor), span, owner));
        new_pos.extend(args_in_order);
        Some(NodeOccurrence::new_expr(
            Expr::Apply {
                recv_type: None,
                functor: fd_sym,
                pos_args: new_pos,
                // WI-1040: `out` survives the rewrite unchanged. The resolver arm
                // reads only POSITIONALS to decide the guard, so carrying the
                // output here cannot alter what the guard decides — it only says
                // where to put the dictionary once it has.
                named_args: out_arg.iter().map(|(n, v)| (*n, Rc::clone(v))).collect(),
                type_args: Vec::new(),
            },
            span,
            owner,
        ))
    };

    // Whole-body DFS for the first `Apply` whose functor passes `gate` AND exposes an
    // X-keyed carrier parameter (`op_has_spec_carrier_param`), rewritten to a
    // `find_dictionary` witness goal via `make_witness`. Shared by the transitive and
    // inherited scans below — they are identical but for `gate`. Children are pushed
    // BEFORE the node is examined, so a NESTED witness is reached: `member(?x, ?xs)`
    // inside the conjunct `eq(member(?x, ?xs), true)`. A functor failing either gate is
    // skipped; both scans returning `None` falls through to the loud "no witness" error
    // (honest that the requirement is ungroundable, never a dead/unsound guard).
    let scan_body_dfs = |gate: fn(&KnowledgeBase, Symbol, Symbol) -> bool,
                         covers: bool|
     -> Option<GroundedRequirement> {
        let mut stack: Vec<Rc<NodeOccurrence>> = body_nodes.iter().cloned().collect();
        while let Some(cand) = stack.pop() {
            let Some(expr) = cand.as_expr() else { continue };
            for_each_child(expr, |c| stack.push(Rc::clone(c)));
            let Expr::Apply {
                functor,
                pos_args,
                named_args,
                ..
            } = expr
            else {
                continue;
            };
            if *functor == fd_sym {
                continue;
            }
            if !gate(kb, *functor, spec_canon) {
                continue;
            }
            if !op_has_spec_carrier_param(kb, *functor, spec_canon) {
                continue;
            }
            if let Some(goal) = make_witness(kb, *functor, pos_args, named_args) {
                return Some(GroundedRequirement {
                    goal: Some(goal),
                    // The transitive / inherited / defaulted scans do NOT take the
                    // bracket into account: HRFR5 widened the DIRECT scan only, which is
                    // where a carrier argument names the spec's own carrier parameter.
                    bracket_attributed: false,
                    covered_calls: if covers {
                        collect_covered_calls(kb, body_nodes, spec_canon)
                    } else {
                        Vec::new()
                    },
                });
            }
        }
        None
    };

    // Find a DIRECT WITNESS: a body call to one of spec X's OWN operations. Its
    // carrier arguments (in the op's parameter order) decide the instance at fire
    // time.
    // WI-20260917-HRFR5 — THE CARRIER THE BRACKET WRITES, read once for the direct scan
    // below. `None` for a self-representing spec (its carrier is the sort, not a
    // parameter, so a bracket names no carrier there) and for every bracket that writes
    // nothing readable.
    let witness_carrier_param = if spec_is_self_representing(kb, spec_canon) {
        None
    } else {
        spec_carrier_param_or_sole(kb, spec_canon)
    };
    let written_carrier =
        witness_carrier_param.and_then(|p| written_carrier_sort(kb, spec_arg, p, spec_canon));

    // The candidates, in body order: a body call to one of spec X's OWN operations whose
    // arguments can ground the instance.
    let mut direct: Vec<usize> = Vec::new();
    for (i, cand) in body_nodes.iter().enumerate() {
        let Some(Expr::Apply { functor, .. }) = cand.as_expr() else {
            continue;
        };
        if *functor == fd_sym {
            continue; // don't treat a find_dictionary goal as its own witness
        }
        // The op must be a (body-less) spec op OF THIS spec, AND actually carry the
        // spec in a parameter — a nullary / all-content op (`Monoid.unit()`) never
        // grounds the instance from its arguments, so it is not a usable witness
        // (choosing it would make the guard permanently `DontFire`).
        match lookup_spec_op_dispatch(kb, *functor) {
            Some(parent) if kb.canonical_sort_sym(parent) == spec_canon => {}
            _ => continue,
        }
        if !op_has_spec_carrier_param(kb, *functor, spec_canon) {
            continue;
        }
        direct.push(i);
    }

    // WI-20260917-HRFR5 — THE WRITTEN BRACKET CHOOSES AMONG THEM, and this is the whole
    // of lifting the anchored gate on this path.
    //
    // A witness was picked by SCAN ORDER, which is why two `require`s on one spec both
    // landed on the first call and nothing could say which dictionary was which. Where
    // the bracket names a carrier and EXACTLY ONE candidate's carrier argument
    // statically names it, the bracket has chosen that call as surely as it chooses a
    // head binding on the anchor path — so it is put first and marked as chosen.
    //
    // EXACTLY ONE, never "the first that matches": two calls at one carrier are two
    // calls the same dictionary covers, and picking between THEM would be scan order
    // again, wearing the bracket's name.
    //
    // A CLAUSE THE BRACKET CANNOT SPEAK ABOUT IS UNTOUCHED: no written carrier, or no
    // candidate whose carrier is readable at load, leaves this list in body order and
    // `bracket_attributed` false — which is what keeps every clause that loads today
    // taking exactly the witness it takes today.
    let chosen: Option<usize> = written_carrier.and_then(|w| {
        let named: Vec<usize> = direct
            .iter()
            .copied()
            .filter(|i| match body_nodes[*i].as_expr() {
                Some(Expr::Apply {
                    functor,
                    pos_args,
                    named_args,
                    ..
                }) => call_names_carrier(kb, *functor, pos_args, named_args, spec_canon, bounds, w),
                _ => false,
            })
            .collect();
        (named.len() == 1).then(|| named[0])
    });
    let order: Vec<(usize, bool)> = chosen
        .into_iter()
        .map(|i| (i, true))
        .chain(
            direct
                .iter()
                .copied()
                .filter(|i| Some(*i) != chosen)
                .map(|i| (i, false)),
        )
        .collect();

    for (i, attributed) in order {
        let Some(Expr::Apply {
            functor,
            pos_args,
            named_args,
            ..
        }) = body_nodes[i].as_expr()
        else {
            continue;
        };
        if let Some(goal) = make_witness(kb, *functor, pos_args, named_args) {
            // A call to X's OWN operation is both the witness AND a call this
            // dictionary covers: its dispatch is exactly what the dictionary decides.
            let covered = collect_covered_calls(kb, body_nodes, spec_canon);
            return Ok(GroundedRequirement {
                goal: Some(goal),
                bracket_attributed: attributed,
                // A BRACKET THAT CHOSE ITS WITNESS ALSO NARROWS WHAT IT COVERS, or the
                // two dictionaries it just separated would be woven into each other's
                // calls one step later — the one-dictionary-per-call refusal fires and
                // the pair is refused after all. Narrowed only where the bracket chose,
                // so a single `require` keeps covering every call it covers today.
                // NOT NARROWED BY THE BRACKET, AND THAT WAS BUILT AND MEASURED AWAY.
                // A first cut filtered these to the calls whose carrier the bracket
                // names, on the argument that two dictionaries would otherwise be woven
                // into each other's calls. Backing that filter out failed ZERO rows,
                // including this ticket's own acceptance, and the reason is structural:
                // the filter can only engage where a carrier argument is READABLE, and
                // exactly there the call is VALUE-DIRECTED — a carrier-bearing spec op
                // dispatches on its argument, so which dictionary it carries decides
                // nothing. The weave decides dispatch only for a CARRIER-LESS op
                // (WI-20260909-NAR1X), which exposes no carrier argument to select on.
                // The two mechanisms are disjoint by construction.
                covered_calls: covered,
            });
        }
    }

    // Find a TRANSITIVE WITNESS (WI-625 gap 3 / WI-300 Tier B): no direct spec-op of
    // X appears in the body, but a body call to an operation that itself DECLARES
    // `requires X` grounds our requirement through the SAME carrier argument. This is
    // "rules use operations' `requires`": e.g. a rule's `requires(Eq[T])` is witnessed
    // by a call to `List.member` (`member(x: T, l: List) requires Eq[T]`) — member's
    // own element `Eq` obligation, discharged at the concrete element type of the
    // `member(?x, ?xs)` call, IS the rule's.
    //
    // Scanned only AFTER the direct scan finds nothing, so a body with a genuine
    // direct spec-op witness is unaffected. Two gates keep it sound:
    //   * `transitive_witness_grounds_soundly` — the op's `requires X[P]` must bind X
    //     over a type-param whose name matches X's own, so the fire-time guard reads
    //     the argument the op's requirement actually ranges over (not a name-coincident
    //     sibling parameter);
    //   * `op_has_spec_carrier_param` — the op must expose a carrier parameter the
    //     guard recognizes for X, else the emitted guard would be permanently
    //     `DontFire` (a silently-dead rule).
    // `covers: false` — the call GROUNDS X (its own `requires X` is discharged at
    // the same carrier) but is not a call to one of X's operations, so X's
    // dictionary does not decide its dispatch. Threading a dictionary INTO such a
    // callee is the §6 crossing, not this weave.
    if let Some(found) = scan_body_dfs(transitive_witness_grounds_soundly, false) {
        return Ok(found);
    }

    // Find an INHERITED-SPEC-OP WITNESS (WI-625 Direction A): no direct or transitive
    // witness appears, but a body call to an op of a spec `X` REQUIRES grounds the
    // requirement through the same carrier. `requires(Eq[T])` witnessed by `eq(?x, ?y)`
    // — post WI-644 `eq` is `PartialEq.eq` and `Eq requires PartialEq`, so `Eq` owns no
    // op of its own to serve as a direct witness. `requires(Ord[T])` via `gt`.
    //
    // Ord LAST, on purpose: for `has_elem` the body has BOTH `member` (a transitive
    // witness that grounds the ELEMENT type) AND `eq(member(…), true)` (an inherited
    // witness over Bool). The transitive scan runs first, so `member` wins — grounding
    // `requires(Eq[T])` at the element, not at the Bool the `eq` compares. Were this
    // scan first it would pick the Bool `eq` and check the wrong carrier.
    //
    // Like the DIRECT scan, an inherited witness grounds the requirement at the
    // COMPARISON's operand type — `eq(?x, ?y)` at `?x`'s type, `eq(f(?a), true)` at the
    // `Bool` result. This is exactly the behavior the direct scan had pre-WI-644, when
    // `eq` was `Eq`'s OWN op: an under-constrained `requires(Eq[T])` whose only
    // comparison is over `Bool` unifies `T` with `Bool` (a trivially-satisfiable, inert
    // guard) rather than erroring — consistent with the direct scan, not a silent
    // mis-decision. A rule that means to constrain a container ELEMENT should compare
    // elements (or use an op like `List.member` that DECLARES `requires Eq[T]`, caught
    // by the transitive scan first).
    // `covers: false` — the witness is an op of a spec X *requires* (`eq` for
    // `Eq`), so reaching its implementation from X's dictionary needs a projection
    // into a sub-slot; the value it grounds X at is still correct.
    if let Some(found) = scan_body_dfs(inherited_spec_op_witness_grounds_soundly, false) {
        return Ok(found);
    }

    // Find a DEFAULTED-SPEC-OP WITNESS. `lookup_spec_op_dispatch` — the DIRECT
    // scan's gate — answers only for a BODY-LESS spec op, so a call to a spec op
    // that carries a DEFAULT body (`operation describe(x: T) -> Int64 = 1`) was no
    // witness at all and its `requires`/`require` was rejected as ungroundable. It
    // grounds the instance exactly as the body-less sibling does: the carrier
    // parameter is declared with the spec's own type-parameter, so the argument's
    // carried type decides — which is why `op_has_spec_carrier_param` (shared with
    // every scan above) is the only other gate needed.
    //
    // ORDERED LAST, and that ordering is what makes it a zero-blast-radius
    // addition rather than a re-attribution: reaching here means all three scans
    // above found nothing, which until now was the hard error below. No rule that
    // loads today can change which witness it picks.
    if let Some(found) = scan_body_dfs(defaulted_spec_op_witness_grounds_soundly, true) {
        return Ok(found);
    }

    // THE SECOND ANCHOR — a TYPED HEAD BINDING (proposal 060 §3, WI-20260909-QMFC5).
    // Reached only when every witness scan above found nothing, so no clause that loads
    // today can change which witness it picks; and skipped entirely when the clause has
    // no bound, which is what keeps the UNTYPED twin refused exactly as before.
    if let Some(anchored) = anchor_grounding(
        kb, spec_arg, spec_base, spec_canon, bounds, span, owner, fd_sym, &out_arg, body_nodes,
        &err,
    ) {
        return anchored;
    }

    Err(err(
        format!(
            "a body call to one of `{}`'s operations (or to an operation that \
             `requires` it, directly or by spec inheritance) to ground the requirement",
            kb.local_name_of(spec_base)
        ),
        "no such call in the rule body".into(),
    ))
}

/// WI-20260909-S8CBV gate (1) — does this `require` bracket bind ANY of the spec's type
/// parameters to a PATH PROJECTION (`Desc[T = p.E]`)?
///
/// ASKED BEFORE THE WITNESS SCANS, and that ordering is the whole point. A witness grounds
/// the requirement from a COVERED CALL's arguments, which have nothing to do with the
/// receiver the author named — so a clause carrying both took the witness path, the
/// bracket was silently ignored, and the resolver's δ then rewrote the WITNESS's first
/// argument as though it were the projection root. MEASURED by `/code-review`:
/// `rule r(p: Box, ?q, ?res) :- ?d = require[Desc[T = p.E]], Desc.describe(?q, ?res)`
/// loaded clean and residualized where the same clause with a CONCRETE bracket answered a
/// definite `90`, and `require[Desc[T = p.Zork]]` beside a witness call escaped the
/// member check entirely. Both are one defect: the projection is only READ on the anchor
/// path, so a projected bracket must TAKE that path or be refused.
///
/// ANY binding, not the carrier parameter's: this asks "did the author write a projection
/// here", which is a question about the source and not about which slot it fills.
fn spec_arg_has_projection(kb: &KnowledgeBase, spec_arg: &Rc<NodeOccurrence>) -> bool {
    let Some(Expr::Apply { named_args, .. }) = spec_arg.as_expr() else {
        return false;
    };
    named_args.iter().any(|(_, v)| {
        matches!(
            v.as_expr(),
            Some(Expr::Apply { functor, .. })
                if kb.qualified_name_of(*functor) == "anthill.prelude.TypeExtractor.ExprCarried"
        )
    })
}

/// WI-20260909-S8CBV gate (1) — the De Bruijn index of the head binding a `require`
/// bracket's carrier PROJECTS OFF (`require[Desc[T = p.E]]` ⟹ `p`'s index), plus the
/// member it projects. `None` when the bracket names no projection, which is every
/// spelling that existed before this ticket.
///
/// THE ROOT IS THE ANCHOR, AND IT IS NOT TESTED FOR `provides`. That is the whole
/// difference from the concrete path and it is forced by what the two brackets MEAN:
/// `require[Desc[T = Box]]` says the carrier IS `Box`, so `Box` must provide `Desc`;
/// `require[Desc[T = p.E]]` says the carrier is `p`'s ELEMENT, about which the bound
/// `Box` says nothing at all. Asking `carrier_provides_spec(Box, Desc)` here is what
/// refused the shape before this ticket, with a message naming the wrong sort.
///
/// THE INDEX IS READ OFF A CLOSED OCCURRENCE. The loader lowers the projection as an
/// `Expr::Apply` over `ExprCarried` whose `value` child is an ordinary `Expr::Var`, so
/// the rule's own De Bruijn closing rewrites it; the index it leaves is directly
/// comparable with [`KnowledgeBase::rule_type_bounds`]' keys, which are produced by the
/// same reversal. A receiver that is still `Var(Global)` means the closing did not see
/// it — a loader bug, not a shape to tolerate — so it answers `None` and the clause
/// falls to the ordinary refusal rather than grounding on a variable nothing binds.
pub(super) fn written_projection_anchor(
    kb: &KnowledgeBase,
    spec_arg: &Rc<NodeOccurrence>,
    carrier_param: Symbol,
) -> Option<(u32, Symbol)> {
    let Some(Expr::Apply { named_args, .. }) = spec_arg.as_expr() else {
        return None;
    };
    let binding = named_args
        .iter()
        .find(|(k, _)| same_label(kb, *k, carrier_param))
        .map(|(_, v)| v)?;
    let Some(Expr::Apply {
        functor,
        named_args: proj_args,
        ..
    }) = binding.as_expr()
    else {
        return None;
    };
    if kb.qualified_name_of(*functor) != "anthill.prelude.TypeExtractor.ExprCarried" {
        return None;
    }
    let mut root = None;
    let mut member = None;
    for (k, v) in proj_args.iter() {
        match kb.local_name_of(*k) {
            "value" => {
                if let Some(Expr::Var(Var::DeBruijn(i))) = v.as_expr() {
                    root = Some(*i);
                }
            }
            "member" => {
                if let Some(Expr::Ref(m)) | Some(Expr::Ident(m)) = v.as_expr() {
                    member = Some(*m);
                }
            }
            _ => {}
        }
    }
    Some((root?, member?))
}

/// WI-20260909-QMFC5 — proposal 060 §3's SECOND ANCHOR: ground a clause's requirement
/// from a TYPED HEAD BINDING instead of from a covered body call.
///
/// `None` when the clause carries no bound at all — the caller then falls through to its
/// "no such call in the rule body" error, which is what keeps the UNTYPED twin refused and
/// makes that refusal the control saying the ANNOTATION is what grounds an anchored one.
/// `Some(Err(..))` for a clause that HAS bounds but none that anchors: a located refusal
/// of its own, because reporting the witness error there would say the author must add a
/// call when what they must fix is the bound.
///
/// # Why this is a second grounding PATH and not one added disjunct
///
/// The rewritten witness goal is `find_dictionary(spec, op_functor, witness_args…)`, and
/// every consumer below it is keyed on that `op_functor`: [`simp_guard_holds_core`] reads
/// the op's params to learn which arguments carry the spec (WI-596's two shapes), and
/// [`witness_sort_goal`] reads the same signature to learn which spec PARAMETER each
/// argument's carried type binds. A typed head has no op. So the emitted goal puts the
/// SPEC BASE where the op functor sits — a SORT, which is how the resolver tells the two
/// forms apart — and the carrier VALUE in the argument slot.
///
/// # The bound is TWO different things, and that is the discriminator
///
///   * a CONCRETE bound (`?x: Leaf`) records the CARRIER: test `sort_provides`;
///   * an INTRODUCER bound (`rule p[A](?x: A) :- Desc[A]`) records THE SPEC, because
///     `Loader::rule_head_bound_alias` substitutes `A` → `Desc` before `make_sort_ref`:
///     test `bound == spec`.
///
/// Two non-overlapping tests over one channel (`rule_type_bounds`).
///
/// # The bound is not the carrier VALUE
///
/// It is an UPPER bound — `bare_sort_compatible` admits the sort, its
/// `sort_sym_compatible` relatives, and anything that PROVIDES it — so it decides WHICH
/// head variable anchors the spec and never stands in for the carrier. A spec bound
/// differs from the carrier by design (the clause is polymorphic over the spec's
/// providers). That is why the emitted goal carries the VARIABLE and the carried type is
/// read at run time, exactly as the witness path reads its arguments'.
#[allow(clippy::too_many_arguments)]
pub(super) fn anchor_grounding(
    kb: &KnowledgeBase,
    spec_arg: &Rc<NodeOccurrence>,
    spec_base: Symbol,
    spec_canon: Symbol,
    bounds: &[(u32, TermId)],
    span: crate::span::SourceSpan,
    owner: Option<Symbol>,
    fd_sym: Symbol,
    out_arg: &Option<(Symbol, Rc<NodeOccurrence>)>,
    body_nodes: &[Rc<NodeOccurrence>],
    err: &dyn Fn(String, String) -> TypeError,
) -> Option<Result<GroundedRequirement, TypeError>> {
    if bounds.is_empty() {
        return None;
    }
    // WHICH head variable anchors this spec. The bound's own head symbol is read through
    // the shared `TermIdView` reader, so an APPLIED bound (`?x: List[T = Int64]`) answers
    // by its base exactly as a bare one does.
    // The spec's SHAPE facts, read before the anchor selection because the selection needs
    // the carrier parameter to read the written bracket. Branch order mirrors
    // `anchor_sort_goal`'s — self-representing FIRST — see the gate below.
    let spec_self_rep = spec_is_self_representing(kb, spec_canon);
    let carrier_param = if spec_self_rep {
        None
    } else {
        spec_carrier_param_or_sole(kb, spec_canon)
    };
    // WI-20260909-S8CBV gate (1) — THE PROJECTION ROUTE, taken before the `provides`
    // scan below because it asks a different question. See
    // [`written_projection_anchor`]: a projected carrier anchors on its ROOT, and the
    // root's own bound is not required to provide the spec.
    let projection_anchor = carrier_param.and_then(|p| written_projection_anchor(kb, spec_arg, p));
    let mut anchors: Vec<(u32, Symbol)> = Vec::new();
    let mut seen_bounds: Vec<Symbol> = Vec::new();
    for &(db_index, bound_tid) in bounds {
        let Some(bound_head) = sort_functor_of_view(kb, &TermIdView(bound_tid)) else {
            continue;
        };
        if !seen_bounds.contains(&bound_head) {
            seen_bounds.push(bound_head);
        }
        // `carrier_provides_spec`, not a bare `sort_provides` — see the twin gate in
        // [`anchor_guard`], which this must agree with or the clause loads and then
        // answers nothing (measured by `/code-review`, both directions).
        if kb.canonical_sort_sym(bound_head) == spec_canon
            || carrier_provides_spec(kb, bound_head, spec_canon)
        {
            anchors.push((db_index, bound_head));
        }
    }
    let names = |syms: &[Symbol]| {
        syms.iter()
            .map(|s| kb.local_name_of(*s).to_owned())
            .collect::<Vec<_>>()
            .join(", ")
    };
    // THE PROJECTION'S ROOT REPLACES THE WHOLE SELECTION. Not merged into `anchors`:
    // that list is "bounds that provide the spec", and a projection root belongs to it
    // for no such reason — folding it in would make the >1 refusal below count it
    // against bounds chosen by a different rule.
    if let Some((root_index, _member)) = projection_anchor {
        let Some(&(db_index, _)) = bounds.iter().find(|(i, _)| *i == root_index) else {
            // The projection's receiver is a variable this clause's HEAD does not bind
            // with a type — no type, so no member to read off it.
            //
            // NOT REACHABLE FROM ANY SURFACE TODAY, and that is recorded rather than
            // trusted: `Loader::try_require_spec_projection` resolves its root in
            // `rule_param_vars`, which holds ONLY annotated parameters and stages a bound
            // for every one it mints, so an unannotated root never becomes a projection at
            // all. MEASURED 2026-09-13 on `rule anchored(p: Box, q, ?r) :- ?d =
            // require[Desc[T = q.E]], …`: it is refused one phase earlier, by
            // WI-20260909-51W18's drop rule (`q.E` names neither a sort nor one of
            // `Desc`'s own type parameters) — driven by
            // [`a_projection_off_a_name_this_clause_does_not_bind_keeps_the_drop_rule_message`].
            //
            // KEPT AS A REFUSAL AND NOT AN `unreachable!` because what makes it
            // unreachable is a property of ANOTHER function in another file: widen that
            // lookup and this becomes the only thing between a projection and an anchor
            // grounded on a variable nothing binds. A located error is the right failure
            // for that; a panic in the loader is not.
            return Some(Err(err(
                format!(
                    "the `{}` this `require` projects off to be a TYPED head binding of \
                     this clause",
                    kb.local_name_of(spec_base),
                ),
                "its projection root is a clause parameter with no type annotation, so \
                 there is no type whose member could be read"
                    .to_owned(),
            )));
        };
        // The REAL bound is kept, not a sentinel: the two checks below that compare it
        // against the spec are switched off by `projection_anchor` explicitly, so nothing
        // depends on what this symbol happens to be.
        let bound_head = bounds
            .iter()
            .find(|(i, _)| *i == root_index)
            .and_then(|(_, t)| sort_functor_of_view(kb, &TermIdView(*t)))
            .unwrap_or(spec_base);
        // A MEMBER THE ROOT'S BOUND CANNOT HAVE IS A LOAD ERROR, not a run-time delay.
        //
        // MEASURED by `/code-review`: `require[Desc[T = p.Zork]]` under `p: Box` loaded
        // CLEAN and residualized with no diagnostic anywhere, while the typo one
        // character over — `require[Desc[T = Zork]]`, a bogus SORT — is a load error. The
        // rung that admits the projection validates only that the last segment is
        // Capitalized; the bound sort's declared parameters are right here in `bounds`
        // and nothing was asking them.
        //
        // The SUSPEND discipline below does not cover this and its own justification says
        // why: "the head variable may not be bound yet" is a RUN-TIME condition, and a
        // member the bound sort statically cannot declare is not waiting for anything.
        //
        // ONLY WHERE THE BOUND IS A DATA SORT, and that gate is §8.4's measured rule
        // rather than caution: a `provides` onto a constructor-declaring sort is refused
        // ("nothing is-a a data sort"), so no run-time carrier can be NARROWER than such
        // a bound and its declared parameters are the whole truth. A SPEC bound (the
        // introducer form) admits every provider, and a provider may declare members the
        // spec does not — so that shape keeps the delay.
        if let Some((_, member)) = projection_anchor {
            if kb.sort_has_constructors(bound_head) {
                let declared = kb.type_params_of_sort(bound_head);
                let member_name = kb.local_name_of(member).to_owned();
                if !declared.iter().any(|d| *d == member_name) {
                    return Some(Err(err(
                        format!(
                            "`{}` to name a type parameter of `{}`, which this \
                             `require` projects off",
                            member_name,
                            kb.local_name_of(bound_head),
                        ),
                        if declared.is_empty() {
                            format!("`{}` declares none", kb.local_name_of(bound_head))
                        } else {
                            format!(
                                "`{}` declares {}",
                                kb.local_name_of(bound_head),
                                declared.join(", "),
                            )
                        },
                    )));
                }
            }
        }
        anchors = vec![(db_index, bound_head)];
    }
    // ZERO. The clause annotated its head and the annotation does not reach this spec —
    // a fault in the BOUND, so say that rather than ask for a body call. Before this
    // existed the row was refused by the witness error, which is why the acceptance
    // control "a bound that does not provide stays refused" did not discriminate.
    if anchors.is_empty() {
        return Some(Err(err(
            format!(
                "a typed head binding whose bound provides `{}` (or is `{}` itself), \
                 or a body call to one of its operations",
                kb.local_name_of(spec_base),
                kb.local_name_of(spec_base),
            ),
            if seen_bounds.is_empty() {
                // Every bound term had no readable sort head (a tuple, an arrow, a bare
                // variable). `bounds` is non-empty — so this is not the untyped twin —
                // but there is no NAME to print, and "head bound(s) —  — provide no
                // `Desc`" is a sentence with a hole in it.
                format!(
                    "no head bound of this clause names a sort, so none can provide `{}`",
                    kb.local_name_of(spec_base),
                )
            } else {
                format!(
                    "this clause's head bound(s) — {} — provide no `{}`",
                    names(&seen_bounds),
                    kb.local_name_of(spec_base),
                )
            },
        )));
    }
    // MORE THAN ONE. Two anchors are TWO dictionaries (the implicit-parameter reading,
    // `060-implementation.md` §8.5), and choosing between them needs the written
    // bracket's attribution plus a carrier-directed weave. Refused loudly here rather
    // than picked, because picking would silently thread one carrier's dictionary into
    // the other's call. Owned by WI-20260909-96ZTM (S4).
    // NOT COLLAPSED — NOT EVEN FOR TWO BOUNDS THAT ARE BYTE-IDENTICAL. An earlier fix
    // in this ticket collapsed two anchors of one DATA sort into one dictionary, on the
    // argument that nothing can widen to a constructor-declaring sort so both carriers
    // ARE that sort at run time and select the same row. The first clause is true and the
    // second does not follow, and `/code-review` drove three separate counterexamples:
    //
    //   * a PARAMETERIZED data sort — `?x: Box[E = Leaf], ?y: Box[E = Other]` — collapses
    //     on the head symbol alone (`sort_functor_of_view` discards the arguments), and
    //     the conditional provision's sub-dictionary differs. The surviving `?d` is then
    //     woven into BOTH calls. This shape SHIPS: `pair`, `list` and `option` all have
    //     it;
    //   * two BARE, byte-identical `Wrap` bounds still diverge when the provision is
    //     conditional (`Wrap provides Sh[T = Wrap] :- Sh[A]`) — measured `?r = 7` one way
    //     and a residual the other, decided by nothing but which head variable was
    //     written first. So comparing the full bound TERMS does not rescue the collapse
    //     either: the predicate it needs is "the carriers are equal AT RUN TIME", which a
    //     load-time bound cannot answer;
    //   * the gate itself was source-order-dependent — `sort_has_constructors` reads
    //     `kind_of`, the FIRST-DECLARED category, so a `Leaf` with an `operation leaf()`
    //     declared above its `entity leaf` stopped being a data sort and the same clause
    //     was refused again. (That read is fixed below, but it is not what makes the
    //     collapse wrong.)
    //
    // SO THE REFUSAL STANDS, and `rule p(?x: Leaf, ?y: Leaf)` is refused with it. That is
    // a real cost and it is the right side to err on: a refusal is loud and names its
    // owner, where the collapse silently threaded one carrier's dictionary into the
    // other's call. Two anchors are TWO dictionaries (the implicit-parameter reading,
    // `060-implementation.md` §8.5) and the honest repair is one goal per anchor plus a
    // carrier-directed weave — which is exactly WI-20260909-96ZTM (S4), already filed.
    // MORE THAN ONE ANCHOR: THE WRITTEN BRACKET SAYS WHICH ONE THIS `require` MEANS.
    // `rule p(?x: Leaf, ?y: Other) :- ?d = require[Desc[T = Leaf]]` names `Leaf`, so `?x`
    // anchors and `?y` does not — the ticket's own "a written `require[Spec[P = <one of
    // the two bounds>]]` pre-binds the matching one", with S1's retention as the reader.
    //
    // MATCHED ON THE BOUND'S HEAD SYMBOL, and that is a real limit rather than an
    // oversight: two bounds of one parameterized sort at different instantiations
    // (`?x: Box[E = Leaf], ?y: Box[E = Other]`) both answer `Box`, so the bracket cannot
    // separate them and the refusal below still fires. Recorded, with its own row.
    if anchors.len() > 1 {
        if let Some(p) = carrier_param {
            if matches!(spec_arg.as_expr(), Some(Expr::Apply { .. })) {
                let written = written_carrier_sort(kb, spec_arg, p, spec_canon);
                if let Some(w) = written {
                    let wc = kb.canonical_sort_sym(w);
                    let matched: Vec<(u32, Symbol)> = anchors
                        .iter()
                        .copied()
                        .filter(|(_, b)| kb.canonical_sort_sym(*b) == wc)
                        .collect();
                    match matched.len() {
                        1 => anchors = matched,
                        // ZERO. The bracket names a sort that anchors NOTHING in this
                        // clause — a typo, almost always. Say that, rather than falling
                        // through to a refusal about the head-binding COUNT which never
                        // mentions the name the author got wrong.
                        0 => {
                            return Some(Err(err(
                                format!(
                                    "the written `{}[{} = ...]` to name one of this \
                                     clause's head bindings",
                                    kb.local_name_of(spec_base),
                                    kb.local_name_of(p),
                                ),
                                format!(
                                    "it names `{}`, which none of them binds — they bind {}",
                                    kb.local_name_of(w),
                                    names(&anchors.iter().map(|(_, s)| *s).collect::<Vec<_>>()),
                                ),
                            )));
                        }
                        // MORE THAN ONE anchor of the same sort — genuinely ambiguous,
                        // and the refusal below says so.
                        _ => {}
                    }
                }
            }
        }
    }
    // STILL more than one, so the bracket did not choose — it named nothing, named
    // something both bounds share, or named a head-introduced type VARIABLE, which
    // `rule_type_bounds` records by its BOUND and so cannot be matched back to a head
    // variable. That last one is the stated boundary; the others are genuine ambiguity.
    if anchors.len() > 1 {
        return Some(Err(err(
            format!(
                "one typed head binding anchoring `{}`",
                kb.local_name_of(spec_base)
            ),
            format!(
                "{} of them do — {} — and the written bracket names no one of them, so \
                 nothing says which dictionary this `require` is",
                anchors.len(),
                names(&anchors.iter().map(|(_, s)| *s).collect::<Vec<_>>()),
            ),
        )));
    }
    let (db_index, anchor_bound) = anchors[0];
    // WHICH PARAMETER THE CARRIER FILLS must be answerable, or the goal this would emit
    // could pin nothing and would delay for a reason no diagnostic names.
    // [`spec_carrier_param_or_sole`] answers `None` for exactly two shapes, and only one
    // of them is a fault: a SELF-REPRESENTING spec needs no parameter (the carrier is the
    // sort, and the goal's own carrier discriminant takes it), while a multi-parameter
    // spec with no receiving operation has no non-arbitrary answer at all. Told apart by
    // the same [`spec_is_self_representing`] reader that predicate's second rung is gated
    // on, so the two cannot drift.
    if !spec_self_rep && spec_carrier_param_or_sole(kb, spec_canon).is_none() {
        return Some(Err(err(
            format!(
                "a spec whose carrier parameter is identifiable — `{}` must declare an \
                 operation that receives on one of its type parameters, or have exactly one",
                kb.local_name_of(spec_base),
            ),
            format!(
                "`{}` declares neither, so a typed head binding cannot say which of its \
                 parameters the carrier fills",
                kb.local_name_of(spec_base),
            ),
        )));
    }
    // BRANCH ORDER MIRRORS THE EMITTER'S, and that is not a detail. [`anchor_sort_goal`]
    // asks `spec_is_self_representing` FIRST and only reaches
    // [`spec_carrier_param_or_sole`] in the other arm — so a self-representing spec pins
    // NO parameter no matter what that predicate would answer for it. Asking it here
    // unconditionally made the two gates disagree, and the first thing it did was refuse
    // `a_self_representing_spec_whose_provider_pins_a_sibling_concretely_delays`, a shape
    // the emitter handles by the carrier discriminant. The condition is written the same
    // way round in both places so a future edit to one is visible against the other.
    let bound_is_the_spec = kb.canonical_sort_sym(anchor_bound) == spec_canon;
    // ── THE SECOND GATE [`spec_carrier_param_or_sole`]'s OWN DOC DEMANDS ──────────────
    //
    // That predicate answers "which parameter an operation RECEIVES on", and its doc says
    // in as many words that this "is not by itself which parameter names the carrier" —
    // its own counterexample is `touch(c: Spec, x: P)`, which answers `P`. Until now this
    // site performed only a PRESENCE test (is the answer `Some`?) and never compared it
    // against anything, and I had recorded "no independent second gate" as a stated
    // boundary on the argument that the shape the doc warns about takes the
    // self-representing branch. `/code-review` falsified that by driving it:
    //
    //   sort Sp { sort C = ?; sort P = ?; operation touch(x: P) -> Int64; operation tag() }
    //   sort Leaf provides Sp[C = Leaf, P = Int64]
    //
    // `Sp` is NOT self-representing, so it sails past the presence test; the answer is
    // `P`, the received parameter, while the provisions carry the carrier in `C`. The
    // emitted goal pinned `P |-> Leaf`, matched no provider row, and the clause loaded
    // clean and answered a residual — where VVM1R's acceptance says such a spec "must
    // produce a LOCATED refusal naming the shape, never a silent non-grounding".
    //
    // THE CHECK IS AGAINST THE BOUND'S OWN PROVISION ROW, used as a CHECK and never as a
    // producer — deriving the parameter FROM the row would be circular, since the row is
    // what the emitted goal is meant to select. A provider binds the carrier parameter to
    // ITSELF (`Leaf provides Desc[T = Leaf]`), so the gate is "does the row bind the
    // parameter we are about to pin to the provider we are about to pin it for".
    //
    // SKIPPED IN TWO SHAPES, both because there is no row to read: a SELF-REPRESENTING
    // spec pins no parameter at all, and an INTRODUCER bound IS the spec (`?x: A` under
    // `:- Desc[A]`), which no sort declares a provision for.
    // THE CARRIER-PARAMETER AGREEMENT CHECKS BELOW DO NOT APPLY TO A PROJECTION, and
    // switching them off explicitly is what keeps the anchor list honest. Both compare
    // the WRITTEN carrier against the anchor's BOUND as sorts; a projected carrier is
    // neither — it is a member of that bound, and the two are equal only by accident.
    let sort_carrier_checks = projection_anchor.is_none();
    if let (Some(p), false, true) = (carrier_param, bound_is_the_spec, sort_carrier_checks) {
        let row = provides_rows_of_spec(kb, spec_canon)
            .find(|row| kb.canonical_sort_sym(row.provider) == kb.canonical_sort_sym(anchor_bound));
        if let Some(ProvidesRow { bindings, .. }) = row {
            let pins_the_carrier = bindings.iter().any(|(k, v)| {
                same_label(kb, *k, p)
                    && sort_functor_of_view(kb, &TermIdView(*v)).is_some_and(|h| {
                        kb.canonical_sort_sym(h) == kb.canonical_sort_sym(anchor_bound)
                    })
            });
            if !pins_the_carrier {
                let bound_to = bindings
                    .iter()
                    .find(|(k, _)| same_label(kb, *k, p))
                    .and_then(|(_, v)| sort_functor_of_view(kb, &TermIdView(*v)))
                    .map(|h| kb.local_name_of(h).to_owned())
                    .unwrap_or_else(|| "nothing".to_owned());
                return Some(Err(err(
                    format!(
                        "a spec whose carrier parameter is identifiable — `{}` must receive \
                         its carrier on the parameter its providers bind to themselves",
                        kb.local_name_of(spec_base),
                    ),
                    format!(
                        "`{}` receives on `{}`, but `{} provides {}[...]` binds `{}` to `{}` \
                         — so a typed head binding cannot say which of `{}`'s parameters the \
                         carrier fills",
                        kb.local_name_of(spec_base),
                        kb.local_name_of(p),
                        kb.local_name_of(anchor_bound),
                        kb.local_name_of(spec_base),
                        kb.local_name_of(p),
                        bound_to,
                        kb.local_name_of(spec_base),
                    ),
                )));
            }
        }
    }
    // ── THE WRITTEN BRACKET MUST AGREE WITH THE BOUND THE ANCHOR SELECTED ─────────────
    //
    // `rule anchored(?x: Leaf, ?r) :- ?d = require[Desc[T = Other]], ...` loaded clean and
    // answered `7` — `Leaf`'s dictionary — silently ignoring the author's explicit
    // `T = Other`. `060-implementation.md` §8.6 said "nothing decides that today because
    // nothing can"; S1's retention is what makes it possible, and this is the retention's
    // first real reader on the anchor path.
    //
    // ONLY A CONCRETE DISAGREEMENT IS REFUSED. A binding that named a type VARIABLE was
    // already dropped upstream as a wildcard (S1's rule), so anything still standing here
    // names a real sort; and a binding that AGREES is the ordinary spelling
    // (`require[Desc[T = Leaf]]` under `?x: Leaf`), which every acceptance row uses.
    if let (Some(p), false, true) = (carrier_param, bound_is_the_spec, sort_carrier_checks) {
        if let Some(Expr::Apply { named_args, .. }) = spec_arg.as_expr() {
            for (k, v) in named_args.iter() {
                if !same_label(kb, *k, p) {
                    continue;
                }
                let written = match v.as_expr() {
                    Some(Expr::Ref(s)) | Some(Expr::Ident(s)) => *s,
                    _ => continue,
                };
                if kb.canonical_sort_sym(written) != kb.canonical_sort_sym(anchor_bound) {
                    return Some(Err(err(
                        format!(
                            "the written `{}[{} = ...]` to name the same carrier the head \
                             binding anchors — `{}`",
                            kb.local_name_of(spec_base),
                            kb.local_name_of(p),
                            kb.local_name_of(anchor_bound),
                        ),
                        format!(
                            "it names `{}`, but this clause's head binding anchors `{}`, and \
                             the dictionary would be `{}`'s",
                            kb.local_name_of(written),
                            kb.local_name_of(anchor_bound),
                            kb.local_name_of(anchor_bound),
                        ),
                    )));
                }
            }
        }
    }
    // THE CHECK TIER EMITS THE SAME GOAL THE BIND TIER DOES — no `out:`, nothing else
    // different. `requires(X)` IS the no-`out` case of one relation (WI-1040), and the
    // cheapest way to keep the two spellings from answering differently is to give them
    // one producer and one consumer rather than a load-time twin of the runtime verdict.
    //
    // AN EARLIER DRAFT RESOLVED THIS TIER AT LOAD and returned `goal: None`, on the
    // argument that the anchor selection had already established the requirement so no
    // runtime question was left. `/code-review` falsified that argument three separate
    // ways, each measured on a program where the load-time verdict said SATISFIED and the
    // bind tier — the identical clause, one spelling apart — left a residual:
    //
    //   * a CONDITIONAL provision (`Wrap provides Sh[T = Wrap] :- Sh[A]`) is not decided
    //     by the bound: `Wrap[A = Bad]` provides nothing, and `sort_provides` is
    //     type-argument-blind, so the check tier answered the spec DEFAULT where the bind
    //     tier correctly declined;
    //   * `sort_refines` (the `requires` chain) admits a carrier through
    //     `bare_sort_compatible` that `sort_provides` never walks, so a refining sort that
    //     provides nothing discharged the requirement;
    //   * a WITNESS-SUPPLIED provision (`sort Rival provides Desc[T = Leaf]`) travels the
    //     `carrier_provided_by_witness` channel, which the bare `sort_provides` here is
    //     blind to.
    //
    // Each of the three has a different single-site repair and every one of them leaves
    // the other two open — which is the tell that the load-time verdict was the wrong
    // shape, not that its predicate needed widening. The runtime goal gets all three
    // right because it asks the question where the carrier's ACTUAL type is known.
    //
    // AND THE ARM COULD EMPTY A RULE BODY. `rule fe: f(?x: Leaf) <=> 1 :- requires(...)
    // @[simp]` has that goal as its ONLY body atom, so dropping it left `new_body == []`
    // and tripped `set_rule_body_nodes`'s fact-ness assert; with `debug_assertions` off
    // the rule silently became an UNCONDITIONAL law. No anchored equation-headed row
    // existed to catch it — `equation_headed_anchor_keeps_its_body` is now that row.
    //
    // THE STATED OBJECTION WAS ALSO WRONG. "Emitting a goal would make the clause DELAY
    // on something already decided" — the bind tier emits this same goal in this same
    // body position and resolves it by rotation, so there was never a delay to avoid.
    // THE EMITTED GOAL: `find_dictionary(spec_instance, spec_base, ?x[, out: ?d])`. Slot 1
    // holds the SPEC BASE where the witness form holds an OP FUNCTOR, and the resolver
    // tells the forms apart by asking whether that symbol is a SORT — a spec op is an
    // operation, so the two can never be confused, and no new kernel symbol is minted for
    // a discriminator the shapes already carry.
    let carrier = NodeOccurrence::new_expr(Expr::Var(Var::DeBruijn(db_index)), span, owner);
    let goal = NodeOccurrence::new_expr(
        Expr::Apply {
            recv_type: None,
            functor: fd_sym,
            pos_args: vec![
                // THE WRITTEN INSTANCE, not a re-minted `Expr::Ref(spec_base)`. Slot 0 is
                // where the retained bracket lives (WI-20260909-51W18), and re-minting it
                // here would erase it for every anchored clause — the same defect that
                // ticket had to fix in `make_witness`, one emitter over. Caught by
                // `wi_51w18…::a_head_introduced_type_variable_resolves_inside_the_bracket`
                // going from `[("T", "Desc")]` to `[]`.
                Rc::clone(spec_arg),
                // Slot 1 is the discriminant: a SORT here means the anchor form.
                NodeOccurrence::new_expr(Expr::Ref(spec_base), span, owner),
                carrier,
            ],
            named_args: out_arg.iter().map(|(n, v)| (*n, Rc::clone(v))).collect(),
            type_args: Vec::new(),
        },
        span,
        owner,
    );
    Some(Ok(GroundedRequirement {
        goal: Some(goal),
        // The dictionary this anchor grounds decides the dispatch of every call to the
        // spec's own operations in the clause — the same population the DIRECT witness
        // scan covers, and for the same reason.
        //
        // CARRIER-BLIND, AND THAT IS AN OPEN AXIS RATHER THAN A SETTLED ONE.
        // `collect_covered_calls` filters on the functor's parent spec, arity and
        // `classified_apply_target` — never on WHICH carrier the call names. So a clause
        // with one anchored bound and a second, UNBOUND variable of another provider
        // would weave the anchor's dictionary into that variable's call too, and the
        // `>1 anchors` refusal cannot see it because it counts BOUNDS. `/code-review`
        // could not drive it to a wrong value — the anchor path is only reachable when no
        // witness call exists, and the shapes left name no carrier to differ on — so it
        // is recorded here rather than claimed as fixed or as impossible. The
        // carrier-directed weave (WI-20260909-96ZTM) is what closes it.
        covered_calls: collect_covered_calls(kb, body_nodes, spec_canon),
        // THE ANCHOR PATH IS A BRACKET-CHOOSING PATH BY CONSTRUCTION: reading the
        // written bracket is what selected the head binding above.
        bracket_attributed: true,
    }))
}

/// WI-1040 — is `functor` an operation of spec `spec_canon` that carries a DEFAULT
/// body? The gate for [`rewrite_find_dictionary_goal`]'s last witness scan.
///
/// WI-1042 — asks [`defaulted_spec_op_parent`], the ONE owner of that question. It read
/// the body-AGNOSTIC [`spec_op_parent_sort`] and left the DEFAULT half to the caller's
/// scan order ("a body-less op was already taken by the direct scan"), which is the
/// prose-held coupling this ticket exists to delete: the predicate's NAME claimed a test
/// its body did not make, so a reordering of the scans above would have changed what it
/// means with nothing to notice.
///
/// NOT OBSERVABLE, and said plainly rather than dressed as a fix: if the scan order holds,
/// a body-less op never reaches here and the two readings agree — no test can distinguish
/// them, and none is claimed. What changes is the FAILURE MODE if the order ever stops
/// holding: the strict gate answers `false` and the caller falls through to its "no such
/// call in the rule body" error, instead of grounding the requirement on a witness whose
/// dispatch the dictionary cannot decide.
pub(super) fn defaulted_spec_op_witness_grounds_soundly(
    kb: &KnowledgeBase,
    functor: Symbol,
    spec_canon: Symbol,
) -> bool {
    defaulted_spec_op_parent(kb, functor)
        .is_some_and(|parent| kb.canonical_sort_sym(parent) == spec_canon)
}

/// The nominal head symbol of an occurrence in spec-instance / reference position
/// (`Eq[T]` → `Eq`, `Ref(Eq)` → `Eq`).
pub(super) fn occ_head_symbol(occ: &NodeOccurrence) -> Option<Symbol> {
    let expr = occ.as_expr()?;
    match expr {
        Expr::Ref(s) | Expr::Ident(s) => Some(*s),
        _ => expr_call_parts(expr).map(|(f, _, _)| f),
    }
}

/// WI-20260923-32XFQ — a functor-bearing expression as `(functor, positional, named)`: an
/// `Apply`, or a `Constructor` / `Instantiation`, the two forms a head takes when it was
/// MATERIALIZED from a term rather than lowered from source (`forall_impl` names no
/// operation; a spec-op head can come back a `Constructor`). The occurrence analogue of
/// `Term::Fn`, which carries all three the same way; `None` for every other form.
///
/// The one reading of those three shapes, which ten sites spelled as a two-arm `match`.
/// Only the DESTRUCTURE is shared: the walks around it keep their own order — two stack
/// walkers in `elaborate.rs` push in SOURCE order and the rest do not, and moving them to
/// one walker would reorder the diagnostics they emit.
#[allow(clippy::type_complexity)]
pub(super) fn expr_call_parts(
    expr: &Expr,
) -> Option<(
    Symbol,
    &[Rc<NodeOccurrence>],
    &[(Symbol, Rc<NodeOccurrence>)],
)> {
    match expr {
        Expr::Apply {
            functor,
            pos_args,
            named_args,
            ..
        } => Some((*functor, pos_args, named_args)),
        Expr::Constructor {
            name,
            pos_args,
            named_args,
            ..
        }
        | Expr::Instantiation {
            name,
            pos_args,
            named_args,
        } => Some((*name, pos_args, named_args)),
        _ => None,
    }
}

/// Reorder a spec-op call's arguments into the operation's declared parameter
/// order, so the resolver reads them at the same indices `simp_guard_holds_core`
/// consults. `None` if any parameter is unprovided (a partial call — not a usable
/// witness). Positional args map by index; a named arg maps by parameter name.
pub(super) fn align_call_args_to_params(
    kb: &KnowledgeBase,
    params: &[(Symbol, Value)],
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
) -> Option<Vec<Rc<NodeOccurrence>>> {
    let mut out: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(params.len());
    for (i, (pname, _pty)) in params.iter().enumerate() {
        if let Some(a) = pos_args.get(i) {
            out.push(a.clone());
        } else if let Some((_, a)) = named_args.iter().find(|(n, _)| same_label(kb, *n, *pname)) {
            out.push(a.clone());
        } else {
            return None;
        }
    }
    Some(out)
}

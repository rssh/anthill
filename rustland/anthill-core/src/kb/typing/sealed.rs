//! WI-20261010-9BKZ4 — A SEALED LOAD'S BODIES ARE TYPED ONCE: what a later load may not
//! do to them, and the instrument that says the typer skipped nothing it should have
//! typed.
//!
//! The typer's two whole-KB sweeps — every operation body no sort of the load owns
//! (`sorts::type_check_sorts_collect`), every rule body (`rules::type_rule_bodies`) —
//! skip what a seal holds ([`crate::kb::load::SealedDeclarations`]). MEASURED before
//! this, a copy of the loaded standard library and then a four-line file: 99 ms and
//! 11 ms of that 267 ms load were the two sweeps typing the library again.
//!
//! Typing a library body again was not only waste: it is how a later load REACHED INTO
//! one. Measured, a library file sealed with the standard library and then a program,
//! against one call over both (`wi_9bkz4_sealed_bodies_test`):
//!
//!   * a `@[simp]` rule the program wrote over a library operation REWROTE the library
//!     bodies calling it, in both orders — in the later load because the sweep typed
//!     them again;
//!   * a provision the program wrote for a library spec at library types, strictly more
//!     specific than the library's own, was selected by the library's call in one call
//!     and by NO call in two — not the library's, and not the program's own;
//!   * a provider and an override for a type of the program's own reached a generic
//!     library body the same way in both, through the dictionary its caller passes;
//!   * an operation added to a library scope under a name a library body reads was
//!     refused in both already (proposal 059 R4's capture rule).
//!
//! So the first two are REFUSED behind a seal (user, 2026-10-10), here; the third is
//! what must keep working and needs nothing; the fourth needed nothing either.

use super::*;

// ── The count ────────────────────────────────────────────────────────

thread_local! {
    /// Operation bodies and rule bodies the typer has typed on this thread.
    static BODIES_TYPED: std::cell::Cell<(usize, usize)> = const { std::cell::Cell::new((0, 0)) };
}

pub(super) enum BodyKind {
    Operation,
    Rule,
}

pub(super) fn count_body_typed(kind: BodyKind) {
    BODIES_TYPED.with(|c| {
        let (ops, rules) = c.get();
        c.set(match kind {
            BodyKind::Operation => (ops + 1, rules),
            BodyKind::Rule => (ops, rules + 1),
        });
    });
}

/// How many operation bodies and rule bodies the typer has typed ON THIS THREAD, ever
/// — `(operations, rules)`. An instrument for the one thing a result cannot show: that
/// a body was NOT typed. A test reads it before and after a load and asserts on the
/// difference (`wi_9bkz4_sealed_bodies_test`); a libtest thread runs one test.
pub fn bodies_typed_by_this_thread() -> (usize, usize) {
    BODIES_TYPED.with(|c| c.get())
}

// ── The oracle ───────────────────────────────────────────────────────

/// `ANTHILL_TYPER_ORACLE=1` — type the sealed bodies AS WELL, as every load did before
/// this ticket, and fail the typer run if doing so changed one or reported anything. A
/// TEST INSTRUMENT: the trap of a narrowed sweep is a body skipped that should have
/// been typed, which fails in silence and leaves the suite green, and this is the run
/// that would say so. Read once per typer run.
///
/// WHAT IT CANNOT SEE, so that a clean run is not read for more than it is: a stored
/// body holds no dot call (the typer resolved each when it typed the body), so typing
/// it again presents a later load's DOT RULE with nothing to fire on — that shape is
/// refused on its domain instead ([`simp_rules_that_reach_a_sealed_body`]); and it
/// compares WHICH supplier a call selected, not the terms a classification carries.
pub(super) fn oracle_on() -> bool {
    std::env::var("ANTHILL_TYPER_ORACLE")
        .map(|v| v == "1")
        .unwrap_or(false)
}

thread_local! {
    /// What the oracle found in the typer run in flight on this thread.
    static ORACLE_HITS: std::cell::RefCell<Vec<String>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// A new typer run: what an earlier one on this thread found is not this one's.
pub(super) fn oracle_reset() {
    ORACLE_HITS.with(|h| h.borrow_mut().clear());
}

fn oracle_hit(what: String) {
    ORACLE_HITS.with(|h| h.borrow_mut().push(what));
}

/// The oracle's verdict on the typer run that is ending. A run that REFUSED the KB for
/// changing sealed code is not judged: that refusal is the answer, and its shapes are
/// exactly ones the oracle also sees. Any other error does not excuse a finding — a
/// load refused for something else still changed a sealed body.
pub(super) fn oracle_verdict(refused_for_sealed_code: bool) {
    let hits = ORACLE_HITS.with(|h| std::mem::take(&mut *h.borrow_mut()));
    if !refused_for_sealed_code && !hits.is_empty() {
        panic!(
            "ANTHILL_TYPER_ORACLE: typing a SEALED body again gives something else, and \
             the typer no longer types sealed bodies — {} finding(s):\n  {}",
            hits.len(),
            hits.join("\n  ")
        );
    }
}

/// Every stamp the typer left under `root` that a later run could change the meaning
/// of, in walk order: each call's classification — which supplier it selected, down
/// its resolution tree — and its dictionary slots. NOT the inferred types, and not the
/// IDENTITY of a term or a variable inside a classification: a run mints its own rigids
/// and so its own terms for the same type, and two runs that agree differ in every one
/// (measured: one stdlib body, `FilteredStream.splitFirst`, in every later load). The
/// dictionary slots are compared as they are: they name providers, and were the same
/// across every load of the suite.
fn stamps_of(root: &Rc<NodeOccurrence>) -> String {
    use std::fmt::Write;
    let mut out = String::new();
    let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(root)];
    while let Some(o) = stack.pop() {
        if let NodeKind::Expr {
            classification,
            op_dicts,
            ..
        } = &o.kind
        {
            if let Some(c) = classification.borrow().as_ref() {
                let _ = write!(out, "{};", without_run_minted_ids(&format!("{c:?}")));
            }
            let dicts = op_dicts.borrow();
            if !dicts.is_empty() {
                let _ = write!(out, "{:?};", &*dicts);
            }
        }
        if let Some(e) = o.as_expr() {
            for_each_child(e, |c| stack.push(Rc::clone(c)));
        }
    }
    out
}

/// `rendered` with the number inside every `TermId(…)` and `VarId(…)` blanked.
fn without_run_minted_ids(rendered: &str) -> String {
    let mut out = String::with_capacity(rendered.len());
    let mut rest = rendered;
    loop {
        let next = ["TermId(", "VarId("]
            .iter()
            .filter_map(|tag| rest.find(tag).map(|at| at + tag.len()))
            .min();
        let Some(after_tag) = next else {
            out.push_str(rest);
            return out;
        };
        out.push_str(&rest[..after_tag]);
        out.push('_');
        rest = rest[after_tag..].trim_start_matches(|c: char| c.is_ascii_digit());
    }
}

/// Where two stamp renderings part, with a little of each side — enough to see WHICH
/// call changed and how.
fn first_difference(was: &str, now: &str) -> String {
    let at = was
        .char_indices()
        .zip(now.chars())
        .find(|((_, a), b)| a != b)
        .map(|((i, _), _)| i)
        .unwrap_or_else(|| was.len().min(now.len()));
    let from = (0..=at.saturating_sub(120))
        .rev()
        .find(|i| was.is_char_boundary(*i) && now.is_char_boundary(*i))
        .unwrap_or(0);
    let side = |s: &str| s[from..].chars().take(360).collect::<String>();
    format!("was `…{}`, is `…{}`", side(was), side(now))
}

/// The oracle's half of the free-operation sweep: type the SEALED operation bodies the
/// sweep skipped, and record each one that came out different or reported anything.
pub(super) fn oracle_type_sealed_operations(
    kb: &mut KnowledgeBase,
    sealed_ops: &[Symbol],
    region_sorts: &HashSet<Symbol>,
) {
    let before: Vec<(Symbol, Rc<NodeOccurrence>, String)> = sealed_ops
        .iter()
        .filter_map(|&op| {
            let body = Rc::clone(kb.op_body_node(op)?);
            let stamps = stamps_of(&body);
            Some((op, body, stamps))
        })
        .collect();
    let (errors, parked) = type_operation_bodies_aside(kb, sealed_ops, region_sorts);
    for e in &errors {
        oracle_hit(format!(
            "typing a sealed operation body again reported: {}",
            e.to_load_error(kb)
        ));
    }
    if parked > 0 {
        oracle_hit(format!(
            "typing the sealed operation bodies again parked {parked} requirement \
             refusal(s)"
        ));
    }
    for (op, body, stamps) in before {
        let name = kb.qualified_name_of(op).to_string();
        match kb.op_body_node(op) {
            Some(now) if !Rc::ptr_eq(now, &body) => {
                oracle_hit(format!("the body of sealed operation '{name}' was REWRITTEN"));
                // Put back, so that the check that REFUSES this shape, which runs next
                // and asks the same question, is asked it of the sealed body.
                kb.set_op_body_node(op, body);
            }
            Some(now) => {
                let after = stamps_of(now);
                if after != stamps {
                    oracle_hit(format!(
                        "a call in the body of sealed operation '{name}' was classified \
                         differently: {}",
                        first_difference(&stamps, &after)
                    ));
                }
            }
            None => oracle_hit(format!("the body of sealed operation '{name}' is gone")),
        }
    }
}

/// Type `ops`' bodies OUTSIDE the run's own sweep: what the pass reports comes back
/// instead of joining the run's errors, and what it parks for the end-of-typing report
/// (`dict::report_unsuppliable_requirements`) is taken off that queue and counted. The
/// other queue typing a body fills, the citation routes, is left to the run it is
/// called in, which settles it after the sweeps — so this is called from INSIDE a
/// typer run, above that point, and nowhere else.
fn type_operation_bodies_aside(
    kb: &mut KnowledgeBase,
    ops: &[Symbol],
    region_sorts: &HashSet<Symbol>,
) -> (Vec<TypeError>, usize) {
    let parked_before = kb.unsuppliable_requirements.len();
    let (mut errors, mut sources) = (Vec::new(), Vec::new());
    check_operation_bodies(kb, ops, &mut errors, &mut sources, region_sorts);
    let parked = kb.unsuppliable_requirements.len() - parked_before;
    kb.unsuppliable_requirements.truncate(parked_before);
    (errors, parked)
}

/// The oracle's half of the rule-body sweep, the same way.
pub(super) fn oracle_type_sealed_rules(kb: &mut KnowledgeBase, reportable: &HashSet<RuleId>) {
    let sealed: Vec<RuleId> = kb
        .live_rule_ids_iter()
        .filter(|&rid| !kb.is_fact(rid) && rule_body_is_typed_once(kb, rid))
        .collect();
    let stamps = |kb: &KnowledgeBase, rid: RuleId| -> Vec<String> {
        kb.rule_body_nodes(rid).iter().map(stamps_of).collect()
    };
    let before: Vec<(RuleId, Vec<String>)> =
        sealed.iter().map(|&rid| (rid, stamps(kb, rid))).collect();
    let (mut errors, mut sources) = (Vec::new(), Vec::new());
    type_rule_bodies(kb, reportable, RuleBodies::SealedOnly, &mut errors, &mut sources);
    for e in &errors {
        oracle_hit(format!(
            "typing a sealed rule body again reported: {}",
            e.to_load_error(kb)
        ));
    }
    for (rid, was) in before {
        if stamps(kb, rid) != was {
            let head = match kb.rule_head_value(rid) {
                Value::Term { id, .. } => kb.head_functor(*id),
                _ => None,
            };
            oracle_hit(format!(
                "a goal in the body of a sealed rule of '{}' was classified differently",
                head.map(|s| kb.qualified_name_of(s).to_string())
                    .unwrap_or_else(|| "?".to_string())
            ));
        }
    }
}

/// Which rule bodies one call of [`type_rule_bodies`] types.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum RuleBodies {
    /// Every rule a seal does not hold — the sweep.
    NotSealed,
    /// The sealed ones only — the oracle's half.
    SealedOnly,
}

/// The rule's body was typed by the sealed load that wrote it: its head is in a sealed
/// source whose load ran its typer. One with no recorded head site — a derived or a
/// host-asserted clause — is nobody's, and is typed.
pub(super) fn rule_body_is_typed_once(kb: &KnowledgeBase, rid: RuleId) -> bool {
    kb.rule_head_span(rid)
        .is_some_and(|head| kb.sealed.holds_typed_source(head))
}

/// The clause was in the KB when the seal was taken — of the KB the sealed bodies were
/// typed against, which a later clause is held to and not judged by.
fn clause_is_of_the_sealed_kb(kb: &KnowledgeBase, rid: RuleId) -> bool {
    kb.sealed.holds_rule_slot(rid.index())
}

// ── The refusals ─────────────────────────────────────────────────────
//
// BOTH READ THE KB, NOT THE LOAD: every `@[simp]` rule and every provision asserted
// since the seal was taken is judged at every typer run. A refused load does not unwind,
// so the rule or the provision it brought is still there for the next one — which would
// find it "earlier" and load clean over it had the checks read only what a load added.

/// A [`TypeError::ChangesSealedCode`] at `site`, pushed with its source beside it as
/// every tagging pass of the typer pushes.
fn refuse(
    message: String,
    site: Option<crate::span::SourceSpan>,
    errors: &mut Vec<TypeError>,
    sources: &mut Vec<Option<crate::span::SourceId>>,
) {
    errors.push(TypeError::ChangesSealedCode {
        span: site.map(|s| s.span),
        message,
    });
    sources.push(site.map(|s| s.source));
}

/// (1) A `@[simp]` RULE, NOT A SEALED LOAD'S, THAT REACHES A SEALED BODY.
///
/// A `@[simp]` equation fires where a body is TYPED, on the calls and constructions its
/// left-hand side matches, and the rewritten body is what runs. In one load over a
/// library and a program, a program's rule over a library operation therefore rewrites
/// the library bodies that call it; with the library sealed nothing types them again,
/// and the rule would silently not reach them. Refused, by asking the typer itself:
/// each sealed body that calls or constructs the head of such a rule is typed once
/// more, and one that comes back REWRITTEN — or that no longer types — is one the rule
/// reached.
///
/// Exact on purpose. "Its head is a sealed operation" would refuse the program that
/// declares `rule fact_monotonicity(Mine) <=> …` for its own sort, which the library
/// documents as the way to say it and which no library body calls; "some sealed body
/// calls the head" would refuse a rule over a library operation for an argument only
/// the program can write, which matches no library call.
///
/// A DOT RULE (`dot_apply(?e, member, …) <=> …`) cannot be asked that way: a stored
/// body holds no dot call any more. It is refused on its DOMAIN — a dot rule written
/// for a sealed sort's members is one a sealed body's dot calls were resolved without.
///
/// NOT REACHED, and said rather than hidden: a sealed load's own GUARDED equation
/// (`lhs = rhs :- g @[simp]`) fires where its guard is provable when a body is typed,
/// and a later load's FACTS can make it provable. One load of both rewrites the sealed
/// body; after the seal nothing does, and nothing here looks for it.
///
/// Called from INSIDE the typer run, after its free-operation sweep: the rules are
/// indexed, and what typing a body queues is drained by the run.
pub(super) fn simp_rules_that_reach_a_sealed_body(
    kb: &mut KnowledgeBase,
    region_sorts: &HashSet<Symbol>,
    errors: &mut Vec<TypeError>,
    sources: &mut Vec<Option<crate::span::SourceId>>,
) {
    if kb.sealed.is_empty() {
        return;
    }
    let dot_apply = crate::kb::simp_rewrite::dot_apply_head_sym(kb);
    // The rules, by the sealed operation or constructor their LHS is headed by.
    let mut by_head: HashMap<Symbol, Vec<RuleId>> = HashMap::new();
    let mut candidates = kb.simp_equation_rids();
    candidates.sort_by_key(|rid| rid.index());
    for rid in candidates {
        if kb.rules[rid.index()].retracted
            || !crate::kb::simp_rewrite::is_simp_equation(kb, rid)
            || clause_is_of_the_sealed_kb(kb, rid)
        {
            continue;
        }
        let Some(head) = crate::kb::simp_rewrite::stored_lhs_functor(kb, rid) else {
            continue;
        };
        if Some(head) == dot_apply {
            let domain = kb.rule_domain(rid);
            if kb.sealed.holds_sort(kb.canonical_sort_sym(domain)) {
                let message = format!(
                    "a `@[simp]` dot rule is written for '{}', which a sealed load \
                     declared: the dot calls in that load's bodies were resolved when it \
                     typed them, and its bodies are not typed again, so a dot rule \
                     loaded after it cannot reach them. Put the rule in the source that \
                     declares '{}', or write it for a sort of your own",
                    kb.qualified_name_of(domain),
                    kb.qualified_name_of(domain),
                );
                refuse(message, kb.rule_head_span(rid), errors, sources);
            }
            continue;
        }
        if kb.sealed.holds_operation(head) || kb.sealed.holds_sort(kb.canonical_sort_sym(head)) {
            by_head.entry(head).or_default().push(rid);
        }
    }
    if by_head.is_empty() {
        return;
    }
    // The sealed bodies that call or construct one of those heads, and which — in the
    // order of their symbols, the map they are read from having none.
    let mut callers: Vec<(Symbol, Rc<NodeOccurrence>, Vec<Symbol>)> = kb
        .op_bodies_iter()
        .filter(|(op, _)| kb.sealed.holds_operation(*op))
        .filter_map(|(op, body)| {
            let called = heads_reached(body, &by_head);
            (!called.is_empty()).then(|| (op, Rc::clone(body), called))
        })
        .collect();
    callers.sort_by_key(|(op, _, _)| op.index());
    for (op, body, called) in callers {
        // One at a time, so that what typing reports is this body's: a rule that makes
        // the body fail to type leaves it unwritten, and only the report says so.
        let (reported, parked) = type_operation_bodies_aside(kb, &[op], region_sorts);
        let rewritten = !kb.op_body_node(op).is_some_and(|now| Rc::ptr_eq(now, &body));
        if !rewritten && reported.is_empty() && parked == 0 {
            continue;
        }
        // The body goes back as the sealed load left it: the KB is refused.
        kb.set_op_body_node(op, body);
        let site = called
            .iter()
            .flat_map(|h| by_head[h].iter().copied())
            .find_map(|rid| kb.rule_head_span(rid));
        let heads: Vec<String> = called
            .iter()
            .map(|h| format!("'{}'", kb.qualified_name_of(*h)))
            .collect();
        let message = format!(
            "a `@[simp]` rule over {} {} the body of '{}', which a sealed load declared: \
             that operation's body was typed by the load that declared it and is not \
             typed again, so a rule loaded after it cannot be applied to it. Put the \
             rule in the source that declares '{}', or write it so that it matches only \
             calls of your own — over a type or a constructor that source cannot name",
            heads.join(", "),
            if rewritten { "rewrites" } else { "breaks" },
            kb.qualified_name_of(op),
            kb.qualified_name_of(op),
        );
        refuse(message, site, errors, sources);
    }
}

/// The members of `heads` that `body` calls or constructs.
fn heads_reached(body: &Rc<NodeOccurrence>, heads: &HashMap<Symbol, Vec<RuleId>>) -> Vec<Symbol> {
    let mut reached: Vec<Symbol> = Vec::new();
    let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(body)];
    while let Some(o) = stack.pop() {
        let Some(expr) = o.as_expr() else { continue };
        let head = match expr {
            Expr::Apply { functor, .. } | Expr::ApplyWithin { functor, .. } => Some(*functor),
            Expr::Constructor { name, .. } => Some(*name),
            _ => None,
        };
        if let Some(head) = head {
            if heads.contains_key(&head) && !reached.contains(&head) {
                reached.push(head);
            }
        }
        for_each_child(expr, |c| stack.push(Rc::clone(c)));
    }
    reached.sort_by_key(|s| s.index());
    reached
}

/// (2) A PROVISION, NOT A SEALED LOAD'S, THAT CHANGES WHO ANSWERS A SEALED DISPATCH.
///
/// An unselected dispatch is answered by the most specific provision, then by the
/// default (kernel-language.md §8.7, *Instance coherence*), over EVERY provision loaded
/// — "no declaration anywhere can invalidate a previously compiled call site, there
/// being none". A sealed body is one. So a provision is refused when ALL ITS ELEMENTS
/// ARE A SEALED LOAD'S — the spec, every type its head mentions (the loader has read
/// each alias as what it stands for), and its CARRIER where that is not in the head: a
/// self-representing
/// spec (`Stream`, `FiniteStream`) is dispatched by the receiver, so its carrier is the
/// provider. A goal a sealed body asks can name nothing else, so a provision with a
/// type of the program's own among them answers no such goal: it loads, and is reached
/// through the dictionary a generic body is passed. And one of:
///
///   * its PROVIDER is a sealed sort that already provides the spec at an overlapping
///     head — a provision put into a sealed sort beside its own. With nothing of the
///     later load's in it, it can only repeat that one or dispute it; or
///   * at its own head, the answer over the sealed provisions alone IS NOT the answer
///     over all of them: it is strictly more specific than the sealed one, or it ties
///     with it and no default arbitrates; or
///   * it OVERLAPS a sealed provision with neither the more specific
///     (`Desc[Pair[A = Leaf, B = B]]` beside `Desc[Pair[A = A, B = Leaf]]`): at the types
///     both describe, the one that answered alone would tie. Refused on the overlap
///     itself, without asking whether a default or a third provision would arbitrate
///     there — stricter than one load, which objects only at a call that meets the tie.
///
/// A second provider of a sealed spec for a sealed carrier that leaves the answer where
/// it was — `ByLength provides Ord[T = String]` beside `String`'s own — is the language's
/// named-instance feature and loads: a call selects it by name, and no sealed call does.
///
/// NOT REACHED: a type no source declares is in no seal, so a provision whose head
/// mentions one is taken for the program's.
///
/// Called at the END of the typer run, whose provision index it asks.
pub(super) fn provisions_that_change_a_sealed_dispatch(
    kb: &mut KnowledgeBase,
    errors: &mut Vec<TypeError>,
    sources: &mut Vec<Option<crate::span::SourceId>>,
) {
    if kb.sealed.is_empty() {
        return;
    }
    let Some(relation) = kb.try_resolve_symbol("anthill.reflect.SortProvidesInfo") else {
        return;
    };
    let mut rids = kb.rules_by_functor(relation);
    rids.sort_by_key(|rid| rid.index());
    let rows: Vec<ProvidesRow> = rids
        .into_iter()
        .filter(|rid| !clause_is_of_the_sealed_kb(kb, *rid))
        .filter_map(|rid| decode_provides_row(kb, rid, |_| true))
        .collect();
    let not_sealed: HashSet<RuleId> = rows.iter().map(|row| row.rid).collect();
    for row in rows {
        if !kb.sealed.holds_sort(kb.canonical_sort_sym(row.spec_base)) {
            continue;
        }
        // A CONVERSION — a spec of the program's providing the sealed one at its own
        // parameter, `sort Base { sort T = ?  provides Additive[T = T] }` — provides at
        // no type and is no candidate at any goal (WI-1110). Its head mentions no type
        // at all, so it would pass for a sealed load's and "overlap" every provision
        // the spec has (measured: `wi_n2865_provision_edge_scope_test`, three rows).
        if is_conversion_row(kb, &row) {
            continue;
        }
        let bindings = row.bindings(kb);
        // The spec's TYPE parameters: a provision also binds operations (`eq = ceq`),
        // and whose those are says nothing about which goals it answers.
        let type_params = kb.type_params_of_sort(row.spec_base);
        let mut elements: Vec<Symbol> = Vec::new();
        for (param, value) in &bindings {
            if type_params.iter().any(|n| n == kb.local_name_of(*param)) {
                type_heads(kb, value, &mut elements);
            }
        }
        let provider_is_sealed = kb.sealed.holds_sort(kb.canonical_sort_sym(row.provider));
        if spec_is_self_representing(kb, row.spec_base) && !provider_is_sealed {
            continue; // the carrier is the provider, and the provider is the program's
        }
        if elements
            .iter()
            .any(|s| !kb.sealed.holds_sort(kb.canonical_sort_sym(*s)))
        {
            continue;
        }
        let site = provision_site(kb, &row);
        let goal = SortGoal {
            spec_sort: row.spec_base,
            bindings,
            carrier: None,
        };
        // A provision put INTO a sealed sort beside one it already makes of this spec at
        // an overlapping head: the dispatcher reads the two as one candidate (WI-1032),
        // so the comparison below sees no change, while one load of both meets the tie
        // between their members at the sealed call (measured: `provides Desc[T = Leaf,
        // describe = other]` in a later `namespace …Leaf` — refused in one call, loaded
        // clean in two). NOT every later row a sealed sort is the provider of: a sort's
        // domain and its `Fillable` are derived for a library sort by the first load
        // that reads them, and those are rows where the sort provided nothing before.
        if provider_is_sealed {
            let restated = provides_rows_of_provider(kb, row.provider)
                .filter(|q| !not_sealed.contains(&q.rid))
                .filter(|q| same_sort_canonical(kb, q.spec_base, row.spec_base))
                .any(|q| heads_overlap(kb, &type_params, &goal.bindings, &q.bindings(kb)));
            if restated {
                let message = format!(
                    "this provision of {} is written for '{}', which a sealed load \
                     declared and which already provides it there: with nothing of a \
                     later load's in it, it can only repeat that provision or dispute \
                     it, and that sort's provisions are what the sealed load's bodies \
                     were typed against. Put it in the source that declares '{}'",
                    format_goal(kb, &goal),
                    kb.qualified_name_of(row.provider),
                    kb.qualified_name_of(row.provider),
                );
                refuse(message, site, errors, sources);
                continue;
            }
        }
        let candidates = collect_provides_candidates(kb, &goal, None);
        let answer = |kb: &KnowledgeBase, among: &[Candidate]| -> Option<Symbol> {
            pick_most_specific(kb, among)
                .or_else(|| default_among_candidates(kb, &goal, among))
                .map(|i| kb.canonical_sort_sym(among[i].impl_sort))
        };
        let now = answer(kb, &candidates);
        let sealed: Vec<Candidate> = candidates
            .into_iter()
            .filter(|c| !not_sealed.contains(&c.row))
            .collect();
        // The sealed provisions that are NOT candidates at this head — each at least as
        // specific somewhere — and overlap it without this one being a candidate at
        // theirs: neither is the more specific, and where both apply they tie. Not a
        // conversion, which is no candidate anywhere and whose bare parameter
        // "overlaps" everything.
        let at_this_head: Vec<RuleId> = sealed.iter().map(|c| c.row).collect();
        let others: Vec<ProvidesRow> = provides_rows_of_spec(kb, row.spec_base)
            .filter(|q| !not_sealed.contains(&q.rid) && !at_this_head.contains(&q.rid))
            .filter(|q| !is_conversion_row(kb, q))
            .collect();
        for other in others {
            let theirs = other.bindings(kb);
            if !heads_overlap(kb, &type_params, &goal.bindings, &theirs) {
                continue;
            }
            let their_goal = SortGoal {
                spec_sort: other.spec_base,
                bindings: theirs,
                carrier: None,
            };
            let more_general = collect_provides_candidates(kb, &their_goal, None)
                .iter()
                .any(|c| c.row == row.rid);
            if more_general {
                continue; // theirs is the more specific, and goes on answering
            }
            let message = format!(
                "this provision of {} overlaps the one '{}' makes at {}, which a sealed \
                 load declared, and neither is the more specific: at the types both \
                 describe the two would tie, where code of the sealed load was answered \
                 by '{}' alone. Its bodies were typed when it loaded and are not typed \
                 again. Put the provision in the source that declares them, or provide \
                 the spec for a type of your own",
                format_goal(kb, &goal),
                kb.qualified_name_of(other.provider),
                format_goal(kb, &their_goal),
                kb.qualified_name_of(other.provider),
            );
            refuse(message, site, errors, sources);
        }
        // No sealed provision answered here, or the sealed ones did not agree on an
        // answer: no sealed call site was given one, so there is none to change.
        let Some(was) = answer(kb, &sealed) else {
            continue;
        };
        if now == Some(was) {
            continue;
        }
        let message = format!(
            "this provision changes who answers {} in code a sealed load declared: there \
             it is '{}', and with this provision {}. The spec and every type in the \
             provision are a sealed load's, whose bodies were typed when it loaded and \
             are not typed again, so they would go on calling '{}' while code loaded \
             after them does not. Put the provision in the source that declares them; \
             or make '{}' a named instance a call selects (leave the sealed one the \
             default); or provide the spec for a type of your own",
            format_goal(kb, &goal),
            kb.qualified_name_of(was),
            match now {
                Some(p) => format!("it would be '{}'", kb.qualified_name_of(p)),
                None => "no single provider answers".to_string(),
            },
            kb.qualified_name_of(was),
            kb.qualified_name_of(row.provider),
        );
        refuse(message, site, errors, sources);
    }
}

/// Two provision heads describe some type in common: at each TYPE parameter of the spec
/// both bind, the two bindings overlap ([`carrier_views_overlap`], which errs toward
/// saying so); a parameter one of them leaves out is any.
fn heads_overlap(
    kb: &KnowledgeBase,
    type_params: &[String],
    mine: &[(Symbol, Value)],
    theirs: &[(Symbol, Value)],
) -> bool {
    mine.iter()
        .filter(|(k, _)| type_params.iter().any(|n| n == kb.local_name_of(*k)))
        .all(|(k, mine)| {
            theirs
                .iter()
                .find(|(q, _)| kb.local_name_of(*q) == kb.local_name_of(*k))
                .is_none_or(|(_, their)| carrier_views_overlap(kb, mine, their))
        })
}

/// Every type at a head in `ty`, at any depth, a type PARAMETER left out.
///
/// Not `display::mentioned_sort_syms`' filter, though it is its walk
/// ([`for_each_head_symbol`]): that keeps what the KB records as a sort, and a
/// free-standing entity — a type of its own — is not recorded as one, so a provision
/// for the program's `entity Foo` read as mentioning nothing and passed for a sealed
/// load's (measured: `PartialEq[T = test.persist_failure.Foo]`, a derived row).
///
/// AN ALIAS NEVER REACHES HERE: the loader reads a written type through it, so a head
/// written `Wrap[A = Blade]` over `sort Blade = Leaf` is stored at `Leaf`. Nothing here
/// resolves one, and `a_more_specific_provision_written_through_an_alias_is_refused`
/// is the row that fails the day a head arrives spelled by its alias.
fn type_heads<V: TermView>(kb: &KnowledgeBase, ty: &V, out: &mut Vec<Symbol>) {
    for_each_head_symbol(kb, ty, &mut |f| {
        if !is_sort_param_symbol(kb, f) {
            out.push(f);
        }
    });
}

/// Where a provision is written: the clause, else the view it wrote, else the provider —
/// a derived row has neither of the first two, and still has someone to point at.
fn provision_site(kb: &KnowledgeBase, row: &ProvidesRow) -> Option<crate::span::SourceSpan> {
    kb.rule_head_span(row.rid)
        .or_else(|| kb.term_span(row.spec_view))
        .or_else(|| kb.functor_span(row.provider))
}

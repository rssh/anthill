//! Per-predicate translation policy — lookup and lowering dispatch
//! (proposal 030 phase δ).
//!
//! Reads `TranslationPolicy(predicate, backend, policy)` facts from
//! the KB and resolves them at codegen time. A BODIED
//! `TranslationPolicy` rule anywhere in the KB is a hard error
//! (WI-772): this reader never evaluates guards, so lookups are
//! fallible rather than silently falling back. Per-backend defaults
//! kick in when no fact is present:
//!   - `LiftedAxiom` for predicates appearing in any `using` clause
//!     (mechanical: a citing proof needs the predicate's claim
//!     forall-quantified as a hypothesis, which is what LiftedAxiom
//!     emits).
//!   - `Inline` otherwise — preserves today's "always inline"
//!     behavior for predicates with no cite-side use.
//!
//! WI-781 wired this into the prove/emit path. Until then
//! `policy_for` had no production caller: `TranslationPolicy` facts
//! parsed and loaded but did not reach lowering, and the WI-772
//! bodied-policy refusal was unreachable outside unit tests. The
//! prove driver now consults [`render_cited_lemma_under_policy`] per
//! cite, so a policy fact observably changes the emitted document and
//! a bodied policy rule fails the proof through the CLI error channel.
//!
//! SCOPE: that is the CITE channel only. `Emitter::process_body_goal`
//! — which lowers a reference to a predicate inside a rule BODY —
//! still does not consult the policy, so a `TranslationPolicy` on a
//! predicate that is used but never cited remains inert. Routing that
//! is the rest of proposal 030 δ.4.

use std::collections::BTreeSet;

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::typing::get_named_arg;

use crate::{lift_rule_to_implication_clause, refuse_if_bodied, SmtGenError};

/// The backend identifier the z3 SMT path presents to policy lookup —
/// the `backend` field a `TranslationPolicy` fact must carry to apply
/// here, matching the name the schema documents
/// (`stdlib/anthill/realization/policy.anthill`).
///
/// A CONSTANT of the strategy, deliberately NOT derived from the
/// prove driver's `--solver` flag. That flag names the solver BINARY
/// ("Override for non-standard installs"), so `--solver /opt/z3/bin/z3`
/// would otherwise mint a backend name no fact could ever match — and
/// a policy lookup that silently never matches is exactly the defect
/// WI-781 exists to fix. `by z3(…)` is the backend; which binary runs
/// it is not.
pub const SMT_Z3_BACKEND: &str = "smt-z3";

/// One of the four lowering strategies the kernel currently
/// distinguishes (proposal 030 §Per-predicate translation policy).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PredicatePolicy {
    Inline,
    DefineFun,
    DeclareFun,
    LiftedAxiom,
}

/// Look up the explicit `TranslationPolicy(predicate, backend, ...)`
/// fact for a given predicate-and-backend pair, or fall back to the
/// inferred default.
///
/// `cited_predicates` is the set of predicate QNs that appear in
/// some proof's `using` clause across the project — used to drive
/// the LiftedAxiom default. The caller is responsible for collecting
/// this set. Note the CITE path does not come through here: it knows
/// its default and calls [`policy_for_with_default`]. This entry
/// point is for a caller asking about a predicate that may or may not
/// be cited — the body-goal call-site channel, still unrouted (see
/// the module header).
///
/// Errs on any BODIED `TranslationPolicy` rule in the KB (WI-772):
/// this reader head-matches facts and never evaluates a body, so a
/// guarded policy would otherwise silently fall back to the default.
pub fn policy_for(
    kb: &KnowledgeBase,
    predicate: &str,
    backend: &str,
    cited_predicates: &BTreeSet<String>,
) -> Result<PredicatePolicy, SmtGenError> {
    let inferred = if cited_predicates.contains(predicate) {
        PredicatePolicy::LiftedAxiom
    } else {
        PredicatePolicy::Inline
    };
    policy_for_with_default(kb, predicate, backend, inferred)
}

/// [`policy_for`] with the inferred default supplied directly.
///
/// For a caller that already KNOWS the default because of where it
/// stands. The cite path is the case in point: everything it asks
/// about is by definition cited, so the membership test in
/// [`policy_for`] would be unconditionally true and the set it
/// consults carries no information. Stating `LiftedAxiom` outright
/// says the same thing without building a set to encode it — and says
/// it in the one place a reader looks to find out what a cite
/// defaults to.
pub fn policy_for_with_default(
    kb: &KnowledgeBase,
    predicate: &str,
    backend: &str,
    default: PredicatePolicy,
) -> Result<PredicatePolicy, SmtGenError> {
    match lookup_explicit_policy(kb, predicate, backend)? {
        Some(p) => Ok(p),
        None => Ok(default),
    }
}

/// Render the hypothesis clauses a citing proof should splice for one
/// cited lemma, under that lemma's translation policy.
///
/// THE PRODUCTION ENTRY POINT for [`policy_for`] (WI-781). The prove
/// driver calls this once per cite instead of calling
/// [`lift_rule_to_implication_clause`] unconditionally.
///
/// Emits SMT-LIB, so `backend` selects WHICH policy row applies (an
/// `smt-cvc5` project reuses this renderer), not which language comes
/// out. A non-SMT backend needs its own renderer, not this one with a
/// different string.
///
/// `consumer_is_abstract` is the citing proof's `abstract_body` — see
/// the `Inline` arm, which is the only one that depends on it.
///
/// The four arms:
///
///  * `LiftedAxiom` — [`lift_rule_to_implication_clause`], today's
///    behavior and the default for anything cited. So absent an
///    explicit fact this arm always wins and the emitted document is
///    byte-identical to pre-WI-781.
///  * `Inline` — no separate hypothesis, because the policy means
///    "inline the body at every call site; the predicate symbol
///    disappears from the emitted document" (schema, `policy.anthill`).
///    Where the consumer's body references the predicate, the
///    consumer's own emission inlines it and the cite is redundant.
///    ONLY sound when the consumer actually inlines: under
///    `abstract_body` the emitter short-circuits every rule call
///    without descending (`process_body_goal`), so nothing is inlined
///    ANYWHERE and an `Inline` cite would contribute nothing while
///    appearing to have been honoured. That combination is refused
///    below rather than silently dropped — it is unsatisfiable as
///    stated, not merely unhelpful, and structured proofs run
///    abstract precisely BECAUSE they rely on the cited lifts.
///  * `DefineFun` / `DeclareFun` — refused loudly. Both need emission
///    that does not exist yet (a `define-fun` body render and an
///    uninterpreted `declare-fun` with typed args); silently falling
///    back to the lift would discharge the proof under a policy the
///    author did not ask for, which is precisely the confusion this
///    wiring removes.
///
/// Where a clause IS dropped legitimately (`Inline`, concrete
/// consumer), that is the SAFE direction: assumptions are conjoined
/// with the negated goal and `unsat` means proved, so a missing
/// hypothesis can only lose an `unsat` — the proof FAILS rather than
/// passing on a premise it never stated.
///
/// Errs on a bodied `TranslationPolicy` rule (WI-772).
pub fn render_cited_lemma_under_policy(
    kb: &KnowledgeBase,
    cited: &str,
    backend: &str,
    consumer_is_abstract: bool,
) -> Result<Vec<String>, SmtGenError> {
    // A cite is cited — that IS the default, stated rather than
    // rediscovered from a set membership that could only be true.
    let policy =
        policy_for_with_default(kb, cited, backend, PredicatePolicy::LiftedAxiom)?;
    match policy {
        PredicatePolicy::LiftedAxiom => lift_rule_to_implication_clause(kb, cited),
        PredicatePolicy::Inline if consumer_is_abstract => Err(SmtGenError::new(format!(
            "TranslationPolicy for `{cited}` (backend `{backend}`) selects Inline, \
             but the citing proof is emitted ABSTRACTLY — its body's rule calls are \
             not descended into, so there is no call site for the body to be inlined \
             at and the citation would contribute nothing at all. Structured proofs \
             emit abstractly because they depend on their cited lifts, so this would \
             quietly remove the hypothesis the proof rests on. Use LiftedAxiom (the \
             default for a cited predicate), or drop the `using` clause if the lemma \
             really is not needed."
        ))),
        PredicatePolicy::Inline => Ok(Vec::new()),
        unsupported @ (PredicatePolicy::DefineFun | PredicatePolicy::DeclareFun) => {
            Err(SmtGenError::new(format!(
                "TranslationPolicy for `{cited}` (backend `{backend}`) selects \
                 {unsupported:?}, which that backend's emitter does not implement \
                 yet — only Inline and LiftedAxiom are lowered today. Change the \
                 policy fact to LiftedAxiom (the default for a cited predicate) \
                 or Inline, or drop the fact to take the default. Refusing rather \
                 than falling back to LiftedAxiom, which would prove the goal \
                 under a policy you did not ask for."
            )))
        }
    }
}

/// Walk `TranslationPolicy` facts looking for an exact (predicate,
/// backend) match. Returns the first found policy, or None if no
/// such fact exists. Any bodied candidate is refused loudly (WI-772)
/// in a pre-scan over ALL candidates — before predicate/backend
/// matching, since a bodied rule's head fields may be variables that
/// would match anything, and before the match walk's early return, so
/// a matching fact sitting ahead of the bodied rule in the candidate
/// list (insertion order — source/file-load order) cannot hide it.
fn lookup_explicit_policy(
    kb: &KnowledgeBase,
    predicate: &str,
    backend: &str,
) -> Result<Option<PredicatePolicy>, SmtGenError> {
    let Some(policy_sym) = kb.try_resolve_symbol(
        "anthill.realization.policy.TranslationPolicy"
    ) else {
        return Ok(None);
    };
    let candidates = kb.rules_by_functor(policy_sym);
    for &rid in &candidates {
        refuse_if_bodied(
            kb,
            rid,
            "TranslationPolicy rule",
            "a guarded policy would silently fall back to the \
             per-backend default",
        )?;
    }
    for rid in candidates {
        let head = kb.rule_head(rid);
        let named = match kb.get_term(head) {
            Term::Fn { named_args, .. } => named_args,
            _ => continue,
        };
        // Skip malformed records (non-string `predicate` / `backend`
        // fields) — only user-asserted policy facts are matched.
        // (WI-515: the synthetic schema-declaration fact this filter
        // also used to exclude is no longer asserted.)
        let pred = match read_string_field(kb, named, "predicate") {
            Some(s) => s, None => continue,
        };
        let bk = match read_string_field(kb, named, "backend") {
            Some(s) => s, None => continue,
        };
        if pred != predicate || bk != backend { continue; }
        let policy_tid = match get_named_arg(kb, named, "policy") {
            Some(t) => t, None => continue,
        };
        if let Some(p) = decode_policy_term(kb, policy_tid) {
            return Ok(Some(p));
        }
    }
    Ok(None)
}

fn decode_policy_term(kb: &KnowledgeBase, tid: TermId) -> Option<PredicatePolicy> {
    let functor = match kb.get_term(tid) {
        Term::Fn { functor, .. } => *functor,
        Term::Ref(s) | Term::Ident(s) => *s,
        _ => return None,
    };
    let qn = kb.qualified_name_of(functor);
    let short = qn.rsplit('.').next().unwrap_or(qn);
    match short {
        "Inline" => Some(PredicatePolicy::Inline),
        "DefineFun" => Some(PredicatePolicy::DefineFun),
        "DeclareFun" => Some(PredicatePolicy::DeclareFun),
        "LiftedAxiom" => Some(PredicatePolicy::LiftedAxiom),
        _ => None,
    }
}

fn read_string_field(
    kb: &KnowledgeBase,
    named: &smallvec::SmallVec<[(anthill_core::intern::Symbol, TermId); 2]>,
    key: &str,
) -> Option<String> {
    let tid = get_named_arg(kb, named, key)?;
    if let Term::Const(Literal::String(s)) = kb.get_term(tid) {
        Some(s.clone())
    } else {
        None
    }
}

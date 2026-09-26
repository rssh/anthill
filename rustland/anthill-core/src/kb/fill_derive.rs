//! WI-20260925-SHED7 (proposal 060 §2.3, proposal 067) — derive every sort's `SortDomain`:
//! the relation its `fill` runs, `<Sort>.domain`, PER ENTITY and PER FIELD.
//!
//! ```text
//! List provides SortDomain[T = List[T = T]] :- SortDomain[T = T]        -- the row
//! List.domain(?x) :- find_dictionary(SortDomain, SortDomain, ?x, out: ?self),
//!                    ( ?x <=> nil()
//!                    | ?x <=> cons(head: ?h, tail: ?t),
//!                      apply_domain(?self, ?t),                        -- the tail first
//!                      apply_domain(__domain_sub(?self, 0), ?h) )     -- then the head
//! ```
//!
//! **EACH FIELD'S TYPE DECIDES HOW IT IS FILLED** (060 §2.3's table): the sort itself is the
//! recursion, through the same dictionary; a type PARAMETER is filled through the
//! sub-dictionary its CONDITION places (the provision is conditional on it); a CONCRETE type
//! is filled through its own `SortDomain` — and the sort has one only if every field of every
//! entity can be filled. So the conditions are PER FIELD, not per parameter: `SortedSet`'s
//! `O`, which no field fills, is no condition.
//!
//! **THE ORDER IS SEMANTIC, two rules, both WI-743's measurements**: the cases with no
//! recursive field first (`nil` before `cons` — `combine` is ordered concatenation, 067 §2,
//! and an infinite first operand starves the second), and inside a case the recursive fields
//! first (`tail` before `head` — head first, a free list descends one spine forever).
//!
//! **A PRIMITIVE HAS NO CASES** (user, 2026-09-25: every type has a `SortDomain`): its `fill`
//! is the waiting type check, `anthill.kernel.domain(?x, Int64)` — it leaves `?x` free and
//! decides once something binds it, so `List[T = Int64]` fills to skeletons.
//!
//! **THE DICTIONARY IS HANDED IN, NEVER A HEAD ARGUMENT** (060 §5): `?self` is the clause's
//! implicit parameter — a requirement READ, which `apply_domain` fills through the citation
//! channel (`resolve::within_requirements_goal`) and a citation fills from its route. A read
//! of `SortDomain` that arrives filled is TRUSTED, not checked: a domain involves no choice
//! among providers, and `fill` itself refuses a value its dictionary does not describe.
//!
//! **A DICTIONARY'S SUB MAY BE A TYPE.** The layout recorded here is what lets the resolver
//! build a dictionary from a TYPE, one level at a time and only when `fill` reads it
//! (060 §2.3, decided: a condition is resolved when `fill` reads it, and a read waits while
//! its type is unpinned — `[]` is a `List[?]`, and its `nil` case never reads the element).

use std::collections::{BTreeSet, HashMap, HashSet};

use smallvec::SmallVec;

use crate::intern::Symbol;
use crate::kb::load::{DomainJob, LoadError};
use crate::kb::term::{Literal, Term, TermId, Var, VarId};
use crate::kb::{ClauseKind, KnowledgeBase, SymbolKind};

/// The sorts whose values are LITERALS, not constructor applications — the primitives, each
/// of which provides `SortDomain` through the waiting type check rather than a derivation.
/// The literal sorts of `typing::literal_sort`, by qualified name.
pub(crate) const PRIMITIVE_SORTS: &[&str] = &[
    "anthill.prelude.Int64",
    "anthill.prelude.BigInt",
    "anthill.prelude.Float",
    "anthill.prelude.Bool",
    "anthill.prelude.String",
];

/// The marker a derived `fill` clause spells "the `k`-th sub-dictionary of `?self`" with —
/// `__domain_sub(?self, k)` — evaluated by `apply_domain` when it reads its dictionary
/// operand, never run as a goal (`resolve::BuiltinTag::DomainSub`).
pub(crate) const DOMAIN_SUB: &str = "anthill.kernel.__domain_sub";

/// Where a sort's `SortDomain` comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SortDomainKind {
    /// Derived from the sort's constructors, here.
    Derived,
    /// The sort's own written `domain(?x)` — it IS the generator, and replaces the
    /// derivation (060 §2.2).
    Written,
    /// A literal sort: `fill` is the waiting type check.
    Primitive,
}

/// One sort's `SortDomain` — see `KnowledgeBase::sort_domains`.
#[derive(Clone, Debug)]
pub(crate) struct SortDomainEntry {
    /// The relation `fill` runs at this sort: `<Sort>.domain`.
    pub(crate) fill: Symbol,
    /// The sort's declared type parameters in declaration order: the binding key a written
    /// `List[T = …]` uses, and the parameter's canonical variable.
    pub(crate) params: Vec<(Symbol, TermId)>,
    /// The CONDITIONS — the parameters some field fills — as indices into `params`, in
    /// declaration order: the dictionary's sub `sub_offset + k` is the evidence for
    /// `params[conditions[k]]`.
    pub(crate) conditions: Vec<usize>,
    /// Where the conditions start among the dictionary's subs — after `SortDomain`'s own
    /// chain and the sort's sort-level `requires`, the TYPER's layout
    /// (`typing::sort_domain_sub_offset`), which every `SortDomain` dictionary follows.
    pub(crate) sub_offset: usize,
    pub(crate) kind: SortDomainKind,
}

/// A derivation candidate: a sort with constructors and no written domain.
struct Candidate {
    job: DomainJob,
    /// `List[T = ?T]` — the head type of the sort's own values.
    self_type: TermId,
    /// Per constructor (declaration order), per field: name and repaired type.
    fields: Vec<Vec<(Symbol, TermId)>>,
}

/// Derive the `SortDomain` of every sort in `pending` — a sort with constructors, each with
/// its written `domain` when it has one — and of every primitive.
///
/// Runs at the drain, after every file's sorts are loaded: a field type naming a
/// parameterised sort bare is repaired against that sort's parameter list, which a forward
/// reference does not have at its use site (WI-743).
pub(crate) fn run(
    kb: &mut KnowledgeBase,
    pending: Vec<(DomainJob, Option<Symbol>)>,
) -> Vec<LoadError> {
    let mut errors = Vec::new();
    derive_primitives(kb, &mut errors);
    let mut candidates: Vec<Candidate> = Vec::new();
    for (job, hand) in pending {
        if let Some(fill) = hand {
            // A WRITTEN domain is the sort's `fill` as it stands; a parametric one is refused
            // upstream, so it has no conditions.
            kb.record_sort_domain(
                job.sort,
                SortDomainEntry {
                    fill,
                    params: job.params.clone(),
                    conditions: Vec::new(),
                    sub_offset: 0,
                    kind: SortDomainKind::Written,
                },
            );
            continue;
        }
        let self_type = domain_self_type(kb, job.sort, &job.params);
        let mut fields: Vec<Vec<(Symbol, TermId)>> = Vec::with_capacity(job.ctors.len());
        let mut unrepairable: Option<(Symbol, Symbol)> = None;
        'ctors: for c in &job.ctors {
            let mut fs = Vec::with_capacity(c.fields.len());
            for &(f, t) in &c.fields {
                // A field typed by an ALIAS is filled as its target is (`dealias_type`).
                let t = crate::kb::typing::dealias_type(kb, t);
                match super::load::repair_self_reference(kb, t, job.sort, self_type) {
                    Some(t) => fs.push((f, t)),
                    None => {
                        unrepairable = Some((c.ctor, f));
                        break 'ctors;
                    }
                }
            }
            fields.push(fs);
        }
        if let Some((ctor, field)) = unrepairable {
            // A BARE reference to some OTHER parameterised sort names no element type
            // (`repair_self_reference`'s rule, WI-743).
            decline(
                kb,
                job.sort,
                format!(
                    "field `{}` of constructor `{}` names a parameterised sort with no type \
                     arguments, which has no element domain to fill",
                    kb.qualified_name_of(field),
                    kb.qualified_name_of(ctor),
                ),
            );
            continue;
        }
        candidates.push(Candidate {
            job,
            self_type,
            fields,
        });
    }
    if candidates.is_empty() {
        return errors;
    }
    let conditions = condition_fixpoint(kb, &candidates);
    let Some(syms) = ClauseSyms::resolve(kb) else {
        errors.push(LoadError::Other {
            message: "WI-20260925-SHED7: a resolver primitive the derived `fill` clauses are \
                      built from (`unify` / `push_choice` / `push_and` / `apply_domain`) is \
                      not registered"
                .to_string(),
        });
        return errors;
    };
    // A PARAMETRIC `fill` reads its dictionary (the `SortDomain` read and the runtime
    // `Dictionary`), which a KB that never loaded `anthill.reflect` cannot spell. Such a sort
    // has no domain there — said, not skipped — and the fixpoint below carries that to every
    // sort whose field it fills.
    let mut declined: HashSet<Symbol> = HashSet::new();
    if syms.reads.is_none() {
        for c in &candidates {
            let canon = kb.canonical_sort_sym(c.job.sort);
            if conditions.get(&canon).is_some_and(|s| !s.is_empty()) {
                decline(
                    kb,
                    c.job.sort,
                    "a parametric sort's `fill` reads its `SortDomain` dictionary, and this KB \
                     never loaded `anthill.reflect.SortDomain` / the runtime `Dictionary`"
                        .to_string(),
                );
                declined.insert(canon);
            }
        }
    }
    let alive = fillable_fixpoint(kb, &candidates, &conditions, &declined);
    // Record every surviving entry BEFORE emitting any clause: a field of a later sort in
    // this batch is filled through an earlier one's `fill`, and the other way round.
    for c in &candidates {
        let canon = kb.canonical_sort_sym(c.job.sort);
        if !alive.contains(&canon) {
            continue;
        }
        let fill = fill_symbol(kb, c.job.sort);
        let conds: Vec<usize> = conditions
            .get(&canon)
            .map(|s| s.iter().copied().collect())
            .unwrap_or_default();
        let sub_offset = if conds.is_empty() {
            0
        } else {
            crate::kb::typing::sort_domain_sub_offset(kb, c.job.sort)
        };
        kb.record_sort_domain(
            c.job.sort,
            SortDomainEntry {
                fill,
                params: c.job.params.clone(),
                conditions: conds,
                sub_offset,
                kind: SortDomainKind::Derived,
            },
        );
    }
    for c in &candidates {
        if kb.sort_domain(c.job.sort).map(|e| e.kind) != Some(SortDomainKind::Derived) {
            continue;
        }
        emit_fill_clause(kb, &syms, c);
    }
    errors
}

/// Record that `sort` has no `SortDomain`, and why — the reason a typed head over it, and a
/// citation of its `.domain`, report.
fn decline(kb: &mut KnowledgeBase, sort: Symbol, reason: String) {
    kb.forget_domain_params(sort);
    kb.record_sort_domain_declined(sort, reason);
}

/// The relation `sort`'s `fill` is derived under: `<sort>.domain`, minted in pass 1 — the
/// VALUE FACE a citation reads (`Colour.domain.takeN(5)`) — when it is still a relation with
/// no clauses.
///
/// WHERE SOMETHING ELSE HOLDS THAT NAME — kernel-language §5.3's case: an operation, a
/// const, the author's own relation at another arity — the sort KEEPS ITS DOMAIN under an
/// internal `<sort>.__fill`, which only its `SortDomain` entry names, and has no `.domain`
/// to cite it by; the reason is recorded, so a citation says why rather than answering
/// through an unrelated relation (WT8WG's `/code-review` finding: a 3-ary `domain` once
/// took the value face over in silence).
fn fill_symbol(kb: &mut KnowledgeBase, sort: Symbol) -> Symbol {
    let qn = kb.qualified_name_of(sort).to_string();
    let name = format!("{qn}.domain");
    let reason = match kb.symbols.by_qualified_name.get(&name).copied() {
        Some(sym) if kb.has_kind(sym, SymbolKind::Goal) && !kb.has_clauses_under(sym) => {
            return sym;
        }
        Some(sym) if kb.has_kind(sym, SymbolKind::Goal) => {
            let arity = kb.clause_ids_of(sym).first().and_then(|&rid| {
                match crate::kb::term_view::TermView::head(kb.rule_head_value(rid), kb) {
                    crate::kb::term_view::ViewHead::Functor { pos_arity, .. } => Some(pos_arity),
                    _ => None,
                }
            });
            match arity {
                Some(n) => format!(
                    "`{name}` already names a relation of arity {n}, which is not the member \
                     shape — a sort's own domain is written `domain(?x)`"
                ),
                None => format!("`{name}` already names a relation that is not the member shape"),
            }
        }
        Some(sym) => format!("the name `{name}` is already bound (as {:?})", kb.kind_of(sym)),
        None => format!("the name `{name}` is not available for the derived relation"),
    };
    kb.record_domain_value_face_declined(sort, reason);
    let internal = format!("{qn}.__fill");
    if let Some(&sym) = kb.symbols.by_qualified_name.get(&internal) {
        return sym;
    }
    let scope = kb.symbols.scope_id(sort);
    kb.symbols
        .define_qualified_only("__fill", &internal, SymbolKind::Goal, scope)
}

/// Every PRIMITIVE sort this KB declares gets its `fill` — the waiting type check:
/// `Int64.domain(?x) :- anthill.kernel.domain(?x, Int64)`.
fn derive_primitives(kb: &mut KnowledgeBase, errors: &mut Vec<LoadError>) {
    for qn in PRIMITIVE_SORTS {
        let Some(sort) = kb.try_resolve_symbol(qn) else {
            continue;
        };
        if !kb.has_kind(sort, SymbolKind::Sort) || kb.has_sort_domain(sort) {
            continue;
        }
        let Some(check) = kb.try_resolve_symbol(crate::kb::typing::TYPE_DOMAIN_GOAL) else {
            errors.push(LoadError::Other {
                message: format!(
                    "WI-20260925-SHED7: `{}` is not declared, so the primitive `{qn}` has no \
                     `fill`",
                    crate::kb::typing::TYPE_DOMAIN_GOAL
                ),
            });
            return;
        };
        let fill = fill_symbol(kb, sort);
        let self_type = kb.make_sort_ref(sort);
        let (x_var, x) = fresh_global_var(kb, "x");
        let head = pos_fn(kb, fill, &[x]);
        let body = vec![pos_fn(kb, check, &[x, self_type])];
        let body_nodes = kb.term_body_to_nodes(&body);
        let domain = kb
            .symbols
            .declaring_scope(sort)
            .map(|s| s.owner())
            .unwrap_or(sort);
        let rid =
            kb.assert_rule_debruijn_with_nodes(head, body_nodes, ClauseKind::Rule, domain, None);
        kb.install_rule_type_bounds(rid, &[(x_var, self_type)]);
        kb.record_sort_domain(
            sort,
            SortDomainEntry {
                fill,
                params: Vec::new(),
                conditions: Vec::new(),
                sub_offset: 0,
                kind: SortDomainKind::Primitive,
            },
        );
    }
}

/// The CONDITIONS of every candidate — the parameters some field fills — as a LEAST
/// fixpoint: a field of type `H[args]` fills the arguments at `H`'s own conditions, and `H`
/// may be a candidate of this batch whose conditions are still growing.
fn condition_fixpoint(
    kb: &KnowledgeBase,
    candidates: &[Candidate],
) -> HashMap<Symbol, BTreeSet<usize>> {
    let mut conds: HashMap<Symbol, BTreeSet<usize>> = candidates
        .iter()
        .map(|c| (kb.canonical_sort_sym(c.job.sort), BTreeSet::new()))
        .collect();
    let params_of: HashMap<Symbol, &[(Symbol, TermId)]> = candidates
        .iter()
        .map(|c| (kb.canonical_sort_sym(c.job.sort), c.job.params.as_slice()))
        .collect();
    loop {
        let mut changed = false;
        for c in candidates {
            let canon = kb.canonical_sort_sym(c.job.sort);
            let mut found: BTreeSet<usize> = BTreeSet::new();
            for fs in &c.fields {
                for &(_, t) in fs {
                    collect_conditions(kb, t, c, &conds, &params_of, &mut found);
                }
            }
            let entry = conds.get_mut(&canon).expect("every candidate is seeded");
            for i in found {
                changed |= entry.insert(i);
            }
        }
        if !changed {
            return conds;
        }
    }
}

/// The parameters of `c` a field of type `t` fills — see [`condition_fixpoint`].
fn collect_conditions(
    kb: &KnowledgeBase,
    t: TermId,
    c: &Candidate,
    conds: &HashMap<Symbol, BTreeSet<usize>>,
    params_of: &HashMap<Symbol, &[(Symbol, TermId)]>,
    out: &mut BTreeSet<usize>,
) {
    if t == c.self_type {
        return;
    }
    if let Some(i) = param_index(kb, t, &c.job.params) {
        out.insert(i);
        return;
    }
    let Some(head) = type_head(kb, t) else {
        return;
    };
    let hc = kb.canonical_sort_sym(head);
    let (params, filled): (&[(Symbol, TermId)], Vec<usize>) = match (conds.get(&hc), params_of.get(&hc)) {
        (Some(set), Some(ps)) => (ps, set.iter().copied().collect()),
        _ => match kb.sort_domain(hc) {
            Some(e) => (e.params.as_slice(), e.conditions.clone()),
            None => return,
        },
    };
    for j in filled {
        if let Some(arg) = type_arg(kb, t, params, j) {
            collect_conditions(kb, arg, c, conds, params_of, out);
        }
    }
}

/// The candidates that CAN be filled, as a GREATEST fixpoint: a sort drops out when some
/// field of some entity names a type with no `SortDomain` — a function type, a tuple, a sort
/// with no constructors that is no primitive, or a sort that itself dropped out — at a
/// position `fill` reads. Mutually recursive sorts keep each other.
fn fillable_fixpoint(
    kb: &mut KnowledgeBase,
    candidates: &[Candidate],
    conds: &HashMap<Symbol, BTreeSet<usize>>,
    declined: &HashSet<Symbol>,
) -> HashSet<Symbol> {
    let mut alive: HashSet<Symbol> = candidates
        .iter()
        .map(|c| kb.canonical_sort_sym(c.job.sort))
        .filter(|s| !declined.contains(s))
        .collect();
    let params_of: HashMap<Symbol, Vec<(Symbol, TermId)>> = candidates
        .iter()
        .map(|c| (kb.canonical_sort_sym(c.job.sort), c.job.params.clone()))
        .collect();
    loop {
        let mut dropped: Vec<(Symbol, String)> = Vec::new();
        for c in candidates {
            let canon = kb.canonical_sort_sym(c.job.sort);
            if !alive.contains(&canon) {
                continue;
            }
            'fields: for (ci, fs) in c.fields.iter().enumerate() {
                for &(f, t) in fs {
                    if !field_fillable(kb, t, c, &alive, conds, &params_of) {
                        dropped.push((
                            c.job.sort,
                            format!(
                                "field `{}` of constructor `{}` has a type with no \
                                 `SortDomain`, so the field cannot be filled",
                                kb.qualified_name_of(f),
                                kb.qualified_name_of(c.job.ctors[ci].ctor),
                            ),
                        ));
                        break 'fields;
                    }
                }
            }
        }
        if dropped.is_empty() {
            return alive;
        }
        for (s, reason) in dropped {
            alive.remove(&kb.canonical_sort_sym(s));
            decline(kb, s, reason);
        }
    }
}

/// Can a field of type `t` of candidate `c` be filled, given the sorts still `alive`?
fn field_fillable(
    kb: &KnowledgeBase,
    t: TermId,
    c: &Candidate,
    alive: &HashSet<Symbol>,
    conds: &HashMap<Symbol, BTreeSet<usize>>,
    params_of: &HashMap<Symbol, Vec<(Symbol, TermId)>>,
) -> bool {
    if t == c.self_type || param_index(kb, t, &c.job.params).is_some() {
        return true;
    }
    let Some(head) = type_head(kb, t) else {
        return false;
    };
    let hc = kb.canonical_sort_sym(head);
    let (params, filled): (Vec<(Symbol, TermId)>, Vec<usize>) = if alive.contains(&hc) {
        (
            params_of.get(&hc).cloned().unwrap_or_default(),
            conds
                .get(&hc)
                .map(|s| s.iter().copied().collect())
                .unwrap_or_default(),
        )
    } else if let Some(e) = kb.sort_domain(hc) {
        (e.params.clone(), e.conditions.clone())
    } else {
        return false;
    };
    filled.into_iter().all(|j| match type_arg(kb, t, &params, j) {
        Some(arg) => field_fillable(kb, arg, c, alive, conds, params_of),
        // An argument the type does not write is a fresh type — filled when something pins
        // it, as `[]`'s element is.
        None => true,
    })
}

/// The resolver primitives a derived clause is spelled with.
struct ClauseSyms {
    unify: Symbol,
    choice: Symbol,
    and: Symbol,
    apply: Symbol,
    /// What a PARAMETRIC `fill` needs to read its dictionary — `None` in a KB that never
    /// loaded `anthill.reflect`, where no parametric sort has a domain.
    reads: Option<ReadSyms>,
}

struct ReadSyms {
    find_dictionary: Symbol,
    spec: Symbol,
    out_label: Symbol,
    sub: Symbol,
    dict_ctor: Symbol,
    dict_impl: Symbol,
}

impl ClauseSyms {
    fn resolve(kb: &mut KnowledgeBase) -> Option<Self> {
        let reads = (|| {
            let (dict_ctor, dict_impl) = crate::kb::term_view::dictionary_view_syms(kb)?;
            Some(ReadSyms {
                find_dictionary: crate::kb::typing::find_dictionary_symbol(kb)?,
                spec: kb.try_resolve_symbol(crate::kb::typing::SORT_DOMAIN_SPEC)?,
                out_label: kb.intern(crate::kb::typing::REQUIREMENT_OUT_LABEL),
                sub: kb.try_resolve_symbol(DOMAIN_SUB)?,
                dict_ctor,
                dict_impl,
            })
        })();
        Some(Self {
            unify: kb.try_resolve_symbol("anthill.kernel.unify")?,
            choice: kb.try_resolve_symbol("anthill.kernel.push_choice")?,
            and: kb.try_resolve_symbol("anthill.kernel.push_and")?,
            apply: kb.try_resolve_symbol(crate::kb::typing::APPLY_DOMAIN_GOAL)?,
            reads,
        })
    }

    /// The read symbols — present whenever a clause needs them, because a parametric sort
    /// is declined above where they are absent.
    fn reads(&self) -> &ReadSyms {
        self.reads
            .as_ref()
            .expect("a sort whose `fill` reads a dictionary is declined where the read symbols are absent")
    }
}

/// How one field is filled — see [`fill_goal`].
enum Evidence {
    /// The dictionary the clause was handed: the recursion.
    SelfDict,
    /// Sub-dictionary `k` of it: a parameter's condition.
    Sub(usize),
    /// A ground type: its dictionary is built from the type when read.
    Type(TermId),
    /// `Dictionary(subs…, impl: H)` for a type `H[args]` mentioning the sort's parameters.
    Dict(Symbol, Vec<Evidence>),
    /// A sort whose `fill` needs no dictionary (no conditions): called by name.
    Static { fill: Symbol, ty: TermId },
    /// A slot of the layout no `fill` reads — `SortDomain`'s own chain, a sort-level
    /// `requires` — in a dictionary built here.
    Placeholder,
}

/// Emit `c`'s `fill` clause.
fn emit_fill_clause(kb: &mut KnowledgeBase, syms: &ClauseSyms, c: &Candidate) {
    let entry = kb
        .sort_domain(c.job.sort)
        .cloned()
        .expect("a candidate is emitted only once recorded");
    let needs_self = !entry.conditions.is_empty();
    let (x_var, x) = fresh_global_var(kb, "x");
    let self_var = fresh_global(kb, "self");
    // BASE CONSTRUCTORS FIRST, recursive ones after, each group in declaration order.
    let recursive: Vec<bool> = c
        .fields
        .iter()
        .map(|fs| fs.iter().any(|&(_, t)| mentions_sort(kb, t, c.job.sort)))
        .collect();
    let mut order: Vec<usize> = (0..c.fields.len()).collect();
    order.sort_by_key(|&i| recursive[i]);
    let mut branches: Vec<TermId> = Vec::with_capacity(order.len());
    for i in order {
        let ctor = c.job.ctors[i].ctor;
        let fs = &c.fields[i];
        let vars: Vec<(Symbol, TermId)> = fs
            .iter()
            .map(|&(f, _)| {
                let name = kb.symbols.local_name(f).to_owned();
                (f, fresh_global(kb, &name))
            })
            .collect();
        let ctor_term = if fs.is_empty() {
            kb.alloc(Term::Ref(ctor))
        } else {
            let named: SmallVec<[(Symbol, TermId); 2]> = vars.iter().copied().collect();
            kb.make_entity_term(ctor, SmallVec::new(), named)
        };
        let mut goals: Vec<TermId> = vec![pos_fn(kb, syms.unify, &[x, ctor_term])];
        // RECURSIVE FIELDS FIRST inside the case — the other half of fairness.
        for want_rec in [true, false] {
            for (k, &(_, t)) in fs.iter().enumerate() {
                if mentions_sort(kb, t, c.job.sort) != want_rec {
                    continue;
                }
                let ev = evidence(kb, t, c, &entry);
                goals.push(fill_goal(kb, syms, ev, vars[k].1, self_var));
            }
        }
        branches.push(right_fold(kb, syms.and, &goals));
    }
    let head = pos_fn(kb, entry.fill, &[x]);
    let mut body: Vec<TermId> = Vec::with_capacity(2);
    if needs_self {
        // The clause's IMPLICIT PARAMETER: its own dictionary, a requirement read the
        // citation channel fills. Witnessed by `?x`, so a citation routes it from the
        // column's type and an unfilled read derives it from `?x`'s carried type.
        let reads = syms.reads();
        let spec_ref = kb.alloc(Term::Ref(reads.spec));
        let read = kb.alloc(Term::Fn {
            functor: reads.find_dictionary,
            pos_args: SmallVec::from_slice(&[spec_ref, spec_ref, x]),
            named_args: SmallVec::from_slice(&[(reads.out_label, self_var)]),
        });
        body.push(read);
    }
    body.push(right_fold(kb, syms.choice, &branches));
    let body_nodes = kb.term_body_to_nodes(&body);
    let rid =
        kb.assert_rule_debruijn_with_nodes(head, body_nodes, ClauseKind::Rule, c.job.domain, None);
    // The column type a citation of `<Sort>.domain` reads, and where the clause reports.
    kb.install_rule_type_bounds(rid, &[(x_var, c.self_type)]);
    kb.set_rule_head_span(rid, c.job.span);
}

/// How a field of type `t` of candidate `c` is filled.
fn evidence(kb: &mut KnowledgeBase, t: TermId, c: &Candidate, entry: &SortDomainEntry) -> Evidence {
    if t == c.self_type {
        return if entry.conditions.is_empty() {
            Evidence::Static {
                fill: entry.fill,
                ty: t,
            }
        } else {
            Evidence::SelfDict
        };
    }
    if let Some(i) = param_index(kb, t, &c.job.params) {
        let k = entry
            .conditions
            .iter()
            .position(|&j| j == i)
            .expect("a parameter a field fills is a condition");
        return Evidence::Sub(entry.sub_offset + k);
    }
    let head = type_head(kb, t).expect("a fillable field type has a nominal head");
    let target = kb
        .sort_domain(head)
        .cloned()
        .expect("a fillable field type's sort has a SortDomain");
    // A sort whose `fill` reads no dictionary is called by name, whatever its arguments.
    if target.conditions.is_empty() {
        return Evidence::Static {
            fill: target.fill,
            ty: t,
        };
    }
    if !term_mentions_params(kb, t, &c.job.params) {
        return Evidence::Type(t);
    }
    // THE TYPER'S LAYOUT: the prefix `sub_offset` slots are never read by a `fill`, and a
    // placeholder holds them; the conditions follow.
    let mut subs: Vec<Evidence> = (0..target.sub_offset).map(|_| Evidence::Placeholder).collect();
    for &j in &target.conditions {
        subs.push(match type_arg(kb, t, &target.params, j) {
            Some(arg) => evidence(kb, arg, c, entry),
            // Unwritten: a fresh type, pending until pinned.
            None => Evidence::Type(fresh_global(kb, "T")),
        });
    }
    Evidence::Dict(head, subs)
}

/// The goal that fills `v` through `ev`.
fn fill_goal(kb: &mut KnowledgeBase, syms: &ClauseSyms, ev: Evidence, v: TermId, self_var: TermId) -> TermId {
    match ev {
        Evidence::Static { fill, .. } => pos_fn(kb, fill, &[v]),
        other => {
            let e = evidence_term(kb, syms, other, self_var);
            pos_fn(kb, syms.apply, &[e, v])
        }
    }
}

/// The TERM `apply_domain` reads its dictionary from.
fn evidence_term(kb: &mut KnowledgeBase, syms: &ClauseSyms, ev: Evidence, self_var: TermId) -> TermId {
    match ev {
        Evidence::SelfDict => self_var,
        Evidence::Sub(k) => {
            let idx = kb.alloc(Term::Const(Literal::Int(k as i64)));
            pos_fn(kb, syms.reads().sub, &[self_var, idx])
        }
        Evidence::Type(t) | Evidence::Static { ty: t, .. } => t,
        Evidence::Placeholder => kb.alloc(Term::Bottom),
        Evidence::Dict(head, subs) => {
            let subs: SmallVec<[TermId; 4]> = subs
                .into_iter()
                .map(|s| evidence_term(kb, syms, s, self_var))
                .collect();
            let impl_ref = kb.alloc(Term::Ref(head));
            let reads = syms.reads();
            kb.alloc(Term::Fn {
                functor: reads.dict_ctor,
                pos_args: subs,
                named_args: SmallVec::from_slice(&[(reads.dict_impl, impl_ref)]),
            })
        }
    }
}

/// Is `t` the canonical variable of one of `params`, and which?
fn param_index(kb: &KnowledgeBase, t: TermId, params: &[(Symbol, TermId)]) -> Option<usize> {
    let Term::Var(Var::Global(v)) = kb.get_term(t) else {
        return None;
    };
    params
        .iter()
        .position(|&(_, pt)| matches!(kb.get_term(pt), Term::Var(Var::Global(pv)) if pv == v))
}

/// Does `t` mention any of `params`' canonical variables?
fn term_mentions_params(kb: &KnowledgeBase, t: TermId, params: &[(Symbol, TermId)]) -> bool {
    let vars: Vec<VarId> = params
        .iter()
        .filter_map(|&(_, pt)| match kb.get_term(pt) {
            Term::Var(Var::Global(v)) => Some(*v),
            _ => None,
        })
        .collect();
    kb.collect_vars(&t).iter().any(|v| vars.contains(v))
}

/// Does `t` mention the sort `s` (at any depth) — a recursive field?
fn mentions_sort(kb: &KnowledgeBase, t: TermId, s: Symbol) -> bool {
    let canon = kb.canonical_sort_sym(s);
    match kb.get_term(t) {
        Term::Ref(h) => kb.canonical_sort_sym(*h) == canon,
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } => {
            kb.canonical_sort_sym(*functor) == canon
                || pos_args.iter().any(|&a| mentions_sort(kb, a, s))
                || named_args.iter().any(|&(_, a)| mentions_sort(kb, a, s))
        }
        _ => false,
    }
}

/// The nominal head of a type term, or `None` for a variable, an arrow, a tuple.
fn type_head(kb: &KnowledgeBase, t: TermId) -> Option<Symbol> {
    match kb.get_term(t) {
        Term::Ref(s) => Some(*s),
        Term::Fn { functor, .. } if kb.has_kind(*functor, SymbolKind::Sort) => Some(*functor),
        _ => None,
    }
}

/// The argument type `t` writes for `params[j]`: by its binding key's SHORT NAME (the two
/// sides reach their keys through different resolutions, `pin_type_vars`' rule), else by
/// position — [`condition_arg_position`]'s. The one reader of a TERM type's condition
/// argument; the resolver and the citation route read a `Value` type the same way.
pub(crate) fn type_arg(kb: &KnowledgeBase, t: TermId, params: &[(Symbol, TermId)], j: usize) -> Option<TermId> {
    let Term::Fn {
        functor,
        pos_args,
        named_args,
    } = kb.get_term(t)
    else {
        return None;
    };
    let (key, _) = params.get(j)?;
    let short = kb.local_name_of(*key);
    named_args
        .iter()
        .find(|(k, _)| kb.local_name_of(*k) == short)
        .map(|&(_, a)| a)
        .or_else(|| {
            condition_arg_position(kb, *functor, params, j).and_then(|p| pos_args.get(p).copied())
        })
}

/// Where a POSITIONAL type application of `sort` writes the argument for `params[j]` — one of
/// the sort's `sort T = ?` parameters, as a `SortDomainEntry` or a derivation candidate lists
/// them: its position among the sort's DECLARED type parameters, which is not `j` where a
/// WI-452 marked structured parameter is declared too (`sort Tagged[F[T], A]`: `A` is
/// `params[0]` and position 1). Read by `j` instead, a condition took `F`'s argument.
pub(crate) fn condition_arg_position(
    kb: &KnowledgeBase,
    sort: Symbol,
    params: &[(Symbol, TermId)],
    j: usize,
) -> Option<usize> {
    let decl = condition_param_sym(kb, sort, params, j)?;
    kb.type_param_syms_of(sort).iter().position(|&p| p == decl)
}

/// The type-parameter symbol `sort` DECLARES for `params[j]` — whose keys are interned short
/// names — as a provision row conditions on it.
pub(crate) fn condition_param_sym(
    kb: &KnowledgeBase,
    sort: Symbol,
    params: &[(Symbol, TermId)],
    j: usize,
) -> Option<Symbol> {
    kb.type_param_sym_of(sort, kb.local_name_of(params.get(j)?.0))
}

/// `List[T = ?T]` — the type of the sort's own values, at its canonical parameters.
fn domain_self_type(kb: &mut KnowledgeBase, sort: Symbol, params: &[(Symbol, TermId)]) -> TermId {
    let base = kb.make_sort_ref(sort);
    if params.is_empty() {
        return base;
    }
    kb.make_parameterized_type(base, params)
}

fn fresh_global(kb: &mut KnowledgeBase, name: &str) -> TermId {
    fresh_global_var(kb, name).1
}

fn fresh_global_var(kb: &mut KnowledgeBase, name: &str) -> (VarId, TermId) {
    let sym = kb.intern(name);
    let vid = kb.fresh_var(sym);
    (vid, kb.alloc(Term::Var(Var::Global(vid))))
}

fn pos_fn(kb: &mut KnowledgeBase, f: Symbol, args: &[TermId]) -> TermId {
    kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::from_slice(args),
        named_args: SmallVec::new(),
    })
}

/// `a & b & c` / `a | b | c` as a right-nested chain under `connective`.
fn right_fold(kb: &mut KnowledgeBase, connective: Symbol, goals: &[TermId]) -> TermId {
    match goals {
        [] => kb.alloc(Term::Bottom),
        [only] => *only,
        [first, rest @ ..] => {
            let tail = right_fold(kb, connective, rest);
            pos_fn(kb, connective, &[*first, tail])
        }
    }
}

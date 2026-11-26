//! WI-20261126-JR3AD — an override's contract clauses against the spec operation's, UP TO
//! ONE RENAMING of the operation's clause variables.
//!
//! The contract legs of [`check_override_refinement`] compare clauses structurally, in the
//! spec operation's vocabulary: the parameters, the `result` binder and the paired type
//! parameters are aligned first. What no alignment reaches is a variable the CLAUSES hold —
//! a written `?x`, one per name per operation and shared by every clause of the operation
//! that writes it, or a filler the loader puts in a field an entity pattern leaves out,
//! fresh per pattern. Each operation has its own, so an override restating
//! `ensures holds(result, ?k)` held a `?k` of its own and was never structurally equal to
//! the spec operation's: a spec operation whose `ensures` holds a variable had NO POSSIBLE
//! PROVIDER, however faithfully it was restated (MEASURED on the ticket's probe).
//!
//! THE READING. A spec operation's clause variable corresponds to one override variable,
//! and the same one in EVERY clause of the operation — `requires` and `ensures` alike, the
//! scope a written `?x` has — and the correspondence is ONE-TO-ONE. Two clauses sharing a
//! variable restated with two unrelated ones say less (`∃x. p(x) ∧ q(x)` against
//! `∃x. p(x) ∧ ∃y. q(y)`), and one variable restating two says something else. The check
//! stays syntactic: `p(?x, ?x)` does not restate `p(?a, ?b)`, logically stronger or not.
//!
//! WHICH VARIABLES ARE RENAMED. Only those the two SIGNATURES do not bind ([`ClauseVariables`]):
//! a variable a parameter type, the result type or an effect row writes, an operation's
//! type parameter, and a declaring sort's parameter keep their identity, as
//! [`views_structurally_equal`] compares them. The paired type parameters were already
//! aligned into the spec operation's spelling ([`substitute_clause_vars`]); renaming one
//! of them would let `Eq[T = A]` restate `Eq[T = B]` for two parameters nothing pairs.
//! Over-counting a variable as bound is the safe direction: it is compared by identity,
//! which refuses — today's verdict, and one the author sees.
//!
//! THE SEARCH, AND WHY IT IS NOT GREEDY. A greedy pass — each clause extending the renaming
//! with its first counterpart that fits, never revisited — refuses a faithful restatement
//! whenever an earlier counterpart fits a clause on its own and the correspondence it fixes
//! conflicts later. Taking the clause with the fewest counterparts first settles some of
//! those (spec `p(?a), p(?b), q(?b)` against `p(?x), p(?y), q(?x)`: `q` goes first and fixes
//! `b ↦ x`), and not the rest: spec `holds(n, ?a), holds(n, ?b), holds(?b, result)` against
//! `holds(n, ?x), holds(n, ?y), holds(?x, result), holds(?z, result)` gives every clause two
//! counterparts, greedy takes `a ↦ x`, and the restatement is `a ↦ y, b ↦ x`. So it is a
//! backtracking search over each clause's counterparts, the clause with fewest first,
//! complete within [`CONTRACT_RENAMING_BUDGET`] attempts. The budget is a bound and
//! not a timeout: restating clauses that agree up to their variables is subgraph
//! matching, and a pigeonhole — ten spec clauses `has(s, ?c)` and nine in the override —
//! explores every partial correspondence before it fails. Running out is a REFUSAL with
//! its own reason ([`ContractMisfit::SearchAbandoned`]), never a pass.
use super::*;

/// How many clause pairs the search for one renaming tries before it gives up
/// ([`ContractMisfit::SearchAbandoned`]). A renaming the search reaches without turning
/// back is found in at most as many attempts as there are clause pairs that fit on their
/// own; the bound is reached only by clauses that agree up to their variables many times
/// over.
pub(super) const CONTRACT_RENAMING_BUDGET: usize = 100_000;

/// The variables of one spec-operation / override pair that their SIGNATURES bind: the
/// rest of the variables their clauses hold are the clauses' own, which a renaming may
/// map ([`Renaming`]). One set for both operations: their `VarId`s are distinct, and a
/// spec operation's type parameter the alignment wrote into the override's clause is
/// bound THERE too.
pub(super) struct ClauseVariables {
    signature_bound: HashSet<VarId>,
}

impl ClauseVariables {
    /// What `spec_op`'s and `impl_op`'s signatures bind: every variable of a parameter
    /// type, the result type and an effect label ([`collect_value_type`], the walk the
    /// type rewriters close over), every operation type parameter, and the declaring
    /// sort's parameters — the sources [`signature_bound_vars`] reads, the effects added,
    /// since an effect row's variable is no clause's either. A `requires` clause is not a
    /// source here: its own variables are what is being renamed.
    ///
    /// [`collect_value_type`]: crate::kb::node_occurrence::collect_value_type
    pub(super) fn of_pair(
        kb: &KnowledgeBase,
        spec_op: Symbol,
        spec_info: &crate::kb::op_info::OpInfoRecord,
        impl_op: Symbol,
        impl_info: &crate::kb::op_info::OpInfoRecord,
    ) -> Self {
        let mut vids: Vec<VarId> = Vec::new();
        let mut seen: HashSet<u32> = HashSet::new();
        for (op, info) in [(spec_op, spec_info), (impl_op, impl_info)] {
            let types = info
                .params
                .iter()
                .map(|(_, ty)| ty)
                .chain(std::iter::once(&info.return_type))
                .chain(info.effects.iter());
            for ty in types {
                crate::kb::node_occurrence::collect_value_type(kb, ty, &mut vids, &mut seen);
            }
            vids.extend(info.type_params.iter().filter_map(|(_, v)| v.as_global()));
            if let Some(parent) = impl_parent_sort_of_op(kb, op) {
                for (_, canonical) in sort_type_params_as_pairs(kb, parent).iter() {
                    if let Term::Var(Var::Global(vid)) = kb.get_term(*canonical) {
                        vids.push(*vid);
                    }
                }
            }
        }
        Self {
            signature_bound: vids.into_iter().collect(),
        }
    }

    /// `v` when it is a clause's own variable: a flex variable no signature binds. A
    /// rigid or bound (De Bruijn) variable is no clause variable — it is compared by
    /// identity, as [`views_structurally_equal`] compares it.
    fn clause_variable(&self, v: &Var) -> Option<VarId> {
        v.as_global().filter(|vid| !self.signature_bound.contains(vid))
    }

    /// The clause variables `clauses` hold, read by the walk that collects a term's flex
    /// variables on either carrier ([`KnowledgeBase::collect_vars_rec`]).
    fn clause_variables_in(&self, kb: &KnowledgeBase, clauses: &[Value]) -> HashSet<VarId> {
        let mut vids: Vec<VarId> = Vec::new();
        let mut seen: HashSet<u32> = HashSet::new();
        for clause in clauses {
            kb.collect_vars_rec(clause, &mut vids, &mut seen);
        }
        vids.into_iter()
            .filter(|vid| !self.signature_bound.contains(vid))
            .collect()
    }
}

/// A one-to-one correspondence between spec-operation clause variables and override
/// clause variables, kept in both directions so that a clash either way is one lookup.
/// Extended by [`Self::extended_to`] and never shrunk: the search backtracks by keeping
/// the renaming it held before the attempt.
#[derive(Clone, Default)]
struct Renaming {
    spec_to_impl: HashMap<VarId, VarId>,
    impl_to_spec: HashMap<VarId, VarId>,
}

impl Renaming {
    /// This renaming extended so that the override's clause `imp` restates the spec
    /// operation's `spec`, or `None` where no extension does. On a copy, because the walk
    /// can consult the renaming on a pair of variables before it finds a mismatch
    /// ([`views_equal_matching_vars`]).
    fn extended_to(
        &self,
        kb: &KnowledgeBase,
        vars: &ClauseVariables,
        spec: &Value,
        imp: &Value,
    ) -> Option<Renaming> {
        let mut next = self.clone();
        views_equal_matching_vars(kb, spec, imp, &mut |s, i| next.relate(vars, s, i)).then_some(next)
    }

    /// Does the spec operation's variable `s` stand where the override's `i` does, under
    /// this renaming — extending it when neither is mapped yet? Two clause variables
    /// correspond when the renaming says so or can be made to without mapping either one
    /// twice; a clause variable never corresponds to a bound one; two bound variables
    /// correspond when they are one.
    fn relate(&mut self, vars: &ClauseVariables, s: &Var, i: &Var) -> bool {
        match (vars.clause_variable(s), vars.clause_variable(i)) {
            (Some(sv), Some(iv)) => match (self.spec_to_impl.get(&sv), self.impl_to_spec.contains_key(&iv)) {
                // A mapped spec variable answers by its image; its image is mapped back to
                // it, so the reverse lookup has nothing to add.
                (Some(image), _) => *image == iv,
                // `iv` already restates another of the spec operation's variables.
                (None, true) => false,
                (None, false) => {
                    self.spec_to_impl.insert(sv, iv);
                    self.impl_to_spec.insert(iv, sv);
                    true
                }
            },
            (None, None) => s == i,
            _ => false,
        }
    }

    fn is_empty(&self) -> bool {
        self.spec_to_impl.is_empty()
    }
}

/// Why an override's contract is not the spec operation's, one entry per refusal
/// [`check_override_refinement`] reports.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ContractMisfit {
    /// An override `requires` clause no spec operation clause restates, under any
    /// renaming: one entry per such clause.
    StrengthenedPrecondition,
    /// A spec operation `ensures` clause no override clause restates, under any renaming:
    /// one entry per such clause.
    WeakenedPostcondition,
    /// Every clause has its counterpart under SOME renaming, and no one renaming gives
    /// them all: a variable the spec operation's clauses share is restated by two, or two
    /// of its variables by one. At most one entry.
    NoOneRenaming,
    /// Renamings restate every clause, and each of them restates a variable the spec
    /// operation's `requires` binds by one none of the override's `requires` binds — the
    /// override dropped the precondition and kept the promise made about its variable
    /// ([`RenamingSearch::keeps_preconditions_variables`]). At most one entry.
    UnboundPostconditionVariable,
    /// The search for one renaming ran out of [`CONTRACT_RENAMING_BUDGET`] before it found
    /// one or ruled every one out. At most one entry.
    SearchAbandoned,
}

impl ContractMisfit {
    /// The refusal's reason, as [`LoadError::IncompatibleOverride`] words it.
    pub(super) fn reason(self) -> String {
        match self {
            Self::StrengthenedPrecondition => "it strengthens the precondition — the override \
                `requires` a condition the spec operation does not"
                .to_string(),
            Self::WeakenedPostcondition => "it weakens the postcondition — the override does not \
                `ensure` a condition the spec operation promises"
                .to_string(),
            Self::NoOneRenaming => "its contract clauses restate the spec operation's only under \
                different renamings of their variables — a variable corresponds to one variable \
                across all of an operation's clauses: one the spec operation's clauses share is \
                one the override's share, and two that differ stay two"
                .to_string(),
            Self::UnboundPostconditionVariable => "it weakens the postcondition — its `ensures` \
                restates a variable the spec operation's `requires` binds by one none of its own \
                `requires` binds, so it promises the condition of some value and not of the one \
                the precondition names"
                .to_string(),
            Self::SearchAbandoned => format!(
                "matching the variables of its contract clauses with the spec operation's was \
                 given up after {CONTRACT_RENAMING_BUDGET} attempts, with no one renaming found \
                 that restates them all"
            ),
        }
    }
}

/// One clause the override owes, with the counterparts that restate it on their own.
struct Obligation<'a> {
    /// Each counterpart as `(spec operation's clause, override's clause)`.
    pairs: Vec<(&'a Value, &'a Value)>,
}

enum Search {
    Found,
    Exhausted,
    Abandoned,
}

/// The override's contract against the spec operation's, as [`check_override_refinement`]'s
/// two contract legs read it: every override precondition one the spec operation
/// requires (`impl_pre` ⊆ `spec_pre`), every spec operation postcondition one the override
/// ensures (`spec_post` ⊆ `impl_post`) — each clause up to ONE renaming of the clause
/// variables, the same one across both legs. The override's clauses arrive aligned into
/// the spec operation's vocabulary.
///
/// The misfits come in the legs' order: each clause with no counterpart under any renaming,
/// preconditions first, one entry each, then at most one entry for the clauses that do have
/// counterparts but no renaming they share. Empty when the override restates the contract.
pub(super) fn contract_misfits(
    kb: &KnowledgeBase,
    vars: &ClauseVariables,
    impl_pre: &[Value],
    spec_pre: &[Value],
    spec_post: &[Value],
    impl_post: &[Value],
) -> Vec<ContractMisfit> {
    let mut misfits = Vec::new();
    let mut obligations: Vec<Obligation<'_>> = Vec::new();
    let owed = impl_pre
        .iter()
        .map(|ic| {
            let candidates: Vec<(&Value, &Value)> = spec_pre.iter().map(|sc| (sc, ic)).collect();
            (ContractMisfit::StrengthenedPrecondition, candidates)
        })
        .chain(spec_post.iter().map(|sc| {
            let candidates: Vec<(&Value, &Value)> = impl_post.iter().map(|ic| (sc, ic)).collect();
            (ContractMisfit::WeakenedPostcondition, candidates)
        }));
    for (misfit, candidates) in owed {
        let mut fitting = candidates
            .into_iter()
            .filter_map(|(s, i)| Some((s, i, Renaming::default().extended_to(kb, vars, s, i)?)));
        match fitting.next() {
            None => misfits.push(misfit),
            // A clause that fits with NOTHING renamed holds no clause variable — every one it
            // held would have been mapped — so its counterparts constrain no other clause and
            // it is settled by the first, as every clause was before the renaming. The rest are
            // not walked: a ground clause is all the corpus held before this.
            Some((_, _, renaming)) if renaming.is_empty() => {}
            Some((s, i, _)) => {
                let mut pairs = vec![(s, i)];
                pairs.extend(fitting.map(|(s, i, _)| (s, i)));
                obligations.push(Obligation { pairs });
            }
        }
    }
    // Fewest counterparts first: a clause with one fixes its variables before the search
    // branches on another's. Stable, so ties keep the legs' order.
    obligations.sort_by_key(|o| o.pairs.len());
    let mut search = RenamingSearch {
        kb,
        vars,
        bound_by_spec_pre: vars.clause_variables_in(kb, spec_pre),
        bound_by_impl_pre: vars.clause_variables_in(kb, impl_pre),
        budget: CONTRACT_RENAMING_BUDGET,
        unbound_at_a_leaf: false,
    };
    match search.extend(&obligations, &Renaming::default()) {
        Search::Found => {}
        Search::Exhausted if search.unbound_at_a_leaf => {
            misfits.push(ContractMisfit::UnboundPostconditionVariable)
        }
        Search::Exhausted => misfits.push(ContractMisfit::NoOneRenaming),
        Search::Abandoned => misfits.push(ContractMisfit::SearchAbandoned),
    }
    misfits
}

/// The search for one renaming under which every obligation has a counterpart.
struct RenamingSearch<'a> {
    kb: &'a KnowledgeBase,
    vars: &'a ClauseVariables,
    /// The clause variables the spec operation's `requires` clauses hold.
    bound_by_spec_pre: HashSet<VarId>,
    /// The clause variables the override's `requires` clauses hold.
    bound_by_impl_pre: HashSet<VarId>,
    /// Clause pairs still to be tried ([`CONTRACT_RENAMING_BUDGET`]).
    budget: usize,
    /// A renaming restated every obligation and was turned down by
    /// [`Self::keeps_preconditions_variables`].
    unbound_at_a_leaf: bool,
}

impl RenamingSearch<'_> {
    /// A renaming extending `held` under which every one of `owed` has a counterpart.
    fn extend(&mut self, owed: &[Obligation<'_>], held: &Renaming) -> Search {
        let Some((first, rest)) = owed.split_first() else {
            if self.keeps_preconditions_variables(held) {
                return Search::Found;
            }
            self.unbound_at_a_leaf = true;
            return Search::Exhausted;
        };
        for (spec, imp) in &first.pairs {
            if self.budget == 0 {
                return Search::Abandoned;
            }
            self.budget -= 1;
            if let Some(next) = held.extended_to(self.kb, self.vars, spec, imp) {
                match self.extend(rest, &next) {
                    Search::Exhausted => {}
                    done => return done,
                }
            }
        }
        Search::Exhausted
    }

    /// Does the renaming keep every variable the spec operation's preconditions bind bound
    /// by the override's? A variable a spec `requires` holds is the one the precondition
    /// names, and an `ensures` sharing it promises something of THAT value
    /// (`requires holds(n, ?k) ensures holds(result, ?k)`). An override that drops the
    /// precondition and restates the promise over a variable of its own promises it of
    /// some value, not of that one — a weaker postcondition, which no clause-by-clause
    /// comparison sees: the `ensures` reads the same. A variable the spec operation's
    /// `ensures` alone holds is the clause's own, and its image may be anything.
    ///
    /// The other direction holds by construction: an override variable its `requires`
    /// holds restates one the spec operation's `requires` holds, since every override
    /// precondition is one of the spec operation's under the renaming.
    fn keeps_preconditions_variables(&self, held: &Renaming) -> bool {
        held.spec_to_impl.iter().all(|(sv, iv)| {
            !self.bound_by_spec_pre.contains(sv) || self.bound_by_impl_pre.contains(iv)
        })
    }
}

/// WI-20260822-59CDQ's question for [`result_binder_discharges`], read up to a renaming:
/// does the override's clause `imp` restate the spec operation's `spec` under SOME renaming
/// of their clause variables? Each pair on its own, not the contract's one renaming: the
/// question is whether the `result` alignment is what makes a pair fit, and a pair that
/// fits with it under one renaming and without it under none is that.
pub(super) fn restates_up_to_renaming(kb: &KnowledgeBase, vars: &ClauseVariables, spec: &Value, imp: &Value) -> bool {
    Renaming::default().extended_to(kb, vars, spec, imp).is_some()
}

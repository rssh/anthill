//! WI-20261121-G8E02 — the proof an SLD search makes, kept by the search in PROOF MODE and
//! given back as an `anthill.reflect.SLDProof` term (proposal 075; `docs/kernel-language.md`
//! §8.3, "The proof of a goal"; the relation is `anthill.reflect.SLDProof.of`).
//!
//! THE RECORD. A search in proof mode tags every goal it holds with a NODE ([`ProofTag`]): the
//! goal's place in the derivation — a query goal, or a body goal of an INSTANCE. An instance is
//! what one ATTEMPT of a node took: a clause opened for it, a builtin's answer, an assumption,
//! a mounted row, the parts a structure splits into (a `forall`'s instances, a side of `|`, a
//! splice), a discharge, a negation that held. An attempt is one asking of a node's goal on one
//! branch. The three tables only GROW, so what a branch recorded survives the backtracking that
//! drops the branch — which is what makes a refutation, the record of a search that failed on
//! every branch, buildable after the fact.
//!
//! A POSITIVE proof is read along ONE branch: the frame's [`PathCell`] list names the instance
//! each node took on it, newest first, and the proof is built from the query's node down.
//!
//! A REFUTATION is read off the WHOLE record. An attempt that never EXITED — its goal was proved
//! on no branch below it — and was not POSTPONED (delayed or rotated, to be asked again) is a
//! failure, and the failed attempts of its instances' body nodes are its steps: for each clause
//! whose head matched, on each branch, the body goal the branch failed at. The goals after the
//! one a branch failed at were never asked, and are in no step.
//!
//! An attempt EXITS each time its goal is proved on a branch: when the instance it took has no
//! body goal left in the frame. [`ProofRecorder::proved`] is told when an instance with no body
//! is taken, and propagates upward through every instance whose last outstanding goal that was.
//!
//! OFF BY DEFAULT. A search that is not asked for a proof has no recorder, tags no goal and
//! keeps no path: every hook in the resolver is behind `self.proof.is_some()`.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use smallvec::SmallVec;

use crate::eval::value::Value;
use crate::intern::Symbol;

use super::subst::Substitution;
use super::term::{Literal, Term, TermId, Var};
use super::{KnowledgeBase, RuleId};

/// A goal's place in the proof record: its NODE, and the ATTEMPT that is asking it now (`0`
/// while it is not being asked — before its turn, and again after a rotation). `0` for both
/// outside proof mode, and for the goals the resolver adds that are no goal of the derivation
/// (a discharge's assumption-pop marker).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct ProofTag {
    pub(crate) node: u32,
    pub(crate) attempt: u32,
}

impl ProofTag {
    pub(crate) const NONE: ProofTag = ProofTag { node: 0, attempt: 0 };

    /// A node that has not been asked yet.
    pub(crate) fn of(node: u32) -> Self {
        ProofTag { node, attempt: 0 }
    }

    /// The same node, no longer being asked: it was rotated behind the tail, to be asked again.
    pub(crate) fn unasked(self) -> Self {
        ProofTag { node: self.node, attempt: 0 }
    }
}

/// What one attempt of a node took.
#[derive(Clone, Debug)]
pub(crate) enum InstanceKind {
    /// A clause of the knowledge base, a fact or a rule.
    Clause(RuleId),
    /// A row of a mounted extent: a fact of no clause.
    Row,
    /// An assumption of an enclosing discharge.
    Assumption,
    /// A builtin that held, with nothing left to prove.
    Builtin,
    /// The goals a structure splits into: a `forall`'s instances, a side of `|` or a `some`'s
    /// element, the goals a builtin spliced in, a conjunction's two sides.
    Parts,
    /// A discharge `(forall(?x…), A -: C)`: its fresh constants (each binder's name and the
    /// rigid variable's id) and its assumptions, skolemized. The body is `C`.
    Discharge { fresh: Vec<(Symbol, u32)>, assumed: Vec<Value> },
    /// A negation `!q` that held: its proof is `q`'s refutation, built already.
    NegationHolds(TermId),
}

struct NodeRec {
    /// The instance the node is a body goal of; `0` for a query goal.
    parent: u32,
}

struct AttemptRec {
    node: u32,
    /// The goal as it was asked, its substitution applied then; a proof applies the final one.
    goal: Value,
    /// The goal was a builtin when it was asked (a goal a view rewrote into one counts).
    builtin: bool,
    /// How many times the goal was proved on a branch below this attempt.
    exits: u32,
    /// The goal was rotated behind the tail to be asked again: it did not fail here.
    postponed: bool,
    /// For a negation `!q` that FAILED: the proof of `q` that made it fail.
    negated: Option<TermId>,
    instances: Vec<u32>,
}

struct InstanceRec {
    attempt: u32,
    kind: InstanceKind,
    body: Vec<u32>,
}

/// One step of a branch's path: on it, `node` took `instance`. A persistent list, newest
/// first, shared with the frames the branch was copied from, so a choice point's branches share
/// their common prefix and backtracking drops a branch's part with the branch.
pub(crate) struct PathCell {
    node: u32,
    instance: u32,
    prev: Option<Rc<PathCell>>,
}

/// The path `prev` extended by `node` taking `instance`.
pub(crate) fn extend_path(prev: &Option<Rc<PathCell>>, node: u32, instance: u32) -> Option<Rc<PathCell>> {
    Some(Rc::new(PathCell {
        node,
        instance,
        prev: prev.clone(),
    }))
}

/// The proof record of one search ([`super::resolve::SearchStream`] in proof mode).
#[derive(Default)]
pub(crate) struct ProofRecorder {
    nodes: Vec<NodeRec>,
    attempts: Vec<AttemptRec>,
    instances: Vec<InstanceRec>,
}

impl ProofRecorder {
    /// A query goal's node.
    pub(crate) fn root(&mut self) -> u32 {
        self.nodes.push(NodeRec { parent: 0 });
        self.nodes.len() as u32
    }

    fn node(&self, id: u32) -> &NodeRec {
        &self.nodes[id as usize - 1]
    }

    fn attempt(&self, id: u32) -> &AttemptRec {
        &self.attempts[id as usize - 1]
    }

    fn attempt_mut(&mut self, id: u32) -> &mut AttemptRec {
        &mut self.attempts[id as usize - 1]
    }

    fn instance(&self, id: u32) -> &InstanceRec {
        &self.instances[id as usize - 1]
    }

    /// `node` is asked: a new attempt, of `goal` as it is asked.
    pub(crate) fn begin_attempt(&mut self, node: u32, goal: Value) -> u32 {
        self.attempts.push(AttemptRec {
            node,
            goal,
            builtin: false,
            exits: 0,
            postponed: false,
            negated: None,
            instances: Vec::new(),
        });
        self.attempts.len() as u32
    }

    /// The goal `attempt` asks is a builtin.
    pub(crate) fn mark_builtin(&mut self, attempt: u32) {
        if attempt != 0 {
            self.attempt_mut(attempt).builtin = true;
        }
    }

    /// `attempt`'s goal is rotated behind the tail, to be asked again by a later attempt.
    pub(crate) fn postpone(&mut self, attempt: u32) {
        if attempt != 0 {
            self.attempt_mut(attempt).postponed = true;
        }
    }

    /// `attempt` asks a negation `!q` that FAILED, because `q` holds with `proof`.
    pub(crate) fn set_negated(&mut self, attempt: u32, proof: TermId) {
        if attempt != 0 {
            self.attempt_mut(attempt).negated = Some(proof);
        }
    }

    /// `attempt` takes an instance of `kind` with `n` body goals: the instance, and the nodes of
    /// its body goals, in order.
    pub(crate) fn open(&mut self, attempt: u32, kind: InstanceKind, n: usize) -> (u32, Vec<u32>) {
        self.instances.push(InstanceRec {
            attempt,
            kind,
            body: Vec::with_capacity(n),
        });
        let id = self.instances.len() as u32;
        let mut body = Vec::with_capacity(n);
        for _ in 0..n {
            self.nodes.push(NodeRec { parent: id });
            body.push(self.nodes.len() as u32);
        }
        self.instances[id as usize - 1].body = body.clone();
        if attempt != 0 {
            self.attempt_mut(attempt).instances.push(id);
        }
        (id, body)
    }

    /// `attempt`'s goal is PROVED on this branch — by an instance with no body goal, or by one
    /// whose body goals the frame no longer holds. `remaining` are the nodes of the goals the
    /// frame still holds. The exit propagates to every enclosing instance that held no other
    /// outstanding goal.
    pub(crate) fn proved(&mut self, attempt: u32, remaining: impl Iterator<Item = u32>) {
        if attempt == 0 {
            return;
        }
        // Every instance some remaining goal is inside: those are not done.
        let mut open: HashSet<u32> = HashSet::new();
        for r in remaining {
            let mut n = r;
            while n != 0 {
                let inst = self.node(n).parent;
                if inst == 0 || !open.insert(inst) {
                    break;
                }
                let a = self.instance(inst).attempt;
                if a == 0 {
                    break;
                }
                n = self.attempt(a).node;
            }
        }
        let mut a = attempt;
        loop {
            self.attempt_mut(a).exits += 1;
            let inst = self.node(self.attempt(a).node).parent;
            if inst == 0 || open.contains(&inst) {
                return;
            }
            a = self.instance(inst).attempt;
            if a == 0 {
                return;
            }
        }
    }

    /// The positive proof of the query goal `root` along the branch whose path is `path`, under
    /// the branch's final substitution. `residual` are the goals the branch left unchecked, by
    /// node. An `Err` names a goal the branch discharged by a step that recorded nothing — a
    /// resolver path proof mode does not cover yet, which is reported, never guessed.
    pub(crate) fn positive(
        &self,
        kb: &mut KnowledgeBase,
        path: &Option<Rc<PathCell>>,
        root: u32,
        subst: &Substitution,
        residual: &[(u32, Value)],
    ) -> Result<TermId, String> {
        let mut took: HashMap<u32, u32> = HashMap::new();
        let mut cell = path.as_ref();
        while let Some(c) = cell {
            took.entry(c.node).or_insert(c.instance);
            cell = c.prev.as_ref();
        }
        let left: HashMap<u32, &Value> = residual.iter().map(|(n, g)| (*n, g)).collect();
        let syms = ProofSyms::resolve(kb)?;
        let mut b = Builder { kb, syms, subst };
        self.positive_node(&mut b, &took, &left, root)
    }

    fn positive_node(
        &self,
        b: &mut Builder<'_>,
        took: &HashMap<u32, u32>,
        left: &HashMap<u32, &Value>,
        node: u32,
    ) -> Result<TermId, String> {
        let Some(&inst) = took.get(&node) else {
            return match left.get(&node) {
                Some(goal) => {
                    let g = b.goal(goal)?;
                    Ok(b.entity(b.syms.residual, &[g]))
                }
                None => Err(format!(
                    "proof mode: goal node {node} was discharged by a step that recorded no proof"
                )),
            };
        };
        let rec = self.instance(inst);
        let goal_value = self.attempt(rec.attempt).goal.clone();
        let goal = b.goal(&goal_value)?;
        let body = |b: &mut Builder<'_>| -> Result<TermId, String> {
            let parts: Vec<TermId> = rec
                .body
                .iter()
                .map(|&n| self.positive_node(b, took, left, n))
                .collect::<Result<_, _>>()?;
            Ok(b.kb.build_list(&parts))
        };
        match &rec.kind {
            InstanceKind::Clause(rid) => {
                let clause = b.clause_label(Some(*rid));
                let body = body(b)?;
                Ok(b.entity(b.syms.by_clause, &[goal, clause, body]))
            }
            InstanceKind::Row | InstanceKind::Parts => {
                let clause = b.clause_label(None);
                let body = body(b)?;
                Ok(b.entity(b.syms.by_clause, &[goal, clause, body]))
            }
            InstanceKind::Assumption => Ok(b.entity(b.syms.by_assumption, &[goal])),
            InstanceKind::Builtin => Ok(b.entity(b.syms.by_builtin, &[goal])),
            InstanceKind::NegationHolds(refutation) => Ok(*refutation),
            InstanceKind::Discharge { fresh, assumed } => {
                let fresh_terms: Vec<TermId> = fresh.iter().map(|&(n, id)| b.fresh_constant(n, id)).collect();
                let fresh = b.kb.build_list(&fresh_terms);
                let assumed_terms: Vec<TermId> = assumed.iter().map(|a| b.goal(a)).collect::<Result<_, _>>()?;
                let assumed = b.kb.build_list(&assumed_terms);
                let proof = if rec.body.len() == 1 {
                    self.positive_node(b, took, left, rec.body[0])?
                } else {
                    let clause = b.clause_label(None);
                    let body = body(b)?;
                    b.entity(b.syms.by_clause, &[goal, clause, body])
                };
                Ok(b.entity(b.syms.by_discharge, &[goal, fresh, assumed, proof]))
            }
        }
    }

    /// The refutation of the query goal `root`, read off the record of a search that ended
    /// with no answer and was complete. An `Err` where the record holds no failed attempt of
    /// `root`.
    pub(crate) fn refutation(&self, kb: &mut KnowledgeBase, root: u32) -> Result<TermId, String> {
        let mut by_node: HashMap<u32, Vec<u32>> = HashMap::new();
        for (i, a) in self.attempts.iter().enumerate() {
            by_node.entry(a.node).or_default().push(i as u32 + 1);
        }
        let failed_root = by_node
            .get(&root)
            .and_then(|atts| atts.iter().rev().copied().find(|&a| self.failed(a)))
            .ok_or_else(|| "proof mode: the record holds no failed attempt of the goal".to_string())?;
        let syms = ProofSyms::resolve(kb)?;
        let empty = Substitution::default();
        let mut b = Builder { kb, syms, subst: &empty };
        self.refuted_attempt(&mut b, &by_node, failed_root)
    }

    fn failed(&self, a: u32) -> bool {
        let rec = self.attempt(a);
        rec.exits == 0 && !rec.postponed
    }

    /// The proof that `attempt`'s goal fails: of `!goal`.
    fn refuted_attempt(
        &self,
        b: &mut Builder<'_>,
        by_node: &HashMap<u32, Vec<u32>>,
        attempt: u32,
    ) -> Result<TermId, String> {
        let rec = self.attempt(attempt);
        if let Some(p) = rec.negated {
            // A negation `!q` that failed: `q` holds, and its proof is the reason.
            return Ok(p);
        }
        let goal = b.goal(&rec.goal.clone())?;
        if rec.instances.is_empty() {
            if rec.builtin {
                return Ok(b.entity(b.syms.builtin_false, &[goal]));
            }
            let none = b.kb.build_list(&[]);
            return Ok(b.entity(b.syms.refuted, &[goal, none]));
        }
        // One discharge instance: the proof of !discharge is the discharge, under its fresh
        // constants and assumptions, with its consequent refuted.
        if rec.instances.len() == 1 {
            if let InstanceKind::Discharge { fresh, assumed } = &self.instance(rec.instances[0]).kind {
                let inst = self.instance(rec.instances[0]);
                let fresh_terms: Vec<TermId> = fresh.iter().map(|&(n, id)| b.fresh_constant(n, id)).collect();
                let fresh = b.kb.build_list(&fresh_terms);
                let assumed_terms: Vec<TermId> = assumed.iter().map(|a| b.goal(a)).collect::<Result<_, _>>()?;
                let assumed = b.kb.build_list(&assumed_terms);
                let failed_only = match inst.body.as_slice() {
                    [only] => by_node.get(only).and_then(|atts| atts.iter().copied().find(|&a| self.failed(a))),
                    _ => None,
                };
                let inner = match failed_only {
                    Some(a) => self.refuted_attempt(b, by_node, a)?,
                    None => {
                        let steps = self.steps(b, by_node, inst)?;
                        let list = b.kb.build_list(&steps);
                        b.entity(b.syms.refuted, &[goal, list])
                    }
                };
                return Ok(b.entity(b.syms.by_discharge, &[goal, fresh, assumed, inner]));
            }
        }
        let mut steps = Vec::new();
        for &inst in &rec.instances {
            steps.extend(self.steps(b, by_node, self.instance(inst))?);
        }
        let list = b.kb.build_list(&steps);
        Ok(b.entity(b.syms.refuted, &[goal, list]))
    }

    /// The steps of one instance: each failed attempt of one of its body goals, on its branch.
    fn steps(
        &self,
        b: &mut Builder<'_>,
        by_node: &HashMap<u32, Vec<u32>>,
        inst: &InstanceRec,
    ) -> Result<Vec<TermId>, String> {
        let clause = match &inst.kind {
            InstanceKind::Clause(rid) => b.clause_label(Some(*rid)),
            _ => b.clause_label(None),
        };
        let mut out = Vec::new();
        for n in &inst.body {
            let Some(atts) = by_node.get(n) else { continue };
            for &a in atts {
                if !self.failed(a) {
                    continue;
                }
                let failing = b.goal(&self.attempt(a).goal.clone())?;
                let because = self.refuted_attempt(b, by_node, a)?;
                out.push(b.entity(b.syms.step, &[clause, failing, because]));
            }
        }
        Ok(out)
    }
}

/// The symbols of `anthill.reflect.SLDProof`'s constructors and of what they hold.
struct ProofSyms {
    by_clause: Symbol,
    by_builtin: Symbol,
    by_assumption: Symbol,
    residual: Symbol,
    refuted: Symbol,
    builtin_false: Symbol,
    by_discharge: Symbol,
    step: Symbol,
    fresh_constant: Symbol,
    some: Symbol,
    none: Symbol,
}

impl ProofSyms {
    fn resolve(kb: &KnowledgeBase) -> Result<Self, String> {
        let get = |qn: &str| {
            kb.try_resolve_symbol(qn)
                .ok_or_else(|| format!("`{qn}` is not loaded: a proof is given only where `anthill.reflect` is"))
        };
        Ok(ProofSyms {
            by_clause: get("anthill.reflect.SLDProof.by_clause")?,
            by_builtin: get("anthill.reflect.SLDProof.by_builtin")?,
            by_assumption: get("anthill.reflect.SLDProof.by_assumption")?,
            residual: get("anthill.reflect.SLDProof.residual")?,
            refuted: get("anthill.reflect.SLDProof.refuted")?,
            builtin_false: get("anthill.reflect.SLDProof.builtin_false")?,
            by_discharge: get("anthill.reflect.SLDProof.by_discharge")?,
            step: get("anthill.reflect.Step")?,
            fresh_constant: get("anthill.reflect.FreshConstant")?,
            some: get("anthill.prelude.Option.some")?,
            none: get("anthill.prelude.Option.none")?,
        })
    }
}

/// Builds the terms of a proof.
struct Builder<'a> {
    kb: &'a mut KnowledgeBase,
    syms: ProofSyms,
    subst: &'a Substitution,
}

impl Builder<'_> {
    /// `functor` over its declared fields, `args` in declaration order.
    fn entity(&mut self, functor: Symbol, args: &[TermId]) -> TermId {
        let fields: Vec<Symbol> = self
            .kb
            .entity_field_names(functor)
            .map(|f| f.to_vec())
            .unwrap_or_else(|| panic!("`{}` declares no fields", self.kb.qualified_name_of(functor)));
        assert_eq!(
            fields.len(),
            args.len(),
            "`{}` declares {} fields, {} given",
            self.kb.qualified_name_of(functor),
            fields.len(),
            args.len()
        );
        let named: SmallVec<[(Symbol, TermId); 2]> = fields.into_iter().zip(args.iter().copied()).collect();
        self.kb.make_entity_term(functor, SmallVec::new(), named)
    }

    /// A clause by its label: `some(label)`, or `none` where there is no clause or it has none.
    fn clause_label(&mut self, rid: Option<RuleId>) -> TermId {
        match rid.and_then(|r| self.kb.rule_label(r)) {
            Some(label) => {
                let l = self.kb.alloc(Term::Ref(label));
                let some = self.syms.some;
                self.entity(some, &[l])
            }
            None => self.kb.alloc(Term::Ref(self.syms.none)),
        }
    }

    fn fresh_constant(&mut self, name: Symbol, id: u32) -> TermId {
        let name_text = self.kb.local_name_of(name).to_string();
        let n = self.kb.alloc(Term::Const(Literal::String(name_text)));
        let i = self.kb.alloc(Term::Const(Literal::Int(i64::from(id))));
        let f = self.syms.fresh_constant;
        self.entity(f, &[n, i])
    }

    /// A goal as a proof holds it: the final substitution applied, every fresh constant a
    /// [`FreshConstant`](ProofSyms::fresh_constant) and every call quoted, as a `Term` field
    /// holds one (§8.3).
    /// A goal holding a value with no term form (a closure, a stream) cannot be written in a
    /// proof, and is an `Err`, never a stand-in.
    fn goal(&mut self, goal: &Value) -> Result<TermId, String> {
        let applied = self.kb.reify_value(goal, self.subst);
        let term = super::node_occurrence::value_to_term(self.kb, &applied)
            .map_err(|e| format!("proof mode: a goal has no term form to write in a proof ({e:?})"))?;
        let term = self.without_rigid(term);
        Ok(self.kb.quoted_code_term(term))
    }

    /// `t` with each rigid variable a `FreshConstant`.
    fn without_rigid(&mut self, t: TermId) -> TermId {
        match self.kb.get_term(t).clone() {
            Term::Var(Var::Rigid(v)) => self.fresh_constant(v.name(), v.raw()),
            Term::Fn {
                functor,
                pos_args,
                named_args,
            } => {
                let pos: SmallVec<[TermId; 4]> = pos_args.iter().map(|&a| self.without_rigid(a)).collect();
                let named: SmallVec<[(Symbol, TermId); 2]> =
                    named_args.iter().map(|&(k, a)| (k, self.without_rigid(a))).collect();
                if pos == pos_args && named == named_args {
                    t
                } else {
                    self.kb.alloc(Term::Fn {
                        functor,
                        pos_args: pos,
                        named_args: named,
                    })
                }
            }
            _ => t,
        }
    }
}

#[cfg(test)]
mod tests {
    //! THE CONTROL: proof mode changes no search. Each goal is resolved twice, once as an ordinary
    //! search and once in proof mode, under one configuration: the two take the same number of
    //! steps and give the same answers. A hook that altered the search — a goal reordered, a
    //! candidate dropped, a step added — would move a count here, which a proof's shape need not
    //! show. Passes with the hooks and without them, by design: it is the guard on the hooks.
    use crate::eval::value::Value;
    use crate::kb::resolve::ResolveConfig;
    use crate::kb::term::{Literal, Term, TermId, Var};
    use crate::kb::KnowledgeBase;

    const SRC: &str = "namespace g8u
  import anthill.prelude.{Int64}
  rule pos(?x) :- ?x > 0
  rule big(?x) :- ?x > 5
  rule even(?x) :- ?x % 2 = 0
  rule good(?x) :- pos(?x), big(?x), even(?x)
  fact edge(1, 2)
  fact edge(1, 3)
  rule reach_big(?x) :- edge(?x, ?y), big(?y)
  rule all_big(?xs) :- (forall ?y in ?xs: ?y > 5)
  rule q(?x) :- ?x > 0
  rule notq(?x) :- !q(?x)
  rule loop(?x) :- loop(?x)
  rule guarded(?x) :- loop(?x), ?x > 5
  enum IntList
    entity i_nil
    entity i_cons(head: Int64, tail: IntList)
  end
  fact prop_holds(i_nil)
  rule prop_holds(i_cons(head: ?_h, tail: ?t)) :- prop_holds(?t)
end
";

    fn int(kb: &mut KnowledgeBase, n: i64) -> TermId {
        kb.alloc(Term::Const(Literal::Int(n)))
    }

    fn goal(kb: &mut KnowledgeBase, qn: &str, args: Vec<TermId>) -> Value {
        let f = kb.try_resolve_symbol(qn).unwrap_or_else(|| panic!("`{qn}` resolves"));
        kb.make_goal_value(f, args.into_iter().map(Value::term).collect())
    }

    #[test]
    fn proof_mode_takes_the_steps_and_gives_the_answers_of_the_search() {
        let mut kb = crate::kb::test_support::load_stdlib(Some(SRC));
        let config = ResolveConfig {
            max_depth: 40,
            dedup_answers: false,
            ..ResolveConfig::default()
        };
        let (six, one) = (int(&mut kb, 6), int(&mut kb, 1));
        let five = int(&mut kb, 5);
        let elems = [7, 3, 9].map(|n| int(&mut kb, n));
        let list = kb.build_list(&elems);
        let y_name = kb.intern("y");
        let y = kb.fresh_var(y_name);
        let y = kb.alloc(Term::Var(Var::Global(y)));
        let pred = kb.try_resolve_symbol("g8u.prop_holds").unwrap();
        let pred = kb.alloc(Term::Ref(pred));
        let goals = vec![
            goal(&mut kb, "g8u.good", vec![six]),
            goal(&mut kb, "g8u.good", vec![one]),
            goal(&mut kb, "g8u.reach_big", vec![one]),
            goal(&mut kb, "g8u.all_big", vec![list]),
            goal(&mut kb, "g8u.notq", vec![one]),
            goal(&mut kb, "g8u.notq", vec![five]),
            goal(&mut kb, "g8u.edge", vec![one, y]),
            goal(&mut kb, "g8u.guarded", vec![one]),
            goal(&mut kb, "g8u.IntList.induction", vec![pred]),
        ];
        for g in goals {
            let (plain, stats) = kb.resolve_goals_with_stats(vec![g.clone()], &config);
            let stream = kb.resolve_lazy_goal_with_proof(g.clone(), &config);
            let proved = stream.drain_with_proofs(&mut kb, false);
            assert_eq!(proved.steps, stats.steps, "proof mode took other steps for {g:?}");
            assert_eq!(proved.truncated, stats.truncated, "proof mode cut the search otherwise for {g:?}");
            assert_eq!(proved.answers.len(), plain.len(), "proof mode answered otherwise for {g:?}");
            for ((a, proof), b) in proved.answers.iter().zip(&plain) {
                assert_eq!(a.is_definite(), b.is_definite(), "{g:?}");
                assert!(proof.is_ok(), "every answer has its proof, for {g:?}: {proof:?}");
            }
        }
    }

    /// `SLDProof.of(!g, ?p)` is decided as `!g` is, under Γ too (kernel-language §8.3): a
    /// negand that holds an open-world reference — a `var_ref`, a binder whose value is
    /// unknown — has no answer and never will, so the negation flounders and its proof form
    /// gives no refutation. Each is asked as a query of its own, and the two verdicts agree.
    ///
    /// PASSES WITH AND WITHOUT a gate of `step_naf`'s in `step_sld_proof_of`, BY DESIGN
    /// (MEASURED 2026-11-22, the open-world gate added and taken out): the search for the
    /// negand answers the `var_ref` goal `Unknown` itself, so the proof form needs no gate of
    /// its own. It guards that agreement, which a change to either path could break.
    #[test]
    fn a_negation_under_gamma_is_decided_as_the_negation_is() {
        use crate::kb::discrim::SubstTree;
        use smallvec::SmallVec;
        let mut kb = crate::kb::test_support::load_stdlib(Some(SRC));
        let config = ResolveConfig {
            gamma: Some(std::rc::Rc::new(SubstTree::new())),
            ..ResolveConfig::default()
        };
        let var_ref = kb.try_resolve_symbol("anthill.reflect.Expr.var_ref").unwrap();
        let name_field = kb.entity_field_names(var_ref).unwrap()[0];
        let x = kb.intern("x");
        let x = kb.alloc(Term::Ref(x));
        let open = kb.make_entity_term(var_ref, SmallVec::new(), SmallVec::from_slice(&[(name_field, x)]));
        // No fact matches it, so a search refutes it outright; the negation must not.
        let nine = int(&mut kb, 9);
        let inner = goal(&mut kb, "g8u.edge", vec![open, nine]);
        let not = kb.try_resolve_symbol("anthill.kernel.not").unwrap();
        let negation = kb.make_goal_value(not, vec![inner]);
        let of = kb.try_resolve_symbol("anthill.reflect.SLDProof.of").unwrap();
        let p_name = kb.intern("p");
        let p = kb.fresh_var(p_name);
        let p = Value::term(kb.alloc(Term::Var(Var::Global(p))));
        let ask = kb.make_goal_value(of, vec![negation.clone(), p]);

        let (plain, _) = kb.resolve_goals_with_stats(vec![negation], &config);
        let (proved, _) = kb.resolve_goals_with_stats(vec![ask], &config);
        assert_eq!((plain.len(), proved.len()), (1, 1), "each is answered, conditionally");
        assert!(
            plain.iter().all(|s| !s.is_definite()),
            "the control: `!edge(var_ref(x), 9)` under Γ is undecided"
        );
        assert!(
            proved.iter().all(|s| !s.is_definite()),
            "its proof form is undecided too, never a refutation: {} definite answer(s)",
            proved.iter().filter(|s| s.is_definite()).count()
        );
    }
}

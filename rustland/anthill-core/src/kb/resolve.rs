/// SLD resolution + equational simplification.
///
/// Two behavioral modes, both backed by the same KB:
/// - **Derivation rule** (body non-empty): backward-chaining SLD resolution
/// - **Equation** (head is `eq(lhs, rhs)`, body empty): rewrite `lhs` → `rhs`
///
/// Ground facts (head not `eq(...)`, body empty) are matched directly during
/// resolution as base cases.
///
/// Goals are always maximally concrete (no unresolved var chains). The answer
/// substitution is always flat (path-compressed on merge) — no `walk` needed.

use smallvec::SmallVec;

use super::subst::Substitution;
use super::term::{Term, TermId};
use super::RuleId;
use super::KnowledgeBase;

// ── Configuration ───────────────────────────────────────────────

/// Configuration for SLD resolution.
pub struct ResolveConfig {
    /// Maximum resolution depth (default 100).
    pub max_depth: usize,
    /// Maximum number of solutions to collect (0 = unlimited).
    pub max_solutions: usize,
    /// Whether to apply equational rewriting as fallback during resolution.
    pub simplify: bool,
}

impl Default for ResolveConfig {
    fn default() -> Self {
        Self {
            max_depth: 100,
            max_solutions: 0,
            simplify: false,
        }
    }
}

// ── Solution ────────────────────────────────────────────────────

/// A successful resolution result: variable bindings collected during proof.
///
/// The substitution is always flat (path-compressed) — use `subst.resolve(vid)`
/// directly, no `walk` needed.
pub struct Solution {
    pub subst: Substitution,
}

// ── EqChange ────────────────────────────────────────────────────

/// Record of an equational rewrite step.
#[allow(dead_code)]
pub struct EqChange {
    pub rule_id: RuleId,
    pub original: TermId,
    pub rewritten: TermId,
}

// ── SLD Resolution ──────────────────────────────────────────────

impl KnowledgeBase {
    /// Resolve a list of goals using SLD resolution.
    ///
    /// Returns all solutions (up to `config.max_solutions`) that satisfy all
    /// goals simultaneously. Each solution contains variable bindings from
    /// the original query variables to ground terms.
    pub fn resolve(&mut self, goals: &[TermId], config: &ResolveConfig) -> Vec<Solution> {
        let mut solutions = Vec::new();
        let goals = goals.to_vec();
        let subst = Substitution::new();
        self.resolve_goals(&goals, &subst, 0, config, &mut solutions);
        solutions
    }

    fn resolve_goals(
        &mut self,
        goals: &[TermId],
        answer_subst: &Substitution,
        depth: usize,
        config: &ResolveConfig,
        solutions: &mut Vec<Solution>,
    ) {
        // Check limits
        if depth > config.max_depth {
            return;
        }
        if config.max_solutions > 0 && solutions.len() >= config.max_solutions {
            return;
        }

        // All goals solved — success
        if goals.is_empty() {
            solutions.push(Solution { subst: answer_subst.clone() });
            return;
        }

        // Select first goal (already maximally concrete)
        let goal = goals[0];

        // Query discrimination tree for candidate rules/facts
        let mut candidates = self.query(goal);

        // Fallback: if no non-equation matches, try equational rewriting
        if config.simplify {
            let has_non_eq = candidates.iter().any(|(rid, _)| !self.is_equation(*rid));
            if !has_non_eq {
                let (rewritten, changes) = self.apply_eq_rules(goal, 100);
                if !changes.is_empty() {
                    candidates = self.query(rewritten);
                }
            }
        }

        for (rid, tree_subst) in candidates {
            if config.max_solutions > 0 && solutions.len() >= config.max_solutions {
                return;
            }

            // Skip equations during resolution — they are used by simplify
            if self.is_equation(rid) {
                continue;
            }

            let body = self.rule_body(rid).to_vec();

            if body.is_empty() {
                // Ground fact — apply concrete bindings to remaining goals
                let remaining = self.apply_subst_each(&goals[1..], &tree_subst);
                let mut merged = answer_subst.clone();
                merged.bind_compressed(
                    tree_subst.bindings.into_iter(),
                    &self.terms,
                );
                self.resolve_goals(&remaining, &merged, depth + 1, config, solutions);
            } else {
                // Rule with body — one walk: rename vars + substitute concrete values
                let (fresh_body, answer_links) = self.with_fresh_vars(rid, &tree_subst);

                // Apply tree_subst's query-var bindings to remaining goals
                let remaining = self.apply_subst_each(&goals[1..], &tree_subst);

                // Merge answer links (query vars → fresh vars) into answer_subst
                let mut merged = answer_subst.clone();
                merged.bind_compressed(
                    answer_links.bindings.into_iter(),
                    &self.terms,
                );

                // Prepend fresh body goals before remaining goals
                let mut new_goals = fresh_body;
                new_goals.extend(remaining);
                self.resolve_goals(&new_goals, &merged, depth + 1, config, solutions);
            }
        }
    }

    // ── Equational Rewriting ────────────────────────────────────

    /// Simplify a term using equational rules in the KB.
    ///
    /// Strategy: innermost (simplify subterms first, then try rewriting
    /// at the top level). Uses fuel to prevent non-termination from
    /// divergent rewrite systems.
    pub fn simplify(&mut self, term: TermId) -> TermId {
        let (result, _) = self.apply_eq_rules(term, 100);
        result
    }

    /// Apply equational rules to rewrite a term.
    ///
    /// Strategy: innermost — rewrite subterms first, then try top level.
    /// Returns `(rewritten_term, changes)`.
    pub fn apply_eq_rules(&mut self, term: TermId, fuel: usize) -> (TermId, Vec<EqChange>) {
        if fuel == 0 {
            return (term, vec![]);
        }

        let mut changes = Vec::new();

        // 1. Innermost: try rewriting subterms first
        let current = match self.terms.get(term).clone() {
            Term::Fn { functor, pos_args, named_args } => {
                let new_pos: SmallVec<[TermId; 4]> = pos_args
                    .iter()
                    .map(|&id| {
                        let (rewritten, sub_changes) = self.apply_eq_rules(id, fuel - 1);
                        changes.extend(sub_changes);
                        rewritten
                    })
                    .collect();
                let new_named: SmallVec<[(crate::intern::Symbol, TermId); 2]> = named_args
                    .iter()
                    .map(|&(sym, id)| {
                        let (rewritten, sub_changes) = self.apply_eq_rules(id, fuel - 1);
                        changes.extend(sub_changes);
                        (sym, rewritten)
                    })
                    .collect();
                self.alloc(Term::Fn { functor, pos_args: new_pos, named_args: new_named })
            }
            _ => term,
        };

        // 2. Try rewriting at top level using eq(current, ?result) pattern
        let r_sym = self.intern("_r");
        let r_vid = self.fresh_var(r_sym);
        let result_var = self.alloc(Term::Var(r_vid));

        let eq_sym = self.intern("eq");
        let pattern = self.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[current, result_var]),
            named_args: SmallVec::new(),
        });

        let candidates = self.query(pattern);

        for (rid, tree_subst) in candidates {
            if !self.is_equation(rid) {
                continue;
            }

            // Reify the result variable to get the RHS
            let rhs = self.reify(result_var, &tree_subst);

            changes.push(EqChange {
                rule_id: rid,
                original: current,
                rewritten: rhs,
            });

            // Continue rewriting the result
            let (final_term, more_changes) = self.apply_eq_rules(rhs, fuel - 1);
            changes.extend(more_changes);
            return (final_term, changes);
        }

        (current, changes)
    }
}

// ── Tests ───────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kb::term::{Literal, Term};
    use smallvec::SmallVec;

    // ── match_term tests (via discrim tree) ─────────────────────

    #[test]
    fn match_term_var_const() {
        let mut kb = KnowledgeBase::new();
        let x_sym = kb.intern("x");
        let vid = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(vid));
        let val = kb.alloc(Term::Const(Literal::Int(42)));

        let s = kb.match_term(var_x, val).expect("should match");
        assert_eq!(s.resolve(vid), Some(val));
    }

    #[test]
    fn match_term_fn_structure() {
        let mut kb = KnowledgeBase::new();
        let f_sym = kb.intern("f");
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(vx));
        let val = kb.alloc(Term::Const(Literal::Int(1)));

        let t1 = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let t2 = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });

        let s = kb.match_term(t1, t2).expect("should match");
        assert_eq!(s.resolve(vx), Some(val));
    }

    #[test]
    fn match_term_mismatch() {
        let mut kb = KnowledgeBase::new();
        let v1 = kb.alloc(Term::Const(Literal::Int(1)));
        let v2 = kb.alloc(Term::Const(Literal::Int(2)));

        assert!(kb.match_term(v1, v2).is_none());
    }

    // ── bind_compressed chain tests ────────────────────────────

    #[test]
    fn bind_compressed_transitive_chain() {
        // x → y → z → 99: sequential bind_compressed calls should
        // compress all vars to point directly to 99.
        let mut kb = KnowledgeBase::new();
        let x_sym = kb.intern("x");
        let y_sym = kb.intern("y");
        let z_sym = kb.intern("z");
        let vx = kb.fresh_var(x_sym);
        let vy = kb.fresh_var(y_sym);
        let vz = kb.fresh_var(z_sym);
        let var_y = kb.alloc(Term::Var(vy));
        let var_z = kb.alloc(Term::Var(vz));
        let val = kb.alloc(Term::Const(Literal::Int(99)));

        let mut s = Substitution::new();

        // x → y
        s.bind_compressed([(vx, var_y)], &kb.terms);
        assert_eq!(s.resolve(vx), Some(var_y));

        // y → z: should also compress x → z
        s.bind_compressed([(vy, var_z)], &kb.terms);
        assert_eq!(s.resolve(vy), Some(var_z));
        assert_eq!(s.resolve(vx), Some(var_z));

        // z → 99: should compress x → 99 and y → 99
        s.bind_compressed([(vz, val)], &kb.terms);
        assert_eq!(s.resolve(vz), Some(val));
        assert_eq!(s.resolve(vy), Some(val));
        assert_eq!(s.resolve(vx), Some(val));
    }

    // ── Reify tests ─────────────────────────────────────────────

    #[test]
    fn reify_deep_chase() {
        let mut kb = KnowledgeBase::new();
        let f_sym = kb.intern("f");
        let x_sym = kb.intern("x");
        let y_sym = kb.intern("y");
        let vx = kb.fresh_var(x_sym);
        let vy = kb.fresh_var(y_sym);
        let var_x = kb.alloc(Term::Var(vx));
        let var_y = kb.alloc(Term::Var(vy));
        let val = kb.alloc(Term::Const(Literal::Int(42)));

        // f(?x) where x -> y -> 42
        let term = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });

        let mut s = Substitution::new();
        s.bind(vx, var_y);
        s.bind(vy, val);

        let result = kb.reify(term, &s);
        match kb.get_term(result) {
            Term::Fn { pos_args, .. } => {
                assert_eq!(pos_args[0], val);
            }
            other => panic!("expected Fn, got {:?}", other),
        }
    }

    // ── is_equation tests ───────────────────────────────────────

    #[test]
    fn is_equation_true() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Eq");
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");

        let lhs = kb.alloc(Term::Const(Literal::Int(1)));
        let rhs = kb.alloc(Term::Const(Literal::Int(1)));
        let head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[lhs, rhs]),
            named_args: SmallVec::new(),
        });

        let rid = kb.assert_fact(head, sort, domain, None);
        assert!(kb.is_equation(rid));
    }

    #[test]
    fn is_equation_false_for_rule() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Eq");
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");
        let g_sym = kb.intern("g");

        let lhs = kb.alloc(Term::Const(Literal::Int(1)));
        let rhs = kb.alloc(Term::Const(Literal::Int(1)));
        let head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[lhs, rhs]),
            named_args: SmallVec::new(),
        });
        let body = kb.alloc(Term::Fn {
            functor: g_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });

        let rid = kb.assert_rule(head, vec![body], sort, domain, None);
        assert!(!kb.is_equation(rid));
    }

    // ── SLD Resolution tests ────────────────────────────────────

    #[test]
    fn resolve_ground_fact() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");
        let parent_sym = kb.intern("parent");

        let alice = kb.alloc(Term::Const(Literal::String("alice".into())));
        let bob = kb.alloc(Term::Const(Literal::String("bob".into())));

        let fact = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[alice, bob]),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(fact, sort, domain, None);

        // Query: parent(?x, "bob")
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(vx));
        let goal = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[var_x, bob]),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let results = kb.resolve(&[goal], &config);
        assert_eq!(results.len(), 1);
        // answer_subst is flat — resolve directly, no walk needed
        assert_eq!(results[0].subst.resolve(vx), Some(alice));
    }

    #[test]
    fn resolve_simple_rule() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Rule");
        let domain = kb.make_name_term("test");
        let parent_sym = kb.intern("parent");
        let grandparent_sym = kb.intern("grandparent");

        let alice = kb.alloc(Term::Const(Literal::String("alice".into())));
        let bob = kb.alloc(Term::Const(Literal::String("bob".into())));
        let charlie = kb.alloc(Term::Const(Literal::String("charlie".into())));

        // Facts: parent("alice", "bob"), parent("bob", "charlie")
        let f1 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[alice, bob]),
            named_args: SmallVec::new(),
        });
        let f2 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[bob, charlie]),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(f1, sort, domain, None);
        kb.assert_fact(f2, sort, domain, None);

        // Rule: grandparent(?x, ?z) :- parent(?x, ?y), parent(?y, ?z)
        let x_sym = kb.intern("x");
        let y_sym = kb.intern("y");
        let z_sym = kb.intern("z");
        let vx = kb.fresh_var(x_sym);
        let vy = kb.fresh_var(y_sym);
        let vz = kb.fresh_var(z_sym);
        let var_x = kb.alloc(Term::Var(vx));
        let var_y = kb.alloc(Term::Var(vy));
        let var_z = kb.alloc(Term::Var(vz));

        let head = kb.alloc(Term::Fn {
            functor: grandparent_sym,
            pos_args: SmallVec::from_slice(&[var_x, var_z]),
            named_args: SmallVec::new(),
        });
        let b1 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[var_x, var_y]),
            named_args: SmallVec::new(),
        });
        let b2 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[var_y, var_z]),
            named_args: SmallVec::new(),
        });
        kb.assert_rule(head, vec![b1, b2], sort, domain, None);

        // Query: grandparent(?a, ?b)
        let a_sym = kb.intern("a");
        let b_sym = kb.intern("b");
        let va = kb.fresh_var(a_sym);
        let vb = kb.fresh_var(b_sym);
        let var_a = kb.alloc(Term::Var(va));
        let var_b = kb.alloc(Term::Var(vb));
        let goal = kb.alloc(Term::Fn {
            functor: grandparent_sym,
            pos_args: SmallVec::from_slice(&[var_a, var_b]),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let results = kb.resolve(&[goal], &config);
        assert_eq!(results.len(), 1);
        // Use reify to resolve through fresh var chains
        assert_eq!(kb.reify(var_a, &results[0].subst), alice);
        assert_eq!(kb.reify(var_b, &results[0].subst), charlie);
    }

    #[test]
    fn resolve_recursive_rule() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Rule");
        let domain = kb.make_name_term("test");
        let parent_sym = kb.intern("parent");
        let ancestor_sym = kb.intern("ancestor");

        let alice = kb.alloc(Term::Const(Literal::String("alice".into())));
        let bob = kb.alloc(Term::Const(Literal::String("bob".into())));
        let charlie = kb.alloc(Term::Const(Literal::String("charlie".into())));

        // Facts
        let f1 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[alice, bob]),
            named_args: SmallVec::new(),
        });
        let f2 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[bob, charlie]),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(f1, sort, domain, None);
        kb.assert_fact(f2, sort, domain, None);

        // Rule 1: ancestor(?x, ?y) :- parent(?x, ?y)
        {
            let x_sym = kb.intern("x");
            let y_sym = kb.intern("y");
            let vx = kb.fresh_var(x_sym);
            let vy = kb.fresh_var(y_sym);
            let var_x = kb.alloc(Term::Var(vx));
            let var_y = kb.alloc(Term::Var(vy));

            let head = kb.alloc(Term::Fn {
                functor: ancestor_sym,
                pos_args: SmallVec::from_slice(&[var_x, var_y]),
                named_args: SmallVec::new(),
            });
            let body = kb.alloc(Term::Fn {
                functor: parent_sym,
                pos_args: SmallVec::from_slice(&[var_x, var_y]),
                named_args: SmallVec::new(),
            });
            kb.assert_rule(head, vec![body], sort, domain, None);
        }

        // Rule 2: ancestor(?x, ?z) :- parent(?x, ?y), ancestor(?y, ?z)
        {
            let x_sym = kb.intern("x");
            let y_sym = kb.intern("y");
            let z_sym = kb.intern("z");
            let vx = kb.fresh_var(x_sym);
            let vy = kb.fresh_var(y_sym);
            let vz = kb.fresh_var(z_sym);
            let var_x = kb.alloc(Term::Var(vx));
            let var_y = kb.alloc(Term::Var(vy));
            let var_z = kb.alloc(Term::Var(vz));

            let head = kb.alloc(Term::Fn {
                functor: ancestor_sym,
                pos_args: SmallVec::from_slice(&[var_x, var_z]),
                named_args: SmallVec::new(),
            });
            let b1 = kb.alloc(Term::Fn {
                functor: parent_sym,
                pos_args: SmallVec::from_slice(&[var_x, var_y]),
                named_args: SmallVec::new(),
            });
            let b2 = kb.alloc(Term::Fn {
                functor: ancestor_sym,
                pos_args: SmallVec::from_slice(&[var_y, var_z]),
                named_args: SmallVec::new(),
            });
            kb.assert_rule(head, vec![b1, b2], sort, domain, None);
        }

        // Query: ancestor("alice", ?w)
        let w_sym = kb.intern("w");
        let vw = kb.fresh_var(w_sym);
        let var_w = kb.alloc(Term::Var(vw));
        let goal = kb.alloc(Term::Fn {
            functor: ancestor_sym,
            pos_args: SmallVec::from_slice(&[alice, var_w]),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig { max_depth: 20, ..Default::default() };
        let results = kb.resolve(&[goal], &config);

        // Should find: ancestor(alice, bob) and ancestor(alice, charlie)
        let bound: Vec<TermId> = results.iter()
            .map(|sol| kb.reify(var_w, &sol.subst))
            .collect();
        assert_eq!(bound.len(), 2);
        assert!(bound.contains(&bob));
        assert!(bound.contains(&charlie));
    }

    #[test]
    fn resolve_multiple_solutions() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");
        let likes_sym = kb.intern("likes");

        let alice = kb.alloc(Term::Const(Literal::String("alice".into())));
        let cats = kb.alloc(Term::Const(Literal::String("cats".into())));
        let dogs = kb.alloc(Term::Const(Literal::String("dogs".into())));

        let f1 = kb.alloc(Term::Fn {
            functor: likes_sym,
            pos_args: SmallVec::from_slice(&[alice, cats]),
            named_args: SmallVec::new(),
        });
        let f2 = kb.alloc(Term::Fn {
            functor: likes_sym,
            pos_args: SmallVec::from_slice(&[alice, dogs]),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(f1, sort, domain, None);
        kb.assert_fact(f2, sort, domain, None);

        // Query: likes("alice", ?what)
        let w_sym = kb.intern("what");
        let vw = kb.fresh_var(w_sym);
        let var_w = kb.alloc(Term::Var(vw));
        let goal = kb.alloc(Term::Fn {
            functor: likes_sym,
            pos_args: SmallVec::from_slice(&[alice, var_w]),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let results = kb.resolve(&[goal], &config);
        assert_eq!(results.len(), 2);
    }

    #[test]
    fn resolve_max_solutions() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");
        let f_sym = kb.intern("f");

        for i in 0..5 {
            let val = kb.alloc(Term::Const(Literal::Int(i)));
            let fact = kb.alloc(Term::Fn {
                functor: f_sym,
                pos_args: SmallVec::from_elem(val, 1),
                named_args: SmallVec::new(),
            });
            kb.assert_fact(fact, sort, domain, None);
        }

        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(vx));
        let goal = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig { max_solutions: 2, ..Default::default() };
        let results = kb.resolve(&[goal], &config);
        assert_eq!(results.len(), 2);
    }

    #[test]
    fn resolve_depth_limit() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Rule");
        let domain = kb.make_name_term("test");
        let loop_sym = kb.intern("loop");

        // Infinite loop: loop(?x) :- loop(?x)
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(vx));
        let head = kb.alloc(Term::Fn {
            functor: loop_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let body = kb.alloc(Term::Fn {
            functor: loop_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_rule(head, vec![body], sort, domain, None);

        let val = kb.alloc(Term::Const(Literal::Int(1)));
        let goal = kb.alloc(Term::Fn {
            functor: loop_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig { max_depth: 5, ..Default::default() };
        let results = kb.resolve(&[goal], &config);
        assert!(results.is_empty());
    }

    #[test]
    fn resolve_no_solution() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");
        let f_sym = kb.intern("f");
        let g_sym = kb.intern("g");

        let val = kb.alloc(Term::Const(Literal::Int(1)));
        let fact = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(fact, sort, domain, None);

        // Query for g(1) — no matching facts
        let goal = kb.alloc(Term::Fn {
            functor: g_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let results = kb.resolve(&[goal], &config);
        assert!(results.is_empty());
    }

    // ── Equational rewriting tests ──────────────────────────────

    #[test]
    fn simplify_constant_equation() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Eq");
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");

        // Equation: eq(double(2), 4)
        let double_sym = kb.intern("double");
        let two = kb.alloc(Term::Const(Literal::Int(2)));
        let four = kb.alloc(Term::Const(Literal::Int(4)));
        let lhs = kb.alloc(Term::Fn {
            functor: double_sym,
            pos_args: SmallVec::from_elem(two, 1),
            named_args: SmallVec::new(),
        });
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[lhs, four]),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(eq_head, sort, domain, None);

        // Simplify double(2) → should get 4
        let result = kb.simplify(lhs);
        assert_eq!(result, four);
    }

    #[test]
    fn simplify_variable_equation() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Eq");
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");

        // Equation: eq(negate(negate(?x)), ?x)
        let negate_sym = kb.intern("negate");
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(vx));

        let inner_neg = kb.alloc(Term::Fn {
            functor: negate_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let double_neg = kb.alloc(Term::Fn {
            functor: negate_sym,
            pos_args: SmallVec::from_elem(inner_neg, 1),
            named_args: SmallVec::new(),
        });
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[double_neg, var_x]),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(eq_head, sort, domain, None);

        // Simplify negate(negate(5)) → should get 5
        let five = kb.alloc(Term::Const(Literal::Int(5)));
        let neg5 = kb.alloc(Term::Fn {
            functor: negate_sym,
            pos_args: SmallVec::from_elem(five, 1),
            named_args: SmallVec::new(),
        });
        let double_neg5 = kb.alloc(Term::Fn {
            functor: negate_sym,
            pos_args: SmallVec::from_elem(neg5, 1),
            named_args: SmallVec::new(),
        });
        let result = kb.simplify(double_neg5);
        assert_eq!(result, five);
    }

    #[test]
    fn simplify_nested_subterms() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Eq");
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");

        // Equation: eq(double(?x), twice(?x))
        let double_sym = kb.intern("double");
        let twice_sym = kb.intern("twice");
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(vx));

        let lhs = kb.alloc(Term::Fn {
            functor: double_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let rhs = kb.alloc(Term::Fn {
            functor: twice_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[lhs, rhs]),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(eq_head, sort, domain, None);

        // Simplify f(double(3)) → f(twice(3))
        let f_sym = kb.intern("f");
        let three = kb.alloc(Term::Const(Literal::Int(3)));
        let double_3 = kb.alloc(Term::Fn {
            functor: double_sym,
            pos_args: SmallVec::from_elem(three, 1),
            named_args: SmallVec::new(),
        });
        let term = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(double_3, 1),
            named_args: SmallVec::new(),
        });

        let result = kb.simplify(term);
        let expected_inner = kb.alloc(Term::Fn {
            functor: twice_sym,
            pos_args: SmallVec::from_elem(three, 1),
            named_args: SmallVec::new(),
        });
        let expected = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(expected_inner, 1),
            named_args: SmallVec::new(),
        });
        assert_eq!(result, expected);
    }

    #[test]
    fn simplify_no_match_passthrough() {
        let mut kb = KnowledgeBase::new();
        let f_sym = kb.intern("f");
        let val = kb.alloc(Term::Const(Literal::Int(42)));
        let term = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });

        // No equations in KB, term should pass through unchanged
        let result = kb.simplify(term);
        assert_eq!(result, term);
    }

    // ── Integration: resolve with equational fallback ────────────

    #[test]
    fn resolve_with_simplification() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Rule");
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");
        let f_sym = kb.intern("f");
        let g_sym = kb.intern("g");

        // Equation: eq(f(?x), g(?x)) — f rewrites to g
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(vx));
        let f_x = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let g_x = kb.alloc(Term::Fn {
            functor: g_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[f_x, g_x]),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(eq_head, sort, domain, None);

        // Fact: g(42)
        let val = kb.alloc(Term::Const(Literal::Int(42)));
        let g_42 = kb.alloc(Term::Fn {
            functor: g_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(g_42, sort, domain, None);

        // Query: f(42) — with simplification, f(42) → g(42), which matches the fact
        let f_42 = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig { simplify: true, ..Default::default() };
        let results = kb.resolve(&[f_42], &config);
        assert_eq!(results.len(), 1);
    }

    #[test]
    fn apply_eq_rules_returns_changes() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Eq");
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");

        // Equation: eq(double(2), 4)
        let double_sym = kb.intern("double");
        let two = kb.alloc(Term::Const(Literal::Int(2)));
        let four = kb.alloc(Term::Const(Literal::Int(4)));
        let lhs = kb.alloc(Term::Fn {
            functor: double_sym,
            pos_args: SmallVec::from_elem(two, 1),
            named_args: SmallVec::new(),
        });
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[lhs, four]),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(eq_head, sort, domain, None);

        let (result, changes) = kb.apply_eq_rules(lhs, 100);
        assert_eq!(result, four);
        assert_eq!(changes.len(), 1);
        assert_eq!(changes[0].original, lhs);
        assert_eq!(changes[0].rewritten, four);
    }
}

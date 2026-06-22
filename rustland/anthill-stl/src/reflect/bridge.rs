use std::cell::RefCell;
use std::rc::Rc;

use anthill_core::eval::Value;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::{Term as CoreTerm, TermId, Literal, Var, VarId};
use anthill_core::kb::term_view::{TermView, ViewHead};
use anthill_core::kb::resolve::{SearchStream, ResolveConfig};

use crate::prelude::{Stream, Modifiable, Type};
use crate::reflect::*;

// ── Boundary helpers (WI-540) ───────────────────────────────────
//
// The reflect API speaks `Term` (= `ReflectTerm`) and `Symbol` (=
// `ReflectSymbol`); the internal `Value` / `TermId` / `intern::Symbol` are
// converted here, only inside the impl. `Value` never appears in a signature.

/// Lift an internal `Value` into the reflect `Term`.
#[inline]
fn rterm(v: Value) -> Term {
    ReflectTerm::new(v)
}

/// Lift a KB-resident hash-consed `TermId` into the reflect `Term`.
#[inline]
fn term(id: TermId) -> Term {
    ReflectTerm::new(Value::Term(id))
}

/// Lift a contract-clause `TermId` into the reflect `NodeOccurrence` (WI-545).
/// The loader stores op `requires`/`ensures` clauses as goal terms, so the
/// carrier is a `Value::Term`.
#[inline]
fn nocc(id: TermId) -> NodeOccurrence {
    ReflectNodeOccurrence::new(Value::Term(id))
}

/// Map a core [`Literal`] to its host [`LiteralRepr`] (struct-variant form).
/// A `BigInt` maps to the first-class `BigIntLiteral` (WI-543) — carrier-
/// faithful, so it is no longer indistinguishable from a real string. A
/// `Handle` lowers to its id.
fn literal_to_repr(lit: Literal) -> LiteralRepr {
    match lit {
        Literal::String(s) => LiteralRepr::StringLiteral { value: s },
        Literal::Int(n) => LiteralRepr::IntLiteral { value: n },
        Literal::BigInt(n) => LiteralRepr::BigIntLiteral { value: n },
        Literal::Float(f) => LiteralRepr::FloatLiteral { value: f.into() },
        Literal::Bool(b) => LiteralRepr::BoolLiteral { value: b },
        Literal::Handle(_, id) => LiteralRepr::IntLiteral { value: id as i64 },
    }
}

// ── KbBridge ────────────────────────────────────────────────────

pub struct KbBridge {
    pub kb: Rc<RefCell<KnowledgeBase>>,
}

/// The generated `trait KB: Modifiable` — the host bridge is a `Modifiable`
/// resource (marker only; runtime dispatch lives in anthill-core).
impl Modifiable for KbBridge {}

impl KbBridge {
    pub fn new(kb: KnowledgeBase) -> Self {
        Self { kb: Rc::new(RefCell::new(kb)) }
    }

    /// Lift a name `TermId` (a `Ref`/`Ident`) into the reflect `Symbol`. A
    /// non-ref carrier is interned by its display name (names are references in
    /// practice, so this is a defensive fallback).
    fn sym_of(&self, tid: TermId) -> Symbol {
        let direct = {
            let kb = self.kb.borrow();
            match kb.get_term(tid) {
                CoreTerm::Ref(s) | CoreTerm::Ident(s) => Some(*s),
                _ => None,
            }
        };
        let sym = match direct {
            Some(s) => s,
            None => {
                let name = self.term_display_name(tid);
                self.kb.borrow_mut().intern(&name)
            }
        };
        ReflectSymbol::new(sym)
    }

    /// Reify any [`TermView`] carrier — a hash-consed `TermId` / `Value::Term`,
    /// a `Value::Node` occurrence, a `Value::Entity`, or a value-level `Var` —
    /// to a flat [`TermRepr`]. The single reifier behind both `KB::reify` and
    /// `KB::rules`; reads structure through `TermView`, so every carrier
    /// produces the same shape. Functor/ref names ride as `Symbol` (the spec
    /// types them so); a functor-less aggregate or opaque value in a term slot
    /// panics loudly.
    fn reify_view<V: TermView>(&self, view: &V) -> TermRepr {
        let kb = self.kb.borrow();
        // A var of any kind reifies to a `VarRepr` (string name). `index_var`
        // surfaces Global / Rigid / DeBruijn (the latter two read as `Opaque`).
        if let Some(var) = view.index_var(&kb) {
            let name = match var {
                Var::Global(vid) => kb.resolve_sym(vid.name()).to_string(),
                Var::Rigid(vid) => format!("!{}", kb.resolve_sym(vid.name())),
                Var::DeBruijn(n) => format!("_{n}"),
            };
            return TermRepr::VarRepr { name };
        }
        match view.head(&kb) {
            ViewHead::Var(vid) => TermRepr::VarRepr {
                name: kb.resolve_sym(vid.name()).to_string(),
            },
            ViewHead::Const(lit) => TermRepr::ConstRepr { value: literal_to_repr(lit) },
            ViewHead::Ref(sym) | ViewHead::Ident(sym) => {
                TermRepr::RefRepr { name: ReflectSymbol::new(sym) }
            }
            ViewHead::Bottom => {
                drop(kb);
                let bottom_sym = self.kb.borrow_mut().intern("⊥");
                TermRepr::RefRepr { name: ReflectSymbol::new(bottom_sym) }
            }
            ViewHead::Functor { functor: Some(functor), pos_arity, named_arity } => {
                // Materialize each child into an owned `Value` (releasing the
                // `kb` borrow a `ViewItem` holds), then recurse. Positional
                // first, then named in canonical (`named_keys`) order.
                let named_keys = view.named_keys(&kb);
                let mut child_values: Vec<Value> = Vec::with_capacity(pos_arity + named_arity);
                for i in 0..pos_arity {
                    let child = view.pos_arg(&kb, i).unwrap_or_else(|| {
                        panic!("reify_view: positional arg {i} missing below arity {pos_arity}")
                    });
                    child_values.push(child.to_value());
                }
                for key in named_keys {
                    if let Some(child) = view.named_arg(&kb, key) {
                        child_values.push(child.to_value());
                    }
                }
                let args = child_values.iter().map(|c| self.reify_view(c)).collect();
                TermRepr::FnRepr { name: ReflectSymbol::new(functor), args }
            }
            ViewHead::Functor { functor: None, .. } | ViewHead::Opaque => panic!(
                "KbBridge::reify_view: non-term carrier in a Term slot (functor-less \
                 aggregate or opaque value)",
            ),
        }
    }

    /// Resolve a name string to a sort-level TermId via make_name_term.
    fn resolve_sort_name(&self, name: &str) -> TermId {
        self.kb.borrow_mut().make_name_term(name)
    }

    /// Get all hash-consed fact head TermIds for a given KB sort name. A
    /// Node-carrying value-fact head (WI-348/342) is skipped — the
    /// carrier-faithful path for those is the interpreter `KB.*` builtins.
    fn facts_by_sort_name(&self, sort_name: &str) -> Vec<(anthill_core::kb::RuleId, TermId)> {
        let sort_term = self.resolve_sort_name(sort_name);
        let kb = self.kb.borrow();
        kb.by_sort(sort_term)
            .into_iter()
            .filter_map(|rid| match kb.rule_head_value(rid) {
                anthill_core::eval::Value::Term(t) => Some((rid, *t)),
                _ => None,
            })
            .collect()
    }

    /// The entity functor a reference `Value` names — the host twin of core's
    /// `eval::value_functor` (which is `pub(crate)` to anthill-core, so it can't
    /// be reused across the crate boundary). Matches core arm-for-arm: an
    /// `Entity` carries its functor directly; a `Term` carrier reads the
    /// hash-consed `Fn`/`Ref` head; anything else (a literal, a var, an
    /// unresolved `Ident`) names no entity. Keep in lock-step with core.
    fn value_functor(&self, v: &Value) -> Option<anthill_core::intern::Symbol> {
        match v {
            Value::Entity { functor, .. } => Some(*functor),
            Value::Term(tid) => match self.kb.borrow().get_term(*tid) {
                CoreTerm::Fn { functor, .. } => Some(*functor),
                CoreTerm::Ref(sym) => Some(*sym),
                _ => None,
            },
            _ => None,
        }
    }

    /// Extract the functor name from a Fn term.
    fn term_functor_name(&self, id: TermId) -> Option<String> {
        let kb = self.kb.borrow();
        match kb.get_term(id) {
            CoreTerm::Fn { functor, .. } => Some(kb.resolve_sym(*functor).to_string()),
            _ => None,
        }
    }

    /// Extract named args from a Fn term as (name_str, TermId) pairs.
    fn term_named_args(&self, id: TermId) -> Vec<(String, TermId)> {
        let kb = self.kb.borrow();
        match kb.get_term(id) {
            CoreTerm::Fn { named_args, .. } => {
                named_args.iter()
                    .map(|&(sym, tid)| (kb.resolve_sym(sym).to_string(), tid))
                    .collect()
            }
            _ => vec![],
        }
    }

    /// Extract positional args from a Fn term.
    fn term_pos_args(&self, id: TermId) -> Vec<TermId> {
        let kb = self.kb.borrow();
        match kb.get_term(id) {
            CoreTerm::Fn { pos_args, .. } => pos_args.iter().copied().collect(),
            _ => vec![],
        }
    }

    /// Get a displayable name for a TermId.
    fn term_display_name(&self, id: TermId) -> String {
        let kb = self.kb.borrow();
        match kb.get_term(id) {
            CoreTerm::Ref(sym) | CoreTerm::Ident(sym) => kb.resolve_sym(*sym).to_string(),
            CoreTerm::Fn { functor, .. } => kb.resolve_sym(*functor).to_string(),
            CoreTerm::Const(Literal::String(s)) => s.clone(),
            CoreTerm::Const(Literal::Int(n)) => n.to_string(),
            CoreTerm::Const(Literal::BigInt(n)) => n.to_string(),
            CoreTerm::Const(Literal::Float(f)) => f.to_string(),
            CoreTerm::Const(Literal::Bool(b)) => b.to_string(),
            CoreTerm::Const(Literal::Handle(kind, id)) => format!("<{:?}:{}>", kind, id),
            CoreTerm::Var(Var::Global(vid)) => format!("?{}", kb.resolve_sym(vid.name())),
            CoreTerm::Var(Var::DeBruijn(n)) => format!("?_{n}"),
            CoreTerm::Var(Var::Rigid(vid)) => format!("!{}", kb.resolve_sym(vid.name())),
            CoreTerm::Bottom => "⊥".into(),
            CoreTerm::ParseAux(_) => "<parse-aux>".into(),
        }
    }

    /// Get the short (last segment) of a qualified name.
    fn short_name(&self, qualified: &str) -> String {
        qualified.rsplit('.').next().unwrap_or(qualified).to_string()
    }

    /// Collect member names of a given kind under a parent domain.
    fn members_of_kind(&self, parent_name: &str, kind: &str) -> Vec<String> {
        let mut results = vec![];
        for (_rid, head) in self.facts_by_sort_name("Member") {
            let pos = self.term_pos_args(head);
            if pos.len() == 3 {
                let member_kind = self.term_display_name(pos[1]);
                let member_parent = self.term_display_name(pos[2]);
                if member_kind == kind
                    && (member_parent == parent_name
                        || self.short_name(&member_parent) == parent_name)
                {
                    results.push(self.term_display_name(pos[0]));
                }
            }
        }
        results
    }

    /// Walk a cons-list term and collect all head elements as TermIds.
    fn collect_list_terms(&self, list_tid: TermId) -> Vec<TermId> {
        let mut results = vec![];
        let mut current = list_tid;
        loop {
            let kb = self.kb.borrow();
            match kb.get_term(current) {
                CoreTerm::Fn { functor, named_args, .. } => {
                    let name = kb.resolve_sym(*functor);
                    if name == "nil" {
                        break;
                    }
                    if name == "cons" {
                        let head = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "head");
                        let tail = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "tail");
                        if let Some(&(_, h)) = head {
                            results.push(h);
                        }
                        match tail {
                            Some(&(_, t)) => { current = t; }
                            None => break,
                        }
                    } else {
                        break;
                    }
                }
                _ => break,
            }
        }
        results
    }

    /// Walk a cons-list and collect head elements (same as collect_list_terms).
    fn collect_list_refs(&self, list_tid: TermId) -> Vec<TermId> {
        self.collect_list_terms(list_tid)
    }

    /// Look up an Entity definition by name, returning its functor symbol and
    /// the list of field name symbols. Falls back to inferring schema from
    /// existing facts with matching functor if no Entity definition exists.
    fn find_entity_schema(&self, sort_name: &str) -> Option<(anthill_core::intern::Symbol, Vec<anthill_core::intern::Symbol>)> {
        let entity_facts = self.facts_by_sort_name("Entity");
        {
            let kb = self.kb.borrow();
            for (_rid, head) in &entity_facts {
                if let CoreTerm::Fn { functor, named_args, .. } = kb.get_term(*head) {
                    let fname = kb.resolve_sym(*functor);
                    if fname == sort_name || fname.rsplit('.').next() == Some(sort_name) {
                        let fields: Vec<anthill_core::intern::Symbol> = named_args
                            .iter()
                            .map(|&(sym, _)| sym)
                            .collect();
                        return Some((*functor, fields));
                    }
                }
            }
        }

        let mut kb = self.kb.borrow_mut();
        let plain_sym = kb.resolve_name_in_global(sort_name)
            .unwrap_or_else(|| kb.intern(sort_name));
        let rids = kb.rules_by_functor(plain_sym);
        for rid in rids {
            let head = match kb.rule_head_value(rid) {
                anthill_core::eval::Value::Term(t) => *t,
                _ => continue,
            };
            if let CoreTerm::Fn { functor, named_args, .. } = kb.get_term(head) {
                let fields: Vec<anthill_core::intern::Symbol> = named_args
                    .iter()
                    .map(|&(s, _)| s)
                    .collect();
                return Some((*functor, fields));
            }
        }

        None
    }

    /// Convert a `LogicalQuery` to goal [`Value`]s and a `ResolveConfig`.
    fn query_to_goals_and_config(
        &self,
        query: &LogicalQuery,
    ) -> Result<(Vec<Value>, ResolveConfig), Error> {
        let mut config = ResolveConfig::default();
        let goals = self.query_to_goals(query, &mut config)?;
        Ok((goals, config))
    }

    /// Recursively convert a `LogicalQuery` into goal [`Value`]s. A
    /// `PatternQuery`'s `Term` carries an internal `Value` (occurrence-faithful)
    /// reached directly by `resolve_lazy_goals`.
    fn query_to_goals(
        &self,
        query: &LogicalQuery,
        config: &mut ResolveConfig,
    ) -> Result<Vec<Value>, Error> {
        match query {
            LogicalQuery::EmptyQuery => Ok(vec![]),
            LogicalQuery::PatternQuery { term } => Ok(vec![term.value().clone()]),
            LogicalQuery::SortQuery { sort_name } => {
                let entity_info = self.find_entity_schema(sort_name);

                let mut kb = self.kb.borrow_mut();
                match entity_info {
                    Some((functor, field_syms)) => {
                        let named_args_vec: Vec<(anthill_core::intern::Symbol, TermId)> = field_syms
                            .iter()
                            .map(|&field_sym| {
                                let sym_name = format!("?_{}", kb.resolve_sym(field_sym));
                                let var_name = kb.intern(&sym_name);
                                let vid = kb.fresh_var(var_name);
                                let var_term = kb.alloc(CoreTerm::Var(Var::Global(vid)));
                                (field_sym, var_term)
                            })
                            .collect();
                        let goal = kb.alloc(CoreTerm::Fn {
                            functor,
                            pos_args: Default::default(),
                            named_args: named_args_vec.into(),
                        });
                        Ok(vec![Value::Term(goal)])
                    }
                    None => {
                        let sort_sym = kb.intern(sort_name);
                        let query_var_sym = kb.intern("?_query");
                        let vid = kb.fresh_var(query_var_sym);
                        let var_term = kb.alloc(CoreTerm::Var(Var::Global(vid)));
                        let goal = kb.alloc(CoreTerm::Fn {
                            functor: sort_sym,
                            pos_args: vec![var_term].into(),
                            named_args: Default::default(),
                        });
                        Ok(vec![Value::Term(goal)])
                    }
                }
            }
            LogicalQuery::Conjunction { left, right } => {
                let mut goals = self.query_to_goals(left, config)?;
                goals.extend(self.query_to_goals(right, config)?);
                Ok(goals)
            }
            LogicalQuery::Limited { query, count } => {
                config.max_solutions = *count as usize;
                self.query_to_goals(query, config)
            }
            _ => Err(Error(format!("unsupported query variant: {:?}", query))),
        }
    }
}

// ── SearchStreamAdapter ─────────────────────────────────────────

/// Adapts a resolver `SearchStream` (consuming `split_first` + `&mut KB`) to the
/// `Stream<Solution, Error>` trait. Each pull yields a reflect `Solution`:
/// `definite(subst)` (empty residual) or `undecided(subst, residual)` — mirroring
/// the interpreter's `make_solution_value`, so the host `execute` is verdict- and
/// residual-honest (WI-534, absorbed by WI-540). `subst`/`residual` carry the
/// internal `Value`s wrapped at the boundary.
struct SearchStreamAdapter {
    inner: RefCell<Option<SearchStream>>,
    kb: Rc<RefCell<KnowledgeBase>>,
}

impl SearchStreamAdapter {
    /// Wrap one resolver solution as a reflect `Solution`.
    fn make_solution(&self, sol: anthill_core::kb::resolve::Solution) -> Solution {
        let anthill_core::kb::resolve::Solution { subst, residual } = sol;
        let subst_bridge: Box<dyn Substitution> =
            Box::new(SubstBridge::from_core(subst, Rc::clone(&self.kb)));
        if residual.is_empty() {
            Solution::Definite { subst: subst_bridge }
        } else {
            let residual = residual.into_iter().map(rterm).collect();
            Solution::Undecided { subst: subst_bridge, residual }
        }
    }
}

impl Stream<Solution, Error> for SearchStreamAdapter {
    fn split_first(&self) -> Result<Option<(Solution, Box<dyn Stream<Solution, Error>>)>, Error> {
        let stream = self.inner.borrow_mut().take()
            .ok_or_else(|| Error("stream already consumed".into()))?;
        let result = {
            let mut kb = self.kb.borrow_mut();
            stream.split_first(&mut kb)
        };
        match result {
            Some((sol, rest)) => {
                let elem = self.make_solution(sol);
                let cont: Box<dyn Stream<Solution, Error>> = Box::new(SearchStreamAdapter {
                    inner: RefCell::new(Some(rest)),
                    kb: Rc::clone(&self.kb),
                });
                Ok(Some((elem, cont)))
            }
            None => Ok(None),
        }
    }

    fn head(&self) -> Result<Option<Solution>, Error> {
        match self.split_first()? {
            Some((h, _)) => Ok(Some(h)),
            None => Ok(None),
        }
    }

    fn tail(&self) -> Result<Box<dyn Stream<Solution, Error>>, Error> {
        match self.split_first()? {
            Some((_, t)) => Ok(t),
            None => Ok(Box::new(SearchStreamAdapter {
                inner: RefCell::new(None),
                kb: Rc::clone(&self.kb),
            })),
        }
    }

    fn take_n(&self, n: i64) -> Result<Vec<Solution>, Error> {
        let mut results = Vec::new();
        let mut current = self.inner.borrow_mut().take();
        for _ in 0..n {
            let next = match current.take() {
                Some(s) => {
                    let mut kb = self.kb.borrow_mut();
                    s.split_first(&mut kb)
                }
                None => break,
            };
            match next {
                Some((sol, rest)) => {
                    results.push(self.make_solution(sol));
                    current = Some(rest);
                }
                None => break,
            }
        }
        *self.inner.borrow_mut() = current;
        Ok(results)
    }

    fn collect_all(&self) -> Result<Vec<Solution>, Error> {
        let mut results = Vec::new();
        let mut current = self.inner.borrow_mut().take();
        loop {
            let next = match current.take() {
                Some(s) => {
                    let mut kb = self.kb.borrow_mut();
                    s.split_first(&mut kb)
                }
                None => break,
            };
            match next {
                Some((sol, rest)) => {
                    results.push(self.make_solution(sol));
                    current = Some(rest);
                }
                None => break,
            }
        }
        Ok(results)
    }

    fn is_empty(&self) -> Result<bool, Error> {
        let inner = self.inner.borrow();
        match inner.as_ref() {
            Some(s) => Ok(s.is_empty()),
            None => Ok(true),
        }
    }
}

impl KB for KbBridge {
    /// DECISION (WI-546): `kb()` is the spec's *ambient*-KB accessor — a
    /// zero-arg op the runtime answers with the one interpreter-instance KB.
    /// The host has no ambient instance: a `KbBridge` is built explicitly from a
    /// `KnowledgeBase` (`KbBridge::new`), so there is nothing for a static
    /// `kb()` to return. It stays an explicit panic rather than fabricating an
    /// empty KB (which would silently answer queries against the wrong store).
    fn kb() -> Box<dyn KB> {
        panic!("KB.kb(): no ambient host KB — construct a KbBridge from a KnowledgeBase instead")
    }

    fn reify(&self, t: Term) -> TermRepr {
        self.reify_view(t.value())
    }

    fn reflect(&self, r: TermRepr) -> Term {
        match r {
            TermRepr::ConstRepr { value } => {
                let lit = match value {
                    LiteralRepr::IntLiteral { value } => Literal::Int(value),
                    LiteralRepr::BigIntLiteral { value } => Literal::BigInt(value),
                    LiteralRepr::FloatLiteral { value } => Literal::Float(value.into()),
                    LiteralRepr::StringLiteral { value } => Literal::String(value),
                    LiteralRepr::BoolLiteral { value } => Literal::Bool(value),
                };
                term(self.kb.borrow_mut().alloc(CoreTerm::Const(lit)))
            }
            TermRepr::VarRepr { name } => {
                let mut kb = self.kb.borrow_mut();
                let sym = kb.intern(&name);
                let vid = kb.fresh_var(sym);
                term(kb.alloc(CoreTerm::Var(Var::Global(vid))))
            }
            TermRepr::FnRepr { name, args } => {
                let functor = name.symbol();
                // `reflect` rebuilds a flat hash-consed term, so each child is a
                // `Value::Term`; a stray non-term child fails loud via `expect_term`.
                let child_ids: Vec<TermId> = args.into_iter()
                    .map(|a| self.reflect(a).into_value().expect_term())
                    .collect();
                term(self.kb.borrow_mut().alloc(CoreTerm::Fn {
                    functor,
                    pos_args: child_ids.into(),
                    named_args: Default::default(),
                }))
            }
            TermRepr::RefRepr { name } => {
                term(self.kb.borrow_mut().alloc(CoreTerm::Ref(name.symbol())))
            }
            TermRepr::QuotedRepr { source, .. } => {
                term(self.kb.borrow_mut().alloc(CoreTerm::Const(Literal::String(source))))
            }
        }
    }

    fn nonvar(&self, x: Term) -> bool {
        match x.value() {
            Value::Var(_) => false,
            Value::Term(t) => !matches!(self.kb.borrow().get_term(*t), CoreTerm::Var(_)),
            _ => true,
        }
    }

    fn ground(&self, x: Term) -> bool {
        // Mirrors the core resolver's `value_is_ground`.
        match x.value() {
            Value::Var(_) => false,
            Value::Term(t) => self.kb.borrow().collect_vars(*t).is_empty(),
            Value::Node(occ) =>
                !anthill_core::kb::node_occurrence::occurrence_has_unbound_var(occ),
            _ => true,
        }
    }

    fn sorts(&self, namespace: Option<String>) -> Vec<SortInfo> {
        let mut results = vec![];

        for (_rid, head) in self.facts_by_sort_name("Sort") {
            let functor = self.term_functor_name(head);
            if functor.as_deref() != Some("SortInfo") {
                continue;
            }
            let named = self.term_named_args(head);
            let field = |key: &str| named.iter().find(|(n, _)| n == key).map(|(_, tid)| *tid);

            let name_tid = match field("name") {
                Some(tid) => tid,
                None => continue,
            };
            let definition_tid = match field("definition") {
                Some(tid) => tid,
                None => continue,
            };

            if let Some(ref ns) = namespace {
                let name_str = self.term_display_name(name_tid);
                if !name_str.starts_with(ns) {
                    continue;
                }
            }

            let kind = match field("kind") {
                Some(tid) => self.sym_of(tid),
                None => ReflectSymbol::new(self.kb.borrow_mut().intern("sort")),
            };
            let ctors = field("constructors").map(|t| self.collect_list_refs(t)).unwrap_or_default();
            let ops = field("operations").map(|t| self.collect_list_refs(t)).unwrap_or_default();
            let params = field("parameters").map(|t| self.collect_list_refs(t)).unwrap_or_default();
            let reqs = field("requires").map(|t| self.collect_list_terms(t)).unwrap_or_default();

            results.push(SortInfo {
                name: self.sym_of(name_tid),
                kind,
                definition: term(definition_tid),
                constructors: ctors.into_iter().map(|t| self.sym_of(t)).collect(),
                operations: ops.into_iter().map(|t| self.sym_of(t)).collect(),
                parameters: params.into_iter().map(|t| self.sym_of(t)).collect(),
                requires: reqs.into_iter().map(term).collect(),
            });
        }

        results
    }

    fn operations(&self, sort_name: String) -> Vec<OperationInfo> {
        let mut results = vec![];

        for (rid, head) in self.facts_by_sort_name("Operation") {
            let functor = self.term_functor_name(head);
            if functor.as_deref() != Some("OperationInfo") {
                continue;
            }

            let domain = {
                let kb = self.kb.borrow();
                kb.fact_domain(rid)
            };
            let domain_name = self.term_display_name(domain);
            if domain_name != sort_name && self.short_name(&domain_name) != sort_name {
                continue;
            }

            let named = self.term_named_args(head);
            let field = |key: &str| named.iter().find(|(n, _)| n == key).map(|(_, tid)| *tid);

            let name_tid = match field("name") {
                Some(tid) => tid,
                None => continue,
            };
            let return_type_tid = match field("return_type") {
                Some(tid) => tid,
                None => continue,
            };

            let params = field("params")
                .map(|t| {
                    self.collect_list_terms(t)
                        .into_iter()
                        .map(|fi_tid| {
                            let fi_named = self.term_named_args(fi_tid);
                            let fi_field = |key: &str| fi_named.iter().find(|(n, _)| n == key).map(|(_, tid)| *tid);
                            let name = match fi_field("name") {
                                Some(t) => self.sym_of(t),
                                None => ReflectSymbol::new(self.kb.borrow_mut().intern("_")),
                            };
                            let type_name = fi_field("type_name").unwrap_or(fi_tid);
                            FieldInfo { name, type_name: term(type_name) }
                        })
                        .collect()
                })
                .unwrap_or_default();

            let effects = field("effects")
                .map(|t| self.collect_list_terms(t).into_iter().map(term).collect())
                .unwrap_or_default();

            // `requires`/`ensures` are lists of contract-clause goal terms in
            // the fact (same list encoding as `effects`); wrap each as a
            // `NodeOccurrence` carrier (WI-545). `requires` includes the loader's
            // auto-inferred `EffectsRuntime[Effects=E]` clause (WI-320); `ensures`
            // is user clauses only. A Node-carrying value fact (denoted effect)
            // is still skipped upstream by `facts_by_sort_name`.
            let requires = field("requires")
                .map(|t| self.collect_list_terms(t).into_iter().map(nocc).collect())
                .unwrap_or_default();
            let ensures = field("ensures")
                .map(|t| self.collect_list_terms(t).into_iter().map(nocc).collect())
                .unwrap_or_default();

            // `meta` is a `Term`; default to a bare `meta` ref when the fact
            // lacks it.
            let meta_tid = match field("meta") {
                Some(t) => t,
                None => {
                    let mut kb = self.kb.borrow_mut();
                    let s = kb.intern("meta");
                    kb.alloc(CoreTerm::Ref(s))
                }
            };

            results.push(OperationInfo {
                name: self.sym_of(name_tid),
                params,
                return_type: term(return_type_tid),
                effects,
                requires,
                ensures,
                meta: term(meta_tid),
            });
        }

        results
    }

    fn constructors(&self, sort_name: String) -> Vec<String> {
        self.members_of_kind(&sort_name, "Constructor")
            .into_iter()
            .map(|n| self.short_name(&n))
            .collect()
    }

    fn fields(&self, name: String) -> Vec<FieldInfo> {
        let mut results = vec![];

        for (_rid, head) in self.facts_by_sort_name("Entity") {
            let functor = match self.term_functor_name(head) {
                Some(n) => n,
                None => continue,
            };
            if functor != name && self.short_name(&functor) != name {
                continue;
            }
            let named = self.term_named_args(head);
            for (field_name, field_tid) in named {
                let name_sym = ReflectSymbol::new(self.kb.borrow_mut().intern(&field_name));
                results.push(FieldInfo {
                    name: name_sym,
                    type_name: term(field_tid),
                });
            }
            break;
        }

        results
    }

    fn rules(&self, sort_name: String) -> Vec<TermRepr> {
        let mut results = vec![];

        for (rid, head) in self.facts_by_sort_name("Rule") {
            let domain = {
                let kb = self.kb.borrow();
                kb.fact_domain(rid)
            };
            let domain_name = self.term_display_name(domain);
            if domain_name != sort_name && self.short_name(&domain_name) != sort_name {
                continue;
            }
            results.push(self.reify_view(&head));
        }

        results
    }

    fn descriptions(&self, target: Option<String>) -> Vec<DescriptionInfo> {
        let mut results = vec![];

        for (_rid, head) in self.facts_by_sort_name("Description") {
            let pos = self.term_pos_args(head);
            if pos.len() < 3 {
                continue;
            }
            let desc_target_tid = pos[0];
            let desc_content = self.term_display_name(pos[1]);
            let desc_index = match self.kb.borrow().get_term(pos[2]) {
                CoreTerm::Const(Literal::Int(n)) => *n,
                _ => continue,
            };

            if let Some(ref t) = target {
                let desc_target_name = self.term_display_name(desc_target_tid);
                if &desc_target_name != t && &self.short_name(&desc_target_name) != t {
                    continue;
                }
            }

            results.push(DescriptionInfo {
                target: self.sym_of(desc_target_tid),
                content: desc_content,
                index: desc_index,
            });
        }

        results
    }

    fn execute(
        &self,
        query: LogicalQuery,
    ) -> Result<Box<dyn Stream<Solution, Error>>, Error> {
        let (goals, config) = self.query_to_goals_and_config(&query)?;
        let stream = self.kb.borrow().resolve_lazy_goals(goals, &config);
        Ok(Box::new(SearchStreamAdapter {
            inner: RefCell::new(Some(stream)),
            kb: Rc::clone(&self.kb),
        }))
    }

    fn facts_of(&self, sort: Type) -> Vec<Term> {
        // The entity is passed by reference (`facts_of(kb(), WorkItem)`); the
        // `Type` carrier wraps that referencing `Value`. Extract its functor
        // (mirroring core `eval::value_functor`), then enumerate every asserted
        // fact with that head functor. Carrier-agnostic: `rule_head_value`
        // returns the head `Value` directly, so a value-fact head (e.g. an
        // `OperationInfo` carrying a `denoted` effect, WI-348) rides through as
        // a `Term` rather than being dropped — same as the interpreter
        // `kb_facts_of`.
        // A non-entity `sort` (a literal, a var, a Fn-with-args) names no fact
        // set — a caller type error, not "zero facts". Surface it loudly
        // (mirroring the interpreter `kb_facts_of`, which raises a type
        // mismatch, and the bridge's own `reify_view` panic discipline) rather
        // than returning an empty list a caller would misread as "none
        // asserted". The trait fixes the return as `Vec<Term>`, so a panic is
        // the only loud channel.
        let functor = self.value_functor(sort.value()).unwrap_or_else(|| {
            panic!(
                "KB.facts_of: `sort` is not an entity reference (expected a \
                 Ref / Fn / Entity carrier that names a functor)"
            )
        });
        let kb = self.kb.borrow();
        kb.rules_by_functor(functor)
            .into_iter()
            .map(|rid| rterm(kb.rule_head_value(rid).clone()))
            .collect()
    }

    fn sort_template(&self, sort_name: String) -> LogicalQuery {
        LogicalQuery::SortQuery { sort_name }
    }

    fn instantiation_query(
        &self,
        sort_name: String,
        _bindings: &dyn Substitution,
    ) -> LogicalQuery {
        LogicalQuery::SortQuery { sort_name }
    }

    /// Assert a fact with integrity checking (WI-546). The fact head must be a
    /// hash-consed term (a denoted value-fact head is loud via `expect_term`).
    /// The fact's sort — the key `assert_checked` triggers guards on and indexes
    /// by — is the head functor's trigger sort (`fact_trigger_sort`, the exact
    /// computation the loader uses for a constraint, so a registered guard
    /// fires); the explicit `sort` reference is the fallback when the head names
    /// no sort. Runtime-asserted facts take that sort as their own domain.
    /// Returns the new fact's id, or `None` when a registered constraint rejects
    /// the fact (which is then retracted) — the spec's "violated constraint → none".
    fn assert(&mut self, term: Term, sort: Type) -> Option<FactId> {
        let head = term.into_value();
        let term_tid = head.clone().expect_term();
        let arg_sort_sym = self.value_functor(sort.value());
        let mut kb = self.kb.borrow_mut();
        let sort_tid = kb.fact_trigger_sort(&head).unwrap_or_else(|| {
            let sym = arg_sort_sym.unwrap_or_else(|| {
                panic!("KB.assert: cannot determine the fact's sort from its head or the `sort` arg")
            });
            kb.make_name_term_from_sym(sym)
        });
        kb.assert_checked(term_tid, sort_tid, sort_tid, None)
    }

    fn add_guard(&mut self, _guard: LogicalQuery) -> ConstraintId {
        // WI-549: needs a reflect-`LogicalQuery`-enum → structured KB query
        // Value reifier (negation/conjunction/pattern_query nodes that
        // `collect_trigger_sorts`/`evaluate_guard` walk) — distinct from
        // `query_to_goals`, which flattens to resolver goals. Filed separately.
        panic!("KB.add_guard not yet implemented (WI-549)")
    }
}

// ── SubstBridge: impl Substitution ──────────────────────────────
//
// `SubstBridge` carries its own `KnowledgeBase` handle so `apply` / `compose` /
// `lookup` need only the wrapped core substitution (the trait's `&dyn KB`
// param is the spec shape but unused here — the host carries its KB).

impl SubstBridge {
    /// The `VarId` a variable-`Term` carries — as produced by `bindings`
    /// (`Value::Term(Var)`) or a raw `Value::Var`. `None` for a non-var carrier.
    fn vid_of(&self, v: &Value) -> Option<VarId> {
        match v {
            Value::Var(var) => var.as_global(),
            Value::Term(tid) => match self.kb.borrow().get_term(*tid) {
                CoreTerm::Var(var) => var.as_global(),
                _ => None,
            },
            _ => None,
        }
    }
}

impl Substitution for SubstBridge {
    fn apply(&self, t: Term, _kb: &dyn KB) -> Term {
        // Carrier-faithful: a `Value::Node` binding substitutes through
        // `reify_value`'s `substitute_occurrence`, preserving identity/span.
        rterm(self.kb.borrow_mut().reify_value(t.value(), &self.inner))
    }

    /// Full composition `σ2 ∘ σ1` (WI-544): (1) apply `s2` to each of self's
    /// binding values (self's range), then (2) extend with `s2`'s standalone
    /// bindings for variables self does not already bind. Step 2 needs to
    /// ENUMERATE `s2` by variable IDENTITY — now possible through the trait via
    /// `bindings()`, which carries each variable as a var `Term` (the VarIds are
    /// otherwise opaque across the `&dyn Substitution` boundary). Mirrors the
    /// interpreter `subst_compose` (which has concrete bindings).
    ///
    /// Step 1 re-applies `s2` via `apply`/`reify_value`, which (WI-547) now
    /// chases a bound *bare* `Value::Var` self-binding too — so a
    /// `z ↦ Value::Var(w)` with `s2 = {w ↦ v}` resolves to `z ↦ v`, not a
    /// dangling `z ↦ w`. Term-/Node-carried vars were always chased.
    fn compose(&self, s2: &dyn Substitution, kb: &dyn KB) -> Box<dyn Substitution> {
        let mut result = self.inner.clone();
        for (_var, val) in result.bindings.iter_mut() {
            *val = s2.apply(rterm(val.clone()), kb).into_value();
        }
        for (var_term, val_term) in s2.bindings() {
            match self.vid_of(var_term.value()) {
                // Only insert when self lacks the variable — self's (already
                // s2-applied) binding wins on overlap.
                Some(vid) => {
                    result.bindings.entry(vid).or_insert_with(|| val_term.into_value());
                }
                None => panic!(
                    "SubstBridge::compose: a `bindings()` entry's variable is not a \
                     var Term — the Substitution contract is violated"
                ),
            }
        }
        Box::new(SubstBridge { inner: result, kb: Rc::clone(&self.kb) })
    }

    /// Spec semantics: returns the bound value for ANY variable whose SHORT
    /// (last-segment) name matches — fresh logical vars have no anthill-side
    /// name, so `KB.execute` consumers look up a field by its short name. On a
    /// short-name COLLISION (two distinct vars sharing a tail) the result is the
    /// first match in substitution-map order, i.e. unspecified-which — the same
    /// "any matching variable" looseness the interpreter `lookup` builtin has.
    fn lookup(&self, name: String) -> Option<Term> {
        let kb = self.kb.borrow();
        for (var, val) in self.inner.iter() {
            let var_name = kb.resolve_sym(var.name());
            let short = var_name.rsplit('.').next().unwrap_or(var_name);
            if short == name {
                return Some(rterm(val.clone()));
            }
        }
        None
    }

    /// Enumerate the substitution as (variable, value) pairs. The variable
    /// rides as a `Value::Term(Var)` so its identity is recoverable (via
    /// `vid_of`); this is what lets `compose` merge by variable across the
    /// `&dyn Substitution` boundary.
    fn bindings(&self) -> Vec<(Term, Term)> {
        let entries: Vec<(VarId, Value)> =
            self.inner.iter().map(|(vid, val)| (*vid, val.clone())).collect();
        let mut kb = self.kb.borrow_mut();
        entries
            .into_iter()
            .map(|(vid, val)| {
                let var_tid = kb.alloc(CoreTerm::Var(Var::Global(vid)));
                (term(var_tid), rterm(val))
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use anthill_core::kb::KnowledgeBase;
    use anthill_core::kb::load::{self, NullResolver};
    use anthill_core::parse;

    /// Parse and load a single source snippet into a KbBridge.
    fn load_source_bridge(source: &str) -> KbBridge {
        let parsed = parse::parse(source).expect("parse failed");
        let mut kb = KnowledgeBase::new();
        load::register_prelude(&mut kb);
        kb.register_standard_builtins();
        load::load(&mut kb, &parsed, &NullResolver).expect("load failed");
        KbBridge::new(kb)
    }

    /// Load the full stdlib plus `source` into a KbBridge. Needed when the test
    /// exercises a path that depends on the reflect stdlib being present — e.g.
    /// a quantified `constraint`, whose loader lowering + guard trigger-sort
    /// extraction resolve `anthill.reflect.LogicalQuery.*` symbols.
    fn load_source_bridge_with_stdlib(source: &str) -> KbBridge {
        fn collect(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
            for e in std::fs::read_dir(dir).expect("read stdlib dir").flatten() {
                let p = e.path();
                if p.is_dir() { collect(&p, out); }
                else if p.extension().and_then(|s| s.to_str()) == Some("anthill") { out.push(p); }
            }
        }
        let stdlib_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../stdlib/anthill");
        let mut files = Vec::new();
        collect(&stdlib_dir, &mut files);
        assert!(!files.is_empty(), "stdlib empty");
        let mut parsed: Vec<_> = files.iter().map(|f| {
            let src = std::fs::read_to_string(f).expect("read stdlib");
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", f.display()))
        }).collect();
        parsed.push(parse::parse(source).expect("parse user source"));
        let refs: Vec<_> = parsed.iter().collect();
        let mut kb = KnowledgeBase::new();
        load::register_prelude(&mut kb);
        kb.register_standard_builtins();
        load::load_all(&mut kb, &refs, &NullResolver)
            .unwrap_or_else(|errs| { for e in &errs { eprintln!("{e}"); } panic!("load failed"); });
        KbBridge::new(kb)
    }

    #[test]
    fn execute_sort_query_finds_operations() {
        let bridge = load_source_bridge(r#"
sort Store {
  entity store
  operation persist(s: Store, fact: Int64) -> Int64
  operation retract(s: Store, id: Int64) -> Int64
  operation flush(s: Store) -> Int64
}
"#);
        let query = LogicalQuery::SortQuery { sort_name: "OperationInfo".into() };
        let stream = bridge.execute(query).expect("execute failed");
        let results = stream.collect_all().expect("collect failed");
        assert!(results.len() >= 3,
            "should find at least 3 OperationInfo facts, got {}", results.len());
        // Each result is a definite Solution.
        assert!(results.iter().all(|s| matches!(s, Solution::Definite { .. })),
            "sort-query solutions should be definite");
    }

    #[test]
    fn execute_sort_query_nonexistent_is_empty() {
        let bridge = load_source_bridge("sort Foo { entity bar }");
        let query = LogicalQuery::SortQuery { sort_name: "Nonexistent".into() };
        let stream = bridge.execute(query).expect("execute failed");
        let results = stream.collect_all().expect("collect failed");
        assert_eq!(results.len(), 0, "nonexistent sort query should return 0 results");
    }

    #[test]
    fn execute_empty_query() {
        let bridge = load_source_bridge("sort Foo { entity bar }");
        let query = LogicalQuery::EmptyQuery;
        let stream = bridge.execute(query).expect("execute failed");
        let results = stream.collect_all().expect("collect failed");
        assert_eq!(results.len(), 1, "empty query should return 1 result (trivial solution)");
        assert!(matches!(results[0], Solution::Definite { .. }));
    }

    #[test]
    fn execute_pattern_query() {
        let bridge = load_source_bridge(r#"
sort Animal { entity dog entity cat }
fact dog
fact cat
"#);
        let goal = {
            let mut kb = bridge.kb.borrow_mut();
            kb.resolve_qualified_name_term("Animal.dog")
        };
        let query = LogicalQuery::PatternQuery { term: ReflectTerm::new(Value::Term(goal)) };
        let stream = bridge.execute(query).expect("execute failed");
        let results = stream.collect_all().expect("collect failed");
        assert!(results.len() >= 1, "pattern query for 'dog' should find at least 1 result, got {}", results.len());
    }

    #[test]
    fn execute_limited_query() {
        let bridge = load_source_bridge(r#"
sort Store {
  entity store
  operation persist(s: Store, fact: Int64) -> Int64
  operation retract(s: Store, id: Int64) -> Int64
  operation flush(s: Store) -> Int64
}
"#);
        let query = LogicalQuery::Limited {
            query: Box::new(LogicalQuery::SortQuery { sort_name: "OperationInfo".into() }),
            count: 2,
        };
        let stream = bridge.execute(query).expect("execute failed");
        let results = stream.take_n(2).expect("take_n failed");
        assert!(results.len() <= 2,
            "limited query should return at most 2 results, got {}", results.len());
        assert!(!results.is_empty(), "should return at least 1 result");
    }

    #[test]
    fn reify_var_carriers_yield_varrepr() {
        // Every var kind reifies to a `VarRepr` (Rigid/DeBruijn read as Opaque
        // heads, recovered via `index_var`) rather than panicking.
        let bridge = load_source_bridge("sort Foo { entity bar }");
        let (global, rigid, debruijn) = {
            let mut kb = bridge.kb.borrow_mut();
            let s = kb.intern("x");
            let vid = kb.fresh_var(s);
            (
                ReflectTerm::new(Value::Term(kb.alloc(CoreTerm::Var(Var::Global(vid))))),
                ReflectTerm::new(Value::Term(kb.alloc(CoreTerm::Var(Var::Rigid(vid))))),
                ReflectTerm::new(Value::Term(kb.alloc(CoreTerm::Var(Var::DeBruijn(0))))),
            )
        };
        for (label, v) in [("global", global), ("rigid", rigid), ("debruijn", debruijn)] {
            assert!(
                matches!(bridge.reify(v), TermRepr::VarRepr { .. }),
                "{label} var carrier should reify to VarRepr",
            );
        }
        let var_value = {
            let mut kb = bridge.kb.borrow_mut();
            let s = kb.intern("y");
            let vid = kb.fresh_var(s);
            ReflectTerm::new(Value::Var(Var::Global(vid)))
        };
        assert!(!bridge.nonvar(var_value.clone()), "Value::Var is a variable");
        assert!(!bridge.ground(var_value), "Value::Var is not ground");
    }

    #[test]
    fn facts_of_enumerates_by_entity_reference() {
        // `facts_of` takes the entity by reference (a `Type` carrying a
        // `Ref(Color.red)` Value) and returns every rule head with that functor.
        // Parity with the interpreter `kb_facts_of` (`rules_by_functor`): the
        // result is the user facts PLUS the synthetic entity declaration (whose
        // field values are unbound logical vars) — so the count is
        // user-facts + 1.
        let bridge = load_source_bridge(r#"
sort Color {
  entity red(shade: Int64)
  entity blue(shade: Int64)
}
fact red(shade: 1)
fact red(shade: 2)
fact blue(shade: 3)
"#);
        // Count heads carrying a GROUND `shade` literal — that distinguishes the
        // two user facts from the synthetic entity decl (whose shade is a var).
        let ground_count = |facts: &[Term]| -> usize {
            facts.iter().filter(|t| match bridge.reify((*t).clone()) {
                TermRepr::FnRepr { args, .. } =>
                    args.iter().any(|a| matches!(a, TermRepr::ConstRepr { .. })),
                _ => false,
            }).count()
        };

        let red_ref = {
            let mut kb = bridge.kb.borrow_mut();
            Value::Term(kb.resolve_qualified_name_term("Color.red"))
        };
        let reds = bridge.facts_of(Type::new(red_ref));
        assert_eq!(reds.len(), 3, "2 user facts + 1 synthetic entity decl, got {}", reds.len());
        assert_eq!(ground_count(&reds), 2, "two ground `red` user facts");

        let blue_ref = {
            let mut kb = bridge.kb.borrow_mut();
            Value::Term(kb.resolve_qualified_name_term("Color.blue"))
        };
        let blues = bridge.facts_of(Type::new(blue_ref));
        assert_eq!(blues.len(), 2, "1 user fact + 1 synthetic entity decl");
        assert_eq!(ground_count(&blues), 1, "one ground `blue` user fact");
    }

    #[test]
    #[should_panic(expected = "not an entity reference")]
    fn facts_of_non_entity_reference_panics() {
        // A `Type` carrying a non-entity Value (a literal) names no functor —
        // a caller type error, surfaced loudly rather than as an empty list.
        let bridge = load_source_bridge("sort Foo { entity bar }");
        let lit = {
            let mut kb = bridge.kb.borrow_mut();
            Value::Term(kb.alloc(CoreTerm::Const(Literal::Int(7))))
        };
        let _ = bridge.facts_of(Type::new(lit));
    }

    #[test]
    fn bigint_literal_round_trips_as_bigint() {
        // A BigInt larger than i64 reifies to `BigIntLiteral` (not a lossy
        // `StringLiteral`) and reflects back to a `Const(BigInt)` (WI-543).
        let bridge = load_source_bridge("sort Foo { entity bar }");
        let big: num_bigint::BigInt =
            "123456789012345678901234567890".parse().expect("parse bigint");
        let term = {
            let mut kb = bridge.kb.borrow_mut();
            ReflectTerm::new(Value::Term(kb.alloc(CoreTerm::Const(Literal::BigInt(big.clone())))))
        };
        match bridge.reify(term) {
            TermRepr::ConstRepr { value: LiteralRepr::BigIntLiteral { value } } => {
                assert_eq!(value, big, "BigInt should survive reify intact");
            }
            other => panic!("expected ConstRepr(BigIntLiteral), got {other:?}"),
        }
        // Reflect the repr back to a term and confirm the core literal.
        let reflected = bridge.reflect(TermRepr::ConstRepr {
            value: LiteralRepr::BigIntLiteral { value: big.clone() },
        });
        let tid = reflected.into_value().expect_term();
        let core_term = bridge.kb.borrow().get_term(tid).clone();
        match core_term {
            CoreTerm::Const(Literal::BigInt(n)) => assert_eq!(n, big),
            other => panic!("expected Const(BigInt), got {other:?}"),
        }
    }

    #[test]
    fn compose_full_union_merges_standalone_bindings() {
        // σ1 = {x ↦ y}, σ2 = {y ↦ 5}. Full compose σ2∘σ1 = {x ↦ 5, y ↦ 5}:
        // `x` is the first-half apply (σ2 applied to σ1's range), `y` is the
        // second-half merge (σ2's standalone binding, absent in σ1). The OLD
        // partial compose dropped `y` — this pins the WI-544 fix.
        let bridge = load_source_bridge("sort Foo { entity bar }");
        // A var-to-var binding carried inside a `Value::Term(Var)` (the common
        // shape real substitutions use). The bare-`Value::Var` shape is covered
        // by `compose_chases_bare_value_var` (WI-547).
        let (vid_x, vid_y, five, var_y) = {
            let mut kb = bridge.kb.borrow_mut();
            let sx = kb.intern("x");
            let sy = kb.intern("y");
            let vx = kb.fresh_var(sx);
            let vy = kb.fresh_var(sy);
            let five = kb.alloc(CoreTerm::Const(Literal::Int(5)));
            let var_y = kb.alloc(CoreTerm::Var(Var::Global(vy)));
            (vx, vy, five, var_y)
        };
        let mut s1_inner = anthill_core::kb::subst::Substitution::new();
        s1_inner.bindings.insert(vid_x, Value::Term(var_y));
        let mut s2_inner = anthill_core::kb::subst::Substitution::new();
        s2_inner.bindings.insert(vid_y, Value::Term(five));

        let s1 = SubstBridge::from_core(s1_inner, Rc::clone(&bridge.kb));
        let s2 = SubstBridge::from_core(s2_inner, Rc::clone(&bridge.kb));
        let composed = s1.compose(&s2, &bridge);

        // Both variables are bound, both to the literal 5.
        for name in ["x", "y"] {
            let bound = composed.lookup(name.to_string())
                .unwrap_or_else(|| panic!("compose result should bind `{name}`"));
            match bridge.reify(bound) {
                TermRepr::ConstRepr { value: LiteralRepr::IntLiteral { value } } =>
                    assert_eq!(value, 5, "`{name}` should be 5"),
                other => panic!("`{name}` should reify to IntLiteral(5), got {other:?}"),
            }
        }
    }

    #[test]
    fn compose_chases_bare_value_var() {
        // σ1 = {z ↦ Value::Var(w)} (a BARE value-level var, not term-wrapped),
        // σ2 = {w ↦ 7}. compose must chase z → w → 7, not leave z ↦ w dangling
        // (WI-547). Before the fix `reify_value` passed a bare `Value::Var`
        // through, so `z` stayed unresolved.
        let bridge = load_source_bridge("sort Foo { entity bar }");
        let (vid_z, vid_w, seven) = {
            let mut kb = bridge.kb.borrow_mut();
            let sz = kb.intern("z");
            let sw = kb.intern("w");
            let vz = kb.fresh_var(sz);
            let vw = kb.fresh_var(sw);
            let seven = kb.alloc(CoreTerm::Const(Literal::Int(7)));
            (vz, vw, seven)
        };
        let mut s1_inner = anthill_core::kb::subst::Substitution::new();
        s1_inner.bindings.insert(vid_z, Value::Var(Var::Global(vid_w)));
        let mut s2_inner = anthill_core::kb::subst::Substitution::new();
        s2_inner.bindings.insert(vid_w, Value::Term(seven));

        let s1 = SubstBridge::from_core(s1_inner, Rc::clone(&bridge.kb));
        let s2 = SubstBridge::from_core(s2_inner, Rc::clone(&bridge.kb));
        let composed = s1.compose(&s2, &bridge);

        let z = composed.lookup("z".to_string()).expect("compose should bind `z`");
        match bridge.reify(z) {
            TermRepr::ConstRepr { value: LiteralRepr::IntLiteral { value } } =>
                assert_eq!(value, 7, "`z` should chase through `w` to 7"),
            other => panic!("`z` should reify to IntLiteral(7), got {other:?}"),
        }
    }

    #[test]
    fn operations_surfaces_requires_and_ensures() {
        // An op with explicit `requires`/`ensures` contract clauses surfaces
        // them as `NodeOccurrence` carriers (WI-545). `ensures` carries only
        // user clauses (no synthetic EffectsRuntime), so it's the clean signal.
        let bridge = load_source_bridge(r#"
sort Tank {
  entity tank(fuel: Int64)
  entity Full(t: Tank)
  operation fill(t: Tank) -> Tank requires Full(t) ensures Full(t)
}
"#);
        let ops = bridge.operations("Tank".into());
        let short_name = |o: &OperationInfo| {
            let kb = bridge.kb.borrow();
            let n = kb.resolve_sym(o.name.symbol()).to_string();
            n.rsplit('.').next().unwrap_or(&n).to_string()
        };
        let fill = ops.iter().find(|o| short_name(o) == "fill").expect("fill op");
        assert!(!fill.ensures.is_empty(), "fill should surface its `ensures` clause");
        assert!(!fill.requires.is_empty(), "fill should surface its `requires` clause");
        // Each clause is carried as a goal-term Value.
        match fill.ensures[0].value() {
            Value::Term(_) => {}
            other => panic!("ensures clause should be a Value::Term goal, got {other:?}"),
        }
    }

    #[test]
    fn assert_adds_fact_findable_via_facts_of() {
        // Happy path (WI-546): assert returns a fact id and the fact is then
        // enumerable via `facts_of`.
        let mut bridge = load_source_bridge("sort Slot { entity slot(n: Int64) }");
        let (slot5, slot_sort_type, slot_entity_type) = {
            let mut kb = bridge.kb.borrow_mut();
            let slot_sym = kb.try_resolve_symbol("Slot.slot").expect("Slot.slot");
            let slot_sort_sym = kb.try_resolve_symbol("Slot").expect("Slot");
            let n_sym = kb.intern("n");
            let val5 = kb.alloc(CoreTerm::Const(Literal::Int(5)));
            let s5 = kb.alloc(CoreTerm::Fn {
                functor: slot_sym, pos_args: Default::default(),
                named_args: vec![(n_sym, val5)].into(),
            });
            let sort_ref = kb.alloc(CoreTerm::Ref(slot_sort_sym));
            let entity_ref = kb.alloc(CoreTerm::Ref(slot_sym));
            (s5, Type::new(Value::Term(sort_ref)), Type::new(Value::Term(entity_ref)))
        };
        let id = bridge.assert(ReflectTerm::new(Value::Term(slot5)), slot_sort_type);
        assert!(id.is_some(), "asserting slot(n:5) should succeed");
        assert!(
            bridge.facts_of(slot_entity_type).iter()
                .any(|t| matches!(t.value(), Value::Term(tid) if *tid == slot5)),
            "facts_of should see the asserted slot(n:5)",
        );
    }

    #[test]
    fn assert_rejected_by_violated_constraint() {
        // `no_two_cycle` (a quantified guard — the kind the loader enforces)
        // forbids a 2-cycle through `a`. With only `edge(a→b)` loaded it holds;
        // asserting `edge(b→a)` completes the cycle, so the assert is rejected
        // (None) and retracted (WI-546). Mirrors the wi023 quantified-constraint
        // fixture; needs the full stdlib for the constraint's LogicalQuery
        // lowering + guard trigger-sort extraction.
        let mut bridge = load_source_bridge_with_stdlib(r#"
namespace test.assert_guard
  sort Node
    entity a
    entity b
  end
  sort Rel
    entity edge(from: Node, to: Node)
  end
  fact edge(from: a, to: b)
  constraint no_two_cycle: no ?x: edge(from: a, to: ?x) -: edge(from: ?x, to: a)
end
"#);
        let (edge_ba, rel_type) = {
            let mut kb = bridge.kb.borrow_mut();
            let edge_sym = kb.try_resolve_symbol("test.assert_guard.Rel.edge").expect("edge");
            let rel_sym = kb.try_resolve_symbol("test.assert_guard.Rel").expect("Rel");
            let a_sym = kb.try_resolve_symbol("test.assert_guard.Node.a").expect("a");
            let b_sym = kb.try_resolve_symbol("test.assert_guard.Node.b").expect("b");
            let a_ref = kb.alloc(CoreTerm::Ref(a_sym));
            let b_ref = kb.alloc(CoreTerm::Ref(b_sym));
            let from = kb.intern("from");
            let to = kb.intern("to");
            // edge(from: b, to: a) — named args canonical (from < to).
            let edge = kb.alloc(CoreTerm::Fn {
                functor: edge_sym, pos_args: Default::default(),
                named_args: vec![(from, b_ref), (to, a_ref)].into(),
            });
            let rel_ref = kb.alloc(CoreTerm::Ref(rel_sym));
            (edge, Type::new(Value::Term(rel_ref)))
        };
        let rejected = bridge.assert(ReflectTerm::new(Value::Term(edge_ba)), rel_type);
        assert!(rejected.is_none(),
            "asserting edge(b→a) completes a 2-cycle → rejected by `no_two_cycle`");
    }

    /// Drift-guard (WI-540): the reflect `KB` / `Substitution` interface is
    /// GENERATED from `reflect.anthill` (the single source of truth) and
    /// `include!`d. This statically asserts the host bridge implements that
    /// generated interface — so a spec edit that changes the interface, or a
    /// bridge change that diverges from it, is a compile error *here*. The
    /// "bridge == spec, by construction" guarantee, made explicit.
    #[test]
    fn bridge_implements_generated_reflect_interface() {
        fn assert_kb<T: KB>() {}
        fn assert_substitution<T: Substitution>() {}
        assert_kb::<KbBridge>();
        assert_substitution::<SubstBridge>();
    }
}

use std::cell::RefCell;
use std::rc::Rc;

use anthill_core::eval::Value;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::{Term as CoreTerm, TermId, Literal, Var};
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

/// Map a core [`Literal`] to its host [`LiteralRepr`] (struct-variant form).
/// `reflect.anthill`'s `LiteralRepr` has no `BigInt` case, so a `BigInt` is
/// surfaced as its decimal `StringLiteral` (a Foundation limitation — a
/// first-class `BigIntLiteral` is a follow-up); a `Handle` lowers to its id.
fn literal_to_repr(lit: Literal) -> LiteralRepr {
    match lit {
        Literal::String(s) => LiteralRepr::StringLiteral { value: s },
        Literal::Int(n) => LiteralRepr::IntLiteral { value: n },
        Literal::BigInt(n) => LiteralRepr::StringLiteral { value: n.to_string() },
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
    fn kb() -> Box<dyn KB> {
        panic!("KB.kb() not host-constructible — build a KbBridge from a KnowledgeBase (WI-540 follow-up)")
    }

    fn reify(&self, t: Term) -> TermRepr {
        self.reify_view(t.value())
    }

    fn reflect(&self, r: TermRepr) -> Term {
        match r {
            TermRepr::ConstRepr { value } => {
                let lit = match value {
                    LiteralRepr::IntLiteral { value } => Literal::Int(value),
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

            // `meta` is a `Term`; default to a bare `meta` ref when the fact
            // lacks it. `requires`/`ensures` (NodeOccurrence lists) are not yet
            // surfaced host-side (Foundation) → empty.
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
                // FOUNDATION LIMITATION (WI-540 follow-up): the spec's
                // `requires`/`ensures` are `List[NodeOccurrence]` — real
                // pre/postcondition occurrences the loader stores and the typer
                // reads (`load.rs` `OperationInfo.requires`). The host bridge does
                // not yet surface them as occurrences (`NodeOccurrence` is an
                // opaque host carrier here), so it reports them EMPTY. NOT a
                // silent drop: a host consumer must read these as "not yet
                // populated by the bridge", not "the op has no contracts".
                requires: vec![],
                ensures: vec![],
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

    fn facts_of(&self, _sort: Type) -> Vec<Term> {
        panic!("KB.facts_of not yet implemented (WI-540 follow-up)")
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

    fn assert(&mut self, _term: Term, _sort: Type) -> Option<FactId> {
        panic!("KB.assert not yet implemented (WI-540 follow-up)")
    }

    fn add_guard(&mut self, _guard: LogicalQuery) -> ConstraintId {
        panic!("KB.add_guard not yet implemented (WI-540 follow-up)")
    }
}

// ── SubstBridge: impl Substitution ──────────────────────────────
//
// `SubstBridge` carries its own `KnowledgeBase` handle so `apply` / `compose` /
// `lookup` need only the wrapped core substitution (the trait's `&dyn KB`
// param is the spec shape but unused here — the host carries its KB).

impl Substitution for SubstBridge {
    fn apply(&self, t: Term, _kb: &dyn KB) -> Term {
        // Carrier-faithful: a `Value::Node` binding substitutes through
        // `reify_value`'s `substitute_occurrence`, preserving identity/span.
        rterm(self.kb.borrow_mut().reify_value(t.value(), &self.inner))
    }

    /// PARTIAL through a trait object (WI-540 follow-up): full composition is
    /// `apply s2 to self's range, THEN extend with s2's bindings for vars absent
    /// in self` (the interpreter `subst_compose` does this on concrete substs).
    /// The second half needs to ENUMERATE `s2`'s bindings, which `&dyn
    /// Substitution` cannot expose (the spec trait has only `apply`/`compose`/
    /// `lookup`). So this does only the first half — it applies `s2` to each of
    /// self's binding values and returns those; it does NOT merge in `s2`'s
    /// standalone bindings. NOT silent: a caller needing full composition must
    /// pass concrete substitutions, or the spec's `Substitution` needs a
    /// binding-enumeration op (the follow-up). Currently unused by the bridge.
    fn compose(&self, s2: &dyn Substitution, kb: &dyn KB) -> Box<dyn Substitution> {
        let mut result = self.inner.clone();
        for (_var, val) in result.bindings.iter_mut() {
            *val = s2.apply(rterm(val.clone()), kb).into_value();
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

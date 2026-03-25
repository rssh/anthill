use std::cell::RefCell;
use std::rc::Rc;

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::{Term as CoreTerm, TermId, Literal, Var};
use anthill_core::kb::resolve::{SearchStream, ResolveConfig};

use crate::prelude::Stream;
use crate::reflect::*;

/// Extract the Symbol from a TermId that must be a Ref or Ident term.
/// Panics with `context` in the message if the term is something else.
fn expect_symbol(kb: &KnowledgeBase, id: TermId, context: &str) -> anthill_core::intern::Symbol {
    match kb.get_term(id) {
        CoreTerm::Ref(sym) | CoreTerm::Ident(sym) => *sym,
        other => panic!("{}: expected Ref or Ident term, got {:?}", context, other),
    }
}

// ── KbBridge ────────────────────────────────────────────────────

pub struct KbBridge {
    pub kb: Rc<RefCell<KnowledgeBase>>,
}

impl KbBridge {
    pub fn new(kb: KnowledgeBase) -> Self {
        Self { kb: Rc::new(RefCell::new(kb)) }
    }

    fn reify_term(&self, id: TermId) -> TermRepr {
        let mut kb = self.kb.borrow_mut();
        match kb.get_term(id).clone() {
            CoreTerm::Const(lit) => TermRepr::ConstRepr {
                value: match lit {
                    Literal::String(s) => LiteralRepr::StringLiteral(s),
                    Literal::Int(n) => LiteralRepr::IntLiteral(n),
                    Literal::BigInt(n) => LiteralRepr::BigIntLiteral(n),
                    Literal::Float(f) => LiteralRepr::FloatLiteral(f.into()),
                    Literal::Bool(b) => LiteralRepr::BoolLiteral(b),
                    Literal::Handle(_, id) => LiteralRepr::IntLiteral(id as i64),
                },
            },
            CoreTerm::Var(Var::Global(vid)) => TermRepr::VarRepr {
                name: kb.resolve_sym(vid.name()).to_string(),
            },
            CoreTerm::Var(Var::DeBruijn(n)) => TermRepr::VarRepr {
                name: format!("_{n}"),
            },
            CoreTerm::Fn { functor, pos_args, named_args } => {
                let name_term = kb.alloc(CoreTerm::Ref(functor));
                let pos: Vec<TermId> = pos_args.iter().copied().collect();
                let named: Vec<TermId> = named_args.iter().map(|&(_, id)| id).collect();
                drop(kb);
                let mut args = Vec::with_capacity(pos.len() + named.len());
                for child_id in pos.into_iter().chain(named) {
                    args.push(self.reify_term(child_id));
                }
                TermRepr::FnRepr { name: name_term, args }
            }
            CoreTerm::Ref(sym) => {
                let name_term = kb.alloc(CoreTerm::Ref(sym));
                TermRepr::RefRepr { name: name_term }
            }
            CoreTerm::Bottom => {
                let bottom_sym = kb.intern("⊥");
                let name_term = kb.alloc(CoreTerm::Ref(bottom_sym));
                TermRepr::RefRepr { name: name_term }
            }
            CoreTerm::Ident(sym) => {
                let name_term = kb.alloc(CoreTerm::Ref(sym));
                TermRepr::RefRepr { name: name_term }
            }
        }
    }

    /// Resolve a name string to a sort-level TermId via make_name_term.
    fn resolve_sort_name(&self, name: &str) -> TermId {
        self.kb.borrow_mut().make_name_term(name)
    }

    /// Get all fact head TermIds for a given KB sort name (e.g. "Sort", "Operation").
    fn facts_by_sort_name(&self, sort_name: &str) -> Vec<(anthill_core::kb::RuleId, TermId)> {
        let sort_term = self.resolve_sort_name(sort_name);
        let kb = self.kb.borrow();
        kb.by_sort(sort_term)
            .into_iter()
            .map(|rid| (rid, kb.fact_term(rid)))
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

    /// Get a displayable name for a TermId (resolves Ref/Ident symbols, formats others).
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
            CoreTerm::Bottom => "⊥".into(),
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
            // member(name, kind, parent) — 3 positional args
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

    /// Look up an Entity definition by name, returning its functor symbol
    /// and the list of field name symbols. Falls back to inferring schema
    /// from existing facts with matching functor if no Entity definition exists.
    fn find_entity_schema(&self, sort_name: &str) -> Option<(anthill_core::intern::Symbol, Vec<anthill_core::intern::Symbol>)> {
        // First try Entity definitions
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

        // Fall back: find any fact in the KB with matching functor and infer schema.
        // Use scope-aware resolution from _global (covers qualified names and imports),
        // then fall back to intern for unknown names.
        let mut kb = self.kb.borrow_mut();
        let plain_sym = kb.resolve_name_in_global(sort_name)
            .unwrap_or_else(|| kb.intern(sort_name));
        let rids = kb.by_functor(plain_sym);
        for rid in rids {
            let head = kb.fact_term(rid);
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

    /// Convert a `LogicalQuery` to goal `TermId`s and a `ResolveConfig`.
    fn query_to_goals_and_config(
        &self,
        query: &LogicalQuery,
    ) -> Result<(Vec<TermId>, ResolveConfig), Error> {
        let mut config = ResolveConfig::default();
        let goals = self.query_to_goals(query, &mut config)?;
        Ok((goals, config))
    }

    /// Recursively convert a `LogicalQuery` into goal `TermId`s.
    fn query_to_goals(
        &self,
        query: &LogicalQuery,
        config: &mut ResolveConfig,
    ) -> Result<Vec<TermId>, Error> {
        match query {
            LogicalQuery::EmptyQuery => Ok(vec![]),
            LogicalQuery::PatternQuery { term } => Ok(vec![*term]),
            LogicalQuery::SortQuery { sort_name } => {
                // Build a schema-aware query: look up the Entity definition
                // for sort_name and create a pattern with fresh variables
                // for each named field.
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
                        Ok(vec![goal])
                    }
                    None => {
                        // No entity definition found — fall back to functor(?_query)
                        let sort_sym = kb.intern(sort_name);
                        let query_var_sym = kb.intern("?_query");
                        let vid = kb.fresh_var(query_var_sym);
                        let var_term = kb.alloc(CoreTerm::Var(Var::Global(vid)));
                        let goal = kb.alloc(CoreTerm::Fn {
                            functor: sort_sym,
                            pos_args: vec![var_term].into(),
                            named_args: Default::default(),
                        });
                        Ok(vec![goal])
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

/// Adapts `SearchStream` (consuming split_first + &mut KB) to the
/// `Stream<SubstBridge, Error>` trait (shared-ref split_first).
struct SearchStreamAdapter {
    inner: RefCell<Option<SearchStream>>,
    kb: Rc<RefCell<KnowledgeBase>>,
}

impl Stream<SubstBridge, Error> for SearchStreamAdapter {
    fn split_first(&self) -> Result<Option<(SubstBridge, Box<dyn Stream<SubstBridge, Error>>)>, Error> {
        let stream = self.inner.borrow_mut().take()
            .ok_or_else(|| Error("stream already consumed".into()))?;
        let mut kb = self.kb.borrow_mut();
        match stream.split_first(&mut kb) {
            Some((solution, rest)) => {
                let elem = SubstBridge::from_core(solution.subst);
                let cont: Box<dyn Stream<SubstBridge, Error>> = Box::new(SearchStreamAdapter {
                    inner: RefCell::new(Some(rest)),
                    kb: Rc::clone(&self.kb),
                });
                Ok(Some((elem, cont)))
            }
            None => Ok(None),
        }
    }

    fn head(&self) -> Result<Option<SubstBridge>, Error> {
        match self.split_first()? {
            Some((h, _)) => Ok(Some(h)),
            None => Ok(None),
        }
    }

    fn tail(&self) -> Result<Box<dyn Stream<SubstBridge, Error>>, Error> {
        match self.split_first()? {
            Some((_, t)) => Ok(t),
            None => Ok(Box::new(SearchStreamAdapter {
                inner: RefCell::new(None),
                kb: Rc::clone(&self.kb),
            })),
        }
    }

    fn take_n(&self, n: i64) -> Result<Vec<SubstBridge>, Error> {
        let mut results = Vec::new();
        let mut current = self.inner.borrow_mut().take();
        let mut kb = self.kb.borrow_mut();
        for _ in 0..n {
            match current.take() {
                Some(s) => match s.split_first(&mut kb) {
                    Some((sol, rest)) => {
                        results.push(SubstBridge::from_core(sol.subst));
                        current = Some(rest);
                    }
                    None => break,
                },
                None => break,
            }
        }
        drop(kb);
        *self.inner.borrow_mut() = current;
        Ok(results)
    }

    fn collect_all(&self) -> Result<Vec<SubstBridge>, Error> {
        let mut results = Vec::new();
        let mut current = self.inner.borrow_mut().take();
        let mut kb = self.kb.borrow_mut();
        loop {
            match current.take() {
                Some(s) => match s.split_first(&mut kb) {
                    Some((sol, rest)) => {
                        results.push(SubstBridge::from_core(sol.subst));
                        current = Some(rest);
                    }
                    None => break,
                },
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
    fn reify(&self, t: Term) -> TermRepr {
        self.reify_term(t)
    }

    fn reflect(&self, r: TermRepr) -> Term {
        let mut kb = self.kb.borrow_mut();
        match r {
            TermRepr::ConstRepr { value } => {
                let lit = match value {
                    LiteralRepr::IntLiteral(n) => Literal::Int(n),
                    LiteralRepr::BigIntLiteral(n) => Literal::BigInt(n),
                    LiteralRepr::FloatLiteral(f) => Literal::Float(f.into()),
                    LiteralRepr::StringLiteral(s) => Literal::String(s),
                    LiteralRepr::BoolLiteral(b) => Literal::Bool(b),
                };
                kb.alloc(CoreTerm::Const(lit))
            }
            TermRepr::VarRepr { name } => {
                let sym = kb.intern(&name);
                let vid = kb.fresh_var(sym);
                kb.alloc(CoreTerm::Var(Var::Global(vid)))
            }
            TermRepr::FnRepr { name, args } => {
                let functor = expect_symbol(&kb, name, "FnRepr.name");
                drop(kb);
                let child_ids: Vec<TermId> = args.into_iter()
                    .map(|a| self.reflect(a))
                    .collect();
                let mut kb = self.kb.borrow_mut();
                kb.alloc(CoreTerm::Fn {
                    functor,
                    pos_args: child_ids.into(),
                    named_args: Default::default(),
                })
            }
            TermRepr::RefRepr { name } => {
                let sym = expect_symbol(&kb, name, "RefRepr.name");
                kb.alloc(CoreTerm::Ref(sym))
            }
            TermRepr::QuotedRepr { source, .. } => {
                kb.alloc(CoreTerm::Const(Literal::String(source)))
            }
        }
    }

    fn nonvar(&self, x: Term) -> bool {
        let kb = self.kb.borrow();
        !matches!(kb.get_term(x), CoreTerm::Var(_))
    }

    fn ground(&self, x: Term) -> bool {
        let kb = self.kb.borrow();
        kb.collect_vars(x).is_empty()
    }

    fn apply_core_subst(&self, t: Term, subst: &anthill_core::kb::subst::Substitution) -> Term {
        self.kb.borrow_mut().apply_subst(t, subst)
    }

    fn sorts(&self, namespace: Option<String>) -> Vec<SortInfo> {
        let mut results = vec![];

        // SortInfo facts have named args: name, definition, constructors, operations, parameters, requires
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

            // Filter by namespace if specified
            if let Some(ref ns) = namespace {
                let name_str = self.term_display_name(name_tid);
                if !name_str.starts_with(ns) {
                    continue;
                }
            }

            let ctors = field("constructors").map(|t| self.collect_list_refs(t)).unwrap_or_default();
            let ops = field("operations").map(|t| self.collect_list_refs(t)).unwrap_or_default();
            let params = field("parameters").map(|t| self.collect_list_refs(t)).unwrap_or_default();
            let reqs = field("requires").map(|t| self.collect_list_terms(t)).unwrap_or_default();

            results.push(SortInfo {
                name: name_tid,
                definition: definition_tid,
                constructors: ctors,
                operations: ops,
                parameters: params,
                requires: reqs,
            });
        }

        results
    }

    fn operations(&self, sort_name: &str) -> Vec<OperationInfo> {
        let mut results = vec![];

        // OperationInfo facts have named args: name, sort_context, params, return_type, effects
        for (rid, head) in self.facts_by_sort_name("Operation") {
            let functor = self.term_functor_name(head);
            if functor.as_deref() != Some("OperationInfo") {
                continue;
            }

            // Check that this operation's domain matches the requested sort
            let kb = self.kb.borrow();
            let domain = kb.fact_domain(rid);
            drop(kb);
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
            let sort_context_tid = field("sort_context");
            let return_type_tid = match field("return_type") {
                Some(tid) => tid,
                None => continue,
            };

            // Extract sort_context: some(value: Ref) → Some(Ref), none() → None
            let sort_context = sort_context_tid.and_then(|tid| {
                let fname = self.term_functor_name(tid);
                match fname.as_deref() {
                    Some("some") => {
                        let args = self.term_named_args(tid);
                        args.iter().find(|(n, _)| n == "value").map(|(_, v)| *v)
                    }
                    _ => None,
                }
            });

            // Extract params from cons-list of FieldInfo terms
            let params = field("params")
                .map(|t| {
                    self.collect_list_terms(t)
                        .into_iter()
                        .map(|fi_tid| {
                            let fi_named = self.term_named_args(fi_tid);
                            let fi_field = |key: &str| fi_named.iter().find(|(n, _)| n == key).map(|(_, tid)| *tid);
                            let name = fi_field("name")
                                .map(|t| self.term_display_name(t))
                                .unwrap_or_default();
                            let type_name = fi_field("type_name").unwrap_or(fi_tid);
                            FieldInfo { name, type_name }
                        })
                        .collect()
                })
                .unwrap_or_default();

            let effects = field("effects")
                .map(|t| self.collect_list_terms(t))
                .unwrap_or_default();

            results.push(OperationInfo {
                name: name_tid,
                sort_context,
                params,
                return_type: return_type_tid,
                effects,
            });
        }

        results
    }

    fn constructors(&self, sort_name: &str) -> Vec<String> {
        self.members_of_kind(sort_name, "Constructor")
            .into_iter()
            .map(|n| self.short_name(&n))
            .collect()
    }

    fn fields(&self, name: &str) -> Vec<FieldInfo> {
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
                results.push(FieldInfo {
                    name: field_name,
                    type_name: field_tid,
                });
            }
            break;
        }

        results
    }

    fn rules(&self, sort_name: &str) -> Vec<TermRepr> {
        let mut results = vec![];

        for (rid, head) in self.facts_by_sort_name("Rule") {
            let kb = self.kb.borrow();
            let domain = kb.fact_domain(rid);
            drop(kb);
            let domain_name = self.term_display_name(domain);
            if domain_name != sort_name && self.short_name(&domain_name) != sort_name {
                continue;
            }
            results.push(self.reify_term(head));
        }

        results
    }

    fn descriptions(&self, target: Option<&str>) -> Vec<DescriptionInfo> {
        let mut results = vec![];

        // Description facts: Description(target_term, text_term)
        for (_rid, head) in self.facts_by_sort_name("Description") {
            let pos = self.term_pos_args(head);
            if pos.len() < 2 {
                continue;
            }
            let desc_target_tid = pos[0];
            let desc_content = self.term_display_name(pos[1]);

            if let Some(t) = target {
                let desc_target_name = self.term_display_name(desc_target_tid);
                if desc_target_name != t && self.short_name(&desc_target_name) != t {
                    continue;
                }
            }

            results.push(DescriptionInfo {
                target: desc_target_tid,
                content: desc_content,
            });
        }

        results
    }

    fn execute(
        &self,
        query: LogicalQuery,
    ) -> Result<Box<dyn crate::prelude::Stream<SubstBridge, Error>>, Error> {
        let (goals, config) = self.query_to_goals_and_config(&query)?;
        let stream = self.kb.borrow().resolve_lazy(&goals, &config);
        Ok(Box::new(SearchStreamAdapter {
            inner: RefCell::new(Some(stream)),
            kb: Rc::clone(&self.kb),
        }))
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
}

// ── Substitution impl for SubstBridge ───────────────────────────

impl Substitution for SubstBridge {
    fn apply(&self, t: Term, kb: &dyn KB) -> Term {
        kb.apply_core_subst(t, &self.inner)
    }

    fn compose(&self, s2: &dyn Substitution, kb: &dyn KB) -> Box<dyn Substitution> {
        // Apply s2 to every binding value in self
        let mut result = self.inner.clone();
        for (_var, tid) in result.bindings.iter_mut() {
            *tid = s2.apply(*tid, kb);
        }
        // s2's own bindings that aren't in self are not accessible through
        // the trait — full compose needs same-type access. SubstBridge
        // provides compose_with for that case.
        Box::new(SubstBridge { inner: result })
    }
}

impl SubstBridge {
    /// Full composition when both substitutions are SubstBridge.
    pub fn compose_with(&self, s2: &SubstBridge, kb: &dyn KB) -> SubstBridge {
        let mut result = self.inner.clone();
        for (_var, tid) in result.bindings.iter_mut() {
            *tid = kb.apply_core_subst(*tid, &s2.inner);
        }
        for (var, tid) in s2.inner.iter() {
            result.bindings.entry(*var).or_insert(*tid);
        }
        SubstBridge { inner: result }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;
    use anthill_core::kb::KnowledgeBase;
    use anthill_core::kb::load::{self, NullResolver};
    use anthill_core::kb::term::Literal;
    use anthill_core::parse;

    /// Collect all .anthill files under a directory, recursively.
    #[allow(dead_code)]
    fn collect_anthill_files(dir: &std::path::Path) -> Vec<PathBuf> {
        let mut files = Vec::new();
        if dir.is_dir() {
            for entry in std::fs::read_dir(dir).expect("read stdlib dir") {
                let entry = entry.expect("read dir entry");
                let path = entry.path();
                if path.is_dir() {
                    files.extend(collect_anthill_files(&path));
                } else if path.extension().is_some_and(|e| e == "anthill") {
                    files.push(path);
                }
            }
        }
        files.sort();
        files
    }

    /// Load stdlib into a KnowledgeBase and return it wrapped in a KbBridge.
    #[allow(dead_code)]
    fn load_stdlib_bridge() -> KbBridge {
        let stdlib_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../stdlib/anthill");
        let files = collect_anthill_files(&stdlib_dir);
        let parsed: Vec<_> = files.iter().map(|f| {
            let source = std::fs::read_to_string(f).expect("read file");
            parse::parse(&source).unwrap_or_else(|e| panic!("parse {} failed: {:?}", f.display(), e))
        }).collect();
        let refs: Vec<&_> = parsed.iter().collect();

        let mut kb = KnowledgeBase::new();
        load::register_prelude(&mut kb);
        kb.register_standard_builtins();
        load::load_all(&mut kb, &refs, &NullResolver)
            .unwrap_or_else(|e| panic!("load failed: {:?}", e));

        KbBridge::new(kb)
    }

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
  operation persist(s: Store, fact: Int) -> Int
  operation retract(s: Store, id: Int) -> Int
  operation flush(s: Store) -> Int
}
"#);
        let query = LogicalQuery::SortQuery { sort_name: "OperationInfo".into() };
        let stream = bridge.execute(query).expect("execute failed");
        let results = stream.collect_all().expect("collect failed");
        assert!(results.len() >= 3,
            "should find at least 3 OperationInfo facts, got {}", results.len());
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
        assert_eq!(results.len(), 1, "empty query should return 1 result (trivial substitution)");
    }

    #[test]
    fn execute_pattern_query() {
        let bridge = load_source_bridge(r#"
sort Animal { entity dog entity cat }
fact dog
fact cat
"#);
        // Build a pattern query for dog — use resolve_qualified_name_term to get the
        // same symbol the loader used (dog is defined as entity)
        let goal = {
            let mut kb = bridge.kb.borrow_mut();
            kb.resolve_qualified_name_term("Animal.dog")
        };
        let query = LogicalQuery::PatternQuery { term: goal };
        let stream = bridge.execute(query).expect("execute failed");
        let results = stream.collect_all().expect("collect failed");
        assert!(results.len() >= 1, "pattern query for 'dog' should find at least 1 result, got {}", results.len());
    }

    #[test]
    fn execute_limited_query() {
        let bridge = load_source_bridge(r#"
sort Store {
  entity store
  operation persist(s: Store, fact: Int) -> Int
  operation retract(s: Store, id: Int) -> Int
  operation flush(s: Store) -> Int
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
}

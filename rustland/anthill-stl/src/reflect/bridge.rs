use std::cell::RefCell;
use std::rc::Rc;

use anthill_core::eval::Value;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::{Term as CoreTerm, TermId, Literal, Var, VarId};
use anthill_core::kb::term_view::TermView;
use anthill_core::kb::resolve::{SearchStream, ResolveConfig};

use crate::prelude::{Stream, Modifiable, Type};
use crate::reflect::reader;
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
    ReflectTerm::new(Value::term(id))
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

/// Inverse of [`literal_to_repr`]: a host [`LiteralRepr`] → core [`Literal`].
/// Total (the enum is closed); a `Float` widens back through `OrderedFloat`.
fn repr_to_literal(r: LiteralRepr) -> Literal {
    match r {
        LiteralRepr::IntLiteral { value } => Literal::Int(value),
        LiteralRepr::BigIntLiteral { value } => Literal::BigInt(value),
        LiteralRepr::FloatLiteral { value } => Literal::Float(value.into()),
        LiteralRepr::StringLiteral { value } => Literal::String(value),
        LiteralRepr::BoolLiteral { value } => Literal::Bool(value),
    }
}

/// Host realization of [`reader::ReifyBuilder`]: emits the generated [`TermRepr`]
/// enum. A `Ref`/`Fn` name rides as a `Symbol` (the spec types it so). Stateless
/// — all carrier state is in the emitted `TermRepr`.
struct TermReprBuilder;

impl reader::ReifyBuilder for TermReprBuilder {
    type Repr = TermRepr;

    fn on_literal(&mut self, _kb: &mut KnowledgeBase, lit: Literal) -> TermRepr {
        TermRepr::ConstRepr { value: literal_to_repr(lit) }
    }

    fn on_var(&mut self, _kb: &mut KnowledgeBase, name: String) -> TermRepr {
        TermRepr::VarRepr { name }
    }

    fn on_ref(&mut self, _kb: &mut KnowledgeBase, name: anthill_core::intern::Symbol) -> TermRepr {
        TermRepr::RefRepr { name: ReflectSymbol::new(name) }
    }

    fn on_fn(
        &mut self,
        _kb: &mut KnowledgeBase,
        functor: anthill_core::intern::Symbol,
        args: Vec<TermRepr>,
    ) -> TermRepr {
        TermRepr::FnRepr { name: ReflectSymbol::new(functor), args }
    }
}

/// Host realization of [`reader::ReflectReader`]: classifies the generated
/// [`TermRepr`] enum. Infallible — the enum is closed and every variant maps to
/// a [`reader::ReflectShape`] (a `QuotedRepr` decodes to a `Const` string, the
/// bridge peer of the interpreter reader). Names ride as `Symbol`.
impl reader::ReflectReader for TermRepr {
    type Error = std::convert::Infallible;

    fn classify(
        self,
        _kb: &KnowledgeBase,
    ) -> Result<reader::ReflectShape<Self>, std::convert::Infallible> {
        Ok(match self {
            TermRepr::ConstRepr { value } => reader::ReflectShape::Const(repr_to_literal(value)),
            TermRepr::VarRepr { name } => reader::ReflectShape::Var(name),
            TermRepr::RefRepr { name } => reader::ReflectShape::Ref(name.symbol()),
            TermRepr::FnRepr { name, args } => reader::ReflectShape::Fn(name.symbol(), args),
            TermRepr::QuotedRepr { source, .. } => {
                reader::ReflectShape::Const(Literal::String(source))
            }
        })
    }
}

/// Build a fieldful `Value::Entity` (no positional args) — the record shape the
/// reflect `LogicalQuery.*` constructors take. Used by the WI-549 guard reifier.
#[inline]
fn lq_entity(
    functor: anthill_core::intern::Symbol,
    named: Vec<(anthill_core::intern::Symbol, Value)>,
) -> Value {
    Value::Entity { functor, pos: Vec::new().into(), named: named.into(), ty: None }
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
                let name = reader::term_display_name(&self.kb.borrow(), tid);
                self.kb.borrow_mut().intern(&name)
            }
        };
        ReflectSymbol::new(sym)
    }

    /// Reify any [`TermView`] carrier — a hash-consed `TermId` / `Value::Term`,
    /// a `Value::Node` occurrence, a `Value::Entity`, or a value-level `Var` —
    /// to a flat [`TermRepr`]. The single reifier behind both `KB::reify` and
    /// `KB::rules`, via the shared [`reader::reify_walk`] parameterized by
    /// [`TermReprBuilder`] (the interpreter drives the same walk with its own
    /// `Value`-tree builder). Functor/ref names ride as `Symbol` (the spec types
    /// them so); a functor-less aggregate or opaque value in a term slot panics
    /// loudly.
    fn reify_view<V: TermView>(&self, view: &V) -> TermRepr {
        reader::reify_walk(&mut self.kb.borrow_mut(), view, &mut TermReprBuilder)
    }

    /// Extract named args from a Fn term as (name_str, TermId) pairs. Kept for
    /// decoding an operation's `FieldInfo` parameter terms ([`field_info_of`]),
    /// the one place the bridge still reads a `Fn`'s named args directly.
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

    /// Decode an operation parameter's `FieldInfo` term into the reflect struct.
    /// `name` defaults to `_` when absent; `type_name` falls back to the FieldInfo
    /// term itself (mirrors the prior inline `operations` params decode).
    fn field_info_of(&self, fi_tid: TermId) -> FieldInfo {
        let fi_named = self.term_named_args(fi_tid);
        let fi_field = |key: &str| fi_named.iter().find(|(n, _)| n == key).map(|(_, tid)| *tid);
        let name = match fi_field("name") {
            Some(t) => self.sym_of(t),
            None => ReflectSymbol::new(self.kb.borrow_mut().intern("_")),
        };
        let type_name = fi_field("type_name").unwrap_or(fi_tid);
        FieldInfo { name, type_name: term(type_name) }
    }

    /// Given an already-resolved entity functor, return its field-name symbols.
    /// Prefers the declared entity schema (the `entity_field_types` registry,
    /// WI-515); falls back to inferring the field set from an existing fact with
    /// that functor. `None` means "no declared entity and no matching fact" —
    /// the caller then emits its positional fallback goal. WI-632: the functor
    /// arrives resolved by reference (the caller's `value_functor` extraction),
    /// so there is no name-string resolution and no short-name ambiguity here —
    /// the WI-631 loud-ambiguity stopgap is subsumed at the write site.
    fn find_entity_schema(&self, functor: anthill_core::intern::Symbol) -> Option<Vec<anthill_core::intern::Symbol>> {
        let kb = self.kb.borrow();
        if let Some(fields) = kb.entity_field_types(functor) {
            return Some(fields.iter().map(|&(sym, _)| sym).collect());
        }
        for rid in kb.rules_by_functor(functor) {
            let head = match kb.rule_head_value(rid) {
                anthill_core::eval::Value::Term { id: t, .. } => *t,
                _ => continue,
            };
            if let CoreTerm::Fn { named_args, .. } = kb.get_term(head) {
                return Some(named_args.iter().map(|&(s, _)| s).collect());
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
            LogicalQuery::SortQuery { sort } => {
                // WI-632: `sort` is a by-reference `Term` (a `Ref` resolved at the
                // caller's write site); extract its already-qualified functor via
                // the shared `value_functor` — no name-string resolution.
                let functor = anthill_core::eval::value_functor(&self.kb.borrow(), sort.value())
                    .ok_or_else(|| Error(
                        "KB.sort_query: `sort` is not a sort reference (expected a \
                         Ref / Fn / Entity carrier that names a functor)".to_string()
                    ))?;
                let field_syms = self.find_entity_schema(functor);

                let mut kb = self.kb.borrow_mut();
                match field_syms {
                    Some(field_syms) => {
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
                        Ok(vec![Value::term(goal)])
                    }
                    None => {
                        let query_var_sym = kb.intern("?_query");
                        let vid = kb.fresh_var(query_var_sym);
                        let var_term = kb.alloc(CoreTerm::Var(Var::Global(vid)));
                        let goal = kb.alloc(CoreTerm::Fn {
                            functor,
                            pos_args: vec![var_term].into(),
                            named_args: Default::default(),
                        });
                        Ok(vec![Value::term(goal)])
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

    /// Reify a generated reflect [`LogicalQuery`] into a KB guard [`Value`] built
    /// from the `anthill.reflect.LogicalQuery.*` constructors (WI-549). DISTINCT
    /// from [`query_to_goals`](Self::query_to_goals), which FLATTENS a query to
    /// resolver goals (unwrapping `pattern_query`) — wrong for a guard, whose
    /// structure `collect_trigger_sorts` + `evaluate_guard` must walk intact.
    ///
    /// Built as a `Value::Entity` carrier, uniform with the interpreter's eval-side
    /// reflect builders (`kb_sort_template`) and carrier-faithful: a `PatternQuery`'s
    /// inner term rides verbatim, preserving a `Value::Node` occurrence a hash-consed
    /// `Term::Fn` could not hold. The carrier-agnostic guard machinery (WI-513
    /// `lower_query_with`, `collect_trigger_sorts`) reads it through `TermView`
    /// exactly as it reads the loader's hash-consed form. Total over every enum
    /// variant — no lossy fallback.
    fn reify_logical_query(kb: &mut KnowledgeBase, q: &LogicalQuery) -> Value {
        match q {
            LogicalQuery::EmptyQuery => lq_entity(Self::lq_ctor(kb, "empty_query"), vec![]),
            LogicalQuery::PatternQuery { term } => {
                let f = Self::lq_ctor(kb, "pattern_query");
                let k = kb.intern("term");
                lq_entity(f, vec![(k, term.value().clone())])
            }
            LogicalQuery::SortQuery { sort } => {
                let f = Self::lq_ctor(kb, "sort_query");
                let k = kb.intern("sort");
                lq_entity(f, vec![(k, sort.value().clone())])
            }
            LogicalQuery::Conjunction { left, right } =>
                Self::reify_binary(kb, "conjunction", left, right),
            LogicalQuery::Disjunction { left, right } =>
                Self::reify_binary(kb, "disjunction", left, right),
            LogicalQuery::Negation { query } => {
                let f = Self::lq_ctor(kb, "negation");
                let inner = Self::reify_logical_query(kb, query);
                let k = kb.intern("query");
                lq_entity(f, vec![(k, inner)])
            }
            LogicalQuery::Guarded { query, condition } => {
                let f = Self::lq_ctor(kb, "guarded");
                let inner = Self::reify_logical_query(kb, query);
                let (qk, ck) = (kb.intern("query"), kb.intern("condition"));
                lq_entity(f, vec![(qk, inner), (ck, condition.value().clone())])
            }
            LogicalQuery::Projected { query, vars } => {
                let f = Self::lq_ctor(kb, "projected");
                let inner = Self::reify_logical_query(kb, query);
                let vars_list = Self::reify_string_list(kb, vars);
                let (qk, vk) = (kb.intern("query"), kb.intern("vars"));
                lq_entity(f, vec![(qk, inner), (vk, vars_list)])
            }
            LogicalQuery::Limited { query, count } => {
                let f = Self::lq_ctor(kb, "limited");
                let inner = Self::reify_logical_query(kb, query);
                let (qk, ck) = (kb.intern("query"), kb.intern("count"));
                lq_entity(f, vec![(qk, inner), (ck, Value::Int(*count))])
            }
            // Quantifiers all share `{var, condition, body}` and lower to an
            // enforceable boolean guard (`eval_count_guard`/`eval_forall_guard`).
            LogicalQuery::ForallQ { var, condition, body } =>
                Self::reify_quantifier(kb, "forall_q", var, condition, body),
            LogicalQuery::SomeQ { var, condition, body } =>
                Self::reify_quantifier(kb, "some_q", var, condition, body),
            LogicalQuery::OneQ { var, condition, body } =>
                Self::reify_quantifier(kb, "one_q", var, condition, body),
            LogicalQuery::LoneQ { var, condition, body } =>
                Self::reify_quantifier(kb, "lone_q", var, condition, body),
            LogicalQuery::NoQ { var, condition, body } =>
                Self::reify_quantifier(kb, "no_q", var, condition, body),
            // Aggregations reduce a query to a *value*, not a boolean — they are
            // not constraints, so they cannot be guards. The guard engine cannot
            // lower them (`lower_query_with` → `NotYetImplemented`), so registering
            // one would defer to a misleading panic at the next matching assert
            // (`assert_checked`'s Err arm assumes a load-time `check_all_guards`
            // rejected it — which never runs on this bridge path). Reject loudly
            // and EARLY here instead. The loader never reaches this (its
            // `build_logical_query` returns `None` for `Aggregation`).
            LogicalQuery::CountQ { .. }
            | LogicalQuery::SumQ { .. }
            | LogicalQuery::MinQ { .. }
            | LogicalQuery::MaxQ { .. } => panic!(
                "KB.add_guard: an aggregation LogicalQuery (count_q/sum_q/min_q/max_q) \
                 reduces to a value, not a boolean — it cannot be registered as a guard"),
        }
    }

    /// Reify a binary `{left, right}` LogicalQuery (`conjunction` / `disjunction`).
    fn reify_binary(
        kb: &mut KnowledgeBase,
        short: &str,
        left: &LogicalQuery,
        right: &LogicalQuery,
    ) -> Value {
        let f = Self::lq_ctor(kb, short);
        let l = Self::reify_logical_query(kb, left);
        let r = Self::reify_logical_query(kb, right);
        let (lk, rk) = (kb.intern("left"), kb.intern("right"));
        lq_entity(f, vec![(lk, l), (rk, r)])
    }

    /// Reify a quantifier variant (`forall_q`/`some_q`/`one_q`/`lone_q`/`no_q`) —
    /// all share the `{var, condition, body}` shape (`no ?x: condition -: body`).
    /// `var` (the binder name) rides as a `Symbol` ref matching the spec field type
    /// (`var: Symbol`); it is INERT to evaluation (`eval_count_guard`/
    /// `eval_forall_guard` read only `condition`/`body`) and carries no trigger
    /// sort. (The loader stores this slot as a `String` literal — an inert
    /// representational divergence; the `Symbol` ref is the spec-faithful form.)
    /// `no_q` is the enforced cardinality-zero guard: a 2-cycle
    /// `no ?x: edge(a,?x) -: edge(?x,a)` rejects the assert that completes the cycle.
    fn reify_quantifier(
        kb: &mut KnowledgeBase,
        short: &str,
        var: &Symbol,
        condition: &LogicalQuery,
        body: &LogicalQuery,
    ) -> Value {
        let f = Self::lq_ctor(kb, short);
        let cond = Self::reify_logical_query(kb, condition);
        let bod = Self::reify_logical_query(kb, body);
        let var_ref = kb.alloc(CoreTerm::Ref(var.symbol()));
        let (vk, ck, bk) = (kb.intern("var"), kb.intern("condition"), kb.intern("body"));
        lq_entity(f, vec![(vk, Value::term(var_ref)), (ck, cond), (bk, bod)])
    }

    /// Resolve an `anthill.reflect.LogicalQuery.<short>` constructor symbol, or
    /// panic loudly — a guard cannot be registered without the reflect stdlib
    /// loaded (the symbols `collect_trigger_sorts`/`evaluate_guard` key on).
    fn lq_ctor(kb: &KnowledgeBase, short: &str) -> anthill_core::intern::Symbol {
        kb.try_resolve_symbol(&format!("anthill.reflect.LogicalQuery.{short}"))
            .unwrap_or_else(|| panic!(
                "KB.add_guard: `anthill.reflect.LogicalQuery.{short}` unavailable — \
                 is anthill.reflect loaded?"))
    }

    /// Reify a `Vec<String>` into a prelude `List` cons/nil `Value` of `Value::Str`
    /// elements (the `projected.vars` field). Panics if the prelude `List` ctors
    /// are unavailable, mirroring [`lq_ctor`](Self::lq_ctor).
    fn reify_string_list(kb: &mut KnowledgeBase, items: &[String]) -> Value {
        let cons = kb.try_resolve_symbol("anthill.prelude.List.cons")
            .unwrap_or_else(|| panic!("KB.add_guard: `anthill.prelude.List.cons` unavailable"));
        let nil = kb.try_resolve_symbol("anthill.prelude.List.nil")
            .unwrap_or_else(|| panic!("KB.add_guard: `anthill.prelude.List.nil` unavailable"));
        let (head, tail) = (kb.intern("head"), kb.intern("tail"));
        let mut acc = lq_entity(nil, vec![]);
        for s in items.iter().rev() {
            acc = lq_entity(cons, vec![(head, Value::Str(s.clone())), (tail, acc)]);
        }
        acc
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

    fn head_option(&self) -> Result<Option<Solution>, Error> {
        match self.split_first()? {
            Some((h, _)) => Ok(Some(h)),
            None => Ok(None),
        }
    }

    fn head(&self) -> Result<Solution, Error> {
        // WI-567 ergonomic form: the element directly. An empty stream is the
        // declared `Error[EmptyStream]` — surfaced here as a loud `Err`.
        match self.split_first()? {
            Some((h, _)) => Ok(h),
            None => Err(Error("Stream::head on an empty solution stream".into())),
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

    fn is_empty(&self) -> Result<bool, Error> {
        let inner = self.inner.borrow();
        match inner.as_ref() {
            Some(s) => Ok(s.is_empty()),
            None => Ok(true),
        }
    }

    fn find(&self, _pred: fn(Solution) -> bool) -> Result<Option<Solution>, Error> {
        // `find` returns the matching element, but its predicate consumes the
        // element by value and the reflect `Solution` is not `Clone` (it carries
        // a `Box<dyn Substitution>`), so a tested element cannot also be returned.
        // The host bridge has no `find` caller; surface a loud `Err` rather than a
        // silently wrong answer if one ever appears.
        Err(Error(
            "Stream::find is unsupported on the reflect Solution stream (Solution is not Clone)".into(),
        ))
    }

    fn iterator(&self) -> Box<dyn Stream<Solution, Error>> {
        // `iterator(s) = s`: hand this stream's remaining state to the iterator.
        Box::new(SearchStreamAdapter {
            inner: RefCell::new(self.inner.borrow_mut().take()),
            kb: Rc::clone(&self.kb),
        })
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
        // The shared inverse walk, via `TermRepr`'s `ReflectReader` classify. It
        // is `Infallible` (closed enum), so the `Err` arm is uninhabited.
        match reader::reflect_walk(&mut self.kb.borrow_mut(), r) {
            Ok(tid) => term(tid),
            Err(never) => match never {},
        }
    }

    fn nonvar(&self, x: Term) -> bool {
        match x.value() {
            Value::Var(_) => false,
            Value::Term { id: t, .. } => !matches!(self.kb.borrow().get_term(*t), CoreTerm::Var(_)),
            _ => true,
        }
    }

    fn ground(&self, x: Term) -> bool {
        // Mirrors the core resolver's `value_is_ground`.
        match x.value() {
            Value::Var(_) => false,
            Value::Term { id: t, .. } => self.kb.borrow().collect_vars(*t).is_empty(),
            Value::Node(occ) =>
                !anthill_core::kb::node_occurrence::occurrence_has_unbound_var(occ),
            _ => true,
        }
    }

    fn sorts(&self, namespace: Option<String>) -> Vec<SortInfo> {
        let records = reader::read_sort_infos(&mut self.kb.borrow_mut(), namespace.as_deref());
        records
            .into_iter()
            .map(|rec| SortInfo {
                name: self.sym_of(rec.name),
                kind: match rec.kind {
                    Some(t) => self.sym_of(t),
                    None => ReflectSymbol::new(self.kb.borrow_mut().intern("sort")),
                },
                definition: term(rec.definition),
                constructors: rec.constructors.into_iter().map(|t| self.sym_of(t)).collect(),
                operations: rec.operations.into_iter().map(|t| self.sym_of(t)).collect(),
                parameters: rec.parameters.into_iter().map(|t| self.sym_of(t)).collect(),
                requires: rec.requires.into_iter().map(term).collect(),
            })
            .collect()
    }

    fn operations(&self, sort_name: String) -> Vec<OperationInfo> {
        let records = reader::read_operations(&mut self.kb.borrow_mut(), &sort_name);
        // The shared reader yields `effects` / `requires` / `ensures` as carrier-
        // faithful `Value`s. A `denoted` label / clause rides as a `Value::Node`,
        // wrapped via `rterm` / `ReflectNodeOccurrence::new` — the struct fields
        // are `Term` / `NodeOccurrence` carriers (newtypes over `Value`), so the
        // bridge holds it verbatim rather than skipping the op (the old
        // `facts_by_sort_name` Term-only drop is gone). `requires` includes the
        // loader's auto-inferred `EffectsRuntime[Effects=E]` clause (WI-320);
        // `ensures` is user clauses only.
        records
            .into_iter()
            .map(|rec| OperationInfo {
                name: self.sym_of(rec.name),
                params: rec.params.into_iter().map(|fi_tid| self.field_info_of(fi_tid)).collect(),
                return_type: term(rec.return_type),
                effects: rec.effects.into_iter().map(rterm).collect(),
                requires: rec.requires.into_iter().map(ReflectNodeOccurrence::new).collect(),
                ensures: rec.ensures.into_iter().map(ReflectNodeOccurrence::new).collect(),
                meta: term(rec.meta),
            })
            .collect()
    }

    fn constructors(&self, sort_name: String) -> Vec<String> {
        // `let`-bind first to release the `borrow_mut()` RefMut before mapping (see
        // `fields`); the map here doesn't re-borrow, but keep the pattern uniform.
        let members = reader::members_of_kind(&mut self.kb.borrow_mut(), &sort_name, "Constructor");
        members.into_iter().map(|n| reader::short_of(&n).to_string()).collect()
    }

    fn fields(&self, entity: Type) -> Vec<FieldInfo> {
        // WI-632: the entity is passed BY REFERENCE (`fields(kb(), WorkItem)`); the
        // `Type` carrier wraps that referencing `Value`. Extract its functor via
        // the shared `value_functor` (the `facts_of` precedent) — no name-string
        // resolution, so no short-name ambiguity. A non-entity reference names no
        // schema — a caller type error, panicked loudly (this Vec-returning surface
        // has no error channel; mirrors `facts_of`). The declared `(field_sym,
        // field_type)` pairs ride carrier-agnostically: a value-in-type field type
        // is a `Value::Node`, surfaced verbatim via `rterm` rather than dropped.
        let functor = anthill_core::eval::value_functor(&self.kb.borrow(), entity.value())
            .unwrap_or_else(|| panic!(
                "KB.fields: `entity` is not an entity reference (expected a \
                 Ref / Fn / Entity carrier that names a functor)"
            ));
        let kb = self.kb.borrow();
        match kb.entity_field_types(functor) {
            Some(fields) => fields
                .iter()
                .map(|(field_sym, field_type)| FieldInfo {
                    name: ReflectSymbol::new(*field_sym),
                    type_name: rterm(field_type.clone()),
                })
                .collect(),
            None => vec![],
        }
    }

    fn rules(&self, sort_name: String) -> Vec<TermRepr> {
        let heads = reader::rule_heads_for_sort(&mut self.kb.borrow_mut(), &sort_name);
        heads.iter().map(|head| self.reify_view(head)).collect()
    }

    fn descriptions(&self, target: Option<String>) -> Vec<DescriptionInfo> {
        // `let`-bind first: `self.sym_of(..)` in the map re-borrows the KB, so the
        // `borrow_mut()` RefMut must be dropped before mapping (see `fields`).
        let records = reader::read_descriptions(&mut self.kb.borrow_mut(), target.as_deref());
        records
            .into_iter()
            .map(|rec| DescriptionInfo {
                target: self.sym_of(rec.target),
                content: rec.content,
                index: rec.index,
            })
            .collect()
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
        // `Type` carrier wraps that referencing `Value`. Extract its functor via
        // the shared `value_functor` (core's single source — same reader the
        // interpreter `kb_facts_of` uses), then enumerate every asserted fact with
        // that head functor. Carrier-agnostic: `rule_head_value` returns the head
        // `Value` directly, so a value-fact head (e.g. an `OperationInfo` carrying
        // a `denoted` effect, WI-348) rides through rather than being dropped.
        // A non-entity `sort` (a literal, a var, a Fn-with-args) names no fact
        // set — a caller type error, not "zero facts". Surface it loudly
        // (mirroring the interpreter `kb_facts_of`, which raises a type
        // mismatch, and the bridge's own `reify_view` panic discipline) rather
        // than returning an empty list a caller would misread as "none
        // asserted". The trait fixes the return as `Vec<Term>`, so a panic is
        // the only loud channel.
        let functor = anthill_core::eval::value_functor(&self.kb.borrow(), sort.value()).unwrap_or_else(|| {
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

    fn sort_template(&self, sort: Type) -> LogicalQuery {
        // WI-632: the sort arrives by reference (a `Type` carrying a `Ref`),
        // stored verbatim as the `sort_query.sort` payload — resolution already
        // happened at the caller's write site.
        LogicalQuery::SortQuery { sort: rterm(sort.value().clone()) }
    }

    fn instantiation_query(
        &self,
        sort: Type,
        _bindings: &dyn Substitution,
    ) -> LogicalQuery {
        LogicalQuery::SortQuery { sort: rterm(sort.value().clone()) }
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
        let arg_sort_sym = anthill_core::eval::value_functor(&self.kb.borrow(), sort.value());
        let mut kb = self.kb.borrow_mut();
        let sort_tid = kb.fact_trigger_sort(&head).unwrap_or_else(|| {
            let sym = arg_sort_sym.unwrap_or_else(|| {
                panic!("KB.assert: cannot determine the fact's sort from its head or the `sort` arg")
            });
            kb.make_name_term_from_sym(sym)
        });
        kb.assert_checked(term_tid, sort_tid, sort_tid, None)
    }

    fn add_guard(&mut self, guard: LogicalQuery) -> ConstraintId {
        // WI-549: reify the generated `LogicalQuery` enum into a structured KB
        // guard Value (built from the `anthill.reflect.LogicalQuery.*` ctors) and
        // register it — DISTINCT from `query_to_goals`, which flattens to resolver
        // goals. `add_guard_labeled` extracts the trigger sorts (via
        // `collect_trigger_sorts`) so the guard fires on the right facts. The
        // enforceable forms are the quantifiers (`forall_q`/`some_q`/`one_q`/
        // `lone_q`/`no_q`) and `negation`; a bare pattern_query/conjunction is
        // registered but vacuously holds (WI-023/WI-513). Aggregation variants are
        // rejected loudly by `reify_logical_query` (not boolean constraints).
        // `ConstraintId` is a generated unit struct, so the core id is discarded.
        let mut kb = self.kb.borrow_mut();
        let value = Self::reify_logical_query(&mut kb, &guard);
        kb.add_guard_labeled(value, None);
        ConstraintId
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
            Value::Term { id: tid, .. } => match self.kb.borrow().get_term(*tid) {
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
        // WI-502 Step 2 — `self`'s constraint store is carried by `.clone()`.
        // `s2`'s constraints are NOT carried here: `s2: &dyn Substitution` only
        // exposes `bindings()` across the trait boundary, with no `constraints()`
        // method. This is a documented limitation, not a silent core drop — the
        // concrete-Substitution `subst_compose` (interp/builtins.rs) carries
        // both. Reachable only once a self-hosted resolver mints constraints
        // (post Step 3); extend the `Substitution` trait with `constraints()` then.
        let mut result = self.inner.clone();
        // WI-569: `bindings` is an `imbl::HashMap` (no `iter_mut`). Map each
        // binding value through `s2` into owned pairs, then re-insert — same
        // keys, new values, so this matches the prior in-place rewrite.
        let updated: Vec<_> = result
            .bindings
            .iter()
            .map(|(var, val)| (*var, s2.apply(rterm(val.clone()), kb).into_value()))
            .collect();
        for (var, val) in updated {
            result.bindings.insert(var, val);
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

    /// Drain a `Box<dyn Stream<Solution, Error>>` to a `Vec` by pulling
    /// `split_first` to exhaustion. The host `Stream` trait no longer carries an
    /// eager `collect` (proposal library/003, Phase C / WI-589 moved the eager
    /// drains to `FiniteCollection`), so a bounded test drain is spelled out here.
    fn drain(stream: Box<dyn Stream<Solution, Error>>) -> Vec<Solution> {
        let mut out = Vec::new();
        let mut next = stream.split_first().expect("split_first failed");
        while let Some((h, rest)) = next {
            out.push(h);
            next = rest.split_first().expect("split_first failed");
        }
        out
    }

    /// A `sort_query` payload: the sort BY REFERENCE (a `Term` naming `qname`),
    /// the way the loader lowers a written sort reference (WI-632). A qualified
    /// `qname` resolves to the real symbol; an unknown one interns fresh.
    fn sort_ref(bridge: &KbBridge, qname: &str) -> ReflectTerm {
        let mut kb = bridge.kb.borrow_mut();
        ReflectTerm::new(Value::term(kb.resolve_qualified_name_term(qname)))
    }

    /// The `Type` carrier for an entity/sort passed BY REFERENCE (WI-632), the
    /// way the loader lowers a written `fields(kb(), Foo)` argument.
    fn type_ref(bridge: &KbBridge, qname: &str) -> Type {
        let mut kb = bridge.kb.borrow_mut();
        Type::new(Value::term(kb.resolve_qualified_name_term(qname)))
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
        let query = LogicalQuery::SortQuery { sort: sort_ref(&bridge, "anthill.reflect.OperationInfo") };
        let stream = bridge.execute(query).expect("execute failed");
        let results = drain(stream);
        assert!(results.len() >= 3,
            "should find at least 3 OperationInfo facts, got {}", results.len());
        // Each result is a definite Solution.
        assert!(results.iter().all(|s| matches!(s, Solution::Definite { .. })),
            "sort-query solutions should be definite");
    }

    #[test]
    fn execute_sort_query_nonexistent_is_empty() {
        let bridge = load_source_bridge("sort Foo { entity bar }");
        let query = LogicalQuery::SortQuery { sort: sort_ref(&bridge, "Nonexistent") };
        let stream = bridge.execute(query).expect("execute failed");
        let results = drain(stream);
        assert_eq!(results.len(), 0, "nonexistent sort query should return 0 results");
    }

    #[test]
    fn execute_empty_query() {
        let bridge = load_source_bridge("sort Foo { entity bar }");
        let query = LogicalQuery::EmptyQuery;
        let stream = bridge.execute(query).expect("execute failed");
        let results = drain(stream);
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
        let query = LogicalQuery::PatternQuery { term: ReflectTerm::new(Value::term(goal)) };
        let stream = bridge.execute(query).expect("execute failed");
        let results = drain(stream);
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
            query: Box::new(LogicalQuery::SortQuery { sort: sort_ref(&bridge, "anthill.reflect.OperationInfo") }),
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
                ReflectTerm::new(Value::term(kb.alloc(CoreTerm::Var(Var::Global(vid))))),
                ReflectTerm::new(Value::term(kb.alloc(CoreTerm::Var(Var::Rigid(vid))))),
                ReflectTerm::new(Value::term(kb.alloc(CoreTerm::Var(Var::DeBruijn(0))))),
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
        // result is exactly the user DATA facts — WI-515 removed the synthetic
        // entity-declaration fact that used to ride along as an extra row.
        let bridge = load_source_bridge(r#"
sort Color {
  entity red(shade: Int64)
  entity blue(shade: Int64)
}
fact red(shade: 1)
fact red(shade: 2)
fact blue(shade: 3)
"#);
        // Every returned head carries a GROUND `shade` literal (a data row).
        let ground_count = |facts: &[Term]| -> usize {
            facts.iter().filter(|t| match bridge.reify((*t).clone()) {
                TermRepr::FnRepr { args, .. } =>
                    args.iter().any(|a| matches!(a, TermRepr::ConstRepr { .. })),
                _ => false,
            }).count()
        };

        let red_ref = {
            let mut kb = bridge.kb.borrow_mut();
            Value::term(kb.resolve_qualified_name_term("Color.red"))
        };
        let reds = bridge.facts_of(Type::new(red_ref));
        assert_eq!(reds.len(), 2, "the 2 user facts and nothing else, got {}", reds.len());
        assert_eq!(ground_count(&reds), 2, "two ground `red` user facts");

        let blue_ref = {
            let mut kb = bridge.kb.borrow_mut();
            Value::term(kb.resolve_qualified_name_term("Color.blue"))
        };
        let blues = bridge.facts_of(Type::new(blue_ref));
        assert_eq!(blues.len(), 1, "the 1 user fact and nothing else");
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
            Value::term(kb.alloc(CoreTerm::Const(Literal::Int(7))))
        };
        let _ = bridge.facts_of(Type::new(lit));
    }

    #[test]
    fn fields_by_reference_disambiguates() {
        // WI-632: a short name WI-631 had to reject as ambiguous is now a
        // non-issue — `fields` takes the entity BY REFERENCE, so `Beta.dup` and
        // `Alpha.dup` are two distinct references, each answering its own schema.
        let bridge = load_source_bridge(r#"
namespace test.wi632_bridge
  sort Alpha { entity dup(x: Int64) }
  sort Beta { entity dup(y: String) }
end
"#);
        let beta = bridge.fields(type_ref(&bridge, "test.wi632_bridge.Beta.dup"));
        assert_eq!(beta.len(), 1, "Beta.dup has one field");
        let alpha = bridge.fields(type_ref(&bridge, "test.wi632_bridge.Alpha.dup"));
        assert_eq!(alpha.len(), 1, "Alpha.dup has one field");
        let kb = bridge.kb.borrow();
        assert_eq!(kb.resolve_sym(beta[0].name.symbol()), "y");
        assert_eq!(kb.resolve_sym(alpha[0].name.symbol()), "x");
    }

    #[test]
    #[should_panic(expected = "not an entity reference")]
    fn fields_non_entity_reference_panics() {
        // WI-632: a `Type` carrying a non-entity Value (a literal) names no
        // functor — a caller type error, surfaced loudly (mirrors `facts_of`).
        let bridge = load_source_bridge("sort Foo { entity bar }");
        let lit = {
            let mut kb = bridge.kb.borrow_mut();
            Value::term(kb.alloc(CoreTerm::Const(Literal::Int(7))))
        };
        let _ = bridge.fields(Type::new(lit));
    }

    #[test]
    fn sort_query_by_reference_disambiguates() {
        // WI-632: a short name that WI-631 had to reject as ambiguous is now a
        // non-issue — `sort_query` carries the sort BY REFERENCE, resolved at the
        // write site, so `Beta.dup` and `Alpha.dup` are simply two distinct
        // references. Each lowers to its own sort's goal with no runtime scan.
        let bridge = load_source_bridge(r#"
namespace test.wi632_bridge
  sort Alpha { entity dup(x: Int64) }
  sort Beta { entity dup(y: String) }
end
fact test.wi632_bridge.Beta.dup(y: "hi")
"#);
        let query = LogicalQuery::SortQuery {
            sort: sort_ref(&bridge, "test.wi632_bridge.Beta.dup"),
        };
        let stream = bridge.execute(query).expect("a resolved reference never errors");
        let results = drain(stream);
        assert_eq!(results.len(), 1, "one Beta.dup fact, unambiguously");
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
            ReflectTerm::new(Value::term(kb.alloc(CoreTerm::Const(Literal::BigInt(big.clone())))))
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
        s1_inner.bindings.insert(vid_x, Value::term(var_y));
        let mut s2_inner = anthill_core::kb::subst::Substitution::new();
        s2_inner.bindings.insert(vid_y, Value::term(five));

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
        s2_inner.bindings.insert(vid_w, Value::term(seven));

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
            Value::Term { .. } => {}
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
            (s5, Type::new(Value::term(sort_ref)), Type::new(Value::term(entity_ref)))
        };
        let id = bridge.assert(ReflectTerm::new(Value::term(slot5)), slot_sort_type);
        assert!(id.is_some(), "asserting slot(n:5) should succeed");
        assert!(
            bridge.facts_of(slot_entity_type).iter()
                .any(|t| matches!(t.value(), Value::Term { id: tid, .. } if *tid == slot5)),
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
            (edge, Type::new(Value::term(rel_ref)))
        };
        let rejected = bridge.assert(ReflectTerm::new(Value::term(edge_ba)), rel_type);
        assert!(rejected.is_none(),
            "asserting edge(b→a) completes a 2-cycle → rejected by `no_two_cycle`");
    }

    /// A domain with `edge(a→b)` loaded, for the WI-549 `add_guard` tests. Returns
    /// the bridge plus `edge(b→a)` and the `Rel` sort `Type` (the assert args).
    fn guard_fixture() -> (KbBridge, TermId, Type) {
        let bridge = load_source_bridge_with_stdlib(r#"
namespace test.add_guard
  sort Node
    entity a
    entity b
  end
  sort Rel
    entity edge(from: Node, to: Node)
  end
  fact edge(from: a, to: b)
end
"#);
        let (edge_ba, rel_type) = {
            let mut kb = bridge.kb.borrow_mut();
            let edge_sym = kb.try_resolve_symbol("test.add_guard.Rel.edge").expect("edge");
            let rel_sym = kb.try_resolve_symbol("test.add_guard.Rel").expect("Rel");
            let a_sym = kb.try_resolve_symbol("test.add_guard.Node.a").expect("a");
            let b_sym = kb.try_resolve_symbol("test.add_guard.Node.b").expect("b");
            let a_ref = kb.alloc(CoreTerm::Ref(a_sym));
            let b_ref = kb.alloc(CoreTerm::Ref(b_sym));
            let (from, to) = (kb.intern("from"), kb.intern("to"));
            let edge_ba = kb.alloc(CoreTerm::Fn {
                functor: edge_sym, pos_args: Default::default(),
                named_args: vec![(from, b_ref), (to, a_ref)].into(),
            });
            let rel_ref = kb.alloc(CoreTerm::Ref(rel_sym));
            (edge_ba, Type::new(Value::term(rel_ref)))
        };
        (bridge, edge_ba, rel_type)
    }

    #[test]
    fn add_guard_negation_rejects_violating_assert() {
        // WI-549: a guard registered PROGRAMMATICALLY via the bridge's `add_guard`
        // (reifying a `LogicalQuery` enum, NOT from a source constraint) is enforced
        // like a loaded constraint. `negation(pattern_query(edge(b→a)))` = "there is
        // no edge b→a"; it triggers on the `Rel` sort. With only edge(a→b) present
        // it holds; asserting edge(b→a) gives the inner pattern a solution, so the
        // negation fails → the assert is rejected (None) and retracted.
        let (mut bridge, edge_ba, rel_type) = guard_fixture();

        let guard = LogicalQuery::Negation {
            query: Box::new(LogicalQuery::PatternQuery {
                term: ReflectTerm::new(Value::term(edge_ba)),
            }),
        };
        bridge.add_guard(guard);

        let rejected = bridge.assert(ReflectTerm::new(Value::term(edge_ba)), rel_type);
        assert!(rejected.is_none(),
            "asserting edge(b→a) violates the programmatic `not(edge(b→a))` guard → rejected");
    }

    #[test]
    fn add_guard_no_q_rejects_two_cycle() {
        // WI-549: the quantifier reify path — a `no_q` cardinality guard built via
        // the bridge mirrors the source `no_two_cycle`: `no ?x: edge(a,?x) -:
        // edge(?x,a)`. The two pattern terms SHARE the logical var `?x` (one VarId).
        // With edge(a→b) loaded the count is 0 (no edge(b→a) yet); asserting edge(b→a)
        // makes ?x=b satisfy both patterns → count 1 ≠ 0 → guard violated → rejected.
        let (mut bridge, edge_ba, rel_type) = guard_fixture();

        let (cond_pat, body_pat, x_name) = {
            let mut kb = bridge.kb.borrow_mut();
            let edge_sym = kb.try_resolve_symbol("test.add_guard.Rel.edge").expect("edge");
            let a_sym = kb.try_resolve_symbol("test.add_guard.Node.a").expect("a");
            let a_ref = kb.alloc(CoreTerm::Ref(a_sym));
            let (from, to) = (kb.intern("from"), kb.intern("to"));
            // One shared var `?x` across both patterns — same VarId.
            let x_name = kb.intern("x");
            let x_vid = kb.fresh_var(x_name);
            let x_term = kb.alloc(CoreTerm::Var(Var::Global(x_vid)));
            // condition: edge(from: a, to: ?x)
            let cond = kb.alloc(CoreTerm::Fn {
                functor: edge_sym, pos_args: Default::default(),
                named_args: vec![(from, a_ref), (to, x_term)].into(),
            });
            // body: edge(from: ?x, to: a)
            let body = kb.alloc(CoreTerm::Fn {
                functor: edge_sym, pos_args: Default::default(),
                named_args: vec![(from, x_term), (to, a_ref)].into(),
            });
            (cond, body, x_name)
        };

        let guard = LogicalQuery::NoQ {
            var: ReflectSymbol::new(x_name),
            condition: Box::new(LogicalQuery::PatternQuery {
                term: ReflectTerm::new(Value::term(cond_pat)),
            }),
            body: Box::new(LogicalQuery::PatternQuery {
                term: ReflectTerm::new(Value::term(body_pat)),
            }),
        };
        bridge.add_guard(guard);

        let rejected = bridge.assert(ReflectTerm::new(Value::term(edge_ba)), rel_type);
        assert!(rejected.is_none(),
            "asserting edge(b→a) completes the 2-cycle → rejected by the programmatic `no_q` guard");
    }

    #[test]
    #[should_panic(expected = "reduces to a value, not a boolean")]
    fn add_guard_rejects_aggregation_early() {
        // WI-549: an aggregation LogicalQuery (count_q/sum_q/min_q/max_q) is not a
        // boolean constraint — the guard engine can't lower it, so registering one
        // would defer to a misleading panic at the next matching assert. `add_guard`
        // must reject it LOUDLY and EARLY (at registration), not silently accept it.
        let (mut bridge, _edge_ba, _rel_type) = guard_fixture();
        let x_name = bridge.kb.borrow_mut().intern("x");
        let guard = LogicalQuery::CountQ {
            var: ReflectSymbol::new(x_name),
            condition: Box::new(LogicalQuery::EmptyQuery),
            body: Box::new(LogicalQuery::EmptyQuery),
        };
        bridge.add_guard(guard); // panics in reify_logical_query before registration
    }

    #[test]
    fn introspection_record_ops_map_via_shared_reader() {
        // WI-551: exercise the bridge `sorts`/`fields`/`constructors`/
        // `descriptions`/`rules` entry points DIRECTLY. Before the consolidation
        // only `operations`/`facts_of`/`execute` had bridge tests; these five mapped
        // their own walks untested (verified only via the analogous interpreter
        // builtins). Now they map the shared `reader` records — this pins both the
        // result correctness AND the borrow-safety of the `.map` closures (e.g.
        // `sorts`' `kind: None => self.kb.borrow_mut().intern("sort")` running while
        // the per-field `self.sym_of(..)` borrows the same RefCell).
        let bridge = load_source_bridge(r#"
namespace test.wi551_bridge
  sort Color
    entity red(shade: Int64)
    entity blue(shade: Int64)
  end
  describe Color {< a color sort >}
end
"#);
        let short = |sym: &ReflectSymbol| {
            let kb = bridge.kb.borrow();
            let n = kb.resolve_sym(sym.symbol()).to_string();
            n.rsplit('.').next().unwrap_or(&n).to_string()
        };

        let ctors = bridge.constructors("Color".into());
        assert!(
            ctors.iter().any(|c| c == "red") && ctors.iter().any(|c| c == "blue"),
            "constructors should list red+blue, got {ctors:?}",
        );

        let fields = bridge.fields(type_ref(&bridge, "test.wi551_bridge.Color.red"));
        assert!(
            fields.iter().any(|f| short(&f.name) == "shade"),
            "red should surface a `shade` field, got {:?}",
            fields.iter().map(|f| short(&f.name)).collect::<Vec<_>>(),
        );

        let sorts = bridge.sorts(None);
        assert!(
            sorts.iter().any(|s| short(&s.name) == "Color"),
            "sorts(None) should include Color",
        );
        // The namespace filter is honored — a non-matching prefix yields nothing
        // for our sort.
        assert!(
            !bridge.sorts(Some("no.such.namespace".into()))
                .iter()
                .any(|s| short(&s.name) == "Color"),
            "a non-matching namespace filter should exclude Color",
        );

        let descs = bridge.descriptions(None);
        assert!(
            descs.iter().any(|d| d.content.contains("a color sort")),
            "descriptions(None) should include Color's text, got {:?}",
            descs.iter().map(|d| &d.content).collect::<Vec<_>>(),
        );

        // `rules` reifies each Rule head via `reify_view` (`let heads` + map, so its
        // borrow path is the same safe shape as the others); smoke-call it to
        // exercise that path. Head reification itself is covered by the reify tests.
        let _ = bridge.rules("Color".into());
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

    /// Drift-guard (WI-553): the `Stream` trait is GENERATED from
    /// `prelude/stream.anthill` (single source of truth) and `include!`d via
    /// `prelude::stream`. This statically asserts (a) the host
    /// `SearchStreamAdapter` implements that generated trait, and (b) the trait
    /// is object-safe — `KB.execute` returns `Box<dyn Stream<Solution, Error>>`,
    /// so a codegen change that breaks dyn-compatibility, or a spec edit that
    /// changes the interface, is a compile error here.
    #[test]
    fn adapter_implements_generated_stream_interface() {
        fn assert_stream<T: Stream<Solution, Error>>() {}
        assert_stream::<SearchStreamAdapter>();
        // Fails to compile if `Stream` is not object-safe.
        let _obj_safe: Option<Box<dyn Stream<Solution, Error>>> = None;
    }
}

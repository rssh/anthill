/// Tree-sitter CST → Parse IR conversion.
///
/// One function per grammar node kind. Uses child iteration to walk
/// the CST and build typed IR nodes.

use std::collections::HashMap;

use ordered_float::OrderedFloat;
use smallvec::SmallVec;
use tree_sitter::Node;

use crate::intern::{Interner, Symbol};
use crate::span::Span;
use crate::kb::term::{Term, TermId, FnArg, Literal, VarId};

/// Join name segments into a single dot-separated string for interning.
fn join_name_segments(interner: &crate::intern::Interner, segments: &[Symbol]) -> String {
    let mut out = String::new();
    for (i, &sym) in segments.iter().enumerate() {
        if i > 0 {
            out.push('.');
        }
        out.push_str(interner.resolve(sym));
    }
    out
}

use super::error::ParseError;
use super::ir::*;

pub(super) struct Converter<'a> {
    source: &'a str,
    pub interner: Interner,
    pub terms: SimpleTermStore,
    pub items: Vec<Item>,
    pub errors: Vec<ParseError>,
    /// Counter for fresh VarId allocation.
    next_var: u32,
    /// Current variable scope: maps variable name Symbol → VarId.
    /// Reset at each rule/constraint/operation boundary so that
    /// `?x` in different rules gets distinct VarIds.
    var_scope: HashMap<Symbol, VarId>,
}

impl<'a> Converter<'a> {
    pub fn new(source: &'a str) -> Self {
        Self {
            source,
            interner: Interner::new(),
            terms: SimpleTermStore::new(),
            items: Vec::new(),
            errors: Vec::new(),
            next_var: 0,
            var_scope: HashMap::new(),
        }
    }

    // ── Helpers ─────────────────────────────────────────────────

    fn text(&self, node: Node) -> &'a str {
        &self.source[node.start_byte()..node.end_byte()]
    }

    fn span(&self, node: Node) -> Span {
        Span::from_ts_node(&node)
    }

    fn intern(&mut self, s: &str) -> Symbol {
        self.interner.intern(s)
    }

    fn err(&mut self, msg: impl Into<String>, node: Node) {
        self.errors.push(ParseError::new(msg, self.span(node)));
    }

    /// Allocate a fresh VarId or reuse one from the current scope.
    fn get_or_create_var(&mut self, name: Symbol) -> VarId {
        if let Some(&vid) = self.var_scope.get(&name) {
            return vid;
        }
        let vid = VarId::new(self.next_var, name);
        self.next_var += 1;
        self.var_scope.insert(name, vid);
        vid
    }

    /// Clear the variable scope (call at rule/constraint/operation boundaries).
    fn reset_var_scope(&mut self) {
        self.var_scope.clear();
    }

    /// Intern a Name's segments as a single dot-joined symbol.
    fn intern_name(&mut self, name: &Name) -> Symbol {
        if name.segments.len() == 1 {
            // Already a single segment — just re-use it
            name.segments[0]
        } else {
            let joined = join_name_segments(&self.interner, &name.segments);
            self.intern(&joined)
        }
    }

    /// Find the first named child of a given kind.
    fn child_by_kind<'t>(&self, node: Node<'t>, kind: &str) -> Option<Node<'t>> {
        let mut cursor = node.walk();
        let result = node.named_children(&mut cursor)
            .find(|c| c.kind() == kind);
        result
    }

    /// Find the first child with a given field name.
    fn field<'t>(&self, node: Node<'t>, name: &str) -> Option<Node<'t>> {
        node.child_by_field_name(name)
    }

    /// All named children of a given kind.
    fn children_by_kind<'t>(&self, node: Node<'t>, kind: &str) -> Vec<Node<'t>> {
        let mut cursor = node.walk();
        node.named_children(&mut cursor)
            .filter(|c| c.kind() == kind)
            .collect()
    }

    // ── Root ────────────────────────────────────────────────────

    pub fn convert_file(&mut self, root: Node) {
        let mut cursor = root.walk();
        for child in root.named_children(&mut cursor) {
            if let Some(item) = self.convert_item(child) {
                self.items.push(item);
            }
        }
    }

    fn convert_item(&mut self, node: Node) -> Option<Item> {
        match node.kind() {
            "domain_declaration" => self.convert_domain(node).map(Item::Domain),
            "abstract_sort" => self.convert_abstract_sort(node).map(Item::AbstractSort),
            "sort_with_body" => self.convert_sort_with_body(node).map(Item::SortWithBody),
            "rule_declaration" => self.convert_rule(node).map(Item::Rule),
            "operation_declaration" => self.convert_operation(node).map(Item::Operation),
            "entity_declaration" => self.convert_entity(node).map(Item::Entity),
            "fact_declaration" => self.convert_fact(node).map(Item::Fact),
            "constraint_declaration" => self.convert_constraint(node).map(Item::Constraint),
            "operation_block" => self.convert_operation_block(node).map(Item::OperationBlock),
            "rule_block" => self.convert_rule_block(node).map(Item::RuleBlock),
            "project_declaration" => self.convert_project(node).map(Item::Project),
            "tool_declaration" => self.convert_tool(node).map(Item::Tool),
            "workitem_declaration" => self.convert_workitem(node).map(Item::WorkItem),
            "feedback_declaration" => self.convert_feedback(node).map(Item::Feedback),
            "import_tools_declaration" => self.convert_import_tools(node).map(Item::ImportTools),
            "line_comment" | "block_comment" => None,
            other => {
                self.err(format!("unexpected top-level node: {other}"), node);
                None
            }
        }
    }

    // ── Name ────────────────────────────────────────────────────

    fn convert_name(&mut self, node: Node) -> Name {
        let span = self.span(node);
        let mut segments = SmallVec::new();
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            if child.kind() == "identifier" {
                let sym = self.intern(self.text(child));
                segments.push(sym);
            }
        }
        if segments.is_empty() {
            // fallback: treat entire node text as one segment
            let sym = self.intern(self.text(node));
            segments.push(sym);
        }
        Name { segments, span }
    }

    // ── Type expressions ────────────────────────────────────────

    fn convert_type(&mut self, node: Node) -> TypeExpr {
        match node.kind() {
            "simple_type" => {
                let name_node = self.child_by_kind(node, "name")
                    .unwrap_or(node);
                TypeExpr::Simple(self.convert_name(name_node))
            }
            "parameterized_type" => {
                let name_node = self.child_by_kind(node, "name").unwrap_or(node);
                let name = self.convert_name(name_node);
                let bindings = self.children_by_kind(node, "sort_binding")
                    .into_iter()
                    .map(|b| self.convert_sort_binding(b))
                    .collect();
                TypeExpr::Parameterized { name, bindings }
            }
            _ => {
                self.err(format!("unexpected type node: {}", node.kind()), node);
                let sym = self.intern("?");
                TypeExpr::Simple(Name::simple(sym, self.span(node)))
            }
        }
    }

    fn convert_sort_binding(&mut self, node: Node) -> SortBinding {
        let param = self.field(node, "param")
            .map(|n| self.convert_name(n))
            .unwrap_or_else(|| {
                let sym = self.intern("?");
                Name::simple(sym, self.span(node))
            });
        let bound = self.field(node, "type")
            .map(|n| self.convert_type(n))
            .unwrap_or_else(|| {
                let sym = self.intern("?");
                TypeExpr::Simple(Name::simple(sym, self.span(node)))
            });
        SortBinding { param, bound }
    }

    // ── Terms ───────────────────────────────────────────────────

    fn convert_term(&mut self, node: Node) -> TermId {
        match node.kind() {
            "string_literal" => {
                let raw = self.text(node);
                // Strip quotes
                let s = &raw[1..raw.len() - 1];
                let term = Term::Const(Literal::String(s.to_string()));
                self.terms.alloc(term)
            }
            "integer_literal" => {
                let text = self.text(node);
                match text.parse::<i64>() {
                    Ok(n) => self.terms.alloc(Term::Const(Literal::Int(n))),
                    Err(_) => {
                        self.err(format!("invalid integer: {text}"), node);
                        self.terms.alloc(Term::Const(Literal::Int(0)))
                    }
                }
            }
            "float_literal" => {
                let text = self.text(node);
                match text.parse::<f64>() {
                    Ok(f) => self.terms.alloc(Term::Const(Literal::Float(OrderedFloat(f)))),
                    Err(_) => {
                        self.err(format!("invalid float: {text}"), node);
                        self.terms.alloc(Term::Const(Literal::Float(OrderedFloat(0.0))))
                    }
                }
            }
            "boolean_literal" => {
                let b = self.text(node) == "true";
                self.terms.alloc(Term::Const(Literal::Bool(b)))
            }
            "variable" => {
                // ?x — child is identifier
                let ident = self.child_by_kind(node, "identifier");
                let name = ident.map(|n| self.text(n)).unwrap_or("_");
                let sym = self.intern(name);
                let vid = self.get_or_create_var(sym);
                self.terms.alloc(Term::Var(vid))
            }
            "fn_term" => self.convert_fn_term(node),
            "ref_term" => {
                let name_node = self.child_by_kind(node, "name");
                let sym = if let Some(n) = name_node {
                    let name = self.convert_name(n);
                    self.intern_name(&name)
                } else {
                    self.intern("?")
                };
                self.terms.alloc(Term::Ref(sym))
            }
            "unspecified_term" => self.convert_unspecified(node),
            "infix_term" => self.convert_infix(node),
            "identifier" => {
                let sym = self.intern(self.text(node));
                self.terms.alloc(Term::Ident(sym))
            }
            other => {
                self.err(format!("unexpected term node: {other}"), node);
                self.terms.alloc(Term::Bottom)
            }
        }
    }

    fn convert_fn_term(&mut self, node: Node) -> TermId {
        let name_node = self.field(node, "name").unwrap_or(node);
        let name = self.convert_name(name_node);
        let functor = self.intern_name(&name);

        let mut args = SmallVec::new();
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            match child.kind() {
                "named_arg" => {
                    let key_node = self.field(child, "name");
                    let val_node = self.field(child, "value");
                    if let (Some(k), Some(v)) = (key_node, val_node) {
                        let sym = self.intern(self.text(k));
                        let tid = self.convert_term(v);
                        args.push(FnArg::Named(sym, tid));
                    }
                }
                "name" => { /* already handled */ }
                _ if is_term_kind(child.kind()) => {
                    let tid = self.convert_term(child);
                    args.push(FnArg::Positional(tid));
                }
                _ => {}
            }
        }

        self.terms.alloc(Term::Fn { functor, args })
    }

    fn convert_unspecified(&mut self, node: Node) -> TermId {
        // Extract the text between <" and "> or <" and ",
        let raw = self.text(node);
        let text = if let Some(start) = raw.find("<\"") {
            let after = &raw[start + 2..];
            if let Some(end) = after.find('"') {
                after[..end].to_string()
            } else {
                String::new()
            }
        } else {
            String::new()
        };

        let mut hints = SmallVec::new();
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            if is_term_kind(child.kind()) {
                hints.push(self.convert_term(child));
            }
        }

        self.terms.alloc(Term::Unspecified { text, hints })
    }

    /// Desugar infix syntax to a `Fn` term: `a + b` → `add(a, b)`.
    fn convert_infix(&mut self, node: Node) -> TermId {
        let mut named_children = Vec::new();
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            named_children.push(child);
        }

        if named_children.len() < 2 {
            self.err("infix term needs at least two operands", node);
            return self.terms.alloc(Term::Bottom);
        }

        let lhs = self.convert_term(named_children[0]);
        let rhs = self.convert_term(named_children[1]);
        let functor_name = self.find_infix_functor(node);
        let functor = self.intern(functor_name);

        self.terms.alloc(Term::Fn {
            functor,
            args: SmallVec::from_slice(&[FnArg::Positional(lhs), FnArg::Positional(rhs)]),
        })
    }

    /// Map an infix operator token to its functor name.
    fn find_infix_functor(&self, node: Node) -> &'static str {
        for i in 0..node.child_count() {
            if let Some(child) = node.child(i) {
                if !child.is_named() {
                    match self.text(child) {
                        "=" => return "eq",
                        ">" => return "gt",
                        ">=" => return "gte",
                        "<" => return "lt",
                        "<=" => return "lte",
                        "+" => return "add",
                        "-" => return "sub",
                        "*" => return "mul",
                        _ => {}
                    }
                }
            }
        }
        "eq" // fallback
    }

    // ── Visibility ──────────────────────────────────────────────

    fn convert_visibility(&mut self, node: Node) -> Option<Visibility> {
        self.child_by_kind(node, "visibility").map(|v| {
            match self.text(v) {
                "internal" => Visibility::Internal,
                "export" => Visibility::Export,
                "public" => Visibility::Public,
                other => {
                    self.err(format!("unknown visibility: {other}"), v);
                    Visibility::Internal
                }
            }
        })
    }

    // ── Meta ────────────────────────────────────────────────────

    fn convert_meta_block(&mut self, node: Node) -> Option<MetaBlock> {
        self.child_by_kind(node, "meta_block").map(|mb| {
            let entries = self.children_by_kind(mb, "meta_entry")
                .into_iter()
                .map(|e| self.convert_meta_entry(e))
                .collect();
            MetaBlock { entries }
        })
    }

    fn convert_meta_entry(&mut self, node: Node) -> MetaEntry {
        let key = self.field(node, "key")
            .map(|n| self.convert_name(n))
            .unwrap_or_else(|| Name::simple(self.intern("?"), self.span(node)));
        let value = self.field(node, "value")
            .map(|n| self.convert_term(n))
            .unwrap_or_else(|| self.terms.alloc(Term::Bottom));
        MetaEntry { key, value }
    }

    // ── Rule body ───────────────────────────────────────────────

    fn convert_rule_body(&mut self, node: Node) -> Vec<TermId> {
        let mut terms = Vec::new();
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            if is_term_kind(child.kind()) {
                terms.push(self.convert_term(child));
            }
        }
        terms
    }

    // ── Domain ──────────────────────────────────────────────────

    fn convert_domain(&mut self, node: Node) -> Option<Domain> {
        let name = self.field(node, "name")
            .map(|n| self.convert_name(n))?;
        let span = self.span(node);

        let imports = self.children_by_kind(node, "import_clause")
            .into_iter()
            .map(|ic| self.convert_import(ic))
            .collect();

        let exports = self.child_by_kind(node, "export_clause")
            .map(|ec| self.children_by_kind(ec, "name")
                .into_iter()
                .map(|n| self.convert_name(n))
                .collect())
            .unwrap_or_default();

        // Domain body items
        let mut items = Vec::new();
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            match child.kind() {
                "name" | "import_clause" | "export_clause" => {}
                _ => {
                    if let Some(item) = self.convert_item(child) {
                        items.push(item);
                    }
                }
            }
        }

        Some(Domain {
            name,
            imports,
            exports,
            items,
            span,
        })
    }

    fn convert_import(&mut self, node: Node) -> Import {
        let names: Vec<_> = self.children_by_kind(node, "name")
            .into_iter()
            .map(|n| self.convert_name(n))
            .collect();

        let path = names.into_iter().next().unwrap_or_else(|| {
            Name::simple(self.intern("?"), self.span(node))
        });

        // Selected imports from { ... }
        // For simplicity, re-scan for names after the first
        let all_names: Vec<_> = self.children_by_kind(node, "name")
            .into_iter()
            .map(|n| self.convert_name(n))
            .collect();

        let selected = if all_names.len() > 1 {
            Some(all_names[1..].to_vec())
        } else {
            None
        };

        let where_clause = self.child_by_kind(node, "where_clause").map(|wc| {
            self.children_by_kind(wc, "sort_binding")
                .into_iter()
                .map(|b| self.convert_sort_binding(b))
                .collect()
        });

        Import {
            path,
            selected,
            where_clause,
        }
    }

    // ── Sort ────────────────────────────────────────────────────

    fn convert_abstract_sort(&mut self, node: Node) -> Option<AbstractSort> {
        let name = self.field(node, "name")
            .map(|n| self.convert_name(n))?;
        let visibility = self.convert_visibility(node);
        let meta = self.convert_meta_block(node);
        let span = self.span(node);
        Some(AbstractSort { visibility, name, meta, span })
    }

    fn convert_sort_with_body(&mut self, node: Node) -> Option<SortWithBody> {
        let name = self.field(node, "name")
            .map(|n| self.convert_name(n))?;
        let visibility = self.convert_visibility(node);
        let meta = self.convert_meta_block(node);
        let span = self.span(node);

        let imports = self.children_by_kind(node, "import_clause")
            .into_iter()
            .map(|ic| self.convert_import(ic))
            .collect();

        let exports = self.child_by_kind(node, "export_clause")
            .map(|ec| self.children_by_kind(ec, "name")
                .into_iter()
                .map(|n| self.convert_name(n))
                .collect())
            .unwrap_or_default();

        let mut items = Vec::new();
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            match child.kind() {
                "name" | "visibility" | "import_clause" | "export_clause" | "meta_block" => {}
                _ => {
                    if let Some(item) = self.convert_item(child) {
                        items.push(item);
                    }
                }
            }
        }

        Some(SortWithBody {
            visibility,
            name,
            imports,
            exports,
            items,
            meta,
            span,
        })
    }

    fn convert_field_decl(&mut self, node: Node) -> FieldDecl {
        let name_node = self.field(node, "name");
        let name = name_node
            .map(|n| self.intern(self.text(n)))
            .unwrap_or_else(|| self.intern("?"));

        let ty = self.field(node, "type")
            .map(|t| self.convert_type(t))
            .unwrap_or_else(|| {
                let sym = self.intern("?");
                TypeExpr::Simple(Name::simple(sym, self.span(node)))
            });

        FieldDecl { name, ty }
    }

    // ── Rule ────────────────────────────────────────────────────

    fn convert_rule(&mut self, node: Node) -> Option<Rule> {
        self.reset_var_scope();
        let span = self.span(node);

        let label = self.field(node, "label")
            .map(|n| self.convert_name(n));

        let head = self.field(node, "head")
            .map(|h| self.convert_rule_head(h))
            .unwrap_or(RuleHead::Bottom);

        let body = self.field(node, "body")
            .map(|b| self.convert_rule_body(b));

        let meta = self.convert_meta_block(node);

        Some(Rule { label, head, body, meta, span })
    }

    fn convert_rule_head(&mut self, node: Node) -> RuleHead {
        let text = self.text(node);
        if text.contains('⊥') {
            return RuleHead::Bottom;
        }
        // The rule_head is choice(⊥, _term) — if not bottom, it's a term
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            if is_term_kind(child.kind()) {
                return RuleHead::Term(self.convert_term(child));
            }
        }
        // If rule_head itself is a term kind
        if is_term_kind(node.kind()) {
            return RuleHead::Term(self.convert_term(node));
        }
        RuleHead::Bottom
    }

    // ── Operation ───────────────────────────────────────────────

    fn convert_operation(&mut self, node: Node) -> Option<Operation> {
        self.reset_var_scope();
        let span = self.span(node);
        let name = self.field(node, "name")
            .map(|n| self.convert_name(n))?;
        let visibility = self.convert_visibility(node);

        let params = self.children_by_kind(node, "param")
            .into_iter()
            .map(|p| self.convert_param(p))
            .collect();

        let return_type = self.field(node, "return_type")
            .map(|t| self.convert_type(t))
            .unwrap_or_else(|| {
                let sym = self.intern("Void");
                TypeExpr::Simple(Name::simple(sym, span))
            });

        let mut requires = Vec::new();
        let mut ensures = Vec::new();
        let mut effects = Vec::new();

        for clause in self.children_by_kind(node, "operation_clause") {
            let mut cursor = clause.walk();
            for child in clause.named_children(&mut cursor) {
                match child.kind() {
                    "requires_clause" => {
                        if let Some(body) = self.child_by_kind(child, "rule_body") {
                            requires.push(self.convert_rule_body(body));
                        }
                    }
                    "ensures_clause" => {
                        if let Some(body) = self.child_by_kind(child, "rule_body") {
                            ensures.push(self.convert_rule_body(body));
                        }
                    }
                    "effects_clause" => {
                        for eff in self.children_by_kind(child, "effect") {
                            if let Some(e) = self.convert_effect(eff) {
                                effects.push(e);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        let meta = self.convert_meta_block(node);

        Some(Operation {
            visibility,
            name,
            params,
            return_type,
            requires,
            ensures,
            effects,
            meta,
            span,
        })
    }

    fn convert_param(&mut self, node: Node) -> Param {
        let name = self.field(node, "name")
            .map(|n| self.intern(self.text(n)))
            .unwrap_or_else(|| self.intern("?"));

        let ty = self.field(node, "type")
            .map(|t| self.convert_type(t))
            .unwrap_or_else(|| {
                let sym = self.intern("?");
                TypeExpr::Simple(Name::simple(sym, self.span(node)))
            });

        Param { name, ty }
    }

    fn convert_effect(&mut self, node: Node) -> Option<Effect> {
        let text = self.text(node);
        let name_node = self.child_by_kind(node, "name")?;
        let name = self.convert_name(name_node);

        if text.starts_with("Modifies") {
            Some(Effect::Modifies(name))
        } else if text.starts_with("Reads") {
            Some(Effect::Reads(name))
        } else if text.starts_with("Emits") {
            Some(Effect::Emits(name))
        } else if text.starts_with("Errors") {
            Some(Effect::Errors(name))
        } else if text.starts_with("Requires") {
            Some(Effect::Requires(name))
        } else {
            self.err(format!("unknown effect: {text}"), node);
            None
        }
    }

    // ── Sugar: entity, fact, constraint ─────────────────────────

    fn convert_entity(&mut self, node: Node) -> Option<Entity> {
        let name = self.field(node, "name")
            .map(|n| self.convert_name(n))?;
        let visibility = self.convert_visibility(node);
        let span = self.span(node);

        let fields = self.children_by_kind(node, "field_decl")
            .into_iter()
            .map(|f| self.convert_field_decl(f))
            .collect();

        let meta = self.convert_meta_block(node);

        Some(Entity { visibility, name, fields, meta, span })
    }

    fn convert_fact(&mut self, node: Node) -> Option<Fact> {
        let span = self.span(node);
        let term = self.field(node, "term")
            .map(|t| self.convert_term(t))?;
        let meta = self.convert_meta_block(node);
        Some(Fact { term, meta, span })
    }

    fn convert_constraint(&mut self, node: Node) -> Option<Constraint> {
        self.reset_var_scope();
        let span = self.span(node);
        let label = self.field(node, "label")
            .map(|n| self.convert_name(n));
        let body = self.field(node, "body")
            .map(|b| self.convert_rule_body(b))
            .unwrap_or_default();
        let meta = self.convert_meta_block(node);
        Some(Constraint { label, body, meta, span })
    }

    // ── Sugar: blocks ───────────────────────────────────────────

    fn convert_operation_block(&mut self, node: Node) -> Option<OperationBlock> {
        let span = self.span(node);
        let entries = self.children_by_kind(node, "operation_entry")
            .into_iter()
            .filter_map(|e| self.convert_operation_entry(e))
            .collect();
        Some(OperationBlock { entries, span })
    }

    fn convert_operation_entry(&mut self, node: Node) -> Option<Operation> {
        // operation_entry has the same structure as operation_declaration
        // but without the "operation" keyword
        self.reset_var_scope();
        let span = self.span(node);
        let name = self.field(node, "name")
            .map(|n| self.convert_name(n))?;
        let visibility = self.convert_visibility(node);

        let params = self.children_by_kind(node, "param")
            .into_iter()
            .map(|p| self.convert_param(p))
            .collect();

        let return_type = self.field(node, "return_type")
            .map(|t| self.convert_type(t))
            .unwrap_or_else(|| {
                let sym = self.intern("Void");
                TypeExpr::Simple(Name::simple(sym, span))
            });

        let mut requires = Vec::new();
        let mut ensures = Vec::new();
        let mut effects = Vec::new();

        for clause in self.children_by_kind(node, "operation_clause") {
            let mut cursor = clause.walk();
            for child in clause.named_children(&mut cursor) {
                match child.kind() {
                    "requires_clause" => {
                        if let Some(body) = self.child_by_kind(child, "rule_body") {
                            requires.push(self.convert_rule_body(body));
                        }
                    }
                    "ensures_clause" => {
                        if let Some(body) = self.child_by_kind(child, "rule_body") {
                            ensures.push(self.convert_rule_body(body));
                        }
                    }
                    "effects_clause" => {
                        for eff in self.children_by_kind(child, "effect") {
                            if let Some(e) = self.convert_effect(eff) {
                                effects.push(e);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        let meta = self.convert_meta_block(node);

        Some(Operation {
            visibility,
            name,
            params,
            return_type,
            requires,
            ensures,
            effects,
            meta,
            span,
        })
    }

    fn convert_rule_block(&mut self, node: Node) -> Option<RuleBlock> {
        let span = self.span(node);
        let entries = self.children_by_kind(node, "rule_entry")
            .into_iter()
            .filter_map(|e| self.convert_rule_entry(e))
            .collect();
        Some(RuleBlock { entries, span })
    }

    fn convert_rule_entry(&mut self, node: Node) -> Option<Rule> {
        self.reset_var_scope();
        let span = self.span(node);
        let label = self.field(node, "label")
            .map(|n| self.convert_name(n));
        let head = self.field(node, "head")
            .map(|h| self.convert_rule_head(h))
            .unwrap_or(RuleHead::Bottom);
        let body = self.field(node, "body")
            .map(|b| self.convert_rule_body(b));
        let meta = self.convert_meta_block(node);
        Some(Rule { label, head, body, meta, span })
    }

    // ── Stage 0: project ────────────────────────────────────────

    fn convert_project(&mut self, node: Node) -> Option<Project> {
        let span = self.span(node);
        let name = self.field(node, "name")
            .map(|n| self.convert_name(n))?;

        let fields_node = self.child_by_kind(node, "project_fields");

        let mut structure = ProjectStructure::ToolsOnly;
        let mut import_tools_list = Vec::new();
        let mut tools = Vec::new();
        let mut domains = Vec::new();
        let mut meta = None;

        if let Some(pf) = fields_node {
            // Check for simple_project_fields
            if let Some(spf) = self.child_by_kind(pf, "simple_project_fields") {
                structure = ProjectStructure::Simple(self.convert_simple_project_fields(spf));
            } else if let Some(ml) = self.child_by_kind(pf, "module_list") {
                let modules = self.children_by_kind(ml, "module_declaration")
                    .into_iter()
                    .filter_map(|m| self.convert_module_decl(m))
                    .collect();
                structure = ProjectStructure::Modules(modules);
            }

            // Import tools declarations
            for it in self.children_by_kind(pf, "import_tools_declaration") {
                if let Some(imp) = self.convert_import_tools(it) {
                    import_tools_list.push(imp);
                }
            }

            // Tools and domains are just name lists — we need to find them
            // by scanning for "name" children that appear after "tools:" or "domains:"
            // For simplicity, collect all remaining name children
            let all_names: Vec<_> = self.children_by_kind(pf, "name")
                .into_iter()
                .map(|n| self.convert_name(n))
                .collect();

            // Heuristic: names before "domains:" are tools, after are domains
            // Actually, let's just look at the raw text structure
            let pf_text = self.text(pf);
            if let Some(tools_pos) = pf_text.find("tools") {
                if let Some(domains_pos) = pf_text.find("domains") {
                    // Split names into tools and domains based on position
                    for n in &all_names {
                        let name_start = n.span.start as usize - pf.start_byte();
                        if name_start > domains_pos {
                            domains.push(n.clone());
                        } else if name_start > tools_pos {
                            tools.push(n.clone());
                        }
                    }
                } else {
                    // All names after "tools:" are tools
                    for n in &all_names {
                        let name_start = n.span.start as usize - pf.start_byte();
                        if name_start > tools_pos {
                            tools.push(n.clone());
                        }
                    }
                }
            }

            meta = self.convert_meta_block(pf);
        }

        Some(Project {
            name,
            structure,
            import_tools: import_tools_list,
            tools,
            domains,
            meta,
            span,
        })
    }

    fn convert_simple_project_fields(&mut self, node: Node) -> SimpleProjectFields {
        let idents: Vec<_> = self.children_by_kind(node, "identifier")
            .into_iter()
            .map(|n| self.text(n).to_string())
            .collect();

        let language = idents.first().cloned().unwrap_or_default();
        let build = idents.get(1).cloned();

        let sources = self.children_by_kind(node, "source_root")
            .into_iter()
            .map(|s| self.convert_source_root(s))
            .collect();

        SimpleProjectFields { language, build, sources }
    }

    fn convert_module_decl(&mut self, node: Node) -> Option<ModuleDecl> {
        let span = self.span(node);
        let name = self.field(node, "name")
            .map(|n| self.convert_name(n))?;

        let fields = self.child_by_kind(node, "module_fields");
        let (root, language, build, sources, meta) = if let Some(mf) = fields {
            let strings: Vec<_> = self.children_by_kind(mf, "string_literal")
                .into_iter()
                .map(|s| {
                    let raw = self.text(s);
                    raw[1..raw.len() - 1].to_string()
                })
                .collect();
            let root = strings.first().cloned().unwrap_or_default();

            let idents: Vec<_> = self.children_by_kind(mf, "identifier")
                .into_iter()
                .map(|n| self.text(n).to_string())
                .collect();
            let language = idents.first().cloned().unwrap_or_default();
            let build = idents.get(1).cloned();

            let sources = self.children_by_kind(mf, "source_root")
                .into_iter()
                .map(|s| self.convert_source_root(s))
                .collect();

            let meta = self.convert_meta_block(mf);
            (root, language, build, sources, meta)
        } else {
            (String::new(), String::new(), None, Vec::new(), None)
        };

        Some(ModuleDecl { name, root, language, build, sources, meta, span })
    }

    fn convert_source_root(&mut self, node: Node) -> SourceRoot {
        let strings: Vec<_> = self.children_by_kind(node, "string_literal")
            .into_iter()
            .map(|s| {
                let raw = self.text(s);
                raw[1..raw.len() - 1].to_string()
            })
            .collect();

        let path = strings.first().cloned().unwrap_or_default();

        let language = self.children_by_kind(node, "identifier")
            .first()
            .map(|n| self.text(*n).to_string());

        let scope = self.child_by_kind(node, "source_scope")
            .map(|s| match self.text(s) {
                "Main" => SourceScope::Main,
                "Test" => SourceScope::Test,
                "Generated" => SourceScope::Generated,
                "Docs" => SourceScope::Docs,
                _ => SourceScope::Main,
            })
            .unwrap_or(SourceScope::Main);

        SourceRoot { path, language, scope }
    }

    fn convert_import_tools(&mut self, node: Node) -> Option<ImportTools> {
        let span = self.span(node);
        let names = self.children_by_kind(node, "name")
            .into_iter()
            .map(|n| self.convert_name(n))
            .collect();
        Some(ImportTools { names, span })
    }

    // ── Stage 0: tool ───────────────────────────────────────────

    fn convert_tool(&mut self, node: Node) -> Option<Tool> {
        let span = self.span(node);
        let name = self.field(node, "name")
            .map(|n| self.convert_name(n))?;

        let fields_node = self.child_by_kind(node, "tool_fields");

        let (command, args, working_dir, timeout, success, meta) =
            if let Some(tf) = fields_node {
                let strings: Vec<_> = self.children_by_kind(tf, "string_literal")
                    .into_iter()
                    .map(|s| {
                        let raw = self.text(s);
                        raw[1..raw.len() - 1].to_string()
                    })
                    .collect();

                let command = strings.first().cloned().unwrap_or_default();

                // args: all string literals after the first, until a non-string is found
                // This is a simplification; proper handling would check positions
                let args = if strings.len() > 1 {
                    // Check if "args" keyword is in text
                    let tf_text = self.text(tf);
                    if tf_text.contains("args") {
                        strings[1..].to_vec()
                            .into_iter()
                            .take_while(|_| true) // simplified
                            .collect()
                    } else {
                        Vec::new()
                    }
                } else {
                    Vec::new()
                };

                let working_dir = {
                    let tf_text = self.text(tf);
                    if tf_text.contains("working_dir") {
                        strings.last().cloned()
                    } else {
                        None
                    }
                };

                let timeout = self.child_by_kind(tf, "duration_literal")
                    .map(|d| self.text(d).to_string());

                let success = self.child_by_kind(tf, "success_criterion")
                    .map(|sc| self.convert_success_criterion(sc))
                    .unwrap_or(SuccessCriterion::ExitZero);

                let meta = self.convert_meta_block(tf);

                (command, args, working_dir, timeout, success, meta)
            } else {
                (String::new(), Vec::new(), None, None, SuccessCriterion::ExitZero, None)
            };

        Some(Tool { name, command, args, working_dir, timeout, success, meta, span })
    }

    fn convert_success_criterion(&mut self, node: Node) -> SuccessCriterion {
        let text = self.text(node);
        if text.starts_with("ExitZero") {
            SuccessCriterion::ExitZero
        } else if text.starts_with("ExitCode") {
            let int = self.child_by_kind(node, "integer_literal")
                .and_then(|n| self.text(n).parse::<i64>().ok())
                .unwrap_or(0);
            SuccessCriterion::ExitCode(int)
        } else if text.starts_with("OutputMatches") {
            let s = self.child_by_kind(node, "string_literal")
                .map(|n| {
                    let raw = self.text(n);
                    raw[1..raw.len() - 1].to_string()
                })
                .unwrap_or_default();
            SuccessCriterion::OutputMatches(s)
        } else if text.starts_with("Custom") {
            let mut cursor = node.walk();
            let term = node.named_children(&mut cursor)
                .find(|c| is_term_kind(c.kind()))
                .map(|c| self.convert_term(c))
                .unwrap_or_else(|| self.terms.alloc(Term::Bottom));
            SuccessCriterion::Custom(term)
        } else {
            SuccessCriterion::ExitZero
        }
    }

    // ── Stage 0: workitem ───────────────────────────────────────

    fn convert_workitem(&mut self, node: Node) -> Option<WorkItem> {
        let span = self.span(node);
        let id = self.field(node, "id")
            .map(|n| self.convert_name(n))?;

        let fields_node = self.child_by_kind(node, "workitem_fields");
        let wf = fields_node?;

        // Description
        let description = {
            let mut found = None;
            for i in 0..wf.child_count() {
                if let Some(child) = wf.child(i) {
                    if !child.is_named() && self.text(child) == "description" {
                        // Next named sibling should be the term
                        for j in (i+1)..wf.child_count() {
                            if let Some(next) = wf.child(j) {
                                if next.is_named() && is_term_kind(next.kind()) {
                                    found = Some(self.convert_term(next));
                                    break;
                                }
                            }
                        }
                        break;
                    }
                }
            }
            found
        };

        // Context refs
        let context = self.children_by_kind(wf, "context_ref")
            .into_iter()
            .filter_map(|c| self.convert_context_ref(c))
            .collect();

        // Acceptance criteria
        let acceptance = self.children_by_kind(wf, "acceptance_criterion")
            .into_iter()
            .filter_map(|a| self.convert_acceptance_criterion(a))
            .collect();

        // depends_on
        let depends_on = Vec::new(); // simplified for now

        // generates
        let generates = Vec::new(); // simplified for now

        // capabilities
        let requires_capability = self.children_by_kind(wf, "capability")
            .into_iter()
            .filter_map(|c| self.convert_capability(c))
            .collect();

        // status
        let status = self.child_by_kind(wf, "work_status")
            .map(|s| self.convert_work_status(s))
            .unwrap_or(WorkStatus::Draft);

        let meta = self.convert_meta_block(wf);

        Some(WorkItem {
            id,
            description,
            context,
            acceptance,
            depends_on,
            generates,
            requires_capability,
            status,
            meta,
            span,
        })
    }

    fn convert_context_ref(&mut self, node: Node) -> Option<ContextRef> {
        let text = self.text(node);
        if text.starts_with("FileRef") {
            let strings: Vec<_> = self.children_by_kind(node, "string_literal")
                .into_iter()
                .map(|s| {
                    let raw = self.text(s);
                    raw[1..raw.len() - 1].to_string()
                })
                .collect();
            let path = strings.first().cloned().unwrap_or_default();

            let ints: Vec<_> = self.children_by_kind(node, "integer_literal")
                .into_iter()
                .filter_map(|n| self.text(n).parse::<i64>().ok())
                .collect();
            let lines = if ints.len() >= 2 {
                Some((ints[0], ints[1]))
            } else {
                None
            };

            Some(ContextRef::FileRef { path, lines })
        } else if text.starts_with("FactRef") {
            let name = self.child_by_kind(node, "name")
                .map(|n| self.convert_name(n))?;
            let mut cursor = node.walk();
            let term = node.named_children(&mut cursor)
                .find(|c| is_term_kind(c.kind()))
                .map(|c| self.convert_term(c))
                .unwrap_or_else(|| self.terms.alloc(Term::Bottom));
            Some(ContextRef::FactRef { name, term })
        } else if text.starts_with("WorkItemRef") {
            let name = self.child_by_kind(node, "name")
                .map(|n| self.convert_name(n))?;
            Some(ContextRef::WorkItemRef(name))
        } else {
            None
        }
    }

    fn convert_acceptance_criterion(&mut self, node: Node) -> Option<AcceptanceCriterion> {
        let text = self.text(node);
        if text.starts_with("ToolPasses") {
            let name = self.child_by_kind(node, "name")
                .map(|n| self.convert_name(n))?;
            Some(AcceptanceCriterion::ToolPasses { tool: name, bindings: None })
        } else if text.starts_with("FactHolds") {
            let name = self.child_by_kind(node, "name")
                .map(|n| self.convert_name(n))?;
            let mut cursor = node.walk();
            let term = node.named_children(&mut cursor)
                .find(|c| is_term_kind(c.kind()))
                .map(|c| self.convert_term(c))
                .unwrap_or_else(|| self.terms.alloc(Term::Bottom));
            Some(AcceptanceCriterion::FactHolds { name, term })
        } else if text.starts_with("Compiles") {
            if let Some(sr) = self.child_by_kind(node, "source_root") {
                Some(AcceptanceCriterion::Compiles(
                    CompileTarget::SourceRoot(self.convert_source_root(sr))
                ))
            } else if let Some(n) = self.child_by_kind(node, "name") {
                Some(AcceptanceCriterion::Compiles(
                    CompileTarget::Module(self.convert_name(n))
                ))
            } else {
                None
            }
        } else if text.starts_with("Constraint") {
            let mut cursor = node.walk();
            let term = node.named_children(&mut cursor)
                .find(|c| is_term_kind(c.kind()))
                .map(|c| self.convert_term(c))
                .unwrap_or_else(|| self.terms.alloc(Term::Bottom));
            Some(AcceptanceCriterion::Constraint(term))
        } else {
            None
        }
    }

    fn convert_capability(&mut self, node: Node) -> Option<Capability> {
        let text = self.text(node);
        if text.starts_with("Code") {
            let strings: Vec<_> = self.children_by_kind(node, "string_literal")
                .into_iter()
                .map(|s| {
                    let raw = self.text(s);
                    raw[1..raw.len() - 1].to_string()
                })
                .collect();
            Some(Capability::Code { languages: strings })
        } else {
            match text.trim() {
                "Test" => Some(Capability::Test),
                "Refine" => Some(Capability::Refine),
                "Review" => Some(Capability::Review),
                "Decompose" => Some(Capability::Decompose),
                "Architect" => Some(Capability::Architect),
                "HumanJudgment" => Some(Capability::HumanJudgment),
                _ => None,
            }
        }
    }

    fn convert_work_status(&mut self, node: Node) -> WorkStatus {
        let text = self.text(node).trim();
        if text == "Draft" {
            WorkStatus::Draft
        } else if text == "Open" {
            WorkStatus::Open
        } else if text.starts_with("Claimed") {
            let strings = self.extract_keyed_strings(node);
            WorkStatus::Claimed {
                agent: strings.get("agent").cloned().unwrap_or_default(),
                since: strings.get("since").cloned().unwrap_or_default(),
            }
        } else if text.starts_with("Delivered") {
            let strings = self.extract_keyed_strings(node);
            WorkStatus::Delivered {
                agent: strings.get("agent").cloned().unwrap_or_default(),
                at: strings.get("at").cloned().unwrap_or_default(),
            }
        } else if text.starts_with("Verified") {
            let strings = self.extract_keyed_strings(node);
            WorkStatus::Verified {
                at: strings.get("at").cloned().unwrap_or_default(),
            }
        } else if text.starts_with("Rejected") {
            let strings = self.extract_keyed_strings(node);
            WorkStatus::Rejected {
                reason: strings.get("reason").cloned().unwrap_or_default(),
                at: strings.get("at").cloned().unwrap_or_default(),
            }
        } else if text.starts_with("ProposalRejected") {
            let strings = self.extract_keyed_strings(node);
            WorkStatus::ProposalRejected {
                reason: strings.get("reason").cloned().unwrap_or_default(),
                at: strings.get("at").cloned().unwrap_or_default(),
            }
        } else if text.starts_with("Stale") {
            let strings = self.extract_keyed_strings(node);
            WorkStatus::Stale {
                reason: strings.get("reason").cloned().unwrap_or_default(),
                since: strings.get("since").cloned().unwrap_or_default(),
            }
        } else {
            WorkStatus::Draft
        }
    }

    /// Extract key:value string pairs from a node like `Claimed(agent: "x", since: "y")`
    fn extract_keyed_strings(&self, node: Node) -> std::collections::HashMap<String, String> {
        let mut result = std::collections::HashMap::new();
        let mut prev_key: Option<String> = None;

        for i in 0..node.child_count() {
            if let Some(child) = node.child(i) {
                if !child.is_named() {
                    let t = self.text(child);
                    // Keys are anonymous tokens like "agent", "since", "at", "reason"
                    match t {
                        "agent" | "since" | "at" | "reason" => {
                            prev_key = Some(t.to_string());
                        }
                        _ => {}
                    }
                } else if child.kind() == "string_literal" {
                    if let Some(key) = prev_key.take() {
                        let raw = self.text(child);
                        let val = raw[1..raw.len() - 1].to_string();
                        result.insert(key, val);
                    }
                }
            }
        }
        result
    }

    // ── Stage 0: feedback ───────────────────────────────────────

    fn convert_feedback(&mut self, node: Node) -> Option<Feedback> {
        let span = self.span(node);
        let fields_node = self.child_by_kind(node, "feedback_fields")?;

        let workitem = self.child_by_kind(fields_node, "name")
            .map(|n| self.convert_name(n))
            .unwrap_or_else(|| Name::simple(self.intern("?"), span));

        let strings: Vec<_> = self.children_by_kind(fields_node, "string_literal")
            .into_iter()
            .map(|s| {
                let raw = self.text(s);
                raw[1..raw.len() - 1].to_string()
            })
            .collect();

        let author = strings.first().cloned().unwrap_or_default();
        let at = strings.get(1).cloned().unwrap_or_default();

        let mut cursor = fields_node.walk();
        let content = fields_node.named_children(&mut cursor)
            .find(|c| is_term_kind(c.kind()))
            .map(|c| self.convert_term(c))
            .unwrap_or_else(|| self.terms.alloc(Term::Bottom));

        let meta = self.convert_meta_block(fields_node);

        Some(Feedback { workitem, author, content, at, meta, span })
    }
}

/// Check if a node kind is a term.
fn is_term_kind(kind: &str) -> bool {
    matches!(
        kind,
        "string_literal"
            | "integer_literal"
            | "float_literal"
            | "boolean_literal"
            | "variable"
            | "fn_term"
            | "ref_term"
            | "unspecified_term"
            | "infix_term"
            | "identifier"
    )
}

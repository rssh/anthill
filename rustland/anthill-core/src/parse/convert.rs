/// Tree-sitter CST → Parse IR conversion.
///
/// One function per grammar node kind. Uses child iteration to walk
/// the CST and build typed IR nodes.

use std::collections::HashMap;

use ordered_float::OrderedFloat;
use smallvec::SmallVec;
use tree_sitter::Node;

use crate::intern::{SymbolTable, Symbol};
use crate::span::Span;
use crate::kb::term::{Term, TermId, Literal, VarId};

/// Join name segments into a single dot-separated string for interning.
fn join_name_segments(symbols: &crate::intern::SymbolTable, segments: &[Symbol]) -> String {
    let mut out = String::new();
    for (i, &sym) in segments.iter().enumerate() {
        if i > 0 {
            out.push('.');
        }
        out.push_str(symbols.name(sym));
    }
    out
}

use super::error::ParseError;
use super::ir::*;

pub(super) struct Converter<'a> {
    source: &'a str,
    pub symbols: SymbolTable,
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
            symbols: SymbolTable::new(),
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
        self.symbols.intern(s)
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
            let joined = join_name_segments(&self.symbols, &name.segments);
            self.intern(&joined)
        }
    }

    /// Intern a positional tuple label: _1, _2, _3, ...
    fn intern_positional_label(&mut self, index: usize) -> Symbol {
        self.intern(&format!("_{}", index + 1))
    }

    /// Allocate a Fn term with only positional args (no named args).
    fn alloc_fn_term(&mut self, functor_name: &str, pos_args: SmallVec<[TermId; 4]>) -> TermId {
        let functor = self.intern(functor_name);
        self.terms.alloc(Term::Fn {
            functor,
            pos_args,
            named_args: SmallVec::new(),
        })
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

    /// All children with a given field name (for repeated fields).
    fn fields_by_name<'t>(&self, node: Node<'t>, name: &str) -> Vec<Node<'t>> {
        let mut cursor = node.walk();
        node.children_by_field_name(name, &mut cursor).collect()
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
            "namespace_declaration" => self.convert_namespace(node).map(Item::Namespace),
            "abstract_sort" => self.convert_abstract_sort(node).map(Item::AbstractSort),
            "sort_with_body" => self.convert_sort_with_body(node).map(Item::SortWithBody),
            "rule_declaration" => self.convert_rule(node).map(Item::Rule),
            "operation_declaration" => self.convert_operation(node).map(Item::Operation),
            "requires_declaration" => self.convert_requires_decl(node).map(Item::RequiresDecl),
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
            "describe_declaration" => self.convert_describe(node).map(Item::Describe),
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
            "variable_term" => {
                let var_node = self.child_by_kind(node, "variable").unwrap_or(node);
                let term_id = self.convert_variable_node(var_node);
                let descriptions = self.fields_by_name(node, "description")
                    .into_iter()
                    .map(|d| strip_description_delimiters(self.text(d)))
                    .collect();
                TypeExpr::Variable { term_id, descriptions }
            }
            "variable" => {
                let term_id = self.convert_variable_node(node);
                TypeExpr::Variable { term_id, descriptions: Vec::new() }
            }
            "tuple_type" => {
                self.convert_tuple_type(node)
            }
            "arrow_type" => {
                self.convert_arrow_type(node)
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
            .map(|n| self.convert_name(n));
        let type_field = self.field(node, "type");

        match (param, type_field) {
            // Named: Eq{T = Int} — param and type both present
            (Some(p), Some(t)) => SortBinding { param: Some(p), bound: self.convert_type(t) },
            // Positional: List{Int} or List{T} — no `=`, value binds to next param
            (Some(p), None) => {
                let bound = TypeExpr::Simple(p);
                SortBinding { param: None, bound }
            }
            // Variable: Modify{?} or Modify{?r} — positional with variable type
            (None, Some(t)) => {
                let bound = self.convert_type(t);
                SortBinding { param: None, bound }
            }
            // Fallback (shouldn't happen)
            (None, None) => {
                let sym = self.intern("?");
                let name = Name::simple(sym, self.span(node));
                SortBinding { param: None, bound: TypeExpr::Simple(name) }
            }
        }
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
                if let Ok(n) = text.parse::<i64>() {
                    self.terms.alloc(Term::Const(Literal::Int(n)))
                } else if let Ok(big) = text.parse::<num_bigint::BigInt>() {
                    self.terms.alloc(Term::Const(Literal::BigInt(big)))
                } else {
                    self.err(format!("invalid integer: {text}"), node);
                    self.terms.alloc(Term::Const(Literal::Int(0)))
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
                // variable is a single token: ?name or bare ?
                self.convert_variable_node(node)
            }
            "variable_term" => {
                // variable_term wraps variable + zero or more description_blocks
                let var_node = self.child_by_kind(node, "variable").unwrap_or(node);
                let tid = self.convert_variable_node(var_node);
                let descs: Vec<String> = self.fields_by_name(node, "description")
                    .into_iter()
                    .map(|d| strip_description_delimiters(self.text(d)))
                    .collect();
                if !descs.is_empty() {
                    self.terms.descriptions.insert(tid, descs);
                }
                tid
            }
            "fn_term" => self.convert_fn_term(node),
            "instantiation_term" => self.convert_instantiation_term(node),
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
            "infix_term" => self.convert_infix(node),
            "prefix_term" => self.convert_prefix(node),
            "field_access" => self.convert_field_access(node),
            "set_literal" => self.convert_set_literal(node),
            "tuple_literal" => self.convert_tuple_literal(node),
            "paren_expr" => {
                // (a) = a — unwrap parenthesized expression
                let inner = node.named_child(0).unwrap_or(node);
                self.convert_term(inner)
            }
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

    fn convert_variable_node(&mut self, node: Node) -> TermId {
        let text = self.text(node);
        if text.len() > 1 {
            // Named variable: ?x (shared within scope)
            let name = &text[1..]; // strip leading '?'
            let sym = self.intern(name);
            let vid = self.get_or_create_var(sym);
            self.terms.alloc(Term::Var(vid))
        } else {
            // Bare ? — anonymous variable (always fresh, like _ in Prolog)
            let sym = self.intern("_");
            let vid = VarId::new(self.next_var, sym);
            self.next_var += 1;
            self.terms.alloc(Term::Var(vid))
        }
    }

    fn convert_fn_term(&mut self, node: Node) -> TermId {
        let name_node = self.field(node, "name").unwrap_or(node);
        let name = self.convert_name(name_node);
        let functor = self.intern_name(&name);

        let mut pos_args: SmallVec<[TermId; 4]> = SmallVec::new();
        let mut named_args: SmallVec<[(crate::intern::Symbol, TermId); 2]> = SmallVec::new();
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            match child.kind() {
                "named_arg" => {
                    let key_node = self.field(child, "name");
                    let val_node = self.field(child, "value");
                    if let (Some(k), Some(v)) = (key_node, val_node) {
                        let sym = self.intern(self.text(k));
                        let tid = self.convert_term(v);
                        named_args.push((sym, tid));
                    }
                }
                "name" => { /* already handled */ }
                _ if is_term_kind(child.kind()) => {
                    let tid = self.convert_term(child);
                    pos_args.push(tid);
                }
                _ => {}
            }
        }

        self.terms.alloc(Term::Fn { functor, pos_args, named_args })
    }

    fn convert_instantiation_term(&mut self, node: Node) -> TermId {
        // Eq{Int} or Eq{T = Int} — parameterized type in term position
        let name_node = self.field(node, "name").unwrap_or(node);
        let name = self.convert_name(name_node);
        let functor = self.intern_name(&name);

        let mut pos_args: SmallVec<[TermId; 4]> = SmallVec::new();
        let mut named_args: SmallVec<[(crate::intern::Symbol, TermId); 2]> = SmallVec::new();
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            if child.kind() == "sort_binding" {
                let param_node = self.field(child, "param");
                let type_node = self.field(child, "type");
                match (param_node, type_node) {
                    (Some(p), Some(t)) => {
                        // Explicit: Eq{T = Int} — convert the type to a Ref term
                        let param_name = self.convert_name(p);
                        let param_sym = self.intern_name(&param_name);
                        let type_name = self.convert_type_to_name(t);
                        let type_sym = self.intern_name(&type_name);
                        named_args.push((param_sym, self.terms.alloc(Term::Ref(type_sym))));
                    }
                    (Some(p), None) => {
                        // Positional: List{Int} — value binds to next param in order
                        let name = self.convert_name(p);
                        let sym = self.intern_name(&name);
                        pos_args.push(self.terms.alloc(Term::Ref(sym)));
                    }
                    (None, Some(t)) => {
                        // Variable binding: Modify{?} or Modify{?r}
                        let tid = self.convert_term(t);
                        pos_args.push(tid);
                    }
                    (None, None) => {}
                }
            }
        }

        self.terms.alloc(Term::Fn { functor, pos_args, named_args })
    }

    /// Extract a Name from a type CST node (simple_type or parameterized_type).
    fn convert_type_to_name(&mut self, node: Node) -> Name {
        // simple_type is just a name node; parameterized_type starts with a name
        let name_node = self.child_by_kind(node, "name").unwrap_or(node);
        self.convert_name(name_node)
    }

    /// Desugar infix syntax via Pratt parsing.
    ///
    /// Collects the flat chain of operands and operators from the CST node,
    /// then delegates to the Pratt resolver for precedence/associativity.
    fn convert_infix(&mut self, node: Node) -> TermId {
        use super::pratt::{InfixElement, desugar_infix_chain};

        let mut elements = Vec::new();
        for i in 0..node.child_count() {
            if let Some(child) = node.child(i) {
                let kind = child.kind();
                if kind == "operator_symbol" {
                    // Named operator_symbol node
                    elements.push(InfixElement::Operator(self.text(child)));
                } else if is_term_kind(kind) || kind == "prefix_term" {
                    // Operand (a term node)
                    elements.push(InfixElement::Operand(self.convert_term(child)));
                } else if !child.is_named() {
                    // Anonymous token = keyword operator (!=, or, and, @, etc.)
                    // or word operator (mod, div)
                    let text = self.text(child);
                    if text != "," {
                        elements.push(InfixElement::Operator(text));
                    }
                }
            }
        }

        match desugar_infix_chain(&elements, &mut self.terms, &mut self.symbols) {
            Ok(tid) => tid,
            Err(msg) => {
                self.err(format!("infix desugaring: {msg}"), node);
                self.terms.alloc(Term::Bottom)
            }
        }
    }

    /// Convert a prefix_term node: `!?a` → `not(?a)`.
    fn convert_prefix(&mut self, node: Node) -> TermId {
        use super::pratt::prefix_entry;

        let mut op_text = None;
        let mut operand_tid = None;

        for i in 0..node.child_count() {
            if let Some(child) = node.child(i) {
                let kind = child.kind();
                if is_term_kind(kind) || kind == "prefix_term" {
                    operand_tid = Some(self.convert_term(child));
                } else if op_text.is_none() {
                    // First non-term child is the operator
                    op_text = Some(self.text(child));
                }
            }
        }

        let op = op_text.unwrap_or("!");
        let operand = operand_tid.unwrap_or_else(|| self.terms.alloc(Term::Bottom));

        let functor_name = match prefix_entry(op) {
            Some(entry) => entry.functor,
            None => {
                self.err(format!("unknown prefix operator: {op}"), node);
                "not"
            }
        };
        let functor = self.intern(functor_name);
        self.terms.alloc(Term::Fn {
            functor,
            pos_args: SmallVec::from_elem(operand, 1),
            named_args: SmallVec::new(),
        })
    }

    /// Convert field access: `?x.y` → `field_access(?x, Ident(y))`.
    /// Desugars to `Fn { functor: "field_access", pos_args: [object, Ident(field)] }`.
    fn convert_field_access(&mut self, node: Node) -> TermId {
        let object_node = self.field(node, "object").unwrap_or(node);
        let object_tid = self.convert_term(object_node);

        let field_node = self.field(node, "field").unwrap_or(node);
        let field_sym = self.intern(self.text(field_node));
        let field_tid = self.terms.alloc(Term::Ident(field_sym));

        let functor = self.intern("field_access");
        self.terms.alloc(Term::Fn {
            functor,
            pos_args: SmallVec::from_slice(&[object_tid, field_tid]),
            named_args: SmallVec::new(),
        })
    }

    /// Convert set literal: `{x, y, z}` → `SetLiteral(x, y, z)`.
    /// `{}` → `SetLiteral()`.
    /// Desugaring to Set.insert/empty happens later when scope is known.
    fn convert_set_literal(&mut self, node: Node) -> TermId {
        let functor = self.intern("SetLiteral");

        let mut elements: SmallVec<[TermId; 4]> = SmallVec::new();
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            if is_term_kind(child.kind()) {
                elements.push(self.convert_term(child));
            }
        }

        self.terms.alloc(Term::Fn {
            functor,
            pos_args: elements,
            named_args: SmallVec::new(),
        })
    }

    fn convert_tuple_literal(&mut self, node: Node) -> TermId {
        let functor = self.intern("TupleLiteral");

        let mut positional: SmallVec<[TermId; 4]> = SmallVec::new();
        let mut named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            match child.kind() {
                "named_arg" => {
                    let key_node = self.field(child, "name");
                    let val_node = self.field(child, "value");
                    if let (Some(k), Some(v)) = (key_node, val_node) {
                        let sym = self.intern(self.text(k));
                        let tid = self.convert_term(v);
                        named.push((sym, tid));
                    }
                }
                _ if is_term_kind(child.kind()) => {
                    positional.push(self.convert_term(child));
                }
                _ => {}
            }
        }

        // All-or-nothing: error if mixing positional and named
        if !positional.is_empty() && !named.is_empty() {
            self.err("tuple literal cannot mix positional and named arguments", node);
        }

        if !positional.is_empty() {
            // Desugar positional to _1, _2, _3, ...
            for (i, tid) in positional.into_iter().enumerate() {
                let label = self.intern_positional_label(i);
                named.push((label, tid));
            }
        }

        self.terms.alloc(Term::Fn {
            functor,
            pos_args: SmallVec::new(),
            named_args: named,
        })
    }

    fn convert_tuple_type(&mut self, node: Node) -> TypeExpr {
        let mut positional: Vec<TypeExpr> = Vec::new();
        let mut named: Vec<(Symbol, TypeExpr)> = Vec::new();
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            match child.kind() {
                "field_decl" => {
                    let name_node = self.field(child, "name");
                    let type_node = self.field(child, "type");
                    if let (Some(n), Some(t)) = (name_node, type_node) {
                        let sym = self.intern(self.text(n));
                        let ty = self.convert_type(t);
                        named.push((sym, ty));
                    }
                }
                "simple_type" | "parameterized_type" | "variable_term" | "variable" | "tuple_type" => {
                    positional.push(self.convert_type(child));
                }
                _ => {}
            }
        }

        // All-or-nothing: error if mixing positional and named
        if !positional.is_empty() && !named.is_empty() {
            self.err("tuple type cannot mix positional and named fields", node);
        }

        if !positional.is_empty() {
            // Desugar positional to _1, _2, _3, ...
            for (i, ty) in positional.into_iter().enumerate() {
                let label = self.intern_positional_label(i);
                named.push((label, ty));
            }
        }

        TypeExpr::Tuple(named)
    }

    fn convert_arrow_type(&mut self, node: Node) -> TypeExpr {
        // Params are inside the arrow_params node (via "params" field)
        let params_node = self.field(node, "params");
        let params: Vec<TypeExpr> = if let Some(pn) = params_node {
            let mut cursor = pn.walk();
            pn.named_children(&mut cursor)
                .map(|child| match child.kind() {
                    "field_decl" => {
                        // Named param: (a: A) -> B — extract the type
                        let type_node = self.field(child, "type").unwrap_or(child);
                        self.convert_type(type_node)
                    }
                    _ => self.convert_type(child),
                })
                .collect()
        } else {
            Vec::new()
        };

        let return_type = self.field(node, "return_type")
            .map(|n| Box::new(self.convert_type(n)))
            .unwrap_or_else(|| {
                self.err("arrow type missing return type", node);
                let sym = self.intern("?");
                Box::new(TypeExpr::Simple(Name::simple(sym, self.span(node))))
            });
        let effect = self.field(node, "effect")
            .map(|n| Box::new(self.convert_type(n)));

        TypeExpr::Arrow { params, return_type, effect }
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

    // ── Namespace ───────────────────────────────────────────────

    fn convert_namespace(&mut self, node: Node) -> Option<Namespace> {
        let name = self.field(node, "name")
            .map(|n| self.convert_name(n))?;
        let span = self.span(node);

        let imports = self.children_by_kind(node, "import_clause")
            .into_iter()
            .map(|ic| self.convert_import(ic))
            .collect();

        let mut exports = Vec::new();
        for ec in self.children_by_kind(node, "export_clause") {
            for n in self.children_by_kind(ec, "name") {
                exports.push(self.convert_name(n));
            }
        }

        // Namespace body items
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

        Some(Namespace {
            name,
            imports,
            exports,
            items,
            span,
        })
    }

    fn convert_import(&mut self, node: Node) -> Import {
        // import_clause → import_path → identifier+ [selective_import | wildcard_import]
        let import_path = self.child_by_kind(node, "import_path")
            .unwrap_or(node);

        let mut cursor = import_path.walk();
        let children: Vec<_> = import_path.named_children(&mut cursor).collect();

        // Check for wildcard or selective import (last segment)
        let has_wildcard = children.iter().any(|c| c.kind() == "wildcard_import");
        let selective = children.iter()
            .find(|c| c.kind() == "selective_import");

        if has_wildcard {
            // import a.b.* → path = a.b, kind = Wildcard
            let path_segments: SmallVec<_> = children.iter()
                .filter(|c| c.kind() == "identifier")
                .map(|c| self.intern(self.text(*c)))
                .collect();
            let path = Name { segments: path_segments, span: self.span(import_path) };
            Import { path, kind: ImportKind::Wildcard }
        } else if let Some(sel_node) = selective {
            // import a.b.{X, Y} → path = a.b, kind = Selective([X, Y])
            let path_segments: SmallVec<_> = children.iter()
                .filter(|c| c.kind() == "identifier")
                .map(|c| self.intern(self.text(*c)))
                .collect();
            let path = Name { segments: path_segments, span: self.span(import_path) };

            let sel = *sel_node;
            let mut sel_cursor = sel.walk();
            let selected: Vec<_> = sel.named_children(&mut sel_cursor)
                .filter(|c| c.kind() == "identifier")
                .map(|c| {
                    let sym = self.intern(self.text(c));
                    Name::simple(sym, self.span(c))
                })
                .collect();
            Import { path, kind: ImportKind::Selective(selected) }
        } else {
            // import a.b.c → path = a.b.c, kind = Plain
            let path_segments: SmallVec<_> = children.iter()
                .filter(|c| c.kind() == "identifier")
                .map(|c| self.intern(self.text(*c)))
                .collect();
            let path = Name { segments: path_segments, span: self.span(import_path) };
            Import { path, kind: ImportKind::Plain }
        }
    }

    // ── Sort ────────────────────────────────────────────────────

    fn convert_abstract_sort(&mut self, node: Node) -> Option<AbstractSort> {
        let name = self.field(node, "name")
            .map(|n| self.convert_name(n))?;
        let visibility = self.convert_visibility(node);
        let meta = self.convert_meta_block(node);
        let span = self.span(node);

        let definition = self.field(node, "definition")
            .map(|def| self.convert_type(def))
            .unwrap_or_else(|| {
                // Fallback: anonymous variable
                let sym = self.intern("_");
                let vid = crate::kb::term::VarId::new(self.next_var, sym);
                self.next_var += 1;
                let tid = self.terms.alloc(Term::Var(vid));
                TypeExpr::Variable { term_id: tid, descriptions: Vec::new() }
            });

        // Descriptions: collect abstract_sort's own description fields first,
        // then hoist from variable_term's descriptions if empty.
        let mut descriptions: Vec<String> = self.fields_by_name(node, "description")
            .into_iter()
            .map(|d| strip_description_delimiters(self.text(d)))
            .collect();
        if descriptions.is_empty() {
            if let TypeExpr::Variable { descriptions: ref var_descs, .. } = definition {
                descriptions = var_descs.clone();
            }
        }

        Some(AbstractSort { visibility, name, definition, descriptions, meta, span })
    }

    fn convert_sort_with_body(&mut self, node: Node) -> Option<SortWithBody> {
        let name = self.field(node, "name")
            .map(|n| self.convert_name(n))?;
        let visibility = self.convert_visibility(node);
        let meta = self.convert_meta_block(node);
        let span = self.span(node);

        let descriptions: Vec<String> = self.fields_by_name(node, "description")
            .into_iter()
            .map(|d| strip_description_delimiters(self.text(d)))
            .collect();

        let imports = self.children_by_kind(node, "import_clause")
            .into_iter()
            .map(|ic| self.convert_import(ic))
            .collect();

        let mut exports = Vec::new();
        for ec in self.children_by_kind(node, "export_clause") {
            for n in self.children_by_kind(ec, "name") {
                exports.push(self.convert_name(n));
            }
        }

        let mut items = Vec::new();
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            match child.kind() {
                "name" | "visibility" | "import_clause" | "export_clause" | "meta_block"
                | "description_block" => {}
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
            descriptions,
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
                        let mut cursor2 = child.walk();
                        for type_child in child.named_children(&mut cursor2) {
                            match type_child.kind() {
                                "simple_type" | "parameterized_type" | "variable_term" => {
                                    effects.push(Effect { type_expr: self.convert_type(type_child) });
                                }
                                _ => {}
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        let body = self.field(node, "body").map(|b| self.convert_expr_body(b));
        let meta = self.convert_meta_block(node);

        Some(Operation {
            visibility,
            name,
            params,
            return_type,
            requires,
            ensures,
            effects,
            body,
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

    // ── Requires declaration ──────────────────────────────────────

    fn convert_requires_decl(&mut self, node: Node) -> Option<RequiresDecl> {
        let span = self.span(node);
        let type_expr = self.field(node, "type")
            .map(|t| self.convert_type(t))?;
        Some(RequiresDecl { type_expr, span })
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
        let head = self.field(node, "head")
            .map(|b| self.convert_rule_body(b))
            .unwrap_or_default();
        let guard = self.field(node, "guard")
            .map(|b| self.convert_rule_body(b));
        let meta = self.convert_meta_block(node);
        Some(Constraint { label, head, guard, meta, span })
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
                        let mut cursor2 = child.walk();
                        for type_child in child.named_children(&mut cursor2) {
                            match type_child.kind() {
                                "simple_type" | "parameterized_type" | "variable_term" => {
                                    effects.push(Effect { type_expr: self.convert_type(type_child) });
                                }
                                _ => {}
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        let body = self.field(node, "body").map(|b| self.convert_expr_body(b));
        let meta = self.convert_meta_block(node);

        Some(Operation {
            visibility,
            name,
            params,
            return_type,
            requires,
            ensures,
            effects,
            body,
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

    // ── Describe ────────────────────────────────────────────────

    fn convert_describe(&mut self, node: Node) -> Option<Describe> {
        let target = self.field(node, "target")
            .map(|n| self.convert_name(n))?;
        let contents: Vec<String> = self.fields_by_name(node, "content")
            .into_iter()
            .map(|d| strip_description_delimiters(self.text(d)))
            .collect();
        let span = self.span(node);
        Some(Describe { target, contents, span })
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

    // ── Expressions ──────────────────────────────────────────────

    /// Convert an expression body node (match_expr, if_expr, let_expr,
    /// lambda_expr, or a plain term).
    fn convert_expr_body(&mut self, node: Node) -> TermId {
        match node.kind() {
            "match_expr" => self.convert_match_expr(node),
            "if_expr" => self.convert_if_expr(node),
            "let_expr" => self.convert_let_expr(node),
            "lambda_expr" => self.convert_lambda_expr(node),
            _ => self.convert_term(node),
        }
    }

    fn convert_match_expr(&mut self, node: Node) -> TermId {
        let scrutinee = self.field(node, "scrutinee")
            .map(|n| self.convert_term(n))
            .unwrap_or_else(|| self.terms.alloc(Term::Bottom));

        let mut pos_args: SmallVec<[TermId; 4]> = SmallVec::new();
        pos_args.push(scrutinee);
        for branch in self.children_by_kind(node, "match_branch") {
            pos_args.push(self.convert_match_branch(branch));
        }

        self.alloc_fn_term("match_expr", pos_args)
    }

    fn convert_match_branch(&mut self, node: Node) -> TermId {
        let pattern = self.field(node, "pattern")
            .map(|p| self.convert_pattern(p))
            .unwrap_or_else(|| self.terms.alloc(Term::Bottom));

        let body = self.field(node, "body")
            .map(|b| self.convert_expr_body(b))
            .unwrap_or_else(|| self.terms.alloc(Term::Bottom));

        self.alloc_fn_term("match_branch", SmallVec::from_slice(&[pattern, body]))
    }

    fn convert_if_expr(&mut self, node: Node) -> TermId {
        let condition = self.field(node, "condition")
            .map(|n| self.convert_term(n))
            .unwrap_or_else(|| self.terms.alloc(Term::Bottom));

        let then_branch = self.field(node, "then")
            .map(|n| self.convert_expr_body(n))
            .unwrap_or_else(|| self.terms.alloc(Term::Bottom));

        let else_branch = self.field(node, "else")
            .map(|n| self.convert_expr_body(n))
            .unwrap_or_else(|| self.terms.alloc(Term::Bottom));

        self.alloc_fn_term("if_expr", SmallVec::from_slice(&[condition, then_branch, else_branch]))
    }

    fn convert_let_expr(&mut self, node: Node) -> TermId {
        let pattern = self.field(node, "pattern")
            .map(|p| self.convert_pattern(p))
            .unwrap_or_else(|| self.terms.alloc(Term::Bottom));

        let value = self.field(node, "value")
            .map(|v| self.convert_expr_body(v))
            .unwrap_or_else(|| self.terms.alloc(Term::Bottom));

        let body = self.field(node, "body")
            .map(|b| self.convert_expr_body(b))
            .unwrap_or_else(|| self.terms.alloc(Term::Bottom));

        self.alloc_fn_term("let_expr", SmallVec::from_slice(&[pattern, value, body]))
    }

    fn convert_lambda_expr(&mut self, node: Node) -> TermId {
        let param = self.field(node, "param")
            .map(|p| self.convert_pattern(p))
            .unwrap_or_else(|| self.terms.alloc(Term::Bottom));

        let body = self.field(node, "body")
            .map(|b| self.convert_expr_body(b))
            .unwrap_or_else(|| self.terms.alloc(Term::Bottom));

        self.alloc_fn_term("lambda", SmallVec::from_slice(&[param, body]))
    }

    // ── Patterns ─────────────────────────────────────────────────

    fn convert_pattern(&mut self, node: Node) -> TermId {
        match node.kind() {
            "pattern_wildcard" => {
                self.alloc_fn_term("pattern_wildcard", SmallVec::new())
            }
            "pattern_var" | "identifier" => {
                let id_node = self.child_by_kind(node, "identifier").unwrap_or(node);
                let sym = self.intern(self.text(id_node));
                let name_tid = self.terms.alloc(Term::Ident(sym));
                self.alloc_fn_term("pattern_var", SmallVec::from_elem(name_tid, 1))
            }
            "pattern_literal" => {
                let child = node.named_child(0).unwrap_or(node);
                let lit_tid = self.convert_term(child);
                self.alloc_fn_term("pattern_literal", SmallVec::from_elem(lit_tid, 1))
            }
            "pattern_constructor" => {
                let name_node = self.field(node, "name").unwrap_or(node);
                let name = self.convert_name(name_node);
                let name_sym = self.intern_name(&name);
                let name_tid = self.terms.alloc(Term::Ident(name_sym));

                let mut pos_args: SmallVec<[TermId; 4]> = SmallVec::new();
                pos_args.push(name_tid);
                let mut cursor = node.walk();
                for child in node.named_children(&mut cursor) {
                    if is_pattern_kind(child.kind()) {
                        pos_args.push(self.convert_pattern(child));
                    }
                }

                self.alloc_fn_term("pattern_constructor", pos_args)
            }
            "pattern_tuple" => {
                let mut pos_args: SmallVec<[TermId; 4]> = SmallVec::new();
                let mut cursor = node.walk();
                for child in node.named_children(&mut cursor) {
                    if is_pattern_kind(child.kind()) {
                        pos_args.push(self.convert_pattern(child));
                    }
                }

                self.alloc_fn_term("pattern_tuple", pos_args)
            }
            other => {
                self.err(format!("unexpected pattern node: {other}"), node);
                self.terms.alloc(Term::Bottom)
            }
        }
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
            | "variable_term"
            | "fn_term"
            | "instantiation_term"
            | "ref_term"
            | "infix_term"
            | "prefix_term"
            | "field_access"
            | "set_literal"
            | "tuple_literal"
            | "paren_expr"
            | "identifier"
    )
}

/// Check if a node kind is a pattern.
fn is_pattern_kind(kind: &str) -> bool {
    matches!(
        kind,
        "pattern_wildcard"
            | "pattern_var"
            | "pattern_literal"
            | "pattern_constructor"
            | "pattern_tuple"
    )
}

/// Strip `{<` and `>}` delimiters from a description block token.
fn strip_description_delimiters(raw: &str) -> String {
    let trimmed = raw.trim();
    let inner = trimmed
        .strip_prefix("{<")
        .and_then(|s| s.strip_suffix(">}"))
        .unwrap_or(trimmed);
    inner.trim().to_string()
}

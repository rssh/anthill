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
use crate::kb::term::{Term, TermId, Literal, Var, VarId};

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

/// Work-stack opcode for the iterative CST → IR walker covering
/// term / expression-body / pattern subtrees. `Visit` dispatches a
/// tree-sitter node (leaf → emit TermId; non-leaf → push a `Build`
/// frame + child Visits). `Build` consumes already-converted
/// children from the result stack and assembles the parent. Mirrors
/// the post-WI-253 NodeOccurrence materializer / kb/load.rs
/// expression loader pattern, keeping host stack O(1) regardless of
/// source nesting depth.
#[derive(Copy, Clone)]
enum WorkKind {
    Term,
    ExprBody,
    Pattern,
}

enum WorkOp<'t> {
    Visit(WorkKind, Node<'t>),
    Build(BuildFrame<'t>),
    /// Push a precomputed TermId to the result stack when this op
    /// pops. Lets `visit_*` stand in a synthetic Bottom for a missing
    /// optional child without violating sibling result-stack ordering
    /// (`results.push(bot)` inline would land bot at the wrong slot
    /// relative to its sibling Visits, which haven't yet popped).
    Yield(TermId),
}

/// One slot in a function-application / tuple / pattern-constructor
/// argument list. Positional slots consume the next result; named
/// slots carry the field-name symbol and consume one result.
#[derive(Copy, Clone)]
enum ArgSlot {
    Positional,
    Named(Symbol),
}

/// One slot in an infix chain. Operands consume the next result;
/// operator slots carry the operator's source text (heap-allocated
/// because tree-sitter Node lifetimes don't outlive the build phase).
enum InfixSlot {
    Operand,
    Operator(String),
}

enum BuildFrame<'t> {
    // ── Term-side frames ────────────────────────────────────────
    FnTerm {
        node: Node<'t>,
        is_ho: bool,
        functor: Symbol,
        slots: SmallVec<[ArgSlot; 4]>,
        /// Bindings collected off an `instantiation_term` callee
        /// (`op[bindings](args)`); empty for the untyped form.
        type_args: Vec<SortBinding>,
    },
    Infix {
        node: Node<'t>,
        slots: SmallVec<[InfixSlot; 8]>,
    },
    Prefix {
        node: Node<'t>,
        op_text: String,
    },
    FieldAccess {
        node: Node<'t>,
        field_sym: Symbol,
        field_span: Span,
    },
    /// Value-receiver dot form (WI-278): `?x.field` (no args, `slots`
    /// empty) or `?x.method(args)`. Emitted as `dot_apply(receiver,
    /// Ident(name), ...args)` so the receiver is preserved (the old
    /// `collect_field_access_segments` flatten dropped it) and the
    /// `[simp]` dot rules can dispatch on the receiver's sort. Only
    /// `variable` receivers route here; `Foo.bar` keeps qualified-name
    /// flattening.
    DotApply {
        node: Node<'t>,
        name_sym: Symbol,
        name_span: Span,
        slots: SmallVec<[ArgSlot; 4]>,
    },
    SetLiteral {
        node: Node<'t>,
        count: usize,
    },
    CollectionLiteral {
        node: Node<'t>,
        elem_count: usize,
        has_tail: bool,
    },
    TupleLiteral {
        node: Node<'t>,
        slots: SmallVec<[ArgSlot; 4]>,
    },
    // ── Expression-body frames ──────────────────────────────────
    MatchExpr {
        node: Node<'t>,
        branch_count: usize,
    },
    MatchBranch {
        node: Node<'t>,
    },
    IfExpr {
        node: Node<'t>,
    },
    LetExpr {
        node: Node<'t>,
        type_anno: Option<TypeExpr>,
    },
    LambdaExpr {
        node: Node<'t>,
    },
    // ── Pattern frames ──────────────────────────────────────────
    PatternLiteral {
        node: Node<'t>,
    },
    PatternConstructor {
        node: Node<'t>,
        name_tid: TermId,
        slots: SmallVec<[ArgSlot; 4]>,
    },
    PatternTuple {
        node: Node<'t>,
        count: usize,
    },
}

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
    /// Snapshot of each labeled rule's final var_scope, keyed by the
    /// rule's label symbol (proposal 031). Lets a subsequent
    /// `convert_proof` for the same target restore the parent rule's
    /// scope so structured-proof step variables that share source
    /// names with the parent (`?d_prev`, `?delta`, …) get the SAME
    /// VarId — the lift's forall quantification then ranges over the
    /// PARENT's vars, so the step's claim chains arithmetically with
    /// the parent's body in the consumer's SMT preamble.
    rule_var_scopes: HashMap<Symbol, HashMap<Symbol, VarId>>,
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
            rule_var_scopes: HashMap::new(),
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
    fn alloc_fn_term(
        &mut self,
        functor_name: &str,
        pos_args: SmallVec<[TermId; 4]>,
        span: Span,
    ) -> TermId {
        let functor = self.intern(functor_name);
        self.terms.alloc(
            Term::Fn {
                functor,
                pos_args,
                named_args: SmallVec::new(),
            },
            span,
        )
    }

    /// Bottom-term factory for error/unwrap_or_else paths.
    fn alloc_bottom(&mut self, span: Span) -> TermId {
        self.terms.alloc(Term::Bottom, span)
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
            "sort_with_body" => self.convert_sort_like(node, SortDeclKind::Sort).map(Item::SortWithBody),
            "enum_declaration" => self.convert_sort_like(node, SortDeclKind::Enum).map(Item::SortWithBody),
            "rule_declaration" => self.convert_rule(node).map(Item::Rule),
            "operation_declaration" => self.convert_operation(node).map(Item::Operation),
            "requires_declaration" => self.convert_requires_decl(node).map(Item::RequiresDecl),
            "entity_declaration" => self.convert_entity(node).map(Item::Entity),
            "fact_declaration" => self.convert_fact(node).map(Item::Fact),
            "constraint_declaration" => self.convert_constraint(node).map(Item::Constraint),
            "operation_block" => self.convert_operation_block(node).map(Item::OperationBlock),
            "rule_block" => self.convert_rule_block(node).map(Item::RuleBlock),
            "describe_declaration" => self.convert_describe(node).map(Item::Describe),
            "proof_declaration" => self.convert_proof(node).map(Item::Proof),
            "provides_clause" => self.convert_provides_clause(node).map(Item::ProvidesClause),
            "provides_block" => self.convert_provides_block(node).map(Item::ProvidesBlock),
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
        if node.kind() == "field_access" {
            self.collect_field_access_segments(node, &mut segments);
            return Name { segments, span };
        }
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

    fn collect_field_access_segments(
        &mut self,
        node: Node,
        segments: &mut SmallVec<[Symbol; 2]>,
    ) {
        let object = self.field(node, "object");
        let field = self.field(node, "field");
        if let Some(o) = object {
            if o.kind() == "field_access" {
                self.collect_field_access_segments(o, segments);
            } else if o.kind() == "identifier" {
                let sym = self.intern(self.text(o));
                segments.push(sym);
            } else if o.kind() == "instantiation_term" {
                // Form (3) of proposal 035: `Map[K = String, V = Int].empty()`.
                // The instantiation term names a sort with type bindings; for
                // the runtime call path we only need the sort's name segment
                // (bindings are erased). The type checker reads the bindings
                // via the original node when it walks the call site.
                let inst_name = self.field(o, "name").unwrap_or(o);
                let sym = self.intern(self.text(inst_name));
                segments.push(sym);
            }
        }
        if let Some(f) = field {
            let sym = self.intern(self.text(f));
            segments.push(sym);
        }
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
            // Named: Eq[T = Int] — param and type both present
            (Some(p), Some(t)) => SortBinding { param: Some(p), bound: self.convert_type(t) },
            // Positional: List[Int] or List[T] — no `=`, value binds to next param
            (Some(p), None) => {
                let bound = TypeExpr::Simple(p);
                SortBinding { param: None, bound }
            }
            // Variable: Modify[?] or Modify[?r] — positional with variable type
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
        self.convert_expr_iter(node, WorkKind::Term)
    }

    /// Iterative CST→IR walker. Single entry point for the recursive
    /// term / expression-body / pattern subtree converters; runs a
    /// work-stack loop so host stack usage stays O(1) regardless of
    /// source nesting depth. Each `Visit(kind, node)` dispatches by
    /// kind+`node.kind()` to either emit a leaf TermId or push a
    /// `Build` frame + child `Visit`s; `Build` frames consume
    /// already-converted children from the result stack and assemble
    /// the parent.
    fn convert_expr_iter<'t>(&mut self, root: Node<'t>, init_kind: WorkKind) -> TermId {
        let mut work: Vec<WorkOp<'t>> = Vec::with_capacity(64);
        let mut results: Vec<TermId> = Vec::with_capacity(64);
        work.push(WorkOp::Visit(init_kind, root));
        while let Some(op) = work.pop() {
            match op {
                WorkOp::Visit(kind, node) => match kind {
                    WorkKind::Term => self.visit_term(node, &mut work, &mut results),
                    WorkKind::ExprBody => self.visit_expr_body(node, &mut work, &mut results),
                    WorkKind::Pattern => self.visit_pattern(node, &mut work, &mut results),
                },
                WorkOp::Build(frame) => self.build_parse(frame, &mut results),
                WorkOp::Yield(tid) => results.push(tid),
            }
        }
        debug_assert_eq!(results.len(), 1, "iterative parse: expected exactly one result");
        results.pop().expect("iterative parse: empty result stack")
    }

    /// Dispatch a single parse-time term node: produce a leaf TermId
    /// directly or push a `Build` frame + child `Visit`s.
    fn visit_term<'t>(
        &mut self,
        node: Node<'t>,
        work: &mut Vec<WorkOp<'t>>,
        results: &mut Vec<TermId>,
    ) {
        let span = self.span(node);
        match node.kind() {
            "string_literal" => {
                let term = Term::Const(Literal::String(decode_string_lit(self.text(node))));
                results.push(self.terms.alloc(term, span));
            }
            "integer_literal" => {
                let text = self.text(node);
                let tid = if let Ok(n) = text.parse::<i64>() {
                    self.terms.alloc(Term::Const(Literal::Int(n)), span)
                } else if let Ok(big) = text.parse::<num_bigint::BigInt>() {
                    self.terms.alloc(Term::Const(Literal::BigInt(big)), span)
                } else {
                    self.err(format!("invalid integer: {text}"), node);
                    self.terms.alloc(Term::Const(Literal::Int(0)), span)
                };
                results.push(tid);
            }
            "float_literal" => {
                let text = self.text(node);
                let tid = match text.parse::<f64>() {
                    Ok(f) => self.terms.alloc(Term::Const(Literal::Float(OrderedFloat(f))), span),
                    Err(_) => {
                        self.err(format!("invalid float: {text}"), node);
                        self.terms.alloc(Term::Const(Literal::Float(OrderedFloat(0.0))), span)
                    }
                };
                results.push(tid);
            }
            "boolean_literal" => {
                let b = self.text(node) == "true";
                results.push(self.terms.alloc(Term::Const(Literal::Bool(b)), span));
            }
            "variable" => {
                let tid = self.convert_variable_node(node);
                results.push(tid);
            }
            "variable_term" => {
                let var_node = self.child_by_kind(node, "variable").unwrap_or(node);
                let tid = self.convert_variable_node(var_node);
                let descs: Vec<String> = self.fields_by_name(node, "description")
                    .into_iter()
                    .map(|d| strip_description_delimiters(self.text(d)))
                    .collect();
                if !descs.is_empty() {
                    self.terms.descriptions.insert(tid, descs);
                }
                results.push(tid);
            }
            "fn_term" => self.push_fn_term(node, work),
            "nested_implication" => {
                // Rare in expression contexts (rule bodies only) — stays
                // recursive since `convert_rule_body` re-enters
                // `convert_term` per goal and per-goal depth is bounded
                // by rule structure rather than nested expressions.
                let tid = self.convert_nested_implication(node);
                results.push(tid);
            }
            "instantiation_term" => {
                // Type values are shallow in practice (`Function[A=T, B=U,
                // E=Es]`); the recursive `convert_instantiation_term`
                // stays.
                let tid = self.convert_instantiation_term(node);
                results.push(tid);
            }
            "ref_term" => {
                let name_node = self.child_by_kind(node, "name");
                let sym = if let Some(n) = name_node {
                    let name = self.convert_name(n);
                    self.intern_name(&name)
                } else {
                    self.intern("?")
                };
                results.push(self.terms.alloc(Term::Ref(sym), span));
            }
            "infix_term" => self.push_infix(node, work),
            "prefix_term" => self.push_prefix(node, work, results),
            "field_access" => self.push_field_access(node, work),
            "set_literal" => self.push_set_literal(node, work),
            "collection_literal" => self.push_collection_literal(node, work),
            "tuple_literal" => self.push_tuple_literal(node, work),
            "paren_expr" => {
                let inner = node.named_child(0).unwrap_or(node);
                work.push(WorkOp::Visit(WorkKind::Term, inner));
            }
            "identifier" => {
                let sym = self.intern(self.text(node));
                results.push(self.terms.alloc(Term::Ident(sym), span));
            }
            other => {
                self.err(format!("unexpected term node: {other}"), node);
                results.push(self.alloc_bottom(span));
            }
        }
    }

    fn push_fn_term<'t>(&mut self, node: Node<'t>, work: &mut Vec<WorkOp<'t>>) {
        let name_node = self.field(node, "name").unwrap_or(node);
        // WI-278: a method call `?x.method(args)` parses as an fn_term whose
        // callee is a `field_access` over a value receiver. Route it to
        // `dot_apply` (preserving the receiver the old flatten dropped).
        // `Foo.bar(...)` (name receiver) falls through to the normal call.
        if name_node.kind() == "field_access" {
            if let Some(receiver) = self.field(name_node, "object") {
                if self.is_value_receiver(receiver) {
                    self.push_dot_method_call(node, name_node, receiver, work);
                    return;
                }
            }
        }
        let is_ho = name_node.kind() == "variable";
        let functor = if is_ho {
            self.intern("ho_apply")
        } else {
            let name = self.convert_name(name_node);
            self.intern_name(&name)
        };

        // Side-channel for the typer at `Name[bindings](args)` callees.
        let type_args: Vec<SortBinding> = if name_node.kind() == "instantiation_term" {
            self.children_by_kind(name_node, "sort_binding")
                .into_iter()
                .map(|b| self.convert_sort_binding(b))
                .collect()
        } else {
            Vec::new()
        };

        // Collect child layout (positional vs named with key) and the
        // ordered list of child nodes whose TermIds the Build phase
        // will consume. For HO predicates the variable head slot is
        // a positional leaf; emit it directly to results in pushed
        // order so it doesn't need a Visit op.
        let mut slots: SmallVec<[ArgSlot; 4]> = SmallVec::new();
        let mut child_nodes: SmallVec<[Node<'t>; 4]> = SmallVec::new();
        if is_ho {
            // The HO head is a `variable` leaf; treat it as a positional
            // child that requires a Visit so we don't have to specialize
            // build assembly. Each operand still produces a single TermId.
            slots.push(ArgSlot::Positional);
            child_nodes.push(name_node);
        }
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            if child == name_node {
                continue;
            }
            match child.kind() {
                "named_arg" => {
                    let key_node = self.field(child, "name");
                    let val_node = self.field(child, "value");
                    if let (Some(k), Some(v)) = (key_node, val_node) {
                        let sym = self.intern(self.text(k));
                        slots.push(ArgSlot::Named(sym));
                        child_nodes.push(v);
                    }
                }
                k if is_term_kind(k) => {
                    slots.push(ArgSlot::Positional);
                    child_nodes.push(child);
                }
                _ => {}
            }
        }

        work.push(WorkOp::Build(BuildFrame::FnTerm { node, is_ho, functor, slots, type_args }));
        for child in child_nodes.iter().rev() {
            work.push(WorkOp::Visit(WorkKind::Term, *child));
        }
    }

    /// WI-278: a value-receiver method call `receiver.name(args)` —
    /// `node` is the fn_term, `name_node` its `field_access` callee,
    /// `receiver` the callee's value object. Collect the call's args
    /// (positional + named, excluding the callee) and emit `dot_apply`.
    fn push_dot_method_call<'t>(
        &mut self,
        node: Node<'t>,
        name_node: Node<'t>,
        receiver: Node<'t>,
        work: &mut Vec<WorkOp<'t>>,
    ) {
        let field_node = self.field(name_node, "field").unwrap_or(name_node);
        let name_span = self.span(field_node);
        let name_sym = self.intern(self.text(field_node));
        let mut slots: SmallVec<[ArgSlot; 4]> = SmallVec::new();
        let mut child_nodes: SmallVec<[Node<'t>; 4]> = SmallVec::new();
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            if child == name_node {
                continue;
            }
            match child.kind() {
                "named_arg" => {
                    let key_node = self.field(child, "name");
                    let val_node = self.field(child, "value");
                    if let (Some(k), Some(v)) = (key_node, val_node) {
                        let sym = self.intern(self.text(k));
                        slots.push(ArgSlot::Named(sym));
                        child_nodes.push(v);
                    }
                }
                k if is_term_kind(k) => {
                    slots.push(ArgSlot::Positional);
                    child_nodes.push(child);
                }
                _ => {}
            }
        }
        work.push(WorkOp::Build(BuildFrame::DotApply { node, name_sym, name_span, slots }));
        // Args pushed reversed, then the receiver last so it pops (and lands
        // on the result stack) first — matching the DotApply build's drain.
        for child in child_nodes.iter().rev() {
            work.push(WorkOp::Visit(WorkKind::Term, *child));
        }
        work.push(WorkOp::Visit(WorkKind::Term, receiver));
    }

    fn push_infix<'t>(&mut self, node: Node<'t>, work: &mut Vec<WorkOp<'t>>) {
        let mut slots: SmallVec<[InfixSlot; 8]> = SmallVec::new();
        let mut operand_nodes: SmallVec<[Node<'t>; 4]> = SmallVec::new();
        for i in 0..node.child_count() {
            let Some(child) = node.child(i) else { continue };
            let kind = child.kind();
            if kind == "operator_symbol" {
                slots.push(InfixSlot::Operator(self.text(child).to_string()));
            } else if is_term_kind(kind) || kind == "prefix_term" {
                slots.push(InfixSlot::Operand);
                operand_nodes.push(child);
            } else if !child.is_named() {
                let text = self.text(child);
                if text != "," {
                    slots.push(InfixSlot::Operator(text.to_string()));
                }
            }
        }
        work.push(WorkOp::Build(BuildFrame::Infix { node, slots }));
        for child in operand_nodes.iter().rev() {
            work.push(WorkOp::Visit(WorkKind::Term, *child));
        }
    }

    fn push_prefix<'t>(
        &mut self,
        node: Node<'t>,
        work: &mut Vec<WorkOp<'t>>,
        results: &mut Vec<TermId>,
    ) {
        let mut op_text: Option<String> = None;
        let mut operand_node: Option<Node<'t>> = None;
        for i in 0..node.child_count() {
            let Some(child) = node.child(i) else { continue };
            let kind = child.kind();
            if is_term_kind(kind) || kind == "prefix_term" {
                operand_node = Some(child);
            } else if op_text.is_none() {
                op_text = Some(self.text(child).to_string());
            }
        }
        let op_text = op_text.unwrap_or_else(|| "!".to_string());
        work.push(WorkOp::Build(BuildFrame::Prefix { node, op_text }));
        match operand_node {
            Some(operand) => work.push(WorkOp::Visit(WorkKind::Term, operand)),
            None => {
                // Unreachable from valid grammar; emit a Bottom directly
                // so the Prefix Build drains a slot rather than panicking.
                let span = self.span(node);
                results.push(self.terms.alloc(Term::Bottom, span));
            }
        }
    }

    /// Whether a dot receiver denotes a runtime *value* (→ `dot_apply`) vs a
    /// sort/namespace *name* (→ qualified-name flattening / field_access).
    /// Walks the receiver down its `field_access` / `paren_expr` chain to the
    /// root atom: a name iff that root is an `identifier` or `instantiation_term`
    /// (`Foo.bar`, `Map[K=…].empty`, the deferred `p.x` identifier case); a
    /// value otherwise (`?x`, a call result like `xs.map(f)`, a literal, …).
    /// WI-278; the chain walk is what lets `?x.y.z` and `?xs.map(?f).filter(?p)`
    /// route every level to `dot_apply` rather than dropping the receiver.
    fn is_value_receiver(&self, node: Node) -> bool {
        let mut cur = node;
        loop {
            match cur.kind() {
                "field_access" => match self.field(cur, "object") {
                    Some(o) => cur = o,
                    None => return false,
                },
                "paren_expr" => match cur.named_child(0) {
                    Some(inner) => cur = inner,
                    None => return true,
                },
                "identifier" | "instantiation_term" => return false,
                _ => return true,
            }
        }
    }

    fn push_field_access<'t>(&mut self, node: Node<'t>, work: &mut Vec<WorkOp<'t>>) {
        let object_node = self.field(node, "object").unwrap_or(node);
        let field_node = self.field(node, "field").unwrap_or(node);
        let field_span = self.span(field_node);
        let field_sym = self.intern(self.text(field_node));
        // WI-278: `?x.field` (value receiver) becomes `dot_apply(?x, field)`
        // with no args; non-value receivers keep the field_access builtin.
        if self.is_value_receiver(object_node) {
            work.push(WorkOp::Build(BuildFrame::DotApply {
                node,
                name_sym: field_sym,
                name_span: field_span,
                slots: SmallVec::new(),
            }));
        } else {
            work.push(WorkOp::Build(BuildFrame::FieldAccess { node, field_sym, field_span }));
        }
        work.push(WorkOp::Visit(WorkKind::Term, object_node));
    }

    fn push_set_literal<'t>(&mut self, node: Node<'t>, work: &mut Vec<WorkOp<'t>>) {
        let mut elements: SmallVec<[Node<'t>; 4]> = SmallVec::new();
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            if is_term_kind(child.kind()) {
                elements.push(child);
            }
        }
        let count = elements.len();
        work.push(WorkOp::Build(BuildFrame::SetLiteral { node, count }));
        for child in elements.iter().rev() {
            work.push(WorkOp::Visit(WorkKind::Term, *child));
        }
    }

    fn push_collection_literal<'t>(&mut self, node: Node<'t>, work: &mut Vec<WorkOp<'t>>) {
        let tail_node = self.field(node, "tail");
        let mut elements: SmallVec<[Node<'t>; 4]> = SmallVec::new();
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            if is_term_kind(child.kind()) && tail_node != Some(child) {
                elements.push(child);
            }
        }
        let elem_count = elements.len();
        let has_tail = tail_node.is_some();
        work.push(WorkOp::Build(BuildFrame::CollectionLiteral { node, elem_count, has_tail }));
        if let Some(t) = tail_node {
            work.push(WorkOp::Visit(WorkKind::Term, t));
        }
        for child in elements.iter().rev() {
            work.push(WorkOp::Visit(WorkKind::Term, *child));
        }
    }

    fn push_tuple_literal<'t>(&mut self, node: Node<'t>, work: &mut Vec<WorkOp<'t>>) {
        let mut slots: SmallVec<[ArgSlot; 4]> = SmallVec::new();
        let mut child_nodes: SmallVec<[Node<'t>; 4]> = SmallVec::new();
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            match child.kind() {
                "named_arg" => {
                    let key_node = self.field(child, "name");
                    let val_node = self.field(child, "value");
                    if let (Some(k), Some(v)) = (key_node, val_node) {
                        let sym = self.intern(self.text(k));
                        slots.push(ArgSlot::Named(sym));
                        child_nodes.push(v);
                    }
                }
                k if is_term_kind(k) => {
                    slots.push(ArgSlot::Positional);
                    child_nodes.push(child);
                }
                _ => {}
            }
        }
        work.push(WorkOp::Build(BuildFrame::TupleLiteral { node, slots }));
        for child in child_nodes.iter().rev() {
            work.push(WorkOp::Visit(WorkKind::Term, *child));
        }
    }

    /// Dispatch a single parse-time expression-body node. Falls
    /// through to `visit_term` for anything that isn't one of the
    /// recognized expression-body kinds.
    fn visit_expr_body<'t>(
        &mut self,
        node: Node<'t>,
        work: &mut Vec<WorkOp<'t>>,
        results: &mut Vec<TermId>,
    ) {
        match node.kind() {
            "match_expr" => {
                let scrutinee = self.field(node, "scrutinee");
                let branches: SmallVec<[Node<'t>; 4]> =
                    self.children_by_kind(node, "match_branch").into_iter().collect();
                let branch_count = branches.len();
                work.push(WorkOp::Build(BuildFrame::MatchExpr { node, branch_count }));
                for branch in branches.iter().rev() {
                    let pattern = self.field(*branch, "pattern");
                    let body = self.field(*branch, "body");
                    let branch_span = self.span(*branch);
                    work.push(WorkOp::Build(BuildFrame::MatchBranch { node: *branch }));
                    self.push_child_or_yield(work, body, WorkKind::ExprBody, branch_span);
                    self.push_child_or_yield(work, pattern, WorkKind::Pattern, branch_span);
                }
                let node_span = self.span(node);
                self.push_child_or_yield(work, scrutinee, WorkKind::Term, node_span);
            }
            "if_expr" => {
                let cond = self.field(node, "condition");
                let then_b = self.field(node, "then");
                let else_b = self.field(node, "else");
                let span = self.span(node);
                work.push(WorkOp::Build(BuildFrame::IfExpr { node }));
                self.push_child_or_yield(work, else_b, WorkKind::ExprBody, span);
                self.push_child_or_yield(work, then_b, WorkKind::ExprBody, span);
                self.push_child_or_yield(work, cond, WorkKind::Term, span);
            }
            "let_chain" => {
                let pattern = self.field(node, "pattern");
                let value = self.field(node, "value");
                let body = self.field(node, "body");
                let type_anno = self.field(node, "type").map(|t| self.convert_type(t));
                let span = self.span(node);
                work.push(WorkOp::Build(BuildFrame::LetExpr { node, type_anno }));
                self.push_child_or_yield(work, body, WorkKind::ExprBody, span);
                self.push_child_or_yield(work, value, WorkKind::ExprBody, span);
                self.push_child_or_yield(work, pattern, WorkKind::Pattern, span);
            }
            "lambda_expr" => {
                let param = self.field(node, "param");
                let body = self.field(node, "body");
                let span = self.span(node);
                work.push(WorkOp::Build(BuildFrame::LambdaExpr { node }));
                self.push_child_or_yield(work, body, WorkKind::ExprBody, span);
                self.push_child_or_yield(work, param, WorkKind::Pattern, span);
            }
            _ => self.visit_term(node, work, results),
        }
    }

    /// Dispatch a single parse-time pattern node.
    fn visit_pattern<'t>(
        &mut self,
        node: Node<'t>,
        work: &mut Vec<WorkOp<'t>>,
        results: &mut Vec<TermId>,
    ) {
        let span = self.span(node);
        match node.kind() {
            "pattern_wildcard" => {
                let tid = self.alloc_fn_term("pattern_wildcard", SmallVec::new(), span);
                results.push(tid);
            }
            "pattern_var" | "identifier" => {
                let id_node = self.child_by_kind(node, "identifier").unwrap_or(node);
                let sym = self.intern(self.text(id_node));
                let name_tid = self.terms.alloc(Term::Ident(sym), self.span(id_node));
                let tid = self.alloc_fn_term("pattern_var", SmallVec::from_elem(name_tid, 1), span);
                results.push(tid);
            }
            "pattern_literal" => {
                let child = node.named_child(0).unwrap_or(node);
                work.push(WorkOp::Build(BuildFrame::PatternLiteral { node }));
                work.push(WorkOp::Visit(WorkKind::Term, child));
            }
            "pattern_constructor" => {
                let name_node = self.field(node, "name").unwrap_or(node);
                let name_span = self.span(name_node);
                let name = self.convert_name(name_node);
                let name_sym = self.intern_name(&name);
                let name_tid = self.terms.alloc(Term::Ident(name_sym), name_span);

                let mut slots: SmallVec<[ArgSlot; 4]> = SmallVec::new();
                let mut child_ops: SmallVec<[WorkOp<'t>; 4]> = SmallVec::new();
                let mut cursor = node.walk();
                for child in node.named_children(&mut cursor) {
                    if child.kind() == "named_pattern_field" {
                        let field_name = self.field(child, "field_name")
                            .map(|n| self.intern(self.text(n)))
                            .unwrap_or_else(|| self.intern("_"));
                        slots.push(ArgSlot::Named(field_name));
                        match self.field(child, "field_pattern") {
                            Some(p) => child_ops.push(WorkOp::Visit(WorkKind::Pattern, p)),
                            None => {
                                let bot = self.alloc_bottom(self.span(child));
                                child_ops.push(WorkOp::Yield(bot));
                            }
                        }
                    } else if is_pattern_kind(child.kind()) {
                        slots.push(ArgSlot::Positional);
                        child_ops.push(WorkOp::Visit(WorkKind::Pattern, child));
                    }
                }
                work.push(WorkOp::Build(BuildFrame::PatternConstructor {
                    node,
                    name_tid,
                    slots,
                }));
                for op in child_ops.into_iter().rev() {
                    work.push(op);
                }
            }
            "pattern_tuple" => {
                let mut child_nodes: SmallVec<[Node<'t>; 4]> = SmallVec::new();
                let mut cursor = node.walk();
                for child in node.named_children(&mut cursor) {
                    if is_pattern_kind(child.kind()) {
                        child_nodes.push(child);
                    }
                }
                let count = child_nodes.len();
                work.push(WorkOp::Build(BuildFrame::PatternTuple { node, count }));
                for child in child_nodes.iter().rev() {
                    work.push(WorkOp::Visit(WorkKind::Pattern, *child));
                }
            }
            other => {
                self.err(format!("unexpected pattern node: {other}"), node);
                results.push(self.alloc_bottom(span));
            }
        }
    }

    /// Push a child `Visit(kind, node)` if the child node exists, or
    /// a `Yield(Bottom)` placeholder so the Build frame still drains a
    /// slot in the right order. Direct `results.push` would land the
    /// Bottom at the current end-of-stack, which breaks ordering once
    /// sibling Visits later push their own results.
    fn push_child_or_yield<'t>(
        &mut self,
        work: &mut Vec<WorkOp<'t>>,
        child: Option<Node<'t>>,
        kind: WorkKind,
        fallback_span: Span,
    ) {
        match child {
            Some(n) => work.push(WorkOp::Visit(kind, n)),
            None => {
                let bot = self.alloc_bottom(fallback_span);
                work.push(WorkOp::Yield(bot));
            }
        }
    }

    /// Assemble a parent TermId from its already-converted children.
    fn build_parse<'t>(&mut self, frame: BuildFrame<'t>, results: &mut Vec<TermId>) {
        match frame {
            BuildFrame::FnTerm { node, is_ho, functor, slots, type_args } => {
                let span = self.span(node);
                let drain_start = results.len() - slots.len();
                let mut pos_args: SmallVec<[TermId; 4]> = SmallVec::new();
                let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
                for (i, slot) in slots.iter().enumerate() {
                    let value = results[drain_start + i];
                    match slot {
                        ArgSlot::Positional => pos_args.push(value),
                        ArgSlot::Named(sym) => named_args.push((*sym, value)),
                    }
                }
                results.truncate(drain_start);
                let _ = is_ho;
                // WI-271: embed `op[A = Int, B = String]` call-site
                // bindings inline as a `type_args` named-arg child
                // pointing at a `Term::ParseAux(SortBindings(...))`
                // node — replaces the prior
                // `SimpleTermStore::call_type_args` HashMap. The loader
                // unwraps and lowers it via the existing build path.
                if !type_args.is_empty() {
                    let aux = Term::ParseAux(Box::new(
                        super::ir::ParseAux::SortBindings(type_args),
                    ));
                    let aux_tid = self.terms.alloc(aux, span);
                    let type_args_key = self.intern("type_args");
                    named_args.push((type_args_key, aux_tid));
                }
                let tid = self.terms.alloc(
                    Term::Fn { functor, pos_args, named_args },
                    span,
                );
                results.push(tid);
            }
            BuildFrame::Infix { node, slots } => {
                use super::pratt::{InfixElement, desugar_infix_chain};
                let span = self.span(node);
                let operand_count = slots.iter().filter(|s| matches!(s, InfixSlot::Operand)).count();
                let drain_start = results.len() - operand_count;
                let mut elements: Vec<InfixElement<'_>> = Vec::with_capacity(slots.len());
                let mut op_idx = 0;
                for slot in slots.iter() {
                    match slot {
                        InfixSlot::Operand => {
                            elements.push(InfixElement::Operand(results[drain_start + op_idx]));
                            op_idx += 1;
                        }
                        InfixSlot::Operator(text) => {
                            elements.push(InfixElement::Operator(text.as_str()));
                        }
                    }
                }
                let tid = match desugar_infix_chain(&elements, &mut self.terms, &mut self.symbols) {
                    Ok(tid) => tid,
                    Err(msg) => {
                        self.err(format!("infix desugaring: {msg}"), node);
                        self.alloc_bottom(span)
                    }
                };
                results.truncate(drain_start);
                results.push(tid);
            }
            BuildFrame::Prefix { node, op_text } => {
                use super::pratt::prefix_entry;
                let span = self.span(node);
                let operand = results.pop().expect("prefix: missing operand on result stack");
                let functor_name = match prefix_entry(&op_text) {
                    Some(entry) => entry.functor,
                    None => {
                        self.err(format!("unknown prefix operator: {op_text}"), node);
                        "not"
                    }
                };
                let functor = self.intern(functor_name);
                results.push(self.terms.alloc(
                    Term::Fn {
                        functor,
                        pos_args: SmallVec::from_elem(operand, 1),
                        named_args: SmallVec::new(),
                    },
                    span,
                ));
            }
            BuildFrame::FieldAccess { node, field_sym, field_span } => {
                let span = self.span(node);
                let object = results.pop().expect("field_access: missing object");
                let field_tid = self.terms.alloc(Term::Ident(field_sym), field_span);
                let functor = self.intern("field_access");
                results.push(self.terms.alloc(
                    Term::Fn {
                        functor,
                        pos_args: SmallVec::from_slice(&[object, field_tid]),
                        named_args: SmallVec::new(),
                    },
                    span,
                ));
            }
            BuildFrame::DotApply { node, name_sym, name_span, slots } => {
                // Result layout (drain_start..): receiver, then one entry per
                // slot in source order. Parse shape:
                // `dot_apply(receiver, Ident(name), ...positional, named...)`.
                let span = self.span(node);
                let drain_start = results.len() - (1 + slots.len());
                let receiver = results[drain_start];
                let name_tid = self.terms.alloc(Term::Ident(name_sym), name_span);
                let mut pos_args: SmallVec<[TermId; 4]> = SmallVec::new();
                pos_args.push(receiver);
                pos_args.push(name_tid);
                let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
                for (i, slot) in slots.iter().enumerate() {
                    let value = results[drain_start + 1 + i];
                    match slot {
                        ArgSlot::Positional => pos_args.push(value),
                        ArgSlot::Named(sym) => named_args.push((*sym, value)),
                    }
                }
                results.truncate(drain_start);
                let functor = self.intern("dot_apply");
                results.push(self.terms.alloc(Term::Fn { functor, pos_args, named_args }, span));
            }
            BuildFrame::SetLiteral { node, count } => {
                let span = self.span(node);
                let drain_start = results.len() - count;
                let elements: SmallVec<[TermId; 4]> =
                    results[drain_start..].iter().copied().collect();
                results.truncate(drain_start);
                results.push(self.alloc_fn_term("SetLiteral", elements, span));
            }
            BuildFrame::CollectionLiteral { node, elem_count, has_tail } => {
                let span = self.span(node);
                let drain_start = results.len() - (elem_count + usize::from(has_tail));
                let tail_tid = if has_tail {
                    Some(results[drain_start + elem_count])
                } else {
                    None
                };
                let elements: SmallVec<[TermId; 4]> =
                    results[drain_start..drain_start + elem_count].iter().copied().collect();
                results.truncate(drain_start);
                let functor = self.intern("ListLiteral");
                let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
                if let Some(t) = tail_tid {
                    let tail_key = self.intern("tail");
                    named_args.push((tail_key, t));
                }
                results.push(self.terms.alloc(
                    Term::Fn {
                        functor,
                        pos_args: elements,
                        named_args,
                    },
                    span,
                ));
            }
            BuildFrame::TupleLiteral { node, slots } => {
                let span = self.span(node);
                let drain_start = results.len() - slots.len();
                let mut positional: SmallVec<[TermId; 4]> = SmallVec::new();
                let mut named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
                for (i, slot) in slots.iter().enumerate() {
                    let value = results[drain_start + i];
                    match slot {
                        ArgSlot::Positional => positional.push(value),
                        ArgSlot::Named(sym) => named.push((*sym, value)),
                    }
                }
                results.truncate(drain_start);

                // All-or-nothing: error if mixing positional and named.
                if !positional.is_empty() && !named.is_empty() {
                    self.err("tuple literal cannot mix positional and named arguments", node);
                }
                if !positional.is_empty() {
                    for (i, tid) in positional.into_iter().enumerate() {
                        let label = self.intern_positional_label(i);
                        named.push((label, tid));
                    }
                }
                let functor = self.intern("TupleLiteral");
                results.push(self.terms.alloc(
                    Term::Fn {
                        functor,
                        pos_args: SmallVec::new(),
                        named_args: named,
                    },
                    span,
                ));
            }
            BuildFrame::MatchExpr { node, branch_count } => {
                let span = self.span(node);
                let drain_start = results.len() - (branch_count + 1);
                let scrutinee = results[drain_start];
                let mut pos_args: SmallVec<[TermId; 4]> = SmallVec::with_capacity(branch_count + 1);
                pos_args.push(scrutinee);
                pos_args.extend(results[drain_start + 1..].iter().copied());
                results.truncate(drain_start);
                results.push(self.alloc_fn_term("match_expr", pos_args, span));
            }
            BuildFrame::MatchBranch { node } => {
                let span = self.span(node);
                let drain_start = results.len() - 2;
                let pattern = results[drain_start];
                let body = results[drain_start + 1];
                results.truncate(drain_start);
                results.push(self.alloc_fn_term(
                    "match_branch",
                    SmallVec::from_slice(&[pattern, body]),
                    span,
                ));
            }
            BuildFrame::IfExpr { node } => {
                let span = self.span(node);
                let drain_start = results.len() - 3;
                let condition = results[drain_start];
                let then_branch = results[drain_start + 1];
                let else_branch = results[drain_start + 2];
                results.truncate(drain_start);
                results.push(self.alloc_fn_term(
                    "if_expr",
                    SmallVec::from_slice(&[condition, then_branch, else_branch]),
                    span,
                ));
            }
            BuildFrame::LetExpr { node, type_anno } => {
                let span = self.span(node);
                let drain_start = results.len() - 3;
                let pattern = results[drain_start];
                let value = results[drain_start + 1];
                let body = results[drain_start + 2];
                results.truncate(drain_start);
                // WI-271: embed `let pat : T = …` annotation inline as
                // a `type_name` named-arg child pointing at a
                // `Term::ParseAux(TypeExpr(T))` node — replaces the
                // prior `SimpleTermStore::let_type_annotations` HashMap.
                // The loader unwraps and calls `type_expr_to_term`.
                let mut named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
                if let Some(ty) = type_anno {
                    let aux = Term::ParseAux(Box::new(super::ir::ParseAux::TypeExpr(ty)));
                    let aux_tid = self.terms.alloc(aux, span);
                    let type_name_key = self.intern("type_name");
                    named.push((type_name_key, aux_tid));
                }
                let functor = self.intern("let_expr");
                let let_id = self.terms.alloc(
                    Term::Fn {
                        functor,
                        pos_args: SmallVec::from_slice(&[pattern, value, body]),
                        named_args: named,
                    },
                    span,
                );
                results.push(let_id);
            }
            BuildFrame::LambdaExpr { node } => {
                let span = self.span(node);
                let drain_start = results.len() - 2;
                let param = results[drain_start];
                let body = results[drain_start + 1];
                results.truncate(drain_start);
                results.push(self.alloc_fn_term(
                    "lambda",
                    SmallVec::from_slice(&[param, body]),
                    span,
                ));
            }
            BuildFrame::PatternLiteral { node } => {
                let span = self.span(node);
                let value = results.pop().expect("pattern_literal: missing value");
                results.push(self.alloc_fn_term(
                    "pattern_literal",
                    SmallVec::from_elem(value, 1),
                    span,
                ));
            }
            BuildFrame::PatternConstructor { node, name_tid, slots } => {
                let span = self.span(node);
                let drain_start = results.len() - slots.len();
                let mut pos_args: SmallVec<[TermId; 4]> = SmallVec::new();
                let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
                pos_args.push(name_tid);
                for (i, slot) in slots.iter().enumerate() {
                    let value = results[drain_start + i];
                    match slot {
                        ArgSlot::Positional => pos_args.push(value),
                        ArgSlot::Named(sym) => named_args.push((*sym, value)),
                    }
                }
                results.truncate(drain_start);
                if named_args.is_empty() {
                    results.push(self.alloc_fn_term("pattern_constructor", pos_args, span));
                } else {
                    let functor = self.intern("pattern_constructor");
                    results.push(self.terms.alloc(
                        Term::Fn { functor, pos_args, named_args },
                        span,
                    ));
                }
            }
            BuildFrame::PatternTuple { node, count } => {
                let span = self.span(node);
                let drain_start = results.len() - count;
                let pos_args: SmallVec<[TermId; 4]> =
                    results[drain_start..].iter().copied().collect();
                results.truncate(drain_start);
                results.push(self.alloc_fn_term("pattern_tuple", pos_args, span));
            }
        }
    }

    fn convert_variable_node(&mut self, node: Node) -> TermId {
        let span = self.span(node);
        let text = self.text(node);
        if text.len() > 1 {
            // Named variable: ?x (shared within scope)
            let name = &text[1..]; // strip leading '?'
            let sym = self.intern(name);
            let vid = self.get_or_create_var(sym);
            self.terms.alloc(Term::Var(Var::Global(vid)), span)
        } else {
            // Bare ? — anonymous variable (always fresh, like _ in Prolog)
            let sym = self.intern("_");
            let vid = VarId::new(self.next_var, sym);
            self.next_var += 1;
            self.terms.alloc(Term::Var(Var::Global(vid)), span)
        }
    }

    fn convert_nested_implication(&mut self, node: Node) -> TermId {
        let span = self.span(node);
        let mut binders: SmallVec<[TermId; 4]> = SmallVec::new();
        for n in self.fields_by_name(node, "binder") {
            binders.push(self.convert_variable_node(n));
        }
        let antecedents: SmallVec<[TermId; 4]> = self.field(node, "antecedents")
            .map(|n| self.convert_rule_body(n).into_iter().collect())
            .unwrap_or_default();
        let consequent: SmallVec<[TermId; 4]> = self.field(node, "consequent")
            .map(|n| self.convert_rule_body(n).into_iter().collect())
            .unwrap_or_default();

        let binders_tuple = self.alloc_fn_term("tuple", binders, span);
        let antecedents_tuple = self.alloc_fn_term("tuple", antecedents, span);
        let consequent_tuple = self.alloc_fn_term("tuple", consequent, span);
        self.alloc_fn_term(
            "forall_impl",
            SmallVec::from_slice(&[binders_tuple, antecedents_tuple, consequent_tuple]),
            span,
        )
    }

    fn convert_instantiation_term(&mut self, node: Node) -> TermId {
        // Eq[Int] or Eq[T = Int] — parameterized type in term position
        let span = self.span(node);
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
                        // Explicit: Eq[T = Int] — convert the type to a term.
                        // When t is `parameterized_type`, preserve its inner
                        // bindings as a Term::Fn (so conditional resolution
                        // can read them); only `simple_type` / bare names
                        // collapse to `Term::Ref(Name)`.
                        let param_name = self.convert_name(p);
                        let param_sym = self.intern_name(&param_name);
                        let value_tid = self.convert_type_value(t);
                        named_args.push((param_sym, value_tid));
                    }
                    (Some(p), None) => {
                        // Positional: List[Int] — value binds to next param in order.
                        let p_span = self.span(p);
                        let name = self.convert_name(p);
                        let sym = self.intern_name(&name);
                        pos_args.push(self.terms.alloc(Term::Ref(sym), p_span));
                    }
                    (None, Some(t)) => {
                        // Positional binding. Bare names (`List[Int]`) and
                        // parameterised types (`Tree[List[Int]]`) become
                        // `Term::Ref(Name)`; variable forms and tuple/arrow
                        // types fall through to `convert_term`.
                        let t_span = self.span(t);
                        let tid = match t.kind() {
                            "simple_type" | "parameterized_type" => {
                                let name = self.convert_type_to_name(t);
                                let sym = self.intern_name(&name);
                                self.terms.alloc(Term::Ref(sym), t_span)
                            }
                            _ => self.convert_term(t),
                        };
                        pos_args.push(tid);
                    }
                    (None, None) => {}
                }
            }
        }

        self.terms.alloc(Term::Fn { functor, pos_args, named_args }, span)
    }

    /// Convert a `_type` CST node into a Term value suitable for use
    /// as a fact-binding value. Preserves parametric inner shapes
    /// (`List[T = Int]` → `Fn(List, [(T, Int)])`) instead of
    /// flattening to bare `Ref(List)`. Bare names and variables
    /// still collapse to `Term::Ref` / `Term::Var`; other term
    /// shapes fall back to flatten-to-name to preserve compatibility
    /// with existing programs.
    fn convert_type_value(&mut self, node: Node) -> TermId {
        let span = self.span(node);
        match node.kind() {
            "simple_type" => {
                let name = self.convert_type_to_name(node);
                let sym = self.intern_name(&name);
                self.terms.alloc(Term::Ref(sym), span)
            }
            "parameterized_type" => {
                let name_node = self.child_by_kind(node, "name").unwrap_or(node);
                let name = self.convert_name(name_node);
                let functor = self.intern_name(&name);
                let mut pos_args: SmallVec<[TermId; 4]> = SmallVec::new();
                let mut named_args: SmallVec<[(crate::intern::Symbol, TermId); 2]> =
                    SmallVec::new();
                let mut cursor = node.walk();
                for child in node.named_children(&mut cursor) {
                    if child.kind() == "sort_binding" {
                        let param_node = self.field(child, "param");
                        let type_node = self.field(child, "type");
                        match (param_node, type_node) {
                            (Some(p), Some(t)) => {
                                let param_name = self.convert_name(p);
                                let param_sym = self.intern_name(&param_name);
                                let value_tid = self.convert_type_value(t);
                                named_args.push((param_sym, value_tid));
                            }
                            (Some(p), None) => {
                                let p_span = self.span(p);
                                let name = self.convert_name(p);
                                let sym = self.intern_name(&name);
                                pos_args.push(self.terms.alloc(Term::Ref(sym), p_span));
                            }
                            (None, Some(t)) => {
                                pos_args.push(self.convert_type_value(t));
                            }
                            (None, None) => {}
                        }
                    }
                }
                self.terms.alloc(Term::Fn { functor, pos_args, named_args }, span)
            }
            // Variables (`?` / `?x`) — preserve as Var terms; resolution
            // treats these as wildcards, not as named refs.
            "variable_term" | "variable" => self.convert_term(node),
            // Other non-type term shapes (function calls, tuples, arrows)
            // appearing in binding-value position collapse to `Ref(Name)`
            // — the SLD resolver doesn't need to introspect them.
            _ => {
                let name = self.convert_type_to_name(node);
                let sym = self.intern_name(&name);
                self.terms.alloc(Term::Ref(sym), span)
            }
        }
    }

    /// Extract a Name from a type CST node (simple_type or parameterized_type).
    fn convert_type_to_name(&mut self, node: Node) -> Name {
        let name_node = self.child_by_kind(node, "name").unwrap_or(node);
        self.convert_name(name_node)
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
        // The `effect` field is repeated under `_effect_set`: a single
        // `_type` (e.g. `@ E`) yields one entry; a braced set
        // (`@ {E1, E2}`) yields one entry per element. No annotation →
        // empty Vec. `_effect_set` is a hidden production, so its
        // delimiters (`{`, `,`, `}`) inherit the `effect` field name —
        // skip the anonymous tokens and only keep the type-kind nodes.
        let effects: Vec<TypeExpr> = self.fields_by_name(node, "effect")
            .into_iter()
            .filter(|n| n.is_named())
            .map(|n| self.convert_type(n))
            .collect();

        TypeExpr::Arrow { params, return_type, effects }
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
        let span = self.span(node);
        let key = self.field(node, "key")
            .map(|n| self.convert_name(n))
            .unwrap_or_else(|| Name::simple(self.intern("?"), span));
        let value = self.field(node, "value")
            .map(|n| self.convert_term(n))
            .unwrap_or_else(|| self.terms.alloc(Term::Bottom, span));
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
                let tid = self.terms.alloc(Term::Var(Var::Global(vid)), span);
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

    fn convert_sort_like(&mut self, node: Node, kind: SortDeclKind) -> Option<SortWithBody> {
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
            kind,
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

        let heads = self.field(node, "heads")
            .map(|h| self.convert_rule_heads(h))
            .unwrap_or_else(|| vec![RuleHead::Bottom]);

        let body = self.field(node, "body")
            .map(|b| self.convert_rule_body(b));

        let meta = self.convert_meta_block(node);

        self.snapshot_rule_var_scope(&label);
        Some(Rule { label, heads, body, meta, span })
    }

    /// Save the current `var_scope` keyed by the rule's label so a
    /// subsequent `convert_proof` for the same target can restore
    /// the parent rule's variable identities. Single-segment labels
    /// only — multi-segment names aren't proof targets.
    fn snapshot_rule_var_scope(&mut self, label: &Option<Name>) {
        if let Some(label_name) = label {
            if label_name.segments.len() == 1 {
                self.rule_var_scopes.insert(label_name.segments[0], self.var_scope.clone());
            }
        }
    }

    /// Convert a `rule_heads` CST node into a list of head terms.
    /// `rule_heads ::= '⊥' | term (',' term)*` per proposal 032 — the
    /// `⊥` arm has no named children (the symbol is an anonymous
    /// token), so a zero-named-child count uniquely identifies denial.
    fn convert_rule_heads(&mut self, node: Node) -> Vec<RuleHead> {
        if node.named_child_count() == 0 {
            return vec![RuleHead::Bottom];
        }
        let mut cursor = node.walk();
        node.named_children(&mut cursor)
            .filter(|c| is_term_kind(c.kind()))
            .map(|c| RuleHead::Term(self.convert_term(c)))
            .collect()
    }

    // ── Operation ───────────────────────────────────────────────

    fn convert_operation(&mut self, node: Node) -> Option<Operation> {
        self.reset_var_scope();
        let span = self.span(node);
        let name = self.field(node, "name")
            .map(|n| self.convert_name(n))?;
        let visibility = self.convert_visibility(node);

        let type_params = self.convert_operation_type_params(node);

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
            type_params,
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

    fn convert_operation_type_params(&mut self, node: Node) -> Vec<TypeParam> {
        let Some(list) = self.child_by_kind(node, "operation_type_param_list") else {
            return Vec::new();
        };
        self.children_by_kind(list, "operation_type_param")
            .into_iter()
            .map(|p| self.convert_operation_type_param(p))
            .collect()
    }

    fn convert_operation_type_param(&mut self, node: Node) -> TypeParam {
        let span = self.span(node);
        let name = self.field(node, "name")
            .map(|n| self.intern(self.text(n)))
            .unwrap_or_else(|| self.intern("?"));
        let default = self.field(node, "default").map(|t| self.convert_type(t));
        TypeParam { name, default, span }
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
        Some(Fact { term, sort: None, meta, span })
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
        // operation_entry shares operation_declaration's field/child
        // names (minus the literal `operation` keyword), so the same
        // converter handles both node kinds.
        let entries = self.children_by_kind(node, "operation_entry")
            .into_iter()
            .filter_map(|e| self.convert_operation(e))
            .collect();
        Some(OperationBlock { entries, span })
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
        let heads = self.field(node, "heads")
            .map(|h| self.convert_rule_heads(h))
            .unwrap_or_else(|| vec![RuleHead::Bottom]);
        let body = self.field(node, "body")
            .map(|b| self.convert_rule_body(b));
        let meta = self.convert_meta_block(node);
        self.snapshot_rule_var_scope(&label);
        Some(Rule { label, heads, body, meta, span })
    }

    // ── Describe ────────────────────────────────────────────────

    // ── Proof / provides (proposal 025) ─────────────────────────

    fn convert_proof(&mut self, node: Node) -> Option<ProofDecl> {
        let target = self.field(node, "target").map(|n| self.convert_name(n))?;
        // Restore the parent rule's var_scope before
        // converting the proof body so structured-proof step
        // variables that share source names with the parent (e.g.
        // `?d_prev`, `?delta`) get the SAME parse-IR VarId. Without
        // this, each step's scope is independent and the cited-rule
        // lift forall-quantifies the step's vars over arbitrary
        // reals, producing vacuous axioms in the SMT preamble.
        self.reset_var_scope();
        if target.segments.len() == 1 {
            if let Some(parent_scope) = self.rule_var_scopes.get(&target.segments[0]).cloned() {
                self.var_scope = parent_scope;
            }
        }
        let strategy = self.field(node, "strategy").map(|n| self.convert_proof_strategy(n));
        let body = self.convert_proof_body(node);
        let using = self.field(node, "using")
            .map(|n| self.convert_proof_using_list(n))
            .unwrap_or_default();
        let span = self.span(node);
        Some(ProofDecl { target, strategy, body, using, span })
    }

    /// Pull each `name` child of a `proof_using_list` node into a
    /// `Vec<Name>`. Empty input yields an empty vector — the loader
    /// treats that as "no cited lemmas".
    fn convert_proof_using_list(&mut self, node: Node) -> Vec<Name> {
        let mut out = Vec::new();
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            if child.kind() == "name" {
                out.push(self.convert_name(child));
            }
        }
        out
    }

    /// Convert a single `named_arg` node into a synthetic
    /// `named_arg(name: "...", value: <term>)` term so it can be carried
    /// alongside positional args in proof strategies.
    fn convert_named_arg(&mut self, node: Node) -> TermId {
        let span = self.span(node);
        let key_node = self.field(node, "name");
        let val_node = self.field(node, "value");
        if let (Some(k), Some(v)) = (key_node, val_node) {
            let key_str = self.terms.alloc(
                Term::Const(Literal::String(self.text(k).to_string())),
                self.span(k),
            );
            let val_tid = self.convert_term(v);
            let functor = self.intern("named_arg");
            let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
            named_args.push((self.intern("name"), key_str));
            named_args.push((self.intern("value"), val_tid));
            self.terms.alloc(Term::Fn { functor, pos_args: SmallVec::new(), named_args }, span)
        } else {
            self.alloc_bottom(span)
        }
    }

    fn convert_proof_strategy(&mut self, node: Node) -> ProofStrategy {
        let span = self.span(node);
        let name = self.field(node, "name")
            .map(|n| self.intern(self.text(n)))
            .unwrap_or_else(|| self.intern("derivation"));
        // Args are positional/named children of the proof_strategy node.
        // _fn_arg can be either a term (positional) or a named_arg.
        let mut args: Vec<TermId> = Vec::new();
        let mut tactic_args: Vec<TacticArg> = Vec::new();
        let mut explicit_tactic: Option<Tactic> = None;
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            match child.kind() {
                "named_arg" => {
                    args.push(self.convert_named_arg(child));
                    let arg = self.convert_tactic_named_arg(child);
                    if let Some(arg) = arg {
                        if self.parse_symbol_name(arg.name) == Some("tactic") {
                            if let TacticArgValue::Tactic(t) = arg.value {
                                explicit_tactic = Some(*t);
                                continue;
                            }
                        }
                        tactic_args.push(arg);
                    }
                }
                "identifier" | "name" => {
                    // The strategy name itself — skip.
                }
                _ => {
                    args.push(self.convert_term(child));
                    if let Some(value) = self.convert_tactic_term_node(child) {
                        tactic_args.push(TacticArg { name: None, value });
                    }
                }
            }
        }

        // Build the typed Tactic IR for z3 strategies. Backwards compat:
        // `by z3(logic: "LRA")` desugars to `by z3(tactic: smt(logic: "LRA"))`.
        let tactic = if self.symbol_text(name) == "z3" {
            Some(explicit_tactic.unwrap_or_else(|| {
                Tactic::App(self.intern("smt"), tactic_args)
            }))
        } else {
            None
        };

        ProofStrategy { name, args, tactic, span }
    }

    /// Lift one parse-side `named_arg` into a `TacticArg`. Returns
    /// `None` if the value can't be classified (which keeps malformed
    /// inputs from corrupting the typed IR; the legacy `args` field
    /// still carries them).
    fn convert_tactic_named_arg(&mut self, node: Node) -> Option<TacticArg> {
        let key_node = self.field(node, "name")?;
        let val_node = self.field(node, "value")?;
        let name = Some(self.intern(self.text(key_node)));
        let value = self.convert_tactic_term_node(val_node)?;
        Some(TacticArg { name, value })
    }

    /// Convert a parse-tree node into a `TacticArgValue`. Recognises
    /// literals, name references, and nested tactic applications.
    fn convert_tactic_term_node(&mut self, node: Node) -> Option<TacticArgValue> {
        match node.kind() {
            "string_literal" => Some(TacticArgValue::String(
                decode_string_lit(self.text(node))
            )),
            "integer_literal" => self.text(node).parse::<i64>().ok()
                .map(TacticArgValue::Int),
            "boolean_literal" => Some(TacticArgValue::Bool(
                self.text(node) == "true"
            )),
            "identifier" => {
                // A bare identifier in tactic position — interpret as
                // `Tactic::Bare`. (e.g. `then(smt, simplify)` — args are
                // bare identifier tactics.)
                let sym = self.intern(self.text(node));
                Some(TacticArgValue::Tactic(Box::new(Tactic::Bare(sym))))
            }
            "fn_term" => {
                let tactic = self.convert_tactic_fn_term(node)?;
                Some(TacticArgValue::Tactic(Box::new(tactic)))
            }
            "name" => {
                let n = self.convert_name(node);
                Some(TacticArgValue::Name(n))
            }
            _ => None,
        }
    }

    /// Recognise a `fn_term` as a tactic application. `smt(...)`,
    /// `then(t1, t2)`, `induction(over: …, base: …)`, `raw("...")`
    /// all flow through here. Returns `None` if the fn_term doesn't
    /// have a tactic shape (then the caller falls back to the legacy
    /// args path).
    fn convert_tactic_fn_term(&mut self, node: Node) -> Option<Tactic> {
        let name_node = self.field(node, "name")?;
        let fn_name = self.text(name_node).to_string();

        // raw("…") — single positional string literal.
        if fn_name == "raw" {
            let mut cursor = node.walk();
            for child in node.named_children(&mut cursor) {
                if child == name_node { continue; }
                if child.kind() == "string_literal" {
                    return Some(Tactic::Raw(decode_string_lit(self.text(child))));
                }
            }
            return None;
        }

        let functor = self.intern(&fn_name);
        let mut args: Vec<TacticArg> = Vec::new();
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            if child == name_node { continue; }
            match child.kind() {
                "named_arg" => {
                    if let Some(a) = self.convert_tactic_named_arg(child) {
                        args.push(a);
                    }
                }
                _ => {
                    if let Some(v) = self.convert_tactic_term_node(child) {
                        args.push(TacticArg { name: None, value: v });
                    }
                }
            }
        }
        Some(Tactic::App(functor, args))
    }

    fn parse_symbol_name(&self, sym: Option<Symbol>) -> Option<&str> {
        sym.map(|s| self.symbols.name(s))
    }

    fn symbol_text(&self, sym: Symbol) -> &str {
        self.symbols.name(sym)
    }

    /// _proof_body is either `:- hints` or `query "..." [mapping {...}]`,
    /// or (proposal 031) the structured form: a sequence of `proof_step`
    /// children plus an optional `proof_concluding_clause`.
    fn convert_proof_body(&mut self, proof_node: Node) -> Option<ProofBody> {
        // Hints case: child `rule_body` field named "hints"
        if let Some(hints_node) = self.field(proof_node, "hints") {
            let mut hints = Vec::new();
            let mut cursor = hints_node.walk();
            for child in hints_node.named_children(&mut cursor) {
                hints.push(self.convert_term(child));
            }
            return Some(ProofBody::Hints(hints));
        }
        // Query case: string_literal field named "query"
        if let Some(q_node) = self.field(proof_node, "query") {
            let raw = self.text(q_node);
            let text = decode_string_lit(raw);
            let mapping = self.field(proof_node, "mapping")
                .map(|n| self.convert_mapping_block(n));
            return Some(ProofBody::Query { text, mapping });
        }
        // Structured case (proposal 031): `proof_step` children plus an
        // optional `proof_concluding_clause`. Detect by presence of any
        // proof_step child; the concluding clause is optional.
        let steps: Vec<ProofStep> = self.children_by_kind(proof_node, "proof_step")
            .into_iter()
            .filter_map(|n| self.convert_proof_step(n))
            .collect();
        if !steps.is_empty() {
            let conclude = self.child_by_kind(proof_node, "proof_concluding_clause")
                .and_then(|n| self.convert_proof_concluding_clause(n));
            return Some(ProofBody::Structured { steps, conclude });
        }
        None
    }

    fn convert_proof_step(&mut self, node: Node) -> Option<ProofStep> {
        // Do NOT reset_var_scope here. Steps inherit the
        // parent rule's scope (set by convert_proof) so source names
        // like `?d_prev` map to the SAME VarId across the parent and
        // every step; they also share with previously-converted steps
        // in the same proof body, so a later step's `?v_diff_scaled`
        // matches the earlier step that introduced it.
        let span = self.span(node);

        let label = self.field(node, "label").map(|n| self.convert_name(n));
        let heads = self.field(node, "heads")
            .map(|h| self.convert_rule_heads(h))
            .unwrap_or_else(|| vec![RuleHead::Bottom]);
        let body = self.field(node, "body").map(|b| self.convert_rule_body(b));
        let meta = self.convert_meta_block(node);
        let using = self.field(node, "using")
            .map(|n| self.convert_proof_using_list(n))
            .unwrap_or_default();
        let strategy = self.field(node, "tactic")
            .map(|n| self.convert_proof_strategy(n))?;

        let rule = Rule { label, heads, body, meta, span };
        Some(ProofStep { rule, using, strategy, span })
    }

    fn convert_proof_concluding_clause(&mut self, node: Node) -> Option<ConcludeClause> {
        let span = self.span(node);
        let using = self.field(node, "using")
            .map(|n| self.convert_proof_using_list(n))
            .unwrap_or_default();
        let strategy = self.field(node, "tactic")
            .map(|n| self.convert_proof_strategy(n))?;
        Some(ConcludeClause { using, strategy, span })
    }

    fn convert_mapping_block(&mut self, node: Node) -> MappingBlock {
        let entries: Vec<MappingEntry> = self.children_by_kind(node, "mapping_entry")
            .into_iter()
            .map(|e| self.convert_mapping_entry(e))
            .collect();
        MappingBlock { entries }
    }

    fn convert_mapping_entry(&mut self, node: Node) -> MappingEntry {
        let source = self.field(node, "source")
            .map(|n| self.convert_name(n))
            .unwrap_or_else(|| Name::simple(self.intern("?"), self.span(node)));
        let target = self.field(node, "target")
            .map(|n| match n.kind() {
                "string_literal" => decode_string_lit(self.text(n)),
                _ => self.text(n).to_string(),
            })
            .unwrap_or_default();
        MappingEntry { source, target }
    }

    fn convert_provides_clause(&mut self, node: Node) -> Option<ProvidesClause> {
        let spec = self.field(node, "spec").map(|n| self.convert_type(n))?;
        let span = self.span(node);
        Some(ProvidesClause { spec, span })
    }

    fn convert_provides_block(&mut self, node: Node) -> Option<ProvidesBlock> {
        let spec = self.field(node, "spec").map(|n| self.convert_type(n))?;
        let language = self.field(node, "language")
            .map(|n| self.intern(self.text(n)))?;
        let mut items: Vec<ProvidesItem> = Vec::new();
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            match child.kind() {
                "rule_declaration" => {
                    if let Some(r) = self.convert_rule(child) { items.push(ProvidesItem::Rule(r)); }
                }
                "rule_block" => {
                    if let Some(rb) = self.convert_rule_block(child) { items.push(ProvidesItem::RuleBlock(rb)); }
                }
                "fact_declaration" => {
                    if let Some(f) = self.convert_fact(child) { items.push(ProvidesItem::Fact(f)); }
                }
                "proof_declaration" => {
                    if let Some(p) = self.convert_proof(child) { items.push(ProvidesItem::Proof(p)); }
                }
                "artifact_clause" => {
                    if let Some(p) = self.field(child, "path") {
                        items.push(ProvidesItem::Artifact(decode_string_lit(self.text(p))));
                    }
                }
                "carrier_clause" => {
                    items.push(ProvidesItem::Carrier(self.convert_provides_bindings(child)
                        .into_iter().map(|(s, t)| CarrierBinding { anthill_param: s, host_type: t }).collect()));
                }
                "namespace_map_clause" => {
                    items.push(ProvidesItem::NamespaceMap(self.convert_provides_bindings(child)
                        .into_iter().map(|(s, t)| NamespaceMapEntry { anthill_namespace: s, host_module: t }).collect()));
                }
                _ => {}
            }
        }
        let span = self.span(node);
        Some(ProvidesBlock { spec, language, items, span })
    }

    fn convert_provides_bindings(&mut self, node: Node) -> Vec<(Symbol, TermId)> {
        // bindings: '{' commaSep1(seq(identifier, ':', term)) '}'
        let mut out: Vec<(Symbol, TermId)> = Vec::new();
        if let Some(bindings) = self.field(node, "bindings") {
            let mut cursor = bindings.walk();
            let children: Vec<Node> = bindings.named_children(&mut cursor).collect();
            // Walk pairs (identifier, term)
            let mut i = 0;
            while i + 1 < children.len() {
                if children[i].kind() == "identifier" {
                    let key = self.intern(self.text(children[i]));
                    let val = self.convert_term(children[i + 1]);
                    out.push((key, val));
                    i += 2;
                } else {
                    i += 1;
                }
            }
        }
        out
    }

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

    // ── Expressions ──────────────────────────────────────────────

    /// Convert an expression body node (match_expr / if_expr /
    /// let_chain / lambda_expr / plain term). Delegates to the
    /// iterative walker.
    fn convert_expr_body(&mut self, node: Node) -> TermId {
        self.convert_expr_iter(node, WorkKind::ExprBody)
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
            | "nested_implication"
            | "instantiation_term"
            | "ref_term"
            | "infix_term"
            | "prefix_term"
            | "field_access"
            | "set_literal"
            | "collection_literal"
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
            | "named_pattern_field"
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

/// Strip surrounding quotes from a `string_literal` token and decode escapes.
fn decode_string_lit(raw: &str) -> String {
    let trimmed = raw.trim();
    let inner = if trimmed.starts_with('"') && trimmed.ends_with('"') && trimmed.len() >= 2 {
        &trimmed[1..trimmed.len() - 1]
    } else {
        trimmed
    };
    if inner.contains('\\') {
        decode_string_escapes(inner)
    } else {
        inner.to_string()
    }
}

/// Decode the `\\.`-style escape sequences the grammar accepts inside
/// string literals. The matching encoder is `persistence::print`'s
/// String case (\" \\ \n \r \t). Unknown escapes pass the trailing
/// char through; a lone trailing backslash is kept literal.
fn decode_string_escapes(inner: &str) -> String {
    let mut decoded = String::with_capacity(inner.len());
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('"')  => decoded.push('"'),
                Some('\\') => decoded.push('\\'),
                Some('n')  => decoded.push('\n'),
                Some('r')  => decoded.push('\r'),
                Some('t')  => decoded.push('\t'),
                Some(other) => decoded.push(other),
                None => decoded.push('\\'),
            }
        } else {
            decoded.push(c);
        }
    }
    decoded
}

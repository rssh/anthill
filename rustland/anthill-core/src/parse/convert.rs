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
        has_guard: bool,
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
    /// In-body / control-flow proof (WI-538). The visited children are
    /// the continuation `body` and the optional `conclude` goal; the
    /// `target` / `strategy_name` / `using` clauses are leaf metadata
    /// carried here and emitted as a `ParseAux::ProofStmt` child.
    ProofStmt {
        node: Node<'t>,
        target: Name,
        strategy_name: Option<Symbol>,
        using: Vec<Name>,
        has_conclude: bool,
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

    /// WI-446: dangling-`case` attachment hazard. The grammar attaches a
    /// trailing `case` arm to the innermost open `match` (`match_expr` is
    /// `prec.right(repeat1(match_branch))`, with no indentation awareness),
    /// so an arm the author indented for an ENCLOSING `match` silently lands
    /// on a nested one instead — dropping the outer arm with no syntax error.
    ///
    /// The parse tree alone can't recover intent, but the source indentation
    /// can: a branch indented strictly LESS than this match's first branch
    /// was visually written for an outer match. Flag the mismatch loudly
    /// (CLAUDE.md: "prefer a loud error over a silent skip"). A `match` has no
    /// closing delimiter in the grammar, so the remedy is to make the inner
    /// `match` the enclosing match's LAST arm, or bind it to a `let` (the
    /// trailing reference terminates the inner branch list).
    ///
    /// Indentation is compared by leading-whitespace PREFIX, not by column:
    /// tree-sitter's column is a byte offset, so a tab (1 byte) would look
    /// shallower than spaces and spuriously reject valid tab-indented code.
    /// A branch is "shallower" only when its leading whitespace is a proper
    /// prefix of the first branch's — tab/space-mix safe, and conservative
    /// (incomparable indentation is left alone). Branches that don't start
    /// their own line (arms written inline on one line) carry no indentation
    /// signal and are skipped — so single-line nested matches aren't checked,
    /// but there the parse matches the visual reading anyway.
    fn check_dangling_case(&mut self, branches: &[Node]) {
        let Some(base) = branches.first().and_then(|b| self.line_indent(*b)) else {
            return;
        };
        for branch in &branches[1..] {
            if let Some(indent) = self.line_indent(*branch) {
                if indent.len() < base.len() && base.starts_with(indent) {
                    self.err(
                        "this `case` is less indented than the match's first \
                         arm, so it was likely written for an enclosing \
                         `match` but binds to this nested one (silently \
                         dropping the outer arm); make the inner `match` the \
                         enclosing match's last arm, or bind it to a `let`",
                        *branch,
                    );
                }
            }
        }
    }

    /// The leading whitespace of `node`'s line, IF `node` is the first
    /// non-whitespace token on that line; otherwise `None` (e.g. an arm
    /// written inline after other tokens). Returned as the raw source slice
    /// so indentation can be compared by prefix rather than by byte column.
    fn line_indent(&self, node: Node) -> Option<&'a str> {
        let start = node.start_byte();
        let line_start = self.source[..start].rfind('\n').map_or(0, |i| i + 1);
        let prefix = &self.source[line_start..start];
        prefix.bytes().all(|b| b == b' ' || b == b'\t').then_some(prefix)
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
            let items = self.convert_items_at(child);
            self.items.extend(items);
        }
    }

    /// One CST node → its IR item(s).
    ///
    /// Most CST nodes map 1:1 onto an `Item` (handled in `convert_item`). The
    /// `effects_sort_item` sugar (WI-320 / proposal 045) is the exception: a
    /// single `effects E [= T]` source node desugars to TWO IR items —
    /// `AbstractSort(E [= T])` followed by `RequiresDecl(EffectsRuntime[Effects = E])`.
    /// Returning `Vec<Item>` keeps the three sort/namespace/root walks uniform.
    fn convert_items_at(&mut self, node: Node) -> Vec<Item> {
        match node.kind() {
            "effects_sort_item" => self.convert_effects_sort_item(node),
            _ => self.convert_item(node).into_iter().collect(),
        }
    }

    fn convert_item(&mut self, node: Node) -> Option<Item> {
        match node.kind() {
            "namespace_declaration" => self.convert_namespace(node).map(Item::Namespace),
            "abstract_sort" => self.convert_abstract_sort(node).map(Item::AbstractSort),
            "sort_with_body" => self.convert_sort_like(node, SortDeclKind::Sort).map(Item::SortWithBody),
            "sort_var_binder" | "sort_bracket_binder" => self.convert_sort_binder(node),
            "enum_declaration" => self.convert_sort_like(node, SortDeclKind::Enum).map(Item::SortWithBody),
            "rule_declaration" => self.convert_rule(node).map(Item::Rule),
            "operation_declaration" => self.convert_operation(node).map(Item::Operation),
            "const_declaration" => self.convert_const(node).map(Item::Const),
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
        if node.kind() == "application" {
            // WI-311: `Name[bindings]` — the functor/name is the `name` field (a
            // `name` node now, not a bare identifier), read it directly. The
            // bindings are consumed separately by callers (e.g. push_fn_term's
            // type_args). Without this, the identifier-child scan below misses
            // the nested `name` node and falls back to interning the whole
            // `Name[binding…]` text as one bogus segment.
            if let Some(name_node) = self.field(node, "name") {
                return self.convert_name(name_node);
            }
            // A malformed application without a `name` field falls through to
            // the generic scan / text fallback — never recurse on `node`.
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
            } else if o.kind() == "application" {
                // Form (3) of proposal 035: `Map[K = String, V = Int].empty()`.
                // The application names a (possibly qualified) sort with type
                // bindings; for the runtime call path we need the sort's name
                // segments (bindings erased). The base is a `name` node and may
                // be dotted (`a.b.Map[…].empty()`), so push all its segments
                // rather than interning the joined text as one symbol.
                let inst_name = self.field(o, "name").unwrap_or(o);
                let nm = self.convert_name(inst_name);
                for seg in nm.segments.iter() {
                    segments.push(*seg);
                }
            }
            // WI-312: a bare `name` object is no longer possible — a bare/dotted
            // identifier path is a `name` node (not a `field_access`), so a
            // qualified-companion `field_access` only ever has an `application`
            // receiver or a nested `field_access`. (A degenerate paren-wrapped
            // path like `(p).y` reaches here with a `paren_expr` object; its
            // segments are dropped as before — pre-existing, out of scope.)
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
            "application" => {
                // WI-311: was `parameterized_type`; the base is now an
                // `identifier` field, not a `name` child node.
                let name_node = self.field(node, "name").unwrap_or(node);
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
            // WI-375 (proposal 045 §2): a WRITTEN effect-row in a type-argument
            // value slot (`Stream[E = {}]` / `Stream[E = {Modify[c]}]`). Lower
            // each listed effect through `convert_effect_into` — identical to
            // the arrow-effects walker — so `merge(…)` flattens and `-E` lowers
            // to `EffectAbsent`. The empty `{}` row yields `EffectRow(vec![])`.
            "effect_row" => {
                let mut effect_items: Vec<Effect> = Vec::new();
                let mut cursor = node.walk();
                for child in node.named_children(&mut cursor) {
                    self.convert_effect_into(child, &mut effect_items);
                }
                let effects: Vec<TypeExpr> =
                    effect_items.into_iter().map(|e| e.type_expr).collect();
                TypeExpr::EffectRow(effects)
            }
            "integer_literal" | "float_literal" | "string_literal" | "boolean_literal" => {
                // WI-302: a literal standing in a type-argument position
                // (`Vector[Int, 3]`) is value-in-type → denoted(value).
                TypeExpr::Denoted(self.convert_term(node))
            }
            // WI-327: `+E` — explicit presence sugar. Presence is the
            // default for bare labels, so unwrap to the inner.
            "effect_presence" => {
                let inner = self.field(node, "effect")
                    .map(|n| self.convert_type(n))
                    .unwrap_or_else(|| {
                        self.err("effect_presence missing inner effect", node);
                        let sym = self.intern("?");
                        TypeExpr::Simple(Name::simple(sym, self.span(node)))
                    });
                inner
            }
            // WI-327: `-E` — absence / lacks-constraint. Wrap inner in
            // EffectAbsent; the loader lowers to make_effect_expression_
            // absent(...).
            "effect_absence" => {
                let inner = self.field(node, "effect")
                    .map(|n| self.convert_type(n))
                    .unwrap_or_else(|| {
                        self.err("effect_absence missing inner effect", node);
                        let sym = self.intern("?");
                        TypeExpr::Simple(Name::simple(sym, self.span(node)))
                    });
                TypeExpr::EffectAbsent(Box::new(inner))
            }
            // WI-327: `merge(E1, …, En)` should not reach this single-
            // TypeExpr return path — merge flattens into the parent
            // effects vec at the effects_clause / arrow-effects walker.
            // If it does reach here, the caller used merge in a single-
            // type context (not inside an effects collection); fall
            // through to the error arm rather than silently lose the
            // children.
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
            "let_binding" => {
                // proposal 049: `let ?v = e` is sugar for `?v <=> e`; lower to the same
                // `unify(?v, e)` IR pratt builds for `<=>` (WI-522). Per-goal depth is
                // bounded, so the recursive `convert_term` on the children is fine.
                let tid = self.convert_let_binding(node);
                results.push(tid);
            }
            "nested_implication" => {
                // Rare in expression contexts (rule bodies only) — stays
                // recursive since `convert_rule_body` re-enters
                // `convert_term` per goal and per-goal depth is bounded
                // by rule structure rather than nested expressions.
                let tid = self.convert_nested_implication(node);
                results.push(tid);
            }
            "bounded_quantification" => {
                // WI-027: `(forall ?x in xs: P(?x))` / `(some ?x in xs: P(?x))`.
                // Rule bodies only; recursive like `nested_implication` (per-goal
                // depth bounded by rule structure).
                let tid = self.convert_bounded_quantification(node);
                results.push(tid);
            }
            "application" => {
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
            "name" => {
                // The bare-reference atom is `$.name` (WI-311; was
                // `$.identifier`). A single segment is a plain ref, identical
                // to the former `identifier` atom. WI-312: a dotted term path
                // (`p.x`, `a.b.c`) now parses as a `name` too — `field_access`
                // is reserved for value receivers — so this arm folds a
                // multi-segment name into the same
                // `field_access(object, Ident(field))` builtin an
                // identifier-rooted projection produces. The loader sees a term
                // identical to the former field_access shape and classifies the
                // path (projection vs qualified-ref) via SymbolKind.
                let nm = self.convert_name(node);
                let segs = nm.segments;
                let mut acc = self.terms.alloc(Term::Ident(segs[0]), span);
                if segs.len() > 1 {
                    let field_access_sym = self.intern("field_access");
                    for seg in &segs[1..] {
                        let field_tid = self.terms.alloc(Term::Ident(*seg), span);
                        acc = self.terms.alloc(Term::Fn {
                            functor: field_access_sym,
                            pos_args: SmallVec::from_slice(&[acc, field_tid]),
                            named_args: SmallVec::new(),
                        }, span);
                    }
                }
                results.push(acc);
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
        let type_args: Vec<SortBinding> = if name_node.kind() == "application" {
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
            work.push(WorkOp::Visit(fn_arg_work_kind(child.kind()), *child));
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
        // A lambda arg (`xs.fold(0, lambda (a, x) -> a + x)`) visits as an
        // `ExprBody`; see `fn_arg_work_kind`.
        for child in child_nodes.iter().rev() {
            work.push(WorkOp::Visit(fn_arg_work_kind(child.kind()), *child));
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
                "name" | "application" => return false,
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
        // `tuple_literal` shares the `_fn_arg` rule, which admits a lambda
        // element (`(lambda x -> x, 5)`); dispatch it as `ExprBody` like
        // the other `_fn_arg` sites. See `fn_arg_work_kind`.
        for child in child_nodes.iter().rev() {
            work.push(WorkOp::Visit(fn_arg_work_kind(child.kind()), *child));
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
                self.check_dangling_case(&branches);
                let branch_count = branches.len();
                work.push(WorkOp::Build(BuildFrame::MatchExpr { node, branch_count }));
                for branch in branches.iter().rev() {
                    let pattern = self.field(*branch, "pattern");
                    let body = self.field(*branch, "body");
                    // WI-537: the optional arm guard `case p | g -> …` is a `_term`.
                    let guard = self.field(*branch, "guard");
                    let branch_span = self.span(*branch);
                    work.push(WorkOp::Build(BuildFrame::MatchBranch {
                        node: *branch,
                        has_guard: guard.is_some(),
                    }));
                    // Push the guard first so it drains AFTER pattern/body
                    // (results order [pattern, body, guard]).
                    if let Some(g) = guard {
                        work.push(WorkOp::Visit(WorkKind::Term, g));
                    }
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
            "proof_statement" => {
                // WI-538: an in-body / control-flow proof.  The `target`
                // name, `by <strategy>` name, and `using` cites are leaf
                // metadata (carried on the build frame → a
                // `ParseAux::ProofStmt`).  The visited children are the
                // continuation `body` (an `_expr_body`) and the optional
                // `conclude <goal>` (`_term`) — lowered as ordinary
                // occurrences so the goal's names (the local `b` in
                // `neq(b, 0)`, the `neq` rule) resolve in scope.
                let target = self.convert_name(
                    self.field(node, "target").expect("proof_statement: target"));
                let strategy_name = self
                    .field(node, "strategy")
                    .map(|s| self.convert_proof_strategy(s).name);
                let using = self
                    .field(node, "using")
                    .map(|u| self.convert_proof_using_list(u))
                    .unwrap_or_default();
                let conclude = self.field(node, "conclude");
                let body = self.field(node, "body");
                let span = self.span(node);
                work.push(WorkOp::Build(BuildFrame::ProofStmt {
                    node,
                    target,
                    strategy_name,
                    using,
                    has_conclude: conclude.is_some(),
                }));
                // Results order [body, conclude?]: push conclude first
                // (drains last), body last (drains first).
                if let Some(c) = conclude {
                    self.push_child_or_yield(work, Some(c), WorkKind::Term, span);
                }
                self.push_child_or_yield(work, body, WorkKind::ExprBody, span);
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
            // WI-517: the parenthesized single typed binder `(x: T)` wraps a
            // `typed_binder` in a named node (so the lambda's `param` field
            // resolves cleanly). Unwrap to the inner binder — it lowers to a
            // single typed `pattern_var`, NOT a 1-tuple.
            "pattern_typed" => {
                match self.child_by_kind(node, "typed_binder") {
                    Some(binder) => self.visit_pattern(binder, work, results),
                    None => {
                        self.err("pattern_typed: missing typed_binder".to_string(), node);
                        results.push(self.alloc_bottom(span));
                    }
                }
            }
            // WI-517: a type-annotated lambda binder (`(x: T)` or a tuple
            // element `(a: A, b: B)`). Lowers to the SAME `pattern_var`
            // functor as a bare binder — so name-collection and the pattern
            // recognizers stay unchanged — but carries the declared type as
            // a `ParseAux::TypeExpr` under the `type` named arg. The loader
            // (`load_pattern_var`) lowers it into the var_pattern's `type_ann`
            // slot, which the typer reads to constrain inference.
            "typed_binder" => {
                let name_node = self.field(node, "name").unwrap_or(node);
                let sym = self.intern(self.text(name_node));
                let name_tid = self.terms.alloc(Term::Ident(sym), self.span(name_node));
                let type_tid = match self.field(node, "type") {
                    Some(t) => {
                        let te = self.convert_type(t);
                        self.terms.alloc(
                            Term::ParseAux(Box::new(ParseAux::TypeExpr(te))),
                            self.span(t),
                        )
                    }
                    None => {
                        self.err("typed_binder: missing type annotation".to_string(), node);
                        self.alloc_bottom(span)
                    }
                };
                let functor = self.intern("pattern_var");
                let type_key = self.intern("type");
                let tid = self.terms.alloc(
                    Term::Fn {
                        functor,
                        pos_args: SmallVec::from_elem(name_tid, 1),
                        named_args: SmallVec::from_slice(&[(type_key, type_tid)]),
                    },
                    span,
                );
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
            BuildFrame::MatchBranch { node, has_guard } => {
                let span = self.span(node);
                let n = if has_guard { 3 } else { 2 };
                let drain_start = results.len() - n;
                // WI-537: carry the optional guard as a 3rd positional arg
                // (load.rs reshapes it to the named `guard: some(g)` slot).
                let mut args: SmallVec<[TermId; 4]> =
                    SmallVec::from_slice(&results[drain_start..drain_start + 2]);
                if has_guard {
                    args.push(results[drain_start + 2]);
                }
                results.truncate(drain_start);
                results.push(self.alloc_fn_term("match_branch", args, span));
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
                // The loader unwraps it and lowers via `type_expr_to_value`.
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
                    "lambda_expr",
                    SmallVec::from_slice(&[param, body]),
                    span,
                ));
            }
            BuildFrame::ProofStmt { node, target, strategy_name, using, has_conclude } => {
                // WI-538: `proof_stmt(body [, conclude]) { proof_meta }`.
                // Results order is [body, conclude?]; the target/strategy/
                // using clauses ride as a `ParseAux::ProofStmt` named
                // child the loader reads back off this parse term.
                let span = self.span(node);
                let n = if has_conclude { 2 } else { 1 };
                let drain_start = results.len() - n;
                let body = results[drain_start];
                let conclude = if has_conclude { Some(results[drain_start + 1]) } else { None };
                results.truncate(drain_start);
                let meta = Term::ParseAux(Box::new(ParseAux::ProofStmt(super::ir::ProofStmtIr {
                    target,
                    strategy_name,
                    using,
                    span,
                })));
                let meta_tid = self.terms.alloc(meta, span);
                let mut pos_args: SmallVec<[TermId; 4]> = SmallVec::new();
                pos_args.push(body);
                if let Some(c) = conclude {
                    pos_args.push(c);
                }
                let meta_key = self.intern("proof_meta");
                let functor = self.intern("proof_stmt");
                results.push(self.terms.alloc(
                    Term::Fn { functor, pos_args, named_args: SmallVec::from_slice(&[(meta_key, meta_tid)]) },
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

    /// WI-027: lower `(forall ?x in xs: body)` → `forall_in(?x, xs, tuple(body))`
    /// and `(some ?x in xs: body)` → `some_in(?x, xs, tuple(body))`. The binder
    /// `?x` shares its `VarId` with its uses inside `body` (both go through
    /// `get_or_create_var`), so the resolver can structurally substitute each
    /// concrete list element for the binder. The collection is any term (a list
    /// literal, a variable bound earlier in the rule, a call returning a list).
    fn convert_bounded_quantification(&mut self, node: Node) -> TermId {
        let span = self.span(node);
        // The `quantifier` field is an anonymous `forall` / `some` token; read its
        // source text. Own it as a `String` first so the error arm may borrow
        // `self` mutably.
        let q = self.field(node, "quantifier").map(|n| self.text(n).to_string());
        let functor = match q.as_deref() {
            Some("forall") => "forall_in",
            Some("some") => "some_in",
            other => {
                self.err(
                    &format!("unsupported bounded quantifier `{}`", other.unwrap_or("?")),
                    node,
                );
                "forall_in"
            }
        };
        let binder = match self.field(node, "binder") {
            Some(n) => {
                // A bare `?` binder mints a fresh anonymous var that does NOT
                // flow into the body, so the quantifier would bind nothing —
                // reject it loudly rather than silently iterate with an
                // unsubstituted body (loud-over-silent).
                if self.text(n) == "?" {
                    self.err("bounded quantifier binder must be a named variable (`?name`), not anonymous `?`", n);
                }
                self.convert_variable_node(n)
            }
            None => {
                self.err("bounded quantifier is missing its binder variable", node);
                self.alloc_bottom(span)
            }
        };
        let collection = match self.field(node, "collection") {
            Some(n) => self.convert_term(n),
            None => {
                self.err("bounded quantifier is missing its collection", node);
                self.alloc_bottom(span)
            }
        };
        let body: SmallVec<[TermId; 4]> = self.field(node, "body")
            .map(|n| self.convert_rule_body(n).into_iter().collect())
            .unwrap_or_default();
        let body_tuple = self.alloc_fn_term("tuple", body, span);
        self.alloc_fn_term(
            functor,
            SmallVec::from_slice(&[binder, collection, body_tuple]),
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
                        // Positional binding. WI-449: a parameterized positional
                        // value (`fact IndexedSeq[List[T], T]` → the `List[T]`
                        // slot) must PRESERVE its inner args rather than flatten to
                        // a bare `Ref(List)` (the old lossy "preserve compatibility"
                        // path, which diverged from the structure-keeping `provides`
                        // lowering and dropped `T`). Route through `convert_type_value`
                        // — the SAME structure-preserving converter the named arm
                        // above uses — so a `simple_type` still lowers to `Ref(Name)`
                        // but an `application` keeps its `Fn{base, …}` shape, letting
                        // the loader's `canonicalize_fact_binding_value` map it
                        // positional→named (byte-identical to `sort_inst_to_value`).
                        // Variable / tuple / arrow shapes keep `convert_term`.
                        let tid = match t.kind() {
                            "simple_type" | "application" => self.convert_type_value(t),
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
            "application" => {
                let name_node = self.field(node, "name").unwrap_or(node);
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
            // WI-366 B1: a WRITTEN effect-row in a term-position type-argument
            // slot (`fact Spec[E = {}]`). A parse `Term` has no structural
            // effect-row form, so the default arm below used to stringify `{}`
            // to `Ref("{}")` → an `unresolved name '{}'` load error (a written
            // row could not ride on a fact head). Carry the real `TypeExpr`
            // through `ParseAux` instead; the loader lowers it via the SAME
            // `lower_effect_row` the type-aware `provides` path uses, so the
            // fact-head and `provides` emissions produce a byte-identical
            // `effects_rows(EffectExpression)` Type (the empty `{}` closed-pure
            // row, and any ground row).
            "effect_row" => {
                let te = self.convert_type(node);
                self.terms.alloc(Term::ParseAux(Box::new(ParseAux::TypeExpr(te))), span)
            }
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

    /// Extract a Name from a type CST node (simple_type or application).
    fn convert_type_to_name(&mut self, node: Node) -> Name {
        // WI-311: `application` carries its base as an `identifier` field;
        // `simple_type` carries a `name` child. Prefer the field.
        let name_node = self.field(node, "name")
            .or_else(|| self.child_by_kind(node, "name"))
            .unwrap_or(node);
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
                "simple_type" | "application" | "variable_term" | "variable" | "tuple_type" => {
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
        let params: Vec<(Option<Symbol>, TypeExpr)> = if let Some(pn) = params_node {
            let mut cursor = pn.walk();
            pn.named_children(&mut cursor)
                .map(|child| match child.kind() {
                    "field_decl" => {
                        // Named param: (a: A) -> B — keep the name (spec §5.4)
                        // and the type.
                        let name = self.field(child, "name").map(|n| self.intern(self.text(n)));
                        let type_node = self.field(child, "type").unwrap_or(child);
                        (name, self.convert_type(type_node))
                    }
                    _ => (None, self.convert_type(child)),
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
        //
        // WI-327: route through [`convert_effect_into`] so `merge(…)`
        // flattens into multiple TypeExpr entries and `-E` lowers to
        // `EffectAbsent`.
        let mut effect_items: Vec<Effect> = Vec::new();
        for n in self.fields_by_name(node, "effect") {
            if !n.is_named() {
                continue;
            }
            self.convert_effect_into(n, &mut effect_items);
        }
        let effects: Vec<TypeExpr> =
            effect_items.into_iter().map(|e| e.type_expr).collect();

        TypeExpr::Arrow { params, return_type, effects }
    }

    /// WI-327: lower one effect-position CST node into one or more
    /// [`Effect`] entries. Bare label / variable / application / presence /
    /// absence forms append a single entry; `effect_merge` recurses into
    /// each child so a nested `merge(merge(A, B), C)` flattens to three
    /// entries.
    fn convert_effect_into(&mut self, node: Node, out: &mut Vec<Effect>) {
        match node.kind() {
            "effect_merge" => {
                let mut cursor = node.walk();
                for child in node.named_children(&mut cursor) {
                    self.convert_effect_into(child, out);
                }
            }
            // Single-entry forms — direct convert_type covers each.
            "simple_type"
            | "application"
            | "variable_term"
            | "effect_presence"
            | "effect_absence" => {
                out.push(Effect { type_expr: self.convert_type(node) });
            }
            // WI-478 (proposal 048): a guarded effect `E :- guard` (bare or
            // parenthesized) → one `EffectGuarded` entry.
            "guarded_effect" | "paren_guarded_effect" => {
                out.push(Effect { type_expr: self.convert_guarded_effect(node) });
            }
            _ => {
                // Unknown node — skip silently (mirrors prior behavior
                // for unexpected children).
            }
        }
    }

    /// WI-478: lower a `guarded_effect` (`E :- p`) or `paren_guarded_effect`
    /// (`( E :- p, q )`) CST node into a [`TypeExpr::EffectGuarded`]. The `effect`
    /// field is the guarded label (`_simple_effect`); the `guard` field is a single
    /// `_term` (bare) or a `rule_body` (paren) — both collected to a `Vec<TermId>`
    /// of goal terms.
    fn convert_guarded_effect(&mut self, node: Node) -> TypeExpr {
        let label = self.field(node, "effect")
            .map(|n| self.convert_type(n))
            .unwrap_or_else(|| {
                self.err("guarded effect missing label", node);
                let sym = self.intern("?");
                TypeExpr::Simple(Name::simple(sym, self.span(node)))
            });
        let guard: Vec<TermId> = match self.field(node, "guard") {
            Some(g) if g.kind() == "rule_body" => self.convert_rule_body(g),
            Some(g) => vec![self.convert_term(g)],
            None => {
                self.err("guarded effect missing guard", node);
                Vec::new()
            }
        };
        TypeExpr::EffectGuarded { label: Box::new(label), guard }
    }

    // ── Visibility ──────────────────────────────────────────────

    fn convert_visibility(&mut self, node: Node) -> Option<Visibility> {
        self.child_by_kind(node, "visibility").map(|v| {
            match self.text(v) {
                "internal" => Visibility::Internal,
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

        // Namespace body items
        let mut items = Vec::new();
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            match child.kind() {
                "name" | "import_clause" => {}
                _ => {
                    let converted = self.convert_items_at(child);
                    items.extend(converted);
                }
            }
        }

        Some(Namespace {
            name,
            imports,
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
            .unwrap_or_else(|| self.fresh_anon_type_var(span));

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

    /// WI-320 / proposal 045: desugar an `effects E = T` sort-item into the
    /// canonical pair
    ///   `sort E = T`  +  `requires EffectsRuntime[Effects = E]`
    /// at convert time. The rest of the loader treats the two pieces as
    /// ordinary `AbstractSort` + `RequiresDecl` items — no new loader hook,
    /// no new IR variant. Returning `Vec<Item>` lets one CST node fan out to
    /// two IR items; callers splice the result into their item list via
    /// `convert_items_at`.
    ///
    /// The grammar requires an explicit `= …` form (typical `effects E = ?`
    /// for an anonymous row variable, or `effects E = X` for one bound to a
    /// concrete carrier) — the bare `effects E` form would collide with
    /// `effects_clause` at the sort-content/operation-clause boundary. The
    /// `Vec::new()` arm below remains defensive against parses with no
    /// `definition` field; in practice the grammar guarantees one is present.
    fn convert_effects_sort_item(&mut self, node: Node) -> Vec<Item> {
        let Some(name) = self.field(node, "name").map(|n| self.convert_name(n)) else {
            // Grammar guarantees `name`; this arm fires only on tree-sitter
            // error recovery. Per CLAUDE.md 'avoid fallbacks, better know
            // about errors early' — record the diagnostic instead of
            // silently dropping the whole desugar, so the user sees
            // *something* attributing later `unresolved E` errors to a
            // malformed declaration here.
            self.err("effects_sort_item missing required `name` field", node);
            return Vec::new();
        };
        let visibility = self.convert_visibility(node);
        let meta = self.convert_meta_block(node);
        let span = self.span(node);

        let definition = self.field(node, "definition")
            .map(|def| self.convert_type(def))
            .unwrap_or_else(|| self.fresh_anon_type_var(span));

        let mut descriptions: Vec<String> = self.fields_by_name(node, "description")
            .into_iter()
            .map(|d| strip_description_delimiters(self.text(d)))
            .collect();
        if descriptions.is_empty() {
            if let TypeExpr::Variable { descriptions: ref var_descs, .. } = definition {
                descriptions = var_descs.clone();
            }
        }

        let abstract_sort = AbstractSort {
            visibility,
            name: name.clone(),
            definition,
            descriptions,
            meta,
            span,
        };

        // Build `EffectsRuntime[Effects = <row-var-name>]`. The base name is
        // bare `EffectsRuntime` — the loader resolves it through the prelude
        // imports just like every other reference to a stdlib sort. `Effects`
        // is EffectsRuntime's row-parameter slot (`sort Effects = ?` in
        // `prelude/effects-runtime.anthill` / `register_stdlib_scopes`).
        let effects_runtime_sym = self.intern("EffectsRuntime");
        let effects_param_sym = self.intern("Effects");
        let requires_type = TypeExpr::Parameterized {
            name: Name::simple(effects_runtime_sym, span),
            bindings: vec![SortBinding {
                param: Some(Name::simple(effects_param_sym, span)),
                bound: TypeExpr::Simple(name),
            }],
        };
        let requires_decl = RequiresDecl {
            type_expr: requires_type,
            span,
        };

        vec![
            Item::AbstractSort(abstract_sort),
            Item::RequiresDecl(requires_decl),
        ]
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

        let mut items = Vec::new();
        // WI-451 (§5.4): an enclosing type-param list `sort Spec[F[T], A, B]`
        // desugars into marked body items, PREPENDED so the params precede the
        // members that reference them. A simple param `A` → `sort A = ?`; a
        // higher-kinded `F[T]` → a `sort F { sort T = ? }` marked `is_type_param`.
        if let Some(list) = self.child_by_kind(node, "sort_type_param_list") {
            items.extend(self.desugar_sort_type_param_list(list));
        }
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            match child.kind() {
                "name" | "visibility" | "import_clause" | "meta_block"
                | "description_block" | "sort_type_param_list" => {}
                _ => {
                    let converted = self.convert_items_at(child);
                    items.extend(converted);
                }
            }
        }

        Some(SortWithBody {
            kind,
            is_type_param: false,
            visibility,
            name,
            descriptions,
            imports,
            items,
            meta,
            span,
        })
    }

    /// WI-451 (§5.4 non-rigid type-variable marker): desugar an enclosing sort
    /// type-param list `[F[T], A, B]` into marked body items.
    fn desugar_sort_type_param_list(&mut self, list: Node) -> Vec<Item> {
        self.children_by_kind(list, "sort_type_param")
            .into_iter()
            .map(|p| self.desugar_sort_type_param(p))
            .collect()
    }

    /// One enclosing type-param binder. A SIMPLE param `A` becomes `sort A = ?`
    /// (an `AbstractSort` whose definition is a fresh anonymous variable —
    /// byte-identical to the existing type-param form). A HIGHER-KINDED param
    /// `F[T]` becomes a `SortWithBody` marked `is_type_param: true` whose body
    /// holds its members (recursively desugared); the loader (WI-452) reads the
    /// marker to mint the carrier's backing var. A `= Default` keeps the default.
    fn desugar_sort_type_param(&mut self, node: Node) -> Item {
        let span = self.span(node);
        let name_sym = self.field(node, "name")
            .map(|n| self.intern(self.text(n)))
            .unwrap_or_else(|| self.intern("?"));
        let name = Name::simple(name_sym, span);

        // Higher-kinded `F[T]` carries its own member list → marked carrier; a simple
        // `A` → `sort A = ?`. No `= default` form (sort-param defaults are undefined by
        // §5.4 and the grammar does not admit one here). Shares the IR construction
        // with the WI-454 per-statement binder via `make_type_param_item`.
        let members = self
            .child_by_kind(node, "sort_type_param_list")
            .map(|list| self.desugar_sort_type_param_list(list));
        self.make_type_param_item(name, members, None, None, span)
    }

    /// WI-454 (§5.4 surface sugar): a per-statement non-rigid type-variable binder
    /// — `sort ?X` (the `?x` logical-var marker as the binder name) or `sort [X]`
    /// (standalone bracket binder). Desugars to EXACTLY the IR the WI-451
    /// enclosing-list param produces (`desugar_sort_type_param`): a BARE binder →
    /// `sort X = ?` (an `AbstractSort` with a fresh anonymous var); a STRUCTURED
    /// binder `sort ?F { sort ?T }` / `sort [F] { sort [T] }` → a `SortWithBody`
    /// marked `is_type_param` whose body holds the (recursively converted) members.
    /// So `sort CpsMonad\n  sort [F] { sort [T] }\n  sort [A]\nend` is
    /// parse-IR-equivalent to `sort CpsMonad[F[T], A]`.
    fn convert_sort_binder(&mut self, node: Node) -> Option<Item> {
        let span = self.span(node);
        let visibility = self.convert_visibility(node);
        // Name: a `?X` marker (strip the leading `?`) or a bracket `[X]` identifier.
        let name = if let Some(m) = self.field(node, "marker") {
            let text = self.text(m).to_string();
            let stripped = text.strip_prefix('?').unwrap_or(&text);
            // A bare `sort ?` (anonymous marker, no name) binds nothing referenceable
            // — a loud error, not a silent `_` (the `?`-each-occurrence-distinct
            // semantics elsewhere has no meaning for a NAMED type-param declaration).
            if stripped.is_empty() {
                self.err(
                    "anonymous `sort ?` binder binds no referenceable type variable — \
                     give it a name (`sort ?X`)"
                        .to_string(),
                    node,
                );
                return None;
            }
            Name::simple(self.intern(stripped), span)
        } else if let Some(n) = self.field(node, "name") {
            Name::simple(self.intern(self.text(n)), self.span(n))
        } else {
            self.err("sort binder is missing a name".to_string(), node);
            return None;
        };

        // A structured binder carries its (binder-only, grammar-enforced) members in
        // a brace body — `Some(members)` mints the `is_type_param`-marked carrier; a
        // bare binder (`None`) is the simple `sort X = ?` form.
        let members = self.child_by_kind(node, "sort_binder_body").map(|body| {
            let mut items = Vec::new();
            let mut cursor = body.walk();
            for child in body.named_children(&mut cursor) {
                items.extend(self.convert_items_at(child));
            }
            items
        });
        let meta = self.convert_meta_block(node);
        Some(self.make_type_param_item(name, members, visibility, meta, span))
    }

    /// Construct a non-rigid type-parameter `Item` — the SHARED desugar target of
    /// the WI-451 enclosing-list param (`desugar_sort_type_param`) and the WI-454
    /// per-statement binder (`convert_sort_binder`), so the two surface spellings
    /// cannot drift in the IR they produce. `Some(members)` → a higher-kinded
    /// carrier `F[…]`: a `SortWithBody` MARKED `is_type_param` whose body holds the
    /// (already-desugared) members. `None` → a simple param: `sort X = ?` (an
    /// `AbstractSort` with a fresh `?`). The loader (WI-452) reads the marker to mint
    /// the carrier's backing var.
    fn make_type_param_item(
        &mut self,
        name: Name,
        members: Option<Vec<Item>>,
        visibility: Option<Visibility>,
        meta: Option<MetaBlock>,
        span: Span,
    ) -> Item {
        match members {
            Some(items) => Item::SortWithBody(SortWithBody {
                kind: SortDeclKind::Sort,
                is_type_param: true,
                visibility,
                name,
                descriptions: Vec::new(),
                imports: Vec::new(),
                items,
                meta,
                span,
            }),
            None => Item::AbstractSort(AbstractSort {
                visibility,
                name,
                definition: self.fresh_anon_type_var(span),
                descriptions: Vec::new(),
                meta,
                span,
            }),
        }
    }

    /// A fresh anonymous type variable — the `?` an unspecified `sort X = ?`
    /// carries (a `Term::Var(Global)` wrapped in `TypeExpr::Variable`). Shared by
    /// `convert_abstract_sort`'s and `convert_effects_sort_item`'s missing-`=`
    /// fallbacks and the WI-451 type-param desugar, which all produce this IR.
    fn fresh_anon_type_var(&mut self, span: Span) -> TypeExpr {
        let sym = self.intern("_");
        let vid = crate::kb::term::VarId::new(self.next_var, sym);
        self.next_var += 1;
        let tid = self.terms.alloc(Term::Var(Var::Global(vid)), span);
        TypeExpr::Variable { term_id: tid, descriptions: Vec::new() }
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
            .filter_map(|c| {
                // proposal 049: heads and body share the `_goal` rule, so a `let_binding`
                // can appear here syntactically — reject it loudly (a head is a conclusion,
                // not a binding goal).
                if c.kind() == "let_binding" {
                    self.err("`let` binding is not allowed in a rule head", c);
                    None
                } else {
                    Some(RuleHead::Term(self.convert_term(c)))
                }
            })
            .collect()
    }

    /// proposal 049: lower a goal-position `let ?v = expr` to `unify(?v, expr)` — the same
    /// IR pratt builds for `?v <=> expr`. The bound var is a `variable_term`; the value is
    /// a `_term`. A malformed binding (a missing field) is a loud error.
    fn convert_let_binding(&mut self, node: Node) -> TermId {
        let span = self.span(node);
        let var = self.field(node, "var").map(|n| self.convert_term(n));
        let value = self.field(node, "value").map(|n| self.convert_term(n));
        match (var, value) {
            (Some(v), Some(e)) => self.alloc_fn_term("unify", SmallVec::from_slice(&[v, e]), span),
            _ => {
                self.err("malformed `let` binding (expected `let ?v = expr`)", node);
                self.alloc_fn_term("unify", SmallVec::new(), span)
            }
        }
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
        // WI-087: entries from `meta [...]` clauses. Accumulated across clauses
        // (like effects / requires / ensures in this same loop) so repeated
        // `meta` clauses merge rather than the last silently winning. Falls back
        // below to a trailing bare meta_block when no `meta` clause is present.
        let mut meta_entries: Vec<MetaEntry> = Vec::new();

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
                            self.convert_effect_into(type_child, &mut effects);
                        }
                    }
                    // WI-087: `meta [Marker, Key: value]` — the meta_block is
                    // nested one level under the meta_clause.
                    "meta_clause" => {
                        if let Some(mb) = self.convert_meta_block(child) {
                            meta_entries.extend(mb.entries);
                        }
                    }
                    _ => {}
                }
            }
        }

        let body = self.field(node, "body").map(|b| self.convert_expr_body(b));
        // Prefer the accumulated `meta` clauses; otherwise fall back to a trailing
        // bare meta_block (a direct child of the operation node).
        let meta = if meta_entries.is_empty() {
            self.convert_meta_block(node)
        } else {
            Some(MetaBlock { entries: meta_entries })
        };

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

    /// Convert a `const_declaration` CST node (proposal 039 / WI-084). Mirrors
    /// `convert_operation`'s description / visibility / optional-body handling,
    /// minus the operation-only machinery (params, type-params, clauses). The
    /// `type` field is mandatory in the grammar; a missing one means a parse
    /// error already occurred, so `?` bails (no silent default).
    fn convert_const(&mut self, node: Node) -> Option<Const> {
        self.reset_var_scope();
        let span = self.span(node);
        let name = self.field(node, "name").map(|n| self.convert_name(n))?;
        let visibility = self.convert_visibility(node);
        let ty = self.field(node, "type").map(|t| self.convert_type(t))?;
        let value = self.field(node, "value").map(|v| self.convert_expr_body(v));
        let meta = self.convert_meta_block(node);
        Some(Const { visibility, name, ty, value, meta, span })
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
        // `head` resolves the `_constraint_body` choice: a `quantified_constraint`
        // / `aggregation_constraint` node, or a `rule_body` for the plain denial
        // form (whose `:- guard` is hoisted to this `constraint_declaration` node).
        let head_node = self.field(node, "head")?;
        let body = match head_node.kind() {
            "quantified_constraint" => self.convert_quantified(head_node)?,
            "aggregation_constraint" => self.convert_aggregation(head_node)?,
            _ => {
                let head = self.convert_rule_body(head_node);
                let guard = self.field(node, "guard")
                    .map(|b| self.convert_rule_body(b));
                // WI-023: the `head -: conclusion` implication form is parsed but
                // not yet lowered/enforced — reject loudly rather than silently
                // dropping the conclusion.
                if self.field(node, "conclusion").is_some() {
                    self.err(
                        "constraint implication form `head -: conclusion` is not yet \
                         supported (use `:- guard`)",
                        node,
                    );
                }
                ConstraintBody::Denial { head, guard }
            }
        };
        let meta = self.convert_meta_block(node);
        Some(Constraint { label, body, meta, span })
    }

    fn convert_quantified(&mut self, node: Node) -> Option<ConstraintBody> {
        let quantifier = match self.field(node, "quantifier").map(|n| self.text(n)) {
            Some("forall") => Quantifier::Forall,
            Some("some") => Quantifier::Some,
            Some("one") => Quantifier::One,
            Some("lone") => Quantifier::Lone,
            Some("no") => Quantifier::No,
            _ => return None,
        };
        // Three binder shapes (grammar): `(?x: T)` typed sugar, `?x: cond`, `?x`.
        let (var, condition) = if let Some(tb) = self.field(node, "typed_binding") {
            self.convert_typed_binding(tb)
        } else {
            let var = self.field(node, "var")
                .map(|n| self.variable_name(n))
                .unwrap_or_default();
            let condition = self.field(node, "condition")
                .map(|b| self.convert_rule_body(b))
                .unwrap_or_default();
            (var, condition)
        };
        let body_node = self.field(node, "body")?;
        // WI-023: a `:- guard` / `-: conclusion` on the quantifier's `-:` body
        // hoists (via the inlined `_constraint_body`) onto this node; the loader
        // does not lower it, so reject loudly rather than silently dropping it.
        if self.field(node, "guard").is_some() || self.field(node, "conclusion").is_some() {
            self.err(
                "a `:- guard` / `-: conclusion` on a quantifier body is not yet supported",
                node,
            );
        }
        let body = Box::new(self.convert_constraint_inner_body(body_node));
        Some(ConstraintBody::Quantified { quantifier, var, condition, body })
    }

    /// Recursive `_constraint_body` in a quantifier's `-: body` slot: a nested
    /// quantifier/aggregation, or a leaf conjunction of patterns.
    fn convert_constraint_inner_body(&mut self, node: Node) -> ConstraintBody {
        match node.kind() {
            "quantified_constraint" => match self.convert_quantified(node) {
                Some(b) => b,
                None => {
                    self.err("malformed nested quantified constraint", node);
                    ConstraintBody::Patterns(Vec::new())
                }
            },
            "aggregation_constraint" => match self.convert_aggregation(node) {
                Some(b) => b,
                None => {
                    self.err("malformed nested aggregation constraint", node);
                    ConstraintBody::Patterns(Vec::new())
                }
            },
            _ => ConstraintBody::Patterns(self.convert_rule_body(node)),
        }
    }

    /// `(?x: T)` desugars (per grammar) to binder `x` with condition
    /// `TypeOf(occ: ?x, type: T)`.
    fn convert_typed_binding(&mut self, node: Node) -> (String, Vec<TermId>) {
        let var_node = self.field(node, "var");
        let var = var_node.map(|n| self.variable_name(n)).unwrap_or_default();
        let mut condition = Vec::new();
        if let (Some(vn), Some(tn)) = (var_node, self.field(node, "type")) {
            let span = self.span(node);
            let occ_term = self.convert_variable_node(vn);
            let type_term = self.convert_term(tn);
            let occ_field = self.intern("occ");
            let type_field = self.intern("type");
            let functor = self.intern("TypeOf");
            let named_args: SmallVec<[(Symbol, TermId); 2]> =
                SmallVec::from_slice(&[(occ_field, occ_term), (type_field, type_term)]);
            condition.push(self.terms.alloc(
                Term::Fn { functor, pos_args: SmallVec::new(), named_args },
                span,
            ));
        }
        (var, condition)
    }

    fn convert_aggregation(&mut self, node: Node) -> Option<ConstraintBody> {
        let aggregate = match self.field(node, "aggregate").map(|n| self.text(n)) {
            Some("count") => Aggregate::Count,
            Some("sum") => Aggregate::Sum,
            Some("min") => Aggregate::Min,
            Some("max") => Aggregate::Max,
            _ => return None,
        };
        let var = self.field(node, "var")
            .map(|n| self.variable_name(n))
            .unwrap_or_default();
        let condition = self.field(node, "condition")
            .map(|b| self.convert_rule_body(b))
            .unwrap_or_default();
        let body = self.field(node, "body")
            .map(|b| self.convert_rule_body(b))
            .unwrap_or_default();
        let op = match self.field(node, "op").map(|n| self.text(n)) {
            Some("<=") => CompareOp::Le,
            Some(">=") => CompareOp::Ge,
            Some("<") => CompareOp::Lt,
            Some(">") => CompareOp::Gt,
            Some("=") => CompareOp::Eq,
            Some("!=") => CompareOp::Ne,
            _ => return None,
        };
        let bound = self.field(node, "bound").map(|n| self.convert_term(n))?;
        Some(ConstraintBody::Aggregation { aggregate, var, condition, body, op, bound })
    }

    /// Binder name: the variable's source text without its leading `?`.
    fn variable_name(&self, node: Node) -> String {
        self.text(node).strip_prefix('?').unwrap_or("").to_string()
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
                // WI-311: bare references are now `name` (was `identifier`). A
                // single-segment name in tactic position is a bare tactic, like
                // the former `identifier` case (`then(smt, simplify)`); a dotted
                // name stays a qualified `Name`.
                let n = self.convert_name(node);
                if n.segments.len() == 1 {
                    Some(TacticArgValue::Tactic(Box::new(Tactic::Bare(n.segments[0]))))
                } else {
                    Some(TacticArgValue::Name(n))
                }
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
            | "bounded_quantification"
            | "application"
            | "ref_term"
            | "infix_term"
            | "prefix_term"
            | "field_access"
            | "set_literal"
            | "collection_literal"
            | "tuple_literal"
            | "paren_expr"
            | "identifier"
            | "name"
            // A lambda is a value expression collectible as a positional
            // argument: `map(xs, lambda x -> f(x))`. The grammar only
            // admits `lambda_expr` in `_fn_arg` / `_expr_body` positions,
            // so the other `is_term_kind` call sites (infix operands, dot
            // receivers, pattern contexts) never receive one.
            | "lambda_expr"
            // Goal-position `let ?v = expr` (proposal 049); lowered to `unify(?v, expr)`
            // by `visit_term`. Rejected in head position by `convert_rule_heads`.
            | "let_binding"
    )
}

/// `WorkKind` for visiting a collected call-argument child. A
/// `lambda_expr` argument must be visited as an `ExprBody` (only that
/// dispatch builds the lambda); every other argument kind is a plain
/// `Term`. `visit_expr_body` falls back to `visit_term` for non-lambda
/// nodes, so this stays correct if the grammar later admits more
/// `_expr_body` forms as arguments.
fn fn_arg_work_kind(kind: &str) -> WorkKind {
    if kind == "lambda_expr" {
        WorkKind::ExprBody
    } else {
        WorkKind::Term
    }
}

/// Check if a node kind is a pattern.
fn is_pattern_kind(kind: &str) -> bool {
    matches!(
        kind,
        "pattern_wildcard"
            | "pattern_var"
            | "typed_binder"
            | "pattern_typed"
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

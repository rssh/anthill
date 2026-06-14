/// Term printer — converts terms back to `.anthill` text.
///
/// Generic over `TermSource` so it works against either a `KnowledgeBase`
/// (hash-consed) or a `ParsedFile` (parse-IR). The canonical printed form
/// is the same in both cases — used by persistence-side retract matching.

use std::rc::Rc;

use crate::eval::value::Value;
use crate::intern::Symbol;
use crate::kb::KnowledgeBase;
use crate::kb::node_occurrence::{EffectExprNode, Expr, NodeOccurrence, TypeChild, TypeNode};
use crate::kb::term::{Literal, Term, TermId, TermSource, Var};

/// Append `s` quoted with `.anthill`-syntax escapes for `"`, `\`, `\n`,
/// `\r`, `\t`. Shared by `TermPrinter` and any other code that needs to
/// emit a string literal in canonical form.
pub fn write_anthill_string(s: &str, buf: &mut String) {
    buf.push('"');
    for ch in s.chars() {
        match ch {
            '"' => buf.push_str("\\\""),
            '\\' => buf.push_str("\\\\"),
            '\n' => buf.push_str("\\n"),
            '\r' => buf.push_str("\\r"),
            '\t' => buf.push_str("\\t"),
            _ => buf.push(ch),
        }
    }
    buf.push('"');
}

/// Prints terms as `.anthill` source text.
pub struct TermPrinter<'a, V: TermSource + ?Sized> {
    view: &'a V,
}

impl<'a> TermPrinter<'a, KnowledgeBase> {
    pub fn new(kb: &'a KnowledgeBase) -> Self {
        Self { view: kb }
    }

    /// Print a rule-body-atom occurrence as `.anthill` text (WI-246). Mirrors
    /// `write_term` over the occurrence `Expr` substrate (rule bodies are now
    /// occurrences, not terms); embedded `TermId` fields (patterns, params)
    /// defer to `write_term`. Used by CLI rule/query display.
    pub fn print_occurrence(&self, occ: &NodeOccurrence) -> String {
        let mut buf = String::new();
        self.write_occurrence(occ, &mut buf);
        buf
    }

    /// WI-318: render a Pattern-kind occurrence in surface form.
    /// Recurses into sub-patterns (Constructor.pos_args /
    /// Tuple.positional). Var-pattern's optional `type_ann` is rendered
    /// as `name: <type>` (the type is an Expr-kind occurrence). If a
    /// sub-occurrence isn't Pattern-kind (the reflection-meta-var case
    /// from term_pattern_as_expr_occ), delegate to `write_occurrence`
    /// so the term shape is rendered as data instead of the literal
    /// `<not-a-pattern>` placeholder.
    fn write_pattern(&self, occ: &NodeOccurrence, buf: &mut String) {
        use crate::kb::node_occurrence::Pattern;
        let Some(pat) = occ.as_pattern() else {
            // Expr-kind (or RuleHead) child in a pattern slot — render
            // via the generic occurrence writer so the term shape
            // surfaces faithfully.
            return self.write_occurrence(occ, buf);
        };
        match pat {
            Pattern::Var { name, type_ann } => {
                buf.push_str(self.view.sym_name(*name));
                if let Some(t) = type_ann {
                    buf.push_str(": ");
                    self.write_occurrence(t, buf);
                }
            }
            Pattern::Wildcard => buf.push('_'),
            Pattern::Literal { value } => self.write_literal(value, buf),
            Pattern::Constructor { name, pos_args, named_args } => {
                buf.push_str(self.view.sym_name(*name));
                buf.push('(');
                for (i, p) in pos_args.iter().enumerate() {
                    if i > 0 { buf.push_str(", "); }
                    self.write_pattern(p, buf);
                }
                // WI-445: named sub-patterns render `field: pat` after the
                // positionals (the `Foo(field: pat)` surface form).
                for (i, (field, p)) in named_args.iter().enumerate() {
                    if i > 0 || !pos_args.is_empty() { buf.push_str(", "); }
                    buf.push_str(self.view.sym_name(*field));
                    buf.push_str(": ");
                    self.write_pattern(p, buf);
                }
                buf.push(')');
            }
            Pattern::Tuple { positional, .. } => {
                buf.push('(');
                for (i, p) in positional.iter().enumerate() {
                    if i > 0 { buf.push_str(", "); }
                    self.write_pattern(p, buf);
                }
                buf.push(')');
            }
        }
    }

    /// Render a `Type`-child — a ground hash-consed type (`write_term`) or a
    /// nested occurrence (`write_occurrence`), uniformly (WI-348/349).
    fn write_type_child(&self, child: &TypeChild, buf: &mut String) {
        match child {
            TypeChild::Ground(t) => self.write_term(*t, buf),
            TypeChild::Node(occ) => self.write_occurrence(occ, buf),
        }
    }

    /// WI-361: render a field type carried as a [`Value`] (a `named_tuple` `fields`
    /// `List[TypeField]` element) — `Value::Term` is a hash-consed term, `Value::Node`
    /// a poisoned occurrence; both reuse the existing writers. A type is only ever
    /// `Term` or `Node`, so the fallback is unreachable.
    fn write_type_value(&self, v: &Value, buf: &mut String) {
        match v {
            Value::Term(t) => self.write_term(*t, buf),
            Value::Node(occ) => self.write_occurrence(occ, buf),
            _ => buf.push('?'),
        }
    }

    /// Render a `Type`-sort occurrence (WI-342 IR). Structural and faithful —
    /// `Parameterized` shows its `[param = value]` bindings (the part a
    /// `denoted` value-index like `Modify[c]` lives in), `denoted(..)` marks a
    /// value-in-type so it reads distinctly from a type argument.
    fn write_type_node(&self, tn: &TypeNode, buf: &mut String) {
        match tn {
            TypeNode::Denoted { value } => {
                buf.push_str("denoted(");
                self.write_occurrence(value, buf);
                buf.push(')');
            }
            TypeNode::Parameterized { base, bindings } => {
                self.write_type_child(base, buf);
                buf.push('[');
                for (i, (sym, val)) in bindings.iter().enumerate() {
                    if i > 0 { buf.push_str(", "); }
                    buf.push_str(self.view.sym_name(*sym));
                    buf.push_str(" = ");
                    self.write_type_child(val, buf);
                }
                buf.push(']');
            }
            TypeNode::EffectsRows { effects_expr } => {
                buf.push_str("effects_rows(");
                self.write_type_child(effects_expr, buf);
                buf.push(')');
            }
            TypeNode::Arrow { param, result, effects } => {
                self.write_type_child(param, buf);
                buf.push_str(" -> ");
                self.write_type_child(result, buf);
                buf.push_str(" ! ");
                self.write_type_child(effects, buf);
            }
            // WI-397: a compound-receiver projection `(a.b).M` — receiver then `.member`.
            TypeNode::ExprCarried { value, member } => {
                self.write_type_child(value, buf);
                buf.push('.');
                self.write_type_child(member, buf);
            }
            TypeNode::NamedTuple { fields } => {
                // WI-361: `fields` is a `Value`-carried `List[TypeField]`; decode it
                // via the one shared decoder (the typer's `named_tuple_fields` uses
                // the same) and render `(n: T, …)`.
                buf.push('(');
                let pairs =
                    crate::kb::typing::list_records_to_pairs(self.view, fields, "name", "type");
                for (i, (name, ty)) in pairs.iter().enumerate() {
                    if i > 0 {
                        buf.push_str(", ");
                    }
                    buf.push_str(self.view.sym_name(*name));
                    buf.push_str(": ");
                    self.write_type_value(ty, buf);
                }
                buf.push(')');
            }
        }
    }

    /// Render an `EffectExpression`-sort occurrence (the row algebra, WI-342).
    fn write_effect_expr_node(&self, en: &EffectExprNode, buf: &mut String) {
        match en {
            EffectExprNode::Merge { left, right } => {
                self.write_type_child(left, buf);
                buf.push_str(", ");
                self.write_type_child(right, buf);
            }
            EffectExprNode::Present { label } => self.write_type_child(label, buf),
            EffectExprNode::Absent { label } => {
                buf.push('-');
                self.write_type_child(label, buf);
            }
            EffectExprNode::Open { tail } => self.write_type_child(tail, buf),
            EffectExprNode::EmptyRow => buf.push_str("{}"),
        }
    }

    fn write_occurrence(&self, occ: &NodeOccurrence, buf: &mut String) {
        if occ.as_pattern().is_some() {
            self.write_pattern(occ, buf);
            return;
        }
        // WI-348/349: a `Type` / `EffectExpr` occurrence (e.g. a `Modify[c]`
        // effect label on an `OperationInfo` value fact) is not an `Expr`, so it
        // used to fall to the `<head>` placeholder. Render it structurally —
        // including `Parameterized.bindings`, which `TermView` hides — so query
        // output and diagnostics show the actual type, not `<head>`.
        if let Some(tn) = occ.as_type() {
            self.write_type_node(tn, buf);
            return;
        }
        if let Some(en) = occ.as_effect_expr() {
            self.write_effect_expr_node(en, buf);
            return;
        }
        let Some(expr) = occ.as_expr() else {
            // A genuine rule-head wrapper has no surface body form; bodies are Expr.
            buf.push_str("<head>");
            return;
        };
        match expr {
            Expr::Var(Var::Global(vid)) => {
                buf.push('?');
                buf.push_str(self.view.sym_name(vid.name()));
            }
            Expr::Var(Var::DeBruijn(n)) => buf.push_str(&format!("?#{n}")),
            Expr::Var(Var::Rigid(vid)) => {
                buf.push('!');
                buf.push_str(self.view.sym_name(vid.name()));
            }
            Expr::Const(lit) => self.write_literal(lit, buf),
            Expr::Ref(sym) | Expr::Ident(sym) | Expr::VarRef { name: sym } => {
                buf.push_str(self.view.sym_name(*sym));
            }
            Expr::Bottom => buf.push_str("bottom"),
            Expr::Apply { functor, pos_args, named_args, .. } => {
                let fname = self.view.sym_name(*functor);
                // Round-trip the forall_impl encoding to surface syntax — the
                // occurrence twin of `write_term`'s special case.
                if fname == "forall_impl" && pos_args.len() == 3 && named_args.is_empty() {
                    if let (Some(binders), Some(ants), Some(cons)) = (
                        self.occ_unwrap_tuple(&pos_args[0]),
                        self.occ_unwrap_tuple(&pos_args[1]),
                        self.occ_unwrap_tuple(&pos_args[2]),
                    ) {
                        buf.push_str("(forall(");
                        self.write_occ_inner(binders, &[], buf);
                        buf.push_str("), ");
                        self.write_occ_inner(ants, &[], buf);
                        buf.push_str(" -: ");
                        self.write_occ_inner(cons, &[], buf);
                        buf.push(')');
                        return;
                    }
                }
                self.write_occ_fn(fname, pos_args, named_args, buf);
            }
            Expr::ApplyWithin { functor, args, named_args, .. } => {
                self.write_occ_fn(self.view.sym_name(*functor), args, named_args, buf);
            }
            Expr::Constructor { name, pos_args, named_args }
            | Expr::Instantiation { name, pos_args, named_args }
            | Expr::ConstructorWithin { name, pos_args, named_args, .. } => {
                self.write_occ_fn(self.view.sym_name(*name), pos_args, named_args, buf);
            }
            Expr::DotApply { receiver, name, pos_args, named_args } => {
                self.write_occurrence(receiver, buf);
                buf.push('.');
                buf.push_str(self.view.sym_name(*name));
                if !pos_args.is_empty() || !named_args.is_empty() {
                    self.write_occ_args(pos_args, named_args, buf);
                }
            }
            Expr::HoApply { predicate, args }
            | Expr::HoApplyWithin { predicate, args, .. } => {
                self.write_occurrence(predicate, buf);
                self.write_occ_args(args, &[], buf);
            }
            Expr::If { condition, then_branch, else_branch } => {
                buf.push_str("if ");
                self.write_occurrence(condition, buf);
                buf.push_str(" then ");
                self.write_occurrence(then_branch, buf);
                buf.push_str(" else ");
                self.write_occurrence(else_branch, buf);
            }
            Expr::Let { pattern, value, body, .. } => {
                // WI-318: pattern is a Pattern-kind occurrence.
                buf.push_str("let ");
                self.write_pattern(pattern, buf);
                buf.push_str(" = ");
                self.write_occurrence(value, buf);
                buf.push_str(" in ");
                self.write_occurrence(body, buf);
            }
            Expr::Lambda { param, body }
            | Expr::LambdaWithin { param, body, .. } => {
                // WI-318: `param` is a Pattern-kind occurrence — render
                // structurally via `write_pattern`.
                buf.push('(');
                self.write_pattern(param, buf);
                buf.push_str(") => ");
                self.write_occurrence(body, buf);
            }
            Expr::Match { scrutinee, branches } => {
                buf.push_str("match ");
                self.write_occurrence(scrutinee, buf);
                buf.push_str(" { ");
                for b in branches.iter() {
                    // WI-318: b.pattern is a Pattern-kind occurrence.
                    self.write_pattern(&b.pattern, buf);
                    buf.push_str(" => ");
                    self.write_occurrence(&b.body, buf);
                    buf.push_str("; ");
                }
                buf.push('}');
            }
            Expr::ListLit(es) => self.write_occ_seq('[', ']', es, buf),
            Expr::SetLit(es) => self.write_occ_seq('{', '}', es, buf),
            Expr::TupleLit { positional, named } => {
                buf.push('(');
                self.write_occ_inner(positional, named, buf);
                buf.push(')');
            }
            Expr::RequirementAtSort { chain, slot } => {
                buf.push_str("requirement_at_sort(");
                self.write_occurrence(chain, buf);
                buf.push_str(&format!(", {slot})"));
            }
            Expr::ConstructRequirement { impl_functor, requirements } => {
                buf.push_str("construct_requirement(");
                buf.push_str(self.view.sym_name(*impl_functor));
                buf.push_str(", ");
                self.write_occ_seq('[', ']', requirements, buf);
                buf.push(')');
            }
        }
    }

    fn write_occ_fn(
        &self,
        fname: &str,
        pos: &[Rc<NodeOccurrence>],
        named: &[(Symbol, Rc<NodeOccurrence>)],
        buf: &mut String,
    ) {
        buf.push_str(fname);
        if !pos.is_empty() || !named.is_empty() {
            self.write_occ_args(pos, named, buf);
        }
    }

    fn write_occ_args(
        &self,
        pos: &[Rc<NodeOccurrence>],
        named: &[(Symbol, Rc<NodeOccurrence>)],
        buf: &mut String,
    ) {
        buf.push('(');
        self.write_occ_inner(pos, named, buf);
        buf.push(')');
    }

    fn write_occ_inner(
        &self,
        pos: &[Rc<NodeOccurrence>],
        named: &[(Symbol, Rc<NodeOccurrence>)],
        buf: &mut String,
    ) {
        let mut first = true;
        for c in pos.iter() {
            if !first { buf.push_str(", "); }
            first = false;
            self.write_occurrence(c, buf);
        }
        for (sym, c) in named.iter() {
            if !first { buf.push_str(", "); }
            first = false;
            buf.push_str(self.view.sym_name(*sym));
            buf.push_str(": ");
            self.write_occurrence(c, buf);
        }
    }

    fn write_occ_seq(
        &self,
        open: char,
        close: char,
        es: &[Rc<NodeOccurrence>],
        buf: &mut String,
    ) {
        buf.push(open);
        for (i, e) in es.iter().enumerate() {
            if i > 0 { buf.push_str(", "); }
            self.write_occurrence(e, buf);
        }
        buf.push(close);
    }

    /// If `occ` is a `tuple(...)` apply occurrence with no named args, return a
    /// borrowed slice over its positional children — the occurrence twin of
    /// `unwrap_tuple`, used by the `forall_impl` surface-syntax rendering.
    fn occ_unwrap_tuple<'o>(&self, occ: &'o NodeOccurrence) -> Option<&'o [Rc<NodeOccurrence>]> {
        match occ.as_expr()? {
            Expr::Apply { functor, pos_args, named_args, .. }
                if self.view.sym_name(*functor) == "tuple" && named_args.is_empty() =>
            {
                Some(pos_args)
            }
            _ => None,
        }
    }
}

impl<'a, V: TermSource + ?Sized> TermPrinter<'a, V> {
    /// Construct a printer over an arbitrary `TermSource`.
    pub fn over(view: &'a V) -> Self {
        Self { view }
    }

    /// Print a term as `.anthill` source text.
    pub fn print_term(&self, id: TermId) -> String {
        let mut buf = String::new();
        self.write_term(id, &mut buf);
        buf
    }

    /// If `id` is a `tuple(...)` Fn term with no named args, return a
    /// borrowed slice over its positional contents. Used by the
    /// `forall_impl` pretty-printer.
    fn unwrap_tuple(&self, id: TermId) -> Option<&[TermId]> {
        match self.view.term(id) {
            Term::Fn { functor, pos_args, named_args }
                if self.view.sym_name(*functor) == "tuple" && named_args.is_empty() =>
            {
                Some(pos_args.as_slice())
            }
            _ => None,
        }
    }

    fn write_comma_sep(&self, ts: &[TermId], buf: &mut String) {
        for (i, &t) in ts.iter().enumerate() {
            if i > 0 { buf.push_str(", "); }
            self.write_term(t, buf);
        }
    }

    /// The element terms of a GROUND cons/nil list spine (named
    /// `cons(head: …, tail: …)` or positional `cons(…, …)`, ending in a
    /// nullary `nil`), or `None` for anything else — a var tail, a
    /// non-nil end, a non-list term. Used by `write_term` to print list
    /// spines as `[…]` literals: the bare-name nullary print (`nil`)
    /// reloads as a NAME REFERENCE, which no longer unifies with
    /// `nil()` / `cons(…)` patterns — the round-trip bug that made
    /// runtime-persisted work items invisible to the workflow rules.
    pub fn unwrap_list_spine(&self, id: TermId) -> Option<Vec<TermId>> {
        let mut items = Vec::new();
        let mut cur = id;
        loop {
            match self.view.term(cur) {
                Term::Fn { functor, pos_args, named_args } => {
                    let fname = self.view.sym_name(*functor);
                    let short = fname.rsplit('.').next().unwrap_or(fname);
                    if short == "nil" && pos_args.is_empty() && named_args.is_empty() {
                        return Some(items);
                    }
                    if short != "cons" {
                        return None;
                    }
                    let named_head = named_args
                        .iter()
                        .find(|(s, _)| self.view.sym_name(*s) == "head")
                        .map(|(_, t)| *t);
                    let named_tail = named_args
                        .iter()
                        .find(|(s, _)| self.view.sym_name(*s) == "tail")
                        .map(|(_, t)| *t);
                    let (head, tail) = match (named_head, named_tail) {
                        // EXACTLY head+tail — a cons carrying extra named or
                        // positional args is not a list spine; folding it
                        // would silently drop the extras.
                        (Some(h), Some(t))
                            if named_args.len() == 2 && pos_args.is_empty() =>
                        {
                            (h, t)
                        }
                        (None, None) if pos_args.len() == 2 && named_args.is_empty() => {
                            (pos_args[0], pos_args[1])
                        }
                        _ => return None,
                    };
                    items.push(head);
                    cur = tail;
                }
                _ => return None,
            }
        }
    }

    fn write_term(&self, id: TermId, buf: &mut String) {
        match self.view.term(id) {
            Term::Const(lit) => self.write_literal(lit, buf),
            Term::Var(Var::Global(vid)) => {
                buf.push('?');
                buf.push_str(self.view.sym_name(vid.name()));
            }
            Term::Var(Var::DeBruijn(n)) => {
                buf.push_str(&format!("?#{n}"));
            }
            Term::Var(Var::Rigid(vid)) => {
                buf.push('!');
                buf.push_str(self.view.sym_name(vid.name()));
            }
            Term::Fn { functor, pos_args, named_args } => {
                // A ground cons/nil spine prints as a list literal (see
                // `unwrap_list_spine` for why the cons form must not be
                // written to disk).
                if let Some(items) = self.unwrap_list_spine(id) {
                    buf.push('[');
                    self.write_comma_sep(&items, buf);
                    buf.push(']');
                    return;
                }
                let fname = self.view.sym_name(*functor);
                // The parse-IR list form (`[…]` parses to `Fn(ListLiteral,
                // pos_args)`) prints back as a bracket literal too, so the
                // KB-side and parse-side canonical forms agree — the
                // content-keyed retract match in the file store compares
                // exactly these two prints.
                if fname == "ListLiteral" && named_args.is_empty() {
                    buf.push('[');
                    self.write_comma_sep(pos_args, buf);
                    buf.push(']');
                    return;
                }
                // Round-trip the forall_impl encoding produced by
                // convert_nested_implication back to surface syntax.
                if fname == "forall_impl"
                    && pos_args.len() == 3
                    && named_args.is_empty()
                {
                    if let (Some(binders), Some(ants), Some(cons)) = (
                        self.unwrap_tuple(pos_args[0]),
                        self.unwrap_tuple(pos_args[1]),
                        self.unwrap_tuple(pos_args[2]),
                    ) {
                        buf.push_str("(forall(");
                        self.write_comma_sep(binders, buf);
                        buf.push_str("), ");
                        self.write_comma_sep(ants, buf);
                        buf.push_str(" -: ");
                        self.write_comma_sep(cons, buf);
                        buf.push(')');
                        return;
                    }
                }
                buf.push_str(fname);
                if !pos_args.is_empty() || !named_args.is_empty() {
                    buf.push('(');
                    let mut first = true;
                    for &tid in pos_args.iter() {
                        if !first { buf.push_str(", "); }
                        first = false;
                        self.write_term(tid, buf);
                    }
                    for &(sym, tid) in named_args.iter() {
                        if !first { buf.push_str(", "); }
                        first = false;
                        buf.push_str(self.view.sym_name(sym));
                        buf.push_str(": ");
                        self.write_term(tid, buf);
                    }
                    buf.push(')');
                }
            }
            Term::Ref(sym) => {
                buf.push_str(self.view.sym_name(*sym));
            }
            Term::Ident(sym) => {
                buf.push_str(self.view.sym_name(*sym));
            }
            Term::Bottom => {
                buf.push_str("bottom");
            }
            Term::ParseAux(aux) => {
                // Parse-only variant; reaches the printer only when
                // it's invoked on a parse-side Term (e.g. for an error
                // message). KB-side it never appears — the loader
                // strips it before any KB allocation. Print the inner
                // payload Debug-format so diagnostics carry the
                // annotation/type-args text even though it's not in
                // surface syntax.
                use crate::parse::ir::ParseAux;
                match aux.as_ref() {
                    ParseAux::TypeExpr(te) => buf.push_str(&format!("<type-anno {:?}>", te)),
                    ParseAux::SortBindings(b) => buf.push_str(&format!("<type-args {:?}>", b)),
                }
            }
        }
    }

    fn write_literal(&self, lit: &Literal, buf: &mut String) {
        match lit {
            Literal::Int(n) => {
                buf.push_str(&n.to_string());
            }
            Literal::BigInt(n) => {
                buf.push_str(&n.to_string());
            }
            Literal::Float(f) => {
                let s = f.to_string();
                buf.push_str(&s);
                // Ensure there's a decimal point so it parses back as float
                if !s.contains('.') {
                    buf.push_str(".0");
                }
            }
            Literal::String(s) => write_anthill_string(s, buf),
            Literal::Bool(b) => {
                buf.push_str(if *b { "true" } else { "false" });
            }
            Literal::Handle(kind, id) => {
                buf.push_str(&format!("<handle:{:?}:{}>", kind, id));
            }
        }
    }
}

/// Print a fact as a `fact` declaration in `.anthill` syntax. Generic
/// over `TermSource` so persistence's retract path can canonicalize both
/// live-KB heads and parse-IR heads through the same code.
pub fn print_fact<V: TermSource + ?Sized>(view: &V, term: TermId, meta: Option<TermId>) -> String {
    let printer = TermPrinter::over(view);
    let mut out = String::from("fact ");
    out.push_str(&printer.print_term(term));
    if let Some(meta_id) = meta {
        out.push_str(" {\n  ");
        out.push_str(&printer.print_term(meta_id));
        out.push_str("\n}");
    }
    out.push('\n');
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kb::term::Literal;
    use ordered_float::OrderedFloat;
    use smallvec::SmallVec;

    #[test]
    fn print_int_literal() {
        let mut kb = KnowledgeBase::new();
        let t = kb.alloc(Term::Const(Literal::Int(42)));
        let printer = TermPrinter::new(&kb);
        assert_eq!(printer.print_term(t), "42");
    }

    #[test]
    fn print_float_literal() {
        let mut kb = KnowledgeBase::new();
        let t = kb.alloc(Term::Const(Literal::Float(OrderedFloat(3.14))));
        let printer = TermPrinter::new(&kb);
        assert_eq!(printer.print_term(t), "3.14");
    }

    #[test]
    fn print_string_literal() {
        let mut kb = KnowledgeBase::new();
        let t = kb.alloc(Term::Const(Literal::String("hello \"world\"".into())));
        let printer = TermPrinter::new(&kb);
        assert_eq!(printer.print_term(t), "\"hello \\\"world\\\"\"");
    }

    #[test]
    fn print_bool_literal() {
        let mut kb = KnowledgeBase::new();
        let t = kb.alloc(Term::Const(Literal::Bool(true)));
        let printer = TermPrinter::new(&kb);
        assert_eq!(printer.print_term(t), "true");
    }

    #[test]
    fn print_var() {
        let mut kb = KnowledgeBase::new();
        let sym = kb.intern("x");
        let vid = kb.fresh_var(sym);
        let t = kb.alloc(Term::Var(Var::Global(vid)));
        let printer = TermPrinter::new(&kb);
        assert_eq!(printer.print_term(t), "?x");
    }

    #[test]
    fn print_nullary_fn() {
        let mut kb = KnowledgeBase::new();
        let t = kb.make_name_term("Account");
        let printer = TermPrinter::new(&kb);
        assert_eq!(printer.print_term(t), "Account");
    }

    #[test]
    fn print_fn_with_positional_args() {
        let mut kb = KnowledgeBase::new();
        let sym = kb.intern("parent");
        let a = kb.alloc(Term::Const(Literal::String("alice".into())));
        let b = kb.alloc(Term::Const(Literal::String("bob".into())));
        let t = kb.alloc(Term::Fn {
            functor: sym,
            pos_args: SmallVec::from_slice(&[a, b]),
            named_args: SmallVec::new(),
        });
        let printer = TermPrinter::new(&kb);
        assert_eq!(printer.print_term(t), "parent(\"alice\", \"bob\")");
    }

    #[test]
    fn print_fn_with_named_args() {
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("Account");
        let id_sym = kb.intern("id");
        let name_sym = kb.intern("name");
        let id_val = kb.alloc(Term::Const(Literal::String("A001".into())));
        let name_val = kb.alloc(Term::Const(Literal::String("Savings".into())));
        let t = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[
                (id_sym, id_val),
                (name_sym, name_val),
            ]),
        });
        let printer = TermPrinter::new(&kb);
        assert_eq!(
            printer.print_term(t),
            "Account(id: \"A001\", name: \"Savings\")"
        );
    }

    #[test]
    fn print_bottom() {
        let mut kb = KnowledgeBase::new();
        let t = kb.alloc(Term::Bottom);
        let printer = TermPrinter::new(&kb);
        assert_eq!(printer.print_term(t), "bottom");
    }

    #[test]
    fn print_fact_no_meta() {
        let mut kb = KnowledgeBase::new();
        let sym = kb.intern("Eq");
        let t_sym = kb.intern("T");
        let int = kb.make_name_term("Int64");
        let t = kb.alloc(Term::Fn {
            functor: sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(t_sym, int)]),
        });
        let out = print_fact(&kb, t, None);
        assert_eq!(out, "fact Eq(T: Int64)\n");
    }
}

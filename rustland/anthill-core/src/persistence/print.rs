/// Term printer — converts terms back to `.anthill` text.
///
/// Generic over `TermSource` so it works against either a `KnowledgeBase`
/// (hash-consed) or a `ParsedFile` (parse-IR). The canonical printed form
/// is the same in both cases — used by persistence-side retract matching.

use std::rc::Rc;

use crate::intern::Symbol;
use crate::kb::KnowledgeBase;
use crate::kb::node_occurrence::{Expr, NodeOccurrence};
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

    fn write_occurrence(&self, occ: &NodeOccurrence, buf: &mut String) {
        let Some(expr) = occ.as_expr() else {
            // A rule-head wrapper has no surface body form; bodies are Expr.
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
                buf.push_str("let ");
                self.write_term(*pattern, buf);
                buf.push_str(" = ");
                self.write_occurrence(value, buf);
                buf.push_str(" in ");
                self.write_occurrence(body, buf);
            }
            Expr::Lambda { param, body }
            | Expr::LambdaWithin { param, body, .. } => {
                buf.push('(');
                self.write_term(*param, buf);
                buf.push_str(") => ");
                self.write_occurrence(body, buf);
            }
            Expr::Match { scrutinee, branches } => {
                buf.push_str("match ");
                self.write_occurrence(scrutinee, buf);
                buf.push_str(" { ");
                for b in branches.iter() {
                    self.write_term(b.pattern, buf);
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
                let fname = self.view.sym_name(*functor);
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
        let int = kb.make_name_term("Int");
        let t = kb.alloc(Term::Fn {
            functor: sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(t_sym, int)]),
        });
        let out = print_fact(&kb, t, None);
        assert_eq!(out, "fact Eq(T: Int)\n");
    }
}

/// Term printer — converts terms back to `.anthill` text.
///
/// Generic over `TermSource` so it works against either a `KnowledgeBase`
/// (hash-consed) or a `ParsedFile` (parse-IR). The canonical printed form
/// is the same in both cases — used by persistence-side retract matching.

use crate::kb::KnowledgeBase;
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

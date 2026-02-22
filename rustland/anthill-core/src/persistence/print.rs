/// Term printer — converts KB terms back to `.anthill` text.
///
/// This is the inverse of parsing: given a `TermId` + `&KnowledgeBase`,
/// produce the textual representation suitable for writing to `.anthill` files.

use crate::kb::KnowledgeBase;
use crate::kb::term::{Literal, Term, TermId};

/// Prints KB terms as `.anthill` source text.
pub struct TermPrinter<'a> {
    kb: &'a KnowledgeBase,
}

impl<'a> TermPrinter<'a> {
    pub fn new(kb: &'a KnowledgeBase) -> Self {
        Self { kb }
    }

    /// Print a term as `.anthill` source text.
    pub fn print_term(&self, id: TermId) -> String {
        let mut buf = String::new();
        self.write_term(id, &mut buf);
        buf
    }

    fn write_term(&self, id: TermId, buf: &mut String) {
        match self.kb.get_term(id) {
            Term::Const(lit) => self.write_literal(lit, buf),
            Term::Var(vid) => {
                buf.push('?');
                buf.push_str(self.kb.resolve_sym(vid.name()));
            }
            Term::Fn { functor, pos_args, named_args } => {
                buf.push_str(self.kb.resolve_sym(*functor));
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
                        buf.push_str(self.kb.resolve_sym(sym));
                        buf.push_str(": ");
                        self.write_term(tid, buf);
                    }
                    buf.push(')');
                }
            }
            Term::Ref(sym) => {
                buf.push_str(self.kb.resolve_sym(*sym));
            }
            Term::Ident(sym) => {
                buf.push_str(self.kb.resolve_sym(*sym));
            }
            Term::Bottom => {
                buf.push_str("bottom");
            }
        }
    }

    fn write_literal(&self, lit: &Literal, buf: &mut String) {
        match lit {
            Literal::Int(n) => {
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
            Literal::String(s) => {
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
            Literal::Bool(b) => {
                buf.push_str(if *b { "true" } else { "false" });
            }
        }
    }
}

/// Print a fact as a `fact` declaration in `.anthill` syntax.
///
/// Produces text like: `fact Term` or `fact Term { meta }`
pub fn print_fact(kb: &KnowledgeBase, term: TermId, meta: Option<TermId>) -> String {
    let printer = TermPrinter::new(kb);
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
        let t = kb.alloc(Term::Var(vid));
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

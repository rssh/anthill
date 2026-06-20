/// Pratt parser for operator precedence desugaring.
///
/// The tree-sitter grammar produces flat infix chains: `[a, +, b, *, c]`.
/// This module applies operator precedence and associativity to produce
/// nested `Term::Fn` calls: `add(a, mul(b, c))`.

use smallvec::SmallVec;

use crate::intern::SymbolTable;
use crate::kb::term::{Term, TermId};
use crate::span::Span;
use super::ir::SimpleTermStore;

// ── Operator properties ─────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Assoc {
    Left,
    Right,
    None,
}

struct InfixEntry {
    priority: u8,
    assoc: Assoc,
    functor: &'static str,
    /// For ternary: continuation token (e.g. "@" for `->`, ":" for `?`).
    /// If Some, after the middle operand expect this token, then parse third operand.
    continuation: Option<ContinuationEntry>,
}

struct ContinuationEntry {
    token: &'static str,
    functor: &'static str,
}

pub(crate) struct PrefixEntry {
    priority: u8,
    pub(crate) functor: &'static str,
}

// ── Dictionary ──────────────────────────────────────────────────

fn infix_entry(op: &str) -> Option<&'static InfixEntry> {
    static TABLE: &[(&str, InfixEntry)] = &[
        ("|",  InfixEntry { priority: 1, assoc: Assoc::Left,  functor: "or",  continuation: None }),
        ("or", InfixEntry { priority: 1, assoc: Assoc::Left,  functor: "or",  continuation: None }),
        ("&",  InfixEntry { priority: 2, assoc: Assoc::Left,  functor: "and", continuation: None }),
        ("and",InfixEntry { priority: 2, assoc: Assoc::Left,  functor: "and", continuation: None }),
        ("=",  InfixEntry { priority: 3, assoc: Assoc::None,  functor: "eq",  continuation: None }),
        ("!=", InfixEntry { priority: 3, assoc: Assoc::None,  functor: "neq", continuation: None }),
        // WI-522 / proposal 049: `<=>` = unify (anthill.kernel.unify). It lexes as one
        // `operator_symbol` token (the regex matches the longest run, so `<=>` wins over
        // `<=`); here it maps to the `unify` functor. The resolver `builtin_unify` is WI-523.
        ("<=>",InfixEntry { priority: 3, assoc: Assoc::None,  functor: "unify", continuation: None }),
        ("<",  InfixEntry { priority: 4, assoc: Assoc::None,  functor: "lt",  continuation: None }),
        ("<=", InfixEntry { priority: 4, assoc: Assoc::None,  functor: "lte", continuation: None }),
        (">",  InfixEntry { priority: 4, assoc: Assoc::None,  functor: "gt",  continuation: None }),
        (">=", InfixEntry { priority: 4, assoc: Assoc::None,  functor: "gte", continuation: None }),
        ("+",  InfixEntry { priority: 5, assoc: Assoc::Left,  functor: "add", continuation: None }),
        ("-",  InfixEntry { priority: 5, assoc: Assoc::Left,  functor: "sub", continuation: None }),
        ("*",  InfixEntry { priority: 6, assoc: Assoc::Left,  functor: "mul", continuation: None }),
        ("/",  InfixEntry { priority: 6, assoc: Assoc::Left,  functor: "div", continuation: None }),
        ("%",  InfixEntry { priority: 6, assoc: Assoc::Left,  functor: "mod", continuation: None }),
        ("mod",InfixEntry { priority: 6, assoc: Assoc::Left,  functor: "mod", continuation: None }),
        ("div",InfixEntry { priority: 6, assoc: Assoc::Left,  functor: "div", continuation: None }),
        ("^",  InfixEntry { priority: 7, assoc: Assoc::Right, functor: "pow", continuation: None }),
        ("->", InfixEntry {
            priority: 8,
            assoc: Assoc::Right,
            functor: "arrow",
            continuation: Some(ContinuationEntry { token: "@", functor: "arrow_effect" }),
        }),
    ];
    TABLE.iter().find(|(k, _)| *k == op).map(|(_, v)| v)
}

pub(crate) fn prefix_entry(op: &str) -> Option<&'static PrefixEntry> {
    static TABLE: &[(&str, PrefixEntry)] = &[
        ("!",   PrefixEntry { priority: 9, functor: "not" }),
        ("not", PrefixEntry { priority: 9, functor: "not" }),
        ("-",   PrefixEntry { priority: 9, functor: "neg" }),
    ];
    TABLE.iter().find(|(k, _)| *k == op).map(|(_, v)| v)
}

// ── Elements ────────────────────────────────────────────────────

/// An element in a flat infix chain (alternating operands and operators).
pub enum InfixElement<'a> {
    Operand(TermId),
    Operator(&'a str),
}

// ── Pratt algorithm ─────────────────────────────────────────────

/// Desugar a flat chain of operands and operators into nested `Term::Fn` calls.
///
/// The `elements` slice alternates: `[operand, op, operand, op, operand, ...]`
/// or `[op, operand, ...]` for prefix-led chains.
///
/// Returns a single `TermId` representing the desugared expression.
pub fn desugar_infix_chain(
    elements: &[InfixElement<'_>],
    terms: &mut SimpleTermStore,
    symbols: &mut SymbolTable,
) -> Result<TermId, String> {
    if elements.is_empty() {
        return Err("empty infix chain".to_string());
    }
    let (result, pos) = desugar(elements, 0, 0, terms, symbols)?;
    if pos < elements.len() {
        return Err(format!("unconsumed elements at position {pos}"));
    }
    Ok(result)
}

/// Span of a synthesized op-node: merge the first and last operand span.
/// For a prefix op the operator token has no TermId, so the start offset
/// drops by the operator's width — accepted trade-off.
fn op_span(terms: &SimpleTermStore, first: TermId, last: TermId) -> Span {
    Span::merge(terms.span(first), terms.span(last))
}

fn desugar(
    elements: &[InfixElement<'_>],
    mut pos: usize,
    min_bp: u8,
    terms: &mut SimpleTermStore,
    symbols: &mut SymbolTable,
) -> Result<(TermId, usize), String> {
    if pos >= elements.len() {
        return Err("unexpected end of infix chain".to_string());
    }

    // nud: prefix operator or operand
    let mut left = match &elements[pos] {
        InfixElement::Operator(op) => {
            let entry = prefix_entry(op)
                .ok_or_else(|| format!("unknown prefix operator: {op}"))?;
            pos += 1;
            let (right, new_pos) = desugar(elements, pos, entry.priority, terms, symbols)?;
            pos = new_pos;
            let functor = symbols.intern(entry.functor);
            let span = op_span(terms, right, right);
            terms.alloc(
                Term::Fn {
                    functor,
                    pos_args: SmallVec::from_elem(right, 1),
                    named_args: SmallVec::new(),
                },
                span,
            )
        }
        InfixElement::Operand(tid) => {
            pos += 1;
            *tid
        }
    };

    // led: infix operators
    while pos < elements.len() {
        let op = match &elements[pos] {
            InfixElement::Operator(op) => *op,
            InfixElement::Operand(_) => break,
        };

        let entry = match infix_entry(op) {
            Some(e) => e,
            None => break, // unknown op — stop parsing, let caller handle
        };

        if entry.priority < min_bp {
            break;
        }

        // None-associative: reject chaining of same-priority operators
        if entry.assoc == Assoc::None && entry.priority == min_bp {
            return Err(format!(
                "non-associative operator `{op}` cannot be chained"
            ));
        }

        pos += 1; // consume operator

        // Check for ternary continuation
        if let Some(cont) = &entry.continuation {
            // Parse middle operand with min_bp=0 (allows anything)
            let (middle, new_pos) = desugar(elements, pos, 0, terms, symbols)?;
            pos = new_pos;

            // Check if continuation token follows
            let is_ternary = matches!(
                elements.get(pos),
                Some(InfixElement::Operator(tok)) if *tok == cont.token
            );

            if is_ternary {
                pos += 1; // consume continuation token
                let (right, new_pos) = desugar(elements, pos, entry.priority, terms, symbols)?;
                pos = new_pos;
                let functor = symbols.intern(cont.functor);
                let span = op_span(terms, left, right);
                left = terms.alloc(
                    Term::Fn {
                        functor,
                        pos_args: SmallVec::from_slice(&[left, middle, right]),
                        named_args: SmallVec::new(),
                    },
                    span,
                );
            } else {
                // No continuation — binary infix
                let functor = symbols.intern(entry.functor);
                let span = op_span(terms, left, middle);
                left = terms.alloc(
                    Term::Fn {
                        functor,
                        pos_args: SmallVec::from_slice(&[left, middle]),
                        named_args: SmallVec::new(),
                    },
                    span,
                );
            }
        } else {
            // Binary infix
            let right_bp = match entry.assoc {
                Assoc::Left => entry.priority + 1,
                Assoc::Right | Assoc::None => entry.priority,
            };
            let (right, new_pos) = desugar(elements, pos, right_bp, terms, symbols)?;
            pos = new_pos;

            let functor = symbols.intern(entry.functor);
            let span = op_span(terms, left, right);
            left = terms.alloc(
                Term::Fn {
                    functor,
                    pos_args: SmallVec::from_slice(&[left, right]),
                    named_args: SmallVec::new(),
                },
                span,
            );
        }
    }

    Ok((left, pos))
}

// ── Tests ───────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn run(ops: &[&str]) -> (SimpleTermStore, SymbolTable, TermId) {
        let mut terms = SimpleTermStore::new();
        let mut symbols = SymbolTable::new();
        let z = Span::default();

        // Build elements: classify by dictionary lookup — if it's a known
        // infix/prefix operator, treat as operator; otherwise as operand.
        let mut elements = Vec::new();
        for s in ops {
            if infix_entry(s).is_some() || prefix_entry(s).is_some() || *s == "@" {
                elements.push(InfixElement::Operator(s));
            } else {
                let sym = symbols.intern(s);
                let tid = terms.alloc(Term::Ident(sym), z);
                elements.push(InfixElement::Operand(tid));
            }
        }

        let result = desugar_infix_chain(&elements, &mut terms, &mut symbols).unwrap();
        (terms, symbols, result)
    }

    fn fmt_term(terms: &SimpleTermStore, symbols: &SymbolTable, tid: TermId) -> String {
        match terms.get(tid) {
            Term::Ident(sym) => symbols.name(*sym).to_string(),
            Term::Fn { functor, pos_args, .. } => {
                let name = symbols.name(*functor);
                let args: Vec<String> = pos_args.iter()
                    .map(|&a| fmt_term(terms, symbols, a))
                    .collect();
                format!("{name}({})", args.join(", "))
            }
            other => format!("{other:?}"),
        }
    }

    #[test]
    fn left_assoc() {
        let (terms, symbols, result) = run(&["a", "+", "b", "+", "c"]);
        assert_eq!(fmt_term(&terms, &symbols, result), "add(add(a, b), c)");
    }

    #[test]
    fn right_assoc() {
        let (terms, symbols, result) = run(&["a", "^", "b", "^", "c"]);
        assert_eq!(fmt_term(&terms, &symbols, result), "pow(a, pow(b, c))");
    }

    #[test]
    fn mixed_precedence() {
        let (terms, symbols, result) = run(&["a", "+", "b", "*", "c"]);
        assert_eq!(fmt_term(&terms, &symbols, result), "add(a, mul(b, c))");
    }

    #[test]
    fn mixed_precedence_reverse() {
        let (terms, symbols, result) = run(&["a", "*", "b", "+", "c"]);
        assert_eq!(fmt_term(&terms, &symbols, result), "add(mul(a, b), c)");
    }

    #[test]
    fn ternary_arrow_effect() {
        let (terms, symbols, result) = run(&["a", "->", "b", "@", "c"]);
        assert_eq!(fmt_term(&terms, &symbols, result), "arrow_effect(a, b, c)");
    }

    #[test]
    fn binary_arrow_fallback() {
        let (terms, symbols, result) = run(&["a", "->", "b"]);
        assert_eq!(fmt_term(&terms, &symbols, result), "arrow(a, b)");
    }

    #[test]
    fn prefix_not() {
        let (terms, symbols, result) = run(&["!", "a"]);
        assert_eq!(fmt_term(&terms, &symbols, result), "not(a)");
    }

    #[test]
    fn prefix_with_infix() {
        let (terms, symbols, result) = run(&["!", "a", "+", "b"]);
        assert_eq!(fmt_term(&terms, &symbols, result), "add(not(a), b)");
    }

    #[test]
    fn word_operators() {
        let (terms, symbols, result) = run(&["a", "or", "b"]);
        assert_eq!(fmt_term(&terms, &symbols, result), "or(a, b)");
    }

    #[test]
    fn new_operators() {
        let (terms, symbols, result) = run(&["a", "|", "b"]);
        assert_eq!(fmt_term(&terms, &symbols, result), "or(a, b)");

        let (terms, symbols, result) = run(&["a", "!=", "b"]);
        assert_eq!(fmt_term(&terms, &symbols, result), "neq(a, b)");

        let (terms, symbols, result) = run(&["a", "/", "b"]);
        assert_eq!(fmt_term(&terms, &symbols, result), "div(a, b)");

        let (terms, symbols, result) = run(&["a", "%", "b"]);
        assert_eq!(fmt_term(&terms, &symbols, result), "mod(a, b)");

        // WI-522 / proposal 049: `<=>` desugars to the `unify` functor (greedy over `<=`).
        let (terms, symbols, result) = run(&["a", "<=>", "b"]);
        assert_eq!(fmt_term(&terms, &symbols, result), "unify(a, b)");
    }

    #[test]
    fn none_assoc_rejects_chaining() {
        let mut terms = SimpleTermStore::new();
        let mut symbols = SymbolTable::new();

        let z = Span::default();
        let a = terms.alloc(Term::Ident(symbols.intern("a")), z);
        let b = terms.alloc(Term::Ident(symbols.intern("b")), z);
        let c = terms.alloc(Term::Ident(symbols.intern("c")), z);
        let elements = vec![
            InfixElement::Operand(a),
            InfixElement::Operator("="),
            InfixElement::Operand(b),
            InfixElement::Operator("="),
            InfixElement::Operand(c),
        ];
        let result = desugar_infix_chain(&elements, &mut terms, &mut symbols);
        assert!(result.is_err(), "chaining none-associative `=` should fail");
        assert!(result.unwrap_err().contains("non-associative"));
    }
}

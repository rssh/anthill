//! Pattern matching against runtime values.
//!
//! Per proposal 026 §Pattern-match uniformity: a constructor pattern
//! matches both `Value::Entity { functor: F, .. }` and `Value::Term(tid)`
//! where `kb.get_term(tid) = Term::Fn { functor: F, .. }`. Consumers don't
//! care which lineage produced the scrutinee.

use smallvec::SmallVec;

use crate::intern::Symbol;
use crate::kb::term::{Literal, Term, TermId};
use crate::kb::typing::list_to_vec;

use super::value::Value;
use super::Interpreter;

pub type Bindings = SmallVec<[(Symbol, Value); 4]>;

/// Try to match `scrutinee` against the pattern term. Returns the bindings
/// produced by the pattern's variables (empty for wildcard / literal).
/// Returns `None` if the pattern doesn't match.
pub fn match_pattern(
    interp: &Interpreter,
    pattern_tid: TermId,
    scrutinee: &Value,
) -> Option<Bindings> {
    let kb = &interp.kb;
    let term = kb.get_term(pattern_tid).clone();

    match &term {
        Term::Fn { functor, named_args, .. } => {
            let f = Some(*functor);
            if f == interp.reflect.var_pattern {
                let sym = var_pattern_name(interp, named_args)?;
                let mut b = SmallVec::new();
                b.push((sym, scrutinee.clone()));
                Some(b)
            } else if f == interp.reflect.wildcard {
                Some(SmallVec::new())
            } else if f == interp.reflect.literal_pattern {
                let value_tid = lookup(named_args, interp.fields.value)?;
                if literal_matches(kb, value_tid, scrutinee) {
                    Some(SmallVec::new())
                } else {
                    None
                }
            } else if f == interp.reflect.constructor_pattern {
                match_constructor_pattern(interp, named_args, scrutinee)
            } else if f == interp.reflect.tuple_pattern {
                match_tuple_pattern(interp, named_args, scrutinee)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Extract the bound-variable `Symbol` from a `var_pattern` term. Used by
/// both the var_pattern arm of [`match_pattern`] and [`Interpreter::reduce_lambda`]
/// (lambdas accept a restricted var_pattern param). Returns `None` when the
/// term isn't a var_pattern or lacks a `name` field.
pub fn extract_var_pattern_sym(interp: &Interpreter, pat_tid: TermId) -> Option<Symbol> {
    let kb = &interp.kb;
    match kb.get_term(pat_tid) {
        Term::Fn { functor, named_args, .. } if Some(*functor) == interp.reflect.var_pattern => {
            var_pattern_name(interp, named_args)
        }
        _ => None,
    }
}

/// Peek at a constructor pattern's `name` field without allocating a full
/// match attempt. Returns `None` if `pat_tid` isn't a constructor pattern.
pub fn constructor_pattern_name(
    interp: &Interpreter,
    pat_tid: TermId,
) -> Option<Symbol> {
    let kb = &interp.kb;
    match kb.get_term(pat_tid) {
        Term::Fn { functor, named_args, .. }
            if Some(*functor) == interp.reflect.constructor_pattern =>
        {
            let name_tid = lookup(named_args, interp.fields.name)?;
            term_as_symbol(kb, name_tid)
        }
        _ => None,
    }
}

// ── internals ───────────────────────────────────────────────────

fn var_pattern_name(
    interp: &Interpreter,
    named_args: &smallvec::SmallVec<[(Symbol, TermId); 2]>,
) -> Option<Symbol> {
    let name_tid = lookup(named_args, interp.fields.name)?;
    term_as_symbol(&interp.kb, name_tid)
}

fn match_constructor_pattern(
    interp: &Interpreter,
    named_args: &smallvec::SmallVec<[(Symbol, TermId); 2]>,
    scrutinee: &Value,
) -> Option<Bindings> {
    let kb = &interp.kb;
    let name_tid = lookup(named_args, interp.fields.name)?;
    let ctor_sym = term_as_symbol(kb, name_tid)?;
    let args_tid = lookup(named_args, interp.fields.args)?;
    let sub_patterns = list_to_vec(kb, args_tid);
    // WI-445: named sub-patterns (`Box(v: some(x))`) ride a `named:
    // List[NamedPattern]` field (absent for the all-positional form).
    let named_subs: Vec<(Symbol, TermId)> = lookup(named_args, interp.fields.named)
        .map(|t| list_to_vec(kb, t))
        .unwrap_or_default()
        .iter()
        .filter_map(|&np| crate::kb::node_occurrence::read_named_pattern_term(kb, np))
        .collect();

    // Pattern-match uniformity: present positional-then-named for both
    // lineage forms so the positional sub-pattern loop is agnostic. The
    // scrutinee's sub-values are in declaration order (positional fields then
    // `sort_named_canonical`-ordered named fields), so a named sub-pattern
    // maps to its field's declaration index.
    // Arity-strict: the total of positional + named sub-patterns must equal
    // the value's field count, with no field covered twice — previously `<`
    // would happily bind the first N of an N+1 value and discard the rest.
    let sub_values = constructor_sub_values(kb, ctor_sym, scrutinee)?;
    let n = sub_values.len();
    if sub_patterns.len() + named_subs.len() != n {
        return None;
    }

    let mut covered = vec![false; n];
    let mut bindings = SmallVec::new();
    // Positional sub-patterns fill the leading field indices.
    for (i, sub_pat) in sub_patterns.iter().enumerate() {
        covered[i] = true;
        let mut sub_b = match_pattern(interp, *sub_pat, &sub_values[i])?;
        bindings.append(&mut sub_b);
    }
    // Named sub-patterns resolve to their field's declaration index. A field
    // the constructor doesn't declare, an out-of-range index, or a double
    // cover is no match (mirrors the arity-strict positional behaviour).
    let field_order = kb.entity_field_names(ctor_sym);
    for (field_sym, sub_pat) in named_subs {
        let idx = field_order.and_then(|order| order.iter().position(|f| *f == field_sym))?;
        if idx >= n || covered[idx] {
            return None;
        }
        covered[idx] = true;
        let mut sub_b = match_pattern(interp, sub_pat, &sub_values[idx])?;
        bindings.append(&mut sub_b);
    }
    Some(bindings)
}

fn match_tuple_pattern(
    interp: &Interpreter,
    named_args: &smallvec::SmallVec<[(Symbol, TermId); 2]>,
    scrutinee: &Value,
) -> Option<Bindings> {
    let kb = &interp.kb;
    let elems_tid = lookup(named_args, interp.fields.elements)?;
    let sub_patterns = list_to_vec(kb, elems_tid);
    let pos = match scrutinee {
        Value::Tuple { pos, .. } => pos,
        _ => return None,
    };
    if pos.len() != sub_patterns.len() { return None; }

    let mut bindings = SmallVec::new();
    for (sub_pat, sub_val) in sub_patterns.iter().zip(pos.iter()) {
        let mut sub_b = match_pattern(interp, *sub_pat, sub_val)?;
        bindings.append(&mut sub_b);
    }
    Some(bindings)
}

/// Extract `(positional ++ named)` sub-values when the scrutinee carries the
/// expected constructor functor. Constructor patterns are positional today,
/// so named entity args are exposed after positionals in declaration order.
fn constructor_sub_values(
    kb: &crate::kb::KnowledgeBase,
    expected: Symbol,
    scrutinee: &Value,
) -> Option<Vec<Value>> {
    match scrutinee {
        Value::Entity { functor, pos, named } => {
            if !functor_matches(kb, expected, *functor) { return None; }
            let mut all: Vec<Value> = pos.to_vec();
            all.extend(named.iter().map(|(_, v)| v.clone()));
            Some(all)
        }
        Value::Term(tid) => match kb.get_term(*tid) {
            Term::Fn { functor, pos_args, named_args } => {
                if !functor_matches(kb, expected, *functor) { return None; }
                let mut all: Vec<Value> = pos_args.iter().map(|t| Value::Term(*t)).collect();
                all.extend(named_args.iter().map(|(_, t)| Value::Term(*t)));
                Some(all)
            }
            // Term::Fn with no args round-trips through the printer as a
            // bare identifier (the printer omits parens for 0-arg shapes),
            // and the parser then loads it back as Term::Ref / Term::Ident.
            // Accept those as a 0-arg constructor so a `case nil()` arm
            // matches both `cons("x", nil)` (after reload) and the
            // original Fn(nil, []) shape.
            Term::Ref(sym) | Term::Ident(sym) => {
                if !functor_matches(kb, expected, *sym) { return None; }
                Some(Vec::new())
            }
            _ => None,
        },
        _ => None,
    }
}

/// Compare a pattern-side constructor functor against a scrutinee functor.
/// Scope-aware loading normally resolves both to the same qualified symbol,
/// so symbol equality is the fast path. The short-name comparison remains as
/// a fallback for values built host-side whose Symbol carries a different
/// qualified path than the pattern's. Shared with the eval-side MatchDispatch
/// pre-filter.
pub(crate) fn functor_matches(
    kb: &crate::kb::KnowledgeBase,
    pattern_sym: Symbol,
    scrutinee_sym: Symbol,
) -> bool {
    if pattern_sym == scrutinee_sym { return true; }
    let pattern_short = kb.resolve_sym(pattern_sym).rsplit('.').next().unwrap_or("");
    let scrut_short = kb.resolve_sym(scrutinee_sym).rsplit('.').next().unwrap_or("");
    !pattern_short.is_empty() && pattern_short == scrut_short
}

fn literal_matches(kb: &crate::kb::KnowledgeBase, lit_tid: TermId, scrutinee: &Value) -> bool {
    match (kb.get_term(lit_tid), scrutinee) {
        (Term::Const(Literal::Int(a)), Value::Int(b)) => *a == *b,
        (Term::Const(Literal::Bool(a)), Value::Bool(b)) => *a == *b,
        (Term::Const(Literal::String(a)), Value::Str(b)) => a == b,
        (Term::Const(Literal::Float(a)), Value::Float(b)) => a.into_inner() == *b,
        _ => false,
    }
}

/// Symbol-keyed named-arg lookup. Cheap because keys are pre-interned in
/// `FieldSymbols`; we never pay the `kb.resolve_sym(*s) == "…"` string
/// compare `kb::typing::get_named_arg` would do.
fn lookup(args: &smallvec::SmallVec<[(Symbol, TermId); 2]>, key: Symbol) -> Option<TermId> {
    args.iter().find(|(s, _)| *s == key).map(|(_, v)| *v)
}

fn term_as_symbol(kb: &crate::kb::KnowledgeBase, tid: TermId) -> Option<Symbol> {
    match kb.get_term(tid) {
        Term::Ref(s) | Term::Ident(s) => Some(*s),
        _ => None,
    }
}

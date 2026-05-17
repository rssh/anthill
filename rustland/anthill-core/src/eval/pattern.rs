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

    // Pattern-match uniformity: present positional-then-named for both
    // lineage forms so the positional sub-pattern loop is agnostic.
    // Arity-strict: a 3-pattern constructor_pattern only matches a
    // 3-positional value — previously `<` would happily bind the first
    // N of an N+1 value and discard the rest.
    let sub_values = constructor_sub_values(kb, ctor_sym, scrutinee)?;
    if sub_values.len() != sub_patterns.len() { return None; }

    let mut bindings = SmallVec::new();
    for (sub_pat, sub_val) in sub_patterns.iter().zip(sub_values.iter()) {
        let mut sub_b = match_pattern(interp, *sub_pat, sub_val)?;
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
            let mut all = pos.clone();
            all.extend(named.iter().map(|(_, v)| v.clone()));
            Some(all)
        }
        Value::Term(tid) => {
            if let Term::Fn { functor, pos_args, named_args } = kb.get_term(*tid) {
                if !functor_matches(kb, expected, *functor) { return None; }
                let mut all: Vec<Value> = pos_args.iter().map(|t| Value::Term(*t)).collect();
                all.extend(named_args.iter().map(|(_, t)| Value::Term(*t)));
                Some(all)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Pattern-side constructor name may be the short symbol (`wis`); the
/// scrutinee carries the loader-registered qualified symbol
/// (`…FileBasedWorkitemStore.wis`). The kb's short→qualified index makes
/// these comparable. Shared with the eval-side MatchDispatch pre-filter.
pub(crate) fn functor_matches(
    kb: &crate::kb::KnowledgeBase,
    pattern_sym: Symbol,
    scrutinee_sym: Symbol,
) -> bool {
    if pattern_sym == scrutinee_sym { return true; }
    if let Some(q) = kb.entity_qualified_for_short(pattern_sym) {
        if q == scrutinee_sym { return true; }
    }
    if let Some(q) = kb.entity_qualified_for_short(scrutinee_sym) {
        if q == pattern_sym { return true; }
    }
    // Fallback: compare by last-dotted-segment short names. Covers
    // patterns whose Symbol came from a nested-sort scope where the
    // short-name redirect was registered for a different qualified
    // resolution than the host-built value carries.
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

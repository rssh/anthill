//! Pattern matching against runtime values.
//!
//! Per proposal 026 §Pattern-match uniformity: a constructor pattern
//! matches both `Value::Entity { functor: F, .. }` and `Value::Term(tid)`
//! where `kb.get_term(tid) = Term::Fn { functor: F, .. }`. Consumers don't
//! care which lineage produced the scrutinee.
//!
//! WI-511: the pattern side reads the [`Pattern`] enum (a `NodeKind::Pattern`
//! occurrence) DIRECTLY — it is never serialized to a reflect `Term::Fn`
//! first — so the matcher is independent of the `Ref(c)` vs `Fn{c}` storage
//! form for nullary constructors (notably `wildcard`). The scrutinee side
//! still bridges `Value::Entity` and `Value::Term` (see `constructor_sub_values`).

use std::rc::Rc;

use smallvec::SmallVec;

use crate::intern::Symbol;
use crate::kb::node_occurrence::{NodeOccurrence, Pattern};
use crate::kb::term::{Literal, Term};

use super::value::Value;
use super::Interpreter;

pub type Bindings = SmallVec<[(Symbol, Value); 4]>;

/// Try to match `scrutinee` against the pattern occurrence. Returns the
/// bindings produced by the pattern's variables (empty for wildcard /
/// literal). Returns `None` if the pattern doesn't match.
pub fn match_pattern(
    interp: &Interpreter,
    pattern: &Rc<NodeOccurrence>,
    scrutinee: &Value,
) -> Option<Bindings> {
    // WI-511: reflection meta-var params (`lambda(param: ?x, …)` built as
    // reflective data) surface as Expr-kind occurrences, not Pattern. They
    // never name a bindable runtime pattern, so they don't match — mirroring
    // the old term path, where an `Expr::Var` serialized to a `Term::Var`
    // that the `Term::Fn` matcher rejected.
    match pattern.as_pattern()? {
        Pattern::Var { name, .. } => {
            let mut b = SmallVec::new();
            b.push((*name, scrutinee.clone()));
            Some(b)
        }
        Pattern::Wildcard => Some(SmallVec::new()),
        Pattern::Literal { value } => {
            if literal_matches(value, scrutinee) {
                Some(SmallVec::new())
            } else {
                None
            }
        }
        Pattern::Constructor { name, pos_args, named_args } => {
            match_constructor_pattern(interp, *name, pos_args, named_args, scrutinee)
        }
        Pattern::Tuple { positional, named } => {
            match_tuple_pattern(interp, positional, named, scrutinee)
        }
    }
}

/// Peek at a constructor pattern's name without a full match attempt. Returns
/// `None` if the occurrence isn't a constructor pattern.
pub fn constructor_pattern_name(pattern: &Rc<NodeOccurrence>) -> Option<Symbol> {
    match pattern.as_pattern()? {
        Pattern::Constructor { name, .. } => Some(*name),
        _ => None,
    }
}

// ── internals ───────────────────────────────────────────────────

fn match_constructor_pattern(
    interp: &Interpreter,
    ctor_sym: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    scrutinee: &Value,
) -> Option<Bindings> {
    let kb = &interp.kb;
    // Pattern-match uniformity: present positional-then-named for both
    // lineage forms so the positional sub-pattern loop is agnostic. The
    // scrutinee's sub-values are in declaration order (positional fields then
    // `canonicalize_record_named_args`-ordered named fields), so a named sub-pattern
    // maps to its field's declaration index.
    // Arity-strict: the total of positional + named sub-patterns must equal
    // the value's field count, with no field covered twice — previously `<`
    // would happily bind the first N of an N+1 value and discard the rest.
    let sub_values = constructor_sub_values(kb, ctor_sym, scrutinee)?;
    let n = sub_values.len();
    if pos_args.len() + named_args.len() != n {
        return None;
    }

    let mut covered = vec![false; n];
    let mut bindings = SmallVec::new();
    // Positional sub-patterns fill the leading field indices.
    for (i, sub_pat) in pos_args.iter().enumerate() {
        covered[i] = true;
        let mut sub_b = match_pattern(interp, sub_pat, &sub_values[i])?;
        bindings.append(&mut sub_b);
    }
    // WI-445: named sub-patterns (`Box(v: some(x))`) resolve to their field's
    // declaration index. A field the constructor doesn't declare, an
    // out-of-range index, or a double cover is no match (mirrors the
    // arity-strict positional behaviour).
    let field_order = kb.entity_field_names(ctor_sym);
    for (field_sym, sub_pat) in named_args {
        let idx = field_order.and_then(|order| order.iter().position(|f| *f == *field_sym))?;
        if idx >= n || covered[idx] {
            return None;
        }
        covered[idx] = true;
        let mut sub_b = match_pattern(interp, sub_pat, &sub_values[idx])?;
        bindings.append(&mut sub_b);
    }
    Some(bindings)
}

/// Match a tuple pattern, binding each binder to the component in the same
/// position — for a positionally-keyed AND a name-keyed tuple alike.
///
/// Reading only `Value::Tuple.pos` (as this did) meant a NAME-keyed tuple showed
/// up as zero components, so a destructuring binder never matched one:
/// `lambda (acc, x) -> …` applied to `(acc: 3, x: 10)` failed the arity test and
/// raised, while the same lambda over the positional `(3, 10)` bound fine and an
/// operation taking one `(acc: Int64, x: Int64)` parameter worked too. Only the
/// destructuring-lambda-over-named-tuple corner was broken.
///
/// Binding by POSITION rather than by matching binder names to labels is forced:
/// a tuple pattern has no way to spell a label (the grammar's tuple-pattern
/// element is a pattern or a WI-517 `name: Type` TYPED BINDER, never a
/// `named_pattern_field` — that production is constructor-only), so a binder
/// name is a fresh binder, not a selector. By-name would break `lambda (a, b)`
/// over `(acc: …, x: …)` outright. It also agrees with the typer, which aligns
/// an arrow's parameter list positionally (WI-775 `TupleAlign::ParamList`).
///
/// ## Why `pos ++ named` is source order
///
/// A tuple's components are split across `pos` and `named` by `classify_ctor_arg`
/// (eval/eval.rs), which unwraps the parser's synthetic `_N` labels for positional
/// syntax back into `pos`. WI-786 made that unwrap exact — the label must be the
/// synthetic name for its own source index, and nothing may already have gone to
/// `named` — so `pos` is always a source-order PREFIX and `named` the remainder in
/// order. Concatenating them therefore reproduces the components as written.
///
/// That invariant is load-bearing here, and it is young: before WI-786 the unwrap
/// was a bare `_`-prefix test, which also caught user labels like `_b` and
/// silently scrambled the order — `lambda (p, q) -> p - q` over `(a: 3, _b: 10)`
/// yielded 7 instead of -7, and an operation declared `-> Int64` returned a
/// `String`. If that unwrap is ever widened again, this walk is what breaks.
fn match_tuple_pattern(
    interp: &Interpreter,
    positional: &[Rc<NodeOccurrence>],
    named: &[(Symbol, Rc<NodeOccurrence>)],
    scrutinee: &Value,
) -> Option<Bindings> {
    let (val_pos, val_named) = match scrutinee {
        Value::Tuple { pos, named } => (pos, named),
        _ => return None,
    };
    // Nothing mints a labelled tuple sub-pattern: the grammar has no production
    // for one, the parser emits `pattern_tuple` with positional elements only,
    // and the sole `Pattern::Tuple` producer hardcodes `named: Vec::new()`.
    // Refuse rather than carry untestable code for a shape that cannot occur —
    // and note a future label rule would have to agree with `field_access`'
    // short-name lookup (eval/builtins.rs), not raw symbol identity.
    debug_assert!(named.is_empty(), "no producer mints a labelled tuple sub-pattern");
    if !named.is_empty() {
        return None;
    }
    if positional.len() != val_pos.len() + val_named.len() {
        return None;
    }
    // Source order, per the invariant above. Same idiom the Tuple/Entity walk in
    // eval/effects.rs uses, and allocation-free as the old `pos`-only zip was.
    let components = val_pos.iter().chain(val_named.iter().map(|(_, v)| v));

    let mut bindings = SmallVec::new();
    for (sub_pat, sub_val) in positional.iter().zip(components) {
        let mut sub_b = match_pattern(interp, sub_pat, sub_val)?;
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
        Value::Entity { functor, pos, named, .. } => {
            if !functor_matches(kb, expected, *functor) { return None; }
            let mut all: Vec<Value> = pos.to_vec();
            all.extend(named.iter().map(|(_, v)| v.clone()));
            Some(all)
        }
        Value::Term { id: tid, .. } => match kb.get_term(*tid) {
            Term::Fn { functor, pos_args, named_args } => {
                if !functor_matches(kb, expected, *functor) { return None; }
                let mut all: Vec<Value> = pos_args.iter().map(|t| Value::term(*t)).collect();
                all.extend(named_args.iter().map(|(_, t)| Value::term(*t)));
                Some(all)
            }
            // A 0-arg constructor stored as `Term::Ref` (WI-436/WI-511: the
            // canonical nullary-constructor form) or reloaded as
            // `Term::Ref`/`Term::Ident` (the printer renders a 0-arg shape as a
            // bare identifier). Accept those so a `case nil()` arm matches both
            // `cons("x", nil)` and the bare `nil`.
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

fn literal_matches(lit: &Literal, scrutinee: &Value) -> bool {
    match (lit, scrutinee) {
        (Literal::Int(a), Value::Int(b)) => *a == *b,
        (Literal::Bool(a), Value::Bool(b)) => *a == *b,
        (Literal::String(a), Value::Str(b)) => a == b,
        (Literal::Float(a), Value::Float(b)) => a.into_inner() == *b,
        _ => false,
    }
}

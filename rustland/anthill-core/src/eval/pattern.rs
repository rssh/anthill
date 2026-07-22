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

use super::value::{TupleComponents, Value};
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
        Pattern::Tuple { positional, labels } => {
            match_tuple_pattern(interp, positional, labels, scrutinee)
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

/// Match a tuple pattern, binding each binder to the component the typer
/// assigned it: BY LABEL when the typer resolved one (WI-803), else by position.
///
/// ## The by-label arm
///
/// `labels[i]` is the component name binder `i` selects, resolved by the typer
/// from the pattern's expected named-tuple type — never from what the binder is
/// called. A binder name remains a fresh binder, so `lambda (p, q)` over an
/// `(a: …, b: …)` slot still binds `p` and `q`; what the labels add is WHICH
/// component each one receives.
///
/// This is what makes `TupleAlign::DATA` safe to be fully name-keyed. Reading by
/// slot, a permuted value handed binder `i` the value's `i`-th component while the
/// typer had typed it from the DECLARED `i`-th field, so an operation declared
/// `-> Int64` returned a `String` on a clean load (WI-788). Fetching `labels[i]`
/// by name hands back the component the typer typed it from, whatever slot it
/// sits in.
///
/// It also drops the COUNT test, and must: width subtyping lets an
/// `(a: A, b: B, c: C)` value reach a binder list typed `(a: A, b: B)`, and a
/// by-label fetch does not care how many components it did not ask for. The count
/// test survives on the positional path, where it is still the only arity guard
/// (`arity_mismatch_still_refuses_to_match`).
///
/// A label with no matching component is NO MATCH, which raises through
/// `raise_match_failed` — loud, not a skipped binder.
///
/// ## The positional arm
///
/// Reached on ANY of three conditions, and the second is the one most executions
/// take. The `by_label` gate below spells all three:
///
///  * the typer resolved no labels (an unannotated `let`, a reflectively-built
///    pattern, a rule-body occurrence), so there is no DECLARED order for the
///    value's own order to disagree with;
///  * the VALUE is a positional carrier with no names to match the labels
///    against. Here the labels are real and so is the declared order — what is
///    missing is the value's half of the correspondence. This is the shape a
///    SPREAD call arrives in (`f(3, 10)` gathers to `Tuple { pos, named: [] }`),
///    which covers `foldLeft` and every other two-binder callback. See
///    [`TupleComponents::is_name_keyed`] on why reading it by slot is exact
///    rather than a degradation; or
///  * the LABELS are the synthetic `_1.._n` convention, i.e. the expected type is
///    a POSITIONAL tuple, where `_i` means slot `i` and a by-label read adds
///    nothing — see [`TupleComponents::labels_are_positional`], which also
///    explains why it does not merely add nothing but actively FAILS when the
///    value is name-keyed.
///
/// In each case the components are read in source order, which is then the only
/// available reading and the correct one. Below on why it cannot be by-name.
///
/// Reading only `Value::Tuple.pos` (as this did) meant a NAME-keyed tuple showed
/// up as zero components, so a destructuring binder never matched one:
/// `lambda (acc, x) -> …` applied to `(acc: 3, x: 10)` failed the arity test and
/// raised, while the same lambda over the positional `(3, 10)` bound fine and an
/// operation taking one `(acc: Int64, x: Int64)` parameter worked too. Only the
/// destructuring-lambda-over-named-tuple corner was broken.
///
/// Deriving the label from the BINDER NAME is what is forced out, on both arms: a
/// tuple pattern has no way to spell a label (the grammar's tuple-pattern element
/// is a pattern or a WI-517 `name: Type` TYPED BINDER, never a
/// `named_pattern_field` — that production is constructor-only), so a binder name
/// is a fresh binder, not a selector, and matching binder names against labels
/// would break `lambda (a, b)` over `(acc: …, x: …)` outright. WI-803 changes
/// where the label comes FROM (the expected type), not that one is written.
///
/// The components come from [`Value::tuple_components`], which owns the
/// `pos ++ named` = source-order invariant and explains why (WI-787). That
/// invariant is load-bearing for the POSITIONAL arm and it is young: before WI-786 the
/// `classify_ctor_arg` unwrap was a bare `_`-prefix test, which also caught user
/// labels like `_b` and silently scrambled the order — `lambda (p, q) -> p - q`
/// over `(a: 3, _b: 10)` yielded 7 instead of -7, and an operation declared
/// `-> Int64` returned a `String`. If that unwrap is ever widened again, this
/// walk is what breaks.
fn match_tuple_pattern(
    interp: &Interpreter,
    positional: &[Rc<NodeOccurrence>],
    labels: &[Symbol],
    scrutinee: &Value,
) -> Option<Bindings> {
    let components = scrutinee.tuple_components()?;
    let mut bindings = SmallVec::new();

    // The by-label arm needs the correspondence to be REAL on all three counts:
    // labels from the typer, names on the value to match them against, and labels
    // that actually name something a slot does not.
    //
    //  * a POSITIONAL carrier has no names — see `TupleComponents::is_name_keyed`
    //    on why reading it by slot is exact rather than a degradation, and why a
    //    spread call (`f(3, 10)`) arrives this way even at a fully named type;
    //  * SYNTHETIC `_1.._n` labels say "positional tuple", where `_i` MEANS slot
    //    `i` — see `TupleComponents::labels_are_positional`. Routing those through
    //    the by-label arm does not just waste a lookup, it FAILS on a name-keyed
    //    value (no component is called `_1`, and the `_N` fallback indexes an empty
    //    `pos`), which is reachable via an all-named relation row.
    let by_label = !labels.is_empty()
        && components.is_name_keyed()
        && !TupleComponents::labels_are_positional(interp.kb(), labels);
    if !by_label {
        // Source order, per the invariant above — read through the owning accessor
        // (WI-787), not off either half.
        if positional.len() != components.len() {
            return None;
        }
        for (sub_pat, sub_val) in positional.iter().zip(components.iter()) {
            let mut sub_b = match_pattern(interp, sub_pat, sub_val)?;
            bindings.append(&mut sub_b);
        }
        return Some(bindings);
    }

    // WI-803: one label per binder, or none at all — `bind_and_label_pattern`
    // only records the list when it has a component for every binder. A SHORTER
    // list would zip-truncate and leave the trailing binders silently unbound,
    // which is a match reported as succeeding on binders that were never given a
    // value.
    debug_assert_eq!(
        labels.len(),
        positional.len(),
        "WI-803: a labelled tuple pattern carries one label per binder",
    );
    if labels.len() != positional.len() {
        return None;
    }
    // WI-803: which components have been claimed, so two binders cannot be served
    // the SAME one. `match_constructor_pattern` above has kept this invariant since
    // WI-445 (its `covered` vec); the by-label tuple arm needs it for the same
    // reason and did not have it at first.
    //
    // Two labels collide either by being EQUAL — a tuple type carrying a repeated
    // component name — or by being distinct QUALIFIED names sharing a last segment,
    // since the lookup compares short names. Either way the second binder would be
    // handed a component the typer typed the FIRST from, while the component it was
    // actually typed from goes unread: a wrong-TYPED value on a clean load, which is
    // the whole WI-788 family. Refusing is loud (the caller raises
    // `Error[MatchFailed]`) and costs nothing on well-formed types, whose component
    // names are distinct.
    //
    // WI-805 closed the EQUAL mode at every producer that keys a tuple on labels the
    // author wrote: the literal and the tuple type, refused at parse
    // (`check_label_unique`, parse/convert.rs), and a `...rest: R` capture's
    // leftover named arguments, refused in `normalize_variadic_capture`
    // (kb/typing.rs). The capture is the one that mattered HERE — until WI-805 it was
    // this guard's only end-to-end witness in the corpus, and it was live:
    // `let (p, q) = cap(1, a: 2, a: 3)` loaded clean and raised `MatchFailed` from the
    // `covered` check below.
    //
    // So this now has NO live driver, and is kept deliberately rather than by
    // oversight. The QUALIFIED mode is untouched by any of those guards: they compare
    // labels as WRITTEN, while this compares SHORT names of symbols that may arrive
    // qualified off a TYPE's field list, so two distinct qualified labels sharing a
    // last segment still collide here and nowhere else. Pinned at the reader in
    // `eval::value::tests::wi803_by_label_reader`; the end-to-end history is recorded
    // in `wi805_duplicate_tuple_label_test` beside the capture guard that closed it.
    let mut covered: SmallVec<[usize; 8]> = SmallVec::new();
    for (sub_pat, label) in positional.iter().zip(labels.iter()) {
        // Resolved through the ONE by-name tuple reader, shared with
        // `field_access` — see `TupleComponents::by_label_index` on why the two must
        // not each carry their own rule, and why this resolves an INDEX. A component
        // the value does not have is NO MATCH; it is not a binder quietly skipped.
        let idx = components.by_label_index(interp.kb(), interp.kb().resolve_sym(*label))?;
        if covered.contains(&idx) {
            return None;
        }
        covered.push(idx);
        let sub_val = components.component_at(idx)?;
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

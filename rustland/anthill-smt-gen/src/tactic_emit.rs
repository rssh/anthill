//! Serialise a tactic into the body of a Z3 `(check-sat-using ...)` form.
//!
//! Trivial-default elision (`smt` with only preamble-routed params):
//! return `None` so the renderer emits the canonical `(check-sat)`
//! instead. Without this, every legacy `by z3(logic: "LRA")` proof
//! would change its emitted bytes and miss the cache.

use anthill_core::intern::{Symbol, SymbolTable};
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::parse::ir::{Tactic, TacticArg, TacticArgValue};

/// Produce a Z3 tactic expression. Returns `None` for the trivial
/// `smt` (no params) case — caller should emit `(check-sat)`.
///
/// `symbols` is the parse-side symbol table that owns the `Symbol`s
/// inside the `Tactic` IR. Callers that walk a stored Tactic alongside
/// its origin `ParsedFile` already have it.
pub fn emit_tactic_expr(symbols: &SymbolTable, tactic: &Tactic) -> Option<String> {
    match tactic {
        Tactic::Bare(sym) => {
            let name = symbols.name(*sym);
            if is_default_smt(symbols, name, &[]) { None } else { Some(name.to_string()) }
        }
        Tactic::App(sym, args) => {
            let name = symbols.name(*sym);
            if is_default_smt(symbols, name, args) { return None; }
            Some(emit_app(symbols, name, args))
        }
        Tactic::Raw(s) => Some(s.clone()),
        Tactic::Mapping(_) => {
            // Mapping isn't a Z3 tactic — it's emitted as
            // (define-fun ...) preamble, not in the tactic position.
            // Return None; the preamble emitter handles it.
            None
        }
    }
}

fn is_default_smt(symbols: &SymbolTable, name: &str, args: &[TacticArg]) -> bool {
    if name != "smt" { return false; }
    // `logic` / `timeout` flow through preamble (set-logic / set-option).
    // Only args in that "preamble" set are considered no-ops at the
    // tactic-expression level. Any other arg (e.g. random_seed,
    // model.compact) requires a `using-params` wrapper, so we don't
    // elide.
    args.iter().all(|a| match a.name {
        Some(sym) => matches!(symbols.name(sym), "logic" | "timeout"),
        None => false,
    })
}

fn emit_app(symbols: &SymbolTable, name: &str, args: &[TacticArg]) -> String {
    match name {
        // Combinators map directly to Z3's S-expression form.
        "then" => emit_combinator(symbols, "then", args),
        "or_else" => emit_combinator(symbols, "or-else", args),
        "par" => emit_combinator(symbols, "par-or", args),
        "repeat" => emit_repeat(symbols, args),
        "smt" => emit_using_params(symbols, "smt", args),
        // Pass-through Z3-native tactics: simplify, qe,
        // propagate-values, ctx-simplify, ... — anything we don't
        // know about gets the same `(using-params <name> ...)`
        // treatment when there are args, or just the bare name.
        _ => emit_using_params(symbols, name, args),
    }
}

fn emit_combinator(symbols: &SymbolTable, kw: &str, args: &[TacticArg]) -> String {
    let mut out = String::from("(");
    out.push_str(kw);
    for a in args {
        if let TacticArgValue::Tactic(t) = &a.value {
            out.push(' ');
            out.push_str(&emit_tactic_force(symbols, t));
        }
    }
    out.push(')');
    out
}

fn emit_tactic_force(symbols: &SymbolTable, tactic: &Tactic) -> String {
    match tactic {
        Tactic::Bare(sym) => symbols.name(*sym).to_string(),
        Tactic::App(sym, args) => {
            let name = symbols.name(*sym);
            emit_app(symbols, name, args)
        }
        Tactic::Raw(s) => s.clone(),
        Tactic::Mapping(_) => "smt".to_string(),
    }
}

fn emit_repeat(symbols: &SymbolTable, args: &[TacticArg]) -> String {
    // `repeat(t, times: N)` → `(repeat <t> <N>)`. Z3's actual surface
    // is `(repeat <t>)` with default count or `(repeat <t> :max <N>)`
    // depending on version; we use the (parameterised) form via
    // `using-params` when N is supplied, else `(repeat <t>)`.
    let mut tactic_arg: Option<&Tactic> = None;
    let mut times: Option<i64> = None;
    for a in args {
        match (a.name.as_ref().map(|s| symbols.name(*s)), &a.value) {
            (Some("times"), TacticArgValue::Int(n)) => times = Some(*n),
            (None, TacticArgValue::Tactic(t)) => tactic_arg = Some(t.as_ref()),
            _ => {}
        }
    }
    let inner = tactic_arg
        .map(|t| emit_tactic_force(symbols, t))
        .unwrap_or_else(|| "smt".to_string());
    match times {
        Some(n) => format!("(repeat {inner} {n})"),
        None => format!("(repeat {inner})"),
    }
}

fn emit_using_params(symbols: &SymbolTable, name: &str, args: &[TacticArg]) -> String {
    // Filter to the args that are actually Z3 `:param value` pairs —
    // i.e. named args with primitive values. Tactic-typed named args
    // and positional args are skipped (they belong to anthill-layer
    // meta-tactics like `induction`/`ranking`, handled elsewhere).
    let kv: Vec<(String, String)> = args.iter().filter_map(|a| {
        let key = symbols.name(a.name.as_ref().copied()?);
        let val = match &a.value {
            TacticArgValue::String(s) => format!("\"{s}\""),
            TacticArgValue::Int(n) => n.to_string(),
            TacticArgValue::Bool(b) => b.to_string(),
            _ => return None,
        };
        // Skip params that flow through preamble (logic, timeout) —
        // they're set via (set-logic ...) / (set-option ...) higher up.
        if matches!(key, "logic" | "timeout") { return None; }
        Some((key.to_string(), val))
    }).collect();

    if kv.is_empty() {
        name.to_string()
    } else {
        let mut out = format!("(using-params {name}");
        for (k, v) in kv {
            out.push_str(&format!(" :{k} {v}"));
        }
        out.push(')');
        out
    }
}

// ── Runtime-term walker (CLI dispatch path) ─────────────────────
//
// The CLI reads strategy args from `ProofRecord` facts in the loaded
// KB rather than the parse-side IR. This walker mirrors
// `emit_tactic_expr` but reads `Term::Fn` directly.

/// Walk a runtime KB term as a tactic expression at the top level.
/// Returns `None` for the trivial-default `smt(logic: ...)` case
/// (caller emits `(check-sat)` instead).
pub fn emit_tactic_from_term(kb: &KnowledgeBase, term: TermId) -> Option<String> {
    let (name, arg_pairs) = match kb.get_term(term) {
        Term::Ident(sym) | Term::Ref(sym) => {
            (short_name(kb.qualified_name_of(*sym)), Vec::new())
        }
        Term::Fn { functor, pos_args, named_args } => {
            let fn_name = short_name(kb.qualified_name_of(*functor));
            let arg_pairs = collect_arg_pairs(pos_args, named_args);
            (fn_name, arg_pairs)
        }
        _ => return None,
    };
    if is_default_smt_term(kb, name, &arg_pairs) { return None; }
    Some(emit_term_inner(kb, name, &arg_pairs))
}

/// Always-emit form (no elision) — used recursively for combinator
/// children where `smt` must be preserved verbatim.
fn emit_term_force(kb: &KnowledgeBase, term: TermId) -> String {
    match kb.get_term(term) {
        Term::Ident(sym) | Term::Ref(sym) => {
            short_name(kb.qualified_name_of(*sym)).to_string()
        }
        Term::Fn { functor, pos_args, named_args } => {
            let fn_name = short_name(kb.qualified_name_of(*functor));
            let arg_pairs = collect_arg_pairs(pos_args, named_args);
            emit_term_inner(kb, fn_name, &arg_pairs)
        }
        _ => "smt".to_string(),
    }
}

fn collect_arg_pairs(
    pos_args: &smallvec::SmallVec<[TermId; 4]>,
    named_args: &smallvec::SmallVec<[(Symbol, TermId); 2]>,
) -> Vec<(Option<Symbol>, TermId)> {
    let mut v = Vec::with_capacity(pos_args.len() + named_args.len());
    for &p in pos_args.iter() { v.push((None, p)); }
    for &(name_sym, val) in named_args.iter() {
        v.push((Some(name_sym), val));
    }
    v
}

fn emit_term_inner(
    kb: &KnowledgeBase,
    name: &str,
    arg_pairs: &[(Option<Symbol>, TermId)],
) -> String {
    if name == "raw" {
        if let Some((_, first)) = arg_pairs.first() {
            if let Term::Const(Literal::String(s)) = kb.get_term(*first) {
                return s.clone();
            }
        }
        return "smt".to_string();
    }
    if arg_pairs.is_empty() {
        return name.to_string();
    }
    emit_app_term(kb, name, arg_pairs)
}

fn is_default_smt_term(
    kb: &KnowledgeBase,
    name: &str,
    arg_pairs: &[(Option<Symbol>, TermId)],
) -> bool {
    if name != "smt" { return false; }
    arg_pairs.iter().all(|(name_opt, _)| match name_opt {
        Some(sym) => matches!(
            short_name(kb.qualified_name_of(*sym)),
            "logic" | "timeout"
        ),
        None => false,
    })
}

fn short_name(qn: &str) -> &str {
    qn.rsplit('.').next().unwrap_or(qn)
}

fn emit_app_term(
    kb: &KnowledgeBase,
    name: &str,
    arg_pairs: &[(Option<Symbol>, TermId)],
) -> String {
    match name {
        "then" => emit_combinator_term(kb, "then", arg_pairs),
        "or_else" => emit_combinator_term(kb, "or-else", arg_pairs),
        "par" => emit_combinator_term(kb, "par-or", arg_pairs),
        "repeat" => emit_repeat_term(kb, arg_pairs),
        _ => emit_using_params_term(kb, name, arg_pairs),
    }
}

fn emit_combinator_term(
    kb: &KnowledgeBase,
    kw: &str,
    arg_pairs: &[(Option<Symbol>, TermId)],
) -> String {
    let mut out = String::from("(");
    out.push_str(kw);
    for (_, t) in arg_pairs {
        out.push(' ');
        out.push_str(&emit_term_force(kb, *t));
    }
    out.push(')');
    out
}

fn emit_repeat_term(
    kb: &KnowledgeBase,
    arg_pairs: &[(Option<Symbol>, TermId)],
) -> String {
    let mut tactic_term: Option<TermId> = None;
    let mut times: Option<i64> = None;
    for (name_opt, t) in arg_pairs {
        let key = name_opt.map(|s| short_name(kb.qualified_name_of(s)));
        match (key, kb.get_term(*t)) {
            (Some("times"), Term::Const(Literal::Int(n))) => times = Some(*n),
            (None, _) => tactic_term = Some(*t),
            _ => {}
        }
    }
    let inner = tactic_term
        .map(|t| emit_term_force(kb, t))
        .unwrap_or_else(|| "smt".to_string());
    match times {
        Some(n) => format!("(repeat {inner} {n})"),
        None => format!("(repeat {inner})"),
    }
}

fn emit_using_params_term(
    kb: &KnowledgeBase,
    name: &str,
    arg_pairs: &[(Option<Symbol>, TermId)],
) -> String {
    let kv: Vec<(&str, String)> = arg_pairs.iter().filter_map(|(name_opt, t)| {
        let key = short_name(kb.qualified_name_of((*name_opt)?));
        if matches!(key, "logic" | "timeout") { return None; }
        let val = match kb.get_term(*t) {
            Term::Const(Literal::String(s)) => format!("\"{s}\""),
            Term::Const(Literal::Int(n)) => n.to_string(),
            Term::Const(Literal::Bool(b)) => b.to_string(),
            _ => return None,
        };
        Some((key, val))
    }).collect();

    if kv.is_empty() {
        name.to_string()
    } else {
        let mut out = format!("(using-params {name}");
        for (k, v) in kv {
            out.push_str(&format!(" :{k} {v}"));
        }
        out.push(')');
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use anthill_core::intern::SymbolTable;
    use anthill_core::parse::ir::{Tactic, TacticArg, TacticArgValue};

    fn syms() -> SymbolTable { SymbolTable::new() }

    fn smt_logic_lra(s: &mut SymbolTable) -> Tactic {
        Tactic::App(s.intern("smt"), vec![TacticArg {
            name: Some(s.intern("logic")),
            value: TacticArgValue::String("LRA".into()),
        }])
    }

    #[test]
    fn default_smt_elides_to_none() {
        let mut s = syms();
        let t = smt_logic_lra(&mut s);
        assert_eq!(emit_tactic_expr(&s, &t), None,
            "smt with only logic/timeout params is the default — \
             caller emits (check-sat)");
    }

    #[test]
    fn bare_simplify_emits_name() {
        let mut s = syms();
        let t = Tactic::Bare(s.intern("simplify"));
        assert_eq!(emit_tactic_expr(&s, &t), Some("simplify".into()));
    }

    #[test]
    fn raw_passes_through_verbatim() {
        let s = syms();
        let t = Tactic::Raw("(then simplify smt)".into());
        assert_eq!(emit_tactic_expr(&s, &t), Some("(then simplify smt)".into()));
    }

    #[test]
    fn then_combinator_serialises_as_sexp() {
        let mut s = syms();
        let then_sym = s.intern("then");
        let simp = s.intern("simplify");
        let smt = s.intern("smt");
        let t = Tactic::App(then_sym, vec![
            TacticArg { name: None, value: TacticArgValue::Tactic(Box::new(Tactic::Bare(simp))) },
            TacticArg { name: None, value: TacticArgValue::Tactic(Box::new(Tactic::Bare(smt))) },
        ]);
        assert_eq!(emit_tactic_expr(&s, &t), Some("(then simplify smt)".into()));
    }

    #[test]
    fn or_else_combinator_uses_dashed_keyword() {
        let mut s = syms();
        let or_else = s.intern("or_else");
        let smt = s.intern("smt");
        let qe = s.intern("qe");
        let t = Tactic::App(or_else, vec![
            TacticArg { name: None, value: TacticArgValue::Tactic(Box::new(Tactic::Bare(smt))) },
            TacticArg { name: None, value: TacticArgValue::Tactic(Box::new(Tactic::Bare(qe))) },
        ]);
        assert_eq!(emit_tactic_expr(&s, &t), Some("(or-else smt qe)".into()));
    }

    #[test]
    fn par_combinator_uses_par_or() {
        let mut s = syms();
        let par = s.intern("par");
        let smt = s.intern("smt");
        let qe = s.intern("qe");
        let t = Tactic::App(par, vec![
            TacticArg { name: None, value: TacticArgValue::Tactic(Box::new(Tactic::Bare(smt))) },
            TacticArg { name: None, value: TacticArgValue::Tactic(Box::new(Tactic::Bare(qe))) },
        ]);
        assert_eq!(emit_tactic_expr(&s, &t), Some("(par-or smt qe)".into()));
    }

    #[test]
    fn repeat_with_explicit_times() {
        let mut s = syms();
        let rep = s.intern("repeat");
        let simp = s.intern("simplify");
        let times = s.intern("times");
        let t = Tactic::App(rep, vec![
            TacticArg { name: None, value: TacticArgValue::Tactic(Box::new(Tactic::Bare(simp))) },
            TacticArg { name: Some(times), value: TacticArgValue::Int(5) },
        ]);
        assert_eq!(emit_tactic_expr(&s, &t), Some("(repeat simplify 5)".into()));
    }

    #[test]
    fn pass_through_with_random_seed() {
        let mut s = syms();
        let smt = s.intern("smt");
        let seed = s.intern("random_seed");
        let t = Tactic::App(smt, vec![TacticArg {
            name: Some(seed),
            value: TacticArgValue::Int(42),
        }]);
        assert_eq!(emit_tactic_expr(&s, &t),
            Some("(using-params smt :random_seed 42)".into()));
    }

    #[test]
    fn nested_combinators() {
        let mut s = syms();
        let then_s = s.intern("then");
        let or_else_s = s.intern("or_else");
        let smt = s.intern("smt");
        let qe = s.intern("qe");
        let simp = s.intern("simplify");
        let inner = Tactic::App(or_else_s, vec![
            TacticArg { name: None, value: TacticArgValue::Tactic(Box::new(Tactic::Bare(smt))) },
            TacticArg { name: None, value: TacticArgValue::Tactic(Box::new(Tactic::Bare(qe))) },
        ]);
        let outer = Tactic::App(then_s, vec![
            TacticArg { name: None, value: TacticArgValue::Tactic(Box::new(Tactic::Bare(simp))) },
            TacticArg { name: None, value: TacticArgValue::Tactic(Box::new(inner)) },
        ]);
        assert_eq!(emit_tactic_expr(&s, &outer),
            Some("(then simplify (or-else smt qe))".into()));
    }
}

//! The shape of a call: an occurrence's nominal head, a call's functor and arguments, and its
//! arguments in parameter order.

use super::*;

/// The nominal head symbol of an occurrence in spec-instance / reference position
/// (`Eq[T]` → `Eq`, `Ref(Eq)` → `Eq`).
pub(super) fn occ_head_symbol(occ: &NodeOccurrence) -> Option<Symbol> {
    let expr = occ.as_expr()?;
    match expr {
        Expr::Ref(s) | Expr::Ident(s) => Some(*s),
        _ => expr_call_parts(expr).map(|(f, _, _)| f),
    }
}

/// WI-20260923-32XFQ — a functor-bearing expression as `(functor, positional, named)`: an
/// `Apply`, or a `Constructor` / `Instantiation`, the two forms a head takes when it was
/// MATERIALIZED from a term rather than lowered from source (`forall_impl` names no
/// operation; a spec-op head can come back a `Constructor`). The occurrence analogue of
/// `Term::Fn`, which carries all three the same way; `None` for every other form.
///
/// The one reading of those three shapes, which ten sites spelled as a two-arm `match`.
/// Only the DESTRUCTURE is shared: the walks around it keep their own order — two stack
/// walkers in `elaborate.rs` push in SOURCE order and the rest do not, and moving them to
/// one walker would reorder the diagnostics they emit.
#[allow(clippy::type_complexity)]
pub(super) fn expr_call_parts(
    expr: &Expr,
) -> Option<(
    Symbol,
    &[Rc<NodeOccurrence>],
    &[(Symbol, Rc<NodeOccurrence>)],
)> {
    match expr {
        Expr::Apply {
            functor,
            pos_args,
            named_args,
            ..
        } => Some((*functor, pos_args, named_args)),
        Expr::Constructor {
            name,
            pos_args,
            named_args,
            ..
        }
        | Expr::Instantiation {
            name,
            pos_args,
            named_args,
        } => Some((*name, pos_args, named_args)),
        _ => None,
    }
}

/// Reorder a rule-body call's arguments into the operation's declared parameter
/// order, so the resolver reads them at the same indices `simp_guard_holds_core`
/// consults. `None` if the call does not fill the parameter list ([`bound_args`]: a
/// partial call, or a labelled one with a positional argument left over — not a usable
/// witness).
///
/// Which argument a parameter takes is [`bound_arg`]'s answer, the one every reader of a
/// call's arguments by parameter gives: a positional argument ranks among the parameters
/// the labels left open, so in `isLess(?b, x: ?a)` over `(x, y)` it is `?a` that is `x`.
/// Paired by index — `x := ?b`, then nothing for `y` — that call aligned to nothing, and
/// was given no condition where its positional twin `isLess(?a, ?b)` is given one. A goal
/// written at arity + 1 with no label keeps its result column out of the answer: it is
/// bound to no parameter.
pub(super) fn align_call_args_to_params(
    kb: &KnowledgeBase,
    params: &[(Symbol, Value)],
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
) -> Option<Vec<Rc<NodeOccurrence>>> {
    Some(
        bound_args(kb, params, pos_args.len(), named_args)?
            .into_iter()
            .map(|arg| Rc::clone(arg.of(pos_args, named_args)))
            .collect(),
    )
}

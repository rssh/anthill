//! Typing pass — type-check expressions following typing_pass_spec.anthill.
//!
//! Rust implementation of TypingEnv, TypeResult, TypeError, and type_check.
//! Types carry logical variables and unify; a type rides as a `TermId` or as a `Value`
//! carrier (`Value::Node` for arrows and other binders) — see the representation note in
//! the top-level CLAUDE.md. Effects are tracked as a list of effect values alongside the
//! value type.
//!
//! LAYOUT. The typer is one module split across files for navigation, NOT encapsulation:
//! every child starts with `use super::*;` and is glob-imported back here, so the files
//! share one namespace and a `pub(super)` item is visible to the whole typer. There is no
//! encapsulation seam to cut along — WI-20260830-009H2 measured the call graph (one
//! community holds 903 of its 1001 free functions). Where things live:
//!
//!  * Diagnostics — `error` (`TypeError`), `display` (type rendering).
//!  * State — `env` (`TypingEnv`, `FlowEnv`, `Env`), `gamma` (proving from Γ),
//!    `result` (`TypeResult`), `type_ctor` (type-level constructors, relation schemas).
//!  * The expression walker — `expr` (entry points, work ops), `visit` / `build` (the two
//!    halves of the iterative typer), `forms`, `apply` (`check_apply_iter`), `arg_hints`,
//!    `args`, `constructor`, `callable`, `relation`, `eta`, `dot_rule`, `pattern`,
//!    `projection`.
//!  * Dispatch and dictionaries — `call_class`, `dispatch`, `slots`, `dict`,
//!    `dep_projection`, `bridge`, `requires`.
//!  * Instance synthesis and provisions — `synth`, `candidates`, `provides_index`,
//!    `provision`, `carrier`, `coherence`.
//!  * Type relations — `unify`, `subtype`, `effects`, `tuples` (under `tuple_align`),
//!    `sort_alias`, `type_preds`, `extract`, `value_type`.
//!  * Declaration checks — `sorts` (`type_check_sorts`), `signature`, `elaborate`,
//!    `op_bodies`.
//!  * Rules — `rules`, `rule_requirements`, `anchor`, `rule_dispatch`, `rule_constraints`.
use std::collections::{HashMap, HashSet};
use std::ops::Range;
use std::rc::Rc;

use smallvec::SmallVec;

use super::discrim::SubstTree;
use super::load::LoadError;
use super::node_occurrence::{
    for_each_child, for_each_pattern_child, materialize_from_handle, pattern_annotation_value,
    value_to_pattern_annotation, value_to_term, with_pattern_annotation, EffectExprNode, Expr,
    MatchBranch, NodeKind, NodeOccurrence, Pattern, TypeChild, TypeNode,
};
use super::persist_subst::BindValue;
use super::resolve::PositionalPlan;
use super::subst::Substitution;
use super::term::{Literal, Term, TermId, Var, VarId};
use super::term_view::{views_structurally_equal, TermIdView, TermView, ViewHead, ViewItem};
use super::{KnowledgeBase, RuleId, SortKind};
use crate::eval::value::{Dictionary, Value};
use crate::intern::{is_positional_label_at, positional_label, ScopeId, Symbol};
use crate::parse::desugar_target as dt;
use crate::span::Span;

/// The typer's own unit tests, moved out of `typing.rs` by WI-20260830-009H2. See
/// `typing/tests.rs` for what that move did and, just as importantly, what it did NOT do.
#[cfg(test)]
mod tests;

/// WI-799: the alignment policy and its axes, SEALED in a private module.
/// WI-803 added a THIRD axis ([`TupleOrder`]); the seal below is stated over the
/// width×names pair because that is the pairing it has to make unconstructible.
///
/// Width and names are independent, which yields FOUR combinations while only
/// THREE are disciplines. The fourth — `Subset` width with the synthetic escape —
/// is not
/// merely unused, it is UNSOUND: the escape branch in
/// [`align_named_tuple_slots`] zips the two lists without consulting width, and
/// `zip` stops at the shorter one, so a subset width would silently relate
/// `(a: Int64, b: String, c: Bool)` to the positional `(Int64, String)` by
/// truncation — precisely the relation proposal 004 rule 4 forbids, reached
/// through the back door of the OTHER axis.
///
/// So the fields are private to this module and the three constants are the only
/// constructors: the illegal combination is a COMPILE ERROR outside, not a
/// convention. This is why the constants are associated rather than free consts
/// in the [`GateSpec`](crate::kb::resolve) style — here they are the type's
/// constructors, not merely named values of it.
mod tuple_align;
use tuple_align::{TupleAlign, TupleNames, TupleOrder, TupleWidth};

mod anchor;
mod apply;
mod arg_hints;
mod args;
mod bridge;
mod build;
mod call_class;
mod callable;
mod candidates;
mod carrier;
mod coherence;
mod constructor;
mod dep_projection;
mod dict;
mod dispatch;
mod display;
mod dot_rule;
mod effects;
mod elaborate;
mod env;
mod error;
mod eta;
mod expr;
mod extract;
mod forms;
mod gamma;
mod op_bodies;
mod pattern;
mod projection;
mod provides_index;
mod provision;
mod relation;
mod requires;
mod result;
mod rule_constraints;
mod rule_dispatch;
mod rule_requirements;
mod rules;
mod signature;
mod slots;
mod sort_alias;
mod sorts;
mod subtype;
mod synth;
mod tuples;
mod type_ctor;
mod type_preds;
mod unify;
mod value_type;
mod visit;

use anchor::*;
pub use apply::*;
use arg_hints::*;
pub(crate) use args::*;
pub(crate) use bridge::*;
pub(crate) use build::*;
pub use call_class::*;
pub(crate) use callable::*;
pub use candidates::*;
pub use carrier::*;
pub use coherence::*;
use constructor::*;
pub use dep_projection::*;
pub use dict::*;
pub use dispatch::*;
pub use display::*;
use dot_rule::*;
pub(crate) use effects::*;
use elaborate::*;
pub use env::*;
pub use error::*;
pub(crate) use eta::*;
pub use expr::*;
pub use extract::*;
pub(crate) use forms::*;
pub use gamma::*;
use op_bodies::*;
use pattern::*;
pub(crate) use projection::*;
pub(crate) use provides_index::*;
pub(crate) use provision::*;
pub(crate) use relation::*;
pub use requires::*;
pub use result::*;
use rule_constraints::*;
use rule_dispatch::*;
use rule_requirements::*;
pub(crate) use rules::*;
pub use signature::*;
pub use slots::*;
pub(crate) use sort_alias::*;
pub use sorts::*;
pub use subtype::*;
pub use synth::*;
use tuples::*;
use type_ctor::*;
pub use type_preds::*;
pub use unify::*;
pub use value_type::*;
use visit::*;

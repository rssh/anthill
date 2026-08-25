//! WI-20260825-5W3RJ — THE ADDRESSES THE CONVERTER DESUGARS INTO.
//!
//! `match` / `if` / `let` / `lambda`, member access, the higher-order and dotted
//! application forms, and the `[…]` / `{…}` / `(…)` literals are SYNTHESIZED: the
//! converter builds a `Term::Fn` for each, and its functor has to denote a declaration
//! in `anthill.reflect`. These constants are what it names.
//!
//! # Why a full name and not a short one
//!
//! Until this ticket the converter minted the SHORT name (`alloc_marker_term("if_expr",
//! …)`) and the loader looked it up in `KERNEL_VOCAB_QUALIFIED` — 28 stdlib addresses
//! written into the resolver as the lowest rung of the name ladder. That encoded one
//! fact twice: the mint site said *which form*, the table said *where it lives*, and
//! nothing kept the two agreeing. Renaming a declaration in `reflect.anthill` silently
//! unbound the mint; a user's same-spelled name in scope CAPTURED it, because a bare
//! name is a name and the tier sat below scope resolution.
//!
//! Naming the target outright removes the second encoding rather than re-sourcing it.
//! There is no table and no fallback rung: the mint resolves through the ordinary
//! dotted ladder.
//!
//! THAT IS NOT THE SAME AS "nothing has to be kept in step", and an earlier draft of
//! this doc said so wrongly. What went away is the DUPLICATION — a lookup keyed on a
//! name produced elsewhere. These constants still have to name declarations that exist,
//! and they are supplied by two mechanisms: `load::register_stdlib_scopes` pre-defines
//! the literal carriers and the `Expr` entities in Rust, while `field_access` exists
//! only because `stdlib/anthill/reflect/reflect.anthill` declares it. A rename in either
//! surfaces at the USE site rather than as a named orphan, so
//! `wi040_reserved_vocab_test::every_desugar_target_is_declared_by_the_standard_load`
//! is the row that names it. Raised by `/code-review`. `Loader::ExprBuilderSyms` already resolved this same vocabulary this
//! same way — the short-name rung was the duplicate of it, not the mechanism.
//!
//! # THE `..` MARKER IS LOAD-BEARING, and an unmarked path does NOT do this
//!
//! Every constant carries [`crate::intern::ABSOLUTE_PATH_MARKER`]. An *unmarked*
//! `anthill.reflect.Expr.if_expr` takes the RELATIVE, head-qualified reading (WI-1075):
//! `resolve_in_scope("anthill", scope)` first, and only then a lookup under whatever
//! that answered. So the head segment IS a scope rung, and any scope where `anthill`
//! resolves to something else captures the desugaring.
//!
//! MEASURED, with a control, on the unmarked version: a sibling `namespace
//! myapp.anthill` beside the using namespace turned `(a: 1, b: 2)`, `{1, 2}` and a
//! higher-order `?P(?x)` into "unknown functor" / "names nothing" — while renaming that
//! sibling to `myapp.anthillX` loaded clean. A file-local `sort anthill` does it too.
//! The breakage is PARTIAL, which is what makes it hard to attribute: `if` / `match` /
//! `let` / lambda and an identifier-receiver `p.x` survive, because their loader arms are
//! shape-gated and never resolve the functor at all. Found by `/code-review`.
//!
//! The marker is the right instrument rather than a special case in the resolver: it is
//! unspellable by any identifier (`_identifier_token` cannot contain `..`), so a marked
//! head can collide with no user declaration — which is precisely the guarantee a
//! desugar target needs.
//!
//! # Reading one back
//!
//! A parse-level reader asking "is this functor that form?" must use [`is`], never `==`
//! against a short spelling: the converter's own nodes now carry the address, while a
//! name a USER wrote is still short. Both readings are the same question and [`is`]
//! answers it once. (Every reader whose arm is already gated on
//! `SimpleTermStore::is_minted` may compare to the constant directly — provenance has
//! already excluded the written spelling there.)
//!
//! THE READERS ARE NOT ALL IN THE LOADER, and a census that assumes so misses the ones
//! that cost most. `persistence::print` compares a functor name too, and it runs over a
//! `ParsedFile` as well as a KB — so with `==` the parse-side print of `[1, 2]` stopped
//! rendering as a bracket, the content-addressed retract key stopped matching the
//! KB-side print, and a retracted fact was left on disk with no error anywhere. Found by
//! `wi1099_list_literal_twin_test::a_persisted_literal_is_still_retractable`, which
//! documents itself as the only row that measures that split.
//!
//! THAT FIX IS PER NAME AND THE SPLIT IS PER VIEW — stated rather than left implicit.
//! `TermSource::sym_name` returns the interned functor VERBATIM for a `ParsedFile` and
//! the short local name for a KB, so the two views disagree about every desugared
//! functor, not just `ListLiteral`. Only `[…]` is surface-printed today, so no other
//! form reaches a print where the disagreement matters — but the failure it produces is
//! a retracted fact silently left on disk, so the boundary is worth knowing: keying the
//! parse view on the last segment would close it once instead of per name. Raised by
//! `/code-review`; not changed here because `sym_name`'s contract has readers well
//! outside this concern and narrowing it needs its own census.

/// `x.field` — emitted for every member access.
pub const FIELD_ACCESS: &str = "..anthill.reflect.field_access";
/// `?P(a, b)` — higher-order application.
pub const HO_APPLY: &str = "..anthill.reflect.Expr.ho_apply";
/// `receiver.name(args)` — the pre-dispatch dotted form (WI-278).
pub const DOT_APPLY: &str = "..anthill.reflect.Expr.dot_apply";
/// `{x, y}`
pub const SET_LITERAL: &str = "..anthill.reflect.SetLiteral";
/// `[x, y]`
pub const LIST_LITERAL: &str = "..anthill.reflect.ListLiteral";
/// `(x, y)` / `(name: v)` / `()`
pub const TUPLE_LITERAL: &str = "..anthill.reflect.TupleLiteral";
/// `match e { … }`
pub const MATCH_EXPR: &str = "..anthill.reflect.Expr.match_expr";
/// `if c then t else e`
pub const IF_EXPR: &str = "..anthill.reflect.Expr.if_expr";
/// `let p = v in b`
pub const LET_EXPR: &str = "..anthill.reflect.Expr.let_expr";
/// `\p -> b`
pub const LAMBDA_EXPR: &str = "..anthill.reflect.Expr.lambda_expr";

/// The short spelling of a desugar target — its last segment, which is the name a user
/// can still write and the local name the resolved symbol carries. The `..` marker rides
/// on the HEAD segment, so it never reaches this.
pub fn short(target: &str) -> &str {
    target.rsplit('.').next().unwrap_or(target)
}

/// Does the parse-level functor name `name` denote the desugar target `target`?
///
/// TRUE FOR BOTH SPELLINGS, and that is the point: the converter's own nodes carry the
/// address, a user writing `field_access(…)` by hand carries the short name, and a
/// reader asking about the SHAPE means both. Readers gated on `is_minted` have already
/// excluded the written spelling and compare to the constant directly instead.
pub fn is(name: &str, target: &str) -> bool {
    name == target || name == short(target)
}

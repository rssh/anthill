//! WI-20260825-5W3RJ — THE ADDRESSES THE CONVERTER DESUGARS INTO.
//!
//! `match` / `if` / `let` / `lambda`, member access, the higher-order and dotted
//! application forms, the `[…]` / `{…}` / `(…)` literals, `!` and `requires(X)` /
//! `require[X]` are SYNTHESIZED: the converter builds a `Term::Fn` for each, and its
//! functor has to denote something the loader can resolve. These constants are what it
//! names.
//!
//! # Two namespaces, and three ways the target comes to exist
//!
//! Most targets are reflect VOCABULARY — the reified shape of a source form. Two are
//! `anthill.kernel` CONTROL primitives: [`CUT`] (`!`) and [`FIND_DICTIONARY`]
//! (`requires(X)` / `require[X]`). The namespace follows what the form denotes; the
//! minting mechanism is the same.
//!
//! WHAT IS *NOT* THE SAME IS HOW THE TARGET GETS DEFINED, and an earlier draft of this
//! section asserted a uniformity that does not hold. Three mechanisms, not two:
//!   1. `load::register_stdlib_scopes` pre-defines the literal carriers and the `Expr`
//!      entities in Rust.
//!   2. `stdlib/anthill/reflect/reflect.anthill` declares `field_access`;
//!      `stdlib/anthill/kernel/kernel.anthill` declares `operation cut() -> Bool`.
//!   3. `KnowledgeBase::register_builtin_tags` DEFINES a missing qualified name rather
//!      than skipping it (`kb/mod.rs`), which is the only thing that defines
//!      [`FIND_DICTIONARY`] — **no `.anthill` file declares it anywhere**, so for that
//!      one member "names a declaration" is false and "names a bootstrap-minted symbol"
//!      is the truth. `load.rs` records the same fact at `find_dictionary`'s own site.
//! Mechanism 3 is also why [`CUT`]'s row in the orphan watchdog is WEAKER than
//! `FIELD_ACCESS`'s: deleting `operation cut()` from kernel.anthill leaves the symbol
//! minted and the test green. Said at that row too.
//!
//! # The class is closed for converter mints
//!
//! `CUT` and `FIND_DICTIONARY` replaced two `PRELUDE_QUALIFIED` rows, and a draft of
//! this doc called them "the last two converter mints that still depended on that
//! fallback". That was wrong when written — [`crate::parse::pratt::UNIFY_FUNCTOR`] and
//! [`crate::parse::pratt::STRUCT_EQ_FUNCTOR`] were short mints on the tier too, because
//! `<=>`, `===` and a goal-position `let` name no functor either — and WI-909 made it
//! true by migrating them, so no converter mint resolves through the tier now. A second
//! WI-909 pass then took the rung to FOUR rows — the constructors `cons` / `nil` /
//! `some` / `none`, the only names a person writes bare in SOURCE — and a third emptied
//! it and DELETED the machinery. There is no tier and no `kb::load::PRELUDE_QUALIFIED`
//! to ask; a bare constructor needs an import like any other written name. Kept as
//! history rather than cut because it records WHY the migration went in three passes.
//!
//! THOSE TWO LIVE IN `pratt`, NOT HERE, and the split is by who mints rather than by
//! what the target is: this module is the CONVERTER's table, and `<=>` / `===` are minted
//! by the infix desugar, whose functor table already holds `EQ_FUNCTOR`'s address beside
//! them. Splitting the equality family across two modules to unify the *namespace*
//! instead would put `eq` here, away from the list `is_equality_family_functor` reads.
//! What IS shared is the mechanism, and [`qualified`] is the seam: `kb::load`'s
//! connective-agreement tests read pratt's constants through it.
//!
//! Everything downstream keys on a [`crate::kb::resolve::BuiltinTag`] registered by
//! QUALIFIED name, never on the short spelling, so the address lands on the same symbol
//! the tier was reaching and reaches it one rung higher. Consumers outside the converter
//! read the address through [`qualified`] rather than writing it out. S66VH completed
//! that rule for the ten reflect targets: symbol resolution, bootstrap definitions,
//! shape comparisons, eval/codegen recognizers and their unit tests all source the
//! address here. The two dual-spelling field-access recognizers named by S66VH use
//! [`is`] instead.
//!
//! ONE RESIDUE, AND IT IS NOT A MISS — it is a language limit, stated here so the next
//! reader does not conclude the sweep is total and walk past the drift. Nine short
//! spellings are still hand-written as `match` PATTERNS: eight in
//! `kb::node_occurrence` (`materialize_from_handle`'s dispatch and
//! `is_reflect_form_functor`'s membership list) and `Some("ListLiteral")` in
//! `kb::resolve::bounded_list_elements`. A pattern cannot call [`short`], and [`short`]
//! cannot be a `const fn` without `unsafe` slicing. They are held to the addresses by
//! `node_occurrence::tests::the_hand_written_dispatch_arms_still_key_off_their_addresses`,
//! which drives the real dispatch-key function so a rename fails LOUDLY there rather
//! than quietly disabling an arm. Raised by `/code-review`.
//!
//! ONE THING THE HIGHER RUNG ADDS: A VISIBILITY GATE. The absolute rung runs
//! `resolve_dotted_in_kb`, which filters on `internal_visible_from`; the implicit tier it
//! replaced was a raw `by_qualified_name` lookup with no filter at all. Inert today —
//! nothing in `anthill.kernel` is marked `internal` — but the consequence is sharp if
//! that changes, and `kernel.anthill`'s own header ("Resolver primitives. Not for
//! application code") is a standing invitation to mark it: every `!` in every user
//! namespace would become a ForbiddenInternalAccess error citing `..anthill.kernel.cut`,
//! a string the author never typed, at the span of a one-character operator. Under the
//! tier the same edit was a no-op. Raised by `/code-review`; recorded rather than
//! guarded, because the guard would be a special case in the resolver and the marking
//! is the thing that should not happen.
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
//! name produced elsewhere. Each constant still has to name something that exists, by
//! one of the three mechanisms above, and
//! `wi040_reserved_vocab_test::every_desugar_target_is_declared_by_the_standard_load`
//! is the row that names a miss. `Loader::ExprBuilderSyms` already resolved this same
//! vocabulary this same way — the short-name rung was the duplicate of it, not the
//! mechanism.
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
//! EXCEPT FOR THE TWO KERNEL CONTROL TARGETS, where the rule INVERTS and [`is`] is the
//! wrong tool. `!` and `requires(X)` name no functor, so there is no written spelling
//! that means them: a user's `cut(…)` is an ordinary unrelated call, and admitting it
//! would reinstate the capture these addresses removed. Compare to [`CUT`] /
//! [`FIND_DICTIONARY`] directly — safe because `..` is unspellable. [`is`] asserts
//! against the misuse rather than trusting this paragraph. Raised by `/code-review`,
//! which found the module telling a reader to walk into the bug.
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
//! parse view on the last segment would close it once instead of per name. [`CUT`] and
//! [`FIND_DICTIONARY`] widen the affected set without changing that boundary: the KB
//! view prints their SHORT names, so a rendered rule body still reads `cut(0)` /
//! `find_dictionary(Eq)` — text that no longer re-parses bare from any namespace. Rules
//! are not surface-printed, so this is display-only today. Raised by
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

/// `!` in goal position — the cut control primitive (proposal 033.1 / WI-568). Minted
/// NULLARY; the resolver bakes the rule's barrier into it and keys on
/// [`crate::kb::resolve::BuiltinTag::Cut`].
pub const CUT: &str = "..anthill.kernel.cut";

/// `requires(X)` and `require[X]` — the rule-body requirement guard (WI-300, proposal
/// 060 §1). Both spellings lower here, differing only in an `out:` named argument; keyed
/// downstream by [`crate::kb::resolve::BuiltinTag::FindDictionary`] and by the typer,
/// which reads this constant through [`qualified`].
pub const FIND_DICTIONARY: &str = "..anthill.kernel.find_dictionary";

/// The kernel CONTROL targets — this module's own [`ALL`] members that are control
/// primitives rather than reflect vocabulary.
///
/// Their surface forms (`!`, `requires(X)`) name no functor, so unlike the reflect
/// vocabulary they have no legitimate written spelling. Published through
/// [`is_kernel_control`] as the partition of [`ALL`]; the guard on [`is`] reads the
/// WIDER [`NO_SURFACE_FUNCTOR`] below, which is a different question.
const KERNEL_CONTROL: &[&str] = &[CUT, FIND_DICTIONARY];

/// EVERY address whose surface form names NO FUNCTOR — the set [`is`] must never be
/// asked about, because [`is`] admits the SHORT spelling and there is no written
/// spelling that means these: a user's `cut(…)` or `unify(a, b, kb)` is an ordinary
/// unrelated call, and admitting it is the capture the addresses exist to make
/// unrepresentable.
///
/// WIDER THAN [`KERNEL_CONTROL`], AND THAT IS THE POINT (WI-909, raised by
/// `/code-review`). The guard used to read that list, which was exactly right while `!`
/// and `requires(X)` were the only two surface forms without a functor. `<=>`, `===` and
/// a goal-position `let` are three more, and when they took addresses they landed in
/// `crate::parse::pratt` — so a guard keyed on this module's own partition stopped
/// covering the class it was written for. `dt::is(name, pratt::UNIFY_FUNCTOR)` would
/// have passed the assert and answered `true` for a written short `unify`, i.e. for
/// `anthill.reflect.unify` — precisely the WI-888 capture, re-admitted through the
/// helper whose doc promises it cannot happen. No caller does that today; the guard
/// exists for the next one.
///
/// KEYED ON THE PROPERTY, not on the module a constant happens to live in, so a fourth
/// functor-less surface form joins by being listed here rather than by someone noticing
/// the omission. Four comparisons on [`is`]'s path instead of two — see that function's
/// own cost note.
const NO_SURFACE_FUNCTOR: &[&str] = &[
    CUT,
    FIND_DICTIONARY,
    crate::parse::pratt::UNIFY_FUNCTOR,
    crate::parse::pratt::STRUCT_EQ_FUNCTOR,
];

/// Is `target` one of the kernel CONTROL targets rather than reflect vocabulary?
///
/// The partition itself, published so a consumer does not have to re-derive it. S66VH's
/// `/code-review` caught `wi040_reserved_vocab_test` re-deriving it as
/// `qualified(target).starts_with("anthill.reflect.")` — which is true today and is a
/// SILENT SKIP the moment a reflect target moves namespace or a third kernel control
/// appears: the row would quietly stop covering it while reading as though it did. The
/// set is the authority, the namespace is a coincidence of it.
pub fn is_kernel_control(target: &str) -> bool {
    KERNEL_CONTROL.contains(&target)
}

/// EVERY desugar target, so a reader that must cover the set does not hand-copy it.
///
/// `wi040_reserved_vocab_test::every_desugar_target_is_declared_by_the_standard_load`
/// walks this; before it existed that test held a literal mirror of the constants, and a
/// constant added without a matching row was simply never checked for being an orphan —
/// the failure the test is named after. Peer of
/// [`crate::parse::pratt::SPEC_OP_FUNCTORS`] / [`crate::parse::pratt::CONNECTIVE_FUNCTORS`],
/// which the same test already chains. Found by `/code-review`.
pub const ALL: &[&str] = &[
    FIELD_ACCESS,
    HO_APPLY,
    DOT_APPLY,
    SET_LITERAL,
    LIST_LITERAL,
    TUPLE_LITERAL,
    MATCH_EXPR,
    IF_EXPR,
    LET_EXPR,
    LAMBDA_EXPR,
    CUT,
    FIND_DICTIONARY,
];

/// The short spelling of a desugar target — its last segment, which is the name a user
/// can still write and the local name the resolved symbol carries. The `..` marker rides
/// on the HEAD segment, so it never reaches this.
pub fn short(target: &str) -> &str {
    target.rsplit('.').next().unwrap_or(target)
}

/// The desugar target as an ORDINARY qualified name — the `..` marker stripped.
///
/// This is what a consumer OUTSIDE the converter needs. The constants carry the marker
/// because the converter mints a name for the resolver to read, but
/// `KnowledgeBase::try_resolve_symbol` and `register_builtin_tag` take the plain
/// qualified name, so without this every such site wrote the address out by hand. S66VH
/// retired the reflect ten's live resolution/comparison sites — the ticket measured 54
/// in the qualified currency, and `/code-review` on the delivering diff found five more
/// in the SHORT currency (`load.rs`'s `ho_apply` intern fallback and its
/// `TypeExpr::Tuple` base name, `resolve.rs`'s `ho_apply` recognizer, two test
/// interns), which read [`short`]. WI-909 had already routed the four
/// `FIND_DICTIONARY` sites. Found by `/code-review`.
///
/// Delegates to [`crate::intern::absolute_path_target`] rather than stripping the marker
/// here, because that function's doc claims to be its SOLE reader and the claim is worth
/// more than the line it saves. Total for every constant here, and CHECKED rather than
/// asserted: `kernel_mint_address_test::every_desugar_target_carries_the_absolute_marker`
/// walks [`ALL`] for the marker. Passing an unmarked name is a programming error and
/// panics; no input a program can write reaches it.
///
/// CALLED ON PER-NODE TYPER PATHS (`type_head`, `constructor_value_type`,
/// `check_constructor_iter`, …), which `/code-review` flagged against `kb/mod.rs`'s note
/// that `tuple_literal_sym` exists to avoid per-call string work on exactly those paths.
/// The comparison it feeds — `qualified_name_of(sym) == …`, a symbol-table lookup plus a
/// 30-byte `str` compare — was already there and dominates; what this adds is one
/// `strip_prefix` on a `&'static str`. The `Symbol`-compare fast paths that actually
/// answer WI-653's concern (`tuple_literal_sym`, `dot_apply_head_sym`) are unchanged and
/// still run first where they exist. Restructuring the remaining name-compares into
/// symbol-compares is a real improvement and a different ticket; it is not what a naming
/// sweep should do to a hot path unmeasured.
pub fn qualified(target: &str) -> &str {
    crate::intern::absolute_path_target(target)
        .expect("a desugar target is written with the absolute-path marker")
}

/// Does the functor name `name` denote the desugar target `target`?
///
/// TRUE FOR EVERY CARRIER spelling, and that is the point: the converter's own nodes
/// carry the marked address, a resolved KB symbol reports the ordinary qualified name,
/// and a user writing `field_access(…)` by hand carries the short name. A reader asking
/// about the SHAPE means all three. Readers gated on `is_minted` have already excluded
/// the written spelling and compare to the constant directly instead.
///
/// THE MIDDLE ARM IS NEW IN S66VH AND IT WIDENS SEVEN PRE-EXISTING CALLERS, which
/// `/code-review` was right to make explicit rather than let ride as a side effect of
/// two migrations. Two callers needed it — `body_specialize::field_access_parts` and
/// smt-gen's mirror read `qualified_name_of` — but `is` has no per-caller currency, so
/// the loader's parse-name sites (`load.rs` 19060 / 19939 / 20117 / 20559 / 20676) and
/// `persistence::print`'s two list-literal rows admit the plain qualified spelling now
/// as well. On the KB view nothing changes: `local_name_of` yields the short name, so
/// the middle arm is unreachable there. On the PARSE view it is reachable, and the
/// answer it gives is the RIGHT one: a source file writing
/// `anthill.reflect.ListLiteral(1, 2)` in full already resolves through the absolute
/// rung and is already lowered by `load::list_literal_lowering`
/// (`wi040_reserved_vocab_test::query_pattern_list_literal_needs_its_address` measures
/// the resolve), so printing it as `[1, 2]` narrows the parse-view/KB-view gap that
/// `print.rs`'s own comment complains about instead of widening it. The one visible
/// consequence: a fact hand-authored in that fully-qualified spelling gets a different
/// content-addressed retract key than it did before. No producer writes it — a
/// round-trip persist prints from the KB view, i.e. the short name — so only a
/// hand-written file is affected.
pub fn is(name: &str, target: &str) -> bool {
    // NOT FOR THE KERNEL CONTROL TARGETS. Admitting the short spelling is right for
    // reflect vocabulary — a hand-written `field_access(…)` is the same SHAPE — and
    // exactly wrong for `!` / `requires(X)`, whose surface forms name no functor: there
    // a user's `cut(…)` is an unrelated call, and reading it as the primitive
    // reinstates the capture the addresses were introduced to remove. Caught by
    // `/code-review` as a contract that would have been followed into the bug.
    // A PLAIN `assert!`, not `debug_assert!`: the misuse it catches produces a silent
    // wrong answer (a user's `cut(...)` read as the control primitive), and WI-1122
    // records what a release-only gap costs. The cost is FOUR string comparisons against
    // the [`NO_SURFACE_FUNCTOR`] constants (`<[&str]>::contains` compares contents, not
    // pointers) — two until WI-909 widened the guard from [`KERNEL_CONTROL`],
    // on a call that already does three of its own PLUS the `strip_prefix` inside
    // `qualified` — negligible, but stated correctly: this comment said "pointer
    // comparisons" until `/code-review` read the impl, then undercounted the third
    // comparison and the `qualified` call until it read the impl again, and a mis-sized
    // load cost is what WI-653 had to re-diagnose.
    assert!(
        !NO_SURFACE_FUNCTOR.contains(&target),
        "desugar_target::is admits the short spelling and must not be used for a target \
         whose surface form names no functor ({target}); compare to the constant directly"
    );
    name == target || name == qualified(target) || name == short(target)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The SMT WI-681 path supplies `KnowledgeBase::qualified_name_of` here, while the
    /// parse and persistence paths supply the other two carriers.
    ///
    /// THE BACK-OUT IS IN `is`, NOT IN THIS TEST. The doc here used to say "removing
    /// the middle assertion" made qualified field access fall through — which is not a
    /// control at all, since deleting an assertion cannot change production behaviour.
    /// What backs the change out is deleting `name == qualified(target)` from [`is`];
    /// that reds the middle row here and, more to the point, reds
    /// `body_specialize::s66vh_field_access_recognizer_tests`, which DRIVES one of the
    /// two recognizers the arm was added for (the other is smt-gen's, out of this
    /// crate's reach). The first and last rows pass either way and are the
    /// representation control.
    #[test]
    fn reflect_shape_recognition_accepts_every_name_carrier() {
        assert!(is(FIELD_ACCESS, FIELD_ACCESS));
        assert!(is(qualified(FIELD_ACCESS), FIELD_ACCESS));
        assert!(is(short(FIELD_ACCESS), FIELD_ACCESS));
    }

    /// A kernel control target must never reach [`is`] — the short spelling it admits
    /// is a user's unrelated `cut(…)`. The `assert!` is a plain one precisely so this
    /// holds in release; this row is what says so out loud.
    #[test]
    #[should_panic(expected = "whose surface form names no functor")]
    fn a_kernel_control_target_is_refused_by_is() {
        let _ = is(qualified(CUT), CUT);
    }

    /// …AND SO IS A CONNECTIVE THAT LIVES IN `pratt` (WI-909). Same class, different
    /// module: `<=>` names no functor, so admitting `is`'s SHORT arm would read a
    /// written `unify(a, b, kb)` — `anthill.reflect.unify`, a real 3-arg operation — as
    /// the kernel primitive. That is the WI-888 capture the address removed.
    ///
    /// FAILS ON BACK-OUT of the guard's widening (`NO_SURFACE_FUNCTOR` -> the narrower
    /// `KERNEL_CONTROL`): `is` then returns `true` instead of panicking, and this row is
    /// the only thing that says so. Raised by `/code-review`, which found the guard had
    /// silently stopped covering the class its own doc names.
    #[test]
    #[should_panic(expected = "whose surface form names no functor")]
    fn a_functor_less_connective_is_refused_by_is_even_though_pratt_owns_it() {
        let _ = is("unify", crate::parse::pratt::UNIFY_FUNCTOR);
    }

    /// Every target's short spelling is its last segment and carries no marker — the
    /// property `node_occurrence`'s hand-written `match` arms depend on, and the one
    /// `is`'s third arm must not collide with.
    #[test]
    fn every_target_short_name_is_its_last_segment() {
        for target in ALL {
            let q = qualified(target);
            assert!(!short(target).contains('.'), "{target}: short name is a segment");
            assert!(!q.starts_with(".."), "{target}: qualified name drops the marker");
            assert!(
                q.ends_with(short(target)),
                "{target}: short name is the tail of the qualified name",
            );
        }
    }
}

/// Pratt parser for operator precedence desugaring.
///
/// The tree-sitter grammar produces flat infix chains: `[a, +, b, *, c]`.
/// This module applies operator precedence and associativity to produce
/// nested `Term::Fn` calls: `add(a, mul(b, c))`.
use smallvec::SmallVec;

use super::ir::SimpleTermStore;
use crate::intern::{Symbol, SymbolTable};
use crate::kb::term::{Term, TermId};
use crate::span::Span;

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

/// The functor the infix `->` desugars to (a binary arrow-type term).
pub const ARROW_FUNCTOR: &str = "arrow";
/// The functor the ternary `-> … @ …` desugars to (an effectful arrow type).
pub const ARROW_EFFECT_FUNCTOR: &str = "arrow_effect";

/// WI-20260825-KD9SW — THE TWELVE SPEC-OPERATION ADDRESSES A MINTED OPERATOR NAMES.
///
/// A minted operator used to carry the SHORT functor (`"add"`) and `kb::load`'s
/// `PRELUDE_QUALIFIED` said where that lived (`anthill.prelude.Additive.add`). Two
/// encodings of one fact, with nothing keeping them in step — and the second sat BELOW
/// scope resolution, so a same-spelled name in scope CAPTURED the operator. Driven,
/// before this ticket: with `import Weird.{add}` in scope, `1 + 2` answered `99`.
///
/// This is WI-20260825-5W3RJ's move one table over, and the reasoning is entirely that
/// module's — see [`crate::parse::desugar_target`] for why the `..` marker is the right
/// instrument (it is unspellable by any identifier, so a marked head can collide with no
/// user declaration) and for the reader rule that comes with it.
///
/// THE ADDRESS IS THE SPEC OP, NOT A CARRIER, so this costs no polymorphism: the spec op
/// is what dispatches. Driven — a `Money` providing `Additive[T = Money]` answers
/// `money(700) + money(25)` = 725 through its own `add`, with `+` naming
/// `..anthill.prelude.Additive.add`.
///
/// AND IT IS WHY THE SPEC SPLITS HAD TO LAND FIRST. The address names where the
/// operation is DECLARED, so WI-20260825-1WBZT moving `add` off `Numeric` onto
/// `Additive` changed it. These are the post-1WBZT / post-VT8CF homes, and a later split
/// must move them HERE rather than leaving a table to drift.
pub const ADD_FUNCTOR: &str = "..anthill.prelude.Additive.add";
pub const SUB_FUNCTOR: &str = "..anthill.prelude.Additive.sub";
pub const NEG_FUNCTOR: &str = "..anthill.prelude.Additive.neg";
pub const MUL_FUNCTOR: &str = "..anthill.prelude.Multiplicative.mul";
pub const DIV_FUNCTOR: &str = "..anthill.prelude.Divisible.div";
pub const MOD_FUNCTOR: &str = "..anthill.prelude.EuclideanDomain.mod";
pub const NEQ_FUNCTOR: &str = "..anthill.prelude.PartialEq.neq";
pub const LT_FUNCTOR: &str = "..anthill.prelude.PartialOrd.lt";
pub const LTE_FUNCTOR: &str = "..anthill.prelude.PartialOrd.lte";
pub const GT_FUNCTOR: &str = "..anthill.prelude.PartialOrd.gt";
pub const GTE_FUNCTOR: &str = "..anthill.prelude.PartialOrd.gte";

/// WI-20260825-P9Y67 — THE THREE CONNECTIVE ADDRESSES A MINTED BOOLEAN OPERATOR NAMES.
///
/// [`SPEC_OP_FUNCTORS`] one table over, and for the same reason: a minted operator that
/// carries a SHORT functor is resolved down the ordinary name ladder, whose lowest rung
/// is the implicit tier, so a same-spelled declaration in scope CAPTURES it. Driven,
/// before this ticket, on all six rows — a namespace-level `operation or(a: Bool, b:
/// Bool) -> Bool = false` turned an op-body `true | true` into `false`, and a rule body's
/// `p(?x) | p(99)` from `?x = 1` into a floundered conditional with the residual
/// `eq(or(p(?_), p(99)), true)`. The goal row is the one that matters: the disjunction
/// stops being a disjunction, `?x` never binds, and nothing is reported.
///
/// THE ADDRESS IS THE KERNEL CONNECTIVE, NOT A SPEC OP, which is the one way this list
/// differs from the twelve — and it is why no library move had to land first. `+` needed
/// WI-1WBZT to split `Numeric` because the address names where the operation is
/// DECLARED and `Numeric.add` was a bundle. These three already have exactly one honest
/// declaration each: the resolver primitive. `|` IS disjunction, and disjunction is
/// `push_choice`; there is no spec to split and none to invent.
///
/// THE VALUE READING IS NOT LOST, and this is the whole reason the goal spelling is the
/// right address rather than a choice between two. `not`/`or`/`and` are POSITION-DIRECTED
/// (§6.6): a rule-body goal means the primitive, an operation body means the dispatched
/// `Bool` op. That routing already runs on the RESOLVED SYMBOL, downstream of the ladder
/// — `Loader::redirect_op_body_boolean` maps `kernel.X` to `Bool.X` whenever
/// `in_op_body_value` — so an addressed mint reaches the value op exactly as a
/// tier-resolved short name did, and its goal-position peer
/// (`Loader::route_body_goal_boolean`) is simply a no-op on a functor already at the goal
/// spelling. NO NEW ROUTING IS ADDED ANYWHERE, and that is what distinguishes this from
/// the attempt withdrawn from WI-20260824-BFB9A: `reclaim_minted_operator` added a
/// `goal_position_boolean` call to `convert_query_term_expecting`'s `Term::Fn` arm, which
/// recurses through itself into positional AND named args, so it routed at every depth
/// and on WRITTEN calls — measured, a fact holding `or(true, false)` became unqueryable
/// by any spelling, exit 0, no diagnostic. A written `or` carries no `..`, so that
/// failure mode is unreachable here.
///
/// THIS TICKET TRIED TO ADD ROUTING ANYWAY AND HAD TO BACK IT OUT, which is why the
/// sentence above is a rule rather than an observation. §6.6 says a goal's ARGUMENT is a
/// value expression, so redirecting a rule body's non-goal slots (`kernel.X` → `Bool.X`)
/// looked like a missing mirror. It reproduced BFB9A's defect from the other side: fact
/// heads, rule heads and query patterns build through `convert_term` and are NOT
/// redirected, so `rule r() :- holds(not(true))` stopped matching `fact holds(not(true))`
/// — exit 0, no diagnostic, with an entity control in the same file still green. A DATA
/// SLOT HOLDS A TERM and a term's spelling is its identity. Position knowledge belongs at
/// a consumer that knows it is reading a condition (`anthill-smt-gen`'s condition
/// lowering reads both spellings); the loader cannot tell a condition from a reified goal
/// being stored. Caught by `/code-review`; the lesson is recorded at the site in
/// `kb::load` as well, because that is where the next attempt would be written.
///
/// THE TIER ENTRIES ARE GONE TOO (WI-20260826-XED22). This doc used to say the three
/// KEEP their `kb::load::PRELUDE_QUALIFIED` entries because "the stdlib writes bare
/// `not(...)` in rule bodies throughout" — measured, and that reason was wrong twice
/// over. A written bare `or(...)` / `and(...)` now needs an import like any other name.
/// A written `not(...)` needs NOTHING, and never did: `not` is a PREFIX OPERATOR
/// (`prefix_entry`), so `not(x)` mints [`NOT_FUNCTOR`] and never runs the name ladder at
/// all — its tier entry was already dead. So the split KD9SW drew still holds, with one
/// name fewer on the written side than it looked: the operator is uncapturable, and the
/// written spelling is an ordinary name wherever there IS one.
pub const OR_FUNCTOR: &str = "..anthill.kernel.or";
pub const AND_FUNCTOR: &str = "..anthill.kernel.and";
pub const NOT_FUNCTOR: &str = "..anthill.kernel.not";

/// The three, as one list. Peer of [`SPEC_OP_FUNCTORS`], kept SEPARATE rather than merged
/// into it because the two answer different questions: every member of that list is a
/// spec operation on a parametric carrier and dispatches, and these are resolver
/// primitives that never dispatch at all. Merging them would make the name of the wider
/// list a lie at three of fifteen entries — and `spec_op`-shaped readers ask a real
/// question. Both lists are chained by
/// `wi040_reserved_vocab_test::every_desugar_target_is_declared_by_the_standard_load`,
/// which is what keeps either from naming an orphan.
pub const CONNECTIVE_FUNCTORS: &[&str] = &[OR_FUNCTOR, AND_FUNCTOR, NOT_FUNCTOR];

/// The twelve, as one list — the population `kb::load::check_rival_spec_operations`
/// existed to refuse a capture of, and which this ticket makes uncapturable instead.
///
/// ELEVEN OF THEM ARE REACHABLE FROM SOURCE. [`NEG_FUNCTOR`] is the prefix `-` entry's
/// target, and no surface form mints it: a prefix `-` on a non-literal is a SYNTAX ERROR
/// (WI-529 — it collides with negative-literal lexing; kernel-language.md §6.6 states
/// it), so `-x` does not parse and `-5` lexes as a literal. It stays in this list because
/// it is what that entry names, and because the tier entry it replaces WAS real — a
/// WRITTEN `neg(x)` resolved through `PRELUDE_QUALIFIED` and now needs an import like any
/// other written name. Its address is therefore pinned only by
/// `wi040_reserved_vocab_test::every_desugar_target_is_declared_by_the_standard_load`;
/// nothing can drive it from source. Found by `/code-review`, which caught the earlier
/// doc here claiming a coverage it did not have.
pub const SPEC_OP_FUNCTORS: &[&str] = &[
    ADD_FUNCTOR,
    SUB_FUNCTOR,
    NEG_FUNCTOR,
    MUL_FUNCTOR,
    DIV_FUNCTOR,
    MOD_FUNCTOR,
    EQ_FUNCTOR,
    NEQ_FUNCTOR,
    LT_FUNCTOR,
    LTE_FUNCTOR,
    GT_FUNCTOR,
    GTE_FUNCTOR,
];

/// The functors the infix desugar mints for the equality family, `=`/`<=>`/`===`
/// (proposal 049/051). Only `unify` is an EQUATION connective — see
/// [`EQUATION_FUNCTORS`].
///
/// `EQ_FUNCTOR` is one of [`SPEC_OP_FUNCTORS`] and so carries an ADDRESS, while `unify`
/// and `struct_eq` are KERNEL primitives and stay short. Every reader of this family
/// compares against these constants rather than against a spelling, which is what lets
/// the list be mixed without a second rule.
pub const EQ_FUNCTOR: &str = "..anthill.prelude.PartialEq.eq";
pub const UNIFY_FUNCTOR: &str = "unify";
pub const STRUCT_EQ_FUNCTOR: &str = "struct_eq";

/// The equality-family connectives — every functor the infix desugar mints for a
/// binary equality operator, whatever it MEANS. One SHAPE: the connective at the
/// head, its operands at `pos_args[0]` and `[1]`. Read by
/// [`is_equality_family_functor`].
///
/// This is the list a reader consults when its question is about the shape rather
/// than the meaning — WHERE a head's `[T]` introducer rides
/// (`Loader::collect_rule_tvar_names`, WI-619) is such a question, and its answer is
/// "on the LHS operand" for every member, including the ones that define nothing.
/// WI-1090 learned that the hard way: narrowing [`EQUATION_FUNCTORS`] alone silently
/// took a bodied `g[T](?x) === ?x :- p(?x)`'s bracket away from the one reader that
/// consumes it, which is precisely the WI-619 defect for a new spelling.
pub const EQUALITY_FAMILY_FUNCTORS: &[&str] = &[EQ_FUNCTOR, UNIFY_FUNCTOR, STRUCT_EQ_FUNCTOR];

/// The EQUATION connectives: the SUBSET of [`EQUALITY_FAMILY_FUNCTORS`] whose minted
/// node, as a bodyless rule head, is a DEFINING EQUATION — the subject at
/// `pos_args[0]` is a name the rule introduces and the normalizer can fire. Read by
/// [`is_equation_functor`], which is the only way to ask.
///
/// IT HAS ONE MEMBER, and the spec's equality table decides which
/// (§"Equality: test vs. bind, structural vs. semantic"): `=` and `===` are the TEST
/// column, `<=>` is the BIND column alone, and only a connective that BINDS can head
/// an equation — the head *unifies* the redex with the LHS and derives the RHS.
/// `struct_eq` left under WI-1090, `eq` under WI-888, and the two departures are the
/// same rule applied to the same table row rather than two decisions.
///
/// THEY WERE NOT THE SAME DEFECT, though, and the difference is why the second one
/// needed a ticket of its own. A `===` head was silently USELESS: measured on a
/// `[simp]`-tagged `g(?x) === ?x`, the subject was stamped
/// [`SymbolKind::EquationFunctor`](crate::intern::SymbolKind) with ZERO clauses under
/// it, `simp_equation_rids` (the eq+unify buckets) could never reach the rule, and
/// citing `g` was refused with "defined by equations … no defining equation for it can
/// be found" — about an equation written three lines up. An `=` head WORKED: measured
/// across all four (connective × attribute) combinations on one shape (WI-884), the
/// answer tracks the `[simp]` ATTRIBUTE alone — `=` fires and `<=>` without the tag is
/// dead. So `=` is refused not to repair a silence but to finish proposal 049's
/// migration (build step 6, WI-526), whose 40-head first pass left 44 more in the
/// stdlib and whose affordance — the KB owner matching BOTH connectives — was
/// documented from the start as holding only "while the relabel is in flight".
///
/// THE KB-SIDE OWNER IS DELIBERATELY WIDER, and this is the one place the two lists
/// part company. [`KnowledgeBase::is_equality_connective_functor`](crate::kb::KnowledgeBase)
/// still answers `true` for `eq`, because it is asked a different question: which head
/// SHAPES the WI-139 cite-required unindexing withholds from `rules_by_functor`, and
/// that must keep covering a BODIED `f(?x) = g(?x) :- p(?x)` — a shape this list never
/// judged and WI-888 deliberately did not move (proposal 049 draws its migration
/// boundary at the empty body). `load::wi888_connective_agreement_tests` pins the
/// containment in both directions so neither side can drift.
pub const EQUATION_FUNCTORS: &[&str] = &[UNIFY_FUNCTOR];

/// Is `name` one of the arrow-family functors the pratt desugar mints for
/// `->`/`@`? The loader's bare-arrow diagnostics (WI-605/WI-618) key on this
/// together with `SimpleTermStore::is_minted` — one source of truth with the
/// TABLE below, so a new arrow spelling cannot drift out of the diagnostics.
pub fn is_arrow_functor(name: &str) -> bool {
    name == ARROW_FUNCTOR || name == ARROW_EFFECT_FUNCTOR
}

/// Is `name` an EQUATION connective — one of [`EQUATION_FUNCTORS`]? Kept as one
/// source of truth with the TABLE below (via the shared constants), so a new
/// equation spelling cannot drift out of the loader's equational-head recognition
/// (WI-619: the `[T]` introducer on an equational head rides on the LHS operand,
/// not the whole `eq(lhs, rhs)` node). Parse-layer peer of the KB-side
/// `is_equational_head` — a SUBSET of it, not a mirror, for the reason
/// [`EQUATION_FUNCTORS`] records; the containment is pinned by
/// `load::wi888_connective_agreement_tests`, which walks this list, the family list
/// and the KB cache.
///
/// WI-948 — A NAME, NOT A VERDICT. The spellings are ordinary identifiers a user may
/// write as a call, so this predicate never decides ON ITS OWN that a node is an
/// equation: pair it with [`SimpleTermStore::is_minted`](crate::parse::ir::SimpleTermStore::is_minted),
/// exactly as [`is_arrow_functor`] is paired above. `load::parse_equation_lhs` is the
/// one caller that asks the question about a rule HEAD, and it carries the pairing.
pub fn is_equation_functor(name: &str) -> bool {
    EQUATION_FUNCTORS.contains(&name)
}

/// Is `name` an equality-family connective — one of [`EQUALITY_FAMILY_FUNCTORS`]?
/// The SHAPE question, wider than [`is_equation_functor`] by exactly the connectives
/// that compare without defining. Ask this one when what you need is where the
/// operands sit; ask the other when what you need is whether the head DEFINES.
pub fn is_equality_family_functor(name: &str) -> bool {
    EQUALITY_FAMILY_FUNCTORS.contains(&name)
}

fn infix_entry(op: &str) -> Option<&'static InfixEntry> {
    static TABLE: &[(&str, InfixEntry)] = &[
        (
            "|",
            InfixEntry {
                priority: 1,
                assoc: Assoc::Left,
                functor: OR_FUNCTOR,
                continuation: None,
            },
        ),
        (
            "or",
            InfixEntry {
                priority: 1,
                assoc: Assoc::Left,
                functor: OR_FUNCTOR,
                continuation: None,
            },
        ),
        (
            "&",
            InfixEntry {
                priority: 2,
                assoc: Assoc::Left,
                functor: AND_FUNCTOR,
                continuation: None,
            },
        ),
        (
            "and",
            InfixEntry {
                priority: 2,
                assoc: Assoc::Left,
                functor: AND_FUNCTOR,
                continuation: None,
            },
        ),
        (
            "=",
            InfixEntry {
                priority: 3,
                assoc: Assoc::None,
                functor: EQ_FUNCTOR,
                continuation: None,
            },
        ),
        (
            "!=",
            InfixEntry {
                priority: 3,
                assoc: Assoc::None,
                functor: NEQ_FUNCTOR,
                continuation: None,
            },
        ),
        // WI-522 / proposal 049: `<=>` = unify (anthill.kernel.unify). It lexes as one
        // `operator_symbol` token (the regex matches the longest run, so `<=>` wins over
        // `<=`); here it maps to the `unify` functor. The resolver `builtin_unify` is WI-523.
        (
            "<=>",
            InfixEntry {
                priority: 3,
                assoc: Assoc::None,
                functor: UNIFY_FUNCTOR,
                continuation: None,
            },
        ),
        // WI-615 / proposal 051: `===` = structural identity test (anthill.kernel.struct_eq).
        // Like `<=>`, it lexes as one `operator_symbol` token — the longest-run regex makes
        // `===` win over `==`/`=` — so no grammar change is needed. Maps to the `struct_eq`
        // functor; the resolver reuses `builtin_eq` (structural, never dispatches). Distinct
        // from `=`/`eq` (`anthill.prelude.PartialEq.eq`), which is semantic (Phase 2 / WI-616).
        (
            "===",
            InfixEntry {
                priority: 3,
                assoc: Assoc::None,
                functor: STRUCT_EQ_FUNCTOR,
                continuation: None,
            },
        ),
        (
            "<",
            InfixEntry {
                priority: 4,
                assoc: Assoc::None,
                functor: LT_FUNCTOR,
                continuation: None,
            },
        ),
        (
            "<=",
            InfixEntry {
                priority: 4,
                assoc: Assoc::None,
                functor: LTE_FUNCTOR,
                continuation: None,
            },
        ),
        (
            ">",
            InfixEntry {
                priority: 4,
                assoc: Assoc::None,
                functor: GT_FUNCTOR,
                continuation: None,
            },
        ),
        (
            ">=",
            InfixEntry {
                priority: 4,
                assoc: Assoc::None,
                functor: GTE_FUNCTOR,
                continuation: None,
            },
        ),
        (
            "+",
            InfixEntry {
                priority: 5,
                assoc: Assoc::Left,
                functor: ADD_FUNCTOR,
                continuation: None,
            },
        ),
        (
            "-",
            InfixEntry {
                priority: 5,
                assoc: Assoc::Left,
                functor: SUB_FUNCTOR,
                continuation: None,
            },
        ),
        (
            "*",
            InfixEntry {
                priority: 6,
                assoc: Assoc::Left,
                functor: MUL_FUNCTOR,
                continuation: None,
            },
        ),
        (
            "/",
            InfixEntry {
                priority: 6,
                assoc: Assoc::Left,
                functor: DIV_FUNCTOR,
                continuation: None,
            },
        ),
        (
            "%",
            InfixEntry {
                priority: 6,
                assoc: Assoc::Left,
                functor: MOD_FUNCTOR,
                continuation: None,
            },
        ),
        (
            "mod",
            InfixEntry {
                priority: 6,
                assoc: Assoc::Left,
                functor: MOD_FUNCTOR,
                continuation: None,
            },
        ),
        (
            "div",
            InfixEntry {
                priority: 6,
                assoc: Assoc::Left,
                functor: DIV_FUNCTOR,
                continuation: None,
            },
        ),
        (
            "^",
            InfixEntry {
                priority: 7,
                assoc: Assoc::Right,
                functor: "pow",
                continuation: None,
            },
        ),
        (
            "->",
            InfixEntry {
                priority: 8,
                assoc: Assoc::Right,
                functor: ARROW_FUNCTOR,
                continuation: Some(ContinuationEntry {
                    token: "@",
                    functor: ARROW_EFFECT_FUNCTOR,
                }),
            },
        ),
    ];
    TABLE.iter().find(|(k, _)| *k == op).map(|(_, v)| v)
}

pub(crate) fn prefix_entry(op: &str) -> Option<&'static PrefixEntry> {
    static TABLE: &[(&str, PrefixEntry)] = &[
        (
            "!",
            PrefixEntry {
                priority: 9,
                functor: NOT_FUNCTOR,
            },
        ),
        (
            "not",
            PrefixEntry {
                priority: 9,
                functor: NOT_FUNCTOR,
            },
        ),
        (
            "-",
            PrefixEntry {
                priority: 9,
                functor: NEG_FUNCTOR,
            },
        ),
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

/// Allocate a synthesized operator node, recording its pratt provenance
/// (WI-618) so consumers can tell the minted infix/prefix term from a
/// user-written call to a functor of the same name. Also used by the
/// converter's standalone-prefix build (`BuildFrame::Prefix`), which mints
/// the same operator shapes outside an infix chain.
pub(crate) fn mint_op_node(
    terms: &mut SimpleTermStore,
    functor: Symbol,
    pos_args: SmallVec<[TermId; 4]>,
    span: Span,
) -> TermId {
    let tid = terms.alloc(
        Term::Fn {
            functor,
            pos_args,
            named_args: SmallVec::new(),
        },
        span,
    );
    terms.mark_minted(tid);
    tid
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
            let entry = prefix_entry(op).ok_or_else(|| format!("unknown prefix operator: {op}"))?;
            pos += 1;
            let (right, new_pos) = desugar(elements, pos, entry.priority, terms, symbols)?;
            pos = new_pos;
            let functor = symbols.intern(entry.functor);
            let span = op_span(terms, right, right);
            mint_op_node(terms, functor, SmallVec::from_elem(right, 1), span)
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
            return Err(format!("non-associative operator `{op}` cannot be chained"));
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
                left = mint_op_node(
                    terms,
                    functor,
                    SmallVec::from_slice(&[left, middle, right]),
                    span,
                );
            } else {
                // No continuation — binary infix
                let functor = symbols.intern(entry.functor);
                let span = op_span(terms, left, middle);
                left = mint_op_node(terms, functor, SmallVec::from_slice(&[left, middle]), span);
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
            left = mint_op_node(terms, functor, SmallVec::from_slice(&[left, right]), span);
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

    /// Renders the SHORT spelling of a functor, so these rows go on stating
    /// ASSOCIATIVITY and PRECEDENCE rather than restating each address twelve times.
    /// WI-20260825-KD9SW made the twelve spec operations carry an address; which address
    /// each carries is pinned once, by
    /// [`minted_operators_carry_their_spec_op_address`], and that the address DENOTES
    /// something by `wi040_reserved_vocab_test::every_desugar_target_is_declared_by_the_standard_load`.
    fn fmt_term(terms: &SimpleTermStore, symbols: &SymbolTable, tid: TermId) -> String {
        match terms.get(tid) {
            Term::Ident(sym) => symbols.local_name(*sym).to_string(),
            Term::Fn {
                functor, pos_args, ..
            } => {
                let name = crate::parse::desugar_target::short(symbols.local_name(*functor));
                let args: Vec<String> = pos_args
                    .iter()
                    .map(|&a| fmt_term(terms, symbols, a))
                    .collect();
                format!("{name}({})", args.join(", "))
            }
            other => format!("{other:?}"),
        }
    }

    /// WI-20260825-KD9SW — THE ADDRESS, pinned once. Every other row here renders the
    /// short spelling, so this is the only place that would notice a mint silently going
    /// back to a bare name — which is the state where a same-spelled declaration in scope
    /// captures the operator again.
    ///
    /// THAT THE ADDRESS DENOTES SOMETHING IS A DIFFERENT CLAIM, and it is
    /// `wi040_reserved_vocab_test::every_desugar_target_is_declared_by_the_standard_load`
    /// that carries it — this row checks only the SPELLING. An earlier draft of this doc
    /// said that test covered these constants when it walked `desugar_target`'s ten
    /// alone; it walks [`SPEC_OP_FUNCTORS`] now. Found by `/code-review`.
    ///
    /// EVERY ONE CARRIES THE MARKER, and that is the property rather than the strings:
    /// `..` is unspellable by any identifier, so a marked head can collide with no user
    /// declaration. The negative half is what says the list is not simply "everything":
    /// `pow` is deliberately NOT here, because no spec owns it.
    ///
    /// THE BOOLEAN THREE ARE ADDRESSED TOO NOW (WI-20260825-P9Y67) — but at the KERNEL
    /// connective, not a prelude spec op, so they ride [`CONNECTIVE_FUNCTORS`] and the
    /// `..anthill.prelude.` assertion above stays exact. They used to be listed here as
    /// exclusions on the ground that they are position-directed; that was the reason they
    /// carried no address, and it was wrong — the position routing runs on the RESOLVED
    /// symbol, so an address at the goal spelling preserves both readings. The two lists
    /// are asserted DISJOINT below, which is the row that would notice either drifting
    /// into the other.
    #[test]
    fn minted_operators_carry_their_spec_op_address() {
        for f in SPEC_OP_FUNCTORS {
            assert!(
                f.starts_with(crate::intern::ABSOLUTE_PATH_MARKER),
                "`{f}` must be an ABSOLUTE address — a relative path takes the \
                 head-qualified reading (WI-1075) and its head segment is a scope rung"
            );
            assert!(
                f.starts_with("..anthill.prelude."),
                "`{f}` must name a prelude declaration"
            );
        }
        assert_eq!(SPEC_OP_FUNCTORS.len(), 12, "the population is the twelve");
        assert!(
            !SPEC_OP_FUNCTORS
                .iter()
                .any(|f| super::super::desugar_target::short(f) == "pow"),
            "`pow` is NOT one of the twelve: no spec owns it"
        );
        for f in CONNECTIVE_FUNCTORS {
            assert!(
                f.starts_with(crate::intern::ABSOLUTE_PATH_MARKER),
                "`{f}` must be an ABSOLUTE address, for the reason above"
            );
            assert!(
                f.starts_with("..anthill.kernel."),
                "`{f}` must name the RESOLVER PRIMITIVE — the goal spelling is the \
                 address, and `redirect_op_body_boolean` supplies the value reading"
            );
            assert!(
                !SPEC_OP_FUNCTORS.contains(f),
                "`{f}` is a connective, not a spec op: the two lists are disjoint"
            );
        }
        assert_eq!(CONNECTIVE_FUNCTORS.len(), 3, "the population is the three");
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

        // WI-615 / proposal 051: `===` desugars to the `struct_eq` functor (greedy over `==`/`=`).
        let (terms, symbols, result) = run(&["a", "===", "b"]);
        assert_eq!(fmt_term(&terms, &symbols, result), "struct_eq(a, b)");
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

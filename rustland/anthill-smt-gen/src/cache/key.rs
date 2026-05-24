//! Cache-key construction for proof caching. WI-096.
//!
//! See `docs/proposals/025.1-z3-tactic-dsl.md` §"Cache key" for the
//! key composition rationale and the two-layer transitive-dep
//! guarantee. Property pinned by `tests/cache_key_test.rs`: a body or
//! fact change at any depth in the transitively-consulted set MUST
//! invalidate the cache key — no silent stale hits.

use std::collections::BTreeSet;

use anthill_core::intern::Symbol;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::node_occurrence::{for_each_child, Expr, NodeOccurrence};
use anthill_core::kb::term::Var;
use anthill_core::persistence::print::TermPrinter;
use sha2::{Digest, Sha256};

// v2 (WI-246): rule bodies are hashed from their occurrence form
// (`rule_body_nodes`) rather than the term body — a different byte stream, so
// pre-WI-246 cached keys must not false-hit.
pub const CACHE_FORMAT_VERSION: u32 = 2;

// ASCII control codes used as framing separators in the hash input
// stream. Naming makes the structure of `build_key` explicit.
const FIELD_SEP: u8 = 0x1e; // record separator (between top-level fields)
const ITEM_SEP: u8 = 0x1f;  // unit separator (between items within a list)
const GROUP_SEP: u8 = 0x1d; // group separator (between dep-set entries)

/// Inputs to the cache key. Order of fields matches order of
/// concatenation; do not reorder without bumping `CACHE_FORMAT_VERSION`.
pub struct KeyInputs<'a> {
    pub emitted_smt_lib: &'a str,
    pub tactic_canon: &'a str,
    pub hint_qns: &'a [String],
    pub visited_rules: &'a BTreeSet<String>,
    pub stdlib_version: &'a str,
    pub z3_version: &'a str,
}

/// Build the cache key as a 64-char lowercase-hex sha256 digest.
pub fn build_key(kb: &KnowledgeBase, inputs: &KeyInputs<'_>) -> String {
    let mut h = Sha256::new();

    field(&mut h, b"smt:", inputs.emitted_smt_lib.as_bytes());
    field(&mut h, b"tactic:", inputs.tactic_canon.as_bytes());

    h.update(b"hints:");
    for qn in inputs.hint_qns {
        h.update(qn.as_bytes());
        h.update([ITEM_SEP]);
    }
    h.update([FIELD_SEP]);

    let (rule_dep, referenced_functors) = walk_visited(kb, inputs.visited_rules);
    field(&mut h, b"rule_deps:", rule_dep.as_bytes());

    let fact_dep = fact_dep_hash_from(kb, &referenced_functors);
    field(&mut h, b"fact_deps:", fact_dep.as_bytes());

    field(&mut h, b"stdlib:", inputs.stdlib_version.as_bytes());
    field(&mut h, b"z3:", inputs.z3_version.as_bytes());

    h.update(b"cfv:");
    h.update(CACHE_FORMAT_VERSION.to_le_bytes());

    hex::encode(h.finalize())
}

/// Format version for `state_hash`. Bumping this invalidates every
/// recorded `ProofRecord.state_hash` — do so on changes to the input
/// envelope (label strings, framing bytes, included fields).
pub const STATE_HASH_FORMAT_VERSION: u32 = 2;

/// Per-`ProofRecord` state hash (proposal 030 phase α.4): canonical
/// hash of the kb-state slice a discharge depended on. Composed of
/// the same `walk_visited` + `fact_dep_hash_from` content as
/// `build_key`, but **without** the SMT-document, tactic, hint,
/// stdlib, or solver-version envelope. Two proofs that consult the
/// same rules + facts produce the same state hash regardless of
/// which tactic discharged them.
///
/// Returned as a 64-char lowercase-hex sha256 digest.
pub fn state_hash(kb: &KnowledgeBase, visited: &BTreeSet<String>) -> String {
    let mut h = Sha256::new();
    let (rule_dep, referenced_functors) = walk_visited(kb, visited);
    field(&mut h, b"rule_deps:", rule_dep.as_bytes());
    let fact_dep = fact_dep_hash_from(kb, &referenced_functors);
    field(&mut h, b"fact_deps:", fact_dep.as_bytes());
    h.update(b"shfv:");
    h.update(STATE_HASH_FORMAT_VERSION.to_le_bytes());
    hex::encode(h.finalize())
}

fn field(h: &mut Sha256, label: &[u8], value: &[u8]) {
    h.update(label);
    h.update(value);
    h.update([FIELD_SEP]);
}

/// Walk every transitively-visited rule. Per visited QN: append the
/// rule's head term + body-atom occurrences to the rule-content hasher AND
/// collect every functor referenced by any body atom. Returns the rolled-up
/// rule hash and the referenced-functor set (consumed by `fact_dep_hash_from`).
///
/// One pass over `visited` does both the rule_dep_hash content walk and
/// the fact_dep_hash functor collection. Functor set is keyed by
/// `Symbol::index()` (Symbol itself isn't Ord) — canonical sorted order
/// for hash stability.
fn walk_visited(
    kb: &KnowledgeBase,
    visited: &BTreeSet<String>,
) -> (String, BTreeSet<u32>) {
    let mut h = Sha256::new();
    let mut referenced: BTreeSet<u32> = BTreeSet::new();
    let printer = TermPrinter::new(kb);

    for qn in visited {
        h.update(qn.as_bytes());
        h.update([ITEM_SEP]);
        let Some(sym) = kb.try_resolve_symbol(qn) else {
            h.update([GROUP_SEP]);
            continue;
        };
        for rid in kb.by_functor(sym) {
            // Head stays a hash-consed term (searched in the discrim tree).
            let head = kb.rule_head(rid);
            h.update(printer.print_term(head).as_bytes());
            h.update([ITEM_SEP]);
            // Body atoms are occurrences (WI-246). Hash their structure and
            // collect referenced functors in one walk.
            for atom in kb.rule_body_nodes(rid) {
                hash_occurrence(kb, atom, &mut h, &mut referenced);
                h.update([ITEM_SEP]);
            }
            h.update([FIELD_SEP]);
        }
        h.update([GROUP_SEP]);
    }
    (hex::encode(h.finalize()), referenced)
}

fn fact_dep_hash_from(kb: &KnowledgeBase, referenced: &BTreeSet<u32>) -> String {
    let mut h = Sha256::new();
    let printer = TermPrinter::new(kb);
    for &raw in referenced {
        let functor = Symbol::from_raw(raw);
        h.update(kb.qualified_name_of(functor).as_bytes());
        h.update([ITEM_SEP]);
        for rid in kb.by_functor(functor) {
            if !kb.is_fact(rid) { continue; }
            let head = kb.rule_head(rid);
            h.update(printer.print_term(head).as_bytes());
            h.update([ITEM_SEP]);
        }
        h.update([GROUP_SEP]);
    }
    hex::encode(h.finalize())
}

/// Feed a rule-body-atom occurrence's structure into the rule-content hasher
/// and collect every functor it references — the occurrence twin of the former
/// term-based `collect_functors` (WI-246). Total over `Expr` (a conditional
/// rule's body element may be an `If` / `Let` / `Match` / requirement form, not
/// just an `Apply`): every node contributes a discriminant tag plus its
/// identifying content, and Fn-shaped nodes also contribute their functor to
/// the referenced set (which drives `fact_dep_hash_from`). The byte stream is
/// for cache invalidation only — stable + sensitive, not a human rendering.
fn hash_occurrence(
    kb: &KnowledgeBase,
    occ: &NodeOccurrence,
    h: &mut Sha256,
    out: &mut BTreeSet<u32>,
) {
    let Some(expr) = occ.as_expr() else {
        // Bodies are always `Expr`-kind; be total regardless.
        h.update(b"#");
        return;
    };
    match expr {
        // Fn-shaped: tag + functor QN, and contribute the functor.
        Expr::Apply { functor, .. } => fn_node(kb, b"A", *functor, h, out),
        Expr::ApplyWithin { functor, .. } => fn_node(kb, b"AW", *functor, h, out),
        Expr::Constructor { name, .. } => fn_node(kb, b"C", *name, h, out),
        Expr::ConstructorWithin { name, .. } => fn_node(kb, b"CW", *name, h, out),
        Expr::Instantiation { name, .. } => fn_node(kb, b"I", *name, h, out),
        Expr::ConstructRequirement { impl_functor, .. } => fn_node(kb, b"CR", *impl_functor, h, out),
        // Member/leaf symbols (not functors — don't feed `out`).
        Expr::DotApply { name, .. } => leaf_sym(kb, b"D", *name, h),
        Expr::VarRef { name } => leaf_sym(kb, b"VR", *name, h),
        Expr::Ref(s) => leaf_sym(kb, b"r", *s, h),
        Expr::Ident(s) => leaf_sym(kb, b"i", *s, h),
        Expr::Var(Var::DeBruijn(idx)) => { h.update(b"v"); h.update(idx.to_le_bytes()); }
        Expr::Var(other) => { h.update(b"v?"); h.update(format!("{other:?}").as_bytes()); }
        Expr::Const(lit) => { h.update(b"k"); h.update(format!("{lit:?}").as_bytes()); }
        Expr::RequirementAtSort { slot, .. } => { h.update(b"R"); h.update(slot.to_le_bytes()); }
        // Child-bearing control-flow / collection forms: a discriminant tag is
        // enough — the children are hashed by the recursion below.
        Expr::HoApply { .. } => h.update(b"H"),
        Expr::HoApplyWithin { .. } => h.update(b"HW"),
        Expr::Match { .. } => h.update(b"M"),
        Expr::If { .. } => h.update(b"F"),
        Expr::Let { .. } => h.update(b"L"),
        Expr::Lambda { .. } | Expr::LambdaWithin { .. } => h.update(b"Lam"),
        Expr::ListLit(_) => h.update(b"["),
        Expr::SetLit(_) => h.update(b"{"),
        Expr::TupleLit { .. } => h.update(b"("),
        Expr::Bottom => h.update(b"_"),
    }
    h.update([ITEM_SEP]);
    for_each_child(expr, |child| hash_occurrence(kb, child, h, out));
}

fn fn_node(kb: &KnowledgeBase, tag: &[u8], functor: Symbol, h: &mut Sha256, out: &mut BTreeSet<u32>) {
    h.update(tag);
    h.update(kb.qualified_name_of(functor).as_bytes());
    out.insert(functor.index());
}

fn leaf_sym(kb: &KnowledgeBase, tag: &[u8], sym: Symbol, h: &mut Sha256) {
    h.update(tag);
    h.update(kb.resolve_sym(sym).as_bytes());
}

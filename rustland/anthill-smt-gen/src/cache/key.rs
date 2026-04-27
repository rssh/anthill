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
use anthill_core::kb::term::{Term, TermId};
use anthill_core::persistence::print::TermPrinter;
use sha2::{Digest, Sha256};

pub const CACHE_FORMAT_VERSION: u32 = 1;

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

fn field(h: &mut Sha256, label: &[u8], value: &[u8]) {
    h.update(label);
    h.update(value);
    h.update([FIELD_SEP]);
}

/// Walk every transitively-visited rule. Per visited QN: append the
/// rule's head + body terms to the rule-content hasher AND collect every
/// functor referenced by any body term. Returns the rolled-up rule hash
/// and the referenced-functor set (consumed by `fact_dep_hash_from`).
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
            let head = kb.rule_head(rid);
            h.update(printer.print_term(head).as_bytes());
            h.update([ITEM_SEP]);
            for &body_t in kb.rule_body(rid) {
                h.update(printer.print_term(body_t).as_bytes());
                h.update([ITEM_SEP]);
                collect_functors(kb, body_t, &mut referenced);
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
            if !kb.rule_body(rid).is_empty() { continue; }
            let head = kb.rule_head(rid);
            h.update(printer.print_term(head).as_bytes());
            h.update([ITEM_SEP]);
        }
        h.update([GROUP_SEP]);
    }
    hex::encode(h.finalize())
}

fn collect_functors(kb: &KnowledgeBase, term: TermId, out: &mut BTreeSet<u32>) {
    if let Term::Fn { functor, pos_args, named_args } = kb.get_term(term) {
        out.insert(functor.index());
        for &arg in pos_args.iter() {
            collect_functors(kb, arg, out);
        }
        for &(_, arg) in named_args.iter() {
            collect_functors(kb, arg, out);
        }
    }
}

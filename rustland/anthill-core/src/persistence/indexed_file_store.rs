//! IndexedFileStore — `FileStore` augmented with a per-rule source map
//! so retract can drop the exact byte range a fact occupies on disk
//! without reconstructing it from a content fingerprint.
//!
//! The underlying `FileStore` keeps doing the actual file I/O — pull,
//! persist's append-to-pending, and flush's atomic rewrite all stay in
//! the inner store. `IndexedFileStore` adds:
//!
//! - `pull_with_source(&mut KnowledgeBase)` — load each `.anthill` file
//!   in the root, record `(rule_id → (path, span))` for every fact;
//! - `Store::retract` — consult the source map; if the rule was loaded
//!   from a file, buffer a span-based retract; otherwise fall back to
//!   the inner store's content-keyed retract for runtime-asserted
//!   facts.
//! - `flush` — apply span retracts (drop byte ranges directly), then
//!   delegate the rest to the inner store.
//!
//! Rationale: the legacy content-keyed retract path produces a
//! loader-normalized canonical (logical vars in unspecified named-args,
//! list-literal desugaring, constructor-arg expansion) that never
//! string-equals the parse-side print of the same fact in source. For
//! any entity with optional named-args (e.g. `WorkItem`) the retract
//! silently no-ops on disk. Span-based retract sidesteps the canonical
//! comparison entirely. (WI-187.)

use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;

use crate::kb::typing::get_named_arg;
use crate::kb::{KnowledgeBase, RuleId};
use crate::kb::term::{Literal, Term, TermId};
use crate::span::Span;

use super::file_store::{FileConvention, FileStore};
use super::{BulkStore, IndexedStore, PersistenceError, Store};

pub struct IndexedFileStore {
    inner: FileStore,
    /// Per-rule source location: which file the rule was loaded from
    /// and the byte range its `fact …(…)` block occupies. Populated by
    /// `pull_with_source`; consulted by `retract`.
    source_map: HashMap<RuleId, (PathBuf, Span)>,
    /// Span retracts queued for the next flush. `(file, byte_range)`
    /// tuples — flush drops the range from the file.
    pending_span_retracts: Vec<(PathBuf, Span)>,
    /// Primary-key index: maps the value of a fact's `id` field (when
    /// String-typed) to its `RuleId`. v0.1 convention: every entity
    /// stored in an `IndexedFileStore` is expected to carry a `String`
    /// `id` field; missing or non-String id → not indexed (the rule
    /// stays in `source_map` for retract). `retrieve(pattern)` uses
    /// this index for O(1) lookup when the pattern has `id` bound to
    /// a String literal; falls back to O(N) scan-and-unify otherwise.
    by_id: HashMap<String, RuleId>,
}

impl IndexedFileStore {
    pub fn new(root: PathBuf, convention: FileConvention) -> Self {
        Self {
            inner: FileStore::new(root, convention),
            source_map: HashMap::new(),
            pending_span_retracts: Vec::new(),
            by_id: HashMap::new(),
        }
    }

    /// Record source location for a single fact. Callers that drove
    /// their own load path (e.g. the bundle's main.rs which loads
    /// stdlib + bundle + project together via `load_all_per_file`)
    /// populate the source map fact-by-fact without re-parsing.
    pub fn record_source(&mut self, rule_id: RuleId, path: PathBuf, span: Span) {
        self.source_map.insert(rule_id, (path, span));
    }

    /// Populate the primary-key index for a rule. The host calls this
    /// after `record_source` for each pulled fact; if the rule's head
    /// has a String-typed `id` field, the entry `by_id[id_str] = rule_id`
    /// is added. Facts without an `id` field are skipped silently —
    /// they remain unindexable but still retract-tracked via `source_map`.
    pub fn index_by_id(&mut self, rule_id: RuleId, kb: &KnowledgeBase) {
        if let Some(id_str) = extract_string_id(kb, kb.rule_head(rule_id)) {
            self.by_id.insert(id_str, rule_id);
        }
    }
}

/// Read a String-typed `id` named argument from a term. Returns the
/// value if present and the field is a String literal.
fn extract_string_id(kb: &KnowledgeBase, term_id: TermId) -> Option<String> {
    let Term::Fn { named_args, .. } = kb.get_term(term_id) else { return None };
    let val = get_named_arg(kb, named_args, "id")?;
    if let Term::Const(Literal::String(s)) = kb.get_term(val) {
        return Some(s.clone());
    }
    None
}

impl IndexedStore for IndexedFileStore {
    type Location = (PathBuf, Span);

    fn location_of(&self, id: RuleId) -> Option<Self::Location> {
        self.source_map.get(&id).cloned()
    }
}

impl Store for IndexedFileStore {
    fn persist(
        &mut self,
        kb: &KnowledgeBase,
        fact: TermId,
        sort: TermId,
        domain: TermId,
        meta: Option<TermId>,
    ) -> Result<(), PersistenceError> {
        // by_id population for runtime-persisted facts happens in the
        // persist builtin, which has the freshly-allocated RuleId
        // (eval/builtins.rs persistence_persist calls index_by_id).
        self.inner.persist(kb, fact, sort, domain, meta)
    }

    fn retract(&mut self, kb: &KnowledgeBase, id: RuleId) -> Result<bool, PersistenceError> {
        if !kb.is_rule_alive(id) {
            return Ok(false);
        }
        if let Some(id_str) = extract_string_id(kb, kb.rule_head(id)) {
            self.by_id.remove(&id_str);
        }
        match self.source_map.remove(&id) {
            Some((path, span)) => {
                self.pending_span_retracts.push((path, span));
                Ok(true)
            }
            // Runtime-asserted fact (no source) — fall through to the
            // inner store's content-keyed retract.
            None => self.inner.retract(kb, id),
        }
    }

    fn retrieve(
        &self,
        kb: &KnowledgeBase,
        pattern: TermId,
    ) -> Result<Vec<TermId>, PersistenceError> {
        // Fast path: pattern has `id` bound; look up via by_id, verify
        // the rest of the pattern matches the fact head.
        if let Some(id_str) = extract_string_id(kb, pattern) {
            if let Some(&rule_id) = self.by_id.get(&id_str) {
                if kb.is_rule_alive(rule_id) {
                    let head = kb.rule_head(rule_id);
                    if pattern_matches(kb, pattern, head) {
                        return Ok(vec![head]);
                    }
                }
            }
            return Ok(Vec::new());
        }

        // Slow path: walk by_functor (already retract-filtered),
        // pattern-match each candidate. Multi-store disambiguation is
        // out of v0.1 scope.
        let Term::Fn { functor, .. } = kb.get_term(pattern) else {
            return Ok(Vec::new());
        };
        let functor = *functor;
        Ok(kb.by_functor(functor)
            .into_iter()
            .map(|rid| kb.rule_head(rid))
            .filter(|head| pattern_matches(kb, pattern, *head))
            .collect())
    }

    fn flush(&mut self, kb: &KnowledgeBase) -> Result<(), PersistenceError> {
        // Span retracts first: drop byte ranges from each file.
        // Group by path so we can apply all retracts to a file in one
        // rewrite, then sort within each file by descending start so
        // earlier drops don't shift the offsets of later ones.
        if !self.pending_span_retracts.is_empty() {
            let mut by_path: HashMap<PathBuf, Vec<Span>> = HashMap::new();
            for (path, span) in self.pending_span_retracts.drain(..) {
                by_path.entry(path).or_default().push(span);
            }
            for (path, mut spans) in by_path {
                let source = fs::read_to_string(&path).map_err(|e| {
                    PersistenceError::Io(format!("read {}: {e}", path.display()))
                })?;
                spans.sort_by(|a, b| b.start.cmp(&a.start));
                let mut content = source;
                for span in spans {
                    drop_range(&mut content, span.start as usize, span.end as usize);
                }
                let temp_path = path.with_extension("anthill.tmp");
                fs::write(&temp_path, &content).map_err(|e| {
                    PersistenceError::Io(format!(
                        "write {}: {e}", temp_path.display()
                    ))
                })?;
                fs::rename(&temp_path, &path).map_err(|e| {
                    PersistenceError::Io(format!(
                        "rename {} → {}: {e}",
                        temp_path.display(), path.display(),
                    ))
                })?;
            }
        }
        // Inner flush handles persisted writes and any content-keyed
        // retracts that fell through (runtime-asserted facts).
        self.inner.flush(kb)
    }
}

impl BulkStore for IndexedFileStore {
    fn pull(&self) -> Result<Vec<crate::parse::ir::ParsedFile>, PersistenceError> {
        self.inner.pull()
    }
}

/// Subset pattern match: `fact` satisfies `pattern` iff for every
/// constraint expressed in pattern, the fact has a matching subterm.
/// Pattern variables match anything; the fact may have extra named
/// args the pattern doesn't mention. (kb.match_term doesn't fit
/// because the resolver's discrim tree expects full-shape matching
/// against rule heads, not the partial-pattern semantics retrieve
/// needs for queries like `WorkItem(id: x)` against a fact that also
/// carries `status` and other fields.)
fn pattern_matches(kb: &KnowledgeBase, pattern: TermId, fact: TermId) -> bool {
    match (kb.get_term(pattern), kb.get_term(fact)) {
        (Term::Var(_), _) => true,
        (Term::Const(pc), Term::Const(fc)) => pc == fc,
        (Term::Ref(ps), Term::Ref(fs)) => ps == fs,
        (Term::Ident(ps), Term::Ident(fs)) => ps == fs,
        (
            Term::Fn { functor: pf, pos_args: pp, named_args: pn },
            Term::Fn { functor: ff, pos_args: fp, named_args: fn_args },
        ) => {
            if pf != ff || pp.len() != fp.len() {
                return false;
            }
            if !pp.iter().zip(fp.iter()).all(|(a, b)| pattern_matches(kb, *a, *b)) {
                return false;
            }
            pn.iter().all(|&(p_name, p_val)| {
                fn_args.iter()
                    .find(|(n, _)| *n == p_name)
                    .is_some_and(|(_, fv)| pattern_matches(kb, p_val, *fv))
            })
        }
        _ => false,
    }
}

fn drop_range(content: &mut String, start: usize, end: usize) {
    let drop_end = super::extend_drop_end(content.as_bytes(), end);
    content.replace_range(start..drop_end, "");
}

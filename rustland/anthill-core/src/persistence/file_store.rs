/// FileStore — filesystem persistence backend.
///
/// Reads/writes `.anthill` files. Implements `BulkStore`:
/// - `persist()` buffers facts as text
/// - `retract()` buffers a canonical-printed-form for the rule's head
/// - `flush()` rewrites affected files (drop matching fact blocks, then
///   append persisted texts) atomically via temp + rename
/// - `pull()` reads all `.anthill` files under the root directory
///
/// Retract semantics: a fact in the source file is matched by the
/// canonical printed form of its head term (`TermPrinter::print_term`).
/// Inter-fact text — comments, blank lines, anything outside a
/// `fact …(…)` block — is preserved across rewrites. Comments inside a
/// fact block are not preserved (the block is treated as a single unit).

use std::collections::HashMap;
use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};

use crate::kb::{RuleId, KnowledgeBase};
use crate::kb::term::TermId;
use crate::parse;
use crate::parse::ir::Item;

use super::print;
use super::{BulkStore, PersistenceError, Store};

// ── File naming convention ─────────────────────────────────────

/// How facts map to file paths.
#[derive(Clone, Debug)]
pub enum FileConvention {
    /// All facts go to a single `facts.anthill` file.
    Flat,
    /// Facts are grouped by their domain name: `<domain>.anthill`.
    ByDomain,
}

// ── Pending operations ─────────────────────────────────────────

struct PendingWrite {
    path: PathBuf,
    text: String,
}

struct PendingRetract {
    path: PathBuf,
    /// Canonical printed form of the rule's head term, captured at
    /// retract-buffer time before the caller retracts the rule from the
    /// KB. Compared to the canonical printed form of every parsed fact
    /// in the target file at flush time.
    head_canonical: String,
}

// ── FileStore ──────────────────────────────────────────────────

pub struct FileStore {
    root: PathBuf,
    convention: FileConvention,
    pending_writes: Vec<PendingWrite>,
    pending_retracts: Vec<PendingRetract>,
}

impl FileStore {
    pub fn new(root: PathBuf, convention: FileConvention) -> Self {
        Self {
            root,
            convention,
            pending_writes: Vec::new(),
            pending_retracts: Vec::new(),
        }
    }

    /// Determine the file path for a fact based on convention.
    fn fact_path(&self, kb: &KnowledgeBase, _sort: TermId, domain: TermId) -> PathBuf {
        match &self.convention {
            FileConvention::Flat => self.root.join("facts.anthill"),
            FileConvention::ByDomain => {
                let printer = print::TermPrinter::new(kb);
                let domain_name = printer.print_term(domain);
                // Sanitize: replace dots with path separators, strip non-alphanum
                let sanitized: String = domain_name
                    .chars()
                    .map(|c| if c == '.' { '/' } else if c.is_alphanumeric() || c == '_' { c } else { '_' })
                    .collect();
                self.root.join(format!("{sanitized}.anthill"))
            }
        }
    }

    /// Public root accessor for `IndexedFileStore` (sibling type) so it
    /// can drive its own `pull_with_source` over the same directory
    /// without re-parsing the FileStore's internals.
    pub fn root_path(&self) -> &Path {
        &self.root
    }

    /// Public wrapper around `collect_anthill_files` so wrapper stores
    /// (e.g. `IndexedFileStore`) can enumerate the same set of files.
    pub fn collect_anthill_files_pub(dir: &Path) -> Result<Vec<PathBuf>, PersistenceError> {
        Self::collect_anthill_files(dir)
    }

    /// Recursively collect all `.anthill` files under a directory.
    fn collect_anthill_files(dir: &Path) -> Result<Vec<PathBuf>, PersistenceError> {
        let mut files = Vec::new();
        if !dir.exists() {
            return Ok(files);
        }
        Self::collect_recursive(dir, &mut files)?;
        files.sort();
        Ok(files)
    }

    fn collect_recursive(dir: &Path, files: &mut Vec<PathBuf>) -> Result<(), PersistenceError> {
        let entries = fs::read_dir(dir).map_err(|e| {
            PersistenceError::Io(format!("failed to read directory {}: {e}", dir.display()))
        })?;
        for entry in entries {
            let entry = entry.map_err(|e| {
                PersistenceError::Io(format!("failed to read dir entry: {e}"))
            })?;
            let path = entry.path();
            if path.is_dir() {
                Self::collect_recursive(&path, files)?;
            } else if path.extension().is_some_and(|e| e == "anthill") {
                files.push(path);
            }
        }
        Ok(())
    }
}

impl Store for FileStore {
    fn persist(
        &mut self,
        kb: &KnowledgeBase,
        fact: TermId,
        sort: TermId,
        domain: TermId,
        meta: Option<TermId>,
    ) -> Result<(), PersistenceError> {
        let path = self.fact_path(kb, sort, domain);
        let text = print::print_fact(kb, fact, meta);
        self.pending_writes.push(PendingWrite { path, text });
        Ok(())
    }

    fn retract(&mut self, kb: &KnowledgeBase, id: RuleId) -> Result<bool, PersistenceError> {
        if !kb.is_rule_alive(id) {
            return Ok(false);
        }
        let head = kb.rule_head(id);
        let sort = kb.rule_sort(id);
        let domain = kb.rule_domain(id);
        let path = self.fact_path(kb, sort, domain);
        let head_canonical = print::TermPrinter::new(kb).print_term(head);
        self.pending_retracts.push(PendingRetract { path, head_canonical });
        Ok(true)
    }

    fn flush(&mut self, _kb: &KnowledgeBase) -> Result<(), PersistenceError> {
        // Group pending operations by path. Retracts apply first; persists
        // append after.
        let mut writes_by_path: HashMap<PathBuf, Vec<String>> = HashMap::new();
        for pw in self.pending_writes.drain(..) {
            writes_by_path.entry(pw.path).or_default().push(pw.text);
        }
        let mut retracts_by_path: HashMap<PathBuf, HashSet<String>> = HashMap::new();
        for pr in self.pending_retracts.drain(..) {
            retracts_by_path.entry(pr.path).or_default().insert(pr.head_canonical);
        }

        // Union of affected paths.
        let mut affected: HashSet<&PathBuf> = HashSet::new();
        for p in writes_by_path.keys() {
            affected.insert(p);
        }
        for p in retracts_by_path.keys() {
            affected.insert(p);
        }
        let affected: Vec<PathBuf> = affected.into_iter().cloned().collect();

        for path in affected {
            // Ensure parent directory exists.
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).map_err(|e| {
                    PersistenceError::Io(format!(
                        "failed to create directory {}: {e}",
                        parent.display()
                    ))
                })?;
            }

            let existing = if path.exists() {
                fs::read_to_string(&path).map_err(|e| {
                    PersistenceError::Io(format!(
                        "failed to read {}: {e}",
                        path.display()
                    ))
                })?
            } else {
                String::new()
            };

            // Apply retracts: parse the source, drop fact blocks whose head
            // matches a retract canonical, preserve everything else.
            let after_retract = match retracts_by_path.get(&path) {
                Some(retracts) if !retracts.is_empty() => {
                    apply_retracts(&existing, retracts)?
                }
                _ => existing,
            };

            // Append newly persisted facts (current behaviour).
            let mut content = after_retract;
            if let Some(writes) = writes_by_path.get(&path) {
                for text in writes {
                    content.push_str(text);
                }
            }

            // Atomic write: temp file + rename.
            let temp_path = path.with_extension("anthill.tmp");
            fs::write(&temp_path, &content).map_err(|e| {
                PersistenceError::Io(format!(
                    "failed to write temp file {}: {e}",
                    temp_path.display()
                ))
            })?;
            fs::rename(&temp_path, &path).map_err(|e| {
                PersistenceError::Io(format!(
                    "failed to rename {} → {}: {e}",
                    temp_path.display(),
                    path.display()
                ))
            })?;
        }

        Ok(())
    }
}

impl BulkStore for FileStore {
    fn pull(&self) -> Result<Vec<crate::parse::ir::ParsedFile>, PersistenceError> {
        let files = Self::collect_anthill_files(&self.root)?;
        let mut parsed_files = Vec::new();

        for path in files {
            let source = fs::read_to_string(&path).map_err(|e| {
                PersistenceError::Io(format!("failed to read {}: {e}", path.display()))
            })?;
            let parsed = parse::parse(&source).map_err(PersistenceError::Parse)?;
            parsed_files.push(parsed);
        }

        Ok(parsed_files)
    }
}

// ── Retract application ────────────────────────────────────────

/// Parse `source`, identify each `fact …(…)` block whose head term
/// canonicalizes to a string in `retracts`, and rebuild the source
/// without those blocks. Inter-fact text (comments, blank lines, other
/// items) is preserved verbatim.
///
/// If multiple in-source facts share the same head canonical, all of
/// them are removed (a retract canonical is a *content* identifier, and
/// duplicates on disk mean the user already has a problem).
fn apply_retracts(source: &str, retracts: &HashSet<String>) -> Result<String, PersistenceError> {
    let parsed = parse::parse(source).map_err(PersistenceError::Parse)?;

    let mut drop_ranges: Vec<(usize, usize)> = Vec::new();
    let printer = print::TermPrinter::over(&parsed);

    for item in &parsed.items {
        let Item::Fact(fact) = item else { continue };
        let head_canonical = printer.print_term(fact.term);
        if retracts.contains(&head_canonical) {
            drop_ranges.push((fact.span.start as usize, fact.span.end as usize));
        }
    }

    if drop_ranges.is_empty() {
        return Ok(source.to_string());
    }

    drop_ranges.sort_by_key(|(s, _)| *s);

    // Rebuild source by concatenating the regions between drop ranges,
    // then collapse leftover blank-line clusters where a fact was removed
    // so the output doesn't accumulate growing blank gaps across repeated
    // retract cycles.
    let mut rebuilt = String::with_capacity(source.len());
    let mut cursor = 0;
    for (start, end) in &drop_ranges {
        // Extend the range to swallow the trailing newline (and one
        // following blank line if present), so removing a fact that's
        // separated from its successor by a blank line doesn't leave two
        // blanks in a row.
        let mut drop_end = *end;
        let bytes = source.as_bytes();
        if drop_end < bytes.len() && bytes[drop_end] == b'\n' {
            drop_end += 1;
        }
        if drop_end < bytes.len() && bytes[drop_end] == b'\n' {
            drop_end += 1;
        }
        rebuilt.push_str(&source[cursor..*start]);
        cursor = drop_end;
    }
    rebuilt.push_str(&source[cursor..]);
    Ok(rebuilt)
}

/// FileStore — filesystem persistence backend.
///
/// Reads/writes `.anthill` files. Implements `BulkStore`:
/// - `persist()` buffers facts as text
/// - `flush()` writes buffered text to files (atomic: temp + rename)
/// - `pull()` reads all `.anthill` files under the root directory

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

use crate::kb::{RuleId, KnowledgeBase};
use crate::kb::term::TermId;
use crate::parse;

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

// ── Pending write ──────────────────────────────────────────────

struct PendingWrite {
    path: PathBuf,
    text: String,
}

// ── FileStore ──────────────────────────────────────────────────

pub struct FileStore {
    root: PathBuf,
    convention: FileConvention,
    pending_writes: Vec<PendingWrite>,
    pending_retracts: Vec<RuleId>,
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

    fn retract(&mut self, id: RuleId) -> Result<bool, PersistenceError> {
        // Stage 0: record the retraction but don't modify files.
        // File modification on retract is deferred to a future stage.
        self.pending_retracts.push(id);
        Ok(true)
    }

    fn flush(&mut self, _kb: &KnowledgeBase) -> Result<(), PersistenceError> {
        // Group pending writes by path
        let mut by_path: HashMap<PathBuf, Vec<String>> = HashMap::new();
        for pw in self.pending_writes.drain(..) {
            by_path.entry(pw.path).or_default().push(pw.text);
        }

        // Write each file atomically (temp file + rename)
        for (path, texts) in by_path {
            // Ensure parent directory exists
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).map_err(|e| {
                    PersistenceError::Io(format!(
                        "failed to create directory {}: {e}",
                        parent.display()
                    ))
                })?;
            }

            // Build content: read existing file (if any) and append new facts
            let mut content = if path.exists() {
                fs::read_to_string(&path).map_err(|e| {
                    PersistenceError::Io(format!(
                        "failed to read {}: {e}",
                        path.display()
                    ))
                })?
            } else {
                String::new()
            };

            for text in texts {
                content.push_str(&text);
            }

            // Write atomically: temp file + rename
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

        // Clear pending retracts (stage 0: no file modification)
        self.pending_retracts.clear();

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

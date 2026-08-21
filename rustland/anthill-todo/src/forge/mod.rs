//! The `Forge` carrier: the host half of the mirror (WI-1117).
//!
//! Design: `docs/design/backend-github-coordination.md` §7 (amended), §8.3.
//!
//! ONE HOST FUNCTION PER OPERATION, resolving the RECEIVER to a backend — the
//! same shape `anthill.persistence`'s six storage operations already use, and
//! for the same reason: `create_entry` on a `GithubForge` and on a `FakeForge`
//! differ in the backend, not in the signature, so mapping them per carrier
//! would copy five signatures per target to say the same thing twice. Which
//! targets this host realizes at all is the separate question, and
//! `coordination.anthill`'s one-line `provides GithubForge` / `provides
//! FakeForge` blocks answer it.
//!
//! REGISTERED BY THE EMBEDDER, THROUGH THE WI-1122 SEAM. `HOST_FNS` in
//! anthill-core is a closed `const` slice that knows nothing about forges;
//! putting the `gh` shell-out there would make the kernel learn about them.
//! [`register`] therefore runs BEFORE `load_all` — load itself builds
//! interpreters, and a table registered later is refused by the seal.

use std::path::{Path, PathBuf};

use anthill_core::eval::{value_functor, EvalError, Interpreter, Value};
use anthill_core::kb::KnowledgeBase;

mod fake;
mod gh;

/// What an export target must be able to do (design §8.3, narrowed by the §7
/// amendment). Five operations: name yourself, create an entry, overwrite one,
/// list what you hold, and read one entry's comments back.
///
/// `String` errors rather than a typed enum: every one of them reaches anthill
/// as the payload of the `Error` effect the operations declare, so the only
/// thing a caller does with it is print it.
trait ForgeBackend {
    /// The target's own name for itself, as `MirrorEntry.target` records it.
    /// It must distinguish two targets of the SAME kind — two GitHub repos are
    /// two targets — or export would adopt one's entries into the other's links.
    fn target_name(&self) -> String;

    fn create_entry(&self, title: &str, body: &str) -> Result<String, String>;

    fn update_entry(&self, entry: &str, title: &str, body: &str) -> Result<(), String>;

    fn list_entries(&self) -> Result<Vec<Entry>, String>;

    fn entry_comments(&self, entry: &str) -> Result<Vec<Comment>, String>;
}

/// One entry as a target reports it. `entry` is the same opaque handle
/// `MirrorEntry.entry` holds — the two must be the same spelling, or an adopted
/// entry and a created one would not compare equal.
#[derive(Debug)]
pub(crate) struct Entry {
    pub entry: String,
    pub title: String,
}

/// One comment as a target reports it. `(author, at)` is what ingestion dedups
/// on, so both must be stable across reads (§8.3's contract item 4).
#[derive(Debug)]
pub(crate) struct Comment {
    pub author: String,
    pub at: String,
    pub body: String,
}

/// Register the five host functions the `Forge` binding block names.
///
/// MUST RUN BEFORE `load_all` — enforced, not documented: the seam seals its
/// registry when the loader builds its mapping cache, and a later registration
/// is refused (WI-1122).
///
/// `config_dir` is CAPTURED rather than passed, which is why these are closures
/// and not bare `fn`s: `FakeForge(dir:)` is written relative to the project, the
/// same as `ExtentBinding`'s `root`, and a config file has no business naming an
/// absolute path. A bare `fn` pointer captures nothing, and would force this
/// into a `static`.
pub fn register(kb: &mut KnowledgeBase, config_dir: &Path) -> Result<(), String> {
    let entries: [(&'static str, usize, HostFn); 5] = [
        ("forge_target_name", 1, host_target_name),
        ("forge_create_entry", 3, host_create_entry),
        ("forge_update_entry", 4, host_update_entry),
        ("forge_list_entries", 1, host_list_entries),
        ("forge_entry_comments", 2, host_entry_comments),
    ];
    for (key, arity, f) in entries {
        let root = config_dir.to_path_buf();
        kb.register_host_fn(key, arity, move |interp: &mut Interpreter, args: &[Value]| {
            f(&root, interp, args)
        })
        .map_err(|e| format!("registering the forge host functions: {e}"))?;
    }
    Ok(())
}

type HostFn = fn(&Path, &mut Interpreter, &[Value]) -> Result<Value, EvalError>;

// ── The receiver → backend resolution ────────────────────────────

/// The backend the receiver VALUE names.
///
/// BY RESOLVED SYMBOL, never by name text — the same rule, and for the same
/// measured reason, as `resolve_backend` for stores: an `ends_with` test read
/// naturally and accepted a `GitHubForge` defined nowhere, so a project asking
/// for a target this build does not have got a silent write instead of a
/// refusal.
fn backend_of(
    interp: &Interpreter,
    root: &Path,
    receiver: &Value,
) -> Result<Box<dyn ForgeBackend>, EvalError> {
    let functor = value_functor(interp.kb(), receiver)
        .ok_or_else(|| raised("the mirror target names no forge".to_string()))?;
    let name = interp.kb().qualified_name_of(functor);
    match name {
        GITHUB_FORGE => Ok(Box::new(gh::Gh {
            repo: string_field(interp, receiver, "repo")?,
        })),
        FAKE_FORGE => {
            let declared = string_field(interp, receiver, "dir")?;
            Ok(Box::new(fake::Fake {
                dir: resolve_dir(root, &declared),
                declared,
            }))
        }
        other => Err(raised(format!(
            "`{other}` is not a mirror target this build provides. This binary realizes \
             `{GITHUB_FORGE}` and `{FAKE_FORGE}`; a target it does not have is a refusal, \
             not a fallback — declarative configuration chooses AMONG a host's \
             implementations and cannot introduce native code."
        ))),
    }
}

const GITHUB_FORGE: &str = "anthill.stage0.GithubForge";
const FAKE_FORGE: &str = "anthill.stage0.FakeForge";

/// A declared directory against the directory the project's configuration lives
/// in — the same anchor `ExtentBinding`'s `root: "."` resolves against, so the
/// two relative paths in one config file mean the same thing. An absolute one is
/// taken as written, so a test outside the tree can still name a place.
fn resolve_dir(root: &Path, dir: &str) -> PathBuf {
    let p = Path::new(dir);
    if p.is_absolute() {
        p.to_path_buf()
    } else {
        root.join(p)
    }
}

/// A `String`-valued field of the target term, in either carrier a declaration
/// can arrive in: a host-built `Value::Str` or the hash-consed literal a
/// source-written fact carries.
fn string_field(interp: &Interpreter, value: &Value, field: &str) -> Result<String, EvalError> {
    use anthill_core::kb::term::{Literal, Term, TermSource};
    let found = interp
        .kb()
        .row_field(value, field)
        .ok_or_else(|| raised(format!("the mirror target carries no `{field}`")))?;
    match found {
        Value::Str(s) => Ok(s),
        Value::Term { id, .. } => match interp.kb().term(id) {
            Term::Const(Literal::String(s)) => Ok(s.clone()),
            other => Err(raised(format!(
                "the mirror target's `{field}` must be a string, got {other:?}"
            ))),
        },
        other => Err(raised(format!(
            "the mirror target's `{field}` must be a string, got {other:?}"
        ))),
    }
}

/// An entry handle, checked before it reaches a filesystem path or an argv slot.
///
/// THE HANDLE IS DATA FROM THE TREE. It arrives from a `MirrorEntry` row — a
/// `- mirrors:` line anyone can hand-edit or a merge can mangle — or from a
/// target's own listing, so it is not this program's own string. The fake joins
/// it into a path (`<dir>/<entry>.entry`), where `../../evil` writes outside the
/// mirror directory; `gh` takes it as a positional argv token, where a leading
/// `-` is read as a flag. One rule covers both, and it is not a narrowing worth
/// worrying about: an external id that is not `[A-Za-z0-9._-]+` does not exist on
/// any target this build talks to.
fn checked_handle(entry: &str) -> Result<&str, String> {
    let ok = !entry.is_empty()
        && !entry.starts_with('-')
        && entry
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '-'))
        && entry != "."
        && entry != "..";
    if ok {
        Ok(entry)
    } else {
        Err(format!(
            "`{entry}` is not a usable entry handle. A link's entry reaches a file path and a \
             command line, so it must be a plain identifier — letters, digits, `.`, `_` and \
             `-`, not starting with `-`. Fix the `- mirrors:` line of the item that names it."
        ))
    }
}

/// A failure on the `Error` effect channel the `Forge` operations declare. It
/// reaches the user as `error: <message>` through `exit_code_from_main`, which
/// is what every one of these is for.
fn raised(message: String) -> EvalError {
    EvalError::Raised {
        payload: Value::Str(message),
    }
}

// ── The five host functions ──────────────────────────────────────

fn host_target_name(
    root: &Path,
    interp: &mut Interpreter,
    args: &[Value],
) -> Result<Value, EvalError> {
    let [f] = expect::<1>("Forge.target_name", args)?;
    Ok(Value::Str(backend_of(interp, root, &f)?.target_name()))
}

fn host_create_entry(
    root: &Path,
    interp: &mut Interpreter,
    args: &[Value],
) -> Result<Value, EvalError> {
    let [f, title, body] = expect::<3>("Forge.create_entry", args)?;
    let entry = backend_of(interp, root, &f)?
        .create_entry(&str_arg(&title, "title")?, &str_arg(&body, "body")?)
        .map_err(raised)?;
    Ok(Value::Str(entry))
}

fn host_update_entry(
    root: &Path,
    interp: &mut Interpreter,
    args: &[Value],
) -> Result<Value, EvalError> {
    let [f, entry, title, body] = expect::<4>("Forge.update_entry", args)?;
    let entry = str_arg(&entry, "entry")?;
    backend_of(interp, root, &f)?
        .update_entry(
            checked_handle(&entry).map_err(raised)?,
            &str_arg(&title, "title")?,
            &str_arg(&body, "body")?,
        )
        .map_err(raised)?;
    unit(interp)
}

fn host_list_entries(
    root: &Path,
    interp: &mut Interpreter,
    args: &[Value],
) -> Result<Value, EvalError> {
    let [f] = expect::<1>("Forge.list_entries", args)?;
    let entries = backend_of(interp, root, &f)?.list_entries().map_err(raised)?;
    // A LISTING IS EXTERNAL TOO, so its handles are checked on the way in rather
    // than on the way back out: an adopted entry's handle is written into the
    // tree and then addressed on every later run.
    for e in &entries {
        checked_handle(&e.entry).map_err(raised)?;
    }
    let values: Vec<Value> = entries
        .into_iter()
        .map(|e| {
            entity(
                interp,
                "anthill.stage0.ForgeEntry",
                &[("entry", Value::Str(e.entry)), ("title", Value::Str(e.title))],
            )
        })
        .collect::<Result<_, _>>()?;
    value_list(interp, values)
}

fn host_entry_comments(
    root: &Path,
    interp: &mut Interpreter,
    args: &[Value],
) -> Result<Value, EvalError> {
    let [f, entry] = expect::<2>("Forge.entry_comments", args)?;
    let entry = str_arg(&entry, "entry")?;
    let comments = backend_of(interp, root, &f)?
        .entry_comments(checked_handle(&entry).map_err(raised)?)
        .map_err(raised)?;
    let values: Vec<Value> = comments
        .into_iter()
        .map(|c| {
            entity(
                interp,
                "anthill.stage0.ForgeComment",
                &[
                    ("author", Value::Str(c.author)),
                    ("at", Value::Str(c.at)),
                    ("body", Value::Str(c.body)),
                ],
            )
        })
        .collect::<Result<_, _>>()?;
    value_list(interp, values)
}

// ── Argument and result plumbing ─────────────────────────────────

/// The operands, at the arity the binding block declared. A disagreement is
/// caught at interpreter build (WI-876/WI-1122), so reaching this is a runtime
/// invariant violation rather than a user-facing condition — but it is still
/// surfaced rather than assumed away, because an EMBEDDER's declared arity is on
/// trust: nothing can introspect a Rust function's expected argument count.
fn expect<const N: usize>(op: &'static str, args: &[Value]) -> Result<[Value; N], EvalError> {
    <[Value; N]>::try_from(args.to_vec()).map_err(|_| EvalError::ArityMismatch {
        op,
        expected: N,
        got: args.len(),
    })
}

fn str_arg(v: &Value, what: &str) -> Result<String, EvalError> {
    match v {
        Value::Str(s) => Ok(s.clone()),
        other => Err(raised(format!(
            "`{what}` must be a string, got {other:?}"
        ))),
    }
}

fn entity(
    interp: &mut Interpreter,
    qualified: &str,
    fields: &[(&str, Value)],
) -> Result<Value, EvalError> {
    let functor = interp.kb().try_resolve_symbol(qualified).ok_or_else(|| {
        raised(format!(
            "`{qualified}` does not resolve — the bundled mirror domain is not loaded"
        ))
    })?;
    let named: Vec<_> = fields
        .iter()
        .map(|(name, value)| (interp.kb_mut().intern(name), value.clone()))
        .collect();
    Ok(Value::Entity {
        functor,
        pos: Vec::new().into(),
        named: named.into(),
    })
}

fn value_list(interp: &mut Interpreter, elems: Vec<Value>) -> Result<Value, EvalError> {
    let cons = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.List.cons")
        .ok_or_else(|| raised("`anthill.prelude.List.cons` does not resolve".to_string()))?;
    let nil = interp
        .kb()
        .try_resolve_symbol("anthill.prelude.List.nil")
        .ok_or_else(|| raised("`anthill.prelude.List.nil` does not resolve".to_string()))?;
    let head = interp.kb_mut().intern("head");
    let tail = interp.kb_mut().intern("tail");
    let mut list = Value::Entity {
        functor: nil,
        pos: Vec::new().into(),
        named: Vec::new().into(),
    };
    for elem in elems.into_iter().rev() {
        list = Value::Entity {
            functor: cons,
            pos: Vec::new().into(),
            named: vec![(head, elem), (tail, list)].into(),
        };
    }
    Ok(list)
}

/// `Value::Unit`, the same carrier `Cell.set` answers a `-> Unit` operation with.
fn unit(_interp: &mut Interpreter) -> Result<Value, EvalError> {
    Ok(Value::Unit)
}

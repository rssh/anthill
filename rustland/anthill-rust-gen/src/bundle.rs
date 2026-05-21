//! `rust+anthill` bundle generator. Emits a self-contained Rust crate
//! whose `main()` parses the embedded anthill spec into a KB and
//! dispatches the named entry-point operation through the interpreter.
//!
//! The output is a runnable cargo project with this layout:
//!
//! ```text
//! <output>/
//!   Cargo.toml
//!   src/main.rs
//!   spec/                 — verbatim copies of the bundled anthill files
//!     stdlib/anthill/...  — every stdlib file
//!     user/...            — user-supplied program sources
//! ```
//!
//! All anthill files are vendored into `spec/` and baked in via
//! `include_str!`, so the resulting binary needs no `.anthill` files
//! at runtime.

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

#[derive(Debug)]
pub enum BundleError {
    Io(io::Error, PathBuf),
    StdlibNotFound(PathBuf),
    NoSources,
}

impl std::fmt::Display for BundleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BundleError::Io(e, p) => write!(f, "io error at {}: {e}", p.display()),
            BundleError::StdlibNotFound(p) => write!(f, "stdlib directory not found at {}", p.display()),
            BundleError::NoSources => write!(f, "no user sources to bundle"),
        }
    }
}
impl std::error::Error for BundleError {}

/// How the generated `Cargo.toml` should reference `anthill-core`.
///
/// `Path` is the development default — points at a local checkout, builds
/// instantly without the network, but is not portable across machines.
/// `Git` pins to a specific commit on a public repository — portable and
/// reproducible without crates.io publication; the consumer needs git
/// access at build time. When `anthill-core` ships to crates.io a third
/// `Registry { version }` variant becomes the right default; until then
/// `Git` is the recommended portable choice.
#[derive(Clone, Debug)]
pub enum CoreDep {
    Path(PathBuf),
    Git { url: String, rev: String },
}

/// Inputs for [`generate_bundle`].
#[derive(Clone, Debug)]
pub struct BundleOptions {
    /// Name of the generated cargo crate (and binary).
    pub project_name: String,
    /// Optional one-line description for the crate's `Cargo.toml`. Skipped
    /// when `None`. Cargo accepts an absent `description` more gracefully
    /// than an empty quoted string, and `cargo publish` rejects empty
    /// descriptions outright — keeping this `Option` avoids both pitfalls.
    pub description: Option<String>,
    /// Operation qualified name to dispatch as the program entry, e.g.
    /// `"my.app.main"`. Must take `args: List[T = String]` and return `Int`.
    pub entry_qname: String,
    /// User anthill sources to bundle. Tuples are (relative path inside the
    /// generated `spec/user/` tree, file contents).
    pub user_sources: Vec<(String, String)>,
    /// Path to the workspace's `stdlib/anthill/` directory. Every `.anthill`
    /// file underneath is vendored into the bundle.
    pub stdlib_dir: PathBuf,
    /// How the generated `Cargo.toml` references `anthill-core`. See
    /// [`CoreDep`] for the trade-offs between path / git / registry.
    pub anthill_core_dep: CoreDep,
}

/// Emit the bundle into `output_dir`. The directory is created if absent;
/// existing files in it are overwritten without warning.
pub fn generate_bundle(opts: &BundleOptions, output_dir: &Path) -> Result<(), BundleError> {
    if opts.user_sources.is_empty() {
        return Err(BundleError::NoSources);
    }
    if !opts.stdlib_dir.is_dir() {
        return Err(BundleError::StdlibNotFound(opts.stdlib_dir.clone()));
    }

    let src_dir = output_dir.join("src");
    let spec_user = output_dir.join("spec/user");
    let spec_stdlib = output_dir.join("spec/stdlib");
    fs::create_dir_all(&src_dir).map_err(|e| BundleError::Io(e, src_dir.clone()))?;
    fs::create_dir_all(&spec_user).map_err(|e| BundleError::Io(e, spec_user.clone()))?;
    fs::create_dir_all(&spec_stdlib).map_err(|e| BundleError::Io(e, spec_stdlib.clone()))?;

    let mut user_rel_paths: Vec<String> = Vec::new();
    for (rel, content) in &opts.user_sources {
        let dest = spec_user.join(rel);
        if let Some(parent) = dest.parent() {
            fs::create_dir_all(parent).map_err(|e| BundleError::Io(e, parent.to_path_buf()))?;
        }
        fs::write(&dest, content).map_err(|e| BundleError::Io(e, dest.clone()))?;
        user_rel_paths.push(rel.clone());
    }

    // Vendor stdlib by copying every .anthill file under stdlib_dir.
    let mut stdlib_rel_paths: Vec<String> = Vec::new();
    copy_anthill_tree(&opts.stdlib_dir, &spec_stdlib, &PathBuf::new(), &mut stdlib_rel_paths)?;
    if stdlib_rel_paths.is_empty() {
        return Err(BundleError::StdlibNotFound(opts.stdlib_dir.clone()));
    }

    let core_dep = render_core_dep(&opts.anthill_core_dep);
    let desc_line = match &opts.description {
        Some(d) if !d.is_empty() => format!("description = \"{}\"\n", escape_toml(d)),
        _ => String::new(),
    };
    let cargo_toml = format!(
        r#"[package]
name = "{name}"
version = "0.1.0"
edition = "2021"
{desc_line}
[[bin]]
name = "{name}"
path = "src/main.rs"

[dependencies]
anthill-core = {core_dep}
"#,
        name = opts.project_name,
    );
    let cargo_path = output_dir.join("Cargo.toml");
    fs::write(&cargo_path, cargo_toml).map_err(|e| BundleError::Io(e, cargo_path.clone()))?;

    let main_rs = render_main(opts, &user_rel_paths, &stdlib_rel_paths);
    let main_path = src_dir.join("main.rs");
    fs::write(&main_path, main_rs).map_err(|e| BundleError::Io(e, main_path.clone()))?;

    Ok(())
}

fn copy_anthill_tree(
    src_root: &Path,
    dst_root: &Path,
    rel: &Path,
    out_paths: &mut Vec<String>,
) -> Result<(), BundleError> {
    let src = src_root.join(rel);
    let entries = fs::read_dir(&src).map_err(|e| BundleError::Io(e, src.clone()))?;
    for entry in entries {
        let entry = entry.map_err(|e| BundleError::Io(e, src.clone()))?;
        let entry_rel = rel.join(entry.file_name());
        let path = entry.path();
        if path.is_dir() {
            let dest_dir = dst_root.join(&entry_rel);
            fs::create_dir_all(&dest_dir).map_err(|e| BundleError::Io(e, dest_dir.clone()))?;
            copy_anthill_tree(src_root, dst_root, &entry_rel, out_paths)?;
        } else if path.extension().and_then(|e| e.to_str()) == Some("anthill") {
            let dest = dst_root.join(&entry_rel);
            if let Some(parent) = dest.parent() {
                fs::create_dir_all(parent).map_err(|e| BundleError::Io(e, parent.to_path_buf()))?;
            }
            fs::copy(&path, &dest).map_err(|e| BundleError::Io(e, dest.clone()))?;
            // Use forward slashes for the rendered include_str! literal regardless of host OS.
            let rel_str = entry_rel.components()
                .filter_map(|c| match c {
                    std::path::Component::Normal(s) => s.to_str().map(|s| s.to_string()),
                    _ => None,
                })
                .collect::<Vec<_>>()
                .join("/");
            out_paths.push(rel_str);
        }
    }
    Ok(())
}

fn escape_toml(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

fn render_core_dep(dep: &CoreDep) -> String {
    match dep {
        CoreDep::Path(p) => format!("{{ path = \"{}\" }}", escape_toml(&p.display().to_string())),
        CoreDep::Git { url, rev } => {
            format!("{{ git = \"{}\", rev = \"{}\" }}", escape_toml(url), escape_toml(rev))
        }
    }
}

/// Render the generated `src/main.rs`. The shim parses the embedded sources,
/// builds a KB, registers the standard runtime, and dispatches the entry op.
fn render_main(opts: &BundleOptions, user_rel: &[String], stdlib_rel: &[String]) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "// Generated by anthill-rust-gen (rust+anthill profile).\n\
         // Entry: {entry}\n\
         //\n\
         // Hand edits will be lost the next time `anthill bundle` runs.\n\n\
         use std::process::ExitCode;\n\
         \n\
         use anthill_core::eval::{{self, Interpreter, Value}};\n\
         use anthill_core::kb::KnowledgeBase;\n\
         use anthill_core::kb::load::{{self, NullResolver}};\n\
         use anthill_core::parse;\n\n",
        entry = opts.entry_qname,
    ));

    // Embedded sources table.
    out.push_str("static EMBEDDED_SOURCES: &[(&str, &str)] = &[\n");
    for rel in stdlib_rel {
        out.push_str(&format!(
            "    (\"stdlib/{rel}\", include_str!(\"../spec/stdlib/{rel}\")),\n"
        ));
    }
    for rel in user_rel {
        out.push_str(&format!(
            "    (\"user/{rel}\", include_str!(\"../spec/user/{rel}\")),\n"
        ));
    }
    out.push_str("];\n\n");

    out.push_str(&format!(
        r#"fn build_kb() -> Result<KnowledgeBase, String> {{
    let mut parsed = Vec::new();
    for (path, source) in EMBEDDED_SOURCES {{
        match parse::parse(source) {{
            Ok(p) => parsed.push(p),
            Err(errs) => {{
                let detail: Vec<String> = errs.iter().map(|e| format!("{{e}}")).collect();
                return Err(format!("parse {{path}}: {{}}", detail.join("; ")));
            }}
        }}
    }}
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    if let Err(errs) = load::load_all(&mut kb, &refs, &NullResolver) {{
        let detail: Vec<String> = errs.iter().map(|e| format!("{{e}}")).collect();
        return Err(format!("load failed: {{}}", detail.join("; ")));
    }}
    Ok(kb)
}}

fn run(argv: Vec<String>) -> Result<i64, String> {{
    let kb = build_kb()?;
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp)
        .map_err(|e| format!("register builtins: {{e:?}}"))?;
    interp.register_standard_effect_handlers()
        .map_err(|e| format!("register effects: {{e:?}}"))?;
    let args_value = build_string_list(&mut interp, argv);
    let result = interp.call("{entry}", &[args_value])
        .map_err(|e| format!("dispatch {entry}: {{e:?}}"))?;
    result.as_int().ok_or_else(|| format!("entry returned non-Int: {{}}", result.type_name()))
}}

// Build a Value::Entity cons-list of strings: cons(s0, cons(s1, ..., nil)).
fn build_string_list(interp: &mut Interpreter, args: Vec<String>) -> Value {{
    let cons_sym = interp.kb().resolve_symbol("anthill.prelude.List.cons");
    let nil_sym  = interp.kb().resolve_symbol("anthill.prelude.List.nil");
    let mut acc = Value::Entity {{ functor: nil_sym, pos: Vec::new().into(), named: Vec::new().into() }};
    for s in args.into_iter().rev() {{
        acc = Value::Entity {{
            functor: cons_sym,
            pos: vec![Value::Str(s), acc].into(),
            named: Vec::new().into(),
        }};
    }}
    acc
}}

fn main() -> ExitCode {{
    let argv: Vec<String> = std::env::args().skip(1).collect();
    match run(argv) {{
        Ok(code) => {{
            if code < 0 || code > 255 {{
                eprintln!("warning: entry returned out-of-range exit code {{code}}; using 1");
                ExitCode::from(1)
            }} else {{
                ExitCode::from(code as u8)
            }}
        }}
        Err(msg) => {{
            eprintln!("error: {{msg}}");
            ExitCode::from(2)
        }}
    }}
}}
"#,
        entry = opts.entry_qname,
    ));

    out
}
